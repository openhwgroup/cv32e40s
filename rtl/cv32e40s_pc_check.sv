// Copyright 2021 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40s_pc_check                                          //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This module will check the recomputed PC values for jumps, //
//                 branches and sequential instructions.                      //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_pc_check import cv32e40s_pkg::*;
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        if_valid_i,
  input  logic        id_ready_i,
  input  logic        id_valid_i,
  input  logic        ex_ready_i,
  input  logic        ex_valid_i,
  input  logic        wb_ready_i,
  input  logic [31:0] pc_if_i,                // Current IF stage PC
  input  ctrl_fsm_t   ctrl_fsm_i,             // Controller struct
  input  if_id_pipe_t if_id_pipe_i,           // IF/ID pipeline registers
  input  id_ex_pipe_t id_ex_pipe_i,           //
  input  logic [31:0] jump_target_id_i,       // Jump target from ID stage
  input  logic [31:0] branch_target_ex_i,     // Branch target from EX stage
  input  logic        branch_decision_ex_i,   // Branch decision from EX stage

  // Last_op inputs
  input  logic        last_sec_op_id_i,       // Using last_sec_op from ID (may harden tablejump suboperations which are not 'last_op')
  input  logic        last_op_ex_i,           // Using last_op from EX, only used for hardening of branches where last_sec_op == last_op

  // CLIC inputs
  input  logic        prefetch_is_ptr_i,      // Indicates that "instruction" in IF is a pointer

  // CSR inputs
  input  logic [31:0] mepc_i,
  input  logic [24:0] mtvec_addr_i,
  input  logic [31:0] dpc_i,
  input  logic [JVT_ADDR_WIDTH-1:0] jvt_addr_i,

  // Static core inputs
  input  logic [31:0] boot_addr_i,         // Boot address from toplevel pins
  input  logic [31:0] dm_halt_addr_i,      // Debug address from toplevel pins
  input  logic [31:0] dm_exception_addr_i, // Debug exception from toplevel pins

  // Error output
  output logic        pc_err_o             // Error flag
);

// Flopped versions of pc_set and pc_mux
logic    pc_set_q;        // pc_set was active previous cycle
logic    if_id_q;         // if_valid && id_ready was active previous cycle
logic    jmp_taken_q;     // A jump was taken. Sticky until last part of instruction is done
logic    bch_taken_q;     // A branch was taken. Sticky until last part of instruction is done
pc_mux_e pc_mux_q;        // Last value of pc_mux (for address comparison)


logic    compare_enable_q;

// Expected PC for incremental execution
logic [31:0] incr_addr;

// Address for comparison with pc_if
logic [31:0] check_addr;

// Address for non-sequential PC changes
logic [31:0] ctrl_flow_addr;

// Address comparison error
logic addr_err;

// Control flow decision error
logic jump_mret_taken_err;
logic jump_mret_untaken_err;
logic branch_taken_err;
logic branch_untaken_err;
logic ctrl_flow_err;
logic ctrl_flow_taken_err;    // Signals error on taken jump/mret/branch
logic ctrl_flow_untaken_err;  // Signals error on untaken jump/mret/branch

logic [31:0] nmi_addr;

assign nmi_addr = {mtvec_addr_i, NMI_MTVEC_INDEX, 2'b00};


//////////////////////////////////////////
// PC checking
//////////////////////////////////////////

// Set expected address for sequential updates based on address in ID
// and type of instruction (compressed +2 / uncompressed + 4)
assign incr_addr = if_id_pipe_i.pc + (if_id_pipe_i.instr_meta.dummy      ? 32'd0 :
                                      if_id_pipe_i.instr_meta.tbljmp     ? 32'd2 : // Table jumps ack the prefetcher, PC in IF increase by 2.
                                     (!if_id_pipe_i.last_op)             ? 32'd0 : // sequenced instructions keep the same PC until last_op
                                      if_id_pipe_i.instr_meta.compressed ? 32'd2 : 32'd4);

// Control flow address chosen based on flopped ctrl_fsm_i.pc_mux
// If the pc_mux is glitched, this mux may choose the wrong address
// and an address comparison error is likely to happen.

assign ctrl_flow_addr = (pc_mux_q == PC_JUMP)     ? jump_target_id_i      :
                        (pc_mux_q == PC_MRET)     ? mepc_i                :
                        (pc_mux_q == PC_BRANCH)   ? branch_target_ex_i    :
                        (pc_mux_q == PC_TRAP_DBD) ? dm_halt_addr_i        :
                        (pc_mux_q == PC_TRAP_DBE) ? dm_exception_addr_i   :
                        (pc_mux_q == PC_TRAP_NMI) ? nmi_addr              :
                        (pc_mux_q == PC_TRAP_EXC) ? {mtvec_addr_i, 7'h0 } : // Also covered by CSR hardening
                        (pc_mux_q == PC_DRET)     ? dpc_i                 :
                        (pc_mux_q == PC_POINTER)  ? if_id_pipe_i.ptr      : // Only for Zc, gated by not raising pc_set_q for CLIC pointers.
                        (pc_mux_q == PC_TBLJUMP)  ? {jvt_addr_i, ctrl_fsm_i.jvt_pc_mux, 2'b00} : {boot_addr_i[31:2], 2'b00};

// Choose which address to check vs pc_if, sequential or control flow.
// Instructions are 16 bit aligned since the core supports the C extension.
// This tieoff of bit 0 is similar to the connection of the prefetch unit in the if_stage.
assign check_addr = !pc_set_q ? incr_addr : {ctrl_flow_addr[31:1], 1'b0};

// Comparator for address
// Comparison is only valid the cycle after pc_set or the cycle
// after an instruction goes from IF to ID.
assign addr_err = (pc_set_q || if_id_q) ? (check_addr != pc_if_i)  : 1'b0;

//////////////////////////////////
// Decision check
//////////////////////////////////

// Check if taken jumps, mret and branches are correct
// Jumps and branches shall be taken during the first cycle of the instruction.
// If a taken jump or branch is observed (*_taken_q flag is set), a jump or branch
// instruction must still be in ID (jumps) or EX (branches). Using the _raw signals
// from the controller disregards any halts or kills that could change instr_valid. The instruction
// control signals shall still be present in the pipeline stages.
// Not factoring in last_sec_op_* signals, as this would cause the checks to fail if a jump or branch
// was stalled such that the taken flags would be set while the first half was still in ID or EX.
assign jump_mret_taken_err   = jmp_taken_q && !(ctrl_fsm_i.jump_in_id_raw);
assign branch_taken_err      = bch_taken_q && !(ctrl_fsm_i.branch_in_ex_raw && branch_decision_ex_i);

// Check if jumps or branches should have been taken when the controller did not take them.
// Since jumps and branches shall be taken during the first operation of the instruction,
// we cannot observe an untaken jump/branch (*_taken_q is not set) and at the same time have a valid
// jump or branch instruction with the last_sec_op bit set. Qualifying with registered instr_valid to make sure
// the instruction was not killed earlier, which would cause the jump or branch to correctly be not taken.
assign jump_mret_untaken_err = !jmp_taken_q && (ctrl_fsm_i.jump_in_id_raw   && if_id_pipe_i.instr_valid && last_sec_op_id_i);
assign branch_untaken_err    = !bch_taken_q && (ctrl_fsm_i.branch_in_ex_raw && id_ex_pipe_i.instr_valid && last_op_ex_i && branch_decision_ex_i);


assign ctrl_flow_taken_err = jump_mret_taken_err || branch_taken_err;
assign ctrl_flow_untaken_err = jump_mret_untaken_err || branch_untaken_err;





assign ctrl_flow_err = ctrl_flow_taken_err || ctrl_flow_untaken_err;

///////////
// Flops //
///////////
always_ff @(posedge clk, negedge rst_n) begin
  if (rst_n == 1'b0) begin
    pc_set_q         <= 1'b0;
    pc_mux_q         <= PC_BOOT;
    compare_enable_q <= 1'b0;
    if_id_q          <= 1'b0;
    jmp_taken_q      <= 1'b0;
    bch_taken_q      <= 1'b0;
  end else begin
    // Signal that a pc_set set was performed.
    // Exclude cases of PC_WB_PLUS4, PC_TRAP_IRQ and CLIC pointers as the pipeline currently has no easy way to recompute these targets.
    // Pointers (if_id_pipe.ptr) should already be hardened by parity checks.
    // Used for the address comparison
    // Todo: may stretch this until the target instruction leaves IF stage
    pc_set_q <= ctrl_fsm_i.pc_set && !((ctrl_fsm_i.pc_mux == PC_WB_PLUS4) || (ctrl_fsm_i.pc_mux == PC_TRAP_IRQ) ||
                                       (ctrl_fsm_i.pc_mux == PC_TRAP_CLICV) ||
                                       ((ctrl_fsm_i.pc_mux == PC_POINTER) && !if_id_pipe_i.instr_meta.tbljmp));

    // Set a flag for a valid IF->ID stage transition.
    // Used for checking sequential PCs.
    // Exlude the case where a pointer goes from IF to ID as to avoid mismatch on addresses
    // (pointer address may have LSBs that indicate a compressed instruction)
    if_id_q  <= (if_valid_i && id_ready_i) && !prefetch_is_ptr_i;

    // Flag for taken jump
    // Jumps are taken from ID, and the flag can thus only be cleared when the last part (2/2) of the instruction
    // is done in the ID stage, or ID stage is killed.
    if((id_valid_i && ex_ready_i && last_sec_op_id_i) || ctrl_fsm_i.kill_id) begin
      jmp_taken_q <= 1'b0;
    end else begin
      // Set flag for jumps and mret
      // Both operations of a table jump counts as a jump (instruction word remain the same, only the pointer field change)
      if(ctrl_fsm_i.pc_set && ((ctrl_fsm_i.pc_mux == PC_JUMP) || (ctrl_fsm_i.pc_mux == PC_MRET) ||
        (ctrl_fsm_i.pc_mux == PC_TBLJUMP) || ((ctrl_fsm_i.pc_mux == PC_POINTER) && if_id_pipe_i.instr_meta.tbljmp))) begin
        jmp_taken_q <= 1'b1;
      end
    end

    // Flag for taken branches
    // Branches are taken from EX, and the flag can thus only be cleared when the last part (2/2) of the instruction
    // is done in the EX stage, or EX stage is killed.
    if((ex_valid_i && wb_ready_i && last_op_ex_i) || ctrl_fsm_i.kill_ex) begin
      bch_taken_q <= 1'b0;
    end else begin
      // Set flag for branches
      if(ctrl_fsm_i.pc_set && (ctrl_fsm_i.pc_mux == PC_BRANCH)) begin
        bch_taken_q <= 1'b1;
      end
    end

    // On a pc_set, flop the pc_mux and set a sticky compare_enable_q bit.
    if(ctrl_fsm_i.pc_set) begin
      pc_mux_q <= ctrl_fsm_i.pc_mux;
      compare_enable_q <= 1'b1;
    end
  end
end

// Assign error output
assign pc_err_o = (addr_err || ctrl_flow_err) && compare_enable_q;

endmodule // cv32e40s_pc_check
