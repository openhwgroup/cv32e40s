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
  input  logic [31:0] pc_if_i,             // Current IF stage PC
  input  ctrl_fsm_t   ctrl_fsm_i,          // Controller struct
  input  if_id_pipe_t if_id_pipe_i,        // IF/ID pipeline registers
  input  logic [31:0] jump_target_i,       // Jump target from ID stage
  input  logic [31:0] branch_target_i,     // Branch target from EX stage
  input  logic        branch_decision_i,   // Branch decision from EX stage
  
  // Last_op inputs
  input  logic        last_op_id_i,
  input  logic        last_op_ex_i,

  // CSR inputs
  input  logic [31:0] mepc_i,
  input  logic [23:0] mtvec_addr_i,
  input  logic [31:0] dpc_i,
  
  // Static core inputs
  input  logic [31:0] boot_addr_i,         // Boot address from toplevel pins
  input  logic [31:0] dm_halt_addr_i,      // Debug address from toplevel pins
  input  logic [31:0] dm_exception_addr_i, // Debug exception from toplevel pins
  input  logic [31:0] nmi_addr_i,          // NMI address from toplevel pins

  // Error output
  output logic        pc_err_o             // Error flag
);

// Flopped versions of pc_set and pc_mux
logic    pc_set_q; // pc_set was active previous cycle
logic    if_id_q;  // if_valkd && id_ready was active previous cycle
pc_mux_e pc_mux_q; // Last value of pc_mux

logic    compare_enable;

// Expected PC for incremental execution
logic [31:0] incr_addr;

// Address for comparison with pc_if
logic [31:0] check_addr;

// Address for non-sequential PC changes
logic [31:0] ctrl_flow_addr;

// Address comparison error
logic addr_err;

// Control flow decision error
logic ctrl_flow_err;
logic ctrl_flow_taken_err;    // Signals error on taken jump/mret/branch
logic ctrl_flow_untaken_err;  // Signals error on untaken jump/mret/branch

//////////////////////////////////////////
// PC checking
//////////////////////////////////////////

// Set expected address for sequential updates based on address in ID
// and type of instruction (compressed +2 / uncompressed + 4)
assign incr_addr = if_id_pipe_i.pc + (if_id_pipe_i.instr_meta.compressed ? 32'd2 : 32'd4);

// Control flow address chosen based on flopped ctrl_fsm_i.pc_mux
// If the pc_mux is glitched, this mux may choose the wrong address
// and an address comparison error is likely to happen.
assign ctrl_flow_addr = (pc_mux_q == PC_JUMP)     ? jump_target_i         :
                        (pc_mux_q == PC_MRET)     ? mepc_i                :
                        (pc_mux_q == PC_BRANCH)   ? branch_target_i       :
                        (pc_mux_q == PC_TRAP_DBD) ? dm_halt_addr_i        :
                        (pc_mux_q == PC_TRAP_DBE) ? dm_exception_addr_i   :
                        (pc_mux_q == PC_TRAP_NMI) ? nmi_addr_i            :
                        (pc_mux_q == PC_TRAP_EXC) ? {mtvec_addr_i, 8'h0 } : // Also covered by CSR hardening
                        (pc_mux_q == PC_DRET)     ? dpc_i                 : {boot_addr_i[31:2], 2'b00};

// Choose which address to check vs pc_if, sequential or control flow.
assign check_addr = !pc_set_q ? incr_addr : {ctrl_flow_addr[31:1], 1'b0};

// Comparator for address
// Comparison is only valid the cycle after pc_set or the cycle
// after an instruction goes from IF to ID and it is not a dummy.
assign addr_err = (pc_set_q || (if_id_q && !if_id_pipe_i.instr_meta.dummy)) ? (check_addr != pc_if_i)  : 1'b0;

//////////////////////////////////
// Decision check
//////////////////////////////////

// Comparator for control flow decision
// Check if taken jumps, mret and branches are correct by checking the decision
// in the last cycle of the instructions.
// Not checking for the cases of:
// - pc_set_q == 1 && ctrl_fsm_i.pc_set == 1 as this indicates another decision in control flow has taken place
//   and will override the previous pc_set (interrupts, NMI, debug can be sources for this)
// - ID stage is halted. This may happen for pending interrupts and debug, and will possibly change the state of
//   ctrl_fsm_i.branch_in_ex. Unless an interrupt is retracted, jumps and branches will be killed before the
//   interrupt is taken.
assign ctrl_flow_taken_err = (((pc_mux_q == PC_JUMP)   && !ctrl_fsm_i.jump_in_id)                          ||
                              ((pc_mux_q == PC_BRANCH) && !(ctrl_fsm_i.branch_in_ex && branch_decision_i)) ||
                              ((pc_mux_q == PC_MRET)   && !ctrl_fsm_i.jump_in_id))                         &&
                             (pc_set_q && !ctrl_fsm_i.pc_set && !ctrl_fsm_i.halt_id);

// Check if we should have taken a jump, mret or branch when pc_set was not set
assign ctrl_flow_untaken_err = !pc_set_q &&
                               ((ctrl_fsm_i.jump_taken_id && last_op_id_i) || // includes mret
                                (ctrl_fsm_i.branch_taken_ex && last_op_ex_i));
                                

assign ctrl_flow_err = ctrl_flow_taken_err || ctrl_flow_untaken_err;

///////////
// Flops //
///////////
always_ff @(posedge clk, negedge rst_n) begin
  if (rst_n == 1'b0) begin
    pc_set_q <= 1'b0;
    pc_mux_q <= PC_BOOT;
    compare_enable <= 1'b0;
    if_id_q <= 1'b0;
  end else begin
    // Signal that a pc_set set was performed.
    // Exlucde cases of PC_WB_PLUS4 and PC_TRAP_IRQ as the pipeline currently has no easy way to recompute these targets.
    // Also exclude if ID stage is halted as this indicates interrupt, NMI or debug that will change the program flow and kill
    // younger instructions.
    pc_set_q <= ctrl_fsm_i.pc_set && !((ctrl_fsm_i.pc_mux == PC_WB_PLUS4) || (ctrl_fsm_i.pc_mux == PC_TRAP_IRQ)) && !ctrl_fsm_i.halt_id;

    // Set a flag for a valid IF->ID stage transition.
    if_id_q  <= if_valid_i && id_ready_i;

    // On a pc_set, flop the pc_mux and set a sticky compare_enable bit.
    if(ctrl_fsm_i.pc_set) begin
      pc_mux_q <= ctrl_fsm_i.pc_mux;
      compare_enable <= 1'b1;
    end
  end
end

// Assign error output
assign pc_err_o = (addr_err || ctrl_flow_err) && compare_enable;

endmodule // cv32e40s_pc_check
