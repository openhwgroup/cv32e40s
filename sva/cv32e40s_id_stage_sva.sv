// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Renzo Andri - andrire@student.ethz.ch                      //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the id_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_id_stage_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
#(
  parameter int unsigned REGFILE_NUM_READ_PORTS = 2
)
(
  input logic           clk,
  input logic           rst_n,

  input logic [31:0]    instr,
  input logic           rf_we,
  input logic           alu_en,
  input logic           div_en,
  input logic           mul_en,
  input logic           csr_en,
  input logic           sys_en,
  input logic           lsu_en,
  input logic           xif_en,
  input alu_op_a_mux_e  alu_op_a_mux_sel,
  input alu_op_b_mux_e  alu_op_b_mux_sel,
  input logic           lsu_we,
  input op_c_mux_e      op_c_mux_sel,
  input logic           sys_dret_insn,
  input logic           sys_ebrk_insn,
  input logic           sys_ecall_insn,
  input logic           sys_fencei_insn,
  input logic           sys_mret_insn,
  input logic           sys_wfi_insn,
  input logic           ex_ready_i,
  input logic           illegal_insn,
  input logic [31:0]    operand_a_fw,
  input logic [31:0]    operand_b_fw,
  input logic [REGFILE_NUM_READ_PORTS-1:0] rf_re_o,
  input rf_addr_t       rf_raddr_o[REGFILE_NUM_READ_PORTS],
  input rf_data_t       rf_rdata_i[REGFILE_NUM_READ_PORTS],
  input csr_opcode_e    csr_op,
  input if_id_pipe_t    if_id_pipe_i,
  input id_ex_pipe_t    id_ex_pipe_o,
  input ex_wb_pipe_t    ex_wb_pipe,
  input logic           id_ready_o,
  input logic           id_valid_o,
  input ctrl_fsm_t      ctrl_fsm_i,
  input ctrl_byp_t      ctrl_byp_i,
  input mstatus_t       mstatus_i,
  input logic           xif_insn_accept,
  input logic           last_sec_op,
  input logic [31:0]    jalr_fw,
  input logic           alu_jmp,
  input logic           alu_jmpr,
  input logic [31:0]    jmp_target_o,
  input logic           jmp_taken_id_ctrl_i



);

/* todo: check and fix/remove
      // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
      // and that EX stage is ready to receive flushed instruction immediately
      property p_branch_taken_ex;
        @(posedge clk) disable iff (!rst_n) (branch_taken_ex == 1'b1) |-> ((ex_ready_i == 1'b1) &&
                                                                           (alu_en == 1'b0) &&
                                                                           (mul_en == 1'b0) &&
                                                                           (rf_we == 1'b0) &&
                                                                           (lsu_en == 1'b0));
      endproperty

      a_branch_taken_ex : assert property(p_branch_taken_ex) else `uvm_error("id_stage", "Assertion p_branch_taken_ex failed")
*/

/* todo: check and fix/remove
      // Check that if IRQ PC update does not coincide with IRQ related CSR write
      // MIE is excluded from the check because it has a bypass.
      property p_irq_csr;
        @(posedge clk) disable iff (!rst_n)
          (pc_set_o &&
           ((pc_mux_o == PC_TRAP_EXC) || (pc_mux_o == PC_TRAP_IRQ)) &&
           id_ex_pipe_o.csr_access && (id_ex_pipe_o.csr_op != CSR_OP_READ)) |->
                                  ((id_ex_pipe_o.alu_operand_b[11:0] != CSR_MSTATUS) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MEPC) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MCAUSE) &&
                                   (id_ex_pipe_o.alu_operand_b[11:0] != CSR_MTVEC));
      endproperty

      a_irq_csr : assert property(p_irq_csr) else `uvm_error("id_stage", "Assertion p_irq_csr failed")
*/

  // Check that illegal instruction has no other side effects
  // If XIF accepts instruction, rf_we may still be 1
  a_illegal_1 :
    assert property (@(posedge clk) disable iff (!rst_n)
      (illegal_insn == 1'b1) |-> !(alu_en || csr_en || sys_en || mul_en || div_en || lsu_en))
    else `uvm_error("id_stage", "No functional units (except for XIF) should be enabled for illegal instructions")

  a_illegal_2 :
    assert property (@(posedge clk) disable iff (!rst_n)
      (illegal_insn == 1'b1) |-> (
      (csr_op == CSR_OP_READ) &&
      (alu_op_a_mux_sel == OP_A_NONE) && (alu_op_b_mux_sel == OP_B_NONE) || (op_c_mux_sel == OP_C_NONE) &&
      !(rf_we && !xif_insn_accept)))
    else `uvm_error("id_stage", "Illegal instructions should not have side effects")

  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_id && !ctrl_fsm_i.kill_id)
                      |-> (!id_ready_o && !id_valid_o))
      else `uvm_error("id_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_id)
                      |-> (id_ready_o && !id_valid_o))
      else `uvm_error("id_stage", "Kill should imply ready and not valid")

  // Assert that we never get a triggermatch on a dummy instruction
  a_no_trigger_match_on_dummy :
    assert property (@(posedge clk) disable iff (!rst_n)
                     if_id_pipe_i.instr_meta.dummy |-> !if_id_pipe_i.trigger_match)
      else `uvm_error("id_stage", "Trigger match on dummy instruction")


  // Assert that regular (non-dummy, non-hint) instructions use 0 instead of the R0 register value
  a_non_dummy_or_hint_reads_0_from_r0_p0:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[0] && (rf_raddr_o[0] == 'b0) && !(if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) |-> (operand_a_fw == 32'h0))
      else `uvm_error("id_stage", "Non-dummy or non-hint instruction used non-zero value from R0 (on read port 0)")

  a_non_dummy_or_hint_reads_0_from_r0_p1:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[1] && (rf_raddr_o[1] == 'b0) && !(if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) |-> (operand_b_fw == 32'h0))
      else `uvm_error("id_stage", "Non-dummy instruction used non-zero value from R0 (on read port 1)")

  // Cover to check that dummies can read non-zero values from x0
  a_dummy_can_read_r0_p0:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[0] && (rf_raddr_o[0] == 'b0) && (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) && (operand_a_fw != '0)|-> 1'b1)
      else `uvm_error("id_stage", "Dummy or hint instruction could not read from R0 (on read port 0)")

  // Cover to check that dummies can read non-zero values from x0
  a_dummy_can_read_r0_p1:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[1] && (rf_raddr_o[1] == 'b0) && (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) && (operand_b_fw != '0)|-> 1'b1)
      else `uvm_error("id_stage", "Dummy or hint instruction could not read from R0 (on read port 1)")

  // LFSR should be used for x1-bx31, regfile or relevant forwards for x0
  a_dummy_opa_mux_check:
    assert property (@(posedge clk) disable iff (!rst_n)
                     (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) |-> ( ((ctrl_byp_i.operand_a_fw_mux_sel == SEL_LFSR)    && (rf_raddr_o[0] != 'b0))  ||
                                                                                           ((ctrl_byp_i.operand_a_fw_mux_sel == SEL_REGFILE) && (rf_raddr_o[0] == 'b0))   ||
                                                                                           ((ctrl_byp_i.operand_a_fw_mux_sel == SEL_FW_EX)   && (rf_raddr_o[0] == 'b0))   ||
                                                                                           ((ctrl_byp_i.operand_a_fw_mux_sel == SEL_FW_WB)   && (rf_raddr_o[0] == 'b0))))
      else `uvm_error("id_stage", "Illegal operand a mux select value for dummy or hint instruction")

  // LFSR should be used for x1-bx31, regfile or relevant forwards for x0
  a_dummy_opb_mux_check:
    assert property (@(posedge clk) disable iff (!rst_n)
                     (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) |-> ( ((ctrl_byp_i.operand_b_fw_mux_sel == SEL_LFSR)    && (rf_raddr_o[1] != 'b0))  ||
                                                                                           ((ctrl_byp_i.operand_b_fw_mux_sel == SEL_REGFILE) && (rf_raddr_o[1] == 'b0))   ||
                                                                                           ((ctrl_byp_i.operand_b_fw_mux_sel == SEL_FW_EX)   && (rf_raddr_o[1] == 'b0))   ||
                                                                                           ((ctrl_byp_i.operand_b_fw_mux_sel == SEL_FW_WB)   && (rf_raddr_o[1] == 'b0))))
      else `uvm_error("id_stage", "Illegal operand b mux select value for dummy or hint instruction")


  // Ensure that functional unit enables are one-hot (ALU and DIV both use the ALU though)
  a_functional_unit_enable_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot0({alu_en, div_en, mul_en, csr_en, sys_en, lsu_en, xif_en}))
      else `uvm_error("id_stage", "Multiple functional units enabled")

  // Check that second part of a multicycle mret does not stall on the first part of the same instruction
  a_mret_self_stall :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (sys_en && sys_mret_insn && last_sec_op) &&
                      ((id_ex_pipe_o.sys_en && id_ex_pipe_o.sys_mret_insn) ||
                       (ex_wb_pipe.sys_en && ex_wb_pipe.sys_mret_insn))
                       |-> !ctrl_byp_i.csr_stall)
      else `uvm_error("id_stage", "mret stalls on itself")


  // Assert that jalr_fw has the same value as operand_a_fw when a jump is taken
  // Only checking for JALR, as regular JAL do not use any RF or bypass operands for the jump target.
  // Checked because RVFI is using operand_a_fw only, even for JALR instructions. With this assert proven,
  // there is no need to mux in jalr_fw inside RVFI.
  a_jalr_fw_match :
    assert property (@(posedge clk) disable iff (!rst_n)
                      jmp_taken_id_ctrl_i && alu_jmpr
                      |->
                      (jalr_fw == operand_a_fw))
      else `uvm_error("id_stage", "jalr_fw does not match operand_a_fw")

  // Assert stable jump target for a jump instruction that stays multiple cycles in ID
  // Target must remain stable until instruction exits ID (id_valid && ex_ready, or
  // instructions is killed.
  property p_jmp_target_stable;
    logic [31:0] jmp_target;
    @(posedge clk) disable iff (!rst_n)
    (jmp_taken_id_ctrl_i && !ctrl_fsm_i.kill_id, jmp_target=jmp_target_o)
    |->
    (jmp_target == jmp_target_o) until_with ((id_valid_o && ex_ready_i) || ctrl_fsm_i.kill_id);
  endproperty

  a_jmp_target_stable: assert property (p_jmp_target_stable)
    else `uvm_error("id_stage", "Jump target not stable")
endmodule

