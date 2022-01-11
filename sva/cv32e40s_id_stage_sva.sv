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
  input logic           id_ready_o,
  input logic           id_valid_o,
  input ctrl_fsm_t      ctrl_fsm_i,
  input mstatus_t       mstatus_i,
  input logic           xif_insn_accept
);

    // the instruction delivered to the ID stage should always be valid
    a_valid_instr :
      assert property (@(posedge clk)
                       (if_id_pipe_i.instr_valid & (~if_id_pipe_i.illegal_c_insn)) |-> (!$isunknown(instr)) )
        else `uvm_error("id_stage", $sformatf("%t, Instruction is valid, but has at least one X", $time));
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

/* todo: fix
      generate
        if (!A_EXT) begin : gen_no_a_extension_assertions

          // Check that A extension opcodes are decoded as illegal when A extension not enabled
          property p_illegal_0;
          @(posedge clk) disable iff (!rst_n) (instr[6:0] == OPCODE_AMO) |-> (illegal_insn == 'b1);
        endproperty

          a_illegal_0 : assert property(p_illegal_0) else `uvm_error("id_stage", "Assertion p_illegal_0 failed")

        end
      endgenerate
*/
      // Check that illegal instruction has no other side effects
      // If xif accepts instruction, rf_we may still be 1
      property p_illegal_2;
        @(posedge clk) disable iff (!rst_n) (illegal_insn == 1'b1) |-> !((sys_en && sys_ebrk_insn) ||
                                                                         (sys_en && sys_mret_insn) ||
                                                                         (sys_en && sys_dret_insn) ||
                                                                         (sys_en && sys_ecall_insn) ||
                                                                         (sys_en && sys_wfi_insn) ||
                                                                         (sys_en && sys_fencei_insn) ||
                                                                         alu_en ||
                                                                         mul_en ||
                                                                         div_en ||
                                                                         (rf_we && !xif_insn_accept) ||
                                                                         (csr_op != CSR_OP_READ) ||
                                                                        lsu_en);
      endproperty

      a_illegal_2 : assert property(p_illegal_2) else `uvm_error("id_stage", "Assertion p_illegal_2 failed")

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


  // Assert that regular (non-dummy) instructions use 0 instead of the R0 register value
  a_non_dummy_reads_0_from_r0_p0:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[0] && (rf_raddr_o[0] == 32'h0) && !if_id_pipe_i.instr_meta.dummy |-> (operand_a_fw == 32'h0))
      else `uvm_error("id_stage", "Non-dummy instruction used non-zero value from R0 (on read port 0)")

  a_non_dummy_reads_0_from_r0_p1:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[1] && (rf_raddr_o[1] == 32'h0) && !if_id_pipe_i.instr_meta.dummy |-> (operand_b_fw == 32'h0))
      else `uvm_error("id_stage", "Non-dummy instruction used non-zero value from R0 (on read port 1)")

  a_dummy_can_read_r0_p0:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[0] && (rf_raddr_o[0] == 32'h0) && if_id_pipe_i.instr_meta.dummy |-> (operand_a_fw == rf_rdata_i[0]))
      else `uvm_error("id_stage", "Dummy instruction could not read from R0 (on read port 0)")

  a_dummy_can_read_r0_p1:
    assert property (@(posedge clk) disable iff (!rst_n)
                     rf_re_o[1] && (rf_raddr_o[1] == 32'h0) && if_id_pipe_i.instr_meta.dummy |-> (operand_b_fw == rf_rdata_i[1]))
      else `uvm_error("id_stage", "Dummy instruction could not read from R0 (on read port 1)")
  // Ensure that functional unit enables are one-hot (ALU and DIV both use the ALU though)
  a_functional_unit_enable_onehot :
    assert property (@(posedge clk) disable iff (!rst_n)
                     $onehot0({alu_en, div_en, mul_en, csr_en, sys_en, lsu_en, xif_en}))
      else `uvm_error("id_stage", "Multiple functional units enabled")

/* todo:ab:insert once sys* transformation is complete
  // Ensure that the A operand is only used for certain functional units
  a_alu_op_a_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (alu_op_a_mux_sel != OP_A_NONE)
                      |-> ((alu_en || div_en || csr_en || lsu_en) && !(mul_en || sys_en || xif_en)))
      else `uvm_error("id_stage", "Unexpected A operand usage")

  // Ensure that the B operand is only used for certain functional units
  a_alu_op_b_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (alu_op_b_mux_sel != OP_B_NONE)
                      |-> ((alu_en || div_en || csr_en || lsu_en) && !(mul_en || sys_en || xif_en)))
      else `uvm_error("id_stage", "Unexpected A operand usage")

  // Ensure that the C operand is only used for certain functional units
  a_op_c_mux_sel :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (op_c_mux_sel != OP_C_NONE)
                      |-> ((alu_en || (lsu_en && lsu_we))))
      else `uvm_error("id_stage", "Unexpected A operand usage")
*/

endmodule // cv32e40s_id_stage_sva

