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
// Authors:        Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the core module                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_core_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int PMA_NUM_REGIONS = 0,
    parameter bit SMCLIC = 0
  )
  (
  input logic        clk,
  input logic        rst_ni,

  input ctrl_fsm_t   ctrl_fsm,
  input logic [10:0] exc_cause,
  input logic [31:0] mie,
  input logic [31:0] mip,
  input dcsr_t       dcsr,
  input              if_id_pipe_t if_id_pipe,
  input              id_stage_multi_op_id_stall,
  input logic        id_stage_id_valid,
  input logic        ex_ready,
  input logic        irq_ack, // irq ack output
  input logic        irq_clic_shv, // ack'ed irq is a CLIC SHV
  input ex_wb_pipe_t ex_wb_pipe,
  input id_ex_pipe_t id_ex_pipe,
  input logic        sys_en_id,
  input logic        sys_mret_insn_id,
  input logic        wb_valid,
  input logic        branch_taken_in_ex,
  input logic        last_op_wb,

  input privlvl_t    priv_lvl,
  input privlvl_t    priv_lvl_if,
  input privlvl_t    priv_lvl_if_q,

  // Instruction memory interface
  input  logic        instr_req_o,
  input  logic        instr_reqpar_o,
  input  logic        instr_gnt_i,
  input  logic        instr_gntpar_i,
  input  logic        instr_rvalid_i,
  input  logic        instr_rvalidpar_i,
  input  logic [31:0] instr_addr_o,
  input  logic [11:0] instr_achk_o,
  input  logic [1:0]  instr_memtype_o,
  input  logic [2:0]  instr_prot_o,
  input  logic        instr_dbg_o,
  input  logic [31:0] instr_rdata_i,
  input  logic [4:0]  instr_rchk_i,
  input  logic        instr_err_i,

  // Data memory interface
  input  logic        data_req_o,
  input  logic        data_reqpar_o,
  input  logic        data_gnt_i,
  input  logic        data_gntpar_i,
  input  logic        data_rvalid_i,
  input  logic        data_rvalidpar_i,
  input  logic        data_we_o,
  input  logic [3:0]  data_be_o,
  input  logic [31:0] data_addr_o,
  input  logic [11:0] data_achk_o,
  input  logic [1:0]  data_memtype_o,
  input  logic [2:0]  data_prot_o,
  input  logic        data_dbg_o,
  input  logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic [4:0]  data_rchk_i,
  input  logic        data_err_i,
  input alu_op_a_mux_e alu_op_a_mux_sel_id_i,
  input alu_op_b_mux_e alu_op_b_mux_sel_id_i,
  input logic [31:0]   operand_a_id_i,
  input logic [31:0]   operand_b_id_i,
  input logic [31:0]   jalr_fw_id_i,
  input logic [31:0]   rf_wdata_wb,
  input logic          rf_we_wb,

  input logic        alu_jmpr_id_i,
  input logic        alu_en_id_i,

  // probed controller signals
  input logic        ctrl_debug_mode_n,
  input logic        ctrl_pending_debug,
  input logic        ctrl_debug_allowed,
  input              ctrl_state_e ctrl_fsm_ns,
  input ctrl_byp_t   ctrl_byp,
   // probed cs_registers signals
  input logic [31:0] cs_registers_mie_q,
  input logic [31:0] cs_registers_mepc_n,
  input mcause_t     cs_registers_csr_cause_i, // From controller
  input mcause_t     cs_registers_mcause_q,    // From cs_registers, flopped mcause
  input mstatus_t    cs_registers_mstatus_q,
  input logic        pc_err_if,
  input logic        csr_err,
  input logic        itf_int_err,
  input logic        rf_ecc_err,

  input logic        sys_mret_unqual_id_bypass,
  input logic        jmpr_unqual_id_bypass,
  input logic        mret_self_stall_bypass,
  input logic        jumpr_self_stall_bypass,
  input logic        last_sec_op_id_i
  );

if(SMCLIC) begin
  property p_clic_mie_tieoff;
    @(posedge clk)
    |mie == 1'b0;
  endproperty
  a_clic_mie_tieoff : assert property(p_clic_mie_tieoff) else `uvm_error("core", "MIE not tied to 0 in CLIC mode")

  property p_clic_mip_tieoff;
    @(posedge clk)
    |mip == 1'b0;
  endproperty
  a_clic_mip_tieoff : assert property(p_clic_mip_tieoff) else `uvm_error("core", "MIP not tied to 0 in CLIC mode")

  //todo: add CLIC related assertions (level thresholds etc)
end else begin
  // SMCLIC == 0
  // Check that a taken IRQ is actually enabled (e.g. that we do not react to an IRQ that was just disabled in MIE)
  // The actual mie_n value may be different from mie_q if mie is not
  // written to.
  // Only checking mstatus.mie for interrupts in Machine mode. During User mode, interrupts shall be taken regardsless
  // of the mstatus.mie bit (but still have to have the interrupt enabled in MIE CSR)
  // Priv spec: "Interrupts for higher-privilege modes, y>x, are always globally enabled regardless of the setting of the global yIE
  // bit for the higher-privilege mode. "
  property p_irq_enabled_0;
    @(posedge clk) disable iff (!rst_ni)
    (ctrl_fsm.pc_set && (ctrl_fsm.pc_mux == PC_TRAP_IRQ)) |->
    (mie[exc_cause] && ((priv_lvl == PRIV_LVL_M) ? (cs_registers_mstatus_q.mie && (exc_cause[10:5] == 6'b0)) : 1'b1));
  endproperty

  a_irq_enabled_0 : assert property(p_irq_enabled_0) else `uvm_error("core", "Assertion a_irq_enabled_0 failed")

  // Check that a taken IRQ was for an enabled cause and that mstatus.mie gets disabled
  property p_irq_enabled_1;
    @(posedge clk) disable iff (!rst_ni)
      (ctrl_fsm.pc_set && (ctrl_fsm.pc_mux == PC_TRAP_IRQ)) |=>
      (cs_registers_mcause_q.irq && cs_registers_mie_q[cs_registers_mcause_q.exception_code[4:0]] && !cs_registers_mstatus_q.mie);
  endproperty

  a_irq_enabled_1 : assert property(p_irq_enabled_1) else `uvm_error("core", "Assertion a_irq_enabled_1 failed")

  // Assert that no pointer can be in any pipeline stage when SMCLIC == 0
  property p_clic_noptr_in_pipeline;
    @(posedge clk) disable iff (!rst_ni)
      1'b1 |-> (!if_id_pipe.instr_meta.clic_ptr && !id_ex_pipe.instr_meta.clic_ptr && !ex_wb_pipe.instr_meta.clic_ptr);
  endproperty

  a_clic_noptr_in_pipeline : assert property(p_clic_noptr_in_pipeline) else `uvm_error("core", "CLIC pointer in pipeline when CLIC is not configured.")
end // SMCLIC

// First illegal instruction decoded
logic         first_illegal_found;
logic         first_mmode_ecall_found;
logic         first_umode_ecall_found;
logic         first_ebrk_found;
logic         first_instr_err_found;
logic         first_instr_mpuerr_found;
logic [31:0]  expected_illegal_mepc;
logic [31:0]  expected_mmode_ecall_mepc;
logic [31:0]  expected_umode_ecall_mepc;
logic [31:0]  expected_ebrk_mepc;
logic [31:0]  expected_instr_err_mepc;
logic [31:0]  expected_instr_mpuerr_mepc;

always_ff @(posedge clk , negedge rst_ni)
  begin
    if (rst_ni == 1'b0) begin
      first_illegal_found   <= 1'b0;
      first_mmode_ecall_found <= 1'b0;
      first_umode_ecall_found <= 1'b0;
      first_ebrk_found      <= 1'b0;
      first_instr_err_found <= 1'b0;
      first_instr_mpuerr_found <= 1'b0;
      expected_illegal_mepc <= 32'b0;
      expected_mmode_ecall_mepc   <= 32'b0;
      expected_umode_ecall_mepc   <= 32'b0;
      expected_ebrk_mepc    <= 32'b0;
      expected_instr_err_mepc <= 32'b0;
      expected_instr_mpuerr_mepc <= 32'b0;
    end
    else begin
      // The code below checks for first occurence of each exception type in WB
      // Multiple exceptions may occur at the same time, so the following
      // code needs to check priority of what to expect
      if (!first_illegal_found && ex_wb_pipe.instr_valid && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
        !(ex_wb_pipe.instr.bus_resp.err || (ex_wb_pipe.instr.mpu_status != MPU_OK)) &&
        !(ctrl_fsm.pc_mux == PC_TRAP_NMI) &&
          ex_wb_pipe.illegal_insn && !ctrl_debug_mode_n) begin
        first_illegal_found   <= 1'b1;
        expected_illegal_mepc <= ex_wb_pipe.pc;
      end
      if (!first_mmode_ecall_found && ex_wb_pipe.instr_valid && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
        !(ex_wb_pipe.instr.bus_resp.err || (ex_wb_pipe.instr.mpu_status != MPU_OK) || ex_wb_pipe.illegal_insn) &&
        !(ctrl_fsm.pc_mux == PC_TRAP_NMI) &&
          ex_wb_pipe.sys_en &&  ex_wb_pipe.sys_ecall_insn && !ctrl_debug_mode_n && (priv_lvl == PRIV_LVL_M)) begin
        first_mmode_ecall_found   <= 1'b1;
        expected_mmode_ecall_mepc <= ex_wb_pipe.pc;
      end
      if (!first_umode_ecall_found && ex_wb_pipe.instr_valid && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
        !(ex_wb_pipe.instr.bus_resp.err || (ex_wb_pipe.instr.mpu_status != MPU_OK) || ex_wb_pipe.illegal_insn) &&
        !(ctrl_fsm.pc_mux == PC_TRAP_NMI) &&
          ex_wb_pipe.sys_en &&  ex_wb_pipe.sys_ecall_insn && !ctrl_debug_mode_n && (priv_lvl == PRIV_LVL_U)) begin
        first_umode_ecall_found   <= 1'b1;
        expected_umode_ecall_mepc <= ex_wb_pipe.pc;
      end
      if (!first_ebrk_found && ex_wb_pipe.instr_valid && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
        !(ex_wb_pipe.instr.bus_resp.err || (ex_wb_pipe.instr.mpu_status != MPU_OK) || ex_wb_pipe.illegal_insn || (ex_wb_pipe.sys_en && ex_wb_pipe.sys_ecall_insn)) &&
        !(ctrl_fsm.pc_mux == PC_TRAP_NMI) && ex_wb_pipe.sys_en && ex_wb_pipe.sys_ebrk_insn) begin
        first_ebrk_found   <= 1'b1;
        expected_ebrk_mepc <= ex_wb_pipe.pc;
      end

      if (!first_instr_err_found && (ex_wb_pipe.instr.mpu_status == MPU_OK) && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
         !(ctrl_fsm.pc_mux == PC_TRAP_NMI) &&
          ex_wb_pipe.instr_valid && ex_wb_pipe.instr.bus_resp.err && !ctrl_debug_mode_n ) begin
        first_instr_err_found   <= 1'b1;
        expected_instr_err_mepc <= ex_wb_pipe.pc;
      end

      if (!first_instr_mpuerr_found && ex_wb_pipe.instr_valid && !irq_ack && !(ctrl_pending_debug && ctrl_debug_allowed) &&
         !(ctrl_fsm.pc_mux == PC_TRAP_NMI) &&
          (ex_wb_pipe.instr.mpu_status != MPU_OK) && !ctrl_debug_mode_n) begin
        first_instr_mpuerr_found   <= 1'b1;
        expected_instr_mpuerr_mepc <= ex_wb_pipe.pc;
      end

    end
  end

  // First mepc write for illegal instruction exception
  logic         first_cause_illegal_found;
  logic         first_cause_mmode_ecall_found;
  logic         first_cause_umode_ecall_found;
  logic         first_cause_ebrk_found;
  logic         first_cause_instr_err_found;
  logic         first_cause_instr_mpuerr_found;
  logic [31:0]  actual_illegal_mepc;
  logic [31:0]  actual_mmode_ecall_mepc;
  logic [31:0]  actual_umode_ecall_mepc;
  logic [31:0]  actual_ebrk_mepc;
  logic [31:0]  actual_instr_err_mepc;
  logic [31:0]  actual_instr_mpuerr_mepc;

  always_ff @(posedge clk , negedge rst_ni)
    begin
      if (rst_ni == 1'b0) begin
        first_cause_illegal_found <= 1'b0;
        first_cause_mmode_ecall_found   <= 1'b0;
        first_cause_umode_ecall_found   <= 1'b0;
        first_cause_ebrk_found    <= 1'b0;
        first_cause_instr_err_found <= 1'b0;
        first_cause_instr_mpuerr_found <= 1'b0;
        actual_illegal_mepc       <= 32'b0;
        actual_mmode_ecall_mepc         <= 32'b0;
        actual_umode_ecall_mepc         <= 32'b0;
        actual_ebrk_mepc          <= 32'b0;
        actual_instr_err_mepc     <= 32'b0;
        actual_instr_mpuerr_mepc  <= 32'b0;
      end
      else begin
        // Disregard saved CSR due to interrupts when chekcing exceptions
        if(!cs_registers_csr_cause_i.irq) begin
          if (!first_cause_illegal_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_ILLEGAL_INSN) && ctrl_fsm.csr_save_cause) begin
            first_cause_illegal_found <= 1'b1;
            actual_illegal_mepc       <= cs_registers_mepc_n;
          end
          if (!first_cause_mmode_ecall_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_ECALL_MMODE) && ctrl_fsm.csr_save_cause) begin
            first_cause_mmode_ecall_found <= 1'b1;
            actual_mmode_ecall_mepc       <= cs_registers_mepc_n;
          end
          if (!first_cause_umode_ecall_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_ECALL_UMODE) && ctrl_fsm.csr_save_cause) begin
            first_cause_umode_ecall_found <= 1'b1;
            actual_umode_ecall_mepc       <= cs_registers_mepc_n;
          end
          if (!first_cause_ebrk_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_BREAKPOINT) && ctrl_fsm.csr_save_cause) begin
            first_cause_ebrk_found <= 1'b1;
            actual_ebrk_mepc       <= cs_registers_mepc_n;
          end
          if (!first_cause_instr_err_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_INSTR_BUS_FAULT) && ctrl_fsm.csr_save_cause) begin
            first_cause_instr_err_found <= 1'b1;
            actual_instr_err_mepc       <= cs_registers_mepc_n;
          end
          if (!first_cause_instr_mpuerr_found && (cs_registers_csr_cause_i.exception_code == EXC_CAUSE_INSTR_FAULT) && ctrl_fsm.csr_save_cause) begin
            first_cause_instr_mpuerr_found <= 1'b1;
            actual_instr_mpuerr_mepc       <= cs_registers_mepc_n;
          end
        end
      end
    end

  // Check that mepc is updated with PC of illegal instruction
  property p_illegal_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_illegal_found && first_cause_illegal_found) |=> (expected_illegal_mepc == actual_illegal_mepc);
  endproperty

  a_illegal_mepc : assert property(p_illegal_mepc) else `uvm_error("core", "Assertion a_illegal_mepc failed")

  // Check that mepc is updated with PC of the ECALL instruction during M mode
  property p_mmode_ecall_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_mmode_ecall_found && first_cause_mmode_ecall_found) |=> (expected_mmode_ecall_mepc == actual_mmode_ecall_mepc);
  endproperty

  a_mmode_ecall_mepc : assert property(p_mmode_ecall_mepc) else `uvm_error("core", "Assertion p_ecall_mepc failed in machine mode")


  // Check that mepc is updated with PC of the ECALL instruction during U mode
  property p_umode_ecall_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_umode_ecall_found && first_cause_umode_ecall_found) |=> (expected_umode_ecall_mepc == actual_umode_ecall_mepc);
  endproperty

  a_umode_ecall_mepc : assert property(p_umode_ecall_mepc) else `uvm_error("core", "Assertion p_ecall_mepc failed in user mode")

  // Check that mepc is updated with PC of EBRK instruction
  property p_ebrk_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_ebrk_found && first_cause_ebrk_found) |=> (expected_ebrk_mepc == actual_ebrk_mepc);
  endproperty


  // Check that mepc is updated with PC of instr_err instruction
  property p_instr_err_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_instr_err_found && first_cause_instr_err_found) |=> (expected_instr_err_mepc == actual_instr_err_mepc);
  endproperty

  a_instr_err_mepc : assert property(p_instr_err_mepc) else `uvm_error("core", "Assertion a_instr_err_mepc failed")

  // Check that mepc is updated with PC of mpu_err instruction
  property p_instr_mpuerr_mepc;
    @(posedge clk) disable iff (!rst_ni)
      (first_instr_mpuerr_found && first_cause_instr_mpuerr_found) |=> (expected_instr_mpuerr_mepc == actual_instr_mpuerr_mepc);
  endproperty

  // No mpu errors will occur if the PMA is deconfigured
  generate
    if (PMA_NUM_REGIONS) begin
      a_instr_mpuerr_mepc : assert property(p_instr_mpuerr_mepc) else `uvm_error("core", "Assertion a_instr_mpuerr_mepc failed")
    end
  endgenerate

  // For checking single step, ID stage is used as it contains a 'multi_op_id_stall' signal.
  // This makes it easy to count misaligned LSU ins as one instruction instead of two.
  logic inst_taken;
  assign inst_taken = id_stage_id_valid && ex_ready && !id_stage_multi_op_id_stall;

  // Support for single step assertion
  // In case of single step + taken interrupt, the first instruction
  // of the interrupt handler must be fetched and passed down the pipeline.
  // In that case ID stage will issue two instructions in M-mode instead of one.
  logic interrupt_taken;
  always_ff @(posedge clk , negedge rst_ni)
    begin
      if (rst_ni == 1'b0) begin
        interrupt_taken <= 1'b0;
      end
      else begin
        if(irq_ack == 1'b1) begin
          interrupt_taken <= 1'b1;
        end else if(ctrl_debug_mode_n) begin
          interrupt_taken <= 1'b0;
        end
      end
    end


  // Single step without interrupts
  // Should issue exactly one instruction from ID before entering debug_mode
  a_single_step_no_irq :
    assert property (@(posedge clk) disable iff (!rst_ni || interrupt_taken)
                     (inst_taken && dcsr.step && !ctrl_fsm.debug_mode)
                     ##1 inst_taken [->1]
                     |-> (ctrl_fsm.debug_mode && dcsr.step))
      else `uvm_error("core", "Assertion a_single_step_no_irq failed")

if (SMCLIC) begin
  // Non-SHV interrupt taken during single stepping.
  // If this happens, no instructions should retire until the core is in debug mode.
  // irq_ack is asserted during FUNCTIONAL state. debug_mode_n will be set during
  // DEBUG_TAKEN one cycle later
  a_single_step_with_irq_nonshv :
    assert property (@(posedge clk) disable iff (!rst_ni)
                      (dcsr.step && !ctrl_fsm.debug_mode && irq_ack && !irq_clic_shv)
                      |->
                      !wb_valid ##1 (!wb_valid && ctrl_debug_mode_n && dcsr.step))
      else `uvm_error("core", "Assertion a_single_step_with_irq_nonshv failed")

  // An SHV CLIC interrupt will first do one fetch to get a function pointer,
  // then a second fetch to the actual interrupt handler. If this second fetch has
  // no faults, debug is entered with dpc pointing to the handler entry.
  // Otherwise, if the pointer fetch failed, we will eventually end up in debug mode
  // with dpc pointing to the respective exception/NMI handler.
  // In any way, wb_valid shall remain low until we retire the first instruction in debug mode.
  a_single_step_with_irq_shv :
    assert property (@(posedge clk) disable iff (!rst_ni)
                      (dcsr.step && !ctrl_fsm.debug_mode && irq_ack && irq_clic_shv)
                      |->
                      !wb_valid until (wb_valid && ctrl_fsm.debug_mode && dcsr.step))
      else `uvm_error("core", "Assertion a_single_step_with_irq_shv failed")


end else begin
  // Interrupt taken during single stepping.
  // If this happens, no intstructions should retire until the core is in debug mode.
  // irq_ack is asserted during FUNCTIONAL state. debug_mode_n will be set during
  // DEBUG_TAKEN one cycle later
  a_single_step_with_irq :
    assert property (@(posedge clk) disable iff (!rst_ni)
                      (dcsr.step && !ctrl_fsm.debug_mode && irq_ack)
                      |->
                      !wb_valid ##1 (!wb_valid && ctrl_debug_mode_n && dcsr.step))
      else `uvm_error("core", "Assertion a_single_step_with_irq failed")
end
  // Check that only a single instruction can retire during single step
  a_single_step_retire :
  assert property (@(posedge clk) disable iff (!rst_ni)
                    (wb_valid && last_op_wb && dcsr.step && !ctrl_fsm.debug_mode)
                    ##1 wb_valid [->1]
                    |-> (ctrl_fsm.debug_mode && dcsr.step))
    else `uvm_error("core", "Multiple instructions retired during single stepping")


  // Check priviledge level consistency accross the pipeline.
  // The only scenario where priv_lvl_if_q and priv_lvl are allowed to differ is when there's an MRET in the pipe
  // MRET in ID will immediatly update the priviledge level for the IF stage, but priv_lvl won't be updated until the MRET retires in the WB stage
  a_priv_lvl_consistency :
    assert property (@(posedge clk) disable iff (!rst_ni)
                     (priv_lvl_if_q != priv_lvl) |-> ((sys_en_id && sys_mret_insn_id) || (id_ex_pipe.sys_en && id_ex_pipe.sys_mret_insn) || (ex_wb_pipe.sys_en && ex_wb_pipe.sys_mret_insn)))
    else `uvm_error("core", "IF priviledge level not consistent with current priviledge level")

  // Assert that change to user mode only happens when and MRET is in ID and mstatus.mpp == PRIV_LVL_U
  a_priv_lvl_u_mode_mret:
    assert property (@(posedge clk) disable iff (!rst_ni)
                     $changed(priv_lvl_if) && (priv_lvl_if == PRIV_LVL_U) |->
                     ((sys_en_id && sys_mret_insn_id) && if_id_pipe.instr_valid && (cs_registers_mstatus_q.mpp == PRIV_LVL_U)))
    else `uvm_error("core", "IF priviledge level changed to user mode when there's no MRET in ID stage")

  // Helper signal. Indicate that pc_mux is set to a trap
  logic pc_mux_is_trap;
  assign pc_mux_is_trap = (ctrl_fsm.pc_mux == PC_TRAP_EXC) ||
                          (ctrl_fsm.pc_mux == PC_TRAP_IRQ) ||
                          (ctrl_fsm.pc_mux == PC_TRAP_DBD) ||
                          (ctrl_fsm.pc_mux == PC_TRAP_DBE) ||
                          (ctrl_fsm.pc_mux == PC_TRAP_NMI);

  // Assert that change to machine mode only happens upon an exception
  // If IF is killed (for instance due to a fencei), priviledege level can be restored to PRIV_LVL_M without jumping to an exception
  // ##1 is to avoid trigging the assertion in cycle 1
  a_priv_lvl_m_mode_exception:
    assert property (@(posedge clk) disable iff (!rst_ni)
                     ##1 $changed(priv_lvl_if) && (priv_lvl_if == PRIV_LVL_M) |->
                     (ctrl_fsm.pc_set && pc_mux_is_trap || ctrl_fsm.kill_if))
    else `uvm_error("core", "IF priviledge level changed to user mode when there's no MRET in ID stage")

  // Assert that all exceptions trap to machine mode, except when in debug mode (todo: revisit when debug related part of user mode is implemented)
  a_priv_lvl_exception :
    assert property (@(posedge clk) disable iff (!rst_ni)
                      (!(ctrl_fsm.debug_mode || ctrl_fsm.debug_csr_save) && ctrl_fsm.pc_set && pc_mux_is_trap)
                      |-> (priv_lvl_if == PRIV_LVL_M))
    else `uvm_error("core", "Exception not trapping to machine mode")

  // Assert that jumps to mepc is done with priviledge level from mstatus.mpp
  a_priv_lvl_mepc :
    assert property (@(posedge clk) disable iff (!rst_ni)
                      (ctrl_fsm.pc_set && (ctrl_fsm.pc_mux == PC_MRET))
                      |-> (priv_lvl_if == cs_registers_mstatus_q.mpp))
    else `uvm_error("core", "MEPC fetch not performed with priviledge level from mstatus.mpp")

  // Check that instruction fetches are always word aligned
  a_instr_addr_word_aligned :
    assert property (@(posedge clk) disable iff (!rst_ni)
                     (instr_addr_o[1:0] == 2'b00))
      else `uvm_error("core", "Instruction fetch not word aligned")

  // Check that instruction fetches are always non-bufferable
  a_instr_non_bufferable :
    assert property (@(posedge clk) disable iff (!rst_ni)
                     (!instr_memtype_o[0]))
      else `uvm_error("core", "Instruction fetch classified as bufferable")

  // Check that loads are always non-bufferable
  a_load_non_bufferable :
    assert property (@(posedge clk) disable iff (!rst_ni)
                     (data_req_o && !data_we_o |-> !data_memtype_o[0]))
      else `uvm_error("core", "Load instruction classified as bufferable")


  // There should not be any major alerts active at any time
  a_no_csr_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> !csr_err)
          else `uvm_error("core", "csr_err shall be zero.")

  a_no_ecc_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> !rf_ecc_err)
          else `uvm_error("core", "rf_ecc_err shall be zero.")

  a_no_itf_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> !itf_int_err)
          else `uvm_error("core", "itf_int_err shall be zero.")

  a_no_pc_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> !pc_err_if)
          else `uvm_error("core", "pc_err_if shall be zero.")

  // There should be no parity error on output signals
  logic instr_reqpar_expected;
  logic data_reqpar_expected;

  assign instr_reqpar_expected = !instr_req_o;
  assign data_reqpar_expected = !data_req_o;
  // Check that operand_a data forwarded from EX to ID actually is written to RF in WB
  property p_opa_fwd_ex;
    logic [31:0] opa;
    @(posedge clk) disable iff (!rst_ni)
    (id_stage_id_valid && ex_ready && (alu_op_a_mux_sel_id_i == OP_A_REGA_OR_FWD) && (ctrl_byp.operand_a_fw_mux_sel == SEL_FW_EX), opa=operand_a_id_i)
    |=> (opa == rf_wdata_wb) && (rf_we_wb || (ctrl_fsm.kill_ex || ctrl_fsm.halt_ex));
  endproperty

  a_opa_fwd_ex: assert property (p_opa_fwd_ex)
    else `uvm_error("core", "Forwarded data (operand_a) from EX not written to RF the following cycle")

  // Check that operand_a data forwarded from WB to ID actually is written to RF in WB
  property p_opa_fwd_wb;
    @(posedge clk) disable iff (!rst_ni)
    (id_stage_id_valid && ex_ready && (alu_op_a_mux_sel_id_i == OP_A_REGA_OR_FWD) && (ctrl_byp.operand_a_fw_mux_sel == SEL_FW_WB))
    |-> (operand_a_id_i == rf_wdata_wb) && rf_we_wb;
  endproperty

  a_opa_fwd_wb: assert property (p_opa_fwd_wb)
    else `uvm_error("core", "Forwarded data (operand_a) from WB not written to RF in the same cycle")

  // Check that operand_b data forwarded from EX to ID actually is written to RF in WB
  property p_opb_fwd_ex;
    logic [31:0] opb;
    @(posedge clk) disable iff (!rst_ni)
    (id_stage_id_valid && ex_ready && (alu_op_b_mux_sel_id_i == OP_B_REGB_OR_FWD) && (ctrl_byp.operand_b_fw_mux_sel == SEL_FW_EX), opb=operand_b_id_i)
    |=> (opb == rf_wdata_wb) && (rf_we_wb || (ctrl_fsm.kill_ex || ctrl_fsm.halt_ex));
  endproperty

  a_opb_fwd_ex: assert property (p_opb_fwd_ex)
    else `uvm_error("core", "Forwarded data (operand_b) from EX not written to RF the following cycle")

  // Check that operand_b data forwarded from WB to ID actually is written to RF in WB
  property p_opb_fwd_wb;
    @(posedge clk) disable iff (!rst_ni)
    (id_stage_id_valid && ex_ready && (alu_op_b_mux_sel_id_i == OP_B_REGB_OR_FWD) && (ctrl_byp.operand_b_fw_mux_sel == SEL_FW_WB))
    |-> (operand_b_id_i == rf_wdata_wb) && rf_we_wb;
  endproperty

  a_opb_fwd_wb: assert property (p_opb_fwd_wb)
    else `uvm_error("core", "Forwarded data (operand_b) from WB not written to RF in the same cycle")

  // Check that data forwarded from WB to a JALR instruction in ID is actully written to the RF
  property p_jalr_fwd;
    @(posedge clk) disable iff (!rst_ni)
    (alu_jmpr_id_i && alu_en_id_i && if_id_pipe.instr_valid) && (ctrl_byp.jalr_fw_mux_sel == SELJ_FW_WB) && !ctrl_byp.jalr_stall
    |->
    (jalr_fw_id_i == rf_wdata_wb) && (rf_we_wb || (ctrl_fsm.kill_id || ctrl_fsm.halt_id));
  endproperty

  a_jalr_fwd: assert property(p_jalr_fwd)
    else `uvm_error("core", "Forwarded jalr data from WB to ID not written to RF")

  a_no_parity_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> (instr_reqpar_o == instr_reqpar_expected) && (data_reqpar_o == data_reqpar_expected))
          else `uvm_error("core", "Parity mismatch.")

  // There should be no checksum error on output signals
  logic [11:0] instr_achk_expected;
  logic [11:0] data_achk_expected;

  assign instr_achk_expected = {
    ~^{8'b0},
    ~^{8'b0},
    ~^{8'b0},
    ~^{8'b0},
    ~^{6'b0},
    ~^{instr_dbg_o},
    ~^{4'b1111, 1'b0},
    ~^{instr_prot_o[2:0], instr_memtype_o[1:0]},
    ~^{instr_addr_o[31:24]},
    ~^{instr_addr_o[23:16]},
    ~^{instr_addr_o[15:8]},
    ~^{instr_addr_o[7:0]}
  };

  assign data_achk_expected = {
    ~^{data_wdata_o[31:24]},
    ~^{data_wdata_o[23:16]},
    ~^{data_wdata_o[15:8]},
    ~^{data_wdata_o[7:0]},
    ~^{6'b0},
    ~^{data_dbg_o},
    ~^{data_be_o[3:0], data_we_o},
    ~^{data_prot_o[2:0], data_memtype_o[1:0]},
    ~^{data_addr_o[31:24]},
    ~^{data_addr_o[23:16]},
    ~^{data_addr_o[15:8]},
    ~^{data_addr_o[7:0]}
  };

  a_no_checksum_err:
    assert property (@(posedge clk) disable iff (!rst_ni)
                    1'b1 |-> (instr_achk_o == instr_achk_expected) && (data_achk_o == data_achk_expected))
          else `uvm_error("core", "Checksum mismatch.")

// Helper logic for qualified mret_self_stall, should be the same as unqualified.
logic mret_self_stall_qual;
assign mret_self_stall_qual = ((sys_en_id && sys_mret_unqual_id_bypass && last_sec_op_id_i) && // MRET 2/2 in ID
                              ((id_ex_pipe.sys_en && id_ex_pipe.sys_mret_insn && !id_ex_pipe.last_op && id_ex_pipe.instr_valid) || // mret 1/2 in EX
                               (ex_wb_pipe.sys_en && ex_wb_pipe.sys_mret_insn && !ex_wb_pipe.last_op     && ex_wb_pipe.instr_valid))) &&  // mret 1/2 in WB
                               !(id_ex_pipe.sys_en && id_ex_pipe.sys_mret_insn && id_ex_pipe.last_op && id_ex_pipe.instr_valid);
a_mret_self_stall_qual:
  assert property (@(posedge clk) disable iff (!rst_ni)
                  1'b1 |-> (mret_self_stall_qual == mret_self_stall_bypass))
        else `uvm_error("core", "mret_self_stall mismatch.")

// Helper logic for qualified jumpr_self_stall, should be the same as unqualified.
logic jumpr_self_stall_qual;
assign jumpr_self_stall_qual = (alu_en_id_i && jmpr_unqual_id_bypass && last_sec_op_id_i) &&
                              ((id_ex_pipe.alu_jmp && id_ex_pipe.alu_en && !id_ex_pipe.last_op && id_ex_pipe.instr_valid));

a_jumpr_self_stall_qual:
  assert property (@(posedge clk) disable iff (!rst_ni)
                  1'b1 |-> (jumpr_self_stall_qual == jumpr_self_stall_bypass))
        else `uvm_error("core", "jumpr_self_stall mismatch.")



  // Check that a table jump in ID is stalled when a CSR is written in EX or WB (could be JVT being written)
  property p_tbljmp_stall;
    @(posedge clk) disable iff (!rst_ni)
    (id_ex_pipe.instr_valid && id_ex_pipe.csr_en) ||
    (ex_wb_pipe.instr_valid && ex_wb_pipe.csr_en)
    |->
    !ctrl_fsm.pc_set_tbljmp;
  endproperty;

  a_tbljmp_stall: assert property(p_tbljmp_stall)
    else `uvm_error("core", "Table jump not stalled while CSR is written");

endmodule

