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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Robert Balas - balasr@iis.ee.ethz.ch                       //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40s_controller_bypass                                 //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Bypass logic, hazard detection and stall control           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_controller_bypass import cv32e40s_pkg::*;
#(
  parameter int unsigned REGFILE_NUM_READ_PORTS = 2
)
(
  // From decoder
  input  logic [REGFILE_NUM_READ_PORTS-1:0]     rf_re_id_i, // Read enables from decoder
  input rf_addr_t     rf_raddr_id_i[REGFILE_NUM_READ_PORTS],// Read addresses from decoder

  // Pipeline registers
  input if_id_pipe_t  if_id_pipe_i,
  input id_ex_pipe_t  id_ex_pipe_i,
  input ex_wb_pipe_t  ex_wb_pipe_i,

  // From ID
  input  logic        alu_jmpr_id_i,              // ALU jump register (JALR)
  input  logic        sys_mret_id_i,              // mret in ID
  input  logic        csr_en_raw_id_i,            // CSR in ID (not gated with deassert)
  input  csr_opcode_e csr_op_id_i,                // CSR opcode (ID) // todo: Not used (is this on purpose or should it be used here?)
  input  logic        sys_wfi_id_i,               // WFI instruction in ID
  input  logic        last_sec_op_id_i,

  // From EX
  input  logic        csr_counter_read_i,         // CSR is reading a counter (EX).
  input  logic        csr_mnxti_read_i,           // CSR is reading mnxti (EX)

  // From WB
  input  logic        wb_ready_i,                 // WB stage is ready
  input  logic        csr_irq_enable_write_i,     // WB is writing to a CSR that may enable an interrupt.

  // Controller Bypass outputs
  output ctrl_byp_t   ctrl_byp_o
);

  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_match;            // Register file address match (ID vs. EX). Not qualified with rf_we_ex yet.
  logic                              rf_rd_ex_jalr_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_match;            // Register file address match (ID vs. WB). Not qualified with rf_we_wb yet.
  logic                              rf_rd_wb_jalr_match;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_hz;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_hz;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_ex_hz_en;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_rd_wb_hz_en;

  logic                              csr_write_in_ex_wb;        // Detect CSR write in EX or WB (implicit and explicit)

  logic                              rf_we_ex;                  // EX register file write enable
  logic                              rf_we_wb;                  // WB register file write enable
  logic                              lsu_en_wb;                 // WB lsu_en

  rf_addr_t                          rf_waddr_ex;               // EX rf_waddr
  rf_addr_t                          rf_waddr_wb;               // WB rf_waddr

  // Detect if a SECURE mret would stall on itself
  logic mret_self_stall;

  // Detect if a jumpr would stall on itself
  logic jumpr_self_stall;

  logic                              sys_mret_unqual_id;        // MRET in ID (not qualified with sys_en)
  logic                              csr_exp_unqual_id;         // Explicit CSR in ID (not qualified with csr_en)
  logic                              csr_unqual_id;             // Explicit or implicit CSR in ID (not qualified)
  logic                              jmpr_unqual_id;            // JALR in ID (not qualified with alu_en)
  logic                              sys_wfi_unqual_id;         // WFI in ID (not qualified with sys_en)
  logic                              tbljmp_unqual_id;          // Table jump in ID (not qualified with alu_en)

  // Dummy or hint instructions in stages
  logic                              dummy_hint_id;
  logic                              dummy_hint_ex;
  logic                              dummy_hint_wb;



  // todo: make all qualifiers here, and use those signals later in the file

  assign rf_we_ex = id_ex_pipe_i.rf_we && id_ex_pipe_i.instr_valid;
  assign rf_we_wb = ex_wb_pipe_i.rf_we && ex_wb_pipe_i.instr_valid;
  assign lsu_en_wb = ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid;

  assign rf_waddr_ex = id_ex_pipe_i.rf_waddr;
  assign rf_waddr_wb = ex_wb_pipe_i.rf_waddr; // TODO: If XIF OoO is allowed, we need to look at WB stage outputs instead

  // The following unqualified signals are such that they can have a false positive (but no false negative).
  //
  // There are two reasons why these signals are considered unqualified:
  // - The corresponding _en signal is not used
  // - A raw _en signal is used (i.e. deassert_we is ignored)
  //
  // This can lead to stall cycles (via jalr_stall or csr_stall) when they should not actually be needed.
  // Such cases are however rare as the difference between qualified and unqualified signals will only
  // occur in case that deassert_we = 1. Permanent stalls are avoided because the EX, WB stages will
  // eventually empty out removing that reasons for stall conditions.

  assign sys_mret_unqual_id = sys_mret_id_i && if_id_pipe_i.instr_valid;
  assign csr_exp_unqual_id = csr_en_raw_id_i && if_id_pipe_i.instr_valid;
  assign jmpr_unqual_id = alu_jmpr_id_i && if_id_pipe_i.instr_valid;
  assign sys_wfi_unqual_id = sys_wfi_id_i && if_id_pipe_i.instr_valid;
  assign tbljmp_unqual_id = if_id_pipe_i.instr_meta.tbljmp && if_id_pipe_i.instr_valid;

  assign csr_unqual_id = csr_exp_unqual_id || sys_mret_unqual_id || sys_wfi_unqual_id || tbljmp_unqual_id;

  assign dummy_hint_id = if_id_pipe_i.instr_valid && (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint);
  assign dummy_hint_ex = id_ex_pipe_i.instr_valid && (id_ex_pipe_i.instr_meta.dummy || id_ex_pipe_i.instr_meta.hint);
  assign dummy_hint_wb = ex_wb_pipe_i.instr_valid && (ex_wb_pipe_i.instr_meta.dummy || ex_wb_pipe_i.instr_meta.hint);


  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////

  //TODO:OK:low This CSR stall check is very restrictive
  //         Should only check EX vs WB, and also CSR/rd addr
  //         Also consider whether ID or EX should be stalled
  // The controller mechanism for checking mcause.mpp/mcause.minhv when an mret is in the ID stage depends on this stall.
  // Detect when a CSR insn is in ID (including WFI which reads mstatus.tw and priv level)
  // Note that hazard detection uses the registered instr_valid signals. Usage of the local
  // instr_valid signals would lead to a combinatorial loop via the halt signal.

  // todo:low:Above loop reasoning only applies to halt_id; for other pipeline stages a local instr_valid signal can maybe be used.

  // Detect when a CSR insn  in in EX or WB
  // mret and dret implicitly writes to CSR. (dret is killing IF/ID/EX once it is in WB and can be disregarded here.

  assign csr_write_in_ex_wb = (
                              (id_ex_pipe_i.instr_valid && (id_ex_pipe_i.csr_en || (id_ex_pipe_i.sys_en && id_ex_pipe_i.sys_mret_insn))) ||
                              (ex_wb_pipe_i.instr_valid && (ex_wb_pipe_i.csr_en || (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_mret_insn)))
                              );

  // Detect if a secure mret has its last phase (2/2) in ID while the first is in EX or WB.
  // Used to avoid csr_stall in the case where an mret would stall on itself.
  // Using unqualified sys_mret_unqual_id and qualified sys_en/sys_mret_insn from EX and WB.
  // Using qualified or unqualified from ID does not matter for the value of the self_stall (assert in core_sva).
  // ctrl_byp_o.deassert_we needs to be 1 for the sys_en to be deasserted, and this cannot
  // happen for the last part (ID) if it didn't already happen to the first part (EX or WB).
  //
  // Last line excludes setting the self stall signal in case a last part of an mret is in EX stage.
  // - Last part of mret in EX means any mret in ID must a different mret instruction.
  // - This mret must then be flagged as faulted (deassert_we=1) for it to have last_sec_op_id_i set. Any csr_stall will then be active, although
  // - the instruction will not do any side effects and eventually take an exception when it reaches WB.
  assign mret_self_stall = ((sys_mret_unqual_id && last_sec_op_id_i) && // MRET 2/2 in ID
                           ((id_ex_pipe_i.sys_en && id_ex_pipe_i.sys_mret_insn && !id_ex_pipe_i.last_op && id_ex_pipe_i.instr_valid) ||    // mret 1/2 in EX
                            (ex_wb_pipe_i.sys_en && ex_wb_pipe_i.sys_mret_insn && !ex_wb_pipe_i.last_op && ex_wb_pipe_i.instr_valid))) &&  // mret 1/2 in WB
                            !(id_ex_pipe_i.sys_en && id_ex_pipe_i.sys_mret_insn && id_ex_pipe_i.last_op && id_ex_pipe_i.instr_valid);


  // Detect if a jumpr instruction is stalling on itself (Can only happen if the last part is in ID and the first in EX)
  // Any stall due to first part being in WB would be allowed to forward to ID.
  // ctrl_byp_o.deassert_we needs to be 1 for the alu_en to be deasserted, and this cannot
  // happen for the last part (ID) if it didn't already happen to the first part (EX or WB).
  // Using unqualified or qualified jumpr get the same result. (Assert in core_sva)
  assign jumpr_self_stall = (jmpr_unqual_id && last_sec_op_id_i) &&
                            ((id_ex_pipe_i.alu_jmp && id_ex_pipe_i.alu_en && !id_ex_pipe_i.last_op && id_ex_pipe_i.instr_valid));


  // Stall ID when WFI or WFE is active in EX.
  // Prevent load/store following a WFI or WFE in the pipeline
  assign ctrl_byp_o.wfi_wfe_stall = (id_ex_pipe_i.sys_en && (id_ex_pipe_i.sys_wfi_insn || id_ex_pipe_i.sys_wfe_insn) && id_ex_pipe_i.instr_valid);

  // Stall ID when mnxti CSR is accessed in EX
  // This is needed because the data bypass from EX uses csr_rdata, and for mnxti this is actually mstatus and not the result
  // that will be written to the register file. Could be optimized to only stall when the result from the CSR instruction is used in ID,
  // but the common usecase is a CSR access followed by a branch using the mnxti result in the RF, so it would likely stall in most cases anyway.
  assign ctrl_byp_o.mnxti_id_stall = csr_mnxti_read_i;

  // Stall EX stage when an mnxti is in EX and an LSU instruction is in WB.
  // This is needed to make sure that any external interrupt clearing (due to a LSU instruction) gets picked
  // up correctly by the mnxti access.
  assign ctrl_byp_o.mnxti_ex_stall = csr_mnxti_read_i && (ex_wb_pipe_i.lsu_en && ex_wb_pipe_i.instr_valid);

  genvar i;
  generate
    for(i=0; i<REGFILE_NUM_READ_PORTS; i++) begin : gen_forward_signals
      // For dummies/hints x0 exist in flops, non-dummies/hints have their writes to x0 ignored and reads as zero.
      // Exclude x0 from hazard detection for
      //   - Regular non-dommy/hint instructions
      //   - Dummy/hint instructions reading in ID while non-dummies/hints are writing in EX or WB
      // Include x0 in hazard detection for dummies/hints which read in ID while dummies/hints are also writing in EX or WB
      assign rf_rd_ex_hz_en[i] = !dummy_hint_id ? |rf_raddr_id_i[i] : |rf_raddr_id_i[i] || dummy_hint_ex;
      assign rf_rd_wb_hz_en[i] = !dummy_hint_id ? |rf_raddr_id_i[i] : |rf_raddr_id_i[i] || dummy_hint_wb;

      // Does register file read address match write address in EX (excluding R0 for regular instructions)?
      assign rf_rd_ex_match[i] = (rf_waddr_ex == rf_raddr_id_i[i]) && rf_rd_ex_hz_en[i] && rf_re_id_i[i];

      // Does register file read address match write address in WB (excluding R0 for regular instructions)?
      assign rf_rd_wb_match[i] = (rf_waddr_wb == rf_raddr_id_i[i]) && rf_rd_wb_hz_en[i] && rf_re_id_i[i];

      // Load-read hazard (for any instruction following a load)
      assign rf_rd_ex_hz[i] = rf_rd_ex_match[i];
      assign rf_rd_wb_hz[i] = rf_rd_wb_match[i];
    end
  endgenerate

  // JALR rs1 match (rf_re_id_i[0] implied by JALR).
  // Not qualified yet with JALR instruction nor with read enable (implied by JALR)
  assign rf_rd_ex_jalr_match = (rf_waddr_ex == rf_raddr_id_i[0]) && |rf_raddr_id_i[0];
  assign rf_rd_wb_jalr_match = (rf_waddr_wb == rf_raddr_id_i[0]) && |rf_raddr_id_i[0];

  always_comb
  begin
    ctrl_byp_o.load_stall          = 1'b0;
    ctrl_byp_o.deassert_we         = 1'b0;
    ctrl_byp_o.csr_stall           = 1'b0;
    ctrl_byp_o.minstret_stall      = 1'b0;
    ctrl_byp_o.irq_enable_stall    = 1'b0;

    // deassert WE when the core has an exception in ID (ins converted to nop and propagated to WB)
    // Also deassert for trigger match, as with dcsr.timing==0 we do not execute before entering debug mode
    // CLIC pointer fetches go through the pipeline, but no write enables should be active.
    if (if_id_pipe_i.instr.bus_resp.err || !(if_id_pipe_i.instr.mpu_status == MPU_OK) || if_id_pipe_i.trigger_match ||
        if_id_pipe_i.instr_meta.clic_ptr || if_id_pipe_i.instr.bus_resp.integrity_err) begin
      ctrl_byp_o.deassert_we = 1'b1;
    end

    // Stall because of load or XIF operation
    if (
        ((id_ex_pipe_i.lsu_en || id_ex_pipe_i.xif_en) && rf_we_ex && |rf_rd_ex_hz) || // load-use hazard (EX)
        (!wb_ready_i                                  && rf_we_wb && |rf_rd_wb_hz)    // load-use hazard (WB during wait-state)
       )
    begin
      ctrl_byp_o.load_stall  = 1'b1;
    end

    // Stall because of jalr path. Stall if a result is to be forwarded to the PC except if result from WB is an ALU result.
    // No need to deassert anything in ID as ID stage is stalled anyway. JALR implies rf_re_id_i[0].
    // Also stalling when a CSR access to MNXTI is in WB. This is because the jalr forward uses the ex_wb_pipe.rf_wdata as data,
    // and forwarding the CSR result (pointer address for mnxti) would need the forward mux to also include the pointer address from cs_registers.
    // Cannot use wb_stage.rf_wdata_o due to the timing path from the data OBI.
    if (jmpr_unqual_id &&
         ((rf_we_wb && rf_rd_wb_jalr_match && lsu_en_wb) ||
          (rf_we_wb && rf_rd_wb_jalr_match && (ex_wb_pipe_i.csr_mnxti_access && ex_wb_pipe_i.csr_en)) ||
          (rf_we_ex && rf_rd_ex_jalr_match)) && !jumpr_self_stall) begin
      ctrl_byp_o.jalr_stall = 1'b1;
    end else begin
      ctrl_byp_o.jalr_stall = 1'b0;
    end

    // Stall because of CSR read (direct or implied) in ID while CSR (implied or direct) is written in EX/WB
    if (csr_unqual_id && csr_write_in_ex_wb && !mret_self_stall) begin
      ctrl_byp_o.csr_stall = 1'b1;
    end

    // Stall (EX) due to performance counter read
    // csr_counter_read_i is derived from csr_raddr, which is gated with id_ex_pipe.csr_en and id_ex_pipe.instr_valid
    if (csr_counter_read_i && ex_wb_pipe_i.instr_valid) begin
      ctrl_byp_o.minstret_stall = 1'b1;
    end

    // Stall EX when an interrupt may be enabled from WB while there is a LSU instruction in EX.
    if (csr_irq_enable_write_i && (id_ex_pipe_i.instr_valid && id_ex_pipe_i.lsu_en)) begin
      ctrl_byp_o.irq_enable_stall = 1'b1;
    end
  end

  assign ctrl_byp_o.id_stage_abort = ctrl_byp_o.deassert_we;

  // Forwarding control unit
  always_comb
  begin
    // default assignements
    ctrl_byp_o.operand_a_fw_mux_sel = SEL_REGFILE;
    ctrl_byp_o.operand_b_fw_mux_sel = SEL_REGFILE;
    ctrl_byp_o.jalr_fw_mux_sel      = SELJ_REGFILE;

    // Forwarding WB -> ID
    if (rf_we_wb) begin
      if (rf_rd_wb_match[0]) begin
        ctrl_byp_o.operand_a_fw_mux_sel = SEL_FW_WB;
      end
      if (rf_rd_wb_match[1]) begin
        ctrl_byp_o.operand_b_fw_mux_sel = SEL_FW_WB;
      end
    end

    // Forwarding EX -> ID (not actually used when there is a load in EX)
    if (rf_we_ex) begin
      if (rf_rd_ex_match[0]) begin
        ctrl_byp_o.operand_a_fw_mux_sel = SEL_FW_EX;
      end
      if (rf_rd_ex_match[1]) begin
        ctrl_byp_o.operand_b_fw_mux_sel = SEL_FW_EX;
      end
    end

    // Forwarding WB->ID for the jump register path
    // Only used if WB is writing back an ALU result. No forwarding for load result because of timing reasons.
    // Non qualified rf_rd_wb_jalr_match is used as it is a don't care if jmpr_unqual_id = 0 or jalr_stall = 1.
    if (rf_we_wb) begin
      if (rf_rd_wb_jalr_match) begin
        ctrl_byp_o.jalr_fw_mux_sel = SELJ_FW_WB;
      end
    end

    if (if_id_pipe_i.instr_meta.dummy || if_id_pipe_i.instr_meta.hint) begin
      // Overriding operands with data from LFSRs for dummy and hint instructions, except for reads from R0
      if (rf_raddr_id_i[0] != '0) begin
        ctrl_byp_o.operand_a_fw_mux_sel = SEL_LFSR;
      end

      if (rf_raddr_id_i[1] != '0) begin
        ctrl_byp_o.operand_b_fw_mux_sel = SEL_LFSR;
      end
    end

  end // always_comb

  // Stall EX if offloaded instruction in WB may trigger an exception
  assign ctrl_byp_o.xif_exception_stall = ex_wb_pipe_i.xif_en && ex_wb_pipe_i.xif_meta.exception && ex_wb_pipe_i.instr_valid;

endmodule
