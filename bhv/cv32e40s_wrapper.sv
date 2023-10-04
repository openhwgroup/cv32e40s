// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a cv32e40s, containing cv32e40s and RVFI
// Contributors: Davide Schiavone <davide@openhwgroup.org>
//               Halfdan Bechmann <halfdan.behcmann@silabs.com>

`ifndef COREV_ASSERT_OFF
  `include "cv32e40s_alignment_buffer_sva.sv"
  `include "cv32e40s_controller_fsm_sva.sv"
  `include "cv32e40s_core_sva.sv"
  `include "cv32e40s_cs_registers_sva.sv"
  `include "cv32e40s_decoder_sva.sv"
  `include "cv32e40s_div_sva.sv"
  `include "cv32e40s_register_file_sva.sv"
  `include "cv32e40s_dummy_instr_sva.sv"
  `include "cv32e40s_if_stage_sva.sv"
  `include "cv32e40s_id_stage_sva.sv"
  `include "cv32e40s_ex_stage_sva.sv"
  `include "cv32e40s_wb_stage_sva.sv"
  `include "cv32e40s_load_store_unit_sva.sv"
  `include "cv32e40s_write_buffer_sva.sv"
  `include "cv32e40s_lsu_response_filter_sva.sv"
  `include "cv32e40s_mpu_sva.sv"
  `include "cv32e40s_mult_sva.sv"
  `include "cv32e40s_prefetcher_sva.sv"
  `include "cv32e40s_prefetch_unit_sva.sv"
  `include "cv32e40s_sleep_unit_sva.sv"
  `include "cv32e40s_rvfi_sva.sv"
  `include "cv32e40s_pc_check_sva.sv"
  `include "cv32e40s_sequencer_sva.sv"
  `include "cv32e40s_clic_int_controller_sva.sv"
  `include "cv32e40s_instr_obi_interface_sva.sv"
  `include "cv32e40s_data_obi_interface_sva.sv"
  `include "cv32e40s_wpt_sva.sv"
  `include "cv32e40s_debug_triggers_sva.sv"
  `include "cv32e40s_parameter_sva.sv"
`endif

`include "cv32e40s_wrapper.vh"
`include "cv32e40s_core_log.sv"
`include "cv32e40s_dbg_helper.sv"

`ifdef RISCV_FORMAL
  `include "rvfi_macros.vh"
`endif

module cv32e40s_wrapper
  import cv32e40s_pkg::*;
#(
  parameter              LIB                          = 0,
  parameter rv32_e       RV32                         = RV32I,
  parameter b_ext_e      B_EXT                        = B_NONE,
  parameter m_ext_e      M_EXT                        = M,
  parameter int unsigned PMP_GRANULARITY              = 0,
  parameter int          PMP_NUM_REGIONS              = 0,
  parameter pmpncfg_t    PMP_PMPNCFG_RV[PMP_NUM_REGIONS-1:0] = '{default:PMPNCFG_DEFAULT},
  parameter [31:0]       PMP_PMPADDR_RV[PMP_NUM_REGIONS-1:0] = '{default:32'h0},
  parameter mseccfg_t    PMP_MSECCFG_RV                      = MSECCFG_DEFAULT,
  parameter bit          CLIC                         = 0,
  parameter int unsigned CLIC_ID_WIDTH                = 5,
  parameter int          DBG_NUM_TRIGGERS             = 1,
  parameter int          PMA_NUM_REGIONS              = 0,
  parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT},
  parameter lfsr_cfg_t   LFSR0_CFG                    = LFSR_CFG_DEFAULT, // Do not use default value for LFSR configuration
  parameter lfsr_cfg_t   LFSR1_CFG                    = LFSR_CFG_DEFAULT, // Do not use default value for LFSR configuration
  parameter lfsr_cfg_t   LFSR2_CFG                    = LFSR_CFG_DEFAULT, // Do not use default value for LFSR configuration
  parameter bit          CORE_LOG_ENABLE              = 1,
  parameter bit          DEBUG                        = 1,
  parameter logic [31:0] DM_REGION_START              = 32'hF0000000,
  parameter logic [31:0] DM_REGION_END                = 32'hF0003FFF
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        scan_cg_en_i,                     // Enable all clock gates for testing

  // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [31:0] mtvec_addr_i,
  input  logic [31:0] dm_halt_addr_i,
  input  logic [31:0] mhartid_i,
  input  logic  [3:0] mimpid_patch_i,
  input  logic [31:0] dm_exception_addr_i,

  // Instruction memory interface
  output logic        instr_req_o,
  output logic        instr_reqpar_o,
  input  logic        instr_gnt_i,
  input  logic        instr_gntpar_i,
  input  logic        instr_rvalid_i,
  input  logic        instr_rvalidpar_i,
  output logic [31:0] instr_addr_o,
  output logic [12:0] instr_achk_o,
  output logic [1:0]  instr_memtype_o,
  output logic [2:0]  instr_prot_o,
  output logic        instr_dbg_o,
  input  logic [31:0] instr_rdata_i,
  input  logic [4:0]  instr_rchk_i,
  input  logic        instr_err_i,

  // Data memory interface
  output logic        data_req_o,
  output logic        data_reqpar_o,
  input  logic        data_gnt_i,
  input  logic        data_gntpar_i,
  input  logic        data_rvalid_i,
  input  logic        data_rvalidpar_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [12:0] data_achk_o,
  output logic [1:0]  data_memtype_o,
  output logic [2:0]  data_prot_o,
  output logic        data_dbg_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic [4:0]  data_rchk_i,
  input  logic        data_err_i,

  // Cycle Count
  output logic [63:0] mcycle_o,

  // Interrupt inputs
  input  logic [31:0] irq_i,                    // CLINT interrupts + CLINT extension interrupts

  // WFE input
  input  logic        wu_wfe_i,

  // CLIC Interface
  input  logic                       clic_irq_i,
  input  logic [CLIC_ID_WIDTH-1:0]   clic_irq_id_i,
  input  logic [ 7:0]                clic_irq_level_i,
  input  logic [ 1:0]                clic_irq_priv_i,
  input  logic                       clic_irq_shv_i,

  // Fencei flush handshake
  output logic        fencei_flush_req_o,
  input  logic        fencei_flush_ack_i,

  // Security Alerts
  output logic        alert_minor_o,
  output logic        alert_major_o,

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_havereset_o,
  output logic        debug_running_o,
  output logic        debug_halted_o,
  output logic        debug_pc_valid_o,
  output logic [31:0] debug_pc_o,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_sleep_o

`ifdef RISCV_FORMAL
  ,`RVFI_OUTPUTS
`endif
);


`ifndef COREV_ASSERT_OFF
  // Localparam to avoid hierarchical bind to localparam within cs_registers.sva
  localparam PMP_ADDR_WIDTH = (PMP_GRANULARITY > 0) ? 33 - PMP_GRANULARITY : 32;

  // RTL Assertions

  bind cv32e40s_core: core_i cv32e40s_parameter_sva
    #(
      .PMA_NUM_REGIONS (PMA_NUM_REGIONS ),
      .PMA_CFG         (PMA_CFG         ),
      .DM_REGION_START (DM_REGION_START ),
      .DM_REGION_END   (DM_REGION_END   ),
      .DBG_NUM_TRIGGERS(DBG_NUM_TRIGGERS),
      .CLIC_ID_WIDTH   (CLIC_ID_WIDTH   ),
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS),
      .PMP_NUM_REGIONS (PMP_NUM_REGIONS ),
      .PMP_PMPNCFG_RV  (PMP_PMPNCFG_RV  ),
      .PMP_MSECCFG_RV  (PMP_MSECCFG_RV  ),
      .PMP_GRANULARITY (PMP_GRANULARITY ),
      .LFSR0_CFG       (LFSR0_CFG       ),
      .LFSR1_CFG       (LFSR1_CFG       ),
      .LFSR2_CFG       (LFSR2_CFG       )
      )
  param_sva(.*);


  bind cv32e40s_if_stage:
    core_i.if_stage_i cv32e40s_if_stage_sva #(.CLIC(CLIC)) if_stage_sva
    (
      .m_c_obi_instr_if (core_i.m_c_obi_instr_if), // SVA monitor modport cannot connect to a master modport
      .*
    );

  bind cv32e40s_pc_check:
    core_i.if_stage_i.pc_check_i cv32e40s_pc_check_sva pc_check_sva
    (
      .*
    );

  bind cv32e40s_register_file:
    core_i.register_file_wrapper_i.register_file_i cv32e40s_register_file_sva
      #(.REGFILE_NUM_READ_PORTS (REGFILE_NUM_READ_PORTS),
        .REGFILE_NUM_WORDS(core_i.register_file_wrapper_i.register_file_i.REGFILE_NUM_WORDS),
        .RV32(RV32)) register_file_sva (.*);

  generate
    if (SECURE) begin
      bind cv32e40s_dummy_instr :
        core_i.if_stage_i.gen_dummy_instr.dummy_instr_i cv32e40s_dummy_instr_sva
      dummy_instr_sva
    (
      .if_valid_i ( core_i.if_valid                   ),
      .id_ready_i ( core_i.id_ready                   ),
      .hint_if_i  ( core_i.if_stage_i.instr_hint      ),
      .*
    );
    end
  endgenerate

  bind cv32e40s_id_stage:
    core_i.id_stage_i cv32e40s_id_stage_sva #(.RV32(RV32)) id_stage_sva
    (
      .ex_wb_pipe             (core_i.ex_wb_pipe                                  ),
      .jmp_taken_id_ctrl_i    (core_i.controller_i.controller_fsm_i.jump_taken_id ),
      .*
    );

  bind cv32e40s_ex_stage:
    core_i.ex_stage_i cv32e40s_ex_stage_sva ex_stage_sva
    (
      .branch_taken_ex_ctrl_i (core_i.controller_i.controller_fsm_i.branch_taken_ex ),
      .ctrl_flush_ack_n       (core_i.controller_i.controller_fsm_i.csr_flush_ack_n ),
      .wb_valid_i             (core_i.wb_valid                                      ),
      .*
    );

  bind cv32e40s_wb_stage:
    core_i.wb_stage_i cv32e40s_wb_stage_sva #(.DEBUG(DEBUG)) wb_stage_sva
    (
      .*
    );

  bind cv32e40s_id_stage:
    core_i.id_stage_i
    cv32e40s_dbg_helper
      dbg_help_i(.is_compressed (if_id_pipe_i.instr_meta.compressed),
                 .rf_re         (core_i.rf_re_id                   ),
                 .rf_raddr      (core_i.rf_raddr_id                ),
                 .rf_we         (core_i.id_stage_i.rf_we           ),
                 .rf_waddr      (core_i.id_stage_i.rf_waddr        ),
                 .illegal_insn  (core_i.id_stage_i.illegal_insn    ),
                 .*);

  generate
    if(M_EXT != M_NONE) begin: mul_sva
      bind cv32e40s_mult:
        core_i.ex_stage_i.mul.mult_i cv32e40s_mult_sva mult_sva (.*);
    end
  endgenerate

  bind cv32e40s_controller_fsm:
    core_i.controller_i.controller_fsm_i
      cv32e40s_controller_fsm_sva
        #(.DEBUG(DEBUG),
          .CLIC(CLIC),
          .CLIC_ID_WIDTH(CLIC_ID_WIDTH),
          .RV32(RV32))
        controller_fsm_sva   (
                              .lsu_outstanding_cnt (core_i.load_store_unit_i.cnt_q),
                              .rf_we_wb_i          (core_i.wb_stage_i.rf_we_wb_o  ),
                              .csr_we_i            (core_i.cs_registers_i.csr_we_int  ),
                              .mstatus_i           (core_i.mstatus),
                              .priv_lvl_i          (core_i.priv_lvl),
                              .priv_lvl_n          (core_i.cs_registers_i.priv_lvl_n),
                              .sys_en_id_i         (core_i.id_stage_i.sys_en),
                              .sys_wfi_insn_id_i   (core_i.id_stage_i.sys_wfi_insn),
                              .sys_wfe_insn_id_i   (core_i.id_stage_i.sys_wfe_insn),
                              .sys_mret_insn_id_i  (core_i.id_stage_i.sys_mret_insn),
                              .id_valid_i          (core_i.id_stage_i.id_valid_o),
                              .csr_illegal_i       (core_i.cs_registers_i.csr_illegal_o),

                              .last_sec_op_id_i    (core_i.controller_i.last_sec_op_id_i),
                              .lsu_trans_valid     (core_i.load_store_unit_i.trans_valid),
                              .last_op_id_i        (core_i.id_stage_i.last_op_o),
                              .first_op_if_i                (core_i.if_stage_i.first_op),
                              .first_op_ex_i                (core_i.ex_stage_i.first_op),
                              .prefetch_valid_if_i          (core_i.if_stage_i.prefetch_valid),
                              .prefetch_is_tbljmp_ptr_if_i  (core_i.if_stage_i.prefetch_is_tbljmp_ptr),
                              .prefetch_is_mret_ptr_if_i    (core_i.if_stage_i.prefetch_is_mret_ptr),
                              .prefetch_is_clic_ptr_if_i    (core_i.if_stage_i.prefetch_is_clic_ptr),
                              .lsu_trans_valid_i            (core_i.load_store_unit_i.trans_valid),
                              .csr_en_id_i                  (core_i.id_stage_i.csr_en),
                              .ptr_in_if_i                  (core_i.if_stage_i.ptr_in_if_o),
                              .instr_req_o                  (core_i.instr_req_o),
                              .instr_dbg_o                  (core_i.instr_dbg_o),
                              .rf_mem_i                     (core_i.register_file_wrapper_i.register_file_i.mem),
                              .alu_jmpr_id_i                (core_i.alu_jmpr_id),
                              .jalr_fw_id_i                 (core_i.id_stage_i.jalr_fw),
                              .response_filter_bus_cnt_q_i  (core_i.load_store_unit_i.response_filter_i.bus_cnt_q),
                              .*);
  bind cv32e40s_cs_registers:
    core_i.cs_registers_i
      cv32e40s_cs_registers_sva
        #(.CLIC  (CLIC),
          .DEBUG (DEBUG),
          .PMP_ADDR_WIDTH (PMP_ADDR_WIDTH))
        cs_registers_sva (.wb_valid_i  (core_i.wb_valid                                 ),
                          .ctrl_fsm_cs (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                          .*);


  bind cv32e40s_load_store_unit:
    core_i.load_store_unit_i cv32e40s_load_store_unit_sva #(.DEPTH (DEPTH), .DEBUG(DEBUG)) load_store_unit_sva (
      // The SVA's monitor modport can't connect to a master modport, so it is connected to the interface instance directly:
      .m_c_obi_data_if(core_i.m_c_obi_data_if),
      .ex_wb_pipe_i   (core_i.ex_wb_pipe),
      .write_buffer_state_i (core_i.load_store_unit_i.write_buffer_i.state),
      .id_valid       (core_i.id_valid),
      .ex_ready       (core_i.ex_ready),
      .lsu_en_id      (core_i.id_stage_i.lsu_en),
      .ctrl_fsm_cs    (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
      .ctrl_fsm_ns    (core_i.controller_i.controller_fsm_i.ctrl_fsm_ns),
      .*);

  generate
    if (DBG_NUM_TRIGGERS > 0) begin : debug_sva
      bind cv32e40s_wpt:
        core_i.load_store_unit_i.gen_wpt.wpt_i
          cv32e40s_wpt_sva wpt_sva(
            .mpu_state (core_i.load_store_unit_i.mpu_i.state_q),
            .*);

      bind cv32e40s_debug_triggers:
        core_i.cs_registers_i.debug_triggers_i
          cv32e40s_debug_triggers_sva
            #(.DBG_NUM_TRIGGERS(DBG_NUM_TRIGGERS))
            debug_triggers_sva (.csr_wdata     (core_i.cs_registers_i.csr_wdata),
                                .csr_waddr     (core_i.cs_registers_i.csr_waddr),
                                .csr_op        (core_i.cs_registers_i.csr_op),
                                .ex_wb_pipe_i  (core_i.ex_wb_pipe),
                                .tselect_q     (core_i.cs_registers_i.debug_triggers_i.gen_triggers.tselect_q),
                                .tdata1_q      (core_i.cs_registers_i.debug_triggers_i.gen_triggers.tdata1_q),
                                .tdata2_q      (core_i.cs_registers_i.debug_triggers_i.gen_triggers.tdata2_q),
                                .trigger_match_if_wb (core_i.ex_wb_pipe.trigger_match),
                                .trigger_match_ex_wb (core_i.wpt_match_wb),
                                .wb_valid_i          (core_i.wb_valid),
                                .*);
    end
  endgenerate

  bind cv32e40s_prefetch_unit:
    core_i.if_stage_i.prefetch_unit_i
      cv32e40s_prefetch_unit_sva
      #(.CLIC(CLIC))
      prefetch_unit_sva (
                          .ctrl_fsm_cs     (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                          .debug_req_i     (core_i.debug_req_i),
                          .*);

  generate
    if(M_EXT == M) begin: div_sva
      bind cv32e40s_div:
        core_i.ex_stage_i.div.div_i cv32e40s_div_sva div_sva (.*);
    end
  endgenerate

  bind cv32e40s_alignment_buffer:
    core_i.if_stage_i.prefetch_unit_i.alignment_buffer_i
      cv32e40s_alignment_buffer_sva
        alignment_buffer_sva (.*);

  bind cv32e40s_prefetcher:
    core_i.if_stage_i.prefetch_unit_i.prefetcher_i
      cv32e40s_prefetcher_sva
        #(.CLIC(CLIC))
        prefetcher_sva ( .prefetch_is_clic_ptr (core_i.if_stage_i.prefetch_unit_i.prefetch_is_clic_ptr_o),
                        .*);

  bind cv32e40s_core:
    core_i cv32e40s_core_sva
      #(.DEBUG (DEBUG),
        .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
        .CLIC(CLIC),
        .REGFILE_NUM_READ_PORTS(core_i.REGFILE_NUM_READ_PORTS),
        .DBG_NUM_TRIGGERS(DBG_NUM_TRIGGERS))
      core_sva (// probed cs_registers signals
                .cs_registers_mie_q               (core_i.cs_registers_i.mie_q),
                .cs_registers_mepc_n              (core_i.cs_registers_i.mepc_n),
                .cs_registers_mcause_q            (core_i.cs_registers_i.mcause_q),
                .cs_registers_mstatus_q           (core_i.cs_registers_i.mstatus_q),
                .cs_registers_csr_cause_i         (core_i.cs_registers_i.ctrl_fsm_i.csr_cause),
                .branch_taken_in_ex               (core_i.controller_i.controller_fsm_i.branch_taken_ex),
                .exc_cause                        (core_i.controller_i.controller_fsm_i.exc_cause),
                // probed controller signals
                .ctrl_debug_mode_n                (core_i.controller_i.controller_fsm_i.debug_mode_n),
                .id_stage_multi_op_id_stall       (core_i.id_stage_i.multi_op_id_stall),
                .ctrl_pending_async_debug         (core_i.controller_i.controller_fsm_i.pending_async_debug),
                .ctrl_async_debug_allowed         (core_i.controller_i.controller_fsm_i.async_debug_allowed),
                .ctrl_pending_sync_debug          (core_i.controller_i.controller_fsm_i.pending_sync_debug),
                .ctrl_sync_debug_allowed          (core_i.controller_i.controller_fsm_i.sync_debug_allowed),
                .ctrl_pending_interrupt           (core_i.controller_i.controller_fsm_i.pending_interrupt),
                .ctrl_interrupt_allowed           (core_i.controller_i.controller_fsm_i.interrupt_allowed),
                .ctrl_debug_cause_n               (core_i.controller_i.controller_fsm_i.debug_cause_n),
                .ctrl_pending_nmi                 (core_i.controller_i.controller_fsm_i.pending_nmi),
                .ctrl_fsm_cs                      (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),

                .id_stage_id_valid                (core_i.id_stage_i.id_valid_o),
                .priv_lvl_if                      (core_i.if_stage_i.prefetch_priv_lvl),
                .priv_lvl_if_q                    (core_i.if_stage_i.prefetch_unit_i.alignment_buffer_i.instr_priv_lvl_q),
                .alu_op_a_mux_sel_id_i            (core_i.id_stage_i.alu_op_a_mux_sel),
                .alu_op_b_mux_sel_id_i            (core_i.id_stage_i.alu_op_b_mux_sel),
                .operand_a_id_i                   (core_i.id_stage_i.operand_a),
                .operand_b_id_i                   (core_i.id_stage_i.operand_b),
                .jalr_fw_id_i                     (core_i.id_stage_i.jalr_fw),
                .alu_en_id_i                      (core_i.id_stage_i.alu_en),
                .alu_jmpr_id_i                    (core_i.alu_jmpr_id),
                .irq_ack                          (core_i.irq_ack),
                .sys_mret_unqual_id_bypass        (core_i.controller_i.bypass_i.sys_mret_unqual_id),
                .jmpr_unqual_id_bypass            (core_i.controller_i.bypass_i.jmpr_unqual_id),
                .mret_self_stall_bypass           (core_i.controller_i.bypass_i.mret_self_stall),
                .jumpr_self_stall_bypass          (core_i.controller_i.bypass_i.jumpr_self_stall),
                .last_sec_op_id_i                 (core_i.id_stage_i.last_sec_op),
                .last_op_id                       (core_i.id_stage_i.last_op_o),
                .mie_n                            (core_i.cs_registers_i.mie_n),
                .mie_we                           (core_i.cs_registers_i.mie_we),
                .lsu_wpt_match_wb                 (core_i.wb_stage_i.lsu_wpt_match),
                .prefetch_is_mret_ptr_i           (core_i.if_stage_i.prefetch_is_mret_ptr),
                .lsu_cnt_q                        (core_i.load_store_unit_i.cnt_q),
                .resp_filter_bus_cnt_q            (core_i.load_store_unit_i.response_filter_i.bus_cnt_q),
                .resp_filter_core_cnt_q           (core_i.load_store_unit_i.response_filter_i.core_cnt_q),
                .write_buffer_state               (core_i.load_store_unit_i.write_buffer_i.state),
                .first_op_if                      (core_i.if_stage_i.first_op),
                .*);
generate
if (CLIC) begin : clic_asserts
  bind cv32e40s_clic_int_controller:
    core_i.gen_clic_interrupt.clic_int_controller_i
      cv32e40s_clic_int_controller_sva
        clic_int_controller_sva (.ctrl_pending_interrupt  (core_i.controller_i.controller_fsm_i.pending_interrupt),
                                 .ctrl_interrupt_allowed  (core_i.controller_i.controller_fsm_i.interrupt_allowed),
                                 .ctrl_pending_nmi        (core_i.controller_i.controller_fsm_i.pending_nmi),
                                 .ctrl_pending_async_debug(core_i.controller_i.controller_fsm_i.pending_async_debug),
                                 .ctrl_fsm_cs             (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                                 .ctrl_fsm                (core_i.ctrl_fsm),
                                 .dcsr                    (core_i.dcsr),
                                 .*);
end
endgenerate

  bind cv32e40s_sleep_unit:
    core_i.sleep_unit_i cv32e40s_sleep_unit_sva
      sleep_unit_sva (// probed id_stage_i.controller_i signals
                      .ctrl_fsm_cs (core_i.controller_i.controller_fsm_i.ctrl_fsm_cs),
                      .ctrl_fsm_ns (core_i.controller_i.controller_fsm_i.ctrl_fsm_ns),
                      .*);

  bind cv32e40s_decoder: core_i.id_stage_i.decoder_i cv32e40s_decoder_sva
    decoder_sva(.clk   (core_i.id_stage_i.clk),
                .rst_n (core_i.id_stage_i.rst_n),
                .if_id_pipe (core_i.if_id_pipe),
                .*);

  // MPU assertions
  bind cv32e40s_mpu:
    core_i.if_stage_i.mpu_i
    cv32e40s_mpu_sva
      #(.PMP_NUM_REGIONS                        (PMP_NUM_REGIONS),
        .PMP_GRANULARITY                        (PMP_GRANULARITY),
        .PMA_NUM_REGIONS                        (PMA_NUM_REGIONS),
        .PMA_CFG                                (PMA_CFG),
        .IS_INSTR_SIDE                          (1),
        .CORE_RESP_TYPE                         (cv32e40s_pkg::inst_resp_t),
        .CORE_REQ_TYPE                          (cv32e40s_pkg::obi_inst_req_t),
        .DEBUG                                  (DEBUG),
        .DM_REGION_START                        (DM_REGION_START),
        .DM_REGION_END                          (DM_REGION_END))
  mpu_if_sva(.pma_addr                          (pma_i.trans_addr_i),
             .pma_cfg                           (pma_i.pma_cfg),
             .pma_dbg                           (core_i.if_stage_i.mpu_i.core_trans_i.dbg),
             .obi_memtype                       (core_i.instr_memtype_o),
             .obi_addr                          (core_i.instr_addr_o),
             .obi_req                           (core_i.instr_req_o),
             .obi_gnt                           (core_i.instr_gnt_i),
             .obi_dbg                           (core_i.instr_dbg_o),
             .write_buffer_state                (cv32e40s_pkg::WBUF_EMPTY),
             .write_buffer_valid_o              ('0),
             .write_buffer_txn_bufferable       ('0),
             .write_buffer_txn_cacheable        ('0),
             .obi_if_state                      (core_i.if_stage_i.instruction_obi_i.state_q),
             .lsu_split_0                       (1'b0),
             .lsu_split_q                       (1'b0),
             .lsu_ctrl_update                   (1'b0),
             .ctrl_exception_wb                 (1'b0),
             .*);

  bind cv32e40s_mpu:
    core_i.load_store_unit_i.mpu_i
    cv32e40s_mpu_sva
      #(.PMP_NUM_REGIONS                        (PMP_NUM_REGIONS),
        .PMP_GRANULARITY                        (PMP_GRANULARITY),
        .PMA_NUM_REGIONS                        (PMA_NUM_REGIONS),
        .PMA_CFG                                (PMA_CFG),
        .IS_INSTR_SIDE                          (0),
        .CORE_RESP_TYPE                         (cv32e40s_pkg::data_resp_t),
        .CORE_REQ_TYPE                          (cv32e40s_pkg::obi_data_req_t),
        .DEBUG                                  (DEBUG),
        .DM_REGION_START                        (DM_REGION_START),
        .DM_REGION_END                          (DM_REGION_END))
  mpu_lsu_sva(.pma_addr                         (pma_i.trans_addr_i),
             .pma_cfg                           (pma_i.pma_cfg),
             .pma_dbg                           (core_i.load_store_unit_i.mpu_i.core_trans_i.dbg),
             .obi_memtype                       (core_i.data_memtype_o),
             .obi_addr                          (core_i.data_addr_o),
             .obi_req                           (core_i.data_req_o),
             .obi_gnt                           (core_i.data_gnt_i),
             .obi_dbg                           (core_i.data_dbg_o),
             .write_buffer_state                (core_i.load_store_unit_i.write_buffer_i.state),
             .write_buffer_valid_o              (core_i.load_store_unit_i.write_buffer_i.valid_o),
             .write_buffer_txn_bufferable       (core_i.load_store_unit_i.write_buffer_i.trans_o.memtype[0]),
             .write_buffer_txn_cacheable        (core_i.load_store_unit_i.write_buffer_i.trans_o.memtype[1]),
             .obi_if_state                      (cv32e40s_pkg::TRANSPARENT),
             .lsu_split_0                       (core_i.load_store_unit_i.lsu_split_0_o),
             .lsu_split_q                       (core_i.load_store_unit_i.split_q),
             .lsu_ctrl_update                   (core_i.load_store_unit_i.ctrl_update),
             .ctrl_exception_wb                 (core_i.controller_i.controller_fsm_i.exception_in_wb),
             .*);

  bind cv32e40s_lsu_response_filter :
    core_i.load_store_unit_i.response_filter_i
    cv32e40s_lsu_response_filter_sva #(.DEPTH(DEPTH))
      lsu_response_filter_sva (.*);

  bind cv32e40s_write_buffer:
    core_i.load_store_unit_i.write_buffer_i
    cv32e40s_write_buffer_sva
             #(.PMA_NUM_REGIONS(PMA_NUM_REGIONS),
               .PMA_CFG(PMA_CFG))
      write_buffer_sva(.*);

  bind cv32e40s_sequencer:
    core_i.if_stage_i.gen_seq.sequencer_i
      cv32e40s_sequencer_sva
        #(.RV32(RV32))
        sequencer_sva (.ex_wb_pipe_i         (core_i.ex_wb_pipe                                      ),
                       .wb_valid_i           (core_i.wb_stage_i.wb_valid_o                           ),
                       .exception_in_wb_i    (core_i.controller_i.controller_fsm_i.exception_in_wb   ),
                       .pending_sync_debug_i (core_i.controller_i.controller_fsm_i.pending_sync_debug),
                       .csr_addr_id_i        (core_i.id_stage_i.operand_b[11:0]),
                       .csr_en_id_i          (core_i.id_stage_i.csr_en),
                       .instr_valid_id_i     (core_i.id_stage_i.instr_valid),
                       .csr_raddr_ex_i       (core_i.cs_registers_i.csr_raddr),
                       .csr_waddr_wb_i       (core_i.cs_registers_i.csr_waddr),
                       .csr_we_wb_i          (core_i.cs_registers_i.csr_we_int),
                       .priv_lvl_id_i        (core_i.if_id_pipe.priv_lvl),
                       .csr_illegal_i        (core_i.cs_registers_i.csr_illegal_o),
                       .*);

  bind cv32e40s_instr_obi_interface :
    core_i.if_stage_i.instruction_obi_i
    cv32e40s_instr_obi_interface_sva
      instr_obi_sva( .m_c_obi_instr_if (core_i.m_c_obi_instr_if), // SVA monitor modport cannot connect to a master modport
                     .gntpar_err_q     (core_i.if_stage_i.instruction_obi_i.secure.integrity_fifo_i.gntpar_err_q),
                     .*);

  bind cv32e40s_data_obi_interface :
    core_i.load_store_unit_i.data_obi_i
    cv32e40s_data_obi_interface_sva
      data_obi_sva( .m_c_obi_data_if (core_i.m_c_obi_data_if), // SVA monitor modport cannot connect to a master modport
      .gntpar_err_q     (core_i.load_store_unit_i.data_obi_i.secure.integrity_fifo_i.gntpar_err_q),
      .resp_is_store    (core_i.load_store_unit_i.data_obi_i.secure.integrity_fifo_i.resp_is_store),
                    .*);

`ifndef FORMAL
  bind cv32e40s_rvfi:
    rvfi_i
    cv32e40s_rvfi_sim_trace
      tracer_i(.*);
`endif

  bind cv32e40s_rvfi:
    rvfi_i
    cv32e40s_rvfi_sva
      #(.CLIC  (CLIC ),
        .DEBUG (DEBUG))
      rvfi_sva(.irq_ack(core_i.irq_ack),
               .dbg_ack(core_i.dbg_ack),
               .ebreak_in_wb_i(core_i.controller_i.controller_fsm_i.ebreak_in_wb),
               .mtvec_addr_i(core_i.mtvec_addr),
               .obi_instr_fifo_q(rvfi_i.rvfi_instr_obi_i.fifo_q),
               .obi_instr_rptr_q_inc(rvfi_i.rvfi_instr_obi_i.rptr_q_inc),
               .obi_instr_rptr_q(rvfi_i.rvfi_instr_obi_i.rptr_q),
               .pc_ex_i          (core_i.id_ex_pipe.pc),
               .m_c_obi_data_if  (core_i.m_c_obi_data_if),
               .*);

`endif //  `ifndef COREV_ASSERT_OFF

    cv32e40s_core_log
      #(.ENABLE(CORE_LOG_ENABLE),
         .RV32                               (RV32),
         .B_EXT                              (B_EXT),
         .M_EXT                              (M_EXT),
         .DEBUG                              (DEBUG),
         .DM_REGION_START                    (DM_REGION_START),
         .DM_REGION_END                      (DM_REGION_END),
         .DBG_NUM_TRIGGERS                   (DBG_NUM_TRIGGERS),
         .PMA_NUM_REGIONS                    (PMA_NUM_REGIONS),
         .PMA_CFG                            (PMA_CFG),
         .CLIC                               (CLIC),
         .CLIC_ID_WIDTH                      (CLIC_ID_WIDTH),
         .PMP_GRANULARITY                    (PMP_GRANULARITY),
         .PMP_NUM_REGIONS                    (PMP_NUM_REGIONS),
         .PMP_PMPNCFG_RV                     (PMP_PMPNCFG_RV),
         .PMP_PMPADDR_RV                     (PMP_PMPADDR_RV),
         .PMP_MSECCFG_RV                     (PMP_MSECCFG_RV),
         .LFSR0_CFG                          (LFSR0_CFG),
         .LFSR1_CFG                          (LFSR1_CFG),
         .LFSR2_CFG                          (LFSR2_CFG))
    core_log_i(
          .clk_i              ( core_i.id_stage_i.clk              ),
          .ex_wb_pipe_i       ( core_i.ex_wb_pipe                  ),
          .mhartid_i          ( core_i.mhartid_i                   )

      );

    cv32e40s_rvfi
      #(.CLIC  (CLIC  ),
        .DEBUG (DEBUG))
      rvfi_i
        (.clk_i                    ( clk_i                                                                ),
         .rst_ni                   ( rst_ni                                                               ),

         // Non-pipeline Probes
         .m_c_obi_instr_if         ( core_i.m_c_obi_instr_if                                              ),

         // IF Probes
         .if_valid_i               ( core_i.if_stage_i.if_valid_o                                         ),
         .pc_if_i                  ( core_i.if_stage_i.pc_if_o                                            ),
         .instr_pmp_err_if_i       ( core_i.if_stage_i.mpu_i.pmp_err                                      ),
         .last_op_if_i             ( core_i.if_stage_i.last_op_o                                          ),
         .abort_op_if_i            ( core_i.if_stage_i.abort_op_o                                         ),
         .prefetch_valid_if_i      ( core_i.if_stage_i.prefetch_unit_i.prefetch_valid_o                   ),
         .prefetch_ready_if_i      ( core_i.if_stage_i.prefetch_unit_i.prefetch_ready_i                   ),
         .prefetch_addr_if_i       ( core_i.if_stage_i.prefetch_unit_i.prefetch_addr_o                    ),
         .prefetch_compressed_if_i ( core_i.if_stage_i.instr_compressed                                   ),
         .prefetch_instr_if_i      ( core_i.if_stage_i.prefetch_unit_i.prefetch_instr_o                   ),
         .clic_ptr_if_i            ( core_i.if_stage_i.prefetch_is_clic_ptr                               ),
         .mret_ptr_if_i            ( core_i.if_stage_i.prefetch_is_mret_ptr                               ),
         .mpu_status_i             ( core_i.if_stage_i.mpu_i.core_resp_o.mpu_status                       ),
         .prefetch_trans_valid_i   ( core_i.if_stage_i.prefetch_trans_valid                               ),
         .prefetch_trans_ready_i   ( core_i.if_stage_i.prefetch_trans_ready                               ),
         .prefetch_resp_valid_i    ( core_i.if_stage_i.prefetch_resp_valid                                ),

         // ID Probes
         .id_valid_i               ( core_i.id_stage_i.id_valid_o                                         ),
         .id_ready_i               ( core_i.id_stage_i.id_ready_o                                         ),
         .pc_id_i                  ( core_i.id_stage_i.if_id_pipe_i.pc                                    ),
         .rf_re_id_i               ( core_i.id_stage_i.rf_re_o                                            ),
         .sys_mret_id_i            ( core_i.controller_i.controller_fsm_i.sys_mret_id                     ),
         .tbljmp_id_i              ( core_i.id_stage_i.if_id_pipe_i.instr_meta.tbljmp                     ),
         .jump_in_id_i             ( core_i.controller_i.controller_fsm_i.jump_in_id                      ),
         .is_compressed_id_i       ( core_i.id_stage_i.if_id_pipe_i.instr_meta.compressed                 ),
         .lsu_en_id_i              ( core_i.id_stage_i.lsu_en                                             ),
         .lsu_we_id_i              ( core_i.id_stage_i.lsu_we                                             ),
         .lsu_size_id_i            ( core_i.id_stage_i.lsu_size                                           ),
         .rs1_addr_id_i            ( core_i.register_file_wrapper_i.raddr_i[0]                            ),
         .rs2_addr_id_i            ( core_i.register_file_wrapper_i.raddr_i[1]                            ),
         .operand_a_fw_id_i        ( core_i.id_stage_i.operand_a_fw                                       ),
         .operand_b_fw_id_i        ( core_i.id_stage_i.operand_b_fw                                       ),
         .first_op_id_i            ( core_i.id_stage_i.first_op                                           ),
         .hint_id_i                ( core_i.id_stage_i.if_id_pipe_i.instr_meta.hint                       ),
         .clic_ptr_in_id_i         ( core_i.controller_i.controller_fsm_i.clic_ptr_in_id                  ),
         .mret_ptr_in_id_i         ( core_i.controller_i.controller_fsm_i.mret_ptr_in_id                  ),
         // EX Probes
         .ex_ready_i               ( core_i.ex_stage_i.ex_ready_o                                         ),
         .ex_valid_i               ( core_i.ex_stage_i.ex_valid_o                                         ),
         .branch_in_ex_i           ( core_i.controller_i.controller_fsm_i.branch_in_ex                    ),
         .branch_decision_ex_i     ( core_i.ex_stage_i.branch_decision_o                                  ),
         .dret_in_ex_i             ( core_i.ex_stage_i.id_ex_pipe_i.sys_dret_insn                         ),
         .lsu_en_ex_i              ( core_i.ex_stage_i.id_ex_pipe_i.lsu_en                                ),
         .lsu_pma_err_ex_i         ( core_i.load_store_unit_i.mpu_i.pma_i.pma_err_o                       ),
         .lsu_pma_err_atomic_ex_i  ( 1'b0                        /* Atomics not implemented in cv32e40s*/ ),
         .lsu_pma_cfg_ex_i         ( core_i.load_store_unit_i.mpu_i.pma_i.pma_cfg                         ),
         .lsu_misaligned_ex_i      ( core_i.load_store_unit_i.misaligned_access                           ),
         .buffer_trans_ex_i        ( core_i.load_store_unit_i.buffer_trans                                ),
         .buffer_trans_valid_ex_i  ( core_i.load_store_unit_i.buffer_trans_valid                          ),
         .lsu_split_q_ex_i         ( core_i.load_store_unit_i.split_q                                     ),
         .lsu_split_0_ex_i         ( core_i.load_store_unit_i.lsu_split_0_o                               ),

         // WB Probes
         .wb_valid_i               ( core_i.wb_stage_i.wb_valid_o                                         ),
         .wb_ready_i               ( core_i.wb_stage_i.wb_ready_o                                         ),
         .pc_wb_i                  ( core_i.wb_stage_i.ex_wb_pipe_i.pc                                    ),
         .instr_rdata_wb_i         ( core_i.wb_stage_i.ex_wb_pipe_i.instr.bus_resp.rdata                  ),
         .ebreak_in_wb_i           ( core_i.controller_i.controller_fsm_i.ebreak_in_wb                    ),
         .csr_en_wb_i              ( core_i.wb_stage_i.ex_wb_pipe_i.csr_en                                ),
         .sys_wfi_insn_wb_i        ( core_i.wb_stage_i.ex_wb_pipe_i.sys_wfi_insn                          ),
         .sys_en_wb_i              ( core_i.wb_stage_i.ex_wb_pipe_i.sys_en                                ),
         .last_op_wb_i             ( core_i.wb_stage_i.last_op_o                                          ),
         .first_op_wb_i            ( core_i.wb_stage_i.ex_wb_pipe_i.first_op                              ),
         .rf_we_wb_i               ( core_i.wb_stage_i.rf_we_wb_o                                         ),
         .rf_addr_wb_i             ( core_i.wb_stage_i.rf_waddr_wb_o                                      ),
         .rf_wdata_wb_i            ( core_i.wb_stage_i.rf_wdata_wb_o                                      ),
         .lsu_rdata_wb_i           ( core_i.load_store_unit_i.lsu_rdata_1_o                               ),
         .is_dummy_instr_wb_i      ( core_i.wb_stage_i.ex_wb_pipe_i.instr_meta.dummy                      ),
         .lsu_exokay_wb_i          ( 1'b0     /* No atomic support on cv32e40s */                         ),
         .lsu_err_wb_i             ( core_i.load_store_unit_i.lsu_err_1_o                                 ),
         .abort_op_wb_i            ( core_i.wb_stage_i.abort_op_o                                         ),
         .clic_ptr_wb_i            ( core_i.wb_stage_i.ex_wb_pipe_i.instr_meta.clic_ptr                   ),
         .hint_wb_i                ( core_i.id_stage_i.ex_wb_pipe_i.instr_meta.hint                       ),
         .mret_ptr_wb_i            ( core_i.wb_stage_i.ex_wb_pipe_i.instr_meta.mret_ptr                   ),
         .wpt_match_wb_i           ( core_i.wb_stage_i.wpt_match_wb_o                                     ),
         .mpu_status_wb_i          ( core_i.wb_stage_i.mpu_status_wb_o                                    ),
         .csr_mscratchcsw_in_wb_i  ( core_i.cs_registers_i.mscratchcsw_in_wb                              ),
         .csr_mscratchcswl_in_wb_i ( core_i.cs_registers_i.mscratchcswl_in_wb                             ),
         .csr_mnxti_in_wb_i        ( core_i.cs_registers_i.mnxti_in_wb                                    ),

         .branch_addr_n_i          ( core_i.if_stage_i.branch_addr_n                                      ),

         .priv_lvl_i               ( core_i.priv_lvl                                                      ),
         .ctrl_fsm_i               ( core_i.ctrl_fsm                                                      ),
         .ctrl_fsm_cs_i            ( core_i.controller_i.controller_fsm_i.ctrl_fsm_cs                     ),
         .ctrl_fsm_ns_i            ( core_i.controller_i.controller_fsm_i.ctrl_fsm_ns                     ),
         .pending_single_step_i    ( core_i.controller_i.controller_fsm_i.pending_single_step             ),
         .single_step_allowed_i    ( core_i.controller_i.controller_fsm_i.single_step_allowed             ),
         .nmi_pending_i            ( core_i.controller_i.controller_fsm_i.nmi_pending_q                   ),
         .nmi_is_store_i           ( core_i.controller_i.controller_fsm_i.nmi_is_store_q                  ),
         .debug_mode_q_i           ( core_i.controller_i.controller_fsm_i.debug_mode_q                    ),
         .debug_cause_n_i          ( core_i.controller_i.controller_fsm_i.debug_cause_n                   ),
         .etrigger_in_wb_i         ( core_i.controller_i.controller_fsm_i.etrigger_in_wb                  ),
         .irq_i                    ( core_i.irq_i & IRQ_MASK                                              ),
         .irq_wu_ctrl_i            ( core_i.irq_wu_ctrl                                                   ),
         .irq_id_ctrl_i            ( core_i.irq_id_ctrl                                                   ),

         // CSRs
         .csr_jvt_n_i              ( core_i.cs_registers_i.jvt_n                                          ),
         .csr_jvt_q_i              ( core_i.cs_registers_i.jvt_rdata                                      ),
         .csr_jvt_we_i             ( core_i.cs_registers_i.jvt_we                                         ),
         .csr_mstatus_n_i          ( core_i.cs_registers_i.mstatus_n                                      ),
         .csr_mstatus_q_i          ( core_i.cs_registers_i.mstatus_rdata                                  ),
         .csr_mstatus_we_i         ( core_i.cs_registers_i.mstatus_we                                     ),
         .csr_misa_n_i             ( core_i.cs_registers_i.misa_n                                         ),
         .csr_misa_q_i             ( core_i.cs_registers_i.misa_rdata                                     ),
         .csr_misa_we_i            ( core_i.cs_registers_i.misa_we                                        ),
         .csr_mie_n_i              ( core_i.cs_registers_i.mie_n                                          ),
         .csr_mie_q_i              ( core_i.cs_registers_i.mie_rdata                                      ),
         .csr_mie_we_i             ( core_i.cs_registers_i.mie_we                                         ),
         .csr_mtvec_n_i            ( core_i.cs_registers_i.mtvec_n                                        ),
         .csr_mtvec_q_i            ( core_i.cs_registers_i.mtvec_rdata                                    ),
         .csr_mtvec_we_i           ( core_i.cs_registers_i.mtvec_we                                       ),
         .csr_mtvt_n_i             ( core_i.cs_registers_i.mtvt_n                                         ),
         .csr_mtvt_q_i             ( core_i.cs_registers_i.mtvt_rdata                                     ),
         .csr_mtvt_we_i            ( core_i.cs_registers_i.mtvt_we                                        ),
         .csr_mcountinhibit_n_i    ( core_i.cs_registers_i.mcountinhibit_n                                ),
         .csr_mcountinhibit_q_i    ( core_i.cs_registers_i.mcountinhibit_rdata                            ),
         .csr_mcountinhibit_we_i   ( core_i.cs_registers_i.mcountinhibit_we                               ),
         .csr_mhpmevent_n_i        ( core_i.cs_registers_i.mhpmevent_n                                    ),
         .csr_mhpmevent_q_i        ( core_i.cs_registers_i.mhpmevent_rdata                                ),
         .csr_mhpmevent_we_i       ( {31'h0, core_i.cs_registers_i.mhpmevent_we} <<
                                     core_i.cs_registers_i.csr_waddr[4:0] ),
         .csr_mscratch_n_i         ( core_i.cs_registers_i.mscratch_n                                     ),
         .csr_mscratch_q_i         ( core_i.cs_registers_i.mscratch_rdata                                 ),
         .csr_mscratch_we_i        ( core_i.cs_registers_i.mscratch_we                                    ),
         .csr_mepc_n_i             ( core_i.cs_registers_i.mepc_n                                         ),
         .csr_mepc_q_i             ( core_i.cs_registers_i.mepc_rdata                                     ),
         .csr_mepc_we_i            ( core_i.cs_registers_i.mepc_we                                        ),
         .csr_mcause_n_i           ( core_i.cs_registers_i.mcause_n                                       ),
         .csr_mcause_q_i           ( core_i.cs_registers_i.mcause_rdata                                   ),
         .csr_mcause_we_i          ( core_i.cs_registers_i.mcause_we                                      ),
         .csr_mip_n_i              ( core_i.cs_registers_i.mip_n                                          ),
         .csr_mip_q_i              ( core_i.cs_registers_i.mip_rdata                                      ),
         .csr_mip_we_i             ( core_i.cs_registers_i.mip_we                                         ),
         .csr_mnxti_n_i            ( core_i.cs_registers_i.mnxti_n                                        ),
         .csr_mnxti_q_i            ( core_i.cs_registers_i.mnxti_rdata                                    ),
         .csr_mnxti_we_i           ( core_i.cs_registers_i.mnxti_we                                       ),
         .csr_mintstatus_n_i       ( core_i.cs_registers_i.mintstatus_n                                   ),
         .csr_mintstatus_q_i       ( core_i.cs_registers_i.mintstatus_rdata                               ),
         .csr_mintstatus_we_i      ( core_i.cs_registers_i.mintstatus_we                                  ),
         .csr_mintthresh_n_i       ( core_i.cs_registers_i.mintthresh_n                                   ),
         .csr_mintthresh_q_i       ( core_i.cs_registers_i.mintthresh_rdata                               ),
         .csr_mintthresh_we_i      ( core_i.cs_registers_i.mintthresh_we                                  ),
         .csr_mscratchcsw_n_i      ( core_i.cs_registers_i.mscratchcsw_n                                  ),
         .csr_mscratchcsw_q_i      ( core_i.cs_registers_i.mscratchcsw_rdata                              ),
         .csr_mscratchcsw_we_i     ( core_i.cs_registers_i.mscratchcsw_we                                 ),
         .csr_mscratchcswl_n_i     ( core_i.cs_registers_i.mscratchcswl_n                                 ),
         .csr_mscratchcswl_q_i     ( core_i.cs_registers_i.mscratchcswl_rdata                             ),
         .csr_mscratchcswl_we_i    ( core_i.cs_registers_i.mscratchcswl_we                                ),
         .csr_tdata1_n_i           ( core_i.cs_registers_i.debug_triggers_i.tdata1_n_r                    ),
         .csr_tdata1_q_i           ( core_i.cs_registers_i.tdata1_rdata                                   ),
         .csr_tdata1_we_i          ( core_i.cs_registers_i.debug_triggers_i.tdata1_we_r                   ),
         .csr_tdata2_n_i           ( core_i.cs_registers_i.debug_triggers_i.tdata2_n_r                    ),
         .csr_tdata2_q_i           ( core_i.cs_registers_i.tdata2_rdata                                   ),
         .csr_tdata2_we_i          ( core_i.cs_registers_i.debug_triggers_i.tdata2_we_r                   ),
         .csr_tinfo_n_i            ( core_i.cs_registers_i.debug_triggers_i.tinfo_n                       ),
         .csr_tinfo_q_i            ( core_i.cs_registers_i.tinfo_rdata                                    ),
         .csr_tinfo_we_i           ( core_i.cs_registers_i.tinfo_we                                       ),
         .csr_dcsr_n_i             ( core_i.cs_registers_i.dcsr_n                                         ),
         .csr_dcsr_q_i             ( core_i.cs_registers_i.dcsr_rdata                                     ),
         .csr_dcsr_we_i            ( core_i.cs_registers_i.dcsr_we                                        ),
         .csr_dpc_n_i              ( core_i.cs_registers_i.dpc_n                                          ),
         .csr_dpc_q_i              ( core_i.cs_registers_i.dpc_rdata                                      ),
         .csr_dpc_we_i             ( core_i.cs_registers_i.dpc_we                                         ),
         .csr_dscratch0_n_i        ( core_i.cs_registers_i.dscratch0_n                                    ),
         .csr_dscratch0_q_i        ( core_i.cs_registers_i.dscratch0_rdata                                ),
         .csr_dscratch0_we_i       ( core_i.cs_registers_i.dscratch0_we                                   ),
         .csr_dscratch1_n_i        ( core_i.cs_registers_i.dscratch1_n                                    ),
         .csr_dscratch1_q_i        ( core_i.cs_registers_i.dscratch1_rdata                                ),
         .csr_dscratch1_we_i       ( core_i.cs_registers_i.dscratch1_we                                   ),
         .csr_mhpmcounter_n_i      ( core_i.cs_registers_i.mhpmcounter_n                                  ),
         .csr_mhpmcounter_q_i      ( core_i.cs_registers_i.mhpmcounter_rdata                              ),
         .csr_mhpmcounter_we_i     ( core_i.cs_registers_i.mhpmcounter_we                                 ),
         .csr_mvendorid_i          ( core_i.cs_registers_i.mvendorid_rdata                                ),
         .csr_marchid_i            ( core_i.cs_registers_i.marchid_rdata                                  ),
         .csr_mhartid_i            ( core_i.cs_registers_i.mhartid_rdata                                  ),
         .csr_mimpid_i             ( core_i.cs_registers_i.mimpid_rdata                                   ),
         .csr_mstatush_n_i         ( core_i.cs_registers_i.mstatush_n                                     ),
         .csr_mstatush_q_i         ( core_i.cs_registers_i.mstatush_rdata                                 ),
         .csr_mstatush_we_i        ( core_i.cs_registers_i.mstatush_we                                    ),
         .csr_tselect_n_i          ( core_i.cs_registers_i.debug_triggers_i.tselect_n                     ),
         .csr_tselect_q_i          ( core_i.cs_registers_i.tselect_rdata                                  ),
         .csr_tselect_we_i         ( core_i.cs_registers_i.tselect_we                                     ),

         .csr_mconfigptr_n_i       ( '0                                                                   ),
         .csr_mconfigptr_q_i       ( '0                                                                   ),
         .csr_mconfigptr_we_i      ( '0                                                                   ),

         .csr_mcounteren_n_i       ( core_i.cs_registers_i.mcounteren_n                                   ),
         .csr_mcounteren_q_i       ( core_i.cs_registers_i.mcounteren_rdata                               ),
         .csr_mcounteren_we_i      ( core_i.cs_registers_i.mcounteren_we                                  ),

         .csr_pmpncfg_n_i          ( core_i.cs_registers_i.pmpncfg_n                                      ),
         .csr_pmpncfg_q_i          ( core_i.cs_registers_i.pmpncfg_rdata                                  ),
         .csr_pmpncfg_we_i         ( core_i.cs_registers_i.pmpncfg_we                                     ),
         .csr_pmpaddr_n_i          ( core_i.cs_registers_i.pmp_addr_n_r                                   ), // Next read value can differ from written/stored value
         .csr_pmpaddr_q_i          ( core_i.cs_registers_i.pmp_addr_rdata                                 ),
         .csr_pmpaddr_we_i         ( core_i.cs_registers_i.pmp_addr_we                                    ),
         .csr_mseccfg_n_i          ( core_i.cs_registers_i.pmp_mseccfg_n                                  ),
         .csr_mseccfg_q_i          ( core_i.cs_registers_i.pmp_mseccfg_rdata                              ),
         .csr_mseccfg_we_i         ( core_i.cs_registers_i.pmp_mseccfg_we                                 ),
         .csr_mseccfgh_n_i         ( core_i.cs_registers_i.pmp_mseccfgh_n                                 ),
         .csr_mseccfgh_q_i         ( core_i.cs_registers_i.pmp_mseccfgh_rdata                             ),
         .csr_mseccfgh_we_i        ( core_i.cs_registers_i.pmp_mseccfgh_we                                ),
         .csr_menvcfg_n_i          ( core_i.cs_registers_i.menvcfg_n                                      ),
         .csr_menvcfg_q_i          ( core_i.cs_registers_i.menvcfg_rdata                                  ),
         .csr_menvcfg_we_i         ( core_i.cs_registers_i.menvcfg_we                                     ),
         .csr_menvcfgh_n_i         ( core_i.cs_registers_i.menvcfgh_n                                     ),
         .csr_menvcfgh_q_i         ( core_i.cs_registers_i.menvcfgh_rdata                                 ),
         .csr_menvcfgh_we_i        ( core_i.cs_registers_i.menvcfgh_we                                    ),
         .csr_cpuctrl_n_i          ( core_i.cs_registers_i.cpuctrl_n                                      ),
         .csr_cpuctrl_q_i          ( core_i.cs_registers_i.cpuctrl_rdata                                  ),
         .csr_cpuctrl_we_i         ( core_i.cs_registers_i.cpuctrl_we                                     ),
         .csr_secureseed0_n_i      ( core_i.cs_registers_i.secureseed0_n                                  ),
         .csr_secureseed0_q_i      ( core_i.cs_registers_i.secureseed0_rdata                              ),
         .csr_secureseed0_we_i     ( core_i.cs_registers_i.secureseed0_we                                 ),
         .csr_secureseed1_n_i      ( core_i.cs_registers_i.secureseed1_n                                  ),
         .csr_secureseed1_q_i      ( core_i.cs_registers_i.secureseed1_rdata                              ),
         .csr_secureseed1_we_i     ( core_i.cs_registers_i.secureseed1_we                                 ),
         .csr_secureseed2_n_i      ( core_i.cs_registers_i.secureseed2_n                                  ),
         .csr_secureseed2_q_i      ( core_i.cs_registers_i.secureseed2_rdata                              ),
         .csr_secureseed2_we_i     ( core_i.cs_registers_i.secureseed2_we                                 ),
         .csr_mstateen0_n_i        ( core_i.cs_registers_i.mstateen0_n                                    ),
         .csr_mstateen0_q_i        ( core_i.cs_registers_i.mstateen0_rdata                                ),
         .csr_mstateen0_we_i       ( core_i.cs_registers_i.mstateen0_we                                   ),
         .csr_mstateen1_n_i        ( core_i.cs_registers_i.mstateen1_n                                    ),
         .csr_mstateen1_q_i        ( core_i.cs_registers_i.mstateen1_rdata                                ),
         .csr_mstateen1_we_i       ( core_i.cs_registers_i.mstateen1_we                                   ),
         .csr_mstateen2_n_i        ( core_i.cs_registers_i.mstateen2_n                                    ),
         .csr_mstateen2_q_i        ( core_i.cs_registers_i.mstateen2_rdata                                ),
         .csr_mstateen2_we_i       ( core_i.cs_registers_i.mstateen2_we                                   ),
         .csr_mstateen3_n_i        ( core_i.cs_registers_i.mstateen3_n                                    ),
         .csr_mstateen3_q_i        ( core_i.cs_registers_i.mstateen3_rdata                                ),
         .csr_mstateen3_we_i       ( core_i.cs_registers_i.mstateen3_we                                   ),
         .csr_mstateen0h_n_i       ( core_i.cs_registers_i.mstateen0h_n                                   ),
         .csr_mstateen0h_q_i       ( core_i.cs_registers_i.mstateen0h_rdata                               ),
         .csr_mstateen0h_we_i      ( core_i.cs_registers_i.mstateen0h_we                                  ),
         .csr_mstateen1h_n_i       ( core_i.cs_registers_i.mstateen1h_n                                   ),
         .csr_mstateen1h_q_i       ( core_i.cs_registers_i.mstateen1h_rdata                               ),
         .csr_mstateen1h_we_i      ( core_i.cs_registers_i.mstateen1h_we                                  ),
         .csr_mstateen2h_n_i       ( core_i.cs_registers_i.mstateen2h_n                                   ),
         .csr_mstateen2h_q_i       ( core_i.cs_registers_i.mstateen2h_rdata                               ),
         .csr_mstateen2h_we_i      ( core_i.cs_registers_i.mstateen2h_we                                  ),
         .csr_mstateen3h_n_i       ( core_i.cs_registers_i.mstateen3h_n                                   ),
         .csr_mstateen3h_q_i       ( core_i.cs_registers_i.mstateen3h_rdata                               ),
         .csr_mstateen3h_we_i      ( core_i.cs_registers_i.mstateen3h_we                                  )


`ifdef RISCV_FORMAL
         ,`RVFI_CONN
`else
         ,`RVFI_TIEOFF
`endif
         );


    // instantiate the core
    cv32e40s_core
        #(
          .LIB                   ( LIB                   ),
          .RV32                  ( RV32                  ),
          .B_EXT                 ( B_EXT                 ),
          .M_EXT                 ( M_EXT                 ),
          .PMP_GRANULARITY       ( PMP_GRANULARITY       ),
          .PMP_NUM_REGIONS       ( PMP_NUM_REGIONS       ),
          .PMP_PMPNCFG_RV        ( PMP_PMPNCFG_RV        ),
          .PMP_PMPADDR_RV        ( PMP_PMPADDR_RV        ),
          .PMP_MSECCFG_RV        ( PMP_MSECCFG_RV        ),
          .CLIC                  ( CLIC                  ),
          .CLIC_ID_WIDTH         ( CLIC_ID_WIDTH         ),
          .DEBUG                 ( DEBUG                 ),
          .DM_REGION_START       ( DM_REGION_START       ),
          .DM_REGION_END         ( DM_REGION_END         ),
          .DBG_NUM_TRIGGERS      ( DBG_NUM_TRIGGERS      ),
          .PMA_NUM_REGIONS       ( PMA_NUM_REGIONS       ),
          .PMA_CFG               ( PMA_CFG               ),
          .LFSR0_CFG             ( LFSR0_CFG             ),
          .LFSR1_CFG             ( LFSR1_CFG             ),
          .LFSR2_CFG             ( LFSR2_CFG             ))
    core_i (.*);

endmodule
