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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_if_stage import cv32e40s_pkg::*;
#(
  parameter b_ext_e      B_EXT           = B_NONE,
  parameter bit          X_EXT           = 0,
  parameter int          X_ID_WIDTH      = 4,
  parameter int          PMA_NUM_REGIONS = 0,
  parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT},
  parameter int          PMP_GRANULARITY = 0,
  parameter int          PMP_NUM_REGIONS = 0,
  parameter bit          DUMMY_INSTRUCTIONS = 0,
  parameter int unsigned MTVT_ADDR_WIDTH = 26,
  parameter bit          SMCLIC          = 1'b0,
  parameter int          SMCLIC_ID_WIDTH = 5,
  parameter bit          ZC_EXT          = 0,
  parameter m_ext_e      M_EXT           = M_NONE
)
(
  input  logic          clk,
  input  logic          rst_n,

  // Target addresses
  input  logic [31:0]   boot_addr_i,            // Boot address
  input  logic [31:0]   branch_target_ex_i,     // Branch target address
  input  logic [31:0]   dm_exception_addr_i,    // Debug mode exception address
  input  logic [31:0]   dm_halt_addr_i,         // Debug mode halt address
  input  logic [31:0]   dpc_i,                  // Debug PC (restore upon return from debug)
  input  logic [31:0]   jump_target_id_i,       // Jump target address
  input  logic [31:0]   mepc_i,                 // Exception PC (restore upon return from exception/interrupt)
  input  logic [24:0]   mtvec_addr_i,           // Exception/interrupt address (MSBs)

  input  logic          branch_decision_ex_i,   // Current branch decision from EX

  input  logic          last_sec_op_id_i,
  output logic          pc_err_o,               // Error signal for the pc checker module
  input  logic [MTVT_ADDR_WIDTH-1:0]   mtvt_addr_i,            // Base address for CLIC vectoring

  input  logic [JVT_ADDR_WIDTH-1:0]    jvt_addr_i,

  input ctrl_fsm_t      ctrl_fsm_i,
  input  logic          trigger_match_i,


  // Instruction bus interface
  if_c_obi.master       m_c_obi_instr_if,

  output if_id_pipe_t   if_id_pipe_o,           // IF/ID pipeline stage
  output logic [31:0]   pc_if_o,                // Program counter
  output logic          csr_mtvec_init_o,       // Tell CS regfile to init mtvec
  output logic          if_busy_o,              // Is the IF stage busy fetching instructions?
  output logic          ptr_in_if_o,            // The IF stage currently holds a pointer

  // Stage ready/valid
  output logic          if_valid_o,
  input  logic          id_ready_i,

  input  logic          id_valid_i,
  input  logic          ex_ready_i,

  input  logic          ex_valid_i,
  input  logic          wb_ready_i,

  input  id_ex_pipe_t   id_ex_pipe_i,

  // PMP CSR's
  input pmp_csr_t       csr_pmp_i,

  // mstateen CSR
  input  logic [31:0]   mstateen0_i,

  // Privilege mode
  input privlvlctrl_t   priv_lvl_ctrl_i,
  input privlvl_t       priv_lvl_clic_ptr_i,    // Priv level for CLIC pointers. Must respect mstatus.mprv (done in cs_registers)

  // Dummy Instruction Control
  input xsecure_ctrl_t  xsecure_ctrl_i,
  output  logic         lfsr_shift_o,

  // eXtension interface
  if_xif.cpu_compressed xif_compressed_if,      // XIF compressed interface
  input  logic          xif_offloading_id_i     // ID stage attempts to offload an instruction
);

  logic              if_ready;

  // prefetch buffer related signals
  logic              prefetch_busy;

  logic       [31:0] branch_addr_n;

  logic              prefetch_valid;
  inst_resp_t        prefetch_instr;
  privlvl_t          prefetch_priv_lvl;
  logic              prefetch_is_clic_ptr;
  logic              prefetch_is_tbljmp_ptr;

  // flag for predecoded cm.jt / cm.jalt.
  // Maps to custom use of JAL instruction
  logic              tbljmp_raw; // Raw table jump from compressed decoder
  logic              tbljmp;     // Table jump which may deassert due to exceptions

  logic              illegal_c_insn;

  inst_resp_t        instr_decompressed;
  logic              instr_compressed_int;

  // Transaction signals to/from obi interface
  logic              prefetch_resp_valid;
  logic              prefetch_trans_valid;
  logic              prefetch_trans_ready;
  logic [31:0]       prefetch_trans_addr;
  inst_resp_t        prefetch_inst_resp;
  logic              prefetch_one_txn_pend_n;

  logic              bus_resp_valid;
  obi_inst_resp_t    bus_resp;
  logic              bus_trans_valid;
  logic              bus_trans_ready;
  obi_inst_req_t     bus_trans;
  obi_inst_req_t     core_trans;

  logic              dummy_insert;
  inst_resp_t        dummy_instr;

  // Local instr_valid
  logic instr_valid;

  // eXtension interface signals
  logic [X_ID_WIDTH-1:0] xif_id;

  // Flag for last operation - used by Zc*
  logic              last_op;

  // Fetch address selection
  always_comb
  begin
    // Default assign PC_BOOT (should be overwritten in below case)
    branch_addr_n = {boot_addr_i[31:2], 2'b0};

    unique case (ctrl_fsm_i.pc_mux)
      PC_BOOT:       branch_addr_n = {boot_addr_i[31:2], 2'b0};
      PC_JUMP:       branch_addr_n = jump_target_id_i;
      PC_BRANCH:     branch_addr_n = branch_target_ex_i;
      PC_MRET:       branch_addr_n = mepc_i;                                                      // PC is restored when returning from IRQ/exception
      PC_DRET:       branch_addr_n = dpc_i;
      PC_WB_PLUS4:   branch_addr_n = ctrl_fsm_i.pipe_pc;                                          // Jump to next instruction forces prefetch buffer reload
      PC_TRAP_EXC:   branch_addr_n = {mtvec_addr_i, 7'h0};                                        // All the exceptions go to base address
      PC_TRAP_IRQ:   branch_addr_n = {mtvec_addr_i, ctrl_fsm_i.mtvec_pc_mux, 2'b00};     // interrupts are vectored
      PC_TRAP_DBD:   branch_addr_n = {dm_halt_addr_i[31:2], 2'b0};
      PC_TRAP_DBE:   branch_addr_n = {dm_exception_addr_i[31:2], 2'b0};
      PC_TRAP_NMI:   branch_addr_n = {mtvec_addr_i, NMI_MTVEC_INDEX, 2'b00};
      PC_TRAP_CLICV: branch_addr_n = {mtvt_addr_i, ctrl_fsm_i.mtvt_pc_mux[SMCLIC_ID_WIDTH-1:0], 2'b00};
      // CLIC and Zc* spec requires to clear bit 0. This clearing is done in the alignment buffer.
      PC_POINTER :   branch_addr_n = if_id_pipe_o.ptr;
      // JVT + (index << 2)
      PC_TBLJUMP :   branch_addr_n = {jvt_addr_i, ctrl_fsm_i.jvt_pc_mux[7:0], 2'b00};

      default:;
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (ctrl_fsm_i.pc_mux == PC_BOOT) & ctrl_fsm_i.pc_set;

  // prefetch buffer, caches a fixed number of instructions
  cv32e40s_prefetch_unit
  #(
      .SMCLIC (SMCLIC)
  )
  prefetch_unit_i
  (
    .clk                      ( clk                         ),
    .rst_n                    ( rst_n                       ),

    .ctrl_fsm_i               ( ctrl_fsm_i                  ),
    .priv_lvl_ctrl_i          ( priv_lvl_ctrl_i             ),

    .branch_addr_i            ( {branch_addr_n[31:1], 1'b0} ),

    .prefetch_ready_i         ( if_ready                    ),
    .prefetch_valid_o         ( prefetch_valid              ),
    .prefetch_instr_o         ( prefetch_instr              ),
    .prefetch_addr_o          ( pc_if_o                     ),
    .prefetch_priv_lvl_o      ( prefetch_priv_lvl           ),
    .prefetch_is_clic_ptr_o   ( prefetch_is_clic_ptr        ),
    .prefetch_is_tbljmp_ptr_o ( prefetch_is_tbljmp_ptr      ),

    .trans_valid_o            ( prefetch_trans_valid        ),
    .trans_ready_i            ( prefetch_trans_ready        ),
    .trans_addr_o             ( prefetch_trans_addr         ),

    .resp_valid_i             ( prefetch_resp_valid         ),
    .resp_i                   ( prefetch_inst_resp          ),

    // Prefetch Buffer Status
    .prefetch_busy_o          ( prefetch_busy               ),
    .one_txn_pend_n           ( prefetch_one_txn_pend_n     )
  );

  //////////////////////////////////////////////////////////////////////////////
  // MPU
  //////////////////////////////////////////////////////////////////////////////

  // TODO: The prot bits are currently not checked for correctness anywhere
  assign core_trans.addr      = prefetch_trans_addr;
  assign core_trans.dbg       = ctrl_fsm_i.debug_mode_if;
  assign core_trans.prot[0]   = 1'b0;                        // Transfers from IF stage are instruction transfers
  assign core_trans.prot[2:1] = prefetch_priv_lvl;           // Privilege level
  assign core_trans.memtype   = 2'b00;                       // memtype is assigned in the MPU
  assign core_trans.achk      = 12'b0;                       // Integrity signals assigned in bus interface


  cv32e40s_mpu
  #(
    .IF_STAGE             ( 1                       ),
    .CORE_REQ_TYPE        ( obi_inst_req_t          ),
    .CORE_RESP_TYPE       ( inst_resp_t             ),
    .BUS_RESP_TYPE        ( obi_inst_resp_t         ),
    .PMA_NUM_REGIONS      ( PMA_NUM_REGIONS         ),
    .PMA_CFG              ( PMA_CFG                 ),
    .PMP_GRANULARITY      ( PMP_GRANULARITY         ),
    .PMP_NUM_REGIONS      ( PMP_NUM_REGIONS         )
  )
  mpu_i
  (
    .clk                  ( clk                     ),
    .rst_n                ( rst_n                   ),
    .misaligned_access_i  ( 1'b0                    ), // MPU on instruction side will not issue misaligned access fault
                                                       // Misaligned access to main is allowed, and accesses outside main will
                                                       // result in instruction access fault (which will have priority over
                                                       //  misaligned from I/O fault)
    .core_if_data_access_i( 1'b0                    ), // No data access possible from IF
    .priv_lvl_i           ( prefetch_priv_lvl       ), // todo: this is already encoded in the prot[2:1] bits
    .csr_pmp_i            ( csr_pmp_i               ),

    .core_one_txn_pend_n  ( prefetch_one_txn_pend_n ),
    .core_mpu_err_wait_i  ( 1'b1                    ),
    .core_mpu_err_o       (                         ), // Unconnected on purpose
    .core_trans_valid_i   ( prefetch_trans_valid    ),
    .core_trans_ready_o   ( prefetch_trans_ready    ),
    .core_trans_i         ( core_trans              ),
    .core_resp_valid_o    ( prefetch_resp_valid     ),
    .core_resp_o          ( prefetch_inst_resp      ),

    .bus_trans_valid_o    ( bus_trans_valid         ),
    .bus_trans_ready_i    ( bus_trans_ready         ),
    .bus_trans_o          ( bus_trans               ),
    .bus_resp_valid_i     ( bus_resp_valid          ),
    .bus_resp_i           ( bus_resp                )
  );

  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  cv32e40s_instr_obi_interface
  instruction_obi_i
  (
    .clk                  ( clk              ),
    .rst_n                ( rst_n            ),

    .trans_valid_i        ( bus_trans_valid  ),
    .trans_ready_o        ( bus_trans_ready  ),
    .trans_i              ( bus_trans        ),

    .resp_valid_o         ( bus_resp_valid   ),
    .resp_o               ( bus_resp         ),
    .m_c_obi_instr_if     ( m_c_obi_instr_if )
  );

  ///////////////
  // PC checker
  ///////////////
  cv32e40s_pc_check
  pc_check_i
  (
    .clk                  ( clk                  ),
    .rst_n                ( rst_n                ),

    .if_valid_i           ( if_valid_o           ),
    .id_ready_i           ( id_ready_i           ),

    .id_valid_i           ( id_valid_i           ),
    .ex_ready_i           ( ex_ready_i           ),

    .ex_valid_i           ( ex_valid_i           ),
    .wb_ready_i           ( wb_ready_i           ),

    .pc_if_i              ( pc_if_o              ),
    .ctrl_fsm_i           ( ctrl_fsm_i           ),
    .if_id_pipe_i         ( if_id_pipe_o         ),
    .id_ex_pipe_i         ( id_ex_pipe_i         ),
    .jump_target_id_i     ( jump_target_id_i     ),
    .branch_target_ex_i   ( branch_target_ex_i   ),
    .branch_decision_ex_i ( branch_decision_ex_i ),

    .last_sec_op_id_i     ( last_sec_op_id_i     ),
    .last_op_ex_i         ( id_ex_pipe_i.last_op ),

    .prefetch_is_ptr_i    ( ptr_in_if_o          ),

    .mepc_i               ( mepc_i               ),
    .mtvec_addr_i         ( mtvec_addr_i         ),
    .dpc_i                ( dpc_i                ),
    .jvt_addr_i           ( jvt_addr_i           ),

    .boot_addr_i          ( boot_addr_i          ),
    .dm_halt_addr_i       ( dm_halt_addr_i       ),
    .dm_exception_addr_i  ( dm_exception_addr_i  ),

    .pc_err_o             ( pc_err_o             )
  );

  // Local instr_valid when we have valid output from prefetcher or we are inserting a dummy instruction
  // and IF is not halted or killed
  assign instr_valid = (prefetch_valid || dummy_insert) && !ctrl_fsm_i.kill_if && !ctrl_fsm_i.halt_if;

  // if_stage ready when killed, otherwise when not halted or if a dummy instruction is inserted.
  assign if_ready = ctrl_fsm_i.kill_if || (id_ready_i && !dummy_insert && !ctrl_fsm_i.halt_if);

  // if stage valid when local instr_valid is 1
  assign if_valid_o = instr_valid;

  assign if_busy_o = prefetch_busy;

  // Ensures one shift of lfsr0 for each instruction inserted in IF
  assign lfsr_shift_o = (if_valid_o && id_ready_i) && dummy_insert;

  assign ptr_in_if_o = prefetch_is_clic_ptr || prefetch_is_tbljmp_ptr;

  // Last operation of table jumps are set when the pointer is fed to ID stage
  // tbljmp is set when a cm.jt or cm.jalt is decoded in the compressed decoder.
  // todo: Factor in last operation of sequenced Zc* (push/pop)
  assign last_op = tbljmp ? 1'b0 : 1'b1;

  // Populate instruction meta data
  // Fields 'compressed' and 'tbljmp' keep their old value by default.
  //   - In case of a table jump we need the fields to stay as 'compressed=1' and 'tbljmp=1'
  //     even when the pointer is sent to ID (operation 2/2)
  //   - For all cases except table jump pointer we update the values to the current values from predecoding.
  instr_meta_t instr_meta_n;
  always_comb begin
    instr_meta_n = '0;
    instr_meta_n.dummy         = dummy_insert;
    instr_meta_n.compressed    = if_id_pipe_o.instr_meta.compressed;
    instr_meta_n.clic_ptr      = prefetch_is_clic_ptr;
    instr_meta_n.tbljmp        = if_id_pipe_o.instr_meta.tbljmp;
  end

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  // Todo: E40S: We will probably need to prevent dummy instructions between pointer fetcher and the pointer target fetch
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0) begin
      if_id_pipe_o.instr_valid      <= 1'b0;
      if_id_pipe_o.instr            <= INST_RESP_RESET_VAL;
      if_id_pipe_o.instr_meta       <= '0;
      if_id_pipe_o.pc               <= '0;
      if_id_pipe_o.illegal_c_insn   <= 1'b0;
      if_id_pipe_o.compressed_instr <= '0;
      if_id_pipe_o.priv_lvl         <= PRIV_LVL_M;
      if_id_pipe_o.trigger_match    <= 1'b0;
      if_id_pipe_o.xif_id           <= '0;
      if_id_pipe_o.ptr              <= '0;
      if_id_pipe_o.last_op          <= 1'b0;
    end else begin
      // Valid pipeline output if we are valid AND the
      // alignment buffer has a valid instruction
      if (if_valid_o && id_ready_i) begin
        if_id_pipe_o.instr_valid      <= 1'b1;
        if_id_pipe_o.instr_meta       <= instr_meta_n;
        if_id_pipe_o.illegal_c_insn   <= dummy_insert ? 1'b0 : illegal_c_insn;

        if_id_pipe_o.priv_lvl         <= prefetch_priv_lvl;
        if_id_pipe_o.trigger_match    <= dummy_insert ? 1'b0 : trigger_match_i;
        if_id_pipe_o.xif_id           <= xif_id;
        if_id_pipe_o.last_op          <= last_op;

        // No PC update for tablejump pointer, PC of instruction itself is needed later.
        // No update to the meta compressed, as this is used in calculating the link address.
        //   Any pointer could change instr_compressed_int and cause a wrong link address.
        // No update to tbljmp flag, we want flag to be high for both operations.
        if (!prefetch_is_tbljmp_ptr) begin
          if_id_pipe_o.pc                    <= pc_if_o;
          if_id_pipe_o.instr_meta.compressed <= dummy_insert ? 1'b0 : instr_compressed_int;
          if_id_pipe_o.instr_meta.tbljmp     <= tbljmp;

          // Only update compressed_instr for compressed instructions
          if (instr_compressed_int) begin
            if_id_pipe_o.compressed_instr      <= prefetch_instr.bus_resp.rdata[15:0];
          end
        end

        // For pointers, we want to update the if_id_pipe.ptr field, but also any associated error conditions from bus or MPU.
        if (ptr_in_if_o) begin
          // Update pointer value
          if_id_pipe_o.ptr                <= instr_decompressed.bus_resp.rdata;

          // Need to update bus error status and mpu status, but may omit the 32-bit instruction word
          if_id_pipe_o.instr.bus_resp.err <= instr_decompressed.bus_resp.err;
          if_id_pipe_o.instr.mpu_status   <= instr_decompressed.mpu_status;
        end else begin
          // Regular instruction, update the whole instr field
          if_id_pipe_o.instr          <= dummy_insert ? dummy_instr : instr_decompressed;;
        end
      end else if (id_ready_i) begin
        if_id_pipe_o.instr_valid      <= 1'b0;
      end
    end
  end

  cv32e40s_compressed_decoder
  #(
      .ZC_EXT ( ZC_EXT ),
      .B_EXT  ( B_EXT  ),
      .M_EXT  ( M_EXT  )
  )
  compressed_decoder_i
  (
    .instr_i            ( prefetch_instr          ),
    .instr_is_ptr_i     ( ptr_in_if_o             ),
    .mstateen0_i        ( mstateen0_i             ),
    .priv_lvl_i         ( prefetch_priv_lvl       ),
    .instr_o            ( instr_decompressed      ),
    .is_compressed_o    ( instr_compressed_int    ),
    .illegal_instr_o    ( illegal_c_insn          ),
    .tbljmp_o           ( tbljmp_raw              )
  );

  // tbljmp below is used in calculating 'last_op'. If we have a faulted fetch, the instruction word may be anything
  // (not cleared on faulted fetches). A faulted fetch should not be decoded to anything and thus tbljmp is cleared.
  // One could instead set the instruction word itself to all zeros or another illegal instruction on known fetch faults,
  // but this may impact timing more than suppressing control bits.
  // Also clear tbljmp for dummy instructions, as this signal is used to calculate last_op.
  assign tbljmp = (instr_decompressed.bus_resp.err || (instr_decompressed.mpu_status != MPU_OK)) ? 1'b0 :
                  dummy_insert ? 1'b0 : tbljmp_raw;


  //---------------------------------------------------------------------------
  // Dummy Instruction Insertion
  //---------------------------------------------------------------------------

  generate
    if (DUMMY_INSTRUCTIONS) begin : gen_dummy_instr
      logic instr_issued; // Used to count issued instructions between dummy instructions
      assign instr_issued = if_valid_o && id_ready_i;

      cv32e40s_dummy_instr
        dummy_instr_i
          (.clk            ( clk            ),
           .rst_n          ( rst_n          ),
           .instr_issued_i ( instr_issued   ),
           .ctrl_fsm_i     ( ctrl_fsm_i     ),
           .xsecure_ctrl_i ( xsecure_ctrl_i ),
           .dummy_insert_o ( dummy_insert   ),
           .dummy_instr_o  ( dummy_instr    )
           );

    end : gen_dummy_instr
    else begin : gen_no_dummy_instr
      assign dummy_insert = 1'b0;
      assign dummy_instr  = '0;
    end : gen_no_dummy_instr
  endgenerate


  //---------------------------------------------------------------------------
  // eXtension interface
  //---------------------------------------------------------------------------

  generate
    if (X_EXT) begin : x_ext

      // TODO: implement offloading of compressed instruction
      assign xif_compressed_if.compressed_valid = '0;
      assign xif_compressed_if.compressed_req   = '0;

      // TODO: assert that the oustanding IDs are unique
      assign xif_id = xif_offloading_id_i ? if_id_pipe_o.xif_id + 1 : if_id_pipe_o.xif_id;

    end else begin : no_x_ext

      assign xif_compressed_if.compressed_valid = '0;
      assign xif_compressed_if.compressed_req   = '0;

      assign xif_id                             = '0;

    end
  endgenerate

endmodule
