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
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MULT: computes normal multiplications                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_ex_stage import cv32e40s_pkg::*;
#(
  parameter b_ext_e B_EXT = B_NONE,
  parameter m_ext_e M_EXT = M
)
(
  input  logic        clk,
  input  logic        rst_n,

  // IF/ID pipeline
  input if_id_pipe_t  if_id_pipe_i,

  // ID/EX pipeline
  input id_ex_pipe_t  id_ex_pipe_i,

  // CSR interface
  input  logic [31:0] csr_rdata_i,
  input  logic        csr_illegal_i,
  input  logic        csr_mnxti_read_i,
  input  csr_hz_t     csr_hz_i,

  // EX/WB pipeline
  output ex_wb_pipe_t ex_wb_pipe_o,

  // From controller FSM
  input  ctrl_fsm_t   ctrl_fsm_i,

  // Xsecure control
  input xsecure_ctrl_t xsecure_ctrl_i,

  // Register file forwarding signals (to ID)
  output logic [31:0] rf_wdata_o,

  // To IF: Jump and branch target and decision
  output logic        branch_decision_o,
  output logic [31:0] branch_target_o,

  // LSU handshake interface
  input  logic        lsu_valid_i,
  output logic        lsu_ready_o,
  output logic        lsu_valid_o,
  input  logic        lsu_ready_i,
  input  logic        lsu_split_i,      // LSU is performing first part of a misaligned/split instruction
  input  logic        lsu_last_op_i,
  input  logic        lsu_first_op_i,

  // Stage ready/valid
  output logic        ex_ready_o,       // EX stage is ready for new data
  output logic        ex_valid_o,       // EX stage has valid (non-bubble) data for next stage
  input  logic        wb_ready_i,       // WB stage is ready for new data

  output logic        last_op_o
);

  // Ready and valid signals
  logic           instr_valid;
  logic           alu_ready;
  logic           alu_valid;
  logic           csr_ready;
  logic           csr_valid;
  logic           sys_ready;
  logic           sys_valid;
  logic           mul_ready;
  logic           mul_valid;
  logic           div_ready;
  logic           div_valid;

  // Result signals
  logic [31:0]    alu_result;
  logic           alu_cmp_result;
  logic [31:0]    mul_result;
  logic [31:0]    div_result;

  // Gated enable signals factoring in instr_valid)
  logic           lsu_en_gated;

  // Divider signals
  logic           div_en;               // Not affected by instr_valid (kill/halt)
  logic           div_clz_en;
  logic [31:0]    div_clz_data_rev;
  logic [5:0]     div_clz_result;
  logic           div_shift_en;
  logic [5:0]     div_shift_amt;
  logic [31:0]    div_op_b_shifted;

  // Multiplier signals
  logic           mul_en;

  // Misc signals
  logic           forced_nop; // Exception or trigger forces this instruction to be a nop with no enables active
  logic           forced_nop_valid;
  logic           first_op;

  assign instr_valid = id_ex_pipe_i.instr_valid && !ctrl_fsm_i.kill_ex && !ctrl_fsm_i.halt_ex;

  // The multiplier and divider both factor in halt_ex and kill_ex.
  // MUL/DIV instructions in flight will keep state while halted, and reset state on kill.
  assign mul_en = id_ex_pipe_i.mul_en && id_ex_pipe_i.instr_valid; // Valid MUL in EX, not affected by kill/halt
  assign div_en = id_ex_pipe_i.div_en && id_ex_pipe_i.instr_valid; // Valid DIV in EX, not affected by kill/halt

  // The lsu_en_gated factors in halt_ex and kill_ex via instr_valid.
  // A halted or killed LSU instruction must not generate a data_req to ensure no OBI protocol is violated.
  assign lsu_en_gated = id_ex_pipe_i.lsu_en && instr_valid; // Factoring in instr_valid to suppress bus transactions on kill/halt


  // Exception happened during IF or ID, or trigger match in ID (converted to NOP).
  // signal needed for ex_valid to go high in such cases
  assign forced_nop = (id_ex_pipe_i.illegal_insn                     ||
                       id_ex_pipe_i.instr.bus_resp.integrity_err     ||
                       id_ex_pipe_i.instr.bus_resp.err               ||
                       (id_ex_pipe_i.instr.mpu_status != MPU_OK)     ||
                       |id_ex_pipe_i.trigger_match)                  &&
                      id_ex_pipe_i.instr_valid;

  // ALU write port mux
  always_comb
  begin
    // There is no need to use gated versions of alu_en, mul_en, etc. as rf_wdata_o will be ignored
    // for invalid instructions (as the register file write enable will be suppressed).
    unique case (1'b1)
      id_ex_pipe_i.alu_en : rf_wdata_o = alu_result;
      id_ex_pipe_i.mul_en : rf_wdata_o = mul_result;
      id_ex_pipe_i.div_en : rf_wdata_o = div_result;
      id_ex_pipe_i.csr_en : rf_wdata_o = csr_rdata_i;
      default             : rf_wdata_o = alu_result;
    endcase
  end

  // Branch handling
  generate
    if (SECURE) begin : secure_branches
      always_comb begin
        if (xsecure_ctrl_i.cpuctrl.dataindtiming) begin
          // Data independent timing enabled, always "take" branch.
          branch_decision_o = 1'b1;

          if (alu_cmp_result) begin
            // Branch was taken
            branch_target_o = id_ex_pipe_i.operand_c;
          end
          else begin
            // ID and EX stage both contain the branch instruction, target addr is in IF.
            // Using the IF stage PC as observed when the branch was in ID,
            // flopped to the id_ex_pipe. This ensures that branch_target_o
            // remains stable for all parts of a branch when dataindependent
            // timing is turned on.
            branch_target_o = id_ex_pipe_i.pc_next;
          end
        end
        else begin
          // Data independent timing not enabled
          branch_decision_o = alu_cmp_result;
          branch_target_o   = id_ex_pipe_i.operand_c;
        end
      end
    end else begin : regular_branches //!SECURE
      assign branch_decision_o = alu_cmp_result;
      assign branch_target_o   = id_ex_pipe_i.operand_c;
    end
  endgenerate

  // Detect last operation. Both last_op and last_sec_op must be true
  // Both parts of a split misaligned load/store will reach WB, but only the second half will be marked with "last_op"
  assign last_op_o = id_ex_pipe_i.lsu_en ? (lsu_last_op_i && id_ex_pipe_i.last_op) : id_ex_pipe_i.last_op;

  assign first_op  = id_ex_pipe_i.lsu_en ? (lsu_first_op_i && id_ex_pipe_i.first_op) : id_ex_pipe_i.first_op;

  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  cv32e40s_alu
    #(.B_EXT(B_EXT))
  alu_i
  (
    .operator_i          ( id_ex_pipe_i.alu_operator     ),
    .operand_a_i         ( id_ex_pipe_i.alu_operand_a    ),
    .operand_b_i         ( id_ex_pipe_i.alu_operand_b    ),
    .muldiv_operand_b_i  ( id_ex_pipe_i.muldiv_operand_b ),

    // ALU CLZ interface
    .div_clz_en_i        ( div_clz_en                    ),
    .div_clz_data_rev_i  ( div_clz_data_rev              ),
    .div_clz_result_o    ( div_clz_result                ),

    // ALU shifter interface
    .div_shift_en_i      ( div_shift_en                  ),
    .div_shift_amt_i     ( div_shift_amt                 ),
    .div_op_b_shifted_o  ( div_op_b_shifted              ),

    // Result(s)
    .result_o            ( alu_result                    ),
    .cmp_result_o        ( alu_cmp_result                )
  );

  ////////////////////////////////////////////////////
  //  ____ _____     __     __  ____  _____ __  __  //
  // |  _ \_ _\ \   / /    / / |  _ \| ____|  \/  | //
  // | | | | | \ \ / /    / /  | |_) |  _| | |\/| | //
  // | |_| | |  \ V /    / /   |  _ <| |___| |  | | //
  // |____/___|  \_/    /_/    |_| \_\_____|_|  |_| //
  //                                                //
  ////////////////////////////////////////////////////

  generate
    if (M_EXT == M) begin: div

      cv32e40s_div div_i
        (
         .clk                ( clk                                  ),
         .rst_n              ( rst_n                                ),

         // Input IF
         .data_ind_timing_i  ( xsecure_ctrl_i.cpuctrl.dataindtiming ),
         .operator_i         ( id_ex_pipe_i.div_operator            ),
         .op_a_i             ( id_ex_pipe_i.muldiv_operand_a        ),
         .op_b_i             ( id_ex_pipe_i.muldiv_operand_b        ),

         // ALU CLZ interface
         .alu_clz_result_i   ( div_clz_result                       ),
         .alu_clz_en_o       ( div_clz_en                           ),
         .alu_clz_data_rev_o ( div_clz_data_rev                     ),

         // ALU shifter interface
         .alu_op_b_shifted_i ( div_op_b_shifted                     ),
         .alu_shift_en_o     ( div_shift_en                         ),
         .alu_shift_amt_o    ( div_shift_amt                        ),

         // Result
         .result_o           ( div_result                           ),

         // Handshakes
         .halt_i             ( ctrl_fsm_i.halt_ex                   ),
         .kill_i             ( ctrl_fsm_i.kill_ex                   ),
         .valid_i            ( div_en                               ),
         .ready_o            ( div_ready                            ),
         .valid_o            ( div_valid                            ),
         .ready_i            ( wb_ready_i                           )
         );

    end
    else begin: no_div

      // No divider, tie off outputs
      assign div_clz_en       = 1'b0;
      assign div_clz_data_rev = 32'h0;
      assign div_shift_en     = 1'b0;
      assign div_shift_amt    = 6'h0;
      assign div_ready        = 1'b1;
      assign div_valid        = 1'b0;
      assign div_result       = 32'h0;

    end
  endgenerate

  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  generate
    if (M_EXT != M_NONE) begin: mul

      cv32e40s_mult mult_i
        (
         .clk             ( clk                           ),
         .rst_n           ( rst_n                         ),

         .operator_i      ( id_ex_pipe_i.mul_operator     ),
         .signed_mode_i   ( id_ex_pipe_i.mul_signed_mode  ),
         .op_a_i          ( id_ex_pipe_i.muldiv_operand_a ),
         .op_b_i          ( id_ex_pipe_i.muldiv_operand_b ),

         // Result
         .result_o        ( mul_result                    ),

         .halt_i          ( ctrl_fsm_i.halt_ex            ),
         .kill_i          ( ctrl_fsm_i.kill_ex            ),

         // Handshakes
         .valid_i         ( mul_en                        ),
         .ready_o         ( mul_ready                     ),
         .valid_o         ( mul_valid                     ),
         .ready_i         ( wb_ready_i                    )
         );

    end
    else begin: no_mul

      // No multiplier, tie off outputs
      assign mul_result = 32'h0;
      assign mul_ready  = 1'b1;
      assign mul_valid  = 1'b0;

    end
  endgenerate

  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      ex_wb_pipe_o.instr_valid        <= 1'b0;
      ex_wb_pipe_o.rf_we              <= 1'b0;
      ex_wb_pipe_o.rf_waddr           <= '0;
      ex_wb_pipe_o.rf_wdata           <= 32'b0;
      ex_wb_pipe_o.pc                 <= 32'h0;
      ex_wb_pipe_o.instr              <= INST_RESP_RESET_VAL;
      ex_wb_pipe_o.instr_meta         <= '0;

      ex_wb_pipe_o.illegal_insn       <= 1'b0;

      ex_wb_pipe_o.alu_jmp_qual       <= 1'b0;
      ex_wb_pipe_o.alu_bch_qual       <= 1'b0;
      ex_wb_pipe_o.alu_bch_taken_qual <= 1'b0;

      ex_wb_pipe_o.sys_en             <= 1'b0;
      ex_wb_pipe_o.sys_dret_insn      <= 1'b0;
      ex_wb_pipe_o.sys_ebrk_insn      <= 1'b0;
      ex_wb_pipe_o.sys_ecall_insn     <= 1'b0;
      ex_wb_pipe_o.sys_fence_insn     <= 1'b0;
      ex_wb_pipe_o.sys_fencei_insn    <= 1'b0;
      ex_wb_pipe_o.sys_mret_insn      <= 1'b0;
      ex_wb_pipe_o.sys_wfi_insn       <= 1'b0;
      ex_wb_pipe_o.sys_wfe_insn       <= 1'b0;

      ex_wb_pipe_o.trigger_match      <= '0;

      ex_wb_pipe_o.lsu_en             <= 1'b0;
      ex_wb_pipe_o.csr_en             <= 1'b0;
      ex_wb_pipe_o.csr_op             <= CSR_OP_READ;
      ex_wb_pipe_o.csr_addr           <= 12'h000;
      ex_wb_pipe_o.csr_wdata          <= 32'h00000000;
      ex_wb_pipe_o.csr_mnxti_access   <= 1'b0;
      ex_wb_pipe_o.first_op           <= 1'b0;
      ex_wb_pipe_o.last_op            <= 1'b0;
      ex_wb_pipe_o.last_sec_op        <= 1'b0;
      ex_wb_pipe_o.abort_op           <= 1'b0;
      ex_wb_pipe_o.csr_impl_wr        <= 1'b0;

      ex_wb_pipe_o.priv_lvl           <= PRIV_LVL_M;
    end
    else
    begin
      if (ex_valid_o && wb_ready_i) begin
        ex_wb_pipe_o.instr_valid <= 1'b1;
        ex_wb_pipe_o.priv_lvl    <= id_ex_pipe_i.priv_lvl;
        ex_wb_pipe_o.last_op     <= last_op_o;
        ex_wb_pipe_o.last_sec_op <= id_ex_pipe_i.last_sec_op;
        ex_wb_pipe_o.first_op    <= first_op;
        ex_wb_pipe_o.abort_op    <= id_ex_pipe_i.abort_op; // MPU exceptions and watchpoint triggers have WB timing and will not impact ex_wb_pipe.abort_op
        // Deassert rf_we in case of illegal csr instruction or when the first half of a misaligned/split LSU goes to WB.
        // Also deassert if CSR was accepted both by eXtension if and pipeline
        ex_wb_pipe_o.rf_we       <= (csr_illegal_i || lsu_split_i) ? 1'b0 : id_ex_pipe_i.rf_we;
        ex_wb_pipe_o.lsu_en      <= id_ex_pipe_i.lsu_en;

        if (id_ex_pipe_i.rf_we) begin
          ex_wb_pipe_o.rf_waddr <= id_ex_pipe_i.rf_waddr;
          if (!id_ex_pipe_i.lsu_en) begin
            ex_wb_pipe_o.rf_wdata <= rf_wdata_o;
          end
        end

        ex_wb_pipe_o.alu_jmp_qual       <= id_ex_pipe_i.alu_jmp && id_ex_pipe_i.alu_en;
        ex_wb_pipe_o.alu_bch_qual       <= id_ex_pipe_i.alu_bch && id_ex_pipe_i.alu_en;
        ex_wb_pipe_o.alu_bch_taken_qual <= id_ex_pipe_i.alu_bch && id_ex_pipe_i.alu_en && branch_decision_o;

        // Update signals for CSR access in WB
        // deassert csr_en in case of an internal illegal csr instruction
        // to avoid writing to CSRs inside the core.
        ex_wb_pipe_o.csr_en     <= csr_illegal_i ? 1'b0 : id_ex_pipe_i.csr_en;
        if (id_ex_pipe_i.csr_en) begin
          // The ex_wb_pipe_o.csr_addr is used (for RVFI) even for CSR instructions that do not write to the CSR
          // Any future clock gating improvements to ex_wb_pipe.csr_addr must take this into account.
          ex_wb_pipe_o.csr_addr         <= id_ex_pipe_i.alu_operand_b[11:0];
          ex_wb_pipe_o.csr_wdata        <= id_ex_pipe_i.alu_operand_a;
          ex_wb_pipe_o.csr_op           <= id_ex_pipe_i.csr_op;
          ex_wb_pipe_o.csr_mnxti_access <= csr_mnxti_read_i;
          ex_wb_pipe_o.csr_impl_wr      <= csr_hz_i.impl_wr_ex;
        end

        // Propagate signals needed for exception handling in WB
        ex_wb_pipe_o.pc             <= id_ex_pipe_i.pc;
        ex_wb_pipe_o.instr          <= id_ex_pipe_i.instr;
        ex_wb_pipe_o.instr_meta     <= id_ex_pipe_i.instr_meta;

        ex_wb_pipe_o.sys_en            <= id_ex_pipe_i.sys_en;
        if (id_ex_pipe_i.sys_en) begin
          ex_wb_pipe_o.sys_dret_insn   <= id_ex_pipe_i.sys_dret_insn;
          ex_wb_pipe_o.sys_ebrk_insn   <= id_ex_pipe_i.sys_ebrk_insn;
          ex_wb_pipe_o.sys_ecall_insn  <= id_ex_pipe_i.sys_ecall_insn;
          ex_wb_pipe_o.sys_fence_insn  <= id_ex_pipe_i.sys_fence_insn;
          ex_wb_pipe_o.sys_fencei_insn <= id_ex_pipe_i.sys_fencei_insn;
          ex_wb_pipe_o.sys_mret_insn   <= id_ex_pipe_i.sys_mret_insn;
          ex_wb_pipe_o.sys_wfi_insn    <= id_ex_pipe_i.sys_wfi_insn;
          ex_wb_pipe_o.sys_wfe_insn    <= id_ex_pipe_i.sys_wfe_insn;
        end

        // CSR illegal instruction detected in this stage, OR'ing in the status
        ex_wb_pipe_o.illegal_insn   <= id_ex_pipe_i.illegal_insn || csr_illegal_i;
        ex_wb_pipe_o.trigger_match  <= id_ex_pipe_i.trigger_match;

      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we introduce a bubble
        ex_wb_pipe_o.instr_valid <= 1'b0;
      end
    end
  end

  // LSU inputs are valid when LSU is enabled; LSU outputs need to remain valid until downstream stage is ready
  // If a trigger matches LSU address, this valid will be gated off inside the load_store_unit to prevent the instruction
  // from accessing the bus.
  assign lsu_valid_o = lsu_en_gated;
  assign lsu_ready_o = wb_ready_i;

  // ALU is single-cycle and output is therefore immediately valid (no handshake to optimize timing)
  assign alu_valid = 1'b1;
  assign alu_ready = wb_ready_i;

  // CSR is single-cycle and output is therefore immediately valid (no handshake to optimize timing)
  assign csr_valid = 1'b1;
  assign csr_ready = wb_ready_i;

  // SYS instructions (ebreak, wfi, etc.) are single-cycle (and have no result output) (no handshake to optimize timing)
  assign sys_valid = 1'b1;
  assign sys_ready = wb_ready_i;

  // Forced nop (exceptions or trigger matches) will pass through the EX stage in a single cycle.
  assign forced_nop_valid = 1'b1;

  // CLIC and mret pointers pass through the EX stage in a single cycle
  assign clic_ptr_valid = 1'b1;
  assign mret_ptr_valid = 1'b1;

  // EX stage is ready immediately when killed and otherwise when its functional units are ready,
  // unless the stage is being halted. The late (data_rvalid_i based) downstream wb_ready_i signal
  // fans into the ready signals of all functional units.

  assign ex_ready_o = ctrl_fsm_i.kill_ex || (alu_ready && csr_ready && sys_ready && mul_ready && div_ready && lsu_ready_i && !ctrl_fsm_i.halt_ex);

  assign ex_valid_o = ((id_ex_pipe_i.alu_en && alu_valid)                   ||
                       (id_ex_pipe_i.csr_en && csr_valid)                   ||
                       (id_ex_pipe_i.sys_en && sys_valid)                   ||
                       (id_ex_pipe_i.mul_en && mul_valid)                   ||
                       (id_ex_pipe_i.div_en && div_valid)                   ||
                       (id_ex_pipe_i.lsu_en && lsu_valid_i)                 ||
                       (id_ex_pipe_i.instr_meta.clic_ptr && clic_ptr_valid) ||
                       (id_ex_pipe_i.instr_meta.mret_ptr && mret_ptr_valid) ||
                       (forced_nop && forced_nop_valid)
                      ) && instr_valid;

endmodule
