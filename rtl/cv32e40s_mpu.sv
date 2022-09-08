// Copyright 2021 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    MPU (Memory Protection Unit)                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_mpu import cv32e40s_pkg::*;
  #(  parameter bit          IF_STAGE                     = 1,
      parameter int          OUTSTND_CNT_WIDTH            = 2,
      parameter type         CORE_REQ_TYPE                = obi_inst_req_t,
      parameter type         CORE_RESP_TYPE               = inst_resp_t,
      parameter type         BUS_RESP_TYPE                = obi_inst_resp_t,
      parameter int          PMP_GRANULARITY              = 0,
      parameter int          PMP_NUM_REGIONS              = 0,
      parameter int          PMA_NUM_REGIONS              = 0,
      parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT})
  (
   input logic  clk,
   input logic  rst_n,

   input logic  misaligned_access_i, // Indicate that ongoing access is part of a misaligned access

   // Interface towards bus interface
   input logic  bus_trans_ready_i,
   output logic bus_trans_valid_o,
   output       CORE_REQ_TYPE bus_trans_o,

   input logic  bus_resp_valid_i,
   input        BUS_RESP_TYPE bus_resp_i,

   // Interface towards core
   input logic  core_trans_valid_i,
   output logic core_trans_ready_o,
   input        CORE_REQ_TYPE core_trans_i,

   output logic core_resp_valid_o,
   output       CORE_RESP_TYPE core_resp_o,

   // PMP CSR's
   input        pmp_csr_t csr_pmp_i,

   // Privilege mode
   input              privlvl_t priv_lvl_i,

   // Indication from the core that there will be one pending transaction in the next cycle
   input logic                         core_one_txn_pend_n,
   // Core side counter for outstanding transactions
   input logic [OUTSTND_CNT_WIDTH-1:0] core_outstnd_cnt_q,

   // Indication from the core that MPU errors should be reported after all in flight transactions
   // are complete (default behavior for main core requests, but not used for XIF requests)
   input logic  core_mpu_err_wait_i,

   // Report MPU errors to the core immediatly (used in case core_mpu_err_wait_i is not asserted)
   output logic core_mpu_err_o
   );

  localparam bit PMP = SECURE;

  logic        pma_err;
  logic        pma_integrity;
  logic        pmp_err;
  logic        mpu_err;
  logic        mpu_block_core;
  logic        mpu_block_bus;
  logic        mpu_err_trans_valid;
  logic        mpu_err_trans_ready;
  mpu_status_e mpu_status;
  mpu_state_e  state_q, state_n;
  logic        bus_trans_cacheable;
  logic        bus_trans_bufferable;
  logic        core_trans_we;
  pmp_req_e    pmp_req_type;
  logic [33:0] pmp_req_addr;
  logic        instr_fetch_access;
  logic        load_access;

  // Integrity FIFO is 1 bit deeper than the maximum value of core_outstnd_cnt_q
  // Bit 0 is tied low to enable direct use of core_outstnd_cnt_q to pick correct FIFO index.
  localparam INT_FIFO_DEPTH = (2**OUTSTND_CNT_WIDTH);
  logic [INT_FIFO_DEPTH-1:0] integrity_fifo_q;

  // FSM that will "consume" transfers failing PMA or PMP checks.
  // Upon failing checks, this FSM will prevent the transfer from going out on the bus
  // and wait for all in flight bus transactions to complete while blocking new transfers.
  // When all in flight transactions are complete, it will respond with the correct status before
  // allowing new transfers to go through.
  // The input signal core_one_txn_pend_n indicates that there, from the core's point of view,
  // will be one pending transaction in the next cycle. Upon MPU error, this transaction
  // will be completed by this FSM
  always_comb begin

    state_n             = state_q;
    mpu_status          = MPU_OK;
    mpu_block_core      = 1'b0;
    mpu_block_bus       = 1'b0;
    mpu_err_trans_valid = 1'b0;
    mpu_err_trans_ready = 1'b0;

    case(state_q)
      MPU_IDLE: begin
        if (mpu_err && core_trans_valid_i) begin

          // Block transfer from going out on the bus.
          mpu_block_bus  = 1'b1;

          // Signal to the core that the transfer was accepted (but will be consumed by the MPU)
          mpu_err_trans_ready = 1'b1;

          if (core_mpu_err_wait_i) begin
            if(core_trans_we) begin
              // MPU error on write
              state_n = core_one_txn_pend_n ? MPU_WR_ERR_RESP : MPU_WR_ERR_WAIT;
            end
            else begin
              // MPU error on read
              state_n = core_one_txn_pend_n ? MPU_RE_ERR_RESP : MPU_RE_ERR_WAIT;
            end
          end

        end
      end
      MPU_RE_ERR_WAIT, MPU_WR_ERR_WAIT: begin

        // Block new transfers while waiting for in flight transfers to complete
        mpu_block_bus  = 1'b1;
        mpu_block_core = 1'b1;

        if (core_one_txn_pend_n) begin
          state_n = (state_q == MPU_RE_ERR_WAIT) ? MPU_RE_ERR_RESP : MPU_WR_ERR_RESP;
        end
      end
      MPU_RE_ERR_RESP, MPU_WR_ERR_RESP: begin

        // Keep blocking new transfers
        mpu_block_bus  = 1'b1;
        mpu_block_core = 1'b1;

        // Set up MPU error response towards the core
        mpu_err_trans_valid = 1'b1;
        mpu_status = (state_q == MPU_RE_ERR_RESP) ? MPU_RE_FAULT : MPU_WR_FAULT;

        // Go back to IDLE uncoditionally.
        // The core is expected to always be ready for the response
        state_n = MPU_IDLE;

      end
      default: ;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      state_q <= MPU_IDLE;
    end
    else begin
      state_q <= state_n;
    end
  end

  // FIFO to keep track of integrity attribute for outstanding transactions
  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      integrity_fifo_q <= {INT_FIFO_DEPTH{1'b0}};
    end
    else begin
      if (core_trans_valid_i && core_trans_ready_o) begin
        // Accepted address phase, populate FIFO with PMA integrity attribute
        integrity_fifo_q <= {integrity_fifo_q[INT_FIFO_DEPTH-2:1], pma_integrity, 1'b0};
      end
    end
  end

  // Forward transaction request towards bus interface
  assign bus_trans_valid_o = core_trans_valid_i && !mpu_block_bus;

  always_comb begin
    bus_trans_o            = core_trans_i;
    bus_trans_o.memtype[0] = bus_trans_bufferable;
    bus_trans_o.memtype[1] = bus_trans_cacheable;
  end

  // Forward transaction response towards core
  assign core_resp_valid_o      = bus_resp_valid_i || mpu_err_trans_valid;
  assign core_resp_o.bus_resp   = bus_resp_i;
  assign core_resp_o.mpu_status = mpu_status;
  assign core_resp_o.integrity  = integrity_fifo_q[core_outstnd_cnt_q];

  // Report MPU errors to the core immediatly
  assign core_mpu_err_o = mpu_err;

  // Signal ready towards core
  assign core_trans_ready_o = (bus_trans_ready_i && !mpu_block_core) || mpu_err_trans_ready;

  // PMA - Physical Memory Attribution
  cv32e40s_pma
    #(.PMA_NUM_REGIONS          ( PMA_NUM_REGIONS      ),
      .PMA_CFG                  ( PMA_CFG              )
  )
  pma_i
    (
    .trans_addr_i               ( core_trans_i.addr    ),
    .instr_fetch_access_i       ( instr_fetch_access   ),
    .misaligned_access_i        ( misaligned_access_i  ),
    .load_access_i              ( load_access          ),
    .pma_err_o                  ( pma_err              ),
    .pma_integrity_o            ( pma_integrity        ),
    .pma_bufferable_o           ( bus_trans_bufferable ),
    .pma_cacheable_o            ( bus_trans_cacheable  )
  );

  assign pmp_req_addr = {2'b00, core_trans_i.addr};

  generate
    if (PMP) begin: pmp
      cv32e40s_pmp
        #(// Parameters
          .PMP_GRANULARITY                  (PMP_GRANULARITY),
          .PMP_NUM_REGIONS                  (PMP_NUM_REGIONS))
      pmp_i
        (// Outputs
         .pmp_req_err_o                     (pmp_err),
         // Inputs
         .clk                               (clk),
         .rst_n                             (rst_n),
         .pmp_req_type_i                    (pmp_req_type),
         .csr_pmp_i                         (csr_pmp_i),
         .priv_lvl_i                        (priv_lvl_i),
         .pmp_req_addr_i                    (pmp_req_addr));
    end
    else begin: no_pmp
      assign pmp_err = 1'b0;
    end
  endgenerate

  assign mpu_err = pmp_err || pma_err;

  // Writes are only supported on the data interface
  // Tie to 1'b0 if this MPU is instantiatied in the IF stage
  generate
    if (IF_STAGE) begin: mpu_if
      assign instr_fetch_access = 1'b1;
      assign load_access        = 1'b0;
      assign core_trans_we      = 1'b0;
      assign pmp_req_type       = PMP_ACC_EXEC;
    end
    else begin: mpu_lsu
      assign instr_fetch_access = 1'b0;
      assign load_access        = !core_trans_i.we;
      assign core_trans_we      = core_trans_i.we;
      assign pmp_req_type       = core_trans_we ? PMP_ACC_WRITE : PMP_ACC_READ;
    end
  endgenerate

// TODO:OE any way to check that the 2nd access of a failed misalgn will not reach the MPU?

endmodule
