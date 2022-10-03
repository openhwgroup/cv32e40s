// Copyright 2022 Silicon Labs, Inc.
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
// Engineer:       Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40s_obi_integrity_check_fifo                          //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Module checks grant parity,  synchronizes parity faults    //
//                 and integrity bit from the incoming transaction from the   //
//                 address phase to the reponse phase of the OBI transaction  //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_obi_integrity_fifo import cv32e40s_pkg::*;
#(  parameter int unsigned  MAX_OUTSTANDING   = 2,
    parameter type RESP_TYPE = obi_inst_resp_t
 )
(
  input  logic                       clk,
  input  logic                       rst_n,

  // gnt parity error
  input  logic                        gntpar_err_i,

  // Transaction inputs
  input  logic                        trans_integrity_i,
  input  logic                        trans_we_i,

  // Xsecure
  input xsecure_ctrl_t                xsecure_ctrl_i,

  // Response phase properties
  output logic                        gntpar_err_resp_o,
  output logic                        integrity_resp_o,
  output logic                        rchk_err_resp_o,

  // Protocol hardening error output
  output logic                        protocol_err_o,

  // OBI handshake signals
  input  logic                        obi_req_i,
  input  logic                        obi_gnt_i,
  input  logic                        obi_rvalid_i,
  input  RESP_TYPE                    obi_resp_i

);

  localparam OUTSTND_CNT_WIDTH = $clog2(MAX_OUTSTANDING+1);

  typedef struct packed {
    logic        integrity;
    logic        gnterr;
    logic        store;
  } fifo_t;

  // FIFO is 1 bit deeper than the maximum value of bus_cnt_i
  // Index 0 is tied low to enable direct use of bus_cnt_i to pick correct FIFO index.
  fifo_t [MAX_OUTSTANDING:0] fifo_q;
  fifo_t fifo_input;

  // Parity and rchk error signals
  logic       gntpar_err_q;                           // gnt parity error (sticky for waited grants)
  logic [1:0] rchk_en;                                // Rchk enable. bit0: for bits 3:0, bit1: bit 4 of rchk
  logic       resp_is_store;

  // Outstanding counter signals
  logic [OUTSTND_CNT_WIDTH-1:0] cnt_q;                        // Transaction counter
  logic [OUTSTND_CNT_WIDTH-1:0] next_cnt;                     // Next value for cnt_q
  logic                         count_up;
  logic                         count_down;



  /////////////////////////////////////////////////////////////
  // Outstanding transactions counter
  // Used for tracking parity errors and integrity attribute
  /////////////////////////////////////////////////////////////
  assign count_up = obi_req_i && obi_gnt_i;  // Increment upon accepted transfer request
  assign count_down = obi_rvalid_i;                       // Decrement upon accepted transfer response

  always_comb begin
    case ({count_up, count_down})
      2'b00 : begin
        next_cnt = cnt_q;
      end
      2'b01 : begin
        next_cnt = cnt_q - 1'b1;
      end
      2'b10 : begin
        next_cnt = cnt_q + 1'b1;
      end
      2'b11 : begin
        next_cnt = cnt_q;
      end
      default:;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= next_cnt;
    end
  end

  /////////////////
  // Integrity
  /////////////////

  // gntpar_err_q is a sticky gnt error bit.
  // Any gnt parity error detected during req will be remembered and propagated
  // to the fifo when the address phase ends.
  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      gntpar_err_q <= '0;
    end
    else begin
      if (obi_req_i) begin
        // Address phase active, set sticky gntpar_err if not granted
        // When granted, sticky bit will be cleared for the next address phase
        if (!obi_gnt_i) begin
          gntpar_err_q <= gntpar_err_i || gntpar_err_q;
        end else begin
          gntpar_err_q <= 1'b0;
        end
      end
    end
  end

  // FIFO to keep track of gnt parity errors, integrity bit from PMA and if transaction is load or store for outstanding transactions

  assign fifo_input.integrity = trans_integrity_i;
  assign fifo_input.gnterr    = (gntpar_err_i || gntpar_err_q);
  assign fifo_input.store     = trans_we_i;

  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      fifo_q <= '0;
    end
    else begin
      if (obi_req_i && obi_gnt_i) begin
        // Accepted address phase, populate FIFO with gnt parity error and PMA integrity bit
        fifo_q <= {fifo_q[MAX_OUTSTANDING-1:1], fifo_input, 3'b000};
      end
    end
  end

  assign integrity_resp_o  = fifo_q[cnt_q].integrity;
  assign resp_is_store     = fifo_q[cnt_q].store;
  assign gntpar_err_resp_o = fifo_q[cnt_q].gnterr;

  // Enable rchk when in response phase and cpuctrl.integrity is set
  // Only enable check of bits 3:0 (rchk_en[0]) for loads
  assign rchk_en[0] = obi_rvalid_i && xsecure_ctrl_i.cpuctrl.integrity && !resp_is_store;
  assign rchk_en[1] = obi_rvalid_i && xsecure_ctrl_i.cpuctrl.integrity;

  // Recompute and check rchk
  cv32e40s_rchk_check
  #(
      .RESP_TYPE (RESP_TYPE)
  )
  rchk_i
  (
    .resp_i   (obi_resp_i     ),
    .enable_i (rchk_en        ),
    .err_o    (rchk_err_resp_o)
  );

  assign protocol_err_o = obi_rvalid_i && !(|cnt_q);


 endmodule
