// Copyright 2020 Silicon Labs, Inc.
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
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    OBI (Open Bus Interface)                                   //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Open Bus Interface adapter. Translates transaction request //
//                 on the trans_* interface into an OBI A channel transfer.   //
//                 The OBI R channel transfer translated (i.e. passed on) as  //
//                 a transaction response on the resp_* interface.            //
//                                                                            //
//                 This adapter does not limit the number of outstanding      //
//                 OBI transactions in any way.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_data_obi_interface import cv32e40s_pkg::*;
#(  parameter int unsigned  MAX_OUTSTANDING   = 2,
    parameter int unsigned  OUTSTND_CNT_WIDTH = $clog2(MAX_OUTSTANDING+1)
 )
(
  input  logic        clk,
  input  logic        rst_n,

  // Transaction request interface
  input  logic         trans_valid_i,
  output logic         trans_ready_o,
  input obi_data_req_t trans_i,

  // Transaction response interface
  output logic           resp_valid_o,          // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
  output obi_data_resp_t resp_o,

  output logic         integrity_err_o,

  input xsecure_ctrl_t   xsecure_ctrl_i,

  // outstanding transactions count from LSU response filter
  input logic [OUTSTND_CNT_WIDTH-1:0] bus_cnt_i,

  // OBI interface
  if_c_obi.master     m_c_obi_data_if
);



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
  logic       gntpar_err;
  logic       gntpar_err_q;                           // gnt parity error (sticky for waited grants)
  logic       rvalidpar_err;                          // rvalid parity error (immediate during response phase)
  logic       gntpar_err_resp;                        // grant error with reponse timing (output of fifo)
  logic [1:0] rchk_en;                                // Rchk enable. bit0: for bits 3:0, bit1: bit 4 of rchk
  logic       rchk_err;

    logic           resp_is_store;


  //////////////////////////////////////////////////////////////////////////////
  // OBI R Channel
  //////////////////////////////////////////////////////////////////////////////

  // The OBI R channel signals are passed on directly on the transaction response
  // interface (resp_*). It is assumed that the consumer of the transaction response
  // is always receptive when resp_valid_o = 1 (otherwise a response would get dropped)

  assign resp_valid_o = m_c_obi_data_if.s_rvalid.rvalid;

  always_comb begin
    resp_o  = m_c_obi_data_if.resp_payload;
    resp_o.parity_err  = rvalidpar_err || gntpar_err_resp;
    resp_o.rchk_err    = rchk_err;
    resp_o.integrity   = fifo_q[bus_cnt_i].integrity;
  end

  //////////////////////////////////////////////////////////////////////////////
  // OBI A Channel
  //////////////////////////////////////////////////////////////////////////////

  // If the incoming transaction itself is stable, then it satisfies the OBI protocol
  // and signals can be passed to/from OBI directly.
  always_comb
  begin
    m_c_obi_data_if.s_req.req        = trans_valid_i;
    m_c_obi_data_if.req_payload      = trans_i;

    // Integrity // todo: ensure this will not get optimized away
    m_c_obi_data_if.req_payload.achk = {
                                        ^{m_c_obi_data_if.req_payload.wdata[31:24]},
                                        ^{m_c_obi_data_if.req_payload.wdata[23:16]},
                                        ^{m_c_obi_data_if.req_payload.wdata[15:8]},
                                        ^{m_c_obi_data_if.req_payload.wdata[7:0]},
                                        ^{6'b0},                                         // atop[5:0] = 6'b0
                                        ~^{m_c_obi_data_if.req_payload.dbg},
                                        ~^{m_c_obi_data_if.req_payload.be[3:0], m_c_obi_data_if.req_payload.we},
                                        ~^{m_c_obi_data_if.req_payload.prot[2:0], m_c_obi_data_if.req_payload.memtype[1:0]},
                                        ^{m_c_obi_data_if.req_payload.addr[31:24]},
                                        ^{m_c_obi_data_if.req_payload.addr[23:16]},
                                        ^{m_c_obi_data_if.req_payload.addr[15:8]},
                                        ^{m_c_obi_data_if.req_payload.addr[7:0]}
                                        };

  end

  assign trans_ready_o = m_c_obi_data_if.s_gnt.gnt;

  assign m_c_obi_data_if.s_req.reqpar = !m_c_obi_data_if.s_req.req;


  /////////////////
  // Integrity
  /////////////////

  // Always check gnt parity
  // alert_major will not update when in reset
  assign gntpar_err = (m_c_obi_data_if.s_gnt.gnt == m_c_obi_data_if.s_gnt.gntpar);

  // gntpar_err_q is a sticky gnt error bit.
  // Any gnt parity error detected during req will be remembered and propagated
  // to the fifo when the address phase ends.
  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      gntpar_err_q <= '0;
    end
    else begin
      if (m_c_obi_data_if.s_req.req) begin
        // Address phase active, set sticky gntpar_err if not granted
        // When granted, sticky bit will be cleared for the next address phase
        if (!m_c_obi_data_if.s_gnt.gnt) begin
          gntpar_err_q <= gntpar_err || gntpar_err_q;
        end else begin
          gntpar_err_q <= 1'b0;
        end
      end
    end
  end

  // FIFO to keep track of gnt parity errors, integrity bit from PMA and if transaction is load or store for outstanding transactions

  assign fifo_input.integrity = trans_i.integrity;
  assign fifo_input.gnterr    = (gntpar_err || gntpar_err_q);
  assign fifo_input.store     = trans_i.we;

  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      fifo_q <= '0;
    end
    else begin
      if (m_c_obi_data_if.s_req.req && m_c_obi_data_if.s_gnt.gnt) begin
        // Accepted address phase, populate FIFO with gnt parity error and PMA integrity bit
        fifo_q <= {fifo_q[MAX_OUTSTANDING-1:1], fifo_input, 3'b000};
      end
    end
  end

  // Enable rchk when in response phase and cpuctrl.integrity is set
  // Only enable check of bits 3:0 (rchk_en[0]) for loads
  assign rchk_en[0] = m_c_obi_data_if.s_rvalid.rvalid && xsecure_ctrl_i.cpuctrl.integrity && !resp_is_store;
  assign rchk_en[1] = m_c_obi_data_if.s_rvalid.rvalid && xsecure_ctrl_i.cpuctrl.integrity;

  cv32e40s_rchk_check
  #(
      .RESP_TYPE (obi_data_resp_t)
  )
  rchk_i
  (
    .resp_i   (resp_o),  // Using local output, as is has the PMA integrity bit appended from the fifo. Otherwise inputs from bus.
    .enable_i (rchk_en),
    .err_o    (rchk_err)
  );

  // grant parity for response is read from the fifo
  assign gntpar_err_resp = fifo_q[bus_cnt_i].gnterr;

  assign resp_is_store = fifo_q[bus_cnt_i].store;

  // Checking rvalid parity
  // integrity_err_o will go high immediately
  assign rvalidpar_err = (m_c_obi_data_if.s_rvalid.rvalid == m_c_obi_data_if.s_rvalid.rvalidpar);

  assign integrity_err_o = rchk_err || rvalidpar_err || gntpar_err;

endmodule
