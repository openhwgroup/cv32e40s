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

module cv32e40s_instr_obi_interface import cv32e40s_pkg::*;
#(  parameter int          MAX_OUTSTANDING = 2
 )
(
  input  logic           clk,
  input  logic           rst_n,

  // Transaction request interface
  input  logic           trans_valid_i,
  output logic           trans_ready_o,
  input  obi_inst_req_t  trans_i,

  // Transaction response interface
  output logic           resp_valid_o,          // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
  output obi_inst_resp_t resp_o,

  output logic           integrity_err_o,       // integrity error
  output logic           protocol_err_o,        // protocol error

  input xsecure_ctrl_t   xsecure_ctrl_i,

  // OBI interface
  if_c_obi.master        m_c_obi_instr_if
);


  obi_if_state_e state_q, next_state;

  logic [11:0]          achk;                         // Address phase checksum

  logic                 gntpar_err;                   // gnt parity error (immediate)
  logic                 rvalidpar_err_resp;           // rvalid parity error (immediate during response phase)
  logic                 gntpar_err_resp;              // grant error with reponse timing (output of fifo)
  logic                 rchk_err_resp;                // Local rchk error signal
  logic                 integrity_resp;               // Response has integrity bit set (from fifo)

  logic                 protocol_err;                 // Set if rvalid arrives when no outstanding transactions are active


  //////////////////////////////////////////////////////////////////////////////
  // OBI R Channel
  //////////////////////////////////////////////////////////////////////////////

  // The OBI R channel signals are passed on directly on the transaction response
  // interface (resp_*). It is assumed that the consumer of the transaction response
  // is always receptive when resp_valid_o = 1 (otherwise a response would get dropped)
  // OBI response signals for parity error, integrity from PMA and rchk error are appended.

  assign resp_valid_o       = m_c_obi_instr_if.s_rvalid.rvalid;

  always_comb begin
    resp_o                = m_c_obi_instr_if.resp_payload;
    resp_o.integrity_err  = rvalidpar_err_resp || gntpar_err_resp || rchk_err_resp;
    resp_o.integrity      = integrity_resp;
  end

  //////////////////////////////////////////////////////////////////////////////
  // OBI A Channel
  //////////////////////////////////////////////////////////////////////////////

  // OBI A channel registers (to keep A channel stable)
  obi_inst_req_t        obi_a_req_q;

  // If the incoming transaction itself is not stable; use an FSM to make sure that
  // the OBI address phase signals are kept stable during non-granted requests.

  //////////////////////////////////////////////////////////////////////////////
  // OBI FSM
  //////////////////////////////////////////////////////////////////////////////

  // FSM (state_q, next_state) to control OBI A channel signals.

  always_comb
  begin
    next_state = state_q;

    case(state_q)

      // Default (transparent) state. Transaction requests are passed directly onto the OBI A channel.
      TRANSPARENT:
      begin
        if (m_c_obi_instr_if.s_req.req && !m_c_obi_instr_if.s_gnt.gnt) begin
          // OBI request not immediately granted. Move to REGISTERED state such that OBI address phase
          // signals can be kept stable while the transaction request (trans_*) can possibly change.
          next_state = REGISTERED;
        end
      end // case: TRANSPARENT

      // Registered state. OBI address phase signals are kept stable (driven from registers).
      REGISTERED:
      begin
        if (m_c_obi_instr_if.s_gnt.gnt) begin
          // Received grant. Move back to TRANSPARENT state such that next transaction request can be passed on.
          next_state = TRANSPARENT;
        end
      end // case: REGISTERED
      default: ;
    endcase
  end

  always_comb
  begin
    if (state_q == TRANSPARENT) begin
      m_c_obi_instr_if.s_req.req        = trans_valid_i;                // Do not limit number of outstanding transactions
      m_c_obi_instr_if.req_payload      = trans_i;
      m_c_obi_instr_if.req_payload.achk = achk;
    end else begin
      // state_q == REGISTERED
      m_c_obi_instr_if.s_req.req   = 1'b1;                              // Never retract request
      m_c_obi_instr_if.req_payload = obi_a_req_q;
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // Integrity // todo: ensure this will not get optimized away
  //////////////////////////////////////////////////////////////////////////////

  always_comb begin
    achk = {
      ^{8'b0},                                         // wdata[31:24] = 8'b0
      ^{8'b0},                                         // wdata[23:16] = 8'b0
      ^{8'b0},                                         // wdata[15:8] = 8'b0
      ^{8'b0},                                         // wdata[7:0] = 8'b0
      ^{6'b0},                                         // atop[5:0] = 6'b0
      ~^{m_c_obi_instr_if.req_payload.dbg},
      ~^{4'b1111, 1'b0},                                // be[3:0] = 4'b1111, we = 1'b0
      ~^{m_c_obi_instr_if.req_payload.prot[2:0], m_c_obi_instr_if.req_payload.memtype[1:0]},
      ^{m_c_obi_instr_if.req_payload.addr[31:24]},
      ^{m_c_obi_instr_if.req_payload.addr[23:16]},
      ^{m_c_obi_instr_if.req_payload.addr[15:8]},
      ^{m_c_obi_instr_if.req_payload.addr[7:2], 2'b00} // Bits 1:0 are tied to zero in the core level.
    };
  end

 assign  m_c_obi_instr_if.s_req.reqpar = !m_c_obi_instr_if.s_req.req;

  //////////////////////////////////////////////////////////////////////////////
  // Registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      state_q       <= TRANSPARENT;
      obi_a_req_q   <= OBI_INST_REQ_RESET_VAL;
    end
    else
    begin
      state_q       <= next_state;
      if ((state_q == TRANSPARENT) && (next_state == REGISTERED)) begin
        // Keep OBI A channel signals stable throughout REGISTERED state
        obi_a_req_q <= m_c_obi_instr_if.req_payload;
      end
    end
  end

  // Always ready to accept a new transfer requests when previous A channel
  // transfer has been granted. Note that cv32e40s_obi_interface does not limit
  // the number of outstanding transactions in any way.
  assign trans_ready_o = (state_q == TRANSPARENT);

  //////////////////////////////////////
  // Track parity errors
  //////////////////////////////////////

  // Always check gnt parity
  // alert_major will not update when in reset
  assign gntpar_err = (m_c_obi_instr_if.s_gnt.gnt == m_c_obi_instr_if.s_gnt.gntpar);


  cv32e40s_obi_integrity_fifo
  #(
      .MAX_OUTSTANDING   (MAX_OUTSTANDING),
      .RESP_TYPE         (obi_inst_resp_t)
   )
  integrity_fifo_i
  (
    .clk                (clk                              ),
    .rst_n              (rst_n                            ),

    // gnt parity error
    .gntpar_err_i       (gntpar_err                       ),

    // Transaction inputs
    .trans_integrity_i  (trans_i.integrity                ),
    .trans_we_i         (1'b0                             ),

    // Xsecure
    .xsecure_ctrl_i     (xsecure_ctrl_i                   ),

    // Response phase properties
    .gntpar_err_resp_o  (gntpar_err_resp                  ),
    .integrity_resp_o   (integrity_resp                   ),
    .rchk_err_resp_o    (rchk_err_resp                    ),

    .protocol_err_o     (protocol_err                     ),

    // OBI interface
    .obi_req_i          (m_c_obi_instr_if.s_req.req       ),
    .obi_gnt_i          (m_c_obi_instr_if.s_gnt.gnt       ),
    .obi_rvalid_i       (m_c_obi_instr_if.s_rvalid.rvalid ),
    .obi_resp_i         (resp_o                           )
  );


  // Checking rvalid parity
  // alert_major_o will go high immediately, while the rvalidpar_err_resp for the instruction
  // will only propagate when rvalid==1.
  assign rvalidpar_err_resp = (m_c_obi_instr_if.s_rvalid.rvalid == m_c_obi_instr_if.s_rvalid.rvalidpar);

  // Set integrity error outputs.
  // rchk_err: recomputed checksum mismatch when rvalid=1 and PMA has integrity set for the transaction
  // rvalidpar_err_resp: mismatch on rvalid parity bit at any time
  // gntpar_err: mismatch on gnt parity bit at any time
  assign integrity_err_o = rchk_err_resp || rvalidpar_err_resp || gntpar_err;
  assign protocol_err_o  = protocol_err;




endmodule
