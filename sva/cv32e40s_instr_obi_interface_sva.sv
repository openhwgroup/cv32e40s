// Copyright 2022 Silicon Labs, Inc.
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
// Authors:        Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    RTL assertions for the instr_obi_interface module          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_instr_obi_interface_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
(
  input logic           clk,
  input logic           rst_n,
  if_c_obi.monitor      m_c_obi_instr_if,
  input logic           gntpar_err,
  input logic           gntpar_err_q,
  input obi_inst_resp_t resp_o,
  input logic           gntpar_err_resp
);

 // Support logic (FIFO) to track grant parity fault and integrity bit

localparam MAX_OUTSTND_TXN = 5; // This needs to be larger (or equal) to the max outstanding transactions in IF and LSU

typedef enum logic [1:0] {GNT_ERR, GNT_NOERR, GNT_NONE} gnt_err_chck_e;
logic exp_gnt_err;
logic [$clog2(MAX_OUTSTND_TXN)-1:0] oldest_txn;

gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] trans_fifo_q;
gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] trans_fifo_n;
gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] trans_fifo_tmp;

always_comb begin
  trans_fifo_n   = trans_fifo_q;
  trans_fifo_tmp = trans_fifo_q;

  casez ({m_c_obi_instr_if.s_req.req, m_c_obi_instr_if.s_gnt.gnt, m_c_obi_instr_if.s_rvalid.rvalid})
      3'b110: begin
        // Accepted address phase, add one entry to FIFO
        trans_fifo_n = (gntpar_err || gntpar_err_q) ?
                               {trans_fifo_q[MAX_OUTSTND_TXN-2:0], GNT_ERR} :
                               {trans_fifo_q[MAX_OUTSTND_TXN-2:0], GNT_NOERR};
      end
      3'b0?1, 3'b?01: begin
        // Response phase, remove oldest entry from FIFO
        trans_fifo_n[oldest_txn] = GNT_NONE;
      end
      3'b111: begin
        // Accepted address phase and response phase. Clear oldest transaction and add new to FIFO
        trans_fifo_tmp[oldest_txn] = GNT_NONE;
        trans_fifo_n = (gntpar_err || gntpar_err_q) ?
                               {trans_fifo_tmp[MAX_OUTSTND_TXN-2:0], GNT_ERR} :
                               {trans_fifo_tmp[MAX_OUTSTND_TXN-2:0], GNT_NOERR};
      end
      default; // Do nothing
    endcase
end

// FIFO
always_ff @ (posedge clk, negedge rst_n) begin
  if (!rst_n) begin
    trans_fifo_q <= {MAX_OUTSTND_TXN{GNT_NONE}};
  end
  else begin
    trans_fifo_q <= trans_fifo_n;
  end
end

// Locate oldest entry in FIFO
always_comb begin
  oldest_txn = '0;
  for (int i = 0;  i < MAX_OUTSTND_TXN; i++) begin
    if (trans_fifo_q[i] != GNT_NONE) begin
      oldest_txn = i;
    end
  end
end

// GNT error from the oldest transaction
assign exp_gnt_err = (trans_fifo_q[oldest_txn] == GNT_ERR);

// Assert that integrity bit from MPU corresponds to the expected value
a_pma_integrity :
  assert property (@(posedge clk) disable iff (!rst_n)
                   m_c_obi_instr_if.s_rvalid.rvalid |-> exp_gnt_err == gntpar_err_resp)
    else `uvm_error("mpu", "GNT error bit not correct")

endmodule
