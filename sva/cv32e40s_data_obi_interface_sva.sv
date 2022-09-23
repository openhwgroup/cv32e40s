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
// Description:    RTL assertions for the data_obi_interface module           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_data_obi_interface_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
(
  input logic           clk,
  input logic           rst_n,
  if_c_obi.monitor      m_c_obi_data_if,
  input logic           gntpar_err,
  input logic           gntpar_err_q,
  input obi_data_resp_t resp_o,
  input obi_data_req_t  trans_i,
  input logic           gntpar_err_resp,
  input logic           resp_is_store
);

 // Support logic (FIFO) to track grant parity fault

localparam MAX_OUTSTND_TXN = 5; // This needs to be larger (or equal) to the max outstanding transactions in IF and LSU

typedef enum logic [1:0] {GNT_ERR, GNT_NOERR, GNT_NONE} gnt_err_chck_e;
typedef enum logic [1:0] {INT, NOINT, INT_NONE} integrity_e;
typedef enum logic [1:0] {STORE, LOAD, STORE_NONE} store_e;
logic exp_int;
logic exp_gnt_err;
logic exp_store;
logic [$clog2(MAX_OUTSTND_TXN)-1:0] oldest_txn;

gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] gnt_fifo_q;
gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] gnt_fifo_n;
gnt_err_chck_e [MAX_OUTSTND_TXN-1:0] gnt_fifo_tmp;

integrity_e [MAX_OUTSTND_TXN-1:0] int_fifo_q;
integrity_e [MAX_OUTSTND_TXN-1:0] int_fifo_n;
integrity_e [MAX_OUTSTND_TXN-1:0] int_fifo_tmp;

store_e [MAX_OUTSTND_TXN-1:0] store_fifo_q;
store_e [MAX_OUTSTND_TXN-1:0] store_fifo_n;
store_e [MAX_OUTSTND_TXN-1:0] store_fifo_tmp;

always_comb begin
  gnt_fifo_n   = gnt_fifo_q;
  gnt_fifo_tmp = gnt_fifo_q;
  int_fifo_n   = int_fifo_q;
  int_fifo_tmp = int_fifo_q;
  store_fifo_n = store_fifo_q;
  store_fifo_tmp = store_fifo_q;
  casez ({m_c_obi_data_if.s_req.req, m_c_obi_data_if.s_gnt.gnt, m_c_obi_data_if.s_rvalid.rvalid})
      3'b110: begin
        // Accepted address phase, add one entry to FIFO
        gnt_fifo_n = (gntpar_err || gntpar_err_q) ?
                               {gnt_fifo_q[MAX_OUTSTND_TXN-2:0], GNT_ERR} :
                               {gnt_fifo_q[MAX_OUTSTND_TXN-2:0], GNT_NOERR};

        int_fifo_n = trans_i.integrity ?
                               {int_fifo_q[MAX_OUTSTND_TXN-2:0], INT} :
                               {int_fifo_q[MAX_OUTSTND_TXN-2:0], NOINT};

        store_fifo_n = trans_i.we ?
                               {store_fifo_q[MAX_OUTSTND_TXN-2:0], STORE} :
                               {store_fifo_q[MAX_OUTSTND_TXN-2:0], LOAD};
      end
      3'b0?1, 3'b?01: begin
        // Response phase, remove oldest entry from FIFO
        gnt_fifo_n[oldest_txn] = GNT_NONE;

        int_fifo_n[oldest_txn] = INT_NONE;

        store_fifo_n[oldest_txn] = STORE_NONE;
      end
      3'b111: begin
        // Accepted address phase and response phase. Clear oldest transaction and add new to FIFO
        gnt_fifo_tmp[oldest_txn] = GNT_NONE;
        gnt_fifo_n = (gntpar_err || gntpar_err_q) ?
                               {gnt_fifo_tmp[MAX_OUTSTND_TXN-2:0], GNT_ERR} :
                               {gnt_fifo_tmp[MAX_OUTSTND_TXN-2:0], GNT_NOERR};

        int_fifo_tmp[oldest_txn] = INT_NONE;
        int_fifo_n = trans_i.integrity ?
                                {int_fifo_tmp[MAX_OUTSTND_TXN-2:0], INT} :
                                {int_fifo_tmp[MAX_OUTSTND_TXN-2:0], NOINT};

        store_fifo_tmp[oldest_txn] = STORE_NONE;
        store_fifo_n = trans_i.we ?
                                {store_fifo_tmp[MAX_OUTSTND_TXN-2:0], STORE} :
                                {store_fifo_tmp[MAX_OUTSTND_TXN-2:0], LOAD};
      end
      default; // Do nothing
    endcase
end

// FIFO
always_ff @ (posedge clk, negedge rst_n) begin
  if (!rst_n) begin
    gnt_fifo_q <= {MAX_OUTSTND_TXN{GNT_NONE}};
    int_fifo_q <= {MAX_OUTSTND_TXN{INT_NONE}};
    store_fifo_q <= {MAX_OUTSTND_TXN{STORE_NONE}};
  end
  else begin
    gnt_fifo_q <= gnt_fifo_n;
    int_fifo_q <= int_fifo_n;
    store_fifo_q <= store_fifo_n;
  end
end

// Locate oldest entry in FIFO
// FIFOs for gnt error and integrity bit operate on the same control signals,
// picking oldest index from gnt fifo.
always_comb begin
  oldest_txn = '0;
  for (int i = 0;  i < MAX_OUTSTND_TXN; i++) begin
    if (gnt_fifo_q[i] != GNT_NONE) begin
      oldest_txn = i;
    end
  end
end

// GNT error from the oldest transaction
assign exp_gnt_err = (gnt_fifo_q[oldest_txn] == GNT_ERR);

// Assert that grant error bit comes out in order
a_data_obi_gnt_fifo :
  assert property (@(posedge clk) disable iff (!rst_n)
                   m_c_obi_data_if.s_rvalid.rvalid |-> exp_gnt_err == gntpar_err_resp)
    else `uvm_error("mpu", "GNT error bit not correct")


// GNT error from the oldest transaction
assign exp_int = (int_fifo_q[oldest_txn] == INT);

// Assert that trans integrity bit comes out in order
a_data_obi_int_fifo :
  assert property (@(posedge clk) disable iff (!rst_n)
                   m_c_obi_data_if.s_rvalid.rvalid |-> exp_int == resp_o.integrity)
    else `uvm_error("mpu", "Integrity bit not correct")

// Store bit from the oldest transaction
assign exp_store = (store_fifo_q[oldest_txn] == STORE);

// Assert that trans integrity bit comes out in order
a_data_obi_store_fifo :
  assert property (@(posedge clk) disable iff (!rst_n)
                    m_c_obi_data_if.s_rvalid.rvalid |-> exp_store == resp_is_store)
    else `uvm_error("mpu", "Store bit not correct")
endmodule
