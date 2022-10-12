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
// Authors:        Halfdan Bechmann - Halfdan Bechmann@silabs.com             //
//                                                                            //
// Description:    Dummy Instruction Insertion Assertions                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_dummy_instr_sva
  import cv32e40s_pkg::*;
  import uvm_pkg::*;
  #(parameter MAX_DUMMY_INTERVAL = 64,
    parameter CNT_WIDTH = 7
    )
  (input logic                 clk,
   input logic                 rst_n,

   input logic                 dummy_insert_o,
   input xsecure_ctrl_t        xsecure_ctrl_i,
   input logic [CNT_WIDTH-1:0] cnt_q,
   input logic [5:0]           lfsr_cnt,
   input logic                 instr_issued_i,
   input logic                 cnt_rst,
   input logic                 if_valid_i,
   input logic                 id_ready_i,
   input logic                 hint_id_i
   );

  // Assert that counter stopped correctly when inserting dummy instruction
  // When no hint is in ID, the cnt_q should be exactly lfsr_cnt + 1
  a_no_count_overflow_nohint :
    assert property (@(posedge clk) disable iff (!rst_n)
                     dummy_insert_o && !hint_id_i |-> (cnt_q == lfsr_cnt + 1))
      else `uvm_error("Dummy Instruction Insertion", "Counter counted further than lfsr_cnt + 1");

  // When a dummy is inserted and at the same time a hint is in ID, the counter value
  // may differ by more than one since the hint instruction did an lfsr shift, possibly changing the
  // dummy insertion threshold.
  a_no_count_overflow_hint :
    assert property (@(posedge clk) disable iff (!rst_n)
                      dummy_insert_o && hint_id_i |-> (cnt_q >= (lfsr_cnt + 1)))
      else `uvm_error("Dummy Instruction Insertion", "Counter counted further than lfsr_cnt + 1");

  // Assert that we never count when counter has passed the compare value
  a_never_count_on_overflow :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (cnt_q > lfsr_cnt) |=> (cnt_q <= $past(cnt_q)))
      else `uvm_error("Dummy Instruction Insertion", "Counted when after insert condition was met");

  // Counter should not reset if a dummy instruction is not yet propagated to decode (id_ready == 0)
  a_cnt_reset_on_dummy_issue :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (dummy_insert_o && if_valid_i && !id_ready_i) |-> !cnt_rst)
      else `uvm_error("Dummy Instruction Insertion", "Counter reset before dummy left IF");


endmodule : cv32e40s_dummy_instr_sva


