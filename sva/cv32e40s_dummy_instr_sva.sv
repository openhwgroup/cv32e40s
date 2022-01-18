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
   input logic                 cpuctrl_we,
   input cpuctrl_t             cpuctrl_n,
   input logic                 secureseed0_we,
   input logic [31:0]          secureseed0_n,
   input xsecure_ctrl_t        xsecure_ctrl_i,
   input logic [CNT_WIDTH-1:0] cnt_q,
   input logic [5:0]           lfsr_cnt
   );

  // Check whether the randomization conditions have been changed by software
  logic                        sw_reg_update;
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      sw_reg_update <= '0;
    end else begin
      if (cpuctrl_we && (cpuctrl_n.rnddummyfreq != xsecure_ctrl_i.cpuctrl.rnddummyfreq)) begin
        sw_reg_update <= 1'b1;
      end else if (secureseed0_we && (secureseed0_n != xsecure_ctrl_i.lfsr0)) begin
        sw_reg_update <= 1'b1;
      end else if (dummy_insert_o) begin
        sw_reg_update <= 1'b0;
      end
    end
  end

  // Assert that counter stopped correctly when inserting dummy instruction
  // The count is allowed to be off when the randomization conditions have been changed by software
  a_no_count_overflow :
    assert property (@(posedge clk) disable iff (!rst_n)
                     dummy_insert_o |-> (cnt_q == lfsr_cnt + 1) || sw_reg_update)
      else `uvm_error("Dummy Instruction Insertion", "Counter counted further than lfsr_cnt + 1");

  // Assert that we never count when counter has passed the compare value
  a_never_count_on_overflow :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (cnt_q > lfsr_cnt) |=> (cnt_q <= $past(cnt_q)))
      else `uvm_error("Dummy Instruction Insertion", "Counted when after insert condition was met");

endmodule : cv32e40s_dummy_instr_sva


