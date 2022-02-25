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
// Authors:        Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Description:    RTL assertions for the pc_check module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_pc_check_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
(
  input clk,
  input rst_n,
  input ctrl_flow_taken_err,
  input jump_mret_taken_err,
  input branch_taken_err,
  input jump_mret_untaken_err,
  input branch_untaken_err,
  input ctrl_flow_untaken_err,
  input addr_err,
  input compare_enable_q
);

 
// Assert that no errors should be possible
a_no_flow_taken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(ctrl_flow_taken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for taken jump/branch")
          
a_no_flow_untaken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(ctrl_flow_untaken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for untaken jump/branch")


a_no_jump_taken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(jump_mret_taken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for taken jump/branch")

a_no_jump_untaken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(jump_mret_untaken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for untaken jump/branch")

a_no_branch_taken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(branch_taken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for taken jump/branch")

a_no_branch_untaken_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(branch_untaken_err && compare_enable_q))
    else `uvm_error("pc_check", "Control flow error for untaken jump/branch")

a_no_addr_err:
    assert property (@(posedge clk) disable iff (!rst_n)
                    1'b1 |-> !(addr_err && compare_enable_q))
    else `uvm_error("pc_check", "PC mismatch")
endmodule // cv32e40s_pc_check_sva
