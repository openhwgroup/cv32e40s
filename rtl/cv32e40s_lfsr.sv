// Copyright 2021 Silicon Labs, Inc.
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
// Engineer:       Oivind Ekelund  -  oivind.ekelund@silabs.com               //
//                                                                            //
// Design Name:    cv32e40s_lfsr                                              //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    32 bit Fibonacci Linear Feedback Shift Register            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_lfsr import cv32e40s_pkg::*;
  #(parameter lfsr_cfg_t LFSR_CFG    = LFSR_CFG_DEFAULT
    )
  (input logic         clk,
   input logic         rst_n,

   input logic         enable_i,
   input logic [31:0]  seed_i,
   input logic         seed_we_i,
   input logic         shift_i,

   output logic [31:0] data_o,
   output logic        lockup_o
   );

  logic [31:0]         lfsr_q, lfsr_n;
  logic                lockup_wr;
  logic                lockup_shift;
  logic                clock_en;

  assign lfsr_n[31:1] = lfsr_q[30:0];
  assign lfsr_n[0]    = ^(lfsr_q & LFSR_CFG.coeffs);

  assign clock_en     = seed_we_i || lockup_o || shift_i;

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      lfsr_q <= LFSR_CFG.default_seed;
    end
    else begin
      if (clock_en) begin
        if (lockup_o) begin
          // Lockup in the next cycle detected, set default config instead
          lfsr_q <= LFSR_CFG.default_seed;
        end else if (seed_we_i) begin
          // Write new seed
          lfsr_q <= seed_i;
        end else begin
          // Shift LFSR
          lfsr_q <= lfsr_n;
        end
      end
    end
  end

  // Detect lockup (all 0's with XOR based feedback) in next cycle due to shift
  assign lockup_shift = !(|lfsr_n) && shift_i && !seed_we_i && enable_i;

  // Detect lockup (all 0's with XOR based feedback) in next cycle due to writes
  assign lockup_wr = !(|seed_i) && seed_we_i && enable_i;

  assign lockup_o = lockup_shift || lockup_wr;

  assign data_o = lfsr_q;

endmodule // cv32e40s_lfsr

