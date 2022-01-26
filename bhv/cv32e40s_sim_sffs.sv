// Copyright 2022 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Design Name:    cv32e40s_sffs                                              //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Emulates an instantiated sffs                              //
//                 This file is meant for rtl simulation only!                //
//                 It should not be used for ASIC synthesis.                  //
//                 It should not be used for FPGA synthesis.                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_sffs
#(
  parameter LIB = 0
  )
  (
   input  logic  clk,
   input  logic  rst_n,
   input  logic  d_i,
   output logic  q_o
   );

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      q_o <= 1'b1;
    end else begin
      q_o <= d_i;
    end
  end

endmodule : cv32e40s_sffs

