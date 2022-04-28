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
// Engineer:       Halfdan Bechmann  -  halfdan.bechmann@silabs.com           //
//                                                                            //
// Design Name:    Register file ECC                                          //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    1- and 2bit error detection using Error Correcting Codes   //
//                 for the register file                                      //
////////////////////////////////////////////////////////////////////////////////

/*
                             -Hamming ECC Encoding-

   Error addressing bit distribution:        Practical bit distribution (used here):
       ecc[0] [1] [2] [3] [4] [5]             ecc[0] [1] [2] [3] [4] [5]
           c0  c1  c2  c3  c4  c5                 c0  c1  c2  c3  c4  c5
  0   c0   X   .   .   .   .   .              d0   x   x   .   .   .   .
  1   c1   .   X   .   .   .   .              d1   x   .   x   .   .   .
  2   d0   x   x   .   .   .   .              d2   .   x   x   .   .   .
  3   c2   .   .   X   .   .   .              d3   x   x   x   .   .   .
  4   d1   x   .   x   .   .   .              d4   x   .   .   x   .   .
  5   d2   .   x   x   .   .   .              d5   .   x   .   x   .   .
  6   d3   x   x   x   .   .   .              d6   x   x   .   x   .   .
  7   c3   .   .   .   X   .   .              d7   .   .   x   x   .   .
  8   d4   x   .   .   x   .   .              d8   x   .   x   x   .   .
  9   d5   .   x   .   x   .   .              d9   .   x   x   x   .   .
 10   d6   x   x   .   x   .   .              d10  x   x   x   x   .   .
 11   d7   .   .   x   x   .   .              d11  x   .   .   .   x   .
 12   d8   x   .   x   x   .   .              d12  .   x   .   .   x   .
 13   d9   .   x   x   x   .   .              d13  x   x   .   .   x   .
 14   d10  x   x   x   x   .   .              d14  .   .   x   .   x   .
 15   c4   .   .   .   .   X   .              d15  x   .   x   .   x   .
 16   d11  x   .   .   .   x   .              d16  .   x   x   .   x   .
 17   d12  .   x   .   .   x   .              d17  x   x   x   .   x   .
 18   d13  x   x   .   .   x   .              d18  .   .   .   x   x   .
 19   d14  .   .   x   .   x   .              d19  x   .   .   x   x   .
 20   d15  x   .   x   .   x   .              d20  .   x   .   x   x   .
 21   d16  .   x   x   .   x   .              d21  x   x   .   x   x   .
 22   d17  x   x   x   .   x   .              d22  .   .   x   x   x   .
 23   d18  .   .   .   x   x   .              d23  x   .   x   x   x   .
 24   d19  x   .   .   x   x   .              d24  .   x   x   x   x   .
 25   d20  .   x   .   x   x   .              d25  x   x   x   x   x   .
 26   d21  x   x   .   x   x   .              d26  x   .   .   .   .   x
 27   d22  .   .   x   x   x   .              d27  .   x   .   .   .   x
 28   d23  x   .   x   x   x   .              d28  x   x   .   .   .   x
 29   d24  .   x   x   x   x   .              d29  .   .   x   .   .   x
 30   d25  x   x   x   x   x   .              d30  x   .   x   .   .   x
 31   c5   .   .   .   .   .   X              d31  .   x   x   .   .   x
 32   d26  x   .   .   .   .   x              c0   X   .   .   .   .   . \
 33   d27  .   x   .   .   .   x              c1   .   X   .   .   .   . |
 34   d28  x   x   .   .   .   x              c2   .   .   X   .   .   . |
 35   d29  .   .   x   .   .   x              c3   .   .   .   X   .   . |-- ECC bits
 36   d30  x   .   x   .   .   x              c4   .   .   .   .   X   . |
 37   d31  .   x   x   .   .   x              c5   .   .   .   .   .   X /

 */

module cv32e40s_register_file_ecc import cv32e40s_pkg::*;
  #(
    parameter int unsigned REGFILE_NUM_READ_PORTS = 2
  )
  (// Clock and Reset
   input logic                           clk,
   input logic                           rst_n,
   // Write ports
   input  rf_addr_t                      waddr_i    [REGFILE_NUM_WRITE_PORTS],
   input  rf_data_t                      wdata_i    [REGFILE_NUM_WRITE_PORTS],
   output logic [REGFILE_WORD_WIDTH-1:0] rf_wdata_o [REGFILE_NUM_WRITE_PORTS],
   // Read ports
   input  rf_addr_t                      raddr_i    [REGFILE_NUM_READ_PORTS],
   input  logic [REGFILE_WORD_WIDTH-1:0] rdata_i    [REGFILE_NUM_READ_PORTS],
   // Error output
   output logic                          ecc_err_o
   );

  ////////////////////////////
  //       Encoding         //
  ////////////////////////////

  logic [5:0] ecc [REGFILE_NUM_WRITE_PORTS]; // Error correcting code

  always_comb begin
    for (integer i = 0; i < REGFILE_NUM_WRITE_PORTS; i++) begin
      // Masking in hamming pattern (with half the bits inverted) to select wdata bits for parity calculation
      ecc[i][0] = ^(wdata_i[i] & 32'b0101_0110_1010_1010_1010_1101_0101_1011);
      ecc[i][1] = ^(wdata_i[i] & 32'b1001_1011_0011_0011_0011_0110_0110_1101);
      ecc[i][2] = ^(wdata_i[i] & 32'b1110_0011_1100_0011_1100_0111_1000_1110);
      ecc[i][3] = ^(wdata_i[i] & 32'b0000_0011_1111_1100_0000_0111_1111_0000);
      ecc[i][4] = ^(wdata_i[i] & 32'b0000_0011_1111_1111_1111_1000_0000_0000);
      ecc[i][5] = ^(wdata_i[i] & 32'b1111_1100_0000_0000_0000_0000_0000_0000);

      ecc[i]   ^= 6'b10_1010; // Invert every other bit

      // Add Error Code to write data
      rf_wdata_o[i] = {ecc[i], wdata_i[i]};
    end // for (genvar i = 0; i < REGFILE_NUM_WRITE_PORTS; i++)
  end

  ////////////////////////////
  //       Decoding         //
  ////////////////////////////

  logic [5:0] syndrome [REGFILE_NUM_READ_PORTS];

  always_comb begin
    ecc_err_o = 1'b0;
    for (integer i = 0; i < REGFILE_NUM_READ_PORTS; i++) begin
      //                                  /-ECC-\ /---------- Data ---------------------\
      syndrome[i][0] = ^(rdata_i[i] & 38'b00_0001_0101_0110_1010_1010_1010_1101_0101_1011);
      syndrome[i][1] = ^(rdata_i[i] & 38'b00_0010_1001_1011_0011_0011_0011_0110_0110_1101);
      syndrome[i][2] = ^(rdata_i[i] & 38'b00_0100_1110_0011_1100_0011_1100_0111_1000_1110);
      syndrome[i][3] = ^(rdata_i[i] & 38'b00_1000_0000_0011_1111_1100_0000_0111_1111_0000);
      syndrome[i][4] = ^(rdata_i[i] & 38'b01_0000_0000_0011_1111_1111_1111_1000_0000_0000);
      syndrome[i][5] = ^(rdata_i[i] & 38'b10_0000_1111_1100_0000_0000_0000_0000_0000_0000);

      syndrome[i]   ^= 6'b10_1010; // Invert every other bit

      // Using syndrome for 2-bit detection instead of 1-bit correction
      // The syndrome should always be 0 if there are no errors
      ecc_err_o      |= |syndrome[i];

    end
  end

endmodule // cv32e40s_register_file_ecc
