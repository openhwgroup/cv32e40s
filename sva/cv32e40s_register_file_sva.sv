// Copyright 2022 Silicon Labs, Inc.
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
// Description:    RTL assertions for the register file                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_register_file_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
      parameter int unsigned REGFILE_NUM_READ_PORTS = 2
  )
  (
   input logic                          clk,
   input logic                          rst_n,
   input logic [REGFILE_WORD_WIDTH-1:0] wdata_i   [REGFILE_NUM_WRITE_PORTS],
   input logic [REGFILE_WORD_WIDTH-1:0] rdata_o   [REGFILE_NUM_READ_PORTS],
   input logic [REGFILE_WORD_WIDTH-1:0] mem_gated [REGFILE_NUM_WORDS],
   input logic [REGFILE_WORD_WIDTH-1:0] mem       [REGFILE_NUM_WORDS]
   );

  function bit check_ecc_syndrome (logic [REGFILE_WORD_WIDTH-1:0] data);
    return ((1'b0 === ^(data & 38'b00_0001_0101_0110_1010_1010_1010_1101_0101_1011)) &&
            (1'b1 === ^(data & 38'b00_0010_1001_1011_0011_0011_0011_0110_0110_1101)) &&
            (1'b0 === ^(data & 38'b00_0100_1110_0011_1100_0011_1100_0111_1000_1110)) &&
            (1'b1 === ^(data & 38'b00_1000_0000_0011_1111_1100_0000_0111_1111_0000)) &&
            (1'b0 === ^(data & 38'b01_0000_0000_0011_1111_1111_1111_1000_0000_0000)) &&
            (1'b1 === ^(data & 38'b10_0000_1111_1100_0000_0000_0000_0000_0000_0000)) );
  endfunction

  generate
    if (SECURE) begin
      // This section contains Helper assertion for increased performance in multi-property formal solvers

      for (genvar rf_wp = 0; rf_wp < REGFILE_NUM_WRITE_PORTS; rf_wp++) begin
        // Check write port ECC
        a_check_wdata_ecc:
          assert property (@(posedge clk) disable iff (!rst_n)
                           check_ecc_syndrome(wdata_i[rf_wp]))
            else `uvm_error("register_file", $sformatf("ECC error on write port %d", rf_wp))
      end

      for (genvar rf_rp = 0; rf_rp < REGFILE_NUM_READ_PORTS; rf_rp++) begin
        a_check_rdata_source_ecc_helper:

          assert property (@(posedge clk) disable iff (!rst_n)
                           (rdata_o[rf_rp] inside {mem_gated}))
            else `uvm_error("register_file", "Rdata not in memory")

        // Check read port ECC
        a_check_rdata_ecc:
          assert property (@(posedge clk) disable iff (!rst_n)
                           check_ecc_syndrome(rdata_o[rf_rp]))
            else `uvm_error("register_file", $sformatf("ECC error on read port %d", rf_rp))

      end

      a_check_reg0_mem_ecc_helper:
        assert property (@(posedge clk) disable iff (!rst_n)
                         check_ecc_syndrome(mem[0]))
          else `uvm_error("register_file", "register 0 ecc err")

      // The mem side mux on mem_gated[0] is a bottelneck for solving the read port assertions
      a_check_reg0_mem_gated_ecc_helper:
        assert property (@(posedge clk) disable iff (!rst_n)
                         (mem_gated[0] === mem[0]) |-> check_ecc_syndrome(mem_gated[0]))
          else `uvm_error("register_file", "register 0 ecc err")

      for (genvar i = 0; i < REGFILE_NUM_WORDS; i++) begin
        // Check ecc syndrome for all registers
        a_check_mem_gated_ecc:
          assert property (@(posedge clk) disable iff (!rst_n)
                            check_ecc_syndrome(mem_gated[i]))
            else `uvm_error("register_file", $sformatf("ECC error for register word x%d", i))
      end

    end
  endgenerate

endmodule : cv32e40s_register_file_sva

