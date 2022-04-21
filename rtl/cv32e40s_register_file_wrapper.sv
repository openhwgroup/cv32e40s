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
// Engineers:      Øystein Knauserud - oystein.knauserud@silabs.com           //
//                 Halfdan Bechmann  -  halfdan.bechmann@silabs.com           //
//                                                                            //
// Design Name:    Register file wrapper                                      //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Wrapper for the register file                              //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_register_file_wrapper import cv32e40s_pkg::*;
  #(
    parameter int unsigned REGFILE_NUM_READ_PORTS = 2
  )
  (
   // Clock and Reset
   input logic      clk,
   input logic      rst_n,

   // R0 Dummy instruction handling
    input logic     dummy_instr_id_i,
    input logic     dummy_instr_wb_i,

   // ECC
   output logic     ecc_err_o,

   // Read ports
   input  rf_addr_t raddr_i [REGFILE_NUM_READ_PORTS],
   output rf_data_t rdata_o [REGFILE_NUM_READ_PORTS],

   // Write ports
   input rf_addr_t  waddr_i [REGFILE_NUM_WRITE_PORTS],
   input rf_data_t  wdata_i [REGFILE_NUM_WRITE_PORTS],
   input logic      we_i    [REGFILE_NUM_WRITE_PORTS]
   );

  // Register file data signals
  logic [REGFILE_WORD_WIDTH-1:0] rf_rdata[REGFILE_NUM_READ_PORTS];
  logic [REGFILE_WORD_WIDTH-1:0] rf_wdata[REGFILE_NUM_WRITE_PORTS];

  cv32e40s_register_file
    #(
      .REGFILE_NUM_READ_PORTS ( REGFILE_NUM_READ_PORTS )
      )
    register_file_i
      (
       .clk                ( clk                ),
       .rst_n              ( rst_n              ),

       .dummy_instr_id_i   ( dummy_instr_id_i   ),
       .dummy_instr_wb_i   ( dummy_instr_wb_i   ),

       // Read ports
       .raddr_i            ( raddr_i            ),
       .rdata_o            ( rf_rdata           ),

       // Write ports
       .waddr_i            ( waddr_i            ),
       .wdata_i            ( rf_wdata           ),
       .we_i               ( we_i               )
       );

  generate for (genvar i = 0; i < REGFILE_NUM_READ_PORTS; i++)
    assign rdata_o[i] = rf_data_t'(rf_rdata[i][REGFILE_DATA_WIDTH-1:0]);
  endgenerate

  generate
    if (SECURE) begin
      cv32e40s_register_file_ecc
        #(
          .REGFILE_NUM_READ_PORTS ( REGFILE_NUM_READ_PORTS )
          )
        register_file_ecc
        (
         .clk             ( clk                ),
         .rst_n           ( rst_n              ),

         // Read ports
         .raddr_i         ( raddr_i            ),
         .rdata_i         ( rf_rdata           ),

         // Write ports
         .waddr_i         ( waddr_i            ),
         .wdata_i         ( wdata_i            ),

         // Encoded Write Data
         .rf_wdata_o      ( rf_wdata           ),

         // Error Output
         .ecc_err_o       ( ecc_err_o          )
         );
    end else begin // if (SECURE)
      assign ecc_err_o = 1'b0;
      assign rf_wdata  = wdata_i;
    end
  endgenerate

endmodule

