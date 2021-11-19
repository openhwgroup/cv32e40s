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
// Design Name:    Alert                                                      //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This module combines and flops the core alert outputs.     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_alert
  import cv32e40s_pkg::*;
  (input logic      clk,
   input logic      rst_n,

   // Alert Trigger input Signals
   input ctrl_fsm_t ctrl_fsm_i,

   input logic      rf_ecc_err_i,
   input logic      pc_err_i,
   input logic      csr_err_i,
   input logic      itf_int_err_i,
   input logic      lfsr_lockup_i,

   // Alert outputs
   output logic     alert_minor_o,
   output logic     alert_major_o
   );

  // Alert Outputs
  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      alert_minor_o <= 1'b0;
      alert_major_o <= 1'b0;
    end else begin

      // Minor Alert
      alert_minor_o <=  ctrl_fsm_i.exception_alert || // Trigger condtion constructed in controller FSM
                        lfsr_lockup_i;                // LFSR lockup
      // Major Alert
      alert_major_o <= rf_ecc_err_i || // Register File ECC Error
                       pc_err_i     || // Program Counter Error
                       csr_err_i    || // Control ans Status Register Parity Error
                       itf_int_err_i;  // Interface Integrity Error

    end
  end

endmodule // cv32e40s_alert
