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
// Engineer:       Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40s_rchk_check                                        //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This module will check the recomputed rchk values          //
//                 and signal an error if enalbed and checksums does not match//
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_rchk_check import cv32e40s_pkg::*;
#(
  parameter type RESP_TYPE = obi_inst_resp_t
)
(
  input  RESP_TYPE resp_i,
  input  logic     enable_i,
  output logic     err_o
);

logic [4:0] rchk_res;

// Compute rchk from response inputs
always_comb begin
  rchk_res = {
    ^{resp_i.err, 1'b0},
    ^{resp_i.rdata[31:24]},
    ^{resp_i.rdata[23:16]},
    ^{resp_i.rdata[15:8]},
    ^{resp_i.rdata[7:0]}
  };
end

assign err_o = (enable_i && resp_i.integrity)? (rchk_res != resp_i.rchk) : 1'b0;

endmodule
