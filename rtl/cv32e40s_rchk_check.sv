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
//                 and signal an error if enabled and checksums do not match  //
//                 The enable signal is split in two, one for checking rdata  //
//                 for reads, and one to check the error bit (read and writes)//
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_rchk_check import cv32e40s_pkg::*;
#(
  parameter type RESP_TYPE = obi_inst_resp_t
)
(
  input  RESP_TYPE   resp_i,
  input  logic [1:0] enable_i,
  output logic       err_o
);

logic [4:0] rchk_res;

logic rdata_err;
logic err_err;

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

assign rdata_err = (enable_i[0] && resp_i.integrity) ? (rchk_res[3:0] != resp_i.rchk[3:0]) : 1'b0;
assign err_err   = (enable_i[1] && resp_i.integrity) ? (rchk_res[4] != resp_i.rchk[4]) : 1'b0;
assign err_o = rdata_err || err_err;

endmodule
