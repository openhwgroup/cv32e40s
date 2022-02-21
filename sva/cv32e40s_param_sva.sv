// Copyright 2022 Silicon Labs, Inc.
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
// Authors:        Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Description:    Assertions for top level parameters                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_param_sva import cv32e40s_pkg::*; import uvm_pkg::*;
  #(
    parameter int          PMP_NUM_REGIONS                     =  0,
    parameter pmpncfg_t    PMP_PMPNCFG_RV[PMP_NUM_REGIONS-1:0] = '{default:PMPNCFG_DEFAULT},
    parameter [31:0]       PMP_PMPADDR_RV[PMP_NUM_REGIONS-1:0] = '{default:32'h0},
    parameter mseccfg_t    PMP_MSECCFG_RV                      = MSECCFG_DEFAULT
    )
  (
   );

  // TODO: Move PMA parameter assertions here
  // TODO: Add assertions for LFSR coefficients (e.g. not 0 and MSB =1), see Ibex for inspiration

  ////////////////////////////////////////////
  // Assertions for PMP related parameters  //
  ////////////////////////////////////////////

  generate for (genvar i_pmp = 0; i_pmp < PMP_NUM_REGIONS; i_pmp++)
  begin: pmp_region_asrt

    initial begin

      // Make sure reset value of zero bitfields is zero
      a_param_pmpncfg_rv_zero: assert (PMP_PMPNCFG_RV[i_pmp].zero0 == '0)
        else `uvm_error("param_sva", $sformatf("PMP_PMPNCFG_RV[%2d].zero0 not equal to 0", i_pmp));

      // When mseccfg.mml==0, RW=01 is a reserved combination, and shall be disallowed
      if (!PMP_MSECCFG_RV.mml) begin
        a_param_pmp_no_rw_01: assert ({PMP_PMPNCFG_RV[i_pmp].read, PMP_PMPNCFG_RV[i_pmp].write} != 2'b01)
          else `uvm_error("param_sva", $sformatf("PMP_PMPNCFG_RV[%2d] illegal value: RW = 01", i_pmp));
      end

    end

  end
  endgenerate

  // Make sure reset value of zero bitfields is zero
  initial begin
    a_param_mseccfg_rv_zero: assert (PMP_MSECCFG_RV.zero0 == '0)
      else `uvm_error("param_sva", "PMP_MSECCFG_RV.zero0 not equal to 0");
  end

  // Make sure PMP_NUM_REGIONS is withing supported range
  initial begin
    a_pmp_valid_num_regions : assert  ((0 <= PMP_NUM_REGIONS) && (PMP_NUM_REGIONS <= 64))
        else `uvm_error("param_sva", "PMP_NUM_REGIONS not within range [0,64]");
  end

endmodule
