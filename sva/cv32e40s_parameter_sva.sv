// Copyright 2023 Silicon Labs, Inc.
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

module cv32e40s_parameter_sva import cv32e40s_pkg::*;
  #(
    parameter int          PMA_NUM_REGIONS                     = 0,
    parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0]        = '{default:PMA_R_DEFAULT},
    parameter logic [31:0] DM_REGION_START                     = 32'hF0000000,
    parameter logic [31:0] DM_REGION_END                       = 32'hF0003FFF,
    parameter int          DBG_NUM_TRIGGERS                    = 1,
    parameter int unsigned CLIC_ID_WIDTH                       = 5,
    parameter int unsigned NUM_MHPMCOUNTERS                    = 1,
    parameter int          PMP_NUM_REGIONS                     =  0,
    parameter pmpncfg_t    PMP_PMPNCFG_RV[PMP_NUM_REGIONS-1:0] = '{default:PMPNCFG_DEFAULT},
    parameter mseccfg_t    PMP_MSECCFG_RV                      = MSECCFG_DEFAULT,
    parameter int unsigned PMP_GRANULARITY                     = 0,
    parameter lfsr_cfg_t   LFSR0_CFG                           = LFSR_CFG_DEFAULT,
    parameter lfsr_cfg_t   LFSR1_CFG                           = LFSR_CFG_DEFAULT,
    parameter lfsr_cfg_t   LFSR2_CFG                           = LFSR_CFG_DEFAULT
    )
  (
   input logic clk_i,
   input logic rst_ni
   );

  a_param_pma_num_regions :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= PMA_NUM_REGIONS) && (PMA_NUM_REGIONS <= 16))
    else $fatal(0, "Invalid PMA_NUM_REGIONS");

  generate for (genvar i = 0; i < PMA_NUM_REGIONS; i++)
    begin : a_pma_no_illegal_configs

      if (!PMA_CFG[i].main) begin
        a_param_pma_io_noncacheable :
          assert property (@(posedge clk_i) disable iff (!rst_ni)
                            !PMA_CFG[i].cacheable)
            else $fatal(0, "Invalid PMA region configuration: cacheable I/O region");
      end

      a_param_pma_addr_range :
        assert property (@(posedge clk_i) disable iff (!rst_ni)
                         PMA_CFG[i].word_addr_high >= PMA_CFG[i].word_addr_low)
        else $fatal(0, "Invalid PMA region boundaries");

    end
  endgenerate


  a_param_dm_region :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     DM_REGION_END > DM_REGION_START)
    else $fatal(0, "Invalid combination of DM_REGION_START and DM_REGION_END");

  a_param_dbg_num_triggers :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= DBG_NUM_TRIGGERS) && (DBG_NUM_TRIGGERS <= 4))
    else $fatal(0, "Invalid DBG_NUM_TRIGGERS");

  a_param_clic_id_width :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (1 <= CLIC_ID_WIDTH) && (CLIC_ID_WIDTH <= 10))
    else $fatal(0, "Invalid CLIC_ID_WIDTH");

  a_param_num_mhpmcounters :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= NUM_MHPMCOUNTERS) && (NUM_MHPMCOUNTERS <= 29))
    else $fatal(0, "Invalid NUM_MHPMCOUNTERS");

  a_param_pmp_num_regions :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= PMP_NUM_REGIONS) && (PMP_NUM_REGIONS <= 64))
    else $fatal(0, "Invalid PMP_NUM_REGIONS");

  a_param_pmp_granularity :
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     (0 <= PMP_GRANULARITY) && (PMP_GRANULARITY <= 31))
    else $fatal(0, "Invalid PMP_GRANULARITY");

  generate for (genvar i_pmp = 0; i_pmp < PMP_NUM_REGIONS; i_pmp++)
  begin: pmp_region_asrt

    // Make sure reset value of zero bitfields is zero
    a_param_pmpncfg_rv_zero:
      assert property (@(posedge clk_i) disable iff (!rst_ni)
                       PMP_PMPNCFG_RV[i_pmp].zero0 == '0)
        else $fatal(0, $sformatf("PMP_PMPNCFG_RV[%2d].zero0 not equal to 0", i_pmp));

    // When mseccfg.mml==0, RW=01 is a reserved combination, and shall be disallowed
    if (!PMP_MSECCFG_RV.mml) begin
      a_param_pmp_no_rw_01:
        assert property (@(posedge clk_i) disable iff (!rst_ni)
                         {PMP_PMPNCFG_RV[i_pmp].read, PMP_PMPNCFG_RV[i_pmp].write} != 2'b01)
          else $fatal(0, $sformatf("PMP_PMPNCFG_RV[%2d] illegal value: RW = 01", i_pmp));

      end
  end
  endgenerate

  a_param_mseccfg_rv_zero:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     PMP_MSECCFG_RV.zero0 == '0)
    else $fatal(0, "PMP_MSECCFG_RV.zero0 not equal to 0");

  a_param_lfsr0_cfg:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     LFSR0_CFG != LFSR_CFG_DEFAULT)
    else $fatal(0, "Invalid LFSR0_CFG");

  a_param_lfsr1_cfg:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     LFSR1_CFG != LFSR_CFG_DEFAULT)
    else $fatal(0, "Invalid LFSR1_CFG");

  a_param_lfsr2_cfg:
    assert property (@(posedge clk_i) disable iff (!rst_ni)
                     LFSR2_CFG != LFSR_CFG_DEFAULT)
    else $fatal(0, "Invalid LFSR2_CFG");

endmodule
