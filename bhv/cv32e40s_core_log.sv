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
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    cv32e40s_core_log.sv (cv32e40s_core simulation log)        //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Logs the following:                                        //
//                                                                            //
//                 - top level parameter settings                             //
//                 - illegal instructions                                     //
//                                                                            //
// Note:           This code was here from cv32e40s_core.sv and               //
//                 cv32e40s_controller.sv in order to remove the use of       //
//                 global defines in the RTL code.                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_core_log import cv32e40s_pkg::*;
#(
  parameter bit                         ENABLE                                  = 1'b1,
  parameter                             LIB                                     = 0,
  parameter rv32_e                      RV32                                    = RV32I,
  parameter b_ext_e                     B_EXT                                   = B_NONE,
  parameter m_ext_e                     M_EXT                                   = M,
  parameter bit                         DEBUG                                   = 1,
  parameter logic [31:0]                DM_REGION_START                         = 32'hF0000000,
  parameter logic [31:0]                DM_REGION_END                           = 32'hF0003FFF,
  parameter int                         DBG_NUM_TRIGGERS                        = 1,
  parameter int                         PMA_NUM_REGIONS                         = 0,
  parameter pma_cfg_t                   PMA_CFG[PMA_NUM_REGIONS-1:0]            = '{default:PMA_R_DEFAULT},
  parameter bit                         CLIC                                    = 0,
  parameter int unsigned                CLIC_ID_WIDTH                           = 5,
  parameter int unsigned                PMP_GRANULARITY                         = 0,
  parameter int                         PMP_NUM_REGIONS                         = 0,
  parameter pmpncfg_t                   PMP_PMPNCFG_RV[PMP_NUM_REGIONS-1:0]     = '{default:PMPNCFG_DEFAULT},
  parameter logic [31:0]                PMP_PMPADDR_RV[PMP_NUM_REGIONS-1:0]     = '{default:32'h0},
  parameter mseccfg_t                   PMP_MSECCFG_RV                          = MSECCFG_DEFAULT,
  parameter lfsr_cfg_t                  LFSR0_CFG                               = LFSR_CFG_DEFAULT, // Do not use default value for LFSR configuration
  parameter lfsr_cfg_t                  LFSR1_CFG                               = LFSR_CFG_DEFAULT, // Do not use default value for LFSR configuration
  parameter lfsr_cfg_t                  LFSR2_CFG                               = LFSR_CFG_DEFAULT  // Do not use default value for LFSR configuration
)
(
  input logic        clk_i,
  input ex_wb_pipe_t ex_wb_pipe_i,
  input logic [31:0] mhartid_i

);

`ifndef FORMAL
  generate begin
    if (ENABLE == 1'b1) begin
      // Log top level parameter values
      initial
      begin
        $display("[cv32e40s_core]: RV32                       = %s",    RV32.name()     );
        $display("[cv32e40s_core]: B_EXT                      = %s",    B_EXT.name()    );
        $display("[cv32e40s_core]: M_EXT                      = %s",    M_EXT.name()    );
        $display("[cv32e40s_core]: DEBUG                      = %-1d",  DEBUG           );
        $display("[cv32e40s_core]: DM_REGION_START            = 0x%8h", DM_REGION_START );
        $display("[cv32e40s_core]: DM_REGION_END              = 0x%8h", DM_REGION_END   );
        $display("[cv32e40s_core]: DBG_NUM_TRIGGERS           = %-1d",  DBG_NUM_TRIGGERS);
        $display("[cv32e40s_core]: PMA_NUM_REGIONS            = %-2d",  PMA_NUM_REGIONS );
        for (int i_pma=0; i_pma<PMA_NUM_REGIONS; i_pma++) begin
          $display("[cv32e40s_core]: PMA_CFG[%2d].word_addr_low  = 0x%8h", i_pma, PMA_CFG[i_pma].word_addr_low);
          $display("[cv32e40s_core]: PMA_CFG[%2d].word_addr_high = 0x%8h", i_pma, PMA_CFG[i_pma].word_addr_high);
          $display("[cv32e40s_core]: PMA_CFG[%2d].main           = %-1d",  i_pma, PMA_CFG[i_pma].main);
          $display("[cv32e40s_core]: PMA_CFG[%2d].bufferable     = %-1d",  i_pma, PMA_CFG[i_pma].bufferable);
          $display("[cv32e40s_core]: PMA_CFG[%2d].cacheable      = %-1d",  i_pma, PMA_CFG[i_pma].cacheable);
          $display("[cv32e40s_core]: PMA_CFG[%2d].integrity      = %-1d",  i_pma, PMA_CFG[i_pma].integrity);
        end
        $display("[cv32e40s_core]: CLIC                       = %-1d",  CLIC             );
        $display("[cv32e40s_core]: CLIC_ID_WIDTH              = %-2d",  CLIC_ID_WIDTH    );
        $display("[cv32e40s_core]: PMP_GRANULARITY            = %-2d",  PMP_GRANULARITY  );
        $display("[cv32e40s_core]: PMP_NUM_REGIONS            = %-2d",  PMP_NUM_REGIONS  );
        for (int i_pmp=0; i_pmp<PMP_NUM_REGIONS; i_pmp++) begin
          $display("[cv32e40s_core]: PMP_PMPNCFG_RV[%2d].lock  = %-1d", i_pmp, PMP_PMPNCFG_RV[i_pmp].lock);
          $display("[cv32e40s_core]: PMP_PMPNCFG_RV[%2d].mode  = %s",   i_pmp, PMP_PMPNCFG_RV[i_pmp].mode.name());
          $display("[cv32e40s_core]: PMP_PMPNCFG_RV[%2d].exec  = %-1d", i_pmp, PMP_PMPNCFG_RV[i_pmp].exec);
          $display("[cv32e40s_core]: PMP_PMPNCFG_RV[%2d].write = %-1d", i_pmp, PMP_PMPNCFG_RV[i_pmp].write);
          $display("[cv32e40s_core]: PMP_PMPNCFG_RV[%2d].read  = %-1d", i_pmp, PMP_PMPNCFG_RV[i_pmp].read);
          $display("[cv32e40s_core]: PMP_PMPADDR_RV[%2d]       = 0x%8h", i_pmp, PMP_PMPADDR_RV[i_pmp]);
        end
        $display("[cv32e40s_core]: PMP_MSECCFG_RV.rlb   = %-1d", PMP_MSECCFG_RV.rlb);
        $display("[cv32e40s_core]: PMP_MSECCFG_RV.mmwp  = %-1d", PMP_MSECCFG_RV.mmwp);
        $display("[cv32e40s_core]: PMP_MSECCFG_RV.mml   = %-1d", PMP_MSECCFG_RV.mml);
        $display("[cv32e40s_core]: LFSR0_CFG.coeffs           = 0x%8h", LFSR0_CFG.coeffs);
        $display("[cv32e40s_core]: LFSR0_CFG.default_seed     = 0x%8h", LFSR0_CFG.default_seed);
        $display("[cv32e40s_core]: LFSR1_CFG.coeffs           = 0x%8h", LFSR1_CFG.coeffs);
        $display("[cv32e40s_core]: LFSR1_CFG.default_seed     = 0x%8h", LFSR1_CFG.default_seed);
        $display("[cv32e40s_core]: LFSR2_CFG.coeffs           = 0x%8h", LFSR2_CFG.coeffs);
        $display("[cv32e40s_core]: LFSR2_CFG.default_seed     = 0x%8h", LFSR2_CFG.default_seed);
      end

      // Log illegal instructions
      always_ff @(negedge clk_i)
      begin
        // print warning in case of decoding errors
        if (ex_wb_pipe_i.instr_valid && ex_wb_pipe_i.illegal_insn) begin
          $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, mhartid_i[3:0], ex_wb_pipe_i.pc);
        end
      end
    end
  end
  endgenerate
`endif

endmodule // cv32e40s_core_log
