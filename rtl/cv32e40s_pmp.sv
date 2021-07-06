// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright 2021 Silicon Labs, Inc.
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
// Description:    PMP (Physical Memory Protection)                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_pmp import cv32e40s_pkg::*;
  #(
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMP_GRANULARITY = 0,
    // Number of implemented regions
    parameter int unsigned PMP_NUM_REGIONS = 0
    )
  (
   // Clock and Reset
   input logic        clk,
   input logic        rst_n,

   // Interface to CSRs
   input              pmp_cfg_t csr_pmp_cfg_i [PMP_MAX_REGIONS],
   input logic [33:0] csr_pmp_addr_i [PMP_MAX_REGIONS],
   input              pmp_mseccfg_t csr_pmp_mseccfg_i,

   // Privilege mode
   input              PrivLvl_t priv_lvl_i,
   // Access checking
   input logic [33:0] pmp_req_addr_i,
   input              pmp_req_e pmp_req_type_i,
   output logic       pmp_req_err_o
   );

  // Access Checking Signals
  logic [33:0]                 region_start_addr [PMP_MAX_REGIONS];
  logic [33:PMP_GRANULARITY+2] region_addr_mask  [PMP_MAX_REGIONS];
  logic [PMP_NUM_REGIONS-1:0]  region_match_gt;
  logic [PMP_NUM_REGIONS-1:0]  region_match_lt;
  logic [PMP_NUM_REGIONS-1:0]  region_match_eq;
  logic [PMP_NUM_REGIONS-1:0]  region_match_all;
  logic [PMP_NUM_REGIONS-1:0]  region_basic_perm_check;
  logic [PMP_NUM_REGIONS-1:0]  region_mml_perm_check;
  logic                        access_fault;

  for (genvar r = 0; r < PMP_NUM_REGIONS; r++) begin : g_regions

    // ---------------
    // Access checking
    // ---------------
    
    // Start address for TOR matching
    if (r == 0) begin : g_entry0
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? 34'h000000000 :
                                    csr_pmp_addr_i[r];
    end else begin : g_oth
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? csr_pmp_addr_i[r-1] :
                                    csr_pmp_addr_i[r];
    end
    
    // Address mask for NA matching
    for (genvar b = PMP_GRANULARITY+2; b < 34; b++) begin : g_bitmask
      if (b == 2) begin : g_bit0
        // Always mask bit 2 for NAPOT
        assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT);
      end else begin : g_others
        // We will mask this bit if it is within the programmed granule
        // i.e. addr = yyyy 0111
        //                  ^
        //                  | This bit pos is the top of the mask, all lower bits set
        // thus mask = 1111 0000
        if (PMP_GRANULARITY == 0) begin : g_region_addr_mask_zero_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) ||
                                          !(&csr_pmp_addr_i[r][b-1:2]);
        end else begin : g_region_addr_mask_other_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) ||
                                          !(&csr_pmp_addr_i[r][b-1:PMP_GRANULARITY+1]);
        end
      end
    end
    
    // Comparators are sized according to granularity
    assign region_match_eq[r] = (pmp_req_addr_i[33:PMP_GRANULARITY+2]       & region_addr_mask[r]) ==
                                (region_start_addr[r][33:PMP_GRANULARITY+2] & region_addr_mask[r]);
    assign region_match_gt[r] = pmp_req_addr_i[33:PMP_GRANULARITY+2] >
                                region_start_addr[r][33:PMP_GRANULARITY+2];
    assign region_match_lt[r] = pmp_req_addr_i[33:PMP_GRANULARITY+2] <
                                csr_pmp_addr_i[r][33:PMP_GRANULARITY+2];

    // Determine region match based on mode
    always_comb begin
      region_match_all[r] = 1'b0;
      unique case (csr_pmp_cfg_i[r].mode)
        PMP_MODE_OFF   : region_match_all[r] = 1'b0;
        PMP_MODE_NA4   : region_match_all[r] = region_match_eq[r];
        PMP_MODE_NAPOT : region_match_all[r] = region_match_eq[r];
        PMP_MODE_TOR   : begin
          region_match_all[r] = (region_match_eq[r] || region_match_gt[r]) &&
                                region_match_lt[r];
        end
        default        : region_match_all[r] = 1'b0;
      endcase
    end
    
    // Check specific required permissions
    assign region_basic_perm_check[r] = ((pmp_req_type_i == PMP_ACC_EXEC)  && csr_pmp_cfg_i[r].exec)  ||
                                        ((pmp_req_type_i == PMP_ACC_WRITE) && csr_pmp_cfg_i[r].write) ||
                                        ((pmp_req_type_i == PMP_ACC_READ)  && csr_pmp_cfg_i[r].read);
  
    // Compute permission checks that apply when MSECCFG.MML is set.
    always_comb begin
      region_mml_perm_check[r] = 1'b0;
  
      if (!csr_pmp_cfg_i[r].read && csr_pmp_cfg_i[r].write) begin
        // Special-case shared regions where R = 0, W = 1
        unique case ({csr_pmp_cfg_i[r].lock, csr_pmp_cfg_i[r].exec})
          // Read/write in M, read only in S/U
          2'b00: region_mml_perm_check[r] = (pmp_req_type_i == PMP_ACC_READ) ||
                                            ((pmp_req_type_i == PMP_ACC_WRITE) && (priv_lvl_i == PRIV_LVL_M));
          // Read/write in M/S/U
          2'b01: region_mml_perm_check[r] = (pmp_req_type_i == PMP_ACC_READ) || (pmp_req_type_i == PMP_ACC_WRITE);
          // Execute only on M/S/U
          2'b10: region_mml_perm_check[r] = (pmp_req_type_i == PMP_ACC_EXEC);
          // Read/execute in M, execute only on S/U
          2'b11: region_mml_perm_check[r] = (pmp_req_type_i == PMP_ACC_EXEC) ||
                                            ((pmp_req_type_i == PMP_ACC_READ) && (priv_lvl_i == PRIV_LVL_M));
          default: ;
        endcase
      end else begin
        if (csr_pmp_cfg_i[r].read && csr_pmp_cfg_i[r].write & csr_pmp_cfg_i[r].exec
            && csr_pmp_cfg_i[r].lock) begin
          // Special-case shared read only region when R = 1, W = 1, X = 1, L = 1
          region_mml_perm_check[r] = pmp_req_type_i == PMP_ACC_READ;
        end else begin
          // Otherwise use basic permission check. Permission is always denied if in S/U mode and
          // L is set or if in M mode and L is unset.
          region_mml_perm_check[r] = priv_lvl_i == PRIV_LVL_M ? 
                                     csr_pmp_cfg_i[r].lock && region_basic_perm_check[r] :
                                     !csr_pmp_cfg_i[r].lock && region_basic_perm_check[r];
        end
      end
    end
  end // block: g_regions
  

  // Access fault determination / prioritization
  always_comb begin
    // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
    // modes
    access_fault = csr_pmp_mseccfg_i.mmwp || (priv_lvl_i != PRIV_LVL_M);
    // TODO:OE The spec specifies:
    // "If no PMP entry matches an S-mode or U-mode access, but at least one PMP entry is implemented, the access fails."
    // Accesses would fail for all S- and U-mode accesses if no PMP entires are implemented.

    // PMP entries are statically prioritized, from 0 to N-1
    // The lowest-numbered PMP entry which matches an address determines accessability
    for (int r = PMP_NUM_REGIONS-1; r >= 0; r--) begin
      if (region_match_all[r]) begin
        if (csr_pmp_mseccfg_i.mml) begin
          // When MSECCFG.MML is set use MML specific permission check
          access_fault = !region_mml_perm_check[r];
        end else begin
          // Otherwise use original PMP behaviour
          access_fault = (priv_lvl_i == PRIV_LVL_M) ?
                         // For M-mode, any region which matches with the L-bit clear, or with sufficient
                         // access permissions will be allowed
                         (csr_pmp_cfg_i[r].lock && !region_basic_perm_check[r]) :
                         // For other modes, the lock bit doesn't matter
                         !region_basic_perm_check[r];
        end
      end
    end
  end

  assign pmp_req_err_o = access_fault;
  
  // RLB, rule locking bypass, is only relevant to cv32e40s_cs_registers which controls writes to the
  // PMP CSRs. Tie to unused signal here to prevent lint warnings.
  logic unused_csr_pmp_mseccfg_rlb;
  assign unused_csr_pmp_mseccfg_rlb = csr_pmp_mseccfg_i.rlb;
endmodule
