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
    parameter int PMP_GRANULARITY = 0,
    // Number of implemented regions
    parameter int PMP_NUM_REGIONS = 0
    )
  (
   // Clock and Reset
   input logic        clk,
   input logic        rst_n,

   // Interface to CSRs
   input pmp_csr_t    csr_pmp_i,

   // Privilege mode
   input              privlvl_t priv_lvl_i,
   // Access checking
   input logic [33:0] pmp_req_addr_i,
   input              pmp_req_e pmp_req_type_i,
   output logic       pmp_req_err_o
   );

  // Access Checking Signals
  logic [PMP_NUM_REGIONS-1:0][33:0]                 region_start_addr;
  logic [PMP_NUM_REGIONS-1:0][33:PMP_GRANULARITY+2] region_addr_mask;
  logic [PMP_NUM_REGIONS-1:0]                       region_match_gt;
  logic [PMP_NUM_REGIONS-1:0]                       region_match_lt;
  logic [PMP_NUM_REGIONS-1:0]                       region_match_eq;
  logic [PMP_NUM_REGIONS-1:0]                       region_match_all;
  logic [PMP_NUM_REGIONS-1:0]                       region_basic_perm_check;
  logic [PMP_NUM_REGIONS-1:0]                       region_mml_perm_check;
  logic [PMP_NUM_REGIONS-1:0]                       access_fault_all;
  logic                                             access_fault;

  generate
    for (genvar r_a = 0; r_a < PMP_NUM_REGIONS; r_a++) begin : addr_match

      // ---------------
      // Region matching
      // ---------------
      
      // Start address for TOR matching
      if (r_a == 0) begin : g_entry0
        assign region_start_addr[r_a] = (csr_pmp_i.cfg[r_a].mode == PMP_MODE_TOR) ? 34'h000000000 :
                                        csr_pmp_i.addr[r_a];
      end else begin : g_oth
        assign region_start_addr[r_a] = (csr_pmp_i.cfg[r_a].mode == PMP_MODE_TOR) ? csr_pmp_i.addr[r_a-1] :
                                        csr_pmp_i.addr[r_a];
      end
      
      // Address mask for NA matching
      for (genvar b = PMP_GRANULARITY+2; b < 34; b++) begin : g_bitmask
        if (b == 2) begin : g_bit0
          // Always mask bit 2 for NAPOT
          assign region_addr_mask[r_a][b] = (csr_pmp_i.cfg[r_a].mode != PMP_MODE_NAPOT);
        end else begin : g_others
          // We will mask this bit if it is within the programmed granule
          // i.e. addr = yyyy 0111
          //                  ^
          //                  | This bit pos is the top of the mask, all lower bits set
          // thus mask = 1111 0000
          if (PMP_GRANULARITY == 0) begin : g_region_addr_mask_zero_granularity
            assign region_addr_mask[r_a][b] = (csr_pmp_i.cfg[r_a].mode != PMP_MODE_NAPOT) ||
                                              !(&csr_pmp_i.addr[r_a][b-1:2]);
          end else begin : g_region_addr_mask_other_granularity
            assign region_addr_mask[r_a][b] = (csr_pmp_i.cfg[r_a].mode != PMP_MODE_NAPOT) ||
                                              !(&csr_pmp_i.addr[r_a][b-1:PMP_GRANULARITY+1]);
          end
        end
      end
      
      // Comparators are sized according to granularity
      assign region_match_eq[r_a] = (pmp_req_addr_i[33:PMP_GRANULARITY+2]         & region_addr_mask[r_a]) ==
                                    (region_start_addr[r_a][33:PMP_GRANULARITY+2] & region_addr_mask[r_a]);
      assign region_match_gt[r_a] = pmp_req_addr_i[33:PMP_GRANULARITY+2] >
                                    region_start_addr[r_a][33:PMP_GRANULARITY+2];
      assign region_match_lt[r_a] = pmp_req_addr_i[33:PMP_GRANULARITY+2] <
                                    csr_pmp_i.addr[r_a][33:PMP_GRANULARITY+2];

      // Determine region match based on mode
      always_comb begin
        region_match_all[r_a] = 1'b0;
        unique case (csr_pmp_i.cfg[r_a].mode)
          PMP_MODE_OFF   : region_match_all[r_a] = 1'b0;
          PMP_MODE_NA4   : region_match_all[r_a] = region_match_eq[r_a];
          PMP_MODE_NAPOT : region_match_all[r_a] = region_match_eq[r_a];
          PMP_MODE_TOR   : begin
            region_match_all[r_a] = (region_match_eq[r_a] || region_match_gt[r_a]) &&
                                    region_match_lt[r_a];
          end
          default        : region_match_all[r_a] = 1'b0;
        endcase
      end
      
    end // block: addr_match
  endgenerate

  generate
    for (genvar r_c = 0; r_c < PMP_NUM_REGIONS; r_c++) begin : check_rules

      // ---------------
      // Rule checking
      // ---------------

      // Check specific required permissions
      assign region_basic_perm_check[r_c] = ((pmp_req_type_i == PMP_ACC_EXEC)  && csr_pmp_i.cfg[r_c].exec)  ||
                                            ((pmp_req_type_i == PMP_ACC_WRITE) && csr_pmp_i.cfg[r_c].write) ||
                                            ((pmp_req_type_i == PMP_ACC_READ)  && csr_pmp_i.cfg[r_c].read);
      
      // Compute permission checks that apply when MSECCFG.MML is set.
      always_comb begin
        region_mml_perm_check[r_c] = 1'b0;
        
        if (!csr_pmp_i.cfg[r_c].read && csr_pmp_i.cfg[r_c].write) begin
          // Special-case shared regions where R = 0, W = 1
          unique case ({csr_pmp_i.cfg[r_c].lock, csr_pmp_i.cfg[r_c].exec})
            // Read/write in M, read only in S/U
            2'b00: region_mml_perm_check[r_c] = (pmp_req_type_i == PMP_ACC_READ) ||
                                                ((pmp_req_type_i == PMP_ACC_WRITE) && (priv_lvl_i == PRIV_LVL_M));
            // Read/write in M/S/U
            2'b01: region_mml_perm_check[r_c] = (pmp_req_type_i == PMP_ACC_READ) || (pmp_req_type_i == PMP_ACC_WRITE);
            // Execute only on M/S/U
            2'b10: region_mml_perm_check[r_c] = (pmp_req_type_i == PMP_ACC_EXEC);
            // Read/execute in M, execute only on S/U
            2'b11: region_mml_perm_check[r_c] = (pmp_req_type_i == PMP_ACC_EXEC) ||
                                                ((pmp_req_type_i == PMP_ACC_READ) && (priv_lvl_i == PRIV_LVL_M));
            default: ;
          endcase
        end else begin
          if (csr_pmp_i.cfg[r_c].read && csr_pmp_i.cfg[r_c].write & csr_pmp_i.cfg[r_c].exec
              && csr_pmp_i.cfg[r_c].lock) begin
            // Special-case shared read only region when R = 1, W = 1, X = 1, L = 1
            region_mml_perm_check[r_c] = pmp_req_type_i == PMP_ACC_READ;
          end else begin
            // Otherwise use basic permission check. Permission is always denied if in S/U mode and
            // L is set or if in M mode and L is unset.
            region_mml_perm_check[r_c] = priv_lvl_i == PRIV_LVL_M ?
                                         csr_pmp_i.cfg[r_c].lock && region_basic_perm_check[r_c] :
                                         !csr_pmp_i.cfg[r_c].lock && region_basic_perm_check[r_c];
          end
        end
      end

      // Access fault determination
      always_comb begin

        if (csr_pmp_i.mseccfg.mml) begin
          // When MSECCFG.MML is set use MML specific permission check
          access_fault_all[r_c] = !region_mml_perm_check[r_c];
        end else begin
          // Otherwise use original PMP behaviour
          access_fault_all[r_c] = (priv_lvl_i == PRIV_LVL_M) ?
                                  // For M-mode, any region which matches with the L-bit clear, or with sufficient
                                  // access permissions will be allowed
                                  (csr_pmp_i.cfg[r_c].lock && !region_basic_perm_check[r_c]) :
                                  // For other modes, the lock bit doesn't matter
                                  !region_basic_perm_check[r_c];
        end
      end


    end // block: check_rules
  endgenerate


  // Access fault prioritization
  always_comb begin
    // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
    // modes
    access_fault = csr_pmp_i.mseccfg.mmwp || (priv_lvl_i != PRIV_LVL_M);

    // PMP entries are statically prioritized, from 0 to N-1
    // The lowest-numbered PMP entry which matches an address determines accessability
    for (int i_r = PMP_NUM_REGIONS-1; i_r >= 0; i_r--) begin
      if (region_match_all[i_r]) begin
        access_fault = access_fault_all[i_r];
      end
    end
  end

  // Tie low when PMP is deconfigured
  assign pmp_req_err_o = (PMP_NUM_REGIONS == 0) ? 1'b0 : access_fault;
  
  // RLB, rule locking bypass, is only relevant to cv32e40s_cs_registers which controls writes to the
  // PMP CSRs. Tie to unused signal here to prevent lint warnings.
  logic unused_csr_pmp_mseccfg_rlb;
  assign unused_csr_pmp_mseccfg_rlb = csr_pmp_i.mseccfg.rlb;
endmodule
