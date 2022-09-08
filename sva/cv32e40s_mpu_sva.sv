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
// Description:    MPU (Memory Protection Unit) assertions                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_mpu_sva import cv32e40s_pkg::*; import uvm_pkg::*;
  #(  parameter int PMP_NUM_REGIONS              = 0,
      parameter int PMA_NUM_REGIONS              = 0,
      parameter pma_cfg_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT},
      parameter int unsigned IS_INSTR_SIDE = 0)
  (
   input logic        clk,
   input logic        rst_n,

   input logic        instr_fetch_access,
   input logic        misaligned_access_i,
   input logic        bus_trans_bufferable,
   input logic        bus_trans_cacheable,

   // PMA signals
   input logic        pma_err,
   input logic [31:0] pma_addr,
   input pma_cfg_t    pma_cfg,
   input logic        pma_integrity,

   // PMP signals
   input pmp_csr_t    csr_pmp_i,

   // Core OBI signals
   input logic [ 1:0] obi_memtype,
   input logic [31:0] obi_addr,
   input logic        obi_req,
   input logic        obi_gnt,

   // Interface towards bus interface
   input logic        bus_trans_ready_i,
   input logic        bus_trans_valid_o,

   input logic        bus_resp_valid_i,

   // Write buffer signals
   input write_buffer_state_e write_buffer_state,
   input logic        write_buffer_valid_o,
   input logic        write_buffer_txn_bufferable,
   input logic        write_buffer_txn_cacheable,

   // Interface towards core
   input logic        core_trans_valid_i,
   input logic        core_trans_ready_o,

   input logic        core_resp_valid_o,
   input logic        core_resp_o_integrity,

   input              mpu_status_e mpu_status,
   input logic        mpu_err_trans_valid,
   input logic        mpu_block_core,
   input logic        mpu_block_bus,
   input              mpu_state_e state_q,
   input logic        mpu_err,
   input logic        load_access
   );

  // PMA assertions helper signals

  logic is_addr_match;

  // Not checking bits [1:0]; bit 0 is always 0; bit 1 is not checked because it is only
  // suppressed after the PMA. These address bits are also ignored by the PMA itself.
  assign is_addr_match = obi_addr[31:2] == pma_addr[31:2];

  logic was_obi_waiting;
  logic was_obi_reqnognt;
  logic [1:0] was_obi_memtype;
  assign was_obi_waiting = was_obi_reqnognt && !bus_trans_ready_i;

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      was_obi_reqnognt <= 0;
      was_obi_memtype <= 0;
    end
    else begin
      was_obi_reqnognt <= obi_req && !obi_gnt;
      was_obi_memtype <= obi_memtype;
    end
  end

  function logic bufferable_in_config;
    bufferable_in_config = 0;
    foreach (PMA_CFG[i]) begin
      if (PMA_CFG[i].bufferable) begin
        bufferable_in_config = 1;
      end
    end
  endfunction

  function logic cacheable_in_config;
    cacheable_in_config = 0;
    foreach (PMA_CFG[i]) begin
      if (PMA_CFG[i].cacheable) begin
        cacheable_in_config = 1;
      end
    end
  endfunction

  logic is_lobound_ok;
  logic is_hibound_ok;
  assign is_lobound_ok = {pma_cfg.word_addr_low, 2'b00} <= pma_addr;
  assign is_hibound_ok = pma_addr < {pma_cfg.word_addr_high, 2'b00};

  logic is_pma_matched;
  int pma_match_num;
  logic [$clog2(PMA_NUM_REGIONS)-1:0] pma_lowest_match;
  //int pma_lowest_match;
  always_comb begin
    is_pma_matched = 0;
    pma_match_num = 999;
    pma_lowest_match = 0;

    // Find pma module's attributes among cfgs
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if ((pma_cfg == PMA_CFG[i]) && (pma_cfg != PMA_R_DEFAULT)) begin
        is_pma_matched = 1;
        pma_match_num = i;
        break;
      end
    end

    // Find lowest region matching addr
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if (({PMA_CFG[i].word_addr_low, 2'b00} <= pma_addr) && (pma_addr < {PMA_CFG[i].word_addr_high, 2'b00})) begin
        pma_lowest_match = i;
        break;
      end
    end
  end
  `ifndef FORMAL
    cov_pma_matchnone : cover property (@(posedge clk) disable iff (!rst_n) (!is_pma_matched));
    cov_pma_matchfirst : cover property (@(posedge clk) disable iff (!rst_n) (is_pma_matched && (pma_match_num == 0)));
    cov_pma_matchother : cover property (@(posedge clk) disable iff (!rst_n) (is_pma_matched && (pma_match_num > 0)));
  `endif


  // Checks for illegal PMA region configuration

  always_comb begin
    if (PMA_NUM_REGIONS != 0) begin
      a_pma_valid_config : assert (PMA_NUM_REGIONS == $size(PMA_CFG))
        else `uvm_error("mpu", "PMA_CFG must contain PMA_NUM_REGION entries");
    end
  end

  generate for (genvar i = 0; i < PMA_NUM_REGIONS; i++)
    begin : a_pma_no_illegal_configs
    always_comb begin
        if (PMA_CFG[i].main == 1'b0) begin
          a_io_noncacheable : assert (PMA_CFG[i].cacheable == 1'b0)
            else `uvm_error("mpu", "PMA regions configured as I/O cannot be defined as cacheable");
        end
      end
    end
  endgenerate

  a_pma_valid_num_regions :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (0 <= PMA_NUM_REGIONS) && (PMA_NUM_REGIONS <= 16))
      else `uvm_error("mpu", "PMA number of regions is badly configured")

  // Region matching
  generate
    if (PMA_NUM_REGIONS) begin
      a_pma_match_bounds :
        assert property (@(posedge clk) disable iff (!rst_n)
                         is_pma_matched |-> (is_lobound_ok && is_hibound_ok))
          else `uvm_error("mpu", "PMA region match doesn't fit bounds")
      a_pma_match_lowest :
        assert property (@(posedge clk) disable iff (!rst_n)
                         is_pma_matched |-> (pma_match_num == pma_lowest_match))
          else `uvm_error("mpu", "PMA region match wasn't lowest")
      a_pma_match_index :
        assert property (@(posedge clk) disable iff (!rst_n)
                         is_pma_matched |-> ((0 <= pma_match_num) && (pma_match_num < 16)))
          else `uvm_error("mpu", "illegal cfg index")
    end else begin
      a_pma_match_unreachable :
        assert property (@(posedge clk) disable iff (!rst_n)
          is_pma_matched == 0)
        else `uvm_error("mpu", "No PMA regions defined, PMA should not match any address")
    end
  endgenerate

  // RTL vs SVA expectations
  pma_cfg_t    pma_expected_cfg;
  logic        pma_expected_err;
  always_comb begin
    pma_expected_cfg = NO_PMA_R_DEFAULT;
    if (PMA_NUM_REGIONS) begin
      pma_expected_cfg = is_pma_matched ? PMA_CFG[pma_lowest_match] : PMA_R_DEFAULT;
    end
  end
  assign pma_expected_err = (instr_fetch_access && !pma_expected_cfg.main)  ||
                            (misaligned_access_i && !pma_expected_cfg.main);
  a_pma_expect_cfg :
    assert property (@(posedge clk) disable iff (!rst_n) pma_cfg == pma_expected_cfg)
      else `uvm_error("mpu", "RTL cfg don't match SVA expectations")

  generate
    if (bufferable_in_config() && !IS_INSTR_SIDE) begin
    a_pma_expect_bufferable :
      assert property (@(posedge clk) disable iff (!rst_n) bus_trans_bufferable |-> !load_access && pma_expected_cfg.bufferable)
        else `uvm_error("mpu", "expected different bufferable flag")
    end else begin
    a_pma_no_expect_bufferable :
      assert property (@(posedge clk) disable iff (!rst_n) bus_trans_bufferable == '0)
        else `uvm_error("mpu", "expected different bufferable flag")
    end
  endgenerate

  a_pma_expect_cacheable :
    assert property (@(posedge clk) disable iff (!rst_n) bus_trans_cacheable == pma_expected_cfg.cacheable)
      else `uvm_error("mpu", "expected different cacheable flag")
  a_pma_expect_err :
    assert property (@(posedge clk) disable iff (!rst_n) pma_err == pma_expected_err)
      else `uvm_error("mpu", "expected different err flag")

  // Bufferable
  generate
    if (bufferable_in_config() && !IS_INSTR_SIDE) begin
      a_pma_obi_bufon :
        assert property (@(posedge clk) disable iff (!rst_n)
                        obi_memtype[0] |-> (bus_trans_bufferable) ||
                                           (write_buffer_txn_bufferable && write_buffer_valid_o))
          else `uvm_error("mpu", "obi should have had bufferable flag")
    end else begin
      a_pma_obi_bufon_unreachable :
        assert property (@(posedge clk) disable iff (!rst_n)
                         !obi_memtype[0])
          else `uvm_error("mpu", "obi should never have bufferable flag with no bufferable pma regions or on instruction side")
   end
  endgenerate

  a_pma_obi_bufoff :
    assert property (@(posedge clk) disable iff (!rst_n)
                    !obi_memtype[0] |-> !bus_trans_bufferable)
      else `uvm_error("mpu", "obi should not have had bufferable flag")

  // Cacheable
  logic obicache_expected;
  logic obicache_excuse;
  assign obicache_expected = bus_trans_cacheable || (IS_INSTR_SIDE && was_obi_reqnognt && was_obi_memtype[1]);
  assign obicache_excuse = IS_INSTR_SIDE && bus_trans_cacheable && (was_obi_reqnognt && !was_obi_memtype[1]);

  generate
    if (cacheable_in_config()) begin
      a_pma_obi_cacheon :
        assert property (@(posedge clk) disable iff (!rst_n)
                         obi_memtype[1] |-> (obicache_expected && !obicache_excuse) ||
                                            (write_buffer_txn_cacheable && write_buffer_valid_o))
          else `uvm_error("mpu", "obi should have had cacheable flag")
    end else begin
      a_pma_obi_cacheon_unreachable :
        assert property (@(posedge clk) disable iff (!rst_n)
                         !obi_memtype[1])
          else `uvm_error("mpu", "obi should not have had cacheable flag")
    end
  endgenerate

  a_pma_obi_cacheoff :
    assert property (@(posedge clk) disable iff (!rst_n)
                     !obi_memtype[1] |-> !(obicache_expected && !obicache_excuse) ||
                                         (!write_buffer_txn_cacheable && write_buffer_valid_o))
      else `uvm_error("mpu", "obi should not have had cacheable flag")


  // OBI req vs PMA err
  a_pma_obi_reqallowed :
    assert property (@(posedge clk) disable iff (!rst_n)
                     obi_req
                     |->
                     (!pma_err && is_addr_match) ||
                     (write_buffer_state && write_buffer_valid_o) ||
                     (!is_addr_match && was_obi_waiting && $past(obi_req)))
      else `uvm_error("mpu", "obi made request to pma-forbidden region")

  generate
    if (PMA_NUM_REGIONS) begin
      a_pma_obi_reqdenied :
        assert property (@(posedge clk) disable iff (!rst_n)
                         pma_err
                         |-> !obi_req ||
                             (was_obi_waiting && $past(obi_req)) ||
                             (write_buffer_state && write_buffer_valid_o))
          else `uvm_error("mpu", "pma error should forbid obi req")
    end else begin
      a_pma_obi_reqdenied :
        assert property (@(posedge clk) disable iff (!rst_n)
                        !pma_err)
        else `uvm_error("mpu", "pma deconfigured, should not trigger error")
    end
  endgenerate

  // Cover PMA signals

  covergroup cg_pma @(posedge clk);
    cp_err: coverpoint pma_err;
    cp_instr: coverpoint instr_fetch_access;
    cp_bufferable: coverpoint bus_trans_bufferable;
    cp_cacheable: coverpoint bus_trans_cacheable;
    cp_addr: coverpoint pma_addr[31:2] {
      bins min = {0};
      bins max = {30'h 3FFF_FFFF};
      bins range[3] = {[1 : 30'h 3FFF_FFFe]};
      illegal_bins il = default;
      }

    x_err_instr: cross cp_err, cp_instr;
    x_err_bufferable: cross cp_err, cp_bufferable;
    x_err_cacheable: cross cp_err, cp_cacheable;
  endgroup
  `ifndef FORMAL
    cg_pma cgpma = new;
  `endif

  `ifndef FORMAL
    cov_pma_nondefault :
      cover property (@(posedge clk) disable iff (!rst_n)
        (pma_cfg != PMA_R_DEFAULT) && bus_trans_valid_o);
  `endif

  // MPU FSM and bus interface should never assert trans valid at the same time
  a_mpu_bus_mpu_err_valid :
    assert property (@(posedge clk) disable iff (!rst_n)
                     (! (bus_resp_valid_i && mpu_err_trans_valid) ))
      else `uvm_error("mpu", "MPU FSM and bus interface response collision")

  generate
    if (PMA_NUM_REGIONS) begin
      // Should only give MPU error response during mpu_err_trans_valid
      a_mpu_status_no_obi_rvalid :
        assert property (@(posedge clk) disable iff (!rst_n)
                         (mpu_status != MPU_OK) |-> (mpu_err_trans_valid) )
          else `uvm_error("mpu", "MPU error status wile not mpu_err_trans_valid")

      // Should only block core side upon when waiting for MPU error response
      a_mpu_block_core_iff_wait :
        assert property (@(posedge clk) disable iff (!rst_n)
                         (mpu_block_core) |-> (state_q != MPU_IDLE) )
          else `uvm_error("mpu", "MPU blocking core side when not needed")

      // Should only block OBI side upon MPU error
      a_mpu_block_bus_iff_err :
        assert property (@(posedge clk) disable iff (!rst_n)
                         (mpu_block_bus) |-> (mpu_err || (state_q != MPU_IDLE)) )
          else `uvm_error("mpu", "MPU blocking OBI side when not needed")
        end
  endgenerate


    // PMP checks

    logic any_pmp_locked;
    logic exp_rlb_locked_low;

    always_comb begin
      any_pmp_locked = 1'b0;
      for(int i=0; i < PMP_NUM_REGIONS; i++) begin
        if (csr_pmp_i.cfg[i].lock) begin
          any_pmp_locked = 1'b1;
        end
      end
    end

    always_ff @(posedge clk, negedge rst_n) begin
      if(!rst_n) begin
        exp_rlb_locked_low <= 1'b0;
      end
      else begin
        exp_rlb_locked_low <= exp_rlb_locked_low || (any_pmp_locked && !csr_pmp_i.mseccfg.rlb);
      end
    end

    generate for (genvar i = 0; i < PMP_NUM_REGIONS; i++)
    begin : a_pmp_gen

      a_csr_pmp_no_rw_01:
        assert property (@(posedge clk) disable iff (!rst_n)
                         !csr_pmp_i.mseccfg.mml && $changed(csr_pmp_i.cfg[i])
                         |-> {csr_pmp_i.cfg[i].read, csr_pmp_i.cfg[i].write} != 2'b01)
          else `uvm_error("mpu", "{pmpcfg.read, pmpcfg.write} set to reserved value (RW=01)")

      a_csr_pmp_no_new_mmode_execute:
        assert property (@(posedge clk) disable iff (!rst_n)
                         csr_pmp_i.mseccfg.mml && !csr_pmp_i.mseccfg.rlb && $changed(csr_pmp_i.cfg[i])
                         |->
                         ({csr_pmp_i.cfg[i].lock, csr_pmp_i.cfg[i].read, csr_pmp_i.cfg[i].write, csr_pmp_i.cfg[i].exec} != 4'b1001) &&
                         ({csr_pmp_i.cfg[i].lock, csr_pmp_i.cfg[i].read, csr_pmp_i.cfg[i].write, csr_pmp_i.cfg[i].exec} != 4'b1010) &&
                         ({csr_pmp_i.cfg[i].lock, csr_pmp_i.cfg[i].read, csr_pmp_i.cfg[i].write, csr_pmp_i.cfg[i].exec} != 4'b1011) &&
                         ({csr_pmp_i.cfg[i].lock, csr_pmp_i.cfg[i].read, csr_pmp_i.cfg[i].write, csr_pmp_i.cfg[i].exec} != 4'b1101))
          else `uvm_error("mpu", "Violation of Smepmp v1.0 spec, requirement 4b")

      a_csr_pmp_unlock_rlb:
        assert property (@(posedge clk) disable iff (!rst_n)
                         (##1 $fell(csr_pmp_i.cfg[i].lock))
                         |-> csr_pmp_i.mseccfg.rlb)
          else `uvm_error("mpu", "PMP region unlocked with mseccfg.rlb cleared")

      a_csr_pmp_addr_lock:
        assert property (@(posedge clk) disable iff (!rst_n)
                         ($changed(csr_pmp_i.addr[i]))
                         |-> !(csr_pmp_i.cfg[i].lock && !csr_pmp_i.mseccfg.rlb))
          else `uvm_error("mpu", "PMP address changed when it should be locked")

      if(i < PMP_NUM_REGIONS-1) begin: pmp_tor_lock
        a_csr_pmp_addr_lock_tor:
          assert property (@(posedge clk) disable iff (!rst_n)
                           ($changed(csr_pmp_i.addr[i]))
                           |-> !((csr_pmp_i.cfg[i+1].mode == PMP_MODE_TOR) && csr_pmp_i.cfg[i+1].lock && !csr_pmp_i.mseccfg.rlb))
            else `uvm_error("mpu", "PMP address changed when it should be locked through TOR mode on the next PMP region")
      end
    end
    endgenerate

    a_csr_pmp_rlb:
      assert property (@(posedge clk) disable iff (!rst_n)
                       ($rose(csr_pmp_i.mseccfg.rlb))
                       |-> !exp_rlb_locked_low)
        else `uvm_error("mpu", "mseccfg.rlb set after being locked.")

    a_csr_pmp_mml_sticky:
      assert property (@(posedge clk) disable iff (!rst_n)
                       ##1 !$fell(csr_pmp_i.mseccfg.mml))
        else `uvm_error("mpu", "mseccfg.mml not sticky.")

    a_csr_pmp_mmwp_sticky:
      assert property (@(posedge clk) disable iff (!rst_n)
                       ##1 !$fell(csr_pmp_i.mseccfg.mmwp))
        else `uvm_error("mpu", "mseccfg.mmwp not sticky.")

    // Support logic (FIFO) to track integrity attribute for outstanding transactions

    localparam MAX_OUTSTND_TXN = 5; // This needs to be larger (or equal) to the max outstanding transactions in IF and LSU

    typedef enum logic [1:0] {PMA_INT, PMA_NOINT, PMA_NONE} pma_int_chck_e;
    logic exp_integrity;
    logic [$clog2(MAX_OUTSTND_TXN)-1:0] oldest_txn;

    pma_int_chck_e [MAX_OUTSTND_TXN-1:0] pma_integrity_fifo_q;
    pma_int_chck_e [MAX_OUTSTND_TXN-1:0] pma_integrity_fifo_n;
    pma_int_chck_e [MAX_OUTSTND_TXN-1:0] pma_integrity_fifo_tmp;

    always_comb begin
      pma_integrity_fifo_n   = pma_integrity_fifo_q;
      pma_integrity_fifo_tmp = pma_integrity_fifo_q;

      casez ({core_trans_valid_i, core_trans_ready_o, core_resp_valid_o})
          3'b110: begin
            // Accepted address phase, add one entry to FIFO
            pma_integrity_fifo_n = pma_integrity ?
                                   {pma_integrity_fifo_q[MAX_OUTSTND_TXN-2:0], PMA_INT} :
                                   {pma_integrity_fifo_q[MAX_OUTSTND_TXN-2:0], PMA_NOINT};
          end
          3'b0?1, 3'b?01: begin
            // Response phase, remove oldest entry from FIFO
            pma_integrity_fifo_n[oldest_txn] = PMA_NONE;
          end
          3'b111: begin
            // Accepted address phase and response phase. Clear oldest transaction and add new to FIFO
            pma_integrity_fifo_tmp[oldest_txn] = PMA_NONE;
            pma_integrity_fifo_n = pma_integrity ?
                                   {pma_integrity_fifo_tmp[MAX_OUTSTND_TXN-2:0], PMA_INT} :
                                   {pma_integrity_fifo_tmp[MAX_OUTSTND_TXN-2:0], PMA_NOINT};
          end
          default; // Do nothing
        endcase
    end

    // FIFO
    always_ff @ (posedge clk, negedge rst_n) begin
      if (!rst_n) begin
        pma_integrity_fifo_q <= {MAX_OUTSTND_TXN{PMA_NONE}};
      end
      else begin
        pma_integrity_fifo_q <= pma_integrity_fifo_n;
      end
    end

    // Locate oldest entry in FIFO
    always_comb begin
      oldest_txn = '0;
      for (int i = 0;  i < MAX_OUTSTND_TXN; i++) begin
        if (pma_integrity_fifo_q[i] != PMA_NONE) begin
          oldest_txn = i;
        end
      end
    end

    // Integrity attribute from the oldest transaction
    assign exp_integrity = (pma_integrity_fifo_q[oldest_txn] == PMA_INT);

    // Assert that integrity bit from MPU corresponds to the expected value
    a_pma_integrity :
      assert property (@(posedge clk) disable iff (!rst_n)
                       core_resp_valid_o |-> exp_integrity == core_resp_o_integrity)
        else `uvm_error("mpu", "PMA integrity attribute not correct")

endmodule : cv32e40s_mpu_sva

