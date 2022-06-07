// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Authors:        Renzo Andri - andrire@student.ethz.ch                      //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the if_stage module                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_if_stage_sva
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
(
  input  logic          clk,
  input  logic          rst_n,

  input logic           if_ready,
  input logic           if_valid_o,
  input logic [31:0]    pc_if_o,
  input logic           prefetch_resp_valid,
  input ctrl_fsm_t      ctrl_fsm_i,
  input privlvl_t       prefetch_priv_lvl,
  input logic           dummy_insert,
  input if_id_pipe_t    if_id_pipe_o,
  if_c_obi.monitor      m_c_obi_instr_if,
  input logic [31:0]    mstateen0_i,
  input logic           tbljmp
);

  // Check that bus interface transactions are halfword aligned (will be forced word aligned at core boundary)
  property p_instr_addr_aligned;
    @(posedge clk) (1'b1) |-> (m_c_obi_instr_if.req_payload.addr[0] == 1'b0);
  endproperty

  a_instr_addr_aligned : assert property(p_instr_addr_aligned)
    else `uvm_error("if_stage", "Assertion a_instr_addr_aligned failed")

  // Halt implies not ready and not valid
  a_halt :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.halt_if && !ctrl_fsm_i.kill_if)
                      |-> (!if_ready && !if_valid_o))
      else `uvm_error("if_stage", "Halt should imply not ready and not valid")

  // Kill implies ready and not valid
  a_kill :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (ctrl_fsm_i.kill_if)
                      |-> (if_ready && !if_valid_o))
      else `uvm_error("if_stage", "Kill should imply ready and not valid")


  // Helper logic for a_priv_lvl_change
  logic priv_lvl_change;
  privlvl_t new_priv_lvl;

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      priv_lvl_change <= 1'b0;
      new_priv_lvl    <= PRIV_LVL_M;
    end
    else begin
      if ($changed(prefetch_priv_lvl)) begin
        priv_lvl_change <= 1'b1;
        new_priv_lvl    <= prefetch_priv_lvl;
      end
      if (if_id_pipe_o.instr_valid) begin
        priv_lvl_change <= 1'b0;
      end
    end
  end

  // Assert that upon a privilege level change, the next instruction passed to ID has the correct privilege level
  a_priv_lvl_change :
    assert property (@(posedge clk) disable iff (!rst_n)
                     priv_lvl_change && if_id_pipe_o.instr_valid |->
                     if_id_pipe_o.priv_lvl == new_priv_lvl)
    else `uvm_error("if_stage", "Wrong privilege level sent to ID stage")

  // Assert that the prefetcher is never popped during a dummy instruction unless it's killed
  a_never_pop_prefetcher_on_dummy :
    assert property (@(posedge clk) disable iff (!rst_n)
                     dummy_insert && prefetch_resp_valid && !ctrl_fsm_i.kill_if |=> (ctrl_fsm_i.kill_if || (pc_if_o === $past(pc_if_o))))
      else `uvm_error("if_stage", "Prefetcher popped during dummy instruction")

  // Assert that we do not trigger dummy instructions multiple cycles in a row
  // Todo: When/if we use allow_dummy_instr from controller_fsm to guarantee progress,
  //       this assertion should be updated to check for guaranteed progress
  a_no_back_to_back_dummy_instructions :
    assert property (@(posedge clk) disable iff (!rst_n)
                     dummy_insert |-> !$past(dummy_insert))
      else `uvm_error("if_stage", "Two dummy instructions in a row")


  // No table jumps may occur in user mode while mstateen0[2] is 0
  a_no_illegal_tablejumps :
    assert property (@(posedge clk) disable iff (!rst_n)
                      (prefetch_priv_lvl == PRIV_LVL_U) && !mstateen0_i[2] |-> !tbljmp)
      else `uvm_error("if_stage", "Table jump in user mode without state permissions.")

endmodule // cv32e40s_if_stage

