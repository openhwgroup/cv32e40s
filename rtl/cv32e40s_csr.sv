// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control / status register primitive
 */


module cv32e40s_csr #(
    parameter                 LIB = 0,
    parameter int unsigned    WIDTH = 32,
    parameter bit             SHADOWCOPY = 1'b0,
    parameter bit [WIDTH-1:0] RESETVALUE = '0,
    parameter bit [WIDTH-1:0] MASK = {WIDTH{1'b1}}
 ) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             scan_cg_en_i,

    input  logic [WIDTH-1:0] wr_data_i,
    input  logic             wr_en_i,
    output logic [WIDTH-1:0] rd_data_o,

    output logic             rd_error_o
);

  logic [WIDTH-1:0]          rdata_q;

  assign rd_data_o = rdata_q;

  generate
    if (SHADOWCOPY) begin : gen_hardened
      logic             clk_gated;
      logic [WIDTH-1:0] rdata_d;
      logic [WIDTH-1:0] shadow_d;
      logic [WIDTH-1:0] shadow_q;

      assign rdata_d    =  wr_data_i;
      assign shadow_d   = ~wr_data_i;
      assign rd_error_o = rdata_q != ~shadow_q;

      cv32e40s_clock_gate
        #(.LIB(LIB))
        core_clock_gate_i
        (.clk_i        ( clk          ),
         .en_i         ( wr_en_i      ),
         .scan_cg_en_i ( scan_cg_en_i ),
         .clk_o        ( clk_gated    ));

      // The shadow registers are logically redundant and are therefore easily optimized away by most synthesis tools.
      // These registers are therefore implemented as instantiated cells so that they can be preserved in the synthesis script.
      for (genvar i = 0; i < WIDTH; i++) begin : gen_csr_hardened
        if (MASK[i]) begin : gen_unmasked_hardened
          if (RESETVALUE[i] == 1'b1) begin : gen_rv1
            cv32e40s_sffs #(.LIB(LIB)) sffs_rdatareg  (.clk(clk_gated), .rst_n(rst_n), .d_i(rdata_d[i]),  .q_o(rdata_q[i]));
            cv32e40s_sffr #(.LIB(LIB)) sffr_shadowreg (.clk(clk_gated), .rst_n(rst_n), .d_i(shadow_d[i]), .q_o(shadow_q[i]));
          end else begin : gen_rv0 // (RESETVALUE[i] == 1'b0)
            cv32e40s_sffr #(.LIB(LIB)) sffr_rdatareg  (.clk(clk_gated), .rst_n(rst_n), .d_i(rdata_d[i]),  .q_o(rdata_q[i]));
            cv32e40s_sffs #(.LIB(LIB)) sffs_shadowreg (.clk(clk_gated), .rst_n(rst_n), .d_i(shadow_d[i]), .q_o(shadow_q[i]));
          end
        end else begin : gen_masked_hardened
          if (RESETVALUE[i] == 1'b1) begin : gen_constant_1
            assign rdata_q[i]  = 1'b1;
            assign shadow_q[i] = 1'b0;
          end else begin : gen_constant_0
            assign rdata_q[i]  = 1'b0;
            assign shadow_q[i] = 1'b1;
          end
        end
      end

    end else begin : gen_unhardened
      for (genvar i = 0; i < WIDTH; i++) begin : gen_csr_unhardened
        if (MASK[i]) begin : gen_unmasked_unhardened
          // Bits with mask set are actual flipflops
          always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
              rdata_q[i] <= RESETVALUE[i];
            end else if (wr_en_i) begin
              rdata_q[i] <= wr_data_i[i];
            end
          end
        end else begin : gen_masked_unhardened
          // Bits with mask cleared are tied off to the reset value
          assign rdata_q[i] = RESETVALUE[i];
        end
      end // for
      assign rd_error_o = 1'b0;
    end
  endgenerate

endmodule
