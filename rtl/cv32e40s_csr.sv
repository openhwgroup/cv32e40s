// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control / status register primitive
 */


module cv32e40s_csr #(
    parameter int unsigned    WIDTH = 32,
    parameter bit             SHADOWCOPY = 1'b0,
    parameter bit [WIDTH-1:0] RESETVALUE = '0,
    parameter bit [WIDTH-1:0] MASK = {WIDTH{1'b1}}
 ) (
    input  logic             clk,
    input  logic             rst_n,

    input  logic [WIDTH-1:0] wr_data_i,
    input  logic             wr_en_i,
    output logic [WIDTH-1:0] rd_data_o,

    output logic             rd_error_o
);

  logic [WIDTH-1:0] rdata_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rdata_q <= RESETVALUE & MASK;
    end else if (wr_en_i) begin
      rdata_q <= wr_data_i & MASK;
    end
  end

  assign rd_data_o = rdata_q;

  generate
    if (SHADOWCOPY) begin : gen_shadow
      // The shadow registers are logically redundant and are therefore easily optimized away by most synthesis tools.
      // These registers are therefore implemented as instantiated cells so that they can be preserved in the synthesis script.

      logic [WIDTH-1:0] shadow_q;
      logic [WIDTH-1:0] shadow_d;

      for (genvar i = 0; i < WIDTH; i++) begin : gen_shadow_regs
        if (MASK[i]) begin : gen_unmasked
          assign shadow_d[i] = wr_en_i ? wr_data_i[i] : shadow_q[i];
          if (RESETVALUE[i] == 1'b1) begin : gen_rv1
            cv32e40s_sffs sffs_shadowreg (.clk(clk), .set_n(rst_n), .d_i(shadow_d[i]), .q_o(shadow_q[i]));
          end else begin : gen_rv0 // (RESETVALUE[i] == 1'b0)
            cv32e40s_sffr sffr_shadowreg (.clk(clk), .rst_n(rst_n), .d_i(shadow_d[i]), .q_o(shadow_q[i]));
          end
        end else begin : gen_masked
          assign shadow_q[i] = 1'b0;
        end
      end

    assign rd_error_o = rdata_q != ~shadow_q;

  end else begin : gen_no_shadow
    assign rd_error_o = 1'b0;
  end

  endgenerate

endmodule
