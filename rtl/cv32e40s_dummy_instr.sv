// Copyright 2021 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    cv32e40s_dummy_instr                                       //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Generates random instructions for                          //
//                 random dummy instruction insertion                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module cv32e40s_dummy_instr
  import cv32e40s_pkg::*;
  #()
  (input  logic          clk,
   input  logic          rst_n,
   input  logic          instr_issued_i,
   input  ctrl_fsm_t     ctrl_fsm_i,
   input  xsecure_ctrl_t xsecure_ctrl_i,
   output logic          dummy_insert_o,
   output inst_resp_t    dummy_instr_o
  );

  localparam MAX_DUMMY_INTERVAL = 64;
  // Counter needs to count to one more than MAX_DUMMY_INTERVAL because we are
  // comparing with > to get the 1 to MAX_DUMMY_INTERVAL range (the lfsr_cnt range is 0 to MAX_DUMMY_INTERVAL-1)
  localparam CNT_WIDTH = $clog2(MAX_DUMMY_INTERVAL+1);

  localparam logic [2:0] FUNCT3_ADD  = 3'b000;
  localparam logic [2:0] FUNCT3_MUL  = 3'b000;
  localparam logic [2:0] FUNCT3_AND  = 3'b111;
  localparam logic [2:0] FUNCT3_BLTU = 3'b110;

  localparam logic [6:0] FUNCT7_ADD  = 7'b000_0000;
  localparam logic [6:0] FUNCT7_MUL  = 7'b000_0001;
  localparam logic [6:0] FUNCT7_AND  = 7'b000_0000;

  opcode_e      opcode;
  logic [ 6:0]  funct7;
  logic [ 4:0]  rd;
  logic [ 2:0]  funct3;
  logic [12:0]  imm;
  logic [31:0]  instr;

  logic         dummy_en;

  logic [CNT_WIDTH-1:0] cnt_q;
  logic [CNT_WIDTH-1:0] cnt_next;
  logic                 cnt_rst;

  logic [1:0]   lfsr_instr;
  logic [4:0]   lfsr_rs1;
  logic [4:0]   lfsr_rs2;
  logic [5:0]   lfsr_cnt;

  assign lfsr_instr = xsecure_ctrl_i.lfsr0[ 1: 0];
  assign lfsr_rs1   = xsecure_ctrl_i.lfsr0[12: 8];
  assign lfsr_rs2   = xsecure_ctrl_i.lfsr0[20:16];
  assign lfsr_cnt   = xsecure_ctrl_i.lfsr0[29:24] & {xsecure_ctrl_i.cpuctrl.rnddummyfreq, 2'b11};

  assign dummy_en   = ctrl_fsm_i.allow_dummy_instr && xsecure_ctrl_i.cpuctrl.rnddummy;

  assign dummy_insert_o = (cnt_q > lfsr_cnt) && dummy_en;

  assign cnt_rst        = !dummy_en      ||      // Reset counter when dummy instructions are disabled
                          dummy_insert_o ||      // Reset counter when inserting dummy instruction
                          xsecure_ctrl_i.cntrst; // Reset counter when requested by xsecure_ctrl (due to csr updates)

  assign cnt_next       = cnt_rst        ? '0           : // Reset counter
                          instr_issued_i ? cnt_q + 1'b1 : // Count issued instructions only
                                           cnt_q;

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      if (xsecure_ctrl_i.cpuctrl.rnddummy) begin
        cnt_q <= cnt_next;
      end
    end
  end

  always_comb begin
    unique case (lfsr_instr)
      2'b00 : begin // ADD
        funct3 = FUNCT3_ADD;
        funct7 = FUNCT7_ADD;
        opcode = OPCODE_OP;
      end
      2'b01 : begin // MUL
        funct3 = FUNCT3_MUL;
        funct7 = FUNCT7_MUL;
        opcode = OPCODE_OP;
      end
      2'b10 : begin // AND
        funct3 = FUNCT3_AND;
        funct7 = FUNCT7_AND;
        opcode = OPCODE_OP;
      end
      2'b11 : begin // BLTU
        funct3 = FUNCT3_BLTU;
        funct7 = 7'h0; // Funct7 bits not used for B-type instructions
        opcode = OPCODE_BRANCH;
      end
    endcase // unique case (lfsr[31:30])
  end

  assign rd  =  5'h0; // Ignoring result by writing it to x0
  assign imm = 12'h0; // Offset is 0 because PC of the dummy instruction is the same as the target instruction.

  assign instr[31:25] = (opcode == OPCODE_BRANCH) ? {imm[12], imm[10:5]} : funct7;
  assign instr[24:20] = lfsr_rs2;
  assign instr[19:15] = lfsr_rs1;
  assign instr[14:12] = funct3;
  assign instr[11: 7] = (opcode == OPCODE_BRANCH) ? {imm[4:1], imm[11]}  : rd;
  assign instr[ 6: 0] = opcode;

  assign dummy_instr_o.bus_resp.rdata = instr;
  assign dummy_instr_o.bus_resp.err   = 1'b0;
  assign dummy_instr_o.mpu_status     = MPU_OK;

endmodule : cv32e40s_dummy_instr
