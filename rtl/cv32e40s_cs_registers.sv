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
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.9)        //
//                 Added Floating point support                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40s_cs_registers import cv32e40s_pkg::*;
#(
  parameter A_EXTENSION      = 0,
  parameter USE_PMP          = 0, // TODO:OE remove this if not needed
  parameter PMP_NUM_REGIONS  = 4,
  parameter PMP_GRANULARITY  = 0,
  parameter NUM_MHPMCOUNTERS = 1
)
(
  // Clock and Reset
  input  logic            clk,
  input  logic            rst_n,

  // Hart ID
  input  logic [31:0]     hart_id_i,
  output logic [23:0]     mtvec_addr_o,
  output logic  [1:0]     mtvec_mode_o,
  
  // Used for mtvec address
  input  logic [31:0]     mtvec_addr_i,
  input  logic            csr_mtvec_init_i,

  // IF/ID pipeline
  input if_id_pipe_t      if_id_pipe_i,

  // ID/EX pipeline 
  input id_ex_pipe_t      id_ex_pipe_i,

  // EX/WB pipeline
  input ex_wb_pipe_t      ex_wb_pipe_i,

  // From controller FSM
  input  ctrl_fsm_t       ctrl_fsm_i,

  // To controller bypass logic
  output csr_num_e        csr_raddr_o,
 
  // Interface to registers (SRAM like)
  output logic [31:0]     csr_rdata_o,

  // Interrupts
  output logic [31:0]     mie_o,
  input  logic [31:0]     mip_i,
  output logic            m_irq_enable_o,
  
  output logic [31:0]     mepc_o,

  // PMP CSR's
  output pmp_cfg_t        csr_pmp_cfg_o [PMP_NUM_REGIONS],
  output logic [33:0]     csr_pmp_addr_o [PMP_NUM_REGIONS],
  output pmp_mseccfg_t    csr_pmp_mseccfg_o,

  // debug
  output logic [31:0]     dpc_o,
  output logic            debug_single_step_o,
  output logic            debug_ebreakm_o,
  output logic            debug_trigger_match_o,

  output PrivLvl_t        priv_lvl_o,

  input  logic [31:0]     pc_if_i
);

  
  localparam logic [31:0] MISA_VALUE =
  (32'(A_EXTENSION)                     <<  0)  // A - Atomic Instructions extension
| (32'(1)                               <<  2)  // C - Compressed extension
| (32'(0)                               <<  3)  // D - Double precision floating-point extension
| (32'(0)                               <<  4)  // E - RV32E base ISA
| (32'(0)                               <<  5)  // F - Single precision floating-point extension
| (32'(1)                               <<  8)  // I - RV32I/64I/128I base ISA
| (32'(1)                               << 12)  // M - Integer Multiply/Divide extension
| (32'(0)                               << 13)  // N - User level interrupts supported
| (32'(0)                               << 18)  // S - Supervisor mode implemented
| (32'(0)                               << 20)  // U - User mode implemented
| (32'(0)                          << 23)  // X - Non-standard extensions present
| (32'(MXL)                        << 30); // M-XLEN


  localparam PMP_ADDR_WIDTH = (PMP_GRANULARITY > 0) ? 33 - PMP_GRANULARITY : 32;
  
  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;

  // Interrupt control signals
  logic [31:0] mepc_q, mepc_n;
  logic mepc_we;
  logic mepc_rd_error;

  // Trigger
  logic [31:0] tmatch_control_rdata;
  logic [31:0] tmatch_value_rdata;
  logic [15:0] tinfo_types;
  // Debug
  Dcsr_t       dcsr_q, dcsr_n;
  logic dcsr_we;
  logic dcsr_rd_error;
  logic [31:0] dpc_q, dpc_n;
  logic dpc_we;
  logic dpc_rd_error;

  logic [31:0] dscratch0_q, dscratch0_n;
  logic dscratch0_we, dscratch1_we;
  logic dscratch0_rd_error, dscratch1_rd_error;
  logic [31:0] dscratch1_q, dscratch1_n;

  logic [31:0] mscratch_q, mscratch_n;
  logic mscratch_we;
  logic mscratch_rd_error;

  logic [31:0] exception_pc;
  Status_t mstatus_q, mstatus_n;
  logic mstatus_we;
  logic mstatus_rd_error;

  Mcause_t mcause_q, mcause_n;
  logic mcause_we;
  logic mcause_rd_error;

  Mtvec_t mtvec_n, mtvec_q;
  logic mtvec_we;
  logic mtvec_rd_error;

  logic [31:0] mip;                     // Bits are masked according to IRQ_MASK
  logic [31:0] mie_q, mie_n;            // Bits are masked according to IRQ_MASK
  logic mie_we;
  logic mie_rd_error;

  pmp_cfg_t     pmp_cfg_q[PMP_NUM_REGIONS];
  logic [PMP_CFG_W-1:0]   pmp_cfg_rdata[PMP_MAX_REGIONS];
  logic [PMP_ADDR_WIDTH-1:0]  pmp_addr_q[PMP_NUM_REGIONS];
  logic [31:0]  pmp_addr_rdata[PMP_MAX_REGIONS];
  pmp_mseccfg_t pmp_mseccfg_q;
  logic [31:0]  pmp_mseccfg_rdata;

  logic [PMP_MAX_REGIONS-1:0] pmp_cfg_we;
  logic [PMP_MAX_REGIONS-1:0] pmp_addr_we;
  logic                       pmp_mseccfg_we;

  logic [PMP_NUM_REGIONS-1:0] pmp_cfg_locked;
  logic [PMP_NUM_REGIONS-1:0] pmp_cfg_we_qual;
  logic [PMP_NUM_REGIONS-1:0] pmp_addr_we_qual;
  
  logic [PMP_NUM_REGIONS-1:0] pmp_cfg_rd_error;
  logic [PMP_NUM_REGIONS-1:0] pmp_addr_rd_error;
  logic                       pmp_mseccfg_rd_error;
  logic                       pmp_rd_error;
  
  PrivLvl_t priv_lvl_n, priv_lvl_q;

  // Performance Counter Signals
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_q;                    // performance counters
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_n;                    // performance counters next value
  logic [31:0] [1:0]                   mhpmcounter_we;                   // performance counters write enable
  logic [31:0] [31:0]                  mhpmevent_q, mhpmevent_n;         // event enable
  logic [31:0]                         mcountinhibit_q, mcountinhibit_n; // performance counter enable
  logic [NUM_HPM_EVENTS-1:0]           hpm_events;                       // events for performance counters
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_increment;            // increment of mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_lower;          // write 32 lower bits of mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_upper;          // write 32 upper bits mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_increment;      // write increment of mhpmcounter_q


  csr_opcode_e csr_op;
  csr_num_e    csr_waddr;
  csr_num_e    csr_raddr;
  logic [31:0] csr_wdata;

  //  CSR access. Read in EX, write in WB
  // Setting csr_raddr to zero in case of unused csr to save power (alu_operand_b toggles a lot)
  assign csr_raddr = csr_num_e'((id_ex_pipe_i.csr_en && id_ex_pipe_i.instr_valid) ? id_ex_pipe_i.alu_operand_b[11:0] : 12'b0);
  assign csr_raddr_o = csr_raddr;

  // Not suppressing csr_waddr to zero when unused since its source are dedicated flipflops and would not save power as for raddr
  assign csr_waddr = csr_num_e'(ex_wb_pipe_i.csr_addr);
  assign csr_wdata = ex_wb_pipe_i.csr_wdata;

  //TODO:OK We should have a better way for killing CSR insn other than forcing csr_op to CSR_OP_READ (csr_en already exists in pipeline)
  assign csr_op       =  (!ctrl_fsm_i.kill_wb && ex_wb_pipe_i.instr_valid) ? ex_wb_pipe_i.csr_op : CSR_OP_READ;
    
  // mip CSR
  assign mip = mip_i;


  ////////////////////////////////////////////
  //   ____ ____  ____    ____              //
  //  / ___/ ___||  _ \  |  _ \ ___  __ _   //
  // | |   \___ \| |_) | | |_) / _ \/ _` |  //
  // | |___ ___) |  _ <  |  _ <  __/ (_| |  //
  //  \____|____/|_| \_\ |_| \_\___|\__, |  //
  //                                |___/   //
  ////////////////////////////////////////////

  // NOTE!!!: Any new CSR register added in this file must also be
  //   added to the valid CSR register list cv32e40s_decoder.v

  // read logic
  always_comb
  begin
    case (csr_raddr)
      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: csr_rdata_int = mstatus_q;
      // misa: machine isa register
      CSR_MISA: csr_rdata_int = MISA_VALUE;
      // mie: machine interrupt enable
      CSR_MIE: csr_rdata_int = mie_q;
      // mtvec: machine trap-handler base address
      CSR_MTVEC: csr_rdata_int = mtvec_q;
      // mscratch: machine scratch
      CSR_MSCRATCH: csr_rdata_int = mscratch_q;
      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;
      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = mcause_q;
      // mip: interrupt pending
      CSR_MIP: csr_rdata_int = mip;
      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = hart_id_i;

      // mvendorid: Machine Vendor ID
      CSR_MVENDORID: csr_rdata_int = {MVENDORID_BANK, MVENDORID_OFFSET};

      // marchid: Machine Architecture ID
      CSR_MARCHID: csr_rdata_int = MARCHID;

      // unimplemented, read 0 CSRs
      CSR_MIMPID,
        CSR_MTVAL :
          csr_rdata_int = 'b0;

      CSR_TSELECT,
        CSR_TDATA3,
        CSR_MCONTEXT,
        CSR_SCONTEXT:
              csr_rdata_int = 'b0; // Always read 0
      CSR_TDATA1:
              csr_rdata_int = tmatch_control_rdata;
      CSR_TDATA2:
              csr_rdata_int = tmatch_value_rdata;
      CSR_TINFO:
              csr_rdata_int = tinfo_types;

      CSR_DCSR:
              csr_rdata_int = dcsr_q;
      CSR_DPC:
              csr_rdata_int = dpc_q;
      CSR_DSCRATCH0:
              csr_rdata_int = dscratch0_q;
      CSR_DSCRATCH1:
              csr_rdata_int = dscratch1_q;

      // Hardware Performance Monitor
      CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
      CSR_CYCLE,
      CSR_INSTRET,
      CSR_HPMCOUNTER3,
      CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
      CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
      CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
      CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
      CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
      CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
      CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31:
        csr_rdata_int = mhpmcounter_q[csr_raddr[4:0]][31:0];

      CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
      CSR_CYCLEH,
      CSR_INSTRETH,
      CSR_HPMCOUNTER3H,
      CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
      CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
      CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
      CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
      CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
      CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
      CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H:
        csr_rdata_int = (MHPMCOUNTER_WIDTH == 64) ? mhpmcounter_q[csr_raddr[4:0]][63:32] : '0;

      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;

      CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31:
        csr_rdata_int = mhpmevent_q[csr_raddr[4:0]];

      CSR_PMPCFG0: 
        csr_rdata_int = {pmp_cfg_rdata[3],  pmp_cfg_rdata[2],  pmp_cfg_rdata[1],  pmp_cfg_rdata[0]};
      CSR_PMPCFG1:   
        csr_rdata_int = {pmp_cfg_rdata[7],  pmp_cfg_rdata[6],  pmp_cfg_rdata[5],  pmp_cfg_rdata[4]};
      CSR_PMPCFG2:   
        csr_rdata_int = {pmp_cfg_rdata[11], pmp_cfg_rdata[10], pmp_cfg_rdata[9],  pmp_cfg_rdata[8]};
      CSR_PMPCFG3:   
        csr_rdata_int = {pmp_cfg_rdata[15], pmp_cfg_rdata[14], pmp_cfg_rdata[13], pmp_cfg_rdata[12]};

      CSR_PMPADDR0, CSR_PMPADDR1, CSR_PMPADDR2, CSR_PMPADDR3,
      CSR_PMPADDR4, CSR_PMPADDR5, CSR_PMPADDR6, CSR_PMPADDR7,
      CSR_PMPADDR8, CSR_PMPADDR9, CSR_PMPADDR10, CSR_PMPADDR11,
      CSR_PMPADDR12, CSR_PMPADDR13, CSR_PMPADDR14, CSR_PMPADDR15:
        csr_rdata_int = pmp_addr_rdata[csr_raddr[3:0]];

      CSR_PMPMSECCFG0:
        csr_rdata_int = pmp_mseccfg_rdata;
        
      default:
        csr_rdata_int = '0;
    endcase
  end



  // write logic
  always_comb
  begin
    mscratch_n               = csr_wdata_int;
    mscratch_we              = 1'b0;
    mepc_n                   = csr_wdata_int & ~32'b1;
    mepc_we                  = 1'b0;
    dpc_n                    = csr_wdata_int & ~32'b1;
    dpc_we                   = 1'b0; 

    dcsr_n                   = '{
                                xdebugver : dcsr_q.xdebugver,
                                ebreakm   : csr_wdata_int[15],
                                stepie    : csr_wdata_int[11],
                                step      : csr_wdata_int[2],
                                prv       : PRIV_LVL_M,
                                cause     : dcsr_q.cause,
                                default   : 'd0
                             };
    dcsr_we                  = 1'b0;

    dscratch0_n              = csr_wdata_int;
    dscratch0_we             = 1'b0;
    dscratch1_n              = csr_wdata_int;
    dscratch1_we             = 1'b0;

    mstatus_n                = '{
                              mprv: 1'b0,
                              mpp:  PRIV_LVL_M,
                              mpie: csr_wdata_int[MSTATUS_MPIE_BIT],
                              mie:  csr_wdata_int[MSTATUS_MIE_BIT],
                              default: 'b0
                            };
    mstatus_we    = 1'b0;
    mcause_n      = {csr_wdata_int[31], 26'd0, csr_wdata_int[4:0]};
    mcause_we     = 1'b0;
    exception_pc  = if_id_pipe_i.pc;
    priv_lvl_n    = priv_lvl_q;

    mtvec_n.addr  = csr_mtvec_init_i ? mtvec_addr_i[31:8] : csr_wdata_int[31:8];
    mtvec_n.zero0 = mtvec_q.zero0;
    mtvec_n.mode  = csr_mtvec_init_i ? mtvec_q.mode : {1'b0, csr_wdata_int[0]};
    mtvec_we      = csr_mtvec_init_i;

    mie_n         = csr_wdata_int & IRQ_MASK;
    mie_we        = 1'b0;

    pmp_cfg_we     = {PMP_MAX_REGIONS{1'b0}};
    pmp_addr_we    = {PMP_MAX_REGIONS{1'b0}};
    pmp_mseccfg_we = 1'b0;

    if (csr_we_int) begin
      case (csr_waddr)
        // mstatus: IE bit
        CSR_MSTATUS: begin
          mstatus_we = 1'b1;
        end
        // mie: machine interrupt enable
        CSR_MIE: begin
              mie_we = 1'b1;
        end
        // mtvec: machine trap-handler base address
        CSR_MTVEC: begin
              mtvec_we = 1'b1;
        end
        // mscratch: machine scratch
        CSR_MSCRATCH: begin
              mscratch_we = 1'b1;
        end
        // mepc: exception program counter
        CSR_MEPC: begin
              mepc_we = 1'b1;
        end
        // mcause
        CSR_MCAUSE: begin 
                mcause_we = 1'b1;
        end
        CSR_DCSR: begin
              dcsr_we = 1'b1;
        end
        CSR_DPC: begin
                dpc_we = 1'b1;
        end
        CSR_DSCRATCH0: begin
                dscratch0_we = 1'b1;
        end
        CSR_DSCRATCH1: begin
                dscratch1_we = 1'b1;
        end
        CSR_PMPCFG0: begin
          pmp_cfg_we[3:0]   = 4'hF;
        end
        CSR_PMPCFG1: begin
          pmp_cfg_we[7:4]   = 4'hF;
        end
        CSR_PMPCFG2: begin
          pmp_cfg_we[11:8]  = 4'hF;
        end
        CSR_PMPCFG3: begin
          pmp_cfg_we[15:12] = 4'hF;
        end
        CSR_PMPADDR0, CSR_PMPADDR1, CSR_PMPADDR2, CSR_PMPADDR3,
        CSR_PMPADDR4, CSR_PMPADDR5, CSR_PMPADDR6, CSR_PMPADDR7,
        CSR_PMPADDR8, CSR_PMPADDR9, CSR_PMPADDR10, CSR_PMPADDR11,
        CSR_PMPADDR12, CSR_PMPADDR13, CSR_PMPADDR14, CSR_PMPADDR15: begin
          pmp_addr_we[csr_waddr[3:0]] = 1'b1;
        end
        CSR_PMPMSECCFG0: begin
          pmp_mseccfg_we = 1'b1;
        end
      endcase
    end

    // exception controller gets priority over other writes
    unique case (1'b1)

      ctrl_fsm_i.csr_save_cause: begin
        unique case (1'b1)
          ctrl_fsm_i.csr_save_if:
            exception_pc = pc_if_i;
          ctrl_fsm_i.csr_save_id:
            exception_pc = if_id_pipe_i.pc;
          ctrl_fsm_i.csr_save_ex:
            exception_pc = id_ex_pipe_i.pc;
          ctrl_fsm_i.csr_save_wb:
            exception_pc = ex_wb_pipe_i.pc;
          default:;
        endcase

        if (ctrl_fsm_i.debug_csr_save) begin
            // all interrupts are masked, don't update cause, epc, tval dpc and
            // mpstatus
            dcsr_n = '{
              xdebugver : dcsr_q.xdebugver,
              ebreakm   : dcsr_q.ebreakm,
              stepie    : dcsr_q.stepie,
              step      : dcsr_q.step,
              prv       : PRIV_LVL_M,
              cause     : ctrl_fsm_i.debug_cause,
              default   : 'd0
            };
            dcsr_we = 1'b1;

            dpc_n       = exception_pc;
            dpc_we = 1'b1;
        end else begin
            priv_lvl_n     = PRIV_LVL_M;
            mstatus_n.mpie = mstatus_q.mie;
            mstatus_n.mie  = 1'b0;
            mstatus_n.mpp  = PRIV_LVL_M;
            mstatus_we = 1'b1;

            mepc_n = exception_pc;
            mepc_we = 1'b1;

            mcause_n       = {ctrl_fsm_i.csr_cause[5], 26'd0, ctrl_fsm_i.csr_cause[4:0]};
            mcause_we = 1'b1;
        end
      end //ctrl_fsm_i.csr_save_cause

      ctrl_fsm_i.csr_restore_mret: begin //MRET
        mstatus_n.mie  = mstatus_q.mpie;
        priv_lvl_n     = PRIV_LVL_M;
        mstatus_n.mpie = 1'b1;
        mstatus_n.mpp  = PRIV_LVL_M;
        mstatus_we = 1'b1;
      end //ctrl_fsm_i.csr_restore_mret

      ctrl_fsm_i.csr_restore_dret: begin //DRET
          // Restore to the recorded privilege level
          priv_lvl_n = dcsr_q.prv;
      end //ctrl_fsm_i.csr_restore_dret

      default:;
    endcase
  end


  // CSR operation logic
  // Using ex_wb_pipe_i.rf_wdata for read-modify-write since CSR was read in EX, written in WB
  always_comb // todo: this circuit should use csr_en (if csr_en is 0 then csr_wdata_int should default to csr_wdata for power reasons
  begin
    csr_wdata_int = csr_wdata;
    csr_we_int    = 1'b1;

    case (csr_op)
      CSR_OP_WRITE: csr_wdata_int = csr_wdata;
      CSR_OP_SET:   csr_wdata_int = csr_wdata | ex_wb_pipe_i.rf_wdata;
      CSR_OP_CLEAR: csr_wdata_int = (~csr_wdata) & ex_wb_pipe_i.rf_wdata;

      CSR_OP_READ: begin
        csr_wdata_int = csr_wdata;
        csr_we_int    = 1'b0;
      end
    endcase
  end


  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dscratch0_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dscratch0_n),
    .wr_en_i    (dscratch0_we),
    .rd_data_o  (dscratch0_q),
    .rd_error_o (dscratch0_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dscratch1_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dscratch1_n),
    .wr_en_i    (dscratch1_we),
    .rd_data_o  (dscratch1_q),
    .rd_error_o (dscratch1_rd_error)
  );

 cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (DCSR_RESET_VAL)
  ) dcsr_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dcsr_n),
    .wr_en_i    (dcsr_we),
    .rd_data_o  (dcsr_q),
    .rd_error_o (dcsr_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dpc_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dpc_n),
    .wr_en_i    (dpc_we),
    .rd_data_o  (dpc_q),
    .rd_error_o (dpc_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mepc_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mepc_n),
    .wr_en_i    (mepc_we),
    .rd_data_o  (mepc_q),
    .rd_error_o (mepc_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mscratch_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mscratch_n),
    .wr_en_i    (mscratch_we),
    .rd_data_o  (mscratch_q),
    .rd_error_o (mscratch_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mie_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mie_n),
    .wr_en_i    (mie_we),
    .rd_data_o  (mie_q),
    .rd_error_o (mie_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (MSTATUS_RESET_VAL)
  ) mstatus_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mstatus_n),
    .wr_en_i    (mstatus_we),
    .rd_data_o  (mstatus_q),
    .rd_error_o (mstatus_rd_error)
  );

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mcause_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mcause_n),
    .wr_en_i    (mcause_we),
    .rd_data_o  (mcause_q),
    .rd_error_o (mcause_rd_error)
  );

  

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (MTVEC_RESET_VAL)
  ) mtvec_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mtvec_n),
    .wr_en_i    (mtvec_we),
    .rd_data_o  (mtvec_q),
    .rd_error_o (mtvec_rd_error)
  );

  assign csr_rdata_o = csr_rdata_int;

  // directly output some registers
  assign m_irq_enable_o  = mstatus_q.mie && !(dcsr_q.step && !dcsr_q.stepie);
  assign priv_lvl_o      = priv_lvl_q;
  
  assign mtvec_addr_o    = mtvec_q.addr;
  assign mtvec_mode_o    = mtvec_q.mode;
  
  assign mepc_o          = mepc_q;
  assign dpc_o          = dpc_q;

  assign debug_single_step_o  = dcsr_q.step;
  assign debug_ebreakm_o      = dcsr_q.ebreakm;

  assign priv_lvl_q   = PRIV_LVL_M;

  assign mie_o = mie_q;

  generate
    if(PMP_NUM_REGIONS > 0) begin: csr_pmp
      for(genvar i=0; i < PMP_MAX_REGIONS; i++)  begin: gen_pmp_csr

        if(i < PMP_NUM_REGIONS) begin: pmp_region
          
          pmp_cfg_t pmp_cfg_wdata;
          
          // MSECCFG.RLB allows the lock bit to be bypassed
          assign pmp_cfg_locked[i] = pmp_cfg_q[i].lock && !pmp_mseccfg_q.rlb;

          // Qualify PMPCFG write strobe with lock status
          assign pmp_cfg_we_qual[i] = pmp_cfg_we[i] && !pmp_cfg_locked[i];

          // Extract PMPCFGi bits from wdata
          assign pmp_cfg_wdata.lock = csr_wdata_int[(i%4)*PMP_CFG_W+7];
          
          // NA4 mode is not selectable when G > 0, mode is treated as OFF
          always_comb begin
            unique case (csr_wdata_int[(i%4)*PMP_CFG_W+3+:2])
              PMP_MODE_OFF   : pmp_cfg_wdata.mode = PMP_MODE_OFF;
              PMP_MODE_TOR   : pmp_cfg_wdata.mode = PMP_MODE_TOR;
              PMP_MODE_NA4   : pmp_cfg_wdata.mode = (PMP_GRANULARITY == 0) ? PMP_MODE_NA4 : // TODO:OE is this correct? PMP_GRAN=1 gives PMP_ADDR_WIDTH = 32
                                             PMP_MODE_OFF;
              PMP_MODE_NAPOT : pmp_cfg_wdata.mode = PMP_MODE_NAPOT;
              default : pmp_cfg_wdata.mode = PMP_MODE_OFF;
            endcase
          end
          
          assign pmp_cfg_wdata.exec  = csr_wdata_int[(i%4)*PMP_CFG_W+2];
          assign pmp_cfg_wdata.write = csr_wdata_int[(i%4)*PMP_CFG_W+1]; // TODO:OE Ibex has some logic here, disallowing RW=10 when MML=0, needed? No, just document this in the uarch
          assign pmp_cfg_wdata.read  = csr_wdata_int[(i%4)*PMP_CFG_W+0];
          
          cv32e40x_csr #(
                         .WIDTH      ($bits(pmp_cfg_t)),
                         .SHADOWCOPY (1'b0),
                         .RESETVALUE ('0))
          pmp_cfg_csr_i 
            (.clk        (clk),
             .rst_n      (rst_n),
             .wr_data_i  (pmp_cfg_wdata),
             .wr_en_i    (pmp_cfg_we_qual[i]),
             .rd_data_o  (pmp_cfg_q[i]),
             .rd_error_o (pmp_cfg_rd_error[i]));

          // Extract PMPCFGi rdata
          assign pmp_cfg_rdata[i] = {pmp_cfg_q[i].lock, 2'b00, pmp_cfg_q[i].mode, 
                                     pmp_cfg_q[i].exec, pmp_cfg_q[i].write, pmp_cfg_q[i].read};
          
          // TODO:OE 
          assign csr_pmp_cfg_o[i]  = pmp_cfg_q[i];

          if (i == PMP_NUM_REGIONS-1) begin: pmp_addr_qual_upper
            assign pmp_addr_we_qual[i] = pmp_addr_we[i]     && 
                                         !pmp_cfg_locked[i];
          end
          else begin: pmp_addr_qual_other
            // If the region at the next index is configured as TOR, this region's address register is locked
            assign pmp_addr_we_qual[i] = pmp_addr_we[i]     && 
                                         !pmp_cfg_locked[i] &&
                                         (!pmp_cfg_locked[i+1] || pmp_cfg_q[i+1].mode != PMP_MODE_TOR);
          end
          
          cv32e40x_csr #(
                         .WIDTH      (PMP_ADDR_WIDTH),
                         .SHADOWCOPY (1'b0),
                         .RESETVALUE ('0))
          pmp_addr_csr_i 
            (.clk        (clk),
             .rst_n      (rst_n),
             .wr_data_i  (csr_wdata_int[31-:PMP_ADDR_WIDTH]),
             .wr_en_i    (pmp_addr_we_qual[i]),
             .rd_data_o  (pmp_addr_q[i]),
             .rd_error_o (pmp_addr_rd_error[i]));

          if (PMP_GRANULARITY == 0) begin: pmp_addr_rdata_g0
            // If G == 0, read data is unmodified
            assign pmp_addr_rdata[i] = pmp_addr_q[i];
          end
          else if (PMP_GRANULARITY == 1) begin: pmp_addr_rdata_g1
            // If G == 1, bit [G-1] reads as zero in TOR or OFF mode
            always_comb begin
              pmp_addr_rdata[i] = pmp_addr_q[i];
              if ((pmp_cfg_q[i].mode == PMP_MODE_OFF) || 
                  (pmp_cfg_q[i].mode == PMP_MODE_TOR)) begin
                pmp_addr_rdata[i][PMP_GRANULARITY-1:0] = '0;
              end
            end
          end
          else begin: pmp_addr_rdata_g2
            // For G >= 2, bits are masked to one or zero depending on the mode
            always_comb begin
              // In NAPOT mode, bits [G-2:0] must read as one
              pmp_addr_rdata[i] = {pmp_addr_q[i], {PMP_GRANULARITY-1{1'b1}}};
              
              if ((pmp_cfg_q[i].mode == PMP_MODE_OFF) || 
                  (pmp_cfg_q[i].mode == PMP_MODE_TOR)) begin
              // In TOR or OFF mode, bits [G-1:0] must read as zero
                pmp_addr_rdata[i][PMP_GRANULARITY-1:0] = '0;
              end
            end
          end
          
          // TODO:OE
          assign csr_pmp_addr_o[i] = {pmp_addr_rdata[i], 2'b00};
          
        end // if (i < PMP_NUM_REGIONS)
        else begin: no_pmp_region

          // Tie off outputs for unimplemeted regions
          assign pmp_cfg_rdata[i]  = '0;
          assign pmp_addr_rdata[i] = '0;
          
        end
      end
     
      pmp_mseccfg_t pmp_mseccfg_wdata;

      // MSECCFG.MML/MSECCFG.MMWP cannot be unset once set
      assign pmp_mseccfg_wdata.mml  = csr_wdata_int[CSR_MSECCFG_MML_BIT]  || pmp_mseccfg_q.mml;
      assign pmp_mseccfg_wdata.mmwp = csr_wdata_int[CSR_MSECCFG_MMWP_BIT] || pmp_mseccfg_q.mmwp;

      // MSECFG.RLB cannot be set if any PMP region is locked
      // TODO Spec: When mseccfg.RLB is 0 and pmpcfg.L is 1 in any entry (including disabled entries), then mseccfg.RLB is locked and any further modifications to mseccfg.RLB are ignored (WARL). -> locked is not the same as clear..
      
      // Ibex version: assign pmp_mseccfg_wdata.rlb = csr_wdata_int[CSR_MSECCFG_RLB_BIT]  && !(|pmp_cfg_locked);

      // MSECCFG.RLB cannot be set if RLB=0 and any PMP region is locked
      assign pmp_mseccfg_wdata.rlb  = pmp_mseccfg_q.rlb ? csr_wdata_int[CSR_MSECCFG_RLB_BIT] :
                                      csr_wdata_int[CSR_MSECCFG_RLB_BIT] && !(|pmp_cfg_locked);
        
      cv32e40x_csr #(
                     .WIDTH      ($bits(pmp_mseccfg_t)),
                     .SHADOWCOPY (1'b0),
                     .RESETVALUE ('0))
      pmp_mseccfg_csr_i 
        (.clk        (clk),
         .rst_n      (rst_n),
         .wr_data_i  (pmp_mseccfg_wdata),
         .wr_en_i    (pmp_mseccfg_we),
         .rd_data_o  (pmp_mseccfg_q),
         .rd_error_o (pmp_mseccfg_rd_error));

      // Extract MSECCFG rdata
      always_comb begin
        pmp_mseccfg_rdata                       = '0;
        pmp_mseccfg_rdata[CSR_MSECCFG_MML_BIT]  = pmp_mseccfg_q.mml;
        pmp_mseccfg_rdata[CSR_MSECCFG_MMWP_BIT] = pmp_mseccfg_q.mmwp;
        pmp_mseccfg_rdata[CSR_MSECCFG_RLB_BIT]  = pmp_mseccfg_q.rlb;
      end

      // TOOD:OE
      assign csr_pmp_mseccfg_o = pmp_mseccfg_q;

      // Combine read error signals
      assign pmp_rd_error = |pmp_cfg_rd_error ||
                            |pmp_addr_rd_error ||
                            pmp_mseccfg_rd_error;
      
    end
    else begin: no_csr_pmp
      // Generate tieoffs when PMP is not configured
      for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_tie_pmp_rdata
        assign pmp_cfg_rdata[i]  = '0;
        assign pmp_addr_rdata[i] = '0;
      end
      for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin : g_tie_pmp_outputs
        assign csr_pmp_cfg_o[i]  = pmp_cfg_t'(1'b0);
        assign csr_pmp_addr_o[i] = '0;
      end

      assign pmp_mseccfg_rdata = '0;
      assign csr_pmp_mseccfg_o = '0;
      
      assign pmp_rd_error = 1'b0;
      
    end
  endgenerate

 ////////////////////////////////////////////////////////////////////////
 //  ____       _                   _____     _                        //
 // |  _ \  ___| |__  _   _  __ _  |_   _| __(_) __ _  __ _  ___ _ __  //
 // | | | |/ _ \ '_ \| | | |/ _` |   | || '__| |/ _` |/ _` |/ _ \ '__| //
 // | |_| |  __/ |_) | |_| | (_| |   | || |  | | (_| | (_| |  __/ |    //
 // |____/ \___|_.__/ \__,_|\__, |   |_||_|  |_|\__, |\__, |\___|_|    //
 //                         |___/               |___/ |___/            //
 ////////////////////////////////////////////////////////////////////////

  
  // Register values
  logic [31:0] tmatch_control_q, tmatch_control_n;
  logic [31:0] tmatch_value_q, tmatch_value_n;
  // Write enables
  logic tmatch_control_we;
  logic tmatch_value_we;
  logic tmatch_control_rd_error;
  logic tmatch_value_rd_error;

  // Write select
  assign tmatch_control_we = csr_we_int & ctrl_fsm_i.debug_mode & (csr_waddr == CSR_TDATA1);
  assign tmatch_value_we   = csr_we_int & ctrl_fsm_i.debug_mode & (csr_waddr == CSR_TDATA2);

  // All supported trigger types
  assign tinfo_types = 1 << TTYPE_MCONTROL;

  // Assign write data
  // TDATA0 - only support simple address matching
  assign tmatch_control_n =
              {
              TTYPE_MCONTROL,        // type    : address/data match
              1'b1,                  // dmode   : access from D mode only
              6'h00,                 // maskmax : exact match only
              1'b0,                  // hit     : not supported
              1'b0,                  // select  : address match only
              1'b0,                  // timing  : match before execution
              2'b00,                 // sizelo  : match any access
              4'h1,                  // action  : enter debug mode
              1'b0,                  // chain   : not supported
              4'h0,                  // match   : simple match
              1'b1,                  // m       : match in m-mode
              1'b0,                  // 0       : zero
              1'b0,                  // s       : not supported
              1'b0,                  // u       : match in u-mode
              csr_wdata_int[2],      // execute : match instruction address
              1'b0,                  // store   : not supported
              1'b0};                 // load    : not supported

  assign tmatch_value_n = csr_wdata_int; 

  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (TMATCH_CONTROL_RST_VAL)
  ) tmatch_control_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (tmatch_control_n),
    .wr_en_i    (tmatch_control_we),
    .rd_data_o  (tmatch_control_q),
    .rd_error_o (tmatch_control_rd_error)
  );   
  
  cv32e40s_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) tmatch_value_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (tmatch_value_n),
    .wr_en_i    (tmatch_value_we),
    .rd_data_o  (tmatch_value_q),
    .rd_error_o (tmatch_value_rd_error)
  );  
  
  assign tmatch_control_rdata = tmatch_control_q;
  // TDATA1 - address match value only
  assign tmatch_value_rdata = tmatch_value_q;

  // Breakpoint matching
  // We match against the next address, as the breakpoint must be taken before execution
  assign debug_trigger_match_o = tmatch_control_q[2] &
                                 (if_id_pipe_i.pc[31:0] == tmatch_value_q[31:0]);


  /////////////////////////////////////////////////////////////////
  //   ____            __     ____                  _            //
  // |  _ \ ___ _ __ / _|   / ___|___  _   _ _ __ | |_ ___ _ __  //
  // | |_) / _ \ '__| |_   | |   / _ \| | | | '_ \| __/ _ \ '__| //
  // |  __/  __/ |  |  _|  | |__| (_) | |_| | | | | ||  __/ |    //
  // |_|   \___|_|  |_|(_)  \____\___/ \__,_|_| |_|\__\___|_|    //
  //                                                             //
  /////////////////////////////////////////////////////////////////

  // todo:low decide on whether events need to be registered first (to break critical timing paths)

  // ------------------------
  // Events to count
  assign hpm_events[0]  = 1'b1;                                                 // Cycle counter
  assign hpm_events[1]  = ctrl_fsm_i.mhpmevent.minstret;                        // Instruction counter
  assign hpm_events[2]  = ctrl_fsm_i.mhpmevent.ld_stall;                        // Nr of load use hazards
  assign hpm_events[3]  = ctrl_fsm_i.mhpmevent.jr_stall;                        // Nr of jump register hazards
  assign hpm_events[4]  = ctrl_fsm_i.mhpmevent.imiss;                           // Cycles waiting for instruction fetches, excluding jumps and branches
  assign hpm_events[5]  = ctrl_fsm_i.mhpmevent.load;                            // Nr of loads
  assign hpm_events[6]  = ctrl_fsm_i.mhpmevent.store;                           // Nr of stores
  assign hpm_events[7]  = ctrl_fsm_i.mhpmevent.jump;                            // Nr of jumps (unconditional)
  assign hpm_events[8]  = ctrl_fsm_i.mhpmevent.branch;                          // Nr of branches (conditional)
  assign hpm_events[9]  = ctrl_fsm_i.mhpmevent.branch_taken;                    // Nr of taken branches (conditional)
  assign hpm_events[10] = ctrl_fsm_i.mhpmevent.compressed;                      // Compressed instruction counter
  assign hpm_events[11] = 1'b0;
  assign hpm_events[12] = 1'b0;
  assign hpm_events[13] = 1'b0;
  assign hpm_events[14] = 1'b0;
  assign hpm_events[15] = 1'b0;

  // ------------------------
  // address decoder for performance counter registers
  logic mcountinhibit_we;
  logic mhpmevent_we;

  assign mcountinhibit_we = csr_we_int & (  csr_waddr == CSR_MCOUNTINHIBIT);
  assign mhpmevent_we     = csr_we_int & ( (csr_waddr == CSR_MHPMEVENT3  )||
                                           (csr_waddr == CSR_MHPMEVENT4  ) ||
                                           (csr_waddr == CSR_MHPMEVENT5  ) ||
                                           (csr_waddr == CSR_MHPMEVENT6  ) ||
                                           (csr_waddr == CSR_MHPMEVENT7  ) ||
                                           (csr_waddr == CSR_MHPMEVENT8  ) ||
                                           (csr_waddr == CSR_MHPMEVENT9  ) ||
                                           (csr_waddr == CSR_MHPMEVENT10 ) ||
                                           (csr_waddr == CSR_MHPMEVENT11 ) ||
                                           (csr_waddr == CSR_MHPMEVENT12 ) ||
                                           (csr_waddr == CSR_MHPMEVENT13 ) ||
                                           (csr_waddr == CSR_MHPMEVENT14 ) ||
                                           (csr_waddr == CSR_MHPMEVENT15 ) ||
                                           (csr_waddr == CSR_MHPMEVENT16 ) ||
                                           (csr_waddr == CSR_MHPMEVENT17 ) ||
                                           (csr_waddr == CSR_MHPMEVENT18 ) ||
                                           (csr_waddr == CSR_MHPMEVENT19 ) ||
                                           (csr_waddr == CSR_MHPMEVENT20 ) ||
                                           (csr_waddr == CSR_MHPMEVENT21 ) ||
                                           (csr_waddr == CSR_MHPMEVENT22 ) ||
                                           (csr_waddr == CSR_MHPMEVENT23 ) ||
                                           (csr_waddr == CSR_MHPMEVENT24 ) ||
                                           (csr_waddr == CSR_MHPMEVENT25 ) ||
                                           (csr_waddr == CSR_MHPMEVENT26 ) ||
                                           (csr_waddr == CSR_MHPMEVENT27 ) ||
                                           (csr_waddr == CSR_MHPMEVENT28 ) ||
                                           (csr_waddr == CSR_MHPMEVENT29 ) ||
                                           (csr_waddr == CSR_MHPMEVENT30 ) ||
                                           (csr_waddr == CSR_MHPMEVENT31 ) );

  // ------------------------
  // Increment value for performance counters
  genvar incr_gidx;
  generate
    for (incr_gidx=0; incr_gidx<32; incr_gidx++) begin : gen_mhpmcounter_increment
      assign mhpmcounter_increment[incr_gidx] = mhpmcounter_q[incr_gidx] + 1;
    end
  endgenerate

  // ------------------------
  // next value for performance counters and control registers
  always_comb
    begin
      mcountinhibit_n = mcountinhibit_q;
      mhpmevent_n     = mhpmevent_q;

      
      // Inhibit Control
      if(mcountinhibit_we)
        mcountinhibit_n = csr_wdata_int;

      // Event Control
      if(mhpmevent_we)
        mhpmevent_n[csr_waddr[4:0]] = csr_wdata_int;
    end

  genvar wcnt_gidx;
  generate
    for (wcnt_gidx=0; wcnt_gidx<32; wcnt_gidx++) begin : gen_mhpmcounter_write

      // Write lower counter bits
      assign mhpmcounter_write_lower[wcnt_gidx] = csr_we_int && (csr_waddr == (CSR_MCYCLE + wcnt_gidx));

      // Write upper counter bits
      assign mhpmcounter_write_upper[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                  csr_we_int && (csr_waddr == (CSR_MCYCLEH + wcnt_gidx)) && (MHPMCOUNTER_WIDTH == 64);

      // Increment counter
      
      if (wcnt_gidx == 0) begin : gen_mhpmcounter_mcycle
        // mcycle = mhpmcounter[0] : count every cycle (if not inhibited)
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx];
      end else if (wcnt_gidx == 2) begin : gen_mhpmcounter_minstret
        // minstret = mhpmcounter[2]  : count every retired instruction (if not inhibited)
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx] &&
                                                        hpm_events[1];
      end else if( (wcnt_gidx>2) && (wcnt_gidx<(NUM_MHPMCOUNTERS+3))) begin : gen_mhpmcounter
        // add +1 if any event is enabled and active
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx] &&
                                                        |(hpm_events & mhpmevent_q[wcnt_gidx][NUM_HPM_EVENTS-1:0]);
      end else begin : gen_mhpmcounter_not_implemented
        assign mhpmcounter_write_increment[wcnt_gidx] = 1'b0;
      end
       
    end
  endgenerate

  // ------------------------
  // HPM Registers
  // next value
  genvar nxt_gidx;
  generate
    for (nxt_gidx = 0; nxt_gidx < 32; nxt_gidx++) begin : gen_mhpmcounter_nextvalue
      // mcyclce  is located at index 0
      // there is no counter at index 1
      // minstret is located at index 2
      // Programable HPM counters start at index 3
      if( (nxt_gidx == 1) ||
          (nxt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
          assign mhpmcounter_n[nxt_gidx]  = 'b0;
          assign mhpmcounter_we[nxt_gidx] = 2'b0;
      end
      else begin : gen_implemented_nextvalue
        always_comb begin
          mhpmcounter_we[nxt_gidx] = 2'b0;
          mhpmcounter_n[nxt_gidx]  = mhpmcounter_q[nxt_gidx];
          if (mhpmcounter_write_lower[nxt_gidx]) begin
            mhpmcounter_n[nxt_gidx][31:0] = csr_wdata_int;
            mhpmcounter_we[nxt_gidx][0] = 1'b1;
          end else if (mhpmcounter_write_upper[nxt_gidx]) begin
            mhpmcounter_n[nxt_gidx][63:32] = csr_wdata_int;
            mhpmcounter_we[nxt_gidx][1] = 1'b1;
          end else if (mhpmcounter_write_increment[nxt_gidx]) begin
            mhpmcounter_we[nxt_gidx] = 2'b1;
            mhpmcounter_n[nxt_gidx] = mhpmcounter_increment[nxt_gidx];
          end
        end // always_comb
      end
    end
  endgenerate
  //  Counter Registers: mhpcounter_q[]
  genvar cnt_gidx;
  generate
    for (cnt_gidx = 0; cnt_gidx < 32; cnt_gidx++) begin : gen_mhpmcounter
      // mcyclce  is located at index 0
      // there is no counter at index 1
      // minstret is located at index 2
      // Programable HPM counters start at index 3
      if( (cnt_gidx == 1) ||
          (cnt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
        assign mhpmcounter_q[cnt_gidx] = 'b0;
      end
      else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) begin
            mhpmcounter_q[cnt_gidx] <= 'b0;
          end else begin
            if (mhpmcounter_we[cnt_gidx][0]) begin
              mhpmcounter_q[cnt_gidx][31:0] <= mhpmcounter_n[cnt_gidx][31:0];
            end
            if (mhpmcounter_we[cnt_gidx][1]) begin
              mhpmcounter_q[cnt_gidx][63:32] <= mhpmcounter_n[cnt_gidx][63:32];
            end
          end
      end
    end
  endgenerate

  //  Event Register: mhpevent_q[]
  genvar evt_gidx;
  generate
    for (evt_gidx = 0; evt_gidx < 32; evt_gidx++) begin : gen_mhpmevent
      // programable HPM events start at index3
      if( (evt_gidx < 3) ||
          (evt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
        assign mhpmevent_q[evt_gidx] = 'b0;
      end
      else begin : gen_implemented
        if (NUM_HPM_EVENTS < 32) begin : gen_tie_off
             assign mhpmevent_q[evt_gidx][31:NUM_HPM_EVENTS] = 'b0;
        end
        always_ff @(posedge clk, negedge rst_n)
            if (!rst_n)
                mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0]  <= 'b0;
            else
                mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0]  <= mhpmevent_n[evt_gidx][NUM_HPM_EVENTS-1:0] ;
      end
    end
  endgenerate

  //  Inhibit Regsiter: mcountinhibit_q
  //  Note: implemented counters are disabled out of reset to save power
  genvar inh_gidx;
  generate
    for (inh_gidx = 0; inh_gidx < 32; inh_gidx++) begin : gen_mcountinhibit
      if( (inh_gidx == 1) ||
          (inh_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
        assign mcountinhibit_q[inh_gidx] = 'b0;
      end
      else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n)
            mcountinhibit_q[inh_gidx] <= 'b1; // default disable
          else
            mcountinhibit_q[inh_gidx] <= mcountinhibit_n[inh_gidx];
      end
    end
  endgenerate

endmodule // cv32e40s_cs_registers
