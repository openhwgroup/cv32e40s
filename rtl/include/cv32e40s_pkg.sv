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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Arjan Bink - arjan.bink@silabs.com                         //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
//                                                                            //
// Design Name:    RISC-V processor core                                      //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines for various constants used by the processor core.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package cv32e40s_pkg;

////////////////////////////////////////////////
//    ___         ____          _             //
//   / _ \ _ __  / ___|___   __| | ___  ___   //
//  | | | | '_ \| |   / _ \ / _` |/ _ \/ __|  //
//  | |_| | |_) | |__| (_) | (_| |  __/\__ \  //
//   \___/| .__/ \____\___/ \__,_|\___||___/  //
//        |_|                                 //
////////////////////////////////////////////////

  typedef enum logic [6:0] {
                            OPCODE_SYSTEM    = 7'h73,
                            OPCODE_FENCE     = 7'h0f,
                            OPCODE_OP        = 7'h33,
                            OPCODE_OPIMM     = 7'h13,
                            OPCODE_STORE     = 7'h23,
                            OPCODE_LOAD      = 7'h03,
                            OPCODE_BRANCH    = 7'h63,
                            OPCODE_JALR      = 7'h67,
                            OPCODE_JAL       = 7'h6f,
                            OPCODE_AUIPC     = 7'h17,
                            OPCODE_LUI       = 7'h37,
                            OPCODE_AMO       = 7'h2F
                            } opcode_e;

//////////////////////////////////////////////////////////////////////////////
//      _    _    _   _    ___                       _   _                  //
//     / \  | |  | | | |  / _ \ _ __   ___ _ __ __ _| |_(_) ___  _ __  ___  //
//    / _ \ | |  | | | | | | | | '_ \ / _ \ '__/ _` | __| |/ _ \| '_ \/ __| //
//   / ___ \| |__| |_| | | |_| | |_) |  __/ | | (_| | |_| | (_) | | | \__ \ //
//  /_/   \_\_____\___/   \___/| .__/ \___|_|  \__,_|\__|_|\___/|_| |_|___/ //
//                             |_|                                          //
//////////////////////////////////////////////////////////////////////////////

parameter ALU_OP_WIDTH = 6;

  // TODO:low Could a smarter encoding be used here?

// Note: Certain bits in alu_opcode_e are referred to directly in the ALU:
//
// - Bit 2: Right shift?
//          Used for ALU_SLL, ALU_B_ROL,  ALU_B_ROR, ALU_B_BCLR,
//          ALU_B_BSET, ALU_B_BINV, ALU_SRL, ALU_SRA, ALU_B_BEXT.
// - Bit 3: Should B operand of adder be negated?
//          Used for ALU_ADD, ALU_SUB.
// - Bit 3: Are operands signed?
//          Used for ALU_SLT, ALU_SLTU, ALU_LT, ALU_GE, ALU_LTU, ALU_GEU,
//          ALU_B_MIN, ALU_B_MINU, ALU_B_MAX, ALU_B_MAXU
// - Bit 5: Is the operator a B extension operation?

typedef enum logic [ALU_OP_WIDTH-1:0]
{
 ALU_ADD      = 6'b000000, // funct3 = 000, negate_b(3)
 ALU_SUB      = 6'b001000, // funct3 = 000, negate_b(3)

 ALU_XOR      = 6'b000100, // funct3 = 100
 ALU_OR       = 6'b000110, // funct3 = 110
 ALU_AND      = 6'b000111, // funct3 = 111

 ALU_B_XNOR   = 6'b101100, // funct3 = 100, zbb
 ALU_B_ORN    = 6'b101110, // funct3 = 110, zbb
 ALU_B_ANDN   = 6'b101111, // funct3 = 111, zbb

 // Comparisons // todo: comparator operators do not need to be part of ALU operators
 ALU_EQ       = 6'b010000, // funct3 = 000
 ALU_NE       = 6'b010001, // funct3 = 001
 ALU_SLT      = 6'b011010, // funct3 = 010, signed(3)
 ALU_SLTU     = 6'b010011, // funct3 = 011, unsigned(3)
 ALU_LT       = 6'b011100, // funct3 = 100, signed(3)
 ALU_GE       = 6'b011101, // funct3 = 101, signed(3)
 ALU_LTU      = 6'b010110, // funct3 = 110, unsigned(3)
 ALU_GEU      = 6'b010111, // funct3 = 111, unsigned(3)

 ALU_B_MIN    = 6'b111100, // funct3 = 100, signed(3), minimum(1)
 ALU_B_MINU   = 6'b110101, // funct3 = 101, unsigned(3), minimum(1)
 ALU_B_MAX    = 6'b111110, // funct3 = 110, signed(3), maximum(1)
 ALU_B_MAXU   = 6'b110111, // funct3 = 111, unsigned(3), maximum(1)

 ALU_SLL      = 6'b000001, // funct3 = 001, left(2)
 ALU_B_ROL    = 6'b100001, // funct3 = 001, left(2)
 ALU_B_ROR    = 6'b100101, // funct3 = 101, right(2)
 ALU_B_BCLR   = 6'b101001, // funct3 = 001, Zbs, left(2)
 ALU_B_BSET   = 6'b110001, // funct3 = 001, Zbs, left(2)
 ALU_B_BINV   = 6'b111001, // funct3 = 001, Zbs, left(2)
 ALU_SRL      = 6'b000101, // funct3 = 101, right(2)
 ALU_SRA      = 6'b001101, // funct3 = 101, right(2)
 ALU_B_BEXT   = 6'b111101, // funct3 = 101, Zbs, right(2)

 // B, Zba
 ALU_B_SH1ADD = 6'b100010, // funct3 = 010
 ALU_B_SH2ADD = 6'b100100, // funct3 = 100
 ALU_B_SH3ADD = 6'b100110, // funct3 = 110

 // B, Zbb
 ALU_B_CLZ    = 6'b100000, // (funct3 = 001)
 ALU_B_CTZ    = 6'b101000, // (funct3 = 001)
 ALU_B_CPOP   = 6'b100011, // (funct3 = 001)

 // The following three alu opcodes are shared between B and ZC.
 // Setting bit5==0 allows synth to optimize away most B logic
 // in the ALU in case only ZC_EXT is enabled.
 ALU_B_SEXT_B = 6'b010010,
 ALU_B_SEXT_H = 6'b010100,
 ALU_B_ZEXT_H = 6'b010101,

 ALU_B_REV8   = 6'b110100, // (funct3 = 101)
 ALU_B_ORC_B  = 6'b110010, // (funct3 = 101)

 // B, Zbc
 ALU_B_CLMUL  = 6'b100111, // (funct3 = 001)
 ALU_B_CLMULH = 6'b101011, // funct3 = 011
 ALU_B_CLMULR = 6'b101010  // funct3 = 010

 // Free encodings with bit 5 set (for B_EXT):
 // 6'b101101
 // 6'b110110
 // 6'b111010
 // 6'b111011
 // 6'b111111

} alu_opcode_e;

parameter MUL_OP_WIDTH = 1;

typedef enum logic [MUL_OP_WIDTH-1:0]
{
 MUL_M32 = 1'b0,
 MUL_H   = 1'b1
 } mul_opcode_e;

parameter DIV_OP_WIDTH = 2;

typedef enum logic [DIV_OP_WIDTH-1:0]
{

 DIV_DIVU= 2'b00,
 DIV_DIV = 2'b01,
 DIV_REMU= 2'b10,
 DIV_REM = 2'b11

 } div_opcode_e;

// FSM state encoding
typedef enum logic [2:0] { RESET, BOOT_SET, FUNCTIONAL, SLEEP, DEBUG_TAKEN, POINTER_FETCH} ctrl_state_e;

// Debug FSM state encoding
// State encoding done one-hot to ensure that debug_havereset_o, debug_running_o, debug_halted_o
// will come directly from flip-flops. *_INDEX and debug_state_e encoding must match

parameter HAVERESET_INDEX = 0;
parameter RUNNING_INDEX = 1;
parameter HALTED_INDEX = 2;

typedef enum logic [2:0] { HAVERESET = 3'b001, RUNNING = 3'b010, HALTED = 3'b100 } debug_state_e;

typedef enum logic {IDLE, BRANCH_WAIT} prefetch_state_e;

typedef enum logic [1:0] {MUL_ALBL, MUL_ALBH, MUL_AHBL, MUL_AHBH} mul_state_e;

// ALU divider FSM state encoding
typedef enum logic [1:0] {DIV_IDLE, DIV_DIVIDE, DIV_DUMMY, DIV_FINISH} div_state_e;


/////////////////////////////////////////////////////////
//    ____ ____    ____            _     _             //
//   / ___/ ___|  |  _ \ ___  __ _(_)___| |_ ___ _ __  //
//  | |   \___ \  | |_) / _ \/ _` | / __| __/ _ \ '__| //
//  | |___ ___) | |  _ <  __/ (_| | \__ \ ||  __/ |    //
//   \____|____/  |_| \_\___|\__, |_|___/\__\___|_|    //
//                           |___/                     //
/////////////////////////////////////////////////////////

// CSRs mnemonics
typedef enum logic[11:0] {

  ///////////////////////////////////////////////////////
  // User CSRs
  ///////////////////////////////////////////////////////

  CSR_JVT            = 12'h017,

  ///////////////////////////////////////////////////////
  // User Custom CSRs
  ///////////////////////////////////////////////////////

  // None


  ///////////////////////////////////////////////////////
  // Machine CSRs
  ///////////////////////////////////////////////////////

  // Machine trap setup
  CSR_MSTATUS        = 12'h300,
  CSR_MISA           = 12'h301,
  CSR_MIE            = 12'h304,
  CSR_MTVEC          = 12'h305,
  CSR_MCOUNTEREN     = 12'h306,
  CSR_MTVT           = 12'h307,
  CSR_MSTATEEN0      = 12'h30C,
  CSR_MSTATEEN1      = 12'h30D,
  CSR_MSTATEEN2      = 12'h30E,
  CSR_MSTATEEN3      = 12'h30F,
  CSR_MSTATUSH       = 12'h310,

  CSR_MSTATEEN0H     = 12'h31C,
  CSR_MSTATEEN1H     = 12'h31D,
  CSR_MSTATEEN2H     = 12'h31E,
  CSR_MSTATEEN3H     = 12'h31F,

  // Performance counters
  CSR_MCOUNTINHIBIT  = 12'h320,
  CSR_MHPMEVENT3     = 12'h323,
  CSR_MHPMEVENT4     = 12'h324,
  CSR_MHPMEVENT5     = 12'h325,
  CSR_MHPMEVENT6     = 12'h326,
  CSR_MHPMEVENT7     = 12'h327,
  CSR_MHPMEVENT8     = 12'h328,
  CSR_MHPMEVENT9     = 12'h329,
  CSR_MHPMEVENT10    = 12'h32A,
  CSR_MHPMEVENT11    = 12'h32B,
  CSR_MHPMEVENT12    = 12'h32C,
  CSR_MHPMEVENT13    = 12'h32D,
  CSR_MHPMEVENT14    = 12'h32E,
  CSR_MHPMEVENT15    = 12'h32F,
  CSR_MHPMEVENT16    = 12'h330,
  CSR_MHPMEVENT17    = 12'h331,
  CSR_MHPMEVENT18    = 12'h332,
  CSR_MHPMEVENT19    = 12'h333,
  CSR_MHPMEVENT20    = 12'h334,
  CSR_MHPMEVENT21    = 12'h335,
  CSR_MHPMEVENT22    = 12'h336,
  CSR_MHPMEVENT23    = 12'h337,
  CSR_MHPMEVENT24    = 12'h338,
  CSR_MHPMEVENT25    = 12'h339,
  CSR_MHPMEVENT26    = 12'h33A,
  CSR_MHPMEVENT27    = 12'h33B,
  CSR_MHPMEVENT28    = 12'h33C,
  CSR_MHPMEVENT29    = 12'h33D,
  CSR_MHPMEVENT30    = 12'h33E,
  CSR_MHPMEVENT31    = 12'h33F,

  // Machine trap handling
  CSR_MSCRATCH       = 12'h340,
  CSR_MEPC           = 12'h341,
  CSR_MCAUSE         = 12'h342,
  CSR_MTVAL          = 12'h343,
  CSR_MIP            = 12'h344,
  CSR_MNXTI          = 12'h345,
  CSR_MINTSTATUS     = 12'h346,
  CSR_MINTTHRESH     = 12'h347,
  CSR_MSCRATCHCSW    = 12'h348,
  CSR_MSCRATCHCSWL   = 12'h349,
  CSR_MCLICBASE      = 12'h34A,

  // Physical memory protection (PMP)
  CSR_PMPCFG0        = 12'h3A0,
  CSR_PMPCFG1        = 12'h3A1,
  CSR_PMPCFG2        = 12'h3A2,
  CSR_PMPCFG3        = 12'h3A3,
  CSR_PMPCFG4        = 12'h3A4,
  CSR_PMPCFG5        = 12'h3A5,
  CSR_PMPCFG6        = 12'h3A6,
  CSR_PMPCFG7        = 12'h3A7,
  CSR_PMPCFG8        = 12'h3A8,
  CSR_PMPCFG9        = 12'h3A9,
  CSR_PMPCFG10       = 12'h3AA,
  CSR_PMPCFG11       = 12'h3AB,
  CSR_PMPCFG12       = 12'h3AC,
  CSR_PMPCFG13       = 12'h3AD,
  CSR_PMPCFG14       = 12'h3AE,
  CSR_PMPCFG15       = 12'h3AF,

  CSR_PMPADDR0       = 12'h3B0,
  CSR_PMPADDR1       = 12'h3B1,
  CSR_PMPADDR2       = 12'h3B2,
  CSR_PMPADDR3       = 12'h3B3,
  CSR_PMPADDR4       = 12'h3B4,
  CSR_PMPADDR5       = 12'h3B5,
  CSR_PMPADDR6       = 12'h3B6,
  CSR_PMPADDR7       = 12'h3B7,
  CSR_PMPADDR8       = 12'h3B8,
  CSR_PMPADDR9       = 12'h3B9,
  CSR_PMPADDR10      = 12'h3BA,
  CSR_PMPADDR11      = 12'h3BB,
  CSR_PMPADDR12      = 12'h3BC,
  CSR_PMPADDR13      = 12'h3BD,
  CSR_PMPADDR14      = 12'h3BE,
  CSR_PMPADDR15      = 12'h3BF,
  CSR_PMPADDR16      = 12'h3C0,
  CSR_PMPADDR17      = 12'h3C1,
  CSR_PMPADDR18      = 12'h3C2,
  CSR_PMPADDR19      = 12'h3C3,
  CSR_PMPADDR20      = 12'h3C4,
  CSR_PMPADDR21      = 12'h3C5,
  CSR_PMPADDR22      = 12'h3C6,
  CSR_PMPADDR23      = 12'h3C7,
  CSR_PMPADDR24      = 12'h3C8,
  CSR_PMPADDR25      = 12'h3C9,
  CSR_PMPADDR26      = 12'h3CA,
  CSR_PMPADDR27      = 12'h3CB,
  CSR_PMPADDR28      = 12'h3CC,
  CSR_PMPADDR29      = 12'h3CD,
  CSR_PMPADDR30      = 12'h3CE,
  CSR_PMPADDR31      = 12'h3CF,
  CSR_PMPADDR32      = 12'h3D0,
  CSR_PMPADDR33      = 12'h3D1,
  CSR_PMPADDR34      = 12'h3D2,
  CSR_PMPADDR35      = 12'h3D3,
  CSR_PMPADDR36      = 12'h3D4,
  CSR_PMPADDR37      = 12'h3D5,
  CSR_PMPADDR38      = 12'h3D6,
  CSR_PMPADDR39      = 12'h3D7,
  CSR_PMPADDR40      = 12'h3D8,
  CSR_PMPADDR41      = 12'h3D9,
  CSR_PMPADDR42      = 12'h3DA,
  CSR_PMPADDR43      = 12'h3DB,
  CSR_PMPADDR44      = 12'h3DC,
  CSR_PMPADDR45      = 12'h3DD,
  CSR_PMPADDR46      = 12'h3DE,
  CSR_PMPADDR47      = 12'h3DF,
  CSR_PMPADDR48      = 12'h3E0,
  CSR_PMPADDR49      = 12'h3E1,
  CSR_PMPADDR50      = 12'h3E2,
  CSR_PMPADDR51      = 12'h3E3,
  CSR_PMPADDR52      = 12'h3E4,
  CSR_PMPADDR53      = 12'h3E5,
  CSR_PMPADDR54      = 12'h3E6,
  CSR_PMPADDR55      = 12'h3E7,
  CSR_PMPADDR56      = 12'h3E8,
  CSR_PMPADDR57      = 12'h3E9,
  CSR_PMPADDR58      = 12'h3EA,
  CSR_PMPADDR59      = 12'h3EB,
  CSR_PMPADDR60      = 12'h3EC,
  CSR_PMPADDR61      = 12'h3ED,
  CSR_PMPADDR62      = 12'h3EE,
  CSR_PMPADDR63      = 12'h3EF,

  // Machine configuration
  CSR_MENVCFG        = 12'h30A,
  CSR_MENVCFGH       = 12'h31A,
  CSR_MSECCFG        = 12'h747,
  CSR_MSECCFGH       = 12'h757,

  // Trigger
  CSR_TSELECT        = 12'h7A0,
  CSR_TDATA1         = 12'h7A1,
  CSR_TDATA2         = 12'h7A2,
  CSR_TDATA3         = 12'h7A3,
  CSR_TINFO          = 12'h7A4,
  CSR_TCONTROL       = 12'h7A5,

  // Debug/trace
  CSR_DCSR           = 12'h7B0,
  CSR_DPC            = 12'h7B1,

  // Debug
  CSR_DSCRATCH0      = 12'h7B2,
  CSR_DSCRATCH1      = 12'h7B3,

  // Hardware Performance Monitor
  CSR_MCYCLE         = 12'hB00,
  CSR_MINSTRET       = 12'hB02,
  CSR_MHPMCOUNTER3   = 12'hB03,
  CSR_MHPMCOUNTER4   = 12'hB04,
  CSR_MHPMCOUNTER5   = 12'hB05,
  CSR_MHPMCOUNTER6   = 12'hB06,
  CSR_MHPMCOUNTER7   = 12'hB07,
  CSR_MHPMCOUNTER8   = 12'hB08,
  CSR_MHPMCOUNTER9   = 12'hB09,
  CSR_MHPMCOUNTER10  = 12'hB0A,
  CSR_MHPMCOUNTER11  = 12'hB0B,
  CSR_MHPMCOUNTER12  = 12'hB0C,
  CSR_MHPMCOUNTER13  = 12'hB0D,
  CSR_MHPMCOUNTER14  = 12'hB0E,
  CSR_MHPMCOUNTER15  = 12'hB0F,
  CSR_MHPMCOUNTER16  = 12'hB10,
  CSR_MHPMCOUNTER17  = 12'hB11,
  CSR_MHPMCOUNTER18  = 12'hB12,
  CSR_MHPMCOUNTER19  = 12'hB13,
  CSR_MHPMCOUNTER20  = 12'hB14,
  CSR_MHPMCOUNTER21  = 12'hB15,
  CSR_MHPMCOUNTER22  = 12'hB16,
  CSR_MHPMCOUNTER23  = 12'hB17,
  CSR_MHPMCOUNTER24  = 12'hB18,
  CSR_MHPMCOUNTER25  = 12'hB19,
  CSR_MHPMCOUNTER26  = 12'hB1A,
  CSR_MHPMCOUNTER27  = 12'hB1B,
  CSR_MHPMCOUNTER28  = 12'hB1C,
  CSR_MHPMCOUNTER29  = 12'hB1D,
  CSR_MHPMCOUNTER30  = 12'hB1E,
  CSR_MHPMCOUNTER31  = 12'hB1F,

  CSR_MCYCLEH        = 12'hB80,
  CSR_MINSTRETH      = 12'hB82,
  CSR_MHPMCOUNTER3H  = 12'hB83,
  CSR_MHPMCOUNTER4H  = 12'hB84,
  CSR_MHPMCOUNTER5H  = 12'hB85,
  CSR_MHPMCOUNTER6H  = 12'hB86,
  CSR_MHPMCOUNTER7H  = 12'hB87,
  CSR_MHPMCOUNTER8H  = 12'hB88,
  CSR_MHPMCOUNTER9H  = 12'hB89,
  CSR_MHPMCOUNTER10H = 12'hB8A,
  CSR_MHPMCOUNTER11H = 12'hB8B,
  CSR_MHPMCOUNTER12H = 12'hB8C,
  CSR_MHPMCOUNTER13H = 12'hB8D,
  CSR_MHPMCOUNTER14H = 12'hB8E,
  CSR_MHPMCOUNTER15H = 12'hB8F,
  CSR_MHPMCOUNTER16H = 12'hB90,
  CSR_MHPMCOUNTER17H = 12'hB91,
  CSR_MHPMCOUNTER18H = 12'hB92,
  CSR_MHPMCOUNTER19H = 12'hB93,
  CSR_MHPMCOUNTER20H = 12'hB94,
  CSR_MHPMCOUNTER21H = 12'hB95,
  CSR_MHPMCOUNTER22H = 12'hB96,
  CSR_MHPMCOUNTER23H = 12'hB97,
  CSR_MHPMCOUNTER24H = 12'hB98,
  CSR_MHPMCOUNTER25H = 12'hB99,
  CSR_MHPMCOUNTER26H = 12'hB9A,
  CSR_MHPMCOUNTER27H = 12'hB9B,
  CSR_MHPMCOUNTER28H = 12'hB9C,
  CSR_MHPMCOUNTER29H = 12'hB9D,
  CSR_MHPMCOUNTER30H = 12'hB9E,
  CSR_MHPMCOUNTER31H = 12'hB9F,

  // Machine information
  CSR_MVENDORID      = 12'hF11,
  CSR_MARCHID        = 12'hF12,
  CSR_MIMPID         = 12'hF13,
  CSR_MHARTID        = 12'hF14,
  CSR_MCONFIGPTR     = 12'hF15,

  // Xsecure custom CSRs
  CSR_CPUCTRL        = 12'hBF0,
  CSR_SECURESEED0    = 12'hBF9,
  CSR_SECURESEED1    = 12'hBFA,
  CSR_SECURESEED2    = 12'hBFC
} csr_num_e;

// CSR Bit Implementation Masks
parameter CSR_JVT_MASK          = 32'hFFFFFC00;
parameter CSR_DCSR_MASK         = 32'b1111_0000_0000_0000_1000_1001_1100_0111; // NMI bit taken from ctrl_fsm
parameter CSR_MEPC_MASK         = 32'hFFFFFFFE;
parameter CSR_DPC_MASK          = 32'hFFFFFFFE;
//        CSR_MIE_MASK          = IRQ_MASK;
parameter CSR_MSTATUS_MASK      = 32'b0000_0000_0010_0010_0001_1000_1000_1000;
parameter CSR_MTVEC_BASIC_MASK  = 32'hFFFFFF81;
parameter CSR_MTVEC_CLIC_MASK   = 32'hFFFFFF83;
parameter CSR_MTVT_MASK         = 32'hFFFFFFE0;
parameter CSR_MINTSTATUS_MASK   = 32'hFF000000;
parameter CSR_MSCRATCH_MASK     = 32'hFFFFFFFF;
parameter CSR_CPUCTRL_MASK      = 32'h000F001F;
parameter CSR_PMPNCFG_MASK      = 8'hFF;
parameter CSR_PMPADDR_MASK      = 32'hFFFFFFFF;
parameter CSR_MSECCFG_MASK      = 32'h00000007;
parameter CSR_PRV_LVL_MASK      = 32'hFFFFFFFF;
parameter CSR_MSTATEEN0_MASK    = 32'h00000004;

// CSR operations

parameter CSR_OP_WIDTH = 3;

typedef enum logic [CSR_OP_WIDTH-1:0]
{
 CSR_OP_READ  = 3'b000,
 CSR_OP_WRITE = 3'b001,
 CSR_OP_SET   = 3'b010,
 CSR_OP_CLEAR = 3'b011,
 CSR_OP_CSRRW = 3'b100
} csr_opcode_e;

// CSR interrupt pending/enable bits
parameter int unsigned CSR_MSIX_BIT      = 3;
parameter int unsigned CSR_MTIX_BIT      = 7;
parameter int unsigned CSR_MEIX_BIT      = 11;
parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
parameter int unsigned CSR_MFIX_BIT_HIGH = 31;

// CPUCTRL
typedef struct packed {
  logic [31:20] zero1;
  logic [19:16] rnddummyfreq;
  logic [15: 5] zero0;
  logic         integrity;
  logic         pc_hardening;
  logic         rndhint;
  logic         rnddummy;
  logic         dataindtiming;
} cpuctrl_t;

parameter cpuctrl_t CPUCTRL_RESET_VAL = '{
  integrity     : 1'b1,
  pc_hardening  : 1'b1,
  dataindtiming : 1'b1,
  default:    '0};


typedef struct packed {
  logic [31:0] lfsr2;
  logic [31:0] lfsr1;
  logic [31:0] lfsr0;
  cpuctrl_t    cpuctrl;
  logic        cntrst;
} xsecure_ctrl_t;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} privlvl_t;

parameter privlvl_t PRIV_LVL_LOWEST = PRIV_LVL_U;

// Struct used for setting privilege lelve
typedef struct packed {
  logic        priv_lvl_set;
  privlvl_t    priv_lvl;
} privlvlctrl_t;

// Machine Vendor ID - OpenHW JEDEC ID is '2 decimal (bank 13)'
parameter MVENDORID_OFFSET = 7'h2;      // Final byte without parity bit
parameter MVENDORID_BANK = 25'hC;       // Number of continuation codes

// Machine Architecture ID (https://github.com/riscv/riscv-isa-manual/blob/master/marchid.md)
parameter MARCHID = 32'h15;

// MachineImplementation ID
parameter MIMPID_MAJOR = 4'h0;  // Major ID
parameter MIMPID_MINOR = 4'h0;  // Minor ID

parameter MTVEC_MODE_BASIC  = 2'b01;
parameter MTVEC_MODE_CLIC   = 2'b11;
parameter NUM_HPM_EVENTS    = 2;

parameter MSTATUS_MIE_BIT      = 3;
parameter MSTATUS_MPIE_BIT     = 7;
parameter MSTATUS_MPP_BIT_LOW  = 11;
parameter MSTATUS_MPP_BIT_HIGH = 12;
parameter MSTATUS_MPRV_BIT     = 17;
parameter MSTATUS_TW_BIT       = 21;

parameter MCAUSE_MPIE_BIT      = 27;
parameter MCAUSE_MPP_BIT_LOW   = 28;
parameter MCAUSE_MPP_BIT_HIGH  = 29;

// misa
parameter logic [1:0] MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32

// Types for packed struct CSRs

typedef struct packed {
  logic [31:6] base;
  logic [5: 0] mode;
} jvt_t;

// todo: Might change this is Zc TG changes spec to allow some
// bits of the jvt.base to be WARL
parameter JVT_ADDR_WIDTH = 22;

typedef struct packed {
  logic         sd;     // State dirty
  logic [30:23] zero3;  // Hardwired zero
  logic         tsr;    // Hardwired zero
  logic         tw;     // Hardwired zero
  logic         tvm;    // Hardwired zero
  logic         mxr;    // Hardwired zero
  logic         sum;    // Hardwired zero
  logic         mprv;
  logic [16:15] xs;     // Other extension context
  logic [14:13] fs;     // FPU extension context status
  logic [12:11] mpp;
  logic [10:9]  vs;     // Vector extension context status
  logic         spp;    // Hardwired zero
  logic         mpie;
  logic         ube;    // Hardwired zero
  logic         spie;   // Hardwired zero
  logic         zero2;  // Reserved, hardwired to zero.
  logic         mie;
  logic         zero1;  // Reserved, hardwired to zero.
  logic         sie;    // Hardwired to zero
  logic         zero0;  // Reserved, hardwired zero
} mstatus_t;

typedef struct packed {
  logic [31:6] zero1;
  logic mbe;
  logic sbe;
  logic [3:0] zero0;
} mstatush_t;

// Debug Cause
parameter DBG_CAUSE_NONE       = 3'h0;
parameter DBG_CAUSE_EBREAK     = 3'h1;
parameter DBG_CAUSE_TRIGGER    = 3'h2;
parameter DBG_CAUSE_HALTREQ    = 3'h3;
parameter DBG_CAUSE_STEP       = 3'h4;
parameter DBG_CAUSE_RSTHALTREQ = 3'h5;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;

// Trigger types
typedef enum logic [3:0] {
  TTYPE_MCONTROL = 4'h2,
  TTYPE_ICOUNT = 4'h3,
  TTYPE_ITRIGGER = 4'h4,
  TTYPE_ETRIGGER = 4'h5
} trigger_type_e;

typedef struct packed {
    logic [31:28] xdebugver;
    logic [27:18] zero2;
    logic         ebreakvs; // Hardwired to zero
    logic         ebreakvu; // Hardwired to zero
    logic         ebreakm;
    logic         zero1;
    logic         ebreaks;
    logic         ebreaku;
    logic         stepie;
    logic         stopcount;
    logic         stoptime;
    logic [8:6]   cause;
    logic         v;        // Hardwired to zero
    logic         mprven;
    logic         nmip;
    logic         step;
    privlvl_t     prv;
} dcsr_t;

typedef struct packed {
  logic           irq;
  logic           minhv;           // CLIC only
  logic [29:28]   mpp;             // CLIC only, same as mstatus.mpp
  logic           mpie;            // CLIC only, same as mstatus.mpie
  logic [26:24]   zero1;           // Reserved, hardwired to zero.
  logic [23:16]   mpil;            // CLIC only. Previous interrupt level
  logic [15:11]   zero0;           // Reserved, hardwired to zero.
  logic [10: 0]   exception_code;  // Exception cause
} mcause_t;

typedef struct packed {
  logic [31:7] addr;
  logic        zero0;
  logic [ 5:2] submode;
  logic [ 1:0] mode;
} mtvec_t;

typedef struct packed {
  logic [31:6] addr;
  logic [ 5:0] zero0;
} mtvt_t;

typedef struct packed {
  logic [31:24] mil;
  logic [23:16] zero0;
  logic [15: 8] sil;
  logic [ 7: 0] uil;
} mintstatus_t;


parameter dcsr_t DCSR_RESET_VAL = '{
  xdebugver : XDEBUGVER_STD,
  cause:      DBG_CAUSE_NONE,
  prv:        PRIV_LVL_M,
  default:    '0};

parameter mtvec_t MTVEC_BASIC_RESET_VAL = '{
  addr: 'd0,
  zero0: 'd0,
  submode: 'd0,
  mode:  MTVEC_MODE_BASIC};

parameter mtvec_t MTVEC_CLIC_RESET_VAL = '{
  addr: 'd0,
  zero0: 'd0,
  submode: 'd0,
  mode:  MTVEC_MODE_CLIC};

parameter mtvt_t MTVT_RESET_VAL = '{
  addr:  '0,
  zero0: '0};

parameter mintstatus_t MINTSTATUS_RESET_VAL = '{
  mil:   '0,
  zero0: '0,
  sil:   '0,
  uil:   '0};

parameter mstatus_t MSTATUS_RESET_VAL = '{
  tw      : 1'b0,
  mprv    : 1'b0,
  zero3   : 'b0,
  mpp     : PRIV_LVL_M,
  zero2   : 'b0,
  mpie    : 1'b0,
  zero1   : 'b0,
  mie     : 1'b0,
  zero0   : 'b0,
  default : 'b0};

parameter logic [31:0] TDATA1_RST_VAL = {
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
  1'b0,                  // execute : match instruction address
  1'b0,                  // store   : not supported
  1'b0};                 // load    : not supported


///////////////////////////////////////////////
//   ___ ____    ____  _                     //
//  |_ _|  _ \  / ___|| |_ __ _  __ _  ___   //
//   | || | | | \___ \| __/ _` |/ _` |/ _ \  //
//   | || |_| |  ___) | || (_| | (_| |  __/  //
//  |___|____/  |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// Enable Security Features
parameter SECURE = 1;

// Register file read/write ports
parameter REGFILE_NUM_WRITE_PORTS = 1;

// Address width of register file
parameter REGFILE_ADDR_WIDTH = 5;

// Data width of register file
parameter REGFILE_DATA_WIDTH = 32;

// Width of register file ECC
parameter REGFILE_ECC_WIDTH = 6;

// Word width of register file memory
parameter REGFILE_WORD_WIDTH = (SECURE) ? REGFILE_DATA_WIDTH + REGFILE_ECC_WIDTH : REGFILE_DATA_WIDTH;

// Number of regfile integer registers
parameter REGFILE_NUM_WORDS = 2**(REGFILE_ADDR_WIDTH);

// Register file address type
typedef logic [REGFILE_ADDR_WIDTH-1:0] rf_addr_t;

// Register file data type
typedef logic [REGFILE_DATA_WIDTH-1:0] rf_data_t;

// forwarding operand mux
typedef enum logic[1:0] {
                         SEL_REGFILE = 2'b00,
                         SEL_FW_EX   = 2'b01,
                         SEL_FW_WB   = 2'b10,
                         SEL_LFSR    = 2'b11
                         } op_fw_mux_e;

typedef enum logic {
                         SELJ_REGFILE = 1'b0,
                         SELJ_FW_WB   = 1'b1
                         } jalr_fw_mux_e;

// Operand a selection
typedef enum logic[1:0] {
                         OP_A_REGA_OR_FWD = 2'b00,
                         OP_A_CURRPC      = 2'b01,
                         OP_A_IMM         = 2'b10,
                         OP_A_NONE        = 2'b11
                         } alu_op_a_mux_e;


// Immediate a selection
typedef enum logic {
                    IMMA_Z      = 1'b0,
                    IMMA_ZERO   = 1'b1
                    } imm_a_mux_e;


// Operand b selection
typedef enum logic[1:0] {
                    OP_B_REGB_OR_FWD = 2'b00,
                    OP_B_IMM         = 2'b01,
                    OP_B_NONE        = 2'b10
                    } alu_op_b_mux_e;

// Immediate b selection
typedef enum logic[2:0] {
                         IMMB_I      = 3'b000,
                         IMMB_S      = 3'b001,
                         IMMB_U      = 3'b010,
                         IMMB_PCINCR = 3'b011,
                         IMMB_CIW    = 3'b100,
                         IMMB_CL    = 3'b101
                         } imm_b_mux_e;

// Operand c selection
typedef enum logic[1:0] {
                         OP_C_REGB_OR_FWD = 2'b00,
                         OP_C_BCH         = 2'b01,
                         OP_C_NONE        = 2'b10
                         } op_c_mux_e;

// Control transfer (branch/jump) target mux
typedef enum logic[1:0] {
                         CT_JAL  = 2'b01,
                         CT_JALR = 2'b10,
                         CT_BCH  = 2'b11
                         } bch_jmp_mux_e;

// Decoder control signals
typedef struct packed {
  logic                              alu_en;
  logic                              alu_bch;
  logic                              alu_jmp;
  logic                              alu_jmpr;
  alu_opcode_e                       alu_operator;
  alu_op_a_mux_e                     alu_op_a_mux_sel;
  alu_op_b_mux_e                     alu_op_b_mux_sel;
  op_c_mux_e                         op_c_mux_sel;
  imm_a_mux_e                        imm_a_mux_sel;
  imm_b_mux_e                        imm_b_mux_sel;
  bch_jmp_mux_e                      bch_jmp_mux_sel;
  logic                              mul_en;
  mul_opcode_e                       mul_operator;
  logic [1:0]                        mul_signed_mode;
  logic                              div_en;
  div_opcode_e                       div_operator;
  logic [1:0]                        rf_re; // Core internals will never use more than two read ports.
  logic                              rf_we;
  logic                              csr_en;
  csr_opcode_e                       csr_op;
  logic                              lsu_en;
  logic                              lsu_we;
  logic [1:0]                        lsu_size;
  logic                              lsu_sext;
  logic                              sys_en;
  logic                              illegal_insn;
  logic                              sys_dret_insn;
  logic                              sys_ebrk_insn;
  logic                              sys_ecall_insn;
  logic                              sys_fencei_insn;
  logic                              sys_mret_insn;
  logic                              sys_wfi_insn;
  logic                              sys_wfe_insn;
} decoder_ctrl_t;

  parameter decoder_ctrl_t DECODER_CTRL_ILLEGAL_INSN =  '{
                                                          alu_en                       : 1'b0,
                                                          alu_bch                      : 1'b0,
                                                          alu_jmp                      : 1'b0,
                                                          alu_jmpr                     : 1'b0,
                                                          alu_operator                 : ALU_SLTU,
                                                          alu_op_a_mux_sel             : OP_A_NONE,
                                                          alu_op_b_mux_sel             : OP_B_NONE,
                                                          op_c_mux_sel                 : OP_C_NONE,
                                                          imm_a_mux_sel                : IMMA_ZERO,
                                                          imm_b_mux_sel                : IMMB_I,
                                                          bch_jmp_mux_sel              : CT_JAL,
                                                          mul_en                       : 1'b0,
                                                          mul_operator                 : MUL_M32,
                                                          mul_signed_mode              : 2'b00,
                                                          div_en                       : 1'b0,
                                                          div_operator                 : DIV_DIVU,
                                                          rf_re                        : 2'b00,
                                                          rf_we                        : 1'b0,
                                                          csr_en                       : 1'b0,
                                                          csr_op                       : CSR_OP_READ,
                                                          lsu_en                       : 1'b0,
                                                          lsu_we                       : 1'b0,
                                                          lsu_size                     : 2'b00,
                                                          lsu_sext                     : 1'b0,
                                                          sys_en                       : 1'b0,
                                                          illegal_insn                 : 1'b1,
                                                          sys_dret_insn                : 1'b0,
                                                          sys_ebrk_insn                : 1'b0,
                                                          sys_ecall_insn               : 1'b0,
                                                          sys_fencei_insn              : 1'b0,
                                                          sys_mret_insn                : 1'b0,
                                                          sys_wfi_insn                 : 1'b0,
                                                          sys_wfe_insn                 : 1'b0
                                                          };

///////////////////////////////////////////////
//   ___ _____   ____  _                     //
//  |_ _|  ___| / ___|| |_ __ _  __ _  ___   //
//   | || |_    \___ \| __/ _` |/ _` |/ _ \  //
//   | ||  _|    ___) | || (_| | (_| |  __/  //
//  |___|_|     |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// PC mux selector defines
typedef enum logic[3:0] {
  PC_BOOT       = 4'b0000,
  PC_MRET       = 4'b0001,
  PC_DRET       = 4'b0010,
  PC_JUMP       = 4'b0100,
  PC_BRANCH     = 4'b0101,
  PC_WB_PLUS4   = 4'b0110,
  PC_TRAP_EXC   = 4'b1000,
  PC_TRAP_IRQ   = 4'b1001,
  PC_TRAP_DBD   = 4'b1010,
  PC_TRAP_DBE   = 4'b1011,
  PC_TRAP_NMI   = 4'b1100,
  PC_TRAP_CLICV = 4'b1101,
  PC_POINTER    = 4'b1110,
  PC_TBLJUMP    = 4'b1111
} pc_mux_e;

// Exception Cause
parameter EXC_CAUSE_INSTR_FAULT           = 11'h01;
parameter EXC_CAUSE_ILLEGAL_INSN          = 11'h02;
parameter EXC_CAUSE_BREAKPOINT            = 11'h03;
parameter EXC_CAUSE_LOAD_FAULT            = 11'h05;
parameter EXC_CAUSE_STORE_FAULT           = 11'h07;
parameter EXC_CAUSE_ECALL_UMODE           = 11'h08;
parameter EXC_CAUSE_ECALL_MMODE           = 11'h0B;
parameter EXC_CAUSE_INSTR_INTEGRITY_FAULT = 11'h19;
parameter EXC_CAUSE_INSTR_BUS_FAULT       = 11'h30;

parameter INT_CAUSE_LSU_LOAD_FAULT            = 11'h400;
parameter INT_CAUSE_LSU_STORE_FAULT           = 11'h401;
parameter INT_CAUSE_LSU_LOAD_INTEGRITY_FAULT  = 11'h402;
parameter INT_CAUSE_LSU_STORE_INTEGRITY_FAULT = 11'h403;

// Interrupt mask
parameter IRQ_MASK = 32'hFFFF0888;

// NMI offset
parameter NMI_MTVEC_INDEX = 5'd15;

////////////////////////////
//                        //
//    /\/\    / _ \/\ /\  //
//   /    \  / /_)/ / \ \ //
//  / /\/\ \/ ___/\ \_/ / //
//  \/    \/\/     \___/  //
//                        //
////////////////////////////

// PMA region config
// word_addr_low/high: Address boundaries, containing word aligned 34-bit address (address[33:2])
// main:               Region is defined as main memory (as opposed to I/O memory)
// bufferable:         Transfers in this region are bufferable
// cacheable:          Transfers in this region are cacheable
// integrity:          Transfers in this region are checked for (rchk) integrity
typedef struct packed {
  logic [31:0] word_addr_low;
  logic [31:0] word_addr_high;
  logic        main;
  logic        bufferable;
  logic        cacheable;
  logic        integrity;
} pma_cfg_t;

// Default attribution when PMA is not configured (PMA_NUM_REGIONS=0) (Address is don't care)
parameter pma_cfg_t NO_PMA_R_DEFAULT = '{word_addr_low   : 0,
                                         word_addr_high  : 0,
                                         main            : 1'b1,
                                         bufferable      : 1'b0,
                                         cacheable       : 1'b0,
                                         integrity       : 1'b0};

// Default attribution when PMA is configured (Address is don't care)
parameter pma_cfg_t PMA_R_DEFAULT = '{word_addr_low   : 0,
                                      word_addr_high  : 0,
                                      main            : 1'b0,
                                      bufferable      : 1'b0,
                                      cacheable       : 1'b0,
                                      integrity       : 1'b0};

// MPU status. Used for PMA and PMP
typedef enum logic [1:0] {
                          MPU_OK       = 2'h0,
                          MPU_RE_FAULT = 2'h1,
                          MPU_WR_FAULT = 2'h2
                          } mpu_status_e;

typedef enum logic [2:0] {MPU_IDLE, MPU_RE_ERR_RESP, MPU_RE_ERR_WAIT, MPU_WR_ERR_RESP, MPU_WR_ERR_WAIT} mpu_state_e;

// PMP constants
parameter int unsigned PMP_MAX_REGIONS      = 64;
parameter int unsigned PMPNCFG_W            = 8;

parameter int unsigned CSR_MSECCFG_MML_BIT  = 0;
parameter int unsigned CSR_MSECCFG_MMWP_BIT = 1;
parameter int unsigned CSR_MSECCFG_RLB_BIT  = 2;

// PMP access type
typedef enum logic [1:0] {
  PMP_ACC_EXEC    = 2'b00,
  PMP_ACC_WRITE   = 2'b01,
  PMP_ACC_READ    = 2'b10
} pmp_req_e;

// PMP cfg structures
typedef enum logic [1:0] {
  PMP_MODE_OFF   = 2'b00,
  PMP_MODE_TOR   = 2'b01,
  PMP_MODE_NA4   = 2'b10,
  PMP_MODE_NAPOT = 2'b11
} pmpncfg_mode_e;

// PMP region config
typedef struct packed {
  logic          lock;
  logic [6:5]    zero0;
  pmpncfg_mode_e mode;
  logic          exec;
  logic          write;
  logic          read;
} pmpncfg_t;

// Default PMP region configuration
parameter pmpncfg_t PMPNCFG_DEFAULT = '{lock  : 1'b0,
                                        zero0 : 2'b00,
                                        mode  : PMP_MODE_OFF,
                                        exec  : 1'b0,
                                        write : 1'b0,
                                        read  : 1'b0};

// Machine Security Configuration (SMEPMP)
typedef struct packed {
  logic [31:3] zero0;
  logic        rlb;  // Rule Locking Bypass
  logic        mmwp; // Machine Mode Whitelist Policy
  logic        mml;  // Machine Mode Lockdown
} mseccfg_t;

// Default value for MSECCFG
parameter mseccfg_t MSECCFG_DEFAULT = '{zero0 : 29'h0,
                                        rlb   : 1'b0,
                                        mmwp  : 1'b0,
                                        mml   : 1'b0};

// Struct containing all PMP related CSR's
typedef struct packed {
  pmpncfg_t [PMP_MAX_REGIONS-1:0]   cfg;
  logic [PMP_MAX_REGIONS-1:0][33:0] addr;
  mseccfg_t                         mseccfg;
} pmp_csr_t;


// OBI bus and internal data types

parameter INSTR_ADDR_WIDTH = 32;
parameter INSTR_DATA_WIDTH = 32;
parameter DATA_ADDR_WIDTH = 32;
parameter DATA_DATA_WIDTH = 32;

typedef struct packed {
  logic        req;
  logic        reqpar;
} obi_req_t;

typedef struct packed {
  logic        gnt;
  logic        gntpar;
} obi_gnt_t;

typedef struct packed {
  logic        rvalid;
  logic        rvalidpar;
} obi_rvalid_t;

typedef struct packed {
  logic [INSTR_ADDR_WIDTH-1:0] addr;
  logic [1:0]                  memtype;
  logic [2:0]                  prot;
  logic                        dbg;
  logic [11:0]                 achk;
  logic                        integrity; // PMA integrity attribute, will not be passed onto OBI
} obi_inst_req_t;

typedef struct packed {
  logic [INSTR_DATA_WIDTH-1:0] rdata;
  logic                        err;
  logic [4:0]                  rchk;
  logic                        integrity_err;  // Calculated in instr_obi_interface and appended to struct upon rvalid
  logic                        integrity;   // Tracked through instr_obi_interface and appended to struct upon rvalid
} obi_inst_resp_t;

typedef struct packed {
  logic [DATA_ADDR_WIDTH-1:0]     addr;
  logic                           we;
  logic [(DATA_DATA_WIDTH/8)-1:0] be;
  logic [DATA_DATA_WIDTH-1:0]     wdata;
  logic [1:0]                     memtype;
  logic [2:0]                     prot;
  logic                           dbg;
  logic [11:0]                    achk;
  logic                           integrity; // PMA integrity attribute, will not be passed onto OBI
} obi_data_req_t;

typedef struct packed {
  logic [DATA_DATA_WIDTH-1:0] rdata;
  logic                       err;
  logic [4:0]                 rchk;
  logic                       integrity_err;    // Calculated in data_obi_interface and appended to struct upon rvalid
  logic                       integrity;   // Tracked through data_obi_interface and appended to struct upon rvalid
} obi_data_resp_t;

// Data/instruction transfer bundeled with MPU status
typedef struct packed {
 obi_inst_resp_t             bus_resp;
 mpu_status_e                mpu_status;
} inst_resp_t;

// Reset value for the inst_resp_t type
parameter inst_resp_t INST_RESP_RESET_VAL = '{
  // Setting rdata[1:0] to 2'b11 to easily assert that all
  // instructions in ID are uncompressed
  bus_resp    : '{rdata: 32'h3, err: 1'b0, rchk: 5'b0,integrity_err: 1'b0, integrity: 1'b0},
  mpu_status  : MPU_OK
};

// Reset value for the obi_inst_req_t type
parameter obi_inst_req_t OBI_INST_REQ_RESET_VAL = '{
  addr      : 'h0,
  memtype   : 'h0,
  prot      : {PRIV_LVL_M, 1'b0},
  dbg       : 1'b0,
  achk      : 12'hFFF,
  integrity : 1'b0
};

// Data transfer bundeled with MPU status
typedef struct packed {
  obi_data_resp_t             bus_resp;
  mpu_status_e                mpu_status;
} data_resp_t;

// LSU transaction
typedef struct packed {
  logic [DATA_ADDR_WIDTH-1:0]     addr;
  logic [1:0]                     size;
  logic                           we;
  logic                           sext;
  logic [DATA_DATA_WIDTH-1:0]     wdata;
  logic [1:0]                     mode;
  logic                           dbg;
} trans_req_t;

// Response type for tracking bufferable and load/store in lsu response filter
typedef struct packed {
  logic bufferable;
  logic store;
} outstanding_t;

// Instruction meta data
// TODO: consider moving other instruction meta data to this struct. e.g. xxx_insn, pc, etc (but don't move stuff here that is specific to one functional unit)
typedef struct packed
{
  logic        dummy;
  logic        hint;
  logic        compressed;
  logic        clic_ptr;
  logic        tbljmp;
} instr_meta_t;

// Struct for carrying eXtension interface information
typedef struct packed
{
  logic        exception;       // Can offloaded ins cause an exception?
  logic        loadstore; // Is offloaded ins a load or store?
  logic        dualwrite; // Will oflfoaded ins cause a dual writeback?
  logic [31:0] id;        // ID of offloaded ins
  logic        accepted;  // Was the offloaded instruction accepted or not?
} xif_meta_t;

typedef struct packed
{
  logic        bus_err;
  logic        integrity_err;
  logic        store;
} lsu_err_wb_t;

// IF/ID pipeline
typedef struct packed {
  logic        instr_valid;
  inst_resp_t  instr;
  instr_meta_t instr_meta;
  logic [31:0] pc;
  logic [15:0] compressed_instr;
  logic        illegal_c_insn;
  privlvl_t    priv_lvl;
  logic        trigger_match;
  logic [31:0] xif_id;           // ID of offloaded instruction
  logic [31:0] ptr;              // Flops to hold 32-bit pointer
  logic        first_op;         // First part of multi operation instruction
  logic        last_op;          // Last part of multi operation instruction
  logic        abort_op;         // Instruction will be aborted due to known exceptions or trigger matches
} if_id_pipe_t;

// ID/EX pipeline
typedef struct packed {

  // ALU
  logic         alu_en;
  logic         alu_bch;
  logic         alu_jmp;
  alu_opcode_e  alu_operator;
  logic [31:0]  alu_operand_a;
  logic [31:0]  alu_operand_b;
  logic [31:0]  operand_c;

  // Multiplier
  logic         mul_en;
  mul_opcode_e  mul_operator;
  logic [ 1:0]  mul_signed_mode;

  // Divider
  logic         div_en;
  div_opcode_e  div_operator;

  // Operands for multiplier and divider
  logic [31:0]  muldiv_operand_a;
  logic [31:0]  muldiv_operand_b;

  // CSR
  logic         csr_en;
  csr_opcode_e  csr_op;

  // LSU
  logic         lsu_en;
  logic         lsu_we;
  logic [1:0]   lsu_size;
  logic         lsu_sext;

  // SYS
  logic         sys_en;
  logic         sys_dret_insn;
  logic         sys_ebrk_insn;
  logic         sys_ecall_insn;
  logic         sys_fencei_insn;
  logic         sys_mret_insn;
  logic         sys_wfi_insn;
  logic         sys_wfe_insn;

  logic         illegal_insn;

  // Trigger match on insn
  logic         trigger_match;

  // Register write control
  logic         rf_we;
  rf_addr_t     rf_waddr;

  // Signals for exception handling etc passed on for evaluation in WB stage
  logic [31:0]  pc;
  inst_resp_t   instr;            // Contains instruction word (may be compressed),bus error status and MPU status
  instr_meta_t  instr_meta;
  logic         instr_valid;      // instruction in EX is valid

  // Priviledge level
  privlvl_t    priv_lvl;

  // eXtension interface
  logic         xif_en;           // Instruction has been offloaded via eXtension interface
  xif_meta_t    xif_meta;         // xif meta struct

  logic         first_op;         // First part of multi operation instruction
  logic         last_op;          // Last part of multi operation instruction
  logic         abort_op;         // Instruction will be aborted due to known exceptions or trigger matches

} id_ex_pipe_t;

// EX/WB pipeline
typedef struct packed {
  logic         rf_we;
  rf_addr_t     rf_waddr;
  logic [31:0]  rf_wdata;

  // ALU
  logic         alu_jmp_qual;           // Qualified with alu_en
  logic         alu_bch_qual;           // Qualified with alu_en
  logic         alu_bch_taken_qual;     // Qualified with alu_en

  // CSR
  logic         csr_en;
  csr_opcode_e  csr_op;
  logic [11:0]  csr_addr;
  logic [31:0]  csr_wdata;
  logic         csr_mnxti_access;

  // LSU
  logic         lsu_en;

  // Trigger match on insn
  logic         trigger_match;

  // Signals for exception handling etc
  logic [31:0]  pc;
  inst_resp_t   instr;            // Contains instruction word (may be compressed), bus error status and MPU status
  instr_meta_t  instr_meta;
  logic         instr_valid;      // instruction in WB is valid
  logic         illegal_insn;

  logic         sys_en;
  logic         sys_dret_insn;
  logic         sys_ebrk_insn;
  logic         sys_ecall_insn;
  logic         sys_fencei_insn;
  logic         sys_mret_insn;
  logic         sys_wfi_insn;
  logic         sys_wfe_insn;

  // eXtension interface
  logic         xif_en;           // Instruction has been offloaded via eXtension interface
  xif_meta_t    xif_meta;         // xif meta struct

  logic         first_op;         // First part of multi operation instruction
  logic         last_op;          // Last part of multi operation instruction
  logic         abort_op;         // Instruction will be aborted due to known exceptions or trigger matches
} ex_wb_pipe_t;

// Performance counter events
typedef struct packed {
  logic                              minstret;
} mhpmevent_t;


// Controller Bypass outputs
typedef struct packed {
  op_fw_mux_e   operand_a_fw_mux_sel;   // Operand A forward mux sel
  op_fw_mux_e   operand_b_fw_mux_sel;   // Operand B forward mux sel
  jalr_fw_mux_e jalr_fw_mux_sel;        // Jump target forward mux sel
  logic         jalr_stall;             // Stall due to JALR hazard (JALR used result from EX or LSU result in WB)
  logic         load_stall;             // Stall due to load operation
  logic         csr_stall;
  logic         wfi_wfe_stall;
  logic         mnxti_id_stall;         // Stall ID due to mnxti CSR access in EX
  logic         mnxti_ex_stall;         // Stall EX due to LSU instruction in WB
  logic         minstret_stall;         // Stall due to minstret/h read in EX
  logic         deassert_we;            // Deassert write enable and special insn bits
  logic         id_stage_abort;         // Same signal as deassert_we, with better name for use in the controller.
  logic         xif_exception_stall;    // Stall (EX) if xif insn in WB can cause an exception
  logic         irq_enable_stall;       // Stall (EX) if an interrupt may be enabled by the instruction in WB.
} ctrl_byp_t;

// Controller FSM outputs
typedef struct packed {
  logic        ctrl_busy;             // Core is busy processing instructions

  // to IF stage
  logic        instr_req;             // Start fetching instructions
  logic        pc_set;                // Jump to address set by pc_mux
  logic        pc_set_clicv;          // Signal pc_set it for CLIC vectoring pointer load
  logic        pc_set_tbljmp;         // Signal pc_set is for Zc* cm.jt / cm.jalt pointer load
  pc_mux_e     pc_mux;                // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  logic        allow_dummy_instr;     // Allow dummy instruction insertion

  // To WB stage
  logic        block_data_addr;       // To LSU to prevent data_addr_wb_i updates between error and taken NMI
  logic [4:0]  mtvec_pc_mux;          // Id of taken basic mode irq (to IF, EXC_PC_MUX, zeroed if mtvec_mode==0)
  logic [9:0]  mtvt_pc_mux;           // Id of taken CLIC irq (to IF, EXC_PC_MUX, zeroed if not shv)
                                      // Setting to 11 bits (max), unused bits will be tied off
  logic [7:0]  jvt_pc_mux;            // Index for table jumps

  logic        irq_ack;               // Irq has been taken
  logic [9:0]  irq_id;                // Id of taken irq. Max width (1024 interrupts), unused bits will be tied off
  logic [7:0]  irq_level;             // Level of taken irq (CLIC only)
  logic [1:0]  irq_priv;              // Associated privilege mode for taken irq (CLIC only)
  logic        irq_shv;               // Selective hardware vectoring for taken irq (CLIC only)
  logic        dbg_ack;               // Debug has been taken

  // Debug outputs
  logic        debug_mode_if;          // Flag signalling we are in debug mode, valid for IF
  logic        debug_mode;             // Flag signalling we are in debug mode, valid for ID, EX and WB
  logic [2:0]  debug_cause;            // cause of debug entry
  logic        debug_csr_save;         // Update debug CSRs
  logic        debug_wfi_wfe_no_sleep; // Debug prevents core from sleeping after WFI
  logic        debug_havereset;        // Signal to external debugger that we have reset
  logic        debug_running;          // Signal to external debugger that we are running (not in debug)
  logic        debug_halted;           // Signal to external debugger that we are halted (in debug mode)

  // Alert Trigger for minor alert
  logic        exception_alert_minor;
  // Alert Trigger for major alert
  logic        exception_alert_major;

  // Wakeup Signal to sleep unit
  logic        wake_from_sleep;       // Wakeup (due to irq or debug)

  // CSR signals
  logic [31:0] pipe_pc;             // PC from pipeline
  mcause_t     csr_cause;           // CSR cause (saves to mcause CSR)
  logic        csr_restore_mret;    // Restore CSR due to mret
  logic        csr_restore_dret;    // Restore CSR due to dret
  logic        csr_save_cause;      // Update CSRs
  logic        csr_clear_minhv;     // Clear the mcause.minhv field
  logic        pending_nmi;         // An NMI is pending (for dcsr.nmip)

  logic        mret_jump_id;        // Jump from ID stage due to MRET
  logic        jump_in_id;
  logic        jump_in_id_raw;
  logic        jump_taken_id;       // A jump was taken from ID stage
  logic        branch_in_ex;
  logic        branch_in_ex_raw;    // Branch in EX, not qualified with instr_valid
  logic        branch_taken_ex;     // A branch was taken from EX stage

  // Performance counter events
  mhpmevent_t  mhpmevent;

  // Halt signals
  logic        halt_if; // Halt IF stage
  logic        halt_id; // Halt ID stage
  logic        halt_ex; // Halt EX stage
  logic        halt_wb; // Halt WB stage
  logic        halt_limited_wb; // Halt WB stage during SLEEP, but not cs_registers

  // Kill signals
  logic        kill_if; // Kill IF stage
  logic        kill_id; // Kill ID stage
  logic        kill_ex; // Kill EX stage
  logic        kill_wb; // Kill WB stage

  // Kill signal for xif_commit_if
  logic        kill_xif; // Kill (attempted) offloaded instruction

  // Signal that an exception is in WB
  logic        exception_in_wb;
} ctrl_fsm_t;

  ////////////////////////////////////////
  // Resolution functions

  function automatic privlvl_t dcsr_prv_resolve
  (
    privlvl_t   current_value,
    logic [1:0] next_value
  );
    // dcsr.prv is WARL(0x0, 0x3)
    return ((next_value != PRIV_LVL_M) && (next_value != PRIV_LVL_U)) ? current_value : privlvl_t'(next_value);
  endfunction

  function automatic logic [1:0] mstatus_mpp_resolve
  (
    logic [1:0] current_value,
    logic [1:0] next_value
  );
    // mstatus.mpp is WARL(0x0, 0x3)
    return ((next_value != PRIV_LVL_M) && (next_value != PRIV_LVL_U)) ? current_value : next_value;
  endfunction

  ///////////////////////////
  //                       //
  //    /\/\ (_)___  ___   //
  //   /    \| / __|/ __|  //
  //  / /\/\ \ \__ \ (__   //
  //  \/    \/_|___/\___|  //
  //                       //
  ///////////////////////////

  // RV32 base integer instruction set
  typedef enum logic {RV32I, RV32E} rv32_e;

  // Write buffer FSM state encoding
  typedef enum logic {WBUF_EMPTY, WBUF_FULL} write_buffer_state_e;

  // OBI interface FSM state encoding
  typedef enum logic {TRANSPARENT, REGISTERED} obi_if_state_e;

  // Enum used for configuration of B extension
  typedef enum logic [1:0] {B_NONE, ZBA_ZBB, ZBA_ZBB_ZBS, ZBA_ZBB_ZBC_ZBS} b_ext_e;

  // Enum used for configuration of M extension
  typedef enum logic [1:0] {M_NONE, M, ZMMUL} m_ext_e;

  // LFSR configuration
  typedef struct packed {
    logic [31:0] coeffs;
    logic [31:0] default_seed;
  } lfsr_cfg_t;

  // Defaults for LFSR configuration. Note that default setting should not be used.
  parameter lfsr_cfg_t LFSR_CFG_DEFAULT = '{coeffs       : 32'h0,
                                            default_seed : 32'h0};

  // Pipe PC mux selector defines. Used to control PC mux in control FSM
  typedef enum logic[1:0] {
    PC_IF,
    PC_ID,
    PC_EX,
    PC_WB
  } pipe_pc_mux_e;

  // Multi operation instructions
  // Width of ID stage multi op counter
  parameter MULTI_OP_CNT_WIDTH = 2;

  parameter logic [MULTI_OP_CNT_WIDTH-1:0] JMP_BCH_CYCLES = 2;

  //////////////////
  // Zc Sequencer //
  //////////////////

  typedef logic [4:0] regnum_t;
  typedef logic [3:0] seq_t;    // Max length is 16 for POPRETZ, counter limit is then 15.

  localparam REG_ZERO = 5'd0;
  localparam REG_RA = 5'd1;
  localparam REG_SP = 5'd2;

  typedef enum logic [3:0] {
    INVALID_INST,
    PUSH,
    POP,
    POPRET,
    POPRETZ,
    MVA01S,
    MVSA01,
    TBLJMP
  } seq_instr_e;

  typedef enum logic [3:0] {
    R_NONE    = 4'd0,
    RA_S0     = 4'd1,
    RA_S0_S1  = 4'd2,
    RA_S0_S2  = 4'd3,
    RA_S0_S3  = 4'd4,
    RA_S0_S4  = 4'd5,
    RA_S0_S5  = 4'd6,
    RA_S0_S6  = 4'd7,
    RA_S0_S7  = 4'd8,
    RA_S0_S8  = 4'd9,
    RA_S0_S9  = 4'd10,
    RA_S0_S11 = 4'd12
  } pushpop_rlist_e;


  typedef struct packed {
    logic [11:0]    stack_adj_base;        // Stack adjustment based on space needed by register list
    pushpop_rlist_e registers_saved;       // Number of s-registers saved (excluding ra)
    logic [11:0]    total_stack_adj;       // Total stack adjustment (register space + extra blocks)
    logic [11:0]    current_stack_adj;     // Current stack adjustment for use in sequence
    regnum_t        sreg;                  // Current s-register being pushed/popped
  } pushpop_decode_s;


  // Map any of S0-S11 to X-registers
  function automatic regnum_t sn_to_regnum(regnum_t snum);
    case (snum)
      0, 1:    sn_to_regnum = regnum_t'({(snum[3:1] != 3'd0), 1'b1, snum[2:0]});
      default: sn_to_regnum = regnum_t'({(snum[3:1] != 3'd0), snum[3], snum[2:0]});
    endcase
  endfunction

  // Set stack adjustment base based on rlist as suggested in Zc spec 0.70.4
  function automatic logic [11:0] get_stack_adj_base(logic [3:0] rlist);
    case (rlist)
      4,5,6,7: begin
        get_stack_adj_base = 12'd16;
      end
      8,9,10,11: begin
        get_stack_adj_base = 12'd32;
      end
      12,13,14: begin
        get_stack_adj_base = 12'd48;
      end
      15: begin
        get_stack_adj_base = 12'd64;
      end
      default: begin
        get_stack_adj_base = 12'd0;
      end
    endcase

  endfunction

  function automatic pushpop_rlist_e pushpop_reg_length(logic [3:0] rlist4);
    case (rlist4)
      'd0:     pushpop_reg_length = R_NONE;
      'd1:     pushpop_reg_length = R_NONE;
      'd2:     pushpop_reg_length = R_NONE;
      'd3:     pushpop_reg_length = R_NONE;
      'd4:     pushpop_reg_length = R_NONE;
      'd5:     pushpop_reg_length = RA_S0;
      'd6:     pushpop_reg_length = RA_S0_S1;
      'd7:     pushpop_reg_length = RA_S0_S2;
      'd8:     pushpop_reg_length = RA_S0_S3;
      'd9:     pushpop_reg_length = RA_S0_S4;
      'd10:    pushpop_reg_length = RA_S0_S5;
      'd11:    pushpop_reg_length = RA_S0_S6;
      'd12:    pushpop_reg_length = RA_S0_S7;
      'd13:    pushpop_reg_length = RA_S0_S8;
      'd14:    pushpop_reg_length = RA_S0_S9;
      'd15:    pushpop_reg_length = RA_S0_S11;
      default: pushpop_reg_length = R_NONE;
    endcase
  endfunction

  // State machine definition
  typedef enum logic [3:0] { S_IDLE, S_PUSH, S_POP, S_DMOVE, S_RA, S_SP, S_A0, S_RET} seq_state_e;

endpackage
