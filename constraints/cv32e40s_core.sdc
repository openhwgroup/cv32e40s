# Copyright 2020 Silicon Labs, Inc.
#
# This file, and derivatives thereof are licensed under the
# Solderpad License, Version 2.0 (the "License").
#
# Use of this file means you agree to the terms and conditions
# of the license and are in full compliance with the License.
#
# You may obtain a copy of the License at:
#
#     https://solderpad.org/licenses/SHL-2.0/
#
# Unless required by applicable law or agreed to in writing, software
# and hardware implementations thereof distributed under the License
# is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
# OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
#
# See the License for the specific language governing permissions and
# limitations under the License.

#//////////////////////////////////////////////////////////////////////////////
# Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
#                                                                            //
# Project Name:   CV32E40P                                                   //
#                                                                            //
# Description:    Example synthesis constraints.                             //
#                                                                            //
#                 The clock period and input/output delays are technology    //
#                 and project dependent and are expected to be adjusted as   //
#                 needed.                                                    //
#                                                                            //
#                 OBI related bus inputs arrive late on purpose and OBI      //
#                 related outputs are available earlier (as they shall not   //
#                 combinatorially depend on the OBI inputs)                  //
#                                                                            //
#//////////////////////////////////////////////////////////////////////////////

# 200MHz
set clock_period 5.0

# Input delays for interrupts
set in_delay_irq          [expr $clock_period * 0.50]

# Delay for CLIC
# todo: set final constraints for CLIC signals
set in_delay_clic         [expr $clock_period * 0.50]
set out_delay_clic        [expr $clock_period * 0.50]

# Input delays for early signals

set in_delay_early [expr $clock_period * 0.10] 

# Input delay for fencei handshake
set in_delay_fencei       [expr $clock_period * 0.80]
# Output delay for fencei handshake
set out_delay_fencei      [expr $clock_period * 0.60]

# OBI inputs delays
set in_delay_instr_gnt    [expr $clock_period * 0.70]
set in_delay_instr_rvalid [expr $clock_period * 0.80]
set in_delay_instr_rdata  [expr $clock_period * 0.80]
set in_delay_instr_err    [expr $clock_period * 0.80]

set in_delay_data_gnt     [expr $clock_period * 0.70]
set in_delay_data_rvalid  [expr $clock_period * 0.80]
set in_delay_data_rdata   [expr $clock_period * 0.70]
set in_delay_data_err     [expr $clock_period * 0.80]
set in_delay_data_exokay  [expr $clock_period * 0.80]

# OBI outputs delays
set out_delay_instr_req     [expr $clock_period * 0.60]
set out_delay_instr_addr    [expr $clock_period * 0.60]
set out_delay_instr_memtype [expr $clock_period * 0.60]
set out_delay_instr_prot    [expr $clock_period * 0.60]

set out_delay_data_req     [expr $clock_period * 0.60]
set out_delay_data_we      [expr $clock_period * 0.60]
set out_delay_data_be      [expr $clock_period * 0.60]
set out_delay_data_addr    [expr $clock_period * 0.60]
set out_delay_data_wdata   [expr $clock_period * 0.60]
set out_delay_data_atop    [expr $clock_period * 0.60]
set out_delay_data_memtype [expr $clock_period * 0.60]
set out_delay_data_prot    [expr $clock_period * 0.60]

# I/O delays for non RISC-V Bus Interface ports
set in_delay_other       [expr $clock_period * 0.10]
set out_delay_other      [expr $clock_period * 0.60]

# core_sleep_o output delay
set out_delay_core_sleep [expr $clock_period * 0.25]

# All clocks
set clock_ports [list \
    clk_i \
]

# IRQ Input ports
set irq_input_ports [list \
    irq_i* \
]

# CLIC Input ports
set clic_input_ports [list \
    clic_irq*_i* \
]
# CLIC Output ports
set clic_output_ports [list \
    clic_irq*_o* \
]

# Early Input ports (ideally from register)
set early_input_ports [list \
    debug_req_i \
    boot_addr_i* \
    mtvec_addr_i* \
    dm_halt_addr_i* \
    mhartid_i* \
    mimpid_i* \
    dm_exception_addr_i* \
    nmi_addr_i* \
]

# RISC-V OBI Input ports
set obi_input_ports [list \
    instr_gnt_i \
    instr_rvalid_i \
    instr_rdata_i* \
    instr_err_i \
    data_gnt_i \
    data_rvalid_i \
    data_rdata_i* \
    data_err_i \
    data_exokay_i \
]

# RISC-V OBI Output ports
set obi_output_ports [list \
    instr_req_o \
    instr_addr_o* \
    instr_memtype_o* \
    instr_prot_o* \
    instr_dbg_o \
    data_req_o \
    data_we_o \
    data_be_o* \
    data_addr_o* \
    data_wdata_o* \
    data_atop_o* \
    data_memtype_o* \
    data_prot_o* \
    data_dbg_o \
]

# RISC-V Sleep Output ports
set sleep_output_ports [list \
    core_sleep_o \
]

# Fencei handshake output ports
set fencei_output_ports [list \
    fencei_flush_req_o \
]

# Fencei handshake input ports
set fencei_input_ports [list \
    fencei_flush_ack_i \
]


############## Defining default clock definitions ##############

create_clock \
      -name clk_i \
      -period $clock_period \
      [get_ports clk_i] 


########### Defining Default I/O constraints ###################

set all_clock_ports $clock_ports

set all_other_input_ports  [remove_from_collection [all_inputs]  [get_ports [list $all_clock_ports $obi_input_ports $irq_input_ports $clic_input_ports $early_input_ports $fencei_input_ports ]]]

set all_other_output_ports [remove_from_collection [all_outputs] [get_ports [list $all_clock_ports $obi_output_ports $clic_output_ports $sleep_output_ports $fencei_output_ports]]]

# IRQs
set_input_delay  $in_delay_irq          [get_ports $irq_input_ports        ] -clock clk_i
set_input_delay  $in_delay_clic         [get_ports $clic_input_ports       ] -clock clk_i
set_output_delay $out_delay_clic        [get_ports $clic_output_ports      ] -clock clk_i

# OBI input/output delays
set_input_delay  $in_delay_instr_gnt    [ get_ports instr_gnt_i            ] -clock clk_i
set_input_delay  $in_delay_instr_rvalid [ get_ports instr_rvalid_i         ] -clock clk_i
set_input_delay  $in_delay_instr_rdata  [ get_ports instr_rdata_i*         ] -clock clk_i
set_input_delay  $in_delay_instr_err    [ get_ports instr_err_i*           ] -clock clk_i

set_input_delay  $in_delay_data_gnt     [ get_ports data_gnt_i             ] -clock clk_i
set_input_delay  $in_delay_data_rvalid  [ get_ports data_rvalid_i          ] -clock clk_i
set_input_delay  $in_delay_data_rdata   [ get_ports data_rdata_i*          ] -clock clk_i
set_input_delay  $in_delay_data_err     [ get_ports data_err_i             ] -clock clk_i
set_input_delay  $in_delay_data_exokay  [ get_ports data_exokay_i          ] -clock clk_i

set_output_delay $out_delay_instr_req      [ get_ports instr_req_o         ] -clock clk_i
set_output_delay $out_delay_instr_addr     [ get_ports instr_addr_o*       ] -clock clk_i
set_output_delay $out_delay_instr_memtype  [ get_ports instr_memtype_o*    ] -clock clk_i
set_output_delay $out_delay_instr_prot     [ get_ports instr_prot_o*       ] -clock clk_i

set_output_delay $out_delay_data_req      [ get_ports data_req_o           ] -clock clk_i
set_output_delay $out_delay_data_we       [ get_ports data_we_o            ] -clock clk_i
set_output_delay $out_delay_data_be       [ get_ports data_be_o*           ] -clock clk_i
set_output_delay $out_delay_data_addr     [ get_ports data_addr_o*         ] -clock clk_i
set_output_delay $out_delay_data_wdata    [ get_ports data_wdata_o*        ] -clock clk_i
set_output_delay $out_delay_data_atop     [ get_ports data_atop_o*         ] -clock clk_i
set_output_delay $out_delay_data_memtype  [ get_ports data_memtype_o*      ] -clock clk_i
set_output_delay $out_delay_data_prot     [ get_ports data_prot_o*         ] -clock clk_i

# Fencei handshake
set_input_delay  $in_delay_fencei       [get_ports $fencei_input_ports     ] -clock clk_i
set_output_delay $out_delay_fencei      [get_ports $fencei_output_ports    ] -clock clk_i

# Misc
set_input_delay  $in_delay_early        [get_ports $early_input_ports      ] -clock clk_i
set_input_delay  $in_delay_other        [get_ports $all_other_input_ports  ] -clock clk_i

set_output_delay $out_delay_other       [get_ports $all_other_output_ports ] -clock clk_i
set_output_delay $out_delay_core_sleep  [ get_ports core_sleep_o           ] -clock clk_i

