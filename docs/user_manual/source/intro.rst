Introduction
=============

|corev| is a 4-stage in-order 32-bit RISC-V
processor core. :numref:`blockdiagram` shows a block diagram of the core.

.. figure:: ../images/CV32E40S_Block_Diagram.png
   :name: blockdiagram
   :align: center
   :alt:

   Block Diagram of |corev| RISC-V Core

License
-------
Copyright 2020 OpenHW Group.

Copyright 2018 ETH Zurich and University of Bologna.

Copyright and related rights are licensed under the Solderpad Hardware
License, Version 0.51 (the “License”); you may not use this file except
in compliance with the License. You may obtain a copy of the License at
http://solderpad.org/licenses/SHL-0.51. Unless required by applicable
law or agreed to in writing, software, hardware and materials
distributed under this License is distributed on an “AS IS” BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Standards Compliance
--------------------

|corev| is a standards-compliant 32-bit RISC-V processor.
It follows these specifications:

.. [RISC-V-UNPRIV] RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213 (December 13, 2019),
   https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf

.. [RISC-V-PRIV] RISC-V Instruction Set Manual, Volume II: Privileged Architecture, Document Version 20211105-signoff (November 5, 2021),
   https://github.com/riscv/riscv-isa-manual/releases/download/draft-20211105-c30284b/riscv-privileged.pdf

.. [RISC-V-DEBUG] RISC-V Debug Support, version 1.0.0-STABLE, 9dc1ee4e4653730f1b318731f9ea8e97f116670a,
   https://github.com/riscv/riscv-debug-spec/blob/14a8d628e1fb736043eb54e0596adddb9717f0de/riscv-debug-stable.pdf

.. [RISC-V-SMCLIC] "Smclic" Core-Local Interrupt Controller (CLIC) RISC-V Privileged Architecture Extension, version 0.9-draft, 9/27/2022,
   https://github.com/riscv/riscv-fast-interrupt/blob/2749a7b7adb01fc308173441b8a6131a5d128f20/clic.pdf

.. [RISC-V-SMSTATEEN] RISC-V State Enable Extension, Smstateen, Version 0.6.3-70b1471, 2021-10-13: frozen,
   https://github.com/riscv/riscv-state-enable/releases/download/v0.6.3/Smstateen.pdf

..
.. [RISC-V-ZBA_ZBB_ZBC_ZBS] RISC-V Bit Manipulation ISA-extensions, Version 1.0.0-38-g865e7a7, 2021-06-28,
   https://github.com/riscv/riscv-bitmanip/releases/download/1.0.0/bitmanip-1.0.0-38-g865e7a7.pdf

.. [RISC-V-ZCA_ZCB_ZCMP_ZCMT] RISC-V Standard Extension for the **Zca**, **Zcb**, **Zcmp**, **Zcmt** subsets of **Zc**, v1.0.0-RC5.6 (not ratified yet),
   https://github.com/riscv/riscv-code-size-reduction/blob/cd13c6b17ccb7e1b8fc8b69e76179b339bcc2b32/Zc-specification/Zc.adoc

.. [RISC-V-SMEPMP] PMP Enhancements for memory access and execution prevention on Machine mode, version 1.0, 12/2021,
   https://github.com/riscv/riscv-tee/blob/b20fda89e8e05605ca943af5897c0bb7f4db9841/Smepmp/Smepmp.pdf

.. [RISC-V-CRYPTO] RISC-V Cryptography Extensions Volume I, Scalar & Entropy Source Instructions, Version v1.0.0, 2'nd December, 2021: Ratified,
   https://github.com/riscv/riscv-crypto/releases/download/v1.0.0-scalar/riscv-crypto-spec-scalar-v1.0.0.pdf

.. [OPENHW-OBI] OpenHW Open Bus Interface (OBI) protocol, version 1.5.0,
   https://github.com/openhwgroup/core-v-docs/blob/master/cores/obi/OBI-v1.5.0.pdf

.. [SYMBIOTIC-RVFI] Symbiotic EDA RISC-V Formal Interface
   https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md

Many features in the RISC-V specification are optional, and |corev| can be parameterized to enable or disable some of them.

|corev| supports one of the following base integer instruction sets from [RISC-V-UNPRIV]_.

.. list-table:: |corev| Base Instruction Set
   :header-rows: 1
   :class: no-scrollbar-table

   * - Base Integer Instruction Set
     - Version
     - Configurability

   * - **RV32I**: RV32I Base Integer Instruction Set
     - 2.1
     - optionally enabled based on ``RV32`` parameter

   * - **RV32E**: RV32E Base Integer Instruction Set
     - 1.9 (not ratified yet)
     - optionally enabled based on ``RV32`` parameter

In addition, the following standard instruction set extensions are available from [RISC-V-UNPRIV]_, [RISC-V-ZBA_ZBB_ZBC_ZBS]_, [RISC-V-CRYPTO]_ and [RISC-V-ZCA_ZCB_ZCMP_ZCMT]_.

.. list-table:: |corev| Standard Instruction Set Extensions
   :header-rows: 1
   :class: no-scrollbar-table

   * - Standard Extension
     - Version
     - Configurability

   * - **C**: Standard Extension for Compressed Instructions
     - 2.0
     - always enabled

   * - **M**: Standard Extension for Integer Multiplication and Division
     - 2.0
     - optionally enabled with the ``M_EXT`` parameter

   * - **Zicsr**: Control and Status Register Instructions
     - 2.0
     - always enabled

   * - **Zifencei**: Instruction-Fetch Fence
     - 2.0
     - always enabled

   * - **Zca**: Subset of the standard **Zc** Code-Size Reduction extension consisting of a subset of **C** with the FP load/stores removed.
     - v1.0.0-RC5.6 (not ratified yet; version will change)
     - always enabled

   * - **Zcb**: Subset of the standard **Zc** Code-Size Reduction extension consisting of simple operations.
     - v1.0.0-RC5.6 (not ratified yet; version will change)
     - always enabled

   * - **Zcmp**: Subset of the standard **Zc** Code-Size Reduction extension consisting of push/pop and double move which overlap with **c.fsdsp**.
     - v1.0.0-RC5.6 (not ratified yet; version will change)
     - always enabled

   * - **Zcmt**: Subset of the standard **Zc** Code-Size Reduction extension consisting of table jump.
     - v1.0.0-RC5.6 (not ratified yet; version will change)
     - always enabled

   * - **Zba**: Bit Manipulation Address calculation instructions
     - Version 1.0.0
     - optionally enabled with the ``B_EXT`` parameter

   * - **Zbb**: Bit Manipulation Base instructions
     - Version 1.0.0
     - optionally enabled with the ``B_EXT`` parameter

   * - **Zbc**: Bit Manipulation Carry-Less Multiply instructions
     - Version 1.0.0
     - optionally enabled with the ``B_EXT`` parameter

   * - **Zbs**: Bit Manipulation Bit set, Bit clear, etc. instructions
     - Version 1.0.0
     - optionally enabled with the ``B_EXT`` parameter

   * - **Zkt**: Data Independent Execution Latency
     - Version 1.0.0
     - always enabled

   * - **Zbkc**: Constant time Carry-Less Multiply
     - Version 1.0.0
     - optionally enabled with the ``B_EXT`` parameter

   * - **Zmmul**: Multiplication subset of the **M** extension
     - Version 0.1
     - optionally enabled with the ``M_EXT`` parameter

The following custom instruction set extensions are available.

.. list-table:: |corev| Custom Instruction Set Extensions
   :header-rows: 1
   :class: no-scrollbar-table

   * - Custom Extension
     - Version
     - Configurability

   * - **Xsecure**: Security extensions
     - 1.0
     - always enabled

Most content of the RISC-V privileged specification is optional.
|corev| supports the following features according to the RISC-V Privileged Specification [RISC-V-PRIV]_:

* M-Mode and U-mode
* All CSRs listed in :ref:`cs-registers`
* Hardware Performance Counters as described in :ref:`performance-counters`
* Trap handling supporting direct mode or vectored mode as described at :ref:`exceptions-interrupts`
* Physical Memory Attribution (PMA) as described in :ref:`pma`
* Physical Memory Protection ([RISC-V-SMEPMP]_)
* State enable ([RISC-V-SMSTATEEN]_)

|corev| supports the following ISA extensions from the RISC-V Debug Support specification [RISC-V-DEBUG]_:

* **Sdext**: External Debug support. Always enabled.
* **Sdtrig**: Trigger Module. Optionally enabled with the ``DBG_NUM_TRIGGERS`` parameter.

Synthesis guidelines
--------------------

The |corev| core is fully synthesizable.
It has been designed mainly for ASIC designs, but FPGA synthesis
is supported as well.

All the files in the ``rtl`` and ``rtl/include`` folders are synthesizable. The top level module is called ``cv32e40s_core``.

The user must provide a clock-gating module that instantiates
the clock-gating cells of the target technology. This file must have the same interface and module name of the one provided for simulation-only purposes
at ``bhv/cv32e40s_sim_clock_gate.sv`` (see :ref:`clock-gating-cell`).

The ``constraints/cv32e40s_core.sdc`` file provides an example of synthesis constraints. No synthesis scripts are provided.

ASIC Synthesis
^^^^^^^^^^^^^^

ASIC synthesis is supported for |corev|. The whole design is completely
synchronous and uses positive-edge triggered flip-flops. A technology specific implementation
of a clock gating cell as described in :ref:`clock-gating-cell` needs to
be provided.

FPGA Synthesis
^^^^^^^^^^^^^^^

FPGA synthesis is supported for |corev|. The user needs to provide
a technology specific implementation of a clock gating cell as described
in :ref:`clock-gating-cell`.

Verification
------------

The verification environment (testbenches, testcases, etc.) for the |corev|
core can be found at  `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_.
It is recommended that you start by reviewing the
`CORE-V Verification Strategy <https://core-v-docs-verif-strat.readthedocs.io/en/latest/>`_.

Contents
--------

 * :ref:`getting-started` discusses the requirements and initial steps to start using |corev|.
 * :ref:`core-integration` provides the instantiation template and gives descriptions of the design parameters as well as the input and output ports.
 * :ref:`pipeline-details` described the overal pipeline structure.
 * The instruction and data interfaces of |corev| are explained in :ref:`instruction-fetch` and :ref:`load-store-unit`, respectively.
 * :ref:`xsecure` describes the custom **Xsecure** security features.
 * :ref:`pma` describes the Physical Memory Attribution (PMA) unit.
 * :ref:`pmp` describes the Physical Memory Protection (PMP) unit.
 * The register-file is described in :ref:`register-file`.
 * :ref:`sleep_unit` describes the Sleep unit.
 * The control and status registers are explained in :ref:`cs-registers`.
 * :ref:`performance-counters` gives an overview of the performance monitors and event counters available in |corev|.
 * :ref:`exceptions-interrupts` deals with the infrastructure for handling exceptions and interrupts.
 * :ref:`debug-support` gives a brief overview on the debug infrastructure.
 * :ref:`rvfi` gives a brief overview of the RVFI module.
 * :ref:`glossary` provides definitions of used terminology.

History
-------
|corev| started its life as a fork of the CV32E40P from the OpenHW Group <https://www.openhwgroup.org>.

References
----------

1. `Gautschi, Michael, et al. "Near-Threshold RISC-V Core With DSP Extensions for Scalable IoT Endpoint Devices." in IEEE Transactions on Very Large Scale Integration (VLSI) Systems, vol. 25, no. 10, pp. 2700-2713, Oct. 2017 <https://ieeexplore.ieee.org/document/7864441>`_

2. `Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of ultra-low-power RISC-V cores for Internet-of-Things applications." 27th International Symposium on Power and Timing Modeling, Optimization and Simulation (PATMOS 2017) <https://doi.org/10.1109/PATMOS.2017.8106976>`_

Contributors
------------

| Andreas Traber
  (`*atraber@iis.ee.ethz.ch* <mailto:atraber@iis.ee.ethz.ch>`__)

Michael Gautschi
(`*gautschi@iis.ee.ethz.ch* <mailto:gautschi@iis.ee.ethz.ch>`__)

Pasquale Davide Schiavone
(`*pschiavo@iis.ee.ethz.ch* <mailto:pschiavo@iis.ee.ethz.ch>`__)

Arjan Bink (`*arjan.bink@silabs.com* <mailto:arjan.bink@silabs.com>`__)

Paul Zavalney (`*paul.zavalney@silabs.com* <mailto:paul.zavalney@silabs.com>`__)

| Micrel Lab and Multitherman Lab
| University of Bologna, Italy

| Integrated Systems Lab
| ETH Zürich, Switzerland
