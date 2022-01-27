.. _xsecure:

Xsecure extension
=================

.. note::

   Some Xsecure features have not been implemented yet.

|corev| has a custom extension called Xsecure, which encompass the following categories of security related features:

* Anti-tampering features

  * Protection against glitch attacks
  * Control flow integrity
  * Autonomous (hardware-based, low latency) response mechanisms

* Reduction of side channel leakage

.. _security_alerts:

Security alerts
---------------
|corev| has two alert outputs for signaling security issues: A major and a minor alert. The major alert (``alert_major_o``) indicates a critical security issue from which the core cannot recover. The minor alert (``alert_minor_o``) indicates potential security issues, which can be monitored by a system over time.
These outputs can be used by external hardware to trigger security incident responses like for example a system wide reset or a memory erase.
A security output is high for every clock cycle that the related security issue persists.

The following issues result in a major security alert:

* Register file ECC error
* Hardened PC error
* Hardened CSR error
* Interface integrity error

The following issues result in a minor security alert:

* LFSR0, LFSR1, LFSR2 lockup
* Instruction access fault
* Illegal instruction
* Load access fault
* Store/AMO access fault
* Instruction bus fault

Data independent timing
-----------------------
Data independent timing is enabled by setting the ``dataindtiming`` bit in the ``cpuctrl`` CSR.
This will make execution times of all instructions independent of the input data, making it more difficult for an external
observer to extract information by observing power consumption or exploiting timing side-channels.

When ``dataindtiming`` is set, the DIV, DIVU, REM and REMU instructions will have a fixed (data independent) latency and branches
will have a fixed latency as well, regardless of whether they are taken or not. See :ref:`pipeline-details` for details.

Note that the addresses used by loads and stores will still provide a timing side-channel due to the following properties:

* Misaligned loads and stores differ in cycle count from aligned loads and stores.
* Stores to a bufferable address range react differently to wait states than stores to a non-bufferable address range.

Similarly the target address of branches and jumps will still provide a timing side-channel due to the following property:

* Branches and jumps to non-word-aligned non-RV32C instructions differ in cycle count from other branches and jumps.

These timing side-channels can largely be mitigated by imposing (branch target and data) alignment restrictions on the used software.

Dummy instruction insertion
---------------------------

Dummy instructions are inserted at random intervals into the execution pipeline if enabled via the ``rnddummy`` bit in the ``cpuctrl`` CSR.
The dummy instructions have no functional impact on processor state, but add difficult-to-predict timing and power disruptions to the executed code.
This disruption makes it more difficult for an attacker to infer what is being executed, and also makes it more difficult to execute precisely timed fault injection attacks.

The frequency of injected instructions can be tuned via the ``rnddummyfreq`` bits in the ``cpuctrl`` CSR.

.. table:: Intervals for ``rnddummyfreq`` settings
  :name: Intervals for rnddummyfreq settings

  +------------------+----------------------------------------------------------+
  | ``rnddummyfreq`` | Interval                                                 |
  +------------------+----------------------------------------------------------+
  | 0000             | Dummy instruction every 1 - 4 real instructions          |
  +------------------+----------------------------------------------------------+
  | 0001             | Dummy instruction every 1 - 8 real instructions          |
  +------------------+----------------------------------------------------------+
  | 0011             | Dummy instruction every 1 - 16 real instructions         |
  +------------------+----------------------------------------------------------+
  | 0111             | Dummy instruction every 1 - 32 real instructions         |
  +------------------+----------------------------------------------------------+
  | 1111             | Dummy instruction every 1 - 64 real instructions         |
  +------------------+----------------------------------------------------------+

Other ``rnddummyfreq`` values are legal as well, but will have a less predictable performance impact.

The frequency of the dummy instruction insertion is randomized using an LFSR (LFSR0). The dummy instruction itself is also randomized based on LFSR0
and is constrained to ADD, MUL, AND and BLTU opcodes. The source data for the dummy instructions is obtained from LFSRs (LFSR1 and LFSR2) as opposed to sourcing
it from the register file.

The initial seed and output permutation for the LFSRs can be set using the following parameters from the |corev| top-level:

* ``LFSR0_CFG`` for LFSR0.
* ``LFSR1_CFG`` for LFSR1.
* ``LFSR2_CFG`` for LFSR2.

Software can periodically re-seed the LFSRs with true random numbers (if available) via the ``secureseed*`` CSRs, making the insertion interval of
dummy instructions much harder to predict.

.. note::
  The user is recommended to pick maximum length LFSR configurations and must take care that writes to the ``secureseed*`` CSRs will not cause LFSR lockup.
  An LFSR lockup will result in a minor alert and will automatically cause a re-seed of the LFSR with the default seed from the related parameter.

.. note::
  Dummy instructions do affect the cycle count as visible via the ``mcycle`` CSR, but they are not counted as retired instructions (so they do not affect the ``minstret`` CSR).

Register file ECC
-----------------
ECC checking is added to all reads of the register file, where a checksum is stored for each register file word.
All 1-bit and 2-bit errors will be detected. This can be useful to detect fault injection attacks since the register file covers a reasonably large area of |corev|.
No attempt is made to correct detected errors, but a major alert is raised upon a detected error for the system to take action (see :ref:`security_alerts`).

.. note::
  This feature is logically redundant and might get partially or fully optimized away during synthesis.
  Special care might be needed and the final netlist must be checked to ensure that the ECC and correction logic is still present.
  A netlist test for this feature is recommended.

Hardened PC
-----------
Checking is performed to ensure that the PC increments as expected for sequential code. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

.. _hardened-csrs:

Hardened CSRs
-------------
Critical CSRs (``mstatus``, ``mtvec``, ``pmpcfg``, ``pmpaddr*``, ``mseccfg*``, ``cpuctrl``, ``dcsr``, ``mie`` and ``mepc``) have extra glitch detection enabled.
For these registers a second copy of the register is added which stores a complemented version of the main CSR data. A constant check is made that the two copies are consistent, and a major alert is signaled if not (see :ref:`security_alerts`).

.. note::
  The shadow copies are logically redundant and are therefore likely to be optimized away during synthesis.
  Special care in the synthesis script is necessary (see :ref:`register-cells`) and the final netlist must be checked to ensure that the shadow copies are still present.
  A netlist test for this feature is recommended.

Control flow hardening
----------------------
A hardware check is performed to check if branches are taken (or not taken) as they should.

Functional unit and FSM hardening
---------------------------------
(Encode critical signals and FSM state such that certain glitch attacks can be detected)

Bus interface hardening
-----------------------
Hardware checks are performed to check that the bus protocol is not being violated.

Reduction of profiling infrastructure
-------------------------------------
User mode code is prevented from seeing Machine mode statistics by removal of the **Zicount** (Performance Counters) feature.

.. note::

   **Zicount** is used in this User Manual to refer to the counter, timer, and performance counter related functionality described
   in the Counters chapter of the RISC-V unprivileged specification. Unfortunately RISC-V International did not name this extension,
   so for now we introduced our own name to refer to this functionality.
