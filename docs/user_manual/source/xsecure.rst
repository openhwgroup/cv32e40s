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
|corev| has two alert outputs for signaling security issues, a major and a minor alert. The major alert (alert_major_o) indicates a critical security issue from which the core cannot recover. The minor alert (alert_minor_o) indicates potential security issues which can be monitored over time by a system.
These outputs can be used by external hardware to trigger security incident responses like a system wide reset or memory erase.

Data independent timing
-----------------------
Data independent timing is enabled by setting the **dataindtiming** bit in the **cpuctrl** CSR.
This will make execution times of all instructions independent of the input data, making it more difficult for an external
observer to extract data by observing power consumption or exploiting timing side-channels.
When **dataindtiming** is set, div/divu/rem/remu instructions will have a fixed (data independent) latency.
Branches will also have a fixed latency, regardless of the taken/not-taken status.
See :ref:`pipeline-details` for details.

Note that the addresses used by loads and stores will still provide a timing side-channel due to the following properties:

* Misaligned loads and stores differ in cycle count from aligned loads and stores.
* Stores to a bufferable address range react differently to wait states than stores to a non-bufferable address range.

Similarly the target address of branches and jumps will still provide a timing side-channel due to the following property:

* Branches and jumps to non-word-aligned non-RV32C instructions differ in cycle count from other branches and jumps.

These timing side-channels can largely be mitigated by imposing (branch target and data) alignment restrictions on the used software.

Dummy instruction insertion
---------------------------

When enabled (via the ``rnddummy`` control bit in the ``cpuctrl`` register), dummy instructions will be inserted at random intervals into the execution pipeline.
The dummy instructions have no functional impact on processor state but adds some difficult-to-predict timing and power disruption to executed code.
This disruption makes it more difficult for an attacker to infer what is being executed, and also makes it more difficult to execute precisely timed fault injection attacks.

The frequency of injected instructions can be tuned via the ``rnddummyfreq`` bits in the ``cpuctrl`` register.

.. table:: Intervals for rnddummyfreq settings
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

As the ``rnddummyfreq`` is used as a mask on the random top value of a counter, other values are legal, but will have a less predictable impact.

The interval between instruction insertion, and the instruction itself is randomized in the core using an LFSR (lfsr0). The randomization of the instruction word is constrained to valid ADD, MUL, AND and BLTU opcodes.
Register read data for dummy instructions is replaced with random data from lfsr1 and lfsr2 to further increase the noise.

The initial seed and output permutation for the LFSRs can be set using the following parameters from the |corev| top-level;
``LFSR0_CFG``, ``LFSR1_CFG`` and ``LFSR2_CFG`` for the lfsr0, lfsr1 and lfsr2 respectively.
Software can periodically re-seed the LFSRs with true random numbers (if available) via the ``secureseed*`` CSRs.
This will make the insertion interval of dummy instructions much harder for an attacker to predict.

An example of performance impact from inserting dummy instructions is shown in :numref:`Example of Dummy Instruction Performance Impact`
where coremark has been run with the different ``rnddummyfreq`` settings.

.. table:: Example of Dummy Instruction Performance Impact
  :name: Example of Dummy Instruction Performance Impact

  +----------------+------------------+----------+------------------+
  | ``rnddummyen`` | ``rnddummyfreq`` | Interval | Performance Cost |
  +----------------+------------------+----------+------------------+
  | Disabled       | N/A              | N/A      | 0.0%             |
  +----------------+------------------+----------+------------------+
  | Enabled        | 0000             | 1-4      | 28.4%            |
  +----------------+------------------+----------+------------------+
  | Enabled        | 0001             | 1-8      | 15.9%            |
  +----------------+------------------+----------+------------------+
  | Enabled        | 0011             | 1-16     | 8.5%             |
  +----------------+------------------+----------+------------------+
  | Enabled        | 0111             | 1-32     | 4.4%             |
  +----------------+------------------+----------+------------------+
  | Enabled        | 1111             | 1-64     | 2.2%             |
  +----------------+------------------+----------+------------------+



Register file ECC
-----------------
ECC checking is added to all reads of the register file, where a checksum is stored for each register file word.
All 1-bit and 2-bit errors will be detected and this can be useful to detect fault injection attacks since the register file covers a reasonably large area.
No attempt is made to correct detected errors, but an external alert is raised for the system to take action (see :ref:`security_alerts`).

.. note::
  This feature is logically redundant and might get partially or fully optimized away.
  Special care might be needed and the final netlist must be checked to ensure the ECC and correction logic is kept.
  A netlist test for this feature is recommended.

Hardened PC
-----------
Checking is performed to ensure that the PC increments as expected for sequential code. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

Hardened CSRs
-------------
Critical CSRs (``mstatus``, ``mtvec``, ``pmpcfg``, ``pmpaddr*``, ``mseccfg*``, ``cpuctrl``, ``dcsr``, ``mie`` and ``mepc``) have extra glitch detection enabled.
For these registers a second copy of the register is added which stores a complemented version of the main CSR data. A constant check is made that the two copies are consistent, and a major alert is signaled if not (see :ref:`security_alerts`).

.. note::
  The shadow copy is logically redundant and is therefore likely to be optimized away.
  Special care in the synthesis script is necessary and the final netlist must be checked to ensure the shadow are kept.
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
