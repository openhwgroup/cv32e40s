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

Security alerts
---------------
Security alert outputs are provided for major and minor alerts. External hardware can use these alerts to for example trigger a system wide
reset or memory erase. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

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
The dummy instructions have no functional impact on processor state, but add some difficult-to-predict timing and power disruption to executed code.
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
Sofware can periodically re-seed the LFSRs with true random numbers (if available) via the ``secureseed*`` CSRs.
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
A checksum is associated with register file words to detect (not correct) certain errors. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

Hardened PC
-----------
Checking is performed to ensure that the PC increments as expected for sequential code. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

Hardened CSRs
-------------
Shadow registers are added for critical CSRs to detect certain glitch attacks. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

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
