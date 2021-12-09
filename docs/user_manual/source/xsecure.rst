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

Dummy instructions can be randomly inserted without functional impact to disrupt timing and power profiles. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

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
