.. _xsecure:

Xsecure extension
=================

.. note::

   The Xsecure features have not been implemented yet.

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
Branches and div/divu/rem/remu instructions are of fixed (data independent) latency. See https://ibex-core.readthedocs.io/en/latest/03_reference/security.html.

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
