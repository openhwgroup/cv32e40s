.. _xsecure:

Xsecure extension
=================

|corev| has a custom extension called Xsecure, which encompass the following security related features:

* Security alerts (:ref:`security-alerts`).
* Data independent timing (:ref:`data-independent-timing`).
* Dummy instruction insertion (:ref:`dummy-instruction-insertion`).
* Random instruction for hint (:ref:`random-instruction-for-hint`).
* Register file ECC (:ref:`register-file-ecc`).
* Hardened PC (:ref:`hardened-pc`).
* Hardened CSRs (:ref:`hardened-csrs`).
* Interface integrity (:ref:`interface-integrity`).
* Bus protocol hardening (:ref:`bus-protocol-hardening`).
* Reduction of profiling infrastructure (:ref:`reduction-of-profiling-infrastructure`).

.. _security-alerts:

Security alerts
---------------
|corev| has two alert outputs for signaling security issues: A major and a minor alert. The major alert (``alert_major_o``) indicates a critical security issue from which the core cannot recover. The minor alert (``alert_minor_o``) indicates potential security issues, which can be monitored by a system over time.
These outputs can be used by external hardware to trigger security incident responses like for example a system wide reset or a memory erase.
A security output is high for every clock cycle that the related security issue persists.

The following issues result in a major security alert on ``alert_major_o``:

* Register file ECC error.
* Hardened PC error.
* Hardened CSR error.
* Non-associated instruction interface parity/checksum error.
* Non-associated data interface parity/checksum error.
* Instruction parity/checksum fault (i.e. when triggering the related exception).
* Store parity/checksum fault (i.e. when triggering the related NMI).
* Load parity/checksum fault NMI (i.e. when triggering the related NMI).

The following issues result in a minor security alert on ``alert_minor_o``:

* LFSR0, LFSR1, LFSR2 lockup.
* Instruction access fault (i.e. only when triggering the related exception).
* Illegal instruction fault (i.e. only when triggering the related exception).
* Load access fault (i.e. only when triggering the related exception).
* Store/AMO access fault (i.e. only when triggering the related exception).
* Instruction bus fault (i.e. only when triggering the related exception).
* Store bus fault NMI (i.e. only when triggering the related NMI).
* Load bus fault NMI (i.e. only when triggering the related NMI).

.. _data-independent-timing:

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

.. _dummy-instruction-insertion:

Dummy instruction insertion
---------------------------

Dummy instructions are inserted at random intervals into the execution pipeline if enabled via the ``rnddummy`` bit in the ``cpuctrl`` CSR.
The dummy instructions have no functional impact on the processor state, but add difficult-to-predict timing and power disruptions to the executed code.
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
and is constrained to ``add``, ``mul``, and ``bltu`` instructions. The source data for the dummy instructions is obtained from LFSRs (LFSR1 and LFSR2) as opposed to sourcing
it from the register file.

The initial seed and output permutation for the LFSRs can be set using the following parameters from the |corev| top-level:

* ``LFSR0_CFG`` for LFSR0.
* ``LFSR1_CFG`` for LFSR1.
* ``LFSR2_CFG`` for LFSR2.

These parameters are of the type ``lfsr_cfg_t`` which are described in :numref:`LFSR Configuration Type lfsr_cfg_t`.

.. table:: LFSR Configuration Type lfsr_cfg_t
  :name: LFSR Configuration Type lfsr_cfg_t
  :widths: 15 15 70
  :class: no-scrollbar-table

  +------------------+-------------+---------------------------------------------------------------------------------+
  | **Field**        | **Type**    | **Description**                                                                 |
  +------------------+-------------+---------------------------------------------------------------------------------+
  | coeffs           | logic[31:0] | Coefficient controlling output permutation, must be non-zero                    |
  +------------------+-------------+---------------------------------------------------------------------------------+
  | default_seed     | logic[31:0] | Used as initial seed and for re-seeding in case of lockup, must be non-zero     |
  +------------------+-------------+---------------------------------------------------------------------------------+

Software can periodically re-seed the LFSRs with true random numbers (if available) via the ``secureseed*`` CSRs, making the insertion interval of
dummy instructions much harder to predict.

.. note::
  The user is recommended to pick maximum length LFSR configurations and must take care that writes to the ``secureseed*`` CSRs will not cause LFSR lockup.
  An LFSR lockup will result in a minor alert and will automatically cause a re-seed of the LFSR with the default seed from the related parameter.

.. note::
  Dummy instructions do affect the cycle count as visible via the ``mcycle`` CSR, but they are not counted as retired instructions (so they do not affect the ``minstret`` CSR).

.. _random-instruction-for-hint:

Random instruction for hint
---------------------------

The ``c.slli with rd=x0, nzimm!=0`` RVC custom use hint is replaced by a random instruction if enabled via the ``rndhint`` bit in the ``cpuctrl`` CSR (and will act as a regular ``nop`` otherwise).
The random instruction has no functional impact on the processor state (i.e. it is functionally equivalent to a ``nop``, but it can result in different
cycle count, instruction fetch and power behavior). The random instruction is randomized based on LFSR0 and is constrained to
``add``, ``mul``, and ``bltu`` instructions. The source data for the random instruction is obtained from LFSRs (LFSR1 and LFSR2) as opposed
to sourcing it from the register file.

.. note::
  The ``c.slli with rd=x0, nzimm!=0`` instruction affects the cycle count and retired instruction counts as as visible via the ``mcycle`` CSR and ``minstret`` CSR,
  independent of the value of the ``rndhint`` bit.

.. _register-file-ecc:

Register file ECC
-----------------
ECC checking is added to all reads of the register file, where a checksum is stored for each register file word.
All 1-bit and 2-bit errors will be detected. This can be useful to detect fault injection attacks since the register file covers a reasonably large area of |corev|.
No attempt is made to correct detected errors, but a major alert is raised upon a detected error for the system to take action (see :ref:`security-alerts`).

.. note::
  This feature is logically redundant and might get partially or fully optimized away during synthesis.
  Special care might be needed and the final netlist must be checked to ensure that the ECC and correction logic is still present.
  A netlist test for this feature is recommended.

.. _hardened-pc:

Hardened PC
-----------
PC hardening can be enabled via the ``pcharden`` bit in the ``cpuctrl`` CSR.

If enabled, then during sequential execution the IF stage PC is hardened by checking that it has the correct value compared to the ID stage with an offset determined by the compressed/uncompressed state of the instruction in ID.

In addition, the IF stage PC is then checked for correctness for potential non-sequential execution due to control transfer instructions. For jumps (including mret) and branches, this is done by recomputing the PC target and branch decision (incurring an additional cycle for non-taken branches).

Any error in the check for correct PC or branch/jump decision will result in a pulse on the ``alert_major_o`` pin.

.. _hardened-csrs:

Hardened CSRs
-------------
Critical CSRs (``jvt``, ``mstatus``, ``mtvec``, ``pmpcfg``, ``pmpaddr*``, ``mseccfg*``, ``cpuctrl``, ``dcsr``, ``mie``, ``mepc``,
``mtvt``, ``mscratch``, ``mintstatus``, ``mintthresh``, ``mscratchcsw``, ``mscratchcswl`` and ``mclicbase``)
have extra glitch detection enabled.
For these registers a second copy of the register is added which stores a complemented version of the main CSR data. A constant check is made that the two copies are consistent, and a major alert is signaled if not (see :ref:`security-alerts`).

.. note::
  The shadow copies are logically redundant and are therefore likely to be optimized away during synthesis.
  Special care in the synthesis script is necessary (see :ref:`register-cells`) and the final netlist must be checked to ensure that the shadow copies are still present.
  A netlist test for this feature is recommended.

.. _interface-integrity:

Interface integrity
-------------------

The OBI ([OPENHW-OBI]_) bus interfaces have associated parity and checksum signals:

* |corev| will generate odd parity signals ``instr_reqpar_o`` and ``data_reqpar_o`` for ``instr_req_o`` and ``data_req_o`` respectively (see [OPENHW-OBI]_).
* The environment is expected to drive ``instr_gntpar_i``, ``instr_rvalidpar_i``, ``data_gntpar_i`` and ``data_rvalidpar_i`` with odd parity for ``instr_gnt_i``, ``instr_rvalid_i``, ``data_gnt_i`` and ``data_rvalid_i`` respectively (see [OPENHW-OBI]_).
* |corev| will generate checksums ``instr_achk_o`` and ``data_achk_o`` for the instruction OBI interface and the data OBI interface respectively with checksums as defined in :numref:`Address phase checksum`.
* The environment is expected to drive ``instr_rchk_i`` and ``data_rchk_i`` for the instruction OBI interface and the data OBI interface respectively with checksums as defined in :numref:`Response phase checksum`.

.. table:: Address phase checksum
  :name: Address phase checksum
  :widths: 10 35 55
  :class: no-scrollbar-table

  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | **Signal**   | **Checksum computation**                        | **Comment**                                                                    |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[0]``  | Even parity(``addr[7:0]``)                      |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[1]``  | Even parity(``addr[15:8]``)                     |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[2]``  | Even parity(``addr[23:16]``)                    |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[3]``  | Even parity(``addr[31:24]``)                    |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[4]``  | Odd parity(``prot[2:0]``, ``memtype[1:0]``)     |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[5]``  | Odd parity(``be[3:0]``, ``we``)                 | For the instruction interface ``be[3:0]`` = 4'b1111 and ``we`` = 1'b0 is used. |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[6]``  | Odd parity(``dbg``)                             |                                                                                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[7]``  | Even parity(``atop[5:0]``)                      | ``atop[5:0]`` = 6'b0 as the **A** extension is not implemented.                |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[8]``  | Even parity(``wdata[7:0]``)                     | For the instruction interface ``wdata[7:0]`` = 8'b0.                           |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[9]``  | Even parity(``wdata[15:8]``)                    | For the instruction interface ``wdata[15:8]`` = 8'b0.                          |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[10]`` | Even parity(``wdata[23:16]``)                   | For the instruction interface ``wdata[23:16]`` = 8'b0.                         |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+
  | ``achk[11]`` | Even parity(``wdata[31:24]``)                   | For the instruction interface ``wdata[31:24]`` = 8'b0.                         |
  +--------------+-------------------------------------------------+--------------------------------------------------------------------------------+

.. note::
   |corev| always generates its ``achk[11:8]`` bits dependent on ``wdata`` (even for read transactions). The ``achk[11:8]`` signal bits
   are however not required to be checked against ``wdata`` for read transactions (see [OPENHW-OBI]_). Whether the environment performs these checks or not
   is platform specific.

.. note::
   ``achk[11:8]`` are always valid for ``wdata[31:0]`` (even for sub-word transactions).

.. table:: Response phase checksum
  :name: Response phase checksum
  :widths: 10 35 55
  :class: no-scrollbar-table

  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | **Signal**   | **Checksum computation**                        | **Comment**                                                  |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | ``rchk[0]``  | Even parity(``rdata[7:0]``)                     |                                                              |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | ``rchk[1]``  | Even parity(``rdata[15:8]``)                    |                                                              |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | ``rchk[2]``  | Even parity(``rdata[23:16]``)                   |                                                              |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | ``rchk[3]``  | Even parity(``rdata[31:24]``)                   |                                                              |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+
  | ``rchk[4]``  | Even parity(``err``, ``exokay``)                | ``exokay`` = 1'b0 as the **A** extension is not implemented. |
  +--------------+-------------------------------------------------+--------------------------------------------------------------+

.. note::
   |corev| always allows its ``rchk[3:0]`` bits to be dependent on ``rdata`` (even for write transactions). |corev| however only checks its ``rdata`` signal
   bits against ``rchk[3:0]`` for read transactions (see [OPENHW-OBI]_).

.. note::
   When |corev| checks its ``rdata`` signal bits against ``rchk[3:0]`` it always checks all bits (even for sub-word transactions).

|corev| checks its OBI inputs against the related parity and checksum inputs (i.e. ``instr_gntpar_i``, ``data_gntpar_i``, ``instr_rvalidpar_i``, ``data_rvalidpar_i``, ``instr_rchk_i``
and ``data_rchk_i``) as specified in :numref:`Parity and checksum error detection`. Checksum integrity checking is only performed when both globally (``cpuctrl.integrity`` = 1)
and locally enabled (via PMA, see :ref:`pma_integrity`). Parity integrity checking is always enabled.

.. table:: Parity and checksum error detection
  :name: Parity and checksum error detection
  :widths: 20 20 20 20 20
  :class: no-scrollbar-table

  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | **Parity / Checksum signal** | **Expected value**                | **Check enabled?**        | **Observation interval**   | **Observation interval**  |
  |                              |                                   |                           | **for non-associated**     | **for associated**        |
  |                              |                                   |                           | **interface checking**     | **interface checking**    |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``instr_gntpar_i``           | As defined in [OPENHW-OBI]_       | Always                    | When not in reset          | During instruction access |
  |                              |                                   |                           |                            | address phase             |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``instr_rvalidpar_i``        | As defined in [OPENHW-OBI]_       | Always                    | When not in reset          | During instruction access |
  |                              |                                   |                           |                            | response phase            |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``data_gntpar_i``            | As defined in [OPENHW-OBI]_       | Always                    | When not in reset          | During data access        |
  |                              |                                   |                           |                            | address phase             |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``data_rvalidpar_i``         | As defined in [OPENHW-OBI]_       | Always                    | When not in reset          | During data access        |
  |                              |                                   |                           |                            | response phase            |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``instr_rchk_i``             | As defined in                     | ``cpuctrl.integrity`` = 1 | During instruction access  | During instruction access |
  |                              | :numref:`Response phase checksum` | and PMA attributes access | response phase             | response phase            |
  |                              |                                   | with ``integrity`` = 1    |                            |                           |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+
  | ``data_rchk_i``              | As defined in                     | ``cpuctrl.integrity`` = 1 | During data access         | During data access        |
  |                              | :numref:`Response phase checksum` | and PMA attributes access | response phase             | response phase            |
  |                              |                                   | with ``integrity`` = 1    |                            |                           |
  +------------------------------+-----------------------------------+---------------------------+----------------------------+---------------------------+

Interface checking is performed both associated and non-associated to specific instruction execution.

Non-associated interface checks are performed by only taking into account the bus interfaces themselves plus some state to determine whether checksum checks are enabled for a given transaction. The used observation interval is as wide as
possible (e.g. a data interface related parity error can be detected even if no load or store instruction is actually being executed).
Observed errors will trigger an alert on ``alert_major_o``.

Associated interface checks are the interface checks that can directly be associated to a fetched instruction or bus transaction due to execution of a load or store instruction:

* If a parity/checksum error occurs on the OBI instruction interface while handling an instruction fetch, then a precise exception is triggered (instruction parity fault with exception code 25) if attempting to execute that instruction. This will then also trigger an alert on ``alert_major_o``.
* If a parity/checksum error occurs on the OBI data interface while handling a load, then an imprecise NMI is triggered (load parity/checksum fault NMI with exception code 1026). This will then also trigger an alert on ``alert_major_o``.
* If a parity/checksum error occurs on the OBI data interface while handling a store, then an imprecise NMI is triggered (store parity/checksum fault NMI with exception code 1027). This will then also trigger an alert on ``alert_major_o``.

The environment is expected to check the OBI outputs of |corev| against the related parity and checksum outputs (i.e. ``instr_reqpar_o``, ``data_reqpar_o``, ``instr_rchk_o`` and
``data_rchk_o``) as specified in [OPENHW-OBI]_ and :numref:`Address phase checksum`. It is platform defined how the environment reacts in case of parity or checksum violations.

.. _bus-protocol-hardening:

Bus protocol hardening
----------------------

The OBI protocol (see [OPENHW-OBI]_) is used as the protocol for both the instruction interface and data interface of the |corev|. With respect to its
handshake signals (``req``, ``gnt``, ``rvalid``) the main protocol violation is to receive a response while there is no corresponding outstanding transaction.

An alert is raised on ``alert_major_o`` when ``instr_rvalid_i`` = 1 is received while there are no outstanding OBI instruction transactions.
An alert is raised on ``alert_major_o`` when ``data_rvalid_i`` = 1 is received while there are no outstanding OBI data transactions.

.. _reduction-of-profiling-infrastructure:

Reduction of profiling infrastructure
-------------------------------------
As **Zicntr** and **Zihpm** are not implemented user mode code does not have access to the Base Counters and Timers nor to the
Hardware Performance Counters. Furthermore the machine mode Hardware Performance Counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)``
and related event selector CSRs ``mhpmevent3`` - ``mhpmevent31`` are hard-wired to 0.
