.. _cs-registers:

Control and Status Registers
============================

CSR Map
-------

:numref:`Control and Status Register Map` lists all
implemented CSRs.  To columns in :numref:`Control and Status Register Map` may require additional explanation:

The **Parameter** column identifies those CSRs that are dependent on the value
of specific compile/synthesis parameters. If these parameters are not set as
indicated in :numref:`Control and Status Register Map` then the associated CSR is not implemented.  If the
parameter column is empty then the associated CSR is always implemented.

The **Privilege** column indicates the access mode of a CSR.  The first letter
indicates the lowest privilege level required to access the CSR.  Attempts to
access a CSR with a higher privilege level than the core is currently running
in will throw an illegal instruction exception. The remaining
letters indicate the read and/or write behavior of the CSR when accessed by
the indicated or higher privilge level:

* **RW**: CSR is **read-write**.  That is, CSR instructions (e.g. csrrw) may
  write any value and that value will be returned on a subsequent read (unless
  a side-effect causes the core to change the CSR value).

* **RO**: CSR is **read-only**.  Writes by CSR instructions raise an illegal
  instruction exception.

Writes of a non-supported value to **WLRL** bitfields of a **RW** CSR do not result in an illegal
instruction exception. The exact bitfield access types, e.g. **WLRL** or **WARL**, can be found in the RISC-V
privileged specification.

Reads or writes to a CSR that is not implemented will result in an illegal
instruction exception.

.. table:: Control and Status Register Map
  :name: Control and Status Register Map
  :widths: 12 18 10 27 33
  :class: no-scrollbar-table

  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  |  CSR Address  |   Name            | Privilege | Parameter                |  Description                                            |
  +===============+===================+===========+==========================+=========================================================+
  | Machine CSRs                                                                                                                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x300         | ``mstatus``       | MRW       |                          | Machine Status (lower 32 bits).                         |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x301         | ``misa``          | MRW       |                          | Machine ISA                                             |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x304         | ``mie``           | MRW       |                          | Machine Interrupt Enable Register                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x305         | ``mtvec``         | MRW       |                          | Machine Trap-Handler Base Address                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x307         | ``mtvt``          | MRW       | ``SMCLIC`` = 1           | Machine Trap-Handler Vector Table Base Address          |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x310         | ``mstatush``      | MRW       |                          | Machine Status (upper 32 bits).                         |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x320         | ``mcountinhibit`` | MRW       |                          | (HPM) Machine Counter-Inhibit Register                  |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x323         | ``mhpmevent3``    | MRW       |                          | (HPM) Machine Performance-Monitoring Event Selector 3   |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | .               .                   .           .                                                                                  |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x33F         | ``mhpmevent31``   | MRW       |                          | (HPM) Machine Performance-Monitoring Event Selector 31  |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x340         | ``mscratch``      | MRW       |                          | Machine Scratch                                         |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x341         | ``mepc``          | MRW       |                          | Machine Exception Program Counter                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x342         | ``mcause``        | MRW       |                          | Machine Trap Cause                                      |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x343         | ``mtval``         | MRW       |                          | Machine Trap Value                                      |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x344         | ``mip``           | MRW       |                          | Machine Interrupt Pending Register                      |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x345         | ``mnxti``         | MRW       | ``SMCLIC`` = 1           | Interrupt handler address and enable modifier           |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x347         | ``mintthresh``    | MRW       | ``SMCLIC`` = 1           | Interrupt-level threshold                               |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x348         | ``mscratchcsw``   | MRW       | ``SMCLIC`` = 1           | Conditional scratch swap on priv mode change            |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x349         | ``mscratchcswl``  | MRW       | ``SMCLIC`` = 1           | Conditional scratch swap on level change                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A0         | ``tselect``       | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Select Register                                 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A1         | ``tdata1``        | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Data Register 1                                 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A2         | ``tdata2``        | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Data Register 2                                 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A3         | ``tdata3``        | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Data Register 3                                 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A4         | ``tinfo``         | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Info                                            |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7A5         | ``tcontrol``      | MRW       | ``DBG_NUM_TRIGGERS`` > 0 | Trigger Control                                         |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7B0         | ``dcsr``          | DRW       |                          | Debug Control and Status                                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7B1         | ``dpc``           | DRW       |                          | Debug PC                                                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7B2         | ``dscratch0``     | DRW       |                          | Debug Scratch Register 0                                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x7B3         | ``dscratch1``     | DRW       |                          | Debug Scratch Register 1                                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB00         | ``mcycle``        | MRW       |                          | (HPM) Machine Cycle Counter                             |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB02         | ``minstret``      | MRW       |                          | (HPM) Machine Instructions-Retired Counter              |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB03         | ``mhpmcounter3``  | MRW       |                          | (HPM) Machine Performance-Monitoring Counter 3          |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | .               .                   .           .                                                                                  |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB1F         | ``mhpmcounter31`` | MRW       |                          | (HPM) Machine Performance-Monitoring Counter 31         |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB80         | ``mcycleh``       | MRW       |                          | (HPM) Upper 32 Machine Cycle Counter                    |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB82         | ``minstreth``     | MRW       |                          | (HPM) Upper 32 Machine Instructions-Retired Counter     |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB83         | ``mhpmcounterh3`` | MRW       |                          | (HPM) Upper 32 Machine Performance-Monitoring Counter 3 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | .               .                   .           .                                                                                  |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xB9F         | ``mhpmcounterh31``| MRW       |                          | (HPM) Upper 32 Machine Performance-Monitoring Counter 31|
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF11         | ``mvendorid``     | MRO       |                          | Machine Vendor ID                                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF12         | ``marchid``       | MRO       |                          | Machine Architecture ID                                 |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF13         | ``mimpid``        | MRO       |                          | Machine Implementation ID                               |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF14         | ``mhartid``       | MRO       |                          | Hardware Thread ID                                      |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF15         | ``mconfigptr``    | MRO       |                          | Machine Configuration Pointer                           |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xF46         | ``mintstatus``    | MRO       | ``SMCLIC`` = 1           | Current interrupt levels                                |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+

.. table:: Control and Status Register Map (additional custom CSRs)
  :name: Control and Status Register Map (additional custom CSRs)

  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  |  CSR Address  |   Name            | Privilege | Parameter                |  Description                                            |
  +===============+===================+===========+==========================+=========================================================+
  | Machine CSRs                                                                                                                       |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xBF0         | ``cpuctrl``       | MRW       |                          | CPU control                                             |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xBF9         | ``secureseed0``   | MRW       |                          | Seed for LFSR0                                          |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xBFA         | ``secureseed1``   | MRW       |                          | Seed for LFSR1                                          |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0xBFC         | ``secureseed2``   | MRW       |                          | Seed for LFSR2                                          |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+

.. table:: Control and Status Register Map (Unprivileged and User-Level CSRs)
  :name: Control and Status Register Map (Unprivileged and User-Level CSRs)
  :class: no-scrollbar-table

  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  |  CSR Address  |   Name            | Privilege | Parameter                |  Description                                            |
  +===============+===================+===========+==========================+=========================================================+
  | Unprivileged and User-Level CSRs                                                                                                   |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+
  | 0x017         | ``jvt``           | URW       |                          | Table jump base vector and control register             |
  +---------------+-------------------+-----------+--------------------------+---------------------------------------------------------+

.. only:: ZICNTR

  .. table:: Control and Status Register Map (additional CSRs for Zicntr)
    :name: Control and Status Register Map (additional CSRs for Zicntr)
    :class: no-scrollbar-table

    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    |  CSR Address  |   Name            | Privilege | Parameter           |  Description                                            |
    +===============+===================+===========+=====================+=========================================================+
    | User CSRs                                                                                                                     |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC00         | ``cycle``         | URO       |                     | Cycle Counter                                           |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC02         | ``instret``       | URO       |                     | Instructions-Retired Counter                            |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC80         | ``cycleh``        | URO       |                     | Upper 32 Cycle Counter                                  |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC82         | ``instreth``      | URO       |                     | Upper 32 Instructions-Retired Counter                   |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+

.. only:: ZIHPM

  .. table:: Control and Status Register Map (additional CSRs for Zihpm)
    :name: Control and Status Register Map (additional CSRs for Zihpm)
    :class: no-scrollbar-table

    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    |  CSR Address  |   Name            | Privilege | Parameter           |  Description                                            |
    +===============+===================+===========+=====================+=========================================================+
    | User CSRs                                                                                                                     |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC03         | ``hpmcounter3``   | URO       |                     | (HPM) Performance-Monitoring Counter 3                  |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | .               .                   .           .                     .                                                       |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC1F         | ``hpmcounter31``  | URO       |                     | (HPM) Performance-Monitoring Counter 31                 |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC83         | ``hpmcounterh3``  | URO       |                     | (HPM) Upper 32 Performance-Monitoring Counter 3         |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | .               .                   .           .                     .                                                       |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0xC9F         | ``hpmcounterh31`` | URO       |                     | (HPM) Upper 32 Performance-Monitoring Counter 31        |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+

.. only:: USER

  .. table:: Control and Status Register Map (additional CSRs for User mode support)
    :name: Control and Status Register Map (additional CSRs for User mode support)
    :class: no-scrollbar-table

    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | CSR address       |   Name         | Privilege  | Parameter  |   Description                                      |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | Machine CSRs                                                                                                      |
    +===================+================+============+============+====================================================+
    | 0x306             | ``mcounteren`` | MRW        |            | Machine Counter Enable                             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x30A             | ``menvcfg``    | MRW        |            | Machine Environment Configuration (lower 32 bits)  |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x30C             | ``mstateen0``  | MRW        |            | Machine state enable 0 (lower 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x30D             | ``mstateen1``  | MRW        |            | Machine state enable 1 (lower 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x30E             | ``mstateen2``  | MRW        |            | Machine state enable 2 (lower 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x30F             | ``mstateen3``  | MRW        |            | Machine state enable 3 (lower 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x31A             | ``menvcfgh``   | MRW        |            | Machine Environment Configuration (upper 32 bits)  |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x31C             | ``mstateen0h`` | MRW        |            | Machine state enable 0 (upper 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x31D             | ``mstateen1h`` | MRW        |            | Machine state enable 1 (upper 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x31E             | ``mstateen2h`` | MRW        |            | Machine state enable 2 (upper 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+
    | 0x31F             | ``mstateen3h`` | MRW        |            | Machine state enable 3 (upper 32 bits)             |
    +-------------------+----------------+------------+------------+----------------------------------------------------+

.. only:: PMP

  .. table:: Control and Status Register Map (additional CSRs for PMP)
    :name: Control and Status Register Map (additional CSRs for PMP)
    :class: no-scrollbar-table

    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    |  CSR Address  |   Name            | Privilege | Parameter           |  Description                                            |
    +===============+===================+===========+=====================+=========================================================+
    | Machine CSRs                                                                                                                  |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3A0         | ``pmpcfg0``       | MRW       |                     | Physical memory protection configuration.               |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3A1         | ``pmpcfg1``       | MRW       |                     | Physical memory protection configuration.               |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3A2         | ``pmpcfg2``       | MRW       |                     | Physical memory protection configuration.               |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | ...           | ...               | ...       |                     | ...                                                     |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3AF         | ``pmpcfg15``      | MRW       |                     | Physical memory protection configuration.               |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3B0         | ``pmpaddr0``      | MRW       |                     | Physical memory protection address register.            |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3B1         | ``pmpaddr1``      | MRW       |                     | Physical memory protection address register.            |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3B2         | ``pmpaddr2``      | MRW       |                     | Physical memory protection address register.            |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | ...           | ...               | ...       |                     | ...                                                     |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x3EF         | ``pmpaddr63``     | MRW       |                     | Physical memory protection address register.            |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x747         | ``mseccfg``       | MRW       |                     | Machine Security Configuration (lower 32 bits).         |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x757         | ``mseccfgh``      | MRW       |                     | Machine Security Configuration (upper 32 bits).         |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+

.. only:: FPU

  .. table:: Control and Status Register Map (additional CSRs for F extension)
    :name: Control and Status Register Map (additional CSRs for F extension)
    :class: no-scrollbar-table

    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    |  CSR Address  |   Name            | Privilege | Parameter           |  Description                                            |
    +===============+===================+===========+=====================+=========================================================+
    | User CSRs                                                                                                                     |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x001         | ``fflags``        | URW       | ``FPU`` = 1         | Floating-point accrued exceptions.                      |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x002         | ``frm``           | URW       | ``FPU`` = 1         | Floating-point dynamic rounding mode.                   |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+
    | 0x003         | ``fcsr``          | URW       | ``FPU`` = 1         | Floating-point control and status register.             |
    +---------------+-------------------+-----------+---------------------+---------------------------------------------------------+

CSR Descriptions
-----------------

What follows is a detailed definition of each of the CSRs listed above. The
**R/W** column defines the access mode behavior of each bit field when
accessed by the privilege level specified in :numref:`Control and Status Register Map` (or a higher privilege
level):

* **R**: **read** fields are not affected by CSR write instructions.  Such
  fields either return a fixed value, or a value determined by the operation of
  the core.

* **RW**: **read/write** fields store the value written by CSR writes. Subsequent
  reads return either the previously written value or a value determined by the
  operation of the core.

* **WARL**: **write-any-read-legal** fields store only legal values written by CSR writes.
  The WARL keyword can optionally be followed by a legal value (or comma separated list of legal values) enclosed in brackets.
  If the legal value(s) are not specified, then all possible values are considered valid.
  For example, a WARL (0x0) field supports only the value 0x0. Any value may be written, but
  all reads would return 0x0 regardless of the value being written to it. A WARL field may
  support more than one value. If an unsupported value is (attempted to be) written to a WARL
  field, the value marked with an asterix (the so-called resolution value) is written. If there
  is no such predefined resolution value, then the original (legal) value of the bitfield is
  preserved.

* **WPRI**: Software should ignore values read from these fields, and preserve the values when writing.

.. note::

   The **R/W** information does **not** impact whether CSR accesses result in illegal instruction exceptions or not.

.. only:: FPU

  .. _csr-fflags:

  Floating-point accrued exceptions (``fflags``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x001 (only present if ``FPU`` = 1)

  Reset Value: 0x0000_0000

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------------+-----------+-------------------------------------------------------------------------+
    |   Bit #     |   R/W     |   Description                                                           |
    +=============+===========+=========================================================================+
    | 31:5        | R (0x0)   | Hardwired to 0.                                                         |
    +-------------+-----------+-------------------------------------------------------------------------+
    | 4           | RW        | NV- Invalid Operation                                                   |
    +-------------+-----------+-------------------------------------------------------------------------+
    | 3           | RW        | DZ - Divide by Zero                                                     |
    +-------------+-----------+-------------------------------------------------------------------------+
    | 2           | RW        | OF - Overflow                                                           |
    +-------------+-----------+-------------------------------------------------------------------------+
    | 1           | RW        | UF - Underflow                                                          |
    +-------------+-----------+-------------------------------------------------------------------------+
    | 0           | RW        | NX - Inexact                                                            |
    +-------------+-----------+-------------------------------------------------------------------------+

  .. Comment: I have not tested any CSRs that require FPU=1.  The Mode spec on all of these is suspect.
  .. _csr-frm:

  Floating-point dynamic rounding mode (``frm``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x002 (only present if ``FPU`` = 1)

  Reset Value: 0x0000_0000

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------------+-----------+------------------------------------------------------------------------+
    |   Bit #     |  R/W      |   Description                                                          |
    +=============+===========+========================================================================+
    | 31:3        | R (0x0)   | Hardwired to 0.                                                        |
    +-------------+-----------+------------------------------------------------------------------------+
    | 2:0         | RW        | Rounding mode. 000 = RNE, 001 = RTZ, 010 = RDN, 011 = RUP, 100 = RMM   |
    |             |           | 101 = Invalid, 110 = Invalid, 111 = DYN.                               |
    +-------------+-----------+------------------------------------------------------------------------+

  .. _csr-fcsr:

  Floating-point control and status register (``fcsr``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x003 (only present if ``FPU`` = 1)

  Reset Value: 0x0000_0000

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------------+-----------+------------------------------------------------------------------------+
    |   Bit #     |  R/W      |   Description                                                          |
    +=============+===========+========================================================================+
    | 31:8        | R (0x0)   | Hardwired to 0.                                                        |
    +-------------+-----------+------------------------------------------------------------------------+
    | 7:5         | RW        | Rounding Mode (``frm``)                                                |
    +-------------+-----------+------------------------------------------------------------------------+
    | 4:0         | RW        | Accrued Exceptions (``fflags``)                                        |
    +-------------+-----------+------------------------------------------------------------------------+

.. _csr-jvt:

Jump Vector Table (``jvt``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x017

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +----------+------------+-----------------------------------------------------------------------------------------------+
  |   Bit #  | R/W        |           Description                                                                         |
  +==========+============+===============================================================================================+
  | 31:10    | WARL       | **BASE[31:10]**: Table Jump Base Address, 1024 byte aligned.                                  |
  +----------+------------+-----------------------------------------------------------------------------------------------+
  |  9:6     | WARL (0x0) | **BASE[9:6]**: Table Jump Base Address, 1024 byte aligned. ``jvt[9:6]`` is hardwired to 0x0.  |
  +----------+------------+-----------------------------------------------------------------------------------------------+
  |  5:0     | WARL (0x0) | **MODE**: Jump table mode                                                                     |
  +----------+------------+-----------------------------------------------------------------------------------------------+

Table jump base vector and control register

.. note::
   Memory writes to the ``jvt`` based vector table require an instruction barrier (``fence.i``) to guarantee that they are visible to the instruction fetch (see :ref:`fencei` and [RISC-V-UNPRIV]_).

.. _csr-mstatus:

Machine Status (``mstatus``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x300

Reset Value: 0x0000_1800

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W           |   Description                                                                                                                                                                                                                                                 |
  +=============+=================+===============================================================================================================================================================================================================================================================+
  | 31          | WARL (0x0)      | **SD**. Hardwired to 0.                                                                                                                                                                                                                                       |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 30:23       | WPRI (0x0)      | Reserved. Hardwired to 0.                                                                                                                                                                                                                                     |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 22          | WARL (0x0)      | **TSR**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 21          | WARL            | **TW**: Timeout Wait. When set, WFI executed from user mode causes an illegal exception. The time limit is set to 0 for CV32E40S.                                                                                                                             |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 20          | WARL (0x0)      | **TVM**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 19          | R (0x0)         | **MXR**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 18          | R (0x0)         | **SUM**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 17          | RW              | **MPRV**: Modify Privilege. When MPRV=1, load and store memory addresses are translated and protected as though the current privilege mode were set to MPP.                                                                                                   |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 16:15       | R (0x0)         | **XS**. Hardwired to 0.                                                                                                                                                                                                                                       |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 14:13       | WARL (0x0)      | **FS**. Hardwired to 0.                                                                                                                                                                                                                                       |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 12:11       | WARL (0x0, 0x3) | **MPP**: Machine Previous Priviledge mode. Returns the previous privilege mode. When an mret is executed, the privilege mode is change to the value of MPP.                                                                                                   |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 10:9        | WPRI (0x0)      | **VS**. Hardwired to 0.                                                                                                                                                                                                                                       |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 8           | WARL (0x0)      | **SPP**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 7           | RW              | **MPIE**. When an exception is encountered, MPIE will be set to MIE. When the ``mret`` instruction is executed, the value of MPIE will be stored to MIE.                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 6           | WARL (0x0)      | **UBE**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 5           | R (0x0)         | **SPIE**. Hardwired to 0.                                                                                                                                                                                                                                     |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 4           | WPRI (0x0)      | Reserved. Hardwired to 0.                                                                                                                                                                                                                                     |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 3           | RW              | **MIE**: If you want to enable interrupt handling in your exception handler, set the Interrupt Enable MIE to 1 inside your handler code.                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 2           | WPRI (0x0)      | Reserved. Hardwired to 0.                                                                                                                                                                                                                                     |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 1           | R (0x0)         | **SIE**. Hardwired to 0.                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
  | 0           | WPRI (0x0)      | Reserved. Hardwired to 0                                                                                                                                                                                                                                      |
  +-------------+-----------------+---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+

.. _csr-misa:

Machine ISA (``misa``)
~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x301

Reset Value: defined (based on ``RV32``, ``M_EXT``)

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+------------------------------------------------------------------------+
  |   Bit #     |   R/W      |   Description                                                          |
  +=============+============+========================================================================+
  | 31:30       | WARL (0x1) |  **MXL** (Machine XLEN).                                               |
  +-------------+------------+------------------------------------------------------------------------+
  | 29:26       | WARL (0x0) | (Reserved).                                                            |
  +-------------+------------+------------------------------------------------------------------------+
  | 25          | WARL (0x0) | **Z** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 24          | WARL (0x0) | **Y** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 23          | WARL (0x1) | **X** (Non-standard extensions present).                               |
  +-------------+------------+------------------------------------------------------------------------+
  | 22          | WARL (0x0) | **W** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 21          | WARL (0x0) | **V** (Tentatively reserved for Vector extension).                     |
  +-------------+------------+------------------------------------------------------------------------+
  | 20          | WARL (0x1) | **U** (User mode implemented).                                         |
  +-------------+------------+------------------------------------------------------------------------+
  | 19          | WARL (0x0) | **T** (Tentatively reserved for Transactional Memory extension).       |
  +-------------+------------+------------------------------------------------------------------------+
  | 18          | WARL (0x0) | **S** (Supervisor mode implemented).                                   |
  +-------------+------------+------------------------------------------------------------------------+
  | 17          | WARL (0x0) | **R** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 16          | WARL (0x0) | **Q** (Quad-precision floating-point extension).                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 15          | WARL (0x0) | **P** (Packed-SIMD extension).                                         |
  +-------------+------------+------------------------------------------------------------------------+
  | 14          | WARL (0x0) | **O** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 13          | WARL (0x0) | **N**                                                                  |
  +-------------+------------+------------------------------------------------------------------------+
  | 12          | WARL       | **M** (Integer Multiply/Divide extension).                             |
  +-------------+------------+------------------------------------------------------------------------+
  | 11          | WARL (0x0) | **L** (Tentatively reserved for Decimal Floating-Point extension).     |
  +-------------+------------+------------------------------------------------------------------------+
  | 10          | WARL (0x0) | **K** (Reserved).                                                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 9           | WARL (0x0) | **J** (Tentatively reserved for Dynamically Translated Languages       |
  |             |            | extension).                                                            |
  +-------------+------------+------------------------------------------------------------------------+
  | 8           | WARL       | **I** (RV32I/64I/128I base ISA).                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 7           | WARL (0x0) | **H** (Hypervisor extension).                                          |
  +-------------+------------+------------------------------------------------------------------------+
  | 6           | WARL (0x0) | **G** (Additional standard extensions present).                        |
  +-------------+------------+------------------------------------------------------------------------+
  | 5           | WARL (0x0) | **F** (Single-precision floating-point extension).                     |
  +-------------+------------+------------------------------------------------------------------------+
  | 4           | WARL       | **E** (RV32E base ISA).                                                |
  +-------------+------------+------------------------------------------------------------------------+
  | 3           | WARL (0x0) | **D** (Double-precision floating-point extension).                     |
  +-------------+------------+------------------------------------------------------------------------+
  | 2           | WARL (0x1) | **C** (Compressed extension).                                          |
  +-------------+------------+------------------------------------------------------------------------+
  | 1           | WARL (0x0) | **B** Reserved.                                                        |
  +-------------+------------+------------------------------------------------------------------------+
  | 0           | WARL (0x0) | **A** (Atomic extension).                                              |
  +-------------+------------+------------------------------------------------------------------------+

All bitfields in the ``misa`` CSR read as 0 except for the following:

* **C** = 1
* **I** = 1 if ``RV32`` == RV32I
* **E** = 1 if ``RV32`` == RV32E
* **M** = 1 if ``M_EXT`` == M
* **MXL** = 1 (i.e. XLEN = 32)
* **U** = 1
* **X** = 1

Machine Interrupt Enable Register (``mie``) - ``SMCLIC`` == 0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x304

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                            |
  +=============+===========+==========================================================================================+
  | 31:16       | RW        | Machine Fast Interrupt Enables: Set bit x to enable interrupt irq_i[x].                  |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 15:12       | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 11          | RW        | **MEIE**: Machine External Interrupt Enable, if set, irq_i[11] is enabled.               |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 10          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  9          | WARL (0x0)| **SEIE**. Hardwired to 0                                                                 |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  8          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  7          | RW        | **MTIE**: Machine Timer Interrupt Enable, if set, irq_i[7] is enabled.                   |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  6          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  5          | WARL (0x0)| **STIE**. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  4          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  3          | RW        | **MSIE**: Machine Software Interrupt Enable, if set, irq_i[3] is enabled.                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  2          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  1          | WARL (0x0)| **SSIE**. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  0          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+

Machine Interrupt Enable Register (``mie``) - ``SMCLIC`` == 1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x304

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                            |
  +=============+===========+==========================================================================================+
  | 31:0        | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+

.. note::
   In CLIC mode the ``mie`` CSR is replaced by separate memory-mapped interrupt enables (``clicintie``).

.. _csr-mtvec:

Machine Trap-Vector Base Address (``mtvec``) - ``SMCLIC`` == 0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x305

Reset Value: Defined

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  |   Bit # | R/W              |   Description                                                                                                 |
  +=========+==================+===============================================================================================================+
  | 31:7    | WARL             | **BASE[31:7]**: Trap-handler base address, always aligned to 128 bytes.                                       |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  | 6:2     | WARL (0x0)       | **BASE[6:2]**: Trap-handler base address, always aligned to 128 bytes. ``mtvec[6:2]`` is hardwired to 0x0.    |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  | 1:0     | WARL (0x0, 0x1)  | **MODE**: Interrupt handling mode. 0x0 = non-vectored CLINT mode, 0x1 = vectored CLINT mode.                  |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+

The initial value of ``mtvec`` is equal to {**mtvec_addr_i[31:7]**, 5'b0, 2'b01}.

When an exception or an interrupt is encountered, the core jumps to the corresponding
handler using the content of the ``mtvec[31:7]`` as base address. Both non-vectored CLINT mode and vectored CLINT mode
are supported.

Upon an NMI in non-vectored CLINT mode the core jumps to **mtvec[31:7]**, 5'h0, 2'b00} (i.e. index 0).
Upon an NMI in vectored CLINT mode the core jumps to **mtvec[31:7]**, 5'hF, 2'b00} (i.e. index 15).

.. note::
   For NMIs the exception codes in the ``mcause`` CSR do not match the table index as for regular interrupts.

.. note::
   Memory writes to the ``mtvec`` based vector table require an instruction barrier (``fence.i``) to guarantee that they are visible to the instruction fetch (see :ref:`fencei` and [RISC-V-UNPRIV]_).

.. _csr-mtvec-smclic:

Machine Trap-Vector Base Address (``mtvec``) - ``SMCLIC`` == 1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x305

Reset Value: Defined

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  |   Bit # | R/W              |   Description                                                                                                 |
  +=========+==================+===============================================================================================================+
  | 31:7    | WARL             | **BASE[31:7]**: Trap-handler base address, always aligned to 128 bytes.                                       |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  | 6       | WARL (0x0)       | **BASE[6]**: Trap-handler base address, always aligned to 128 bytes. ``mtvec[6]`` is hardwired to 0x0.        |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  | 5:2     | WARL (0x0)       | **SUBMODE**: Sub mode. Reserved for future use.                                                               |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+
  | 1:0     | WARL (0x3)       | **MODE**: Interrupt handling mode. Always CLIC mode.                                                          |
  +---------+------------------+---------------------------------------------------------------------------------------------------------------+

The initial value of ``mtvec`` is equal to {**mtvec_addr_i[31:7]**, 1'b0, 6'b000011}.

Upon an NMI in CLIC mode the core jumps to **mtvec[31:7]**, 5'h0, 2'b00} (i.e. index 0).

.. note::
   Memory writes to the ``mtvec`` based vector table require an instruction barrier (``fence.i``) to guarantee that they are visible to the instruction fetch (see :ref:`fencei` and [RISC-V-UNPRIV]_).

.. _csr-mtvt:

Machine Trap Vector Table Base Address (``mtvt``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x307

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-----------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                 |
  +=============+============+=======================================================================+
  | 31:N        | RW         | **BASE[31:N]**: Trap-handler vector table base address.               |
  |             |            | N = maximum(6, 2+SMCLIC_ID_WIDTH).                                    |
  |             |            | See note below for alignment restrictions.                            |
  +-------------+------------+-----------------------------------------------------------------------+
  | N-1:6       | WARL (0x0) | **BASE[N-1:6]**: Trap-handler vector table base address.              |
  |             |            | This field is only defined if N > 6.                                  |
  |             |            | N = maximum(6, 2+SMCLIC_ID_WIDTH).                                    |
  |             |            | ``mtvt[N-1:6]`` is hardwired to 0x0.                                  |
  |             |            | See note below for  alignment restrictions.                           |
  +-------------+------------+-----------------------------------------------------------------------+
  | 5:0         | R (0x0)    | Reserved. Hardwired to 0.                                             |
  +-------------+------------+-----------------------------------------------------------------------+

.. note::
   The ``mtvt`` CSR holds the base address of the trap vector table, which has its alignment restricted to both at least 64-bytes and to
   ``2^(2+SMCLIC_ID_WIDTH)`` bytes or greater power-of-two boundary. For example if ``SMCLIC_ID_WIDTH`` = 8, then 256 CLIC interrupts are supported and the trap vector table
   is aligned to 1024 bytes, and therefore **BASE[9:6]** will be WARL (0x0).

.. note::
   Memory writes to the ``mtvt`` based vector table require an instruction barrier (``fence.i``) to guarantee that they are visible to the instruction fetch (see :ref:`fencei` and [RISC-V-UNPRIV]_).

Machine Status (``mstatush``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x310

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +------+--------------+-------------------------------------------------+
  | Bit# |  R/W         | Definition                                      |
  +======+==============+=================================================+
  | 31:6 | WPRI  (0x0)  | Reserved. Hardwired to 0.                       |
  +------+--------------+-------------------------------------------------+
  | 5    | WARL (0x0)   | **MBE**. Hardwired to 0.                        |
  +------+--------------+-------------------------------------------------+
  | 4    | WARL (0x0)   | **SBE**. Hardwired to 0.                        |
  +------+--------------+-------------------------------------------------+
  | 3:0  | WPRI (0x0)   | Reserved. Hardwired to 0.                       |
  +------+--------------+-------------------------------------------------+

.. only:: USER

  Machine Counter Enable (``mcounteren``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x306

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  .. note::
     ``mcounteren`` is WARL (0x0) as the Zicntr and Zihpm extensions are not supported on |corev|.

  Machine Environment Configuration (``menvcfg``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x30A

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +------+-------------+---------------------------------------------------------------+
    | Bit# |  R/W        | Definition                                                    |
    +======+=============+===============================================================+
    | 31:8 | WPRI (0x0)  | Reserved. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+
    | 7    | R (0x0)     | **CBZE**. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+
    | 6    | R (0x0)     | **CBCFE**. Hardwired to 0.                                    |
    +------+-------------+---------------------------------------------------------------+
    | 5:4  | R (0x0)     | **CBIE**. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+
    | 3:1  | R (0x0)     | Reserved. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+
    | 0    | R (0x0)     | **FIOM**. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+

  Machine State Enable 0 (``mstateen0``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x30C

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:3  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+
    | 2     | RW         | Controls user mode access to the ``jvt`` CSR and whether the     |
    |       |            | ``cm.jt`` and ``cm.jalt`` instructions cause an illegal          |
    |       |            | instruction trap in user mode or not.                            |
    +-------+------------+------------------------------------------------------------------+
    | 1:0   | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 1 (``mstateen1``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x30D

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 2 (``mstateen2``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x30E

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 3 (``mstateen3``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x30F

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine Environment Configuration (``menvcfgh``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x31A

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +------+-------------+---------------------------------------------------------------+
    | Bit# |  R/W        | Definition                                                    |
    +======+=============+===============================================================+
    | 31   | R (0x0)     | **STCE**. Hardwired to 0                                      |
    +------+-------------+---------------------------------------------------------------+
    | 30:0 | WPRI (0x0)  | Reserved. Hardwired to 0.                                     |
    +------+-------------+---------------------------------------------------------------+

  Machine State Enable 0 (``mstateen0h``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x31C

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 1 (``mstateen1h``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x31D

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 2 (``mstateen2h``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x31E

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

  Machine State Enable 3 (``mstateen3h``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x31F

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------+------------------------------------------------------------------+
    | Bit#  | R/W        | Description                                                      |
    +=======+============+==================================================================+
    | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
    +-------+------------+------------------------------------------------------------------+

Machine Counter-Inhibit Register (``mcountinhibit``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x320

Reset Value: 0x0000_0005

The performance counter inhibit control register. The default value is to inihibit all implemented counters out of reset.
The bit returns a read value of 0 for non implemented counters.

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-------------+------------------------------------------------------------------+
  | Bit#  | R/W         | Description                                                      |
  +=======+=============+==================================================================+
  | 31:3  | WARL (0x0)  | Hardwired to 0.                                                  |
  +-------+-------------+------------------------------------------------------------------+
  | 2     | WARL        | **IR**: ``minstret`` inhibit                                     |
  +-------+-------------+------------------------------------------------------------------+
  | 1     | WARL (0x0)  | Hardwired to 0.                                                  |
  +-------+-------------+------------------------------------------------------------------+
  | 0     | WARL        | **CY**: ``mcycle`` inhibit                                       |
  +-------+-------------+------------------------------------------------------------------+

Machine Performance Monitoring Event Selector (``mhpmevent3 .. mhpmevent31``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x323 - 0x33F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-------------+---------------------------------------------------------------+
  | Bit#  |  R/W        | Definition                                                    |
  +=======+=============+===============================================================+
  | 31:0  | WARL (0x0)  | Hardwired to 0.                                               |
  +-------+-------------+---------------------------------------------------------------+

Machine Scratch (``mscratch``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x340

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | RW        | Scratch value                                                          |
  +-------------+-----------+------------------------------------------------------------------------+

Machine Exception PC (``mepc``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x341

Reset Value: 0x0000_0000

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+------------------------------------------------------------------------+
  |   Bit #     |   R/W      |   Description                                                          |
  +=============+============+========================================================================+
  | 31:1        | WARL       | Machine Expection Program Counter 31:1                                 |
  +-------------+------------+------------------------------------------------------------------------+
  |    0        | WARL (0x0) | Hardwired to 0.                                                        |
  +-------------+------------+------------------------------------------------------------------------+

When an exception is encountered, the current program counter is saved
in MEPC, and the core jumps to the exception address. When a mret
instruction is executed, the value from MEPC replaces the current
program counter.

Machine Cause (``mcause``) - ``SMCLIC`` == 0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x342

Reset Value: 0x0000_0000

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+----------------------------------------------------------------------------------+
  |   Bit #     |   R/W      |   Description                                                                    |
  +=============+============+==================================================================================+
  | 31          | RW         | **INTERRUPT**. This bit is set when the exception was triggered by an interrupt. |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 30:11       | WLRL (0x0) | **EXCCODE[30:11]**. Hardwired to 0.                                              |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 10:0        | WLRL       | **EXCCODE[10:0]**. See note below.                                               |
  +-------------+------------+----------------------------------------------------------------------------------+

.. note::

   Software accesses to `mcause[10:0]` must be sensitive to the WLRL field specification of this CSR.  For example,
   when `mcause[31]` is set, writing 0x1 to `mcause[1]` (Supervisor software interrupt) will result in UNDEFINED behavior.

Machine Cause (``mcause``) - ``SMCLIC`` == 1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x342

Reset Value: 0x3000_0000

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+----------------------------------------------------------------------------------+
  |   Bit #     |   R/W      |   Description                                                                    |
  +=============+============+==================================================================================+
  | 31          | RW         | **INTERRUPT**. This bit is set when the exception was triggered by an interrupt. |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 30          | RW         | **MINHV**. Set by hardware at start of hardware vectoring, cleared by            |
  |             |            | hardware at end of successful hardware vectoring.                                |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 29:28       | WARL (0x0, | **MPP**: Previous privilege mode. Same as ``mstatus.MPP``                        |
  |             |       0x3) |                                                                                  |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 27          | RW         | **MPIE**: Previous interrupt enable. Same as ``mstatus.MPIE``                    |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 26:24       | RW         | Reserved. Hardwired to 0.                                                        |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 23:16       | RW         | **MPIL**: Previous interrupt level.                                              |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 15:12       | WARL (0x0) | Reserved. Hardwired to 0.                                                        |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 11          | WLRL (0x0) | **EXCCODE[11]**                                                                  |
  +-------------+------------+----------------------------------------------------------------------------------+
  | 10:0        | WLRL       | **EXCCODE[10:0]**                                                                |
  +-------------+------------+----------------------------------------------------------------------------------+

.. note::

   ``mcause.MPP`` and ``mstatus.MPP`` mirror each other. ``mcause.MPIE`` and ``mstatus.MPIE`` mirror each other. Reading or writing the
   fields ``MPP``/``MPIE`` in ``mcause`` is equivalent to reading or writing the homonymous field in ``mstatus``.

Machine Trap Value (``mtval``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x343

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+------------------------------------------------------------------------+
  |   Bit #     |   R/W      |   Description                                                          |
  +=============+============+========================================================================+
  | 31:0        | WARL (0x0) | Hardwired to 0.                                                        |
  +-------------+------------+------------------------------------------------------------------------+

Machine Interrupt Pending Register (``mip``) - ``SMCLIC`` == 0
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x344

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                            |
  +=============+===========+==========================================================================================+
  | 31:16       | R         | Machine Fast Interrupt Enables: Interrupt irq_i[x] is pending.                           |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 15:12       | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 11          | R         | **MEIP**: Machine External Interrupt Enable, if set, irq_i[11] is pending.               |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 10          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  9          | WARL (0x0)| **SEIP**. Hardwired to 0                                                                 |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  8          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  7          | R         | **MTIP**: Machine Timer Interrupt Enable, if set, irq_i[7] is pending.                   |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  6          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  5          | WARL (0x0)| **STIP**. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  4          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  3          | R         | **MSIP**: Machine Software Interrupt Enable, if set, irq_i[3] is pending.                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  2          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  1          | WARL (0x0)| **SSIP**. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  |  0          | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+

Machine Interrupt Pending Register (``mip``) - ``SMCLIC`` == 1
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x344

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                            |
  +=============+===========+==========================================================================================+
  | 31:0        | WARL (0x0)| Reserved. Hardwired to 0.                                                                |
  +-------------+-----------+------------------------------------------------------------------------------------------+

.. note::
   In CLIC mode the ``mip`` CSR is replaced by separate memory-mapped interrupt enables (``clicintip``).

.. _csr-mnxti:

Machine Next Interrupt Handler Address and Interrupt Enable (``mnxti``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x345

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-------------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                   |
  +=============+============+=========================================================================+
  | 31:0        |   RW       | **MNXTI**: Machine Next Interrupt Handler Address and Interrupt Enable. |
  +-------------+------------+-------------------------------------------------------------------------+

This register can be used by the software to service the next interrupt when it is in the same privilege mode,
without incurring the full cost of an interrupt pipeline flush and context save/restore.

.. note::
  The ``mnxti`` CSR is only designed to be used with the CSRR (CSRRS rd,csr,x0), CSRRSI, and CSRRCI instructions.
  Accessing the ``mnxti`` CSR using any other CSR instruction form is reserved and |corev| will treat such instruction as illegal instructions.
  In addition, use of ``mnxti`` with CSRRSI with non-zero uimm values for bits 0, 2, and 4 are reserved for future use and will also be treated as illegal instructions.

.. _csr-mintthresh:

Machine Interrupt-Level Threshold (``mintthresh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x347

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-------------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                   |
  +=============+============+=========================================================================+
  | 31:8        |   R (0x0)  | Reserved. Hardwired to 0.                                               |
  +-------------+------------+-------------------------------------------------------------------------+
  |  7:0        |   WARL     | **TH**: Threshold                                                       |
  +-------------+------------+-------------------------------------------------------------------------+

This register holds the machine mode interrupt level threshold.

.. note::
  The ``SMCLIC_INTTHRESHBITS`` parameter specifies the number of bits actually implemented in the ``mintthresh.th`` field.
  The implemented bits are kept left justified in the most-significant bits of the 8-bit field, with the lower unimplemented
  bits treated as hardwired to 1.

.. _csr-mscratchcsw:

Machine Scratch Swap for Priv Mode Change (``mscratchcsw``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x348

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-------------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                   |
  +=============+============+=========================================================================+
  | 31:0        |   RW       | **MSCRATCHCSW**: Machine scratch swap for privilege mode change         |
  +-------------+------------+-------------------------------------------------------------------------+

Scratch swap register for multiple privilege modes.

.. note::
  Only the read-modify-write (swap/CSRRW) operation is useful for ``mscratchcsw``.
  The behavior of the non-CSRRW variants (i.e. CSRRS/C, CSRRWI, CSRRS/CI) and CSRRW variants with **rd** = **x0** or **rs1** = **x0** on ``mscratchcsw`` are implementation-defined.
  |corev| will treat such instructions as illegal instructions.

.. _csr-mscratchcswl:

Machine Scratch Swap for Interrupt-Level Change (``mscratchcswl``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x349

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-------------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                   |
  +=============+============+=========================================================================+
  | 31:0        |   RW       | **MSCRATCHCSWL**: Machine Scratch Swap for Interrupt-Level Change       |
  +-------------+------------+-------------------------------------------------------------------------+

Scratch swap register for multiple interrupt levels.

.. note::
  Only the read-modify-write (swap/CSRRW) operation is useful for ``mscratchcswl``.
  The behavior of the non-CSRRW variants (i.e. CSRRS/C, CSRRWI, CSRRS/CI) and CSRRW variants with **rd** = **x0** or **rs1** = **x0** on ``mscratchcswl`` are implementation-defined.
  |corev| will treat such instructions as illegal instructions.

.. _csr-tselect:

Trigger Select Register (``tselect``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A0

Reset Value: 0x0000_0000

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------------------------------+----------------------------------------------------------------------------------------+
  |   Bit #     |   R/W                              |   Description                                                                          |
  +=============+====================================+========================================================================================+
  | 31:0        | WARL                               | |corev| implements 0 to ``DBG_NUM_TRIGGERS`` triggers. Selects                         |
  |             | (0x0 - (``DBG_NUM_TRIGGERS``-1))   | which trigger CSRs are accessed through the tdata* CSRs.                               |
  +-------------+------------------------------------+----------------------------------------------------------------------------------------+

.. _csr-tdata1:

Trigger Data 1 (``tdata1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1

Reset Value: 0x2800_1000

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-----------------+----------------------------------------------------------------+
  | Bit#  | R/W             | Description                                                    |
  +=======+=================+================================================================+
  | 31:28 | WARL (0x2, 0x5, | **TYPE**. 0x2 (``mcontrol``), 0x5 (``etrigger``),              |
  |       | 0x6, 0xF)       | 0x6 (``mcontrol6``), 0xF (``disabled``).                       |
  +-------+-----------------+----------------------------------------------------------------+
  | 27    | WARL (0x1)      | **DMODE**. Only debug mode can write ``tdata`` registers.      |
  +-------+-----------------+----------------------------------------------------------------+
  | 26:0  | WARL            | **DATA**. Trigger data depending on type                       |
  +-------+-----------------+----------------------------------------------------------------+

.. note::
   Writing 0x0 to ``tdata1`` disables the trigger and changes the value of ``tdata1`` to
   0xF800_0000, which is the only supported value for a disabled trigger.
   The WARL behavior of ``tdata1.DATA`` depends on the value of ``tdata1.TYPE`` as described in
   :ref:`csr-mcontrol`, :ref:`csr-mcontrol6`, :ref:`csr-etrigger` and :ref:`csr-tdata1_disabled`.

.. _csr-mcontrol:

Match Control Type 2 (``mcontrol``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1 (``mcontrol`` is accessible as ``tdata1`` when ``tdata1.TYPE`` is 0x2)

Reset Value: Not applicable

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-------------+----------------------------------------------------------------+
  | Bit#  | R/W         | Description                                                    |
  +=======+=============+================================================================+
  | 31:28 | WARL (0x2)  | **TYPE**. 2 = Address match trigger (legacy).                  |
  +-------+-------------+----------------------------------------------------------------+
  | 27    | WARL (0x1)  | **DMODE**. Only debug mode can write ``tdata`` registers.      |
  +-------+-------------+----------------------------------------------------------------+
  | 26:21 | WARL (0x0)  | **MASKMAX**. Hardwired to 0.                                   |
  +-------+-------------+----------------------------------------------------------------+
  | 20    | WARL (0x0)  | **HIT**. Hardwired to 0.                                       |
  +-------+-------------+----------------------------------------------------------------+
  | 19    | WARL (0x0)  | **SELECT**. Only address matching is supported.                |
  +-------+-------------+----------------------------------------------------------------+
  | 18    | WARL (0x0)  | **TIMING**. Break before the instruction at the specified      |
  |       |             | address.                                                       |
  +-------+-------------+----------------------------------------------------------------+
  | 17:16 | WARL (0x0)  | **SIZELO**. Match accesses of any size.                        |
  +-------+-------------+----------------------------------------------------------------+
  | 15:12 | WARL (0x1)  | **ACTION**. Enter debug mode on match.                         |
  +-------+-------------+----------------------------------------------------------------+
  | 11    | WARL (0x0)  | **CHAIN**. Hardwired to 0.                                     |
  +-------+-------------+----------------------------------------------------------------+
  | 10:7  | WARL (0x0*, | **MATCH**. 0: Address matches `tdata2`, 2: Address is greater  |
  |       | 0x2, 0x3)   | than or equal to `tdata2`, 3: Address is less than `tdata2`.   |
  +-------+-------------+----------------------------------------------------------------+
  | 6     | WARL        | **M**. Match in machine mode.                                  |
  +-------+-------------+----------------------------------------------------------------+
  | 5     | WARL (0x0)  | Hardwired to 0.                                                |
  +-------+-------------+----------------------------------------------------------------+
  | 4     | WARL (0x0)  | **S**. Hardwired to 0.                                         |
  +-------+-------------+----------------------------------------------------------------+
  | 3     | WARL        | **U**. Match in user mode.                                     |
  +-------+-------------+----------------------------------------------------------------+
  | 2     | WARL        | **EXECUTE**. Enable matching on instruction address.           |
  +-------+-------------+----------------------------------------------------------------+
  | 1     | WARL        | **STORE**. Enable matching on store address.                   |
  +-------+-------------+----------------------------------------------------------------+
  | 0     | WARL        | **LOAD**. Enable matching on load address.                     |
  +-------+-------------+----------------------------------------------------------------+

.. _csr-etrigger:

Exception Trigger (``etrigger``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1 (``etrigger`` is accessible as ``tdata1`` when ``tdata1.TYPE`` is 0x5)

Reset Value: Not applicable

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+--------------+----------------------------------------------------------------+
  | Bit#  | R/W          | Description                                                    |
  +=======+==============+================================================================+
  | 31:28 | WARL (0x5)   | **TYPE**. 5 = Exception trigger.                               |
  +-------+--------------+----------------------------------------------------------------+
  | 27    | WARL (0x1)   | **DMODE**. Only debug mode can write ``tdata`` registers.      |
  +-------+--------------+----------------------------------------------------------------+
  | 26    | WARL (0x0)   | **HIT**. Hardwired to 0.                                       |
  +-------+--------------+----------------------------------------------------------------+
  | 25:13 | WARL (0x0)   | Hardwired to 0.                                                |
  +-------+--------------+----------------------------------------------------------------+
  | 12    | WARL (0x0)   | **VS**. Hardwired to 0.                                        |
  +-------+--------------+----------------------------------------------------------------+
  | 11    | WARL (0x0)   | **VU**. Hardwired to 0.                                        |
  +-------+--------------+----------------------------------------------------------------+
  | 10    | WARL (0x0)   | Hardwired to 0.                                                |
  +-------+--------------+----------------------------------------------------------------+
  | 9     | WARL         | **M**. Match in machine mode.                                  |
  +-------+--------------+----------------------------------------------------------------+
  | 8     | WARL (0x0)   | Hardwired to 0.                                                |
  +-------+--------------+----------------------------------------------------------------+
  | 7     | WARL (0x0)   | **S**. Hardwired to 0.                                         |
  +-------+--------------+----------------------------------------------------------------+
  | 6     | WARL         | **U**. Match in user mode.                                     |
  +-------+--------------+----------------------------------------------------------------+
  | 5:0   | WARL (0x1)   | **ACTION**. Enter debug mode on match.                         |
  +-------+--------------+----------------------------------------------------------------+

.. _csr-mcontrol6:

Match Control Type 6 (``mcontrol6``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1 (``mcontrol6`` is accessible as ``tdata1`` when ``tdata1.TYPE`` is 0x6)

Reset Value: Not applicable

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-------------+----------------------------------------------------------------+
  | Bit#  | R/W         | Description                                                    |
  +=======+=============+================================================================+
  | 31:28 | WARL (0x6)  | **TYPE**. 6 = Address match trigger.                           |
  +-------+-------------+----------------------------------------------------------------+
  | 27    | WARL (0x1)  | **DMODE**. Only debug mode can write ``tdata`` registers.      |
  +-------+-------------+----------------------------------------------------------------+
  | 26:25 | WARL (0x0)  | Hardwired to 0.                                                |
  +-------+-------------+----------------------------------------------------------------+
  | 24    | WARL (0x0)  | **VS**. Hardwired to 0.                                        |
  +-------+-------------+----------------------------------------------------------------+
  | 23    | WARL (0x0)  | **VU**. Hardwired to 0.                                        |
  +-------+-------------+----------------------------------------------------------------+
  | 22    | WARL (0x0)  | **HIT**. Hardwired to 0.                                       |
  +-------+-------------+----------------------------------------------------------------+
  | 21    | WARL (0x0)  | **SELECT**. Only address matching is supported.                |
  +-------+-------------+----------------------------------------------------------------+
  | 20    | WARL (0x0)  | **TIMING**. Break before the instruction at the specified      |
  |       |             | address.                                                       |
  +-------+-------------+----------------------------------------------------------------+
  | 19:16 | WARL (0x0)  | **SIZE**. Match accesses of any size.                          |
  +-------+-------------+----------------------------------------------------------------+
  | 15:12 | WARL (0x1)  | **ACTION**. Enter debug mode on match.                         |
  +-------+-------------+----------------------------------------------------------------+
  | 11    | WARL (0x0)  | **CHAIN**. Hardwired to 0.                                     |
  +-------+-------------+----------------------------------------------------------------+
  | 10:7  | WARL (0x0*, | **MATCH**. 0: Address matches `tdata2`, 2: Address is greater  |
  |       | 0x2, 0x3)   | than or equal to `tdata2`, 3: Address is less than `tdata2`.   |
  +-------+-------------+----------------------------------------------------------------+
  | 6     | WARL        | **M**. Match in machine mode.                                  |
  +-------+-------------+----------------------------------------------------------------+
  | 5     | WARL (0x0)  | Hardwired to 0.                                                |
  +-------+-------------+----------------------------------------------------------------+
  | 4     | WARL (0x0)  | **S**. Hardwired to 0.                                         |
  +-------+-------------+----------------------------------------------------------------+
  | 3     | WARL        | **U**. Match in user mode.                                     |
  +-------+-------------+----------------------------------------------------------------+
  | 2     | WARL        | **EXECUTE**. Enable matching on instruction address.           |
  +-------+-------------+----------------------------------------------------------------+
  | 1     | WARL        | **STORE**. Enable matching on store address.                   |
  +-------+-------------+----------------------------------------------------------------+
  | 0     | WARL        | **LOAD**. Enable matching on load address.                     |
  +-------+-------------+----------------------------------------------------------------+

.. _csr-tdata1_disabled:

Trigger Data 1 (``tdata1``) - ``disabled`` view
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1 (``tdata1`` view when ``tdata1.TYPE`` is 0xF)

Reset Value: Not applicable

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table


  +-------+-------------+----------------------------------------------------------------+
  | Bit#  | R/W         | Description                                                    |
  +=======+=============+================================================================+
  | 31:28 | WARL (0xF)  | **TYPE**. 0xF (``disabled``).                                  |
  +-------+-------------+----------------------------------------------------------------+
  | 27    | WARL (0x1)  | **DMODE**. Only debug mode can write ``tdata`` registers.      |
  +-------+-------------+----------------------------------------------------------------+
  | 26:0  | WARL (0x0)  | **DATA**.                                                      |
  +-------+-------------+----------------------------------------------------------------+

.. note::
   Writing 0x0 to ``tdata1`` disables the trigger and changes the value of ``tdata1`` to
   0xF800_0000, which is the only supported value for a disabled trigger.

.. _csr-tdata2:

Trigger Data Register 2 (``tdata2``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | WARL | **DATA**                                                         |
  +-------+------+------------------------------------------------------------------+

.. note::
   The WARL behavior of ``tdata2`` depends on the values of ``tdata1.TYPE`` and ``tdata1.DMODE`` as described in
   :ref:`csr-tdata2-type-0x2`, :ref:`csr-tdata2-type-0x5`, :ref:`csr-tdata2-type-0x6` and :ref:`csr-tdata2-type-0xf`.

.. _csr-tdata2-type-0x2:

Trigger Data Register 2 (``tdata2``) - View when ``tdata1.TYPE`` is 0x2
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | WARL | **DATA**                                                         |
  +-------+------+------------------------------------------------------------------+

.. note::
   Accessible in Debug Mode or M-Mode, depending on ``tdata1.DMODE``.
   This register stores the instruction address, load address or store address to match against for a breakpoint trigger.

.. _csr-tdata2-type-0x5:

Trigger Data Register 2 (``tdata2``) - View when ``tdata1.TYPE`` is 0x5
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------------+------------------------------------------------------------------+
  | Bit#  | R/W        | Description                                                      |
  +=======+============+==================================================================+
  | 31:26 | WARL (0x0) | **DATA[31:26]**                                                  |
  +-------+------------+------------------------------------------------------------------+
  | 25    | WARL       | **DATA[25]**. Instruction parity/checksum fault.                 |
  +-------+------------+------------------------------------------------------------------+
  | 24    | WARL       | **DATA[24]**. Instruction bus fault.                             |
  +-------+------------+------------------------------------------------------------------+
  | 23:12 | WARL (0x0) | **DATA[23:12]**                                                  |
  +-------+------------+------------------------------------------------------------------+
  | 11    | WARL       | **DATA[11]**. Environment call from M-Mode (ECALL)               |
  +-------+------------+------------------------------------------------------------------+
  | 10:9  | WARL (0x0) | **DATA[10:9]**                                                   |
  +-------+------------+------------------------------------------------------------------+
  | 8     | WARL       | **DATA[8]**. Environment call from U-Mode (ECALL)                |
  +-------+------------+------------------------------------------------------------------+
  | 7     | WARL       | **DATA[7]**. Store/AMO access fault.                             |
  +-------+------------+------------------------------------------------------------------+
  | 6     | WARL (0x0) | **DATA[6]**                                                      |
  +-------+------------+------------------------------------------------------------------+
  | 5     | WARL       | **DATA[5]**. Load access fault.                                  |
  +-------+------------+------------------------------------------------------------------+
  | 4     | WARL (0x0) | **DATA[4]**                                                      |
  +-------+------------+------------------------------------------------------------------+
  | 3     | WARL       | **DATA[3]**. Breakpoint.                                         |
  +-------+------------+------------------------------------------------------------------+
  | 2     | WARL       | **DATA[2]**. Illegal instruction.                                |
  +-------+------------+------------------------------------------------------------------+
  | 1     | WARL       | **DATA[1]**. Instruction access fault.                           |
  +-------+------------+------------------------------------------------------------------+
  | 0     | WARL (0x0) | **DATA[0]**                                                      |
  +-------+------------+------------------------------------------------------------------+

.. note::
   Accessible in Debug Mode or M-Mode, depending on ``tdata1.DMODE``.
   This register stores the currently selected exception codes for an exception trigger.

.. _csr-tdata2-type-0x6:

Trigger Data Register 2 (``tdata2``) - View when ``tdata1.TYPE`` is 0x6
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | WARL | **DATA**                                                         |
  +-------+------+------------------------------------------------------------------+

.. note::
   Accessible in Debug Mode or M-Mode, depending on ``tdata1.DMODE``.
   This register stores the instruction address, load address or store address to match against for a breakpoint trigger.

.. _csr-tdata2-type-0xf:

Trigger Data Register 2 (``tdata2``) - View when ``tdata1.TYPE`` is 0xF
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | WARL | **DATA**                                                         |
  +-------+------+------------------------------------------------------------------+

.. note::
   Accessible in Debug Mode or M-Mode, depending on ``tdata1.DMODE``.

.. _csr-tdata3:

Trigger Data Register 3 (``tdata3``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A3

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------------+------------------------------------------------------------------+
  | Bit#  | R/W        | Description                                                      |
  +=======+============+==================================================================+
  | 31:0  | WARL (0x0) | Hardwired to 0.                                                  |
  +-------+------------+------------------------------------------------------------------+

Accessible in Debug Mode or M-Mode.
|corev| does not support the features requiring this register. CSR is hardwired to 0.

.. _csr-tinfo:

Trigger Info (``tinfo``)
~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A4

Reset Value: 0x0000_8064

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------------+------------------------------------------------------------------+
  | Bit#  | R/W        | Description                                                      |
  +=======+============+==================================================================+
  | 31:16 | WARL (0x0) | Hardwired to 0.                                                  |
  +-------+------------+------------------------------------------------------------------+
  | 15:0  | R (0x8064) | **INFO**. Types 0x2, 0x5, 0x6 and 0xF are supported.             |
  +-------+------------+------------------------------------------------------------------+

The **info** field contains one bit for each possible `type` enumerated in
`tdata1`.  Bit N corresponds to type N.  If the bit is set, then that type is
supported by the currently selected trigger.  If the currently selected trigger
does not exist, this field contains 1.

Accessible in Debug Mode or M-Mode.

.. _csr-tcontrol:

Trigger Control (``tcontrol``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A5

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+-------------+------------------------------------------------------------------+
  | Bit#  | R/W         | Description                                                      |
  +=======+=============+==================================================================+
  | 31:8  | WARL (0x0)  | Hardwired to 0.                                                  |
  +-------+-------------+------------------------------------------------------------------+
  | 7     | WARL (0x0)  | **MPTE**. Hardwired to 0.                                        |
  +-------+-------------+------------------------------------------------------------------+
  | 6:4   | WARL (0x0)  | Hardwired to 0.                                                  |
  +-------+-------------+------------------------------------------------------------------+
  | 3     | WARL (0x0)  | **MTE**. Hardwired to 0.                                         |
  +-------+-------------+------------------------------------------------------------------+
  | 2:0   | WARL (0x0)  | Hardwired to 0.                                                  |
  +-------+-------------+------------------------------------------------------------------+

|corev| does not support the features requiring this register. CSR is hardwired to 0.

.. _csr-dcsr:

Debug Control and Status (``dcsr``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B0

Reset Value: 0x4000_0413

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +----------+--------------+-------------------------------------------------------------------------------------------------+
  |   Bit #  |   R/W        |   Description                                                                                   |
  +==========+==============+=================================================================================================+
  | 31:28    | R (0x4)      | **XDEBUGVER**. External debug support exists as described in [RISC-V-DEBUG]_.                   |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 27:18    | WARL (0x0)   | Reserved                                                                                        |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 17       | WARL (0x0)   | **EBREAKVS**. Hardwired to 0                                                                    |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 16       | WARL (0x0)   | **EBREAKVU**. Hardwired to 0.                                                                   |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 15       | RW           | **EBREAKM**. Set to enter debug mode on ``ebreak`` during machine mode.                         |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 14       | WARL (0x0)   | Hardwired to 0.                                                                                 |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 13       | WARL (0x0)   | **EBREAKS**. Hardwired to 0.                                                                    |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 12       | WARL         | **EBREAKU**. Set to enter debug mode on ``ebreak`` during user mode.                            |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 11       | WARL         | **STEPIE**. Set to enable interrupts during single stepping.                                    |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 10       | WARL         | **STOPCOUNT**.                                                                                  |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 9        | WARL (0x0)   | **STOPTIME**. Hardwired to 0.                                                                   |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 8:6      | R            | **CAUSE**. Return the cause of debug entry.                                                     |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 5        | WARL (0x0)   | **V**. Hardwired to 0.                                                                          |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 4        | WARL (0x1)   | **MPRVEN**. Hardwired to 1.                                                                     |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 3        | R            | **NMIP**. If set, an NMI is pending                                                             |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 2        | RW           | **STEP**. Set to enable single stepping.                                                        |
  +----------+--------------+-------------------------------------------------------------------------------------------------+
  | 1:0      | WARL (0x0,   | **PRV**. Returns the privilege mode before debug entry.                                         |
  |          | 0x3)         |                                                                                                 |
  +----------+--------------+-------------------------------------------------------------------------------------------------+

.. _csr-dpc:

Debug PC (``dpc``)
~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B1

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                                   |
  +=============+===========+=================================================================================================+
  | 31:0        | RW        | **DPC**. Debug PC                                                                               |
  +-------------+-----------+-------------------------------------------------------------------------------------------------+

When the core enters in Debug Mode, DPC contains the virtual address of
the next instruction to be executed.

Debug Scratch Register 0/1 (``dscratch0/1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B2/0x7B3

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                                                   |
  +=============+===========+=================================================================================================+
  | 31:0        | RW        | DSCRATCH0/1                                                                                     |
  +-------------+-----------+-------------------------------------------------------------------------------------------------+

Machine Cycle Counter (``mcycle``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB00

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | RW   | The lower 32 bits of the 64 bit machine mode cycle counter.      |
  +-------+------+------------------------------------------------------------------+

Machine Instructions-Retired Counter (``minstret``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB02

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+---------------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                               |
  +=======+======+===========================================================================+
  | 31:0  | RW   | The lower 32 bits of the 64 bit machine mode instruction retired counter. |
  +-------+------+---------------------------------------------------------------------------+

Machine Performance Monitoring Counter (``mhpmcounter3 .. mhpmcounter31``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB03 - 0xB1F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+----------+------------------------------------------------------------------+
  | Bit#  | R/W      | Description                                                      |
  +=======+==========+==================================================================+
  | 31:0  | R (0x0)  | Hardwired to 0.                                                  |
  +-------+----------+------------------------------------------------------------------+

Upper 32 Machine Cycle Counter (``mcycleh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB80

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                      |
  +=======+======+==================================================================+
  | 31:0  | RW   | The upper 32 bits of the 64 bit machine mode cycle counter.      |
  +-------+------+------------------------------------------------------------------+

Upper 32 Machine Instructions-Retired Counter (``minstreth``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB82

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+------+---------------------------------------------------------------------------+
  | Bit#  | R/W  | Description                                                               |
  +=======+======+===========================================================================+
  | 31:0  | RW   | The upper 32 bits of the 64 bit machine mode instruction retired counter. |
  +-------+------+---------------------------------------------------------------------------+

Upper 32 Machine Performance Monitoring Counter (``mhpmcounter3h .. mhpmcounter31h``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB83 - 0xB9F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------+----------+------------------------------------------------------------------+
  | Bit#  | R/W      | Description                                                      |
  +=======+==========+==================================================================+
  | 31:0  | R (0x0)  | Hardwired to 0.                                                  |
  +-------+----------+------------------------------------------------------------------+

CPU Control (``cpuctrl``)
~~~~~~~~~~~~~~~~~~~~~~~~~
CSR Address: 0xBF0

Reset Value: 0x0000_0019

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:20       | R (0x0)   | Reserved. Hardwired to 0.                                              |
  +-------------+-----------+------------------------------------------------------------------------+
  | 19:16       | RW        | **RNDDUMMYFREQ:** Frequency control for dummy instruction insertion.   |
  |             |           | Dummy instruction inserted every n instructions where n is a range     |
  |             |           | set based on the value written to this register where:                 |
  |             |           | 0x0 = 1-4, 0x1 = 1-8, 0x3 = 1-16, 0x7 = 1-32, 0xF = 1-64.              |
  +-------------+-----------+------------------------------------------------------------------------+
  | 15:5        | R (0x0)   | Reserved. Hardwired to 0.                                              |
  +-------------+-----------+------------------------------------------------------------------------+
  | 4           | RW        | **INTEGRITY:** Enable checksum integrity checking (1 = enable).        |
  +-------------+-----------+------------------------------------------------------------------------+
  | 3           | RW        | **PCHARDEN:** Enable PC hardening (1 = enable).                        |
  +-------------+-----------+------------------------------------------------------------------------+
  | 2           | RW        | **RNDHINT:** Replace ``c.slli with rd=x0, nzimm!=0`` custom hint by    |
  |             |           | a random instruction without registerfile side effects (1 = enable).   |
  +-------------+-----------+------------------------------------------------------------------------+
  | 1           | RW        | **RNDDUMMY:** Dummy instruction insertion enable (1 = enable).         |
  +-------------+-----------+------------------------------------------------------------------------+
  | 0           | RW        | **DATAINDTIMING:** Data independent timing enable (1 = enable).        |
  +-------------+-----------+------------------------------------------------------------------------+

The ``cpuctrl`` register contains configuration registers for core security features.

Secure Seed 0
~~~~~~~~~~~~~
CSR Address: 0xBF9

Reset Value: ``LFSR0_CFG.default_seed``

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | RW        | Seed for LFSR0. Always reads as 0x0.                                   |
  +-------------+-----------+------------------------------------------------------------------------+

The ``secureseed0`` CSR contains seed data for LFSR0.

Secure Seed 1
~~~~~~~~~~~~~
CSR Address: 0xBFA

Reset Value: ``LFSR1_CFG.default_seed``

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | RW        | Seed for LFSR1. Always reads as 0x0.                                   |
  +-------------+-----------+------------------------------------------------------------------------+

The ``secureseed1`` CSR contains seed data for LFSR1.

Secure Seed 2
~~~~~~~~~~~~~
CSR Address: 0xBFC

Reset Value: ``LFSR2_CFG.default_seed``

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | RW        | Seed for LFSR2. Always reads as 0x0.                                   |
  +-------------+-----------+------------------------------------------------------------------------+

The ``secureseed2`` CSR contains seed data for LFSR2.

Machine Vendor ID (``mvendorid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF11

Reset Value: 0x0000_0602

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:7        | R (0xC)   | Number of continuation codes in JEDEC manufacturer ID.                 |
  +-------------+-----------+------------------------------------------------------------------------+
  | 6:0         | R (0x2)   | Final byte of JEDEC manufacturer ID, discarding the parity bit.        |
  +-------------+-----------+------------------------------------------------------------------------+

The ``mvendorid`` encodes the OpenHW JEDEC Manufacturer ID, which is 2 decimal (bank 13).

Machine Architecture ID (``marchid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF12

Reset Value: 0x0000_0015

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |   R/W     |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | R (0x15)  | Machine Architecture ID of |corev| is 0x15 (decimal 21)                |
  +-------------+-----------+------------------------------------------------------------------------+

.. _csr-mimpid:

Machine Implementation ID (``mimpid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF13

Reset Value: Defined

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     |  R/W      |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:20       | R (0x0)   | Hardwired to 0.                                                        |
  +-------------+-----------+------------------------------------------------------------------------+
  | 19:16       | R (0x0)   | **MAJOR**.                                                             |
  +-------------+-----------+------------------------------------------------------------------------+
  | 15:12       | R (0x0)   | Hardwired to 0.                                                        |
  +-------------+-----------+------------------------------------------------------------------------+
  | 11:8        | R (0x0)   | **MINOR**.                                                             |
  +-------------+-----------+------------------------------------------------------------------------+
  | 7:4         | R (0x0)   | Hardwired to 0.                                                        |
  +-------------+-----------+------------------------------------------------------------------------+
  | 3:0         | R         | **PATCH**.  **mimpid_patch_i**, see  :ref:`core-integration`           |
  +-------------+-----------+------------------------------------------------------------------------+

The Machine Implementation ID uses a Major, Minor, Patch versioning scheme. The **PATCH** bitfield is defined and set
by the integrator and shall be set to 0 when no patches are applied. It is made available as **mimpid_patch_i** on the
boundary of |corev| such that it can easily be changed by a metal layer only change.

.. _csr-mhartid:

Hardware Thread ID (``mhartid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF14

Reset Value: Defined

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  |   Bit #     | R/W       |   Description                                                          |
  +=============+===========+========================================================================+
  | 31:0        | R         | Machine Hardware Thread ID **mhartid_i**, see  :ref:`core-integration` |
  +-------------+-----------+------------------------------------------------------------------------+

Machine Configuration Pointer (``mconfigptr``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF15

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +------+----------+-----------------------------------------+
  | Bit# |  R/W     | Definition                              |
  +======+==========+=========================================+
  | 31:0 | R (0x0)  | Reserved                                |
  +------+----------+-----------------------------------------+

.. _csr-mintstatus:

Machine Interrupt Status (``mintstatus``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF46

Reset Value: 0x0000_0000

Include Condition: ``SMCLIC`` = 1

Detailed:

.. table::
  :widths: 10 20 70
  :class: no-scrollbar-table

  +-------------+------------+-------------------------------------------------------------------------+
  |   Bit #     |   R/W      |           Description                                                   |
  +=============+============+=========================================================================+
  | 31:24       |   R        | **MIL**: Machine Interrupt Level                                        |
  +-------------+------------+-------------------------------------------------------------------------+
  | 23:16       |   R (0x0)  | Reserved. Hardwired to 0.                                               |
  +-------------+------------+-------------------------------------------------------------------------+
  | 15: 8       |   R (0x0)  | **SIL**: Supervisor Interrupt Level, hardwired to 0.                    |
  +-------------+------------+-------------------------------------------------------------------------+
  |  7: 0       |   R (0x0)  | **UIL**: User Interrupt Level, hardwired to 0.                          |
  +-------------+------------+-------------------------------------------------------------------------+

This register holds the active interrupt level for each privilege mode.
Only Machine Interrupt Level is supported.

.. only:: PMP

  Machine Security Configuration (``mseccfg``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x747

  Reset Value: defined (based on ``PMP_MSECCFG_RV``)

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | Bit# |  R/W        | Definition                                                                                                                        |
    +======+=============+===================================================================================================================================+
    | 31:10| WPRI (0x0)  | Hardwired to 0.                                                                                                                   |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 9    | R    (0x0)  | **SSEED**. Hardwired to 0.                                                                                                        |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 8    | R    (0x0)  | **USEED**. Hardwired to 0.                                                                                                        |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 7:3  | WPRI (0x0)  | Hardwired to 0.                                                                                                                   |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 2    | WARL        | **RLB**. Rule Locking Bypass.                                                                                                     |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 1    | WARL        | **MMWP**. Machine Mode Whitelist Policy. This is a sticky bit and once set can only be unset due to ``rst_ni`` assertion.         |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | 0    | WARL        | **MML**. Machine Mode Lockdown. This is a sticky bit and once set can only be unset due to ``rst_ni`` assertion.                  |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+

  .. note::
     ``mseccfg`` is hardwired to 0x0 if ``PMP_NUM_REGIONS`` == 0.

  Machine Security Configuration (``mseccfgh``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x757

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+
    | Bit# |  R/W        | Definition                                                                                                                        |
    +======+=============+===================================================================================================================================+
    | 31:0 | WPRI (0x0)  | Hardwired to 0.                                                                                                                   |
    +------+-------------+-----------------------------------------------------------------------------------------------------------------------------------+

  PMP Configuration (``pmpcfg0-pmpcfg15``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x3A0 - 0x3AF

  Reset Value: defined (based on ``PMP_PMPNCFG_RV[]``)

  Detailed ``pmpcfg0``:

  +-------+---------------+
  | Bit#  | Definition    |
  +=======+===============+
  | 31:24 | PMP3CFG       |
  +-------+---------------+
  | 23:16 | PMP2CFG       |
  +-------+---------------+
  | 15:8  | PMP1CFG       |
  +-------+---------------+
  | 7:0   | PMP0CFG       |
  +-------+---------------+

  Detailed ``pmpcfg1``:

  +-------+---------------+
  | Bit#  | Definition    |
  +=======+===============+
  | 31:24 | PMP7CFG       |
  +-------+---------------+
  | 23:16 | PMP6CFG       |
  +-------+---------------+
  | 15:8  | PMP5CFG       |
  +-------+---------------+
  | 7:0   | PMP4CFG       |
  +-------+---------------+

  ...

  Detailed ``pmpcfg15``:

  +-------+---------------+
  | Bit#  | Definition    |
  +=======+===============+
  | 31:24 | PMP63CFG      |
  +-------+---------------+
  | 23:16 | PMP62CFG      |
  +-------+---------------+
  | 15:8  | PMP61CFG      |
  +-------+---------------+
  | 7:0   | PMP60CFG      |
  +-------+---------------+

  The configuration fields for each ``pmpxcfg`` are as follows:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------------------+---------------------------+
    | Bit#  |  R/W             |  Definition               |
    +=======+==================+===========================+
    |    7  | WARL             | **L**. Lock               |
    +-------+------------------+---------------------------+
    |  6:5  | WARL (0x0)       | Reserved                  |
    +-------+------------------+---------------------------+
    |  4:3  | WARL             | **A**. Mode               |
    +-------+------------------+---------------------------+
    |    2  | WARL /           | **X**. Execute permission |
    +-------+ WARL (0x0, 0x1,  +---------------------------+
    |    1  | 0x3, 0x4,        | **W**. Write permission   |
    +-------+ 0x5, 0x7)        +---------------------------+
    |    0  |                  | **R**. Read permission    |
    +-------+------------------+---------------------------+

  .. note::
     When PMP_GRANULARITY >= 1, the NA4 mode (``pmpxcfg.A == 0x2``) mode is not selectable. ``pmpxcfg.A`` will remain unchanged when attempting to enable NA4 mode.

  .. note::
     ``pmpxcfg`` is WARL (0x0) if x >= ``PMP_NUM_REGIONS``.

  .. note::
     If **mseccfg.MML** = 0, then the **R**, **W** and **X**  together form a collective WARL field for which the combinations with **R** = 0 and **W** = 1 are reserved for future use
     The value of the collective  **R**, **W**, **X** bitfield will remain unchanged when attempting to write **R** = 0 and **W** = 1 while **mseccfg.MML** = 0.
     If **mseccfg.MML** = 1, then the **R**, **W** and **X**  together form a collective WARL field in which all values are valid.

  PMP Address (``pmpaddr0`` - ``pmpaddr63``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x3B0 - 0x3EF

  Reset Value: defined (based on ``PMP_PMPADDR_RV[]``)

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+-----------------------+---------------------------+
    | Bit#  |  R/W                  |  Definition               |
    +=======+=======================+===========================+
    | 31:0  | WARL / WARL (0x0)     | ADDRESS[33:2]             |
    +-------+-----------------------+---------------------------+

  .. note::
     When PMP_GRANULARITY >= 1, ``pmpaddrx[PMP_GRANULARITY-1:0]`` will be read as 0 if the PMP mode is TOR (``pmpcfgx.A == 0x1``) or OFF (``pmpcfgx.A == 0x0``).
     When PMP_GRANULARITY >= 2, ``pmpaddrx[PMP_GRANULARITY-2:0]`` will be read as 1 if the PMP mode is NAPOT (``pmpcfgx.A == 0x3``).
     Although changing ``pmpcfgx.A`` affects the value read from ``pmpaddrx``, it does not affect the underlying value stored in that register.

  .. note::
     ``pmpaddrx`` is WARL if x < ``PMP_NUM_REGIONS`` and WARL (0x0) otherwise.

.. only:: ZICNTR

  Cycle Counter (``cycle``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC00

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode cycle counter.


  Instructions-Retired Counter (``instret``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC02

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode instruction retired counter.

.. only:: ZIHPM

  Performance Monitoring Counter (``hpmcounter3 .. hpmcounter31``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC03 - 0xC1F

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode
  performance counter. Non implemented counters always return a read value of 0.

.. only:: ZICNTR

  Upper 32 Cycle Counter (``cycleh``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC80

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode cycle counter.



  Upper 32 Instructions-Retired Counter (``instreth``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC82

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode instruction retired counter.

.. only:: ZIHPM

  Upper 32 Performance Monitoring Counter (``hpmcounter3h .. hpmcounter31h``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0xC83 - 0xC9F

  Reset Value: 0x0000_0000

  Detailed:

  .. table::
    :widths: 10 20 70
    :class: no-scrollbar-table

    +-------+------+------------------------------------------------------------------+
    | Bit#  | R/W  | Description                                                      |
    +=======+======+==================================================================+
    | 31:0  | R    |                                                                  |
    +-------+------+------------------------------------------------------------------+

  Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode
  performance counter. Non implemented counters always return a read value of 0.


Hardened CSRs
--------------

Some CSRs have been implemeted with error detection using an inverted shadow copy. If an attack is successful in altering the register value, the error detection logic will trigger a major alert.

This applies to the following registers:

 - ``cpuctrl``
 - ``dcsr``
 - ``jvt``
 - ``mclicbase``
 - ``mepc``
 - ``mie``
 - ``mintstatus``
 - ``mintthresh``
 - ``mscratch``
 - ``mscratchcsw``
 - ``mscratchcswl``
 - ``mseccfg*``
 - ``mstatus``
 - ``mtvec``
 - ``mtvt``
 - ``pmpaddr*``
 - ``pmpcfg``
