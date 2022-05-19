.. _pma:

Physical Memory Attribution (PMA)
=================================
The |corev| includes a Physical Memory Attribution (PMA) unit that allows compile time attribution of the physical memory map.
The PMA is configured through the top level parameters ``PMA_NUM_REGIONS`` and ``PMA_CFG[]``.
The number of PMA regions is configured through the ``PMA_NUM_REGIONS`` parameter. Valid values are 0-16.
The configuration array, ``PMA_CFG[]``, must consist of ``PMA_NUM_REGIONS`` entries of the type ``pma_cfg_t``, defined in ``cv32e40s_pkg.sv``:

.. code-block:: verilog

  typedef struct packed {
    logic [31:0] word_addr_low;
    logic [31:0] word_addr_high;
    logic        main;
    logic        bufferable;
    logic        cacheable;
    logic        integrity;
  } pma_cfg_t;

In case of address overlap between PMA regions, the region with the lowest index in ``PMA_CFG[]`` will have priority.
The PMA can be deconfigured by setting ``PMA_NUM_REGIONS=0``. When doing this, ``PMA_CFG[]`` should be left unconnected.

Address range
~~~~~~~~~~~~~
The address boundaries of a PMA region are set in ``word_addr_low/word_addr_high``. These contain bits 33:2 of 34-bit, word aligned addresses. To get an address match, the transfer address ``addr`` must be in the range ``{word_addr_low, 2'b00} <= addr[33:0] < {word_addr_high, 2'b00}``. Note that ``addr[33:32] = 2'b00`` as the |corev| does not support Sv32.

Main memory vs I/O
~~~~~~~~~~~~~~~~~~
Memory ranges can be defined as either main (``main=1``) or I/O (``main=0``).

Code execution is allowed from main memory and main memory is considered to be idempotent. Non-aligned transactions are supported in main memory.
Modifiable transactions are supported in main memory.

Code execution is not allowed from I/O regions and an instruction access fault (exception code 1) is raised when attempting to execute from such regions. 
I/O regions are considered to be non-idempotent and therefore the PMA will prevent speculative accesses to such regions.
Non-aligned transactions are not supported in I/O regions. An attempt to perform a non-naturally aligned load access to an I/O region causes a precise
load access fault (exception code 5). An attempt to perform a non-naturally aligned store access to an I/O region causes a precise store access fault (exception code 7).
Modifiable/modified transactions are not supported in I/O regions.  An attempt to perform a modifiable/modified load access to an I/O region causes a precise
load access fault (exception code 5). An attempt to perform a modifiable/modified store access to an I/O region causes a precise store access fault (exception code 7).

.. note::
   The [RISC-V-ZCA_ZCB_ZCMB_ZCMP_ZCMT]_ specification leaves it to the core implementation whether ``cm.push``, ``cm.pop``, ``cm.popret`` and ``cm.popretz`` instructions
   are supported to non-idempotent memories or not. In |corev| the ``cm.push``, ``cm.pop``, ``cm.popret`` and ``cm.popretz`` instructions
   are **not** allowed to perform their load or store acceses to non-idempotent memories (I/O) and a load access fault (exception code 5) or store access fault (exception code 7)
   will occur upon the first such load or store access violating this requirement (meaning that the related ``pop`` or ``push`` might become partially executed).

.. note::
   Modifiable transactions are transactions which allow transformations as for example merging or splitting. For example, a misaligned store word instruction that
   is handled as two subword transactions on the data interface is considered to use modified transactions.

Bufferable and Cacheable
~~~~~~~~~~~~~~~~~~~~~~~~
Accesses to regions marked as bufferable (``bufferable=1``) will result in the OBI ``mem_type[0]`` bit being set, except if the access was an instruction fetch, a load, or part of an atomic memory operation. Bufferable stores will utilize the write buffer, see :ref:`Write buffer <write_buffer>`.

Accesses to regions marked as cacheable (``cacheable=1``) will result in the OBI ``mem_type[1]`` bit being set.

.. note::
   The PMA must be configured such that accesses to the external debug module are non-cacheable, to enable its program buffer to function correctly.

.. _pma_integrity:

Integrity
~~~~~~~~~
Accesses to regions marked with ``integrity=1`` will have their OBI response phase inputs checked against the ``instr_rchk_i`` and ``data_rchk_i`` signals as specified in [OPENHW-OBI]_.
Accesses to regions marked with ``integrity=0`` will never leads to instruction parity/checksum fault (see :ref:`exceptions-interrupts`), load parity/checksum fault NMI (see :ref:`exceptions-interrupts`),
store parity/checksum fault NMI (see :ref:`exceptions-interrupts`) or major alert (see :ref:`interface-integrity`) due to unexpected ``instr_rchk_i`` or ``data_rchk_i`` values.

.. note::
   ``data_rdata_i`` is never checked against ``data_rchk_i`` for write transactions (see [OPENHW-OBI]_).

.. note::
   The ``instr_gntpar_i``, ``instr_rvalidpar_i``, ``data_gntpar_i`` and ``data_rvalidpar_i`` are always checked (also for accesses to regions with ``integrity=0``).

Default attribution
~~~~~~~~~~~~~~~~~~~
If the PMA is deconfigured (``PMA_NUM_REGIONS=0``), the entire memory range will be treated as main memory (``main=1``), non-bufferable (``bufferable=0``), non-cacheable (``cacheable=0``) and no integrity (``integrity=0``).

If the PMA is configured (``PMA_NUM_REGIONS > 0``), memory regions not covered by any PMA regions are treated as I/O memory (``main=0``), non-bufferable (``bufferable=0``), non-cacheable (``cacheable=0``) and no integrity (``integrity=0``).

Every instruction fetch, load and store will be subject to PMA checks and failed checks will result in an exception. PMA checks cannot be disabled.
See :ref:`exceptions-interrupts` for details.
