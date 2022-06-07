.. _core-integration:

Core Integration
================

The main module is named ``cv32e40s_core`` and can be found in ``cv32e40s_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Synthesis Optimization
----------------------

``*Important*``
The |corev| has security features that are logically redundant and likely to be optimised away in synthesis.
Special care is therefore needed in synthesis scripts to ensure these features are preserved in the implemented netlist.

The implementaion of following features should be checked:
- CSR shadow registers
- Register file ECC

Implementing a netlist test verifying these features on the final netlist is recommended.


Instantiation Template
----------------------

.. code-block:: verilog

  cv32e40s_core #(
      .LIB                      (                0 ),
      .RV32                     (            RV32I ),
      .B_EXT                    (             NONE ),
      .M_EXT                    (                M ),
      .DBG_NUM_TRIGGERS         (                1 ),
      .PMP_GRANULARITY          (                0 ),
      .PMP_NUM_REGIONS          (                0 ),
      .PMP_PMPNCFG_RV           ( PMP_PMPNCFG_RV[] ),
      .PMP_PMPADDR_RV           ( PMP_PMPADDR_RV[] ),
      .PMP_MSECCFG_RV           (   PMP_MSECCFG_RV ),
      .PMA_NUM_REGIONS          (                0 ),
      .PMA_CFG                  (        PMA_CFG[] ),
      .SMCLIC                   (                0 ),
      .SMCLIC_ID_WIDTH          (                5 ),
      .LFSR0_CFG                ( LFSR_CFG_DEFAULT ),
      .LFSR1_CFG                ( LFSR_CFG_DEFAULT ),
      .LFSR2_CFG                ( LFSR_CFG_DEFAULT )
  ) u_core (
      // Clock and reset
      .clk_i                    (),
      .rst_ni                   (),
      .scan_cg_en_i             (),

      // Configuration
      .boot_addr_i              (),
      .mtvec_addr_i             (),
      .dm_halt_addr_i           (),
      .dm_exception_addr_i      (),
      .mhartid_i                (),
      .mimpid_patch_i           (),

      // Instruction memory interface
      .instr_req_o              (),
      .instr_reqpar_o           (),
      .instr_gnt_i              (),
      .instr_gntpar_i           (),
      .instr_addr_o             (),
      .instr_memtype_o          (),
      .instr_prot_o             (),
      .instr_achk_o             (),
      .instr_dbg_o              (),
      .instr_rvalid_i           (),
      .instr_rvalidpar_i        (),
      .instr_rdata_i            (),
      .instr_err_i              (),
      .instr_rchk_i             (),

      // Data memory interface
      .data_req_o               (),
      .data_reqpar_o            (),
      .data_gnt_i               (),
      .data_gntpar_i            (),
      .data_addr_o              (),
      .data_be_o                (),
      .data_memtype_o           (),
      .data_prot_o              (),
      .data_dbg_o               (),
      .data_wdata_o             (),
      .data_we_o                (),
      .data_achk_o              (),
      .data_rvalid_i            (),
      .data_rvalidpar_i         (),
      .data_rdata_i             (),
      .data_err_i               (),
      .data_rchk_i              (),

      // Cycle Count
      .mcycle_o                 (),

       // Interrupt interface
      .irq_i                    (),

      .clic_irq_i               (),
      .clic_irq_id_i            (),
      .clic_irq_level_i         (),
      .clic_irq_priv_i          (),
      .clic_irq_shv_i           (),

      // Fencei flush handshake
      .fencei_flush_req_o       (),
      .fencei_flush_ack_i       (),

      // Debug interface
      .debug_req_i              (),
      .debug_havereset_o        (),
      .debug_running_o          (),
      .debug_halted_o           (),

       // Alert interface
      .alert_major_o            (),
      .alert_minor_o            (),

      // Special control signals
      .fetch_enable_i           (),
      .core_sleep_o             ()
  );

Parameters
----------

.. table::
  :widths: 20 10 10 60
  :class: no-scrollbar-table

  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | Name                         | Type/Range     | Default          | Description                                                        |
  +==============================+================+==================+====================================================================+
  | ``LIB``                      | int            | 0                | Standard cell library (semantics defined by integrator)            |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``RV32``                     | rv32_e         | RV32I            | Base Integer Instruction Set.                                      |
  |                              |                |                  | ``RV32`` = RV32I: RV32I Base Integer Instruction Set.              |
  |                              |                |                  | ``RV32`` = RV32E: RV32E Base Integer Instruction Set.              |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``B_EXT``                    | b_ext_e        | NONE             | Enable Bit Manipulation support. ``B_EXT`` = B_NONE: No Bit        |
  |                              |                |                  | Manipulation instructions are supported. ``B_EXT`` = ZBA_ZBB_ZBS:  |
  |                              |                |                  | Zba, Zbb and Zbs are supported. ``B_EXT`` = ZBA_ZBB_ZBC_ZBS:       |
  |                              |                |                  | Zba, Zbb, Zbc and Zbs are supported.                               |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``M_EXT``                    | m_ext_e        | M                | Enable Multiply / Divide support. ``M_EXT`` = M_NONE: No multiply /|
  |                              |                |                  | divide instructions are supported. ``M_EXT`` = ZMMUL: The          |
  |                              |                |                  | multiplication subset of the ``M`` extension is supported.         |
  |                              |                |                  | ``M_EXT`` = M: The ``M`` extension is supported.                   |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``DBG_NUM_TRIGGERS``         | int (0..4 )    | 1                | Number of debug triggers, see :ref:`debug-support`                 |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMA_NUM_REGIONS``          | int (0..16)    | 0                | Number of PMA regions                                              |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMA_CFG[]``                | pma_cfg_t      | PMA_R_DEFAULT    | PMA configuration.                                                 |
  |                              |                |                  | Array of pma_cfg_t with PMA_NUM_REGIONS entries, see :ref:`pma`    |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMP_GRANULARITY``          | int (0..31)    | 0                | Sets minimum granularity of PMP address matching to                |
  |                              |                |                  | 2 :sup:`PMP_GRANULARITY+2` bytes.                                  |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMP_NUM_REGIONS``          | int (0..64)    | 0                | Number of PMP regions                                              |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMP_PMPNCFG_RV[]``         | pmpncfg_t      | PMPNCFG_DEFAULT  | Reset values for ``pmpncfg`` bitfileds in ``pmpcfg`` CSRs.         |
  |                              |                |                  | Array of pmpncfg_t with PMP_NUM_REGIONS entries, see :ref:`pmp`    |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMP_PMPADDR_RV[]``         | logic[31:0]    | 0                | Reset values for ``pmpaddr`` CSRs.                                 |
  |                              |                |                  | Array with PMP_NUM_REGIONS entries, see :ref:`pmp`                 |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``PMP_MSECCFG_RV``           | mseccfg_t      | 0                | Reset value for ``mseccfg`` CSR, see :ref:`pmp`                    |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``SMCLIC``                   | bit            | 0                | Is Smclic supported?                                               |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``SMCLIC_ID_WIDTH``          | int (1..10 )   | 6                | Width of ``clic_irq_id_i`` and ``clic_irq_id_o``. The maximum      |
  |                              |                |                  | number of supported interrupts in CLIC mode is                     |
  |                              |                |                  | ``2^SMCLIC_ID_WIDTH``. Trap vector table alignment is restricted   |
  |                              |                |                  | as described in :ref:`csr-mtvt`.                                   |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``LFSR0``                    | lfsr_cfg_t     | LFSR_CFG_DEFAULT | LFSR0 configuration, see :ref:`xsecure`.                           |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``LFSR1``                    | lfsr_cfg_t     | LFSR_CFG_DEFAULT | LFSR1 configuration, see :ref:`xsecure`.                           |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+
  | ``LFSR2``                    | lfsr_cfg_t     | LFSR_CFG_DEFAULT | LFSR2 configuration, see :ref:`xsecure`.                           |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------+

Interfaces
----------

.. table::
  :widths: 20 10 10 60
  :class: no-scrollbar-table

  +-------------------------+-------------------------+-----+--------------------------------------------+
  | Signal(s)               | Width                   | Dir | Description                                |
  +=========================+=========================+=====+============================================+
  | ``clk_i``               | 1                       | in  | Clock signal                               |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``rst_ni``              | 1                       | in  | Active-low asynchronous reset              |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``scan_cg_en_i``        | 1                       | in  | Scan clock gate enable. Design for test    |
  |                         |                         |     | (DfT) related signal. Can be used during   |
  |                         |                         |     | scan testing operation to force            |
  |                         |                         |     | instantiated clock gate(s) to be enabled.  |
  |                         |                         |     | This signal should be 0 during normal /    |
  |                         |                         |     | functional operation.                      |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``boot_addr_i``         | 32                      | in  | Boot address. First program counter after  |
  |                         |                         |     | reset = ``boot_addr_i``. Must be           |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mtvec_addr_i``        | 32                      | in  | ``mtvec`` address. Initial value for the   |
  |                         |                         |     | address part of :ref:`csr-mtvec`.          |
  |                         |                         |     | Must be 128-byte aligned                   |
  |                         |                         |     | (i.e. ``mtvec_addr_i[6:0]`` = 0).          |
  |                         |                         |     | Do not change after enabling core          |
  |                         |                         |     | via ``fetch_enable_i``                     |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``dm_halt_addr_i``      | 32                      | in  | Address to jump to when entering Debug     |
  |                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``dm_exception_addr_i`` | 32                      | in  | Address to jump to when an exception       |
  |                         |                         |     | occurs when executing code during Debug    |
  |                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mhartid_i``           | 32                      | in  | Hart ID, usually static, can be read from  |
  |                         |                         |     | :ref:`csr-mhartid` CSR                     |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mimpid_patch_i``      | 4                       | in  | Implementation ID patch. Must be static.   |
  |                         |                         |     | Readable as part of :ref:`csr-mimpid` CSR. |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`                  |
  +-------------------------+----------------------------------------------------------------------------+
  | ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                      |
  +-------------------------+----------------------------------------------------------------------------+
  | ``mcycle_o``            | Cycle Counter Output                                                       |
  +-------------------------+----------------------------------------------------------------------------+
  | ``irq_*``               | Interrupt inputs, see :ref:`exceptions-interrupts`                         |
  +-------------------------+----------------------------------------------------------------------------+
  | ``clic_*_i``            | CLIC interface, see :ref:`exceptions-interrupts`                           |
  +-------------------------+----------------------------------------------------------------------------+
  | ``debug_*``             | Debug interface, see :ref:`debug-support`                                  |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``alert_*``             | Alert interface, see :ref:`xsecure`                                        |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``fetch_enable_i``      | 1                       | in  | Enable the instruction fetch of |corev|.   |
  |                         |                         |     | The first instruction fetch after reset    |
  |                         |                         |     | de-assertion will not happen as long as    |
  |                         |                         |     | this signal is 0. ``fetch_enable_i`` needs |
  |                         |                         |     | to be set to 1 for at least one cycle      |
  |                         |                         |     | while not in reset to enable fetching.     |
  |                         |                         |     | Once fetching has been enabled the value   |
  |                         |                         |     | ``fetch_enable_i`` is ignored.             |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``core_sleep_o``        | 1                       | out | Core is sleeping, see :ref:`sleep_unit`.   |
  +-------------------------+-------------------------+-----+--------------------------------------------+
