.. _pmp:

Physical Memory Protection (PMP)
================================

The |corev| includes the Physical Memory Protection (PMP) unit.
The PMP is both statically and dynamically configurable. The static configuration is performed through the top level 
parameters ``PMP_NUM_REGIONS`` and ``PMP_GRANULARITY``. The dynamic configuration is performed through the CSRs described in :ref:`cs-registers`.

The ``PMP_GRANULARITY`` parameter is used to configure the minimum granularity of PMP address matching. The minimum granularity is 2 :sup:`PMP_GRANULARITY+2` bytes, so at least 4 bytes.

The ``PMP_NUM_REGIONS`` parameter is used to configure the number of PMP regions, starting from the lowest numbered region. All PMP CSRs are always implemented, but CSRs (or bitfields of CSRs) related to PMP entries with number ``PMP_NUM_REGIONS`` and above are hardwired to zero.

The reset value of the PMP CSR registers can be set through the top level parameters ``PMP_PMPNCFG_RV[]``, ``PMP_PMPADDR_RV[]`` and ``PMP_MSECCFG_RV``.
``PMP_PMPNCFG_RV[]`` is an array of ``PMP_NUM_REGIONS`` entries of the type ``pmpncfg_t``. Entry N determines the reset value of the ``pmpNcfg`` bitfield in the ``pmpcfg`` CSRs.
``PMP_PMPADDR_RV[]`` is an array of ``PMP_NUM_REGIONS`` entries of ``logic [31:0]``. Entry N determines the reset value of the ``pmpaddrN`` CSR.
``PMP_MSECCFG_RV`` is of the type ``mseccfg_t`` and determines the reset value of the ``mseccfg`` CSR.

The PMP is compliant to [RISC-V-PRIV]_ and [RISC-V-SMEPMP]_.
