.. _pmp:

Physical Memory Protection (PMP)
================================

The |corev| includes the Physical Memory Protection (PMP) unit.
The PMP is both statically and dynamically configurable. The static configuration is performed through the top level 
parameters ``PMP_NUM_REGIONS`` and ``PMP_GRANULARITY``. The dynamic configuration is performed through the CSRs described in :ref:`cs-registers`.

The ``PMP_GRANULARITY`` parameters is used to configure the minimum granularity of PMP address matching. The minimum granularity is 2 :sup:`PMP_NUM_REGIONS+2` bytes, so at least 4 bytes.

The ``PMP_NUM_REGIONS`` parameter is used to configure the number of PMP regions, starting from the lowest numbered region. All PMP CSRs are always implemented, but CSRs (or bitfields of CSRs) related to PMP entries with number ``PMP_NUM_REGIONS`` and above are hardwired to zero.

The PMP is compliant to [RISC-V-PRIV]_ and [RISC-V-SMEPMP]_.
