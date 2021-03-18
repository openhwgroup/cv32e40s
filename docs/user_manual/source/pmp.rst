.. _pmp:

Physical Memory Attribution (PMP)
=================================
The |corev| includes a Physical Memory Protection (PMP) unit.
The PMP is both statically and dynamically configurable. The static configuration is performed through the top level 
parameters ``PMP_NUM_REGIONS`` and ``PMP_GRANULARITY``. The dynamic configuration is performed through the CSRs described in :ref:`cs-registers`.
