.. _performance-counters:

Performance Counters
====================

|corev| implements performance counters according to [RISC-V-PRIV]_.
The performance counters are placed inside the Control and Status Registers (CSRs) and can be accessed with the ``CSRRW(I)`` and ``CSRRS/C(I)`` instructions.

|corev| implements the clock cycle counter ``mcycle(h)`` and the retired instruction counter ``minstret(h)``. The ``mcycle(h)`` and ``minstret(h)`` counters are always available and 64 bit wide.
The event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)`` and the corresponding event selector CSRs ``mhpmevent3`` - ``mhpmevent31`` are hard-wired to 0.
The ``mcountinhibit`` CSR is used to individually enable/disable the counters.

.. note::

   All performance counters are using the gated version of ``clk_i``. The **wfi** instruction impact the gating of ``clk_i`` as explained
   in :ref:`sleep_unit` and can therefore affect the counters.

Controlling the counters from software
--------------------------------------

By default, all available counters are disabled after reset in order to provide the lowest power consumption.

They can be individually enabled/disabled by overwriting the corresponding bit in the ``mcountinhibit`` CSR at address ``0x320`` as described in [RISC-V-PRIV]_.
In particular, to enable/disable ``mcycle(h)``, bit 0 must be written. For ``minstret(h)``, it is bit 2.

The lower 32 bits of all counters can be accessed through the base register, whereas the upper 32 bits are accessed through the ``h``-register.
Reads of all these registers are non-destructive.

Time Registers (``time(h)``)
----------------------------

The user mode ``time(h)`` registers are not implemented. Any access to these
registers will cause an illegal instruction trap. It is recommended that a software trap handler is
implemented to detect access of these CSRs and convert that into access of the
platform-defined ``mtime`` register (if implemented in the platform).
