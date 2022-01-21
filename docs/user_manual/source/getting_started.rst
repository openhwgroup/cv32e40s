.. _getting-started:

Getting Started with |corev|
=============================

This page discusses initial steps and requirements to start using |corev| in your design.

.. _clock-gating-cell:

Clock Gating Cell
-----------------

|corev| requires clock gating cells.
These cells are usually specific to the selected target technology and thus not provided as part of the RTL design.
A simulation-only version of the clock gating cell is provided in ``cv32e40s_sim_clock_gate.sv``. This file contains
a module called ``cv32e40s_clock_gate`` that has the following ports:

* ``clk_i``: Clock Input
* ``en_i``: Clock Enable Input
* ``scan_cg_en_i``: Scan Clock Gate Enable Input (activates the clock even though ``en_i`` is not set)
* ``clk_o``: Gated Clock Output

And the following Parameters:
* ``LIB`` : Standard cell library (semantics defined by integrator)

Inside |corev|, the clock gating cell is used in ``cv32e40s_sleep_unit.sv``.

The ``cv32e40s_sim_clock_gate.sv`` file is not intended for synthesis. For ASIC synthesis and FPGA synthesis the manifest
should be adapted to use a customer specific file that implements the ``cv32e40s_clock_gate`` module using design primitives
that are appropriate for the intended synthesis target technology.


.. _register-cells:

Register Cells
--------------
|corev| requires instantiated registers for some logically redundant security features (such as :ref:`hardened-csrs`).

Like clock gating cells these are specific to the target technology and are therefore not provided as part of the RTL design.
Simulation-only versions for these cells are provided in cv32e40s_sim_sffr.sv and cv32e40s_sim_sffs.sv.
cv32e40s_sim_sffr.sv contains the module ``cv32e40s_sffr`` with the following ports:

* ``clk``   : Clock
* ``rst_n`` : Reset
* ``d_i``   : Data input
* ``q_o``   : Flopped data output

And the following parameters:
* ``LIB`` : Standard cell library (semantics defined by integrator)

cv32e40s_sim_sffs.sv contains the module ``cv32e40s_sffs`` with the following ports:

* ``clk``   : Clock
* ``set_n`` : Set (i.e., reset value == 1)
* ``d_i``   : Data input
* ``q_o``   : Flopped data output

And the following parameters:
* ``LIB`` : Standard cell library (semantics defined by integrator)

These files are not intended for synthesis.
For ASIC synthesis and FPGA synthesis the manifest should be adapted
to use customer specific files that implement the ``cv32e40s_sffr`` and ``cv32e40s_sffs`` modules
using design primitives that are appropriate for the intended synthesis target technology.
