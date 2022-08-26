.. _custom-isa-extensions:

CORE-V Instruction Set Extensions
=================================

Custom instructions
-------------------

|corev| supports the custom instruction(s) listed in :numref:`Custom instructions`.

.. table:: Custom instructions
  :name: Custom instructions
  :widths: 10 10 80
  :class: no-scrollbar-table

  +-------------------------+-------------+--------------------------------------------------+
  | Custom instruction      | Encoding    | Description                                      |
  +=========================+=============+==================================================+
  | ``wfe``                 | 0x8C00_0073 | Wait For Event, see :ref:`wfe`.                  |
  +-------------------------+-------------+--------------------------------------------------+

Custom CSRs
-----------

|corev| supports the custom CSRs listed in :numref:`Control and Status Register Map (additional custom CSRs)`.
