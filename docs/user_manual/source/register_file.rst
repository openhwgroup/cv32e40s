.. _register-file:

Register File
=============

Source file: :file:`rtl/cv32e40s_register_file.sv`

|corev| has 31 32-bit wide registers which form registers ``x1`` to ``x31``.
Register ``x0`` is statically bound to 0 and can only be read, it does not
contain any sequential logic.

The register file has two read ports and one write port. Register file reads are performed in the ID stage.
Register file writes are performed in the WB stage.

General Purpose Register File
-----------------------------

The general purpose register file is flip-flop-based. It uses regular, positive-edge-triggered flip-flops to implement the registers.

Error Detection
---------------

The register file of |corev| has integrated error detection logic and a 6-bit hamming code for each word.
This ensures detection of up to two errors in each register file word. Detected errors trigger the core major alert output.
