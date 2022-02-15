[![Build Status](https://travis-ci.com/pulp-platform/riscv.svg?branch=master)](https://travis-ci.com/pulp-platform/riscv)

# OpenHW Group CORE-V CV32E40S RISC-V IP

CV32E40S is a small and efficient, 32-bit, in-order RISC-V core with a 4-stage pipeline that implements the following instruction set architecture:

* RV32[I|E]
* [M|Zmmul]
* Zca_Zcb_Zcmb_Zcmp_Zcmt
* Xsecure
* [Zba_Zbb_Zbs|Zba_Zbb_Zbc_Zbs]
* Zicsr
* Zifencei

The CV32E40S core is aimed
at security applications and offers both Machine mode and User mode, an enhanced PMP, as well as
various anti-tampering features.

It started its life as a fork of the OpenHW CV32E40P core that in its turn was based on the RI5CY core from
the [PULP platform](https://www.pulp-platform.org/) team.

## Documentation

The CV32E40S user manual can be found in the _docs_ folder and it is
captured in reStructuredText, rendered to html using [Sphinx](https://docs.readthedocs.io/en/stable/intro/getting-started-with-sphinx.html).
These documents are viewable using readthedocs and can be viewed [here](https://docs.openhwgroup.org/projects/cv32e40s-user-manual/en/latest/).

## Verification
The verification environment for the CV32E40S is _not_ in this Repository.

The verification environment for this core as well as other cores in the OpenHW Group CORE-V family is at the
[core-v-verif](https://github.com/openhwgroup/core-v-verif) repository on GitHub.

The Makefiles supported in the **core-v-verif** project automatically clone the appropriate version of the **CV32E40S**  RTL sources.

## Constraints
Example synthesis constraints for the CV32E40S are provided.

## Contributing

We highly appreciate community contributions. We are currently using the lowRISC contribution guide.

To ease our work of reviewing your contributions, please:

* Create your own fork to commit your changes and then open a Pull Request.
* Split large contributions into smaller commits addressing individual changes or bug fixes. Do not
  mix unrelated changes into the same commit!
* Write meaningful commit messages. For more information, please check out the [the Ibex contribution
  guide](https://github.com/lowrisc/ibex/blob/master/CONTRIBUTING.md).
* If asked to modify your changes, do fixup your commits and rebase your branch to maintain a
  clean history.

When contributing SystemVerilog source code, please try to be consistent and adhere to [the lowRISC Verilog
coding style guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).

To get started, please check out the ["Good First Issue"
 list](https://github.com/openhwgroup/cv32e40s/issues?q=is%3Aissue+is%3Aopen+-label%3Astatus%3Aresolved+label%3A%22good+first+issue%22).

## Issues and Troubleshooting

If you find any problems or issues with CV32E40S or the documentation, please check out the [issue
 tracker](https://github.com/openhwgroup/cv32e40s/issues) and create a new issue if your problem is
not yet tracked.
