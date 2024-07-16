<!--
SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>

SPDX-License-Identifier: CC0-1.0
-->

# Kami

A programming language for distributed systems integrated with the rust ecosystem.

## Prototype
There is ongoing work to build the first prototype of the Kami compiler. The various intermediate languages and compilation steps can be found in the `kami-core/src/KamiCore/Language/` subfolders. A short explanation of the purpose of each step, together with a small example which is run through the pipeline is available in `kami-core/src/KamiCore/Pipeline/Definition.agda`.

### Typechecking the prototype
In order to typecheck the current prototype, you need a recent install of [Agda](https://github.com/agda/agda) (e.g. version 2.6.x, or the current master branch).

Additionally, you will need to install the following libraries on your system, as described in the [Agda documentation](https://agda.readthedocs.io/en/v2.6.20240714/tools/package-system.html):

 - [agda standard library](https://github.com/agda/agda-stdlib)
 - [agda prelude](https://github.com/UlfNorell/agda-prelude)
 - [Agora](https://github.com/determi-io/agora)
 - [KamiTheory](https://github.com/kami-language/kami-theory)

In order to typecheck the whole compilation pipeline, and apply it to the example term, change into the `kami-core/src/KamiCore/Pipeline/` subfolder and run `agda Definition.agda`. This will take quite some time as it recursively typechecks all dependencies.


## Funding

This project is funded through [NGI Zero Core](https://nlnet.nl/core), a fund established by [NLnet](https://nlnet.nl) with financial support from the European Commission's [Next Generation Internet](https://ngi.eu) program. Learn more at the [NLnet project page](https://nlnet.nl/Kami).

[<img src="https://nlnet.nl/logo/banner.png" alt="NLnet foundation logo" width="20%" />](https://nlnet.nl)
[<img src="https://nlnet.nl/image/logos/NGI0_tag.svg" alt="NGI Zero Logo" width="20%" />](https://nlnet.nl/core)
