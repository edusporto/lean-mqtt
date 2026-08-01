# LeanMqtt

A formally verified parser and serializer for the MQTT 5.0 network protocol, written in Lean 4. 

This project uses dependent types to enforce correct-by-construction packet modeling. It also provides proofs for parser roundtrip (completeness) and reconstruction (soundness) across the implemented protocol layers. The current phase of the project will be presented at [SBLP 2026](https://cbsoft.sbc.org.br/2026/en/symposiums/sblp/call/). The most up-to-date code can be found in the [project's GitHub repository](https://github.com/edusporto/lean-mqtt).

## Repository Structure

The core source code is located in the `LeanMqtt/` directory, mirroring the MQTT protocol hierarchy:

* **`Primitives/`**: Base protocol types (e.g., Variable Byte Integers, UTF-8 strings) and custom parser combinators (e.g., length-prefixed lists, predicate-constrained fields).
* **`Packets/`**: The packet data structures, including the Fixed Header, Variable Headers, and Payloads (the latter is currently unimplemented).
* **`Core/`**: Core definitions for parsers and codecs.
* **`Helpers/`**: Additional macros or proofs that support the rest of the code.

Most modules are split into two files:
* `Basic.lean`: Contains the data structures, serializers, and parsers.
* `Proofs.lean`: Contains the formal verification theorems (satisfying the `LawfulCodec` and `LawfulByteSize` type classes).

## Building and Usage

To build the project, you will need a working Lean 4 toolchain. To install it, check the instructions at the [official Lean 4 website](https://lean-lang.org/install/). The standard approach is to install it via [`elan`](https://github.com/leanprover/elan).

To compile the code and verify all proofs, run:

```bash
lake build
```

The code is also thoroughly documented using standard Lean tooling. To build the documentation as an HTML web site, check out the instructions at the [`doc-gen4` repository](https://github.com/leanprover/doc-gen4).

The current phase of the project focuses on the verification of the parser properties. Thus, we currently only implement the parser, with future work planned on implementing the full MQTT broker/client.

## Current Status & Future Work

The library currently implements and verifies MQTT fixed headers, variable headers, and properties.

Next steps:
- Finish modeling and verifying the payload layer.
- Build metaprogramming macros to automate packet structure generation.
- Extract the core combinators into a generalized embedded Domain-Specific Language (eDSL) for verifiable network parsing.
