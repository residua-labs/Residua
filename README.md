# Residua

Residua is infrastructure for using another party's computation or proof without trusting that party. Results are
identified by the content address (q) of what they are, not by who produced them or which toolchain version built them,
and they are admitted only by mechanical checking, over a network of formally defined semantics.

Residua is designed so that computation and proof are one: in rsd, its language, a program and a proof are terms of the
same dependent type theory, and the same term is both compiled to native or WebAssembly code and checked by the kernel.
This is not yet demonstrated end to end; version 0.1 ships the compilation half.

## Why

- Re-checking, repair after upstream changes, coordination and review dominate the cost of formal results; the kernel
  check itself is a small share.
- Results are bound to toolchain versions: a compiled proof library does not carry across compiler versions, so every
  upgrade rebuilds and re-checks everything downstream. Residua keeps results and their dependencies as a graph of
  content addresses: an upgrade re-checks only what changed, and a fact checked once stays the same fact.
- Most future producers of results will be machines that cannot be trusted. Only mechanical checking and content identity
  scale to that.
- Formal semantics are siloed (proof assistants, programming languages, virtual machines); results do not compose
  across them.

## Status

This repository is being prepared for the first release, 0.1. Its earlier contents were development tests and have been
removed. Version 0.1 will provide verifiable-provenance compilation: a committed seed that rebuilds the rsd compiler
byte for byte from source with a C compiler alone, frozen formal semantics for each compilation layer, a measured
performance record, and the release's documented limits. The release notes will state exactly what it includes and what
it does not.

## License

Apache License 2.0. See LICENSE and NOTICE.
