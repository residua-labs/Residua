# Residua

English | [中文](README.zh-CN.md)

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

## Release 0.1

Version 0.1 is the minimal self-bootstrap closure: a committed WebAssembly seed of the two rsd compilers (`rsdc`, front
end; `rsc`, back end), the 54 source files the seed was built from, the runtime, the formal semantics of each layer, and
the documents. It is published as one source archive on the
[rsd-0.1 release](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1):

- `rsd-src.tar`, sha256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`, 201 files;
- `rsd-src.tar.sha256`.

What it lets you check: on a clean Linux x86-64 machine with a C compiler and the usual shell tools (no Lean, Node or
OCaml), the recipe in `bootstrap/seed/stage-14274/README.md` rebuilds both compilers from source and reproduces the
committed seed byte for byte. Start with `release/docs/QUICKSTART`; `release/docs/VERIFY-RELEASE` lists every digest
check. An independent agent with no prior knowledge of the project reproduced this fixed point from the documents alone
on a fresh virtual machine.

What it does not include: the proof checker, modules, and the agent tools are later versions. `release/docs/RELEASE-NOTES`,
`TRUST`, `STABILITY` and `RESIDUES` state the limits; `release/docs/PERF-RECORD` gives the measured performance against
Koka on fixed hardware.

Security reports: use GitHub's private vulnerability reporting on this repository.

## License

Apache License 2.0. See LICENSE and NOTICE.
