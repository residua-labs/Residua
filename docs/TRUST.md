# TRUST — what you must trust when you use 0.4

English | [中文](TRUST.zh-CN.md)

Residua's claim is that results are used without trusting their
producer. 0.4 delivers this for compilation, and this is exactly what a
user of 0.4 still trusts:

- The committed [seed](GLOSSARY.md) bytes (two wasm modules). Mitigation in 0.4: the
  seed rebuilds the compiler from source to a byte-identical fixpoint,
  published digests let anyone check it, and we rebuilt it byte for byte
  on Linux x86-64 and macOS arm64. Not yet: reproduction by an
  independent party, and diverse double compiling against an
  independently built compiler.
- The C compiler and the wasm runtime used to run the seed and the
  compilers — they are inside the trusted base in 0.4. The design moves
  running code onto machine-code stencils proved against the ISA
  semantics; in 0.4 that work is partial and not used.
- The host: the operating system, the hardware, and the tools the 0.4
  quick start actually calls — a C11 compiler (`cc`), POSIX `sh`,
  `awk`, `curl`, `tar` (with `xz`), `sha256sum` or `shasum -a 256`,
  `cmp`, `grep`, `uname`, `cp`, `mkdir`, `cat`, `printf` — and the
  pinned, user-downloaded tools: wasmtime v50.0.1's C library
  (`wasmtime.h` / `libwasmtime.a`) and binaryen version_133
  `wasm-opt`. `glue/host/procwt.c`, the C host that runs compiled Proc
  programs, is built by the same `cc`.
- The formal semantics files are definitions; their meaning is fixed by
  their content address, and they are checked by Lean's kernel. Lean is
  used to check the semantics and as an oracle; building and running 0.4
  needs no Lean.

Not claimed by 0.4: that the compiler is proved correct end to end — no
published wasm artifact carries a proof that it refines its source. The
compiler is tested by differential runs; the semantics and the
composition theorems are checked by Lean's kernel. Proof checking
(R-CIC) is not part of 0.4.
