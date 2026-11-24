# TRUST — what you must trust when you use 0.3

English | [中文](TRUST.zh-CN.md)

Residua's claim is that results are used without trusting their
producer. 0.3 delivers this for compilation, and this is exactly what a
user of 0.3 still trusts:

- The committed [seed](GLOSSARY.md) bytes (two wasm modules). Mitigation in 0.3: the
  seed rebuilds the compiler from source to a byte-identical fixpoint,
  published digests let anyone check it, and an independent party
  reproduced it from the bare archive. Not yet: diverse double compiling
  against an independently built compiler.
- The C compiler and the wasm runtime used to run the seed and the
  compilers — they are inside the trusted base in 0.3. The design moves
  running code onto machine-code stencils proved against the ISA
  semantics; in 0.3 that work is partial and not used.
- The host: the operating system, the hardware, and the tools the seed
  recipe actually calls — `env`, `bash`, `uname`, `date`, `sed`, `grep`,
  `printf`, `xargs`, `cmp`, `sha256sum`, `curl`, `tar`, `cat`, `cp`,
  `rm`, `mkdir`, `tee`, `test`, `stat`, `basename` (all coreutils-class
  tools), the C toolchain (`cc` = GCC with GNU binutils, or clang on
  macOS), and the pinned, user-downloaded tools: wasmtime v50.0.1
  (engine plus `wasmtime.h` / `libwasmtime.a`) and binaryen
  version_133 `wasm-opt`. `git` is optional: where no checkout is
  present the recipe verifies the source members by their manifest
  digests instead.
- The formal semantics files are definitions; their meaning is fixed by
  their content address, and they are checked by Lean's kernel. Lean is
  used to check the semantics and as an oracle; building and running 0.3
  needs no Lean.

Not claimed by 0.3: that the compiler is proved correct end to end;
proof checking (R-CIC) is not part of 0.3.
