# TRUST — what you must trust when you use 0.2

English | [中文](TRUST.zh-CN.md)

Residua's claim is that results are used without trusting their
producer. 0.2 delivers this for compilation, and this is exactly what a
user of 0.2 still trusts:

- The committed seed bytes (two wasm modules). Mitigation in 0.2: the
  seed rebuilds the compiler from source to a byte-identical fixpoint,
  published digests let anyone check it, and an independent party
  reproduced it from the bare archive. Not yet: diverse double compiling
  against an independently built compiler.
- The C compiler and wasm2c used to run the seed and the compilers —
  they are inside the trusted base in 0.2. The design moves running code
  onto machine-code stencils proved against the ISA semantics; in 0.2
  that work is partial and not used.
- The host: the operating system, the hardware, and the tools the seed
  recipe actually calls — `env`, `bash`, `uname`, `date`, `sed`, `grep`,
  `printf`, `xargs`, `cmp`, `sha256sum`, `curl`, `tar`, `cat`, `cp`,
  `rm`, `mkdir`, `tee`, `test`, `stat`, `basename` (all coreutils-class
  tools), the C toolchain (`cc` = GCC with GNU binutils), and the pinned
  wabt binaries `wasm2c` and `wasm-validate`. `git` is optional: where
  no checkout is present the recipe verifies the source members by
  their manifest digests instead.
- The formal semantics files are definitions; their meaning is fixed by
  their content address, and they are checked by Lean's kernel. Lean is
  used to check the semantics and as an oracle; building and running 0.2
  needs no Lean.

Not claimed by 0.2: that the compiler is proved correct end to end;
proof checking (R-CIC) is not part of 0.2.
