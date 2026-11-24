# benchmarks/ — third-party performance corpus and measured comparison

This directory is the benchmark corpus behind the 0.1 performance record, and
the measured comparison the record rests on. Nothing here is accepted or
gating: every number is a literal field of the raw runs kept with the suite,
and ratios are computed from those fields. Runs were made on a non-exclusive
arm64 host under sustained load (see Method), so the ratios below are good to
about a factor 1.3 and are not delivery numbers.

Contents: the `.rsd` benchmark sources (their emitted `.rscm` modules
stay repository-side — re-emit one with `rsdc <program>.rsd`),
`MANIFEST.tsv` (per-program provenance), `expected/` (byte-expected outputs),
`rust/` (the Rust reference ports the comparison cites), `arena/` (the two
arena-route source variants), `koka/` (the Koka comparison harness), and
`langs/` (the upstream suite copies the ports derive from).

## The suite

The upstream pages below were fetched on 2026-11-04 (the Benchmarks Game pages
as HTML, kept with the raw runs; the Koka files from
`raw.githubusercontent.com/koka-lang/koka/master/test/bench/`, the other
READMEs from `raw.githubusercontent.com`). A claim marked READ is from that
fetched text; MEASURED is from a run listed below.

Primary list: binary-trees, fannkuch-redux, pidigits from the Computer
Language Benchmarks Game; nqueens, rbtree, rbtree-ck, deriv, cfold from the
Koka/Perceus suite (the PLDI'21 benchmarks, `test/bench` of koka-lang/koka).
Float programs (n-body, spectral-norm, mandelbrot) are excluded by
construction: the wire's constructor set has no float. fasta, k-nucleotide,
reverse-complement, regex-redux are not on the primary list (they need IO
streams, hash tables or a regex engine); they get no row here because they are
not in the primary list, not because they were tried.

| Program | Source (URL) and what it states, READ | Input sizes | Rust reference |
|---|---|---|---|
| binary-trees | benchmarksgame-team.pages.debian.net/benchmarksgame/description/binarytrees.html: allocate a stretch tree, a long-lived tree, many bottom-up trees; "leaf nodes must be the same as interior nodes - the same memory allocation"; "please don't implement your own custom arena"; diff N=10 against the 1 KB output file, N=21 for performance | N=10 (check, expected file kept), N=21 (performance) | The Game's Rust entries use `typed_arena`/`toolshed` arenas (the rule above says arenas are not accepted) and threads, built with `rustc -C opt-level=3 -C target-cpu=ivybridge -C codegen-units=1` (rustc 1.84.1, Game page of entry 1). Not buildable offline and not single-threaded. Used instead: `rust/binarytrees.rs`, one `Box` per node, single thread, the tree type of entry 1; flags below |
| fannkuch-redux | .../description/fannkuchredux.html: the rotation-count permutation order, checksum with alternating sign, max flips; diff N=7 (`228`, `Pfannkuchen(7) = 16`), N=12 for performance (`3968050`, `Pfannkuchen(12) = 65`, entry 2 page) | N=7 check, N=12 performance | The Game's Rust entry 2 (std only, 4 threads), byte for byte, with `main` replaced by a repeat-and-time harness (`rust/fannkuchredux_bg2.rs`); and the same file with the thread-count constant `4` changed to `1` (`rust/fannkuchredux_bg2_t1.rs`), because the subject is single-threaded |
| pidigits | .../description/pidigits.html: arbitrary-precision arithmetic, "the same step-by-step single-threaded algorithm" (Gibbons unbounded spigot, extract(3) and extract(4)), print digits 10 to a line with the running total; diff N=30, N=10000 for performance | N=30 check, N=10000 | The Game's Rust entries need GMP/rug (not buildable offline); `rust/pidigits.rs`, written for this benchmark: the same Ledrug/TeXitoi state machine over a hand-rolled base-2^32 signed-magnitude limb bignum (mul/add by small, signed compare, truncating division with a small quotient via a Knuth-style 64/32 estimate); pidigits-30 byte-equal to the Game's output file, pidigits-10000 byte-equal to the Lean native run |
| nqueens | koka-lang/koka `test/bench/koka/nqueens.kk`; the suite's `readme-pldi40.txt.md` says "n-queens problem of size 13 ... returns the length of that list" | n=13 (73712 solutions) | no Rust version in the suite (its ports are C++, OCaml, Haskell, Swift, Java, Lean, Koka). `rust/nqueens.rs`, written for this benchmark in the shape of the suite's C++ version (persistent lists with shared tails, `Rc` cells) |
| rbtree | `test/bench/koka/rbtree.kk` (from the Lean 4 IFL19 rbmap benchmark); source default `4200000`, printed result `420000` (suite README output) | n=4,200,000 | `rust/rbtree.rs`, written for this benchmark: owned `Box` nodes consumed and rebuilt by each insert (the reuse form of the same algorithm) |
| rbtree-ck | `rbtree-ck.kk`: keeps every 5th intermediate tree alive (`make-tree(5, 4200000)`) | n=4,200,000 (freq 5) | `rust/rbtreeck.rs`, written for this benchmark: the same insert as `rust/rbtree.rs` with `Rc` nodes (the kept list shares subtrees with the live tree, as Koka's reference counting does); the value map is Lean-native == Rust at 2000/20000/4200000 |
| deriv | `deriv.kk` (from Lean 4 IFL19 `deriv.ml`): ten nested symbolic derivatives of `x^x`, prints a count per step | fixed in source | `rust/deriv.rs`, written for this benchmark: Box expressions, smart constructors with deriv.kk's case order; the eleven output lines byte-equal the Lean native run |
| cfold | `cfold.kk`: `mk_expr(20, 1)`, then `reassoc` and `cfold`, prints two evaluations | fixed in source (depth 20) | `rust/cfold.rs`, written for this benchmark: Box expressions, cfold.kk's match arms; both evaluations byte-equal the Lean native run |

Rust compiler and flags for every Rust build here: `rustc 1.99.1` (Homebrew),
`-C opt-level=3 -C codegen-units=1` (the Game's flags without
`-C target-cpu=ivybridge`, which names an x86 core; this machine is arm64). No
`target-cpu=native`.

**Suites read and not adopted, each with its reason:**
- *Are We Fast Yet* (github.com/smarr/are-we-fast-yet, README and its
  guidelines doc): 14 benchmarks ported to ten languages by one rule ("the
  benchmark is identical for all languages"; "use the language
  idiomatically"), measuring *language implementations after warm-up*, not
  smartest-possible programs. Its Queens ("solves the eight queens problem"),
  Permute ("generates permutations of an array"), Storage ("creates and
  verifies a tree of arrays") and List ("recursively creates and traverses
  lists") are the same families as nqueens, fannkuch-redux and binary-trees,
  but with arrays and objects as primitives. Its README lists no Rust port
  (C++, Crystal, Java, JavaScript, Lua, Python, Ruby, SOM, SOMns, Smalltalk)
  and says a Rust port would need additional rules for explicit memory
  management. Not adopted because the primary list was fixed on 2026-11-02
  and its core language assumes arrays and objects that the constructor set
  does not have; it stays as the cross-check for a later array/object
  extension.
- *plb2* (attractivechaos/plb2): four tasks (nqueen with bit operations,
  matmul on floats, sudoku, bedcov) on 25 languages; array and float based,
  so most rows would be "impossible today" for a different reason.
- *hanabi1224/Programming-Language-Benchmarks*: re-publishes the Game's
  programs with CI-generated numbers; adds nothing to the program list, and
  its numbers come from its CI machine, not this measurement environment.
- *kostya/benchmarks*: Brainfuck, Base64, JSON, Matmul, Primes; IO and
  library heavy.

## Coverage — three routes, one row per program

Three routes were tried. A named file is MEASURED, otherwise READ.
- **Untyped route** (U): `.rsd` -> stock Lean 4.14 -> the pinned untyped
  emitter -> lifted evaluator wire. Values are dynamic records, so a
  recursive `inductive` is allowed. Engines: the wire interpreter, and the
  wire's wasm lowering on V8 and wasmtime.
- **Typed route** (T): the typed emitter prototype -> typed `SCMPrograms` ->
  the source-wire encoder -> the rebuilt compiler -> wasm, and `evalSCM` in
  Lean. The typed object language has no recursive type, no float, no bignum.
- **Interned-arena route** (A): the arena generator takes the *untyped*
  emitter's `.scm` modules and produces typed RSCM in which every recursive
  family is a handle into a universal-interning arena (a radix trie of
  nodes, passed in and returned as a record), then the same rebuilt
  compiler. Its cost is reported in the results.

| Program | U (wire interpreter, wasm lowering) | T (typed emission + rebuilt compiler) | A (interned arena + rebuilt compiler) | What is missing, exactly |
|---|---|---|---|---|
| binary-trees | writable now, WRITTEN (`binarytrees.rsd`); N=10 output byte-equal to the Game's file on the interpreter and on the wasm lowering | **T refuses**: `[typed_unrepresentable] recursive_or_indexed(Tree) (in bt.bottom_up)` (MEASURED) | **runs** after a source variant (`binarytrees_arena.rsd`): the unvariated source stops the generator at `[unknown_prim] (* arity 2)`, `(/ arity 2)`, `(mod arity 2)`. The variant's N=10 output (decoded from the arena) is byte-equal to the Game's file; 6.5 s on V8 | T: a recursive type in the typed object language or an encoding. A: the generator has no `*`, `/`, `mod` primitive. Departure from the Game: the arena interns, so structurally equal subtrees are one node (see results; the Game forbids custom arenas) |
| fannkuch-redux | writable now, WRITTEN (`fannkuchredux.rsd`), lists instead of arrays | writable now, WRITTEN: 12 modules, 0 refusals; the rebuilt compiler compiled it; N=7 result equals the Game's (MEASURED) | not needed (no recursive data) | O(1) indexed access and in-place swap: `nth`/`setNth`/prefix reversal are O(n) list rebuilds. Does not block the program; it sets the cost |
| pidigits | impossible today | impossible today | impossible today | arbitrary-precision integers: `Int` is `i64` with checked overflow (a result outside the range is a refusal), the constructor set has no bignum, and none ships in this tree (two searches: a text search over the shipped sources finds only a 64-bit field app differential-tested against Python bigints and a reject-corpus case; a file-name search finds no bignum or limb library). A limb-list library composed from `listAppend`/`listDrop`/`mul`/`divE` is possible in principle, O(n) per limb access, not written |
| nqueens | writable now, WRITTEN (`nqueens.rsd`); counts 92 and 352 equal the known values | writable now, WRITTEN: 6 modules; evalSCM value equal; rebuilt-compiler wasm value equal (MEASURED) | not needed | nothing |
| rbtree | writable now, WRITTEN (`rbtree.rsd`) | **T refuses**: `[typed_unrepresentable] recursive_or_indexed(Tree) (in rb.fold_count)` (MEASURED) | **runs** after a source variant (`rbtree_arena.rsd`: stops at `[unknown_prim] (mod arity 2)` otherwise); n=200 and n=2000 give 20 and 200; 36.9 s for n=2000 on V8 | as binary-trees; the arena is returned in the result packet (21.8 MB at n=2000) |
| rbtree-ck | writable now (differs from rbtree only by a list of kept trees); not written | T refuses, as rbtree (READ: same type) | not tried | as rbtree; sharing is then observable only through the arena |
| deriv | writable with care; not written: recursive `expr`, string names (`eqE` at `str` exists), and Koka's `int` is a bignum while `Int` here is checked `i64`; the printed counts must be checked against the i64 range before a row is claimed | T refuses (READ: recursive type) | not tried | recursive type; i64 range of the derivative coefficients unverified |
| cfold | writable now; not written (`mk_expr` builds only `Add`, depth 20 gives 2^21 leaves, values stay far inside i64); the suite says it needs `ulimit -s unlimited` | T refuses (READ: recursive type) | not tried | recursive type; stack depth (the interpreter needs `RUST_MIN_STACK`, V8 `--stack-size`) |

Float programs (n-body, spectral-norm, mandelbrot): impossible on every route
(no float in the typed object language), excluded by construction.

### Typed emission of the remaining programs (MEASURED 2026-11-05)

The corpus programs written for this suite were pushed through the typed
emitter prototype (in its hold state recursive inductives lower to the
interned-arena representation). Same harness as the binarytrees/rbtree rows
(the library roots compiled into every program); several `Lib.Arena.walk*`
refusals repeat in every row (defunctionalisation, not done).

| Program | emit result | refusals beyond walk* | what is missing, exactly |
|---|---|---|---|
| rbtree-ck | 19 modules, 205,111 B, emit 1.1 s | none | nothing at emit time; the run needs the arena evaluation path (as rbtree) |
| deriv | 0 modules, 101 refusals | `[typed_refused_int_mod] Int % is not the chain's floor modulus; write Int.fmod` in `pownAux`; `application of non-constant head fvar` and `non_constant_type_head(forallE)` for `nest`/`nestAux` (the program passes a function argument) | Int `%` in the port's `pownAux` (Koka's `%` is floor; the chain's is `fmod`); higher-order program shape (defunctionalisation) |
| cfold | 17 modules, 144,027 B, emit 2.2 s | none | nothing at emit time; the run needs the arena evaluation path and a large stack |
| pidigits | 15 modules, 43,063 B, emit 1.2 s | none | emits (state is Int/Nat arithmetic), but the values leave the i64 range within a few terms: the run is unattainable on every typed route until a bignum exists (coverage row above) |

What the refusals imply for the language, without touching the core: (1)
**recursive data is the dominant gap on the typed route** (4 of the 6
non-float, non-bignum programs; the typed emitter refuses all four) but it is
**not impossible**: route A reaches the rebuilt compiler for two of them at a
measured price (a source restricted to the generator's primitives, a 34-fold
(binary-trees N=10) to 900-fold (rbtree n=2000) slower run than the untyped
wasm module on V8, an arena in every signature). A faster answer is the
arena described in `docs/EMITTER.md` built into the typed emitter, unbuilt.
(2) bignum is a library question, not a core one: a limb-list module, costed
first. (3) arrays: their absence costs a factor (index access O(n)), not a
refusal.

## Programs written, and how every output is checked

The `.rsd` sources in this directory: `nqueens.rsd`, `binarytrees.rsd`,
`fannkuchredux.rsd`, `rbtree.rsd`, and `rbtreeck.rsd`, `deriv.rsd`,
`cfold.rsd`, `pidigits.rsd` (faithful ports of the remaining Koka/Game
programs; pidigits is the Game's Gibbons unbounded spigot as run by its
C/Rust entries, over arbitrary-precision signed integers), plus the two
arena-route variants in `arena/`. Each is plain Lean 4.14 (the port subset:
structures, inductives, first-order definitions, structural recursion; loops
are structural recursion on a `Nat` count; no `partial`, no `%` on `Int`, no
`Nat`-subtraction tricks beyond truncation). Header comments name the source
program and every departure. deriv's smart constructors carry an explicit
`Nat` fuel (the port's termination proof, stated in its header as such; it
does not change the case order). pidigits' term-composition loop carries a
fuel bound of 1000 (stated; a digit needs a few terms).

Every source is accepted by stock Lean 4.14 (`lean <name>.rsd`). The corpus
checker builds each source with the pinned untyped emitter, runs the wire
interpreter, and compares with `expected/`, printing one PASS/FAIL line per
claim. The host-side text rendering is `jq` only (binary-trees uses
`render_bt.jq`; fannkuch prints `checksum` and `Pfannkuchen(n) = maxflips`
from the two fields), because the constructor set has no number-to-string.

The corpus programs were also checked by Lean native runs against the Rust
references: for each program, `lean -o <m>.olean <m>.rsd`, a small IO driver
(printing the entry value in the suite's text format), `lean --c=<m>.c` per
module, `leanc -c` for objects, then a relink with the system clang and the
toolchain's Lean libraries with `-Wl,-stack_size,0x10000000` (the
toolchain's own linker output is rejected by this system's loader, and
cfold's deep recursion needs the stack); Rust built with the flags above.
The comparisons are listed below.

Outputs and where they are compared with the suite's expected output
(`expected/`):

| Program | Input | Expected (source) | wire interpreter | wasm lowering V8 | wasm lowering wasmtime | typed evalSCM | rebuilt-compiler wasm (V8, wasmtime) |
|---|---|---|---|---|---|---|---|
| binary-trees | 10 | the Game's output file (byte-equal) | equal | equal (full value) | equal (first 256 of 1037 bytes) | refused | refused (T); arena route equal (decoded) |
| fannkuch-redux | 7 | the Game's output (`228`, `Pfannkuchen(7) = 16`) | equal | equal | equal | equal | equal (V8 and wasmtime) |
| fannkuch-redux | 8 | derived: Rust entry 2 (4 threads and 1 thread) prints `1616`, `Pfannkuchen(8) = 22` | equal | equal | equal | not run | no result: wasmtime traps `out of bounds memory access` at 0x100001f0 in a 0x10000000-byte memory; V8 with `--stack-size=60000` segfaults (exit 139) |
| nqueens | 8, 9 | known counts 92, 352 (OEIS A000170), n=13: 73712 (suite text) | equal | equal | equal | equal at 6 and 8 | equal at 4, 6, 8, 9 |
| rbtree | 2000, 20000 | `n/10` (the suite's printed `420000` is n=4,200,000) | equal | equal | equal | refused | refused (T); arena route equal at 200, 2000 |
| rbtree-ck (corpus port) | 2000, 20000, 4200000 | `expected/rbtreeck.txt` (Lean native == Rust, each size; `n/10` at freq 5) | not run | not run | not run | not run | not run; typed emission emits (see above) |
| deriv (corpus port) | fixed in source | `expected/deriv.txt` (Lean native == Rust, the eleven lines) | not run | not run | not run | refuses | refuses |
| cfold (corpus port) | fixed in source (depth 20) | `expected/cfold.txt` (Lean native == Rust, the two evaluations) | not run | not run | not run | not run | not run; typed emission emits (see above) |
| pidigits (corpus port) | 30, 10000 | 30: the Game's output file, byte-equal (Lean native and Rust); 10000: `expected/pidigits-10000.txt`, byte-equal Lean native == Rust | impossible (bignum) | impossible | impossible | refuses (i64 overflow) | refuses; typed emission emits but the value is unattainable |

"equal (value)" for the wasm lowering means the module's returned JSON value
equals the interpreter's on the same payload; the Game text form is rendered
from that value only for the interpreter.

## Method, machine, how far the load limits the numbers

- Machine: a non-exclusive arm64 host under sustained load (Apple silicon,
  16 cores): the 1-minute load average read 25 to 99 during the Rust and
  wasm runs (every raw line carries `load1_start`; a short window read
  214). Jobs ran under `nice`. Wall times therefore moved by up to 2x
  between repeats of the same run (nqueens 13 on Rust: wall 2.19 s, CPU
  1.39 s). **Every ratio below uses CPU time (user + system of the call,
  one process-wide clock), min over the repeats**, because it moves less
  than wall; wall is in the raw files. This limits the numbers to ratios
  good to about a factor 1.3; nothing here is a delivery number (exclusive
  machine, out of scope).
- Rust: `rustc 1.99.1`, `-C opt-level=3 -C codegen-units=1`, in-process
  best of N repeats, `clock_gettime(CLOCK_PROCESS_CPUTIME_ID)` around one
  run; the program is the full computation including its allocation and
  drops.
  Reproduce: `rustc -C opt-level=3 -C codegen-units=1 -o bin rust/<name>.rs && ./bin <n> <reps>` (stdout is the Game-format output, stderr `best_s best_cpu_s`).
- Untyped wasm lowering: the module is the program with its input baked
  in; the timer is the `eval_wire` call on a fresh instance. V8: node
  v26.12.0, `--stack-size=60000`. wasmtime 50.0.1, default Cranelift, a
  1 GiB wasm stack (the default 512 KiB traps "call stack exhausted" on
  fannkuch 7).
- Rebuilt-compiler wasm: the typed route's `SCMPrograms` encoded by the
  source-wire encoder, compiled by the pinned rebuilt compiler
  (3,576,344 B) through the pinned runner (`--profile-bootstrap512
  --compile-source`, Node 22), then run by the V1-invocation/V2-outcome
  ABI (`compile(1024, len)`), fresh instance per repeat. The route is a
  rebuild for measurement, not part of the shipped artifact set.
- Instruments: `wasmtime` fuel (one unit per wasm instruction, a count
  not a time); `/usr/bin/time -l` instructions retired for Rust (process
  total, the start-up cost measured on a tiny input is subtracted); Lean
  `evalSCM` and a node-counting twin (`cev`, agreement with `evalSCM`
  checked per row; where the twin lacks a constructor it says
  `cev_agrees=false` and its count is discarded); V8 sampling profiles
  at 200 microsecond intervals.

## Results

CPU seconds of one run, min over repeats; in parentheses the ratio to Rust's
CPU seconds on the same input. "untyped" is the wire's wasm lowering;
"compiled" is the rebuilt compiler's output. The wire interpreter is a
process total and is not a subject. A dash is "no row: refused or not run"
(see the coverage table). The wasmtime untyped numbers beat V8 by up to 3x
on the allocation-heavy rows (V8 pays the growth of a memory that is never
freed).

| program input | Rust cpu s | untyped wasmtime cpu s (x Rust) | untyped V8 cpu s (x Rust) | compiled wasmtime cpu s (x Rust) | compiled V8 cpu s (x Rust) | interpreter proc cpu s (x Rust) |
|---|---|---|---|---|---|---|
| nqueens 8 | 0.000271 | 0.0194 (72x) | 0.0198 (73x) | 0.0761 (281x) | 0.0784 (289x) | 0.0723 (267x) |
| nqueens 9 | 0.00135 | 0.121 (90x) | 0.36 (268x) | 0.704 (523x) | 0.685 (509x) | 0.427 (317x) |
| binary-trees 10 | 0.00548 | 0.0542 (10x) | 0.108 (20x) | - | - | 0.298 (54x) |
| binary-trees 12 | 0.0276 | 0.27 (10x) | 2.74 (99x) | - | - | - |
| fannkuch-redux 7 | 0.000197 | 0.146 (742x) | 0.373 (1895x) | 0.549 (2786x) | 0.489 (2482x) | 0.583 (2957x) |
| fannkuch-redux 8 | 0.00198 | 1.41 (715x) | 36 (18201x) | - | - | 1.81 (918x) |
| rbtree 2000 | 0.00165 | 0.0422 (26x) | 0.0387 (23x) | - | - | 0.159 (96x) |
| rbtree 20000 | 0.0203 | 0.686 (34x) | 1.96 (97x) | - | - | 2.04 (101x) |

Rust at the suite's standard size (so its time is not sub-millisecond; the
residua rows cannot run these sizes):

| Rust program | input | CPU s (min) | wall s (min) | reps |
|---|---|---|---|---|
| nqueens (Rust nqueens.rs) | 13 | 1.39 | 2.19 | 5 |
| binary-trees (Box version) | 21 | 27.56 | 31.90 | 3 |
| fannkuch-redux (Game entry 2, 1 thread) | 12 | 45.77 | 59.58 | 3 |
| fannkuch-redux (Game entry 2, 4 threads) | 12 | 48.76 | 21.22 | 3 |
| rbtree (owned Box nodes) | 4200000 | 9.49 | 16.45 | 3 |

(The Game's own Rust entries are faster than the same-input numbers here
because they use arenas and four threads on another machine: published
entry 1 takes 2.10 s at binary-trees 21, entry 2 takes 9.19 s at
fannkuch-redux 12; the single-thread Box version measured here took
27.6 s CPU and 45.8 s CPU respectively. These are different programs and
machines; no ratio is formed.)

Same-run ratios, summarised: the untyped lowering (wasmtime) is 10x to 742x
Rust across its rows; the compiled output (wasmtime) is 281x to 2786x on the
two it runs. Where both run the same program, the compiled output costs
3.9x (nqueens 8), 5.8x (nqueens 9) and 3.8x (fannkuch-redux 7) the CPU
time of the untyped lowering on wasmtime.

Instruction counts (wasmtime fuel units, one program run each, from a
separate pass with fuel metering on):

| Program, input | untyped units | compiled units | Rust instructions retired (net of start-up) | compiled / untyped | untyped / Rust | compiled / Rust |
|---|---|---|---|---|---|---|
| nqueens 8 | 242,703,833 | 1,045,713,249 | 2,871,616 | 4.3x | 85x | 364x |
| nqueens 9 | 1,428,194,158 | 10,507,584,060 | 7,805,265 | 7.4x | 183x | 1346x |
| binary-trees 10 | 609,004,302 | - | 57,694,635 | - | 11x | - |
| fannkuch-redux 7 | 1,347,679,108 | 4,821,007,204 | 2,599,387 | 3.6x | 518x | 1855x |
| rbtree 2000 | 507,718,884 | - | 18,122,636 | - | 28x | - |

Typed-route interpreter (`evalSCM` in Lean, not a speed subject): nqueens 6:
96,274 nodes, 0.28 s; nqueens 8: 2,072,140 nodes, 5.4 s, so the rebuilt
compiler's output executes 505 wasm instructions per source node for
nqueens 8 (1,045,713,249 units / 2,072,140) and the untyped lowering 117
(242,703,833 / 2,072,140; the two are different lowerings of the same source
function set). fannkuch-redux 7 on `evalSCM`: value equal, 20.8 s; the
node-counting twin lacks constructors used there.

### The interned-arena route, separate from the table above

| Program | source change | generator | compile (node 22, loaded) | wasm | run | output |
|---|---|---|---|---|---|---|
| binary-trees N=10 | `*`, `/` removed (the generator stops at `[unknown_prim]` otherwise, MEASURED) | RSCM 20,303 B, 7 modules + 31 helpers, 0 residues | 19.9 s | 257,076 B | 6.55 s wall on V8 (min of 3) | byte-equal to the Game's file after decoding the arena |
| rbtree n=200 / 2000 | `mod` removed (stops at `[unknown_prim] (mod arity 2)` otherwise, MEASURED) | RSCM 102,971 B, 6 modules + 31 helpers, 0 residues | 41.9 s | 853,701 B | 0.65 s / 36.9 s | 20 / 200, equal; result packet 21.8 MB at n=2000 (it returns the arena) |

Against the same programs on the untyped lowering on V8 (binary-trees N=10:
0.189 s wall; rbtree n=2000: 0.041 s wall) that is 34x and 900x slower.
Rust: 5.5 ms and 1.6 ms. The route works as a bridge and is not a
performance route as built. Cost of the route itself: a source subset (no
`*`, `/`, `mod`), a stepwise generator that needs the untyped emitter
first, every signature gains an arena parameter, and every call returns
the arena.

## Attribution (where the time goes)

**Method.** Three instruments, each limited: (1) V8 sampling profiles with
wasm functions identified by role (the untyped modules carry debug names;
the compiled modules do not, so the roles of function indices were read
from the wasm text: indices 9 and 10 begin with the range check `1024 <= p
<= 536870904 && p & 7 == 0` and are the guarded tag/field read helpers, 1
and 7 allocate and box, 26 and 27 are `listAppend` and `listDrop` by the
sizes, 24 and 25 are inferred to be `listLen` and `listFirst` by size only,
54 is a small type-dispatch predicate that calls 9, 56 and 57 are the
generated program bodies); (2) wasmtime fuel counts; (3) repeat counting
on the lifted programs (below). Samples are self time; tiny leaf functions
may be under-attributed.

**Compiled route, share of wasm self time (nqueens 8 / fannkuch-redux 7):**

| Role | nqueens 8 | fannkuch 7 | what would remove it |
|---|---|---|---|
| tag and field read helpers (fn 9, 10) | 24.5% | 25.6% | folding the redundant reloads of guarded reads; the same kind of fold found about half of guarded calls foldable on a record-heavy checker |
| allocation and boxing (fn 1, 7) | 10.5% | 19.4% | regions and uniqueness reuse; unboxed `i64` |
| list helpers (fn 24-27) | 15.6% | 12.3% | O(1) cons or a flat-array representation (the cost here is `listAppend`/`listDrop` copying) |
| type-dispatch predicate (fn 54) | 6.8% | 10.1% | the same representation work |
| generated bodies (fn 56, 57) | 33.8% | 20.1% | fuel and call overhead plus backend quality, not separable here |
| other | 8.8% | 12.5% | |

**Untyped lowering**: the allocator `$bump_val` (function `2`) is 25.3% of
self time on nqueens 9, 54.8% on fannkuch-redux 7, 66.6% on rbtree 20000;
`list_concat` is 9.5% on nqueens 9 and 5.1% on fannkuch; name comparison
(`$8`) 6.2% on rbtree 20000. The memory is a bump arena that is never
freed: 145 MB for nqueens 9, 1.37 GB for fannkuch-redux 8, 366 MB for
binary-trees 12.

**Gap to Rust, by what the instruments show.** compiled/Rust is 281x to
2786x in CPU time and 364x to 1855x in instructions (net of start-up): the
gap is mostly instruction count, not instruction speed. Within the
compiled output, 22% to 25% goes to checks on every value read, 10% to
19% to allocation and boxing, 12% to 16% to list copies. fannkuch-redux is
worse than nqueens by 5x in ratio because indexing is O(n) on lists and
every prefix reversal rebuilds the list; that is a representation cost,
not a code-generation cost.

**Next optimization, ranked by measured share on these programs** (the
share is an upper bound on the gain; none was applied): (1) the tag/field
read helpers, 22% to 26% — folding redundant reloads removes about half of
guarded calls on a record-heavy checker, so roughly 11% to 13% here if the
same fraction holds (NOT measured here); (2) allocation and boxing, 10% to
19% (regions, uniqueness reuse, unboxed `i64`); (3) list copy helpers,
12% to 16% (O(1) cons or flat arrays); (4) fuel and call overhead cannot
be separated and sit inside the 20% to 34% of generated bodies. This
ranking puts representation and memory work ahead of fuel reduction on
these programs; it does not support "fuel first", but the fuel share was
not isolated.

**Repeat counting.** A small interpreter of the lifted wire programs (the
ops these programs use) re-runs the benchmark input and counts every
`call` executed with no memo, the distinct (callee, canonical args) pairs
among them, and the calls whose body runs when each pair is memoised (a
hit skips the body and everything under it). Results agree with the wire
interpreter on the value of every row (asserted).

| Program, input | calls, no memo | distinct (callee, args) | share of calls that repeat |
|---|---|---|---|
| nqueens 6 | 3,071 | 2,739 | 10.8% |
| nqueens 8 | 62,099 | 49,369 | 20.5% |
| fannkuch-redux 6 | 51,021 | 21,830 | 57.2% |
| binary-trees 10 | 547,542 | 1,407 | 99.74% |
| rbtree 2000 | 34,837 | 33,037 | 5.2% |

(fannkuch-redux 7 and rbtree 20000 did not finish in the interpreter within
the session.) On binary-trees memoisation removes essentially all the work,
which is the work the Game forbids optimising away ("don't optimize away
the work"); it is reported as a data point, not a result. On fannkuch-redux
the repeats are the list helpers (`nth`, `setNth`, `takeN`, `dropN`)
called with the same small arguments, not repeated permutations.
Memoisation costs 2 to 3x with no repeats, so on rbtree and nqueens it
would lose; on binary-trees and fannkuch-redux it would win by the repeat
share. The arena route's interning is the same mechanism inside the
program: structurally equal nodes are one node, and it made binary-trees
34x slower than the untyped module, not faster, because the lookups cost
more than the allocations they save at this size.

## The call codec: per-step cost against state size

**Module and ABI.** The instrument is a module *generated by the pinned
rebuilt compiler* (3,576,344 B, seed-bootstrap build) from four
hand-written one-function RSCM sources (13 to 15 bytes each): `bytes ->
bytes` identity, `bytes -> i64` (`bytesLen`), `list i64 -> list i64`
identity, `list i64 -> i64` (`listLen`). Each is the generated invocation
decoder and outcome writer of the V1 ABI (`SourceInvocationV1`: tag 1,
fuel, argument count, typed values; `bytes` is tag 11, a list is tag 3
with one tagged word pair per element) with the V2 outcome packet (value
kind, body length, body), exactly the ABI the pinned runner checks.
Profile `bootstrap512` (public memory 8192 pages). Timed in node v26.12.0
on V8, `compile()` only, fresh instance per repeat, host copy of the
input and the instantiate time excluded (instantiate is in the last
column). Decode-only rows use the result `i64`, whose packet is 32 bytes,
so their time is the decoder plus O(1). Min of 21 repeats; load average
about 29.

| state (wire bytes) | bytes: decode ms | bytes: decode+write ms | bytes: write ms (diff) | list: decode ms | list: decode+write ms | list: write ms (diff) | instantiate ms (min) |
|---|---|---|---|---|---|---|---|
| 0 (0 / 0 elements) | 0.006 | 0.005 | -0.001 | 0.004 | 0.004 | -0.001 | 0.06 |
| 3000 (3000 / 187 elements) | 0.019 | 0.024 | 0.005 | 0.008 | 0.016 | 0.007 | 0.05 |
| 50000 (50000 / 3125 elements) | 0.077 | 0.179 | 0.102 | 0.063 | 0.099 | 0.036 | 0.07 |
| 800000 (800000 / 50000 elements) | 0.836 | 2.095 | 1.259 | 0.902 | 1.387 | 0.485 | 0.18 |
| 3000000 (3000000 / 187500 elements) | 3.088 | 8.161 | 5.073 | 3.452 | 5.475 | 2.024 | 0.56 |

per MB at 3 MB: bytes decode 1.03, write 1.69, round trip 2.72; list decode
1.15, write 0.67, round trip 1.83 ms/MB; at 800 KB: bytes round trip
2.10 ms, list 1.39 ms.

**Reading.** Decoder and writer are linear in the state with no visible
fixed cost above 0.01 ms. Per MB at 3 MB: bytes decode 1.03 ms, write
1.69 ms, round trip 2.72 ms; list of `i64` decode 1.15 ms, write 0.67 ms,
round trip 1.83 ms. At 800 KB the round trip is 2.10 ms (bytes) and
1.39 ms (list). The runtime's working bound was about 1 to 3 ms per MB
per step with a 3 ms ceiling at 1 MB: **the measurement falls inside the
bound** (1.8 to 2.7 ms/MB; 1.4 to 2.1 ms at 800 KB, under the 3 ms
ceiling; 3 MB costs 5.5 to 8.2 ms, over it). Instantiate is 0.05 to
0.9 ms and does not grow with the state.

**How far V1 carries.** It is the V1 invocation with the V2 outcome as the
pinned runner uses it, on a *generated* module. Not established: (1) the
candidate compiler module (4,851,154 B, 32768 pages) was **not driven**:
its `compile` returned the 16-byte `0x82` refusal (pointer 256) for the
two-argument compiler invocation and for six-argument all-`bytes`
invocations (three variants tried); its working six-slot invocation is
built by a prelude in the runtime adapter that was not read to the end.
(2) Only the state shapes `bytes` and `list i64` were timed, not records
or sums; nested state (the arena route's record of lists) was seen to
cost 21.8 MB of output at n=2000, not timed. (3) V2 is not established at
this head, so the writer measured is the one the rebuilt compiler
generates for the V2 packet the runner expects, not a frozen V2 writer.
(4) V8 only; a wasmtime check of the same modules was not made. (5) A
single machine under load.

## What was not measured

Zig, Koka, OCaml and Lean builds of the same programs (the comparison keeps
Rust as the reference language; the same suite's Koka column is measured
separately under `benchmarks/koka/`); pidigits performance runs
(correctness only: 30 and 10000 digits); the corpus programs on the wasm
routes (coverage rows stay "writable now" at READ level except the
typed-emission columns, which are measured); repeat counts for
fannkuch-redux 7 and rbtree 20000; the candidate compiler module of the
codec section; delivery numbers on an exclusive machine; Rust at the
Game's `target-cpu=ivybridge` flag (not valid on arm64).
