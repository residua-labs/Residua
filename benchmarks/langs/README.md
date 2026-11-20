# benchmarks/langs — vendored upstream suites for the reference columns

The reference-language columns of the performance record of the release 0.1: the
suite programs — rbtree, rbtree-ck, nqueens, cfold, deriv, binarytrees —
compiled and run under the record's rules (1 VM,
a pinned core, timecell median of 5, whole-process wall, peak RSS,
code bytes) in every language the pinned third-party suites ship them in.

## Sources (vendored verbatim, unmodified)

- `src/koka/test/bench/{cpp,haskell,java,ocaml,swift}/` — the Perceus
  suite from `koka-lang/koka` commit `facb7932ce6871fdb063f762a304bd8238f35fba`
  (tag `v3.2.9`, the Koka column's own pin). 6 programs per language;
  `java/rbtreeck.java` keeps its upstream name.
- `src/lean4/tests/bench/` — `binarytrees.lean`, `const_fold.lean` (the
  suite's cfold), `deriv.lean`, `rbmap.lean` (rbtree),
  `rbmap_checkpoint.lean` (rbtree-ck), with their `.args` and
  `.expected.out`, from `leanprover/lean4` tag `v4.14.0` commit
  `410fab7284703f41660ca2454218dcca9b2ec896`. The Lean column has no
  nqueens program (none in the pinned suite): an empty cell.
- Rust: `benchmarks/rust/{rbtree,rbtreeck,nqueens,binarytrees,cfold,deriv}.rs`
  in this directory's parent — the reference ports the comparison cites
  (rustc `-C opt-level=3 -C codegen-units=1`); not vendored again.

## Run

The measurement job runs on 1 VM: it installs the
pinned toolchains under `$LANGS_STATE/toolchains` (versions recorded per
run in `pins.txt`), compiles every (language, program) pair, then
measures serially: `timecell.c` from `benchmarks/koka/`, 5 reps on a
pinned core, `ulimit -s unlimited`, 1 value check per cell (the
program's printed numbers against the suite's canonical values). Cells
and raw reps land in `$LANGS_STATE/<runtag>/cells/` and are copied back.
2 runs on 2 VMs; a cell differing by more than 10 percent between
them is re-run.

`state/` is generated and untracked. Never commit a build output,
a toolchain, or a downloaded archive. closure_claim = 0.
