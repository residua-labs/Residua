# Wasm seed bootstrap

Use the [stage-14274 committed seed and CPU bootstrap](seed/stage-14274/README.md)
to rebuild both current compilers.

## Pinned seed bootstrap

The bootstrap follows the seed model named in TASK: committed Wasm compilers
rebuild their sources, and the second and third stages must be byte-identical.
Node's stock Wasm runtime is the default executor; WABT's `wasm2c`, its runtime,
and the system C compiler provide a second executor. All compiler algorithms
remain in the Wasm modules. Neither executor uses Lean or OCaml.

`seed/manifest.json` binds each seed, its entry ABI, its source files and its
provenance. `sources.json` binds the current rsdc source closure, ordered byte
slices, and its entry index. These slices are metadata from the existing
`CI.SourceBundle` header reader and rsdc's existing declaration ordering. The
bootstrap verifies the source hashes before slicing; it has no source parser.
A source edit requires regenerating this metadata with those same functions.

The command is `node bootstrap/Bootstrap.cjs OUT`, with OUT below `out/`.
For a clean rebuild from an existing checkout, run:

```sh
git clone --shared --no-hardlinks . out/z1/clean-checkout &&
cd out/z1/clean-checkout &&
node bootstrap/Bootstrap.cjs out/z1/clean-chain
```

The bootstrap records the commit and whether the checkout was clean when it
started. The collector requires a clean checkout for production-seed rows.
For mini timings append `--max-load 3`: the bootstrap refuses
`bootstrap_timing_load` before running any compiler unless the 1-minute load
is below 3. The host timing gate must also hold the exclusive measurement lock.
Each stage emits rsdc's RSCM with the preceding rsdc, lowers it with the
preceding rsc, and rebuilds rsc with that same rsc. Until C1 accepts rsc's
source closure, the latter input is `seed/rsc.rscm`: the temporary input and
its producer are recorded explicitly. At C1 this edge is replaced by rsdc's
output and the seed is cut again.

The normal command refuses `bootstrap_seed_source_changed` when a compiler
source differs from its cut. `--refresh` permits rebuilding changed rsdc
sources and produces candidates under OUT; it never overwrites the committed
seeds. `--step N:emit-rsdc`, `N:lower-rsdc`, or `N:lower-rsc` runs one bounded
cell. Existing predecessor receipts must match all source, seed and executor
hashes. `--check` only checks inputs; `--verify` checks the completed stages.
`--runner wasm2c` selects the C executor. Each compiler process has a 50 second
wall limit; a host gate supplies the enclosing resource lease.

The full command records every stage, stage-2/stage-3 equality for both
compilers and rsdc's RSCM, and equality with the seed on unchanged sources.
An explicit refresh can have a different seed hash; it must still reach the
byte fixpoint before a separate commit replaces the blobs and manifest.

`--seed-manifest PATH` validates a candidate cut without modifying `seed/`.
PATH is relative to the repository; the record marks `candidate_seed: true`
and binds that manifest and its blobs. The same three-stage and seed-equality
checks apply. This is also the explicit recovery route when an older seed
refuses a compiler source upgrade: record the candidate producer, validate
its fixed point, then commit the new seed as a separate cut.

`node bootstrap/CollectStaged.cjs OUT REPORT` rechecks the nine receipts,
their input and output hashes, predecessor edges, and all three equalities
without running compilers. `--artifacts DIRECTORY` replays a preserved tree
of the recorded bytes after sources or the committed seed have changed.
The runtime binary is a recorded remote-host pin; the collector does not
substitute its own host's executable for that pin.

`node bootstrap/CollectSeedLink.cjs OUT REPORT --artifacts DIRECTORY` replays
the staged records and binds the current seed and source hashes to both
stage-1 outputs. Its report names the exact source, RSCM and Wasm objects for
SOURCE-CERT and Validate. Byte equality alone does not supply either
certificate: the command currently exits 1 with
`bootstrap_seed_certificates_pending`, even when every byte link holds.
The certification owners must check those exact objects. At C1 the temporary
rsc RSCM is replaced, the seed is re-cut and these links are regenerated.

This adds no compiler pass or semantic edge to source -> RSCM -> Wasm. The
ABI adapters and byte comparisons are host observations, not proofs of those
edges. There are no new theorems; `closure_claim = 0` throughout. C1's missing
rsdc -> rsc-source edge remains visible in every bootstrap record.
