# Wasm seed bootstrap

Use the [stage-14274 committed seed and CPU bootstrap](seed/stage-14274/README.md)
to rebuild both compilers. That recipe is the supported 0.1 route: it runs
on a clean Linux x86-64 with a C compiler and needs neither git nor any
language toolchain beyond what this archive ships.

## Older Z1 route (repository-side, not in 0.1)

The repository also carries an earlier Z1 bootstrap: committed wasm
executors recompile their sources under Node's stock Wasm runtime, with
`bootstrap/seed/manifest.json` binding seeds, entry ABIs and provenance
and `bootstrap/sources.json` binding the source closure. Its runner
scripts (Node `.cjs` collectors) are repository-only and are not shipped
in the 0.1 archive, and the `node` toolchain they need is out of scope
here. The stage-14274 recipe above is the bootstrap this release
verifies.

## The 2 C host bridges

The pair of `Wasm2CHost.c` files ships in the archive, and they are not
interchangeable. The recipe's `host=` variable and
`EXECUTOR-SHA256SUMS` pin
`reports/codex4-assign5-stage-word/Wasm2CHost.c`: the execution-layer
adapter for the stage-word ABI the stage-14274 seed exports
(`SEED_FRONTEND` selects the compiler entry; it owns the arena cursor
and pointer-extent checks). `bootstrap/Wasm2CHost.c` is the stock
wasm2c host glue written for the earlier seed ABI (`SEED_WORDS`
arity, madvise/hugepage hints) — it ships as the older route's
companion and plays no role in the stage-14274 recipe; substituting
one for the other fails to compile.

closure_claim = 0
