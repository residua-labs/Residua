# VERIFY-RELEASE — checking a 0.3 release candidate

What a stranger can check with only the release files, `sha256sum`,
`cmp`, `tar`, `sed`, `awk`, `grep` and `diff`. All digests below are
sha256 (FIPS 180-4). The shipped digest tables are
`bootstrap/seed/stage-14274/SHA256SUMS` (seeds and whole-module
sources), `…/SOURCE-MEMBERS-SHA256SUMS` (the 54 source members),
`…/SEED-HOST-SHA256SUMS` (the C host bridge `seed-host.c`),
`…/REBUILT-SHA256SUMS` (the recipe's four products),
`…/WASMTIME-SHA256SUMS` and `…/BINARYEN-SHA256SUMS` (pinned fetches the
user downloads), `…/CUT.tsv` (cut
identity, entries and [seed](GLOSSARY.md) digests) and `docs/SPECS.md` (the
S/W/B/D rows). The repository-side artifact, source-role and build-input
tables do not ship and are named only as citations; `release/BUILD-INPUTS.tsv`
carries path inventories, not digests. For 0.3 the checkable surface
is the seed and the scm formats only (the third-party check; `release/MANIFEST.md`). This
document will change in later versions (0.3+).

## 1. Archive digest and extraction

The archive's sha256 travels beside it:

```sh
sha256sum -c rsd-src.tar.sha256    # expect: rsd-src.tar: OK
```

The archive writes its members at the top level (`bootstrap/`,
`release/`, `lib/`, `rsdc/`, `rsc/`, …) with no leading directory —
extract into a fresh directory so the tree does not mix with other
files:

```sh
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
```

All remaining commands run at this extraction root. The shipped member
list can be cross-checked against the build-input inventory
(`release/BUILD-INPUTS.tsv`, shipped): the `release-source-archive`
rows minus the two recipe inputs that stay repository-side
(`release/SOURCE-ROLES.tsv` and
`reports/release-readiness-r1/SourceArchive.rsd`), deduplicated
(`release/SHIP-RULES.tsv` is recorded twice — once as a shipped
member, once as a recipe input), must equal `tar tf`:

```sh
awk -F'\t' '$1 == "release-source-archive" { print $2 }' \
    release/BUILD-INPUTS.tsv \
  | grep -vx -e release/SOURCE-ROLES.tsv \
             -e reports/release-readiness-r1/SourceArchive.rsd \
  | sort -u > /tmp/archive.want
tar tf ../rsd-src.tar | sort > /tmp/archive.have
diff /tmp/archive.want /tmp/archive.have   # expect: no output
```

## 2. Seed digests

```sh
cd bootstrap/seed/stage-14274
sha256sum -c SHA256SUMS                  # the two seeds + two whole-module sources
cd -                                   # back to the extraction root
sha256sum -c bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS   # all 54 compiler source members
sha256sum -c bootstrap/seed/stage-14274/SEED-HOST-SHA256SUMS        # the C host bridge
```

(`SHA256SUMS` lists seed-directory-relative paths; the member and
host manifests list root-relative paths.)

Expected: every line `OK`. The seed pair is `rsdc.wasm`
`1aeacfb6b097…dbc6be75` and `rsc.wasm` `b7db967608fe…0b2e90`
(`stage-14274/SHA256SUMS`). The pinned fetch manifests
(`WASMTIME-SHA256SUMS`, `BINARYEN-SHA256SUMS`) are checked against the
downloaded payloads inside the recipe (`stage-14274/README.md`).

## 3. Member-to-bundle assembly

The recipe compiles the two whole-module sources
`bootstrap/seed/stage-14274/sources/{rsdc,rsc}.rsd`, not the 54
members directly. Each bundle section is named
`RscSourceModule_<member sha256>` where the sha256 is the member's
own digest in `SOURCE-MEMBERS-SHA256SUMS` — that naming is the
member-to-bundle link. The cut records 55 section references across
the two roots over 54 distinct members — `lib/Tarjan.rsd` is a
section of both bundles.

Check that every member digest appears as a section marker in the
bundles:

```sh
d=bootstrap/seed/stage-14274
awk '{ print $1 }' "$d/SOURCE-MEMBERS-SHA256SUMS" | sort > /tmp/members.want
cat "$d/sources/rsdc.rsd" "$d/sources/rsc.rsd" \
  | grep -o 'RscSourceModule_[0-9a-f]\{64\}' \
  | sed 's/.*RscSourceModule_//' | sort -u > /tmp/members.have
diff /tmp/members.want /tmp/members.have    # expect: no output
```

And that the member files themselves digest to the same values:

```sh
sha256sum -c "$d/SOURCE-MEMBERS-SHA256SUMS"    # expect: every line OK
```

The generated runtime definitions the assembler inserts
(`def runtimeSourcePart*` / `runtimeReuseSourcePart*` /
`runtimeAllocSourcePart*` plus the `…Wire` lists, generated from
`lib/rt/` members) are pinned by the whole-source digests in
`SHA256SUMS`; their derivation is the compiler's own encoding,
exercised end-to-end by the seed round-trip in the next section —
the compilers built from these sources reproduce the committed
executors byte-for-byte. Per-section order and span digests are
recorded in the check's assembly receipts, repository-side.

## 4. Seed reproduction (the strong check)

Run the seed recipe in a clean environment (`env -i
PATH=/usr/bin:/bin`) on Linux x86-64 or macOS arm64 and compare the
rebuilt
`rsdc.wasm`/`rsc.wasm` to the committed seeds — byte-equal is the
closure (`stage-14274/README.md`; the clean-environment run is
recorded repository-side — the stage-2/stage-3 fixed-point run of
this cut is the `SEED-RECUT` check named in `CUT.tsv`). The recipe
compiles one C file — the wasmtime host bridge `seed-host.c` — and
runs the seed's own Wasm form on the pinned wasmtime; there is no
wasm-to-C translation and no C optimizer over the seed.

## 5. scm formats

The scm layer's binary interface is RSCM: bytes begin
`52 53 43 4d` + a version byte. The recipe's emitter writes the v1
header `[82, 83, 67, 77, 1]` (`rsdc/Compile.rsd`, the `EmitResult`
writer; the shipped `rsc` reads it at `rsc/rsc.rsd`
`compileWithLayers`/`eatAll`), so the rebuilt `.rscm` products
(`REBUILT-SHA256SUMS`) are v1:

```sh
od -A x -t x1 -N 5 "$out/rebuilt/rsc.rscm"   # expect 52 53 43 4d 01 (after §4, in the recipe's output dir)
```

The runtime dialect is a separate extension `52 53 43 4d 127 01`
(`lib/RuntimeIR.rsd`). The scm language's text surface (`.scm`
files, the named `printScm`/`parseScm` view) is repository-only in
0.3.

## 6. What is NOT checkable in 0.3

No compiled dispatcher binary, no modules, no application suite, no
proof checking — their checks belong to a later line
(`release/GAPS.tsv`; the proof-certificate check does not apply: 0.3
ships no proof checking). The `rsd` build tool ships as sources whose
build closure is partly repository-side (`docs/BUILD.md`), so building
the tool is not checkable from the archive either. The shipped
specification texts are pinned Lean 4.14/rsd sources — `theorem`
declarations in them are spec text, not checked claims;
`semantics/Effect/AdmissionNF.lean` ships for audit and its imports
are repository-side (`release/GAPS.tsv`).

## 7. Further checkable surfaces

The typed content address (q format v1) is checkable:
`release/checks/qformat/README.md` recomputes six published q vectors and
two planted controls with `sha256sum` alone — `q(kind, c)` =
`SHA-256("<kind> <len>\0" ++ c)`, and a digest stays raw `SHA-256` for
interop. The vector files are generated by one `printf` command each
(the README's §0). Expected outputs are in
`release/checks/qformat/VECTORS.tsv`.
The specification is `docs/QFORMAT.md` / `QFORMAT.zh-CN`.

The `rsd` tool's check suite ships at `release/checks/rsd-tool/` —
`README.md` there gives the planted-row protocol; its `.rsd` programs
run under stock Lean 4.14 as a check tool.
