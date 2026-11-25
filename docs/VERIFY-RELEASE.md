# VERIFY-RELEASE — checking a 0.4 release archive

What a reader or automated agent can check with only the release files,
`sha256sum` (`shasum -a 256` on macOS), `cmp`, `tar`, `sed`, `awk`,
`grep` and `diff` — plus a C11 toolchain and `curl` for the full
bootstrap and example run. All digests below are SHA-256 (FIPS 180-4).

The shipped digest tables under `bootstrap/seed/stage-14274/` are:
- `SHA256SUMS` — the two committed [seed](GLOSSARY.md) modules and the two whole-module source snapshots
- `SOURCE-MEMBERS-SHA256SUMS` — the 54 compiler source members
- `SEED-HOST-SHA256SUMS` — the C11 host bridge `seed-host.c`
- `REBUILT-SHA256SUMS` — the recipe's four rebuilt outputs (`rsdc.rscm`, `rsc.rscm`, `rsdc.wasm`, `rsc.wasm`)
- `WASMTIME-SHA256SUMS` and `BINARYEN-SHA256SUMS` — the pinned runtime and `wasm-opt` archives downloaded by the recipe
- `CUT.tsv` — cut identity, entry ordinals (`f896` for `rsdc`, `f2615` for `rsc` at construction word `14274`) and seed digests

Specification digests are listed in `docs/SPECS.md`, and the typed
content-address checks ship under `release/checks/qformat/`.

## 1. Archive digest and extraction

The archive's SHA-256 travels beside it:

```sh
sha256sum -c rsd-src.tar.sha256    # macOS: shasum -a 256 -c rsd-src.tar.sha256
```

The archive writes its members at the top level (`bootstrap/`,
`release/`, `lib/`, `glue/`, `examples/`, `rsdc/`, `rsc/`, …) with no
leading directory. Extract into a fresh directory outside any `.git`
tree:

```sh
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
```

All remaining commands run at this extraction root. Cross-check the
member list against `release/BUILD-INPUTS.tsv`: the
`release-source-archive` rows minus the two repository-side recipe
inputs (`release/SOURCE-ROLES.tsv` and
`reports/release-readiness-r1/SourceArchive.rsd`), deduplicated, must
equal `tar tf`:

```sh
awk -F'\t' '$1 == "release-source-archive" { print $2 }' \
    release/BUILD-INPUTS.tsv \
  | grep -vx -e release/SOURCE-ROLES.tsv \
             -e reports/release-readiness-r1/SourceArchive.rsd \
  | sort -u > /tmp/archive.want
tar tf ../rsd-src.tar | sort > /tmp/archive.have
diff /tmp/archive.want /tmp/archive.have   # expect: no output
```

## 2. Seed and host digests

```sh
( cd bootstrap/seed/stage-14274 && sha256sum -c SHA256SUMS )
sha256sum -c bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS
sha256sum -c bootstrap/seed/stage-14274/SEED-HOST-SHA256SUMS
```

Expected: every line `OK`. In 0.4:
- `rsdc.wasm`: `845b99efab72a62a022c54985ca3ca8225a386b2e79214c2c96a59730cbfa1c9` (entry `f896`)
- `rsc.wasm`: `b52b07d1009f215e7102c67ae683bf6d9c31692857bf14cbff6615e0a6a959db` (entry `f2615`, word `14274`)
- `sources/rsdc.rsd`: `e330441bb72816f258043672f411ab0787958560b98fd89023616804d7fabbe3`
- `sources/rsc.rsd`: `ae029fc492f0a580673200196416f1ea67e06458a1662d8714bd2879b1777780`
- `seed-host.c`: `ea7a4e2e11727712abd538489e09dcf6f4852e9c0e76250e4742bfce5935fd8e`

### What changed in the 0.4 seed host

`lib/RscBase.rsd` emits an immutable `__heap_base` WebAssembly global
above closed static objects in the data segment when that segment is
present (`765288` in `rsdc.wasm`, `603704` in `rsc.wasm`, where
`[65536, __heap_base)` holds static ground objects). The 0.4
`seed-host.c` reads and validates `__heap_base` before writing input,
using that address for capacity, the initial allocation cursor and
live-byte counters; modules without `__heap_base` retain base `65536`.

## 3. Member-to-bundle assembly

The recipe compiles `bootstrap/seed/stage-14274/sources/{rsdc,rsc}.rsd`.
Each bundle section is wrapped in `RscSourceModule_<member sha256>`
markers matching `SOURCE-MEMBERS-SHA256SUMS` (55 section references
across 54 distinct source members; `lib/Tarjan.rsd` appears in both):

```sh
d=bootstrap/seed/stage-14274
awk '{ print $1 }' "$d/SOURCE-MEMBERS-SHA256SUMS" | sort > /tmp/members.want
cat "$d/sources/rsdc.rsd" "$d/sources/rsc.rsd" \
  | grep -o 'RscSourceModule_[0-9a-f]\{64\}' \
  | sed 's/.*RscSourceModule_//' | sort -u > /tmp/members.have
diff /tmp/members.want /tmp/members.have    # expect: no output
```

## 4. Seed reproduction and measured 0.4 timings

Run the recipe in `bootstrap/seed/stage-14274/README.md` under
`env -i PATH=/usr/bin:/bin bash --noprofile --norc` on Linux x86-64 or
macOS arm64. It fetches pinned `wasmtime` v50.0.1 and `binaryen`
`version_133` (`wasm-opt --translate-to-exnref`), verifies their SHA-256
pins, compiles `seed-host.c`, rebuilds both compilers in Wasm, checks
all four `REBUILT-SHA256SUMS` digests (`rsdc.rscm`
`fed8efe09d739abae6d74c8e7e7fdabc1923e269c8365daa67f2808b62f623f2`,
`rsc.rscm`
`5c6f807409fb3bbb18755e9fc2902adc59d25a5b63f054670ebfe714fecb6d2b`,
and byte-identical `rsdc.wasm` and `rsc.wasm`), and verifies that a
1-byte seed mutation is refused before any compiler call.

Measured 0.4 clean-archive acceptance runs:
- **Linux x86-64**: compiler rebuild `105 s`, full recipe including
  `examples/app04` compilation and 16 verification cases `193 s`, peak
  process RSS `5,978,144 KiB`, 4/4 seed comparisons, 16/16 `app04` cases.
- **macOS arm64**: compiler rebuild `191 s`, full recipe `337 s`, peak
  process RSS `6,058,592 KiB`, 4/4 seed comparisons, 16/16 `app04` cases.

## 5. End-to-end program compilation and execution (`examples/app04`)

Using the Quick start commands in [`README.md`](../README.md), the
rebuilt compilers and the C11 `Proc` host (`glue/host/procwt.c`) compile
and run the three-module CLI `examples/app04/{Stats,Table,Main}.rsd`
(with `lib/Proc{Bytes,,9}.rsd` and `glue/std/{Str,Proc,Args,Files}.rsd`):
- `rsdc` discovers `main` dynamically (`f151`) via `\0RSDC-ENTRIES\n`;
- `rsdc` and `rsc` emit deterministic `app04.rscm` and `app04.wasm`;
- `procwt` executes `app04.wasm`, reading an input file of floating-point
  numbers, computing `count`, `min`, `max`, `mean` and population
  `variance` with `Float`, and writing a formatted `String` summary
  table to an output file (verified across 16 cases up to 100,000 lines
  against stock Lean 4.14.0).

## 6. RSCM header and further checkable surfaces

- **RSCM v1 header**: `od -A x -t x1 -N 5 "$out/rebuilt/rsc.rscm"`
  prints `52 53 43 4d 01` (`RSCM` + version `1`).
- **Typed content address ([q](GLOSSARY.md) format v1)**:
  `release/checks/qformat/README.md` recomputes six published vectors
  and two negative controls against `release/checks/qformat/VECTORS.tsv`
  using `printf` and `sha256sum`.
- **`rsd` tool planted-row checks**: `release/checks/rsd-tool/README.md`
  runs under stock Lean 4.14.0 where a Lean toolchain is installed.

## 7. Open limits in 0.4

See `release/GAPS.tsv` for what is not runnable from this archive alone:
building `rsd`'s full native compiler worker without repository-side
`.lean` glue, `lake build` on `lean/nf-compose/` without `../hyper`,
`semantics/Effect/AdmissionNF.lean`'s repository-side imports, separate
`RMOD1` compilation of cross-module `Proc`/`Float` programs in a C-only
shell without `import` stripping, and proof checking (`R-CIC`).
