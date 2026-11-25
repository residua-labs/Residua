# Stage-14274 bootstrap on a wasm runtime

The two Wasm files in this directory are the seed cut from the fixed point at
`6d56d5b29ccc485253cc7ea9e7007927ebecb335`. The public entries are `f896`
for rsdc at word 0 and `f2615` for rsc at construction word 14274; the recipe
below reads them from `CUT.tsv`, which is the cut's record of itself. The
seed-recut check at that head recorded the four fixed-point comparisons; the
producer commands and their receipts are in reports/rel04/
(repository-side, not in this archive). From this cut the
wasm route compiles with the `narrow` layer as its default; the native
route stays 64-bit.

The two whole-module inputs in `sources/` are the exact RSD byte streams
from that run. They include generated runtime definitions from the original
assembly. Their hashes are in `SHA256SUMS`. The live member checks bind the
cut to 55 source references across the two roots, with 54 distinct files.
A changed source member requires a new cut. rsdc emits both RSCM inputs
during the run.

## The execution route

All four compiler calls run **in the seed's own Wasm form** on a pinned
wasmtime release through a small C host (`seed-host.c`, in this directory,
pinned by `SEED-HOST-SHA256SUMS`). There is no wasm-to-C translation and no C
compiler optimization of the seed anywhere in this recipe; the only host
compile is the import bridge itself.

Two fetched tools are pinned byte-exact, downloaded by the user rather than
shipped:

- **wasmtime v50.0.1 C API** (`WASMTIME-SHA256SUMS`): the release's
  `*-c-api` archives for Linux x86-64 and macOS arm64. The host compiles
  against the fetched headers and static `libwasmtime.a`.
- **binaryen version_133** (`BINARYEN-SHA256SUMS`): the release archives
  for the same two platforms. `wasm-opt` is used for exactly one
  encoding change: the seed modules carry *legacy* exception-handling
  instructions (the `try`/`catch` encoding browsers implemented first),
  which wasmtime does not implement — wasmtime's exceptions proposal is
  the current `exnref`/`try_table` encoding. `wasm-opt
  --translate-to-exnref` rewrites that one instruction form; it is a
  specified wasm→wasm recoding, not an optimization pass and not a
  different toolchain for the seed's semantics. The untranslated seed
  bytes are what `SHA256SUMS` pins; translation runs inside the recipe
  on already-verified input, and the recipe records the translated
  module's sha256 in the run log.

## The recipe

On a clean Linux x86-64 host with GCC, GNU binutils and coreutils, Bash,
curl and tar — or on macOS arm64 with clang, Bash, curl and tar — enter a
shell using `env -i PATH=/usr/bin:/bin bash --noprofile --norc` and run
the following commands at the archive root (the repository root in a
checkout). The commands fetch the two pinned releases and check them
against the sum files. Use a fresh output directory for each run.

```bash
set -euo pipefail
export LC_ALL=C
seed=$PWD/bootstrap/seed/stage-14274
host=$seed/seed-host.c
out=$PWD/out/bootstrap/stage-14274
platform=$(uname -s)-$(uname -m)
case "$platform" in
    Linux-x86_64)
        SHASUM=sha256sum
        binaryen_tar=binaryen-version_133-x86_64-linux.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-x86_64-linux-c-api.tar.xz
        LDL=-ldl ;;
    Darwin-arm64)
        SHASUM="shasum -a 256"
        binaryen_tar=binaryen-version_133-arm64-macos.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-aarch64-macos-c-api.tar.xz
        LDL= ;;
    *) printf 'unsupported host: %s\n' "$platform" >&2; exit 1 ;;
esac
for tool in lean elan lake node ocaml; do
    if command -v "$tool"; then printf 'unexpected tool: %s\n' "$tool" >&2; exit 1; fi
done
if test -d .git; then
    test -z "$(git status --porcelain --untracked-files=all)"
    git rev-parse HEAD
fi
test ! -e "$out"
mkdir -p "$out"/{evidence,rebuilt,translated,tools}
exec > >(tee "$out/evidence/run.log") 2>&1
uname -a
test ! -e /proc/sys/kernel/random/boot_id || cat /proc/sys/kernel/random/boot_id
cc --version
printf 'bootstrap start %s\n' "$(date -u +%FT%TZ)"
( cd "$seed" && $SHASUM -c SHA256SUMS )
$SHASUM -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
$SHASUM -c "$seed/SEED-HOST-SHA256SUMS"
rsdc_entry=$(awk -F'\t' '$1=="rsdc_entry"{print $2}' "$seed/CUT.tsv")
rsc_entry=$(awk -F'\t' '$1=="rsc_entry"{print $2}' "$seed/CUT.tsv")
test -n "$rsdc_entry" && test -n "$rsc_entry"
tools=$out/tools
curl -fsSL --retry 3 -o "$tools/$binaryen_tar" \
    "https://github.com/WebAssembly/binaryen/releases/download/version_133/$binaryen_tar"
curl -fsSL --retry 3 -o "$tools/$wasmtime_tar" \
    "https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.1/$wasmtime_tar"
grep " $binaryen_tar\$" "$seed/BINARYEN-SHA256SUMS" > "$tools/pins"
grep " $wasmtime_tar\$" "$seed/WASMTIME-SHA256SUMS" >> "$tools/pins"
( cd "$tools" && $SHASUM -c pins && tar -xf "$binaryen_tar" && tar -xf "$wasmtime_tar" )
wasmopt=$tools/binaryen-version_133/bin/wasm-opt
capi=$(printf '%s\n' "$tools"/wasmtime-v50.0.1-*-c-api)
"$wasmopt" --version

translate_module() (
    module=$1
    printf 'translate %s %s\n' "$module" "$(date -u +%FT%TZ)"
    "$wasmopt" --all-features "$seed/$module.wasm" --translate-to-exnref \
        -o "$out/translated/$module.wasm"
    ( cd "$out/translated" && $SHASUM "$module.wasm" )
)
translate_module rsdc &
front=$!
translate_module rsc &
back=$!
wait "$front"
wait "$back"

cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" \
    -c "$host" -o "$out/seed-host.o"
cc "$out/seed-host.o" "$capi/lib/libwasmtime.a" -lpthread -lm $LDL -o "$out/run"
$SHASUM "$out/run"
printf 'runtime executor built %s\n' "$(date -u +%FT%TZ)"

rebuild_root() (
    root=$1
    printf 'emit %s %s\n' "$root" "$(date -u +%FT%TZ)"
    "$out/run" rsdc "$rsdc_entry" "$out/translated/rsdc.wasm" \
        "$seed/sources/$root.rsd" "$out/rebuilt/$root.rscm" 0 cons |
        tee "$out/evidence/emit-$root.json"
    printf 'lower %s %s\n' "$root" "$(date -u +%FT%TZ)"
    "$out/run" rsc "$rsc_entry" "$out/translated/rsc.wasm" \
        "$out/rebuilt/$root.rscm" "$out/rebuilt/$root.wasm" 14274 cons |
        tee "$out/evidence/lower-$root.json"
    grep -qF '"tag":"0","status":"0","detail":"0"' "$out/evidence/emit-$root.json"
    grep -qF '"tag":"0","status":"0","detail":"0"' "$out/evidence/lower-$root.json"
    cmp "$seed/$root.wasm" "$out/rebuilt/$root.wasm"
)
rebuild_root rsdc &
front=$!
rebuild_root rsc &
back=$!
wait "$front"
wait "$back"
( cd "$out/rebuilt" && $SHASUM -c "$seed/REBUILT-SHA256SUMS" )
( cd "$seed" && $SHASUM -c SHA256SUMS )
$SHASUM -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
$SHASUM -c "$seed/SEED-HOST-SHA256SUMS"

# mutant control: a one-byte change in rsdc.wasm must be refused by the
# seed digest gate before any compiler call. Replay that gate — and only
# that gate — in a scratch seed copy; the recipe's `set -e` aborts the
# whole run at the same point, before translation, host build or calls.
cp -R "$seed" "$out/evidence/mutant"
printf '\x01' | dd of="$out/evidence/mutant/rsdc.wasm" bs=1 seek=64 conv=notrunc 2>/dev/null
code=0
( cd "$out/evidence/mutant" && $SHASUM -c SHA256SUMS ) \
    > "$out/evidence/mutant-check.log" 2>&1 || code=$?
test "$code" != 0
grep -q 'rsdc.wasm.*FAILED' "$out/evidence/mutant-check.log"
printf 'bootstrap complete %s seed_roundtrip=2/2 images=2/2 mutant_digest_exit=%s\n' \
    "$(date -u +%FT%TZ)" "$code"
```

Expect exit 0, two zero-status emissions, two zero-status lowerings, four
rebuilt hashes and two seed byte comparisons. The mutant control must
produce a nonzero digest-check exit while the scratch directory holds
only the copied seed files — refusal before any compiler call.
Byte comparisons and hashing are linear in
the files they read. The wasmtime C host keeps the import protocol of
the former executor host unchanged.

Per-call costs on the acceptance hosts: translating one module is a few
minutes of `wasm-opt`; the host's first call per module pays one wasmtime
module compile (~1 min) and caches the result as `<module>.cwasm`; the
compiler calls themselves dominate the wall and are recorded as
`wall_ns` in the evidence JSON.

Between cuts, `check` (`lean --run bootstrap/seed/Check.rsd FRESH_OUT`, stock
Lean as the tool host) says whether this seed still builds the head's source
members to a compiler that reproduces itself, and `cut`
(`lean --run bootstrap/seed/Cut.rsd CHECK_OUT NEW_SEED_DIR`) writes the seed
of a head that check passed. A landing that changes a source member does not
cut the seed; the seed is cut again at each version's candidate. The `check`
tool is a chain-internal instrument and keeps its own wasm2c executor route
(the `WABT-*-SHA256SUMS` and `EXECUTOR-SHA256SUMS` manifests in this
directory pin that route, which is repository-side and not the release's
route).
