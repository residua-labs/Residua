# Stage-14274 CPU bootstrap

The two Wasm files in this directory are the seed cut from the fixed point at
`3f879c7d9424496b69c9a8425e1fcd343c962b82`. The public entries are `f794`
for rsdc at word 0 and `f2110` for rsc at construction word 14274. The seed-recut check
at that head recorded the four fixed-point comparisons; the producer
commands and their receipts are kept repository-side.

The two whole-module inputs in `sources/` are the exact RSD byte streams
from that run. They include generated runtime definitions from the original
assembly. Their hashes are in `SHA256SUMS`. The live member checks bind the
cut to 55 source references across the two roots, with 54 distinct files.
A changed source member requires a new cut. rsdc emits both RSCM inputs
during the run.

On a clean Linux x86-64 checkout — or the extracted source archive — with
GCC, GNU binutils and coreutils, Bash, curl and tar, enter a shell using
`env -i PATH=/usr/bin:/bin bash --noprofile --norc` and run the following
commands at the tree root (the repository root, or the archive's extraction
root; no `.git` is needed — the pinned manifests carry the source identity).
The commands
fetch pinned WABT 1.0.42 and runtime sources. If cached, verify them against
the same hashes. WABT translates the Wasm executors into C and GCC builds
them locally. All four compiler calls run in the resulting CPU executables.
Use a fresh output directory for each run.

Compile the first split unit at GCC `-O0`. Its large functions dominate
optimization time even when the generated file is below the size cutoff.

```bash
set -euo pipefail
export LC_ALL=C
seed=$PWD/bootstrap/seed/stage-14274
host=$PWD/reports/codex4-assign5-stage-word/Wasm2CHost.c
out=$PWD/out/bootstrap/stage-14274
test "$(uname -s)-$(uname -m)" = Linux-x86_64
for tool in lean elan lake node ocaml; do
    if command -v "$tool"; then printf 'unexpected tool: %s\n' "$tool" >&2; exit 1; fi
done
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    test -z "$(git status --porcelain --untracked-files=all)"
fi
test ! -e "$out"
mkdir -p "$out"/{evidence,rebuilt,tools/runtime}
exec > >(tee "$out/evidence/run.log") 2>&1
git rev-parse HEAD 2>/dev/null || sha256sum "$seed/SOURCE-MEMBERS-SHA256SUMS"
uname -a
cat /proc/sys/kernel/random/boot_id
cc --version
cc --version | sed -n '1p' | grep -Fv clang
printf 'bootstrap start %s\n' "$(date -u +%FT%TZ)"
( cd "$seed" && sha256sum -c SHA256SUMS )
sha256sum -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
sha256sum -c "$seed/EXECUTOR-SHA256SUMS"
tools=$out/tools
runtime=$tools/runtime
curl -fsSL --retry 3 -o "$tools/wabt.tar.gz" \
    https://github.com/WebAssembly/wabt/releases/download/1.0.42/wabt-1.0.42-linux-x64.tar.gz
(
    cd "$tools"
    sed -n '1p' "$seed/WABT-SHA256SUMS" | sha256sum -c
    tar -xzf wabt.tar.gz --strip-components=2 --wildcards '*/bin/wasm2c' '*/bin/wasm-validate'
    sha256sum -c "$seed/WABT-SHA256SUMS"
)
while read -r hash name; do
    curl -fsSL --retry 3 -o "$runtime/$name" \
        "https://raw.githubusercontent.com/WebAssembly/wabt/ff0ef7e0009402740c805a9744c09b05be063e48/wasm2c/$name"
done < "$seed/WABT-RUNTIME-SHA256SUMS"
( cd "$runtime" && sha256sum -c "$seed/WABT-RUNTIME-SHA256SUMS" )
"$tools/wasm2c" --version
"$tools/wasm-validate" "$seed/rsdc.wasm"
"$tools/wasm-validate" "$seed/rsc.wasm"

build_cpu_executor() (
    module=$1
    entry=$2
    frontend=$3
    mkdir -p "$out/$module"/{generated,objects}
    cd "$out/$module"
    "$tools/wasm2c" "$seed/$module.wasm" -n seed --num-outputs=128 -o generated/seed.c
    test "$(grep -Fc "w2c_seed_$entry(" generated/seed.h)" = 1
    for i in {0..127}; do test -s "generated/seed_$i.c"; done
    flags=(-fno-optimize-sibling-calls -frounding-math -fsignaling-nans)
    sources=(generated/seed_*.c)
    if test -f generated/seed.c; then sources+=(generated/seed.c); fi
    for src in "${sources[@]}"; do
        if test "$src" = generated/seed_0.c; then
            level=-O0
        elif test "$(stat -c %s "$src")" -gt 16777216; then
            level=-O1
        else
            level=-O2
        fi
        printf '%s\0' "$level" "$src" "objects/$(basename "$src" .c).o"
    done | xargs -0 -n3 -P4 bash -ec '
        printf "compile %s %s %s\n" "$1" "$2" "$(date -u +%FT%TZ)"
        cc "$1" -fno-optimize-sibling-calls -frounding-math -fsignaling-nans \
            -I generated -I "$0" -c "$2" -o "$3"
    ' "$runtime"
    for unit in wasm-rt-impl wasm-rt-exceptions-impl wasm-rt-mem-impl; do
        cc -O2 -D_GNU_SOURCE -I generated -I "$runtime" -c "$runtime/$unit.c" -o "objects/$unit.o"
    done
    cc -O2 -std=c11 -Wall -Wextra -Werror -D_GNU_SOURCE -D_POSIX_C_SOURCE=200809L \
        "-DSEED_ENTRY=w2c_seed_$entry" "-DSEED_FRONTEND=$frontend" \
        "${flags[@]}" -I generated -I "$runtime" -c "$host" -o objects/host.o
    cc objects/*.o -lpthread -lm -o run
    sha256sum run
)
build_cpu_executor rsdc f794 1 2>&1 | tee "$out/evidence/build-rsdc.log" &
front=$!
build_cpu_executor rsc f2110 0 2>&1 | tee "$out/evidence/build-rsc.log" &
back=$!
wait "$front"
wait "$back"
printf 'C executors built %s\n' "$(date -u +%FT%TZ)"

rebuild_root() (
    root=$1
    printf 'emit %s %s\n' "$root" "$(date -u +%FT%TZ)"
    "$out/rsdc/run" rsdc "$seed/sources/$root.rsd" "$out/rebuilt/$root.rscm" 0 cons |
        tee "$out/evidence/emit-$root.json"
    printf 'lower %s %s\n' "$root" "$(date -u +%FT%TZ)"
    "$out/rsc/run" rsc "$out/rebuilt/$root.rscm" "$out/rebuilt/$root.wasm" 14274 cons |
        tee "$out/evidence/lower-$root.json"
    "$tools/wasm-validate" "$out/rebuilt/$root.wasm"
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
( cd "$out/rebuilt" && sha256sum -c "$seed/REBUILT-SHA256SUMS" )
( cd "$seed" && sha256sum -c SHA256SUMS )
sha256sum -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
sha256sum -c "$seed/EXECUTOR-SHA256SUMS"

cp "$seed/rsdc.wasm" "$out/evidence/corrupt.wasm"
printf '\0' >> "$out/evidence/corrupt.wasm"
code=0
cmp -s "$out/evidence/corrupt.wasm" "$out/rebuilt/rsdc.wasm" || code=$?
test "$code" = 1
rm "$out/evidence/corrupt.wasm"
printf 'bootstrap complete %s seed_roundtrip=2/2 images=2/2 changed_wasm_cmp_exit=%s\n' \
    "$(date -u +%FT%TZ)" "$code"
```

Expect exit 0, two zero-status emissions, two zero-status lowerings, four
rebuilt hashes and two seed byte comparisons. The altered-Wasm control
must produce comparison exit 1. Byte comparisons and hashing are linear in
the files they read. The C runtime bridge and pinned acquisition inputs
come from the executor named in `EXECUTOR-SHA256SUMS`. Fixed-point and
seed-cut reports are kept repository-side.

Between cuts, repository-side drivers — not shipped in the archive —
maintain the seed: `check` (`lean --run bootstrap/seed/Check.rsd
FRESH_OUT`, stock Lean as the tool host) says whether this seed still
builds the head's source members to a compiler that reproduces itself,
and `cut` (`lean --run bootstrap/seed/Cut.rsd CHECK_OUT NEW_SEED_DIR`)
writes the seed of a head that check passed. A landing that changes a
source member does not cut the seed; the seed is cut again at each
version's candidate.
