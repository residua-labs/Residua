# Stage-14274 CPU bootstrap

The two Wasm files in this directory are the seed cut from the fixed point at
`7aec17aa416092e45f595c0b13c607ff8120b812`. The public entries are `f779`
for rsdc at word 0 and `f1971` for rsc at construction word 14274. The S2
and S4 reports record the producer commands, the four fixed-point comparisons
and the original seed hashes. S4's result has SHA-256
`b0b7f28742905445b2d4bfc46c2200979130cbfd6259c219dcf79515d3504226`.

The two whole-module inputs in `sources/` are the exact RSD byte streams
from that run. They include generated runtime definitions from the original
assembly. Their hashes are in `SHA256SUMS`. The live member checks bind the
cut to 54 source references across the two roots, with 53 distinct files.
A changed source member requires a new cut. rsdc emits both RSCM inputs
during the run.

The recipe runs on two hosts. On a clean Linux x86-64 checkout with GCC, GNU
binutils and coreutils, Bash, curl and tar; or on a clean macOS arm64 account
with Apple clang and the base system (shasum, bsdtar), Bash, curl and tar.
Enter a shell using `env -i PATH=/usr/bin:/bin bash --noprofile --norc` and
run the following commands at the repository root. The commands fetch the
host's pinned WABT 1.0.42 asset and byte-pinned runtime sources. If cached,
verify them against the same hashes. WABT translates the Wasm executors into
C and the host's compiler builds them locally. All four compiler calls run
in the resulting CPU executables. Use a fresh output directory for each run.

Compile the first split unit at GCC `-O0`. Its large functions dominate
optimization time even when the generated file is below the size cutoff.

```bash
set -euo pipefail
export LC_ALL=C
seed=$PWD/bootstrap/seed/stage-14274
host=$PWD/reports/codex4-assign5-stage-word/Wasm2CHost.c
out=$PWD/out/bootstrap/stage-14274
case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)
        sha256() { sha256sum "$@"; }
        stat_size() { stat -c %s "$1"; }
        wabt_url=https://github.com/WebAssembly/wabt/releases/download/1.0.42/wabt-1.0.42-linux-x64.tar.gz
        wabt_sums=$seed/WABT-SHA256SUMS
        wabt_untar() { tar -xzf "$1" --strip-components=2 --wildcards '*/bin/wasm2c' '*/bin/wasm-validate'; }
        boot_id() { cat /proc/sys/kernel/random/boot_id; }
        platform_flags=-D_GNU_SOURCE
        exec_flags=(-fno-optimize-sibling-calls -frounding-math -fsignaling-nans)
        cc_accept() { cc --version | sed -n '1p' | grep -Fv clang; }
        ;;
    Darwin-arm64)
        sha256() { shasum -a 256 "$@"; }
        stat_size() { stat -f %z "$1"; }
        wabt_url=https://github.com/WebAssembly/wabt/releases/download/1.0.42/wabt-1.0.42-macos-arm64.tar.gz
        wabt_sums=$seed/WABT-MACOS-ARM64-SHA256SUMS
        wabt_untar() { bsdtar -xzf "$1" --strip-components=2 '*/bin/wasm2c' '*/bin/wasm-validate'; }
        boot_id() { ( PATH=/usr/bin:/bin:/usr/sbin:/sbin; sysctl -n kern.bootsessionuuid 2>/dev/null || sysctl -n kern.boottime ); }
        platform_flags=-D_DARWIN_C_SOURCE
        exec_flags=(-fno-optimize-sibling-calls -frounding-math)
        cc_accept() { cc --version | sed -n '1p' | grep -F clang; }
        ;;
    *) printf 'unsupported host: %s
' "$(uname -s)-$(uname -m)" >&2; exit 1;;
esac
for tool in lean elan lake node ocaml; do
    if command -v "$tool"; then printf 'unexpected tool: %s\n' "$tool" >&2; exit 1; fi
done
test -z "$(git status --porcelain --untracked-files=all)"
test ! -e "$out"
mkdir -p "$out"/{evidence,rebuilt,tools/runtime}
exec > >(tee "$out/evidence/run.log") 2>&1
git rev-parse HEAD
uname -a
boot_id
cc --version
cc_accept
printf 'bootstrap start %s\n' "$(date -u +%FT%TZ)"
( cd "$seed" && sha256 -c SHA256SUMS )
sha256 -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
sha256 -c "$seed/EXECUTOR-SHA256SUMS"
tools=$out/tools
runtime=$tools/runtime
curl -fsSL --retry 3 -o "$tools/wabt.tar.gz" "$wabt_url"
(
    cd "$tools"
    sed -n '1p' "$wabt_sums" | sha256 -c
    wabt_untar wabt.tar.gz
    sha256 -c "$wabt_sums"
)
while read -r hash name; do
    curl -fsSL --retry 3 -o "$runtime/$name" \
        "https://raw.githubusercontent.com/WebAssembly/wabt/ff0ef7e0009402740c805a9744c09b05be063e48/wasm2c/$name"
done < "$seed/WABT-RUNTIME-SHA256SUMS"
( cd "$runtime" && sha256 -c "$seed/WABT-RUNTIME-SHA256SUMS" )
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
    flags=("${exec_flags[@]}")
    sources=(generated/seed_*.c)
    if test -f generated/seed.c; then sources+=(generated/seed.c); fi
    for src in "${sources[@]}"; do
        if test "$src" = generated/seed_0.c; then
            level=-O0
        elif test "$(stat_size "$src")" -gt 16777216; then
            level=-O1
        else
            level=-O2
        fi
        printf '%s\0' "$level" "$src" "objects/$(basename "$src" .c).o"
    done | xargs -0 -n3 -P4 bash -ec '
        printf "compile %s %s %s\n" "$1" "$2" "$(date -u +%FT%TZ)"
        cc "$1" "${exec_flags[@]}" -I generated -I "$0" -c "$2" -o "$3"
    ' "$runtime"
    for unit in wasm-rt-impl wasm-rt-exceptions-impl wasm-rt-mem-impl; do
        cc -O2 "$platform_flags" -I generated -I "$runtime" -c "$runtime/$unit.c" -o "objects/$unit.o"
    done
    cc -O2 -std=c11 -Wall -Wextra -Werror "$platform_flags" -D_POSIX_C_SOURCE=200809L \
        "-DSEED_ENTRY=w2c_seed_$entry" "-DSEED_FRONTEND=$frontend" \
        "${flags[@]}" -I generated -I "$runtime" -c "$host" -o objects/host.o
    cc objects/*.o -lpthread -lm -o run
    sha256 run
)
build_cpu_executor rsdc f779 1 2>&1 | tee "$out/evidence/build-rsdc.log" &
front=$!
build_cpu_executor rsc f1971 0 2>&1 | tee "$out/evidence/build-rsc.log" &
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
( cd "$out/rebuilt" && sha256 -c "$seed/REBUILT-SHA256SUMS" )
( cd "$seed" && sha256 -c SHA256SUMS )
sha256 -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
sha256 -c "$seed/EXECUTOR-SHA256SUMS"

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
come from ASSIGN-5's S2 executor.

- S2 fixed-point report: `reports/codex4-assign5-stage-word/S2-ARENA.md` (repository-side)
- S4 seed-cut report: `reports/codex4-assign5-stage-word/S4-ARENA.md` (repository-side)

Between cuts, `check` (`lean --run bootstrap/seed/Check.rsd FRESH_OUT`, stock
Lean as the tool host) says whether this seed still builds the head's source
members to a compiler that reproduces itself, and `cut`
(`lean --run bootstrap/seed/Cut.rsd CHECK_OUT NEW_SEED_DIR`) writes the seed
of a head that check passed. A landing that changes a source member does not
cut the seed; the seed is cut again at each version's candidate.
