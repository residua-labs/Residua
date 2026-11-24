# PERF-RECORD — how to read docs/PERF-RECORD.tsv

Each version is meant to ship one performance record in the same
fixed form (the record form pinned by the suite rule), measured by the acceptance
procedure, audited, and kept unchanged afterwards; a later version is
compared row by row with every earlier record. Ratios to Koka are
reported, but the record's primary values are absolute, so versions
compare even if Koka changes.

Where a version's measurement run has not landed, the archive carries
the latest landed record and the gap is named in `release/GAPS.tsv`:
this archive carries the 0.1 record; 0.2 and 0.3 rows are pending.

## Fixed for every version

- Machine: GCP t2d-standard-4 (AMD EPYC, 4 vCPU, 16 GiB); the image
  family and kernel are recorded in the header. Two VMs per run.
- Reference: Koka 3.2.9 with the suite's pinned flags; the C
  (gcc) and Rust columns as that suite names them.
- Suite: the suite's rows — rbtree-kk, rbtree-ck, nqueens-kk,
  binarytrees-kk, deriv, cfold, plus the [qbe](GLOSSARY.md) and
  fixed-width variants it names — at the sizes and inputs it pins (rbtree-kk 4200000 as a
  machine word).
- Routes: native and wasm (emscripten/node versions as the suite pins).
- Rule: each row's printed value equals Koka's, or the row is a named
  refusal; a crashed or trapped run gives no time; each row reports the
  median of the pinned number of runs; the two VMs must agree within
  10 % or the row is re-run.

## What the TSV contains

Header keys: version tag, compiler head, stage word, layers on by
default, [seed](GLOSSARY.md) q, date, machine facts.

Then, per benchmark row and route: wall ms (median), peak RSS KiB, code
size bytes, value check, the VM1 and VM2 values, and Koka's same three
numbers.

Finally, the chain's own costs on the same machine:

- seed bootstrap: wall s and peak RSS of the committed seed recipe from
  a bare archive to the fixpoint
- self-compile: wall s and peak RSS of rsdc compiling the rsdc source
  and of rsc compiling the rsc source
- one compile-speed row: wall of compiling the largest benchmark source

## Procedure

The record is produced by the acceptance run on GCP, by the assigned
measurement run; an independent audit recomputes medians and geomeans
from the raw logs. The
cumulative per-version history is kept repository-side; each version's
own record ships in its archive.

