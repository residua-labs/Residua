# Audit report — MST-NF composition theorems

The shipped `lean/nf-compose/` sources state and prove composition
rules for the pinned necessity-execution model
(`pinned/MSTNecessityExecModelMWE.lean`, vendored inside the
directory): how a step's necessity composes over products, sums,
sequences and dispatch.

## What was checked

- `cd lean/nf-compose && lake build` on the Lean 4.14.0 toolchain —
  the pinned model file is an `extraDepTarget`, so a byte mismatch of
  the pin fails the build. This build runs inside the development
  repository: the `algorithms` library in `lakefile.lean` reads sources
  at `../hyper`, a repository-side directory that is not in this
  archive. The shipped `lean/nf-compose/` tree is the audit copy: the
  pinned model and the `NfCompose` theorem sources are the exact bytes
  the check ran on.
- Axioms: `propext` only, inside the repository's permitted axiom set.
- The build passed on an independent host, exit code `0`;
  verified at commit `57a1c7d0b17158041b811c2fcb1592bf73f8e4d2` on the
  development main line and audited at `85135fd8b6`.

## What the theorems provide

For each composition form the package proves that necessity of the
composite reduces to necessity of the parts — the obligation an
admission check may decompose rather than re-prove whole. `Basic.lean`
states the shared premises; `Sum.lean`, `Prod.lean`, `Seq.lean`,
`Dispatch.lean`, `AtMostOne.lean`, `Bridge.lean` carry the per-form
rules; `Axioms.lean` lists the axiom surface.

## Limits

- Composition only: the theorems say nothing about admission policy,
  which is outside this package.
- The pinned model is a vendored copy; if the upstream model changes,
  the build fails until the pin is updated and re-audited.
