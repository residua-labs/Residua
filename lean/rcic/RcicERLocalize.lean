import rcic.RcicSynSubst

/-!
# ER2 repair — low-level `localize` provider (S13 amendment §1)

`research/rcic/sortrow/S13_R2_SCOPE_AMENDMENT.md` §1 (PR #7367), driven by the
kernel-confirmed ER2 counterexample `W-ERASURE-LSUB-INLINE-SCOPE`
(`RcicERLsubInlineScope`, #7368): a nonzero-cutoff `TyP.lsub` inlines `hv.eps` —
already a *target*-context value — and `resolve` lifts it again across the keeps
of the prefix (`bvar 2` where the actual value is `bvar 1`).

This module is the single low-level home of `localize` — one canonical
definition, consumed both by production `TyP.eps.lsub` (R2, in `RcicSynErase`)
and by `RcicERScope0` (#7374), which re-exports it rather than redefining. It is
kept strictly below `RcicSynErase` (imports `RcicSynSubst` only) — same layer as
`RcicERPiSlot`. `AvoidPrefix` and the free-variable algebra stay in
`RcicERScope0`.
-/

namespace Rcic.Syn

/-- S13 §2: remove the `k` front ambient erased slots — `k` iterations of
    `ETm.inst 0 ETm.star`. The count is `countKeep (ρ.take j)`, never the
    native slot `j`. -/
def localize : Nat → ETm → ETm
  | 0, r => r
  | k + 1, r => localize k (ETm.inst 0 .star r)
