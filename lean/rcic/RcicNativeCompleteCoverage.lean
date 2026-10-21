import rcic.RcicSynBelowCProj

/-!
# The current CompleteC pack's canonical coverage half

`ReadyC` presently records only `DispForC` at the query's own canonical
native context spine.  That evidence is constructed here from the scope
already carried by each `QueryC`; it is not an additional supplier.
`dispForC_of_ctxP` performs the underlying structural recursion on the
context spine, using the spine's stored domain and let-value derivations.
The five level-mapped tags use their own `LevelHom.levelSub`; `cts` uses
`levelSub_id`.  No sort-coherence or native injectivity premise is used.

The resulting `CoverageCAt` covers every query at every key, frame and
bound.  The equivalence at the end identifies `BelowCAt` as the exact
remaining half of the current `CompleteCAt` definition.  Its hypothesis
stays explicit: this module constructs no query goal, `BelowCAt`,
`AllBelowScoped`, or `Step` producer.

This is coverage of the current definition only.  The future original-
frame receipts, environment-origin paths, disposition forests and slot-
origin evidence described in `RcicSynBelowCProj` are not fields of that
definition, and are not constructed by this theorem.

`closure_claim = 0`.
-/

namespace Rcic.Syn.NativeCompleteCoverageAudit

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}

/-- Construct the current readiness evidence from each query's own
native scope and canonical disposition.  This is a finite tag split;
the reused context recursion descends to the original `CtxP` tail. -/
theorem readyC_native : (q : QueryC Eₐ Aw tbl) → ReadyC q
  | .es _ _ S _ hσ _ =>
      dispForC_of_ctxP hσ.levelSub (enrichCtxWfT_of_envWfT S.env S.ctx)
  | .cl _ _ _ _ S _ hσ _ =>
      dispForC_of_ctxP hσ.levelSub (enrichCtxWfT_of_envWfT S.env S.ctx)
  | .eut _ _ _ _ S _ hσ _ =>
      dispForC_of_ctxP hσ.levelSub (enrichCtxWfT_of_envWfT S.env S.ctx)
  | .cts _ _ _ _ S _ =>
      dispForC_ctxP_id (enrichCtxWfT_of_envWfT S.env S.ctx)
  | .pb _ _ _ _ S _ hσ _ =>
      dispForC_of_ctxP hσ.levelSub (enrichCtxWfT_of_envWfT S.env S.ctx)
  | .bitCoh _ _ _ _ S _ hσ _ =>
      dispForC_of_ctxP hσ.levelSub (enrichCtxWfT_of_envWfT S.env S.ctx)

/-- Full-domain coverage of the current readiness definition.  The
frame and strict bound restrict the input domain; canonical readiness
is available even without those restrictions. -/
theorem coverageCAt_native
    (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat) : CoverageCAt key p B :=
  fun q _hframe _hlt => ⟨readyC_native q⟩

/-- The current completed pack from its still-required conclusion
supplier.  Only the coverage field is discharged here. -/
theorem completeCAt_of_belowCAt
    (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat)
    (hBelow : BelowCAt key p B) : CompleteCAt key p B :=
  ⟨coverageCAt_native key p B, hBelow⟩

/-- An exact residual statement, valid in particular at the canonical
combined key `QueryC.combBound`: the current coverage half adds no
further hypothesis to the remaining `BelowCAt` obligation. -/
theorem completeCAt_iff_belowCAt
    (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat) :
    CompleteCAt key p B ↔ BelowCAt key p B :=
  ⟨fun hComplete => hComplete.2, completeCAt_of_belowCAt key p B⟩

#print axioms readyC_native
#print axioms coverageCAt_native
#print axioms completeCAt_of_belowCAt
#print axioms completeCAt_iff_belowCAt

end Rcic.Syn.NativeCompleteCoverageAudit
