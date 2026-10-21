import rcic.RcicSynSRBetaZetaEpsW
import rcic.RcicSynSRBetaZetaStepWCore
import rcic.RcicSynSRLitPiLit
import rcic.RcicSynStepSkeleton

/-!
# `RcicSynSRLitPiEswW` — the ESW+`LevelHom` re-measure layer for sortRow

cc 2026-10-20 20:00Z task, branch `glm/sr2-esw`. On the merged `glm/sr2-clw`
tree the local `GoalW`/`CaseStepW` restatements were DUPLICATES of
`RcicSynSRBetaZetaStepWCore`'s (same names, this branch's earlier
half-migrated `.eut`/`.pb` arms); they are dropped here and the StepWCore
ones are used — at every `.es`/`.cl` query the two agree definitionally
(`ESW`/`CLW` from the shared `RcicSynSRBetaZetaEpsW` base), and the field
walls below only ever state `.es` queries. What stays original here: the
`LevelHom`-gated transport-head supplier `TransportHeadSortAtW` (the ESW
version of #7799's `TransportHeadSortAt`) and the hom bit-congruence.

Kernel pins of the two hom facts the re-measure runs on:

* `levelIsZero_congr_hom` — at every `LevelHom σ`, `levelIsZero (σ ·)` is
  `eqN`-invariant. Every stored-cutoff tooth built on the semantic `eqN`
  slack of two legal typings (row 7's lit cutoffs, row 10's pi cutoffs) is
  dead on-cone: the discriminating `σ` of the landed refutations is not a
  hom (`sr2_σ_not_hom`).
* `TransportHeadSortAtW` at `.ewk`/`.cctx` heads commutes (both heads
  forward `epsW` literally).

Per-row verdicts live in the per-row modules. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §2 the hom bit-congruence (the cutoff tooth class, dead on-cone) -/

/-- At every `LevelHom σ`, `levelIsZero (σ ·)` is `eqN`-invariant: two
    legally-stored eqN-equal cutoffs cannot separate the erasure bit at a
    hom. Via `levelIsZero_iff` and `LevelHom.eqN_map`. -/
theorem levelIsZero_congr_hom {σ : Level → Level} (hσ : LevelHom σ) {u v : Level}
    (h : eqN u v) : levelIsZero (σ u) = levelIsZero (σ v) := by
  cases h1 : levelIsZero (σ u) with
  | true =>
      have hzu : eqN (σ u) .zero := (levelIsZero_iff _).1 h1
      have hzv : eqN (σ v) .zero := fun ρ => (hσ.eqN_map h ρ).symm.trans (hzu ρ)
      exact ((levelIsZero_iff _).2 hzv).symm
  | false =>
      cases h2 : levelIsZero (σ v) with
      | false => rfl
      | true =>
          have hzv : eqN (σ v) .zero := (levelIsZero_iff _).1 h2
          have hzu : eqN (σ u) .zero :=
            fun ρ => (hσ.eqN_map h ρ).trans (hzv ρ)
          exact absurd (levelIsZero_iff (σ u) |>.2 hzu) (by
            rw [h1]; exact fun hh => Bool.noConfusion hh)

#print axioms Rcic.Syn.GoalW
#print axioms Rcic.Syn.CaseStepW
#print axioms Rcic.Syn.levelIsZero_congr_hom

/-! ## §3 the gated transport-head supplier, ESW version -/

/-- `TransportHeadSortAt` (#7799) under BOTH cone restrictions at once:
    the `CLW` (epsW) judgment and the `LevelHom σ` gate. Same-subject
    erasure uniqueness of every re-typing, at homomorphic `σ` only. -/
def TransportHeadSortAtW (tbl : List CRule) (σ : Level → Level)
    (hσ : LevelHom σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : Prop :=
  ∀ {T' : Expr Nat} (D' : TyP E n Γ e T'), CLW tbl σ ρ D D'

/-- Only `.ewk` commutes at fixed `(E, n, Γ, σ, ρ)` — same shape as
    #7799: `cctx` re-indexes the context, `linst` re-scopes `σ`,
    `esub`/`lsub`/`wk` shift `ρ`. The epsW `.ewk` arm forwards the
    erasure literally, so re-typings of the wrapped subject cohere
    exactly when they cohere for `D`. -/
theorem thsaW_ewk_of (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (hext : EnvExt E E) (D : TyP E n Γ e T)
    (h : TransportHeadSortAtW tbl σ hσ ρ D) :
    TransportHeadSortAtW tbl σ hσ ρ (TyP.ewk E E n Γ e T hext D) :=
  fun D' => h D'

/-- THSAW at a hom is exactly THSA's `CLW`-reading: the ungated `CL`
    instances at the same `(σ, ρ)` follow. -/
theorem thsaW_apply (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    {D : TyP E n Γ e T} (h : TransportHeadSortAtW tbl σ hσ ρ D)
    (D' : TyP E n Γ e T') : CLW tbl σ ρ D D' :=
  h D'

#print axioms Rcic.Syn.TransportHeadSortAtW
#print axioms Rcic.Syn.thsaW_ewk_of
#print axioms Rcic.Syn.thsaW_apply

end Rcic.Syn
