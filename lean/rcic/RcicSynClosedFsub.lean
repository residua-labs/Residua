import rcic.RcicSynInstEnd
import rcic.RcicSynStepFields1

/-!
# `StepSuppliers.es_fsub` — closed discharge (swe-fsub lane)

Field: `StepSuppliers.es_fsub` (`RcicSynStepSkeleton.lean:491`). Landed filler:
`es_fsub_field` (`RcicSynStepFieldsDeltaObs.lean:49`) over
`fsub_caseStep_of_ports` (`RcicSynStepFields1.lean:253`); drop-branch variant
`es_fsub_field_drop` (`:66`). `ES[hab]` on the keep branch is already (a) inside
the closer (`fsub_issued_replacement_es`, `:235`, row `fsub_es`).

Port table (measured on main 2026-10-19):

| port | statement | class | pin |
|---|---|---|---|
| `hcl` | `TableClosed tbl` | **(a)** | `TableWF.closed` (`RcicSynE.lean:527`) is `TableClosed`'s def verbatim (`∀ ρ ∈ tbl, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)`, `RcicSynCommute.lean:158`); the assembly supplies `hTbl : TableWF tbl` (`tableWF_build`, `RcicSynTableBuild.lean:222`). Consumed only by `es_fsub_keep → convMod_inst_repl`. |
| `hL` | `CL tbl σ ρ dl (instEnd hB hab.dl hA)` | **(d)** | every `.cl` child the `fsub` node issues is an `occ_cl` occurrence pair at `subAt` payload positions (`fsub_issued_cl_is_occurrence`, `RcicSynStepFields1.lean:288`); `instEnd` is a supplier-built judgment, never a stored subterm (`RcicSynP2Shared` §G); `rootCl` pins `ρ = S.can σ` while the field's `ρ` is arbitrary. Not reachable via `StepIH`, not provable outright: `dl` is arbitrary, its `eps` is derivation-dependent, and the port is half of the `ES` goal itself. |
| `hR` | `CL tbl σ ρ (instEnd hB hab.dr hA) dr` | **(d)** | same, symmetric side (note `dr` types at `instantiate0 a Sx` while `instEnd hB hab.dr hA` types at `instantiate0 b Sx` — `CL` compares `eps` only). |

Not all ports close: `hL`/`hR` stay named (d) hypotheses. Their non-vacuity is
shown two ways below — outright (`*_satisfiable`: reflexivity instances) and
under the semantic `Below` hypothesis (`*_of_below`: the `cl_under` route
`es_of_below_fsub`, `RcicSynInstEnd.lean:126`, takes). The gap is demand-side
only: the query `.cl dl (instEnd …) S σ ρ` is `Before` the node (`instEnd_wt`
bounds it under `hnode.wt`) but is never `Demand`ed, so `StepIH` never answers
it.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- Exact `StepSuppliers.es_fsub` statement (the binder telescope copied verbatim
    from `RcicSynStepSkeleton.lean:491`) under the standard `TableWF tbl` datum —
    `TableClosed tbl` discharged as `TableWF.closed` — plus the two named (d)
    `instEnd` `CL` ports. -/
theorem es_fsub_field_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hTbl : TableWF tbl)
    (hL : CL tbl σ ρ dl (instEnd hB hab.dl hA))
    (hR : CL tbl σ ρ (instEnd hB hab.dr hA) dr) :
    CaseStep Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) :=
  fsub_caseStep_of_ports Aw tbl hB hA hab dl dr S σ ρ hTbl.closed hL hR

/-! ### (d)-port non-vacuity witnesses -/

/-- `hL` is inhabited outright at the canonical endpoint: taking the stored left
    endpoint to be `instEnd hB hab.dl hA` itself makes the port reflexivity.
    The (d) port is satisfiable, not a counterexample. -/
theorem fsub_clL_satisfiable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (ha : TyP E n Γ a A) (σ : Level → Level) (ρ : List Disp) :
    ∃ dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx),
      CL tbl σ ρ dl (instEnd hB ha hA) :=
  ⟨instEnd hB ha hA, .refl _⟩

/-- `hR` is inhabited outright at the canonical endpoint: the stored right
    type `instantiate0 a Sx` agrees with `instEnd hB hb hA`'s `instantiate0 b Sx`
    at `a := b`, where the port is reflexivity. -/
theorem fsub_clR_satisfiable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hb : TyP E n Γ b A) (σ : Level → Level) (ρ : List Disp) :
    ∃ (a : Expr Nat) (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx)),
      CL tbl σ ρ (instEnd hB hb hA) dr :=
  ⟨b, instEnd hB hb hA, .refl _⟩

/-- `hL` under the semantic `Below` hypothesis at the node's measure — the
    `cl_under` route `es_of_below_fsub` (`RcicSynInstEnd.lean:154`) takes:
    `dl` and the canonical `instEnd` both weigh strictly under the `fsub`
    node, so `Below.cl` supplies the pair. The port is true in the intended
    model; only `Demand` never asks for it. -/
theorem fsub_clL_of_below
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr))) :
    CL tbl σ ρ dl (instEnd hB hab.dl hA) := by
  let hnode := CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwcL : (instEnd hB hab.dl hA).wt Aw < hnode.wt Aw := by
    have hlt := CvP.wt_dl_lt Aw hab
    have hpos := TyP.wt_pos Aw dl
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  exact cl_under Aw tbl hnode ht Bel dl (instEnd hB hab.dl hA) σ ρ hρ hwl hwcL

/-- `hR` under `Below` — the symmetric side (same `cl_under` route). -/
theorem fsub_clR_of_below
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr))) :
    CL tbl σ ρ (instEnd hB hab.dr hA) dr := by
  let hnode := CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr
  have ht : hnode.isTransport = false := rfl
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwcR : (instEnd hB hab.dr hA).wt Aw < hnode.wt Aw := by
    have hlt := CvP.wt_dr_lt Aw hab
    have hpos := TyP.wt_pos Aw dr
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  exact cl_under Aw tbl hnode ht Bel (instEnd hB hab.dr hA) dr σ ρ hρ hwcR hwr

#print axioms Rcic.Syn.es_fsub_field_closed
#print axioms Rcic.Syn.fsub_clL_satisfiable
#print axioms Rcic.Syn.fsub_clR_satisfiable
#print axioms Rcic.Syn.fsub_clL_of_below
#print axioms Rcic.Syn.fsub_clR_of_below

end Rcic.Syn
