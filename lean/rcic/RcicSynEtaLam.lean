import rcic.RcicIARecTel
import rcic.RcicSynYes

/-!
# Syntactic sortRow, build step 3ad — η's left endpoint, the pure λ

`research/rcic/semantic/S3_ES_ARMS.md` §29. `es_eta` asks for the erasure of
`dl`, a typing of `lam A (app (lift 0 1 f) (bvar 0))`, to be
`lam (app (F.lift 0 1) (bvar 0))`, with `F` the erasure of `f`.

`etaLam` is that λ built from `f`'s typing: weaken at cutoff 0, apply to
`bvar 0`, wrap in `lam`. On a relevant domain whose function does not erase
to `★`, the erasure is the η redex. On a proof domain the λ and the proof
argument are deleted, and the erasure is `f`'s. A `★` function stays `★`.

This is not `CL` of the stored `dl`. A fresh `lam` pays the domain and the
codomain beside the weakened `f`. `CvP.eta` pays `h`, `dl` and `dr`. The
inequality is not the one `zeta_dr` had, and this module does not claim it.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `bvar j` cancels the lift that opened one slot above it -/

/-- `instantiate_bvar_lift_succ` at `c = 0`. The replacement is never consulted. -/
theorem instantiate_bvar_lift_id (j : Nat) (e : Expr Nat) :
    instantiate j (.bvar j) (lift (j + 1) 1 e) = e := by
  simpa [Nat.zero_add, lift_zero] using instantiate_bvar_lift_succ 0 e j

theorem lookup_assumption_zero (A : Expr Nat) (Γ : LCtx) :
    lookupType (.assumption A :: Γ) 0 = some (lift 0 1 A) := by
  unfold lookupType
  rw [List.get?_cons_zero]

/-- Weaken into a new assumption at position 0. -/
def wkAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A : Expr Nat}
    (D : TyP E n Γ e T) :
    TyP E n (.assumption A :: Γ) (lift 0 1 e) (lift 0 1 T) :=
  tyCastCtx (insertAt_zero (.assumption A) Γ)
    (TyP.wk E n Γ e T (.assumption A) 0 D)

/-! ## §2 the pure η λ -/

/-- `λ. f↑ 0`, typed at the same `Π` as `f`. -/
def etaLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) :=
  let hf := wkAtZero (A := A) h
  let hDom := wkAtZero (A := A) hA
  let ha := TyP.bvar E n (.assumption A :: Γ) 0 (lift 0 1 A) u
    (lookup_assumption_zero A Γ) hDom
  let hT := tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB
  let happ := TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
    (lift 0 1 A) (lift 1 1 B) v hf ha hT
  let hbody := tyCast rfl (instantiate_bvar_lift_id 0 B) happ
  TyP.lam E n Γ A u (.app (lift 0 1 f) (.bvar 0)) B v hA hbody hB

theorem disp_keep_zero (ρ : List Disp) : (.keep :: ρ)[0]? = some .keep := by
  simp [List.get?_cons_zero]

theorem disp_drop_zero (ρ : List Disp) : (.drop :: ρ)[0]? = some .drop := by
  simp [List.get?_cons_zero]

/-- A proof domain deletes the λ and the proof argument. The erasure is `f`'s. -/
theorem etaLam_eps_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) :
    (etaLam h hA hB).eps σ ρ = h.eps σ ρ := by
  simp only [etaLam, wkAtZero, eps_tyCast, eps_lam_clause, hu, lamErasure, binderDisp,
    eps_app_appClause]
  rw [eps_tyCastCtx, eps_wk_not_keep (hk := Or.inr (Or.inl (disp_drop_zero ρ))),
    eps_bvar_proof hu, removeAt_zero, appClause_right_star]

/-- A relevant domain, and a function that is not `★`, is the η redex. -/
theorem etaLam_eps_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hn : h.eps σ ρ ≠ .star) :
    (etaLam h hA hB).eps σ ρ =
      .lam (.app ((h.eps σ ρ).lift 0 1) (.bvar 0)) := by
  simp only [etaLam, wkAtZero, eps_tyCast, eps_lam_clause, hu, lamErasure, binderDisp,
    eps_app_appClause]
  rw [eps_tyCastCtx, eps_wk_keep (hk := disp_keep_zero ρ), eps_bvar_rel hu,
    removeAt_zero, resolve_keep_zero, List.take_zero, countKeep]
  rw [appClause_app (lift_ne_star hn) (by rintro ⟨⟩), lamClause_of_ne (by rintro ⟨⟩)]

/-- A `★` function stays `★` after the λ is built. -/
theorem etaLam_eps_keep_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (h : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false)
    (hs : h.eps σ ρ = .star) :
    (etaLam h hA hB).eps σ ρ = .star := by
  simp only [etaLam, wkAtZero, eps_tyCast, eps_lam_clause, hu, lamErasure, binderDisp,
    eps_app_appClause]
  rw [eps_tyCastCtx, eps_wk_keep (hk := disp_keep_zero ρ), eps_bvar_rel hu,
    removeAt_zero, resolve_keep_zero, List.take_zero, countKeep, hs]
  rfl

end Rcic.Syn

#print axioms Rcic.Syn.instantiate_bvar_lift_id
#print axioms Rcic.Syn.lookup_assumption_zero
#print axioms Rcic.Syn.disp_keep_zero
#print axioms Rcic.Syn.disp_drop_zero
#print axioms Rcic.Syn.wkAtZero
#print axioms Rcic.Syn.etaLam
#print axioms Rcic.Syn.etaLam_eps_drop
#print axioms Rcic.Syn.etaLam_eps_keep
#print axioms Rcic.Syn.etaLam_eps_keep_star
