import rcic.RcicNativeTypedModelK

/-!
# Source provenance for native application spines

An observed constant or variable spine can be built by a function-table
action, by direct rigid extension, or by a saturated computation. Its
compact need not have the native head. This finite Prop-valued trace keeps
the actual alternatives and demands from application inversion.

The supplier recurses on the native argument list, not on an application
result or readback size. Internal observations are raw ApproxTK proofs;
an enclosing information stage bounds the result compact only. In
particular this does not assert a same-stage bound for every internal
table or demand. This is a spine supplier, not general type-view supply.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit

inductive CovTSpineProvenance (E : ResolvedEnv) (arity : Nat)
    (Γ : LCtx) (ρ : EnvT) (head : Expr Nat) :
    List (Expr Nat) → CptT → Prop
  | head {c : CptT} (observed : ApproxTK E arity Γ ρ head c) :
      CovTSpineProvenance E arity Γ ρ head [] c
  | bot (xs : List (Expr Nat)) :
      CovTSpineProvenance E arity Γ ρ head xs .bot
  | app {xs : List (Expr Nat)} {a : Expr Nat}
      {rows : List (List CptT × CptT)} {s : List CptT × CptT}
      (initial : CovTSpineProvenance E arity Γ ρ head xs (.lam rows))
      (row : s ∈ rows)
      (argument : ∀ u ∈ s.1, ApproxTK E arity Γ ρ a u) :
      CovTSpineProvenance E arity Γ ρ head (xs ++ [a]) s.2
  | appSpine {xs : List (Expr Nat)} {a : Expr Nat}
      {r : Nat} {cs : List CptT} {u : CptT}
      (initial : CovTSpineProvenance E arity Γ ρ head xs (.spine r cs))
      (argument : ApproxTK E arity Γ ρ a u) :
      CovTSpineProvenance E arity Γ ρ head (xs ++ [a]) (.spine r (cs ++ [u]))
  | saturated {xs : List (Expr Nat)} {c : CptT}
      (computation : SaturatedComputationTK E arity Γ ρ (foldApps head xs) c) :
      CovTSpineProvenance E arity Γ ρ head xs c

theorem CovTSpineProvenance.observed {E : ResolvedEnv} {arity : Nat}
    {Γ : LCtx} {ρ : EnvT} {head : Expr Nat} {xs : List (Expr Nat)} {c : CptT}
    (h : CovTSpineProvenance E arity Γ ρ head xs c) :
    ApproxTK E arity Γ ρ (foldApps head xs) c := by
  induction h with
  | head ho => exact ho
  | bot => exact .bot _ _ _
  | app _ hs ha ih =>
      rw [foldApps_snoc]
      exact .app ih hs ha
  | appSpine _ ha ih =>
      rw [foldApps_snoc]
      exact .appSpine ih ha
  | saturated hc => exact approxTK_of_saturated hc

theorem covT_spine_provenance_of_observed {E : ResolvedEnv} {arity : Nat}
    {Γ : LCtx} {ρ : EnvT} {head : Expr Nat} {xs : List (Expr Nat)} {c : CptT}
    (h : ApproxTK E arity Γ ρ (foldApps head xs) c) :
    CovTSpineProvenance E arity Γ ρ head xs c := by
  have aux : ∀ (ys : List (Expr Nat)) (c : CptT),
      ApproxTK E arity Γ ρ (foldApps head ys.reverse) c →
      CovTSpineProvenance E arity Γ ρ head ys.reverse c := by
    intro ys
    induction ys with
    | nil => intro c ho; exact .head ho
    | cons a ys ih =>
        intro c ho
        simp only [List.reverse_cons, foldApps_snoc] at ho ⊢
        rcases approxTK_app_inv ho with hb | ha | hs | hc
        · subst c
          exact .bot _
        · obtain ⟨rows, s, rfl, hf, hr, harg⟩ := ha
          exact .app (ih _ hf) hr harg
        · obtain ⟨r, cs, u, rfl, hf, harg⟩ := hs
          exact .appSpine (ih _ hf) harg
        · exact .saturated (by simpa only [foldApps_snoc] using hc)
  simpa only [List.reverse_reverse] using aux xs.reverse c (by
    simpa only [List.reverse_reverse] using h)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_SPINE_ROOTS
#print axioms CovTSpineProvenance
#print axioms CovTSpineProvenance.observed
#print axioms covT_spine_provenance_of_observed
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_SPINE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
