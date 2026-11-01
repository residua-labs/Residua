import rcic.RcicF3PiSyntaxCompile
import rcic.RcicF3Inv
/-!
# Typed structural telescope extraction at a fixed interpretation

The existing hereditary typing inversion supplies leaf sort membership.
It therefore discharges the structural compiler's EndEq obligation, with
no separate leaf-agreement or dichotomy premise. The result index records
the leaf's current semantic denotation; it is not an independent inductive
family label and cannot establish a fixed point. Arbitrary normalized
admission and small raw signatures remain unpaid. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiTypedCompile
open Rcic.Declarative
universe u

/-- A universe member is already the type value of its Ed element set. -/
theorem tyv_ed_of_mem_U (M : Interp.{u}) (W : Nat → PSet.{u})
    {x : PSet.{u}} (k : Nat) (hx : x ∈ U W k) :
    Equiv (tyv (Ed M x)) x := by
  have h : ∃ S, Dich S ∧ Equiv x (tyv S) := by
    cases k with
    | zero =>
      obtain ⟨S, hS, he⟩ := mem_sImage_tyv.mp hx
      exact ⟨S, Or.inl (mem_propSets.mp hS), he⟩
    | succ k =>
      obtain ⟨S, hS, he⟩ := mem_sImage_tyv.mp hx
      obtain ⟨i, hi, heS⟩ := mem_sep.mp hS
      exact ⟨S, (dich_congr heS).mp hi, he⟩
  obtain ⟨S, hS, he⟩ := h
  exact (tyv_congr ((ed_congr M he).trans (ed_tyv M hS))).trans he.symm

def leafIndex (M : Interp.{u}) (σ : Nat → Nat) (b : Expr Nat)
    (ρ : Nat → PSet.{u}) : { S : PSet.{u} // Dich S } :=
  ⟨Ed M (den M σ ρ b), dich_ed M _⟩

theorem typed_endEq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n) (ds : List (Expr Nat)) (b : Expr Nat)
    {l : Level} (d : HasTyT E n Γ (policyPi ds b) (.sort l)) (hd : LOKt σ 4 K d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    PiSyntaxCompile.EndEq (mkM P μ) σ (leafIndex (mkM P μ) σ b)
      (fun i => i.1) b ds ρ := by
  apply (PiSyntaxCompile.endEq_iff (mkM P μ) σ (leafIndex (mkM P μ) σ b)
    (fun i => i.1) b ds ρ).mpr
  intro xs hxs
  obtain ⟨v, hv⟩ := tel_end_type b ds d (hsound_ty (P.good _ rfl) hE d hd) ρ xs hρ hxs
  exact tyv_ed_of_mem_U (mkM P μ) W4 (evalTotal σ v)
    (mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)) hv)

/-- Exact compilation at a fixed semantic interpretation of a typed
structural telescope. The leaf index records its current denotation. -/
theorem compile_spec (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n) (ds : List (Expr Nat)) (b : Expr Nat)
    {l : Level} (d : HasTyT E n Γ (policyPi ds b) (.sort l)) (hd : LOKt σ 4 K d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv ((PiSyntaxCompile.compile (mkM P μ) σ (leafIndex (mkM P μ) σ b) ds ρ).erasedType
      (mkM P μ) (fun i => i.1)) (den (mkM P μ) σ ρ (policyPi ds b)) := by
  exact PiSyntaxCompile.compile_spec (mkM P μ) σ (leafIndex (mkM P μ) σ b)
    (fun i => i.1) (fun i => i.2) b ds ρ
    (typed_endEq P μ σ K hE ds b d hd ρ hρ)
end Rcic.F3.PSet.PiTypedCompile
