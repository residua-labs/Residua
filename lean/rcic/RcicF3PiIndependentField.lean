import rcic.RcicF3PiIndependent
/-! Actual field semantics for independent argument-labelled telescopes.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
universe u v

/-- Leaf element-set agreement suffices; no family type-value premise or
normalized subject-reduction wall is needed for this erased comparison. -/
theorem compile_ed {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b))) :
    ∀ ds ρ, Equiv (Ed M ((PiSyntaxCompile.compile M σ R ds ρ).erasedType M X))
      (Ed M (den M σ ρ (policyPi ds b))) := by
  intro ds
  induction ds with
  | nil => intro ρ; exact (ed_tyv M (hX (R ρ))).trans (hL ρ)
  | cons A ds ih =>
    intro ρ
    let D := Ed M (den M σ ρ A)
    let C := fun a => tyv (classFiber D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedType M X)) a)
    change Equiv (Ed M (piVal M (tyv D) C))
      (Ed M (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b))))
    apply ed_congr M
    refine piVal_ed_congr_on M (ed_tyv M (dich_ed M _))
      (fun _ _ h => ed_congr M (tyv_congr (classFiber_congr D _ h)))
      (fun _ _ h => ed_congr M (den_congr M σ (policyPi ds b)
        (vcons_congr (ρ := ρ) (ρ' := ρ) h (fun _ => Equiv.rfl)))) ?_
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M (dich_ed M _)) ha
    let q := Quotient.mk (FSetoid D) i
    have ef := (classFiber_congr D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedType M X))
      hi.symm).trans (classFiber_at D _ i)
    exact ((ed_tyv M ((dich_congr ef).mpr (dich_ed M _))).trans ef).trans
      ((ih (vcons (PiCompile.classValue D q) ρ)).trans
        (ed_congr M (den_congr M σ (policyPi ds b)
          (vcons_congr ((PiCompile.classValue_at D i).trans hi) (fun _ => Equiv.rfl)))))


/-- Actual recursive-field element sets are read from a fixed base
signature. The variable family is used only at the argument-labelled leaf. -/
theorem recursiveField_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) :
    let M := mkM P (upd μ f X)
    Equiv (Ed M ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ args) ds ρ).erasedType
      M (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) := by
  dsimp only
  have he := compile_free P μ f (μ f) X σ (leafArgs P μ σ args) ds ρ hd
  rw [upd_self] at he
  rw [he]
  apply compile_ed (mkM P (upd μ f X)) σ (leafArgs P μ σ args)
    (fun xs => Ed (mkM P (upd μ f X)) (fapps (X (ls.map (evalTotal σ))) xs))
    (fun _ => dich_ed _ _) (foldApps (.const f ls) args)
  intro ρ'
  rw [leaf_read P μ f X σ ls args ha ρ']
  exact Equiv.rfl


/-- An inhabited normalized recursive field enters the independent large
signature. Only ordinary environment semantics and bounded instances are
used for normalization; the smallness bridge is not asserted here. -/
theorem normalized_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P (upd μ f X)) σ K E n) (hb : BodiesOK E σ K)
    (fuel : Nat) (T : Expr Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel T = some (ds, foldApps (.const f ls) args))
    (hI : InstOK E σ K T) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hx : x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T)) :
    let M := mkM P (upd μ f X)
    x ∈ Ed M ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ args) ds ρ).erasedType
      M (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))) := by
  dsimp only
  have hn := den_piTelescope_of_mem (mkM P (upd μ f X)) σ K hE hb
    fuel T ds (foldApps (.const f ls) args) ρ x hw hI hx
  exact mem_congr_right ((recursiveField_ed P μ f X σ ls ds args hd ha ρ).trans
    (ed_congr (mkM P (upd μ f X)) hn)).symm hx

end Rcic.F3.PSet.PiIndependent
