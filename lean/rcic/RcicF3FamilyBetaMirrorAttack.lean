import rcic.RcicF3FamilyBetaMirror
import rcic.RcicF3NormPropEvalAttack

/-!
# Typed beta mirrors in the actual AccR reader prefix

The hidden expression is typed in the real AccR prefix and has an explicit
typed beta conversion to Prop. Its depth-three version is interpreted at
every valuation and local environment in arbitrary admissible family
candidates. A proof-top candidate and an empty candidate are exhibited and
distinguished, while the SAME parameter fits their hidden telescopes.

This does not replace the stored parameter syntax of the AccR group. It is
a typed mirror component in that group's environment, not an EnvWfT group
whose original constructor contains the new mirror, and not a propOnly
recursor witness. The complete prior normalized-role/evaluation/adversarial
suite is retained literally. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.FamilyBetaMirrorAttack
open Rcic.Declarative RawFamily FamilyBetaMirror PiIndex
open EvalPlanValueAttack (plan)

noncomputable def fd : FamData := EvalPlanNormal.fd plan
def kind : Expr Nat := .pi (.sort .zero) (.sort .zero)

def hidden : Nat → Expr Nat
  | 0 => .sort .zero
  | n + 1 => .app (.lam kind (hidden n)) (.const 0 [])

theorem hidden_closed (n : Nat) :
    ∀ k, Rcic.Declarative.lift k 1 (hidden n) = hidden n := by
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
      intro k
      change Expr.app (.lam kind (Rcic.Declarative.lift (k + 1) 1 (hidden n)))
        (.const 0 []) = Expr.app (.lam kind (hidden n)) (.const 0 [])
      rw [ih]

theorem hidden_eq (n : Nat) : hidden n = mirrors fd 0 n (.sort .zero) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Expr.app (.lam kind (hidden n)) (.const 0 []) =
        mirror fd 0 (mirrors fd 0 n (.sort .zero))
      rw [← ih]
      change Expr.app (.lam kind (hidden n)) (.const 0 []) =
        Expr.app (.lam kind (Rcic.Declarative.lift 0 1 (hidden n))) (.const 0 [])
      rw [hidden_closed n 0]

noncomputable def kind_typed (Γ : LCtx) :
    HasTyT accPrefix 0 Γ kind
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort Γ .zero) (.sort (.assumption (.sort .zero) :: Γ) .zero)

noncomputable def family_typed (Γ : LCtx) :
    HasTyT accPrefix 0 Γ (.const 0 []) kind :=
  .const Γ 0 [] accFamMember rfl rfl rfl

noncomputable def hidden_typed : (n : Nat) → (Γ : LCtx) →
    HasTyT accPrefix 0 Γ (hidden n) (.sort (.succ .zero))
  | 0, Γ => .sort Γ .zero
  | n + 1, Γ =>
      .app Γ (.lam kind (hidden n)) (.const 0 []) kind (.sort (.succ .zero))
        (.lam Γ kind (.imax (.succ .zero) (.succ .zero))
          (hidden n) (.sort (.succ .zero)) (kind_typed Γ)
          (hidden_typed n (.assumption kind :: Γ)))
        (family_typed Γ)

noncomputable def mirror_conversion :
    TyConvT accPrefix 0 [] (hidden 1) (.sort .zero) :=
  .of [] (hidden 1) (.sort .zero) (.succ .zero)
    (.beta [] kind (.sort .zero) (.const 0 []) (.sort (.succ .zero))
      (.imax (.succ .zero) (.succ .zero)) (kind_typed [])
      (.sort [.assumption kind] .zero) (family_typed []))

theorem family_free : ∀ e ∈ fd.params ++ fd.indices,
    occursConst fd.fref e = false := by
  intro e he
  change e ∈ [.sort .zero] at he
  cases List.mem_singleton.mp he
  rfl

theorem family_closed : ∀ k,
    Rcic.Declarative.lift k 1 (famType fd) = famType fd := fun _ => rfl

theorem family_bounded : exprLevelsBounded 0 (famType fd) = true := rfl

noncomputable def emptyFrame : Frame := fun _ _ => pempty

theorem empty_admissible (P : Premises4) : Admissible fd emptyFrame := by
  intro vs i
  change pempty ∈ W4 0 ∧ (if 0 = 0 then
    ∀ z, z ∈ (pempty : PSet.{4}) → Equiv z pempty else
    ∀ z, z ∈ (pempty : PSet.{4}) → ¬ Equiv z pempty)
  rw [if_pos rfl]
  exact ⟨(stageW4 P 0).prop_mem (fun _ h => (not_mem_pempty h).elim),
    fun _ h => (not_mem_pempty h).elim⟩

theorem top_admissible (P : Premises4) : Admissible fd RawFamilyProp.proofTop :=
  (RawFamilyProp.candidate P (NormPropEvalAttack.μ P) fd (fun _ => rfl)).1

theorem frames_different :
    ¬ Equiv (emptyFrame [] (key [])) (RawFamilyProp.proofTop [] (key [])) := by
  intro he
  exact not_mem_pempty (mem_congr_right he.symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩))

theorem den_hidden (P : Premises4) (C : Frame) (hC : Admissible fd C)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (n : Nat) :
    Equiv (den (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ ρ (hidden n))
      (den (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ ρ (.sort .zero)) := by
  rw [hidden_eq]
  exact den_of_group P (NormPropEvalAttack.μ P) plan accFamMember
    [(1, accIntroMember)] .empty AccEnv.accMembersT C hC σ ρ n (.sort .zero)

theorem parameter_fits (P : Premises4) (C : Frame) (hC : Admissible fd C)
    (σ : Nat → Nat) (n : Nat) :
    TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ [hidden n]
      ρ0 [PlanPropEndAttack.parameter] := by
  let M := mkM P (table P (NormPropEvalAttack.μ P) fd C)
  refine ⟨?_, True.intro⟩
  exact mem_congr_right (ed_congr M (den_hidden P C hC σ ρ0 n)).symm
    (tyv_pempty_mem_sort P (table P (NormPropEvalAttack.μ P) fd C) σ ρ0 .zero)

theorem hidden_fits_congr (P : Premises4) (C D : Frame)
    (hC : Admissible fd C) (hD : Admissible fd D)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (n : Nat) (xs : List PSet.{4}) :
    TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ [hidden n] ρ xs ↔
      TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd D)) σ [hidden n] ρ xs := by
  rw [hidden_eq]
  apply fits_candidates P (NormPropEvalAttack.μ P) fd C D hC hD family_free
    0 family_closed family_bounded σ n [.sort .zero] _ ρ xs
  intro e he
  cases List.mem_singleton.mp he
  rfl

def Witness (P : Premises4) : Prop :=
  NormPropEvalAttack.Witness P ∧
  Nonempty (HasTyT accPrefix 0 [] (hidden 3) (.sort (.succ .zero))) ∧
  Nonempty (TyConvT accPrefix 0 [] (hidden 1) (.sort .zero)) ∧
  occursConst 0 (hidden 3) = true ∧
  Admissible fd emptyFrame ∧ Admissible fd RawFamilyProp.proofTop ∧
  ¬ Equiv (emptyFrame [] (key [])) (RawFamilyProp.proofTop [] (key [])) ∧
  (∀ σ ρ n C, Admissible fd C →
    Equiv (den (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ ρ (hidden n))
      (den (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ ρ (.sort .zero))) ∧
  (∀ σ n C, Admissible fd C →
    TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ [hidden n]
      ρ0 [PlanPropEndAttack.parameter]) ∧
  (∀ σ ρ n xs C D, Admissible fd C → Admissible fd D →
    (TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd C)) σ [hidden n] ρ xs ↔
      TelFits (mkM P (table P (NormPropEvalAttack.μ P) fd D)) σ [hidden n] ρ xs))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPropEvalAttack.component_witness P, ⟨hidden_typed 3 []⟩,
    ⟨mirror_conversion⟩, rfl, empty_admissible P, top_admissible P,
    frames_different, fun σ ρ n C hC => den_hidden P C hC σ ρ n,
    fun σ n C hC => parameter_fits P C hC σ n,
    fun σ ρ n xs C D hC hD => hidden_fits_congr P C D hC hD σ ρ n xs⟩

theorem nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.FamilyBetaMirrorAttack
