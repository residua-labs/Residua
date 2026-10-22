import rcic.RcicAnnLR3TypedArms
import rcic.RcicAnnLR3TypedConstantModel

/-!
# Exact const-arm failure, with the immediate semantic IH supplied

The four structural arms below are real supplies at the statement schema.
The const boundary is model-parametric for the empty-family interpretation;
the concrete CodeSystem supplies every semantic and source premise. No
whole fundamental theorem is assumed just to refute one of its fields.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedArmBoundary
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TypedArms TruthAxiomBoundary

/-- Four actual suppliers at the frozen statement surface. -/
theorem ty_sort_supplied (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    Ty_sort M E I n := sort_goal M E I n

theorem conv_refl_supplied (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    Conv_refl M E I n := fun _ _ _ _ ih => ih

theorem conv_symm_supplied (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    Conv_symm M E I n := fun _ _ _ _ _ ih hΓ ν ρ hρ => judgment_symm (ih hΓ ν ρ hρ)

theorem conv_trans_supplied (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    Conv_trans M E I n := fun _ _ _ _ _ _ _ ih₁ ih₂ hΓ ν ρ hρ =>
      judgment_trans (ih₁ hΓ ν ρ hρ) (ih₂ hΓ ν ρ hρ)

/-- This is the semantic content of interpreting the zero-constructor
family by its least constructor closure, not source type uniqueness. -/
def EmptyFamilyInterpretation (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (ρ : EnvI) (k : Option Nat) (R : Relation),
    M.Code k (M.image ν [] ρ emptyType) R → ∀ x : Value, ¬ Member R x

theorem const_arm_false_of_empty (M : AnnSemantics)
    (hEmpty : EmptyFamilyInterpretation M)
    (hType : TyGoal M badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero)) :
    ¬ Ty_const M badEnv (iotaIfaceA badEnv) 0 := by
  intro hconst
  have hgoal := hconst [] 81 [] badAxiom .zero rfl rfl rfl (emptyType_typed rfl) hType
  obtain ⟨k, R, hc, _, hm⟩ := hgoal .nil (fun _ => none) EnvI.bot (.nil EnvI.bot)
  exact hEmpty (fun _ => none) EnvI.bot k R hc _ hm

/-- No admission-wide assignment with an empty least constructor carrier
at this admitted family and its genuine formation IH can fill every arm. -/
theorem all_admitted_false_of_empty (models : ResolvedEnvA → AnnSemantics)
    (hEmpty : EmptyFamilyInterpretation (models badEnv))
    (hType : TyGoal (models badEnv) badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero)) :
    ¬ AllAdmittedFundamental models := by
  intro hAll
  have hF := hAll badEnv (badEnv_admitted _) 0
  have hgoal := hF.1 (badTerm_typed _)
  obtain ⟨k, R, hc, _, hm⟩ := hgoal .nil (fun _ => none) EnvI.bot (.nil EnvI.bot)
  exact hEmpty (fun _ => none) EnvI.bot k R hc _ hm

theorem concrete_empty_family : EmptyFamilyInterpretation TypedConstantModel.model :=
  fun _ _ _ _ h x => TypedConstantModel.code_at_empty_no_member h x

theorem const_arm_false :
    ¬ Ty_const TypedConstantModel.model badEnv (iotaIfaceA badEnv) 0 :=
  const_arm_false_of_empty TypedConstantModel.model concrete_empty_family
    TypedConstantModel.emptyType_goal

theorem all_arms_false : ¬ Arms TypedConstantModel.model badEnv (iotaIfaceA badEnv) 0 :=
  fun h => const_arm_false h.Ty_const

theorem inhabited_const_arm_boundary :
    Nonempty (EnvWfA (iotaIfaceA badEnv) badEnv) ∧
    Nonempty (CtxWfA badEnv (iotaIfaceA badEnv) 0 []) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero)) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType) ∧
    (∀ ν, Realises TypedConstantModel.model ν [] EnvI.bot) ∧
    EmptyFamilyInterpretation TypedConstantModel.model ∧
    TyGoal TypedConstantModel.model badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero) ∧
    ¬ Ty_const TypedConstantModel.model badEnv (iotaIfaceA badEnv) 0 :=
  ⟨⟨badEnv_admitted _⟩, ⟨.nil⟩, ⟨emptyType_typed rfl⟩, ⟨badTerm_typed _⟩,
    fun _ => .nil EnvI.bot, concrete_empty_family, TypedConstantModel.emptyType_goal, const_arm_false⟩

end Rcic.Declarative.Ann.LR3.TypedArmBoundary
