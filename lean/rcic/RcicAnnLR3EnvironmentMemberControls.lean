import rcic.RcicAnnLR3EnvironmentMemberInsertion
import rcic.RcicAnnLR3EnvironmentTypedNeutralBoundary
import rcic.RcicAnnLR3EnvironmentEvalControls

/-!
# Admitted controls for compositional member insertion

An arbitrary number of lambda/application layers retains the typed member
meaning. The actual axiom and opaque source environments and all source
typing premises are supplied. A transparent definition whose body contains
such a nested axiom also has the same typed meaning, by the preserved
delta equation. The semantic members are explicit retained universe codes;
no legacy CodeSystem or general source arm is asserted.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentMemberControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements EnvironmentMemberInsertion

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def nest : Nat → ExprA → ExprA
  | 0, e => e
  | n + 1, e => .app (.lam (.sort one) two (nest n e)) (.sort .zero)

/-- Existing EnvironmentEval composition, instantiated with the internal
member view, proves the all-depth control without a substitution port. -/
theorem nest_image {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {e : ExprA} {V : Value}
    (h : ∀ ρ, ValueEq (image E F ν ρ e) V) (depth : Nat) (ρ : EnvI) :
    ValueEq (image E F ν ρ (nest depth e)) V := by
  induction depth generalizing ρ with
  | zero => exact h ρ
  | succ depth ih =>
      exact (EnvironmentEval.denote_application (internalView E) (hook E F) ν ρ
        (.lam (.sort one) two (nest depth e)) (.sort .zero)).trans
        ((EnvironmentEval.denote_lambda_application (internalView E) (hook E F) ν ρ
          (.sort one) (nest depth e) two (image E F ν ρ (.sort .zero))).trans
          (ih (EnvI.cons (image E F ν ρ (.sort .zero)) ρ)))

def nest_typed {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {e : ExprA}
    (h : ∀ Γ, HasTyA E I n Γ e (.sort one)) :
    (depth : Nat) → (Γ : LCtxA) → HasTyA E I n Γ (nest depth e) (.sort one)
  | 0, Γ => h Γ
  | depth + 1, Γ =>
      .app Γ (.lam (.sort one) two (nest depth e)) (.sort .zero)
        (.sort one) (.sort one) two two two
        (.sort _ one) (.sort Γ one)
        (.lam Γ (.sort one) two (nest depth e) (.sort one) two
          (.sort Γ one) (.sort _ one) (nest_typed h depth (.assumption (.sort one) :: Γ)))
        (.sort Γ .zero)

def axiom_source (Γ : LCtxA) :
    HasTyA EnvironmentTypedNeutralBoundary.env
      (iotaIfaceA EnvironmentTypedNeutralBoundary.env) 0 Γ (.const 92 []) (.sort one) :=
  .const Γ 92 [] EnvironmentTypedNeutralBoundary.member two rfl rfl rfl (.sort Γ one)

theorem axiom_nested_control (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (depth : Nat) :
    Nonempty (EnvWfA (iotaIfaceA EnvironmentTypedNeutralBoundary.env)
      EnvironmentTypedNeutralBoundary.env) ∧
    Nonempty (CtxWfA EnvironmentTypedNeutralBoundary.env
      (iotaIfaceA EnvironmentTypedNeutralBoundary.env) 0 []) ∧
    Nonempty (HasTyA EnvironmentTypedNeutralBoundary.env
      (iotaIfaceA EnvironmentTypedNeutralBoundary.env) 0 []
      (nest depth (.const 92 [])) (.sort one)) ∧
    (StratifiedCandidates.universeCode 1).relation
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92))
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92)) ∧
    ValueEq (image EnvironmentTypedNeutralBoundary.env F ν ρ (nest depth (.const 92 [])))
      (StratifiedCandidates.erase 2
        (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92))) := by
  refine ⟨⟨EnvironmentTypedNeutralBoundary.admitted⟩, ⟨.nil⟩,
    ⟨nest_typed axiom_source depth []⟩, NativeMemberValues.universe_member 1 92, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  apply nest_image
  intro σ
  exact image_axiom (m := EnvironmentTypedNeutralBoundary.member) rfl rfl rfl F ν σ []

def opaque_source (Γ : LCtxA) :
    HasTyA EnvironmentEvalControls.opaqueEnv (iotaIfaceA EnvironmentEvalControls.opaqueEnv)
      0 Γ (.const 91 []) (.sort one) :=
  .const Γ 91 [] EnvironmentEvalControls.opaqueMember two rfl rfl rfl (.sort Γ one)

theorem opaque_nested_control (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (depth : Nat) :
    Nonempty (EnvWfA (iotaIfaceA EnvironmentEvalControls.opaqueEnv)
      EnvironmentEvalControls.opaqueEnv) ∧
    Nonempty (CtxWfA EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 []) ∧
    Nonempty (HasTyA EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 []
      (nest depth (.const 91 [])) (.sort one)) ∧
    (StratifiedCandidates.universeCode 1).relation
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 91))
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 91)) ∧
    ValueEq (image EnvironmentEvalControls.opaqueEnv F ν ρ (nest depth (.const 91 [])))
      (StratifiedCandidates.erase 2
        (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 91))) := by
  refine ⟨⟨EnvironmentEvalControls.opaque_admitted⟩, ⟨.nil⟩,
    ⟨nest_typed opaque_source depth []⟩, NativeMemberValues.universe_member 1 91, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  apply nest_image
  intro σ
  exact image_opaque (m := EnvironmentEvalControls.opaqueMember) rfl rfl rfl F ν σ []

def definitionMember : CheckedMemberA :=
  ⟨.definitionM, 0, .sort one, some (nest 1 (.const 92 [])), 0, none⟩

def definitionEnv : ResolvedEnvA :=
  extendEnvA EnvironmentTypedNeutralBoundary.env 93 definitionMember

def base_admitted (I : IotaIfaceA) : EnvWfA I EnvironmentTypedNeutralBoundary.env :=
  .axiomM emptyEnvA 92 (.sort one) two .empty rfl (.sort [] one) (fun _ => rfl) rfl

def base_axiom_source (I : IotaIfaceA) (Γ : LCtxA) :
    HasTyA EnvironmentTypedNeutralBoundary.env I 0 Γ (.const 92 []) (.sort one) :=
  .const Γ 92 [] EnvironmentTypedNeutralBoundary.member two rfl rfl rfl (.sort Γ one)

def definition_admitted : EnvWfA (iotaIfaceA definitionEnv) definitionEnv :=
  .definitionM EnvironmentTypedNeutralBoundary.env 93 (.sort one)
    (nest 1 (.const 92 [])) two (base_admitted _) rfl (.sort [] one)
    (nest_typed (base_axiom_source _) 1 [])
    (fun _ => rfl) (fun _ => rfl) rfl rfl

def definition_axiom_source (Γ : LCtxA) :
    HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 Γ (.const 92 []) (.sort one) :=
  .const Γ 92 [] EnvironmentTypedNeutralBoundary.member two rfl rfl rfl (.sort Γ one)

def definition_source (Γ : LCtxA) :
    HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 Γ (.const 93 []) (.sort one) :=
  .const Γ 93 [] definitionMember two rfl rfl rfl (.sort Γ one)

def definition_delta_source (Γ : LCtxA) :
    ConvA definitionEnv (iotaIfaceA definitionEnv) 0 Γ
      (.const 93 []) (nest 1 (.const 92 [])) (.sort one) :=
  .delta Γ 93 [] definitionMember (nest 1 (.const 92 [])) rfl rfl rfl rfl rfl
    (nest_typed definition_axiom_source 1 Γ)

theorem definition_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (image definitionEnv F ν ρ (.const 93 [])) (NativeMemberValues.value (some 1) 92) := by
  apply (image_delta (E := definitionEnv) (r := 93) (ls := []) (m := definitionMember)
    (b := nest 1 (.const 92 [])) rfl rfl rfl F ν ρ).trans
  change ValueEq (image definitionEnv F ν ρ (nest 1 (.const 92 []))) _
  apply nest_image
  intro σ
  exact image_axiom (m := EnvironmentTypedNeutralBoundary.member) rfl rfl rfl F ν σ []

theorem definition_nested_control (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (depth : Nat) :
    Nonempty (EnvWfA (iotaIfaceA definitionEnv) definitionEnv) ∧
    Nonempty (CtxWfA definitionEnv (iotaIfaceA definitionEnv) 0 []) ∧
    Nonempty (HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 []
      (nest depth (.const 93 [])) (.sort one)) ∧
    Nonempty (ConvA definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.const 93 []) (nest 1 (.const 92 [])) (.sort one)) ∧
    (StratifiedCandidates.universeCode 1).relation
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92))
      (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92)) ∧
    ValueEq (image definitionEnv F ν ρ (nest depth (.const 93 [])))
      (StratifiedCandidates.erase 2
        (StratifiedCandidates.encode 1 (NativeMemberValues.neutralCode 1 92))) := by
  refine ⟨⟨definition_admitted⟩, ⟨.nil⟩, ⟨nest_typed definition_source depth []⟩,
    ⟨definition_delta_source []⟩, NativeMemberValues.universe_member 1 92, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  exact nest_image (definition_image F ν) depth ρ

end Rcic.Declarative.Ann.LR3.EnvironmentMemberControls
