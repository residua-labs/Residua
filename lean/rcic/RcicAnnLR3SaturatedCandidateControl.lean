import rcic.RcicAnnLR3CandidateActionProducts
import rcic.RcicAnnLR3EnrichedReflectionBoundary

/-!
# Positive replacement for the first fixed-erasure collision

Completing every old stage-one fibre with the same retained typed points
repairs the former disjoint-erasure instance. The old universe fibre is
unchanged extensionally, hence exact sort elimination is preserved.
An actual EnvironmentEval constant lambda realizes an element of every
completed fibre. This is a local positive control, not the complete
source Pi arm, a generic context realization, or a Fundamental theorem.
closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedCandidateControl

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates

/-- The shared stage-one point has a genuine sort-zero erasure. -/
def typedPoint (name : Nat) : Carrier 1 :=
  encode 0 (NativeMemberValues.neutralCode 0 name)

def TypedPoints (x : Carrier 1) : Prop := ∃ name, x = typedPoint name

/-- The existing checked self-edge extension constructs the relation. -/
def saturated (C : Code 1) : Code 1 where
  value := C.value
  level := C.level
  defined := C.defined
  relation := Extend C.relation TypedPoints
  lawful := extend_laws C.lawful TypedPoints
  point := typedPoint
  point_member := fun name => Or.inr ⟨rfl, name, rfl⟩
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem saturated_value (C : Code 1) : (saturated C).value = C.value := rfl

theorem saturated_preserves (C : Code 1) {x y : Carrier 1}
    (h : C.relation x y) : (saturated C).relation x y := Or.inl h

theorem saturated_reflects (C : Code 1) (name : Nat) :
    (saturated C).relation (typedPoint name) (typedPoint name) :=
  Or.inr ⟨rfl, name, rfl⟩

theorem typedPoint_erasure (name : Nat) :
    StratifiedCandidates.erase 1 (typedPoint name) = NativeMemberValues.value (some 0) name := rfl

theorem typedPoint_level (name : Nat) :
    SortMember (some 0) (StratifiedCandidates.erase 1 (typedPoint name)) :=
  NativeMemberValues.value_level _ _

theorem typedPoint_defined (name : Nat) : TypeDefined (StratifiedCandidates.erase 1 (typedPoint name)) :=
  NativeMemberValues.value_defined _ _

/-- No untagged atom was added to the universe. -/
theorem universe_completion_same (x y : Carrier 1) :
    (saturated EnrichedReflectionBoundary.universeFibre).relation x y ↔
      EnrichedReflectionBoundary.universeFibre.relation x y := by
  constructor
  · rintro (h | ⟨rfl, name, rfl⟩)
    · exact h
    · exact universe_member 0 _
  · exact Or.inl

theorem universe_elimination_preserved {x : Carrier 1}
    (hx : (saturated EnrichedReflectionBoundary.universeFibre).relation x x) :
    SortMember (some 0) (StratifiedCandidates.erase 1 x) ∧ TypeDefined (StratifiedCandidates.erase 1 x) :=
  EnrichedReflectionBoundary.universe_member_erasure
    ((universe_completion_same x x).mp hx)

theorem collision_repaired (name : Nat) :
    (saturated EnrichedReflectionBoundary.universeFibre).value =
      (saturated EnrichedReflectionBoundary.neutralFibre).value ∧
    (saturated EnrichedReflectionBoundary.universeFibre).relation
      (typedPoint name) (typedPoint name) ∧
    (saturated EnrichedReflectionBoundary.neutralFibre).relation
      (typedPoint name) (typedPoint name) ∧
    SortMember (some 0) (StratifiedCandidates.erase 1 (typedPoint name)) ∧
    TypeDefined (StratifiedCandidates.erase 1 (typedPoint name)) :=
  ⟨rfl, saturated_reflects _ name, saturated_reflects _ name,
    typedPoint_level name, typedPoint_defined name⟩

/-- The captured result retains an actual native-denotable code. -/
def nativeResult (name : Nat) : CandidateAction.ClosedCode 0 :=
  ⟨NativeMemberValues.neutralCode 0 name, NativeMemberValues.neutralCode_bot 0 name⟩

def nativeAction (ν : Valuation) (ρ : EnvI) (name : Nat) :
    CandidateAction.Action (Code 1) (fun C => C.value) (CodeRelated 1) 0 :=
  CandidateAction.constant (fun C : Code 1 => C.value) (CodeRelated 1)
    emptyEnvA EnvironmentEval.neutralFamilySyntax ν ρ
    (.sort (.succ .zero)) (.succ (.succ .zero)) (nativeResult name)

def nativeFunction (ν : Valuation) (ρ : EnvI) (name : Nat) : Value :=
  (nativeAction ν ρ name).value

theorem native_application (ν : Valuation) (ρ : EnvI) (name : Nat) (C : Code 1) :
    ValueEq (NeutralPi.applyValue (nativeFunction ν ρ name) C.value)
      (StratifiedCandidates.erase 1 (typedPoint name)) :=
  (nativeAction ν ρ name).erased C

/-- The raw semantic function now has a retained legal element in every
completed fibre, including both formerly conflicting fibres. -/
theorem every_completed_fibre (ν : Valuation) (ρ : EnvI) (name : Nat) :
    ∀ C : Code 1, ∃ x : Carrier 1,
      (saturated C).relation x x ∧
      ValueEq (NeutralPi.applyValue (nativeFunction ν ρ name) C.value) (StratifiedCandidates.erase 1 x) :=
  fun C => ⟨typedPoint name, saturated_reflects C name, native_application ν ρ name C⟩

/-- Both source admission and the positive raw product realization are
inhabited. The arbitrary context valuation is not claimed to realize the
source context or to establish any constructor arm. -/
theorem positive_source_control (ν : Valuation) (ρ : EnvI) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0)) ∧
    (∀ C : Code 1, ∃ x : Carrier 1, (saturated C).relation x x ∧
      ValueEq (NeutralPi.applyValue (nativeFunction ν ρ name) C.value) (StratifiedCandidates.erase 1 x)) :=
  ⟨⟨.empty⟩, ⟨EnrichedReflectionBoundary.application_context_wf⟩,
    ⟨EnrichedReflectionBoundary.source_application_typed⟩,
    every_completed_fibre ν ρ name⟩

end Rcic.Declarative.Ann.LR3.SaturatedCandidateControl


namespace Rcic.Declarative.Ann.LR3.SaturatedCandidateControl
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates

/-- The actual native constant function contains bottom. -/
theorem nativeFunction_bot (ν : Valuation) (ρ : EnvI) (name : Nat) :
    nativeFunction ν ρ name .bot :=
  EnvironmentEval.denote_bot _ _ _ _ _

def sourceApplicationImage (ν : Valuation) (ρ : EnvI) (name : Nat)
    (C : CandidateAction.ClosedCode 1) : Value :=
  EnvironmentEval.denote emptyEnvA EnvironmentEval.neutralFamilySyntax ν
    (EnvI.cons (CandidateAction.eraseCode C) (EnvI.cons (nativeFunction ν ρ name) ρ))
    (.app (.bvar 1) (.bvar 0))

theorem source_application_image (ν : Valuation) (ρ : EnvI) (name : Nat)
    (C : CandidateAction.ClosedCode 1) :
    ValueEq (sourceApplicationImage ν ρ name C)
      (StratifiedCandidates.erase 1 (typedPoint name)) := by
  let σ := EnvI.cons (CandidateAction.eraseCode C)
    (EnvI.cons (nativeFunction ν ρ name) ρ)
  apply (EnvironmentEval.denote_application emptyEnvA
    EnvironmentEval.neutralFamilySyntax ν σ (.bvar 1) (.bvar 0)).trans
  apply (NeutralPi.applyValue_congr
    (CandidateAction.bound_image emptyEnvA EnvironmentEval.neutralFamilySyntax ν σ
      1 (nativeFunction ν ρ name) rfl (nativeFunction_bot ν ρ name))
    (CandidateAction.bound_image emptyEnvA EnvironmentEval.neutralFamilySyntax ν σ
      0 (CandidateAction.eraseCode C) rfl C.bot)).trans
  exact native_application ν ρ name C.code

theorem every_source_application_fibre (ν : Valuation) (ρ : EnvI) (name : Nat)
    (C : CandidateAction.ClosedCode 1) :
    ∃ x : StratifiedCandidates.Carrier 1,
      (saturated C.code).relation x x ∧
      ValueEq (sourceApplicationImage ν ρ name C) (StratifiedCandidates.erase 1 x) :=
  ⟨typedPoint name, saturated_reflects C.code name,
    source_application_image ν ρ name C⟩

end Rcic.Declarative.Ann.LR3.SaturatedCandidateControl
