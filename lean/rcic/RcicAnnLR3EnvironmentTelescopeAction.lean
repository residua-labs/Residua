import rcic.RcicAnnLR3EnvironmentTelescopeInsertion
import rcic.RcicAnnLR3CandidateAction

/-!
# Retained actions for actual rigid telescope meanings

The native meanings installed by EnvironmentTelescopeInsertion carry
actual code-valued actions for one and two arguments. Their application
equations are supplied by the native lambda tower, and the constructed
result code is retained throughout. In particular the binary proposition
action accepts every original zero-stage code, without requiring its raw
erasure to contain bottom or narrowing its candidate.

These are actual action producers for the configured EnvironmentEval.
They do not identify a raw value with a selected candidate, provide the
general dependent member telescope, or discharge a uniform Ty_const arm.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentTelescopeAction

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction EnvironmentTelescopeInsertion

universe u v

/-- The installed native code already contains bottom, so this package
retains the exact constructed code and does not need to complete it. -/
def resultCode (k name : Nat) : ClosedCode k :=
  ⟨NativeMemberValues.neutralCode k name, NativeMemberValues.neutralCode_bot k name⟩

theorem resultCode_value (k name : Nat) :
    eraseCode (resultCode k name) = NativeMemberValues.value (some k) name :=
  NativeMemberValues.neutralCode_value k name

/-- An eligible unary member supplies its action; no membership or
code-valued run is requested from a caller. -/
def oneAction {α : Type u} (eraseA : α → Value) (D : α → α → Prop)
    {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level} {k : Nat}
    (hm : E.members r = some m) (he : eligible m = some (1, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (hk : eval ν (instLevel ls l) = some k) : Action α eraseA D k where
  value := image E F ν ρ (.const r ls)
  run := fun _ => resultCode k r
  erased := by
    intro x
    change ValueEq (NeutralPi.applyValue (image E F ν ρ (.const r ls)) (eraseA x))
      (eraseCode (resultCode k r))
    rw [resultCode_value]
    have h := image_telescope hm he F ν ρ ls
    rw [hk] at h
    exact (NeutralPi.applyValue_congr h (ValueEq.refl (eraseA x))).trans
      (NativeTelescopeValues.application 0 (some k) r (eraseA x))
  respect := fun _ _ _ => codeRel_refl (resultCode k r)

/-- The first application retains the actual second action as data.
The second application in turn retains its result code. -/
structure BinaryAction (α : Type u) (eraseA : α → Value) (D : α → α → Prop)
    (β : Type v) (eraseB : β → Value) (Q : β → β → Prop) (k : Nat) where
  value : Value
  run : α → Action β eraseB Q k
  erased : ∀ x, ValueEq (NeutralPi.applyValue value (eraseA x)) (run x).value
  respect : ∀ x y, D x y → ActionRel (run x) (run y)

def BinaryRel {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {β : Type v} {eraseB : β → Value} {Q : β → β → Prop} {k : Nat}
    (f g : BinaryAction α eraseA D β eraseB Q k) : Prop :=
  ∀ x y, D x y → ActionRel (f.run x) (g.run y)

theorem binaryRel_refl {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {β : Type v} {eraseB : β → Value} {Q : β → β → Prop} {k : Nat}
    (f : BinaryAction α eraseA D β eraseB Q k) : BinaryRel f f := f.respect

theorem binaryRel_symm {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {β : Type v} {eraseB : β → Value} {Q : β → β → Prop} {k : Nat}
    (hD : RelLaws D) (hQ : RelLaws Q)
    {f g : BinaryAction α eraseA D β eraseB Q k} (h : BinaryRel f g) : BinaryRel g f :=
  fun x y hxy => actionRel_symm hQ (h y x (hD.symm hxy))

theorem binaryRel_trans {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {β : Type v} {eraseB : β → Value} {Q : β → β → Prop} {k : Nat}
    (hD : RelLaws D) (hQ : RelLaws Q)
    {f g h : BinaryAction α eraseA D β eraseB Q k}
    (hfg : BinaryRel f g) (hgh : BinaryRel g h) : BinaryRel f h := fun x y hxy =>
  actionRel_trans hQ (hfg x y hxy) (hgh y y (hD.trans (hD.symm hxy) hxy))

/-- An actual binary action from the configured evaluator's source
member image. All relations and erasures on arguments are allowed. -/
def binaryAction {α : Type u} (eraseA : α → Value) (D : α → α → Prop)
    {β : Type v} (eraseB : β → Value) (Q : β → β → Prop)
    {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level} {k : Nat}
    (hm : E.members r = some m) (he : eligible m = some (2, l))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level)
    (hk : eval ν (instLevel ls l) = some k) : BinaryAction α eraseA D β eraseB Q k where
  value := image E F ν ρ (.const r ls)
  run := fun x =>
    { value := NeutralPi.applyValue (image E F ν ρ (.const r ls)) (eraseA x)
      run := fun _ => resultCode k r
      erased := by
        intro y
        change ValueEq (NeutralPi.applyValue
          (NeutralPi.applyValue (image E F ν ρ (.const r ls)) (eraseA x)) (eraseB y))
          (eraseCode (resultCode k r))
        rw [resultCode_value]
        have h := image_telescope hm he F ν ρ ls
        rw [hk] at h
        exact (NeutralPi.applyValue_congr
          (NeutralPi.applyValue_congr h (ValueEq.refl (eraseA x)))
          (ValueEq.refl (eraseB y))).trans
          (NativeTelescopeValues.two_applications (some k) r (eraseA x) (eraseB y))
      respect := fun _ _ _ => codeRel_refl (resultCode k r) }
  erased := fun _ => ValueEq.refl _
  respect := fun _ _ _ _ _ _ => codeRel_refl (resultCode k r)

/-- The binary proposition instance quantifies over the entire retained
candidate carrier. Neither original candidate is modified or selected
from its erasure. -/
def propositionAction {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) (he : eligible m = some (2, .zero))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    BinaryAction (Code 0) (fun C => (view 0 C).value) (CodeRelated 0)
      (Code 0) (fun C => (view 0 C).value) (CodeRelated 0) 0 :=
  binaryAction (fun C => (view 0 C).value) (CodeRelated 0)
    (fun C => (view 0 C).value) (CodeRelated 0) hm he F ν ρ [] rfl

theorem propositionAction_result {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) (he : eligible m = some (2, .zero))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (C D : Code 0) :
    ((propositionAction hm he F ν ρ).run C).run D = resultCode 0 r := rfl

theorem propositionAction_erased {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) (he : eligible m = some (2, .zero))
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (C D : Code 0) :
    ValueEq (NeutralPi.applyValue
      (NeutralPi.applyValue (image E F ν ρ (.const r [])) (view 0 C).value)
      (view 0 D).value) (NativeMemberValues.value (some 0) r) :=
  ((propositionAction hm he F ν ρ).run C).erased D

end Rcic.Declarative.Ann.LR3.EnvironmentTelescopeAction
