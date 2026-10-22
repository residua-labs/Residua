import rcic.RcicAnnLR3SaturatedFamilyCode
import rcic.RcicAnnLR3NativeMemberValues

/-!
# Native typed-neutral leaves for the saturated family interface

The existing application closure already contains native tagged values,
with their partial observations intact. Thus the family interface accepts
the very same typed neutrals used for universe reflection, at every
`Option Nat` level, including `none`. This is an explicit bridge between
the two carriers, not an identification with the sparse legacy values.
No source recursor or universe attachment is asserted. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SaturatedFamilyNative

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedInductive NeutralDataFamily

universe u v w

theorem tagged_neutral (ρ : EnvI) (k : Option Nat) (payload : Expr Nat) :
    CandidatePi.Neutral (denI ρ (taggedTerm k payload)) := by
  have head : CandidatePi.Neutral (denI ρ (.const 10 [])) :=
    CandidatePi.neutral_congr
      (FunctionEval.constant_environment EnvI.bot ρ 10 []) (.atom 10)
  have first : CandidatePi.Neutral
      (denI ρ (.app (.const 10 []) (levelTerm k))) :=
    CandidatePi.neutral_congr (NeutralPi.applyValue_denI ρ _ _)
      (.app head _ (CandidatePi.denI_nonempty ρ (levelTerm k)))
  exact CandidatePi.neutral_congr (NeutralPi.applyValue_denI ρ _ _)
    (.app first _ (CandidatePi.denI_nonempty ρ payload))

theorem member_neutral (k : Option Nat) (name : Nat) :
    CandidatePi.Neutral (NativeMemberValues.value k name) :=
  tagged_neutral EnvI.bot k (.const name [])

def reflectTyped {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (k : Option Nat) (name : Nat) : SaturatedFamilyCode.Element S ctor i :=
  SaturatedFamilyCode.reflect S ctor i (NativeMemberValues.value k name)
    (member_neutral k name)

theorem typed_reflection {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (k : Option Nat) (name : Nat) :
    SaturatedFamilyCode.Relation (reflectTyped S ctor i k name)
      (reflectTyped S ctor i k name) ∧
    (reflectTyped S ctor i k name).value = NativeMemberValues.value k name ∧
    SortMember k (reflectTyped S ctor i k name).value ∧
    TypeDefined (reflectTyped S ctor i k name).value :=
  ⟨(reflectTyped S ctor i k name).admitted, rfl,
    NativeMemberValues.value_level k name, NativeMemberValues.value_defined k name⟩

theorem typed_application_reflection {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (k : Option Nat) (name : Nat) (a : Value)
    (ha : CandidatePi.NonemptyValue a) :
    SaturatedFamilyCode.Relation
      (SaturatedFamilyCode.reflectApplication S ctor i
        (NativeMemberValues.value k name) (member_neutral k name) a ha)
      (SaturatedFamilyCode.reflectApplication S ctor i
        (NativeMemberValues.value k name) (member_neutral k name) a ha) ∧
    (SaturatedFamilyCode.reflectApplication S ctor i
      (NativeMemberValues.value k name) (member_neutral k name) a ha).value =
      NeutralPi.applyValue (NativeMemberValues.value k name) a :=
  SaturatedFamilyCode.application_reflection S ctor i _ (member_neutral k name) a ha

end Rcic.Declarative.Ann.LR3.SaturatedFamilyNative
