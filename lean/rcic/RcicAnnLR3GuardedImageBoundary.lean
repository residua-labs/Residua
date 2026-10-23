import rcic.RcicAnnLR3GuardedOpenEqCall
import rcic.RcicAnnLR3GuardedReaderControl

/-!
# Actual branch type images and tag-free neutral identity

The actual Pi minor has a tagged Pi payload. A free native neutral code has
a tagged constant payload. A finite observation separates their raw type
images, even in the admitted positive K control whose call image equals its
minor image. That K equation supplies no equality with the arbitrary native
neutral fallback.

KernelIso retains type_image as well as element images. Consequently a
KernelIso-level conversion arm continues to separate native neutral names,
without changing the existing tag-sensitive CodeRelated relation.
This is a boundary for the common-image premise and current suppliers;
it is not a source-language counterexample. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.GuardedImageBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TaggedSaturatedTower TaggedKClosure

universe u v

theorem neutral_kernelRelated_iff (k r s : Nat) :
    KernelRelated (Code.neutral.{u} k r).kernel (Code.neutral.{u} k s).kernel ↔
      r = s := by
  constructor
  · rintro ⟨e⟩
    exact native_value_name_injective (some k) r s e.type_image
  · intro h
    cases h
    exact kernelRelated_refl _

theorem kernelRelated_type_image {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (h : KernelRelated A B) : ValueEq A.per.value B.per.value := by
  rcases h with ⟨e⟩
  exact e.type_image

/-- Sort-level comparison uses exact type images and definedness, without
requiring a constructor-tag equality premise. -/
theorem kernel_level_unique {k l : Nat} (A : Kernel.{u} k) (B : Kernel.{v} l)
    (h : ValueEq A.per.value B.per.value) : k = l :=
  Option.some.inj (sortMember_unique A.per.level
    (sortMember_congr h.symm B.per.level) A.per.defined)

theorem result_translation (ν : Valuation) :
    UnitModel.translate ν EqLargeFixture.result =
      taggedTerm (some 1) (.pi (sortTerm (some 0)) (sortTerm (some 0))) := rfl

/-- The native-neutral name probe cannot occur in the actual Pi type image. -/
theorem result_probe_not_member (ν : Valuation) (ρ : EnvI) (name : Nat) :
    ¬ TaggedKEvaluation.image ν ρ EqLargeFixture.result (nativeNameProbe name) := by
  intro hc
  have ht := ((TaggedKEvaluation.denote_agrees ν ρ
    (e := EqLargeFixture.result) (by trivial)) (nativeNameProbe name)).mp hc
  change ApproxI ρ (UnitModel.translate ν EqLargeFixture.result)
    (nativeNameProbe name) at ht
  rw [result_translation ν] at ht
  have h := approxI_foldApps_const_inv
    (r := 10) (ls := [])
    (xs := [levelTerm (some 1), .pi (sortTerm (some 0)) (sortTerm (some 0))]) ht
  rcases h with hbot | ⟨us, he, hs⟩
  · cases hbot
  · change (.spine 10 [.bot, .spine name []] : CptI) = .spine 10 us at he
    cases he
    cases hs with
    | cons hlevel hs =>
      cases hs with
      | cons hp hs =>
        cases hp

theorem result_image_not_native (ν : Valuation) (ρ : EnvI)
    (k : Option Nat) (name : Nat) :
    ¬ ValueEq (TaggedKEvaluation.image ν ρ EqLargeFixture.result)
      (NativeMemberValues.value k name) := by
  intro h
  exact result_probe_not_member ν ρ name
    ((h (nativeNameProbe name)).mpr (nativeNameProbe_member k name))

theorem open_minor_not_neutral (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (name : Nat) :
    ¬ ValueEq (GuardedOpenEqCall.minorCode ν a).view.value
      (Code.neutral.{0} 1 name).view.value :=
  result_image_not_native ν (GuardedReaderSource.rawEnvironment a) (some 1) name

theorem control_minor_not_neutral (ν : Valuation) (name : Nat) :
    ¬ ValueEq (TaggedKCoherenceBoundary.minorCode ν).view.value
      (Code.neutral.{0} 1 name).view.value := by
  intro h
  exact result_image_not_native ν UnitModel.fixtureEnv (some 1) name
    ((TaggedKCoherenceBoundary.minorCode_image ν).symm.trans h)

theorem no_common_image {A B : Value} (h : ¬ ValueEq A B) :
    ¬ ∃ V : Value, ValueEq V A ∧ ValueEq V B := by
  rintro ⟨V, hA, hB⟩
  exact h (hA.symm.trans hB)

theorem control_no_common_image (ν : Valuation) (name : Nat) :
    ¬ ∃ V : Value,
      ValueEq V (TaggedKCoherenceBoundary.minorCode ν).view.value ∧
      ValueEq V (Code.neutral.{0} 1 name).view.value :=
  no_common_image (control_minor_not_neutral ν name)

theorem open_no_common_image (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (name : Nat) :
    ¬ ∃ V : Value,
      ValueEq V (GuardedOpenEqCall.minorCode ν a).view.value ∧
      ValueEq V (Code.neutral.{0} 1 name).view.value :=
  no_common_image (open_minor_not_neutral ν a name)

theorem control_kernels_not_related (ν : Valuation) (name : Nat) :
    ¬ KernelRelated (TaggedKCoherenceBoundary.minorCode ν).kernel
      (Code.neutral.{0} 1 name).kernel := by
  intro h
  exact control_minor_not_neutral ν name (kernelRelated_type_image h)

/-- Every source, guard, image and member premise is supplied. The actual K
equation identifies call and minor; it still does not produce a common image
for that minor and the free native neutral fallback. -/
theorem positive_K_common_image_boundary (ν : Valuation) (name : Nat) :
    TaggedKCoherenceBoundary.AtTarget ν (GuardedReaderControl.readFrame ν name) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    Guard (GuardedReaderControl.readFrame ν name) ∧
    ValueEq (TaggedKEvaluation.image ν UnitModel.fixtureEnv
      (EqLargeFixture.call (.bvar 0)))
      (TaggedKCoherenceBoundary.minorCode ν).view.value ∧
    (∃ m : (TaggedKCoherenceBoundary.minorCode ν).Element,
      (TaggedKCoherenceBoundary.minorCode ν).view.relation m m) ∧
    (∃ n : (Code.neutral.{0} 1 name).Element,
      (Code.neutral.{0} 1 name).view.relation n n) ∧
    ¬ ∃ V : Value,
      ValueEq V (TaggedKCoherenceBoundary.minorCode ν).view.value ∧
      ValueEq V (Code.neutral.{0} 1 name).view.value :=
  ⟨GuardedReaderControl.readFrame_atTarget ν name, EqLargeFixture.conversion,
    GuardedReaderControl.readFrame_guard ν name,
    (GuardedReaderControl.readCall_actual_image ν name).symm,
    TaggedKCoherenceBoundary.minor_inhabited ν,
    ⟨(Code.neutral.{0} 1 name).view.point 0,
      (Code.neutral.{0} 1 name).view.point_member 0⟩,
    control_no_common_image ν name⟩

end Rcic.Declarative.Ann.LR3.GuardedImageBoundary
