import rcic.RcicAnnLR3GuardedKernel
import rcic.RcicAnnLR3GuardedImageBoundary

/-!
# Exact raw-neutral reflection and the actual Pi action carrier

The actual Pi minor retains an application equation into the Prop universe.
Applying a raw neutral atom to its constructed argument exposes a unary
spine, which cannot be a tagged universe member. Consequently no element of
this particular Pi action carrier erases to that atom. A raw-neutral
Reflector cannot be supplied for it, or for a true-guard kernel isomorphic
to it.

The designated action points remain inhabited and satisfy their PER. This
does not refute that weaker designated-point property, source typing, or
another Pi carrier/application/reflection design. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedNeutralBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TaggedSaturatedTower

universe u v

theorem atom_application_observed (name : Nat) (a : Value) (ha : a .bot) :
    NeutralPi.applyValue (NeutralPER.neutralAtom name) a (.spine name [.bot]) :=
  Or.inr (Or.inr ⟨name, [], .bot, rfl, NeutralPER.neutralAtom_observed name, ha⟩)

theorem atom_application_not_sort (name : Nat) (a : Value) (ha : a .bot)
    (k : Option Nat) :
    ¬ SortMember k (NeutralPi.applyValue (NeutralPER.neutralAtom name) a) := by
  intro hs
  have ht := hs (.spine name [.bot]) (atom_application_observed name a ha)
  cases ht

/-- This excludes the raw erasure already at the carrier level, independently
of any proposed extension of the carrier's PER. -/
theorem pi_element_not_atom
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (TaggedKPiFixture.code E F ν ρ).Element)
    (name : Nat) :
    ¬ ValueEq ((TaggedKPiFixture.code E F ν ρ).erase f)
      (NeutralPER.neutralAtom name) := by
  intro hf
  have he := NeutralPi.applyValue_congr hf
    (ValueEq.refl (CandidateAction.eraseCode TaggedKPiFixture.argument))
  have hs := sortMember_congr he
    (TaggedKPiFixture.application_sort E F ν ρ f TaggedKPiFixture.argument)
  exact atom_application_not_sort name
    (CandidateAction.eraseCode TaggedKPiFixture.argument)
    TaggedKPiFixture.argument_bot (some 0) hs

theorem pi_no_atom_member
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) :
    ¬ ∃ f : (TaggedKPiFixture.code E F ν ρ).Element,
      (TaggedKPiFixture.code E F ν ρ).view.relation f f ∧
      ValueEq ((TaggedKPiFixture.code E F ν ρ).erase f)
        (NeutralPER.neutralAtom name) := by
  rintro ⟨f, _, he⟩
  exact pi_element_not_atom E F ν ρ f name he

theorem pi_no_reflector
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    ¬ Nonempty (GuardedKernel.Reflector (TaggedKPiFixture.code E F ν ρ).kernel) := by
  rintro ⟨r⟩
  exact pi_element_not_atom E F ν ρ
    (r.reflect (NeutralPER.neutralAtom 0) (.atom 0)) 0
    (r.image (NeutralPER.neutralAtom 0) (.atom 0))

theorem open_minor_no_reflector (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) :
    ¬ Nonempty (GuardedKernel.Reflector (GuardedOpenEqCall.minorCode ν a).kernel) :=
  pi_no_reflector EqLargeFixture.env TaggedKEvaluation.eqSyntax ν
    (GuardedReaderSource.rawEnvironment a)

theorem control_minor_element_not_atom (ν : Valuation)
    (f : (TaggedKCoherenceBoundary.minorCode ν).Element) (name : Nat) :
    ¬ ValueEq ((TaggedKCoherenceBoundary.minorCode ν).erase f)
      (NeutralPER.neutralAtom name) :=
  pi_element_not_atom EqLargeFixture.env TaggedKEvaluation.eqSyntax ν
    UnitModel.fixtureEnv f name

/-- Exact raw-neutral reflection is transported by a genuine KernelIso.
This exposes why a branch reflector cannot be silently inferred. -/
def transportReflector {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) (r : GuardedKernel.Reflector A) : GuardedKernel.Reflector B where
  reflect := fun x hx => e.forward (r.reflect x hx)
  member := fun x hx => (e.relation _ _).mp (r.member x hx)
  image := fun x hx => (e.element_image (r.reflect x hx)).trans (r.image x hx)

theorem guarded_no_reflector_of_true
    {G : Prop} (ν : Valuation) (a : GuardedReaderSource.IndexAssignment)
    (F : Kernel.{v} 1)
    (I : GuardedKernel.TypeImage G (GuardedOpenEqCall.minorCode ν a).kernel F)
    (hG : G) :
    ¬ Nonempty (GuardedKernel.Reflector
      (GuardedKernel.kernel G (GuardedOpenEqCall.minorCode ν a).kernel F I)) := by
  rintro ⟨r⟩
  exact open_minor_no_reflector ν a
    ⟨transportReflector (GuardedKernel.isoTrue I hG) r⟩

/-- A concrete branchwise type image for the already proved positive guard.
No common image of the Pi and native-neutral types is assumed. -/
def positiveTypeImage (ν : Valuation) (fallbackName : Nat) :
    GuardedKernel.TypeImage (GuardedReaderControl.guard ν)
      (TaggedKCoherenceBoundary.minorCode ν).kernel
      (Code.neutral.{0} 1 fallbackName).kernel where
  value := (TaggedKCoherenceBoundary.minorCode ν).view.value
  level := (TaggedKCoherenceBoundary.minorCode ν).view.level
  defined := (TaggedKCoherenceBoundary.minorCode ν).view.defined
  yes_image := fun _ => ValueEq.refl _
  no_image := fun hn => False.elim (hn (TaggedKCoherenceBoundary.frame_guard ν))

def positiveKernel (ν : Valuation) (fallbackName : Nat) : Kernel.{0} 1 :=
  GuardedKernel.kernel (GuardedReaderControl.guard ν)
    (TaggedKCoherenceBoundary.minorCode ν).kernel
    (Code.neutral.{0} 1 fallbackName).kernel (positiveTypeImage ν fallbackName)

def positiveKernelIso (ν : Valuation) (fallbackName : Nat) :
    KernelIso (positiveKernel ν fallbackName)
      (TaggedKCoherenceBoundary.minorCode ν).kernel :=
  GuardedKernel.isoTrue (positiveTypeImage ν fallbackName)
    (TaggedKCoherenceBoundary.frame_guard ν)

/-- This positive suspended kernel has the actual source call's image.
The equation is inherited from the independently proved positive control,
not assumed as a condition on its reflection behavior. -/
theorem positiveKernel_call_image (ν : Valuation) (fallbackName : Nat) :
    ValueEq (positiveKernel ν fallbackName).per.value
      (TaggedKEvaluation.image ν UnitModel.fixtureEnv
        (EqLargeFixture.call (.bvar 0))) :=
  GuardedReaderControl.readCall_actual_image ν fallbackName

theorem positive_point_member (ν : Valuation) (fallbackName name : Nat) :
    (positiveKernel ν fallbackName).per.relation
      ((positiveKernel ν fallbackName).per.point name)
      ((positiveKernel ν fallbackName).per.point name) :=
  (positiveKernel ν fallbackName).per.point_member name

theorem positive_element_not_atom (ν : Valuation) (fallbackName : Nat)
    (x : (positiveKernel ν fallbackName).Element) (name : Nat) :
    ¬ ValueEq ((positiveKernel ν fallbackName).erase x)
      (NeutralPER.neutralAtom name) := by
  intro hx
  exact control_minor_element_not_atom ν
    ((positiveKernelIso ν fallbackName).forward x) name
    (((positiveKernelIso ν fallbackName).element_image x).trans hx)

theorem positive_no_reflector (ν : Valuation) (fallbackName : Nat) :
    ¬ Nonempty (GuardedKernel.Reflector (positiveKernel ν fallbackName)) := by
  rintro ⟨r⟩
  exact positive_element_not_atom ν fallbackName
    (r.reflect (NeutralPER.neutralAtom 0) (.atom 0)) 0
    (r.image (NeutralPER.neutralAtom 0) (.atom 0))

/-- The actual guard, both designated members, the native fallback reflector,
and the true-branch isomorphism are all constructed in this boundary. -/
theorem inhabited_positive_reflection_boundary (ν : Valuation) (fallbackName : Nat) :
    GuardedReaderControl.guard ν ∧
    (∃ x : (positiveKernel ν fallbackName).Element,
      (positiveKernel ν fallbackName).per.relation x x) ∧
    (∃ x : (Code.neutral.{0} 1 fallbackName).Element,
      (Code.neutral.{0} 1 fallbackName).view.relation x x) ∧
    Nonempty (GuardedKernel.Reflector (Code.neutral.{0} 1 fallbackName).kernel) ∧
    Nonempty (KernelIso (positiveKernel ν fallbackName)
      (TaggedKCoherenceBoundary.minorCode ν).kernel) ∧
    ¬ Nonempty (GuardedKernel.Reflector (positiveKernel ν fallbackName)) :=
  ⟨TaggedKCoherenceBoundary.frame_guard ν,
    ⟨(positiveKernel ν fallbackName).per.point 0, positive_point_member ν fallbackName 0⟩,
    ⟨(Code.neutral.{0} 1 fallbackName).view.point 0,
      (Code.neutral.{0} 1 fallbackName).view.point_member 0⟩,
    ⟨GuardedKernel.nativeNeutralReflector 1 fallbackName⟩,
    ⟨positiveKernelIso ν fallbackName⟩, positive_no_reflector ν fallbackName⟩

/-- One fully inhabited source packet: the actual source conversion and
call image, both branch members, the fallback reflector, and the genuine
true-branch isomorphism coexist with the two scoped obstructions. -/
theorem inhabited_source_reflection_boundary (ν : Valuation) (fallbackName : Nat) :
    TaggedKCoherenceBoundary.AtTarget ν
      (GuardedReaderControl.readFrame ν fallbackName) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    GuardedReaderControl.guard ν ∧
    ValueEq (positiveKernel ν fallbackName).per.value
      (TaggedKEvaluation.image ν UnitModel.fixtureEnv
        (EqLargeFixture.call (.bvar 0))) ∧
    (∃ m : (TaggedKCoherenceBoundary.minorCode ν).Element,
      (TaggedKCoherenceBoundary.minorCode ν).view.relation m m) ∧
    (∃ n : (Code.neutral.{0} 1 fallbackName).Element,
      (Code.neutral.{0} 1 fallbackName).view.relation n n) ∧
    (∃ x : (positiveKernel ν fallbackName).Element,
      (positiveKernel ν fallbackName).per.relation x x) ∧
    Nonempty (GuardedKernel.Reflector (Code.neutral.{0} 1 fallbackName).kernel) ∧
    Nonempty (KernelIso (positiveKernel ν fallbackName)
      (TaggedKCoherenceBoundary.minorCode ν).kernel) ∧
    (¬ ∃ V : Value,
      ValueEq V (TaggedKCoherenceBoundary.minorCode ν).view.value ∧
      ValueEq V (Code.neutral.{0} 1 fallbackName).view.value) ∧
    ¬ Nonempty (GuardedKernel.Reflector (positiveKernel ν fallbackName)) := by
  obtain ⟨hat, hconv, _, _, hm, hf, hcommon⟩ :=
    GuardedImageBoundary.positive_K_common_image_boundary ν fallbackName
  obtain ⟨hg, hp, _, hr, hi, hn⟩ :=
    inhabited_positive_reflection_boundary ν fallbackName
  exact ⟨hat, hconv, hg, positiveKernel_call_image ν fallbackName,
    hm, hf, hp, hr, hi, hcommon, hn⟩

end Rcic.Declarative.Ann.LR3.GuardedNeutralBoundary
