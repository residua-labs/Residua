import rcic.RcicAnnLR3GuardedTaggedCode
import rcic.RcicAnnLR3GuardedDisjunction

/-!
# Nonvacuous exact-neutral control for the constructive repair

Both branches are certified proposition codes with the same actual type
image and explicit raw-neutral reflectors. The suspended code therefore
has unconditional exact neutral membership for every guard. On the very
same raw endpoints, the disjunctive relation requires G or not G.

The all-P source-input evidence is retained in the final control, but this
Code 0 diagnostic is not the output interpretation of the actual Code 1
large Eq call. In particular it does not supply the missing reflector for
that call's Pi action carrier. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedPropControl

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel GuardedReaderSource

def trueBranch : GuardedTaggedCode.Code.{0} 0 :=
  GuardedTaggedCode.Code.legacy (GuardDecision.propCode True)

def falseBranch : GuardedTaggedCode.Code.{0} 0 :=
  GuardedTaggedCode.Code.legacy (GuardDecision.propCode False)

def typeImage (G : Prop) :
    GuardedKernel.TypeImage G trueBranch.kernel falseBranch.kernel :=
  GuardedKernel.TypeImage.ofCommon G trueBranch.kernel falseBranch.kernel
    (GuardDecision.propCode_raw_eq True False)

def control (G : Prop) : GuardedTaggedCode.Code.{0} 0 :=
  GuardedTaggedCode.Code.guarded G trueBranch falseBranch (typeImage G)

def trueReflector : GuardedKernel.Reflector trueBranch.kernel :=
  GuardedKernel.propositionReflector.{0} (GuardDecision.propElement True)

def falseReflector : GuardedKernel.Reflector falseBranch.kernel :=
  GuardedKernel.propositionReflector.{0} (GuardDecision.propElement False)

theorem neutral_cr3 (G : Prop) (x : Value) (hx : CandidatePi.Neutral x) :
    GuardedTaggedCode.Decoded (control G).kernel x x :=
  GuardedTaggedCode.guarded_exact_reflection G trueBranch falseBranch
    (typeImage G) trueReflector falseReflector x hx

theorem neutral_comparison (G : Prop) (name : Nat) :
    GuardedTaggedCode.Decoded (control G).kernel
      (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ∧
    (GuardedDisjunction.rawRelation G
      (GuardedDisjunction.certifiedBranch True) (GuardedDisjunction.certifiedBranch False)
      (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ↔ G ∨ ¬ G) :=
  ⟨neutral_cr3 G _ (.atom name),
    GuardedDisjunction.shared_pair_iff
      (GuardedDisjunction.certified_branch_neutral_member True name)
      (GuardedDisjunction.certified_branch_neutral_member False name)⟩

/-- This observable records the constructive difference between implication
and disjunction. It does not decide the guard. -/
theorem unit_member_iff_notnot (G : Prop) :
    GuardedTaggedCode.Decoded (control G).kernel GuardDecision.unit GuardDecision.unit ↔
      ¬ ¬ G := by
  constructor
  · intro h hn
    obtain ⟨a, ha, he⟩ := (GuardedTaggedCode.decoded_member_iff
      (control G).kernel GuardDecision.unit).mp h
    change GuardedKernel.Relation a a at ha
    have hf : TaggedKClosure.Good (GuardDecision.propCode False) GuardDecision.unit :=
      ⟨a.no hn, ha.2 hn, (a.no_image hn).trans he⟩
    exact (GuardDecision.propCode_good_unit_iff False).mp hf
  · intro h
    let a : (control G).Element := {
      value := GuardDecision.unit
      yes := fun _ => ⟨GuardDecision.unit⟩
      no := fun _ => ⟨GuardDecision.unit⟩
      yes_image := fun _ => ValueEq.refl _
      no_image := fun _ => ValueEq.refl _ }
    have ha : (control G).view.relation a a :=
      ⟨fun _ => (GuardDecision.propElement_unit_iff True).mpr True.intro,
        fun hn => False.elim (h hn)⟩
    exact (GuardedTaggedCode.decoded_member_iff _ _).mpr ⟨a, ha, ValueEq.refl _⟩

/-- Every P has the actual admitted call's input-image evidence and this
separate certified proposition control. No source output code is replaced. -/
theorem interpreted_control (ν : Valuation) (P : Prop) (name : Nat) :
    ∃ i : GuardedOpenEqCall.PolicyInput,
      i.assignment = propositionAssignment P 0 ∧ GuardedOpenEqCall.InputImages ν i ∧
      GuardedTaggedCode.Decoded (control (guard i.assignment)).kernel
        (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ∧
      (GuardedDisjunction.rawRelation (guard i.assignment)
        (GuardedDisjunction.certifiedBranch True) (GuardedDisjunction.certifiedBranch False)
        (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ↔ P ∨ ¬ P) := by
  obtain ⟨i, hi, himages⟩ := GuardedOpenEqCall.proposition_policy_images ν P
  refine ⟨i, hi, himages, neutral_cr3 _ _ (.atom name), ?_⟩
  rw [(neutral_comparison (guard i.assignment) name).2, hi]
  exact or_congr (proposition_guard_iff P 0) (not_congr (proposition_guard_iff P 0))

end Rcic.Declarative.Ann.LR3.GuardedPropControl
