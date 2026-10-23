import rcic.RcicAnnLR3GuardedKernel
import rcic.RcicAnnLR3GuardedOpenEqCall

/-! Constructive conditional type images.

The tag predicate is decidable by shallow observation shape; no decision of
the semantic guard is used. A shared full-tag observation gives definedness
of the conditional value. This hypothesis is weaker than equality of the
branch images and holds for the actual Pi minor/native-neutral pair.
This constructs type-image data for the suspended kernel. It does not prove
a source recursor-output evaluator equation. closure_claim = 0. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedTypeImage

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TaggedSaturatedTower GuardedKernel

universe u v

/-- Only the head shape and a natural-number comparison are inspected.
No equality decision for arbitrary compact payloads is required. -/
def levelShapeDecision (i : Option Nat) (a : CptI) :
    Decidable (a = .bot ∨ a = .spine (levelRef i) []) := by
  cases a with
  | bot => exact .isTrue (Or.inl rfl)
  | sort => exact .isFalse (by rintro (h | h) <;> cases h)
  | pi a steps => exact .isFalse (by rintro (h | h) <;> cases h)
  | lam steps => exact .isFalse (by rintro (h | h) <;> cases h)
  | spine r args =>
    cases args with
    | nil =>
      by_cases hr : r = levelRef i
      · subst r
        exact .isTrue (Or.inr rfl)
      · exact .isFalse (by
          rintro (h | h)
          · cases h
          · exact hr (CptI.spine.inj h).1)
    | cons a args => exact .isFalse (by rintro (h | h) <;> cases h)

def tagAtDecision (i : Option Nat) (c : CptI) : Decidable (TagAt i c) := by
  cases c with
  | bot => exact .isTrue .bot
  | sort => exact .isFalse (by intro h; cases h)
  | pi a steps => exact .isFalse (by intro h; cases h)
  | lam steps => exact .isFalse (by intro h; cases h)
  | spine r args =>
    cases args with
    | nil => exact .isFalse (by intro h; cases h)
    | cons a args =>
      cases args with
      | nil => exact .isFalse (by intro h; cases h)
      | cons payload rest =>
        cases rest with
        | cons extra rest => exact .isFalse (by intro h; cases h)
        | nil =>
          by_cases hr : r = 10
          · subst r
            cases levelShapeDecision i a with
            | isTrue ha => exact .isTrue (.tagged a payload ha)
            | isFalse ha =>
              exact .isFalse (by
                intro h
                cases h with
                | tagged a payload hlevel => exact ha hlevel)
          · exact .isFalse (by
              intro h
              cases h with
              | tagged a payload hlevel => exact hr rfl)

theorem tagAt_stable (i : Option Nat) (c : CptI)
    (h : ¬ ¬ TagAt i c) : TagAt i c := by
  cases tagAtDecision i c with
  | isTrue hc => exact hc
  | isFalse hc => exact False.elim (h hc)

/-- Stable observation shape suffices to preserve sort membership through
the two implications. The semantic guard itself need not be decidable. -/
theorem conditional_sortMember {G : Prop} {i : Option Nat} {M F : Value}
    (hm : SortMember i M) (hf : SortMember i F) :
    SortMember i (conditionalValue G M F) := by
  intro c hc
  apply tagAt_stable i c
  intro hn
  have hG : ¬ G := fun hg => hn (hm c (hc.1 hg))
  exact hn (hf c (hc.2 hG))

theorem conditional_defined {G : Prop} {M F : Value}
    (i : Option Nat) (payload : CptI)
    (hm : M (.spine 10 [.spine (levelRef i) [], payload]))
    (hf : F (.spine 10 [.spine (levelRef i) [], payload])) :
    TypeDefined (conditionalValue G M F) :=
  ⟨i, payload, ⟨fun _ => hm, fun _ => hf⟩⟩

/-- Total conditional type-image construction from a shared defined probe.
Neither an equality of the branch images nor a decision of G is required. -/
def ofSharedProbe (G : Prop) {k : Nat} (M : Kernel.{u} k) (F : Kernel.{v} k)
    (payload : CptI)
    (hm : M.per.value (.spine 10 [.spine (levelRef (some k)) [], payload]))
    (hf : F.per.value (.spine 10 [.spine (levelRef (some k)) [], payload])) :
    TypeImage G M F where
  value := conditionalValue G M.per.value F.per.value
  level := conditional_sortMember M.per.level F.per.level
  defined := conditional_defined (some k) payload hm hf
  yes_image := conditionalValue_true G M.per.value F.per.value
  no_image := conditionalValue_false G M.per.value F.per.value

theorem ofSharedProbe_value (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k) (payload : CptI)
    (hm : M.per.value (.spine 10 [.spine (levelRef (some k)) [], payload]))
    (hf : F.per.value (.spine 10 [.spine (levelRef (some k)) [], payload])) :
    (ofSharedProbe G M F payload hm hf).value =
      conditionalValue G M.per.value F.per.value := rfl

def probe (i : Option Nat) : CptI :=
  .spine 10 [.spine (levelRef i) [], .bot]

theorem tagged_probe (ρ : EnvI) (i : Option Nat) (payload : Expr Nat) :
    denI ρ (taggedTerm i payload) (probe i) :=
  approxI_famApp 10 []
    (.cons (.const ρ (levelRef i) []) (.cons (.bot ρ payload) .nil))

theorem native_neutral_probe (k name : Nat) :
    (Code.neutral.{u} k name).view.value (probe (some k)) :=
  tagged_probe EnvI.bot (some k) (.const name [])

theorem pi_minor_probe (ν : Valuation) (a : GuardedReaderSource.IndexAssignment) :
    (GuardedOpenEqCall.minorCode ν a).view.value (probe (some 1)) := by
  rw [GuardedOpenEqCall.minorCode_image]
  apply (TaggedKEvaluation.denote_agrees ν (GuardedReaderSource.rawEnvironment a)
    (e := EqLargeFixture.result) TaggedKEvaluation.result_literalFree _).mpr
  exact tagged_probe (GuardedReaderSource.rawEnvironment a) (some 1)
    (.pi (sortTerm (some 0)) (sortTerm (some 0)))

/-- The actual source-produced Pi minor and the actual native-neutral
fallback share this probe even though their full raw images are not equal. -/
def piNeutral (G : Prop) (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) (name : Nat) :
    TypeImage G (GuardedOpenEqCall.minorCode ν a).kernel
      (Code.neutral.{0} 1 name).kernel :=
  ofSharedProbe G _ _ .bot (pi_minor_probe ν a) (native_neutral_probe.{0} 1 name)

def source (ν : Valuation) (a : GuardedReaderSource.IndexAssignment) (name : Nat) :
    TypeImage (GuardedReaderSource.guard a) (GuardedOpenEqCall.minorCode ν a).kernel
      (Code.neutral.{0} 1 name).kernel :=
  piNeutral (GuardedReaderSource.guard a) ν a name

theorem source_value (ν : Valuation) (a : GuardedReaderSource.IndexAssignment)
    (name : Nat) :
    (source ν a name).value = conditionalValue (GuardedReaderSource.guard a)
      (GuardedOpenEqCall.minorCode ν a).view.value
      (NativeMemberValues.value (some 1) name) := rfl

theorem source_true {ν : Valuation} {a : GuardedReaderSource.IndexAssignment}
    {name : Nat} (hG : GuardedReaderSource.guard a) :
    ValueEq (source ν a name).value
      (TaggedKEvaluation.image ν (GuardedReaderSource.rawEnvironment a)
        EqLargeFixture.result) := by
  rw [← GuardedOpenEqCall.minorCode_image]
  exact (source ν a name).yes_image hG

theorem source_false {ν : Valuation} {a : GuardedReaderSource.IndexAssignment}
    {name : Nat} (hG : ¬ GuardedReaderSource.guard a) :
    ValueEq (source ν a name).value (NativeMemberValues.value (some 1) name) :=
  (source ν a name).no_image hG

end Rcic.Declarative.Ann.LR3.GuardedTypeImage
