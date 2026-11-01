import rcic.RcicF3PropOnlyEmptyMirrorFixture
import rcic.RcicF3DBoundDefs

/-!
# A source-syntax obstruction to extending EmptyMirror recursively

This module concerns the original BoundDG predicate. It does not assume a
stronger parameter fit or a stronger bound. A bounded typing pays every
literal sort occurring in its subject, independently of the local context
and independently of conversions around the subject.

Consequently, putting EmptyMirror's bad high-universe beta redex directly
in a recursive field cannot provide a counterexample under original
BoundDG: at the high recursor instance, every alternative typing of that
same field fails the unchanged bound. This is an exclusion of one proposed
construction, not a universal beta-fit theorem and not a root refutation.

Source draft only. No native Lean process has been run for this module.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderBetaSourceBounds
open Rcic.Declarative
open Rcic.Declarative.PropOnlyEmptyMirror

/-- The sort occurrences in the subject alone consume this part of LOKt.
Local lookup annotations are deliberately not included. -/
def SortBudget (σ : Nat → Nat) (N : Nat) : Expr Nat → Prop
  | .sort l => evalTotal σ l + 1 ≤ N
  | .bvar _ => True
  | .const _ _ => True
  | .pi A B => SortBudget σ N A ∧ SortBudget σ N B
  | .lam A b => SortBudget σ N A ∧ SortBudget σ N b
  | .app f a => SortBudget σ N f ∧ SortBudget σ N a
  | .letE A v b => SortBudget σ N A ∧ SortBudget σ N v ∧ SortBudget σ N b
  | .lit _ => True

variable {E : ResolvedEnv} {n : Nat}

/-- This induction uses the actual bounded source derivation. It makes no
claim about bounded typings of arbitrary conversion endpoints. -/
theorem of_lokt (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {e T : Expr Nat} →
    (d : HasTyT E n Γ e T) → LOKt σ N K d → SortBudget σ N e
  | _, _, _, .sort _ _, hd => hd
  | _, _, _, .bvar _ _ _ _, _ => True.intro
  | _, _, _, .const _ _ _ _ _ _ _, _ => True.intro
  | _, _, _, .pi _ _ _ _ _ dA dB, hd =>
      ⟨of_lokt σ N K dA hd.2.2.1, of_lokt σ N K dB hd.2.2.2⟩
  | _, _, _, .lam _ _ _ _ _ dA db, hd =>
      ⟨of_lokt σ N K dA hd.1, of_lokt σ N K db hd.2⟩
  | _, _, _, .app _ _ _ _ _ df da, hd =>
      ⟨of_lokt σ N K df hd.1, of_lokt σ N K da hd.2⟩
  | _, _, _, .letE _ _ _ _ _ _ dA dv db, hd =>
      ⟨of_lokt σ N K dA hd.1,
        of_lokt σ N K dv hd.2.1, of_lokt σ N K db hd.2.2⟩
  | _, _, _, .lit _ _ _ _, _ => True.intro
  | _, _, _, .conv _ _ _ _ _ d _, hd => of_lokt σ N K d hd.1

/-- A type expression wrapped in the same beta redex as EmptyMirror's
own parameter. The body is shifted across the unused lambda binder. -/
noncomputable def highWrap (A : Expr Nat) : Expr Nat :=
  .app (.lam (.sort domLevel) (Rcic.Declarative.lift 0 1 A)) (.sort argLevel)

theorem highWrap_not_budget (σ : Nat → Nat) (hσ : σ 0 = 3)
    (A : Expr Nat) : ¬ SortBudget σ 4 (highWrap A) := by
  intro h
  have hs := h.1.1
  change σ 0 + 1 + 1 + 1 ≤ 4 at hs
  rw [hσ] at hs
  exact (by decide : ¬ (6 ≤ 4)) hs

/-- The rejection is independent of the chosen typing derivation, its
target type, its global environment, and its possibly nonfitting context. -/
theorem highWrap_not_lokt (σ : Nat → Nat) (hσ : σ 0 = 3)
    (K : Nat → Nat) {Γ : LCtx} {A T : Expr Nat}
    (d : HasTyT E n Γ (highWrap A) T) : ¬ LOKt σ 4 K d := by
  intro hd
  exact highWrap_not_budget σ hσ A (of_lokt σ 4 K d hd)

/-- The proposed field reads to the complete canonical family endpoint.
This is source reader evidence, not an assertion that this field was
admitted in the existing empty-field group. -/
theorem recursive_read :
    piTelescopeFuel ePre 3 (highWrap (famApp (.bvar 0))) =
      some ([], famApp (.bvar 0)) := rfl

/-- The proposed source is genuinely typed in the own-parameter prefix.
Its high-instance bound, rather than unbounded typing, is the obstruction. -/
noncomputable def recursive_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTyT E 1 [.assumption ownParam]
      (highWrap (famApp (.bvar 0))) (.sort .zero) :=
  .app [.assumption ownParam]
    (.lam (.sort domLevel) (famApp (.bvar 1))) (.sort argLevel)
    (.sort domLevel) (.sort .zero)
    (.lam [.assumption ownParam] (.sort domLevel) (.succ domLevel)
      (famApp (.bvar 1)) (.sort .zero)
      (.sort [.assumption ownParam] domLevel)
      (famApp_typed hF [.assumption (.sort domLevel), .assumption ownParam] 1 rfl))
    (.sort [.assumption ownParam] argLevel)

/-- Original BoundDG itself excludes this field at the permitted high
instance. No constructor-bound comparison and no own-parameter fit is
added. The statement ranges over an actual admitted group and RecNode. -/
theorem original_boundDG_excludes_highWrap
    (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (j : Fin node.a.constructors.length)
    (k : Fin (node.a.constructorViews j).fields.length)
    (vs : List Nat) (hlen : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hσ : σOf vs 0 = 3)
    (A : Expr Nat)
    (hfield : (node.a.constructorViews j).fields[k] = highWrap A) : False := by
  obtain ⟨l, d, hd⟩ := hD.2 node j vs hlen hvs k
  have hb := of_lokt (σOf vs) 4 K d hd
  rw [hfield] at hb
  exact highWrap_not_budget (σOf vs) hσ A hb

end Rcic.F3.PSet.ReaderBetaSourceBounds

#print axioms Rcic.F3.PSet.ReaderBetaSourceBounds.of_lokt
#print axioms Rcic.F3.PSet.ReaderBetaSourceBounds.highWrap_not_lokt
#print axioms Rcic.F3.PSet.ReaderBetaSourceBounds.original_boundDG_excludes_highWrap
