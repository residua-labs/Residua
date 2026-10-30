import rcic.RcicF3StepWOpen

/-!
# Exact finite W check with a named refusal

`refusalOf np hw` reuses the landed level-order and finite-walk deciders.
It runs on one group walk and a supplied parameter count, without deciding
the unbounded quantification over `RecNode` in `GroupWChecked`.

Acceptance implies semantic agreement without any global W hypothesis.
At every literal `OpenArm`, acceptance is also necessary, and a refusal
certifies a counterexample. All open-arm checks passing is still equivalent
to `StepWHyp`; no universal pass result is supplied. This diagnostic changes
no admission judgment or policy. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWRefusal

open Rcic.Declarative Rcic.F3.PSet Rcic.F3.StepWMin Rcic.F3.StepWCheck
open Rcic.F3.StepWOpen

inductive Refusal where
  | gapSortBound
  deriving DecidableEq, Repr

/-- The existing W-check refusal name, now returned by a total function. -/
def Refusal.residue : Refusal → String
  | .gapSortBound => "[rcic-f3-stepw-wcheck-refusal]"

/-- Finite diagnostic at a group walk and the recursor's parameter count. -/
def refusalOf (np : Nat) {S Ew E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (hw : GroupMembersT S Ew ms E') :
    Option Refusal :=
  if WalkAgree (AgreeAtDec np) hw then none else some .gapSortBound

/-- Exact success criterion of the finite diagnostic. -/
theorem refusalOf_none_iff (np : Nat) {S Ew E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (hw : GroupMembersT S Ew ms E') :
    refusalOf np hw = none ↔ WalkAgree (AgreeAtDec np) hw := by
  simp [refusalOf]

/-- Exact failure criterion; no admitted counterexample is assumed to exist. -/
theorem refusalOf_gapSortBound_iff (np : Nat) {S Ew E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (hw : GroupMembersT S Ew ms E') :
    refusalOf np hw = some .gapSortBound ↔ ¬ WalkAgree (AgreeAtDec np) hw := by
  simp [refusalOf]

/-- Check soundness on any walk, without a global completeness premise. -/
theorem agrees_of_none (np : Nat) {S Ew E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} (hw : GroupMembersT S Ew ms E')
    (h : refusalOf np hw = none) : WalkAgree (AgreeAt np) hw :=
  walkAgree_congr (fun _ _ _ _ => agreeAt_of_agreeAtDec) hw
    ((refusalOf_none_iff np hw).mp h)

/-- Semantic-to-checked completeness at the literal admitted open arm. -/
theorem checked_of_agrees (w : OpenArm) (h : w.Agrees) : w.Checked :=
  walkAgreeDec_of_walkAgree_gen w.hE w.hfam w.hctors w.hrec w.hmem
    (walkRec_of_group w.hmem) w.node w.uniform w.hmem
    (fun _ hh => hh) (fun _ _ hh => hh) h

/-- At a literal open arm success is necessary and sufficient. -/
theorem openArm_none_iff (w : OpenArm) :
    refusalOf w.node.a.family.parameters.length w.hmem = none ↔ w.Agrees := by
  constructor
  · exact agrees_of_none _ w.hmem
  · intro h
    exact (refusalOf_none_iff _ w.hmem).mpr (checked_of_agrees w h)

/-- A named refusal certifies failure of the semantic conclusion itself. -/
theorem openArm_refusal_iff (w : OpenArm) :
    refusalOf w.node.a.family.parameters.length w.hmem = some .gapSortBound ↔
      ¬ w.Agrees := by
  rw [refusalOf_gapSortBound_iff]
  constructor
  · intro hn h
    exact hn (checked_of_agrees w h)
  · intro hn h
    exact hn (walkAgree_congr (fun _ _ _ _ => agreeAt_of_agreeAtDec) w.hmem h)

/-- A refusal on an actual admitted open arm would refute global W. -/
theorem refusal_refutes_hyp (w : OpenArm)
    (h : refusalOf w.node.a.family.parameters.length w.hmem = some .gapSortBound) :
    ¬ StepWHyp :=
  counterexample_refutes_hyp ⟨w, (openArm_refusal_iff w).mp h⟩

/-- The global no-refusal premise is exactly the original conjecture. -/
theorem all_checks_iff_hyp :
    (∀ w : OpenArm, refusalOf w.node.a.family.parameters.length w.hmem = none) ↔
      StepWHyp := by
  constructor
  · intro h
    exact hyp_iff_all_openArm.mpr (fun w => (openArm_none_iff w).mp (h w))
  · intro h w
    exact (openArm_none_iff w).mpr (hyp_iff_all_openArm.mp h w)

/-- Adapter to the existing apex input; its global premise remains open. -/
theorem stepWChecked_of_all_checks
    (h : ∀ w : OpenArm, refusalOf w.node.a.family.parameters.length w.hmem = none) :
    StepWChecked :=
  stepWChecked_of_hyp (all_checks_iff_hyp.mp h)

/-- Closed evaluation of the admitted Eq-prefix open-arm fixture. -/
theorem eqW_no_refusal : refusalOf 0 eqWMembersT = none := by decide

end Rcic.F3.StepWRefusal
