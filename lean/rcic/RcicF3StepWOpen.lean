import rcic.RcicF3StepWCheck
import rcic.RcicF3StepWObstr

/-!
# StepW open-arm witnesses and the exact global checked face

`OpenArm` retains every premise of `StepWHyp`, including the admitted prefix,
group and recursor node. `eqWOpenArm` inhabits this local input type and its
conclusion is true. This is LOCAL non-vacuity, not a proof of the globally
quantified `StepWHyp` or of its consistency. The global truth question remains
open here. The checked global face is equivalent to that same open question.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWOpen

open Rcic.Declarative Rcic.F3.PSet Rcic.F3.StepWMin Rcic.F3.StepWCheck

/-- A single input to the literal open arm; no environment policy is added. -/
structure OpenArm where
  E : ResolvedEnv
  E' : ResolvedEnv
  f : Nat
  rr : Nat
  fm : CheckedMember
  rm : CheckedMember
  ctors : List (Nat × CheckedMember)
  hE : EnvWfT E
  hfam : fm.mclass = .inductiveM
  hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM
  hrec : rm.mclass = .recursorM
  hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'
  node : RecNode E E' f rr rm
  pend : PendW hmem node
  uniform : UniformType node.a.family.resultLevel
  outside : ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope

/-- The semantic conclusion at a single open-arm input. -/
def OpenArm.Agrees (w : OpenArm) : Prop :=
  WalkAgree (AgreeAt w.node.a.family.parameters.length) w.hmem

/-- The finite checked conclusion at the same input. -/
def OpenArm.Checked (w : OpenArm) : Prop :=
  WalkAgree (AgreeAtDec w.node.a.family.parameters.length) w.hmem

/-- The existing Eq-prefix fixture meets ALL open-arm premises. -/
def eqWOpenArm : OpenArm where
  E := eqEnvT
  E' := eqWEnv
  f := 66
  rr := 68
  fm := eqWV
  rm := eqWRec
  ctors := [(67, eqWMk)]
  hE := eqPrefixWfT
  hfam := rfl
  hctors := fun c hc => by
    simp only [List.mem_singleton] at hc
    subst hc
    rfl
  hrec := rfl
  hmem := eqWMembersT
  node := eqWNode
  pend := eqW_not_walkClass
  uniform := eqW_uniformType
  outside := eqW_not_inScope

/-- Local non-vacuity: the input conjunction does not imply False. -/
theorem openArm_nonempty : Nonempty OpenArm := ⟨eqWOpenArm⟩

/-- The inhabited input also has a true conclusion, without Premises4. -/
theorem eqWOpenArm_agrees : eqWOpenArm.Agrees := eqW_stepW

/-- A refutation at the Eq-prefix fixture is impossible. -/
theorem eqWOpenArm_not_refutation : ¬ (¬ eqWOpenArm.Agrees) :=
  fun h => h eqWOpenArm_agrees

/-- The missing direction of the global equivalence, using check soundness. -/
theorem hyp_of_stepWChecked (h : StepWChecked) : StepWHyp := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
  exact walkAgree_congr (fun _ _ _ _ => agreeAt_of_agreeAtDec) hmem
    (h hE hfam hctors hrec hmem node hPend hT hIS)

/-- A global check is exactly the conjecture; it does not discharge it. -/
theorem stepWChecked_iff_hyp : StepWChecked ↔ StepWHyp :=
  ⟨hyp_of_stepWChecked, stepWChecked_of_hyp⟩

/-- Packaging the local inputs neither weakens nor strengthens the conjecture. -/
theorem hyp_iff_all_openArm : StepWHyp ↔ ∀ w : OpenArm, w.Agrees := by
  constructor
  · intro h w
    exact h w.hE w.hfam w.hctors w.hrec w.hmem w.node w.pend w.uniform w.outside
  · intro h E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
    exact h ⟨E, E', f, rr, fm, rm, ctors, hE, hfam, hctors, hrec, hmem,
      node, hPend, hT, hIS⟩

/-- Under the tier's own decidability premise, global double-negation
non-vacuity already entails the full W conjecture. A local example cannot
satisfy this stronger requirement. -/
theorem global_nonvacuity_iff (P : Premises4) :
    (¬ (StepWHyp → False)) ↔ StepWHyp := by
  constructor
  · intro hn
    cases P.dec StepWHyp with
    | isTrue h => exact h
    | isFalse h => exact (hn h).elim
  · intro h hn
    exact hn h

/-- An actual admitted open-arm counterexample, rather than a failed supplier. -/
def Counterexample : Prop := ∃ w : OpenArm, ¬ w.Agrees

/-- A concrete counterexample suffices to refute the literal global conjecture. -/
theorem counterexample_refutes_hyp (h : Counterexample) : ¬ StepWHyp := by
  obtain ⟨w, hbad⟩ := h
  intro hW
  exact hbad (hW w.hE w.hfam w.hctors w.hrec w.hmem w.node w.pend w.uniform w.outside)

end Rcic.F3.StepWOpen
