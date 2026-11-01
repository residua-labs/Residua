import rcic.RcicF3NormDataRecPkg
import rcic.RcicF3StepWDApex

/-!
# The DATA group step after a small normalized-frame producer

SmallFrameAt keeps the literal GroupStepAt walk, both original bounds,
predecessor invariant and every faithful-table quantifier. Its conclusion
is only a small closed candidate for the actual normalized descriptor.
The original constructor walk, stored recursor membership and stable
legacy iota are then produced by the DATA consumers and composed here.

The frame supplier is an explicit remaining production obligation. This
module does not produce it universally or replace unchecked StepAG. The
optional checked adapter reads parameter equality from the existing D
condition without changing either check. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Exactly the semantic size requirement at a GroupStepAt context. No
reader-soundness, constructor-step, recursor or iota callback is supplied. -/
def SmallFrameAt (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm,
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  NormRole.GInv P K hE →
  ∀ ctx : Nat → Role,
    (∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ plans : EvalRole.Plans,
    (∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
  ∀ μ, EvalRole.Faithful role P μ ctx plans E' →
    ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A

/-- Full new group composition; the sole additional semantic input is
the literal small normalized candidate supplier above. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hSmall : SmallFrameAt P K hE hfam hctors hrec hmem) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro hAg hBound hBoundD hPred ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hsmall := hSmall hAg hBound hBoundD hPred ctx hctx plans hplans μ hFaith
  have hAll := NormDataMember.sound_of_small_frame P μ K hE hfam hctors hrec hmem
    hAg hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hsmall hType
  have hPkg := NormDataRecPkg.rec_pkg P μ K hE hfam hctors hrec hmem
    hAg hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hsmall hType
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful role P μ ctx plans E :=
    fun r m hm => hFaith r m (hsubE r m hm)
  have hPrior := hPred ctx hctxE plans hplansE μ hFaithE
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  refine ⟨hAll, ?_⟩
  intro Efin hsub r m hm hk
  rcases group_member_cases hmem hL hrr p.node hm with
    hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · exact hPrior.2 Efin (fun s n hn => hsub s n (hsubE s n hn)) r m hold hk
  · rw [hfam] at hk
    cases hk
  · exact hPkg.2 Efin hsub
  · rw [(p.node.a.constructorViews j).hasClass] at hk
    cases hk

/-- The original selected-node D condition supplies the parameter equality;
the small-frame supplier remains the only added semantic production input. -/
theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hSmall : SmallFrameAt P K hE hfam hctors hrec hmem) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem :=
  group_step P K hE hfam hctors hrec hmem hType
    ((Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp).1 hSmall

end Rcic.F3.PSet.NormDataGroup
