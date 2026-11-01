import rcic.RcicF3NormDataRecMem
import rcic.RcicF3NormDataPrefix

/-!
# Complete DATA stored-member soundness after a small normalized frame

The actual bounded constructor walk produces the reader environment before
the new recursor. Its soundness uses only predecessor iota. The stored
recursor telescope then supplies the actual parameters, extra-universe
motive, stored minors, indices and data major to the normalized recursion
producer. Full faithfulness supplies every installed value equation.

The only additional semantic production input is a small closed normalized
candidate. The literal walk, BoundG, BoundDG and checked parameter equality
are retained. No current-recursion membership, iota, reader-soundness or
local-minor callback is assumed. The result is AllSound; stable iota and
universal DATA small-frame production remain separate. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataMember
open Rcic.Declarative Rcic.Model.PS RawFamily

theorem sound_of_small_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hsmall : ∃ A,
      Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    AllSound P μ K E' := by
  have hPrefix := NormDataPrefix.sound_of_small_frame P μ K hE hfam hctors hrec hmem
    hAg hBound hPred ctx plans hctx hplans hFaith hsmall
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful role P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hR := NormDataRecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred ctx plans hctxE hplansE hFaithE
    ctx plans hctx hplans hFaith hsmall hType
    (fun fullvs _ _ => hPrefix.2 (σOf fullvs) _)
  have hrm : E'.members rr = some rm := groupMembersT_installed hmem
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  intro r m hm
  by_cases hr : r = rr
  · subst r
    have hm' : m = rm := Option.some.inj (hm.symm.trans hrm)
    subst m
    exact hR
  · exact hPrefix.1 r m hm hr

/-- The original stored recursor member is a consequence of the complete
member producer, with its reader supplied by the preceding actual walk. -/
theorem member_sound_of_small_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hsmall : ∃ A,
      Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    MemberSound P μ K rr rm :=
  sound_of_small_frame P μ K hE hfam hctors hrec hmem hAg hBound hBoundD hpar hPred
    ctx plans hctx hplans hFaith hsmall hType rr rm
    (groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))))

end Rcic.F3.PSet.NormDataMember
