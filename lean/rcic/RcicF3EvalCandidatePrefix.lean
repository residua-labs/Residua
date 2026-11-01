import rcic.RcicF3RawFamilyMember
import rcic.RcicF3EvalRawTable
import rcic.RcicF3RawFamilyReads
import rcic.RcicF3CandidatePrefixFromGroup

/-!
# Candidate prefix soundness for the repaired production role

The predecessor invariant is EvalRole.GInv, with the actual indexed
recursor endpoint and its complete normalized-plan support. A fresh
candidate-family update preserves these new faithful equations. Reapplying
the same predecessor invariant then produces ordinary prefix soundness.
There is no conversion to the refuted PlanRole.GInv. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalCandidatePrefix
open Rcic.Declarative Rcic.Model.PS RawFamily CandidatePrefixFromGroup

theorem candidate_prefix_envSound
    (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hPred : EvalRole.GInv role P K hW)
    (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (hReads : EvalRole.ReadsClosed ctx plans E)
    (fd : FamData) (X : Frame) (hX : Admissible fd X)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (m : CheckedMember) (hTy : m.mtype = famType fd)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hbounded : exprLevelsBounded m.arity m.mtype = true)
    (hbody : m.body = none) (hclass : m.mclass = .inductiveM)
    (hfresh : E.members fd.fref = none)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P μ fd X)) σ K (extendEnv E fd.fref m) n := by
  let ν := table P μ fd X
  let E₁ := extendEnv E fd.fref m
  have hag : AgreeOn μ ν (Dom E) :=
    agreeOn_upd hfresh μ (ofFrame P μ fd X)
  have hFaithν : EvalRole.Faithful role P ν ctx plans E := by
    intro r m' hm vs
    have hdom : Dom E r := dom_of_members hm
    rw [← hag r hdom vs]
    exact (hFaith r m' hm vs).trans
      (EvalRole.member_agree (familyReadsCtx P ctx)
        hag r m' (plans r) (hReads r m' hm) vs)
  have hPrior := hPred ctx hctx plans hplans ν hFaithν
  have hFamily : MemberSound P ν K fd.fref m :=
    family_member_sound P μ fd X hX hf K m hTy hcl hbounded hbody
  have hsub : ∀ r m', E.members r = some m' → E₁.members r = some m' := by
    intro r m' hm
    have hne : r ≠ fd.fref := by
      intro heq
      subst r
      rw [hfresh] at hm
      cases hm
    change (extendEnv E fd.fref m).members r = some m'
    rw [members_extend_ne E fd.fref m r hne]
    exact hm
  have hAll : AllSound P ν K E₁ := by
    intro r m' hm
    by_cases heq : r = fd.fref
    · subst r
      change (extendEnv E fd.fref m).members fd.fref = some m' at hm
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      exact hFamily
    · change (extendEnv E fd.fref m).members r = some m' at hm
      rw [members_extend_ne E fd.fref m r heq] at hm
      exact hPrior.1 r m' hm
  have hI : ∀ r m', E₁.members r = some m' →
      m'.mclass = .recursorM → IotaAt P ν K E₁ r := by
    intro r m' hm hrec
    by_cases heq : r = fd.fref
    · subst r
      change (extendEnv E fd.fref m).members fd.fref = some m' at hm
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      rw [hclass] at hrec
      cases hrec
    · change (extendEnv E fd.fref m).members r = some m' at hm
      rw [members_extend_ne E fd.fref m r heq] at hm
      exact hPrior.2 E₁ hsub r m' hm hrec
  exact envSound_of P (fun _ _ hm => hm) hAll hI σ n

/-- Reapplying the actual predecessor invariant pays old soundness and iota
at both the raw table and each admissible candidate update. Freshness and
the stored typed family supply every remaining prefix hypothesis. -/
theorem group_facts (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    (hPred : EvalRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (role P μ (famDataOf node.a) vs))
    (hRaw : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a))) :
    GroupPrefixFacts P μ K E E' f rr rm fm node := by
  have hRA := EvalRole.readsOKAlong_of_plan_agree hE ctx plans hplans
    (Rcic.F3.StepDGOrder.readsOKAlong_envCtxT hE ctx hctx)
  have hReads := (EvalRole.faithful_envTable role P ctx plans
    (familyReadsCtx P ctx) hE hRA).2
  have hPrior := hPred ctx hctx plans hplans μ hFaith
  have hI : ∀ r m, E.members r = some m → m.mclass = .recursorM →
      IotaAt P μ K E' r :=
    hPrior.2 E' (groupMembersT_preserve hmem)
  obtain ⟨hfm, hty, hfree, hTF, hclosed, hbounded⟩ := syntax_facts hE hmem node
  refine ⟨⟨hPrior.1, hI⟩, hbounded, hfree, hclosed,
    raw_prefix_envSound P K μ hE hfam hmem node hPrior.1 hI hFamily hRaw,
    ?_, hTF, hfm, hty⟩
  intro X hX σ n
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hfresh : E.members (famDataOf node.a).fref = none := by
    change E.members node.a.family.ref = none
    rw [node.fam]
    exact groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hCand := candidate_prefix_envSound P K hE hPred μ ctx plans hctx hplans
    hFaith hReads (famDataOf node.a) X hX hfree fm hty
    (hTF f fm hf').1 (hTF f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf node.a).fref = f from node.fam] using hCand


end Rcic.F3.PSet.EvalCandidatePrefix
