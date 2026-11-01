import rcic.RcicF3PointwiseRole
import rcic.RcicF3NormCandidatePrefix

/-!
# Predecessor reapplication for the separate pointwise family role

The actual arity map and unchanged normalized context/plan metadata are
retained. Produced read congruence transports the new faithful equations
through a fresh family update. The new predecessor then supplies complete
soundness and stable iota; arbitrary admissibility supplies the family-only
prefix. No constructor closure is required. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseRole
open Rcic.Declarative Rcic.Model.PS RawFamily CandidatePrefixFromGroup

theorem prior_at_frame (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hPred : GInv P K hW)
    (α : Arities) (hα : AritiesAgree α E) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r)
    (hFaith : EvalRole.Faithful (familyValue α) P μ ctx plans E)
    (fd : FamData) (X : Frame) (hfresh : E.members fd.fref = none) :
    AllSound P (RawFamily.table P μ fd X) K E ∧
      ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
        ∀ r m, E.members r = some m → m.mclass = .recursorM →
          IotaAt P (RawFamily.table P μ fd X) K Efin r := by
  have hRA := NormRole.planReadsOKAlong hW ctx plans hctx hplans
  have hReads := (EvalRole.faithful_envTable (familyValue α) P ctx plans
    (familyReadsCtx α P ctx) hW hRA).2
  let ν := RawFamily.table P μ fd X
  have hag : AgreeOn μ ν (Dom E) := agreeOn_upd hfresh μ (ofFrame P μ fd X)
  have hFaithν : EvalRole.Faithful (familyValue α) P ν ctx plans E := by
    intro r m hm vs
    have hdom : Dom E r := dom_of_members hm
    rw [← hag r hdom vs]
    exact (hFaith r m hm vs).trans
      (EvalRole.member_agree (familyReadsCtx α P ctx)
        hag r m (plans r) (hReads r m hm) vs)
  exact hPred α hα ctx hctx plans hplans ν hFaithν

theorem candidate_prefix_envSound (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hPred : GInv P K hW)
    (α : Arities) (hα : AritiesAgree α E) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r)
    (hFaith : EvalRole.Faithful (familyValue α) P μ ctx plans E)
    (fd : FamData) (X : Frame) (hX : Admissible fd X)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (m : CheckedMember) (hTy : m.mtype = famType fd)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hbounded : exprLevelsBounded m.arity m.mtype = true)
    (hbody : m.body = none) (hclass : m.mclass = .inductiveM)
    (hfresh : E.members fd.fref = none) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (RawFamily.table P μ fd X)) σ K (extendEnv E fd.fref m) n := by
  let ν := RawFamily.table P μ fd X
  let E₁ := extendEnv E fd.fref m
  have hPrior := prior_at_frame P K hW hPred α hα μ ctx plans hctx hplans hFaith fd X hfresh
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
  have hI : ∀ r m', E₁.members r = some m' → m'.mclass = .recursorM →
      IotaAt P ν K E₁ r := by
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

/-- Every semantic prefix input is produced from this new predecessor. -/
theorem target_facts (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hPred : GInv P K hE) (α : Arities) (hα : AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (familyValue α) P μ ctx plans p.E)
    (D : Frame) (hD : Admissible (famDataOf p.node.a) D) :
    AllSound P (RawFamily.table P μ (famDataOf p.node.a) D) K p.E ∧
      (∀ r m, p.E.members r = some m → m.mclass = .recursorM →
        IotaAt P (RawFamily.table P μ (famDataOf p.node.a) D) K p.E' r) ∧
      (∀ σ n, EnvSound (mkM P (RawFamily.table P μ (famDataOf p.node.a) D)) σ K
        (extendEnv p.E p.f fm) n) := by
  obtain ⟨_, hty, hfree, hTF, _, _⟩ := syntax_facts hE hmem p.node
  have hfresh : p.E.members (famDataOf p.node.a).fref = none := by
    change p.E.members p.node.a.family.ref = none
    rw [p.node.fam]
    exact groupMembersT_fresh_base hmem p.f fm (List.mem_cons_self _ _)
  have hPrior := prior_at_frame P K hE hPred α hα μ ctx plans hctx hplans hFaith
    (famDataOf p.node.a) D hfresh
  refine ⟨hPrior.1, hPrior.2 p.E' (groupMembersT_preserve hmem), ?_⟩
  intro σ n
  have hf' : p.E'.members p.f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem p.f fm (List.mem_cons_self _ _)
  have hCand := candidate_prefix_envSound P K hE hPred α hα μ ctx plans
    hctx hplans hFaith (famDataOf p.node.a) D hD hfree fm hty
    (hTF p.f fm hf').1 (hTF p.f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf p.node.a).fref = p.f from p.node.fam] using hCand

end Rcic.F3.PSet.PointwiseRole
