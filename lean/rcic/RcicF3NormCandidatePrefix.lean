import rcic.RcicF3NormRoleTable
import rcic.RcicF3RawFamilyMember
import rcic.RcicF3CandidatePrefixFromGroup

/-!
# Actual prefix soundness for normalized roles and admissible frames

The normalized predecessor invariant is reapplied after each fresh family
update. Its canonical member and plan reads are produced from admission.
An arbitrary admissible frame supplies family-member soundness, so no
constructor closure is needed to obtain the family-only typing prefix.

The actual-table package accepts the literal family equation for that
frame. Its canonical wrapper derives this equation from the full new
faithful table and uses the actual normalized descriptor. The reused
GroupPrefixFacts record has no raw-frame equation: its rawEnv field is
simply soundness of the actual table at the family-only prefix. No old
invariant, raw closure or normalization callback is assumed.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormCandidatePrefix
open Rcic.Declarative Rcic.Model.PS RawFamily CandidatePrefixFromGroup

/-- A fresh family update preserves all preceding normalized role and
plan equations. Reapplying the actual predecessor produces its complete
soundness and stable legacy-iota package at the updated table. -/
theorem prior_at_frame (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hPred : NormRole.GInv P K hW)
    (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (fd : FamData) (X : Frame) (hfresh : E.members fd.fref = none) :
    AllSound P (table P μ fd X) K E ∧
      ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
        ∀ r m, E.members r = some m → m.mclass = .recursorM →
          IotaAt P (table P μ fd X) K Efin r := by
  have hRA := NormRole.planReadsOKAlong hW ctx plans hctx hplans
  have hReads := (EvalRole.faithful_envTable role P ctx plans
    (familyReadsCtx P ctx) hW hRA).2
  let ν := table P μ fd X
  have hag : AgreeOn μ ν (Dom E) :=
    agreeOn_upd hfresh μ (ofFrame P μ fd X)
  have hFaithν : EvalRole.Faithful role P ν ctx plans E := by
    intro r m hm vs
    have hdom : Dom E r := dom_of_members hm
    rw [← hag r hdom vs]
    exact (hFaith r m hm vs).trans
      (EvalRole.member_agree (familyReadsCtx P ctx)
        hag r m (plans r) (hReads r m hm) vs)
  exact hPred ctx hctx plans hplans ν hFaithν

/-- Every admissible replacement frame produces soundness of the actual
family-only prefix. Its read certificate is supplied internally. -/
theorem candidate_prefix_envSound (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hPred : NormRole.GInv P K hW)
    (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (fd : FamData) (X : Frame) (hX : Admissible fd X)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (m : CheckedMember) (hTy : m.mtype = famType fd)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hbounded : exprLevelsBounded m.arity m.mtype = true)
    (hbody : m.body = none) (hclass : m.mclass = .inductiveM)
    (hfresh : E.members fd.fref = none) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P μ fd X)) σ K (extendEnv E fd.fref m) n := by
  let ν := table P μ fd X
  let E₁ := extendEnv E fd.fref m
  have hPrior := prior_at_frame P K hW hPred μ ctx plans hctx hplans hFaith fd X hfresh
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

/-- The actual table's family prefix is sound for any chosen admissible
frame whose literal family equation holds. No frame closure is required. -/
theorem frame_prefix_envSound (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (N : Frame) (hN : Admissible (famDataOf node.a) N)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (ofFrame P μ (famDataOf node.a) N vs)) :
    ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
  obtain ⟨_, hty, _, hTF, _, _⟩ := syntax_facts hE hmem node
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbf : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m hm
    by_cases hr : r = f
    · subst r
      rw [members_extend_eq] at hm
      cases hm
      exact hf'
    · rw [members_extend_ne E f fm r hr] at hm
      exact hsubE r m hm
  have hfmS : MemberSound P μ K f fm := by
    intro σ ls ρ hlen _
    refine ⟨?_, fun b hb => by rw [hbf] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
      (hTF f fm hf').1 (hlen ▸ (hTF f fm hf').2.1), hty]
    have hF : Equiv (μ f (ls.map (evalTotal σ)))
        (ofFrame P μ (famDataOf node.a) N (ls.map (evalTotal σ))) := by
      simpa only [node.fam] using hFamily (ls.map (evalTotal σ))
    exact mem_congr_left hF.symm (ofFrame_mem P μ (famDataOf node.a) N hN _)
  intro σ n
  refine envSound_of P (Efin := E') hSsub ?_ ?_ σ n
  · intro r m hm
    by_cases hr : r = f
    · subst r
      rw [members_extend_eq] at hm
      cases hm
      exact hfmS
    · rw [members_extend_ne E f fm r hr] at hm
      exact hA r m hm
  · intro r m hm hk
    by_cases hr : r = f
    · subst r
      rw [members_extend_eq] at hm
      cases hm
      rw [hfam] at hk
      cases hk
    · rw [members_extend_ne E f fm r hr] at hm
      exact hI r m hm hk

/-- Reapply the new predecessor at an arbitrary admissible target frame,
producing predecessor soundness, final-environment iota, and prefix soundness. -/
theorem target_facts (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (D : Frame) (hD : Admissible (famDataOf p.node.a) D) :
    AllSound P (table P μ (famDataOf p.node.a) D) K p.E ∧
      (∀ r m, p.E.members r = some m → m.mclass = .recursorM →
        IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r) ∧
      (∀ σ n, EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
        (extendEnv p.E p.f fm) n) := by
  obtain ⟨_, hty, hfree, hTF, _, _⟩ := syntax_facts hE hmem p.node
  have hfresh : p.E.members (famDataOf p.node.a).fref = none := by
    change p.E.members p.node.a.family.ref = none
    rw [p.node.fam]
    exact groupMembersT_fresh_base hmem p.f fm (List.mem_cons_self _ _)
  have hPrior := prior_at_frame P K hE hPred μ ctx plans hctx hplans hFaith
    (famDataOf p.node.a) D hfresh
  refine ⟨hPrior.1, hPrior.2 p.E' (groupMembersT_preserve hmem), ?_⟩
  intro σ n
  have hf' : p.E'.members p.f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem p.f fm (List.mem_cons_self _ _)
  have hCand := candidate_prefix_envSound P K hE hPred μ ctx plans
    hctx hplans hFaith (famDataOf p.node.a) D hD hfree fm hty
    (hTF p.f fm hf').1 (hTF p.f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf p.node.a).fref = p.f from p.node.fam] using hCand

/-- The actual table and every admissible fresh update share one produced
prefix package. The record's rawEnv field asserts only actual-table soundness. -/
theorem group_facts (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (N : Frame) (hN : Admissible (famDataOf node.a) N)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (ofFrame P μ (famDataOf node.a) N vs)) :
    GroupPrefixFacts P μ K E E' f rr rm fm node := by
  have hPrior := hPred ctx hctx plans hplans μ hFaith
  have hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r :=
    hPrior.2 E' (groupMembersT_preserve hmem)
  obtain ⟨hfm, hty, hfree, hTF, hclosed, hbounded⟩ := syntax_facts hE hmem node
  refine ⟨⟨hPrior.1, hI⟩, hbounded, hfree, hclosed,
    frame_prefix_envSound P K μ hE hfam hmem node hPrior.1 hI N hN hFamily,
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
  have hCand := candidate_prefix_envSound P K hE hPred μ ctx plans hctx hplans hFaith
    (famDataOf node.a) X hX hfree fm hty
    (hTF f fm hf').1 (hTF f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf node.a).fref = f from node.fam] using hCand

/-- The canonical normalized family equation follows from the installed
group role; no separate family-semantic premise is needed. -/
theorem family_equation_of_group (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E') :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ vs, Equiv (μ p.node.a.family.ref vs) (role P μ (EvalPlanNormal.fd p) vs) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  change ∀ vs : List Nat, Equiv (μ p.node.a.family.ref vs)
    (role P μ (EvalPlanNormal.fd p) vs)
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  intro vs
  have h := hFaith f fm hf' vs
  rw [hctx f (dom_of_members hf'), NormRole.envCtx_group, groupRoles_at_f] at h
  change Equiv (μ f vs) (role P μ (EvalPlanNormal.fd p) vs) at h
  simpa only [p.node.fam] using h

/-- Full new canonical faithfulness supplies both predecessor agreement and
the actual normalized-frame family equation. The frame's admissibility is
the sole frame input; its closure is not used by this prefix producer. -/
theorem canonical_group_facts (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hN : Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem))
      (frame P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)))) :
    GroupPrefixFacts P μ K E E' f rr rm fm
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := by
    intro r hr
    exact (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := by
    intro r hr
    exact (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful role P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hFamily := family_equation_of_group P μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith
  exact group_facts P K μ hE hfam hmem p.node hPred ctx plans hctxE hplansE hFaithE
    (frame P μ (EvalPlanNormal.fd p)) hN hFamily

end Rcic.F3.PSet.NormCandidatePrefix
