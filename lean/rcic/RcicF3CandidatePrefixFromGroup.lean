import rcic.RcicF3RawFamilyGroup
import rcic.RcicF3RawFamilyCandidatePrefix

/-!
# Ordinary candidate-prefix inputs from the actual group

The group's stored family type and fresh installation produce the syntax
facts used by normalization and candidate restriction. Raw family membership
uses the chosen raw frame's admissibility. The predecessor invariant supplies
old member soundness and old recursor iota; these compose with the family
member to make the family-only prefix sound. No candidate constructor closure
is required. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidatePrefixFromGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Produced ordinary inputs at the actual family-only typing prefix. The
candidate case is universal over admissible frames and requires no closure. -/
structure GroupPrefixFacts (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (E E' : ResolvedEnv) (f rr : Nat) (rm fm : CheckedMember)
    (node : RecNode E E' f rr rm) : Prop where
  prior : AllSound P μ K E ∧
    ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r
  bounded : FamBounded (famDataOf node.a) node.a.family.member.arity
  free : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
    occursConst (famDataOf node.a).fref e = false
  closedReader : EnvClosed node.E0
  rawEnv : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n
  candidateEnv : ∀ X, Admissible (famDataOf node.a) X →
    ∀ σ n, EnvSound (mkM P (table P μ (famDataOf node.a) X)) σ K
      (extendEnv E f fm) n
  facts : TypeFacts E'
  familyMember : node.a.family.member = fm
  familyType : fm.mtype = famType (famDataOf node.a)

/-- The actual group supplies the family member identity, full stored type,
family-free parameter/index domains, final type facts, closed reader bodies,
and the bound on the complete family descriptor. -/
theorem syntax_facts {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    node.a.family.member = fm ∧
    fm.mtype = famType (famDataOf node.a) ∧
    (∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false) ∧
    TypeFacts E' ∧ EnvClosed node.E0 ∧
    FamBounded (famDataOf node.a) node.a.family.member.arity := by
  have hf0 : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hfm : node.a.family.member = fm :=
    Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by
    rw [← hfm, node.a.family.storedType]
    rfl
  refine ⟨hfm, hty, ?_, hTF, ?_, famBounded_node node hTF⟩
  · intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have hd := groupMembersT_head_refs hmem r
      (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at hd
    unfold Dom at hd
    rw [hf0] at hd
    exact absurd hd (by decide)
  · intro r m hm
    have ht := hTF r m (node.sub r m (members_extend_preserved node.fresh r m hm))
    exact ⟨ht.1, fun b hb => (ht.2.2 b hb).1⟩

/-- The raw family-only prefix is sound from predecessor soundness/iota and
admissibility of the chosen raw frame. Constructor closure is not used. -/
theorem raw_prefix_envSound (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (role P μ (famDataOf node.a) vs))
    (hRaw : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a))) :
    ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
  obtain ⟨_, hty, _, hTF, _, _⟩ := syntax_facts hE hmem node
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbf : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m →
      E'.members r = some m := by
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
        (role P μ (famDataOf node.a) (ls.map (evalTotal σ))) := by
      simpa only [node.fam] using (hFamily (ls.map (evalTotal σ)))
    exact mem_congr_left hF.symm
      (ofFrame_mem P μ (famDataOf node.a) (frame P μ (famDataOf node.a)) hRaw _)
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
    (hPred : PlanRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : PlanRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = PlanRole.envPlan hE r)
    (hFaith : PlanRole.Faithful role P μ ctx plans E)
    (hReads : ReadsClosed ctx E)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (role P μ (famDataOf node.a) vs))
    (hRaw : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a))) :
    GroupPrefixFacts P μ K E E' f rr rm fm node := by
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

end Rcic.F3.PSet.CandidatePrefixFromGroup
