import rcic.RcicF3NormPropCtor
import rcic.RcicF3NormPropRecPkg

/-!
# Produced normalized-role group step on the Prop/anySort PendA face

The family frame's admissibility and closure are produced. Original
stored constructors are sound at their own bounds, and the actual indexed
recursor supplies the complete literal RecPkg. These components compose
into the new canonical invariant without an additional semantic callback.

The stated face is uniform Prop with anySort elimination and the original
PendA condition. Data and propOnly faces, invariant migration into W/D,
the apex descriptor and universal shape-schema iota remain separate work.
The IotaAt conjunct retains its current legacy-witness scope.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Checked group composition for this face of the full new StepAG target.
The literal GroupStepAt walk and BoundDG premises remain in its interface. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hPend : ∃ node : RecNode E E' f rr rm, PendA node) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro _hwalk hBound _hBoundD hPred
  intro ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
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
  have hFamily := NormCandidatePrefix.family_equation_of_group P μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith
  have hN := (EvalPlanNormalProp.normalized_closed P μ p fm ctors
    hE hmem (fun _ => 0) (hProp _) hpolicy).1
  obtain ⟨_hfm, hty, _hfree, hTF, _hclosed, _hbounded⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  change fm.mtype = famType (EvalPlanNormal.fd p) at hty
  have hfm : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hfmSound : MemberSound P μ K f fm := by
    intro σ ls ρ hlen _hlevels
    refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
      (hTF f fm hfm).1 (hlen ▸ (hTF f fm hfm).2.1), hty]
    have hf : Equiv (μ f (ls.map (evalTotal σ)))
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) := by
      have hF := hFamily (ls.map (evalTotal σ))
      change Equiv (μ p.node.a.family.ref (ls.map (evalTotal σ)))
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) at hF
      simpa only [p.node.fam] using hF
    exact mem_congr_left hf.symm
      (ofFrame_mem P μ (EvalPlanNormal.fd p) (frame P μ (EvalPlanNormal.fd p)) hN _)
  have hctorSound : ∀ j : Fin p.node.a.constructors.length,
      MemberSound P μ K (f + 1 + j.val) (p.node.a.constructors[j.val]) :=
    fun j => NormPropCtor.member_sound P μ K hE hfam hctors hrec hmem hBound
      hPred ctx plans hctx hplans hFaith hProp hpolicy j
  have hPkg := NormPropRecPkg.rec_pkg P μ K hE hfam hctors hrec hmem hBound hPred
    ctx plans hctxE hplansE hFaithE ctx plans hctx hplans hFaith hProp hpolicy hPend
  constructor
  · intro r m hm
    rcases group_member_cases hmem hL hrr p.node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.1 r m hold
    · exact hfmSound
    · exact hPkg.1
    · exact hctorSound j
  · intro Efin hsub r m hm hk
    rcases group_member_cases hmem hL hrr p.node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.2 Efin (fun s n hn => hsub s n (hsubE s n hn)) r m hold hk
    · rw [hfam] at hk
      cases hk
    · exact hPkg.2 Efin hsub
    · rw [(p.node.a.constructorViews j).hasClass] at hk
      cases hk

end Rcic.F3.PSet.NormPropGroup
