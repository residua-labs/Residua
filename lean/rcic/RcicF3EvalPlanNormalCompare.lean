import rcic.RcicF3EvalPlanNormalProp
import rcic.RcicF3EvalPlanNormalLevels
import rcic.RcicF3EvalPlanNormalTuple
import rcic.RcicF3EvalCandidatePrefix
import rcic.RcicF3PropEvalCandidateLevels

/-!
# Bounded guarded comparison back into the unchanged raw family

Every reached recursive leaf discharges the actual valuation/parameter
guard. The original typed field telescope is then reconstructed in each
admissible raw closed candidate at the full bounded recursor valuation.
Normalized induction and raw leastness yield the reverse inclusion on that
slice. No global inclusion of a guarded restriction, global raw constructor
monotonicity, or changed family role is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalCompare
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily RawFamilyRec
open EvalPlanNormal EvalPlanNormalSlice

/-- The local induction predicate yields an original constructor
presentation in the target candidate, using actual bounded field typings.
The target candidate's closure is not needed for this reconstruction. -/
theorem constructor_to_raw (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (N D : Frame) (hN : Admissible (famDataOf p.node.a) N)
    (hD : Admissible (famDataOf p.node.a) D)
    (hA : AllSound P (table P μ (famDataOf p.node.a) D) K p.E)
    (hI : ∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r)
    (hES : EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (fullvs : List Nat) (hσfull : σ = σOf fullvs)
    (hvs : ∀ v, v ∈ fullvs → v ≤ K p.rr)
    (ps : List PSet.{4}) (vs : List Nat) (i : Index.{4}) (z : PSet.{4})
    (hc : CtorAt P μ (fd p)
      (restrict N (Predicate p.node.a.family.member.arity
        p.node.a.family.parameters.length σ ps D)) vs i z)
    (hσ : ∀ u, u < p.node.a.family.member.arity → σ u = σOf vs u)
    (hkey : paramKey p.node.a.family.parameters.length i = key ps) :
    CtorAt P μ (famDataOf p.node.a) D vs i z := by
  obtain ⟨_, _, hfree, _, _, hrawBound⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  let R := restrict N (Predicate p.node.a.family.member.arity
    p.node.a.family.parameters.length σ ps D)
  let MR := mkM P (table P μ (famDataOf p.node.a) R)
  let MD := mkM P (table P μ (famDataOf p.node.a) D)
  obtain ⟨jn, xs, hpR, hxR, hi, hz⟩ :=
    PropEvalCandidate.ctorAt_parameters_at P μ (fd p) R
      p.node.a.family.member.arity (bounded_of_group p fm ctors hE hmem)
      vs σ hσ i z hc ps hkey h0
  have hnctor := ctor_get p jn
  rw [hnctor] at hxR hi
  let j := index p jn
  have hpD : TelFits MD σ p.node.a.family.parameters ρ0 ps :=
    (PiIndependent.telFits_free P μ (famDataOf p.node.a).fref
      (ofFrame P μ (famDataOf p.node.a) R) (ofFrame P μ (famDataOf p.node.a) D)
      σ p.node.a.family.parameters
      (fun e he => hfree e (List.mem_append_left _ he)) ρ0 ps).mp hpR
  have hxD := fields_to_raw P μ σ K p fm ctors hE hfam hctors hrec hmem hB
    N D hN hD hA hI hES h0 hpolicy fullvs hσfull hvs j ps xs hpD hxR
  have hread := PiIndependent.leafArgs_free P μ (famDataOf p.node.a).fref
    (ofFrame P μ (famDataOf p.node.a) R) (ofFrame P μ (famDataOf p.node.a) D)
    σ (p.node.a.constructorViews j).resultIndices
    (p.node.a.constructorViews j).noFamilyInIndices (push xs (push ps ρ0))
  change (p.node.a.constructorViews j).resultIndices.map
      (den MR σ (push xs (push ps ρ0))) =
    (p.node.a.constructorViews j).resultIndices.map
      (den MD σ (push xs (push ps ρ0))) at hread
  change i = key (ps ++ (p.node.a.constructorViews j).resultIndices.map
    (den MR σ (push xs (push ps ρ0)))) at hi
  rw [hread] at hi
  have hrawMember := famDataOf_ctor p.node.a j
  have hctorBound := hrawBound.ctors _ (List.getElem?_mem hrawMember)
  have hpVs := (TelFits_levels MD hσ p.node.a.family.parameters
    hrawBound.params ρ0 ps).mp hpD
  have hxVs := (TelFits_levels MD hσ (p.node.a.constructorViews j).fields
    hctorBound.1 (push ps ρ0) xs).mp hxD
  rw [map_den_levels MD hσ (p.node.a.constructorViews j).resultIndices
    hctorBound.2 (push xs (push ps ρ0))] at hi
  let jo : Fin (famDataOf p.node.a).ctors.length :=
    ⟨j.val, by simpa only [famDataOf_ctors_length] using j.isLt⟩
  have hrawCtor : (famDataOf p.node.a).ctors.get jo =
      ((p.node.a.constructorViews j).fields, (p.node.a.constructorViews j).resultIndices) := by
    rw [List.getElem?_eq_getElem jo.isLt] at hrawMember
    exact Option.some.inj hrawMember
  have hzero : evalTotal (σOf vs) (famDataOf p.node.a).resLevel = 0 :=
    (selection_prop p.node.a σ h0 hpolicy).1 (σOf vs)
  refine ⟨jo, ps, xs, hpVs, ?_, ?_, ?_, ?_⟩
  · rw [hrawCtor]
    exact hxVs
  · rw [if_pos hzero]
    exact True.intro
  · rw [hrawCtor]
    exact hi
  · rw [if_pos hzero]
    exact hz

/-- Reapply the actual repaired predecessor invariant under the fresh
target-family update. The read certificate and prefix soundness are
produced from canonical admitted plans, not supplied as semantic walls. -/
theorem target_facts (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hPred : EvalRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (D : Frame) (hD : Admissible (famDataOf p.node.a) D) :
    AllSound P (table P μ (famDataOf p.node.a) D) K p.E ∧
    (∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r) ∧
    (∀ σ n, EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) n) := by
  have hRA := EvalRole.readsOKAlong_of_plan_agree hE ctx plans hplans
    (Rcic.F3.StepDGOrder.readsOKAlong_envCtxT hE ctx hctx)
  have hReads := (EvalRole.faithful_envTable role P ctx plans
    (familyReadsCtx P ctx) hE hRA).2
  obtain ⟨hfm, hty, hfree, hTF, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hfresh : p.E.members (famDataOf p.node.a).fref = none := by
    change p.E.members p.node.a.family.ref = none
    rw [p.node.fam]
    exact groupMembersT_fresh_base hmem p.f fm (List.mem_cons_self _ _)
  let ν := table P μ (famDataOf p.node.a) D
  have hag : AgreeOn μ ν (Dom p.E) :=
    agreeOn_upd hfresh μ (ofFrame P μ (famDataOf p.node.a) D)
  have hFaithν : EvalRole.Faithful role P ν ctx plans p.E := by
    intro r m hm vs
    have hdom : Dom p.E r := dom_of_members hm
    rw [← hag r hdom vs]
    exact (hFaith r m hm vs).trans
      (EvalRole.member_agree (familyReadsCtx P ctx) hag r m (plans r)
        (hReads r m hm) vs)
  have hPrior := hPred ctx hctx plans hplans ν hFaithν
  refine ⟨hPrior.1, hPrior.2 p.E' (groupMembersT_preserve hmem), ?_⟩
  intro σ n
  have hf' : p.E'.members p.f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem p.f fm (List.mem_cons_self _ _)
  have hCand := EvalCandidatePrefix.candidate_prefix_envSound P K hE hPred μ ctx plans
    hctx hplans hFaith hReads (famDataOf p.node.a) D hD hfree fm hty
    (hTF p.f fm hf').1 (hTF p.f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf p.node.a).fref = p.f from p.node.fam] using hCand

/-- On the actual bounded valuation and fixed parameter slice, the
normalized frame lies in the unchanged raw intersection. The induction
runs separately against each admissible globally raw-closed candidate;
only reached child keys use its guarded induction hypothesis. -/
theorem normalized_le_raw (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hPred : EvalRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (fullvs : List Nat) (hσfull : σ = σOf fullvs)
    (hvs : ∀ v, v ∈ fullvs → v ≤ K p.rr)
    (ps : List PSet.{4}) :
    ∀ vs i z, z ∈ frame P μ (fd p) vs i →
      (∀ u, u < p.node.a.family.member.arity → σ u = σOf vs u) →
      paramKey p.node.a.family.parameters.length i = key ps →
      z ∈ frame P μ (famDataOf p.node.a) vs i := by
  obtain ⟨hN, hclosed⟩ :=
    EvalPlanNormalProp.normalized_closed P μ p fm ctors hE hmem σ h0 hpolicy
  have hmono := constructorMono_of_group P μ p fm ctors hE hmem
  intro vs i z hz hσ hkey
  have hall : InAll P μ (famDataOf p.node.a) vs i z := by
    intro D hD hDclosed
    obtain ⟨hA, hI, hES⟩ := target_facts P μ K p fm ctors hE hfam hmem hPred
      ctx plans hctx hplans hFaith D hD
    have hInd := frame_induction P μ (fd p) hN hclosed hmono
      (Predicate p.node.a.family.member.arity p.node.a.family.parameters.length σ ps D)
      (fun _ _ _ _ he hq hlevel hparam => mem_congr_left he (hq hlevel hparam))
      (fun vs' i' z' hc hlevel hparam => hDclosed vs' i' z'
        (constructor_to_raw P μ σ K p fm ctors hE hfam hctors hrec hmem hB
          (frame P μ (fd p)) D hN hD hA hI
          (hES σ p.node.a.family.member.arity) h0 hpolicy fullvs hσfull hvs
          ps vs' i' z' hc hlevel hparam))
    exact hInd vs i z hz hσ hkey
  have hzero : evalTotal (σOf vs) (famDataOf p.node.a).resLevel = 0 :=
    (selection_prop p.node.a σ h0 hpolicy).1 (σOf vs)
  have hface := (hN vs i).2
  change (if evalTotal (σOf vs) (famDataOf p.node.a).resLevel = 0 then
    ∀ y, y ∈ frame P μ (fd p) vs i → Equiv y pempty
    else ∀ y, y ∈ frame P μ (fd p) vs i → ¬ Equiv y pempty) at hface
  rw [if_pos hzero] at hface
  have he := hface z hz
  unfold frame
  rw [if_pos hzero]
  exact mem_tv.mpr ⟨fun D hD hc => mem_congr_left he (hall D hD hc), he⟩

end Rcic.F3.PSet.EvalPlanNormalCompare
