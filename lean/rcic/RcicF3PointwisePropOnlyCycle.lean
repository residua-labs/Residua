import rcic.RcicF3NormalizedDirectCycle

/-!
# PropOnly direct-cycle groups with the original bounds and arbitrary mirrors

The normalized frame has no members because every constructor needs an
immediate recursive child. The actual fitting major in the stored
recursor telescope is therefore impossible. This supplies membership at
the installed pointwise table without an evaluation-totality or parameter
mirror premise. The existing fully general PropOnly stable iota theorem
supplies the second RecPkg conjunct.

Family and constructor soundness, ordinary prefix preservation and both
original bound packages are retained in the resulting group step. No W or
D check is required. Other recursive PropOnly shapes remain a separate
residue. Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyCycleRecMem
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

/-- At every bounded full recursor vector, the actual new abstraction is a
member of the actual stored type. Its end obligation is produced inside
this proof from the typed group and the repaired predecessor invariant. -/
theorem memberValue_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hcycles : PropShapeCoverage.DirectCycle p.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (fullvs : List Nat) (hvl : fullvs.length = p.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K p.rr)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hpolicy : p.node.a.policy = .propOnly) :
    EvalPlanValue.memberValue (mkM P μ) (σOf fullvs) p p.rm ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) ρ0 p.rm.mtype) := by
  let M := mkM P μ
  let a := p.node.a
  let σ := σOf fullvs
  let g := EvalPlanValue.endValue M σ p
  change piLam M σ g ρ0 p.rm.mtype ∈ Ed M (den M σ ρ0 p.rm.mtype)
  rw [a.recursorType, policyRecursorType_eq]
  refine piLam_mem M σ (EvalPlanValue.endValue_resp M σ p) _ ρ0 ?_
  refine piGood_policyPi_fits M σ g _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M σ g _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, rest, rfl, hps, hrest⟩ := TelFits_split _ _ ρ0 zs hz
  obtain ⟨mo, rest', rfl, hmo, hrest'⟩ : ∃ mo rest', rest = mo :: rest' ∧
      mo ∈ Ed M (den M σ (push ps ρ0) (policyMotiveType a.family a.policy)) ∧
      TelFits M σ (a.minorTypes ++
        (liftFields (a.minorTypes.length + 1) a.family.indices 0 ++ _))
        (vcons mo (push ps ρ0)) rest' := by
    cases rest with
    | nil => exact hrest.elim
    | cons mo rest' => exact ⟨mo, rest', rfl, hrest.1, hrest.2⟩
  obtain ⟨ms, rest'', rfl, hms, hrest''⟩ := TelFits_split _ _ _ rest' hrest'
  obtain ⟨is, zl, rfl, his, hzl⟩ := TelFits_split _ _ _ rest'' hrest''
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hmsk : ms.length = a.constructors.length := hmsl.trans a.minorCount
  have hisl : is.length = a.family.indices.length := by
    rw [his.length, liftFields_length']
  have hpsl : ps.length = a.family.parameters.length := hps.length
  have hisfit : TelFits M σ a.family.indices (push ps ρ0) is := by
    apply (TelFits_liftFields M σ (mo :: ms) (push ps ρ0)
      a.family.indices [] is).mp
    show TelFits M σ (liftFields (ms.length + 1) a.family.indices 0)
      (push ms (vcons mo (push ps ρ0))) is
    rw [hmsl]
    exact his
  obtain ⟨z, rfl, hmajor⟩ : ∃ z, zl = [z] ∧ z ∈ Ed M
      (den M σ (push is (push ms (vcons mo (push ps ρ0))))
        (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals a.family.parameters.length
            (a.minorTypes.length + 1 + a.family.indices.length) ++
              policyLocals a.family.indices.length))) := by
    match zl, hzl with
    | [z], ⟨hz, _⟩ => exact ⟨z, rfl, hz⟩
  have hres := den_recResult M σ mo z ms is (push ps ρ0)
  rw [hmsl, hisl, ← push_cons_eq] at hres
  rw [hres]
  have hmajorType : den M σ (push is (push ms (vcons mo (push ps ρ0))))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length
          (a.minorTypes.length + 1 + a.family.indices.length) ++
            policyLocals a.family.indices.length)) =
      fapps (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal σ)))
        (ps ++ is) := by
    have hpush : push is (push ms (vcons mo (push ps ρ0))) =
        push (ps ++ (mo :: (ms ++ is))) ρ0 := by
      rw [push_append]
      show push is (push ms (vcons mo (push ps ρ0))) =
        push (ms ++ is) (vcons mo (push ps ρ0))
      rw [push_append]
    have hlength : a.minorTypes.length + 1 + a.family.indices.length =
        (mo :: (ms ++ is)).length := by
      rw [List.length_cons, List.length_append, hmsl, hisl]
      exact Nat.add_right_comm _ _ _
    have hparams : (policyParameterLocals a.family.parameters.length
        (a.minorTypes.length + 1 + a.family.indices.length)).map
        (den M σ (push is (push ms (vcons mo (push ps ρ0))))) = ps := by
      rw [hpush, hlength, ← hpsl]
      exact den_paramLocals M σ ps _ ρ0
    have hindices : (policyLocals a.family.indices.length).map
        (den M σ (push is (push ms (vcons mo (push ps ρ0))))) = is := by
      rw [← hisl]
      exact den_policyLocals M σ is _
    rw [den_foldApps, List.map_append, hparams, hindices]
    rfl
  rw [hmajorType] at hmajor
  change EvalPlanValue.endValue M σ p
    (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ0) ∈
      Ed M (fapps mo (is ++ [z]))
  rw [NormDPlanBridge.endpoint_propOnly M σ p hProp hpolicy,
    recEnd_propOnly M σ (famDataOf p.node.a) _ (hProp σ) hpolicy]
  let C := (EvalPlanValue.context p M σ ρ0).withValues ps mo ms hmsk
  have hmo0 : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi a.family.indices
        (.pi (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyLocals (a.family.parameters.length + a.family.indices.length)))
          (.sort .zero)))) := by
    simpa only [policyMotiveType, show a.policy = .propOnly from hpolicy,
      policyMotiveLevel] using hmo
  exact False.elim (NormalizedDirectCycle.major_false P μ C rfl fm ctors
    hE hmem hcycles hFamily is z hps hisfit hmajor)

/-- The canonical new recursor is sound on the uniformly Prop/propOnly
direct-cycle face. Both equations are read from the actual admitted group
and faithful table; the original bound packages retain their literal types. -/
theorem member_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hcycles : PropShapeCoverage.DirectCycle (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    MemberSound P μ K rr rm := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull hProp
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hbody : rm.body = none :=
    groupMembersT_body_none hmem rr rm
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hTF := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hrecValue := PointwiseRoleEquations.recursor_value_of_group P α μ
    hE hfam hctors hrec hmem ctxFull plansFull hctxFull hplansFull hFaithFull
  intro σ ls ρ hlen hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvs : ∀ u, u ∈ ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hlevels l hl
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype
    (hTF rr rm hrm).1 (hlen ▸ (hTF rr rm hrm).2.1)]
  refine mem_congr_left (hrecValue _).symm ?_
  have hvl : (ls.map (evalTotal σ)).length = p.node.a.family.member.arity := by
    rw [List.length_map, hlen]
    change p.rm.arity = p.node.a.family.member.arity
    have hp : p.node.a.policy = .propOnly := hpolicy
    simpa only [policyRecursorArity, hp] using p.node.a.recursorArity
  exact memberValue_mem P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD hcycles hPred α hα ctx plans hctx hplans hFaith hFamily
    (ls.map (evalTotal σ)) hvl hvs hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyCycleRecMem

namespace Rcic.F3.PSet.PointwisePropOnlyCycleIota
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The produced direct-cycle membership composes with the already-general
PropOnly stable IotaAt theorem at the same actual pointwise table. -/
theorem rec_pkg (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hcycles : PropShapeCoverage.DirectCycle (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    RecPkg P μ K E' rr rm :=
  ⟨PointwisePropOnlyCycleRecMem.member_sound P μ K hE hfam hctors hrec hmem
      hBound hBoundD hcycles hPred α hα ctx plans hctx hplans hFaith
      ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin _ => PointwisePropOnlyIota.iota_at P μ K hE hfam hctors hrec hmem
      α ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy Efin⟩

end Rcic.F3.PSet.PointwisePropOnlyCycleIota

namespace Rcic.F3.PSet.PointwisePropOnlyCycleGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Complete group composition on the admitted direct-cycle face, with
arbitrary constructor parameter mirrors and the original bound packages. -/
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
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hcycles : PropShapeCoverage.DirectCycle (EvalPlan.ofGroup hE hfam hctors hrec hmem).node) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro _hwalk hBound hBoundD hPred
  intro α hα ctx hctx plans hplans μ hFaith
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
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (hsubE r m hm)
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono hsubE
  have hPrior := hPred α hαE ctx hctxE plans hplansE μ hFaithE
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith hProp
  have hN := (NormPropCtorUniform.normalized_closed P μ p fm ctors
    hE hmem hProp).1
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
    fun j => PointwisePropCtor.member_sound P μ K hE hfam hctors hrec hmem hBound
      hPred α hα ctx plans hctx hplans hFaith hProp j
  have hPkg := PointwisePropOnlyCycleIota.rec_pkg P μ K hE hfam hctors hrec hmem
    hBound hBoundD hcycles hPred α hαE ctx plans hctxE hplansE hFaithE
    ctx plans hctx hplans hFaith hProp hpolicy
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


/-- Uniform Prop admission pays the walk premise at every RecNode, so
this invariant step has neither a W check nor a D check. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hcycles : PropShapeCoverage.DirectCycle (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  apply group_step P K hE hfam hctors hrec hmem hProp hpolicy hcycles ?_ hB hD hPred
  intro node
  have hp : UniformProp node.a.family.resultLevel := by
    rw [Rcic.F3.StepWGroup.nodeResult_unique node p.node]
    exact hProp
  exact Rcic.Syn.FamApp.StepW.stepW_of_uniformProp hE hfam hctors hrec hmem node
    (walkRec_of_group hmem) hp

end Rcic.F3.PSet.PointwisePropOnlyCycleGroup


#print axioms Rcic.F3.PSet.PointwisePropOnlyCycleRecMem.memberValue_mem
#print axioms Rcic.F3.PSet.PointwisePropOnlyCycleRecMem.member_sound
#print axioms Rcic.F3.PSet.PointwisePropOnlyCycleIota.rec_pkg
#print axioms Rcic.F3.PSet.PointwisePropOnlyCycleGroup.group_step
#print axioms Rcic.F3.PSet.PointwisePropOnlyCycleGroup.invariant_step
