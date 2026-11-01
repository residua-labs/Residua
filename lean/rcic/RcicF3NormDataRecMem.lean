import rcic.RcicF3NormDataValue

/-!
# Stored DATA recursor membership over the normalized family

The original stored recursor telescope supplies its parameters, motive,
actual stored minors, dependent indices and major. Data admission fixes
anySort and its extra motive universe. The literal production endpoint
reduces to the actual admitted nodeCore on those exact semantic inputs.
The normalized recursion bridge produces its requested motive membership.

The canonical wrapper reads family, constructor, plan and recursor equations
from full normalized faithfulness. Small normalized candidate production and
ordinary node.E0 soundness remain explicit inputs. No recursor membership,
minor-step, iota or recursive-totality premise is supplied. This proves the
stored-member component only; stable iota and universal DATA remain open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRecMem
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

theorem memberValue_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (hCtor : ∀ (j : Fin p.node.a.constructors.length) vs,
      Equiv (μ (p.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
            (p.node.a.constructorViews j).fields.length) ρ0
          (p.node.a.constructors[j.val]).mtype))
    (hsmall : ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofNode p.node)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node)) A)
    (fullvs : List Nat) (hvl : fullvs.length = p.node.a.family.member.arity + 1)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K p.rr)
    (hType : UniformType p.node.a.family.resultLevel)
    (hReader : EnvSound (mkM P μ) (σOf fullvs) K p.node.E0 p.node.a.family.member.arity) :
    EvalPlanValue.memberValue (mkM P μ) (σOf fullvs) p p.rm ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) ρ0 p.rm.mtype) := by
  let M := mkM P μ
  let a := p.node.a
  let σ := σOf fullvs
  let g := EvalPlanValue.endValue M σ p
  have hpolicy : a.policy = .anySort := NormDataRead.data_policy a hType
  have h0 : evalTotal σ a.family.resultLevel ≠ 0 := Nat.ne_of_gt (hType σ)
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
    (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ0) ∈ Ed M (fapps mo (is ++ [z]))
  rw [NormDataRead.endpoint_data M σ p ps mo ms is z ρ0 h0 hmsk hisl]
  let C := (EvalPlanValue.context p M σ ρ0).withValues ps mo ms hmsk
  have hmo0 : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi a.family.indices
        (.pi (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyLocals (a.family.parameters.length + a.family.indices.length)))
          (.sort (.param a.family.member.arity))))) := by
    simpa only [policyMotiveType, hpolicy, policyMotiveLevel] using hmo
  have hcanon : ∀ u, u ∈ (canonL a.family.member.arity).map (evalTotal σ) → u ≤ K p.rr :=
    NormDataRead.family_vector_bound fullvs a.family.member.arity (K p.rr)
      (by rw [hvl]; exact Nat.le_succ _) hvs
  exact NormDataValue.nodeCore_mem P μ K C rfl fm ctors hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hFamily hCtor hsmall
    hcanon h0 hReader (.param a.family.member.arity) hmo0 hms is z hps hisfit hmajor

/-- Full normalized faithfulness pays the installed equations. The exact
small candidate and ordinary reader environment remain the production debts
of this stored-member wrapper; no current recursor package is an input. -/
theorem member_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r → ctxFull r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r → plansFull r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull E')
    (hsmall : ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hReader : ∀ fullvs, fullvs.length = rm.arity → (∀ u, u ∈ fullvs → u ≤ K rr) →
      EnvSound (mkM P μ) (σOf fullvs) K
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.E0
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.member.arity) :
    MemberSound P μ K rr rm := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := NormCandidatePrefix.family_equation_of_group P μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull
  have hCtor := NormDataRead.constructor_value_of_group P μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hbody : rm.body = none :=
    groupMembersT_body_none hmem rr rm
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hTF := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hlt : f < rr := by
    have hr := p.node.a.recursorRef
    rw [p.node.fam] at hr
    change rr = f + 1 + p.node.a.constructors.length at hr
    rw [hr]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self f)
      (Nat.le_add_right (f + 1) p.node.a.constructors.length)
  have hrecValue : ∀ vs, Equiv (μ rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p rm) := by
    intro vs
    have h := hFaithFull rr rm hrm vs
    rw [hctxFull rr (dom_of_members hrm),
      NormRole.envCtx_group hE hfam hctors hrec hmem, groupRoles_at_rr _ hlt] at h
    have hp : plansFull rr = some p := by
      rw [hplansFull rr (dom_of_members hrm)]
      change (if rr = rr then some p else EvalRole.envPlan hE rr) = some p
      exact if_pos rfl
    rw [hp] at h
    exact h
  intro σ ls ρ hlen hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvs : ∀ u, u ∈ ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hlevels l hl
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype
    (hTF rr rm hrm).1 (hlen ▸ (hTF rr rm hrm).2.1)]
  refine mem_congr_left (hrecValue _).symm ?_
  have hactual : (ls.map (evalTotal σ)).length = rm.arity := (List.length_map _ _).trans hlen
  have hvl : (ls.map (evalTotal σ)).length = p.node.a.family.member.arity + 1 := by
    rw [hactual]
    change p.rm.arity = p.node.a.family.member.arity + 1
    have hp : p.node.a.policy = .anySort := NormDataRead.data_policy p.node.a hType
    simpa only [policyRecursorArity, hp] using p.node.a.recursorArity
  exact memberValue_mem P μ K p fm ctors hE hfam hctors hrec hmem hBound hBoundD hpar
    hPred ctx plans hctx hplans hFaith hFamily hCtor hsmall
    (ls.map (evalTotal σ)) hvl hvs hType (hReader _ hactual hvs)

end Rcic.F3.PSet.NormDataRecMem
