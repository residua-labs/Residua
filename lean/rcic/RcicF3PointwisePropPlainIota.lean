import rcic.RcicF3PointwisePropPlainValue
import rcic.RcicF3PointwisePropRecMem
import rcic.RcicF3NormPropPlainIota

/-!
# Nonvacuous plain-Prop legacy iota with the actual new predecessor

The original complete recursor telescope supplies the typed left endpoint.
Produced evaluation and the right hereditary typing compare both sides with
the actual stored minor on its proof fields. New faithfulness and the new
predecessor supply every family/read equation; no earlier DATA family is
identified with an old interpretation. Literal checked shapes, full levels,
complete keys and stable IotaAt scope are retained. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropPlainIota
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

/-- One typed legacy redex, at its actual full recursor universe vector. -/
theorem iota_eq (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (hRec : ∀ vs, Equiv (μ p.rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p p.rm))
    (hN : NoFunRec p.node)
    (hfree : ∀ (j : Fin p.node.a.constructors.length) A,
      A ∈ (p.node.a.constructorViews j).fields →
      occursConst p.node.a.family.ref A = false)
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (h0 : evalTotal (σOf (w.ls.map (evalTotal σ))) p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K p.rr)
    (hspine : SpineFacts (mkM P μ) (den (mkM P μ) σ ρ w.minor)
      ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.kinds w.ctorAfterParams).map (den (mkM P μ) σ ρ)))
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X) :
    Equiv (den (mkM P μ) σ ρ (iotaLhsOf w))
      (den (mkM P μ) σ ρ (iotaRhsOf w)) := by
  let M := mkM P μ
  let a := p.node.a
  let τ := σOf (w.ls.map (evalTotal σ))
  let g := EvalPlanValue.endValue M τ p
  obtain ⟨hnp, hnM, hnq, hfr⟩ := iota_align a w hwr hm
  cases hl0 : M.dec (Equiv (den M σ ρ (iotaLhsOf w)) pempty) with
  | isTrue he => exact rhs_eq_ed_pempty ml mr he
  | isFalse hne =>
    have hk : a.minorTypes.length = a.constructors.length := a.minorCount
    have hjk : j.val < a.constructors.length := j.isLt
    have hrecμ := hRec (w.ls.map (evalTotal σ))
    change Equiv (M.μ p.rr (w.ls.map (evalTotal σ)))
      (piLam M τ g ρ0 p.rm.mtype) at hrecμ
    have hlhs : den M σ ρ (iotaLhsOf w) =
        fapps (M.μ p.rr (w.ls.map (evalTotal σ)))
          (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) := by
      unfold iotaLhsOf recCall
      rw [fapps_den_append_singleton, hwr]
      rfl
    have hpvl : (w.preMajor.map (den M σ ρ)).length =
        a.family.parameters.length + 1 + a.constructors.length + a.family.indices.length := by
      rw [List.length_map, w.hpre, hnp, hnM, hnq]
    rw [recType_eq a] at hrecμ
    have hne' : ¬ Equiv (fapps
        (piLam M τ g ρ0 (policyPi (recPreDomsOf a ++ [recMajorOf a]) (recResultOf a)))
        (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)])) pempty := fun he =>
      hne (by rw [hlhs]; exact (fapps_congr hrecμ _).trans he)
    have hlenD : (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]).length =
        (recPreDomsOf a ++ [recMajorOf a]).length := by
      rw [List.length_append, List.length_append, hpvl, recPreDomsOf_length]
      rfl
    have hresp : EnvResp g := EvalPlanValue.endValue_resp M τ p
    have hfit := fits_of_fapps_ne M τ hresp (recResultOf a)
      (recPreDomsOf a ++ [recMajorOf a]) ρ0 _ hlenD hne'
    have heq := fapps_piLam M τ hresp (recResultOf a)
      (recPreDomsOf a ++ [recMajorOf a]) ρ0 _ hfit
    rw [show recResultOf a = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1)) _ from rfl,
      piLam_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h)] at heq
    have hL : Equiv (den M σ ρ (iotaLhsOf w))
        (g (push (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) ρ0)) := by
      rw [hlhs]
      exact (fapps_congr hrecμ _).trans heq
    obtain ⟨xs0, ys0, hxy, hf1, hf2⟩ := TelFits_split _ _ _ _ hfit
    have hx0 : xs0 = w.preMajor.map (den M σ ρ) := by
      exact (List.append_inj hxy.symm (by rw [hf1.length, hpvl, recPreDomsOf_length])).1
    subst xs0
    have hy0 : ys0 = [den M σ ρ (ctorMajor w)] := (List.append_cancel_left hxy).symm
    subst ys0
    have hmaj : den M σ ρ (ctorMajor w) ∈ Ed M
        (den M τ (push (w.preMajor.map (den M σ ρ)) ρ0) (recMajorOf a)) := hf2.1
    have hsplit := list_split4 (w.preMajor.map (den M σ ρ)) a.family.parameters.length
      a.constructors.length a.family.indices.length hpvl pempty
    generalize hps : (w.preMajor.map (den M σ ρ)).take a.family.parameters.length = ps at hsplit
    generalize hmo : (w.preMajor.map (den M σ ρ)).getD a.family.parameters.length pempty = mo at hsplit
    generalize hms : ((w.preMajor.map (den M σ ρ)).drop (a.family.parameters.length + 1)).take
      a.constructors.length = ms at hsplit
    generalize his : (w.preMajor.map (den M σ ρ)).drop
      (a.family.parameters.length + 1 + a.constructors.length) = is at hsplit
    have hpsl : ps.length = a.family.parameters.length := by rw [← hps, List.length_take]; omega
    have hmsl : ms.length = a.constructors.length := by
      rw [← hms, List.length_take, List.length_drop]
      omega
    have hisl : is.length = a.family.indices.length := by rw [← his, List.length_drop]; omega
    have henv : w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)] =
        ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)])) := by
      rw [hsplit]
      simp only [List.append_assoc, List.cons_append]
    rw [henv] at hL
    rw [hsplit, den_recMajor M _ a ps mo ms is _ hpsl (by rw [hmsl, hk]) hisl] at hmaj
    have hmin : ms.getD j.val pempty = den M σ ρ w.minor := by
      have hm1 := w.hminor
      rw [hnp, hj] at hm1
      have hm2 : (w.preMajor.map (den M σ ρ))[a.family.parameters.length + 1 + j.val]? =
          some (den M σ ρ w.minor) := by
        rw [List.getElem?_map, hm1]
        rfl
      rw [← hms, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hjk,
        List.getElem?_drop, hm2]
      rfl
    have hfl : w.fields.length = (a.constructorViews j).fields.length :=
      witness_fields_length a w hwr hm j hcm
    have hst := (a.constructorViews j).storedType
    have hcpl := (a.constructorViews j).parameterCount
    have hctm : w.ctorMember.mtype =
        policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
          (foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals (a.constructorViews j).parameters.length
              (a.constructorViews j).fields.length ++ (a.constructorViews j).resultIndices)) := by
      rw [hcm]
      exact hst
    have hpeel := w.hpeel
    rw [hctm, show w.nparams + w.fields.length =
        ((a.constructorViews j).parameters ++ (a.constructorViews j).fields).length by
          rw [List.length_append]; omega, peelPis_policyPi] at hpeel
    have hdoms : w.ctorDoms = (a.constructorViews j).parameters ++ (a.constructorViews j).fields :=
      (congrArg Prod.fst (Option.some.inj hpeel)).symm
    have hkinds := w.hkinds
    rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
    have hplainKinds : w.kinds = (a.constructorViews j).fields.map (fun _ => RecKind.plain) := by
      have hp := analyzeFields_plain a.family.ref _ (hfree j)
      rw [hkinds] at hp
      exact Option.some.inj hp
    have hrw : rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.kinds w.ctorAfterParams = w.fields :=
      rhsArgs_plain _ _ _ _ _ _ (fun k hk' => by
        rw [hplainKinds] at hk'
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hk'
        rfl) _
    have hrhs : den M σ ρ (iotaRhsOf w) =
        fapps (den M σ ρ w.minor) (w.fields.map (den M σ ρ)) := by
      unfold iotaRhsOf
      rw [den_foldApps, hrw]
    rw [hrw] at hspine
    rw [hsplit] at hf1
    unfold recPreDomsOf at hf1
    obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hf1
    have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl])).1
    subst xa
    have hxb : xb = mo :: (ms ++ is) := (List.append_cancel_left hxab).symm
    subst xb
    obtain ⟨ya, yb, hyab, hya, hyb⟩ := TelFits_split _ _ _ _ hfb.2
    have hya' : ya = ms := (List.append_inj hyab.symm (by rw [hya.length, hmsl, hk])).1
    subst ya
    have hyb' : yb = is := (List.append_cancel_left hyab).symm
    subst yb
    have hisfit : TelFits M τ a.family.indices (push ps ρ0) is := by
      apply (TelFits_liftFields M τ (mo :: ms) (push ps ρ0) a.family.indices [] is).mp
      show TelFits M τ (liftFields (ms.length + 1) a.family.indices 0)
        (push ms (vcons mo (push ps ρ0))) is
      rw [hmsl, ← hk]
      exact hyb
    have hendpoint := PointwisePropEval.endValue_plain P μ K p fm ctors hE hfam hctors hrec hmem
      hBound hPred α hα ctx plans hctx hplans hFaith hFamily (w.ls.map (evalTotal σ)) hvs h0
      hpolicy hN hfree ps mo ms is (den M σ ρ (ctorMajor w)) hmsl hfa hfb.1 hya hisfit hmaj j
    let C := EvalPlanValue.context p M τ ρ0
    have hplain := PropEval.plain_shapes_of_free C
      (NormDPlanBridge.bodies_of_group hE hmem p.node) hN hfree
    obtain ⟨shapes, fuel, hfs, hd⟩ := p.node.h12 j
    have hsh : shapes = p.node.h14.shapesAt j :=
      fieldShapesFuel_unique hfs (p.node.h14.analyzed j)
    subst shapes
    have hmt := derivedMinor_nonrec a j fuel (p.node.h14.shapesAt j) (hplain j)
      (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
    obtain ⟨b, hstored⟩ : ∃ b, a.minorTypes[j.val]? =
        some (policyPi (liftFields (1 + j.val) (a.constructorViews j).fields 0) b) :=
      ⟨_, hd.symm.trans hmt⟩
    have hjm : j.val < a.minorTypes.length := by rw [hk]; exact j.isLt
    have hmtype : a.minorTypes[j.val] =
        policyPi (liftFields (1 + j.val) (a.constructorViews j).fields 0) b :=
      (List.getElem?_eq_some_iff.mp hstored).2
    have hg := TelFits_get a.minorTypes _ ms hya j.val hjm
    rw [hmtype] at hg
    have hRaw : Admissible (famDataOf p.node.a) (NormPropEval.base P μ C) :=
      (EvalPlanNormalProp.normalized_closed P μ (EvalPlan.ofNode p.node)
        fm ctors hE hmem τ h0 hpolicy).1
    have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem p.node hPred α hα
      ctx plans hctx hplans hFaith (NormPropEval.base P μ C) hRaw hFamily
    have hPT0 : PropTel M τ (a.constructorViews j).fields (push ps ρ0) := by
      apply propTel_of_typings_at P μ K τ a.family.parameters
        (a.constructorViews j).fields (F.rawEnv τ a.family.member.arity) ?_ ps hfa
      intro k
      obtain ⟨l, hl, d, hd⟩ :=
        hBound.2.2.2 p.node (selection_prop a τ h0 hpolicy).1 hpolicy j
          (w.ls.map (evalTotal σ)) hvs k
      exact ⟨l, hl τ, d, hd⟩
    have hprefix : (mo :: ms.take j.val).length = 1 + j.val := by
      rw [List.length_cons, List.length_take,
        Nat.min_eq_left (show j.val ≤ ms.length by rw [hmsl]; exact Nat.le_of_lt j.isLt)]
      exact Nat.add_comm _ _
    have hPT := propTel_liftFields M τ (mo :: ms.take j.val) (push ps ρ0)
      (a.constructorViews j).fields [] hPT0
    change PropTel M τ
      (liftFields (mo :: ms.take j.val).length (a.constructorViews j).fields 0)
      (push (ms.take j.val) (vcons mo (push ps ρ0))) at hPT
    rw [hprefix] at hPT
    have hlen : (w.fields.map (den M σ ρ)).length =
        (liftFields (1 + j.val) (a.constructorViews j).fields 0).length := by
      rw [List.length_map, liftFields_length', hfl]
    rw [hmin] at hg hendpoint
    have hsp := spine_proofs M τ b _ _ _ _ hlen hg hPT hspine
    have he : (a.constructorViews j).fields.map (fun _ => (pempty : PSet.{4})) =
        (w.fields.map (den M σ ρ)).map (fun _ => pempty) := by
      simp only [List.map_const', List.length_map, hfl]
    rw [he] at hendpoint
    rw [hrhs]
    exact hL.trans (hendpoint.trans hsp.symm)

/-- The literal stable IotaAt law, with both installed equations produced
from the full normalized faithful context and actual canonical plan. -/
theorem iota_at (P : Premises4)
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
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hfree : ∀ (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length) A,
      A ∈ ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).fields →
      occursConst (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.ref A = false)
    (Efin : ResolvedEnv)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin rr := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull hProp
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hRec := PointwiseRoleEquations.recursor_value_of_group P α μ
    hE hfam hctors hrec hmem ctxFull plansFull hctxFull hplansFull hFaithFull
  intro S hsub w hwr σ n Γ T ρ hl _ _ hr hrs hls hfit ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨_, hnM, _, hfr⟩ := iota_align p.node.a w hwr hm
  have hjk : w.ctorIdx < p.node.a.constructors.length := by have := w.hidx; omega
  let j : Fin p.node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = p.node.a.family.ref + 1 + j.val := by rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = p.node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := p.node.a.constructorsPresent j
    have h3 := hsubF _ _ (p.node.sub _ _ (members_extend_preserved p.node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  have hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hls l hl
  exact iota_eq P μ K p fm ctors hE hfam hctors hrec hmem hBound hPred α hα
    ctx plans hctx hplans hFaith hFamily hRec hN hfree w hwr hm j rfl hcm σ ρ
    (hProp _) hpolicy hvs
    (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr

/-- The complete literal recursor package on the checked plain Prop face.
Both stored-member typing and stable legacy iota are produced here. -/
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
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hfree : ∀ (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length) A,
      A ∈ ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).fields →
      occursConst (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.ref A = false) :
    RecPkg P μ K E' rr rm :=
  ⟨PointwisePropRecMem.member_sound P μ K hE hfam hctors hrec hmem hBound hPred α hα
      ctx plans hctx hplans hFaith ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin hsub => iota_at P μ K hE hfam hctors hrec hmem hBound hPred α hα
      ctx plans hctx hplans hFaith ctxFull plansFull hctxFull hplansFull hFaithFull
      hProp hpolicy hN hfree Efin hsub⟩

end Rcic.F3.PSet.PointwisePropPlainIota
