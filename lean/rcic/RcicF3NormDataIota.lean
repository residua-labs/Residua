import rcic.RcicF3NormDataIotaRow
import rcic.RcicF3NormDataIotaCases
import rcic.RcicF3NormDataRecMem

/-!
# Typed legacy DATA iota for the normalized production endpoint

The actual installed family is decoded at its complete parameter/index key.
Produced normalized density and bounded original-field transport recover the
constructor tuple in that same model. Only the witnessed row is unfolded:
its legacy analysis supplies direct recursive fields, even if other rows
have positive Pi depth. Each RHS recursive call is shown to fit the original
stored recursor telescope before applying the literal nodeCore endpoint.

The full recursor valuation, including the extra motive universe, and all
child/result indices are retained. The small normalized candidate remains
explicit; there is no raw/normalized fixed-point equality, global NoFunRec,
assumed recursive-call law or assumed iota clause. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataIota
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily RawFamilyRec PropEval

/-- One actual typed legacy redex, using the installed normalized family
and the original stored recursor and constructor equations. -/
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
    (hRec : ∀ vs, Equiv (μ p.rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p p.rm))
    (hCtor : ∀ (j : Fin p.node.a.constructors.length) vs,
      Equiv (μ (p.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
            (p.node.a.constructorViews j).fields.length) ρ0
          (p.node.a.constructors[j.val]).mtype))
    (hsmall : ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofNode p.node)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node)) A)
    (hType : UniformType p.node.a.family.resultLevel)
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K p.rr)
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X) :
    Equiv (den (mkM P μ) σ ρ (iotaLhsOf w))
      (den (mkM P μ) σ ρ (iotaRhsOf w)) := by
  let M := mkM P μ
  let a := p.node.a
  let τ := σOf (w.ls.map (evalTotal σ))
  let g := EvalPlanValue.endValue M τ p
  have h0 : evalTotal τ a.family.resultLevel ≠ 0 := Nat.ne_of_gt (hType τ)
  have hFF := NormDPlanBridge.bodies_of_group hE hmem p.node
  obtain ⟨_, _, _, hTF, _, hB⟩ := CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hCB : ∀ q : Fin a.constructors.length,
      exprLevelsBounded a.family.member.arity (a.constructors[q.val]).mtype = true := by
    intro q
    have h := (hTF _ _ (node_ctor_member p.node q)).2.1
    rw [(a.constructorViews q).arity] at h
    exact h
  let N := frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))
  have hN : Admissible (famDataOf a) N :=
    frame_admissible P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node)) hsmall
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
    have hrf := NormDataIotaRow.row_direct p.node hFF j w.kinds hkinds
    have hrhs : den M σ ρ (iotaRhsOf w) = fapps (den M σ ρ w.minor)
        ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams).map (den M σ ρ)) := by
      unfold iotaRhsOf
      rw [den_foldApps]
    rw [hrhs]
    -- the constructor telescope after the recursor-side parameters, read semantically
    have hsem : SemTel M σ ρ w.ctorAfterParams (a.constructorViews j).fields
        (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
        (push ((w.preMajor.take w.nparams).map (den M σ ρ)) ρ) := by
      have h1 := w.hctorAfter
      rw [hctm] at h1
      have hpl : (w.preMajor.take w.nparams).length = (a.constructorViews j).parameters.length := by
        rw [List.length_take, w.hpre, hcpl, hnp]; omega
      exact SemTel.applyTel (w.preMajor.take w.nparams) (a.constructorViews j).parameters _ hpl _ _
        (semTel_instantiateLevels M σ ρ w.ls _ _) h1
    -- the redex's level valuation agrees with the model's below the family's arity
    have hLlen : a.family.member.arity ≤ (w.ls.map (evalTotal σ)).length := by
      rw [List.length_map, w.hlsLen, hm, a.recursorArity]
      rw [NormDataRead.data_policy a hType]
      exact Nat.le_succ _
    have hσ : ∀ i, i < a.family.member.arity →
        (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i)) i = σOf (w.ls.map (evalTotal σ)) i := by
      intro i hi
      have hi' : i < (w.ls.map (evalTotal σ)).length := Nat.lt_of_lt_of_le hi hLlen
      show ((w.ls.map (evalTotal σ))[i]?).getD (σ i) = (w.ls.map (evalTotal σ)).getD i 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rfl
    have hpsT : (w.preMajor.take w.nparams).map (den M σ ρ) = ps := by
      rw [List.map_take, hnp, hps]
    have hff := NormDataIotaCases.application_mem P μ (famDataOf a) N
      a.family.member.arity hN hB hFamily τ (ps ++ is) (den M σ ρ (ctorMajor w))
      (by simp only [famDataOf, List.length_append, hpsl, hisl]) hmaj
    let C : Context := {
      E := p.E, E' := p.E', f := p.f, rr := p.rr, rm := p.rm, node := p.node
      M := M, σ := τ, parameters := ps, motive := mo, minors := ms
      minor_length := hmsl }
    have hcanon := NormDataRead.family_vector_bound (w.ls.map (evalTotal σ))
      a.family.member.arity (K p.rr) hLlen hvs
    have hkey : paramKey a.family.parameters.length (key (ps ++ is)) = key ps := by
      rw [← hpsl]
      exact paramKey_append ps is
    obtain ⟨j', xs', hp', hfields, hresult, hzd⟩ :=
      NormDataIotaCases.original_cases_at P μ K C rfl fm ctors hE hfam hctors hrec hmem
        hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hFamily hsmall
        hcanon h0 (key (ps ++ is)) (den M σ ρ (ctorMajor w)) hkey hff.2
    have hmne : ¬ Equiv (den M σ ρ (ctorMajor w)) pempty :=
      fun he => dataVal_ne_pempty j'.val xs' (hzd.symm.trans he)
    have hcref : w.ctorRef = a.family.ref + 1 + j.val := by
      rw [w.hctorIdx, hfr, hj]
    have hctorμ : Equiv (M.μ w.ctorRef (w.lsC.map (evalTotal σ)))
        (piLam M (σOf (w.lsC.map (evalTotal σ)))
          (ctorEnd M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
            (a.constructorViews j).fields.length) ρ0 (a.constructors[j.val]).mtype) := by
      rw [hcref]
      exact hCtor j _
    have hmajV : den M σ ρ (ctorMajor w) =
        fapps (M.μ w.ctorRef (w.lsC.map (evalTotal σ))) (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ)) := by
      unfold ctorMajor ctorSpine
      rw [den_foldApps, List.map_append]
      rfl
    rw [hst] at hctorμ
    have hlenC : (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ)).length =
        ((a.constructorViews j).parameters ++ (a.constructorViews j).fields).length := by
      simp [w.hctorParams, hnp, hcpl, hfl]
    have hneC : ¬ Equiv (fapps (piLam M (σOf (w.lsC.map (evalTotal σ))) (ctorEnd M (σOf (w.lsC.map (evalTotal σ)))
        (famDataOf a) j.val (a.constructorViews j).fields.length) (fun _ => pempty)
        (policyPi ((a.constructorViews j).parameters ++ (a.constructorViews j).fields)
          (foldApps (.const a.family.ref (policyFamilyLevels a.family))
            (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
              (a.constructorViews j).resultIndices))))
        (w.ctorParams.map (den M σ ρ) ++ w.fields.map (den M σ ρ))) pempty := fun h =>
      hmne (by rw [hmajV]; exact (fapps_congr hctorμ _).trans h)
    have hfitC := fits_of_fapps_ne M _ (ctorEnd_resp M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
      (a.constructorViews j).fields.length) _ _ (fun _ => pempty) _ hlenC hneC
    have heqC := fapps_piLam M _ (ctorEnd_resp M (σOf (w.lsC.map (evalTotal σ))) (famDataOf a) j.val
      (a.constructorViews j).fields.length) (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews j).parameters.length (a.constructorViews j).fields.length ++
          (a.constructorViews j).resultIndices)) _ (fun _ => pempty) _ hfitC
    rw [piLam_foldApps_const] at heqC
    have h0C : ¬ evalTotal (σOf (w.lsC.map (evalTotal σ))) a.family.resultLevel = 0 := Nat.ne_of_gt (hType _)
    have hzv : Equiv (den M σ ρ (ctorMajor w)) (dataVal j.val (w.fields.map (den M σ ρ))) := by
      rw [hmajV]
      refine (fapps_congr hctorμ _).trans (heqC.trans ?_)
      unfold ctorEnd cond
      cases hd' : M.dec (evalTotal (σOf (w.lsC.map (evalTotal σ))) (famDataOf a).resLevel = 0) with
      | isTrue h => exact absurd h h0C
      | isFalse _ =>
          show Equiv (dataVal j.val (lastVals _ _)) _
          rw [push_append, show (a.constructorViews j).fields.length = (w.fields.map (den M σ ρ)).length by
            rw [List.length_map, hfl], lastVals_push]
          exact Equiv.rfl
    have hjj : j' = j := Fin.ext (by
      have hpair := ordPair_equiv (ordPair_equiv (hzd.symm.trans hzv)).2
      exact ord_inj hpair.1)
    have htel : TelFits M τ (a.constructorViews j).fields (push ps ρ0) xs' := by
      change TelFits M τ (a.constructorViews j').fields (push ps ρ0) xs' at hfields
      rw [hjj] at hfields
      exact hfields
    have hzd' : Equiv (den M σ ρ (ctorMajor w)) (dataVal j.val xs') := by
      simpa only [hjj] using hzd
    have hR : Equiv (g
        (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) ρ0))
        (fapps (ms.getD j.val pempty)
          (ihArgs a.family.ref (RecPlan.nodeCore M p.node ms)
            (a.constructorViews j).fields (w.fields.map (den M σ ρ)))) := by
      change Equiv (EvalPlanValue.endValue M τ p _) _
      rw [NormDataRead.endpoint_data M τ p ps mo ms is
        (den M σ ρ (ctorMajor w)) ρ0 h0 hmsl hisl]
      exact NormDataIotaRow.core_of_row M p.node hFF j w.kinds hkinds ms
        (w.fields.map (den M σ ρ)) (den M σ ρ (ctorMajor w))
        (by rw [List.length_map, hfl]) hzv
    -- the recursive calls
    have hcall : ∀ (k : Nat) (x A : Expr Nat) (idx : List (Expr Nat)), w.fields[k]? = some x →
        w.kinds[k]? = some .directRec →
        (a.constructorViews j).fields[k]? = some (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals w.nparams (0 + k) ++ idx)) → idx.length = a.family.indices.length →
        (familyIdx w.nparams A).map (den M σ ρ) = idx.map (den M (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
          (push ((w.fields.take k).map (den M σ ρ)) (push ((w.preMajor.take w.nparams).map (den M σ ρ)) ρ))) →
        Equiv (den M σ ρ (recCallField (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors x A))
          (RecPlan.nodeCore M p.node ms (den M σ ρ x)) := by
      intro k x A idx hx hkk hF hidxl hidxD
      rw [Nat.zero_add, hnp] at hF
      rw [hpsT] at hidxD
      obtain ⟨hFk, hFk'⟩ := List.getElem?_eq_some_iff.mp hF
      -- the field's value lies in the family at the recursor's parameters and the field's indices
      have hxl : xs'.length = (w.fields.map (den M σ ρ)).length := by rw [htel.length, List.length_map, hfl]
      have hLx : LEq xs' (w.fields.map (den M σ ρ)) := (dataVal_inj hxl (hzd'.symm.trans hzv)).2
      have hget := TelFits_get _ _ xs' htel k hFk
      have hkl : (xs'.take k).length = k := by
        rw [List.length_take, hxl, List.length_map, hfl]; exact Nat.min_eq_left (Nat.le_of_lt hFk)
      have hkl' : ((w.fields.take k).map (den M σ ρ)).length = k := by
        rw [List.length_map, List.length_take, hfl]; exact Nat.min_eq_left (Nat.le_of_lt hFk)
      have hpe : push (xs'.take k) (push ps (fun _ => pempty)) = push (ps ++ xs'.take k) (fun _ => pempty) :=
        (push_append ps _ _).symm
      have hdp : (policyParameterLocals a.family.parameters.length k).map
          (den M τ (push (xs'.take k) (push ps ρ0))) = ps := by
        have h := den_paramLocals M τ ps (xs'.take k) (fun _ => pempty)
        rw [hpsl, hkl, ← hpe] at h
        exact h
      have hFk2 : ((a.constructorViews j).fields)[k]'hFk = foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals a.family.parameters.length k ++ idx) := hFk'
      rw [hFk2, den_foldApps, List.map_append, hdp] at hget
      -- the call's indices are the field's, read below the fields before it
      have hbC : exprLevelsBounded a.family.member.arity w.ctorMember.mtype = true := by rw [hcm]; exact hCB j
      rw [hctm] at hbC
      have hbF := (levelsBounded_policyPi _ _ _ hbC).1 _ (List.mem_append_right _ (List.getElem_mem hFk))
      rw [hFk2] at hbF
      have hcl := w.hctorClosed
      rw [hctm] at hcl
      have hcF := lift_policyPi_append_fixed _ _ _ 0 hcl k hFk
      rw [hFk2, Nat.zero_add, hcpl] at hcF
      have hLe : ∀ e, e ∈ idx →
          Equiv (den M (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i))
            (push ((w.fields.take k).map (den M σ ρ)) (push ps ρ)) e)
            (den M τ (push (xs'.take k) (push ps (fun _ => pempty))) e) := by
        intro e he
        have heF : e ∈ policyParameterLocals a.family.parameters.length k ++ idx := List.mem_append_right _ he
        rw [den_levels_agree M hσ e ((levelsBounded_foldApps _ _ _ hbF).2 e heF)]
        have hle := (lift_foldApps_fixed _ _ _ hcF).2 e heF
        rw [den_cutoff M _ e (a.family.parameters.length + k)
          (fun c' hc' => lift_closed_gen e _ hle c' 1 hc') _ (push ((w.fields.take k).map (den M σ ρ))
            (push ps (fun _ => pempty))) (fun i hi => push_push_agree _ _ _ _ i (by rw [hkl', hpsl]; exact hi))]
        refine den_congr M _ e (push_congr ?_ (fun _ => Equiv.rfl))
        rw [List.map_take]
        exact (LEq.take hLx k).symm
      have hLidx : LEq ((familyIdx w.nparams A).map (den M σ ρ))
          (idx.map (den M τ (push (xs'.take k) (push ps (fun _ => pempty))))) := by
        rw [hidxD]; exact LEq_map_of idx hLe
      have hxk : Equiv (xs'.getD k pempty) (den M σ ρ x) := by
        have := LEq_getD hLx k
        refine this.trans ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]
        exact Equiv.rfl
      obtain ⟨is', his'⟩ : ∃ is', (familyIdx w.nparams A).map (den M σ ρ) = is' := ⟨_, rfl⟩
      rw [his'] at hLidx
      have hisl' : is'.length = a.family.indices.length := by
        rw [hLidx.length, List.length_map, hidxl]
      have hxmem : den M σ ρ x ∈ Ed M (fapps (M.μ a.family.ref
          ((policyFamilyLevels a.family).map (evalTotal τ))) (ps ++ is')) :=
        mem_congr_left hxk (mem_congr_right (ed_congr M (fapps_congr_args _ (LEq_append (LEq.refl ps)
          hLidx.symm))) hget)
      -- the call's arguments fit the recursor's telescope
      have hffit := (NormDataIotaCases.application_mem P μ (famDataOf a) N
        a.family.member.arity hN hB hFamily τ (ps ++ is') (den M σ ρ x)
        (by simp only [famDataOf, List.length_append, hpsl, hisl']) hxmem).1
      obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hffit
      have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl]; rfl)).1
      subst hxa
      have hxb : xb = is' := (List.append_cancel_left hxab).symm
      subst hxb
      have hfidx : TelFits M τ (liftFields (a.minorTypes.length + 1) a.family.indices 0)
          (push (xa ++ mo :: ms) (fun _ => pempty)) xb := by
        have e1 : push (xa ++ mo :: ms) (fun _ => pempty) =
            push ([] : List PSet) (push (mo :: ms) (push xa (fun _ => pempty))) := by
          rw [push_append]; rfl
        have e2 : a.minorTypes.length + 1 = (mo :: ms).length := by
          rw [List.length_cons, hmsl, hk]
        rw [e1, e2, show (0 : Nat) = ([] : List PSet).length from rfl]
        exact (TelFits_liftFields M _ (mo :: ms) (push xa (fun _ => pempty)) a.family.indices [] xb).mpr hfb
      have hpd : recPreDomsOf a = (a.family.parameters ++ policyMotiveType a.family a.policy :: a.minorTypes) ++
          liftFields (a.minorTypes.length + 1) a.family.indices 0 := by
        unfold recPreDomsOf; simp only [List.append_assoc, List.cons_append]
      have hf1' := hf1
      rw [hpd, hsplit, show xa ++ mo :: (ms ++ is) = (xa ++ mo :: ms) ++ is by
        simp only [List.append_assoc, List.cons_append]] at hf1'
      obtain ⟨ya, yb, hyab, hya, _⟩ := TelFits_split _ _ _ _ hf1'
      have hya' : ya = xa ++ mo :: ms := (List.append_inj hyab.symm (by
        rw [hya.length]
        simp only [List.length_append, List.length_cons, hpsl, hmsl, hk])).1
      subst hya'
      have hmajx : den M σ ρ x ∈ Ed M (den M τ
          (push ((xa ++ mo :: ms) ++ xb) (fun _ => pempty)) (recMajorOf a)) := by
        rw [show (xa ++ mo :: ms) ++ xb = xa ++ mo :: (ms ++ xb) by simp only [List.append_assoc, List.cons_append],
          den_recMajor M _ a xa mo ms xb _ hpsl (by rw [hmsl, hk]) hisl']
        exact hxmem
      have hfit2 : TelFits M τ (recPreDomsOf a ++ [recMajorOf a]) (fun _ => pempty)
          ((xa ++ mo :: ms) ++ xb ++ [den M σ ρ x]) := by
        rw [hpd]
        exact TelFits.append (TelFits.append hya hfidx) ⟨hmajx, trivial⟩
      -- the recursive call is the recursor's value at the field
      have hpre' : (recPrefix w.preMajor w.nparams w.nMinors).map (den M σ ρ) = xa ++ mo :: ms := by
        unfold recPrefix
        rw [List.map_take, hsplit, hnp, hnM, show xa ++ mo :: (ms ++ is) = (xa ++ mo :: ms) ++ is by
          simp only [List.append_assoc, List.cons_append]]
        exact List.take_left' (by simp only [List.length_append, List.length_cons, hpsl, hmsl]; omega)
      have hden : den M σ ρ (recCallField (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors x A) =
          fapps (M.μ p.rr (w.ls.map (evalTotal σ))) ((xa ++ mo :: ms) ++ xb ++ [den M σ ρ x]) := by
        unfold recCallField
        rw [den_foldApps, List.map_append, List.map_append, hpre', his', hwr]
        rfl
      rw [hden]
      have heq2 := fapps_piLam M τ hresp (recResultOf a)
        (recPreDomsOf a ++ [recMajorOf a]) ρ0 _ hfit2
      rw [show recResultOf a = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1)) _ from rfl,
        piLam_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h)] at heq2
      refine (fapps_congr hrecμ _).trans (heq2.trans ?_)
      have henv2 : (xa ++ mo :: ms) ++ xb ++ [den M σ ρ x] = xa ++ mo :: (ms ++ (xb ++ [den M σ ρ x])) := by
        simp only [List.append_assoc, List.cons_append]
      rw [henv2]
      change Equiv (EvalPlanValue.endValue M τ p
        (push (xa ++ mo :: (ms ++ (xb ++ [den M σ ρ x]))) ρ0))
        (RecPlan.nodeCore M p.node ms (den M σ ρ x))
      rw [NormDataRead.endpoint_data M τ p xa mo ms xb (den M σ ρ x) ρ0 h0 hmsl hisl']
      exact Equiv.rfl
    have hRHS := rhsArgs_den M σ ρ (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors a.family.ref
      a.family.indices.length (policyFamilyLevels a.family) (RecPlan.nodeCore M p.node ms)
      (fun i => ((w.ls.map (evalTotal σ))[i]?).getD (σ i)) w.fields w.kinds w.ctorAfterParams
      (a.constructorViews j).fields 0 _ hsem hkinds (by rw [hnp]; exact hrf) hfl hcall
    rw [hmin] at hR
    exact hL.trans (hR.trans (fapps_congr_args _ hRHS).symm)

end Rcic.F3.PSet.NormDataIota
