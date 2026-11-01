import rcic.RcicF3IndexedPropSpine
import rcic.RcicF3IndexedPropPlainValue
import rcic.RcicF3NormPropPlainIota

/-!
# Actual plain-redex arguments and the remaining index-coherence boundary

The nonempty installed left application recovers its actual typed recursor
arguments. The typed right spine and same-target memberships then recover
actual ordinary fields in the stored minor telescope. Removing the real
motive/minor prefix gives field TelFits at recursor-side parameters.
No field is erased and no all-fields Prop predicate is used.

This module deliberately stops before a universal iota theorem: Arguments
contains the supplied recursor indices and the actual constructor fields,
but not their unproved index agreement. The required LEq of those indices
with the constructor result-index read must be derived from the actual
left typing and its hereditary soundness/bounds. A legacy witness alone
does not supply it. No key-agreement or field-comparison callback is added
to IotaAt, and no global InScope condition is imposed.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedPropPlainIota
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

/-- The actual recursor valuation, including its motive universe slot. -/
noncomputable def valuation {S : ResolvedEnv} (w : IotaWitness S) (σ : Nat → Nat) : Nat → Nat :=
  σOf (w.ls.map (evalTotal σ))

/-- Produced data for the plain endpoint. Index agreement is deliberately
not a field: proving that extra proposition is the remaining obligation. -/
structure Arguments (M : Interp.{4}) (p : EvalPlan.Plan)
    {S : ResolvedEnv} (w : IotaWitness S) (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (j : Fin p.node.a.constructors.length)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4}) : Prop where
  split : w.preMajor.map (den M σ ρ) = ps ++ mo :: (ms ++ is)
  parameters_length : ps.length = p.node.a.family.parameters.length
  minors_length : ms.length = p.node.a.constructors.length
  indices_length : is.length = p.node.a.family.indices.length
  parameters_fit : TelFits M (valuation w σ) p.node.a.family.parameters ρ0 ps
  motive_fit : mo ∈ Ed M (den M (valuation w σ) (push ps ρ0)
    (policyMotiveType p.node.a.family p.node.a.policy))
  minors_fit : TelFits M (valuation w σ) p.node.a.minorTypes
    (vcons mo (push ps ρ0)) ms
  indices_fit : TelFits M (valuation w σ) p.node.a.family.indices (push ps ρ0) is
  major_fit : den M σ ρ (ctorMajor w) ∈ Ed M
    (fapps (M.μ p.node.a.family.ref
      ((policyFamilyLevels p.node.a.family).map (evalTotal (valuation w σ)))) (ps ++ is))
  fields_fit : TelFits M (valuation w σ) (p.node.a.constructorViews j).fields
    (push ps ρ0) (w.fields.map (den M σ ρ))
  minor_read : ms.getD j.val pempty = den M σ ρ w.minor
  lhs_endpoint : Equiv (den M σ ρ (iotaLhsOf w))
    (EvalPlanValue.endValue M (valuation w σ) p
      (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) ρ0))
  rhs_application : den M σ ρ (iotaRhsOf w) =
    fapps (den M σ ρ w.minor) (w.fields.map (den M σ ρ))

/-- Recover the actual fields from the installed recursor's nonempty
application and the right hereditary typing's spine. All inserted minor
binders are removed only after producing the lifted tuple's membership. -/
theorem arguments_of_nonempty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
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
    (hspine : SpineFacts (mkM P μ) (den (mkM P μ) σ ρ w.minor)
      ((rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.kinds w.ctorAfterParams).map (den (mkM P μ) σ ρ)))
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X)
    (hne : ¬ Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, Arguments (mkM P μ) p w σ ρ j ps mo ms is := by
  let M := mkM P μ
  let a := p.node.a
  let τ := σOf (w.ls.map (evalTotal σ))
  let g := EvalPlanValue.endValue M τ p
  obtain ⟨hnp, hnM, hnq, hfr⟩ := iota_align a w hwr hm
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
  have hprefix : (mo :: ms.take j.val).length = 1 + j.val := by
    rw [List.length_cons, List.length_take,
      Nat.min_eq_left (show j.val ≤ ms.length by rw [hmsl]; exact Nat.le_of_lt j.isLt)]
    exact Nat.add_comm _ _
  rw [hmin] at hg
  have hgLift : den M σ ρ w.minor ∈ Ed M
      (den M τ (push (mo :: ms.take j.val) (push ps ρ0))
        (policyPi (liftFields (mo :: ms.take j.val).length
          (a.constructorViews j).fields 0) b)) := by
    rw [hprefix]
    exact hg
  have hneR : ¬ Equiv (den M σ ρ (iotaRhsOf w)) pempty := by
    intro he
    exact hne ((rhs_eq_ed_pempty mr ml he).symm.trans he)
  have hneFields : ¬ Equiv
      (fapps (den M σ ρ w.minor) (w.fields.map (den M σ ρ))) pempty := by
    rw [← hrhs]
    exact hneR
  have hfields := IndexedPropSpine.fields_of_lifted_minor M τ
    (a.constructorViews j).fields (push ps ρ0) (mo :: ms.take j.val)
    (den M σ ρ w.minor) (w.fields.map (den M σ ρ)) b
    (by rw [List.length_map, hfl]) hgLift hspine hneFields
  exact ⟨ps, mo, ms, is,
    ⟨hsplit, hpsl, hmsl, hisl, hfa, hfb.1, hya, hisfit, hmaj,
      hfields, hmin, hL, hrhs⟩⟩

/-- The actual right-hand typed derivation produces the spine premise;
no ordinary-field fitting callback is accepted by this wrapper. -/
theorem arguments_of_typed_nonempty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
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
    {n : Nat} {Γ : LCtx} {T : Expr Nat}
    (hr : HasTyT S n Γ (iotaRhsOf w) T) (hrs : HSoundT (mkM P μ) σ hr)
    (hfit : Fits (mkM P μ) σ Γ ρ)
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X)
    (hne : ¬ Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, Arguments (mkM P μ) p w σ ρ j ps mo ms is :=
  arguments_of_nonempty P μ p fm ctors hE hmem hRec hN hfree w hwr hm j hj hcm
    σ ρ (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr hne

end Rcic.F3.PSet.IndexedPropPlainIota

#print axioms Rcic.F3.PSet.IndexedPropPlainIota.arguments_of_nonempty
#print axioms Rcic.F3.PSet.IndexedPropPlainIota.arguments_of_typed_nonempty
