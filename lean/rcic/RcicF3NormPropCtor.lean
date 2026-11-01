import rcic.RcicF3NormRoleDelta
import rcic.RcicF3EvalPlanNormalProp
import rcic.RcicF3EvalPlanNormalTuple
import rcic.RcicF3RawFamilyCtor
import rcic.RcicF3NormCandidatePrefix

/-!
# Original stored constructors into the normalized proof-family frame

The argument tuple fits the constructor's own original telescope. Full
stored result typehood recovers the family parameter/index fit by inverting
the nonempty complete family application. Inhabited forward normalization
then supplies the normalized fields at the same values and result key.

This is a bridge for the new normalized family interpretation. It does not
assert closure of the original raw operator or replace parameter mirrors
by syntactic equality. The local theorem keeps the exact component inputs
visible; the canonical wrapper supplies them from the actual group below.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropCtor
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex

/-- The normalized descriptor preserves the ordinary field count used by
the installed constructor endpoint. -/
theorem field_count (p : EvalPlan.Plan) (j : Fin p.node.a.constructors.length) :
    nfOf (EvalPlanNormal.fd p) j.val = (p.node.a.constructorViews j).fields.length := by
  let jn : Fin (EvalPlanNormal.fd p).ctors.length :=
    ⟨j.val, by simpa only [EvalPlanNormal.ctors_length] using j.isLt⟩
  have hi : EvalPlanNormal.index p jn = j := Fin.ext rfl
  have hg := EvalPlanNormal.ctor_get p jn
  rw [hi] at hg
  have hj : (EvalPlanNormal.fd p).ctors[j.val]? =
      some (EvalPlanNormal.fields p j, (p.node.a.constructorViews j).resultIndices) := by
    rw [List.getElem?_eq_getElem jn.isLt]
    exact congrArg some hg
  unfold nfOf
  rw [hj]
  exact (List.length_map _ _).trans
    (EvalPlanNormal.specs_length (p.constructors j).fields)

/-- Constructor membership at the original stored telescope. The own
parameter fit is never transported to a different candidate table. -/
theorem value_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (C : Frame)
    (hC : Admissible (EvalPlanNormal.fd p) C)
    (hc : Closed P μ (EvalPlanNormal.fd p) C)
    (vs : List Nat) (hvs : vs.length = p.node.a.family.member.arity)
    (j : Fin p.node.a.constructors.length)
    (hf : ∀ us, Equiv (μ p.node.a.family.ref us)
      (ofFrame P μ (EvalPlanNormal.fd p) C us))
    (hδ : DeltaNormalize.BodyEquations (mkM P μ) p.node.E0 (σOf vs))
    (h0 : evalTotal (σOf vs) p.node.a.family.resultLevel = 0)
    (htyp : ∀ zs, TelFits (mkM P μ) (σOf vs)
        ((p.node.a.constructorViews j).parameters ++ (p.node.a.constructorViews j).fields)
        ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0)
        (foldApps (.const p.node.a.family.ref (policyFamilyLevels p.node.a.family))
          (policyParameterLocals (p.node.a.constructorViews j).parameters.length
            (p.node.a.constructorViews j).fields.length ++
            (p.node.a.constructorViews j).resultIndices)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v))) :
    piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
          (p.node.a.constructorViews j).fields.length) ρ0
        (p.node.a.constructors[j.val]).mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0
        (p.node.a.constructors[j.val]).mtype) := by
  let M := mkM P μ
  let fd := EvalPlanNormal.fd p
  let cv := p.node.a.constructorViews j
  rw [cv.storedType]
  refine piLam_mem M _ (ctorEnd_resp M _ fd j.val cv.fields.length) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, xs, rfl, hps, hxs⟩ := TelFits_split cv.parameters cv.fields ρ0 zs hz
  have hpl : ps.length = cv.parameters.length := hps.length
  have hxl : xs.length = cv.fields.length := hxs.length
  have hlevels : policyFamilyLevels p.node.a.family =
      (List.range vs.length).map Level.param := by
    rw [hvs]
    rfl
  have hR : Equiv (den M (σOf vs) (push (ps ++ xs) ρ0)
      (foldApps (.const p.node.a.family.ref (policyFamilyLevels p.node.a.family))
        (policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices)))
      (fapps (ofFrame P μ fd C vs)
        (ps ++ cv.resultIndices.map (den M (σOf vs) (push xs (push ps ρ0))))) := by
    rw [hlevels, den_foldApps, List.map_append, ← hpl, ← hxl, den_paramLocals]
    change Equiv (fapps (μ p.node.a.family.ref
      (((List.range vs.length).map Level.param).map (evalTotal (σOf vs)))) _) _
    rw [map_param_σOf, push_append]
    exact fapps_congr (hf vs) _
  obtain ⟨v, hv0⟩ := htyp (ps ++ xs) hz
  have hv := mem_congr_left hR hv0
  have hne := ne_of_mem_sort (M := M) rfl hv
  have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0
      (ps ++ cv.resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))) :=
    fits_of_fapps_ne M (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 _
      (by
        rw [List.length_append, List.length_append, List.length_map,
          hpl, cv.parameterCount, cv.indexCount]
        rfl) hne
  have he := hR.trans (apply_ofFrame P μ fd C vs _ hfit)
  refine mem_congr_right ((ed_congr M he).trans
    (ed_tyv M (admissible_dich hC vs _))).symm ?_
  have hp : TelFits M (σOf vs) fd.params ρ0 ps :=
    telFits_prefix M (σOf vs) fd.params fd.indices ρ0 ps _
      (hpl.trans cv.parameterCount) hfit
  have hn := EvalPlanNormal.fields_forward M p.node.E0 (σOf vs) hδ
    (p.constructors j).fields (push ps ρ0) xs hxs
  let jn : Fin fd.ctors.length :=
    ⟨j.val, by simpa only [fd, EvalPlanNormal.ctors_length] using j.isLt⟩
  have hi : EvalPlanNormal.index p jn = j := Fin.ext rfl
  have hg := EvalPlanNormal.ctor_get p jn
  rw [hi] at hg
  have hh := ctor_end_mem P μ fd C hc hf vs jn ps xs hp
    (by rw [hg]; exact hn.1)
    (by intro hne; exact (hne h0).elim)
  rw [hg] at hh
  rw [← hxl]
  exact hh

/-- The actual group's original stored constructor is sound at its own
bound. Admission, the new predecessor invariant and canonical faithfulness
produce every input of the normalized constructor bridge internally. -/
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length) :
    MemberSound P μ K (f + 1 + j.val)
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors[j.val]) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨hN, hClosed⟩ := EvalPlanNormalProp.normalized_closed P μ p fm ctors
    hE hmem (fun _ => 0) (hProp _) hpolicy
  have hFacts := NormCandidatePrefix.canonical_group_facts P K μ hE hfam hctors
    hrec hmem hPred ctx plans hctx hplans hFaith hN
  have hFamily := NormCandidatePrefix.family_equation_of_group P μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hlenC := node_ctors_length p.node hrr
  have hjr : f + 1 + j.val < rr := by
    have hj : j.val < ctors.length := Nat.lt_of_lt_of_eq j.isLt hlenC
    omega
  have hctor : E'.members (f + 1 + j.val) = some (p.node.a.constructors[j.val]) :=
    node_ctor_member p.node j
  have hbody : (p.node.a.constructors[j.val]).body = none :=
    groupMembersT_body_none hmem _ _ (node_ctor_mem hmem hL hrr p.node j)
  have hvalue : ∀ vs, Equiv (μ (f + 1 + j.val) vs)
      (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
          (nfOf (EvalPlanNormal.fd p) j.val)) ρ0
        (p.node.a.constructors[j.val]).mtype) := by
    intro vs
    have h := hFaith _ _ hctor vs
    rw [hctx _ (dom_of_members hctor), NormRole.envCtx_group,
      groupRoles_at_ctor _ _ hjr] at h
    exact h
  intro σ ls ρ hlen hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvs : (ls.map (evalTotal σ)).length = p.node.a.family.member.arity := by
    rw [List.length_map, hlen, (p.node.a.constructorViews j).arity]
  have hbound : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K (f + 1 + j.val) := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    exact hlevels l hl
  rw [den_inst_canon (mkM P μ) σ ls ρ (p.node.a.constructors[j.val]).mtype
    (hFacts.facts _ _ hctor).1 (hlen ▸ (hFacts.facts _ _ hctor).2.1)]
  refine mem_congr_left (hvalue _).symm ?_
  rw [field_count]
  apply value_mem P μ p (frame P μ (EvalPlanNormal.fd p)) hN hClosed
    (ls.map (evalTotal σ)) hvs j hFamily
    (NormRoleDelta.bodyEquations_at_node P μ ctx plans hE hfam hctors hrec hmem
      hctx hFaith p.node _) (hProp _)
  intro zs hz
  obtain ⟨u, d, hd⟩ := hBound.2.1 p.node j (ls.map (evalTotal σ)) hvs hbound
  have hs := hsound_ty (P.good _ rfl) (hFacts.rawEnv (σOf (ls.map (evalTotal σ))) _) d hd
  exact tel_end_type' _ _ d (p.node.a.constructorViews j).storedType hs
    ρ0 zs True.intro hz

end Rcic.F3.PSet.NormPropCtor
