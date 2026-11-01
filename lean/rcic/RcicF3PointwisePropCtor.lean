import rcic.RcicF3PointwisePropPrefix

/-!
# Original uniformly Prop constructors at the pointwise table

The policy-independent normalized Prop closure is reused literally.
The current Prop family equation is unchanged; all prior families retain
their NEW meanings through PointwiseRole.GInv. The actual stored type and
own constructor bound produce membership, including PropOnly.
No old/new invariant equality is used. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropCtor
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex

/-- Every original stored constructor is sound at its own bound for a
uniformly Prop family, including the propOnly policy. All semantic inputs
of the original-telescope bridge are produced internally. -/
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
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length) :
    MemberSound P μ K (f + 1 + j.val)
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors[j.val]) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨hN, hClosed⟩ := NormPropCtorUniform.normalized_closed P μ p fm ctors hE hmem hProp
  have hFacts := PointwisePropPrefix.canonical_group_facts P K μ hE hfam hctors
    hrec hmem hPred α hα ctx plans hctx hplans hFaith hProp
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith hProp
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
  rw [NormPropCtor.field_count]
  apply NormPropCtor.value_mem P μ p (frame P μ (EvalPlanNormal.fd p)) hN hClosed
    (ls.map (evalTotal σ)) hvs j hFamily
    (PointwiseRoleEquations.bodyEquations_at_node P α μ ctx plans hE hfam hctors hrec hmem
      hctx hFaith p.node _) (hProp _)
  intro zs hz
  obtain ⟨u, d, hd⟩ := hBound.2.1 p.node j (ls.map (evalTotal σ)) hvs hbound
  have hs := hsound_ty (P.good _ rfl) (hFacts.rawEnv (σOf (ls.map (evalTotal σ))) _) d hd
  exact tel_end_type' _ _ d (p.node.a.constructorViews j).storedType hs
    ρ0 zs True.intro hz

end Rcic.F3.PSet.PointwisePropCtor
