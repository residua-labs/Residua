import rcic.RcicF3PointwiseRole
import rcic.RcicF3PointwiseDataLocal
import rcic.RcicF3NormRoleDelta
import rcic.RcicF3NormDataRead

/-!
# Actual group value and delta equations for the separate interpretation

Only the family equation changes. The original stored constructors,
recursor plans, and transparent plain definitions keep their literal
operations. Every equation below is read from new Faithful data and actual
metadata; no old invariant or frame comparison is supplied.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseRoleEquations
open Rcic.Declarative Rcic.Model.PS RawFamily

theorem body_eq_of_faithful (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hF : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (r : Nat) (m : CheckedMember) (b : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = some b)
    (htr : transparent m.mclass = true)
    (σ : Nat → Nat) (ls : List Level) (ρ : Nat → PSet.{4}) :
    Equiv (μ r (ls.map (evalTotal σ)))
      (den (mkM P μ) σ ρ (instantiateLevels ls b)) := by
  obtain ⟨hc, _ha, _hr, hcl, hlvl⟩ :=
    EvalRoleDelta.transparent_body_data hW r m b hm hb htr
  have hrole : ctx r = .plain :=
    (hctx r (dom_of_members hm)).trans (NormRoleDelta.body_plain hW r m b hm hb)
  have hval : Equiv (μ r (ls.map (evalTotal σ)))
      (den (mkM P μ) (fun _ => 0) ρ0 b) := by
    have h := hF r m hm (ls.map (evalTotal σ))
    rw [hrole] at h
    change Equiv (μ r (ls.map (evalTotal σ)))
      (PSet.memberVal P μ m (ls.map (evalTotal σ))) at h
    simpa only [PSet.memberVal, hc, hb] using h
  rw [Ann.instantiateLevels_closed ls b hlvl,
    den_levels_closed (mkM P μ) σ (fun _ => 0) b hlvl ρ,
    den_closed (mkM P μ) (fun _ => 0) b hcl ρ ρ0]
  exact hval

theorem bodyEquations_of_faithful (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hF : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) E σ := by
  intro r ls b hw ρ
  obtain ⟨m, body, hm, htr, hb, he⟩ := transparentBody_some hw
  rw [he]
  exact body_eq_of_faithful P α μ ctx plans hW hctx hF r m body hm hb htr σ ls ρ

private theorem node_new_bodyless
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    ∀ r m, node.E0.members r = some m → E.members r = none → m.body = none := by
  intro r m hm hnone
  have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
  rcases groupMembersT_cases hmem r m hfinal with hold | hnew
  · rw [hold] at hnone
    cases hnone
  · exact groupMembersT_body_none hmem r m hnew

/-- Actual original fields normalize at the installed table using only
the produced body equations of its predecessor. -/
theorem bodyEquations_at_node (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hctx : ∀ r, Dom E' r →
      ctx r = NormRole.envCtx
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hF : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (node : RecNode E E' f rr rm) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) node.E0 σ := by
  have hctx0 : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hF0 : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E := fun r m hm vs =>
    hF r m (groupMembersT_preserve hmem r m hm) vs
  exact EvalRoleDelta.bodyEquations_extension P μ node.base
    (node_new_bodyless hmem node) σ
    (bodyEquations_of_faithful P α μ ctx plans hE hctx0 hF0 σ)


theorem constructor_value_of_group (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E') :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ (j : Fin p.node.a.constructors.length) vs,
      Equiv (μ (p.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
            (p.node.a.constructorViews j).fields.length) ρ0
          (p.node.a.constructors[j.val]).mtype) := by
  dsimp only
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  intro j vs
  have hm : E'.members (f + 1 + j.val) = some (p.node.a.constructors[j.val]) :=
    node_ctor_member p.node j
  have hr : rr = f + 1 + p.node.a.constructors.length := by
    have h := p.node.a.recursorRef
    rw [p.node.fam] at h
    exact h
  have hjr : f + 1 + j.val < rr := by
    exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left j.isLt (f + 1)) hr.symm
  have h := hFaith _ _ hm vs
  rw [hctx _ (dom_of_members hm), NormRole.envCtx_group,
    groupRoles_at_ctor _ _ hjr] at h
  change Equiv (μ (f + 1 + j.val) vs)
    (piLam (mkM P μ) (σOf vs)
      (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
        (nfOf (EvalPlanNormal.fd p) j.val)) ρ0
      (p.node.a.constructors[j.val]).mtype) at h
  rw [NormPropCtor.field_count] at h
  change Equiv (μ (p.node.a.family.ref + 1 + j.val) vs) _
  rw [p.node.fam]
  exact h


theorem family_equation_of_group (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (EvalPlanNormal.fd p) (PointwiseDataLocal.frame P μ p) vs) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  change ∀ vs : List Nat, Equiv (μ p.node.a.family.ref vs)
    (ofFrame P μ (EvalPlanNormal.fd p) (PointwiseDataLocal.frame P μ p) vs)
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  intro vs
  have h := hFaith f fm hf' vs
  rw [hctx f (dom_of_members hf'), NormRole.envCtx_group, groupRoles_at_f] at h
  change Equiv (μ f vs)
    (PointwiseRole.familyValue α P μ (EvalPlanNormal.fd p) vs) at h
  rw [PointwiseRole.familyValue_data α P μ _ hType vs] at h
  have har : α (EvalPlanNormal.fd p).fref = p.node.a.family.member.arity :=
    PointwiseRole.arity_at_node hα p.node
  rw [har] at h
  simpa only [p.node.fam] using h

theorem recursor_value_of_group (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E') :
    ∀ vs, Equiv (μ rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs)
        (EvalPlan.ofGroup hE hfam hctors hrec hmem) rm) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hrm : E'.members rr = some rm := groupMembersT_installed hmem
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hlt : f < rr := by
    have hr := p.node.a.recursorRef
    rw [p.node.fam] at hr
    change rr = f + 1 + p.node.a.constructors.length at hr
    rw [hr]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self f)
      (Nat.le_add_right (f + 1) p.node.a.constructors.length)
  intro vs
  have h := hFaith rr rm hrm vs
  rw [hctx rr (dom_of_members hrm), NormRole.envCtx_group, groupRoles_at_rr _ hlt] at h
  have hp : plans rr = some p := by
    rw [hplans rr (dom_of_members hrm)]
    change (if rr = rr then some p else EvalRole.envPlan hE rr) = some p
    exact if_pos rfl
  rw [hp] at h
  exact h

end Rcic.F3.PSet.PointwiseRoleEquations
