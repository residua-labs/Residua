import rcic.RcicF3NormRole

/-!
# Produced transparent-body equations for the normalized canonical roles

Only the role context changes. An admitted member with a body still has
the plain role, and its faithful equation pays delta at every valuation.
The reader extension is bodyless. No bounded soundness, conversion-mirror
premise or constructor-closure hypothesis is used here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRoleDelta
open Rcic.Declarative Rcic.Model.PS

/-- Group installation cannot assign a family role to a declaration with
a body. This fact concerns the new canonical context literally. -/
theorem body_plain : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ r m b, E.members r = some m → m.body = some b →
      NormRole.envCtx hW r = .plain
  | _, .empty, _, _, _, h, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE _ _ _ _, r, m, b, h, hb => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        exact body_plain hE r m b h hb
  | _, .definition E r0 _ _ _ hE hfresh _ _ _ _ _ _, r, m, b, h, hb => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact NormRole.envCtx_fresh hE r hfresh
      · rw [members_extend_ne E r0 _ r hr] at h
        exact body_plain hE r m b h hb
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, r, m, b, h, hb => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact NormRole.envCtx_fresh hE r hfresh
      · rw [members_extend_ne E r0 _ r hr] at h
        exact body_plain hE r m b h hb
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, r, m, b, h, hb => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact NormRole.envCtx_fresh hE r hfresh
      · rw [members_extend_ne E r0 _ r hr] at h
        exact body_plain hE r m b h hb
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem,
      r, m, b, h, hb => by
      rcases groupMembersT_cases hmem r m h with hold | hnew
      · exact (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r
          (dom_of_members hold)).trans (body_plain hE r m b hold hb)
      · rw [groupMembersT_body_none hmem r m hnew] at hb
        cases hb

/-- The metadata of the declaration is unchanged; the role equation is
supplied by the new canonical context, not by the raw-role invariant. -/
theorem body_eq_of_faithful (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E)
    (r : Nat) (m : CheckedMember) (b : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = some b)
    (htr : transparent m.mclass = true)
    (σ : Nat → Nat) (ls : List Level) (ρ : Nat → PSet.{4}) :
    Equiv (μ r (ls.map (evalTotal σ)))
      (den (mkM P μ) σ ρ (instantiateLevels ls b)) := by
  obtain ⟨hc, _ha, _hr, hcl, hlvl⟩ :=
    EvalRoleDelta.transparent_body_data hW r m b hm hb htr
  have hrole : ctx r = .plain :=
    (hctx r (dom_of_members hm)).trans (body_plain hW r m b hm hb)
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

theorem bodyEquations_of_faithful (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hW r)
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) E σ := by
  intro r ls b hw ρ
  obtain ⟨m, body, hm, htr, hb, he⟩ := transparentBody_some hw
  rw [he]
  exact body_eq_of_faithful P μ ctx plans hW hctx hF r m body hm hb htr σ ls ρ

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
theorem bodyEquations_at_node (P : Premises4)
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
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E')
    (node : RecNode E E' f rr rm) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) node.E0 σ := by
  have hctx0 : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hF0 : EvalRole.Faithful RawFamily.role P μ ctx plans E := fun r m hm vs =>
    hF r m (groupMembersT_preserve hmem r m hm) vs
  exact EvalRoleDelta.bodyEquations_extension P μ node.base
    (node_new_bodyless hmem node) σ
    (bodyEquations_of_faithful P μ ctx plans hE hctx0 hF0 σ)

/-- The same produced equations survive any fresh-family candidate update;
no soundness or admissibility of the new entry is assumed. -/
theorem bodyEquations_update_at_node (P : Premises4)
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
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans E')
    (node : RecNode E E' f rr rm) (X : List Nat → PSet.{4}) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P (upd μ f X)) node.E0 σ := by
  have hfresh : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hctx0 : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hF0 : EvalRole.Faithful RawFamily.role P μ ctx plans E := fun r m hm vs =>
    hF r m (groupMembersT_preserve hmem r m hm) vs
  exact EvalRoleDelta.bodyEquations_extension P _ node.base
    (node_new_bodyless hmem node) σ
    (EvalRoleDelta.bodyEquations_transfer P hE (agreeOn_upd hfresh μ X) σ
      (bodyEquations_of_faithful P μ ctx plans hE hctx0 hF0 σ))

end Rcic.F3.PSet.NormRoleDelta
