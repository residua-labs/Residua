import rcic.RcicF3EvalRoleReads
import rcic.RcicF3DeltaNormalize

/-!
# Transparent-body equations at faithful indexed-evaluation tables

An admitted transparent member is a definition with a closed, level-free
body. Its canonical role is plain, so the new recursor plans do not change
its equation. The proof below uses faithfulness at every level vector;
it does not obtain global typing soundness from a bounded invariant.

The equations also survive a table update fresh for the predecessor and
an extension adding only bodyless members. These are the tables and reader
environments used by the normalized family construction.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalRoleDelta

open Rcic.Declarative
open Rcic.Model.PS (denRefs groupMembersT_preserve)
open Rcic.F3.StepDGOrder

/-- All metadata used by delta comes from the admitted declaration itself.
In particular no numerical valuation bound is needed for these facts. -/
theorem transparent_body_data :
    {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E.members r = some m → m.body = some b →
      transparent m.mclass = true →
        m.mclass = .definitionM ∧ m.arity = 0 ∧
        envCtx hW r = .plain ∧
        (∀ k, Rcic.Declarative.lift k 1 b = b) ∧
        exprLevelsBounded 0 b = true
  | _, .empty, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE _ _ _ _, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_body_data hE r m b h hb htr
  | _, .definition E r0 _ _ _ hE hfresh _ _ _ hclb _ hlvlb,
      r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
        exact ⟨rfl, rfl, envCtx_freshT hE r hfresh, hclb, hlvlb⟩
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_body_data hE r m b h hb htr
  | _, .thm E r0 _ _ hE _ _ _ _ _ _ _, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_body_data hE r m b h hb htr
  | _, .opaque E r0 _ _ _ hE _ _ _ _ _ _ _, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_body_data hE r m b h hb htr
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem,
      r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with hold | hnew
      · obtain ⟨hc, ha, hr, hcl, hlvl⟩ :=
          transparent_body_data hE r m b hold hb htr
        obtain ⟨hL, hrr⟩ :=
          group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
        exact ⟨hc, ha,
          (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r
            (dom_of_members hold)).trans hr, hcl, hlvl⟩
      · rw [groupMembersT_body_none hmem r m hnew] at hb
        cases hb

/-- Faithfulness pays every level-instance equation of an admitted
transparent body, including lists whose length differs from its arity.
The interpretation of a definition ignores that list, and its body has no
level parameters or free local variables. -/
theorem body_eq_of_faithful (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hF : EvalRole.Faithful F P μ ctx plans E)
    (r : Nat) (m : CheckedMember) (b : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = some b)
    (htr : transparent m.mclass = true)
    (σ : Nat → Nat) (ls : List Level) (ρ : Nat → PSet.{4}) :
    Equiv (μ r (ls.map (evalTotal σ)))
      (den (mkM P μ) σ ρ (instantiateLevels ls b)) := by
  obtain ⟨hc, _ha, hr, hcl, hlvl⟩ := transparent_body_data hW r m b hm hb htr
  have hrole : ctx r = .plain := (hctx r (dom_of_members hm)).trans hr
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

/-- The literal input required by unbounded inhabited normalization is
produced from the new role's faithfulness and actual canonical roles. -/
theorem bodyEquations_of_faithful (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hF : EvalRole.Faithful F P μ ctx plans E) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P μ) E σ := by
  intro r ls b hw ρ
  obtain ⟨m, body, hm, htr, hb, he⟩ := transparentBody_some hw
  rw [he]
  exact body_eq_of_faithful F P μ ctx plans hW hctx hF r m body hm hb htr σ ls ρ

/-- Exact body equations are invariant under agreement on the actual
predecessor. Body read support includes the implicit literal references. -/
theorem bodyEquations_transfer (P : Premises4)
    {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    (hW : EnvWfT E) (hag : AgreeOn μ₁ μ₂ (Dom E)) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations (mkM P μ₁) E σ) :
    DeltaNormalize.BodyEquations (mkM P μ₂) E σ := by
  intro r ls b hw ρ
  obtain ⟨m, body, hm, htr, hb, he⟩ := transparentBody_some hw
  have hreads : ∀ s, s ∈ denRefs b → Dom E s := by
    rw [he]
    exact EvalPlanScope.closed_reads (bodiesClosed_of_envWfT hW r m hm body htr hb ls)
  change Equiv (μ₂ r (ls.map (evalTotal σ))) (den (mkM P μ₂) σ ρ b)
  rw [← hag r (dom_of_members hm) (ls.map (evalTotal σ)),
    ← den_agreeOn P hag σ b hreads ρ]
  exact hδ r ls b hw ρ

/-- The reader may add bodyless declarations; every successful delta lookup
is still exactly a lookup in the predecessor. -/
theorem bodyEquations_extension (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) {E Ex : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → Ex.members r = some m)
    (hnew : ∀ r m, Ex.members r = some m → E.members r = none → m.body = none)
    (σ : Nat → Nat) (hδ : DeltaNormalize.BodyEquations (mkM P μ) E σ) :
    DeltaNormalize.BodyEquations (mkM P μ) Ex σ := by
  intro r ls b hw ρ
  exact hδ r ls b ((transparentBody_eq_of_sub hsub hnew r ls).trans hw) ρ

/-- The actual fresh-family update and a bodyless reader extension retain
all delta equations. No assumption is made about the new table entry. -/
theorem bodyEquations_fresh_extension (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E Ex : ResolvedEnv} (hW : EnvWfT E)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hF : EvalRole.Faithful F P μ ctx plans E)
    {f : Nat} (hfresh : E.members f = none) (X : List Nat → PSet.{4})
    (hsub : ∀ r m, E.members r = some m → Ex.members r = some m)
    (hnew : ∀ r m, Ex.members r = some m → E.members r = none → m.body = none)
    (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P (upd μ f X)) Ex σ := by
  exact bodyEquations_extension P _ hsub hnew σ
    (bodyEquations_transfer P hW (agreeOn_upd hfresh μ X) σ
      (bodyEquations_of_faithful F P μ ctx plans hW hctx hF σ))

/-- At an actual admitted recursor reader, all predecessor roles and bodies
are inherited. This composes the group layout, faithfulness and fresh
family update without a separate delta/read premise. -/
theorem bodyEquations_at_node (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hctx : ∀ r, Dom E' r →
      ctx r = envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hF : EvalRole.Faithful F P μ ctx plans E')
    (node : RecNode E E' f rr rm) (X : List Nat → PSet.{4}) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P (upd μ f X)) node.E0 σ := by
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hfresh : E.members f = none := (group_refs hmem hL hrr).1
  have hctx0 : ∀ r, Dom E r → ctx r = envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r hr)
  have hF0 : EvalRole.Faithful F P μ ctx plans E := fun r m hm vs =>
    hF r m (groupMembersT_preserve hmem r m hm) vs
  have hnew : ∀ r m, node.E0.members r = some m → E.members r = none →
      m.body = none := by
    intro r m hm hnone
    have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
    rcases groupMembersT_cases hmem r m hfinal with hold | hnew
    · rw [hold] at hnone
      cases hnone
    · exact groupMembersT_body_none hmem r m hnew
  exact bodyEquations_fresh_extension F P μ ctx plans hE hctx0 hF0
    hfresh X node.base hnew σ

end Rcic.F3.PSet.EvalRoleDelta
