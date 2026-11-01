import rcic.RcicF3EvalRole
import rcic.RcicF3StepDGOrder

/-!
# Produced read support for the canonical indexed-evaluation plan table

Every admitted group supplies its complete endpoint read certificate. Its
plan is installed only at the last recursor member, after all references
in the actual reader environment have been installed. Earlier groups'
plans are preserved, and references outside the environment have no plan.

The final theorem composes these plan facts with the existing unconditional
stored-type read theorem. No semantic read callback or PlanReady premise
remains in the canonical installation interface. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalRole
open Rcic.Declarative Rcic.Model.PS

/-- A canonical plan can occur only at an installed reference. -/
theorem envPlan_none : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ r, E.members r = none → envPlan hW r = none
  | _, .empty, _, _ => rfl
  | _, .axiom _ _ _ _ hE _ _ _ _, r, h =>
      envPlan_none hE r (extendEnv_ne_none h).2
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envPlan_none hE r (extendEnv_ne_none h).2
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envPlan_none hE r (extendEnv_ne_none h).2
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, r, h =>
      envPlan_none hE r (extendEnv_ne_none h).2
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, h => by
      have hrr : E'.members rr = some rm := groupMembersT_installed hmem
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self _ _)))
      have hne : r ≠ rr := by
        intro he
        rw [he, hrr] at h
        cases h
      change (if r = rr then some (EvalPlan.ofGroup hE hfam hctors hrec hmem)
        else envPlan hE r) = none
      rw [if_neg hne]
      exact envPlan_none hE r (groupMembersT_none hmem h)

/-- Installing a group's new recursor preserves every earlier member's plan. -/
theorem envPlan_group_stable {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') (r : Nat) (hr : Dom E r) :
    envPlan (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r =
      envPlan hE r := by
  have hfresh : E.members rr = none := groupMembersT_fresh_base hmem rr rm
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self _ _)))
  have hne : r ≠ rr := by
    intro he
    unfold Dom at hr
    rw [he, hfresh] at hr
    cases hr
  exact if_neg hne

/-- The actual admitted group pays readiness for every model and valuation. -/
theorem planReady_ofGroup {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    PlanReady (EvalPlan.ofGroup hE hfam hctors hrec hmem) := by
  intro P μ σ
  exact EvalPlanScope.endpointReads_of_group
    (EvalPlanValue.context (EvalPlan.ofGroup hE hfam hctors hrec hmem)
      (mkM P μ) σ ρ0) fm ctors hE hfam hctors hrec hmem

private theorem groupReadsOK_append_last {S E' : ResolvedEnv}
    (ctx : Nat → Role) (plans : Plans) (rr : Nat) (rm : CheckedMember) :
    ∀ pre : List (Nat × CheckedMember), ∀ {E : ResolvedEnv}
      (hmem : GroupMembersT S E (pre ++ [(rr, rm)]) E'),
      PSet.GroupReadsOK ctx hmem →
      (∀ r m, (r, m) ∈ pre ++ [(rr, rm)] → r ≠ rr → plans r = none) →
      (∀ Epre, E' = extendEnv Epre rr rm → PlanReadsIn (Dom Epre) (plans rr)) →
      GroupReadsOK ctx plans hmem := by
  intro pre
  induction pre with
  | nil =>
      intro E hmem hstored _ hlast
      cases hmem with
      | cons E r m rest E' hfresh hnobody hcl harity hlvl hcanon harities
          hadm hidx u hT hTc htyped hrest =>
          cases hrest
          exact ⟨⟨hstored.1, hlast E rfl⟩, True.intro⟩
  | cons c pre ih =>
      intro E hmem hstored hnone hlast
      cases hmem with
      | cons E r m rest E' hfresh hnobody hcl harity hlvl hcanon harities
          hadm hidx u hT hTc htyped hrest =>
          have hmissing := groupMembersT_fresh_base hrest rr rm
            (List.mem_append_right _ (List.mem_cons_self _ _))
          have hne : r ≠ rr := by
            intro he
            rw [← he, members_extend_eq] at hmissing
            cases hmissing
          have hn := hnone r m (List.mem_cons_self _ _) hne
          refine ⟨⟨hstored.1, ?_⟩, ?_⟩
          · rw [hn]
            exact True.intro
          · exact ih hrest hstored.2
              (fun r' m' hm' hne' => hnone r' m'
                (List.mem_cons_of_mem _ hm') hne') hlast

/-- Attach the produced plan support to any stored-type read derivation.
The only table condition says that installed plans are the actual canonical
plans; it supplies no read, normalization or evaluation fact. -/
theorem readsOKAlong_of_plan_agree : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ (ctx : Nat → Role) (plans : Plans),
      (∀ r, Dom E r → plans r = envPlan hW r) →
      PSet.ReadsOKAlong ctx hW → ReadsOKAlong ctx plans hW
  | _, .empty, _, _, _, _ => True.intro
  | _, .axiom E r A u hE hfresh hA hcl hlvl, ctx, plans, hp, hs => by
      refine ⟨readsOKAlong_of_plan_agree hE ctx plans
        (fun r' hr => hp r' (dom_extend hfresh r' hr)) hs.1, hs.2, ?_⟩
      rw [hp r dom_self, envPlan, envPlan_none hE r hfresh]
      exact True.intro
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv,
      ctx, plans, hp, hs => by
      refine ⟨readsOKAlong_of_plan_agree hE ctx plans
        (fun r' hr => hp r' (dom_extend hfresh r' hr)) hs.1, hs.2, ?_⟩
      rw [hp r dom_self, envPlan, envPlan_none hE r hfresh]
      exact True.intro
  | _, .thm E r A p hE hfresh hA hP hclA hclP hlvlA hlvlP,
      ctx, plans, hp, hs => by
      refine ⟨readsOKAlong_of_plan_agree hE ctx plans
        (fun r' hr => hp r' (dom_extend hfresh r' hr)) hs.1, hs.2, ?_⟩
      rw [hp r dom_self, envPlan, envPlan_none hE r hfresh]
      exact True.intro
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv,
      ctx, plans, hp, hs => by
      refine ⟨readsOKAlong_of_plan_agree hE ctx plans
        (fun r' hr => hp r' (dom_extend hfresh r' hr)) hs.1, hs.2, ?_⟩
      rw [hp r dom_self, envPlan, envPlan_none hE r hfresh]
      exact True.intro
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem,
      ctx, plans, hp, hs => by
      refine ⟨readsOKAlong_of_plan_agree hE ctx plans
        (fun r hr => (hp r (dom_groupMembersT hmem hr)).trans
          (envPlan_group_stable hE hfam hctors hrec hmem r hr)) hs.1, ?_⟩
      apply groupReadsOK_append_last ctx plans rr rm ((f, fm) :: ctors) hmem hs.2
      · intro r m hin hne
        rw [hp r (dom_of_members (groupMembersT_installed hmem hin))]
        change (if r = rr then some (EvalPlan.ofGroup hE hfam hctors hrec hmem)
          else envPlan hE r) = none
        rw [if_neg hne]
        exact envPlan_none hE r (groupMembersT_fresh_base hmem r m hin)
      · intro Epre hlast
        have hrr : E'.members rr = some rm := groupMembersT_installed hmem
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self _ _)))
        rw [hp rr (dom_of_members hrr)]
        change PlanReadsIn (Dom Epre)
          (if rr = rr then some (EvalPlan.ofGroup hE hfam hctors hrec hmem)
            else envPlan hE rr)
        rw [if_pos rfl]
        refine ⟨planReady_ofGroup hE hfam hctors hrec hmem, ?_⟩
        intro r hr
        cases hm : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.E0.members r with
        | none =>
            unfold Dom at hr
            rw [hm] at hr
            cases hr
        | some m =>
            exact dom_of_members (EvalPlanScope.reader_sub_before_last
              (EvalPlan.ofGroup hE hfam hctors hrec hmem).node hlast r m hm)

/-- Canonical installation consumes only the actual admitted environment.
Both the stored types and the complete normalized evaluation plans read
inside the prefix preceding each installed member. -/
theorem readsOKAlong_envCtxT {E : ResolvedEnv} (hW : EnvWfT E) :
    ReadsOKAlong (envCtx hW) (envPlan hW) hW :=
  readsOKAlong_of_plan_agree hW (envCtx hW) (envPlan hW) (fun _ _ => rfl)
    (Rcic.F3.StepDGOrder.readsOKAlong_envCtxT hW (envCtx hW) (fun _ _ => rfl))

end Rcic.F3.PSet.EvalRole
