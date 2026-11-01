import rcic.RcicF3NormRole
import rcic.RcicF3EvalRoleReads

/-!
# Produced read support for the normalized canonical family roles

The normalized constructor fields are read from the actual admitted plan.
Their original types read the family-only prefix, and every transparent
body used by their reader comes from the closed predecessor environment.
Thus normalization retains the exact permitted family read set, including
literal zero/successor aliases and the family's own reference.

The resulting context read theorem applies to every admitted environment.
The unchanged indexed-evaluation plans contribute their already produced
support through EvalRole.readsOKAlong_of_plan_agree. No semantic read,
normalization, soundness or closure callback is assumed. These are read
facts for the distinct normalized interpretation, not an equivalence with
the existing raw-role invariant. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormRole
open Rcic.Declarative Rcic.Model.PS PropEval PiValueRule

/-- Every body observed in the actual reader prefix is an inherited
predecessor body. New members of the group have no delta bodies. -/
theorem bodies_read_in_base {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    ∀ r m b ls, node.E0.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads (Dom E) (instantiateLevels ls b) := by
  intro r m b ls hm hb htr
  have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
  rcases groupMembersT_cases hmem r m hfinal with hold | hnew
  · exact EvalPlanScope.closed_reads
      (bodiesClosed_of_envWfT hE r m hold b htr hb ls)
  · rw [groupMembersT_body_none hmem r m hnew] at hb
    cases hb

/-- The actual cached reader preserves the support of an original field.
Both its normalized domains and complete terminal argument list are kept. -/
theorem field_reads {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b))
    {fuel f nu np ni prior : Nat} {A : Expr Nat} {s : FieldShape}
    (p : EvalPlan.Field E fuel f nu np ni prior A s)
    (hA : ExprReads S A) :
    ExprReads S (fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec p)) := by
  cases p with
  | plain => exact hA
  | recursive r =>
      have hread := EvalPlanScope.telescope_reads hbodies fuel A r.domains
        (foldApps (.const f (canonL nu)) r.arguments) r.read hA
      have hpi : ∀ ds : List (Expr Nat), RefsIn S ds →
          ExprReads S (policyPi ds (foldApps (.const f (canonL nu)) r.arguments)) := by
        intro ds
        induction ds with
        | nil => exact fun _ => hread.2
        | cons D ds ih =>
            intro hd q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hd D (List.mem_cons_self _ _) q hq
            · exact ih (fun e he => hd e (List.mem_cons_of_mem _ he)) q hq
      exact hpi r.domains hread.1

/-- Field order and binder scopes are unchanged by the normalized cache. -/
theorem fields_reads {E : ResolvedEnv} {S : Nat → Prop}
    (hbodies : ∀ r m b ls, E.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b))
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hFs : RefsIn S Fs) :
    RefsIn S ((EvalPlanNormal.specs p).map (fieldExpr f (canonL nu))) := by
  revert hFs
  induction p with
  | nil => exact fun _ _ he => (List.not_mem_nil _ he).elim
  | @cons prior s A ss Fs head tail ih =>
      intro hFs e he
      change e ∈ fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec head) ::
        (EvalPlanNormal.specs tail).map (fieldExpr f (canonL nu)) at he
      rcases List.mem_cons.mp he with rfl | he
      · exact field_reads hbodies head (hFs A (List.mem_cons_self _ _))
      · exact ih (fun B hB => hFs B (List.mem_cons_of_mem _ hB)) e he

/-- Actual group admission supplies all reads of the normalized family
descriptor before that family is installed. Only recursive field reads
may include the family's own reference. -/
theorem famReads_normal (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => p.f + 1 + i))
    (hrr : p.rr = p.f + 1 + ctors.length) :
    RefsIn (Dom p.E) ((EvalPlanNormal.fd p).params ++ (EvalPlanNormal.fd p).indices) ∧
      FamRefsIn (fun r => Dom p.E r ∨ r = (EvalPlanNormal.fd p).fref)
        (EvalPlanNormal.fd p) := by
  let S := fun r => Dom p.E r ∨ r = (EvalPlanNormal.fd p).fref
  have hraw := famReads_node hmem hL hrr p.node
  have hbodies : ∀ r m b ls, p.node.E0.members r = some m → m.body = some b →
      transparent m.mclass = true → ExprReads S (instantiateLevels ls b) := by
    intro r m b ls hm hb htr r' hr'
    exact Or.inl (bodies_read_in_base hE hmem p.node r m b ls hm hb htr r' hr')
  refine ⟨hraw.1, ?_⟩
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  change RefsIn S ((EvalPlanNormal.fd p).ctors.get ⟨j, hj⟩).1 ∧
    RefsIn S ((EvalPlanNormal.fd p).ctors.get ⟨j, hj⟩).2
  rw [EvalPlanNormal.ctor_get]
  let i := EvalPlanNormal.index p ⟨j, hj⟩
  have hcraw := hraw.2
    ((p.node.a.constructorViews i).fields, (p.node.a.constructorViews i).resultIndices)
    (List.getElem?_mem (famDataOf_ctor p.node.a i))
  exact ⟨fields_reads hbodies (p.constructors i).fields hcraw.1, hcraw.2⟩

/-- Every member's normalized canonical role reads only the preceding
environment. Context agreement carries no semantic support premise. -/
theorem readsOKAlong_envCtxT : {E : ResolvedEnv} → (hW : EnvWfT E) →
    ∀ ctx : Nat → Role,
      (∀ r, Dom E r → ctx r = envCtx hW r) → PSet.ReadsOKAlong ctx hW
  | _, .empty, _, _ => True.intro
  | _, .axiom E r A _ hE hfresh hA _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx
        (fun r' hr => hctx r' (dom_extend hfresh r' hr)), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_fresh hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb => by cases hb⟩
  | _, .definition E r A v _ hE hfresh hA hv _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx
        (fun r' hr => hctx r' (dom_extend hfresh r' hr)), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_fresh hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h,
        fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .thm E r A v hE hfresh hA hv _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx
        (fun r' hr => hctx r' (dom_extend hfresh r' hr)), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_fresh hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h,
        fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .opaque E r A v _ hE hfresh hA hv _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx
        (fun r' hr => hctx r' (dom_extend hfresh r' hr)), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_fresh hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h,
        fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, ctx, hctx => by
      obtain ⟨hL, hrr⟩ :=
        group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
      refine ⟨readsOKAlong_envCtxT hE ctx
        (fun r hr => (hctx r (dom_groupMembersT hmem hr)).trans
          (envCtx_group_stable hE hfam hctors hrec hmem r hr)), ?_⟩
      refine groupReadsOK_of ctx hmem (fun _ h => h) fun c hc fd hcf => ?_
      have hd : Dom E' c.1 := dom_of_members (groupMembersT_installed hmem hc)
      rw [hctx c.1 hd, envCtx_group] at hcf
      obtain ⟨_, rfl⟩ := groupRoles_fam hcf
        (envCtx_fresh hE c.1 (groupMembersT_fresh_base hmem c.1 c.2 hc))
      exact famReads_normal (EvalPlan.ofGroup hE hfam hctors hrec hmem)
        fm ctors hE hmem hL hrr

/-- The original admitted plan table contributes its produced endpoint
support to the new normalized context's member reads. -/
theorem planReadsOKAlong {E : ResolvedEnv} (hW : EnvWfT E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hW r) :
    EvalRole.ReadsOKAlong ctx plans hW :=
  EvalRole.readsOKAlong_of_plan_agree hW ctx plans hplans
    (readsOKAlong_envCtxT hW ctx hctx)

end Rcic.F3.PSet.NormRole
