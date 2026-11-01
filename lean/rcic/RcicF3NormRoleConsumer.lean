import rcic.RcicF3NormRoleTable
import rcic.RcicF3StepWDApex

/-!
# Consumers of the actual normalized family and indexed endpoint

The singleton producer and admission fold retain the canonical normalized
role context and the actual admitted plan at every member. The finalizer
uses the produced faithful table. It needs neither a family-read hypothesis
nor an equality with the legacy invariant.

The fold still consumes its literal group-step input. This module supplies
no universal A or checked group producer. Its scope is the generic consumer
and finalizer, including every extension in the legacy iota conjunct.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRole
open Rcic.Declarative Rcic.Model.PS

/-- A definition, theorem or opaque declaration preserves the normalized
invariant using its actual bounded stored derivation. -/
theorem gInv_singleW (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} {hE : EnvWfT E} {r : Nat}
    {k : MemberClass} {A v : Expr Nat}
    (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none)
    (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true)
    (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (IH : GInv P K hE) (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' →
      ctx r' = envCtx hE r') (plans : EvalRole.Plans)
    (hplans : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' →
      plans r' = EvalRole.envPlan hE r')
    (μ : Nat → List Nat → PSet.{4})
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans
      (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ Efin, (∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' →
        Efin.members r' = some m') →
        ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' →
          m'.mclass = .recursorM → IotaAt P μ K Efin r' := by
  have hsub := members_extend_preserved (m := ⟨k, 0, A, some v⟩) hfresh
  have IHμ := IH ctx (fun r' h => hctx r' (dom_extend hfresh r' h))
    plans (fun r' h => hplans r' (dom_extend hfresh r' h)) μ
    (fun r' m' h => hF r' m' (hsub r' m' h))
  have hES : EnvSound (mkM P μ) (fun _ => 0) K E 0 :=
    envSound_of P (Efin := extendEnv E r ⟨k, 0, A, some v⟩) hsub IHμ.1
      (fun r' m' h hk' => IHμ.2 _ hsub r' m' h hk') _ 0
  have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_fresh hE r hfresh)
  have hval : Equiv (μ r []) (den (mkM P μ) (fun _ => 0) ρ0 v) := by
    have h := hF r _ (members_extend_eq E r _) []
    rw [hr] at h
    change Equiv (μ r []) (RoleModel.memberVal RawFamily.role P μ
      .plain ⟨k, 0, A, some v⟩ []) at h
    have e : RoleModel.memberVal RawFamily.role P μ
        .plain ⟨k, 0, A, some v⟩ [] = den (mkM P μ) (fun _ => 0) ρ0 v :=
      mem_memberVal_def hk A v []
    rw [e] at h
    exact h
  refine ⟨fun r' m' h => ?_, fun Efin hsubF r' m' h hk' => ?_⟩
  · by_cases hr' : r' = r
    · subst r'; rw [members_extend_eq] at h; cases h
      exact memberSound_singleton' hval hclA hclv hlvlA hlvlv hv hl hES
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.1 r' m' h
  · by_cases hr' : r' = r
    · subst r'; rw [members_extend_eq] at h; cases h
      rcases hk with rfl | rfl | rfl <;> cases hk'
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.2 Efin (fun r'' m'' hm => hsubF r'' m'' (hsub r'' m'' hm)) r' m' h hk'

structure GInvSteps (P : Premises4) (K : Nat → Nat) (Cl Bd : ∀ {E : ResolvedEnv}, EnvWfT E → Prop) : Prop where
  stepDef : ∀ (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclv : ∀ k, Rcic.Declarative.lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true),
      Cl (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Bd (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv))
  stepThm : ∀ (E : ResolvedEnv) (r : Nat) (A p : Expr Nat) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort .zero)) (hp : HasTyT E 0 [] p A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclp : ∀ k, Rcic.Declarative.lift k 1 p = p)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlp : exprLevelsBounded 0 p = true),
      Cl (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) →
      Bd (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp))
  stepOpq : ∀ (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclv : ∀ k, Rcic.Declarative.lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true),
      Cl (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Bd (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv))
  stepGrp : ∀ (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
      (rr : Nat) (rm : CheckedMember) (E' : ResolvedEnv) (hE : EnvWfT E)
      (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
      (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
      Cl (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
      Bd (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))

/-- The model invariant along a derivation, from the step hypotheses. The axiom arm is excluded by
`Cl` (`hax`). -/
theorem gInv_of_steps (P : Premises4) (K : Nat → Nat) (Cl Bd : ∀ {E : ResolvedEnv}, EnvWfT E → Prop)
    (S : GInvSteps P K Cl Bd)
    (hax : ∀ {arity : Nat} (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E arity [] A (.sort u)) (hcl : ∀ k, Rcic.Declarative.lift k 1 A = A)
      (hlvl : exprLevelsBounded arity A = true), ¬ Cl (EnvWfT.axiom E r A u hE hfresh hA hcl hlvl)) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Cl hW → Bd hW → GInv P K hW
  | _, .empty, _, _ => gInv_empty P K
  | _, .axiom E r A u hE hfresh hA hcl hlvl, hC, _ => (hax E r A u hE hfresh hA hcl hlvl hC).elim
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB =>
      let t := S.stepDef E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hC, hB =>
      let t := S.stepThm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB =>
      let t := S.stepOpq E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, hB =>
      let t := S.stepGrp E f fm ctors rr rm E' hE hfam hctors hrec hmem hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)

/-- The actual installed normalized table satisfies semantic soundness
whenever the new invariant is produced for this same admitted environment. -/
theorem envSound_of_gInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hI : GInv P K hW) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P hW)) σ K E n := by
  have hIv := hI (envCtx hW) (fun _ _ => rfl)
    (EvalRole.envPlan hW) (fun _ _ => rfl) _ (table_spec P hW).1
  exact envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) σ n

/-- The consistency finalizer uses the literal stored False recursor and
retains the bounded actual typing derivation. -/
theorem false_of_gInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) (hI : GInv P K hW)
    (h1 : E.members 1 = some falseRecMemberU) (n : Nat)
    (e : Expr Nat) (D : HasTyT E n [] e (.const 0 []))
    (hl : LOKt (fun _ => 0) 4 K D) : False := by
  have hIv := hI (envCtx hW) (fun _ _ => rfl)
    (EvalRole.envPlan hW) (fun _ _ => rfl) _ (table_spec P hW).1
  exact empty_of_falseRec P (hIv.1 1 _ h1)
    (sound_ty (P.good _ rfl) (envSound_of_gInv P K hW hI (fun _ => 0) n) D hl ρ0 trivial)

end Rcic.F3.PSet.NormRole
