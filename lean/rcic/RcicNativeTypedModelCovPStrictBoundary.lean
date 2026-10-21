import rcic.RcicNativeTypedModelCovPStrictRealization
import rcic.RcicNativeTypedModelCovPIdentity

/-!
# The strict observation filter leaves the abstract action boundary open

The strict model rejects the displayed application with a bottom type
argument, but the hereditary target still uses the landed compact-action
relation. Its head observation survives, and hereditary realization in the
restricted model implies realization in the landed model. Consequently the
all-code identity and NeutralBody obstructions survive this bounded model
change. This is a measured limitation, not a new strict-action semantics.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovYAudit
open TypedModelCovZMeasureAudit

/-- Inclusion of exact model observations transports the hereditary target.
Typing, demand relations, compact actions and readback remain fixed. -/
theorem hereditaryCovRealizationPAt_model_mono {E : ResolvedEnv}
    (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (Q Q' : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (hm : ∀ Γ ρ A a, (Q Γ).Ap ρ A a → (Q' Γ).Ap ρ A a)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a) :
    HereditaryCovRealizationPAt T Rel Q' R n Γ ρ A c a := by
  rw [HereditaryCovRealizationPAt.eq_def] at h ⊢
  refine ⟨h.1, ?_⟩
  cases a with
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, hc, ?_⟩
        intro ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
        obtain ⟨hd, hB, hL, hR⟩ := ha ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
        exact ⟨fun u hu => hereditaryCovRealizationPAt_model_mono
            T Rel Q Q' R n hm Γ ρ D u d (hd u hu),
          hereditaryCovRealizationPAt_model_mono T Rel Q Q' R n hm _ _ _ _ row.2 hB,
          hereditaryCovRealizationPAt_model_mono T Rel Q Q' R n hm _ _ _ _ row.2 hL,
          hereditaryCovRealizationPAt_model_mono T Rel Q Q' R n hm _ _ _ _ row.2 hR⟩
  | bot => trivial
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, hn, ho⟩
      · exact Or.inl hb
      · exact Or.inr ⟨A₀, hr, hn, hm Γ ρ A₀ _ ho⟩
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

theorem hereditaryCovRealizationPAt_strict_forget {E : ResolvedEnv}
    (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTKStrictP E n)
      R n Γ ρ A c a) :
    HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n) R n Γ ρ A c a :=
  hereditaryCovRealizationPAt_model_mono T Rel
    (ctxModelT_approxTKStrictP E n) (ctxModelT_approxTK E n) R n
    (fun _ _ _ _ h => h.1) Γ ρ A c a h

theorem covP_not_hereditary_strict_identity_spine {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationPAt T Rel (ctxModelT_approxTKStrictP E n)
      (WhStepCK2 E n) n Γ ρ cexPolyIdTy (.spine r us) a := by
  intro a h
  exact covP_not_hereditary_identity_spine hbot n Γ ρ r us a
    (hereditaryCovRealizationPAt_strict_forget T Rel (WhStepCK2 E n) n Γ ρ
      cexPolyIdTy (.spine r us) a h)

theorem covP_not_hereditary_strict_poly_result_spine {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationPAt T Rel (ctxModelT_approxTKStrictP E n)
      (WhStepCK2 E n) n Γ ρ (.pi (.sort (.succ .zero)) (.bvar 0))
      (.spine r us) a := by
  intro a h
  exact covP_not_hereditary_poly_result_spine hbot n Γ ρ r us a
    (hereditaryCovRealizationPAt_strict_forget T Rel (WhStepCK2 E n) n Γ ρ
      (.pi (.sort (.succ .zero)) (.bvar 0)) (.spine r us) a h)

theorem covP_strict_rigidId_head_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKStrictP covZRigidIdEnv n Γ ρ (.const 0 []) (.spine 0 []) := by
  refine ⟨covZRigidIdHead_observed n Γ ρ, ?_⟩
  simp [CovPStrictCompact]

/-- The strict head is still observed in the inhabited identity environment,
but no code realizes it while hereditary actions remain unchanged. -/
theorem covP_strict_identity_boundary_control
    (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    Nonempty (ConvT covZRigidIdEnv n [] (.const 0 []) (.const 0 []) cexPolyIdTy) ∧
    ApproxTKStrictP covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    (CptT.spine 0 []) ≠ .bot ∧
    ¬ ∃ b, HereditaryCovRealizationPAt T Rel (ctxModelT_approxTKStrictP covZRigidIdEnv n)
      (WhStepCK2 covZRigidIdEnv n) n [] EnvT.bot cexPolyIdTy (.spine 0 []) b :=
  ⟨⟨hasTyT_cexPolyId emptyEnv n⟩, ⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩,
    ⟨covZRigidIdHead_hasTy n []⟩, ⟨.refl _ _ _ (covZRigidIdHead_hasTy n [])⟩,
    covP_strict_rigidId_head_observed n [] EnvT.bot, CptT.noConfusion,
    fun ⟨b, hb⟩ => covP_not_hereditary_strict_identity_spine hbot n [] EnvT.bot 0 [] b hb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_BOUNDARY_ROOTS
#print axioms hereditaryCovRealizationPAt_model_mono
#print axioms hereditaryCovRealizationPAt_strict_forget
#print axioms covP_not_hereditary_strict_identity_spine
#print axioms covP_not_hereditary_strict_poly_result_spine
#print axioms covP_strict_rigidId_head_observed
#print axioms covP_strict_identity_boundary_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
