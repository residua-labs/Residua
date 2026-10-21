import rcic.RcicNativeTypedModelCovPStrict

/-!
# Preserve concrete hereditary witnesses in the strict measurement

Strictness is checked at the fixed finite type code. The proof then
transports every exact type observation to the restricted model, recursively.
This is a model change at the same code, not code-order construction.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKAudit TypedModelCovYAudit TypedModelCovZAudit

theorem hereditaryCovRealizationPAt_strict {E : ResolvedEnv}
    (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (hs : CovPStrictCompact E a)
    (h : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      R n Γ ρ A c a) :
    HereditaryCovRealizationPAt T Rel (ctxModelT_approxTKStrictP E n)
      R n Γ ρ A c a := by
  rw [HereditaryCovRealizationPAt.eq_def] at h ⊢
  refine ⟨h.1, ?_⟩
  cases a with
  | pi d g =>
      rw [CovPStrictCompact] at hs
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, hc, ?_⟩
        intro ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
        obtain ⟨hd, hB, hL, hR⟩ := ha ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
        have hrowS := (hs.2 row hrow).2
        exact ⟨fun u hu => hereditaryCovRealizationPAt_strict T Rel R n Γ ρ D u d
            hs.1 (hd u hu),
          hereditaryCovRealizationPAt_strict T Rel R n _ _ _ _ row.2 hrowS hB,
          hereditaryCovRealizationPAt_strict T Rel R n _ _ _ _ row.2 hrowS hL,
          hereditaryCovRealizationPAt_strict T Rel R n _ _ _ _ row.2 hrowS hR⟩
  | bot => trivial
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, hn, ho⟩
      · exact Or.inl hb
      · exact Or.inr ⟨A₀, hr, hn, ho, hs⟩
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

theorem hereditaryCovRealizationYAt_strict (C : CovTyping E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (hs : CovPStrictCompact E a)
    (h : HereditaryCovRealizationYAt C (ctxModelT_approxTK E n) R n Γ ρ A c a) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTKStrictP E n) R n Γ ρ A c a :=
  hereditaryCovRealizationYAt_of_P C (ctxModelT_approxTKStrictP E n) R n Γ ρ A c a
    (hereditaryCovRealizationPAt_strict C.ty (LRSCoreCovY C R n) R n Γ ρ A c a hs
      (hereditaryCovRealizationPAt_of_Y C (ctxModelT_approxTK E n) R n Γ ρ A c a h))

theorem covP_strict_joint_of_code (C : CovTyping E) (R : Readback)
    (n : Nat) (Γ : LCtx) (ρ ρ' : EnvT) (x y A : Expr Nat) (c a : CptT)
    (hs : CovPStrictCompact E a)
    (h : CovZJointCodeAt C (ctxModelT_approxTK E n) R n Γ ρ ρ' x y A c a) :
    CovZJointCodeAt C (ctxModelT_approxTKStrictP E n) R n Γ ρ ρ' x y A c a :=
  ⟨h.1, hereditaryCovRealizationYAt_strict C R n Γ ρ A c a hs h.2.1,
    hereditaryCovRealizationYAt_strict C R n Γ ρ' A c a hs h.2.2⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_REALIZATION_ROOTS
#print axioms hereditaryCovRealizationPAt_strict
#print axioms hereditaryCovRealizationYAt_strict
#print axioms covP_strict_joint_of_code
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
