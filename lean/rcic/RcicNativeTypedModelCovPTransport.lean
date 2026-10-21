import rcic.RcicNativeTypedModelCovPRealization

/-!
# Transport across a change of compact typing at one fixed code

This is not a code order. The code and demand relation remain identical.
The condition is checked at the actual finite code used by each fixture.
It supplies forward typing everywhere, and reverse typing precisely where
the old coverage and selected-row premises need it. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovXAudit TypedModelCovYAudit

def CovPCodeTransport (T U : CptT → CptT → Prop) (a : CptT) : Prop :=
  (∀ c, T c a → U c a) ∧
  match a with
  | .pi d g =>
      (∀ c, U c d → T c d) ∧
      (∀ row ∈ g, ∀ c, U c row.2 → T c row.2) ∧
      CovPCodeTransport T U d ∧ ∀ row ∈ g, CovPCodeTransport T U row.2
  | _ => True
termination_by sizeOf a
decreasing_by
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt ‹row ∈ g›

theorem hereditaryCovRealizationPAt_transport {E : ResolvedEnv}
    (T U : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (ht : CovPCodeTransport T U a)
    (h : HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a) :
    HereditaryCovRealizationPAt U Rel Q R n Γ ρ A c a := by
  rw [CovPCodeTransport.eq_def] at ht
  rw [HereditaryCovRealizationPAt.eq_def] at h ⊢
  refine ⟨ht.1 c h.1, ?_⟩
  cases a with
  | pi d g =>
      obtain ⟨hdom, hout, htd, htg⟩ := ht.2
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, ?_, ?_⟩
        · intro ds out hact hd
          rcases hc ds out hact (fun u hu => hdom u (hd u hu)) with hb | ⟨row, hm, hs⟩
          · exact Or.inl hb
          · have htr := htg row hm
            rw [CovPCodeTransport.eq_def] at htr
            exact Or.inr ⟨row, hm, hs.1, htr.1 out hs.2⟩
        · intro ds out hact hnb row hrow hs N N' hN hN' hconv hrel
          have hs' : CovPSelectedRow T ds out row := ⟨hs.1, hout row hrow out hs.2⟩
          obtain ⟨hd, hB, hL, hR⟩ := ha ds out hact hnb row hrow hs' N N' hN hN' hconv hrel
          exact ⟨fun u hu => hereditaryCovRealizationPAt_transport T U Rel Q R n
              Γ ρ D u d htd (hd u hu),
            hereditaryCovRealizationPAt_transport T U Rel Q R n _ _ _ _ row.2
              (htg row hrow) hB,
            hereditaryCovRealizationPAt_transport T U Rel Q R n _ _ _ _ row.2
              (htg row hrow) hL,
            hereditaryCovRealizationPAt_transport T U Rel Q R n _ _ _ _ row.2
              (htg row hrow) hR⟩
  | bot | prop | sort | lam g | spine r us => exact h.2
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

/-- The native relation payload stays the landed one; only the hereditary
compact-typing interpretation changes. The compatibility premise is not
advertised as a supply until instantiated at a concrete fixture code. -/
theorem hereditaryCovRealizationPAt_from_Y (C : CovTyping E)
    (U : CptT → CptT → Prop) (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (hc : CovPCodeTransport C.ty U a)
    (h : HereditaryCovRealizationYAt C Q R n Γ ρ A c a) :
    HereditaryCovRealizationPAt U (LRSCoreCovY C R n) Q R n Γ ρ A c a :=
  hereditaryCovRealizationPAt_transport C.ty U (LRSCoreCovY C R n) Q R n Γ ρ A c a hc
    (hereditaryCovRealizationPAt_of_Y C Q R n Γ ρ A c a h)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_TRANSPORT_ROOTS
#print axioms CovPCodeTransport
#print axioms hereditaryCovRealizationPAt_transport
#print axioms hereditaryCovRealizationPAt_from_Y
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_TRANSPORT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
