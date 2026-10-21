import rcic.RcicNativeTypedModelCovYRealization

/-!
# Hereditary realization with an explicit compact-typing parameter

Changing `CovTyping.prop_bot` cannot produce an instance of the frozen
`CovTyping`. This new interface exposes just the typing relation and the
demand relation actually used by hereditary realization. The old native
judgments, compact actions, model and readback are imported unchanged.

No new recursive term relation is introduced: callers may supply the landed
CoreY payload. A theorem below identifies that specialization exactly with
the landed hereditary target. This is an interface for measuring the typing
change, not a new fundamental supplier. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovXAudit TypedModelCovYAudit

abbrev CovPDemandRelation :=
  LCtx → Expr Nat → Expr Nat → Expr Nat → CptT → CptT → Prop

def CovPSelectedRow (T : CptT → CptT → Prop) (ds : List CptT) (out : CptT)
    (row : List CptT × CptT) : Prop :=
  (∀ u ∈ row.1, u = .bot ∨ u ∈ ds) ∧ T out row.2

def CovPActionCoverage (E : ResolvedEnv) (T : CptT → CptT → Prop)
    (c d : CptT) (g : List (List CptT × CptT)) : Prop :=
  ∀ ds out, CovXCompactAction E c ds out → (∀ u ∈ ds, T u d) →
    out = .bot ∨ ∃ row ∈ g, CovPSelectedRow T ds out row

/-- The sole change to the hereditary clauses is that their typing and
demand-relation parameters need not carry the old proposition-collapse law.
All exact leaf observations and all three recursive result obligations stay.
-/
def HereditaryCovRealizationPAt {E : ResolvedEnv} (T : CptT → CptT → Prop)
    (Rel : CovPDemandRelation) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT) : Prop :=
  T c a ∧
  match a with
  | .bot => True
  | .pi d g =>
      c = .bot ∨ ∃ D B : Expr Nat, RedR R Γ A (.pi D B) ∧
        CovPActionCoverage E T c d g ∧
        ∀ ds out, CovXCompactAction E c ds out → out ≠ .bot →
        ∀ row, row ∈ g → CovPSelectedRow T ds out row →
        ∀ N N', HasTyT E n Γ N D → HasTyT E n Γ N' D →
        Nonempty (ConvT E n Γ N N' D) →
        (∀ u ∈ ds, Rel Γ N N' D u d) →
          (∀ u ∈ ds, HereditaryCovRealizationPAt T Rel Q R n Γ ρ D u d) ∧
          HereditaryCovRealizationPAt T Rel Q R n (.assumption D :: Γ)
            (EnvT.cons (demandT ds) ρ) B out row.2 ∧
          HereditaryCovRealizationPAt T Rel Q R n Γ ρ (instantiate0 N B) out row.2 ∧
          HereditaryCovRealizationPAt T Rel Q R n Γ ρ (instantiate0 N' B) out row.2
  | _ => c = .bot ∨ ∃ A₀, RedR R Γ A A₀ ∧ NormalR R Γ A₀ ∧ (Q Γ).Ap ρ A₀ a
termination_by sizeOf a
decreasing_by
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt ‹row ∈ g›

theorem hereditaryCovRealizationPAt_typing {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    {Q : LCtx → CtxModelT E} {R : Readback} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c a : CptT}
    (h : HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a) : T c a := by
  rw [HereditaryCovRealizationPAt.eq_def] at h
  exact h.1

theorem hereditaryCovRealizationPAt_bot {E : ResolvedEnv}
    (T : CptT → CptT → Prop) (hb : ∀ a, T .bot a) (Rel : CovPDemandRelation)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (a : CptT) :
    HereditaryCovRealizationPAt T Rel Q R n Γ ρ A .bot a := by
  rw [HereditaryCovRealizationPAt.eq_def]
  refine ⟨hb a, ?_⟩
  cases a <;> first | trivial | exact Or.inl rfl

theorem hereditaryCovRealizationPAt_of_Y (C : CovTyping E)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationYAt C Q R n Γ ρ A c a) :
    HereditaryCovRealizationPAt C.ty (LRSCoreCovY C R n) Q R n Γ ρ A c a := by
  rw [HereditaryCovRealizationYAt.eq_def] at h
  rw [HereditaryCovRealizationPAt.eq_def]
  refine ⟨h.1, ?_⟩
  cases a with
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, hc, ?_⟩
        intro ds out hact hnb row hrow hs N N' hN hN' hconv hrel
        obtain ⟨hd, hB, hL, hR⟩ := ha ds out hact hnb row hrow hs N N' hN hN' hconv hrel
        exact ⟨fun u hu => hereditaryCovRealizationPAt_of_Y C Q R n Γ ρ D u d (hd u hu),
          hereditaryCovRealizationPAt_of_Y C Q R n _ _ _ _ row.2 hB,
          hereditaryCovRealizationPAt_of_Y C Q R n _ _ _ _ row.2 hL,
          hereditaryCovRealizationPAt_of_Y C Q R n _ _ _ _ row.2 hR⟩
  | bot | prop | sort | lam g | spine r us => exact h.2
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

theorem hereditaryCovRealizationYAt_of_P (C : CovTyping E)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationPAt C.ty (LRSCoreCovY C R n) Q R n Γ ρ A c a) :
    HereditaryCovRealizationYAt C Q R n Γ ρ A c a := by
  rw [HereditaryCovRealizationPAt.eq_def] at h
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨h.1, ?_⟩
  cases a with
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, hc, ?_⟩
        intro ds out hact hnb row hrow hs N N' hN hN' hconv hrel
        obtain ⟨hd, hB, hL, hR⟩ := ha ds out hact hnb row hrow hs N N' hN hN' hconv hrel
        exact ⟨fun u hu => hereditaryCovRealizationYAt_of_P C Q R n Γ ρ D u d (hd u hu),
          hereditaryCovRealizationYAt_of_P C Q R n _ _ _ _ row.2 hB,
          hereditaryCovRealizationYAt_of_P C Q R n _ _ _ _ row.2 hL,
          hereditaryCovRealizationYAt_of_P C Q R n _ _ _ _ row.2 hR⟩
  | bot | prop | sort | lam g | spine r us => exact h.2
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

theorem hereditaryCovRealizationPAt_old_iff (C : CovTyping E)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT) :
    HereditaryCovRealizationPAt C.ty (LRSCoreCovY C R n) Q R n Γ ρ A c a ↔
    HereditaryCovRealizationYAt C Q R n Γ ρ A c a :=
  ⟨hereditaryCovRealizationYAt_of_P C Q R n Γ ρ A c a,
    hereditaryCovRealizationPAt_of_Y C Q R n Γ ρ A c a⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_REALIZATION_ROOTS
#print axioms CovPDemandRelation
#print axioms CovPSelectedRow
#print axioms CovPActionCoverage
#print axioms HereditaryCovRealizationPAt
#print axioms hereditaryCovRealizationPAt_typing
#print axioms hereditaryCovRealizationPAt_bot
#print axioms hereditaryCovRealizationPAt_of_Y
#print axioms hereditaryCovRealizationYAt_of_P
#print axioms hereditaryCovRealizationPAt_old_iff
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
