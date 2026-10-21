import rcic.RcicNativeTypedModelCovQTower
import rcic.RcicNativeTypedModelCovPRealization

/-!
# Selecting finite result rows after native instantiation

This is a deliberately weaker measurement of the hereditary interface.
Native arguments precede existential row selection; the binder-body
obligation is omitted. Exact non-Pi leaves are composed from the landed
P predicate. The recursive measure remains the finite type code.

The generic finite-descent theorem is instantiated below, so failure here
cannot be blamed only on choosing a row before the native instance or on
the erased binder environment. No replacement fundamental theorem is claimed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit ReadbackCK2Audit
open TypedModelCovRelAudit TypedModelCovXAudit TypedModelCovYAudit
open TypedModelCovPAudit TypedModelCovZMeasureAudit

def HereditaryCovRealizationQAt {E : ResolvedEnv} (T : CptT → CptT → Prop)
    (Rel : CovPDemandRelation) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT) : Prop :=
  match a with
  | .pi d g => T c (.pi d g) ∧
      (c = .bot ∨ ∃ D B : Expr Nat, RedR R Γ A (.pi D B) ∧
        ∀ ds out, CovXCompactAction E c ds out → out ≠ .bot →
        (∀ u ∈ ds, T u d) →
        ∀ N N', HasTyT E n Γ N D → HasTyT E n Γ N' D →
        Nonempty (ConvT E n Γ N N' D) →
        (∀ u ∈ ds, Rel Γ N N' D u d) →
        ∃ row, ∃ (_hrow : row ∈ g), CovPSelectedRow T ds out row ∧
          (∀ u ∈ ds, HereditaryCovRealizationQAt T Rel Q R n Γ ρ D u d) ∧
          HereditaryCovRealizationQAt T Rel Q R n Γ ρ
            (instantiate0 N B) out row.2 ∧
          HereditaryCovRealizationQAt T Rel Q R n Γ ρ
            (instantiate0 N' B) out row.2)
  | _ => HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a
termination_by sizeOf a
decreasing_by
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt ‹row ∈ g›

theorem hereditaryCovRealizationQAt_typing {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    {Q : LCtx → CtxModelT E} {R : Readback} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c a : CptT}
    (h : HereditaryCovRealizationQAt T Rel Q R n Γ ρ A c a) : T c a := by
  rw [HereditaryCovRealizationQAt.eq_def] at h
  cases a with
  | pi d g => exact h.1
  | bot | prop | sort | lam g | spine r us =>
      exact hereditaryCovRealizationPAt_typing h

/-- This implication checks the weakening against the actual old clauses.
The backward premise uses the actual demand relation, not a code order or
an unconditional reverse inclusion between the two compact typings. -/
theorem hereditaryCovRealizationQAt_from_P {E : ResolvedEnv}
    (T U : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (hmap : ∀ c a, T c a → U c a)
    (hdemand : ∀ Γ N N' D u d, U u d → Rel Γ N N' D u d → T u d)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a) :
    HereditaryCovRealizationQAt U Rel Q R n Γ ρ A c a := by
  rw [HereditaryCovRealizationPAt.eq_def] at h
  rw [HereditaryCovRealizationQAt.eq_def]
  cases a with
  | pi d g =>
      refine ⟨hmap _ _ h.1, ?_⟩
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, ?_⟩
        intro ds out hact hnb htyped N N' hN hN' hconv hrel
        have htypedT : ∀ u ∈ ds, T u d :=
          fun u hu => hdemand Γ N N' D u d (htyped u hu) (hrel u hu)
        rcases hc ds out hact htypedT with hz | ⟨row, hrow, hsel⟩
        · exact (hnb hz).elim
        · obtain ⟨hd, _, hL, hR⟩ :=
            ha ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
          refine ⟨row, hrow, ⟨hsel.1, hmap _ _ hsel.2⟩, ?_, ?_, ?_⟩
          · intro u hu
            exact hereditaryCovRealizationQAt_from_P T U Rel hmap hdemand
              Q R n Γ ρ D u d (hd u hu)
          · exact hereditaryCovRealizationQAt_from_P T U Rel hmap hdemand
              Q R n Γ ρ _ out row.2 hL
          · exact hereditaryCovRealizationQAt_from_P T U Rel hmap hdemand
              Q R n Γ ρ _ out row.2 hR
  | bot | prop | sort | lam g | spine r us =>
      rw [HereditaryCovRealizationPAt.eq_def]
      exact ⟨hmap _ _ h.1, h.2⟩
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals subst a
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt hrow

theorem hereditaryCovRealizationQAt_of_P {E : ResolvedEnv}
    (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c a : CptT)
    (h : HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c a) :
    HereditaryCovRealizationQAt T Rel Q R n Γ ρ A c a :=
  hereditaryCovRealizationQAt_from_P T T Rel (fun _ _ ht => ht)
    (fun _ _ _ _ _ _ ht _ => ht) Q R n Γ ρ A c a h

theorem covQ_hereditary_pi_code {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {D B : Expr Nat} {c a : CptT}
    (hc : c ≠ .bot)
    (h : HereditaryCovRealizationQAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi D B) c a) :
    ∃ d g, a = .pi d g := by
  rw [HereditaryCovRealizationQAt.eq_def] at h
  cases a with
  | pi d g => exact ⟨d, g, rfl⟩
  | bot | prop | sort | lam g | spine r us =>
      exact covP_hereditary_pi_code hbot n hc h

/-- The actual instance-first interface supplies a smaller result code
after every inhabited native empty-demand application. -/
theorem covQ_hereditary_emptyStep {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    CovQEmptyStep E n Γ
      (fun A c a => HereditaryCovRealizationQAt T Rel (ctxModelT_approxTK E n)
        (WhStepCK2 E n) n Γ ρ A c a) := by
  intro D B r us a h N hN
  obtain ⟨d, g, rfl⟩ := covQ_hereditary_pi_code hbot n
    (fun he => CptT.noConfusion he) h
  rw [HereditaryCovRealizationQAt.eq_def] at h
  rcases h.2 with hz | ⟨D', B', hr, ha⟩
  · exact CptT.noConfusion hz
  · have he := redR_of_normal (normalR_piCK2 Γ D B) hr
    obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
    have hact : CovXCompactAction E (.spine r us) []
        (.spine r (us ++ [.bot])) := AppCptT.appSpine (.bot _ _)
    obtain ⟨row, hrow, _, _, hL, _⟩ :=
      ha [] _ hact (fun he => CptT.noConfusion he)
        (fun u hu => (List.not_mem_nil u hu).elim)
        N N hN hN ⟨.refl _ _ _ hN⟩
        (fun u hu => (List.not_mem_nil u hu).elim)
    exact ⟨row.2, covY_sizeOf_selected_codomain_lt hrow, hL⟩

theorem covQ_instance_first_identity_no_code {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationQAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ cexPolyIdTy (.spine r us) a :=
  covQ_no_finite_descending_identity
    (covQ_hereditary_emptyStep (E := E) (T := T) (Rel := Rel) hbot n Γ ρ) r us

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_REINDEX_ROOTS
#print axioms HereditaryCovRealizationQAt
#print axioms hereditaryCovRealizationQAt_typing
#print axioms hereditaryCovRealizationQAt_from_P
#print axioms hereditaryCovRealizationQAt_of_P
#print axioms covQ_hereditary_pi_code
#print axioms covQ_hereditary_emptyStep
#print axioms covQ_instance_first_identity_no_code
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_REINDEX_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit
