import rcic.RcicNativeTypedModelCovWTypedActions
import rcic.RcicSubstTTyped

/-!
# Bounded native typed raw supply

The landed finite `ApproxTW` induction supplies the stronger operational
actions.  The constructive adapter in `CovWTypedActions` restricts their row
tests while native source typing is retained as actual evidence.  The closed
raw supplier below has no Pi-readback, domain-code, or normalization premise.

Its conclusion is deliberately `covWTyped_rawAction`, whose negative
argument premises are still landed operational actions.  It is not the
requested general adequacy theorem for the exact recursive
`CovWTypedAction`.  Exact raw supply is proved here only for bottom and the
three type-head forms, whose action clauses have no negative recursion.

For simultaneous substitution, `covWTyped_raw_instantiated` takes the actual
typing of the substituted term.  `covWTyped_raw_subst` instead derives that
typing from `TypedSubstT` by the landed theorem, retaining its explicit
`IotaSubstT` hypothesis.  This module does not assert a new unconditional
parallel-substitution theorem for legacy derived iota.

No guarded adequacy or observation antireduction is claimed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovVAudit TypedModelCovWAudit

/-- A genuine closed raw supplier for the bounded action.  The conclusion
retains the supplied native type, rather than using it only for arity. -/
theorem covWTyped_raw_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c) :
    covWTyped_rawAction E n Γ c e A :=
  covWTyped_raw_action_of_value ht (covW_raw_closed_actions hW ht ho)

/-- Actual typing at the actual substituted type is required explicitly;
typing in an unrelated source context cannot stand in for this evidence. -/
theorem covWTyped_raw_instantiated {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {ρ : EnvT} {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E ρ e c) (σ : SubstT)
    (hti : HasTyT E n Δ (substT σ e) (substT σ A))
    (hσ : ∀ i u, ρ i u → CovWValueAction E n Δ u (σ i)) :
    covWTyped_rawAction E n Δ c (substT σ e) (substT σ A) :=
  covWTyped_raw_action_of_value hti (covW_raw_typed_actions hW ht ho σ hσ)

/-- Typed simultaneous substitution supplies the actual resulting native
typing.  Its existing iota-transport premise remains visible. -/
theorem covWTyped_raw_subst {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) (hι : IotaSubstT E)
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ)
    {ρ : EnvT} {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E ρ e c) (σ : SubstT)
    (hT : TypedSubstT E n Δ σ Γ)
    (hσ : ∀ i u, ρ i u → CovWValueAction E n Δ u (σ i)) :
    covWTyped_rawAction E n Δ c (substT σ e) (substT σ A) := by
  have hcl := envClosed_of_envWfT hW
  obtain ⟨hti⟩ := hasTyT_substT hW hcl
    (envMembersSubstTStable_of_envClosed hcl) hι hΓ ht hΔ hT
  exact covWTyped_raw_instantiated hW ht ho σ hti hσ

/-- At a concrete raw application, the actual typed raw argument supplies
all of the bounded interface's stronger argument premises constructively. -/
theorem covWTyped_raw_closed_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {f x D B : Expr Nat}
    {rows : List (List CptT × CptT)} {s : List CptT × CptT} {d : CptT}
    (hf : HasTyT E n Γ f (.pi D B))
    (hof : ApproxTW E EnvT.bot f (.lam rows))
    (hD : ApproxTW E EnvT.bot D d) (hs : s ∈ rows)
    (hd : ∀ u ∈ s.1, CTyS E u d)
    (hx : HasTyT E n Γ x D)
    (hox : ∀ u ∈ s.1, ApproxTW E EnvT.bot x u) :
    covWTyped_rawAction E n Γ s.2 (.app f x) (instantiate0 x B) :=
  covWTyped_raw_action_app (covWTyped_raw_closed hW hf hof) hD hs hd hx
    (fun u hu => covW_raw_closed_actions hW hx (hox u hu))

/-- Bottom has an exact typed action without any operational premise. -/
theorem covWTyped_exact_raw_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (ht : HasTyT E n Γ e A)
    (_ho : ApproxTW E EnvT.bot e .bot) : CovWTypedAction E n Γ .bot e A :=
  covWTyped_action_bot ht

/-- The Prop-code leaf has no negative action occurrences. -/
theorem covWTyped_exact_raw_prop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e .prop) :
    CovWTypedAction E n Γ .prop e A := by
  refine ⟨⟨ht⟩, ?_⟩
  have h := covW_raw_closed_actions (Δ := Γ) hW ht ho
  simpa only [CovWValueAction, covWTyped_actionCore] using h

/-- The Sort-code leaf has no negative action occurrences. -/
theorem covWTyped_exact_raw_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e .sort) :
    CovWTypedAction E n Γ .sort e A := by
  refine ⟨⟨ht⟩, ?_⟩
  have h := covW_raw_closed_actions (Δ := Γ) hW ht ho
  simpa only [CovWValueAction, covWTyped_actionCore] using h

/-- The Pi-code clause recovers a native Pi term head.  It is distinct from
the native Pi typing required to test a lambda compact. -/
theorem covWTyped_exact_raw_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {d : CptT}
    {rows : List (List CptT × CptT)}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e (.pi d rows)) :
    CovWTypedAction E n Γ (.pi d rows) e A := by
  refine ⟨⟨ht⟩, ?_⟩
  have h := covW_raw_closed_actions (Δ := Γ) hW ht ho
  simpa only [CovWValueAction, covWTyped_actionCore] using h

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_RAW_ADEQUACY_ROOTS
#print axioms covWTyped_raw_closed
#print axioms covWTyped_raw_instantiated
#print axioms covWTyped_raw_subst
#print axioms covWTyped_raw_closed_row
#print axioms covWTyped_exact_raw_bot
#print axioms covWTyped_exact_raw_prop
#print axioms covWTyped_exact_raw_sort
#print axioms covWTyped_exact_raw_pi
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_RAW_ADEQUACY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit
