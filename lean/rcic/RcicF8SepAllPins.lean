import rcic.RcicF8SepAll
import rcic.RcicAnnEnvBridge
import rcic.RcicAbelCoquandPin
import rcic.RcicF8JEndpointRefutation

/-!
# Concrete consumers of conditional separation

The empty environment supplies sort uniqueness directly through annotation
coherence. This fixture does not assume typed rows or an environment scope
certificate. The general composition still takes `SortUnique` explicitly.

The closed consumer uses the existing typing of `AbelCoquand.bot`. The mutant
deletes only the context-well-formedness check from that consumer's input
domain and actually accepts the canonical `illCtx` Prop typing. It tests
eligibility for separation; it does not assert a sort-to-Prop chain in `illCtx`.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.F8SepAllPins

open F8Measure

/-- A direct, concrete sort-uniqueness supplier for the empty environment. -/
theorem emptyEnv_sortUnique (n : Nat) : F8A2Support.SortUnique emptyEnv n := by
  let hno : Ann.NoGroupEnvA Ann.emptyEnvA :=
    fun _ _ hm => Option.noConfusion hm
  let C : Ann.AnnEnvA Ann.emptyEnvA :=
    Ann.annEnvA_of_bridged hno (fun _ _ => ⟨.empty⟩)
  let hn : Ann.EnvNormEraseA Ann.emptyEnvA := Ann.envNormEraseA_of_noGroup hno
  intro _ Γ T u v hΓ hT₁ hT₂
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := Ann.annCtxWfT' C hn hΓ
  obtain ⟨T₁, U, hT₁e, hU, ⟨t₁⟩⟩ := Ann.annHasTyT' C hn hT₁ hΓA hctx
  obtain ⟨T₂, V, hT₂e, hV, ⟨t₂⟩⟩ := Ann.annHasTyT' C hn hT₂ hΓA hctx
  obtain rfl := Ann.erase_eq_sort hU
  obtain rfl := Ann.erase_eq_sort hV
  exact Ann.annSortA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n)
    Ann.posValA_one hΓA (hT₁e.trans hT₂e.symm) t₁ t₂

/-- The actual input checks of the separation consumer, including a typed Prop. -/
def SepInput (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (P : Expr Nat) : Prop :=
  Nonempty (EnvWfT E) ∧ F8A2Support.SortUnique E n ∧
    Nonempty (CtxWfT E n Γ) ∧ Nonempty (HasTyT E n Γ P (.sort .zero))

/-- Every admitted input invokes the conditional separation composition. -/
theorem sepInput_no_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P : Expr Nat}
    (h : SepInput E n Γ P) (l : Level) :
    ¬ Nonempty (TyConvT E n Γ (.sort l) P) := by
  obtain ⟨⟨hW⟩, su, ⟨hΓ⟩, ⟨hP⟩⟩ := h
  rintro ⟨hc⟩
  exact sepAll_of_sortUnique hW su hΓ hP hc

/-- A real closed Prop is admitted, and separation excludes its sort chains. -/
theorem closed_consumer :
    SepInput emptyEnv 0 [] AbelCoquand.bot ∧
      ∀ l : Level, ¬ Nonempty (TyConvT emptyEnv 0 [] (.sort l) AbelCoquand.bot) := by
  have h : SepInput emptyEnv 0 [] AbelCoquand.bot :=
    ⟨⟨.empty⟩, emptyEnv_sortUnique 0, ⟨.nil⟩, ⟨AbelCoquand.botIsPropAt 0 []⟩⟩
  exact ⟨h, sepInput_no_sort h⟩

/-- Mutant: delete only the context check, retaining the other input checks. -/
def SepInputNoCtxWf (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (P : Expr Nat) : Prop :=
  Nonempty (EnvWfT E) ∧ F8A2Support.SortUnique E n ∧
    Nonempty (HasTyT E n Γ P (.sort .zero))

/-- The original rejects the canonical bad context; the mutant accepts it. -/
theorem ctxWf_gate_mutant :
    (¬ SepInput emptyEnv 0 XTileQ1.illCtx XTileQ1.P₂) ∧
      SepInputNoCtxWf emptyEnv 0 XTileQ1.illCtx XTileQ1.P₂ := by
  constructor
  · intro h
    exact JTileS0.illCtx_not_wf h.2.2.1
  · exact ⟨⟨.empty⟩, emptyEnv_sortUnique 0, ⟨XTileQ1.P₂_prop⟩⟩

end Rcic.Declarative.F8SepAllPins

#print axioms Rcic.Declarative.F8SepAllPins.emptyEnv_sortUnique
#print axioms Rcic.Declarative.F8SepAllPins.SepInput
#print axioms Rcic.Declarative.F8SepAllPins.sepInput_no_sort
#print axioms Rcic.Declarative.F8SepAllPins.closed_consumer
#print axioms Rcic.Declarative.F8SepAllPins.SepInputNoCtxWf
#print axioms Rcic.Declarative.F8SepAllPins.ctxWf_gate_mutant
