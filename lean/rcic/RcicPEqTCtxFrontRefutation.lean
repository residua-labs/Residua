import rcic.RcicPEqT
import rcic.RcicCtxConvT
import rcic.RcicTypedInvert
import rcic.RcicDTMetaTypedSR

/-!
# Raw PEqT does not supply every binder context conversion

The universal `hdom` and `hlet` fronts used by the legacy conditional
`PEqT.symm` / `PEqT.trans` consumers demand a `CtxConvT` from arbitrary
raw `PEqT` inputs. These contracts have no inhabitant, for any E or n.

The counterexample uses two syntactically different ill-typed
applications, related structurally by PEqT using `eqN 0 (max 0 0)`.
An assumption conversion between them cannot be `.same`; the typed
alternative would type `bvar 0` in the empty context. The let example
keeps the declaration type fixed at `sort 0`, but uses these two bad
applications as values. Its typed alternative has the same problem.

This does not refute transport along an already supplied CtxConvT,
or symmetry/transitivity restricted to suitable well-typed inputs.
It refutes the raw universal supplier signatures. No judgment or
existing conditional consumer is changed. `closure_claim = 0`.
-/

namespace Rcic.Declarative

private def peqCtxBad (l : Level) : Expr Nat :=
  .app (.bvar 0) (.sort l)

private def peqCtxBadPair {E : ResolvedEnv} {n : Nat} :
    PEqT E n [] (peqCtxBad .zero) (peqCtxBad (.max .zero .zero)) :=
  .app [] (.bvar 0) (.bvar 0) (.sort .zero) (.sort (.max .zero .zero))
    (.bvar [] 0) (.sort [] .zero (.max .zero .zero) (fun _ => rfl))

private theorem peqCtxBad_not_typed {E : ResolvedEnv} {n : Nat}
    {l : Level} {T : Expr Nat} (h : HasTyT E n [] (peqCtxBad l) T) : False := by
  obtain ⟨_A, _B, hf, _ha, _hc⟩ := hasTyTInv_app h rfl
  obtain ⟨_T, hlookup, _hc⟩ := hasTyTInv_bvar hf rfl
  cases hlookup

private theorem peqCtxBad_assumption_forward {E : ResolvedEnv} {n : Nat}
    (h : CtxConvT E n [.assumption (peqCtxBad .zero)]
      [.assumption (peqCtxBad (.max .zero .zero))]) : False := by
  cases h with
  | assumption _ hA _ _ => exact peqCtxBad_not_typed hA

private theorem peqCtxBad_assumption_backward {E : ResolvedEnv} {n : Nat}
    (h : CtxConvT E n [.assumption (peqCtxBad (.max .zero .zero))]
      [.assumption (peqCtxBad .zero)]) : False := by
  cases h with
  | assumption _ hA _ _ => exact peqCtxBad_not_typed hA

private theorem peqCtxBad_let_forward {E : ResolvedEnv} {n : Nat}
    (h : CtxConvT E n [.letBinding (.sort .zero) (peqCtxBad .zero)]
      [.letBinding (.sort .zero) (peqCtxBad (.max .zero .zero))]) : False := by
  cases h with
  | letBinding _ _ _ _ hv' _ => exact peqCtxBad_not_typed hv'

private theorem peqCtxBad_let_backward {E : ResolvedEnv} {n : Nat}
    (h : CtxConvT E n [.letBinding (.sort .zero) (peqCtxBad (.max .zero .zero))]
      [.letBinding (.sort .zero) (peqCtxBad .zero)]) : False := by
  cases h with
  | letBinding _ _ _ _ hv' _ => exact peqCtxBad_not_typed hv'

/-- The forward `hdom` signature of the legacy conditional symmetry
consumer cannot be supplied, even at the empty base context. -/
theorem no_peqT_ctx_domain_forward_front {E : ResolvedEnv} {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {A A' : Expr Nat},
      PEqT E n Δ A A' →
      CtxConvT E n (.assumption A :: Δ) (.assumption A' :: Δ)) := by
  rintro ⟨hdom⟩
  exact peqCtxBad_assumption_forward (hdom peqCtxBadPair)

/-- The reverse `hdom` signature of the legacy conditional transitivity
consumer has the same raw-input obstruction. -/
theorem no_peqT_ctx_domain_backward_front {E : ResolvedEnv} {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {A A' : Expr Nat},
      PEqT E n Δ A A' →
      CtxConvT E n (.assumption A' :: Δ) (.assumption A :: Δ)) := by
  rintro ⟨hdom⟩
  exact peqCtxBad_assumption_backward (hdom peqCtxBadPair)

/-- The forward `hlet` contract fails even when A=A'=sort 0. Raw
PEqT values need not have the typing demanded by CtxConvT.letBinding. -/
theorem no_peqT_ctx_let_forward_front {E : ResolvedEnv} {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A v :: Δ) (.letBinding A' v' :: Δ)) := by
  rintro ⟨hlet⟩
  exact peqCtxBad_let_forward (hlet (PEqT.refl (.sort .zero)) peqCtxBadPair)

/-- The reverse `hlet` contract has the same obstruction. -/
theorem no_peqT_ctx_let_backward_front {E : ResolvedEnv} {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A' v' :: Δ) (.letBinding A v :: Δ)) := by
  rintro ⟨hlet⟩
  exact peqCtxBad_let_backward (hlet (PEqT.refl (.sort .zero)) peqCtxBadPair)

end Rcic.Declarative

#print axioms Rcic.Declarative.no_peqT_ctx_domain_forward_front
#print axioms Rcic.Declarative.no_peqT_ctx_domain_backward_front
#print axioms Rcic.Declarative.no_peqT_ctx_let_forward_front
#print axioms Rcic.Declarative.no_peqT_ctx_let_backward_front
