import rcic.RcicA2SortSupport
import rcic.RcicF8XStruct
import rcic.RcicEtaKDecide

/-!
# Sort uniqueness supplies separation in well-formed contexts

Integration item 2 of the piRow plan (#7156, cc's ruling): compose the
existing `separationAt_of_sortUniq`, keeping `SortUnique` explicit.
`SepAllWf` is the `CtxWfT`-conditioned form that this theorem supplies.
The existing Γ-unconditional `SepAll` and X suppliers are unchanged.

This module does not obtain sort uniqueness from `TypedRowsWf` or
`InScope`. The piRow construction must supply it independently.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure

/-- Prop/sort separation restricted to well-formed contexts. -/
def SepAllWf (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P : Expr Nat} {l : Level},
    HasTyT E n Γ P (.sort .zero) → TyConvT E n Γ (.sort l) P → False

/-- Conditional composition only: sort uniqueness remains an explicit premise. -/
theorem sepAll_of_sortUnique {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (su : F8A2Support.SortUnique E n) : SepAllWf E n := by
  intro Γ hΓ P l hP hc
  exact F8EtaK.separationAt_of_sortUniq hW (su hW) hΓ hP hc

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.SepAllWf
#print axioms Rcic.Declarative.F8Measure.sepAll_of_sortUnique
