import rcic.RcicNativePiModelIdeal

/-!
# RcicNativePiModelL2 — ApproxSubst by composition

`approxSubst` is the substitution equation already proved for the landed
`Rcic.Declarative.NativeValleys.PiModelIdealAudit` approximation: the index `j`
is interpreted by `denI (EnvI.drop ρ j) r`. This module imports that ideal and
does not redeclare `CptI`, `EnvI`, `ApproxI`, or `denI`, and it does not re-prove
`approxI_subst_intro` or `approxI_subst_elim`.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiModelL2

open Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-- Both directions: the substituted index is the substitute's full approximation set. -/
theorem approxSubst (ρ : EnvI) (j : Nat) (r e : Expr Nat) (c : CptI) :
    ApproxI ρ (instantiate j (lift 0 j r) e) c ↔
      ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) e c := by
  constructor
  · exact approxI_subst_elim e
  · intro h
    exact approxI_subst_intro h ρ j r rfl

#print axioms approxSubst

end Rcic.Declarative.NativeValleys.PiModelL2
