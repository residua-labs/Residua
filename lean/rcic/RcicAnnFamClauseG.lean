import rcic.RcicAnnFamClause
import rcic.RcicAnnLREnvG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnLRRowsG
/-!
# M2-f (4b) — the unbounded `=ₙ` instance

The census of a group step (`CtorClosedA`, `groupCensusA`) moved to `RcicAnnEnvWf`, where the
environment induction carries constructor closure (M2-f (4b)). This file keeps the pins of
M2-f (4b)-1: the clause's data at an unbounded `=ₙ` level list, repaired by M2-f (3d).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (2) the unbounded `=ₙ` instance (M2-f (4b)-1)

Until M2-f (3d) the clause's data quantified over every level list `=ₙ` the carrier's. `=ₙ` does
not bound parameters: `imax a b` evaluates `b` first and returns `0` at a zero `b` without reading
`a`, so `[imax (param 0) zero] =ₙ [zero]` — and the left list is unbounded at arity `0`. A constant
at it is untypeable there (the `const` rule's boundedness, `hasTyA_constsBounded`), so no type headed
by it is valid at any height. A constructor field whose domain is a polymorphic constant at the
family's level parameter therefore had, at that `=ₙ` instance, a domain the clause's `hFld` must
declare valid and could not. (3d) bounds the data's lists (`eqNListB`, `RcicAnnFam`, where
`ConstsBoundedA` and `hasTyA_constsBounded` now live); the bounded tie excludes this instance
(`unboundedTie_notB`). -/

section Unbounded
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- THE PIN: at arity `0`, a constant at `[imax (param 0) zero]` heads no valid type, at any height. -/
theorem unboundedConst_noValidityg {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} (g : Nat)
    (R : ExprA → ExprA → Prop) : ¬ LRTyAg E I 0 ρ₀ k Γ (.const g [.imax (.param 0) .zero]) R := by
  intro h
  rw [LRTyA_eqg] at h
  obtain ⟨_, ⟨hT⟩⟩ := tyKA_hasTyg h
  have hb : levelsBounded 0 [.imax (.param 0) .zero] = true := hasTyA_constsBounded hT
  rw [unboundedTie_notBounded] at hb
  exact Bool.noConfusion hb

end Unbounded

#print axioms unboundedConst_noValidityg

end Rcic.Declarative.Ann
