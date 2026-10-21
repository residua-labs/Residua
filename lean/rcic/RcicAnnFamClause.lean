import rcic.RcicAnnTelIntro

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

/-- `[imax (param 0) zero] =ₙ [zero]`. -/
theorem unboundedTie_eqN : eqNList [Level.zero] [.imax (.param 0) .zero] :=
  ⟨fun _ => rfl, trivial⟩

/-- …and it is not bounded at arity `0`. -/
theorem unboundedTie_notBounded : levelsBounded 0 [.imax (.param 0) .zero] = false := rfl

/-- M2-f (3d): the bounded tie excludes it. -/
theorem unboundedTie_notB : ¬ eqNListB 0 [Level.zero] [.imax (.param 0) .zero] :=
  fun h => Bool.noConfusion (h.2.symm.trans unboundedTie_notBounded)

/-- THE PIN: at arity `0`, a constant at `[imax (param 0) zero]` heads no valid type, at any height. -/
theorem unboundedConst_noValidity {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} (g : Nat)
    (R : ExprA → ExprA → Prop) : ¬ LRTyA E I 0 ρ₀ k Γ (.const g [.imax (.param 0) .zero]) R := by
  intro h
  rw [LRTyA_eq] at h
  obtain ⟨_, ⟨hT⟩⟩ := tyKA_hasTy h
  have hb : levelsBounded 0 [.imax (.param 0) .zero] = true := hasTyA_constsBounded hT
  rw [unboundedTie_notBounded] at hb
  exact Bool.noConfusion hb

end Unbounded

#print axioms hasTyA_constsBounded
#print axioms unboundedTie_eqN
#print axioms unboundedTie_notB
#print axioms unboundedConst_noValidity

end Rcic.Declarative.Ann
