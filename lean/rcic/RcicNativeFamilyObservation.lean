import rcic.RcicFamAppLeftInst

/-!
# Reading native family argument observations at their left domains

A supplied `ConvArgsT` already stores native conversion evidence along
the left argument prefix.  This module reads that evidence at the exact
`instPrefix (pre ++ as.take i) d` domain of `RelevantSlotConv`.

The existing `convArgsT_getElem` in `RcicIARecIH` covers saturated
telescopes ending in a sort.  The extractor here additionally allows an
arbitrary initial prefix, arbitrary residual body, and partial spines.
Its lookup guards restrict the conclusion to represented telescope
slots; no saturation or length premise is added.

The proof inducts on the original `ConvArgsT` derivation.  At a successor
slot it uses the original tail and the existing `instPrefix_snoc` law;
it does not recurse on a generated conversion.  The conclusion remains
`Nonempty (ConvT ...)`, exactly as stored by `ConvArgsT`, so no choice or
elimination from Prop into native conversion data is used.

This is a consumer of an actual native argument observation.  It does
not derive that observation from a family application conversion or
from semantic equality.  A semantic family adequacy proof must still
construct the supplied native observation.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeFamilyObservationAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Read a native slot conversion through an observed telescope
decomposition.  The residual body need not be a sort, and the argument
list need not consume the whole telescope. -/
theorem convArgsT_slot_of_telescope
    {T : Expr Nat} {as as' : List (Expr Nat)}
    (h : ConvArgsT E n Γ T as as') :
    ∀ (pre ds : List (Expr Nat)) (U : Expr Nat),
      T = instPrefix pre (policyPi ds U) →
      ∀ (i : Nat) (x x' d : Expr Nat),
        as[i]? = some x → as'[i]? = some x' → ds[i]? = some d →
        Nonempty (ConvT E n Γ x x'
          (instPrefix (pre ++ as.take i) d)) := by
  induction h with
  | nil _ =>
      intro pre ds U hT i x x' d hx hx' hd
      simp at hx
  | cons A B f f' fs fs' hc hs ih =>
      intro pre ds U hT i x x' d hx hx' hd
      cases ds with
      | nil => simp at hd
      | cons d₀ ds =>
          have hπ : Expr.pi A B =
              .pi (instPrefix pre d₀) (instTel pre (policyPi ds U)) :=
            hT.trans (instPrefix_pi pre d₀ (policyPi ds U))
          injection hπ with hA hB
          cases i with
          | zero =>
              have hx₀ : f = x := by simpa using hx
              have hx₀' : f' = x' := by simpa using hx'
              have hd₀ : d₀ = d := by simpa using hd
              subst x
              subst x'
              subst d
              simpa only [List.take_zero, List.append_nil, hA] using hc
          | succ i =>
              have htailT : instantiate0 f B =
                  instPrefix (pre ++ [f]) (policyPi ds U) := by
                rw [instPrefix_snoc, hB]
              have hslot := ih (pre ++ [f]) ds U htailT i x x' d
                (by simpa only [List.getElem?_cons_succ] using hx)
                (by simpa only [List.getElem?_cons_succ] using hx')
                (by simpa only [List.getElem?_cons_succ] using hd)
              have hpref : (pre ++ [f]) ++ fs.take i =
                  pre ++ (f :: fs).take (i + 1) := by
                rw [List.append_assoc, List.take_succ_cons, List.singleton_append]
              simpa only [hpref] using hslot

/-- The exact relevant-slot port consumed by the native family walk.
The supplied native observation yields conversions at every represented
slot, so this projection does not need the port's sorting/relevance
guards or any native row hypothesis. -/
theorem relevantSlotConv_of_convArgsT
    {pre ds as as' : List (Expr Nat)} {U : Expr Nat}
    (h : ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) as as') :
    RelevantSlotConv E n Γ pre ds as as' := by
  intro i x x' d u hx hx' hd hD hu
  exact convArgsT_slot_of_telescope h pre ds U rfl i x x' d hx hx' hd

#print axioms convArgsT_slot_of_telescope
#print axioms relevantSlotConv_of_convArgsT

end Rcic.Declarative.NativeFamilyObservationAudit
