import rcic.RcicF8JTrans
import rcic.RcicF8XValley

/-!
Task 1: expose actual certified J5a successes to the partial X interface.
The certified option remains available alongside its valley projection.
Neither this projection nor its success contract proves J availability;
the J line's JT work owns AnswerOnDemandW. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.PiRowPackaging
variable {E : ResolvedEnv} {n : Nat}

/-- Preserve the original option and both certificate families without reconstruction. -/
def j5aCertified (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) : Option (J3.Result hW R h) :=
  J5a.dispatchWf hW su R hΓ h hs

/-- Project only the actual certified dispatcher, retaining its refusal domain. -/
def j5aWfP (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => (j5aCertified hW su R hΓ h hs).map (·.valley)

/-- A projected success carries the same actual result and its exact path-indexed tiles. -/
theorem j5aWfP_some_iff (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat}
    (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) (V : Valley R Γ a b T) :
    j5aWfP hW su R hΓ h hs = some V ↔
      ∃ out : J3.Result hW R h,
        j5aCertified hW su R hΓ h hs = some out ∧ out.valley = V := by
  exact Option.map_eq_some'

/-- Strict support is taken from that actual successful result. -/
theorem j5aWfP_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    JContractWfP (j5aWfP hW su) := by
  intro R Γ a b T hΓ h hs V hV
  obtain ⟨out, _, rfl⟩ := (j5aWfP_some_iff hW su R hΓ h hs V).mp hV
  exact out.strict

end Rcic.Declarative.F8Measure.PiRowPackaging

#print axioms Rcic.Declarative.F8Measure.PiRowPackaging.j5aCertified
#print axioms Rcic.Declarative.F8Measure.PiRowPackaging.j5aWfP
#print axioms Rcic.Declarative.F8Measure.PiRowPackaging.j5aWfP_some_iff
#print axioms Rcic.Declarative.F8Measure.PiRowPackaging.j5aWfP_contract
