import rcic.RcicNativeSortValleyObstruction

set_option autoImplicit false

/-!
# A constructed Pi valley over the nonjoining sort-typed pair

The two domain terms `sortLeft` and `sortRight` have an actual native
conversion at `Sort 1`. The preceding obstruction module proves that
those terms have no common raw reduct. Nevertheless, putting them in
the domains of two written Pi expressions gives an actual one-step
native valley: raw `ParRedT.pi` accepts their existing `ConvT` directly.

The codomain is the same literal `Sort 0` on both sides. Its conversion
is reflexive at `Sort 1`, under the left domain's binder. The endpoint
Pi typings, native conversion, `CStepK` certificate, certified star and
raw native valley below are all constructed from this data.

No sorting-coherence, `SortRetype`, `PiInj`, type-uniqueness, Pi-row,
retyping or confluence supplier is used. In particular, the positive
declarations do not invoke the preceding module's negative proof or
the sorting supplier used there. There are no recursive calls.

This is a concrete control, not a general Pi-valley producer.
`closure_claim = 0`. No new axiom and no `sorry`.
-/

namespace Rcic.Declarative.NativeValleys.NativePiValleyControlAudit

open NativeSortValleyObstructionAudit

private abbrev one : Level := .succ .zero

/-- The left nonjoining sort-typed term used as a Pi domain. -/
def piLeft : Expr Nat := .pi sortLeft (.sort .zero)

/-- The right nonjoining sort-typed term used as the other Pi domain. -/
def piRight : Expr Nat := .pi sortRight (.sort .zero)

/-- The left endpoint's literal Pi-formation typing. -/
def piLeftTy : HasTyT trueEnvU 0 sortContext piLeft
    (.sort (.imax one one)) :=
  .pi sortContext sortLeft one (.sort .zero) one
    sortLeftTy (.sort _ .zero)

/-- The right endpoint has the same literal Pi-formation sorting. -/
def piRightTy : HasTyT trueEnvU 0 sortContext piRight
    (.sort (.imax one one)) :=
  .pi sortContext sortRight one (.sort .zero) one
    sortRightTy (.sort _ .zero)

/-- Pi congruence consumes the already constructed native domain
conversion and literal codomain reflexivity. -/
def piConversion : ConvT trueEnvU 0 sortContext piLeft piRight
    (.sort (.imax one one)) :=
  .pi sortContext sortLeft sortRight (.sort .zero) (.sort .zero) one one
    sortConversion
    (.refl (.assumption sortLeft :: sortContext) (.sort .zero) (.sort one)
      (.sort _ .zero))

/-- An actual raw Pi node and its native root certificate, in the
existing enlarged certified carrier. Its domain premise is
`sortConversion`, with no domain reduction or domain valley requested. -/
def piStep : CStepK trueEnvU 0 (ProofLeaf trueEnvU 0)
    sortContext piLeft piRight (.sort (.imax one one)) :=
  ⟨.pi sortContext sortLeft sortRight (.sort .zero) (.sort .zero) one one
      sortLeftTy sortConversion (.sort _ .zero)
      (.refl (.assumption sortLeft :: sortContext) (.sort .zero) (.sort one)
        (.sort _ .zero))
      piRightTy,
    .pi piConversion⟩

/-- The left Pi endpoint reaches the right in one certified step. -/
def piRepair : CStarK trueEnvU 0 (ProofLeaf trueEnvU 0)
    sortContext piLeft piRight (.sort (.imax one one)) :=
  .tail piStep (.refl sortContext piRight (.sort (.imax one one)) piRightTy)

/-- A native valley with one step on the left and reflexivity on the
right, despite the absence of a raw valley between the domain terms. -/
def piValley : NativeValley trueEnvU 0 sortContext piLeft piRight
    (.sort (.imax one one)) where
  centre := piRight
  left := piRepair.forget
  right := .refl sortContext piRight (.sort (.imax one one)) piRightTy

#print axioms piLeft
#print axioms piRight
#print axioms piLeftTy
#print axioms piRightTy
#print axioms piConversion
#print axioms piStep
#print axioms piRepair
#print axioms piValley

end Rcic.Declarative.NativeValleys.NativePiValleyControlAudit
