import rcic.RcicNativeKProjection

/-!
# The exact strength of the Pi-only native valley contract

`ParRedT.pi` takes native component `ConvT` values, not reduction steps.
Consequently, once the two component `TyConvT` chains are supplied,
`SortRetype` packs them into one raw Pi step at the source's actual
component sorts. The source typing inversion supplies the exact chain
from its intrinsic Pi sort to the requested index; the target's given
typing is transported backwards along that chain for the raw node.

This module constructs that step and its one-step/reflexive valley. It
then constructs the reverse adapter

  `PiInj E n -> PiConvValleyData E n`

under `EnvWfT E` and `SortRetype E n`. Zero-sort coherence is needed only
by the already existing adapter in the other direction. Thus under the
three explicit assumptions, the two Type-valued interfaces have
equivalent inhabitedness. This is mutual sufficiency, not an equivalence
of all the data values in the interfaces.

No independent producer of either interface is constructed. In
particular, plugging this reverse adapter into the existing consumer
calls the supplied `PiInj` on a homogenized version of the full original
Pi conversion. That call is not a smaller conversion subproblem.

`closure_claim = 0`. No new axiom and no `sorry`.
-/

namespace Rcic.Declarative.NativeValleys.NativePiValleyContractAudit

open NativeKProjectionAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Supplied component chains give one actual raw Pi step. The only
sorting alignment is `SortRetype` on those chains. The common endpoint
index `T` is retained using the chain returned by the source's own
typing inversion, without type uniqueness or a global step-retyping
theorem. This construction is independent of the proof-leaf carrier. -/
def rawPiStep_of_componentTyConv_sortRetype (hW : EnvWfT E)
    (sr : SortRetype E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ B₁ A₂ B₂ T : Expr Nat}
    (hLeft : HasTyT E n Γ (.pi A₁ B₁) T)
    (hRight : HasTyT E n Γ (.pi A₂ B₂) T)
    (cA : TyConvT E n Γ A₁ A₂)
    (cB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    ParRedT PEq E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T := by
  obtain ⟨u, v, hA, hB, cIndex⟩ := hasTyTInv_pi hLeft rfl
  let hΓA : CtxWfT E n (.assumption A₁ :: Γ) :=
    .assumption Γ A₁ u hΓ hA
  let dA : ConvT E n Γ A₁ A₂ (.sort u) :=
    convT_of_tyConvT_of_sortRetype hW sr hΓ hA cA
  let dB : ConvT E n (.assumption A₁ :: Γ) B₁ B₂ (.sort v) :=
    convT_of_tyConvT_of_sortRetype hW sr hΓA hB cB
  let hRightBase : HasTyT E n Γ (.pi A₂ B₂) (.sort (.imax u v)) :=
    hasTyT_of_tyConvT hRight cIndex.symmT
  exact .conv Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) T
    (.pi Γ A₁ A₂ B₁ B₂ u v hA dA hB dB hRightBase) cIndex

/-- Pack the constructed raw step as a native valley whose centre is
the right endpoint. The left leg has one step and the right leg is
reflexive; no confluence operation is used. -/
def nativePiValley_of_componentTyConv_sortRetype (hW : EnvWfT E)
    (sr : SortRetype E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ B₁ A₂ B₂ T : Expr Nat}
    (hLeft : HasTyT E n Γ (.pi A₁ B₁) T)
    (hRight : HasTyT E n Γ (.pi A₂ B₂) T)
    (cA : TyConvT E n Γ A₁ A₂)
    (cB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    NativeValley E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T where
  centre := .pi A₂ B₂
  left := .tail
    (rawPiStep_of_componentTyConv_sortRetype hW sr hΓ hLeft hRight cA cB)
    (.refl Γ (.pi A₂ B₂) T hRight)
  right := .refl Γ (.pi A₂ B₂) T hRight

/-- Pointwise exactness: for two given endpoint typings, a native Pi
valley and the two component chains are mutually sufficient under the
explicit sorting assumptions. The `Nonempty` values are eliminated
only into the displayed proposition. -/
theorem nativePiValley_nonempty_iff_components (hW : EnvWfT E)
    (sr : SortRetype E n) (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ T : Expr Nat}
    (hLeft : HasTyT E n Γ (.pi A₁ B₁) T)
    (hRight : HasTyT E n Γ (.pi A₂ B₂) T) :
    Nonempty (NativeValley E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T) ↔
      Nonempty (TyConvT E n Γ A₁ A₂ ×
        TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  constructor
  · rintro ⟨V⟩
    exact ⟨nativeValley_pi_inv_of_zsc hW zsc hΓ V⟩
  · rintro ⟨row⟩
    exact ⟨nativePiValley_of_componentTyConv_sortRetype hW sr hΓ
      hLeft hRight row.1 row.2⟩

/-- The reverse interface adapter. It calls the supplied `PiInj` once
on the entire input conversion wrapped as one `TyConvT.of`; it then
constructs the actual valley above. No zero-sort coherence is needed
for this direction. This is a conditional adapter, not a producer
independent of Pi injectivity. -/
def piConvValleyData_of_piInj_sortRetype (hW : EnvWfT E)
    (piInj : PiInj E n) (sr : SortRetype E n) : PiConvValleyData E n :=
  fun {Γ} hΓ {A₁ B₁ A₂ B₂ u} c =>
    let ends := convEnds hW hΓ c
    let row := piInj hΓ (.of Γ (.pi A₁ B₁) (.pi A₂ B₂) u c)
    nativePiValley_of_componentTyConv_sortRetype hW sr hΓ
      ends.1 ends.2.1 row.1 row.2

/-- Under the existing sorting assumptions, the Pi-only valley
contract is inhabited exactly when full Type-valued Pi injectivity is
inhabited. Both directions are actual adapters; neither premise is
asserted to be inhabited. -/
theorem nonempty_piConvValleyData_iff_piInj (hW : EnvWfT E)
    (sr : SortRetype E n) (zsc : HostPropAudit.ZeroSortCoherence E n) :
    Nonempty (PiConvValleyData E n) ↔ Nonempty (PiInj E n) := by
  constructor
  · rintro ⟨join⟩
    exact ⟨piInj_of_piValleyData_sortRetype hW join sr zsc⟩
  · rintro ⟨piInj⟩
    exact ⟨piConvValleyData_of_piInj_sortRetype hW piInj sr⟩

#print axioms rawPiStep_of_componentTyConv_sortRetype
#print axioms nativePiValley_of_componentTyConv_sortRetype
#print axioms nativePiValley_nonempty_iff_components
#print axioms piConvValleyData_of_piInj_sortRetype
#print axioms nonempty_piConvValleyData_iff_piInj

end Rcic.Declarative.NativeValleys.NativePiValleyContractAudit
