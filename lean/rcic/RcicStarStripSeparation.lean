import rcic.RcicCoherentStarStrip
import rcic.RcicCoherentCanonical

set_option maxRecDepth 8192

/-!
# Native eta peaks from computation under the eta binder

The constructions here retain the original `CStep`, `CStar`, and `CValley`
carriers. A certified body step under an eta binder is lifted to an actual
certified lambda step. The other leg is the native eta contraction, with
its stored source typing chosen to be exactly the lambda step's source
typing. Thus the source-decoration equality is definitional.

`iotaAfter_step` combines an actual certified preparation step and a native
iota equation in the existing `iotaSpine` constructor. In particular, a
proof leaf that prepares a constructor major can be followed by iota under
the lambda without adding a K or eta-K certificate.

`starStripValley_of_bodyStep` records the precise valley that an inhabitant
of the published `StarStrip` would have to return on this peak. It does
not assert that every such valley exists. No termination, confluence,
type-uniqueness, Pi-row, or retyping operation is constructed or assumed by
the positive peak builders. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StarStripSeparationAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Compose preparation with native iota in the existing parallel iota
constructor. Both typings and the certificate are actual supplied data. -/
def iotaAfter_step (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a redex rhs T : Expr Nat}
    (p : CStep E n PEq Γ a redex T)
    (hI : DerivedIota E redex rhs) (hrhs : HasTyT E n Γ rhs T) :
    CStep E n PEq Γ a rhs T :=
  let hredex := p.rightTyped L hΓ
  ⟨.iotaSpine Γ a redex rhs T p.step
      (derivedIotaU_ofDerivedIota hI) hredex hrhs,
    .iotaSpine
      (.trans Γ a redex rhs T p.toConvT
        (.iota Γ redex rhs T hI hredex hrhs)) p.cert⟩

/-- Lift an actual body step to a lambda step, keeping the binder domain
fixed. Its target typing is built from the body's actual target typing. -/
def lamAt_bodyStep (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B f rhs : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (p : CStep E n PEq (.assumption A :: Γ)
      (.app (lift 0 1 f) (.bvar 0)) rhs B) :
    CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0)))
      (.lam A rhs) (.pi A B) :=
  let hΓA := CtxWfT.assumption Γ A u hΓ hA
  let hAId := ConvT.refl Γ A (.sort u) hA
  let hright := HasTyT.lam Γ A u rhs B hA (p.rightTyped L hΓA)
  ⟨.lam Γ A A (.app (lift 0 1 f) (.bvar 0)) rhs B u v
      hAId hA hB p.step hright,
    .lam (.lam Γ A A (.app (lift 0 1 f) (.bvar 0)) rhs B u
      hAId p.toConvT) p.cert⟩

/-- The native eta leg on the same source. The source typing is literally
the other leg's source typing, so no decoration repair is needed. -/
def etaAt_bodyStep (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B f rhs : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (p : CStep E n PEq (.assumption A :: Γ)
      (.app (lift 0 1 f) (.bvar 0)) rhs B) :
    CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) :=
  let hl := (lamAt_bodyStep L hΓ hA hB p).leftTyped L hΓ
  ⟨.eta Γ f f A B (.refl Γ f (.pi A B) hf) hl,
    .eta (.eta Γ f A B hf) (.refl (.refl Γ f (.pi A B) hf))⟩

/-- Both actual input source decorations coincide definitionally. -/
theorem etaAt_bodyStep_source (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B f rhs : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (p : CStep E n PEq (.assumption A :: Γ)
      (.app (lift 0 1 f) (.bvar 0)) rhs B) :
    decoOf ((etaAt_bodyStep L hΓ hA hB hf p).leftTyped L hΓ) =
      decoOf ((lamAt_bodyStep L hΓ hA hB p).leftTyped L hΓ) := rfl

/-- An inhabitant of `StarStrip` must join the partial function with the
computed lambda in this concrete constructor pattern. This is a consumer
of the displayed premise, not a construction of that premise. -/
def starStripValley_of_bodyStep (L : LeafIface E n PEq)
    (D : CoherentStarStripAudit.StarStrip L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B f rhs : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hf : HasTyT E n Γ f (.pi A B))
    (p : CStep E n PEq (.assumption A :: Γ)
      (.app (lift 0 1 f) (.bvar 0)) rhs B) :
    CValley E n PEq Γ f (.lam A rhs) (.pi A B) := by
  let q := lamAt_bodyStep L hΓ hA hB p
  let e := etaAt_bodyStep L hΓ hA hB hf p
  let j := D hΓ e (CStar.ofStep L hΓ q) ⟨rfl, True.intro⟩ rfl
  exact ⟨j.centre, j.left, j.right⟩

#print axioms iotaAfter_step
#print axioms lamAt_bodyStep
#print axioms etaAt_bodyStep
#print axioms etaAt_bodyStep_source
#print axioms starStripValley_of_bodyStep

end Rcic.Declarative.NativeValleys.StarStripSeparationAudit
