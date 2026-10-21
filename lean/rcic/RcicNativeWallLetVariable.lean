import rcic.RcicNativeValleyLift
import rcic.RcicNativeValleyOf

/-!
# Native changed-let variable bridge

`closure_claim = 0`.

This file constructs the head-variable case of a changed-let bridge from the
SAME-INDEX certified diamond. It does not assume or construct a generic bridge
for arbitrary certified stars. Leaf weakening is derived from `LeafIface` and
native typing weakening; no generic parallel-to-native back-lift is used.

Dependency pin: `4d3b74e05355f478a03a44166399794a0a68d2a4`.
-/

namespace Rcic.Declarative.NativeValleys.LetVariableAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The leaf interface itself supplies weakening: weaken the proposition and
both endpoint typings, then form a fresh irrelevance leaf. -/
def leaf_weaken (hcl : EnvClosed E) (L : LeafIface E n PEq)
    {Γ : LCtx} {p q T : Expr Nat} {d : LocalDecl} {c : Nat}
    (h : PEq Γ p q T) :
    PEq (insertAt d c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T) :=
  L.ofIrr
    (hasTyTWeaken d hcl (c := c) (L.prop h))
    (hasTyTWeaken d hcl (c := c) (L.typed h).1)
    (hasTyTWeaken d hcl (c := c) (L.typed h).2)

/-- Certified star weakening under a single chosen head declaration. -/
def star_weaken_head (hcl : EnvClosed E) (L : LeafIface E n PEq)
    (d : LocalDecl) {Γ : LCtx} :
    {a b T : Expr Nat} → CStar E n PEq Γ a b T →
    CStar E n PEq (d :: Γ) (lift 0 1 a) (lift 0 1 b) (lift 0 1 T)
  | _, _, _, .refl _ a T h =>
      .refl (d :: Γ) (lift 0 1 a) (lift 0 1 T) (by
        simpa only [insertAt_zero] using hasTyTWeaken d hcl (c := 0) h)
  | _, _, _, .tail s hs =>
      .tail (by
        simpa only [insertAt_zero] using
          cstep_lift d hcl (leaf_weaken hcl L) (c := 0) s.cert)
        (star_weaken_head hcl L d hs)

/-- The ordinary certified local-unfolding step under a head let binding.
Its stored-value child is reflexive in the original tail context. -/
def head_let_unfold (hcl : EnvClosed E) {Γ : LCtx} {A v : Expr Nat}
    (hv : HasTyT E n Γ v A) :
    CStep E n PEq (.letBinding A v :: Γ) (.bvar 0)
      (lift 0 1 v) (lift 0 1 A) :=
  let hr : HasTyT E n (.letBinding A v :: Γ) (lift 0 1 v) (lift 0 1 A) := by
    simpa only [insertAt_zero] using
      hasTyTWeaken (.letBinding A v) hcl (c := 0) hv
  let hl : HasTyT E n (.letBinding A v :: Γ) (.bvar 0) (lift 0 1 A) :=
    .bvar _ 0 _ rfl
  let c : ConvT E n (.letBinding A v :: Γ) (.bvar 0)
      (lift 0 1 v) (lift 0 1 A) :=
    .zetaLocal _ 0 _ _ rfl rfl hr
  ⟨.bvarZeta (.letBinding A v :: Γ) 0 A v v (lift 0 1 A)
      rfl (.refl Γ v A hv) hl hr,
    .bvarZeta c (.refl (.refl Γ v A hv))⟩

/-- The native variable wall, constructed from the same-index diamond.

Join `v ⇒ vd` with `v ⇒* vc` in the tail context at `A`. Under the new
binding, unfold `bvar 0` to `lift vc` and follow the weakened `vc` join leg.
Under the old binding, follow the weakened `vd` join leg. The two contexts
remain distinct throughout; no existing step is transported between them. -/
def let_variable_bridge (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v vd vc : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (p : CStep E n PEq Γ v vd A) (sv : CStar E n PEq Γ v vc A) :
    Σ' (w : Expr Nat),
      CStar E n PEq (.letBinding A vc :: Γ) (.bvar 0)
        (lift 0 1 w) (lift 0 1 A) ×'
      CStar E n PEq (.letBinding A v :: Γ) (lift 0 1 vd)
        (lift 0 1 w) (lift 0 1 A) :=
  let hcl := envClosed_of_envWfT hW
  let ⟨w, sd, sc⟩ := confluence D L hΓ (CStar.ofStep L hΓ p) sv
  let hvc := sv.rightTyped
  let hΓc := CtxWfT.letBinding Γ A u vc hΓ hA hvc
  let sc' := star_weaken_head hcl L (.letBinding A vc) sc
  let sd' := star_weaken_head hcl L (.letBinding A v) sd
  let z := head_let_unfold (PEq := PEq) hcl hvc
  ⟨w, (CStar.ofStep L hΓc z).trans sc', sd'⟩

#print axioms leaf_weaken
#print axioms star_weaken_head
#print axioms head_let_unfold
#print axioms let_variable_bridge

end Rcic.Declarative.NativeValleys.LetVariableAudit
