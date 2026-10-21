import rcic.RcicNativeValleyOf

/-!
# Native let legs at a supplied common value

Actual certified congruence constructions. The body valley consumed by
`valley_let_at_value_centre` is under the COMMON value, not the source value.
This file does not manufacture that body valley, a generic LetBridge, or a
diamond. No generic `parRedT_to_convT` is used.

Dependency pin: `4d3b74e05355f478a03a44166399794a0a68d2a4`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A fixed-value let lifts a certified body star. -/
def letBodyStar (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ v A)
    (hB : HasTyT E n (.letBinding A v :: Γ) B (.sort w)) :
    {b c : Expr Nat} → CStar E n PEq (.letBinding A v :: Γ) b c B →
    CStar E n PEq Γ (.letE A v b) (.letE A v c) (instantiate0 v B)
  | _, _, .refl _ b _ hb =>
      .refl Γ _ _ (.letE Γ A u v B b hA hv hb)
  | _, _, @CStar.tail _ _ _ _ _ b' _ _ s hs =>
      let hb' := s.rightTyped L (.letBinding Γ A u v hΓ hA hv)
      let hTy := hasTyT_substLet0_of_envWfT hW hB hv
      .tail
        ⟨.letE Γ A A v v _ b' B u w (.refl Γ A _ hA) hA
            (.refl Γ v A hv) hB hTy s.step (.letE Γ A u v B b' hA hv hb'),
          .letE (.letE Γ A A v v _ b' B u (.refl Γ A _ hA)
            (.refl Γ v A hv) s.toConvT) (.refl (.refl Γ v A hv)) s.cert⟩
        (letBodyStar hW L hΓ hA hv hB hs)

/-- Change only the let value, retaining the body's syntax. Every step's
native certificate supplies the dependent type conversion needed for its leg.
The recursion is on the supplied value star; accumulated certificates are
auxiliary data and are never recursive inputs. -/
def letValueStar (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v₀ b B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv₀ : HasTyT E n Γ v₀ A)
    (hB₀ : HasTyT E n (.letBinding A v₀ :: Γ) B (.sort w))
    (hb₀ : HasTyT E n (.letBinding A v₀ :: Γ) b B) :
    {v v' : Expr Nat} → CStar E n PEq Γ v v' A → ConvT E n Γ v₀ v A →
    CStar E n PEq Γ (.letE A v b) (.letE A v' b) (instantiate0 v₀ B)
  | _, _, .refl _ v _ hv, c₀ =>
      let cc := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA
        (.refl Γ A _ hA) hv c₀
      let hB := hasTyT_ctx (envClosed_of_envWfT hW) cc hB₀
      let hb := hasTyT_ctx (envClosed_of_envWfT hW) cc hb₀
      .refl Γ _ _
        (.conv Γ _ _ _ w (.letE Γ A u v B b hA hv hb)
          (convT_inst0_valueSortLet hA hv hv₀ hB hB₀ (.symm _ _ _ _ c₀)))
  | _, _, @CStar.tail _ _ _ _ v v' _ _ s hs, c₀ =>
      let hcl := envClosed_of_envWfT hW
      let hv := s.leftTyped L hΓ
      let hv' := s.rightTyped L hΓ
      let c₁ := ConvT.trans _ _ _ _ _ c₀ s.toConvT
      let cc := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA
        (.refl Γ A _ hA) hv c₀
      let cc' := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA
        (.refl Γ A _ hA) hv' c₁
      let hB := hasTyT_ctx hcl cc hB₀
      let hb := hasTyT_ctx hcl cc hb₀
      let hB' := hasTyT_ctx hcl cc' hB₀
      let hb' := hasTyT_ctx hcl cc' hb₀
      let hTy := hasTyT_substLet0_of_envWfT hW hB hv
      let hr : HasTyT E n Γ (.letE A v' b) (instantiate0 v B) :=
        .conv Γ _ _ _ w (.letE Γ A u v' B b hA hv' hb')
          (convT_inst0_valueSortLet hA hv' hv hB' hB (.symm _ _ _ _ s.toConvT))
      let step : CStep E n PEq Γ (.letE A v b) (.letE A v' b) (instantiate0 v B) :=
        ⟨.letE Γ A A v v' b b B u w (.refl Γ A _ hA) hA s.step hB hTy
            (.refl _ b B hb) hr,
          .letE (.letE Γ A A v v' b b B u (.refl Γ A _ hA)
            s.toConvT (.refl _ b B hb)) s.cert (.refl (.refl _ b B hb))⟩
      .tail
        (step.reindex (.of Γ _ _ w
          (convT_inst0_valueSortLet hA hv hv₀ hB hB₀ (.symm _ _ _ _ c₀))))
        (letValueStar hW L hΓ hA hv₀ hB₀ hb₀ hs c₁)

/-- An annotation-only let step is reversible by invoking this construction
with the reverse annotation conversion and the corresponding source typing. -/
def letAnnotationStep (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' v b B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (cA : ConvT E n Γ A A' (.sort u))
    (hv : HasTyT E n Γ v A) (hb : HasTyT E n (.letBinding A v :: Γ) b B) :
    CStep E n PEq Γ (.letE A v b) (.letE A' v b) (instantiate0 v B) :=
  let hΓv := CtxWfT.letBinding Γ A u v hΓ hA hv
  let ⟨w, hB⟩ := tySort hW hΓv hb
  let c := ConvT.letE Γ A A' v v b b B u cA (.refl Γ v A hv) (.refl _ b B hb)
  ⟨.letE Γ A A' v v b b B u w cA hA (.refl Γ v A hv) hB
      (hasTyT_substLet0_of_envWfT hW hB hv) (.refl _ b B hb) (convEnds hW hΓ c).2.1,
    .letE c (.refl (.refl Γ v A hv)) (.refl (.refl _ b B hb))⟩

/-- Move the value to its centre first, then run the body star under that
common value. The required body typing at the starting value is transported
natively from the supplied common-value body star. -/
def letArmToCentre (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v vc b bc B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (sv : CStar E n PEq Γ v vc A)
    (sb : CStar E n PEq (.letBinding A vc :: Γ) b bc B) :
    CStar E n PEq Γ (.letE A v b) (.letE A vc bc) (instantiate0 v B) :=
  let hv := sv.leftTyped L hΓ
  let hvc := sv.rightTyped
  let hΓc := CtxWfT.letBinding Γ A u vc hΓ hA hvc
  let hbc := sb.leftTyped L hΓc
  let ⟨w, hBc⟩ := tySort hW hΓc hbc
  let cc := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA (.refl Γ A _ hA)
    hv (.symm _ _ _ _ sv.toConvT)
  let hBv := hasTyT_ctx (envClosed_of_envWfT hW) cc hBc
  let hbv := hasTyT_ctx (envClosed_of_envWfT hW) cc hbc
  let first := letValueStar hW L hΓ hA hv hBv hbv sv (.refl Γ v A hv)
  let second := (letBodyStar hW L hΓ hA hvc hBc sb).reindex
    (.of Γ _ _ w (convT_inst0_valueSortLet hA hvc hv hBc hBv (.symm _ _ _ _ sv.toConvT)))
  first.trans second

/-- The native `letE` valley once both bodies have been joined under the value
centre. This is a construction, but it does not claim to transport an arbitrary
body star from the old let context to that common-value context. -/
def valley_let_at_value_centre (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' v v' b b' B : Expr Nat} {u : Level}
    (cA : ConvT E n Γ A A' (.sort u))
    (vv : CValley E n PEq Γ v v' A)
    (vb : CValley E n PEq (.letBinding A vv.centre :: Γ) b b' B) :
    CValley E n PEq Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B) :=
  let hcl := envClosed_of_envWfT hW
  let hA := (convEnds hW hΓ cA).1
  let hA' := (convEnds hW hΓ cA).2.1
  let hv := vv.left.leftTyped L hΓ
  let hv' := vv.right.leftTyped L hΓ
  let hvc := vv.left.rightTyped
  let hΓc := CtxWfT.letBinding Γ A u vv.centre hΓ hA hvc
  let hb'c := vb.right.leftTyped L hΓc
  let ⟨w, hBc⟩ := tySort hW hΓc hb'c
  let ccV := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA (.refl Γ A _ hA)
    hv (.symm _ _ _ _ vv.left.toConvT)
  let ccV' := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA (.refl Γ A _ hA)
    hv' (.symm _ _ _ _ vv.right.toConvT)
  let hv'A' := HasTyT.conv Γ v' A A' u hv' cA
  let ccAnn := CtxConvT.letBinding (ctxConvT_refl Γ) hA hA' cA hv'A'
    (.symm _ _ _ _ vv.right.toConvT)
  let hb'Ann := hasTyT_ctx hcl ccAnn hb'c
  let ann := letAnnotationStep (PEq := PEq) hW hΓ hA' (.symm _ _ _ _ cA) hv'A' hb'Ann
  let right₀ := (CStar.ofStep L hΓ ann).trans (letArmToCentre hW L hΓ hA vv.right vb.right)
  let cIdx := convT_inst0_valueSortLet hA hv' hv (hasTyT_ctx hcl ccV' hBc)
    (hasTyT_ctx hcl ccV hBc) (.symm _ _ _ _ vv.toConvT)
  ⟨.letE A vv.centre vb.centre,
    letArmToCentre hW L hΓ hA vv.left vb.left,
    right₀.reindex (.of Γ _ _ w cIdx)⟩

#print axioms letBodyStar
#print axioms letValueStar
#print axioms letAnnotationStep
#print axioms letArmToCentre
#print axioms valley_let_at_value_centre

end Rcic.Declarative.NativeValleys
