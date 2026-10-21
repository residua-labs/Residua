import rcic.RcicNativeWallContext
import rcic.RcicNativeWallLetStars

/-!
# Native valleys from the certified diamond alone

The induction subject is the ORIGINAL `ConvT`, with an independently varying
target context package. The package has concrete identity, assumption, and
changed-let constructors. A local zeta consumes its stored target lookup
valley. A let node recurses on its original body under the common VALUE.

Thus `LetValley` is constructed from `CDiamond`; it is not an independent
input of this producer. This does not construct `CDiamond`, `OpenRows`,
retyping, or a generic bridge for arbitrary certified body stars.

Dependency pin: `4d3b74e05355f478a03a44166399794a0a68d2a4`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Consume a stored target lookup valley directly. The variable's own
target-context unfolding is certified by native local zeta. No diamond or
recursive conversion-producer call is needed in this leaf. -/
def valley_zetaLocal_lookup (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {i : Nat} {A v v' : Expr Nat}
    (hval : lookupValue Γ i = some v') (hty : lookupType Γ i = some A)
    (V : CValley E n PEq Γ v v' A) :
    CValley E n PEq Γ (.bvar i) v A := by
  have hv' := V.right.leftTyped L hΓ
  let s : CStep E n PEq Γ (.bvar i) v' A := by
    obtain ⟨A₀, v₀, hget, hveq⟩ := lookupValue_inv hval
    subst hveq
    exact
      ⟨.bvarZeta Γ i A₀ v₀ v₀ A hget
          (.refl _ v₀ A₀ (ctxWfTLookupValueAtDrop hΓ i hget))
          (.bvar Γ i A hty) hv',
        .bvarZeta (.zetaLocal Γ i A _ hval hty hv')
          (.refl (.refl _ v₀ A₀ (ctxWfTLookupValueAtDrop hΓ i hget)))⟩
  exact ⟨V.centre, .tail s V.right, V.left⟩

/-- Induction on the original native conversion, generalized over a value-only
target context. Every recursive call below is on an actual proper `ConvT`
child. Transported conversions and newly built context packages are auxiliary
data, never recursive subjects. The diamond is a fixed external input. -/
def valleyOf_context (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) :
    {Γ : LCtx} → {a b T : Expr Nat} → (c : ConvT E n Γ a b T) →
    {Γ' : LCtx} → CtxWfT E n Γ' → ContextAudit.Pack E n PEq Γ Γ' →
    CValley E n PEq Γ' a b T
  | _, _, _, _, .refl _ _ _ h, _, _, K =>
      .refl (hasTyT_ctx (envClosed_of_envWfT hW) K.native h)
  | _, _, _, _, .symm _ _ _ _ h, _, hΓ', K =>
      (valleyOf_context hW L D h hΓ' K).symm
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, _, hΓ', K =>
      CValley.trans D L hΓ'
        (valleyOf_context hW L D h₁ hΓ' K)
        (valleyOf_context hW L D h₂ hΓ' K)
  | _, _, _, _, .beta _ A _ _ _ _ hA hb ha, _, hΓ', K =>
      valley_beta hW L hΓ'
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hA)
        (hasTyT_ctx (envClosed_of_envWfT hW) (.same (.assumption A) K.native) hb)
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native ha)
  | _, _, _, _, .zeta _ A v _ _ _ hA hv hb, _, hΓ', K =>
      valley_zeta hW L hΓ'
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hA)
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hv)
        (hasTyT_ctx (envClosed_of_envWfT hW) (.same (.letBinding A v) K.native) hb)
  | _, _, _, _, .zetaLocal _ _ _ _ hval hty _, _, hΓ', K =>
      let ⟨_, hval', V⟩ := K.values hval hty
      valley_zetaLocal_lookup L hΓ' hval' (K.typeAt hty) V
  | _, _, _, _, .delta _ _ _ _ _ hres hbody htr hlen hwf hb, _, hΓ', K =>
      valley_delta L hΓ' hres hbody htr hlen hwf
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hb)
  | _, _, _, _, .iota _ _ _ _ h hl hr, _, hΓ', K =>
      valley_iota L hΓ' h
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hl)
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hr)
  | _, _, _, _, .lit _ _ _ _ h hexp, _, hΓ', K =>
      valley_lit L hΓ' h (hasTyT_ctx (envClosed_of_envWfT hW) K.native hexp)
  | _, _, _, _, .app _ _ _ _ _ _ _ h₁ h₂, _, hΓ', K =>
      valley_app hW L hΓ'
        (convT_ctx (envClosed_of_envWfT hW) K.native h₁)
        (convT_ctx (envClosed_of_envWfT hW) K.native h₂)
        (valleyOf_context hW L D h₁ hΓ' K)
        (valleyOf_context hW L D h₂ hΓ' K)
  | _, _, _, _, .lam _ A _ _ _ _ u hA hb, _, hΓ', K =>
      let hcl := envClosed_of_envWfT hW
      let cA := convT_ctx hcl K.native hA
      let cb := convT_ctx hcl (.same (.assumption A) K.native) hb
      let hΓA := CtxWfT.assumption _ A u hΓ' (convEnds hW hΓ' cA).1
      valley_lam hW L hΓ' cA cb
        (valleyOf_context hW L D hb hΓA (K.assumption hcl L A))
  | _, _, _, _, .pi _ A _ _ _ _ _ hA hB, _, hΓ', K =>
      valley_pi hW L hΓ'
        (convT_ctx (envClosed_of_envWfT hW) K.native hA)
        (convT_ctx (envClosed_of_envWfT hW) (.same (.assumption A) K.native) hB)
  | _, _, _, _, .letE _ A _ _ _ _ _ _ u hA hv hb, _, hΓ', K =>
      let hcl := envClosed_of_envWfT hW
      let cA := convT_ctx hcl K.native hA
      let hA' := (convEnds hW hΓ' cA).1
      let vv := valleyOf_context hW L D hv hΓ' K
      let hΓc := CtxWfT.letBinding _ A u vv.centre hΓ' hA' vv.left.rightTyped
      let Kc := K.letBinding hcl L hA' vv.left
      let vb := valleyOf_context hW L D hb hΓc Kc
      valley_let_at_value_centre hW L hΓ' cA vv vb
  | _, _, _, _, .sorts _ _ _ h, _, hΓ', _ => valley_sorts hW L hΓ' h
  | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h, _, hΓ', _ =>
      valley_consts hW L hΓ' hres hlen hwf hwf' h
  | _, _, _, _, .eta _ _ _ _ h, _, hΓ', K =>
      valley_eta hW L hΓ' (hasTyT_ctx (envClosed_of_envWfT hW) K.native h)
  | _, _, _, _, .irr _ _ _ _ hP hp hq, _, hΓ', K =>
      CValley.ofStep L hΓ' (CStep.irr L
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hP)
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hp)
        (hasTyT_ctx (envClosed_of_envWfT hW) K.native hq))
  | _, _, _, _, .tyConv _ _ _ _ _ u h hA, _, hΓ', K =>
      (valleyOf_context hW L D h hΓ' K).reindex
        (.of _ _ _ u (convT_ctx (envClosed_of_envWfT hW) K.native hA))
termination_by _ _ _ _ c _ _ _ => sizeOf c
decreasing_by all_goals (simp; omega)

/-- Actual total native valley producer from the SAME-INDEX diamond alone.
The identity context package is constructed, not supplied as an oracle. -/
def valleyOf_diamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf_context hW L D c hΓ (ContextAudit.Pack.refl (envClosed_of_envWfT hW) L hΓ)

/-- The branch's original `LetValley` interface is constructed from D.
Its supplied value valley determines the common value component; the original body conversion
is processed under that common value. The old-context body valley need not
be transported. This statement does not assert an arbitrary-star LetBridge. -/
def letValley_of_diamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) : LetValley E n PEq :=
  fun {Γ} hΓ {A _ _ _ _ _ _} {u} cA _cv cb vv _vb =>
    let hcl := envClosed_of_envWfT hW
    let hA := (convEnds hW hΓ cA).1
    let hΓc := CtxWfT.letBinding Γ A u vv.centre hΓ hA vv.left.rightTyped
    let K := ContextAudit.Pack.refl hcl L hΓ
    let Kc := K.letBinding hcl L hA vv.left
    valley_let_at_value_centre hW L hΓ cA vv
      (valleyOf_context hW L D cb hΓc Kc)

theorem nativeConvValleys_of_diamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : CDiamond E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  (valleyOf_diamond hW L D hΓ c).exists_join

#print axioms valley_zetaLocal_lookup
#print axioms valleyOf_context
#print axioms valleyOf_diamond
#print axioms letValley_of_diamond
#print axioms nativeConvValleys_of_diamond

end Rcic.Declarative.NativeValleys
