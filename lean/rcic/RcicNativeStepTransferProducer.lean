import rcic.RcicNativeWallProducer
import rcic.RcicNativeStepTransfer

/-!
# Native valley production from star confluence

The landed producer uses its `CDiamond` argument only to compose valleys at
`ConvT.trans`. This module exposes the weaker operation actually consumed
there: confluence of existing certified stars at one fixed index.

`valleyTrans_of_confluence` constructs the composite from that operation.
`valleyOf_context_confluence` follows the original `ConvT` derivation and
reuses the landed context package and all landed constructor builders.
Only its transitivity case has a different operation. Its original-body
let recursion continues to use the concrete changed-value package.

This module adds no alternate `Deco`, `CStep`, `CStar`, `CValley`, or `Pack`,
and does not change or redefine the landed `valleyOf_context`. The new
recursive dispatcher is necessary because that existing function fixes
`CDiamond` in its type. No supplied `LetValley` is needed.

`StarConfluence` is a premise of the generic consumer, not a theorem that
confluence is closed. The source-decoration repair bridge supplies it
conditionally from the coherent decorated diamond.

The final two declarations construct native valleys from
`CoherentDiamond` by that bridge. The current `CDiamondD`
assembler returns no joining-leg source interfaces or common target
decoration. It does not supply this stronger remaining premise.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StepTransferProducerAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The exact operation needed to compose native certified valleys.
Both input stars and both output legs retain their common index `T`.
This interface is stated using the landed `CStar` and `CValley`. -/
def StarConfluence (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b c T : Expr Nat},
    CStar E n PEq Γ a b T → CStar E n PEq Γ a c T →
    CValley E n PEq Γ b c T

/-- Compose the two existing valleys through confluence at their shared
middle term. Only the resulting joining stars are appended. -/
def valleyTrans_of_confluence (F : StarConfluence E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (v₁ : CValley E n PEq Γ a b T) (v₂ : CValley E n PEq Γ b c T) :
    CValley E n PEq Γ a c T :=
  let j := F hΓ v₁.right v₂.left
  ⟨j.centre, v₁.left.trans j.left, v₂.right.trans j.right⟩

/-- Induction on the original native conversion, generalized over a value-only
target context. Every recursive call below is on an actual proper `ConvT`
child. Transported conversions and newly built context packages are auxiliary
data, never recursive subjects. Star confluence is a fixed external input. -/
def valleyOf_context_confluence (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) :
    {Γ : LCtx} → {a b T : Expr Nat} → (c : ConvT E n Γ a b T) →
    {Γ' : LCtx} → CtxWfT E n Γ' → ContextAudit.Pack E n PEq Γ Γ' →
    CValley E n PEq Γ' a b T
  | _, _, _, _, .refl _ _ _ h, _, _, K =>
      .refl (hasTyT_ctx (envClosed_of_envWfT hW) K.native h)
  | _, _, _, _, .symm _ _ _ _ h, _, hΓ', K =>
      (valleyOf_context_confluence hW L F h hΓ' K).symm
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, _, hΓ', K =>
      valleyTrans_of_confluence F hΓ'
        (valleyOf_context_confluence hW L F h₁ hΓ' K)
        (valleyOf_context_confluence hW L F h₂ hΓ' K)
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
        (valleyOf_context_confluence hW L F h₁ hΓ' K)
        (valleyOf_context_confluence hW L F h₂ hΓ' K)
  | _, _, _, _, .lam _ A _ _ _ _ u hA hb, _, hΓ', K =>
      let hcl := envClosed_of_envWfT hW
      let cA := convT_ctx hcl K.native hA
      let cb := convT_ctx hcl (.same (.assumption A) K.native) hb
      let hΓA := CtxWfT.assumption _ A u hΓ' (convEnds hW hΓ' cA).1
      valley_lam hW L hΓ' cA cb
        (valleyOf_context_confluence hW L F hb hΓA (K.assumption hcl L A))
  | _, _, _, _, .pi _ A _ _ _ _ _ hA hB, _, hΓ', K =>
      valley_pi hW L hΓ'
        (convT_ctx (envClosed_of_envWfT hW) K.native hA)
        (convT_ctx (envClosed_of_envWfT hW) (.same (.assumption A) K.native) hB)
  | _, _, _, _, .letE _ A _ _ _ _ _ _ u hA hv hb, _, hΓ', K =>
      let hcl := envClosed_of_envWfT hW
      let cA := convT_ctx hcl K.native hA
      let hA' := (convEnds hW hΓ' cA).1
      let vv := valleyOf_context_confluence hW L F hv hΓ' K
      let hΓc := CtxWfT.letBinding _ A u vv.centre hΓ' hA' vv.left.rightTyped
      let Kc := K.letBinding hcl L hA' vv.left
      let vb := valleyOf_context_confluence hW L F hb hΓc Kc
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
      (valleyOf_context_confluence hW L F h hΓ' K).reindex
        (.of _ _ _ u (convT_ctx (envClosed_of_envWfT hW) K.native hA))
termination_by _ _ _ _ c _ _ _ => sizeOf c
decreasing_by all_goals (simp; omega)

/-- Actual total native valley producer from same-index star confluence.
The identity context package is constructed, not supplied as an oracle. -/
def valleyOf_confluence (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf_context_confluence hW L F c hΓ (ContextAudit.Pack.refl (envClosed_of_envWfT hW) L hΓ)

/-- Consume actual source repair and coherent confluence through the generic
producer. `CoherentDiamond` remains an explicit undischarged premise; no
ordinary `CDiamond`, retyping, type uniqueness, or Pi-row is supplied. -/
def valleyOf_coherentDiamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : DecoStarAudit.CoherentDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf_confluence hW L
    (StepTransferAudit.confluenceOf_coherentDiamond hW L D) hΓ c

/-- Forget the produced certificates to obtain the existing native-valley
specification, still conditional on the displayed coherent diamond. -/
theorem nativeConvValleys_of_coherentDiamond (hW : EnvWfT E)
    (L : LeafIface E n PEq) (D : DecoStarAudit.CoherentDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  (valleyOf_coherentDiamond hW L D hΓ c).exists_join

#print axioms StarConfluence
#print axioms valleyTrans_of_confluence
#print axioms valleyOf_context_confluence
#print axioms valleyOf_confluence
#print axioms valleyOf_coherentDiamond
#print axioms nativeConvValleys_of_coherentDiamond

end Rcic.Declarative.NativeValleys.StepTransferProducerAudit
