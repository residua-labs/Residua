import rcic.RcicNativeValleyFronts
import rcic.RcicSubstT

/-!
# RcicNativeValleyLamEta — the `lam × eta` row
(Wall 1, `NativeConvValleys`, piece 14)

`OpenRows.lam_eta` (`RcicNativeValleyAssemble`): the λ node steps the η-expansion
`lam A (app (lift 0 1 f) (bvar 0))` to `lam A' body'` (domain by `ConvT`, body by a step under
`A`), the η node contracts it to a reduct `f'` of `f`. Recursion on the certificate of the
body step, its source read through an equation, the index chain to `B₁` accumulated:

* `refl` — CLOSED: the stepped λ is the η-expansion of `f` at the converted annotation `A'`,
  which η-contracts to `f'` (`etaAtConverted`: `f ⇒ f'` moved to `Π A' B₂` by `ConvT.pi`, the
  expansion typed at `Π A' B₂` by weakening `f`'s typing under `A'` — `hasTyTWeaken` — and
  `instantiate_bvar_lift`), the result presented at the λ node's index through `Retype`.
* `peq` (the body is a proof) — CLOSED modulo `PropAlign`: `B₀ : Prop` transfers to the body's
  other type `B₁`, so `Π A B₁ : Prop` (`eqN_imax_zero_right`), which transfers to the
  expansion's other type `Π A B₂`; the join is the stepped λ, reached from `f'` by one
  irrelevance step (the stepped λ typed at `Π A B₂` through `Retype` of the λ node).
* `conv` — peeled.
* `app`, `beta`, `iotaSpine` — the fronts `LamEtaApp`, `LamEtaBeta`, `LamEtaIota`.
* every other root is refuted by the source shape.

`lam_eta_of` has exactly the field's statement.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The η-contraction of the η-expansion of `f` at the CONVERTED annotation `A'`, presented
    at `Π A B₂`: `f ⇒ f'` moved to `Π A' B₂`, the expansion typed there by weakening. -/
def etaAtConverted (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' f f' B₂ : Expr Nat} {u : Level} (hc : ConvT E n Γ A A' (.sort u))
    {hf : ParRedT PEq E n Γ f f' (.pi A B₂)} (cf : Certified hf) :
    CStep E n PEq Γ (.lam A' (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B₂) :=
  let hcl := envClosed_of_envWfT hW
  let hA' : HasTyT E n Γ A' (.sort u) := (convEnds hW hΓ hc).2.1
  let hfΓ : HasTyT E n Γ f (.pi A B₂) := parRedT_hasTy_left L.typed hΓ hf
  match hasTyTInv_pi (tySort hW hΓ hfΓ).2 rfl with
  | ⟨_, v₂, _, hB₂v, _⟩ =>
    let hcpi : ConvT E n Γ (.pi A B₂) (.pi A' B₂) (.sort (.imax u v₂)) :=
      .pi Γ A A' B₂ B₂ u v₂ hc (.refl _ B₂ _ hB₂v)
    let hf' : CStep E n PEq Γ f f' (.pi A' B₂) :=
      (⟨hf, cf⟩ : CStep E n PEq Γ f f' (.pi A B₂)).reindex (.of _ _ _ _ hcpi)
    let hfA' : HasTyT E n Γ f (.pi A' B₂) := hf'.leftTyped L hΓ
    let hliftf : HasTyT E n (.assumption A' :: Γ) (lift 0 1 f) (lift 0 1 (.pi A' B₂)) :=
      hasTyTWeaken (.assumption A') hcl (c := 0) hfA'
    let hbv0 : HasTyT E n (.assumption A' :: Γ) (.bvar 0) (lift 0 1 A') := .bvar _ 0 _ rfl
    let happ : HasTyT E n (.assumption A' :: Γ) (.app (lift 0 1 f) (.bvar 0))
        (instantiate0 (.bvar 0) (lift 1 1 B₂)) :=
      .app _ (lift 0 1 f) (.bvar 0) (lift 0 1 A') (lift 1 1 B₂) hliftf hbv0
    let e : instantiate0 (.bvar 0) (lift 1 1 B₂) = B₂ := instantiate_bvar_lift B₂ 0
    let happ' : HasTyT E n (.assumption A' :: Γ) (.app (lift 0 1 f) (.bvar 0)) B₂ := e ▸ happ
    let hl' : HasTyT E n Γ (.lam A' (.app (lift 0 1 f) (.bvar 0))) (.pi A' B₂) :=
      .lam Γ A' u _ B₂ hA' happ'
    let cert : ConvT E n Γ (.lam A' (.app (lift 0 1 f) (.bvar 0))) f' (.pi A' B₂) :=
      .trans _ _ _ _ _ (.eta Γ f A' B₂ hfA') hf'.toConvT
    let step : CStep E n PEq Γ (.lam A' (.app (lift 0 1 f) (.bvar 0))) f' (.pi A' B₂) :=
      ⟨.eta Γ f f' A' B₂ hf'.step hl', .eta cert hf'.cert⟩
    step.reindex (.of _ _ _ _ (.symm _ _ _ _ hcpi))

/-- The core of `lam × eta`: recursion on the certificate of the body step, the source read
    through `x = app (lift 0 1 f) (bvar 0)`, the index chain `hcB` to the λ node's `B₁`. -/
def lamEtaCore (hW : EnvWfT E) (L : LeafIface E n PEq) (Rt : Retype E n PEq) (PA : PropAlign E n)
    (LA : LamEtaApp E n PEq) (LB : LamEtaBeta E n PEq) (LI : LamEtaIota E n PEq)
    {Γ : LCtx} {A A' f f' B₁ B₂ : Expr Nat} {u v : Level} (m : Nat) (ih : IHBelow E n PEq m) :
    {x body' B₀ : Expr Nat} → {hb : ParRedT PEq E n (.assumption A :: Γ) x body' B₀} →
    Certified hb → (D : LamEtaCtx E n PEq Γ A A' f f' body' B₁ B₂ u v) →
    x = .app (lift 0 1 f) (.bvar 0) → TyConvT E n (.assumption A :: Γ) B₀ B₁ →
    sizeOf hb + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, D, hx, _, _ => by
      subst hx
      have hf'ty : HasTyT E n Γ f' (.pi A B₂) := parRedT_hasTy_right L.typed D.hΓ D.hf
      exact ⟨f', Rt D.hΓ D.hrt (etaAtConverted hW L D.hΓ D.hc D.cf),
        ⟨.refl Γ f' _ hf'ty, .refl (.refl Γ f' _ hf'ty)⟩⟩
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, D, hx, hcB, _ => by
      subst hx
      have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u D.hΓ D.hA
      have hx₀ := (L.typed h).1
      have hx₁ : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) B₁ :=
        hasTyT_of_tyConv hx₀ hcB
      have hB₁0 : HasTyT E n (.assumption A :: Γ) B₁ (.sort .zero) := PA hΓ' hx₀ hx₁ (L.prop h)
      have hpi₁0 : HasTyT E n Γ (.pi A B₁) (.sort .zero) :=
        .conv Γ _ _ _ _ (.pi Γ A u B₁ .zero D.hA hB₁0)
          (.sorts Γ (.imax u .zero) .zero (eqN_imax_zero_right u))
      have hp : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₁) :=
        D.p0.leftTyped L D.hΓ
      have hpi₂0 : HasTyT E n Γ (.pi A B₂) (.sort .zero) := PA D.hΓ hp D.hl hpi₁0
      have hlam' : HasTyT E n Γ (.lam A' _) (.pi A B₂) := (Rt D.hΓ D.hl D.p0).rightTyped L D.hΓ
      have hf'ty : HasTyT E n Γ f' (.pi A B₂) := parRedT_hasTy_right L.typed D.hΓ D.hf
      exact ⟨.lam A' _, ⟨.refl Γ _ _ D.hrt, .refl (.refl Γ _ _ D.hrt)⟩,
        CStep.irr L hpi₂0 hf'ty hlam'⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hcT _ ch, D, hx, hcB, hsz =>
      lamEtaCore hW L Rt PA LA LB LI m ih ch D hx (.trans _ _ _ _ hcT hcB)
        (by simp at hsz; omega)
  | _, _, _, _, cb@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cg cx), D, hx, hcB,
      hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      exact LA D cb cg cx hcB m ih hsz
  | _, _, _, _, cb@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₀ cx), D, hx, hcB,
      hsz => by
      injection hx with h1 h2
      subst h2
      exact LB D h1.symm cb cb₀ cx hcB m ih hsz
  | _, _, _, _, cb@(@Certified.iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ cinner), D, hx, hcB, hsz => by
      subst hx
      exact LI D cb cinner hcB m ih hsz
  | _, _, _, _, .sortEq .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .consts .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .bvarZeta .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .delta .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .lam .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .pi .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .letE .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .zeta .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .lit .., _, hx, _, _ => nomatch hx
  | _, _, _, _, .eta .., _, hx, _, _ => nomatch hx

/-- `OpenRows.lam_eta` from the fronts: exactly the field's statement. -/
noncomputable def lam_eta_of (hW : EnvWfT E) (L : LeafIface E n PEq) (Rt : Retype E n PEq)
    (PA : PropAlign E n) (LA : LamEtaApp E n PEq) (LB : LamEtaBeta E n PEq)
    (LI : LamEtaIota E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' f body' B₁ f' B₂ : Expr Nat} {u v : Level}
    {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
    {hB : HasTyT E n (.assumption A :: Γ) B₁ (.sort v)}
    {hb : ParRedT PEq E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) body' B₁}
    {hrt : HasTyT E n Γ (.lam A' body') (.pi A B₁)}
    {hf : ParRedT PEq E n Γ f f' (.pi A B₂)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₂)},
    Certified (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
      hA hB hb hrt) →
    Certified (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl) →
    Certified hb → Certified hf →
    IHBelow E n PEq
      (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
        hA hB hb hrt) +
       sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl)) →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂) :=
  fun {Γ} hΓ {A A' f body' B₁ f' B₂ u v hc hA hB hb hrt hf hl} cp _ cb cf ih =>
    lamEtaCore hW L Rt PA LA LB LI _ ih cb
      ⟨hΓ, hc, hA, hB, hrt, hf, cf, hl,
        ⟨ParRedT.lam Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc hA hB hb hrt, cp⟩⟩
      rfl (.refl _ _) (by simp; omega)

end Rcic.Declarative.NativeValleys
