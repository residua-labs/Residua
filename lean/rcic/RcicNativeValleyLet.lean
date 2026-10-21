import rcic.RcicNativeValleyFronts

/-!
# RcicNativeValleyLet — the three `let` rows from the `let` diamond
(Wall 1, `NativeConvValleys`, piece 13)

`OpenRows.letE_letE`, `letE_zeta`, `zeta_zeta` (`RcicNativeValleyAssemble`): two steps out of
`letE A value body`, each stepping the value (at `A`) and the body under the SOURCE binding
`letBinding A value`. Every output must step its body under a STEPPED binding
(`ParRedT.letE` / `ParRedT.zeta` step the body under the source's own binding, here
`letBinding Aᵢ valueᵢ`), and a step under `letBinding A value` does not transport to
`letBinding A valueᵢ` (`bvarZeta` reads the stored value). So the three rows reduce to ONE
front, `LetJoin` (the diamond with its body legs under the two stepped bindings), plus:

* `CertLetAnnCtx` — the body legs come back under annotation `A`; the output node's binding
  carries the converted annotation `Aᵢ`;
* `CertSubstLet` (`RcicNativeValleyRows`) — the ζ outputs substitute the stepped value into the
  body leg (the let-hole mixed substitution, not discharged here).

The three rows are then compositional: `letSide` (a `letE` output), `zetaSide` (a substituted
output), `zetaLeg` (a `letE` input ζ-contracting onto the substituted join); every output is
realigned from `B[valueᵢ]` to the node's index `B[value]` by `convT_inst0_valueSortLet` with
the value child's certificate.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The index realignment of a `let` output: `B[value₁] ~ B[value]` at `B`'s sort, from the
    value child's certificate; `B` is sorted under both bindings (context conversion along the
    value certificate). -/
def letIdx (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value value₁ B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    {hv : ParRedT PEq E n Γ value value₁ A} (cv : Certified hv) :
    HasTyT E n (.letBinding A value₁ :: Γ) B (.sort w) ×'
      TyConvT E n Γ (instantiate0 value₁ B) (instantiate0 value B) :=
  let hcl := envClosed_of_envWfT hW
  let hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv
  let hval₁ : HasTyT E n Γ value₁ A := parRedT_hasTy_right L.typed hΓ hv
  let hctx : CtxConvT E n (.letBinding A value :: Γ) (.letBinding A value₁ :: Γ) :=
    .letBinding (ctxConvT_refl Γ) hA hA (.refl _ A _ hA) hval₁ cv.root
  let hB₁ : HasTyT E n (.letBinding A value₁ :: Γ) B (.sort w) := hasTyT_ctx hcl hctx hB
  ⟨hB₁, .of _ _ _ w (convT_inst0_valueSortLet hA hval₁ hval hB₁ hB (.symm _ _ _ _ cv.root))⟩

/-- A `letE` output from the joins: `letE A₁ value₁ body₁ ⇒ letE A v₃ b₃` at the node's index
    `B[value]`; the body leg is moved under the converted annotation (`CertLetAnnCtx`), the
    value leg to `A₁`. The join keeps the source annotation `A`. -/
def letSide (hW : EnvWfT E) (L : LeafIface E n PEq) (Lc : CertLetAnnCtx E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A₁ value value₁ v₃ body₁ b₃ B : Expr Nat} {u w : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    {hv : ParRedT PEq E n Γ value value₁ A} (cv : Certified hv)
    (pv : CStep E n PEq Γ value₁ v₃ A) (pb : CStep E n PEq (.letBinding A value₁ :: Γ) body₁ b₃ B) :
    CStep E n PEq Γ (.letE A₁ value₁ body₁) (.letE A v₃ b₃) (instantiate0 value B) :=
  let hcl := envClosed_of_envWfT hW
  let ⟨hB₁, hidx⟩ := letIdx hW L hΓ hA hB cv
  let hA₁ : HasTyT E n Γ A₁ (.sort u) := (convEnds hW hΓ hc).2.1
  let hval₁ : HasTyT E n Γ value₁ A := pv.leftTyped L hΓ
  let hval₁' : HasTyT E n Γ value₁ A₁ := .conv Γ value₁ A A₁ u hval₁ hc
  let hctxA : CtxConvT E n (.letBinding A value₁ :: Γ) (.letBinding A₁ value₁ :: Γ) :=
    .letBinding (ctxConvT_refl Γ) hA hA₁ hc hval₁' (.refl _ value₁ A hval₁)
  let hB₁' : HasTyT E n (.letBinding A₁ value₁ :: Γ) B (.sort w) := hasTyT_ctx hcl hctxA hB₁
  let pb' : CStep E n PEq (.letBinding A₁ value₁ :: Γ) body₁ b₃ B := Lc hA hA₁ hc hval₁ pb
  let pv' : CStep E n PEq Γ value₁ v₃ A₁ := pv.reindex (.of _ _ _ u hc)
  let hTy : HasTyT E n Γ (instantiate0 value₁ B) (.sort w) := by
    have h0 := hasTyT_substLet0_of_envWfT hW hB₁' hval₁'
    simpa only [instantiate0, instantiate] using h0
  let cert : ConvT E n Γ (.letE A₁ value₁ body₁) (.letE A v₃ b₃) (instantiate0 value₁ B) :=
    .letE Γ A₁ A value₁ v₃ body₁ b₃ B u (.symm _ _ _ _ hc) pv'.toConvT pb'.toConvT
  let step : CStep E n PEq Γ (.letE A₁ value₁ body₁) (.letE A v₃ b₃) (instantiate0 value₁ B) :=
    ⟨.letE Γ A₁ A value₁ v₃ body₁ b₃ B u w (.symm _ _ _ _ hc) hA₁ pv'.step hB₁' hTy pb'.step
      (convEnds hW hΓ cert).2.1, .letE cert pv'.cert pb'.cert⟩
  step.reindex hidx

/-- A substituted output from the joins: `body₁[value₁] ⇒ b₃[v₃]` at `B[value]` by the
    let-hole mixed substitution, realigned by the value child's certificate. -/
def zetaSide (hW : EnvWfT E) (L : LeafIface E n PEq) (SL : CertSubstLet E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A value value₁ v₃ body₁ b₃ B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    {hv : ParRedT PEq E n Γ value value₁ A} (cv : Certified hv)
    (pv : CStep E n PEq Γ value₁ v₃ A) (pb : CStep E n PEq (.letBinding A value₁ :: Γ) body₁ b₃ B) :
    CStep E n PEq Γ (instantiate0 value₁ body₁) (instantiate0 v₃ b₃) (instantiate0 value B) :=
  let ⟨_, hidx⟩ := letIdx hW L hΓ hA hB cv
  (SL hΓ hA (pv.leftTyped L hΓ) pb pv).reindex hidx

/-- A `letE` input ζ-contracting onto the substituted join: `letE A₁ value₁ body₁ ⇒ b₃[v₃]`
    at `B[value]` (`ParRedT.zeta` under the converted annotation; certificate `ConvT.zeta`
    then the let-hole mixed substitution's). -/
def zetaLeg (hW : EnvWfT E) (L : LeafIface E n PEq) (Lc : CertLetAnnCtx E n PEq)
    (SL : CertSubstLet E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ value value₁ v₃ body₁ b₃ B : Expr Nat} {u w : Level}
    (hc : ConvT E n Γ A A₁ (.sort u)) (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
    {hv : ParRedT PEq E n Γ value value₁ A} (cv : Certified hv)
    (pv : CStep E n PEq Γ value₁ v₃ A) (pb : CStep E n PEq (.letBinding A value₁ :: Γ) body₁ b₃ B) :
    CStep E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 v₃ b₃) (instantiate0 value B) :=
  let hcl := envClosed_of_envWfT hW
  let ⟨hB₁, hidx⟩ := letIdx hW L hΓ hA hB cv
  let hA₁ : HasTyT E n Γ A₁ (.sort u) := (convEnds hW hΓ hc).2.1
  let hval₁ : HasTyT E n Γ value₁ A := pv.leftTyped L hΓ
  let hval₁' : HasTyT E n Γ value₁ A₁ := .conv Γ value₁ A A₁ u hval₁ hc
  let hctxA : CtxConvT E n (.letBinding A value₁ :: Γ) (.letBinding A₁ value₁ :: Γ) :=
    .letBinding (ctxConvT_refl Γ) hA hA₁ hc hval₁' (.refl _ value₁ A hval₁)
  let hB₁' : HasTyT E n (.letBinding A₁ value₁ :: Γ) B (.sort w) := hasTyT_ctx hcl hctxA hB₁
  let pb' : CStep E n PEq (.letBinding A₁ value₁ :: Γ) body₁ b₃ B := Lc hA hA₁ hc hval₁ pb
  let pv' : CStep E n PEq Γ value₁ v₃ A₁ := pv.reindex (.of _ _ _ u hc)
  let hΓ₁ : CtxWfT E n (.letBinding A₁ value₁ :: Γ) := .letBinding Γ A₁ u value₁ hΓ hA₁ hval₁'
  let hbody₁ : HasTyT E n (.letBinding A₁ value₁ :: Γ) body₁ B := pb'.leftTyped L hΓ₁
  let hTy : HasTyT E n Γ (instantiate0 value₁ B) (.sort w) := by
    have h0 := hasTyT_substLet0_of_envWfT hW hB₁' hval₁'
    simpa only [instantiate0, instantiate] using h0
  let sub := SL hΓ hA₁ hval₁' pb' pv'
  let cert : ConvT E n Γ (.letE A₁ value₁ body₁) (instantiate0 v₃ b₃) (instantiate0 value₁ B) :=
    .trans _ _ _ _ _ (.zeta Γ A₁ value₁ body₁ B u hA₁ hval₁' hbody₁) sub.toConvT
  let step : CStep E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 v₃ b₃) (instantiate0 value₁ B) :=
    ⟨.zeta Γ A₁ value₁ v₃ body₁ b₃ B u w hA₁ pv'.step hB₁' hTy pb'.step (convEnds hW hΓ cert).2.1,
      .zeta cert pv'.cert pb'.cert⟩
  step.reindex hidx

/-- `OpenRows.letE_letE` from `LetJoin` and `CertLetAnnCtx`: exactly the field's statement. -/
noncomputable def letE_letE_of (hW : EnvWfT E) (L : LeafIface E n PEq) (Lc : CertLetAnnCtx E n PEq)
    (LJ : LetJoin E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A A₁ A₂ value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    {hc₁ : ConvT E n Γ A A₁ (.sort u₁)} {hA₁ : HasTyT E n Γ A (.sort u₁)}
    {hv₁ : ParRedT PEq E n Γ value value₁ A}
    {hB₁ : HasTyT E n (.letBinding A value :: Γ) B₁ (.sort w₁)}
    {hTy₁ : HasTyT E n Γ (instantiate0 value B₁) (.sort w₁)}
    {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁}
    {hrt₁ : HasTyT E n Γ (.letE A₁ value₁ body₁) (instantiate0 value B₁)}
    {hc₂ : ConvT E n Γ A A₂ (.sort u₂)} {hA₂ : HasTyT E n Γ A (.sort u₂)}
    {hv₂ : ParRedT PEq E n Γ value value₂ A}
    {hB₂ : HasTyT E n (.letBinding A value :: Γ) B₂ (.sort w₂)}
    {hTy₂ : HasTyT E n Γ (instantiate0 value B₂) (.sort w₂)}
    {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂}
    {hrt₂ : HasTyT E n Γ (.letE A₂ value₂ body₂) (instantiate0 value B₂)},
    Certified (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) →
    Certified (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
      hB₂ hTy₂ hb₂ hrt₂) →
    Certified hv₁ → Certified hb₁ → Certified hv₂ → Certified hb₂ →
    IHBelow E n PEq
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
        hB₂ hTy₂ hb₂ hrt₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂) :=
  fun {Γ} hΓ {A A₁ A₂ value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hc₁ hA₁ hv₁ hB₁ hTy₁
      hb₁ hrt₁ hc₂ hA₂ hv₂ hB₂ hTy₂ hb₂ hrt₂} _ _ cv₁ cb₁ cv₂ cb₂ ih =>
    let hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
    let ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ := LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ _ ih (by simp; omega)
    ⟨.letE A v₃ b₃, letSide hW L Lc hΓ hc₁ hA₁ hB₁ cv₁ pv₁ pb₁,
      letSide hW L Lc hΓ hc₂ hA₂ hB₂ cv₂ pv₂ pb₂⟩

/-- `OpenRows.letE_zeta` from `LetJoin`, `CertLetAnnCtx` and `CertSubstLet`: the `letE` input
    ζ-contracts onto the substituted join; exactly the field's statement. -/
noncomputable def letE_zeta_of (hW : EnvWfT E) (L : LeafIface E n PEq) (Lc : CertLetAnnCtx E n PEq)
    (SL : CertSubstLet E n PEq) (LJ : LetJoin E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A A₁ value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    {hc₁ : ConvT E n Γ A A₁ (.sort u₁)} {hA₁ : HasTyT E n Γ A (.sort u₁)}
    {hv₁ : ParRedT PEq E n Γ value value₁ A}
    {hB₁ : HasTyT E n (.letBinding A value :: Γ) B₁ (.sort w₁)}
    {hTy₁ : HasTyT E n Γ (instantiate0 value B₁) (.sort w₁)}
    {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁}
    {hrt₁ : HasTyT E n Γ (.letE A₁ value₁ body₁) (instantiate0 value B₁)}
    {hA₂ : HasTyT E n Γ A (.sort u₂)} {hv₂ : ParRedT PEq E n Γ value value₂ A}
    {hB₂ : HasTyT E n (.letBinding A value :: Γ) B₂ (.sort w₂)}
    {hTy₂ : HasTyT E n Γ (instantiate0 value B₂) (.sort w₂)}
    {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂}
    {hred₂ : HasTyT E n Γ (instantiate0 value₂ body₂) (instantiate0 value B₂)},
    Certified (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) →
    Certified (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    Certified hv₁ → Certified hb₁ → Certified hv₂ → Certified hb₂ →
    IHBelow E n PEq
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂) :=
  fun {Γ} hΓ {A A₁ value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hc₁ hA₁ hv₁ hB₁ hTy₁ hb₁
      hrt₁ hA₂ hv₂ hB₂ hTy₂ hb₂ hred₂} _ _ cv₁ cb₁ cv₂ cb₂ ih =>
    let hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
    let ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ := LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ _ ih (by simp; omega)
    ⟨instantiate0 v₃ b₃, zetaLeg hW L Lc SL hΓ hc₁ hA₁ hB₁ cv₁ pv₁ pb₁,
      zetaSide hW L SL hΓ hA₂ hB₂ cv₂ pv₂ pb₂⟩

/-- `OpenRows.zeta_zeta` from `LetJoin` and `CertSubstLet`: exactly the field's statement. -/
noncomputable def zeta_zeta_of (hW : EnvWfT E) (L : LeafIface E n PEq) (SL : CertSubstLet E n PEq)
    (LJ : LetJoin E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    {hA₁ : HasTyT E n Γ A (.sort u₁)} {hv₁ : ParRedT PEq E n Γ value value₁ A}
    {hB₁ : HasTyT E n (.letBinding A value :: Γ) B₁ (.sort w₁)}
    {hTy₁ : HasTyT E n Γ (instantiate0 value B₁) (.sort w₁)}
    {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁}
    {hred₁ : HasTyT E n Γ (instantiate0 value₁ body₁) (instantiate0 value B₁)}
    {hA₂ : HasTyT E n Γ A (.sort u₂)} {hv₂ : ParRedT PEq E n Γ value value₂ A}
    {hB₂ : HasTyT E n (.letBinding A value :: Γ) B₂ (.sort w₂)}
    {hTy₂ : HasTyT E n Γ (instantiate0 value B₂) (.sort w₂)}
    {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂}
    {hred₂ : HasTyT E n Γ (instantiate0 value₂ body₂) (instantiate0 value B₂)},
    Certified (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
      hb₁ hred₁) →
    Certified (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    Certified hv₁ → Certified hb₁ → Certified hv₂ → Certified hb₂ →
    IHBelow E n PEq
      (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
        hb₁ hred₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (instantiate0 value₁ body₁) (instantiate0 value₂ body₂)
      (instantiate0 value B₁) (instantiate0 value B₂) :=
  fun {Γ} hΓ {A value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hA₁ hv₁ hB₁ hTy₁ hb₁ hred₁
      hA₂ hv₂ hB₂ hTy₂ hb₂ hred₂} _ _ cv₁ cb₁ cv₂ cb₂ ih =>
    let hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
    let ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ := LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ _ ih (by simp; omega)
    ⟨instantiate0 v₃ b₃, zetaSide hW L SL hΓ hA₁ hB₁ cv₁ pv₁ pb₁,
      zetaSide hW L SL hΓ hA₂ hB₂ cv₂ pv₂ pb₂⟩

end Rcic.Declarative.NativeValleys
