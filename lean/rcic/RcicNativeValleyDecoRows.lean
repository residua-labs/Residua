import rcic.RcicNativeValleyDecoBook
import rcic.RcicNativeValleyLevels
import rcic.RcicNativeValleyAppBeta
import rcic.RcicNativeValleyLamEta
import rcic.RcicNativeValleyIota
import rcic.RcicNativeValleyLet
import rcic.RcicNativeValleyEtaLeaf
import rcic.RcicNativeWallProofRows

/-!
# RcicNativeValleyDecoRows — `CR_D`: the decorated diamond rows
(Wall 1, `NativeConvValleys`, `NATIVE_VALLEYS_STATUS.md` §9c)

Under the invariant of the **decorated diamond** (`CR_D`), two certified steps `p` and `q` out of
a common term `b` share their source decoration:
```
stepDeco L p = stepDeco L q
```
By `uniqStepD` (`RcicNativeValleyDecoBook`), decoration agreement immediately gives an index
conversion chain `TyConvT E n Γ T₁ T₂` between the two steps' indices without consulting `Retype`,
`PropAlign`, or `Π-injectivity`. This module constructs the `CR_D` rows and proves their
front-elimination properties:

1. **Equivalence of `CDiamondD` and `CoreDiamondD`**:
   Because `stepDeco L p = stepDeco L q` implies `TyConvT E n Γ T₁ T₂` (`uniqStepD`) and
   `CStep.reindex` preserves `stepDeco` (`stepDeco_reindex`), the same-index decorated diamond
   `CDiamondD` and the independent-index decorated diamond `CoreDiamondD` are equivalent under
   `EnvWfT E` (`cdiamondD_of_coreDiamondD`, `coreDiamondD_of_cdiamondD`).
2. **Generic rows (`join_refl_deco`, `join_peq_deco`)**:
   Closed unconditionally under `EnvWfT E` without `Retype`, `PropAlign`, or `ZeroSortCoherence`,
   using `retypeD` and `ProofSourceAudit.join_peq_connected` fed by `uniqStepD`.
3. **Congruence and β² rows (`row_app_app_deco`, `row_lam_lam_deco`, `row_beta_beta_deco`)**:
   At `app × app`, `Deco.app.inj` propagates decoration agreement to both the function children
   (`stepDeco L hf₁ = stepDeco L hf₂`) and the argument children
   (`stepDeco L ha₁ = stepDeco L ha₂`), so `IHBelowD` applies directly to the children via
   `row_app_app`. Likewise at `lam × lam` (`Deco.lam.inj`) and `beta × beta`
   (`Deco.app.inj` + `Deco.lam.inj`).
4. **`app × beta` under `CR_D` (`argJoin_deco`, `appBetaCore_deco`, `app_beta_deco`)**:
   `Deco.app.inj` forces the `app` node's codomain `B'` to equal the `beta` node's codomain `B`
   syntactically (`B' = B`), and forces the argument children `ha` (at `A'`) and `ha₂` (at `A`) to
   share their source decoration (`stepDeco L ha = stepDeco L ha₂`). Hence `uniqStepD` supplies
   `TyConvT E n Γ A' A` directly (`argJoin_deco`, no `Retype`). In the `lam` subcase of the
   function step, `Deco.lam.inj` also forces the two body steps `hb₀` (at `B₀`) and `hb` (at `B`)
   to share their source decoration, so `uniqStepD` supplies `TyConvT E n (.assumption A :: Γ) B₀ B`
   and reindexes the body join to `B` before `CertAssumpCtx`. Consequently:
   * the `refl`, `lam`, and `conv` subcases of `app × beta` close with **zero fronts** (no `Retype`,
     no `PropAlign`, no `PiPropCodom`);
   * the `peq` subcase reduces to `HostPropAudit.ZeroSortCoherence E n` alone (no `Retype`, no
     `PropAlign`, no `PiPropCodom`).
5. **`lam × eta` under `CR_D` (`etaExpansionTy`, `decoOf_etaExpansion`, `lamEtaApp_of_unlift_deco`,
   `etaLeaf_valleyJoin`)**:
   * `decoOf_etaExpansion` computes the decoration of the canonical η-expansion typing using
     `decoOf_hasTyTWeaken`: its body decoration is
     `.app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂) (decoLift 0 1 (decoOf hf)) (.bvar 0)`.
   * When the body steps by `ParRedT.app` (`hg : lift 0 1 f ⇒ g`, `hx : bvar 0 ⇒ x`) sharing this
     lifted decoration, `Deco.app.inj` forces `Bg = lift 1 1 B₂` and
     `stepDeco L hg = decoLift 0 1 (stepDeco L hf)`. By `decoLift_one_inj`
     (`RcicNativeValleyDecoBook`), any un-lifted step `hg₀ : f ⇒ g₀` with
     `stepDeco L hg = decoLift 0 1 (stepDeco L hg₀.step)` automatically satisfies
     `stepDeco L hg₀.step = stepDeco L hf`, feeding `IHBelowD` and closing the join without
     `Retype` (`lamEtaApp_of_unlift_deco`).
   * For the `RcicNativeValleyEtaLeaf` counterexample to the one-step `LamEtaApp` (where an
     irrelevance leaf inside `lift 0 1 f` introduces `bvar 0`), we exhibit the explicit two-step
     certified valley join (`etaLeaf_valleyJoin : ValleyJoin ...`).

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### `CDiamondD`, `CoreDiamondD`, and `IHBelowD` -/

/-- The decorated same-index certified diamond (`CR_D` of `NATIVE_VALLEYS_STATUS.md` §9c):
    two certified steps out of `b` at `T` sharing their source decoration join in one certified
    step each. -/
def CDiamondD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
    stepDeco L p.step = stepDeco L q.step →
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T ×' CStep E n PEq Γ e f T

/-- The decorated independent-index certified diamond: two certified steps out of `b` sharing
    their source decoration join at their respective indices. -/
def CoreDiamondD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T₁ T₂ : Expr Nat}
    (p : CStep E n PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂),
    stepDeco L p.step = stepDeco L q.step → Join E n PEq Γ d e T₁ T₂

/-- Two `ParRedT` steps out of one term with the same `stepDeco` have convertible types. -/
noncomputable def uniqParRedTD (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (p : ParRedT PEq E n Γ b d T₁) (q : ParRedT PEq E n Γ b e T₂)
    (hd : stepDeco L p = stepDeco L q) :
    TyConvT E n Γ T₁ T₂ :=
  uniqD hW (parRedT_hasTy_left L.typed hΓ p) (parRedT_hasTy_left L.typed hΓ q)
    (by rw [decoOf_parRedT_hasTy_left L, decoOf_parRedT_hasTy_left L, hd])

/-- `CoreDiamondD` specializes to `CDiamondD` at `T₁ = T₂ = T`. -/
def cdiamondD_of_coreDiamondD {L : LeafIface E n PEq}
    (D : CoreDiamondD E n PEq L) : CDiamondD E n PEq L :=
  fun {_} hΓ {_ _ _ _} p q hd => D hΓ p q hd

/-- Conversely, `CDiamondD` yields `CoreDiamondD` under `EnvWfT E`: `uniqStepD` connects the two
    indices by `TyConvT`, and `CStep.reindex` preserves `stepDeco`. -/
noncomputable def coreDiamondD_of_cdiamondD (hW : EnvWfT E) {L : LeafIface E n PEq}
    (D : CDiamondD E n PEq L) : CoreDiamondD E n PEq L :=
  fun {_} hΓ {_ _ _ _ _} p q hd =>
    let hc : TyConvT E n _ _ _ := uniqStepD hW L hΓ p q hd
    let q' := q.reindex hc.symmT
    have hd' : stepDeco L p.step = stepDeco L q'.step := by
      rw [stepDeco_reindex]
      exact hd
    let ⟨f, pf, qf⟩ := D hΓ p q' hd'
    ⟨f, pf, qf.reindex hc⟩

/-- The induction hypothesis of the decorated assembler on pairs of certified steps of total size
    below `m` that share their source decoration. -/
def IHBelowD (E : ResolvedEnv) (n : Nat) (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (L : LeafIface E n PEq) (m : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T₁ T₂ : Expr Nat} {p : ParRedT PEq E n Γ b d T₁},
    Certified p → ∀ {q : ParRedT PEq E n Γ b e T₂}, Certified q →
    stepDeco L p = stepDeco L q → sizeOf p + sizeOf q < m → Join E n PEq Γ d e T₁ T₂

/-- `IHBelowD` is monotone in its size bound. -/
def IHBelowD.mono {L : LeafIface E n PEq} {m m' : Nat} (h : m ≤ m')
    (ih : IHBelowD E n PEq L m') : IHBelowD E n PEq L m :=
  fun {_} hΓ {_ _ _ _ _} {_} cp {_} cq hd hlt => ih hΓ cp cq hd (Nat.lt_of_lt_of_le hlt h)

/-- `IHBelowD` is symmetric in its size bound. -/
def IHBelowD.comm {L : LeafIface E n PEq} {a b : Nat}
    (ih : IHBelowD E n PEq L (a + b)) : IHBelowD E n PEq L (b + a) :=
  fun {_} hΓ {_ _ _ _ _} {_} cp {_} cq hd hlt => ih hΓ cp cq hd (by omega)

/-! ### Generic rows (`refl × q` and `peq × q`) under `CR_D` -/

/-- `refl × q` under `CR_D`: `retypeD` presents `q` at the `refl` node's index without the
    `Retype` front. -/
noncomputable def join_refl_deco (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b e T₁ T₂ : Expr Nat} (hb : HasTyT E n Γ b T₁)
    (q : CStep E n PEq Γ b e T₂) (hd : decoOf hb = stepDeco L q.step) :
    Join E n PEq Γ b e T₁ T₂ :=
  ⟨e, retypeD hW L hΓ hb q (by rw [decoOf_leftTyped, hd]),
    ⟨.refl Γ e T₂ (q.rightTyped L hΓ), .refl (.refl Γ e T₂ (q.rightTyped L hΓ))⟩⟩

/-- `peq × q` under `CR_D`: `uniqD` connects `T₁` and `T₂` from the shared decoration of `b`,
    and `ProofSourceAudit.join_peq_connected` joins at `e` without `Retype`, `PropAlign`, or
    `ZeroSortCoherence`. -/
noncomputable def join_peq_deco (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat} (h : PEq Γ b d T₁)
    (q : CStep E n PEq Γ b e T₂) (hd : decoOf (L.typed h).1 = stepDeco L q.step) :
    Join E n PEq Γ d e T₁ T₂ :=
  let chain : TyConvT E n Γ T₁ T₂ :=
    uniqD hW (L.typed h).1 (q.leftTyped L hΓ) (by rw [decoOf_leftTyped, hd])
  ProofSourceAudit.join_peq_connected L hΓ h chain q

/-! ### Congruence and `beta × beta` rows under `CR_D` -/

/-- `app × app` under `CR_D`: `Deco.app.inj` extracts `stepDeco L hf₁ = stepDeco L hf₂` and
    `stepDeco L ha₁ = stepDeco L ha₂`, feeding `IHBelowD` on both child pairs via `row_app_app`. -/
def row_app_app_deco (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ a a₁ a₂ A₁ B₁ T₀₁ A₂ B₂ T₀₂ : Expr Nat} {v₁ w₁ v₂ w₂ : Level}
    {hf₁ : ParRedT PEq E n Γ f f₁ T₀₁} {hc₁ : TyConvT E n Γ T₀₁ (.pi A₁ B₁)}
    {hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁)}
    {hTy₁ : HasTyT E n Γ (instantiate0 a B₁) (.sort w₁)}
    {ha₁ : ParRedT PEq E n Γ a a₁ A₁} {hr₁ : HasTyT E n Γ (.app f₁ a₁) (instantiate0 a B₁)}
    {hf₂ : ParRedT PEq E n Γ f f₂ T₀₂} {hc₂ : TyConvT E n Γ T₀₂ (.pi A₂ B₂)}
    {hB₂ : HasTyT E n (.assumption A₂ :: Γ) B₂ (.sort v₂)}
    {hTy₂ : HasTyT E n Γ (instantiate0 a B₂) (.sort w₂)}
    {ha₂ : ParRedT PEq E n Γ a a₂ A₂} {hr₂ : HasTyT E n Γ (.app f₂ a₂) (instantiate0 a B₂)}
    (cf₁ : Certified hf₁) (ca₁ : Certified ha₁)
    (cf₂ : Certified hf₂) (ca₂ : Certified ha₂)
    (hd : stepDeco L (ParRedT.app Γ f f₁ a a₁ A₁ B₁ T₀₁ v₁ w₁ hf₁ hc₁ hB₁ hTy₁ ha₁ hr₁) =
          stepDeco L (ParRedT.app Γ f f₂ a a₂ A₂ B₂ T₀₂ v₂ w₂ hf₂ hc₂ hB₂ hTy₂ ha₂ hr₂))
    {m : Nat} (ih : IHBelowD E n PEq L m)
    (hszf : sizeOf hf₁ + sizeOf hf₂ < m) (hsza : sizeOf ha₁ + sizeOf ha₂ < m) :
    Join E n PEq Γ (.app f₁ a₁) (.app f₂ a₂) (instantiate0 a B₁) (instantiate0 a B₂) := by
  simp only [stepDeco] at hd
  injection hd with _ _ _ hdf hda
  exact row_app_app hW L hΓ hf₁ hc₁ hB₁ ha₁ ca₁ hf₂ hc₂ hB₂ ha₂ ca₂
    (ih hΓ cf₁ cf₂ hdf hszf) (ih hΓ ca₁ ca₂ hda hsza)

/-- `lam × lam` under `CR_D`: `Deco.lam.inj` extracts `stepDeco L hb₁ = stepDeco L hb₂`, feeding
    `IHBelowD` on the bodies under `.assumption A :: Γ`. -/
def row_lam_lam_deco (hW : EnvWfT E) (L : LeafIface E n PEq) (Ac : CertAssumpCtx E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A₁ A₂ body body₁ body₂ B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    {hc₁ : ConvT E n Γ A A₁ (.sort u₁)} {hA₁ : HasTyT E n Γ A (.sort u₁)}
    {hB₁ : HasTyT E n (.assumption A :: Γ) B₁ (.sort v₁)}
    {hb₁ : ParRedT PEq E n (.assumption A :: Γ) body body₁ B₁}
    {hrt₁ : HasTyT E n Γ (.lam A₁ body₁) (.pi A B₁)}
    {hc₂ : ConvT E n Γ A A₂ (.sort u₂)} {hA₂ : HasTyT E n Γ A (.sort u₂)}
    {hB₂ : HasTyT E n (.assumption A :: Γ) B₂ (.sort v₂)}
    {hb₂ : ParRedT PEq E n (.assumption A :: Γ) body body₂ B₂}
    {hrt₂ : HasTyT E n Γ (.lam A₂ body₂) (.pi A B₂)}
    (cb₁ : Certified hb₁) (cb₂ : Certified hb₂)
    (hd : stepDeco L (ParRedT.lam Γ A A₁ body body₁ B₁ u₁ v₁ hc₁ hA₁ hB₁ hb₁ hrt₁) =
          stepDeco L (ParRedT.lam Γ A A₂ body body₂ B₂ u₂ v₂ hc₂ hA₂ hB₂ hb₂ hrt₂))
    {m : Nat} (ih : IHBelowD E n PEq L m) (hszb : sizeOf hb₁ + sizeOf hb₂ < m) :
    Join E n PEq Γ (.lam A₁ body₁) (.lam A₂ body₂) (.pi A B₁) (.pi A B₂) := by
  simp only [stepDeco] at hd
  injection hd with _ _ _ _ hdb
  exact row_lam_lam hW L Ac hΓ hc₁ hA₁ hB₁ hc₂ hA₂ hB₂
    (ih (.assumption Γ A u₁ hΓ hA₁) cb₁ cb₂ hdb hszb)

/-- `beta × beta` under `CR_D`: `Deco.app.inj` and `Deco.lam.inj` extract
    `stepDeco L hb₁ = stepDeco L hb₂` and `stepDeco L ha₁ = stepDeco L ha₂`, feeding `IHBelowD`
    on both the bodies and the arguments. -/
def row_beta_beta_deco (L : LeafIface E n PEq) (S : CertSubst0 E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A body body₁ body₂ arg arg₁ arg₂ B₁ B₂ : Expr Nat}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    {hA₁ : HasTyT E n Γ A (.sort u₁)} {hB₁ : HasTyT E n (.assumption A :: Γ) B₁ (.sort v₁)}
    {hTy₁ : HasTyT E n Γ (instantiate0 arg B₁) (.sort w₁)}
    {hb₁ : ParRedT PEq E n (.assumption A :: Γ) body body₁ B₁}
    {ha₁ : ParRedT PEq E n Γ arg arg₁ A}
    {hred₁ : HasTyT E n Γ (instantiate0 arg₁ body₁) (instantiate0 arg B₁)}
    {hA₂ : HasTyT E n Γ A (.sort u₂)} {hB₂ : HasTyT E n (.assumption A :: Γ) B₂ (.sort v₂)}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B₂) (.sort w₂)}
    {hb₂ : ParRedT PEq E n (.assumption A :: Γ) body body₂ B₂}
    {ha₂ : ParRedT PEq E n Γ arg arg₂ A}
    {hred₂ : HasTyT E n Γ (instantiate0 arg₂ body₂) (instantiate0 arg B₂)}
    (cb₁ : Certified hb₁) (ca₁ : Certified ha₁)
    (cb₂ : Certified hb₂) (ca₂ : Certified ha₂)
    (hd : stepDeco L (ParRedT.beta Γ A body body₁ arg arg₁ B₁ u₁ v₁ w₁ hA₁ hB₁ hTy₁ hb₁ ha₁ hred₁) =
          stepDeco L (ParRedT.beta Γ A body body₂ arg arg₂ B₂ u₂ v₂ w₂ hA₂ hB₂ hTy₂ hb₂ ha₂ hred₂))
    {m : Nat} (ih : IHBelowD E n PEq L m)
    (hszb : sizeOf hb₁ + sizeOf hb₂ < m) (hsza : sizeOf ha₁ + sizeOf ha₂ < m) :
    Join E n PEq Γ (instantiate0 arg₁ body₁) (instantiate0 arg₂ body₂) (instantiate0 arg B₁)
      (instantiate0 arg B₂) := by
  simp only [stepDeco] at hd
  injection hd with _ _ _ hdlam hda
  injection hdlam with _ _ _ _ hdb
  exact row_beta_beta L S hΓ hA₁ hB₁ ca₁ hA₂ hB₂ ca₂
    (ih (.assumption Γ A u₁ hΓ hA₁) cb₁ cb₂ hdb hszb) (ih hΓ ca₁ ca₂ hda hsza)

/-! ### `app × beta` under `CR_D` -/

/-- Under `CR_D`, the argument children `ha` (at `A'`) and `ha₂` (at `A`) of `app × beta` share
    their source decoration (`stepDeco L ha = stepDeco L ha₂`). Hence `uniqParRedTD` supplies
    `TyConvT E n Γ A' A` directly, and `argJoin_deco` joins the arguments at `A` without `Retype`. -/
noncomputable def argJoin_deco (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {arg a' arg' A' A : Expr Nat}
    {ha : ParRedT PEq E n Γ arg a' A'} (ca : Certified ha)
    {ha₂ : ParRedT PEq E n Γ arg arg' A} (ca₂ : Certified ha₂)
    (hda : stepDeco L ha = stepDeco L ha₂)
    {m : Nat} (ih : IHBelowD E n PEq L m) (hsz : sizeOf ha + sizeOf ha₂ < m) :
    Σ' (a₃ : Expr Nat), CStep E n PEq Γ a' a₃ A ×' CStep E n PEq Γ arg' a₃ A :=
  let hcA : TyConvT E n Γ A' A := uniqParRedTD hW L hΓ ha ha₂ hda
  let ⟨a₃, pa, qa⟩ := ih hΓ ca ca₂ hda hsz
  ⟨a₃, pa.reindex hcA, qa⟩

/-- Reindexing the β-contraction leg from `instantiate0 a' B` back to `instantiate0 arg B` using
    only `uniqParRedTD` on the shared argument decoration (no `Retype`). -/
noncomputable def betaLeftReindex_deco (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A f' a' target arg arg' A' B : Expr Nat} {u v' : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v'))
    {ha : ParRedT PEq E n Γ arg a' A'} (ca : Certified ha)
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    (hda : stepDeco L ha = stepDeco L ha₂)
    (left : CStep E n PEq Γ (.app f' a') target (instantiate0 a' B)) :
    CStep E n PEq Γ (.app f' a') target (instantiate0 arg B) :=
  let hcA : TyConvT E n Γ A' A := uniqParRedTD hW L hΓ ha ha₂ hda
  let haA : CStep E n PEq Γ arg a' A := (⟨ha, ca⟩ : CStep E n PEq Γ arg a' A').reindex hcA
  let harg : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha₂
  let ha' : HasTyT E n Γ a' A := haA.rightTyped L hΓ
  left.reindex (.of _ _ _ v'
    (convT_inst0_valueSort hA hB₂ ha' harg (.symm _ _ _ _ haA.toConvT)))

set_option linter.unusedVariables false in
/-- Decorated `AppBetaEta` front under `CR_D` (where `B' = B`, `stepDeco L hf = .lam ...`, and
    `stepDeco L ha = stepDeco L ha₂`). -/
def AppBetaEtaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A f₀ f' B₀ arg a' A' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    {hf₀ : ParRedT PEq E n Γ f₀ f' (.pi A B₀)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f₀) (.bvar 0))) (.pi A B₀)}
    (hc : TyConvT E n Γ (.pi A B₀) (.pi A' B))
    (hB : HasTyT E n (.assumption A' :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'}
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B))
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) (.app (lift 0 1 f₀) (.bvar 0)) body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)},
    Certified (ParRedT.eta (PEq := PEq) Γ f₀ f' A B₀ hf₀ hl) → Certified hf₀ → Certified ha →
    Certified (ParRedT.beta (PEq := PEq) Γ A (.app (lift 0 1 f₀) (.bvar 0)) body' arg arg' B u v'
      w' hA hB₂ hTy₂ hb ha₂ hred) →
    Certified hb → Certified ha₂ →
    decoOf hl = .lam A (.app (lift 0 1 f₀) (.bvar 0)) u (decoOf hA) (stepDeco L hb) →
    stepDeco L ha = stepDeco L ha₂ →
    (m : Nat) → IHBelowD E n PEq L m →
    sizeOf (ParRedT.eta (PEq := PEq) Γ f₀ f' A B₀ hf₀ hl) + sizeOf ha + sizeOf hb + sizeOf ha₂ <
      m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B)
      (instantiate0 arg B)

set_option linter.unusedVariables false in
/-- Decorated `AppBetaIota` front under `CR_D`. -/
def AppBetaIotaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A body lhs' f' T₀ arg a' A' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    {hstep : ParRedT PEq E n Γ (.lam A body) lhs' T₀} {hI : DerivedIotaU E lhs' f'}
    {hred₀ : HasTyT E n Γ lhs' T₀} {hrhs : HasTyT E n Γ f' T₀}
    (hc : TyConvT E n Γ T₀ (.pi A' B))
    (hB : HasTyT E n (.assumption A' :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'}
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B))
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)},
    Certified (ParRedT.iotaSpine (PEq := PEq) Γ (.lam A body) lhs' f' T₀ hstep hI hred₀ hrhs) →
    Certified hstep → Certified ha →
    Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
      hred) →
    Certified hb → Certified ha₂ →
    stepDeco L hstep = .lam A body u (decoOf hA) (stepDeco L hb) →
    stepDeco L ha = stepDeco L ha₂ →
    (m : Nat) → IHBelowD E n PEq L m →
    sizeOf (ParRedT.iotaSpine (PEq := PEq) Γ (.lam A body) lhs' f' T₀ hstep hI hred₀ hrhs) +
      sizeOf ha + sizeOf hb + sizeOf ha₂ < m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B)
      (instantiate0 arg B)

/-- The core of `app × beta` under `CR_D`:
    * `refl` and `lam` close with **zero fronts** (no `Retype`, no `PropAlign`, no `PiPropCodom`);
    * `conv` peels and preserves `stepDeco`;
    * `peq` closes from `ZeroSortCoherence` alone via `uniqD` on the shared λ decoration (no
      `Retype`, no `PropAlign`, no `PiPropCodom`). -/
noncomputable def appBetaCore_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) (S : CertSubst0 E n PEq)
    (Ac : CertAssumpCtx E n PEq) (AE : AppBetaEtaD E n PEq L) (AI : AppBetaIotaD E n PEq L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body arg a' A' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    (hB : HasTyT E n (.assumption A' :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'} (ca : Certified ha)
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (cq : Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb
      ha₂ hred))
    (cb : Certified hb) (ca₂ : Certified ha₂)
    (hda : stepDeco L ha = stepDeco L ha₂)
    (m : Nat) (ih : IHBelowD E n PEq L m) :
    {x f' T₀ : Expr Nat} → {hf : ParRedT PEq E n Γ x f' T₀} → Certified hf →
    (hx : x = .lam A body) →
    hx ▸ stepDeco L hf = Deco.lam A body u (decoOf hA) (stepDeco L hb) →
    TyConvT E n Γ T₀ (.pi A' B) → HasTyT E n Γ (.app f' a') (instantiate0 arg B) →
    sizeOf hf + sizeOf ha + sizeOf hb + sizeOf ha₂ < m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B)
      (instantiate0 arg B)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx, _, _, _, hsz => by
      subst hx
      obtain ⟨a₃, pa, qa⟩ := argJoin_deco hW L hΓ ca ca₂ hda ih (by omega)
      have hbody' : HasTyT E n (.assumption A :: Γ) body' B :=
        parRedT_hasTy_right L.typed (.assumption Γ A u hΓ hA) hb
      have right := betaRight L S hΓ hA hB₂ ca₂ ⟨.refl _ body' B hbody', .refl (.refl _ _ _ hbody')⟩ qa
      have left := betaLeg hW L S hΓ hA hB₂ ⟨hb, cb⟩ pa
      exact ⟨instantiate0 a₃ body',
        betaLeftReindex_deco hW L hΓ hA hB₂ ca hda left, right⟩
  | _, _, _, _, @Certified.lam _ _ _ _ A₀ A'' body₀ f_body B₀ u₀ v₀ hc₀ hA₀ hB₀ hb₀ _ _ cb₀, hx,
      hdf, _, _, hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      dsimp only [stepDeco] at hdf
      injection hdf with _ _ hu hdA hdb
      have hcl := envClosed_of_envWfT hW
      obtain ⟨a₃, pa, qa⟩ := argJoin_deco hW L hΓ ca ca₂ hda ih (by simp at hsz; omega)
      have hΓA : CtxWfT E n (.assumption A₀ :: Γ) := .assumption Γ A₀ u hΓ hA
      obtain ⟨b₃, pb, qb⟩ := ih hΓA cb₀ cb hdb (by simp at hsz; omega)
      have right := betaRight L S hΓ hA hB₂ ca₂ qb qa
      have hcB₀ : TyConvT E n (.assumption A₀ :: Γ) B₀ B := uniqParRedTD hW L hΓA hb₀ hb hdb
      have pbB : CStep E n PEq (.assumption A₀ :: Γ) f_body b₃ B := pb.reindex hcB₀
      have hA'' : HasTyT E n Γ A'' (.sort u₀) := (convEnds hW hΓ hc₀).2.1
      have hctx : CtxConvT E n (.assumption A₀ :: Γ) (.assumption A'' :: Γ) :=
        .assumption (ctxConvT_refl Γ) hA₀ hA'' hc₀
      have pb'' : CStep E n PEq (.assumption A'' :: Γ) f_body b₃ B := Ac hA₀ hA'' hc₀ pbB
      have hB₂'' : HasTyT E n (.assumption A'' :: Γ) B (.sort v') := hasTyT_ctx hcl hctx hB₂
      have pa'' : CStep E n PEq Γ a' a₃ A'' := pa.reindex (.of _ _ _ u₀ hc₀)
      have left := betaLeg hW L S hΓ hA'' hB₂'' pb'' pa''
      exact ⟨instantiate0 a₃ b₃,
        betaLeftReindex_deco hW L hΓ hA hB₂ ca hda left, right⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hcT _ ch, hx, hdf, hc, hr, hsz =>
      appBetaCore_deco hW L zsc S Ac AE AI hΓ hB hTy ca cq cb ca₂ hda m ih ch hx hdf
        (.trans _ _ _ _ hcT hc) hr (by simp at hsz; omega)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx, hdf, _, hr, _ => by
      subst hx
      dsimp only [stepDeco] at hdf
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      let hbody : HasTyT E n (.assumption A :: Γ) body B := parRedT_hasTy_left L.typed hΓA hb
      let hlamB : HasTyT E n Γ (.lam A body) (.pi A B) := .lam Γ A u body B hA hbody
      have hd_lam : decoOf (L.typed h).1 = decoOf hlamB := by
        dsimp only [hlamB, hbody, decoOf]
        rw [decoOf_parRedT_hasTy_left L hΓA hb]
        exact hdf
      have hc_pi : TyConvT E n Γ _ (.pi A B) := uniqD hW (L.typed h).1 hlamB hd_lam
      have hpi0 : HasTyT E n Γ (.pi A B) (.sort .zero) :=
        HostPropAudit.sort_transport0_data hW zsc hΓ hc_pi (L.prop h)
      have hB0 : HasTyT E n (.assumption A :: Γ) B (.sort .zero) :=
        HostPropAudit.pi_codomain_prop_data hW zsc hΓ hpi0
      have harg : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha₂
      have hP : HasTyT E n Γ (instantiate0 arg B) (.sort .zero) :=
        hasTyT_subst0S hcl hinst hB0 harg
      exact ⟨instantiate0 arg' body', CStep.irr L hP hr hred,
        ⟨.refl Γ _ _ hred, .refl (.refl Γ _ _ hred)⟩⟩
  | _, _, _, _, cf@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₀), hx, hdf, hc, hr, hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      exact AE hΓ hc hB hTy hr cf cf₀ ca cq cb ca₂ hdf hda m ih hsz
  | _, _, _, _, cf@(@Certified.iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ cinner), hx, hdf, hc, hr, hsz => by
      subst hx
      exact AI hΓ hc hB hTy hr cf cinner ca cq cb ca₂ hdf hda m ih hsz
  | _, _, _, _, .sortEq .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .consts .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .bvarZeta .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .delta .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .app .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .beta .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .pi .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .letE .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .zeta .., hx, _, _, _, _ => nomatch hx
  | _, _, _, _, .lit .., hx, _, _, _, _ => nomatch hx

set_option linter.unusedVariables false in
/-- `app × beta` under `CR_D`: `Deco.app.inj` forces `B' = B`, `stepDeco L hf = .lam ...`, and
    `stepDeco L ha = stepDeco L ha₂`, eliminating `Retype`, `PropAlign`, and `PiPropCodom`. -/
noncomputable def app_beta_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n) (S : CertSubst0 E n PEq)
    (Ac : CertAssumpCtx E n PEq) (AE : AppBetaEtaD E n PEq L) (AI : AppBetaIotaD E n PEq L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body f' arg a' A' B' T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ (.lam A body) f' T₀} {hc : TyConvT E n Γ T₀ (.pi A' B')}
    {hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w)}
    {ha : ParRedT PEq E n Γ arg a' A'} {hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B')}
    {body' arg' B : Expr Nat} {u v' w' : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (cp : Certified (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
      ha hr))
    (cq : Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
      hred))
    (cf : Certified hf) (ca : Certified ha) (cb : Certified hb) (ca₂ : Certified ha₂)
    (hd : stepDeco L (ParRedT.app Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy ha hr) =
          stepDeco L (ParRedT.beta Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂ hred))
    (ih : IHBelowD E n PEq L
      (sizeOf (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
        ha hr) +
       sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
        hred))) :
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B) := by
  have hd' := hd
  simp only [stepDeco] at hd'
  injection hd' with _ _ hB_eq hdf hda
  subst hB_eq
  exact appBetaCore_deco hW L zsc S Ac AE AI hΓ hB hTy ca cq cb ca₂ hda _ ih cf rfl hdf hc hr
    (by simp; omega)

/-! ### `lam × eta` under `CR_D`: canonical lifted decoration, structural un-lifting, and the
    two-step valley join of the leaf counterexample -/

/-- The canonical typing of the η-expansion `.lam A (.app (lift 0 1 f) (.bvar 0))` at `.pi A B₂`
    from `hA : HasTyT E n Γ A (.sort u)` and `hf : HasTyT E n Γ f (.pi A B₂)`. -/
def etaExpansionBodyTy (hcl : EnvClosed E) {Γ : LCtx} {A f B₂ : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B₂)) :
    HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) B₂ :=
  let hliftf : HasTyT E n (.assumption A :: Γ) (lift 0 1 f) (.pi (lift 0 1 A) (lift 1 1 B₂)) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hf
  let hbv0 : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) := .bvar _ 0 _ rfl
  let happ : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      (instantiate0 (.bvar 0) (lift 1 1 B₂)) :=
    .app _ (lift 0 1 f) (.bvar 0) (lift 0 1 A) (lift 1 1 B₂) hliftf hbv0
  (instantiate_bvar_lift B₂ 0) ▸ happ

/-- The canonical typing of the η-expansion `.lam A (.app (lift 0 1 f) (.bvar 0))` at `.pi A B₂`. -/
def etaExpansionTy (hcl : EnvClosed E) {Γ : LCtx} {A f B₂ : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B₂)) :
    HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₂) :=
  .lam Γ A u _ B₂ hA (etaExpansionBodyTy hcl hf)

/-- The decoration of `etaExpansionBodyTy` is `.app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂)` applied
    to the lifted decoration `decoLift 0 1 (decoOf hf)` and `.bvar 0`. -/
@[simp] theorem decoOf_etaExpansionBodyTy (hcl : EnvClosed E) {Γ : LCtx} {A f B₂ : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B₂)) :
    decoOf (etaExpansionBodyTy hcl hf) =
      .app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂) (decoLift 0 1 (decoOf hf)) (.bvar 0) := by
  unfold etaExpansionBodyTy
  dsimp only
  have hcast : ∀ {e T₁ T₂ : Expr Nat} (hT : T₁ = T₂) (h : HasTyT E n (.assumption A :: Γ) e T₁),
      decoOf (hT ▸ h) = decoOf h := by
    intro _ _ _ hT _; subst hT; rfl
  rw [hcast]
  simp only [decoOf, decoOf_hasTyTWeaken]

/-- The decoration of `etaExpansionTy` carries the lifted decoration `decoLift 0 1 (decoOf hf)` on
    `lift 0 1 f`. -/
@[simp] theorem decoOf_etaExpansionTy (hcl : EnvClosed E) {Γ : LCtx} {A f B₂ : Expr Nat}
    {u : Level} (hA : HasTyT E n Γ A (.sort u)) (hf : HasTyT E n Γ f (.pi A B₂)) :
    decoOf (etaExpansionTy hcl hA hf) =
      .lam A (.app (lift 0 1 f) (.bvar 0)) u (decoOf hA)
        (.app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂) (decoLift 0 1 (decoOf hf)) (.bvar 0)) := by
  simp only [etaExpansionTy, decoOf, decoOf_etaExpansionBodyTy]

/-- Structural un-lifting of a lifted decoration: if `hg : lift 0 1 f ⇒ g` has the lifted
    decoration `decoLift 0 1 (stepDeco L hf)` (extracted by `Deco.app.inj` from `lam × eta`) and
    is the weakening of `hg₀ : f ⇒ g₀` (`stepDeco L hg = decoLift 0 1 (stepDeco L hg₀.step)`),
    then `hg₀` and `hf` share their source decoration (`stepDeco L hg₀.step = stepDeco L hf`) by
    `decoLift_one_inj`. -/
theorem unlift_stepDeco_eq (L : LeafIface E n PEq) {Γ : LCtx}
    {A f f' g g₀ T₀ B₂ T₁ : Expr Nat}
    (hg : ParRedT PEq E n (.assumption A :: Γ) (lift 0 1 f) g T₀)
    (hf : ParRedT PEq E n Γ f f' (.pi A B₂))
    (hg₀ : CStep E n PEq Γ f g₀ T₁)
    (hd_eta : stepDeco L hg = decoLift 0 1 (stepDeco L hf))
    (hd_wk : stepDeco L hg = decoLift 0 1 (stepDeco L hg₀.step)) :
    stepDeco L hg₀.step = stepDeco L hf :=
  decoLift_one_inj (hd_wk.symm.trans hd_eta)

set_option linter.unusedVariables false in
/-- `LamEtaApp` under `CR_D` when `hg : lift 0 1 f ⇒ lift 0 1 g₀` un-lifts to a certified step
    `hg₀ : CStep E n PEq Γ f g₀ (.pi A B₂)` with `stepDeco L hg = decoLift 0 1 (stepDeco L hg₀.step)`
    and the bound variable argument steps to itself (`x = .bvar 0`):
    * `Deco.app.inj` gives `Bg = lift 1 1 B₂` and `stepDeco L hg = decoLift 0 1 (stepDeco L hf)`;
    * `unlift_stepDeco_eq` gives `stepDeco L hg₀.step = stepDeco L hf`;
    * `IHBelowD` joins `hg₀` and `hf` to `⟨f₃, pf, qf⟩` at `.pi A B₂`;
    * `uniqD` (from the shared body decoration) gives `TyConvT E n Γ (.pi A B₁) (.pi A B₂)`
      via `tyConvT_pi_codom`, so `etaAtConverted` reindexes to `.pi A B₁` without `Retype`. -/
noncomputable def lamEtaApp_of_unlift_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} {A A' f f' g₀ B₁ B₂ A₀ Bg T₀ : Expr Nat} {u v v₀ w₀ : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' (.app (lift 0 1 g₀) (.bvar 0)) B₁ B₂ u v)
    {hg : ParRedT PEq E n (.assumption A :: Γ) (lift 0 1 f) (lift 0 1 g₀) T₀}
    {hcg : TyConvT E n (.assumption A :: Γ) T₀ (.pi A₀ Bg)}
    {hBg : HasTyT E n (.assumption A₀ :: .assumption A :: Γ) Bg (.sort v₀)}
    {hTyg : HasTyT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bg) (.sort w₀)}
    {hx : ParRedT PEq E n (.assumption A :: Γ) (.bvar 0) (.bvar 0) A₀}
    {hr : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 g₀) (.bvar 0))
      (instantiate0 (.bvar 0) Bg)}
    (cb : Certified (ParRedT.app (PEq := PEq) (.assumption A :: Γ) (lift 0 1 f) (lift 0 1 g₀)
      (.bvar 0) (.bvar 0) A₀ Bg T₀ v₀ w₀ hg hcg hBg hTyg hx hr))
    (hcB : TyConvT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bg) B₁)
    (hd_body : stepDeco L (ParRedT.app (.assumption A :: Γ) (lift 0 1 f) (lift 0 1 g₀)
      (.bvar 0) (.bvar 0) A₀ Bg T₀ v₀ w₀ hg hcg hBg hTyg hx hr) =
      .app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂) (decoLift 0 1 (stepDeco L D.hf)) (.bvar 0))
    (hg₀ : CStep E n PEq Γ f g₀ (.pi A B₂))
    (hd_wk : stepDeco L hg = decoLift 0 1 (stepDeco L hg₀.step))
    {m : Nat} (ih : IHBelowD E n PEq L m)
    (hsz : sizeOf hg₀.step + sizeOf D.hf < m) :
    Join E n PEq Γ (.lam A' (.app (lift 0 1 g₀) (.bvar 0))) f' (.pi A B₁) (.pi A B₂) := by
  have hd' := hd_body
  simp only [stepDeco] at hd'
  injection hd' with _ _ hBg_eq hd_eta _
  have hd_f : stepDeco L hg₀.step = stepDeco L D.hf :=
    unlift_stepDeco_eq L hg D.hf hg₀ hd_eta hd_wk
  obtain ⟨f₃, pf, qf⟩ := ih D.hΓ hg₀.cert D.cf hd_f hsz
  have hcl := envClosed_of_envWfT hW
  let hf_left : HasTyT E n Γ f (.pi A B₂) := parRedT_hasTy_left L.typed D.hΓ D.hf
  let hbody_can : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) B₂ :=
    etaExpansionBodyTy hcl hf_left
  have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u D.hΓ D.hA
  let hbody_step : HasTyT E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      (instantiate0 (.bvar 0) Bg) :=
    parRedT_hasTy_left L.typed hΓA
      (ParRedT.app (.assumption A :: Γ) (lift 0 1 f) (lift 0 1 g₀)
        (.bvar 0) (.bvar 0) A₀ Bg T₀ v₀ w₀ hg hcg hBg hTyg hx hr)
  have hd_can : decoOf hbody_step = decoOf hbody_can := by
    dsimp only [hbody_step, hbody_can, hf_left]
    rw [decoOf_parRedT_hasTy_left L hΓA, hd_body, decoOf_etaExpansionBodyTy,
      decoOf_parRedT_hasTy_left L D.hΓ D.hf]
  have hcB₂ : TyConvT E n (.assumption A :: Γ) B₁ B₂ :=
    .trans _ _ _ _ hcB.symmT (uniqD hW hbody_step hbody_can hd_can)
  have hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂) := tyConvT_pi_codom D.hA hcB₂
  have left : CStep E n PEq Γ (.lam A' (.app (lift 0 1 g₀) (.bvar 0))) f₃ (.pi A B₂) :=
    etaAtConverted hW L D.hΓ D.hc pf.cert
  exact ⟨f₃, left.reindex hcPi.symmT, qf⟩

/-- `etaAtConverted` produces a certified η-contraction whose source decoration lifts
    `stepDeco L hf` via `decoLift 0 1`. -/
@[simp] theorem stepDeco_etaAtConverted (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' f f' B₂ : Expr Nat} {u : Level}
    (hc : ConvT E n Γ A A' (.sort u)) {hf : ParRedT PEq E n Γ f f' (.pi A B₂)}
    (cf : Certified hf) :
    stepDeco L (etaAtConverted hW L hΓ hc cf).step =
      .lam A' (.app (lift 0 1 f) (.bvar 0)) u (decoOf (convEnds hW hΓ hc).2.1)
        (.app (lift 0 1 f) (.bvar 0) (lift 1 1 B₂) (decoLift 0 1 (stepDeco L hf)) (.bvar 0)) := by
  unfold etaAtConverted
  generalize hasTyTInv_pi (tySort hW hΓ (parRedT_hasTy_left L.typed hΓ hf)).2 rfl = inv
  rcases inv with ⟨_, v₂, _, hB₂v, _⟩
  dsimp only
  rw [stepDeco_reindex]
  simp only [stepDeco, decoOf]
  have hcast : ∀ {e T₁ T₂ : Expr Nat} (hT : T₁ = T₂) (h : HasTyT E n (.assumption A' :: Γ) e T₁),
      decoOf (hT ▸ h) = decoOf h := by
    intro _ _ _ hT _; subst hT; rfl
  rw [hcast]
  simp only [decoOf, decoOf_hasTyTWeaken, decoOf_leftTyped, stepDeco_reindex,
    decoOf_parRedT_typed_left L hΓ hf]

/-- `eta × eta` under `CR_D` when both η-redex typings `hl₁` and `hl₂` carry canonical lifted
    decorations `decoLift 0 1 (stepDeco L hfᵢ)`: decoration equality on the outer η-steps implies
    `stepDeco L hf₁ = stepDeco L hf₂` by `decoLift_one_inj`, so `IHBelowD` joins `(hf₁, hf₂)`
    directly without `Retype`. -/
def row_eta_eta_deco (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ A B₁ B₂ B₁' B₂' : Expr Nat} {u₁ u₂ : Level} {dA₁ dA₂ : Deco A}
    {hf₁ : ParRedT PEq E n Γ f f₁ (.pi A B₁)}
    {hl₁ : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₁)}
    {hf₂ : ParRedT PEq E n Γ f f₂ (.pi A B₂)}
    {hl₂ : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₂)}
    (cf₁ : Certified hf₁) (cf₂ : Certified hf₂)
    (hd : stepDeco L (ParRedT.eta Γ f f₁ A B₁ hf₁ hl₁) =
          stepDeco L (ParRedT.eta Γ f f₂ A B₂ hf₂ hl₂))
    (hd₁ : decoOf hl₁ = .lam A (.app (lift 0 1 f) (.bvar 0)) u₁ dA₁
      (.app (lift 0 1 f) (.bvar 0) B₁' (decoLift 0 1 (stepDeco L hf₁)) (.bvar 0)))
    (hd₂ : decoOf hl₂ = .lam A (.app (lift 0 1 f) (.bvar 0)) u₂ dA₂
      (.app (lift 0 1 f) (.bvar 0) B₂' (decoLift 0 1 (stepDeco L hf₂)) (.bvar 0)))
    {m : Nat} (ih : IHBelowD E n PEq L m) (hsz : sizeOf hf₁ + sizeOf hf₂ < m) :
    Join E n PEq Γ f₁ f₂ (.pi A B₁) (.pi A B₂) := by
  simp only [stepDeco] at hd
  have h12 := hd₁.symm.trans (hd.trans hd₂)
  injection h12 with _ _ _ _ hbody
  injection hbody with _ _ _ hdf _
  exact row_eta_eta (ih hΓ cf₁ cf₂ (decoLift_one_inj hdf) hsz)

set_option linter.unusedVariables false in
/-- Decorated `LamEtaApp` front under `CR_D` (carrying `hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂)`
    from `uniqParRedTD` on the outer `lam × eta` pair and `IHBelowD`). -/
def LamEtaAppD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} {A A' f f' g x B₁ B₂ A₀ Bg T₀ : Expr Nat} {u v v₀ w₀ : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' (.app g x) B₁ B₂ u v)
    (hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂))
    {hg : ParRedT PEq E n (.assumption A :: Γ) (lift 0 1 f) g T₀}
    {hcg : TyConvT E n (.assumption A :: Γ) T₀ (.pi A₀ Bg)}
    {hBg : HasTyT E n (.assumption A₀ :: .assumption A :: Γ) Bg (.sort v₀)}
    {hTyg : HasTyT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bg) (.sort w₀)}
    {hx : ParRedT PEq E n (.assumption A :: Γ) (.bvar 0) x A₀}
    {hr : HasTyT E n (.assumption A :: Γ) (.app g x) (instantiate0 (.bvar 0) Bg)},
    Certified (ParRedT.app (PEq := PEq) (.assumption A :: Γ) (lift 0 1 f) g (.bvar 0) x A₀ Bg T₀
      v₀ w₀ hg hcg hBg hTyg hx hr) →
    Certified hg → Certified hx →
    TyConvT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) Bg) B₁ →
    (m : Nat) → IHBelowD E n PEq L m →
    sizeOf (ParRedT.app (PEq := PEq) (.assumption A :: Γ) (lift 0 1 f) g (.bvar 0) x A₀ Bg T₀
      v₀ w₀ hg hcg hBg hTyg hx hr) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' (.app g x)) f' (.pi A B₁) (.pi A B₂)

set_option linter.unusedVariables false in
/-- Decorated `LamEtaBeta` front under `CR_D`. -/
def LamEtaBetaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} {A A' f f' A₀ b₀ b₀' x B₀' B₁ B₂ : Expr Nat} {u v u₀ v₀ w₀ : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' (instantiate0 x b₀') B₁ B₂ u v)
    (hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂))
    (hlf : lift 0 1 f = .lam A₀ b₀)
    {hA₀ : HasTyT E n (.assumption A :: Γ) A₀ (.sort u₀)}
    {hB₀' : HasTyT E n (.assumption A₀ :: .assumption A :: Γ) B₀' (.sort v₀)}
    {hTy₀ : HasTyT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) B₀') (.sort w₀)}
    {hb₀ : ParRedT PEq E n (.assumption A₀ :: .assumption A :: Γ) b₀ b₀' B₀'}
    {hx : ParRedT PEq E n (.assumption A :: Γ) (.bvar 0) x A₀}
    {hred₀ : HasTyT E n (.assumption A :: Γ) (instantiate0 x b₀') (instantiate0 (.bvar 0) B₀')},
    Certified (ParRedT.beta (PEq := PEq) (.assumption A :: Γ) A₀ b₀ b₀' (.bvar 0) x B₀' u₀ v₀ w₀
      hA₀ hB₀' hTy₀ hb₀ hx hred₀) →
    Certified hb₀ → Certified hx →
    TyConvT E n (.assumption A :: Γ) (instantiate0 (.bvar 0) B₀') B₁ →
    (m : Nat) → IHBelowD E n PEq L m →
    sizeOf (ParRedT.beta (PEq := PEq) (.assumption A :: Γ) A₀ b₀ b₀' (.bvar 0) x B₀' u₀ v₀ w₀
      hA₀ hB₀' hTy₀ hb₀ hx hred₀) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' (instantiate0 x b₀')) f' (.pi A B₁) (.pi A B₂)

set_option linter.unusedVariables false in
/-- Decorated `LamEtaIota` front under `CR_D`. -/
def LamEtaIotaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} {A A' f f' lhs' rhs T₀ B₁ B₂ : Expr Nat} {u v : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' rhs B₁ B₂ u v)
    (hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂))
    {hstep : ParRedT PEq E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) lhs' T₀}
    {hI : DerivedIotaU E lhs' rhs} {hred₀ : HasTyT E n (.assumption A :: Γ) lhs' T₀}
    {hrhs : HasTyT E n (.assumption A :: Γ) rhs T₀},
    Certified (ParRedT.iotaSpine (PEq := PEq) (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      lhs' rhs T₀ hstep hI hred₀ hrhs) →
    Certified hstep → TyConvT E n (.assumption A :: Γ) T₀ B₁ →
    (m : Nat) → IHBelowD E n PEq L m →
    sizeOf (ParRedT.iotaSpine (PEq := PEq) (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      lhs' rhs T₀ hstep hI hred₀ hrhs) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' rhs) f' (.pi A B₁) (.pi A B₂)

/-- The core of `lam × eta` under `CR_D`:
    * `refl` closes with **zero fronts** (no `Retype`) because `hcPi` from `uniqParRedTD` reindexes
      `etaAtConverted` directly to `.pi A B₁`;
    * `peq` closes from `ZeroSortCoherence` alone (no `Retype`, no `PropAlign`) via
      `HostPropAudit.sort_transport0_data` along `hcB` and `hcPi`;
    * `conv` peels;
    * `app`, `beta`, `iotaSpine` dispatch to `LamEtaAppD`, `LamEtaBetaD`, `LamEtaIotaD`. -/
def lamEtaCore_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    (LA : LamEtaAppD E n PEq L) (LB : LamEtaBetaD E n PEq L) (LI : LamEtaIotaD E n PEq L)
    {Γ : LCtx} {A A' f f' B₁ B₂ : Expr Nat} {u v : Level}
    (hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂))
    (m : Nat) (ih : IHBelowD E n PEq L m) :
    {x body' B₀ : Expr Nat} → {hb : ParRedT PEq E n (.assumption A :: Γ) x body' B₀} →
    Certified hb → (D : LamEtaCtx E n PEq Γ A A' f f' body' B₁ B₂ u v) →
    x = .app (lift 0 1 f) (.bvar 0) → TyConvT E n (.assumption A :: Γ) B₀ B₁ →
    sizeOf hb + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, D, hx, _, _ => by
      subst hx
      have hf'ty : HasTyT E n Γ f' (.pi A B₂) := parRedT_hasTy_right L.typed D.hΓ D.hf
      exact ⟨f', (etaAtConverted hW L D.hΓ D.hc D.cf).reindex hcPi.symmT,
        ⟨.refl Γ f' _ hf'ty, .refl (.refl Γ f' _ hf'ty)⟩⟩
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, D, hx, hcB, _ => by
      subst hx
      have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u D.hΓ D.hA
      have hB₁0 : HasTyT E n (.assumption A :: Γ) B₁ (.sort .zero) :=
        HostPropAudit.sort_transport0_data hW zsc hΓ' hcB (L.prop h)
      have hpi₁0 : HasTyT E n Γ (.pi A B₁) (.sort .zero) :=
        .conv Γ _ _ _ _ (.pi Γ A u B₁ .zero D.hA hB₁0)
          (.sorts Γ (.imax u .zero) .zero (eqN_imax_zero_right u))
      have hpi₂0 : HasTyT E n Γ (.pi A B₂) (.sort .zero) :=
        HostPropAudit.sort_transport0_data hW zsc D.hΓ hcPi hpi₁0
      have hlam' : HasTyT E n Γ (.lam A' _) (.pi A B₂) := hasTyT_of_tyConv D.hrt hcPi
      have hf'ty : HasTyT E n Γ f' (.pi A B₂) := parRedT_hasTy_right L.typed D.hΓ D.hf
      exact ⟨.lam A' _, ⟨.refl Γ _ _ D.hrt, .refl (.refl Γ _ _ D.hrt)⟩,
        CStep.irr L hpi₂0 hf'ty hlam'⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hcT _ ch, D, hx, hcB, hsz =>
      lamEtaCore_deco hW L zsc LA LB LI hcPi m ih ch D hx (.trans _ _ _ _ hcT hcB)
        (by simp at hsz; omega)
  | _, _, _, _, cb@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cg cx), D, hx, hcB,
      hsz => by
      injection hx with h1 h2
      subst h1; subst h2
      exact LA D hcPi cb cg cx hcB m ih hsz
  | _, _, _, _, cb@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₀ cx), D, hx, hcB,
      hsz => by
      injection hx with h1 h2
      subst h2
      exact LB D hcPi h1.symm cb cb₀ cx hcB m ih hsz
  | _, _, _, _, cb@(@Certified.iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ cinner), D, hx, hcB, hsz => by
      subst hx
      exact LI D hcPi cb cinner hcB m ih hsz
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

/-- `lam × eta` under `CR_D`: `uniqParRedTD` on `hd : stepDeco L (ParRedT.lam ...) =
    stepDeco L (ParRedT.eta ...)` supplies `hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂)` up front,
    eliminating `Retype` and `PropAlign`. -/
noncomputable def lam_eta_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    (LA : LamEtaAppD E n PEq L) (LB : LamEtaBetaD E n PEq L) (LI : LamEtaIotaD E n PEq L) :
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
    stepDeco L (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
      hA hB hb hrt) =
    stepDeco L (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
        hA hB hb hrt) +
       sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl)) →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂) :=
  fun {Γ} hΓ {A A' f body' B₁ f' B₂ u v hc hA hB hb hrt hf hl} cp _ cb cf hd ih =>
    let hcPi : TyConvT E n Γ (.pi A B₁) (.pi A B₂) :=
      uniqParRedTD hW L hΓ
        (ParRedT.lam Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc hA hB hb hrt)
        (ParRedT.eta Γ f f' A B₂ hf hl) hd
    lamEtaCore_deco hW L zsc LA LB LI hcPi _ ih cb
      ⟨hΓ, hc, hA, hB, hrt, hf, cf, hl,
        ⟨ParRedT.lam Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc hA hB hb hrt, cp⟩⟩
      rfl (.refl _ _) (by simp; omega)

/-! ### `iota_commute` and `iotaSpine × q` under `CR_D` -/

/-- Decorated `iota_commute`: when `T` and `T'` are connected by `hcT : TyConvT E n Γ T T'`
    (supplied in `CR_D` by `uniqParRedTD` on `stepDeco L (.iotaSpine ... hstep ...) =
    stepDeco L hstep = stepDeco L q`), the re-fired ι step `k ⇒ j` at `T` is reindexed to `T'` by
    `CStep.reindex` without `Retype`. -/
def iotaCommute_deco (L : LeafIface E n PEq) (D : IotaDetU E) (IR : IotaRefireT E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs' rhs k T T' : Expr Nat}
    (hI : DerivedIotaU E lhs' rhs) (hc : ConvT E n Γ lhs' rhs T)
    (pk : CStep E n PEq Γ lhs' k T) (hrhs : HasTyT E n Γ rhs T)
    (hcT : TyConvT E n Γ T T') :
    Σ' (j : Expr Nat), CStep E n PEq Γ rhs j T ×' IotaTail E n Γ k j T' :=
  match iotaCore L D IR hΓ hI pk.cert rfl hc hrhs with
  | ⟨j, pr, .inr h⟩ => ⟨j, pr, .stay h⟩
  | ⟨j, pr, .inl hIj⟩ =>
      let hk : HasTyT E n Γ k T := pk.rightTyped L hΓ
      let hj : HasTyT E n Γ j T := pr.rightTyped L hΓ
      let ckj : ConvT E n Γ k j T :=
        .trans _ _ _ _ _ (.symm _ _ _ _ pk.toConvT) (.trans _ _ _ _ _ hc pr.toConvT)
      let s : CStep E n PEq Γ k j T :=
        ⟨.iotaSpine Γ k k j T (.refl Γ k T hk) hIj hk hj,
          .iotaSpine ckj (.refl (.refl Γ k T hk))⟩
      let s' : CStep E n PEq Γ k j T' := s.reindex hcT
      ⟨j, pr, .refire hIj (s'.rightTyped L hΓ) s'.toConvT⟩

/-- `iotaSpine × q` under `CR_D`: `stepDeco L (.iotaSpine ... hstep ...) = stepDeco L hstep`, so
    `hd : stepDeco L (.iotaSpine ... hstep ...) = stepDeco L q` supplies BOTH the decoration
    agreement for the inner join `jk` AND `hcT : TyConvT E n Γ T₁ T₂` via `uniqParRedTD`, closing
    `iotaSpine × q` from `IotaDetU` and `IotaRefireT` without `Retype`. -/
noncomputable def join_iotaSpine_left_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : IotaDetU E) (IR : IotaRefireT E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {lhs lhs' rhs e T₁ T₂ : Expr Nat}
    {hstep : ParRedT PEq E n Γ lhs lhs' T₁} (hI : DerivedIotaU E lhs' rhs)
    {hlhs : HasTyT E n Γ lhs' T₁} (hrhs : HasTyT E n Γ rhs T₁)
    (hc : ConvT E n Γ lhs' rhs T₁)
    (q : ParRedT PEq E n Γ lhs e T₂)
    (hd : stepDeco L (ParRedT.iotaSpine Γ lhs lhs' rhs T₁ hstep hI hlhs hrhs) = stepDeco L q)
    (jk : Join E n PEq Γ lhs' e T₁ T₂) :
    Join E n PEq Γ rhs e T₁ T₂ :=
  let ⟨k, pk, qk⟩ := jk
  let hk₂ : HasTyT E n Γ k T₂ := qk.rightTyped L hΓ
  let hcT : TyConvT E n Γ T₁ T₂ :=
    uniqParRedTD hW L hΓ (ParRedT.iotaSpine Γ lhs lhs' rhs T₁ hstep hI hlhs hrhs) q hd
  match iotaCommute_deco L D IR hΓ hI hc pk hrhs hcT with
  | ⟨j, pr, .refire hI' hj ck⟩ =>
      ⟨j, pr, ⟨.iotaSpine Γ e k j T₂ qk.step hI' hk₂ hj,
        .iotaSpine (.trans _ _ _ _ _ qk.toConvT ck) qk.cert⟩⟩
  | ⟨j, pr, .stay h⟩ => ⟨j, pr, by subst h; exact qk⟩

/-! ### `letE × letE`, `letE × zeta`, `zeta × zeta` under `CR_D` -/

set_option linter.unusedVariables false in
/-- Decorated `LetJoin` front under `CR_D`: `Deco.letE.inj` extracts `stepDeco L hv₁ =
    stepDeco L hv₂` and `stepDeco L hb₁ = stepDeco L hb₂` from the outer `letE`/`zeta` steps, and
    provides `IHBelowD` on strictly smaller pairs. -/
def LetJoinD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat}
    {u : Level}, HasTyT E n Γ A (.sort u) → HasTyT E n Γ value A →
    ∀ {hv₁ : ParRedT PEq E n Γ value value₁ A}, Certified hv₁ →
    ∀ {hv₂ : ParRedT PEq E n Γ value value₂ A}, Certified hv₂ →
    ∀ {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁}, Certified hb₁ →
    ∀ {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂}, Certified hb₂ →
    stepDeco L hv₁ = stepDeco L hv₂ →
    stepDeco L hb₁ = stepDeco L hb₂ →
    (m : Nat) → IHBelowD E n PEq L m → sizeOf hv₁ + sizeOf hv₂ + sizeOf hb₁ + sizeOf hb₂ < m →
    Σ' (v₃ b₃ : Expr Nat), CStep E n PEq Γ value₁ v₃ A ×' CStep E n PEq Γ value₂ v₃ A ×'
      CStep E n PEq (.letBinding A value₁ :: Γ) body₁ b₃ B₁ ×'
      CStep E n PEq (.letBinding A value₂ :: Γ) body₂ b₃ B₂

/-- Under `CR_D`, the hypotheses of `LetJoinD` (`stepDeco L hv₁ = stepDeco L hv₂` and
    `stepDeco L hb₁ = stepDeco L hb₂`) allow `IHBelowD` to join BOTH the values `(v₃, pv₁, pv₂)` in
    `Γ` AND the bodies `(b₃, pb₁, pb₂)` in the source context `.letBinding A value :: Γ` directly. -/
def letSourceJoin_deco (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hval : HasTyT E n Γ value A)
    {hv₁ : ParRedT PEq E n Γ value value₁ A} (cv₁ : Certified hv₁)
    {hv₂ : ParRedT PEq E n Γ value value₂ A} (cv₂ : Certified hv₂)
    {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁} (cb₁ : Certified hb₁)
    {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂} (cb₂ : Certified hb₂)
    (hdv : stepDeco L hv₁ = stepDeco L hv₂)
    (hdb : stepDeco L hb₁ = stepDeco L hb₂)
    (m : Nat) (ih : IHBelowD E n PEq L m)
    (hsz : sizeOf hv₁ + sizeOf hv₂ + sizeOf hb₁ + sizeOf hb₂ < m) :
    Join E n PEq Γ value₁ value₂ A A ×'
      Join E n PEq (.letBinding A value :: Γ) body₁ body₂ B₁ B₂ :=
  ⟨ih hΓ cv₁ cv₂ hdv (by omega),
    ih (.letBinding Γ A u value hΓ hA hval) cb₁ cb₂ hdb (by omega)⟩

/-- Certified let-value context transport: moving a certified step out of `body'` from the source
    binding `.letBinding A value :: Γ` to the stepped binding `.letBinding A value' :: Γ` along a
    certified value step `value ⇒ value'`. -/
def CertLetValCtx (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A value value' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ value A →
    ∀ {hv : ParRedT PEq E n Γ value value' A}, Certified hv →
    ∀ {body' b₃ B : Expr Nat},
      CStep E n PEq (.letBinding A value :: Γ) body' b₃ B →
      CStep E n PEq (.letBinding A value' :: Γ) body' b₃ B

/-- Under `CR_D`, `LetJoinD` reduces purely to `CertLetValCtx`: `letSourceJoin_deco` joins the
    values in `Γ` and the bodies in `.letBinding A value :: Γ` via `IHBelowD`, and `CertLetValCtx`
    transports the two body legs to `.letBinding A value₁ :: Γ` and `.letBinding A value₂ :: Γ`. -/
def letJoinD_of_letValCtx (L : LeafIface E n PEq) (LV : CertLetValCtx E n PEq) :
    LetJoinD E n PEq L :=
  fun {_} hΓ {_ _ _ _ _ _ _ _ _ _} hA hval {_} cv₁ {_} cv₂ {_} cb₁ {_} cb₂ hdv hdb m ih hsz =>
    let ⟨⟨v₃, pv₁, pv₂⟩, ⟨b₃, pb₁, pb₂⟩⟩ :=
      letSourceJoin_deco L hΓ hA hval cv₁ cv₂ cb₁ cb₂ hdv hdb m ih hsz
    ⟨v₃, b₃, pv₁, pv₂, LV hΓ hA hval cv₁ pb₁, LV hΓ hA hval cv₂ pb₂⟩

/-- `letE × letE` under `CR_D` from `LetJoinD` and `CertLetAnnCtx`. -/
noncomputable def letE_letE_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lc : CertLetAnnCtx E n PEq) (LJ : LetJoinD E n PEq L) :
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
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) =
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
      hB₂ hTy₂ hb₂ hrt₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
        hB₂ hTy₂ hb₂ hrt₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂) := by
  intro Γ hΓ A A₁ A₂ value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hc₁ hA₁ hv₁ hB₁ hTy₁
    hb₁ hrt₁ hc₂ hA₂ hv₂ hB₂ hTy₂ hb₂ hrt₂ _ _ cv₁ cb₁ cv₂ cb₂ hd ih
  simp only [stepDeco] at hd
  injection hd with _ _ _ _ _ hdv hdb
  have hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
  obtain ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ :=
    LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ hdv hdb _ ih (by simp; omega)
  exact ⟨.letE A v₃ b₃, letSide hW L Lc hΓ hc₁ hA₁ hB₁ cv₁ pv₁ pb₁,
    letSide hW L Lc hΓ hc₂ hA₂ hB₂ cv₂ pv₂ pb₂⟩

/-- `letE × zeta` under `CR_D` from `LetJoinD`, `CertLetAnnCtx`, and `CertSubstLet`. -/
noncomputable def letE_zeta_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lc : CertLetAnnCtx E n PEq) (SL : CertSubstLet E n PEq) (LJ : LetJoinD E n PEq L) :
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
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) =
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂) := by
  intro Γ hΓ A A₁ value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hc₁ hA₁ hv₁ hB₁ hTy₁ hb₁
    hrt₁ hA₂ hv₂ hB₂ hTy₂ hb₂ hred₂ _ _ cv₁ cb₁ cv₂ cb₂ hd ih
  simp only [stepDeco] at hd
  injection hd with _ _ _ _ _ hdv hdb
  have hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
  obtain ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ :=
    LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ hdv hdb _ ih (by simp; omega)
  exact ⟨instantiate0 v₃ b₃, zetaLeg hW L Lc SL hΓ hc₁ hA₁ hB₁ cv₁ pv₁ pb₁,
    zetaSide hW L SL hΓ hA₂ hB₂ cv₂ pv₂ pb₂⟩

/-- `zeta × zeta` under `CR_D` from `LetJoinD` and `CertSubstLet`. -/
noncomputable def zeta_zeta_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    (SL : CertSubstLet E n PEq) (LJ : LetJoinD E n PEq L) :
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
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
      hb₁ hred₁) =
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
        hb₁ hred₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (instantiate0 value₁ body₁) (instantiate0 value₂ body₂)
      (instantiate0 value B₁) (instantiate0 value B₂) := by
  intro Γ hΓ A value value₁ value₂ body body₁ body₂ B₁ B₂ u₁ w₁ u₂ w₂ hA₁ hv₁ hB₁ hTy₁ hb₁ hred₁
    hA₂ hv₂ hB₂ hTy₂ hb₂ hred₂ _ _ cv₁ cb₁ cv₂ cb₂ hd ih
  simp only [stepDeco] at hd
  injection hd with _ _ _ _ _ hdv hdb
  have hval : HasTyT E n Γ value A := parRedT_hasTy_left L.typed hΓ hv₁
  obtain ⟨v₃, b₃, pv₁, pv₂, pb₁, pb₂⟩ :=
    LJ hΓ hA₁ hval cv₁ cv₂ cb₁ cb₂ hdv hdb _ ih (by simp; omega)
  exact ⟨instantiate0 v₃ b₃, zetaSide hW L SL hΓ hA₁ hB₁ cv₁ pv₁ pb₁,
    zetaSide hW L SL hΓ hA₂ hB₂ cv₂ pv₂ pb₂⟩

/-! ### `bvarZeta × bvarZeta` and `eta × eta` fronts under `CR_D` -/

set_option linter.unusedVariables false in
/-- Decorated `bvarZeta × bvarZeta` front under `CR_D` (where `Deco (.bvar i)` is a subsingleton
    and does not syntactically record `stepDeco L hvᵢ`). -/
def BvarZetaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {i : Nat}
    {A v v₁ v₂ T₁ T₂ : Expr Nat} (h : Γ.get? i = some (.letBinding A v))
    {hv₁ : ParRedT PEq E n (Γ.drop (i + 1)) v v₁ A}
    {hl₁ : HasTyT E n Γ (.bvar i) T₁} {hr₁ : HasTyT E n Γ (lift 0 (i + 1) v₁) T₁}
    {hv₂ : ParRedT PEq E n (Γ.drop (i + 1)) v v₂ A}
    {hl₂ : HasTyT E n Γ (.bvar i) T₂} {hr₂ : HasTyT E n Γ (lift 0 (i + 1) v₂) T₂},
    Certified (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv₁ hl₁ hr₁) →
    Certified (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₂ T₂ h hv₂ hl₂ hr₂) →
    Certified hv₁ → Certified hv₂ →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv₁ hl₁ hr₁) +
       sizeOf (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₂ T₂ h hv₂ hl₂ hr₂)) →
    Join E n PEq Γ (lift 0 (i + 1) v₁) (lift 0 (i + 1) v₂) T₁ T₂

/-- Whenever the two let-value steps `hv₁` and `hv₂` share their source decoration
    (`stepDeco L hv₁ = stepDeco L hv₂`, e.g. when both are decorated by the context's canonical
    typing of `v` in `hΓ`), `bvarZeta × bvarZeta` closes from `IHBelowD` and `CertLift` without
    `Retype`. -/
def row_bvarZeta_bvarZeta_deco (L : LeafIface E n PEq) (Lf : CertLift E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {i : Nat} {A v v₁ v₂ T₁ T₂ : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v))
    {hv₁ : ParRedT PEq E n (Γ.drop (i + 1)) v v₁ A}
    (hl₁ : HasTyT E n Γ (.bvar i) T₁)
    {hv₂ : ParRedT PEq E n (Γ.drop (i + 1)) v v₂ A}
    (hl₂ : HasTyT E n Γ (.bvar i) T₂)
    (cv₁ : Certified hv₁) (cv₂ : Certified hv₂)
    (hdv : stepDeco L hv₁ = stepDeco L hv₂)
    {m : Nat} (ih : IHBelowD E n PEq L m) (hsz : sizeOf hv₁ + sizeOf hv₂ < m) :
    Join E n PEq Γ (lift 0 (i + 1) v₁) (lift 0 (i + 1) v₂) T₁ T₂ :=
  row_bvarZeta_bvarZeta Lf h hl₁ hl₂ (ih (ctxWfT_drop hΓ _) cv₁ cv₂ hdv hsz)

set_option linter.unusedVariables false in
/-- Decorated `eta × eta` front under `CR_D` (discharged by `row_eta_eta_deco` whenever the
    η-expansion typings `hl₁` and `hl₂` carry canonical lifted decorations). -/
def EtaEtaD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f f₁ f₂ A B₁ B₂ : Expr Nat}
    {hf₁ : ParRedT PEq E n Γ f f₁ (.pi A B₁)}
    {hl₁ : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₁)}
    {hf₂ : ParRedT PEq E n Γ f f₂ (.pi A B₂)}
    {hl₂ : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₂)},
    Certified (ParRedT.eta (PEq := PEq) Γ f f₁ A B₁ hf₁ hl₁) →
    Certified (ParRedT.eta (PEq := PEq) Γ f f₂ A B₂ hf₂ hl₂) →
    Certified hf₁ → Certified hf₂ →
    stepDeco L (ParRedT.eta (PEq := PEq) Γ f f₁ A B₁ hf₁ hl₁) =
    stepDeco L (ParRedT.eta (PEq := PEq) Γ f f₂ A B₂ hf₂ hl₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.eta (PEq := PEq) Γ f f₁ A B₁ hf₁ hl₁) +
       sizeOf (ParRedT.eta (PEq := PEq) Γ f f₂ A B₂ hf₂ hl₂)) →
    Join E n PEq Γ f₁ f₂ (.pi A B₁) (.pi A B₂)

/-- Canonical η-normalization of a `ParRedT.eta` step: replaces the η-expansion typing witness
    `hl` by the canonical `etaExpansionTy (envClosed_of_envWfT hW) hA (parRedT_hasTy_left ...)`,
    preserving the source, target, index, and certificate while giving `stepDeco` the canonical
    lifted decoration `.lam A _ u (decoOf hA) (.app _ _ (lift 1 1 B) (decoLift 0 1 (stepDeco L hf)) (.bvar 0))`. -/
def etaCanon (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u))
    {hf : ParRedT PEq E n Γ f f' (.pi A B)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
    (cp : Certified (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl)) (cf : Certified hf) :
    CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B) :=
  let hcl := envClosed_of_envWfT hW
  let hf_ty : HasTyT E n Γ f (.pi A B) := parRedT_hasTy_left L.typed hΓ hf
  ⟨.eta Γ f f' A B hf (etaExpansionTy hcl hA hf_ty), .eta cp.root cf⟩

/-- `stepDeco` of `etaCanon` is the canonical lifted decoration over `stepDeco L hf`. -/
@[simp] theorem stepDeco_etaCanon (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f f' A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u))
    {hf : ParRedT PEq E n Γ f f' (.pi A B)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
    (cp : Certified (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl)) (cf : Certified hf) :
    stepDeco L (etaCanon hW L hΓ hA cp cf).step =
      .lam A (.app (lift 0 1 f) (.bvar 0)) u (decoOf hA)
        (.app (lift 0 1 f) (.bvar 0) (lift 1 1 B) (decoLift 0 1 (stepDeco L hf)) (.bvar 0)) := by
  simp only [etaCanon, stepDeco, decoOf_etaExpansionTy, decoOf_parRedT_hasTy_left]

/-! ### The decorated assembler (`OpenRowsD`, `RowFrontsD`, `assembleD`) -/

/-- The open rows of the decorated diamond `CR_D`.
    Compared with `OpenRows` (`RcicNativeValleyAssemble`):
    * **NO `retype` field**: `refl × q` and `peq × q` close via `join_refl_deco` and
      `join_peq_deco`, and `iotaSpine × q` closes via `join_iotaSpine_left_deco` from `iotaDet` and
      `iotaRefire` alone.
    * Every recursive row receives `stepDeco L p = stepDeco L q` and `IHBelowD`. -/
structure OpenRowsD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type where
  consts_delta : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {ls ls' : List Level}
    {T₁ T₂ : Expr Nat} {m : CheckedMember} {b : Expr Nat} {h : eqNList ls ls'}
    {hl₁ : HasTyT E n Γ (.const r ls) T₁} {hr₁ : HasTyT E n Γ (.const r ls') T₁}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hl₂ : HasTyT E n Γ (.const r ls) T₂} {hr₂ : HasTyT E n Γ (instantiateLevels ls b) T₂},
    Certified (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl₁ hr₁) →
    Certified (ParRedT.delta (PEq := PEq) Γ r ls m b T₂ hres hbody htr hlen hwf hl₂ hr₂) →
    Join E n PEq Γ (.const r ls') (instantiateLevels ls b) T₁ T₂
  subst0 : CertSubst0 E n PEq
  app_beta : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A body f' arg a' A' B' T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ (.lam A body) f' T₀} {hc : TyConvT E n Γ T₀ (.pi A' B')}
    {hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w)}
    {ha : ParRedT PEq E n Γ arg a' A'} {hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B')}
    {body' arg' B : Expr Nat} {u v' w' : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)},
    Certified (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
      ha hr) →
    Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
      hred) →
    Certified hf → Certified ha → Certified hb → Certified ha₂ →
    stepDeco L (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
      ha hr) =
    stepDeco L (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
      hred) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
        ha hr) +
       sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
        hred)) →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B)
  lam_eta : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' f body' B₁ f' B₂ : Expr Nat} {u v : Level}
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
    stepDeco L (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
      hA hB hb hrt) =
    stepDeco L (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
        hA hB hb hrt) +
       sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl)) →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂)
  letE_letE : ∀ {Γ : LCtx}, CtxWfT E n Γ →
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
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) =
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
      hB₂ hTy₂ hb₂ hrt₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
        hB₂ hTy₂ hb₂ hrt₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂)
  letE_zeta : ∀ {Γ : LCtx}, CtxWfT E n Γ →
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
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
      hB₁ hTy₁ hb₁ hrt₁) =
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂)
  zeta_zeta : ∀ {Γ : LCtx}, CtxWfT E n Γ →
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
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
      hb₁ hred₁) =
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
      hb₂ hred₂) →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
        hb₁ hred₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (instantiate0 value₁ body₁) (instantiate0 value₂ body₂)
      (instantiate0 value B₁) (instantiate0 value B₂)
  iotaDet : IotaDetU E
  iotaRefire : IotaRefireT E n PEq
  bvarZeta_bvarZeta : BvarZetaD E n PEq L
  eta_eta : EtaEtaD E n PEq L

/-- The decorated fronts that `OpenRowsD` reduces to: `Retype`, `PropAlign`, and `PiPropCodom` are
    eliminated and replaced by `ZeroSortCoherence E n`. -/
structure RowFrontsD (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (L : LeafIface E n PEq) : Type where
  zsc : HostPropAudit.ZeroSortCoherence E n
  iotaDet : IotaDetU E
  iotaRefire : IotaRefireT E n PEq
  appBetaEta : AppBetaEtaD E n PEq L
  appBetaIota : AppBetaIotaD E n PEq L
  lamEtaApp : LamEtaAppD E n PEq L
  lamEtaBeta : LamEtaBetaD E n PEq L
  lamEtaIota : LamEtaIotaD E n PEq L
  letJoin : LetJoinD E n PEq L
  bvarZeta : BvarZetaD E n PEq L
  etaEta : EtaEtaD E n PEq L

/-- Assemble `OpenRowsD` from `RowFrontsD` without `Retype`, `PropAlign`, or `PiPropCodom`. -/
noncomputable def openRowsD_of (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (F : RowFrontsD E n PEq L) : OpenRowsD E n PEq L :=
  let S : CertSubst0 E n PEq := certSubst0_of hW L hPEqL
  let SL : CertSubstLet E n PEq := certSubstLet_of hW L hPEqL
  let Ac : CertAssumpCtx E n PEq :=
    certAssumpCtx_of (PEq := PEq) (envClosed_of_envWfT hW)
      (fun hcc hp => hPEqC_ofAssump (PEq := PEq) (fun hcc' hp' => hPEqC hcc' hp') hcc hp)
  let Lc : CertLetAnnCtx E n PEq :=
    certLetAnnCtx_of (PEq := PEq) (envClosed_of_envWfT hW) (fun hcc hp => hPEqC hcc hp)
  { consts_delta := consts_delta_of hW L
    subst0 := S
    app_beta := app_beta_deco hW L F.zsc S Ac F.appBetaEta F.appBetaIota
    lam_eta := lam_eta_deco hW L F.zsc F.lamEtaApp F.lamEtaBeta F.lamEtaIota
    letE_letE := letE_letE_deco hW L Lc F.letJoin
    letE_zeta := letE_zeta_deco hW L Lc SL F.letJoin
    zeta_zeta := zeta_zeta_deco hW L SL F.letJoin
    iotaDet := F.iotaDet
    iotaRefire := F.iotaRefire
    bvarZeta_bvarZeta := F.bvarZeta
    eta_eta := F.etaEta }

/-- Second step against a `sortEq` root under `CR_D`. -/
noncomputable def withSortEqD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {l₁ l₂ : Level} {T₁ : Expr Nat} {h : eqN l₁ l₂}
    {hl : HasTyT E n Γ (.sort l₁) T₁} {hr : HasTyT E n Γ (.sort l₂) T₁}
    (cp : Certified (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .sort l₁) →
    stepDeco L (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h hl hr) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L (sizeOf (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h hl hr) + sizeOf q) →
    Join E n PEq Γ (.sort l₂) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, cq@(@Certified.sortEq _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact row_sortEq_sortEq cp cq
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against a `consts` root under `CR_D`. -/
noncomputable def withConstsD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls ls' : List Level} {T₁ : Expr Nat} {h : eqNList ls ls'}
    {hl : HasTyT E n Γ (.const r ls) T₁} {hr : HasTyT E n Γ (.const r ls') T₁}
    (cp : Certified (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .const r ls) →
    stepDeco L (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl hr) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L (sizeOf (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl hr) + sizeOf q) →
    Join E n PEq Γ (.const r ls') e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact row_consts_consts cp cq
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact R.consts_delta hΓ cp cq
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against a `delta` root under `CR_D`. -/
noncomputable def withDeltaD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b T₁ : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b} {htr : transparent m.mclass = true}
    {hlen : ls.length = m.arity} {hwf : levelsBounded n ls = true}
    {hl : HasTyT E n Γ (.const r ls) T₁} {hr : HasTyT E n Γ (instantiateLevels ls b) T₁}
    (cp : Certified (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .const r ls) →
    stepDeco L (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl hr) =
      hb ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl hr) + sizeOf q) →
    Join E n PEq Γ (instantiateLevels ls b) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact join_swap_indep (R.consts_delta hΓ cq cp)
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact row_delta_delta cp cq
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against a `bvarZeta` root under `CR_D`. -/
noncomputable def withBvarZetaD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {i : Nat} {A v v₁ T₁ : Expr Nat} {h : Γ.get? i = some (.letBinding A v)}
    {hv : ParRedT PEq E n (Γ.drop (i + 1)) v v₁ A}
    {hl : HasTyT E n Γ (.bvar i) T₁} {hr : HasTyT E n Γ (lift 0 (i + 1) v₁) T₁}
    (cp : Certified (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv hl hr)) (cv : Certified hv) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .bvar i) →
    stepDeco L (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv hl hr) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv hl hr) + sizeOf q) →
    Join E n PEq Γ (lift 0 (i + 1) v₁) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, @Certified.bvarZeta _ _ _ _ _ _ _ _ _ h₂ _ _ _ c₂ cv₂, hb, _, ih => by
      cases hb
      have e := Option.some.inj (h.symm.trans h₂)
      cases e
      exact R.bvarZeta_bvarZeta hΓ h cp (.bvarZeta c₂ cv₂) cv cv₂ ih
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against an `app` root under `CR_D`. -/
noncomputable def withAppD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
    {ha : ParRedT PEq E n Γ a a' A} {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
    (cp : Certified (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr))
    (cf : Certified hf) (ca : Certified ha) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .app f a) →
    stepDeco L (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) =
      hb ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) + sizeOf q) →
    Join E n PEq Γ (.app f' a') e (instantiate0 a B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, @Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf₂ ca₂, hb, hd, ih => by
      cases hb
      exact row_app_app_deco hW L hΓ cf ca cf₂ ca₂ hd ih (by simp <;> omega) (by simp <;> omega)
  | _, _, _, _, cq@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂ ca₂), hb, hd,
      ih => by
      cases hb
      exact R.app_beta hΓ cp cq cf ca cb₂ ca₂ hd ih
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against a `beta` root under `CR_D`. -/
noncomputable def withBetaD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body body' arg arg' B : Expr Nat} {u v w : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w)}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B} {ha : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (cp : Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v w hA hB hTy hb ha hred))
    (cb : Certified hb) (ca : Certified ha) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb_eq : b' = .app (.lam A body) arg) →
    stepDeco L (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v w hA hB hTy hb ha hred) =
      hb_eq ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v w hA hB hTy hb ha hred) +
       sizeOf q) →
    Join E n PEq Γ (instantiate0 arg' body') e (instantiate0 arg B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb_eq, hd, ih => by
      subst hb_eq
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb_eq, hd, ih => by
      subst hb_eq
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .consts .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .bvarZeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .delta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, cq@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf₂ ca₂), hb_eq, hd,
      ih => by
      cases hb_eq
      exact join_swap_indep (R.app_beta hΓ cq cp cf₂ ca₂ cb ca hd.symm (IHBelowD.comm ih))
  | _, _, _, _, @Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂ ca₂, hb_eq, hd, ih => by
      cases hb_eq
      exact row_beta_beta_deco L R.subst0 hΓ cb ca cb₂ ca₂ hd ih
        (by simp <;> omega) (by simp <;> omega)
  | _, _, _, _, .lam .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .pi .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .letE .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .zeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .lit .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .eta .., hb_eq, _, _ => nomatch hb_eq

/-- Second step against a `lam` root under `CR_D`. -/
noncomputable def withLamD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' body body' B : Expr Nat} {u v : Level}
    {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {hrt : HasTyT E n Γ (.lam A' body') (.pi A B)}
    (cp : Certified (ParRedT.lam (PEq := PEq) Γ A A' body body' B u v hc hA hB hb hrt))
    (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb_eq : b' = .lam A body) →
    stepDeco L (ParRedT.lam (PEq := PEq) Γ A A' body body' B u v hc hA hB hb hrt) =
      hb_eq ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' body body' B u v hc hA hB hb hrt) + sizeOf q) →
    Join E n PEq Γ (.lam A' body') e (.pi A B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb_eq, hd, ih => by
      subst hb_eq
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb_eq, hd, ih => by
      subst hb_eq
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .consts .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .bvarZeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .delta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .app .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .beta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, @Certified.lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂, hb_eq, hd, ih => by
      cases hb_eq
      exact row_lam_lam_deco hW L Ac hΓ cb cb₂ hd ih (by simp <;> omega)
  | _, _, _, _, .pi .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .letE .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .zeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .lit .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, cq@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₂), hb_eq, hd, ih => by
      cases hb_eq
      exact R.lam_eta hΓ cp cq cb cf₂ hd ih

/-- Second step against an `eta` root under `CR_D`. -/
noncomputable def withEtaD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' A B : Expr Nat} {hf : ParRedT PEq E n Γ f f' (.pi A B)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
    (cp : Certified (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl)) (cf : Certified hf) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .lam A (.app (lift 0 1 f) (.bvar 0))) →
    stepDeco L (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L (sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl) + sizeOf q) →
    Join E n PEq Γ f' e (.pi A B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂), hb, hd, ih => by
      cases hb
      exact join_swap_indep (R.lam_eta hΓ cq cp cb₂ cf hd.symm (IHBelowD.comm ih))
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₂), hb, hd, ih => by
      injection hb with e₁ e₂; injection e₂ with e₃ _
      have e₄ := lift_inj 0 _ _ e₃
      subst e₁; subst e₄
      have hbr : hb = rfl := rfl
      rw [hbr] at hd
      exact R.eta_eta hΓ cp cq cf cf₂ hd ih

/-- Second step against a `pi` root under `CR_D`. -/
noncomputable def withPiD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' B B' : Expr Nat} {u v : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hc : ConvT E n Γ A A' (.sort u)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
    {hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v))}
    (cp : Certified (ParRedT.pi (PEq := PEq) Γ A A' B B' u v hA hc hB hcB hrt)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .pi A B) →
    stepDeco L (ParRedT.pi (PEq := PEq) Γ A A' B B' u v hA hc hB hcB hrt) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L (sizeOf (ParRedT.pi (PEq := PEq) Γ A A' B B' u v hA hc hB hcB hrt) + sizeOf q) →
    Join E n PEq Γ (.pi A' B') e (.sort (.imax u v)) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.pi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact row_pi_pi hW hΓ cp cq
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- Second step against a `letE` root under `CR_D`. -/
noncomputable def withLetED (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' value value' body body' B : Expr Nat} {u w : Level}
    {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
    {hv : ParRedT PEq E n Γ value value' A}
    {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
    {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
    {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
    {hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)}
    (cp : Certified (ParRedT.letE (PEq := PEq) Γ A A' value value' body body' B u w hc hA hv hB
      hTy hb hrt))
    (cv : Certified hv) (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb_eq : b' = .letE A value body) →
    stepDeco L (ParRedT.letE (PEq := PEq) Γ A A' value value' body body' B u w hc hA hv hB
      hTy hb hrt) = hb_eq ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A' value value' body body' B u w hc hA hv hB
        hTy hb hrt) + sizeOf q) →
    Join E n PEq Γ (.letE A' value' body') e (instantiate0 value B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb_eq, hd, ih => by
      subst hb_eq
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb_eq, hd, ih => by
      subst hb_eq
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .consts .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .bvarZeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .delta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .app .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .beta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .lam .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .pi .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, cq@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb_eq, hd,
      ih => by
      cases hb_eq
      exact R.letE_letE hΓ cp cq cv cb cv₂ cb₂ hd ih
  | _, _, _, _, cq@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb_eq, hd,
      ih => by
      cases hb_eq
      exact R.letE_zeta hΓ cp cq cv cb cv₂ cb₂ hd ih
  | _, _, _, _, .lit .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .eta .., hb_eq, _, _ => nomatch hb_eq

/-- Second step against a `zeta` root under `CR_D`. -/
noncomputable def withZetaD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value value' body body' B : Expr Nat} {u w : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hv : ParRedT PEq E n Γ value value' A}
    {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
    {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
    {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
    {hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B)}
    (cp : Certified (ParRedT.zeta (PEq := PEq) Γ A value value' body body' B u w hA hv hB hTy hb
      hred))
    (cv : Certified hv) (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb_eq : b' = .letE A value body) →
    stepDeco L (ParRedT.zeta (PEq := PEq) Γ A value value' body body' B u w hA hv hB hTy hb
      hred) = hb_eq ▸ stepDeco L q →
    IHBelowD E n PEq L
      (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value' body body' B u w hA hv hB hTy hb
        hred) + sizeOf q) →
    Join E n PEq Γ (instantiate0 value' body') e (instantiate0 value B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb_eq, hd, _ => by
      subst hb_eq; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb_eq, hd, ih => by
      subst hb_eq
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb_eq, hd, ih => by
      subst hb_eq
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .consts .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .bvarZeta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .delta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .app .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .beta .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .lam .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .pi .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, cq@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb_eq, hd,
      ih => by
      cases hb_eq
      exact join_swap_indep (R.letE_zeta hΓ cq cp cv₂ cb₂ cv cb hd.symm (IHBelowD.comm ih))
  | _, _, _, _, cq@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb_eq, hd,
      ih => by
      cases hb_eq
      exact R.zeta_zeta hΓ cp cq cv cb cv₂ cb₂ hd ih
  | _, _, _, _, .lit .., hb_eq, _, _ => nomatch hb_eq
  | _, _, _, _, .eta .., hb_eq, _, _ => nomatch hb_eq

/-- Second step against a `lit` root under `CR_D`. -/
noncomputable def withLitD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {t : Nat} {T₁ : Expr Nat} {hexp : HasTyT E n Γ (natExpand t) T₁}
    (cp : Certified (ParRedT.lit (PEq := PEq) Γ t T₁ hexp)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q →
    (hb : b' = .lit t) →
    stepDeco L (ParRedT.lit (PEq := PEq) Γ t T₁ hexp) = hb ▸ stepDeco L q →
    IHBelowD E n PEq L (sizeOf (ParRedT.lit (PEq := PEq) Γ t T₁ hexp) + sizeOf q) →
    Join E n PEq Γ (natExpand t) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_refl_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, hd, _ => by
      subst hb; exact join_swap_indep (join_peq_deco hW L hΓ h' ⟨_, cp⟩ hd.symm)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, hd, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' hd (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, hd, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd.symm
        (join_swap_indep (ih hΓ cp cs hd (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _, _ => nomatch hb
  | _, _, _, _, .app .., hb, _, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.lit _ _ _ _ _ _ _ _), hb, _, _ => by
      cases hb; exact row_lit_lit cp cq
  | _, _, _, _, .eta .., hb, _, _ => nomatch hb

/-- The decorated certified diamond (`CR_D`), assembled from `OpenRowsD` without `Retype`:
    recursion on `sizeOf p + sizeOf q`, preserving `stepDeco L p = stepDeco L q` across `conv`
    peeling, `iotaSpine` peeling, and child congruence calls. -/
noncomputable def assembleD (hW : EnvWfT E) (L : LeafIface E n PEq) (R : OpenRowsD E n PEq L)
    (Ac : CertAssumpCtx E n PEq) :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) → {b d e T₁ T₂ : Expr Nat} →
    {p : ParRedT PEq E n Γ b d T₁} → Certified p → {q : ParRedT PEq E n Γ b e T₂} →
    Certified q → stepDeco L p = stepDeco L q → Join E n PEq Γ d e T₁ T₂
  | _, hΓ, _, _, _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc _ ch, _, cq, hd =>
      let ⟨f, p', q'⟩ := assembleD hW L R Ac hΓ ch cq hd
      ⟨f, p'.reindex hc, q'⟩
  | _, hΓ, _, _, _, _, _, _, @Certified.refl _ _ _ _ _ _ h _, _, cq, hd =>
      join_refl_deco hW L hΓ h ⟨_, cq⟩ hd
  | _, hΓ, _, _, _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, _, cq, hd =>
      join_peq_deco hW L hΓ h ⟨_, cq⟩ hd
  | _, hΓ, _, _, _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, _, cq, hd =>
      join_iotaSpine_left_deco hW L R.iotaDet R.iotaRefire hΓ hI hrhs
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) _ hd
        (assembleD hW L R Ac hΓ cs cq hd)
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.sortEq _ _ _ _ _ _ _ _ _ _ _), _, cq, hd =>
      withSortEqD hW L R Ac hΓ cp cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), _, cq, hd =>
      withConstsD hW L R Ac hΓ cp cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.bvarZeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv), _, cq, hd =>
      withBvarZetaD hW L R Ac hΓ cp cv cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, cq, hd =>
      withDeltaD hW L R Ac hΓ cp cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf ca),
      _, cq, hd =>
      withAppD hW L R Ac hΓ cp cf ca cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb ca),
      _, cq, hd =>
      withBetaD hW L R Ac hΓ cp cb ca cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb), _, cq, hd =>
      withLamD hW L R Ac hΓ cp cb cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.pi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, cq, hd =>
      withPiD hW L R Ac hΓ cp cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _,
      cp@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv cb), _, cq, hd =>
      withLetED hW L R Ac hΓ cp cv cb cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _,
      cp@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv cb), _, cq, hd =>
      withZetaD hW L R Ac hΓ cp cv cb cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.lit _ _ _ _ _ _ _ _), _, cq, hd =>
      withLitD hW L R Ac hΓ cp cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf), _, cq, hd =>
      withEtaD hW L R Ac hΓ cp cf cq rfl hd
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' hd' _ => assembleD hW L R Ac hΓ' cp' cq' hd')
termination_by _ _ _ _ _ _ _ p _ q _ _ => sizeOf p + sizeOf q
decreasing_by all_goals (first | assumption | (simp_wf; assumption) | (simp <;> omega) | (simp_wf; simp <;> omega))

/-- `CoreDiamondD` from `OpenRowsD`. -/
noncomputable def coreDiamondD_of_rowsD (hW : EnvWfT E) (L : LeafIface E n PEq)
    (R : OpenRowsD E n PEq L) (Ac : CertAssumpCtx E n PEq) : CoreDiamondD E n PEq L :=
  fun {_} hΓ {_ _ _ _ _} p q hd => assembleD hW L R Ac hΓ p.cert q.cert hd

/-- `CDiamondD` from `OpenRowsD`. -/
noncomputable def cdiamondD_of_rowsD (hW : EnvWfT E) (L : LeafIface E n PEq)
    (R : OpenRowsD E n PEq L) (Ac : CertAssumpCtx E n PEq) : CDiamondD E n PEq L :=
  fun {_} hΓ {_ _ _ _} p q hd => assembleD hW L R Ac hΓ p.cert q.cert hd

/-- `CDiamondD` from `RowFrontsD` without `Retype`, `PropAlign`, or `PiPropCodom`. -/
noncomputable def cdiamondD_of_frontsD (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (F : RowFrontsD E n PEq L) : CDiamondD E n PEq L :=
  let Ac : CertAssumpCtx E n PEq :=
    certAssumpCtx_of (PEq := PEq) (envClosed_of_envWfT hW)
      (fun hcc hp => hPEqC_ofAssump (PEq := PEq) (fun hcc' hp' => hPEqC hcc' hp') hcc hp)
  cdiamondD_of_rowsD hW L (openRowsD_of hW L hPEqL hPEqC F) Ac

/-- A multi-step certified valley join at independent indices (`CStar` on both legs): the
    postponed/multi-step counterpart of `Join` for peaks where an irrelevance leaf inside an
    η-expansion body prevents a one-step join (`NATIVE_VALLEYS_STATUS.md` §8b). -/
abbrev ValleyJoin (E : ResolvedEnv) (n : Nat) (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ : LCtx) (d e T₁ T₂ : Expr Nat) : Type :=
  Σ' (f : Expr Nat), CStar E n PEq Γ d f T₁ ×' CStar E n PEq Γ e f T₂

/-- Every one-step `Join` is a `ValleyJoin`. -/
def ValleyJoin.ofJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {d e T₁ T₂ : Expr Nat} (j : Join E n PEq Γ d e T₁ T₂) : ValleyJoin E n PEq Γ d e T₁ T₂ :=
  ⟨j.1, CStar.ofStep L hΓ j.2.1, CStar.ofStep L hΓ j.2.2⟩

/-- The `RcicNativeValleyEtaLeaf` counterexample (`etaLeafLamStep` vs `etaLeafEtaStep`, which has
    no one-step `Join` by `etaLeaf_no_join`) joins in TWO certified steps on the λ side
    (`d ⇒ b ⇒ f`) and zero steps on the η side (`f ⇒* f`): first the symmetric irrelevance leaf
    `.bvar 0 ⇒ .bvar 1` under the binder restores the lifted term `lift 0 1 etaLeafF`, and then
    `etaLeafEtaStep` contracts the η-redex to `etaLeafF`. -/
def etaLeaf_valleyJoin (L : LeafIface E n PEq) :
    ValleyJoin E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody') etaLeafF
      (.pi etaLeafP (.sort .zero)) (.pi etaLeafP (.sort .zero)) :=
  let revLeaf : PEq etaLeafCtx₁ (.bvar 0) (.bvar 1) etaLeafP :=
    L.ofIrr (etaLeafP_ty _) etaLeafY_var₁ etaLeafP_var₁
  let revLeafConv : ConvT E n etaLeafCtx₁ (.bvar 0) (.bvar 1) etaLeafP :=
    .irr _ etaLeafP (.bvar 0) (.bvar 1) (etaLeafP_ty _) etaLeafY_var₁ etaLeafP_var₁
  let revInnerStep : ParRedT PEq E n etaLeafCtx₁ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF)
      (.pi etaLeafP (.sort .zero)) :=
    .app _ (.bvar 2) (.bvar 2) (.bvar 0) (.bvar 1) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX
      (.imax .zero (.succ .zero)) (.imax .zero (.succ .zero))
      (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) (.refl _ _) (etaLeafPiP_ty _) (etaLeafPiP_ty _)
      (.peq _ (.bvar 0) (.bvar 1) etaLeafP revLeaf) etaLeafLiftF_ty
  let revInnerConv : ConvT E n etaLeafCtx₁ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF)
      (.pi etaLeafP (.sort .zero)) :=
    .app _ (.bvar 2) (.bvar 2) (.bvar 0) (.bvar 1) etaLeafP (.pi etaLeafP (.sort .zero))
      (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) revLeafConv
  let revInnerCert : Certified revInnerStep :=
    .app revInnerConv (.refl (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁)) (.peq revLeafConv)
  let revBodyStep : ParRedT PEq E n etaLeafCtx₁ etaLeafBody' etaLeafBody (.sort .zero) :=
    .app _ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
      (.pi etaLeafP (.sort .zero)) (.succ .zero) (.succ .zero)
      revInnerStep (.refl _ _) (.sort _ _) (.sort _ _)
      (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁) etaLeafBody_ty
  let revBodyConv : ConvT E n etaLeafCtx₁ etaLeafBody' etaLeafBody (.sort .zero) :=
    .app _ (.app (.bvar 2) (.bvar 0)) (lift 0 1 etaLeafF) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
      revInnerConv (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁)
  let revBodyCert : Certified revBodyStep :=
    .app revBodyConv revInnerCert (.refl (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁))
  let revLamStep : ParRedT PEq E n etaLeafCtx (.lam etaLeafP etaLeafBody')
      (.lam etaLeafP etaLeafBody) (.pi etaLeafP (.sort .zero)) :=
    .lam _ etaLeafP etaLeafP etaLeafBody' etaLeafBody (.sort .zero) .zero (.succ .zero)
      (.refl _ etaLeafP _ (etaLeafP_ty _)) (etaLeafP_ty _) (.sort _ _) revBodyStep etaLeafB_ty
  let revLamCert : Certified revLamStep :=
    .lam (.lam _ etaLeafP etaLeafP etaLeafBody' etaLeafBody (.sort .zero) .zero
      (.refl _ etaLeafP _ (etaLeafP_ty _)) revBodyConv) revBodyCert
  let step1 : CStep E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody')
      (.lam etaLeafP etaLeafBody) (.pi etaLeafP (.sort .zero)) :=
    ⟨revLamStep, revLamCert⟩
  let step2 : CStep E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody) etaLeafF
      (.pi etaLeafP (.sort .zero)) :=
    ⟨etaLeafEtaStep, etaLeafEtaCert⟩
  ⟨etaLeafF,
    .tail step1 (.tail step2 (.refl etaLeafCtx etaLeafF _ etaLeafF_ty)),
    .refl etaLeafCtx etaLeafF _ etaLeafF_ty⟩

#print axioms CDiamondD
#print axioms CoreDiamondD
#print axioms uniqParRedTD
#print axioms cdiamondD_of_coreDiamondD
#print axioms coreDiamondD_of_cdiamondD
#print axioms IHBelowD
#print axioms IHBelowD.mono
#print axioms IHBelowD.comm
#print axioms join_refl_deco
#print axioms join_peq_deco
#print axioms row_app_app_deco
#print axioms row_lam_lam_deco
#print axioms row_beta_beta_deco
#print axioms argJoin_deco
#print axioms betaLeftReindex_deco
#print axioms AppBetaEtaD
#print axioms AppBetaIotaD
#print axioms appBetaCore_deco
#print axioms app_beta_deco
#print axioms etaExpansionBodyTy
#print axioms etaExpansionTy
#print axioms decoOf_etaExpansionBodyTy
#print axioms decoOf_etaExpansionTy
#print axioms unlift_stepDeco_eq
#print axioms lamEtaApp_of_unlift_deco
#print axioms stepDeco_etaAtConverted
#print axioms row_eta_eta_deco
#print axioms LamEtaAppD
#print axioms LamEtaBetaD
#print axioms LamEtaIotaD
#print axioms lamEtaCore_deco
#print axioms lam_eta_deco
#print axioms iotaCommute_deco
#print axioms join_iotaSpine_left_deco
#print axioms LetJoinD
#print axioms letE_letE_deco
#print axioms letE_zeta_deco
#print axioms zeta_zeta_deco
#print axioms BvarZetaD
#print axioms row_bvarZeta_bvarZeta_deco
#print axioms EtaEtaD
#print axioms OpenRowsD
#print axioms RowFrontsD
#print axioms openRowsD_of
#print axioms withSortEqD
#print axioms withConstsD
#print axioms withDeltaD
#print axioms withBvarZetaD
#print axioms withAppD
#print axioms withBetaD
#print axioms withLamD
#print axioms withEtaD
#print axioms withPiD
#print axioms withLetED
#print axioms withZetaD
#print axioms withLitD
#print axioms assembleD
#print axioms coreDiamondD_of_rowsD
#print axioms cdiamondD_of_rowsD
#print axioms cdiamondD_of_frontsD
#print axioms ValleyJoin
#print axioms ValleyJoin.ofJoin
#print axioms etaLeaf_valleyJoin
#print axioms letSourceJoin_deco
#print axioms CertLetValCtx
#print axioms letJoinD_of_letValCtx
#print axioms etaCanon
#print axioms stepDeco_etaCanon

end Rcic.Declarative.NativeValleys
