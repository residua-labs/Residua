import rcic.RcicNativeValleyDeco
import rcic.RcicNativeValleySubst
import rcic.RcicNativeValleyLetCtx

/-!
# RcicNativeValleyDecoBook — decoration bookkeeping for the decorated diamond route
(`NATIVE_VALLEYS_STATUS.md` §9c/§9e)

Makes the decoration operations of the decorated Church–Rosser route explicit and proves their
commutation laws with the landed certified step transports:

* `stepDeco` — the source decoration of a `ParRedT` step, read directly without a `CtxWfT`
  witness, and `decoOf_leftTyped` (`decoOf (s.leftTyped L hΓ) = stepDeco L s.step`).
* `uniqStepD` — two certified steps out of one term with the same `stepDeco` have convertible
  indices (`TyConvT`), via `uniqD`.
* `stepDeco_reindex`, `stepDeco_peel` — index conversion and `.conv` peeling preserve `stepDeco`.
* `decoOf_hasTyT_ctx`, `stepDeco_cstep_ctxTransport`, `stepDeco_cstep_assumpCtx`,
  `stepDeco_cstep_letAnnCtx` — context conversions preserve decorations identically.
* `decoLift`, `decoLift_one_inj`, `decoOf_hasTyTWeaken`, `stepDeco_cstep_lift`,
  `stepDeco_cstep_lift_lctx` — weakening commutes with `decoLift`.
* `decoSubst`, `decoOf_hasTyT_substS`, `decoOf_hasTyT_substLetS`, `decoOf_tySubst`,
  `stepDeco_csubst_arg`, `stepDeco_csubstMixed`, `stepDeco_certSubst0` — substitution and
  one-step certified mixed substitution commute with `decoSubst`.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### cast and subsingleton helpers on `Deco` -/

@[simp] theorem eq_mpr_trans {α β γ : Sort _} (h₁ : α = β) (h₂ : β = γ) (x : γ) :
    Eq.mpr h₁ (Eq.mpr h₂ x) = Eq.mpr (h₁.trans h₂) x := by
  cases h₁; cases h₂; rfl

@[simp] theorem eq_mp_trans {α β γ : Sort _} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    Eq.mp h₂ (Eq.mp h₁ x) = Eq.mp (h₁.trans h₂) x := by
  cases h₁; cases h₂; rfl

/-- `Deco (.sort l)` is a subsingleton: any two decorations of a sort expression coincide. -/
theorem deco_subsingleton_sort {e : Expr Nat} {l : Level} (he : e = .sort l)
    (d₁ d₂ : Deco e) : d₁ = d₂ := by
  subst he; cases d₁; cases d₂; rfl

/-- `Deco (.bvar i)` is a subsingleton: any two decorations of a bound variable coincide. -/
theorem deco_subsingleton_bvar {e : Expr Nat} {i : Nat} (he : e = .bvar i)
    (d₁ d₂ : Deco e) : d₁ = d₂ := by
  subst he; cases d₁; cases d₂; rfl

/-- `Deco (.const r ls)` is a subsingleton: any two decorations of a constant coincide. -/
theorem deco_subsingleton_const {e : Expr Nat} {r : Nat} {ls : List Level}
    (he : e = .const r ls) (d₁ d₂ : Deco e) : d₁ = d₂ := by
  subst he; cases d₁; cases d₂; rfl

/-- `Deco (lift c k (.bvar i))` is a subsingleton. -/
theorem deco_lift_bvar_subsingleton (c k i : Nat) (d₁ d₂ : Deco (lift c k (.bvar i))) :
    d₁ = d₂ := by
  by_cases h : c ≤ i
  · exact deco_subsingleton_bvar (e := lift c k (.bvar i)) (i := i + k)
      (by simp only [lift, if_pos h]) d₁ d₂
  · exact deco_subsingleton_bvar (e := lift c k (.bvar i)) (i := i)
      (by simp only [lift, if_neg h]) d₁ d₂

/-- `Deco (instantiate j w (.bvar i))` is a subsingleton whenever `i ≠ j`. -/
theorem deco_instantiate_bvar_ne_subsingleton (j i : Nat) (w : Expr Nat) (hij : i ≠ j)
    (d₁ d₂ : Deco (instantiate j w (.bvar i))) : d₁ = d₂ := by
  by_cases hgt : j < i
  · exact deco_subsingleton_bvar (e := instantiate j w (.bvar i)) (i := i - 1)
      (by simp only [instantiate, if_neg hij, if_pos hgt]) d₁ d₂
  · exact deco_subsingleton_bvar (e := instantiate j w (.bvar i)) (i := i)
      (by simp only [instantiate, if_neg hij, if_neg hgt]) d₁ d₂

/-- Stripping a dependent `Eq.mpr` on `HasTyT`: `decoOf` depends only on the term index `e`. -/
theorem decoOf_eq_mpr {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
    (hΓ : Γ₁ = Γ₂) (he : e₁ = e₂) (hT : T₁ = T₂)
    (hEq : HasTyT E n Γ₁ e₁ T₁ = HasTyT E n Γ₂ e₂ T₂)
    (x : HasTyT E n Γ₂ e₂ T₂) :
    decoOf (Eq.mpr hEq x) = he ▸ decoOf x := by
  subst hΓ; subst he; subst hT; cases hEq; rfl

/-- Stripping a dependent `Eq.mp` on `HasTyT`: `decoOf` depends only on the term index `e`. -/
theorem decoOf_eq_mp {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
    (hΓ : Γ₁ = Γ₂) (he : e₁ = e₂) (hT : T₁ = T₂)
    (hEq : HasTyT E n Γ₁ e₁ T₁ = HasTyT E n Γ₂ e₂ T₂)
    (x : HasTyT E n Γ₁ e₁ T₁) :
    decoOf (Eq.mp hEq x) = he ▸ decoOf x := by
  subst hΓ; subst he; subst hT; cases hEq; rfl

/-- Forward `Eq.mp` followed by inverse term cast cancels on `decoOf`. -/
theorem decoOf_eq_mp_cancel {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
    (hΓ : Γ₁ = Γ₂) (he : e₁ = e₂) (hT : T₁ = T₂)
    (hEq : HasTyT E n Γ₁ e₁ T₁ = HasTyT E n Γ₂ e₂ T₂)
    (x : HasTyT E n Γ₁ e₁ T₁) :
    he ▸ decoOf (Eq.mp hEq x) = decoOf x := by
  subst hΓ; subst he; subst hT; cases hEq; rfl

/-- Pushing a body cast through `Deco.app (.lam A ·) arg`. -/
theorem deco_app_lam_cast {A arg B : Expr Nat} {v₁ v₂ : Expr Nat} {j : Nat} {u : Level}
    (hm : v₁ = v₂) (body : Expr Nat) (dA : Deco A)
    (db : Deco (instantiate (j + 1) v₂ body)) (da : Deco arg) :
    (congrArg (fun s => Expr.app (.lam A (instantiate (j + 1) s body)) arg) hm) ▸
      Deco.app (.lam A (instantiate (j + 1) v₂ body)) arg B
        (.lam A (instantiate (j + 1) v₂ body) u dA db) da =
    Deco.app (.lam A (instantiate (j + 1) v₁ body)) arg B
      ((congrArg (fun s => Expr.lam A (instantiate (j + 1) s body)) hm) ▸
        Deco.lam A (instantiate (j + 1) v₂ body) u dA db) da := by
  subst hm; rfl

/-- Injectivity of dependent `▸` transport. -/
theorem eq_rec_inj {α : Type _} {P : α → Type _} {a b : α} (h : a = b) {x y : P a}
    (heq : h ▸ x = h ▸ y) : x = y := by
  subst h; exact heq

/-! ### `stepDeco` and `decoOf` on `leftTyped` -/

/-- Wrapping a typing in a `TyConvT` chain adds only `.conv` layers, preserving `decoOf`. -/
@[simp] theorem decoOf_hasTyT_of_tyConvT {Γ : LCtx} {a A A' : Expr Nat}
    (h : HasTyT E n Γ a A) (hc : TyConvT E n Γ A A') :
    decoOf (hasTyT_of_tyConvT h hc) = decoOf h := by
  induction hc with
  | refl => rfl
  | of => rfl
  | trans _ _ _ _ _ ih₁ ih₂ => rw [hasTyT_of_tyConvT, ih₂, ih₁]

/-- The source decoration of a `ParRedT` step, read directly without a `CtxWfT` witness. -/
def stepDeco (L : LeafIface E n PEq) :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Deco a
  | _, _, _, _, .refl _ _ _ h => decoOf h
  | _, _, _, _, .sortEq _ _ _ _ _ hl _ => decoOf hl
  | _, _, _, _, .consts _ _ _ _ _ _ hl _ => decoOf hl
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ _ hl _ => decoOf hl
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ hl _ => decoOf hl
  | _, _, _, _, .app _ f _ a _ _ B _ _ _ hf _ _ _ ha _ =>
      .app f a B (stepDeco L hf) (stepDeco L ha)
  | _, _, _, _, .beta _ A body _ arg _ B u _ _ hA _ _ hb ha _ =>
      .app (.lam A body) arg B (.lam A body u (decoOf hA) (stepDeco L hb)) (stepDeco L ha)
  | _, _, _, _, .lam _ A _ body _ _ u _ _ hA _ hb _ =>
      .lam A body u (decoOf hA) (stepDeco L hb)
  | _, _, _, _, .pi _ A _ B _ u v hA _ hB _ _ =>
      .pi A B u v (decoOf hA) (decoOf hB)
  | _, _, _, _, .letE _ A _ value _ body _ _ u _ _ hA hv _ _ hb _ =>
      .letE A value body u (decoOf hA) (stepDeco L hv) (stepDeco L hb)
  | _, _, _, _, .zeta _ A value _ body _ _ u _ hA hv _ _ hb _ =>
      .letE A value body u (decoOf hA) (stepDeco L hv) (stepDeco L hb)
  | _, _, _, _, .iotaSpine _ _ _ _ _ hstep _ _ _ => stepDeco L hstep
  | _, _, _, _, .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlhs _ => decoOf hlhs
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ _ hf _ _ _ _ _ _ _ _ _ _ => decoOf hf
  | _, _, _, _, .lit _ t _ hexp => .lit t (decoOf hexp)
  | _, _, _, _, .eta _ _ _ _ _ _ hl => decoOf hl
  | _, _, _, _, .peq _ _ _ _ h => decoOf (L.typed h).1
  | _, _, _, _, .conv _ _ _ _ _ h _ => stepDeco L h

/-- Stripping a dependent `Eq.mpr` on `CStep`: `stepDeco` depends only on the left endpoint `a`. -/
theorem stepDeco_cstep_eq_mpr (L : LeafIface E n PEq)
    {Γ₁ Γ₂ : LCtx} {a₁ a₂ b₁ b₂ T₁ T₂ : Expr Nat}
    (hΓ : Γ₁ = Γ₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hT : T₁ = T₂)
    (hEq : CStep E n PEq Γ₁ a₁ b₁ T₁ = CStep E n PEq Γ₂ a₂ b₂ T₂)
    (s : CStep E n PEq Γ₂ a₂ b₂ T₂) :
    stepDeco L (Eq.mpr hEq s).step = ha ▸ stepDeco L s.step := by
  subst hΓ; subst ha; subst hb; subst hT; cases hEq; rfl

/-- Stripping a dependent `Eq.mp` on `CStep`: `stepDeco` depends only on the left endpoint `a`. -/
theorem stepDeco_cstep_eq_mp (L : LeafIface E n PEq)
    {Γ₁ Γ₂ : LCtx} {a₁ a₂ b₁ b₂ T₁ T₂ : Expr Nat}
    (hΓ : Γ₁ = Γ₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hT : T₁ = T₂)
    (hEq : CStep E n PEq Γ₁ a₁ b₁ T₁ = CStep E n PEq Γ₂ a₂ b₂ T₂)
    (s : CStep E n PEq Γ₁ a₁ b₁ T₁) :
    stepDeco L (Eq.mp hEq s).step = ha ▸ stepDeco L s.step := by
  subst hΓ; subst ha; subst hb; subst hT; cases hEq; rfl

/-- `decoOf` of `(parRedT_typed L.typed hΓ p).1` agrees with `stepDeco` for every `hΓ`. -/
@[simp] theorem decoOf_parRedT_typed_left (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) :
    decoOf (parRedT_typed L.typed hΓ p).1 = stepDeco L p := by
  induction p with
  | refl => rfl
  | sortEq => rfl
  | consts => rfl
  | bvarZeta => rfl
  | delta => rfl
  | app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihf iha =>
      simp only [parRedT_typed, stepDeco, decoOf, decoOf_hasTyT_of_tyConvT, ihf hΓ, iha hΓ]
  | beta Γ A _ _ _ _ _ u _ _ hA _ _ _ _ _ ihb iha =>
      simp only [parRedT_typed, stepDeco, decoOf, ihb (.assumption Γ A u hΓ hA), iha hΓ]
  | lam Γ A _ _ _ _ u _ _ hA _ _ _ ihb =>
      simp only [parRedT_typed, stepDeco, decoOf, ihb (.assumption Γ A u hΓ hA)]
  | pi => rfl
  | letE Γ A _ value _ _ _ _ u _ _ hA hv _ _ _ _ ihv ihb =>
      simp only [parRedT_typed, stepDeco, decoOf, ihv hΓ,
        ihb (.letBinding Γ A u value hΓ hA (parRedT_typed L.typed hΓ hv).1)]
  | zeta Γ A value _ _ _ _ u _ hA hv _ _ _ _ ihv ihb =>
      simp only [parRedT_typed, stepDeco, decoOf, ihv hΓ,
        ihb (.letBinding Γ A u value hΓ hA (parRedT_typed L.typed hΓ hv).1)]
  | iotaSpine _ _ _ _ _ _ _ _ _ ih => exact ih hΓ
  | iotaStarK => rfl
  | iotaStarKEta => rfl
  | lit => rfl
  | eta => rfl
  | peq => rfl
  | conv _ _ _ _ _ _ _ ih =>
      simp only [parRedT_typed, stepDeco, decoOf_hasTyT_of_tyConvT, ih hΓ]

/-- `decoOf` of `parRedT_hasTy_left` agrees with `stepDeco` for every `hΓ`. -/
@[simp] theorem decoOf_parRedT_hasTy_left (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) :
    decoOf (parRedT_hasTy_left L.typed hΓ p) = stepDeco L p :=
  decoOf_parRedT_typed_left L hΓ p

/-- `decoOf` of `CStep.leftTyped` is `stepDeco`. -/
@[simp] theorem decoOf_leftTyped (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) :
    decoOf (s.leftTyped L hΓ) = stepDeco L s.step :=
  decoOf_parRedT_hasTy_left L hΓ s.step

/-- Two certified steps out of one term with the same `stepDeco` have convertible types. -/
noncomputable def uniqStepD (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (p : CStep E n PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂)
    (hd : stepDeco L p.step = stepDeco L q.step) :
    TyConvT E n Γ T₁ T₂ :=
  uniqD hW (p.leftTyped L hΓ) (q.leftTyped L hΓ)
    (by rw [decoOf_leftTyped, decoOf_leftTyped, hd])

/-- Reindexing a certified step preserves `stepDeco` definitionally. -/
@[simp] theorem stepDeco_reindex (L : LeafIface E n PEq)
    {Γ : LCtx} {a b T T' : Expr Nat} (s : CStep E n PEq Γ a b T) (hc : TyConvT E n Γ T T') :
    stepDeco L (s.reindex hc).step = stepDeco L s.step :=
  rfl

/-- Reindexing a certified step preserves `decoOf` of its left typing. -/
@[simp] theorem decoOf_reindex_left (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T T' : Expr Nat}
    (s : CStep E n PEq Γ a b T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) := by
  simp only [decoOf_leftTyped, stepDeco_reindex]

/-- Reindexing a certified step preserves `decoOf` of its right typing. -/
@[simp] theorem decoOf_reindex_right (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T T' : Expr Nat}
    (s : CStep E n PEq Γ a b T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).rightTyped L hΓ) = decoOf (s.rightTyped L hΓ) := by
  simp only [CStep.reindex, CStep.rightTyped, parRedT_hasTy_right, parRedT_typed,
    decoOf_hasTyT_of_tyConvT]

/-- Peeling outer `.conv` layers preserves `stepDeco`. -/
@[simp] theorem stepDeco_peel (L : LeafIface E n PEq)
    {Γ : LCtx} {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) (cp : Certified p) :
    stepDeco L (peel p cp).2.1 = stepDeco L p := by
  induction cp with
  | conv _ _ ih => exact ih
  | _ => rfl

/-! ### context transport preserves decorations -/

/-- `hasTyT_ctx` preserves `decoOf` identically. -/
@[simp] theorem decoOf_hasTyT_ctx (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → (hcc : CtxConvT E n Γ Γ') → {e A : Expr Nat} →
    (h : HasTyT E n Γ e A) → decoOf (hasTyT_ctx hcl hcc h) = decoOf h
  | _, _, _, _, _, .sort _ _ => rfl
  | _, _, _, _, _, .bvar _ _ _ _ => deco_subsingleton_bvar rfl _ _
  | _, _, _, _, _, .const _ _ _ _ _ _ _ => rfl
  | _, _, hcc, _, _, .pi _ A _ _ _ hA hB => by
      simp only [hasTyT_ctx, decoOf, decoOf_hasTyT_ctx hcl hcc hA,
        decoOf_hasTyT_ctx hcl (.same (.assumption A) hcc) hB]
  | _, _, hcc, _, _, .lam _ A _ _ _ hA hbody => by
      simp only [hasTyT_ctx, decoOf, decoOf_hasTyT_ctx hcl hcc hA,
        decoOf_hasTyT_ctx hcl (.same (.assumption A) hcc) hbody]
  | _, _, hcc, _, _, .app _ _ _ _ _ hf ha => by
      simp only [hasTyT_ctx, decoOf, decoOf_hasTyT_ctx hcl hcc hf,
        decoOf_hasTyT_ctx hcl hcc ha]
  | _, _, hcc, _, _, .letE _ A _ value _ _ hA hv hb => by
      simp only [hasTyT_ctx, decoOf, decoOf_hasTyT_ctx hcl hcc hA,
        decoOf_hasTyT_ctx hcl hcc hv,
        decoOf_hasTyT_ctx hcl (.same (.letBinding A value) hcc) hb]
  | _, _, hcc, _, _, .lit _ _ _ hexp => by
      simp only [hasTyT_ctx, decoOf, decoOf_hasTyT_ctx hcl hcc hexp]
  | _, _, hcc, _, _, .conv _ _ _ _ _ h _ => decoOf_hasTyT_ctx hcl hcc h

/-- `cstep_ctxTransport` preserves `stepDeco` whenever the leaf transport preserves `decoOf` of
    its left typing (which holds definitionally for `ProofLeaf`). -/
theorem stepDeco_cstep_ctxTransport (L : LeafIface E n PEq)
    {R : LCtx → LCtx → Type} (I : CtxTransport E n R) (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat}, R Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (hPEqCDeco : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat} (hcc : R Γ Γ') (h : PEq Γ p q T),
      decoOf (L.typed (hPEqC hcc h)).1 = decoOf (L.typed h).1)
    {Γ Γ' : LCtx} (hcc : R Γ Γ') {a b T : Expr Nat}
    {p : ParRedT PEq E n Γ a b T} (cp : Certified p) :
    stepDeco L (cstep_ctxTransport (PEq := PEq) I hcl hPEqC hcc cp).step = stepDeco L p := by
  induction cp generalizing Γ' with
  | refl => simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | sortEq => simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | consts => simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | bvarZeta => simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | delta => simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | app _ cf ca ihf iha =>
      simp only [cstep_ctxTransport, stepDeco, ihf hcc, iha hcc]
  | beta _ cb ca ihb iha =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx,
        ihb (I.same _ hcc), iha hcc]
  | lam _ cb ihb =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx, ihb (I.same _ hcc)]
  | pi =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | letE _ cv cb ihv ihb =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx,
        ihv hcc, ihb (I.same _ hcc)]
  | zeta _ cv cb ihv ihb =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx,
        ihv hcc, ihb (I.same _ hcc)]
  | iotaSpine _ _ ih =>
      simp only [cstep_ctxTransport, stepDeco, ih hcc]
  | lit =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | eta =>
      simp only [cstep_ctxTransport, stepDeco, decoOf_hasTyT_ctx]
  | peq _ =>
      simp only [cstep_ctxTransport, stepDeco, hPEqCDeco hcc]
  | conv _ _ ih =>
      simp only [cstep_ctxTransport, stepDeco, ih hcc]

/-- `cstep_assumpCtx` preserves `stepDeco`. -/
theorem stepDeco_cstep_assumpCtx (L : LeafIface E n PEq) (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
      F8EtaK.AssumpCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (hPEqCDeco : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat}
      (hcc : F8EtaK.AssumpCtxConvT E n Γ Γ') (h : PEq Γ p q T),
      decoOf (L.typed (hPEqC hcc h)).1 = decoOf (L.typed h).1)
    {Γ Γ' : LCtx} (hcc : F8EtaK.AssumpCtxConvT E n Γ Γ') {a b T : Expr Nat}
    {p : ParRedT PEq E n Γ a b T} (cp : Certified p) :
    stepDeco L (cstep_assumpCtx (PEq := PEq) hcl hPEqC hcc cp).step = stepDeco L p :=
  stepDeco_cstep_ctxTransport L assumpCtxTransport hcl hPEqC hPEqCDeco hcc cp

/-- `cstep_letAnnCtx` preserves `stepDeco`. -/
theorem stepDeco_cstep_letAnnCtx (L : LeafIface E n PEq) (hcl : EnvClosed E)
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
      LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (hPEqCDeco : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat}
      (hcc : LetAnnCtxConvT E n Γ Γ') (h : PEq Γ p q T),
      decoOf (L.typed (hPEqC hcc h)).1 = decoOf (L.typed h).1)
    {Γ Γ' : LCtx} (hcc : LetAnnCtxConvT E n Γ Γ') {a b T : Expr Nat}
    {p : ParRedT PEq E n Γ a b T} (cp : Certified p) :
    stepDeco L (cstep_letAnnCtx (PEq := PEq) hcl hPEqC hcc cp).step = stepDeco L p :=
  stepDeco_cstep_ctxTransport L letAnnCtxTransport hcl hPEqC hPEqCDeco hcc cp

/-! ### `decoLift` and weakening commutation -/

/-- Lifting a decoration at cutoff `c` by `k`. -/
def decoLift (c k : Nat) : {e : Expr Nat} → Deco e → Deco (lift c k e)
  | _, .sort l => .sort l
  | _, .bvar i => by
      by_cases hic : i < c
      · simp only [lift, if_neg (by omega : ¬ c ≤ i)]
        exact .bvar i
      · simp only [lift, if_pos (by omega : c ≤ i)]
        exact .bvar (i + k)
  | _, .const r ls => .const r ls
  | _, .pi A B u v dA dB =>
      .pi (lift c k A) (lift (c + 1) k B) u v (decoLift c k dA) (decoLift (c + 1) k dB)
  | _, .lam A body u dA db =>
      .lam (lift c k A) (lift (c + 1) k body) u (decoLift c k dA) (decoLift (c + 1) k db)
  | _, .app f a B df da =>
      .app (lift c k f) (lift c k a) (lift (c + 1) k B) (decoLift c k df) (decoLift c k da)
  | _, .letE A value body u dA dv db =>
      .letE (lift c k A) (lift c k value) (lift (c + 1) k body) u
        (decoLift c k dA) (decoLift c k dv) (decoLift (c + 1) k db)
  | _, .lit t d =>
      .lit t (natExpand_lift c k t ▸ decoLift c k d)

/-- `lift c 1` is injective on `Expr Nat` (via `instantiate_lift_id`). -/
theorem lift_one_inj (c : Nat) {e₁ e₂ : Expr Nat} (h : lift c 1 e₁ = lift c 1 e₂) : e₁ = e₂ := by
  have h' := congrArg (instantiate c (.sort .zero)) h
  rwa [instantiate_lift_id, instantiate_lift_id] at h'

/-- `decoLift c 1` is injective on `Deco e`. -/
theorem decoLift_one_inj : {c : Nat} → {e : Expr Nat} → {d₁ d₂ : Deco e} →
    decoLift c 1 d₁ = decoLift c 1 d₂ → d₁ = d₂
  | _, _, .sort _, .sort _, _ => rfl
  | _, _, .bvar _, .bvar _, _ => rfl
  | _, _, .const _ _, .const _ _, _ => rfl
  | _, _, .pi _ _ _ _ dA₁ dB₁, .pi _ _ _ _ dA₂ dB₂, h => by
      simp only [decoLift] at h
      injection h with _ _ hu hv hdA hdB
      subst hu; subst hv
      rw [decoLift_one_inj hdA, decoLift_one_inj hdB]
  | _, _, .lam _ _ _ dA₁ db₁, .lam _ _ _ dA₂ db₂, h => by
      simp only [decoLift] at h
      injection h with _ _ hu hdA hdb
      subst hu
      rw [decoLift_one_inj hdA, decoLift_one_inj hdb]
  | c, _, .app _ _ B₁ df₁ da₁, .app _ _ B₂ df₂ da₂, h => by
      simp only [decoLift] at h
      injection h with _ _ hB hdf hda
      have hBeq : B₁ = B₂ := lift_one_inj (c + 1) hB
      subst hBeq
      rw [decoLift_one_inj hdf, decoLift_one_inj hda]
  | _, _, .letE _ _ _ _ dA₁ dv₁ db₁, .letE _ _ _ _ dA₂ dv₂ db₂, h => by
      simp only [decoLift] at h
      injection h with _ _ _ hu hdA hdv hdb
      subst hu
      rw [decoLift_one_inj hdA, decoLift_one_inj hdv, decoLift_one_inj hdb]
  | c, _, .lit t d₁, .lit _ d₂, h => by
      simp only [decoLift] at h
      injection h with _ h'
      exact congrArg (Deco.lit t) (decoLift_one_inj (eq_rec_inj (natExpand_lift c 1 t) h'))

/-- `hasTyTWeaken` commutes with `decoLift c 1`. -/
@[simp] theorem decoOf_hasTyTWeaken (d : LocalDecl) (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx} → {e A : Expr Nat} → (h : HasTyT E n Γ e A) →
    decoOf (hasTyTWeaken d hcl (c := c) h) = decoLift c 1 (decoOf h)
  | _, _, _, _, .sort _ _ => rfl
  | c, _, _, _, .bvar _ i _ _ => deco_lift_bvar_subsingleton c 1 i _ _
  | _, _, _, _, .const _ _ _ _ _ _ _ => deco_subsingleton_const rfl _ _
  | c, _, _, _, .pi _ _ _ _ _ hA hB => by
      simp only [hasTyTWeaken, decoOf, decoLift,
        decoOf_hasTyTWeaken d hcl (c := c) hA,
        decoOf_hasTyTWeaken d hcl (c := c + 1) hB]
  | c, _, _, _, .lam _ _ _ _ _ hA hb => by
      simp only [hasTyTWeaken, decoOf, decoLift,
        decoOf_hasTyTWeaken d hcl (c := c) hA,
        decoOf_hasTyTWeaken d hcl (c := c + 1) hb]
  | c, _, _, _, .app _ _ a _ B hf ha => by
      unfold hasTyTWeaken
      dsimp only [decoOf, decoLift, id]
      try simp only [eq_mpr_trans]
      rw [decoOf_eq_mpr rfl rfl (lift_instantiate_low 1 c 0 a (by omega) B) _ _]
      simp only [decoOf, decoOf_hasTyTWeaken d hcl (c := c) hf,
        decoOf_hasTyTWeaken d hcl (c := c) ha]
  | c, _, _, _, .letE _ _ _ value B _ hA hv hb => by
      unfold hasTyTWeaken
      dsimp only [decoOf, decoLift, id]
      try simp only [eq_mpr_trans]
      rw [decoOf_eq_mpr rfl rfl (lift_instantiate_low 1 c 0 value (by omega) B) _ _]
      simp only [decoOf, decoOf_hasTyTWeaken d hcl (c := c) hA,
        decoOf_hasTyTWeaken d hcl (c := c) hv,
        decoOf_hasTyTWeaken d hcl (c := c + 1) hb]
  | c, _, _, _, .lit _ t _ hexp => by
      unfold hasTyTWeaken
      dsimp only [decoOf, decoLift, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_lift c 1 t) rfl _ _]
      rw [decoOf_hasTyTWeaken d hcl (c := c) hexp]
  | c, _, _, _, .conv _ _ _ _ _ h _ => by
      simp only [hasTyTWeaken, decoOf, decoOf_hasTyTWeaken d hcl (c := c) h]

/-- `cstep_lift` commutes with `decoLift c 1` on `stepDeco`. -/
theorem stepDeco_cstep_lift (L : LeafIface E n PEq) (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    {c : Nat} {Γ : LCtx} {a b T : Expr Nat} {p : ParRedT PEq E n Γ a b T} (cp : Certified p) :
    stepDeco L (cstep_lift d hcl hPEqL (c := c) cp).step = decoLift c 1 (stepDeco L p) := by
  induction cp generalizing c with
  | refl => simp only [cstep_lift, stepDeco, decoOf_hasTyTWeaken]
  | sortEq => exact deco_subsingleton_sort rfl _ _
  | consts => exact deco_subsingleton_const rfl _ _
  | @bvarZeta _ i => exact deco_lift_bvar_subsingleton c 1 i _ _
  | delta => exact deco_subsingleton_const rfl _ _
  | @app _ f f' a a' A B T₀ v w hf hc hB hTy ha hr c₀ cf ca ihf iha =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl rfl (lift_instantiate_low 1 c 0 a (by omega) B) _ _]
      simp only [stepDeco, decoLift, ihf (c := c), iha (c := c)]
  | @beta _ A body body' arg arg' B u v w hA hB hTy hb ha hred c₀ cb ca ihb iha =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl
        (lift_instantiate_low 1 c 0 arg' (by omega) body')
        (lift_instantiate_low 1 c 0 arg (by omega) B) _ _]
      simp only [stepDeco, decoLift, lift, decoOf_hasTyTWeaken, ihb (c := c + 1), iha (c := c)]
  | @lam _ A A' body body' B u v hc hA hB hb hrt c₀ cb ihb =>
      simp only [cstep_lift, stepDeco, decoLift, decoOf_hasTyTWeaken, ihb (c := c + 1)]
  | pi =>
      simp only [cstep_lift, stepDeco, decoLift, decoOf_hasTyTWeaken]
  | @letE _ A A' value value' body body' B u w hc hA hv hB hTy hb hrt c₀ cv cb ihv ihb =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl rfl (lift_instantiate_low 1 c 0 value (by omega) B) _ _]
      simp only [stepDeco, decoLift, decoOf_hasTyTWeaken, ihv (c := c), ihb (c := c + 1)]
  | @zeta _ A value value' body body' B u w hA hv hB hTy hb hred c₀ cv cb ihv ihb =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl
        (lift_instantiate_low 1 c 0 value' (by omega) body')
        (lift_instantiate_low 1 c 0 value (by omega) B) _ _]
      simp only [stepDeco, decoLift, decoOf_hasTyTWeaken, ihv (c := c), ihb (c := c + 1)]
  | iotaSpine _ _ ih =>
      simp only [cstep_lift, stepDeco, ih (c := c)]
  | @lit _ t T hexp c₀ =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl (natExpand_lift c 1 t) rfl _ _]
      simp only [stepDeco, decoLift, eq_mp_trans]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_lift c 1 t) rfl _ _]
      rw [decoOf_hasTyTWeaken]
  | @eta _ f f' A B hf hl c₀ cf _ =>
      unfold cstep_lift
      dsimp only [id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      have e2 : lift (c + 1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [show c + 1 = 1 + c from by omega,
          ← lift_lift_permute 1 1 c 0 (Nat.zero_le c) f]
      have he : lift c 1 (.lam A (.app (lift 0 1 f) (.bvar 0))) =
          .lam (lift c 1 A) (.app (lift 0 1 (lift c 1 f)) (.bvar 0)) := by
        simp only [lift, if_neg (Nat.not_le_of_gt (Nat.succ_pos c) : ¬ c + 1 ≤ 0), e2]
      rw [stepDeco_cstep_eq_mpr L rfl he rfl rfl _ _]
      simp only [stepDeco, eq_mp_trans]
      rw [decoOf_eq_mp_cancel rfl he rfl _ (hasTyTWeaken d hcl (c := c) hl)]
      exact decoOf_hasTyTWeaken d hcl hl
  | peq _ =>
      simp only [cstep_lift, stepDeco, hPEqLDeco]
  | conv _ _ ih =>
      simp only [cstep_lift, stepDeco, ih (c := c)]

/-! ### `decoSubst`, `decoLift0`, and substitution commutation -/

/-- Weakening a `0`-lifted decoration by one more binder at the top. -/
def decoSubstWk {v : Expr Nat} {j : Nat} (dv : Deco (lift 0 j v)) :
    Deco (lift 0 (j + 1) v) :=
  lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v ▸ decoLift 0 1 dv

/-- Iterated `0`-cutoff lift of a decoration, matching `cstep_lift_lctx`. -/
def decoLift0 : (j : Nat) → {v : Expr Nat} → Deco v → Deco (lift 0 j v)
  | 0, _, dv => (lift_zero 0 _).symm ▸ dv
  | j + 1, _, dv => decoSubstWk (decoLift0 j dv)

/-- `cstep_lift_lctx` commutes with `decoLift0 Δ.length`. -/
theorem stepDeco_cstep_lift_lctx (L : LeafIface E n PEq) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    (Δ : LCtx) {Γ : LCtx} {a b T : Expr Nat} (s : CStep E n PEq Γ a b T) :
    stepDeco L (cstep_lift_lctx hcl hPEqL Δ s).step = decoLift0 Δ.length (stepDeco L s.step) := by
  induction Δ with
  | nil =>
      unfold cstep_lift_lctx decoLift0
      try dsimp only [id, List.length]
      try simp only [eq_mpr_trans]
      exact stepDeco_cstep_eq_mpr L rfl (lift_zero 0 a) (lift_zero 0 b)
        (lift_zero 0 T) _ s
  | cons d Δ ih =>
      unfold cstep_lift_lctx decoLift0 decoSubstWk
      try dsimp only [id, List.length]
      try simp only [eq_mpr_trans]
      rw [stepDeco_cstep_eq_mpr L rfl (lift_zero_succ Δ.length a).symm
        (lift_zero_succ Δ.length b).symm (lift_zero_succ Δ.length T).symm _ _]
      rw [stepDeco_cstep_lift L d hcl hPEqL hPEqLDeco, ih]

/-- Helper for `subst_hvw_of_drop`: casting `cstep_lift_lctx` along `Δ.length = j`. -/
theorem stepDeco_lift_lctx_cast (L : LeafIface E n PEq)
    {Δ : LCtx} {Γ₀ Γ' : LCtx} {k : Nat} {v v' t : Expr Nat}
    (hk : Δ.length = k) (hsplit : Γ' = Δ ++ Γ₀)
    (hEq₁ : CStep E n PEq (Δ ++ Γ₀) (lift 0 Δ.length v) (lift 0 Δ.length v') (lift 0 Δ.length t) =
      CStep E n PEq (Δ ++ Γ₀) (lift 0 k v) (lift 0 k v') (lift 0 k t))
    (hEq₂ : CStep E n PEq Γ' (lift 0 k v) (lift 0 k v') (lift 0 k t) =
      CStep E n PEq (Δ ++ Γ₀) (lift 0 k v) (lift 0 k v') (lift 0 k t))
    (x : CStep E n PEq (Δ ++ Γ₀) (lift 0 Δ.length v) (lift 0 Δ.length v') (lift 0 Δ.length t))
    {dv : Deco v} (hx : stepDeco L x.step = decoLift0 Δ.length dv) :
    stepDeco L (Eq.mpr hEq₂ (Eq.mp hEq₁ x)).step = decoLift0 k dv := by
  subst hk; subst hsplit; cases hEq₁; cases hEq₂; exact hx

/-- `subst_hvw_of_drop` has source decoration `decoLift0 j (stepDeco L hvw₀.step)`. -/
theorem stepDeco_subst_hvw_of_drop (L : LeafIface E n PEq) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    {v v' t : Expr Nat} {j : Nat} {Γ : LCtx} (H : Hole t v j Γ)
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t) :
    stepDeco L (subst_hvw_of_drop hcl hPEqL H hvw₀).step =
      decoLift0 j (stepDeco L hvw₀.step) := by
  unfold subst_hvw_of_drop
  try dsimp only [id]
  have hlt : j < Γ.length := H.lt
  have h1 : (substRemove v j Γ).drop j = Γ.drop (j + 1) := by
    rw [substRemove_drop, if_pos (Nat.le_refl j), Nat.sub_self]
    have hd : substRemove v 0 (Γ.drop j) = (Γ.drop j).drop 1 := by
      cases Γ.drop j <;> simp [substRemove]
    rw [hd, List.drop_drop]
  have hsplit : substRemove v j Γ = (substRemove v j Γ).take j ++ Γ.drop (j + 1) := by
    have hs := (List.take_append_drop j (substRemove v j Γ)).symm
    rw [h1] at hs; exact hs
  have htake : ((substRemove v j Γ).take j).length = j := by
    rw [List.length_take, substRemove_length, if_pos hlt]; omega
  exact stepDeco_lift_lctx_cast L htake hsplit _ _ _
    (stepDeco_cstep_lift_lctx L hcl hPEqL hPEqLDeco ((substRemove v j Γ).take j) hvw₀)

/-- `subst_hvty_wk` commutes with `decoSubstWk`. -/
@[simp] theorem decoOf_subst_hvty_wk (d : LocalDecl) (hcl : EnvClosed E)
    {v t : Expr Nat} {j : Nat} {Γ : LCtx}
    (h : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    decoOf (subst_hvty_wk d hcl h) = decoSubstWk (decoOf h) := by
  unfold subst_hvty_wk decoSubstWk
  dsimp only [id]
  try simp only [eq_mp_trans]
  rw [decoOf_eq_mp rfl (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v)
    (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
  rw [decoOf_hasTyTWeaken]

/-- Transport a decoration along a term equality `e₁ = e₂` (from `Deco e₂` to `Deco e₁`). -/
abbrev decoCast {e₁ e₂ : Expr Nat} (he : e₁ = e₂) (d : Deco e₂) : Deco e₁ :=
  he ▸ d

/-- Substitution on a decoration at depth `j`, with replacement decoration `dv : Deco (lift 0 j v)`. -/
def decoSubst (j : Nat) {v : Expr Nat} (dv : Deco (lift 0 j v)) :
    {e : Expr Nat} → Deco e → Deco (instantiate j (lift 0 j v) e)
  | _, .sort l => .sort l
  | _, .bvar i =>
      if hij : i = j then
        decoCast (if_pos hij : instantiate j (lift 0 j v) (.bvar i) = lift 0 j v) dv
      else if hlt : j < i then
        decoCast (by simp only [instantiate, if_neg hij, if_pos hlt] :
          instantiate j (lift 0 j v) (.bvar i) = .bvar (i - 1)) (.bvar (i - 1))
      else
        decoCast (by simp only [instantiate, if_neg hij, if_neg hlt] :
          instantiate j (lift 0 j v) (.bvar i) = .bvar i) (.bvar i)
  | _, .const r ls => .const r ls
  | _, .pi A B u v₀ dA dB =>
      decoCast (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B))
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v))
        (.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) (lift 0 (j + 1) v) B) u v₀
          (decoSubst j dv dA) (decoSubst (j + 1) (decoSubstWk dv) dB))
  | _, .lam A body u dA db =>
      decoCast (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v) A) (instantiate (j + 1) s body))
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v))
        (.lam (instantiate j (lift 0 j v) A) (instantiate (j + 1) (lift 0 (j + 1) v) body) u
          (decoSubst j dv dA) (decoSubst (j + 1) (decoSubstWk dv) db))
  | _, .app f a B df da =>
      .app (instantiate j (lift 0 j v) f) (instantiate j (lift 0 j v) a)
        (instantiate (j + 1) (lift 0 (j + 1) v) B)
        (decoSubst j dv df) (decoSubst j dv da)
  | _, .letE A value body u dA dv₀ db =>
      decoCast (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v) A)
        (instantiate j (lift 0 j v) value) (instantiate (j + 1) s body))
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v))
        (.letE (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) value)
          (instantiate (j + 1) (lift 0 (j + 1) v) body) u
          (decoSubst j dv dA) (decoSubst j dv dv₀)
          (decoSubst (j + 1) (decoSubstWk dv) db))
  | _, .lit t d =>
      .lit t (natExpand_instantiate j (lift 0 j v) t ▸ decoSubst j dv d)

/-- `hasTyT_substS` commutes with `decoSubst`. -/
theorem decoOf_hasTyT_substS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    (h : HasTyT E n Γ e A) → (hget : Γ[j]? = some (.assumption t)) →
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    decoOf (hasTyT_substS hcl hinst v t (j := j) h hget hvty) =
      decoSubst j (decoOf hvty) (decoOf h)
  | _, _, _, _, .sort _ _, _, _ => deco_subsingleton_sort rfl _ _
  | j, _, _, _, .bvar _ i A h, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        have hA : A = lift 0 (i + 1) t :=
          Option.some.inj (h.symm.trans (lookupType_get_assumption hget))
        subst hA
        unfold hasTyT_substS decoSubst
        dsimp only [decoOf, id]
        simp only [dif_pos rfl, dite_true]
        try simp only [eq_mpr_trans]
        rw [decoOf_eq_mpr rfl
          (if_pos (rfl : i = i) : instantiate i (lift 0 i v) (.bvar i) = lift 0 i v)
          (instantiate_lift_cancel (i + 1) 0 i (lift 0 i v) (by omega) (by omega) _) _ hvty]
      · exact deco_instantiate_bvar_ne_subsingleton j i (lift 0 j v) hij _ _
  | _, _, _, _, .const _ _ _ _ _ _ _, _, _ => deco_subsingleton_const rfl _ _
  | j, Γ, _, _, .pi _ A u B w hA hB, hget, hvty => by
      unfold hasTyT_substS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        rfl _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substS hcl hinst v t hA,
        decoOf_hasTyT_substS hcl hinst v t (j := j + 1) hB]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, Γ, _, _, .lam _ A u body B hA hbody, hget, hvty => by
      unfold hasTyT_substS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v) A) (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substS hcl hinst v t hA,
        decoOf_hasTyT_substS hcl hinst v t (j := j + 1) hbody]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, _, _, _, .app _ _ a _ B hf ha, hget, hvty => by
      have ihf := decoOf_hasTyT_substS hcl hinst v t hf hget hvty
      have iha := decoOf_hasTyT_substS hcl hinst v t ha hget hvty
      unfold hasTyT_substS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      rw [decoOf_eq_mpr rfl rfl (instantiate_instantiate 0 j a (lift 0 j v) (by omega) B) _ _]
      simp only [decoOf, ihf, iha,
        lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, hget, hvty => by
      unfold hasTyT_substS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v) value) (instantiate (j + 1) s body)) hm)
        ((instantiate_instantiate 0 j value (lift 0 j v) (by omega) B).trans
          (congrArg (fun s => instantiate 0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) s B)) hm))
        _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substS hcl hinst v t hA,
        decoOf_hasTyT_substS hcl hinst v t hv,
        decoOf_hasTyT_substS hcl hinst v t (j := j + 1) hb]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, _, _, _, .lit _ tl _ hexp, hget, hvty => by
      have ih := decoOf_hasTyT_substS hcl hinst v t hexp hget hvty
      unfold hasTyT_substS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_instantiate j (lift 0 j v) tl) rfl _ _]
      rw [ih]
  | _, _, _, _, .conv _ _ _ _ _ h _, hget, hvty => by
      simp only [hasTyT_substS, decoOf, decoOf_hasTyT_substS hcl hinst v t h hget hvty]
  termination_by j Γ e A h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- `hasTyT_substLetS` commutes with `decoSubst`. -/
theorem decoOf_hasTyT_substLetS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    (h : HasTyT E n Γ e A) → (hget : Γ[j]? = some (.letBinding t w0)) →
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t)) →
    decoOf (hasTyT_substLetS hcl hinst t w0 (j := j) h hget hvty) =
      decoSubst j (decoOf hvty) (decoOf h)
  | _, _, _, _, .sort _ _, _, _ => deco_subsingleton_sort rfl _ _
  | j, _, _, _, .bvar _ i A h, hget, hvty => by
      by_cases hij : i = j
      · subst hij
        have hA : A = lift 0 (i + 1) t :=
          Option.some.inj (h.symm.trans (lookupType_get_letBinding hget))
        subst hA
        unfold hasTyT_substLetS decoSubst
        dsimp only [decoOf, id]
        simp only [dif_pos rfl, dite_true]
        try simp only [eq_mpr_trans]
        rw [decoOf_eq_mpr rfl
          (if_pos (rfl : i = i) : instantiate i (lift 0 i w0) (.bvar i) = lift 0 i w0)
          (instantiate_lift_cancel (i + 1) 0 i (lift 0 i w0) (by omega) (by omega) _) _ hvty]
      · exact deco_instantiate_bvar_ne_subsingleton j i (lift 0 j w0) hij _ _
  | _, _, _, _, .const _ _ _ _ _ _ _, _, _ => deco_subsingleton_const rfl _ _
  | j, Γ, _, _, .pi _ A u B w hA hB, hget, hvty => by
      unfold hasTyT_substLetS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w0
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j w0) A) (instantiate (j + 1) s B)) hm)
        rfl _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substLetS hcl hinst t w0 hA,
        decoOf_hasTyT_substLetS hcl hinst t w0 (j := j + 1) hB]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, Γ, _, _, .lam _ A u body B hA hbody, hget, hvty => by
      unfold hasTyT_substLetS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w0
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j w0) A) (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j w0) A) (instantiate (j + 1) s B)) hm)
        _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substLetS hcl hinst t w0 hA,
        decoOf_hasTyT_substLetS hcl hinst t w0 (j := j + 1) hbody]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, _, _, _, .app _ _ a _ B hf ha, hget, hvty => by
      have ihf := decoOf_hasTyT_substLetS hcl hinst t w0 hf hget hvty
      have iha := decoOf_hasTyT_substLetS hcl hinst t w0 ha hget hvty
      unfold hasTyT_substLetS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      rw [decoOf_eq_mpr rfl rfl (instantiate_instantiate 0 j a (lift 0 j w0) (by omega) B) _ _]
      simp only [decoOf, ihf, iha,
        lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w0]
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, hget, hvty => by
      unfold hasTyT_substLetS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) w0
      rw [decoOf_eq_mpr rfl
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j w0) A)
          (instantiate j (lift 0 j w0) value) (instantiate (j + 1) s body)) hm)
        ((instantiate_instantiate 0 j value (lift 0 j w0) (by omega) B).trans
          (congrArg (fun s => instantiate 0 (instantiate j (lift 0 j w0) value)
            (instantiate (j + 1) s B)) hm))
        _ _]
      congr 1
      simp only [decoOf, decoOf_hasTyT_substLetS hcl hinst t w0 hA,
        decoOf_hasTyT_substLetS hcl hinst t w0 hv,
        decoOf_hasTyT_substLetS hcl hinst t w0 (j := j + 1) hb]
      congr 2
      unfold decoSubstWk
      try simp only [eq_mp_trans]
      rw [decoOf_eq_mp rfl hm
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t) _ _]
      rw [decoOf_hasTyTWeaken]
  | j, _, _, _, .lit _ tl _ hexp, hget, hvty => by
      have ih := decoOf_hasTyT_substLetS hcl hinst t w0 hexp hget hvty
      unfold hasTyT_substLetS decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_instantiate j (lift 0 j w0) tl) rfl _ _]
      rw [ih]
  | _, _, _, _, .conv _ _ _ _ _ h _, hget, hvty => by
      simp only [hasTyT_substLetS, decoOf, decoOf_hasTyT_substLetS hcl hinst t w0 h hget hvty]
  termination_by j Γ e A h _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- `Hole.tySubst` commutes with `decoSubst` for both assumption and let holes. -/
@[simp] theorem decoOf_tySubst (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {t v : Expr Nat} {j : Nat} {Γ : LCtx} (H : Hole t v j Γ)
    {e A : Expr Nat} (h : HasTyT E n Γ e A)
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    decoOf (H.tySubst hcl hinst h hvty) = decoSubst j (decoOf hvty) (decoOf h) := by
  cases H with
  | assump hget => exact decoOf_hasTyT_substS hcl hinst v t h hget hvty
  | letB hget => exact decoOf_hasTyT_substLetS hcl hinst t v h hget hvty

/-- `csubst_arg` commutes with `decoSubst` and `decoLift0`. -/
theorem stepDeco_csubst_arg (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    {v v' t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (h : HasTyT E n Γ e T) → (H : Hole t v j Γ) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) → (hΓwf : CtxWfT E n Γ) →
    stepDeco L (csubst_arg hW L hPEqL h H hvt hvw₀ hΓ'wf hΓwf).step =
      decoSubst j (decoLift0 j (stepDeco L hvw₀.step)) (decoOf h)
  | _, _, _, _, .sort _ _, _, _, _, _, _ => deco_subsingleton_sort rfl _ _
  | j, _, _, _, .bvar _ i A h, H, _, hvw₀, _, _ => by
      by_cases hij : i = j
      · subst hij
        have hA : A = lift 0 (i + 1) t :=
          Option.some.inj (h.symm.trans H.lookupTy)
        subst hA
        unfold csubst_arg decoSubst
        dsimp only [decoOf, id]
        simp only [dif_pos rfl, dite_true]
        try simp only [eq_mpr_trans]
        rw [stepDeco_cstep_eq_mpr L rfl
          (by simp only [instantiate, if_pos (rfl : i = i)])
          (by simp only [instantiate, if_pos (rfl : i = i)])
          (instantiate_lift_cancel (i + 1) 0 i (lift 0 i v)
            (Nat.zero_le i) (Nat.lt_succ_self i) _) _ _]
        unfold decoCast
        congr 1
        exact stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco H hvw₀
      · exact deco_instantiate_bvar_ne_subsingleton j i (lift 0 j v) hij _ _
  | _, _, _, _, .const _ _ _ _ _ _ _, _, _, _, _, _ => deco_subsingleton_const rfl _ _
  | j, _, _, _, .pi _ A _ B _ _ _, H, _, hvw₀, _, _ => by
      unfold csubst_arg decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v') A) (instantiate (j + 1) s B)) hm')
        rfl _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_subst_hvty_wk, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco H hvw₀]
  | j, Γ, _, _, .lam _ A u body B hA hbody, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      unfold csubst_arg decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v) A)
          (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v') A)
          (instantiate (j + 1) s body)) hm')
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco H hvw₀,
        stepDeco_csubst_arg hW L hPEqL hPEqLDeco hbody, decoLift0]
  | j, _, _, _, .app _ _ a A B hf ha, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      have ihf := stepDeco_csubst_arg hW L hPEqL hPEqLDeco hf H hvt hvw₀ hΓ'wf hΓwf
      have iha := stepDeco_csubst_arg hW L hPEqL hPEqLDeco ha H hvt hvw₀ hΓ'wf hΓwf
      unfold csubst_arg decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) s B)) hm)
      rw [stepDeco_cstep_eq_mpr L rfl rfl rfl hcomm _ _]
      simp only [stepDeco, eq_mp_trans]
      rw [stepDeco_cstep_eq_mp L rfl rfl rfl
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A)
          (instantiate (j + 1) s B)) hm) _ _]
      simp only [ihf, iha]
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      unfold csubst_arg decoSubst
      dsimp only [decoOf, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) s B)) hm)
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v) value) (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v') A)
          (instantiate j (lift 0 j v') value) (instantiate (j + 1) s body)) hm')
        hcomm _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco H hvw₀,
        stepDeco_csubst_arg hW L hPEqL hPEqLDeco hv,
        stepDeco_csubst_arg hW L hPEqL hPEqLDeco hb, decoLift0]
  | j, _, _, _, .lit _ tl _ _, H, _, hvw₀, _, _ => by
      unfold csubst_arg decoSubst
      dsimp only [stepDeco, decoOf, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_instantiate j (lift 0 j v) tl) rfl _ _]
      simp only [decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco H hvw₀]
  | _, _, _, _, .conv _ _ _ _ _ h _, H, hvt, hvw₀, hΓ'wf, hΓwf => by
      simp only [csubst_arg, stepDeco, decoOf,
        stepDeco_csubst_arg hW L hPEqL hPEqLDeco h H hvt hvw₀ hΓ'wf hΓwf]
  termination_by j Γ e T h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

set_option maxHeartbeats 16000000 in
/-- `csubstMixed` at an assumption hole commutes with `decoSubst` and `decoLift0`. -/
theorem stepDeco_csubstMixed (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    (hPEqIrrDeco : ∀ {Γ : LCtx} {p q T : Expr Nat}
      (hP : HasTyT E n Γ T (.sort .zero)) (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T),
      decoOf (L.typed (L.ofIrr hP hp hq)).1 = decoOf hp)
    {v v' t : Expr Nat} {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {p : ParRedT PEq E n Γ a b T} (cp : Certified p)
    (hget : Γ[j]? = some (.assumption t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t)
    (hvw₀ : CStep E n PEq (Γ.drop (j + 1)) v v' t)
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) (hΓwf : CtxWfT E n Γ) :
    stepDeco L (csubstMixed hW L hPEqL cp (.assump hget) hvt hvw₀ hΓ'wf hΓwf).step =
      decoSubst j (decoLift0 j (stepDeco L hvw₀.step)) (stepDeco L p) := by
  induction cp generalizing j with
  | @refl _ _ _ h _ =>
      unfold csubstMixed
      dsimp only [stepDeco, id]
      exact stepDeco_csubst_arg hW L hPEqL hPEqLDeco h (.assump hget) hvt hvw₀ hΓ'wf hΓwf
  | sortEq => exact deco_subsingleton_sort rfl _ _
  | consts => exact deco_subsingleton_const rfl _ _
  | @bvarZeta Γ₀ i A val _ _ hlk _ _ _ _ _ _ =>
      by_cases hij : i = j
      · subst hij
        have h' : Γ₀[i]? = some (.letBinding A val) :=
          (List.get?_eq_getElem? Γ₀ i).symm ▸ hlk
        rw [h'] at hget
        exact nomatch hget
      · exact deco_instantiate_bvar_ne_subsingleton j i (lift 0 j v) hij _ _
  | delta => exact deco_subsingleton_const rfl _ _
  | @app _ _ _ a _ _ B _ _ _ _ _ _ _ _ _ _ cf ca ihf iha =>
      unfold csubstMixed decoSubst
      dsimp only [id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) s B)) hm)
      rw [stepDeco_cstep_eq_mpr L rfl rfl rfl hcomm _ _]
      simp only [stepDeco, ihf hget hvt hvw₀ hΓ'wf hΓwf, iha hget hvt hvw₀ hΓ'wf hΓwf]
  | @beta Γ A body body' arg arg' B u _ _ hA _ _ _ _ _ _ cb ca ihb iha =>
      unfold csubstMixed decoSubst
      dsimp only [Hole.succ, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      have hcommB : instantiate j (lift 0 j v) (instantiate0 arg B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j arg (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) s B)) hm)
      have hcommBody : instantiate j (lift 0 j v') (instantiate0 arg' body') =
          instantiate0 (instantiate j (lift 0 j v') arg')
            (instantiate (j + 1) (lift 0 (j + 1) v') body') :=
        (instantiate_instantiate 0 j arg' (lift 0 j v') (Nat.zero_le j) body').trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v') arg')
            (instantiate (j + 1) s body')) hm')
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.app (.lam (instantiate j (lift 0 j v) A)
          (instantiate (j + 1) s body)) (instantiate j (lift 0 j v) arg)) hm)
        hcommBody hcommB _ _]
      simp only [stepDeco, decoSubst, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀,
        ihb, iha, decoLift0]
      exact deco_app_lam_cast hm body _ _ _
  | @lam Γ A A' body body' B u _ _ hA _ _ _ _ cb ihb =>
      unfold csubstMixed decoSubst
      dsimp only [stepDeco, Hole.succ, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v) A)
          (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.lam (instantiate j (lift 0 j v') A')
          (instantiate (j + 1) s body')) hm')
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀,
        ihb, decoLift0]
  | @pi _ A A' B B' _ _ _ _ _ _ _ _ =>
      unfold csubstMixed decoSubst
      dsimp only [stepDeco, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v) A) (instantiate (j + 1) s B)) hm)
        (congrArg (fun s => Expr.pi (instantiate j (lift 0 j v') A')
          (instantiate (j + 1) s B')) hm')
        rfl _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_subst_hvty_wk, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀]
  | @letE Γ A A' value value' body body' B u _ _ hA hv _ _ _ _ _ cv cb ihv ihb =>
      unfold csubstMixed decoSubst
      dsimp only [stepDeco, Hole.succ, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) s B)) hm)
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v) value) (instantiate (j + 1) s body)) hm)
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v') A')
          (instantiate j (lift 0 j v') value') (instantiate (j + 1) s body')) hm')
        hcomm _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀,
        ihv, ihb, decoLift0]
  | @zeta Γ A value value' body body' B u _ hA hv _ _ _ _ _ cv cb ihv ihb =>
      unfold csubstMixed decoSubst
      dsimp only [stepDeco, Hole.succ, id]
      try simp only [eq_mpr_trans]
      have hm := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v
      have hm' := lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v'
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 (j + 1) v) B) :=
        (instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B).trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) s B)) hm)
      have hcomm' : instantiate j (lift 0 j v') (instantiate0 value' body') =
          instantiate0 (instantiate j (lift 0 j v') value')
            (instantiate (j + 1) (lift 0 (j + 1) v') body') :=
        (instantiate_instantiate 0 j value' (lift 0 j v') (Nat.zero_le j) body').trans
          (congrArg (fun s => instantiate0 (instantiate j (lift 0 j v') value')
            (instantiate (j + 1) s body')) hm')
      rw [stepDeco_cstep_eq_mpr L rfl
        (congrArg (fun s => Expr.letE (instantiate j (lift 0 j v) A)
          (instantiate j (lift 0 j v) value) (instantiate (j + 1) s body)) hm)
        hcomm' hcomm _ _]
      congr 1
      simp only [stepDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀,
        ihv, ihb, decoLift0]
  | iotaSpine _ _ ih =>
      unfold csubstMixed
      dsimp only [stepDeco, id]
      exact ih hget hvt hvw₀ hΓ'wf hΓwf
  | @lit _ tl _ _ _ =>
      unfold csubstMixed decoSubst
      dsimp only [stepDeco, decoOf, id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      rw [stepDeco_cstep_eq_mpr L rfl rfl (natExpand_instantiate j (lift 0 j v') tl) rfl _ _]
      simp only [stepDeco, decoOf]
      congr 1
      rw [decoOf_eq_mp rfl (natExpand_instantiate j (lift 0 j v) tl) rfl _ _]
      simp only [decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀]
  | @eta _ f _ A _ _ hl _ _ _ =>
      unfold csubstMixed
      dsimp only [id]
      try simp only [eq_mpr_trans, eq_mp_trans]
      have e2 : instantiate (j + 1) (lift 0 1 (lift 0 j v)) (lift 0 1 f) =
          lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      have he : instantiate j (lift 0 j v) (.lam A (.app (lift 0 1 f) (.bvar 0))) =
          .lam (instantiate j (lift 0 j v) A)
            (.app (lift 0 1 (instantiate j (lift 0 j v) f)) (.bvar 0)) := by
        simp only [instantiate, if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
          if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0), e2]
      rw [stepDeco_cstep_eq_mpr L rfl he rfl rfl _ _]
      simp only [stepDeco, eq_mp_trans]
      rw [decoOf_eq_mp_cancel rfl he rfl _
        ((Hole.assump hget).tySubst (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW) hl _)]
      simp only [decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀]
  | peq _ =>
      unfold csubstMixed
      dsimp only [stepDeco, id]
      simp only [hPEqIrrDeco, decoOf_tySubst, decoOf_leftTyped,
        stepDeco_subst_hvw_of_drop L (envClosed_of_envWfT hW) hPEqL hPEqLDeco (.assump hget) hvw₀]
  | conv _ _ ih =>
      unfold csubstMixed
      dsimp only [stepDeco, id]
      exact ih hget hvt hvw₀ hΓ'wf hΓwf

/-- Head substitution (`certSubst0_of`, `j = 0`) commutes with `decoSubst 0` on `stepDeco`. -/
theorem stepDeco_certSubst0_of (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
      PEq Γ p q T → PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqLDeco : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat} (h : PEq Γ p q T),
      decoOf (L.typed (hPEqL (d' := d') (c := c) h)).1 = decoLift c 1 (decoOf (L.typed h).1))
    (hPEqIrrDeco : ∀ {Γ : LCtx} {p q T : Expr Nat}
      (hP : HasTyT E n Γ T (.sort .zero)) (hp : HasTyT E n Γ p T) (hq : HasTyT E n Γ q T),
      decoOf (L.typed (L.ofIrr hP hp hq)).1 = decoOf hp)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v v' body body' B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (pb : CStep E n PEq (.assumption A :: Γ) body body' B)
    (pv : CStep E n PEq Γ v v' A) :
    stepDeco L (certSubst0_of hW L hPEqL hΓ hA pb pv).step =
      (congrArg (fun w => instantiate0 w body) (lift_zero 0 v)) ▸
        decoSubst 0 (decoLift0 0 (stepDeco L pv.step)) (stepDeco L pb.step) := by
  unfold certSubst0_of
  dsimp only [id]
  try simp only [eq_mp_trans]
  rw [stepDeco_cstep_eq_mp L rfl
    (congrArg (fun w => instantiate0 w body) (lift_zero 0 v))
    (congrArg (fun w => instantiate0 w body') (lift_zero 0 v'))
    (congrArg (fun w => instantiate0 w B) (lift_zero 0 v)) _ _]
  rw [stepDeco_csubstMixed hW L hPEqL hPEqLDeco hPEqIrrDeco pb.cert
    List.getElem?_cons_zero (pv.leftTyped L hΓ) pv hΓ (.assumption Γ A u hΓ hA)]

#print axioms deco_subsingleton_sort
#print axioms deco_subsingleton_bvar
#print axioms deco_subsingleton_const
#print axioms deco_lift_bvar_subsingleton
#print axioms deco_instantiate_bvar_ne_subsingleton
#print axioms eq_mpr_trans
#print axioms eq_mp_trans
#print axioms decoOf_eq_mpr
#print axioms decoOf_eq_mp
#print axioms decoOf_eq_mp_cancel
#print axioms deco_app_lam_cast
#print axioms eq_rec_inj
#print axioms decoOf_hasTyT_of_tyConvT
#print axioms stepDeco
#print axioms decoOf_parRedT_typed_left
#print axioms decoOf_parRedT_hasTy_left
#print axioms decoOf_leftTyped
#print axioms stepDeco_reindex
#print axioms decoOf_reindex_left
#print axioms decoOf_reindex_right
#print axioms stepDeco_peel
#print axioms stepDeco_cstep_eq_mpr
#print axioms stepDeco_cstep_eq_mp
#print axioms uniqStepD
#print axioms decoOf_hasTyT_ctx
#print axioms stepDeco_cstep_ctxTransport
#print axioms stepDeco_cstep_assumpCtx
#print axioms stepDeco_cstep_letAnnCtx
#print axioms decoLift
#print axioms lift_one_inj
#print axioms decoLift_one_inj
#print axioms decoOf_hasTyTWeaken
#print axioms stepDeco_cstep_lift
#print axioms decoSubstWk
#print axioms decoLift0
#print axioms stepDeco_cstep_lift_lctx
#print axioms stepDeco_lift_lctx_cast
#print axioms stepDeco_subst_hvw_of_drop
#print axioms decoOf_subst_hvty_wk
#print axioms decoCast
#print axioms decoSubst
#print axioms decoOf_hasTyT_substS
#print axioms decoOf_hasTyT_substLetS
#print axioms decoOf_tySubst
#print axioms stepDeco_csubst_arg
#print axioms stepDeco_csubstMixed
#print axioms stepDeco_certSubst0_of

end Rcic.Declarative.NativeValleys
