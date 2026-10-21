import rcic.RcicNativeValleyOpenRows

/-!
# RcicNativeValleyEtaLeaf — the one-step diamond fails at `lam × eta` with an irrelevance leaf
(Wall 1, `NativeConvValleys`, piece 17: a countermodel to the oracle's shape)

The certified diamond `CDiamond` (`RcicNativeValleyCert`) — two certified steps out of one term
at one index join by ONE certified step each — is the hypothesis the whole valley algebra
consumes (`strip`, `confluence`, `CValley.trans`, `valleyOf`). This module exhibits a pair of
certified steps with no one-step join, in the context

```
Γ := p : P, x : P → P → Prop        P := Π (A : Prop), A   (a closed Prop)
f := x p : P → Prop
b := lam P (app (lift 0 1 f) (bvar 0))        the η-expansion of f
```

* the λ node steps the body: `app (lift f) (bvar 0) = app (app x p) (bvar 0)` steps by
  congruence, the inner `p` (lifted) stepping to the BOUND variable `bvar 0 : P` by the
  irrelevance leaf (`P : Prop`, two proofs) — `d := lam P (app (app x (bvar 0)) (bvar 0))`;
* the η node contracts `b` to `e := f` (`f ⇒ f` by `refl`).

Any one-step reduct of `d` is a λ: `d` is not an η-redex any more (the bound variable sits
where the lifted `p` was — `lift 0 1 _` never produces `bvar 0`), and `d` is not a proof. Any
one-step reduct of `e = x p` is an application `x _` (`x` is a variable of a non-`Prop` type,
`f` is not a proof). A λ is not an application. So `CDiamond E n PEq` is FALSE for every leaf
interface `PEq` — in every environment in which the three terms `d`, `f`, `x` are not proofs
(`NotProof`: no type of the term is `Prop`-sorted; the three facts hold in any consistent
environment and are exactly the sort-separation `zero-sort coherence` would deliver, #7519).
Through `cdiamond_of_rows` the same pair refutes `OpenRows` and the session-7 `RowFronts`
(their field `LamEtaApp` asks for this join).

Nothing here refutes `NativeConvValleys` (§5.5): `d ⇒ b ⇒ f` in TWO steps (the leaf fires
back, then η), so the two reducts have a common reduct; what fails is the one-step shape of
the oracle, as the K-rhs rigidity did for the full relation (`NATIVE_VALLEYS_STATUS.md` §2a),
and here also Huet's strong confluence (the λ side needs two steps, in both orientations of
the pair). The classical proof's side condition `x ∉ FV(M)` is not preserved by irrelevance
rewriting; see `NATIVE_VALLEYS_STATUS.md` §8 for the consequences.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the terms -/

/-- `P := Π (A : Prop), A`, a closed `Prop`. -/
def etaLeafP : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- `X := P → P → Prop`. -/
def etaLeafX : Expr Nat := .pi etaLeafP (.pi etaLeafP (.sort .zero))

/-- The context `p : P, x : X` (`bvar 0 = p`, `bvar 1 = x`). -/
def etaLeafCtx : LCtx := [.assumption etaLeafP, .assumption etaLeafX]

/-- `f := x p : P → Prop`. -/
def etaLeafF : Expr Nat := .app (.bvar 1) (.bvar 0)

/-- The η-expansion's body `app (lift 0 1 f) (bvar 0)`. -/
def etaLeafBody : Expr Nat := .app (lift 0 1 etaLeafF) (.bvar 0)

/-- The body after the leaf: `app (app x (bvar 0)) (bvar 0)` — the lifted `p` replaced by the
    bound variable. -/
def etaLeafBody' : Expr Nat := .app (.app (.bvar 2) (.bvar 0)) (.bvar 0)

/-- `lift 0 1` never produces the bound variable `bvar 0`. -/
theorem lift_ne_bvar_zero : (e : Expr Nat) → lift 0 1 e ≠ .bvar 0
  | .bvar _ => by simp [lift]
  | .sort _ => by simp [lift]
  | .const _ _ => by simp [lift]
  | .app _ _ => by simp [lift]
  | .lam _ _ => by simp [lift]
  | .pi _ _ => by simp [lift]
  | .letE _ _ _ => by simp [lift]
  | .lit _ => by simp [lift]

/-- The stepped body is not an η-redex body. -/
theorem etaLeafBody'_not_eta (g : Expr Nat) : etaLeafBody' ≠ .app (lift 0 1 g) (.bvar 0) := by
  intro h
  have h1 : Expr.app (.bvar 2) (.bvar 0) = lift 0 1 g := by
    injection h
  cases g <;> simp [lift] at h1
  obtain ⟨_, h12⟩ := h1
  exact lift_ne_bvar_zero _ h12.symm

/-! ### the typings -/

/-- `P : Prop` in every context (`imax 1 0 =ₙ 0`). -/
def etaLeafP_ty (Γ : LCtx) : HasTyT E n Γ etaLeafP (.sort .zero) :=
  .conv Γ etaLeafP _ _ _
    (.pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero (.sort Γ .zero) (.bvar _ 0 _ rfl))
    (.sorts Γ (.imax (.succ .zero) .zero) .zero (eqN_imax_zero_right _))

/-- `P → Prop` is sorted in every context. -/
def etaLeafPiP_ty (Γ : LCtx) :
    HasTyT E n Γ (.pi etaLeafP (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
  .pi Γ etaLeafP .zero (.sort .zero) (.succ .zero) (etaLeafP_ty Γ) (.sort _ _)

/-- `X` is sorted in every context. -/
def etaLeafX_ty (Γ : LCtx) :
    HasTyT E n Γ etaLeafX (.sort (.imax .zero (.imax .zero (.succ .zero)))) :=
  .pi Γ etaLeafP .zero (.pi etaLeafP (.sort .zero)) _ (etaLeafP_ty Γ) (etaLeafPiP_ty _)

/-- The context is well-formed. -/
def etaLeafCtx_wf : CtxWfT E n etaLeafCtx :=
  .assumption _ _ _ (.assumption _ _ _ .nil (etaLeafX_ty [])) (etaLeafP_ty _)

/-- `x : X`. -/
def etaLeafX_var : HasTyT E n etaLeafCtx (.bvar 1) etaLeafX := .bvar _ 1 _ rfl

/-- `p : P`. -/
def etaLeafP_var : HasTyT E n etaLeafCtx (.bvar 0) etaLeafP := .bvar _ 0 _ rfl

/-- `f = x p : P → Prop`. -/
def etaLeafF_ty : HasTyT E n etaLeafCtx etaLeafF (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 1) (.bvar 0) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX_var etaLeafP_var

/-- The binder context of the η-expansion: `y : P, p : P, x : X`. -/
abbrev etaLeafCtx₁ : LCtx := .assumption etaLeafP :: etaLeafCtx

/-- Under the binder: `x : X`. -/
def etaLeafX_var₁ : HasTyT E n etaLeafCtx₁ (.bvar 2) etaLeafX := .bvar _ 2 _ rfl

/-- Under the binder: `p : P`. -/
def etaLeafP_var₁ : HasTyT E n etaLeafCtx₁ (.bvar 1) etaLeafP := .bvar _ 1 _ rfl

/-- Under the binder: the bound variable `y : P`. -/
def etaLeafY_var₁ : HasTyT E n etaLeafCtx₁ (.bvar 0) etaLeafP := .bvar _ 0 _ rfl

/-- Under the binder: `lift f = x p : P → Prop`. -/
def etaLeafLiftF_ty : HasTyT E n etaLeafCtx₁ (lift 0 1 etaLeafF) (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 1) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX_var₁ etaLeafP_var₁

/-- Under the binder: `x y : P → Prop`. -/
def etaLeafXY_ty :
    HasTyT E n etaLeafCtx₁ (.app (.bvar 2) (.bvar 0)) (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 0) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX_var₁ etaLeafY_var₁

/-- The η-expansion's body: `(x p) y : Prop`. -/
def etaLeafBody_ty : HasTyT E n etaLeafCtx₁ etaLeafBody (.sort .zero) :=
  .app _ (lift 0 1 etaLeafF) (.bvar 0) etaLeafP (.sort .zero) etaLeafLiftF_ty etaLeafY_var₁

/-- The stepped body: `(x y) y : Prop`. -/
def etaLeafBody'_ty : HasTyT E n etaLeafCtx₁ etaLeafBody' (.sort .zero) :=
  .app _ (.app (.bvar 2) (.bvar 0)) (.bvar 0) etaLeafP (.sort .zero) etaLeafXY_ty etaLeafY_var₁

/-- The η-expansion `b : P → Prop`. -/
def etaLeafB_ty : HasTyT E n etaLeafCtx (.lam etaLeafP etaLeafBody) (.pi etaLeafP (.sort .zero)) :=
  .lam _ etaLeafP .zero etaLeafBody (.sort .zero) (etaLeafP_ty _) etaLeafBody_ty

/-- The stepped λ `d : P → Prop`. -/
def etaLeafD_ty :
    HasTyT E n etaLeafCtx (.lam etaLeafP etaLeafBody') (.pi etaLeafP (.sort .zero)) :=
  .lam _ etaLeafP .zero etaLeafBody' (.sort .zero) (etaLeafP_ty _) etaLeafBody'_ty

/-! ### the two certified steps -/

/-- The leaf: the lifted `p` and the bound variable are two proofs of `P` under the binder. -/
def etaLeafLeaf (L : LeafIface E n PEq) : PEq etaLeafCtx₁ (.bvar 1) (.bvar 0) etaLeafP :=
  L.ofIrr (etaLeafP_ty _) etaLeafP_var₁ etaLeafY_var₁

/-- The certificate of the leaf. -/
def etaLeafLeafConv : ConvT E n etaLeafCtx₁ (.bvar 1) (.bvar 0) etaLeafP :=
  .irr _ etaLeafP (.bvar 1) (.bvar 0) (etaLeafP_ty _) etaLeafP_var₁ etaLeafY_var₁

/-- `lift f = x p ⇒ x y` under the binder (congruence, the argument by the leaf). -/
def etaLeafInnerStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx₁ (lift 0 1 etaLeafF) (.app (.bvar 2) (.bvar 0))
      (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0) etaLeafP (.pi etaLeafP (.sort .zero)) etaLeafX
    (.imax .zero (.succ .zero)) (.imax .zero (.succ .zero))
    (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) (.refl _ _) (etaLeafPiP_ty _) (etaLeafPiP_ty _)
    (.peq _ (.bvar 1) (.bvar 0) etaLeafP (etaLeafLeaf L)) etaLeafXY_ty

/-- Its certificate. -/
def etaLeafInnerConv :
    ConvT E n etaLeafCtx₁ (lift 0 1 etaLeafF) (.app (.bvar 2) (.bvar 0))
      (.pi etaLeafP (.sort .zero)) :=
  .app _ (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0) etaLeafP (.pi etaLeafP (.sort .zero))
    (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁) etaLeafLeafConv

/-- The inner step is certified. -/
def etaLeafInnerCert (L : LeafIface E n PEq) : Certified (etaLeafInnerStep L) :=
  .app etaLeafInnerConv (.refl (.refl _ (.bvar 2) etaLeafX etaLeafX_var₁)) (.peq etaLeafLeafConv)

/-- The body step `(x p) y ⇒ (x y) y` under the binder. -/
def etaLeafBodyStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx₁ etaLeafBody etaLeafBody' (.sort .zero) :=
  .app _ (lift 0 1 etaLeafF) (.app (.bvar 2) (.bvar 0)) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
    (.pi etaLeafP (.sort .zero)) (.succ .zero) (.succ .zero)
    (etaLeafInnerStep L) (.refl _ _) (.sort _ _) (.sort _ _)
    (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁) etaLeafBody'_ty

/-- Its certificate. -/
def etaLeafBodyConv : ConvT E n etaLeafCtx₁ etaLeafBody etaLeafBody' (.sort .zero) :=
  .app _ (lift 0 1 etaLeafF) (.app (.bvar 2) (.bvar 0)) (.bvar 0) (.bvar 0) etaLeafP (.sort .zero)
    etaLeafInnerConv (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁)

/-- The body step is certified. -/
def etaLeafBodyCert (L : LeafIface E n PEq) : Certified (etaLeafBodyStep L) :=
  .app etaLeafBodyConv (etaLeafInnerCert L) (.refl (.refl _ (.bvar 0) etaLeafP etaLeafY_var₁))

/-- The λ node: `b ⇒ d` at `P → Prop`. -/
def etaLeafLamStep (L : LeafIface E n PEq) :
    ParRedT PEq E n etaLeafCtx (.lam etaLeafP etaLeafBody) (.lam etaLeafP etaLeafBody')
      (.pi etaLeafP (.sort .zero)) :=
  .lam _ etaLeafP etaLeafP etaLeafBody etaLeafBody' (.sort .zero) .zero (.succ .zero)
    (.refl _ etaLeafP _ (etaLeafP_ty _)) (etaLeafP_ty _) (.sort _ _) (etaLeafBodyStep L) etaLeafD_ty

/-- The λ node is certified. -/
def etaLeafLamCert (L : LeafIface E n PEq) : Certified (etaLeafLamStep L) :=
  .lam (.lam _ etaLeafP etaLeafP etaLeafBody etaLeafBody' (.sort .zero) .zero
    (.refl _ etaLeafP _ (etaLeafP_ty _)) etaLeafBodyConv) (etaLeafBodyCert L)

/-- The η node: `b ⇒ f` at `P → Prop`. -/
def etaLeafEtaStep :
    ParRedT PEq E n etaLeafCtx (.lam etaLeafP etaLeafBody) etaLeafF (.pi etaLeafP (.sort .zero)) :=
  .eta _ etaLeafF etaLeafF etaLeafP (.sort .zero) (.refl _ etaLeafF _ etaLeafF_ty) etaLeafB_ty

/-- The η node is certified. -/
def etaLeafEtaCert : Certified (etaLeafEtaStep (PEq := PEq) (E := E) (n := n)) :=
  .eta (.eta _ etaLeafF etaLeafP (.sort .zero) etaLeafF_ty) (.refl (.refl _ etaLeafF _ etaLeafF_ty))

/-! ### no one-step join -/

/-- `e` is not a proof in `Γ`: no type of `e` is `Prop`-sorted. -/
def NotProof (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∀ {T : Expr Nat}, HasTyT E n Γ e T → HasTyT E n Γ T (.sort .zero) → False

/-- A certified step out of a λ that is neither an η-redex nor a proof lands on a λ: recursion
    on the certificate (`conv` peeled, `iotaSpine` through its inner step — ι never fires at a
    λ, `derivedIotaU_source`). -/
theorem lamStep_target (L : LeafIface E n PEq) {Γ : LCtx} {A b : Expr Nat}
    (hnotEta : ∀ g : Expr Nat, b ≠ .app (lift 0 1 g) (.bvar 0)) (hnp : NotProof E n Γ (.lam A b)) :
    {x j T : Expr Nat} → {p : ParRedT PEq E n Γ x j T} → Certified p → x = .lam A b →
    ∃ A' b' : Expr Nat, j = .lam A' b'
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx => by subst hx; exact ⟨A, b, rfl⟩
  | _, _, _, _, @Certified.lam _ _ _ _ _ A' _ b' _ _ _ _ _ _ _ _ _ _, _ => ⟨A', b', rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, hx => lamStep_target L hnotEta hnp ch hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx => by
      subst hx; exact (hnp (L.typed h).1 (L.prop h)).elim
  | _, _, _, _, @Certified.eta _ _ _ _ g _ _ _ _ _ _ _, hx => by
      injection hx with _ h2
      exact (hnotEta g h2.symm).elim
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, hx => by
      obtain ⟨A', b', e⟩ := lamStep_target L hnotEta hnp cs hx
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl
  | _, _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, _, .consts .., hx => nomatch hx
  | _, _, _, _, .bvarZeta .., hx => nomatch hx
  | _, _, _, _, .delta .., hx => nomatch hx
  | _, _, _, _, .app .., hx => nomatch hx
  | _, _, _, _, .beta .., hx => nomatch hx
  | _, _, _, _, .pi .., hx => nomatch hx
  | _, _, _, _, .letE .., hx => nomatch hx
  | _, _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, _, .lit .., hx => nomatch hx

/-- A certified step out of an assumption variable that is not a proof stays put. -/
theorem bvarStep_target (L : LeafIface E n PEq) {Γ : LCtx} {i : Nat} {X : Expr Nat}
    (hget : Γ.get? i = some (.assumption X)) (hnp : NotProof E n Γ (.bvar i)) :
    {x j T : Expr Nat} → {p : ParRedT PEq E n Γ x j T} → Certified p → x = .bvar i → j = .bvar i
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx => hx
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, hx => bvarStep_target L hget hnp ch hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx => by
      subst hx; exact (hnp (L.typed h).1 (L.prop h)).elim
  | _, _, _, _, @Certified.bvarZeta _ _ _ _ _ _ _ _ _ h _ _ _ _ _, hx => by
      injection hx with hi
      subst hi
      rw [hget] at h
      exact nomatch h
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, hx => by
      have e := bvarStep_target L hget hnp cs hx
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl
  | _, _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, _, .consts .., hx => nomatch hx
  | _, _, _, _, .delta .., hx => nomatch hx
  | _, _, _, _, .app .., hx => nomatch hx
  | _, _, _, _, .beta .., hx => nomatch hx
  | _, _, _, _, .lam .., hx => nomatch hx
  | _, _, _, _, .pi .., hx => nomatch hx
  | _, _, _, _, .letE .., hx => nomatch hx
  | _, _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, _, .lit .., hx => nomatch hx
  | _, _, _, _, .eta .., hx => nomatch hx

/-- A certified step out of `app (bvar i) (bvar k)` — `bvar i` an assumption variable that is
    not a proof, the application not a proof — lands on an application `app (bvar i) _`. -/
theorem appVarStep_target (L : LeafIface E n PEq) {Γ : LCtx} {i k : Nat} {X : Expr Nat}
    (hget : Γ.get? i = some (.assumption X)) (hnpx : NotProof E n Γ (.bvar i))
    (hnpf : NotProof E n Γ (.app (.bvar i) (.bvar k))) :
    {x j T : Expr Nat} → {p : ParRedT PEq E n Γ x j T} → Certified p →
    x = .app (.bvar i) (.bvar k) → ∃ a' : Expr Nat, j = .app (.bvar i) a'
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx => by subst hx; exact ⟨.bvar k, rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, hx =>
      appVarStep_target L hget hnpx hnpf ch hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx => by
      subst hx; exact (hnpf (L.typed h).1 (L.prop h)).elim
  | _, _, _, _, @Certified.app _ _ _ _ _ _ _ a' _ _ _ _ _ _ _ _ _ _ _ _ cf _, hx => by
      injection hx with h1 _
      have e := bvarStep_target L hget hnpx cf h1
      subst e
      exact ⟨a', rfl⟩
  | _, _, _, _, @Certified.beta .., hx => by
      injection hx with h1 _
      exact nomatch h1
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, hx => by
      obtain ⟨a', e⟩ := appVarStep_target L hget hnpx hnpf cs hx
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
      have hs := F8EtaK.appsSpine_fst_of_eq_foldApps_const hl.1
      simp [appsSpine] at hs
  | _, _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, _, .consts .., hx => nomatch hx
  | _, _, _, _, .bvarZeta .., hx => nomatch hx
  | _, _, _, _, .delta .., hx => nomatch hx
  | _, _, _, _, .lam .., hx => nomatch hx
  | _, _, _, _, .pi .., hx => nomatch hx
  | _, _, _, _, .letE .., hx => nomatch hx
  | _, _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, _, .lit .., hx => nomatch hx
  | _, _, _, _, .eta .., hx => nomatch hx

/-- The two reducts have no one-step join at any pair of indices: the λ side only reaches λs,
    the `f` side only applications of `x`. -/
theorem etaLeaf_no_join (L : LeafIface E n PEq)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF) (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    {T₁ T₂ : Expr Nat}
    (j : Join E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody') etaLeafF T₁ T₂) : False := by
  obtain ⟨j, pd, pe⟩ := j
  obtain ⟨A', b', e₁⟩ := lamStep_target L etaLeafBody'_not_eta hnpd pd.cert rfl
  obtain ⟨a', e₂⟩ :=
    appVarStep_target (Γ := etaLeafCtx) (i := 1) (k := 0) (X := etaLeafX) L rfl hnpx hnpf pe.cert rfl
  rw [e₁] at e₂
  exact nomatch e₂

/-- `CDiamond` is false for every leaf interface, in every environment where `d`, `f`, `x` are
    not proofs: the oracle applied to the pair would produce the one-step join. -/
theorem cdiamond_false_of_leaf (L : LeafIface E n PEq)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF) (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (D : CDiamond E n PEq) : False :=
  etaLeaf_no_join L hnpd hnpf hnpx
    (D etaLeafCtx_wf ⟨etaLeafLamStep L, etaLeafLamCert L⟩ ⟨etaLeafEtaStep, etaLeafEtaCert⟩)

/-- Hence `OpenRows` is uninhabited (through `cdiamond_of_rows`), under `EnvWfT` and the two
    leaf transports the assembler consumes. -/
theorem openRows_false_of_leaf (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        F8EtaK.AssumpCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF) (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (R : OpenRows E n PEq) : False :=
  cdiamond_false_of_leaf L hnpd hnpf hnpx
    (cdiamond_of_rows R hW L (certLift_of (PEq := PEq) (envClosed_of_envWfT hW) hPEqL)
      (certAssumpCtx_of (PEq := PEq) (envClosed_of_envWfT hW) (fun hcc hp => hPEqC hcc hp)))

/-- Hence the session-7 `RowFronts` is uninhabited as well (its field `LamEtaApp` asks for this
    join). -/
theorem rowFronts_false_of_leaf (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF) (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (F : RowFronts E n PEq) : False :=
  openRows_false_of_leaf hW L hPEqL (fun hcc hp => hPEqC_ofAssump (PEq := PEq) (fun hcc' hp' => hPEqC hcc' hp') hcc hp) hnpd hnpf hnpx
    (openRows_of hW L hPEqL hPEqC F)

end Rcic.Declarative.NativeValleys
