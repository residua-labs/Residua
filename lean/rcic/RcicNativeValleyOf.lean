import rcic.RcicNativeValleyCert

/-!
# RcicNativeValleyOf — the certified valley of every native `ConvT`, from the diamond oracle
(Wall 1, `NativeConvValleys`, piece 2: the producer)

By induction on the `ConvT` derivation (`valleyOf`): every conversion constructor yields a
certified valley (`CValley`, `RcicNativeValleyCert`) of typed parallel stars, the certificate of
each produced step being the conversion node itself or a composition of the sub-valleys'
certificates. No generic back-lift (`parRedT_to_convT`) is consulted anywhere, and no type
uniqueness: the certificates ARE the conversions the derivation already contains.

Two inputs remain explicit, each an exact theorem shape and neither assumed:

* `CDiamond` — the same-index one-step diamond on certified steps (`RcicNativeValleyCert`),
  consumed exactly once, at `ConvT.trans` (through `CValley.trans`).
* `LetValley` — the `ConvT.letE` row: the valley of two `let`s from the valleys of their
  values and of their bodies under the LEFT binding. It is kept separate because a parallel
  step under `letBinding A v :: Γ` does not transport to `letBinding A v' :: Γ` (the stored
  value is read by `bvarZeta`), so the right leg cannot reuse the body valley directly; the
  ζ-route through typed substitution is the subject of a following module.

Every other row is closed here: `refl`, `symm`, `trans` (oracle), `beta`, `zeta`, `zetaLocal`,
`delta`, `iota` (legacy witness, through `DerivedIotaU.ofU`), `lit`, `app` (function leg then
argument leg, dependent index realigned by `convT_inst0_valueSort` from the stored
certificates), `lam` (body leg under the left domain; the right domain is moved by one
reversible `ParRedT.lam` step with the body fixed, typing transported along `CtxConvT`), `pi`
(one step), `sorts`, `consts`, `eta`, `irr` (the leaf), `tyConv` (index transport).

Endpoint typings and index sorts are DATA (`endpoints3_of_envWfT`, `regularT_of_envWfT`,
`RcicTypedValidity.lean`), so the producer is `Type`-valued; `nativeConvValleys_of` is its
`Nonempty` shadow in the spec's §5.5 shape.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the two data-valued fronts off `EnvWfT` -/

/-- Both endpoint typings and the index's sort typing of a conversion, as data. -/
def convEnds (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) :
    HasTyT E n Γ a T ×' HasTyT E n Γ b T ×' (Σ' w, HasTyT E n Γ T (.sort w)) :=
  endpoints3_of_envWfT hW (substLetT_of_envWfT hW) (constsRightDataT_of_envWfT hW) hΓ c

/-- The sort of a typed term's type, as data. -/
def tySort (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e T : Expr Nat}
    (h : HasTyT E n Γ e T) : Σ' w, HasTyT E n Γ T (.sort w) :=
  regularT_of_envWfT hW (substLetT_of_envWfT hW) (constsRightDataT_of_envWfT hW) hΓ h

/-- `lookupValue` inverted: the stored declaration and the lift. -/
def lookupValue_inv {Γ : LCtx} {i : Nat} {v : Expr Nat} (h : lookupValue Γ i = some v) :
    Σ' (A₀ v₀ : Expr Nat), Γ.get? i = some (.letBinding A₀ v₀) ∧ v = lift 0 (i + 1) v₀ :=
  match hg : Γ.get? i with
  | some (.letBinding A₀ v₀) =>
      ⟨A₀, v₀, rfl, by
        simp only [lookupValue, hg] at h
        exact (Option.some.inj h).symm⟩
  | some (.assumption _) => by
      simp only [lookupValue, hg] at h
      exact nomatch h
  | none => by
      simp only [lookupValue, hg] at h
      exact nomatch h

/-- The remaining `let` row, as an exact shape: the valley of two `let`s from the valleys of
    their values and of their bodies under the LEFT binding. Not assumed; see the module
    docstring. -/
def LetValley (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' v v' b b' B : Expr Nat} {u : Level},
    ConvT E n Γ A A' (.sort u) → ConvT E n Γ v v' A →
    ConvT E n (.letBinding A v :: Γ) b b' B →
    CValley E n PEq Γ v v' A → CValley E n PEq (.letBinding A v :: Γ) b b' B →
    CValley E n PEq Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B)

/-! ### the congruence legs -/

/-- Function-position leg: `app · a` over a certified star on the function at `pi A B`; the
    index `instantiate0 a B` is constant. Each step is `ParRedT.app` with the argument reflexive,
    certified by `ConvT.app` of the step's certificate and `ConvT.refl`. -/
def appFunStar (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B a : Expr Nat} {v : Level}
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) (ha : HasTyT E n Γ a A) :
    {f g : Expr Nat} → CStar E n PEq Γ f g (.pi A B) →
    CStar E n PEq Γ (.app f a) (.app g a) (instantiate0 a B)
  | _, _, .refl _ f _ hf => .refl Γ (.app f a) _ (.app Γ f a A B hf ha)
  | _, _, @CStar.tail _ _ _ _ _ f' _ _ s hs =>
      let hf' : HasTyT E n Γ f' (.pi A B) := s.rightTyped L hΓ
      let hTy : HasTyT E n Γ (instantiate0 a B) (.sort v) :=
        hasTyT_subst0S (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hB ha
      .tail
        ⟨.app Γ _ f' a a A B (.pi A B) v v s.step (.refl Γ (.pi A B)) hB hTy
            (.refl Γ a A ha) (.app Γ f' a A B hf' ha),
          .app (.app Γ _ f' a a A B s.toConvT (.refl Γ a A ha)) s.cert (.refl (.refl Γ a A ha))⟩
        (appFunStar hW L hΓ hB ha hs)

/-- Argument-position leg: `app g ·` over a certified star on the argument at `A`, the function
    fixed and typed at `pi A B`. Each step is at `instantiate0 aᵢ B` and is realigned to the
    leg's head index `instantiate0 a₀ B` by the prefix certificate `c₀ : a₀ ↔ aᵢ`
    (`convT_inst0_valueSort`); the reduct typing uses the step's own certificate. -/
def appArgStar (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B g : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hg : HasTyT E n Γ g (.pi A B)) {a₀ : Expr Nat} (ha₀ : HasTyT E n Γ a₀ A) :
    {a b : Expr Nat} → CStar E n PEq Γ a b A → ConvT E n Γ a₀ a A →
    CStar E n PEq Γ (.app g a) (.app g b) (instantiate0 a₀ B)
  | _, _, .refl _ a₁ _ ha₁, c₀ =>
      .refl Γ (.app g a₁) _
        (hasTyT_of_tyConvT (.app Γ g a₁ A B hg ha₁)
          (.of _ _ _ v (convT_inst0_valueSort hA hB ha₁ ha₀ (.symm _ _ _ _ c₀))))
  | _, _, @CStar.tail _ _ _ _ a a' _ _ s hs, c₀ =>
      let ha : HasTyT E n Γ a A := s.leftTyped L hΓ
      let ha' : HasTyT E n Γ a' A := s.rightTyped L hΓ
      let hTy : HasTyT E n Γ (instantiate0 a B) (.sort v) :=
        hasTyT_subst0S (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hB ha
      let hr : HasTyT E n Γ (.app g a') (instantiate0 a B) :=
        .conv Γ _ _ _ v (.app Γ g a' A B hg ha')
          (convT_inst0_valueSort hA hB ha' ha (.symm _ _ _ _ s.toConvT))
      let step : CStep E n PEq Γ (.app g a) (.app g a') (instantiate0 a B) :=
        ⟨.app Γ g g a a' A B (.pi A B) v v (.refl Γ g _ hg) (.refl Γ (.pi A B)) hB hTy
            s.step hr,
          .app (.app Γ g g a a' A B (.refl Γ g _ hg) s.toConvT) (.refl (.refl Γ g _ hg)) s.cert⟩
      .tail
        (step.reindex (.of _ _ _ v (convT_inst0_valueSort hA hB ha ha₀ (.symm _ _ _ _ c₀))))
        (appArgStar hW L hΓ hA hB hg ha₀ hs (.trans _ _ _ _ _ c₀ s.toConvT))

/-- Body leg of a λ under the LEFT domain: each step is `ParRedT.lam` with the reflexive domain
    conversion, certified by `ConvT.lam`. -/
def lamBodyStar (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    {b c : Expr Nat} → CStar E n PEq (.assumption A :: Γ) b c B →
    CStar E n PEq Γ (.lam A b) (.lam A c) (.pi A B)
  | _, _, .refl _ b _ hb => .refl Γ (.lam A b) _ (.lam Γ A u b B hA hb)
  | _, _, @CStar.tail _ _ _ _ _ b' _ _ s hs =>
      let hb' : HasTyT E n (.assumption A :: Γ) b' B := s.rightTyped L (.assumption Γ A u hΓ hA)
      .tail
        ⟨.lam Γ A A _ b' B u v (.refl Γ A _ hA) hA hB s.step (.lam Γ A u b' B hA hb'),
          .lam (.lam Γ A A _ b' B u (.refl Γ A _ hA) s.toConvT) s.cert⟩
        (lamBodyStar L hΓ hA hB hs)

/-! ### the rows -/

/-- `ConvT.app`: function leg to the function centre, then argument leg to the argument centre;
    the right leg is realigned from `instantiate0 b B` to `instantiate0 a B` by the node's own
    argument conversion. -/
def valley_app (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f g a b A B : Expr Nat}
    (h1 : ConvT E n Γ f g (.pi A B)) (h2 : ConvT E n Γ a b A)
    (vf : CValley E n PEq Γ f g (.pi A B)) (va : CValley E n PEq Γ a b A) :
    CValley E n PEq Γ (.app f a) (.app g b) (instantiate0 a B) :=
  let e1 := convEnds hW hΓ h1
  let e2 := convEnds hW hΓ h2
  match hasTyTInv_pi e1.2.2.2 rfl with
  | ⟨_, v, hA, hB, _⟩ =>
    let hfc : HasTyT E n Γ vf.centre (.pi A B) := vf.left.rightTyped
    let left : CStar E n PEq Γ (.app f a) (.app vf.centre va.centre) (instantiate0 a B) :=
      (appFunStar hW L hΓ hB e2.1 vf.left).trans
        (appArgStar hW L hΓ hA hB hfc e2.1 va.left (.refl Γ a A e2.1))
    let right : CStar E n PEq Γ (.app g b) (.app vf.centre va.centre) (instantiate0 a B) :=
      ((appFunStar hW L hΓ hB e2.2.1 vf.right).trans
        (appArgStar hW L hΓ hA hB hfc e2.2.1 va.right (.refl Γ b A e2.2.1))).reindex
        (.of _ _ _ v (convT_inst0_valueSort hA hB e2.2.1 e2.1 (.symm _ _ _ _ h2)))
    ⟨.app vf.centre va.centre, left, right⟩

/-- `ConvT.lam`: body leg under the left domain on the left; on the right, one reversible
    `ParRedT.lam` step moves the domain `A' → A` with the body fixed (typings transported along
    `CtxConvT.assumption`), then the body leg. The centre is `lam A bc`. -/
def valley_lam (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hb : ConvT E n (.assumption A :: Γ) b b' B)
    (vb : CValley E n PEq (.assumption A :: Γ) b b' B) :
    CValley E n PEq Γ (.lam A b) (.lam A' b') (.pi A B) :=
  let eA := convEnds hW hΓ hA
  let eb := convEnds hW (.assumption Γ A u hΓ eA.1) hb
  match eb.2.2 with
  | ⟨v, hB⟩ =>
    let hcl := envClosed_of_envWfT hW
    let hcc : CtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ) :=
      .assumption (ctxConvT_refl Γ) eA.1 eA.2.1 hA
    let hB' : HasTyT E n (.assumption A' :: Γ) B (.sort v) := hasTyT_ctx hcl hcc hB
    let hb'' : HasTyT E n (.assumption A' :: Γ) b' B := hasTyT_ctx hcl hcc eb.2.1
    let piConv : ConvT E n Γ (.pi A B) (.pi A' B) (.sort (.imax u v)) :=
      .pi Γ A A' B B u v hA (.refl _ B _ hB)
    let step0 : CStep E n PEq Γ (.lam A' b') (.lam A b') (.pi A' B) :=
      ⟨.lam Γ A' A b' b' B u v (.symm _ _ _ _ hA) eA.2.1 hB' (.refl _ b' B hb'')
          (.conv Γ _ _ _ (.imax u v) (.lam Γ A u b' B eA.1 eb.2.1) piConv),
        .lam (.lam Γ A' A b' b' B u (.symm _ _ _ _ hA) (.refl _ b' B hb''))
          (.refl (.refl _ b' B hb''))⟩
    ⟨.lam A vb.centre, lamBodyStar L hΓ eA.1 hB vb.left,
      .tail (step0.reindex (.of _ _ _ (.imax u v) (.symm _ _ _ _ piConv)))
        (lamBodyStar L hΓ eA.1 hB vb.right)⟩

/-- `ConvT.pi`: one `ParRedT.pi` step, the node its own certificate. -/
def valley_pi (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    CValley E n PEq Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) :=
  let eA := convEnds hW hΓ hA
  let eB := convEnds hW (.assumption Γ A u hΓ eA.1) hB
  let c : ConvT E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) := .pi Γ A A' B B' u v hA hB
  let eP := convEnds hW hΓ c
  CValley.ofStep L hΓ ⟨.pi Γ A A' B B' u v eA.1 hA eB.1 hB eP.2.1, .pi c⟩

/-- `ConvT.beta`: one `ParRedT.beta` step with reflexive body and argument. -/
def valley_beta (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    CValley E n PEq Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) :=
  let c : ConvT E n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) :=
    .beta Γ A body arg B u hA hbody harg
  let e := convEnds hW hΓ c
  match tySort hW (.assumption Γ A u hΓ hA) hbody, e.2.2 with
  | ⟨v, hB⟩, ⟨w, hTy⟩ =>
    CValley.ofStep L hΓ
      ⟨.beta Γ A body body arg arg B u v w hA hB hTy (.refl _ body B hbody) (.refl Γ arg A harg)
          e.2.1,
        .beta c (.refl (.refl _ body B hbody)) (.refl (.refl Γ arg A harg))⟩

/-- `ConvT.zeta`: one `ParRedT.zeta` step with reflexive value and body; the index sort by
    `let` substitution. -/
def valley_zeta (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    CValley E n PEq Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B) :=
  let c : ConvT E n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B) :=
    .zeta Γ A value body B u hA hv hb
  let e := convEnds hW hΓ c
  match tySort hW (.letBinding Γ A u value hΓ hA hv) hb with
  | ⟨w, hB⟩ =>
    let hTy : HasTyT E n Γ (instantiate0 value B) (.sort w) :=
      hasTyT_substLet0_of_envWfT hW hB hv
    CValley.ofStep L hΓ
      ⟨.zeta Γ A value value body body B u w hA (.refl Γ value A hv) hB hTy
          (.refl _ body B hb) e.2.1,
        .zeta c (.refl (.refl Γ value A hv)) (.refl (.refl _ body B hb))⟩

/-- `ConvT.zetaLocal`: one `ParRedT.bvarZeta` step with the stored value reflexive. -/
def valley_zetaLocal (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A) : CValley E n PEq Γ (.bvar i) v A :=
  match lookupValue_inv hval with
  | ⟨A₀, v₀, hget, hveq⟩ => by
    subst hveq
    exact CValley.ofStep L hΓ
      ⟨.bvarZeta Γ i A₀ v₀ v₀ A hget (.refl _ v₀ A₀ (ctxWfTLookupValueAtDrop hΓ i hget))
          (.bvar Γ i A hty) hv,
        .bvarZeta (.zetaLocal Γ i A _ hval hty hv)
          (.refl (.refl _ v₀ A₀ (ctxWfTLookupValueAtDrop hΓ i hget)))⟩

/-- `ConvT.delta`: one `ParRedT.delta` step. -/
def valley_delta (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    CValley E n PEq Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype) :=
  CValley.ofStep L hΓ
    ⟨.delta Γ r ls m b _ hres hbody htr hlen hwf (.const Γ r ls m hres hlen hwf) hb,
      .delta (.delta Γ r ls m b hres hbody htr hlen hwf hb)⟩

/-- `ConvT.iota` (legacy witness): one `ParRedT.iotaSpine` step at the unstepped redex, the
    union landing `DerivedIotaU.ofU`. -/
def valley_iota (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T) :
    CValley E n PEq Γ lhs rhs T :=
  CValley.ofStep L hΓ
    ⟨.iotaSpine Γ lhs lhs rhs T (.refl Γ lhs T hlhs) (derivedIotaU_ofDerivedIota h) hlhs hrhs,
      .iotaSpine (.iota Γ lhs rhs T h hlhs hrhs) (.refl (.refl Γ lhs T hlhs))⟩

/-- `ConvT.lit`: one `ParRedT.lit` step. -/
def valley_lit (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t : Nat} {exp T : Expr Nat}
    (h : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp T) :
    CValley E n PEq Γ (.lit t) exp T :=
  by
  cases h with
  | of =>
    exact CValley.ofStep L hΓ ⟨.lit Γ t T hexp, .lit (.lit Γ t (natExpand t) T (.of t) hexp)⟩

/-- `ConvT.sorts`: one `ParRedT.sortEq` step. -/
def valley_sorts (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    CValley E n PEq Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) :=
  let c : ConvT E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) := .sorts Γ l₁ l₂ h
  let e := convEnds hW hΓ c
  CValley.ofStep L hΓ ⟨.sortEq Γ l₁ l₂ _ h e.1 e.2.1, .sortEq c⟩

/-- `ConvT.consts`: one `ParRedT.consts` step. -/
def valley_consts (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls ls' : List Level}
    {m : CheckedMember} (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls') :
    CValley E n PEq Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) :=
  let c : ConvT E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) :=
    .consts Γ r ls ls' m hres hlen hwf hwf' h
  let e := convEnds hW hΓ c
  CValley.ofStep L hΓ ⟨.consts Γ r ls ls' _ h e.1 e.2.1, .consts c⟩

/-- `ConvT.eta`: one `ParRedT.eta` step with the function reflexive. -/
def valley_eta (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f A B : Expr Nat}
    (h : HasTyT E n Γ f (.pi A B)) :
    CValley E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) :=
  let c : ConvT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) := .eta Γ f A B h
  let e := convEnds hW hΓ c
  CValley.ofStep L hΓ ⟨.eta Γ f f A B (.refl Γ f _ h) e.1, .eta c (.refl (.refl Γ f _ h))⟩

/-! ### the producer -/

/-- The certified valley of every native conversion, from the diamond oracle (used only at
    `trans`) and the `let` row. Structural recursion on the `ConvT`; the context grows at
    `lam` / `letE` bodies by the node's own domain typings. -/
def valleyOf (hW : EnvWfT E) (L : LeafIface E n PEq) (D : CDiamond E n PEq)
    (Lt : LetValley E n PEq) :
    {Γ : LCtx} → CtxWfT E n Γ → {a b T : Expr Nat} → ConvT E n Γ a b T →
    CValley E n PEq Γ a b T
  | _, _, _, _, _, .refl _ _ _ h => .refl h
  | _, hΓ, _, _, _, .symm _ _ _ _ h => (valleyOf hW L D Lt hΓ h).symm
  | _, hΓ, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      CValley.trans D L hΓ (valleyOf hW L D Lt hΓ h1) (valleyOf hW L D Lt hΓ h2)
  | _, hΓ, _, _, _, .beta _ _ _ _ _ _ hA hbody harg => valley_beta hW L hΓ hA hbody harg
  | _, hΓ, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => valley_zeta hW L hΓ hA hv hb
  | _, hΓ, _, _, _, .zetaLocal _ _ _ _ hval hty hv => valley_zetaLocal L hΓ hval hty hv
  | _, hΓ, _, _, _, .delta _ _ _ _ _ hres hbody htr hlen hwf hb =>
      valley_delta L hΓ hres hbody htr hlen hwf hb
  | _, hΓ, _, _, _, .iota _ _ _ _ h hlhs hrhs => valley_iota L hΓ h hlhs hrhs
  | _, hΓ, _, _, _, .lit _ _ _ _ h hexp => valley_lit L hΓ h hexp
  | _, hΓ, _, _, _, .app _ _ _ _ _ _ _ h1 h2 =>
      valley_app hW L hΓ h1 h2 (valleyOf hW L D Lt hΓ h1) (valleyOf hW L D Lt hΓ h2)
  | _, hΓ, _, _, _, .lam _ A₁ _ _ _ _ u₁ hA hb =>
      valley_lam hW L hΓ hA hb
        (valleyOf hW L D Lt (.assumption _ A₁ u₁ hΓ (convEnds hW hΓ hA).1) hb)
  | _, hΓ, _, _, _, .pi _ _ _ _ _ _ _ hA hB => valley_pi hW L hΓ hA hB
  | _, hΓ, _, _, _, .letE _ A₁ _ v₁ _ _ _ _ u₁ hA hv hb =>
      Lt hΓ hA hv hb (valleyOf hW L D Lt hΓ hv)
        (valleyOf hW L D Lt
          (.letBinding _ A₁ u₁ v₁ hΓ (convEnds hW hΓ hA).1 (convEnds hW hΓ hv).1) hb)
  | _, hΓ, _, _, _, .sorts _ _ _ h => valley_sorts hW L hΓ h
  | _, hΓ, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h =>
      valley_consts hW L hΓ hres hlen hwf hwf' h
  | _, hΓ, _, _, _, .eta _ _ _ _ h => valley_eta hW L hΓ h
  | _, hΓ, _, _, _, .irr _ _ _ _ hP hp hq => CValley.ofStep L hΓ (CStep.irr L hP hp hq)
  | _, hΓ, _, _, _, .tyConv _ _ _ _ _ u h hA => (valleyOf hW L D Lt hΓ h).reindex (.of _ _ _ u hA)

/-- The spec's `NativeConvValleys` shape (§5.5), for any leaf satisfying `LeafIface`, from the
    two explicit inputs: every conversion in a well-formed context has a valley of typed
    parallel stars. `Nonempty` shadow of `valleyOf`. -/
theorem nativeConvValleys_of (hW : EnvWfT E) (L : LeafIface E n PEq) (D : CDiamond E n PEq)
    (Lt : LetValley E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  (valleyOf hW L D Lt hΓ c).exists_join


end Rcic.Declarative.NativeValleys
