import rcic.RcicNativeValleyLift
import rcic.RcicNativeValleyCtx
import rcic.RcicDTMetaTypedSR

/-!
# RcicNativeValleyAssemble — the core assembler of the certified diamond
(Wall 1, `NativeConvValleys`, piece 7)

`assemble` joins two certified steps out of one term, at INDEPENDENT indices, by recursion on
`sizeOf p + sizeOf q`: the first step's root is matched (through its certificate), every
compatible root of the second step is dispatched by a per-shape helper that reads the second
step's source through an explicit equation (the landed `parRedT_lam` technique, so no two
constructor patterns are ever unified against each other), head-disjoint pairs are refuted by
that equation, `conv` roots are peeled one layer at a time, `refl` / `peq` roots are the generic
rows, `iotaSpine` roots the generic ι row, and the K roots are vacuous (`Certified.noK`).

The rows that close here: `sortEq²`, `consts²`, `pi²`, `delta²`, `lit²` (`RcicNativeValleyRows`),
`app²` and `eta²` from the children's joins (same module), `lam²` from the children's join and
the certified assumption transport (`row_lam_lam`, `RcicNativeValleyCtx`), `bvarZeta²` from the
stored values' join and the certified weakening (`row_bvarZeta_bvarZeta`,
`RcicNativeValleyLift`), `beta²` from the children's joins and the one-step certified mixed
substitution (`row_beta_beta`).

Everything else is a field of ONE structure `OpenRows`, each with its exact statement and the
induction hypothesis on strictly smaller pairs (`IHBelow`) where it recurses; none is equivalent
to the goal:

* `retype` — a certified step out of `b` at `T₂` presented at another type `T₁` of `b`. Consumed
  ONLY at `refl × q` / `p × refl` / `peq × q` / `p × peq` when the two inputs carry DIFFERENT
  indices (`retypeAt` casts when they coincide). It is where same-term type connection enters:
  the children of `app × app` sit at the two nodes' own Π data, so the recursion cannot keep
  the indices connected. See `NATIVE_VALLEYS_STATUS.md` §2b.
* `consts_delta`, `app_beta`, `lam_eta`, `letE_letE`, `letE_zeta`, `zeta_zeta` — the remaining
  core pairs, in row form.
* `subst0` — the one-step certified mixed substitution (`CertSubst0`), consumed by `beta²`.
* `iota_commute` — ι commutes with a certified step out of its (stepped) redex, in the
  one-step shape the diamond needs (the star-shaped `IotaCommuteT` of `RcicNativeValleyRows`
  does not feed a one-step join). Its output at the other input's index is an `IotaTail`:
  ι re-fires at the stepped redex, OR the join is the stepped redex itself — the second
  alternative is forced because the step into it may be an irrelevance LEAF (the assembler
  emits `CStep.irr` legs at `peq` roots, `join_peq_indep`), and ι does not fire at an
  arbitrary proof (session 7 finding; the earlier statement without this alternative was
  unprovable).

`coreDiamond_of_rows` / `cdiamond_of_rows` / `valleyOf_rows` / `nativeConvValleys_of_rows`
close the chain `OpenRows → CoreDiamond → CDiamond → NativeConvValleys (§5.5 shape)`.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the induction hypothesis a row receives -/

/-- The independent-index diamond on every pair of certified steps of total size below `m`. -/
def IHBelow (E : ResolvedEnv) (n : Nat) (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (m : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T₁ T₂ : Expr Nat} {p : ParRedT PEq E n Γ b d T₁},
    Certified p → ∀ {q : ParRedT PEq E n Γ b e T₂}, Certified q →
    sizeOf p + sizeOf q < m → Join E n PEq Γ d e T₁ T₂

/-- The bound is symmetric. -/
def IHBelow.comm {a b : Nat} (ih : IHBelow E n PEq (a + b)) : IHBelow E n PEq (b + a) :=
  fun {_} hΓ {_ _ _ _ _} {_} cp {_} cq hlt => ih hΓ cp cq (by omega)

/-! ### the ι row's output at the other index -/

/-- What the ι row returns at the OTHER input's index `T'`: either ι re-fires at the stepped
    redex `k` (new reduct `j`, typed at `T'`, natively convertible to `k` there), or the join
    IS `k` (`j = k`: the step into `k` went through an irrelevance leaf, so `k`, the original
    reduct and the redex are proofs of one `Prop`, and the original reduct steps to `k` by
    irrelevance at its own index). -/
inductive IotaTail (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (k j T' : Expr Nat) : Type
  | refire (hI' : DerivedIotaU E k j) (hj : HasTyT E n Γ j T') (c : ConvT E n Γ k j T')
  | stay (h : j = k)

/-! ### the open rows -/

/-- The rows the assembler does not close, each in its exact shape (see the module
    docstring). Fields receive the two steps' certificates, the children's certificates where
    they recurse, and the induction hypothesis on strictly smaller pairs. -/
structure OpenRows (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type where
  /-- (R) a certified step out of `b` at `T₂`, presented at another type `T₁` of `b`. -/
  retype : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b e T₁ T₂ : Expr Nat},
    HasTyT E n Γ b T₁ → CStep E n PEq Γ b e T₂ → CStep E n PEq Γ b e T₁
  /-- `consts × delta`: `const r ls → const r ls'` against `const r ls → inst ls b`. -/
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
  /-- the one-step certified mixed substitution at an assumption hole (`beta × beta`). -/
  subst0 : CertSubst0 E n PEq
  /-- `app × beta`: the function child steps out of the λ, the other side contracts. -/
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
    IHBelow E n PEq
      (sizeOf (ParRedT.app (PEq := PEq) Γ (.lam A body) f' arg a' A' B' T₀ v w hf hc hB hTy
        ha hr) +
       sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v' w' hA hB₂ hTy₂ hb ha₂
        hred)) →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B)
  /-- `lam × eta`: the body child steps out of the η-expansion, the other side contracts. -/
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
    IHBelow E n PEq
      (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' (.app (lift 0 1 f) (.bvar 0)) body' B₁ u v hc
        hA hB hb hrt) +
       sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B₂ hf hl)) →
    Join E n PEq Γ (.lam A' body') f' (.pi A B₁) (.pi A B₂)
  /-- `letE × letE`: both bodies step under the SOURCE binding, the outputs step theirs under
      the stepped bindings (the let-value bridge, `LETBRIDGE_STATUS.md`). -/
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
    IHBelow E n PEq
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.letE (PEq := PEq) Γ A A₂ value value₂ body body₂ B₂ u₂ w₂ hc₂ hA₂ hv₂
        hB₂ hTy₂ hb₂ hrt₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂)
  /-- `letE × zeta`. -/
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
    IHBelow E n PEq
      (sizeOf (ParRedT.letE (PEq := PEq) Γ A A₁ value value₁ body body₁ B₁ u₁ w₁ hc₁ hA₁ hv₁
        hB₁ hTy₁ hb₁ hrt₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (.letE A₁ value₁ body₁) (instantiate0 value₂ body₂) (instantiate0 value B₁)
      (instantiate0 value B₂)
  /-- `zeta × zeta`. -/
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
    IHBelow E n PEq
      (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₁ body body₁ B₁ u₁ w₁ hA₁ hv₁ hB₁ hTy₁
        hb₁ hred₁) +
       sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value₂ body body₂ B₂ u₂ w₂ hA₂ hv₂ hB₂ hTy₂
        hb₂ hred₂)) →
    Join E n PEq Γ (instantiate0 value₁ body₁) (instantiate0 value₂ body₂)
      (instantiate0 value B₁) (instantiate0 value B₂)
  /-- (ι) ι commutes with a certified step out of its redex, one-step shape: with `lhs' →ι rhs`
      (its certificate `ConvT lhs' rhs T` supplied), a certified `lhs' ⇒ k` at `T`, `rhs : T`
      and `k : T'`, some `j` has `rhs ⇒ j` at `T` and, at `T'`, ι re-fires at `k` onto `j` or
      `j = k` (`IotaTail`). -/
  iota_commute : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {lhs' rhs k T T' : Expr Nat},
    DerivedIotaU E lhs' rhs → ConvT E n Γ lhs' rhs T → CStep E n PEq Γ lhs' k T →
    HasTyT E n Γ rhs T → HasTyT E n Γ k T' →
    Σ' (j : Expr Nat), CStep E n PEq Γ rhs j T ×' IotaTail E n Γ k j T'

/-! ### index handling -/

/-- Casting a certified step along a syntactic index equation. -/
def CStep.castIdx {Γ : LCtx} {b e T₁ T₂ : Expr Nat} (h : T₁ = T₂)
    (s : CStep E n PEq Γ b e T₂) : CStep E n PEq Γ b e T₁ := by
  subst h; exact s

/-- Present a certified step out of `b` at another type `T₁` of `b`: the cast when the indices
    coincide syntactically, the open row `retype` otherwise. -/
def retypeAt (R : OpenRows E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T₁ T₂ : Expr Nat}
    (hb : HasTyT E n Γ b T₁) (s : CStep E n PEq Γ b e T₂) : CStep E n PEq Γ b e T₁ :=
  if h : T₁ = T₂ then CStep.castIdx h s else R.retype hΓ hb s

/-- Swap the two legs of an independent-index join. -/
def join_swap_indep {Γ : LCtx} {d e T₁ T₂ : Expr Nat} (j : Join E n PEq Γ d e T₁ T₂) :
    Join E n PEq Γ e d T₂ T₁ :=
  ⟨j.1, j.2.2, j.2.1⟩

/-! ### the generic rows at independent indices -/

/-- `refl × q`: the join is `q`'s target; `q` is presented at the `refl`'s index. -/
def join_refl_indep (R : OpenRows E n PEq) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b e T₁ T₂ : Expr Nat} (h : HasTyT E n Γ b T₁)
    (q : CStep E n PEq Γ b e T₂) : Join E n PEq Γ b e T₁ T₂ :=
  ⟨e, retypeAt R hΓ h q,
    ⟨.refl Γ e T₂ (q.rightTyped L hΓ), .refl (.refl Γ e T₂ (q.rightTyped L hΓ))⟩⟩

/-- `peq × q`: the join is `q`'s target, reached from the leaf's target by one irrelevance
    step at the leaf's `Prop`-sorted index (where `q`'s target is typed through `retype`). -/
def join_peq_indep (R : OpenRows E n PEq) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat} (h : PEq Γ b d T₁)
    (q : CStep E n PEq Γ b e T₂) : Join E n PEq Γ d e T₁ T₂ :=
  let he : HasTyT E n Γ e T₁ := (retypeAt R hΓ (L.typed h).1 q).rightTyped L hΓ
  ⟨e, CStep.irr L (L.prop h) (L.typed h).2 he,
    ⟨.refl Γ e T₂ (q.rightTyped L hΓ), .refl (.refl Γ e T₂ (q.rightTyped L hΓ))⟩⟩

/-- `iotaSpine × q` from the join of the inner step with `q`: at the join `k`, ι re-fires
    (`iota_commute`, the original reduct steps to the new one; `q`'s side absorbs the ι into
    one `iotaSpine` step) or the join is `k` itself (`q`'s leg is already there). -/
def join_iotaSpine_left (R : OpenRows E n PEq) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {lhs' rhs e T₁ T₂ : Expr Nat} (hI : DerivedIotaU E lhs' rhs)
    (hc : ConvT E n Γ lhs' rhs T₁) (hrhs : HasTyT E n Γ rhs T₁)
    (jk : Join E n PEq Γ lhs' e T₁ T₂) : Join E n PEq Γ rhs e T₁ T₂ :=
  let ⟨k, pk, qk⟩ := jk
  let hk₂ : HasTyT E n Γ k T₂ := qk.rightTyped L hΓ
  match R.iota_commute hΓ hI hc pk hrhs hk₂ with
  | ⟨j, pr, .refire hI' hj ck⟩ =>
      ⟨j, pr, ⟨.iotaSpine Γ e k j T₂ qk.step hI' hk₂ hj,
        .iotaSpine (.trans _ _ _ _ _ qk.toConvT ck) qk.cert⟩⟩
  | ⟨j, pr, .stay h⟩ => ⟨j, pr, by subst h; exact qk⟩

/-! ### the rows closed here -/

/-- One side of `lam × lam`: from the body join leg `body₁ ⇒ body₃` under the SOURCE domain,
    the certified step `lam A₁ body₁ ⇒ lam A body₃` at the node's own index `pi A B₁`. The join
    keeps the source domain `A` (so no two domain conversions at different sorts are ever
    composed); the body leg moves under `A₁` by the certified assumption transport. -/
def lamSide (hW : EnvWfT E) (L : LeafIface E n PEq) (Ac : CertAssumpCtx E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A₁ body₁ body₃ B₁ : Expr Nat} {u₁ v₁ : Level}
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁)) (hA : HasTyT E n Γ A (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B₁ (.sort v₁))
    (pb : CStep E n PEq (.assumption A :: Γ) body₁ body₃ B₁) :
    CStep E n PEq Γ (.lam A₁ body₁) (.lam A body₃) (.pi A B₁) :=
  let hcl := envClosed_of_envWfT hW
  let hA₁ : HasTyT E n Γ A₁ (.sort u₁) := (convEnds hW hΓ hc₁).2.1
  let hctx : CtxConvT E n (.assumption A :: Γ) (.assumption A₁ :: Γ) :=
    .assumption (ctxConvT_refl Γ) hA hA₁ hc₁
  let hB₁' : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v₁) := hasTyT_ctx hcl hctx hB₁
  let pb' : CStep E n PEq (.assumption A₁ :: Γ) body₁ body₃ B₁ := Ac hA hA₁ hc₁ pb
  let hbody₃ : HasTyT E n (.assumption A :: Γ) body₃ B₁ :=
    pb.rightTyped L (.assumption Γ A u₁ hΓ hA)
  let hrt : HasTyT E n Γ (.lam A body₃) (.pi A₁ B₁) :=
    .conv Γ _ _ _ (.imax u₁ v₁) (.lam Γ A u₁ body₃ B₁ hA hbody₃)
      (.pi Γ A A₁ B₁ B₁ u₁ v₁ hc₁ (.refl _ B₁ _ hB₁))
  let step : CStep E n PEq Γ (.lam A₁ body₁) (.lam A body₃) (.pi A₁ B₁) :=
    ⟨.lam Γ A₁ A body₁ body₃ B₁ u₁ v₁ (.symm _ _ _ _ hc₁) hA₁ hB₁' pb'.step hrt,
      .lam (.lam Γ A₁ A body₁ body₃ B₁ u₁ (.symm _ _ _ _ hc₁) pb'.toConvT) pb'.cert⟩
  step.reindex (.of _ _ _ (.imax u₁ v₁)
    (.pi Γ A₁ A B₁ B₁ u₁ v₁ (.symm _ _ _ _ hc₁) (.refl _ B₁ _ hB₁')))

/-- `lam × lam` from the bodies' join (under the source domain); the two nodes' domain data
    (`hc₁ hA₁ hB₁`, `hc₂ hA₂ hB₂`) are all the row reads. -/
def row_lam_lam (hW : EnvWfT E) (L : LeafIface E n PEq) (Ac : CertAssumpCtx E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A₁ A₂ body₁ body₂ B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁)) (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hc₂ : ConvT E n Γ A A₂ (.sort u₂)) (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B₂ (.sort v₂))
    (jb : Join E n PEq (.assumption A :: Γ) body₁ body₂ B₁ B₂) :
    Join E n PEq Γ (.lam A₁ body₁) (.lam A₂ body₂) (.pi A B₁) (.pi A B₂) :=
  let ⟨body₃, pb, qb⟩ := jb
  ⟨.lam A body₃, lamSide hW L Ac hΓ hc₁ hA₁ hB₁ pb, lamSide hW L Ac hΓ hc₂ hA₂ hB₂ qb⟩

/-- `beta × beta` from the bodies' and arguments' joins through the one-step certified mixed
    substitution; each output is realigned to its node's index by its ARGUMENT child's
    certificate. -/
def row_beta_beta (L : LeafIface E n PEq) (S : CertSubst0 E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A body₁ body₂ arg arg₁ arg₂ B₁ B₂ : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : HasTyT E n Γ A (.sort u₁)) (hB₁ : HasTyT E n (.assumption A :: Γ) B₁ (.sort v₁))
    {ha₁ : ParRedT PEq E n Γ arg arg₁ A} (ca₁ : Certified ha₁)
    (hA₂ : HasTyT E n Γ A (.sort u₂)) (hB₂ : HasTyT E n (.assumption A :: Γ) B₂ (.sort v₂))
    {ha₂ : ParRedT PEq E n Γ arg arg₂ A} (ca₂ : Certified ha₂)
    (jb : Join E n PEq (.assumption A :: Γ) body₁ body₂ B₁ B₂)
    (ja : Join E n PEq Γ arg₁ arg₂ A A) :
    Join E n PEq Γ (instantiate0 arg₁ body₁) (instantiate0 arg₂ body₂) (instantiate0 arg B₁)
      (instantiate0 arg B₂) :=
  let ⟨body₃, pb, qb⟩ := jb
  let ⟨arg₃, pa, qa⟩ := ja
  let harg : HasTyT E n Γ arg A := parRedT_hasTy_left L.typed hΓ ha₁
  let s₁ := S hΓ hA₁ pb pa
  let s₂ := S hΓ hA₂ qb qa
  ⟨instantiate0 arg₃ body₃,
    s₁.reindex (.of _ _ _ v₁
      (convT_inst0_valueSort hA₁ hB₁ (pa.leftTyped L hΓ) harg (.symm _ _ _ _ ca₁.root))),
    s₂.reindex (.of _ _ _ v₂
      (convT_inst0_valueSort hA₂ hB₂ (qa.leftTyped L hΓ) harg (.symm _ _ _ _ ca₂.root)))⟩

/-- `bvarZeta × bvarZeta` from the stored values' join below the binder: the outputs are the
    certified lifts of the join legs (`CertLift`), realigned to the nodes' indices by the
    variable-typing inversion (`hasTyTInv_bvar`). -/
def row_bvarZeta_bvarZeta (Lf : CertLift E n PEq) {Γ : LCtx} {i : Nat}
    {A v v₁ v₂ T₁ T₂ : Expr Nat} (h : Γ.get? i = some (.letBinding A v))
    (hl₁ : HasTyT E n Γ (.bvar i) T₁) (hl₂ : HasTyT E n Γ (.bvar i) T₂)
    (jv : Join E n PEq (Γ.drop (i + 1)) v₁ v₂ A A) :
    Join E n PEq Γ (lift 0 (i + 1) v₁) (lift 0 (i + 1) v₂) T₁ T₂ := by
  obtain ⟨v₃, p₃, q₃⟩ := jv
  have hlt : i < Γ.length := get?_some_lt h
  have hΔ : Γ.take (i + 1) ++ Γ.drop (i + 1) = Γ := List.take_append_drop (i + 1) Γ
  have hlen : (Γ.take (i + 1)).length = i + 1 := by
    rw [List.length_take]; omega
  have s₁ := Lf (Γ.take (i + 1)) p₃
  have s₂ := Lf (Γ.take (i + 1)) q₃
  rw [hΔ, hlen] at s₁ s₂
  have hlk : lookupType Γ i = some (lift 0 (i + 1) A) := by simp only [lookupType, h]
  obtain ⟨A₁', hlk₁, chain₁⟩ := hasTyTInv_bvar hl₁ rfl
  obtain ⟨A₂', hlk₂, chain₂⟩ := hasTyTInv_bvar hl₂ rfl
  rw [hlk] at hlk₁ hlk₂
  have e₁ := Option.some.inj hlk₁
  have e₂ := Option.some.inj hlk₂
  subst e₁
  subst e₂
  exact ⟨lift 0 (i + 1) v₃, s₁.reindex chain₁, s₂.reindex chain₂⟩

/-! ### the per-shape helpers (second step matched against its source equation) -/

/-- Second step against a `sortEq` root. -/
def withSortEq (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {l₁ l₂ : Level} {T₁ : Expr Nat} {h : eqN l₁ l₂}
    {hl : HasTyT E n Γ (.sort l₁) T₁} {hr : HasTyT E n Γ (.sort l₂) T₁}
    (cp : Certified (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .sort l₁ →
    IHBelow E n PEq (sizeOf (ParRedT.sortEq (PEq := PEq) Γ l₁ l₂ T₁ h hl hr) + sizeOf q) →
    Join E n PEq Γ (.sort l₂) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, cq@(@Certified.sortEq _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact row_sortEq_sortEq cp cq
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `consts` root. -/
def withConsts (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls ls' : List Level} {T₁ : Expr Nat} {h : eqNList ls ls'}
    {hl : HasTyT E n Γ (.const r ls) T₁} {hr : HasTyT E n Γ (.const r ls') T₁}
    (cp : Certified (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .const r ls →
    IHBelow E n PEq (sizeOf (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl hr) + sizeOf q) →
    Join E n PEq Γ (.const r ls') e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact row_consts_consts cp cq
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact R.consts_delta hΓ cp cq
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `delta` root. -/
def withDelta (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b T₁ : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b} {htr : transparent m.mclass = true}
    {hlen : ls.length = m.arity} {hwf : levelsBounded n ls = true}
    {hl : HasTyT E n Γ (.const r ls) T₁} {hr : HasTyT E n Γ (instantiateLevels ls b) T₁}
    (cp : Certified (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl hr)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .const r ls →
    IHBelow E n PEq (sizeOf (ParRedT.delta (PEq := PEq) Γ r ls m b T₁ hres hbody htr hlen hwf hl hr) + sizeOf q) →
    Join E n PEq Γ (instantiateLevels ls b) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb
      exact join_swap_indep (R.consts_delta hΓ cq cp)
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact row_delta_delta cp cq
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `bvarZeta` root. -/
def withBvarZeta (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {i : Nat} {A v v₁ T₁ : Expr Nat} {h : Γ.get? i = some (.letBinding A v)}
    {hv : ParRedT PEq E n (Γ.drop (i + 1)) v v₁ A}
    {hl : HasTyT E n Γ (.bvar i) T₁} {hr : HasTyT E n Γ (lift 0 (i + 1) v₁) T₁}
    (cp : Certified (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv hl hr)) (cv : Certified hv) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .bvar i →
    IHBelow E n PEq (sizeOf (ParRedT.bvarZeta (PEq := PEq) Γ i A v v₁ T₁ h hv hl hr) + sizeOf q) →
    Join E n PEq Γ (lift 0 (i + 1) v₁) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, @Certified.bvarZeta _ _ _ _ _ _ _ _ _ h₂ _ hl₂ _ _ cv₂, hb, ih => by
      cases hb
      have e := Option.some.inj (h.symm.trans h₂)
      cases e
      exact row_bvarZeta_bvarZeta Lf h hl hl₂ (ih (ctxWfT_drop hΓ _) cv cv₂ (by simp <;> omega))
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against an `app` root. -/
def withApp (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
    {ha : ParRedT PEq E n Γ a a' A} {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
    (cp : Certified (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr))
    (cf : Certified hf) (ca : Certified ha) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .app f a →
    IHBelow E n PEq (sizeOf (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) + sizeOf q) →
    Join E n PEq Γ (.app f' a') e (instantiate0 a B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, @Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ hf₂ hc₂ hB₂ _ ha₂ _ _ cf₂ ca₂, hb, ih => by
      cases hb
      exact row_app_app hW L hΓ hf hc hB ha ca hf₂ hc₂ hB₂ ha₂ ca₂
        (ih hΓ cf cf₂ (by simp <;> omega)) (ih hΓ ca ca₂ (by simp <;> omega))
  | _, _, _, _, cq@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂ ca₂), hb, ih => by
      cases hb
      exact R.app_beta hΓ cp cq cf ca cb₂ ca₂ ih
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `beta` root. -/
def withBeta (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body body' arg arg' B : Expr Nat} {u v w : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w)}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B} {ha : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)}
    (cp : Certified (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v w hA hB hTy hb ha hred))
    (cb : Certified hb) (ca : Certified ha) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .app (.lam A body) arg →
    IHBelow E n PEq (sizeOf (ParRedT.beta (PEq := PEq) Γ A body body' arg arg' B u v w hA hB hTy hb ha hred) + sizeOf q) →
    Join E n PEq Γ (instantiate0 arg' body') e (instantiate0 arg B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf₂ ca₂), hb, ih => by
      cases hb
      exact join_swap_indep (R.app_beta hΓ cq cp cf₂ ca₂ cb ca (IHBelow.comm ih))
  | _, _, _, _, @Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ hA₂ hB₂ _ _ _ _ _ cb₂ ca₂, hb, ih => by
      cases hb
      exact row_beta_beta L R.subst0 hΓ hA hB ca hA₂ hB₂ ca₂
        (ih (.assumption Γ _ u hΓ hA) cb cb₂ (by simp <;> omega))
        (ih hΓ ca ca₂ (by simp <;> omega))
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `lam` root. -/
def withLam (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' body body' B : Expr Nat} {u v : Level}
    {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hb : ParRedT PEq E n (.assumption A :: Γ) body body' B}
    {hrt : HasTyT E n Γ (.lam A' body') (.pi A B)}
    (cp : Certified (ParRedT.lam (PEq := PEq) Γ A A' body body' B u v hc hA hB hb hrt))
    (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .lam A body →
    IHBelow E n PEq (sizeOf (ParRedT.lam (PEq := PEq) Γ A A' body body' B u v hc hA hB hb hrt) + sizeOf q) →
    Join E n PEq Γ (.lam A' body') e (.pi A B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, @Certified.lam _ _ _ _ _ _ _ _ _ _ _ hc₂ hA₂ hB₂ _ _ _ cb₂, hb, ih => by
      cases hb
      exact row_lam_lam hW L Ac hΓ hc hA hB hc₂ hA₂ hB₂
        (ih (.assumption Γ _ u hΓ hA) cb cb₂ (by simp <;> omega))
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₂), hb, ih => by
      cases hb
      exact R.lam_eta hΓ cp cq cb cf₂ ih

/-- Second step against an `eta` root. -/
def withEta (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f' A B : Expr Nat} {hf : ParRedT PEq E n Γ f f' (.pi A B)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)}
    (cp : Certified (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl)) (cf : Certified hf) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .lam A (.app (lift 0 1 f) (.bvar 0)) →
    IHBelow E n PEq (sizeOf (ParRedT.eta (PEq := PEq) Γ f f' A B hf hl) + sizeOf q) →
    Join E n PEq Γ (f') e (.pi A B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb₂), hb, ih => by
      cases hb
      exact join_swap_indep (R.lam_eta hΓ cq cp cb₂ cf (IHBelow.comm ih))
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, @Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf₂, hb, ih => by
      injection hb with e₁ e₂; injection e₂ with e₃ _
      have e₄ := lift_inj 0 _ _ e₃
      cases e₁; cases e₄
      exact row_eta_eta (ih hΓ cf cf₂ (by simp <;> omega))

/-- Second step against a `pi` root. -/
def withPi (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' B B' : Expr Nat} {u v : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hc : ConvT E n Γ A A' (.sort u)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)}
    {hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v))}
    (cp : Certified (ParRedT.pi (PEq := PEq) Γ A A' B B' u v hA hc hB hcB hrt)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .pi A B →
    IHBelow E n PEq (sizeOf (ParRedT.pi (PEq := PEq) Γ A A' B B' u v hA hc hB hcB hrt) + sizeOf q) →
    Join E n PEq Γ (.pi A' B') e (.sort (.imax u v)) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.pi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact row_pi_pi hW hΓ cp cq
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `letE` root. -/
def withLetE (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' value value' body body' B : Expr Nat} {u w : Level}
    {hc : ConvT E n Γ A A' (.sort u)} {hA : HasTyT E n Γ A (.sort u)}
    {hv : ParRedT PEq E n Γ value value' A}
    {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
    {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
    {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
    {hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)}
    (cp : Certified (ParRedT.letE (PEq := PEq) Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt))
    (cv : Certified hv) (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .letE A value body →
    IHBelow E n PEq (sizeOf (ParRedT.letE (PEq := PEq) Γ A A' value value' body body' B u w hc hA hv hB hTy hb hrt) + sizeOf q) →
    Join E n PEq Γ (.letE A' value' body') e (instantiate0 value B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb, ih => by
      cases hb
      exact R.letE_letE hΓ cp cq cv cb cv₂ cb₂ ih
  | _, _, _, _, cq@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb, ih => by
      cases hb
      exact R.letE_zeta hΓ cp cq cv cb cv₂ cb₂ ih
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `zeta` root. -/
def withZeta (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value value' body body' B : Expr Nat} {u w : Level}
    {hA : HasTyT E n Γ A (.sort u)} {hv : ParRedT PEq E n Γ value value' A}
    {hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w)}
    {hTy : HasTyT E n Γ (instantiate0 value B) (.sort w)}
    {hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B}
    {hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B)}
    (cp : Certified (ParRedT.zeta (PEq := PEq) Γ A value value' body body' B u w hA hv hB hTy hb hred))
    (cv : Certified hv) (cb : Certified hb) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .letE A value body →
    IHBelow E n PEq (sizeOf (ParRedT.zeta (PEq := PEq) Γ A value value' body body' B u w hA hv hB hTy hb hred) + sizeOf q) →
    Join E n PEq Γ (instantiate0 value' body') e (instantiate0 value B) T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb, ih => by
      cases hb
      exact join_swap_indep (R.letE_zeta hΓ cq cp cv₂ cb₂ cv cb (IHBelow.comm ih))
  | _, _, _, _, cq@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv₂ cb₂), hb, ih => by
      cases hb
      exact R.zeta_zeta hΓ cp cq cv cb cv₂ cb₂ ih
  | _, _, _, _, .lit .., hb, _ => nomatch hb
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-- Second step against a `lit` root. -/
def withLit (R : OpenRows E n PEq) (_hW : EnvWfT E) (L : LeafIface E n PEq)
    (_Lf : CertLift E n PEq) (_Ac : CertAssumpCtx E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {t : Nat} {T₁ : Expr Nat} {hexp : HasTyT E n Γ (natExpand t) T₁}
    (cp : Certified (ParRedT.lit (PEq := PEq) Γ t T₁ hexp)) :
    {b' e T₂ : Expr Nat} → {q : ParRedT PEq E n Γ b' e T₂} → Certified q → b' = .lit t →
    IHBelow E n PEq (sizeOf (ParRedT.lit (PEq := PEq) Γ t T₁ hexp) + sizeOf q) →
    Join E n PEq Γ (natExpand t) e T₁ T₂
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_refl_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h' _, hb, _ => by
      subst hb; exact join_swap_indep (join_peq_indep R L hΓ h' ⟨_, cp⟩)
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc' _ ch', hb, ih => by
      subst hb
      obtain ⟨f, p', q'⟩ := ih hΓ cp ch' (by simp <;> omega)
      exact ⟨f, p', q'.reindex hc'⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, hb, ih => by
      subst hb
      exact join_swap_indep (join_iotaSpine_left R L hΓ hI
        (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (join_swap_indep (ih hΓ cp cs (by simp <;> omega))))
  | _, _, _, _, .sortEq .., hb, _ => nomatch hb
  | _, _, _, _, .consts .., hb, _ => nomatch hb
  | _, _, _, _, .bvarZeta .., hb, _ => nomatch hb
  | _, _, _, _, .delta .., hb, _ => nomatch hb
  | _, _, _, _, .app .., hb, _ => nomatch hb
  | _, _, _, _, .beta .., hb, _ => nomatch hb
  | _, _, _, _, .lam .., hb, _ => nomatch hb
  | _, _, _, _, .pi .., hb, _ => nomatch hb
  | _, _, _, _, .letE .., hb, _ => nomatch hb
  | _, _, _, _, .zeta .., hb, _ => nomatch hb
  | _, _, _, _, cq@(@Certified.lit _ _ _ _ _ _ _ _), hb, _ => by
      cases hb; exact row_lit_lit cp cq
  | _, _, _, _, .eta .., hb, _ => nomatch hb

/-! ### the assembler -/

/-- The independent-index certified diamond, assembled from the rows: recursion on
    `sizeOf p + sizeOf q`, the first step's root matched through its certificate, the second
    step dispatched by the per-shape helpers. -/
def assemble (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lf : CertLift E n PEq) (Ac : CertAssumpCtx E n PEq) :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) → {b d e T₁ T₂ : Expr Nat} →
    {p : ParRedT PEq E n Γ b d T₁} → Certified p → {q : ParRedT PEq E n Γ b e T₂} →
    Certified q → Join E n PEq Γ d e T₁ T₂
  | _, hΓ, _, _, _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ hc _ ch, _, cq =>
      let ⟨f, p', q'⟩ := assemble R hW L Lf Ac hΓ ch cq
      ⟨f, p'.reindex hc, q'⟩
  | _, hΓ, _, _, _, _, _, _, @Certified.refl _ _ _ _ _ _ h _, _, cq =>
      join_refl_indep R L hΓ h ⟨_, cq⟩
  | _, hΓ, _, _, _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, _, cq =>
      join_peq_indep R L hΓ h ⟨_, cq⟩
  | _, hΓ, _, _, _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ hrhs c cs, _, cq =>
      join_iotaSpine_left R L hΓ hI (.trans _ _ _ _ _ (.symm _ _ _ _ cs.root) c) hrhs
        (assemble R hW L Lf Ac hΓ cs cq)
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.sortEq _ _ _ _ _ _ _ _ _ _ _), _, cq =>
      withSortEq R hW L Lf Ac hΓ cp cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.consts _ _ _ _ _ _ _ _ _ _ _ _), _, cq =>
      withConsts R hW L Lf Ac hΓ cp cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.bvarZeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv), _, cq =>
      withBvarZeta R hW L Lf Ac hΓ cp cv cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, cq =>
      withDelta R hW L Lf Ac hΓ cp cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf ca),
      _, cq =>
      withApp R hW L Lf Ac hΓ cp cf ca cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb ca),
      _, cq =>
      withBeta R hW L Lf Ac hΓ cp cb ca cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cb), _, cq =>
      withLam R hW L Lf Ac hΓ cp cb cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.pi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, cq =>
      withPi R hW L Lf Ac hΓ cp cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _,
      cp@(@Certified.letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv cb), _, cq =>
      withLetE R hW L Lf Ac hΓ cp cv cb cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _,
      cp@(@Certified.zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cv cb), _, cq =>
      withZeta R hW L Lf Ac hΓ cp cv cb cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.lit _ _ _ _ _ _ _ _), _, cq =>
      withLit R hW L Lf Ac hΓ cp cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
  | _, hΓ, _, _, _, _, _, _, cp@(@Certified.eta _ _ _ _ _ _ _ _ _ _ _ cf), _, cq =>
      withEta R hW L Lf Ac hΓ cp cf cq rfl
        (fun {_} hΓ' {_ _ _ _ _} {_} cp' {_} cq' _ => assemble R hW L Lf Ac hΓ' cp' cq')
termination_by _ _ _ _ _ _ _ p _ q _ => sizeOf p + sizeOf q
decreasing_by all_goals (first | assumption | (simp_wf; assumption) | (simp <;> omega) | (simp_wf; simp <;> omega))

/-! ### the chain closed -/

/-- `CoreDiamond` from the rows. -/
def coreDiamond_of_rows (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lf : CertLift E n PEq) (Ac : CertAssumpCtx E n PEq) : CoreDiamond E n PEq :=
  fun {_} hΓ {_ _ _ _ _} _ cp _ _ cq _ => assemble R hW L Lf Ac hΓ cp cq

/-- `CDiamond` from the rows (the same-index case of the assembler). -/
def cdiamond_of_rows (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lf : CertLift E n PEq) (Ac : CertAssumpCtx E n PEq) : CDiamond E n PEq :=
  fun {_} hΓ {_ _ _ _} p q => assemble R hW L Lf Ac hΓ p.cert q.cert

/-- The valley producer from the rows and the `let` row. -/
def valleyOf_rows (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (Lf : CertLift E n PEq) (Ac : CertAssumpCtx E n PEq) (Lt : LetValley E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf hW L (cdiamond_of_rows R hW L Lf Ac) Lt hΓ c

/-- The spec's §5.5 shape from the rows, the `let` row, and the two landed-front transports
    (`certLift_of`, `certAssumpCtx_of`). -/
theorem nativeConvValleys_of_rows (R : OpenRows E n PEq) (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        F8EtaK.AssumpCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (Lt : LetValley E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  (valleyOf_rows R hW L (certLift_of (PEq := PEq) (envClosed_of_envWfT hW) hPEqL)
    (certAssumpCtx_of (PEq := PEq) (envClosed_of_envWfT hW) (fun hcc hp => hPEqC hcc hp))
    Lt hΓ c).exists_join

end Rcic.Declarative.NativeValleys
