import rcic.RcicNativeValleyAssemble

/-!
# RcicNativeValleyFronts — the exact statements the remaining rows reduce to
(Wall 1, `NativeConvValleys`, piece 10)

Each of the `OpenRows` fields that session 7 does not close outright is reduced, in the
following modules, to one or more of the fronts below — each a `Type` with its exact
statement, none equivalent to a diamond row, none assumed. `RcicNativeValleyOpenRows`
assembles the `OpenRows` record from them.

* `Retype` — `OpenRows.retype` itself (the only index obligation of the assembler,
  `NATIVE_VALLEYS_STATUS.md` §2b). Several rows re-present a certified step out of a term at
  the term's OTHER type; that is this front, never a new one.
* `PropAlign` — two types of one term are `Prop`-sorted together. Where it enters: an
  irrelevance leaf inside one input (`peq` sub-cases of `app × beta`, `lam × eta`, the spine
  prefix of an ι redex) makes the OTHER input's index a `Prop` only up to this transfer. It is
  uniqueness-shaped like `Retype` (same-term, two types) and is NOT derivable from `Retype`
  (a retyped step says nothing about the sort of its index).
* `IotaDetU` — determinism of the union ι relation. The legacy arm is landed (`iotaDet`,
  `RcicIota.lean`); across the two arms (`.ofU` / `.ofUS`) it is not.
* `IotaRefireT` — the classical content of the ι row: after a certified `app`-congruence
  step at an ι redex, ι re-fires at the stepped redex and the original reduct steps to the new
  one in one certified step, or (a leaf in the spine) the new redex IS the join. The erased
  engine is `parRed_iotaRhs_congr_total` (`RcicParRedDiamond.lean`); the typed, certified
  form needs the reduct's spine typing (the ι subject-reduction machinery).
* `PiPropCodom` — a `Prop`-sorted Π has a `Prop`-sorted codomain (the shape of
  `pi_zero_inv0`, #7519, there under zero-sort coherence). Where it enters: the `peq`
  sub-case of `app × beta` — the λ is a proof of `T₀ : Prop`, `T₀ ~ Π A' B'`, and the join by
  irrelevance needs `B'[arg] : Prop`.
* `AppBetaEta`, `AppBetaIota` — the two sub-cases of `app × beta` in which the function child
  does NOT stay a λ: it η-contracts (`eta`), or steps and then ι-contracts (`iotaSpine`; a λ
  reaches an ι redex only through η). Both are the η/β interaction of the typed relation: the
  η side needs a step out of `lift 0 1 f` read back as a step out of `f` (strengthening — not
  landed: `RcicTypedStrengthen` is the predicate layer of `[rcic_cres_wall_strengthening]`)
  together with a size bound usable by the assembler's measure. Each is stated with the exact
  node data and the induction hypothesis at the pair's bound.
* `LamEtaApp`, `LamEtaBeta`, `LamEtaIota` — the three roots of the η-expansion's body step
  that `lam × eta` does not close (`app`: strengthening of a step out of `lift 0 1 f`; `beta`:
  `f` lifted is a λ; `iotaSpine`), over the common data `LamEtaCtx`.
* `LetJoin`, `CertLetAnnCtx` — the `let` rows: the diamond across STEPPED bindings (the
  `ParRedT` form of Wall 2's letRight bridge, `NATIVE_VALLEYS_STATUS.md` §4) and the certified
  transport across a converted let annotation (value fixed; provable by the `RcicNativeValleyCtx`
  recursion over a relation extended by the annotation case).

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

/-- (R) `OpenRows.retype` as a front: a certified step out of `b` at `T₂`, presented at
    another type `T₁` of `b`. -/
def Retype (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b e T₁ T₂ : Expr Nat},
    HasTyT E n Γ b T₁ → CStep E n PEq Γ b e T₂ → CStep E n PEq Γ b e T₁

/-- (P) two types of one term are `Prop`-sorted together. -/
def PropAlign (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e T₁ T₂ : Expr Nat},
    HasTyT E n Γ e T₁ → HasTyT E n Γ e T₂ → HasTyT E n Γ T₁ (.sort .zero) →
    HasTyT E n Γ T₂ (.sort .zero)

/-- (ι-det) the union ι relation is a partial function of its redex. -/
def IotaDetU (E : ResolvedEnv) : Prop :=
  ∀ {l r₁ r₂ : Expr Nat}, DerivedIotaU E l r₁ → DerivedIotaU E l r₂ → r₁ = r₂

/-- The legacy arm of `IotaDetU` is landed: `iotaDet` (`RcicIota.lean`). -/
theorem iotaDetU_ofU {E : ResolvedEnv} (w₁ w₂ : IotaWitness E)
    (h : iotaLhsOf w₁ = iotaLhsOf w₂) : iotaRhsOf w₁ = iotaRhsOf w₂ :=
  iotaDet (DerivedIota.of w₁) (by rw [h]; exact DerivedIota.of w₂)

/-- (ι-refire) the classical ι row at an `app`-congruence root: `app f a →ι rhs` (certificate
    supplied) and a certified `app f a ⇒ app f' a'` at the redex's own index give `j` with
    `rhs ⇒ j` there and either `app f' a' →ι j` or `j = app f' a'`. -/
def IotaRefireT (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    {hf : ParRedT PEq E n Γ f f' T₀} {hc : TyConvT E n Γ T₀ (.pi A B)}
    {hB : HasTyT E n (.assumption A :: Γ) B (.sort v)}
    {hTy : HasTyT E n Γ (instantiate0 a B) (.sort w)}
    {ha : ParRedT PEq E n Γ a a' A} {hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)}
    {rhs : Expr Nat},
    DerivedIotaU E (.app f a) rhs → ConvT E n Γ (.app f a) rhs (instantiate0 a B) →
    Certified (ParRedT.app (PEq := PEq) Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr) →
    Certified hf → Certified ha → HasTyT E n Γ rhs (instantiate0 a B) →
    Σ' (j : Expr Nat), CStep E n PEq Γ rhs j (instantiate0 a B) ×'
      (DerivedIotaU E (.app f' a') j ⊕' j = .app f' a')

/-- (Π-Prop) a `Prop`-sorted Π has a `Prop`-sorted codomain. -/
def PiPropCodom (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat},
    HasTyT E n Γ (.pi A B) (.sort .zero) → HasTyT E n (.assumption A :: Γ) B (.sort .zero)

set_option linter.unusedVariables false in
/-- (β/η) `app × beta` when the function child η-contracts: `lam A (app (lift f₀) (bvar 0)) ⇒ f'`
    by `eta` (`f₀ ⇒ f'` at `Π A B₀`), the app node's index chain `hc`, the beta node's data on
    the same η-expansion body; the induction hypothesis at a bound dominating the four
    sub-steps. -/
def AppBetaEta (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A f₀ f' B₀ arg a' A' B' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    {hf₀ : ParRedT PEq E n Γ f₀ f' (.pi A B₀)}
    {hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f₀) (.bvar 0))) (.pi A B₀)}
    (hc : TyConvT E n Γ (.pi A B₀) (.pi A' B'))
    (hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'}
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B'))
    {hA : HasTyT E n Γ A (.sort u)} {hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v')}
    {hTy₂ : HasTyT E n Γ (instantiate0 arg B) (.sort w')}
    {hb : ParRedT PEq E n (.assumption A :: Γ) (.app (lift 0 1 f₀) (.bvar 0)) body' B}
    {ha₂ : ParRedT PEq E n Γ arg arg' A}
    {hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)},
    Certified (ParRedT.eta (PEq := PEq) Γ f₀ f' A B₀ hf₀ hl) → Certified hf₀ → Certified ha →
    Certified (ParRedT.beta (PEq := PEq) Γ A (.app (lift 0 1 f₀) (.bvar 0)) body' arg arg' B u v'
      w' hA hB₂ hTy₂ hb ha₂ hred) →
    Certified hb → Certified ha₂ →
    HasTyT E n Γ (.app (.lam A (.app (lift 0 1 f₀) (.bvar 0))) arg) (instantiate0 arg B') →
    (m : Nat) → IHBelow E n PEq m →
    sizeOf (ParRedT.eta (PEq := PEq) Γ f₀ f' A B₀ hf₀ hl) + sizeOf ha + sizeOf hb + sizeOf ha₂ <
      m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B)

set_option linter.unusedVariables false in
/-- (β/ι) `app × beta` when the function child steps and then ι-contracts:
    `lam A body ⇒ lhs' →ι f'` (`iotaSpine`), the app node's index chain `hc`, the beta node's
    data; the induction hypothesis at a bound dominating the inner step and the three other
    sub-steps. -/
def AppBetaIota (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A body lhs' f' T₀ arg a' A' B' body' arg' B : Expr Nat}
    {v w u v' w' : Level}
    {hstep : ParRedT PEq E n Γ (.lam A body) lhs' T₀} {hI : DerivedIotaU E lhs' f'}
    {hred₀ : HasTyT E n Γ lhs' T₀} {hrhs : HasTyT E n Γ f' T₀}
    (hc : TyConvT E n Γ T₀ (.pi A' B'))
    (hB : HasTyT E n (.assumption A' :: Γ) B' (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 arg B') (.sort w))
    {ha : ParRedT PEq E n Γ arg a' A'}
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 arg B'))
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
    HasTyT E n Γ (.app (.lam A body) arg) (instantiate0 arg B') →
    (m : Nat) → IHBelow E n PEq m →
    sizeOf (ParRedT.iotaSpine (PEq := PEq) Γ (.lam A body) lhs' f' T₀ hstep hI hred₀ hrhs) +
      sizeOf ha + sizeOf hb + sizeOf ha₂ < m →
    Join E n PEq Γ (.app f' a') (instantiate0 arg' body') (instantiate0 arg B')
      (instantiate0 arg B)

set_option linter.unusedVariables false in
/-- (let-join) the `let` diamond: two certified body steps under the SOURCE binding and two
    certified value steps join by certified steps whose body legs live under the two STEPPED
    bindings — the typed counterpart of MetaCoq's `pred1 Γ Γ'` shape, Wall 2's letRight
    continuation over `ParRedT` (`LETBRIDGE_STATUS.md`); the induction hypothesis at a bound
    dominating the four sub-steps. -/
def LetJoin (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A value value₁ value₂ body body₁ body₂ B₁ B₂ : Expr Nat}
    {u : Level}, HasTyT E n Γ A (.sort u) → HasTyT E n Γ value A →
    ∀ {hv₁ : ParRedT PEq E n Γ value value₁ A}, Certified hv₁ →
    ∀ {hv₂ : ParRedT PEq E n Γ value value₂ A}, Certified hv₂ →
    ∀ {hb₁ : ParRedT PEq E n (.letBinding A value :: Γ) body body₁ B₁}, Certified hb₁ →
    ∀ {hb₂ : ParRedT PEq E n (.letBinding A value :: Γ) body body₂ B₂}, Certified hb₂ →
    (m : Nat) → IHBelow E n PEq m → sizeOf hv₁ + sizeOf hv₂ + sizeOf hb₁ + sizeOf hb₂ < m →
    Σ' (v₃ b₃ : Expr Nat), CStep E n PEq Γ value₁ v₃ A ×' CStep E n PEq Γ value₂ v₃ A ×'
      CStep E n PEq (.letBinding A value₁ :: Γ) body₁ b₃ B₁ ×'
      CStep E n PEq (.letBinding A value₂ :: Γ) body₂ b₃ B₂

/-- (let-ann) certified transport across a converted let ANNOTATION, the stored value fixed
    (the `let` twin of `CertAssumpCtx`; a converted VALUE is not transportable — `bvarZeta`
    reads it — which is exactly why `LetJoin` is a separate front). -/
def CertLetAnnCtx (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} {A A' v : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → HasTyT E n Γ A' (.sort u) → ConvT E n Γ A A' (.sort u) →
    HasTyT E n Γ v A →
    ∀ {a b T : Expr Nat}, CStep E n PEq (.letBinding A v :: Γ) a b T →
      CStep E n PEq (.letBinding A' v :: Γ) a b T

/-! ### the `lam × eta` row's common data and its three open roots -/

/-- The data of a `lam × eta` pair (`OpenRows.lam_eta`): the λ node's domain conversion and
    typings, its right endpoint typing `hrt`, the η node's function step `hf` with certificate,
    the η-expansion's typing `hl`, and the λ node itself as a certified step `p0`. -/
structure LamEtaCtx (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (Γ : LCtx)
    (A A' f f' body' B₁ B₂ : Expr Nat) (u v : Level) : Type where
  hΓ : CtxWfT E n Γ
  hc : ConvT E n Γ A A' (.sort u)
  hA : HasTyT E n Γ A (.sort u)
  hB : HasTyT E n (.assumption A :: Γ) B₁ (.sort v)
  hrt : HasTyT E n Γ (.lam A' body') (.pi A B₁)
  hf : ParRedT PEq E n Γ f f' (.pi A B₂)
  cf : Certified hf
  hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B₂)
  p0 : CStep E n PEq Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam A' body') (.pi A B₁)

set_option linter.unusedVariables false in
/-- (η/app) `lam × eta` when the η-expansion's body steps by `app` congruence
    (`lift 0 1 f ⇒ g`, `bvar 0 ⇒ x`): the step out of `lift 0 1 f` must be read back as a step
    out of `f` (strengthening) and the η re-fired at the converted annotation. -/
def LamEtaApp (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} {A A' f f' g x B₁ B₂ A₀ Bg T₀ : Expr Nat} {u v v₀ w₀ : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' (.app g x) B₁ B₂ u v)
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
    (m : Nat) → IHBelow E n PEq m →
    sizeOf (ParRedT.app (PEq := PEq) (.assumption A :: Γ) (lift 0 1 f) g (.bvar 0) x A₀ Bg T₀
      v₀ w₀ hg hcg hBg hTyg hx hr) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' (.app g x)) f' (.pi A B₁) (.pi A B₂)

set_option linter.unusedVariables false in
/-- (η/β) `lam × eta` when the η-expansion's body β-contracts (`lift 0 1 f` is itself a λ). -/
def LamEtaBeta (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} {A A' f f' A₀ b₀ b₀' x B₀' B₁ B₂ : Expr Nat} {u v u₀ v₀ w₀ : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' (instantiate0 x b₀') B₁ B₂ u v)
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
    (m : Nat) → IHBelow E n PEq m →
    sizeOf (ParRedT.beta (PEq := PEq) (.assumption A :: Γ) A₀ b₀ b₀' (.bvar 0) x B₀' u₀ v₀ w₀
      hA₀ hB₀' hTy₀ hb₀ hx hred₀) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' (instantiate0 x b₀')) f' (.pi A B₁) (.pi A B₂)

set_option linter.unusedVariables false in
/-- (η/ι) `lam × eta` when the η-expansion's body steps and then ι-contracts. -/
def LamEtaIota (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx} {A A' f f' lhs' rhs T₀ B₁ B₂ : Expr Nat} {u v : Level}
    (D : LamEtaCtx E n PEq Γ A A' f f' rhs B₁ B₂ u v)
    {hstep : ParRedT PEq E n (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0)) lhs' T₀}
    {hI : DerivedIotaU E lhs' rhs} {hred₀ : HasTyT E n (.assumption A :: Γ) lhs' T₀}
    {hrhs : HasTyT E n (.assumption A :: Γ) rhs T₀},
    Certified (ParRedT.iotaSpine (PEq := PEq) (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      lhs' rhs T₀ hstep hI hred₀ hrhs) →
    Certified hstep → TyConvT E n (.assumption A :: Γ) T₀ B₁ →
    (m : Nat) → IHBelow E n PEq m →
    sizeOf (ParRedT.iotaSpine (PEq := PEq) (.assumption A :: Γ) (.app (lift 0 1 f) (.bvar 0))
      lhs' rhs T₀ hstep hI hred₀ hrhs) + sizeOf D.hf < m →
    Join E n PEq Γ (.lam A' rhs) f' (.pi A B₁) (.pi A B₂)

end Rcic.Declarative.NativeValleys
