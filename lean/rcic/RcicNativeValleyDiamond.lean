import rcic.RcicNativeValleyOf

/-!
# RcicNativeValleyDiamond — the diamond oracle reduced to its structural core
(Wall 1, `NativeConvValleys`, piece 3: `refl`, `peq`, `conv` rows; the core diamond)

`CDiamond` (`RcicNativeValleyCert`) asks for the one-step join of two certified steps out of the
same term at the same index. Three of the eighteen `ParRedT` constructors are not about the
term at all and are discharged here once and for all:

* `conv` (the index mover) is peeled from both sides (`peel`): a step is a core step at its own
  index plus a `TyConvT` chain, and the outputs are moved back along the chains. The two cores
  may therefore sit at DIFFERENT indices — the core oracle `CoreDiamond` is stated with
  independent indices, each output certified at its own index. (This is where a certificate
  "composed from the inputs" would need type uniqueness; the core rows instead build each
  output certificate from the children's, see the status document.)
* `refl`: the other step is its own join.
* `peq`: the leaf's type is `Prop`-sorted (`LeafIface.prop`), so the other step's target is one
  irrelevance leaf away from the leaf's target (`CStep.irr`); this needs the other step's
  target typed at the leaf's index, which the peeled chain supplies.

What remains is `CoreDiamond`: pairs of steps whose roots are among the fifteen structural
constructors (`isCore`), at independent indices. Its rows are classified in
`research/rcic/sortrow/NATIVE_VALLEYS_STATUS.md`; none is assumed here.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### the root classification -/

/-- The fifteen structural constructors: everything but `refl`, `peq` and `conv`. -/
def isCore {Γ : LCtx} {a b T : Expr Nat} : ParRedT PEq E n Γ a b T → Bool
  | .refl .. => false
  | .peq .. => false
  | .conv .. => false
  | _ => true

/-- A step with no `conv` at the root, classified: reflexive, a leaf, or core. -/
inductive Peeled : {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T → Type
  | refl {Γ : LCtx} {a A : Expr Nat} (h : HasTyT E n Γ a A) : Peeled (.refl Γ a A h)
  | peq {Γ : LCtx} {p q T : Expr Nat} (h : PEq Γ p q T) : Peeled (.peq Γ p q T h)
  | core {Γ : LCtx} {a b T : Expr Nat} (p : ParRedT PEq E n Γ a b T) (hp : isCore p = true) :
      Peeled p

/-- Peel the `conv` nodes off the root of a certified step: a classified core step at its own
    index, its certificate, and the chain back to the original index. The two K roots have
    no certificate (`Certified.noK`): those arms are vacuous. -/
def peel : {Γ : LCtx} → {a b T : Expr Nat} → (p : ParRedT PEq E n Γ a b T) → Certified p →
    Σ' (T₀ : Expr Nat) (p₀ : ParRedT PEq E n Γ a b T₀),
      Certified p₀ ×' Peeled p₀ ×' TyConvT E n Γ T₀ T
  | Γ, _, _, _, .conv _ _ _ _ _ h hc, .conv _ ch =>
      let ⟨T₀, p₀, c₀, v₀, chain⟩ := peel h ch
      ⟨T₀, p₀, c₀, v₀, .trans Γ _ _ _ chain hc⟩
  | Γ, _, _, _, .refl _ _ A h, c => ⟨A, _, c, .refl h, .refl Γ A⟩
  | Γ, _, _, _, .peq _ _ _ T h, c => ⟨T, _, c, .peq h, .refl Γ T⟩
  | Γ, _, _, _, .sortEq .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .consts .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .bvarZeta .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .delta .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .app .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .beta .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .lam .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .pi .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .letE .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .zeta .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .iotaSpine .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | _, _, _, _, .iotaStarK .., c => (Certified.noK c).elim
  | _, _, _, _, .iotaStarKEta .., c => (Certified.noKEta c).elim
  | Γ, _, _, _, .lit .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩
  | Γ, _, _, _, .eta .., c => ⟨_, _, c, .core _ rfl, .refl Γ _⟩

/-! ### the core oracle -/

/-- The diamond on two CORE certified steps out of the same term, at INDEPENDENT indices, each
    output certified at its own input's index. The remaining oracle after this module. -/
def CoreDiamond (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b d e T₁ T₂ : Expr Nat}
    (p : ParRedT PEq E n Γ b d T₁), Certified p → isCore p = true →
    (q : ParRedT PEq E n Γ b e T₂) → Certified q → isCore q = true →
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂

/-! ### the generic rows -/

/-- `refl` against anything: the other step is the join. -/
def join_refl_left (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (q : CStep E n PEq Γ b e T) :
    Σ' (f : Expr Nat), CStep E n PEq Γ b f T ×' CStep E n PEq Γ e f T :=
  ⟨e, q, ⟨.refl Γ e T (q.rightTyped L hΓ), .refl (.refl Γ e T (q.rightTyped L hΓ))⟩⟩

/-- A `peq` leaf `b → d` at `T₁` against any certified step `b → e` at `T`: the join is `e`,
    reached from `d` by one irrelevance leaf at the leaf's index (`T₁ : Prop`), moved to `T`
    along the peeled chain; `e` is typed at `T₁` through the chain. -/
def join_peq_left (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T₁ T : Expr Nat} (h : PEq Γ b d T₁) (chain : TyConvT E n Γ T₁ T)
    (q : CStep E n PEq Γ b e T) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T ×' CStep E n PEq Γ e f T :=
  let he : HasTyT E n Γ e T₁ := hasTyT_of_tyConvT (q.rightTyped L hΓ) chain.symmT
  ⟨e, (CStep.irr L (L.prop h) (L.typed h).2 he).reindex chain,
    ⟨.refl Γ e T (q.rightTyped L hΓ), .refl (.refl Γ e T (q.rightTyped L hΓ))⟩⟩

/-- Swap the two legs of a join. -/
def join_swap {Γ : LCtx} {d e T : Expr Nat}
    (j : Σ' (f : Expr Nat), CStep E n PEq Γ d f T ×' CStep E n PEq Γ e f T) :
    Σ' (f : Expr Nat), CStep E n PEq Γ e f T ×' CStep E n PEq Γ d f T :=
  ⟨j.1, j.2.2, j.2.1⟩

/-! ### the assembly -/

/-- Join two peeled steps: `refl` and `peq` roots generically, two core roots through the core
    oracle at their own indices, the outputs moved back along the chains. (The classifications
    come first so that the dependent arguments are refined with them.) -/
def joinPeeled (C : CoreDiamond E n PEq) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b T : Expr Nat} :
    {d T₁ : Expr Nat} → {p₀ : ParRedT PEq E n Γ b d T₁} → Peeled p₀ →
    CStep E n PEq Γ b d T → Certified p₀ → TyConvT E n Γ T₁ T →
    {e T₂ : Expr Nat} → {q₀ : ParRedT PEq E n Γ b e T₂} → Peeled q₀ →
    CStep E n PEq Γ b e T → Certified q₀ → TyConvT E n Γ T₂ T →
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T ×' CStep E n PEq Γ e f T
  | _, _, _, .refl _, _, _, _, _, _, _, _, q, _, _ => join_refl_left L hΓ q
  | _, _, _, _, p, _, _, _, _, _, .refl _, _, _, _ => join_swap (join_refl_left L hΓ p)
  | _, _, _, .peq h, _, _, chain₁, _, _, _, _, q, _, _ => join_peq_left L hΓ h chain₁ q
  | _, _, _, _, p, _, _, _, _, _, .peq h, _, _, chain₂ => join_swap (join_peq_left L hΓ h chain₂ p)
  | _, _, _, .core p₀ hp, _, cp, chain₁, _, _, _, .core q₀ hq, _, cq, chain₂ =>
      let ⟨f, p', q'⟩ := C hΓ p₀ cp hp q₀ cq hq
      ⟨f, p'.reindex chain₁, q'.reindex chain₂⟩

/-- The same-index diamond from the core diamond: peel the index movers off both roots and
    join the peeled steps. -/
def cdiamond_of_core (C : CoreDiamond E n PEq) (L : LeafIface E n PEq) : CDiamond E n PEq :=
  fun {_} hΓ {_ _ _ _} p q =>
    let ⟨_, _, cp, v₁, chain₁⟩ := peel p.step p.cert
    let ⟨_, _, cq, v₂, chain₂⟩ := peel q.step q.cert
    joinPeeled C L hΓ v₁ p cp chain₁ v₂ q cq chain₂

/-- The valley producer, now from the CORE diamond and the `let` row. -/
def valleyOf_core (hW : EnvWfT E) (L : LeafIface E n PEq) (C : CoreDiamond E n PEq)
    (Lt : LetValley E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf hW L (cdiamond_of_core C L) Lt hΓ c

/-- The spec's §5.5 shape from the core diamond and the `let` row. -/
theorem nativeConvValleys_of_core (hW : EnvWfT E) (L : LeafIface E n PEq)
    (C : CoreDiamond E n PEq) (Lt : LetValley E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  nativeConvValleys_of hW L (cdiamond_of_core C L) Lt hΓ c

end Rcic.Declarative.NativeValleys
