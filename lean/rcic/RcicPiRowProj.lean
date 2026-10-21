import rcic.RcicF8StructPiRequests
import rcic.RcicCtxConvT
import rcic.RcicTypedRowsWf
import rcic.RcicDerivedIotaU
import rcic.RcicParRedT
import rcic.RcicDT0709EnvWf
import rcic.RcicTypedWeaken
import rcic.RcicNormalizingFalsePinLoop

/-!
# Native Π projection (the piRow wall, piece B) — spec
`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §5.

* `binderTransport` — §5.1: move a `TyConvT` codomain chain from under
  `A'`'s binder to under `A`'s binder, given `TyConvT A A'`. The `of`
  clause collapses the domain conversion's endpoints via DT-009
  (`convT_endpoints`) and transports through `CtxConvT.assumption` +
  `F8EtaK.tyConvT_ctx`; `trans` walks back through the right chain
  then the left.
* `PiCompRow`, `piCompRow_refl/symm/trans` — §5.1: the weak-row algebra,
  codomain under the LEFT binder by convention.
* `ProofLeaf`, `PiStep`, `PiStar` — §5.2: the proof-only leaf as data
  (`hT : T : sort 0`, `hp : p : T`, `hq : q : T`), and typed `ParRedT`/
  `ParRedTStar` instantiated at it. All 18 `ParRedT` constructors are
  retained; `peq` consumes `ProofLeaf` via `ConvT.irr`-shaped evidence.
* `piStep_project` — §5.3: exhaustive one-step Π-source projection.
  `refl` gives two raw reflexivities; `pi` gives the domain/codomain
  `ConvT`s through `TyConvT.of`; `conv` recurses on the original
  parallel child; `iotaSpine` recurses on the first step and
  contradicts the intermediate Π shape via `foldApps_snoc_ne_pi`;
  `peq`/`ProofLeaf` is refuted by `SP1.piProofRoot_false`; every other
  constructor's source shape excludes Π. Recursive calls only on
  `conv.h` and `iotaSpine.hstep`.
* `piStar_project`, `NativeValley`, `valley_piCompRow` — §5.4: star
  projection inducts on `ParRedTStar`; a valley is a centre plus left
  and right star paths; a valley between Π types yields the row by
  projecting both paths and composing with a reversed right row.
* `NativeConvValleys`, `weak_piRow_of_nativeValleys` — §5.5: the
  remaining supplier gap is `NativeConvValleys` — an explicit `Prop`
  (every `ConvT` in a well-formed context has a native valley). It is
  NOT assumed as an axiom and NOT proved here: `weak_piRow_of_`-
  `nativeValleys` is conditional on it. Given it, `TyConvT.firstOf`
  gives raw reflexivities when the Π's are syntactically equal, else
  DT-009 sorts the first native edge,
  `convT_of_tyConvT_sort_of_sortUniq` collapses the chain, and valley
  projection finishes.
* `pinLoopX`, `pinLoopX_step`, `pinLoopX_chain`, `pinLoopX_conv`,
  `pinLoop_finite_components` — §5.6: the Loop fixture. `convT_pinLoop`
  is the real equation `X ≡ X → X : Prop` at `pinLoopEraseWfT`'s
  environment; `Xₖ₊₁ := Π(Xₖ, lift Xₖ)` unfolds homogeneously: the step
  is `ConvT.pi` on the previous step and its `convTWeaken`, retyped
  through `eqN_imax00`. This is a statement about FINITE unfoldings of
  the concrete Loop `X` — it does not establish safety for every
  Loop-like group.

`closure_claim = 0`: the `NativeConvValleys` supplier stays an explicit
hypothesis; nothing here claims the row unconditionally.
-/

namespace Rcic.Declarative

open Ann

variable {E : ResolvedEnv} {n : Nat}

/-! ## §5.1 — binder transport and the row algebra -/

/-- move a codomain chain from under the RIGHT domain's binder to under
the LEFT domain's binder. `of`: DT-009 types both domain endpoints at
`sort u`, `CtxConvT.assumption` swaps the two typed binders with the
symmetric conversion, `tyConvT_ctx` transports. `trans`: back through
the right half of the chain, then the left. -/
def binderTransport (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {B B' : Expr Nat} :
    {A A' : Expr Nat} → TyConvT E n Γ A A' →
      TyConvT E n (.assumption A' :: Γ) B B' →
      Nonempty (TyConvT E n (.assumption A :: Γ) B B')
  | _, _, .refl _ _, h => ⟨h⟩
  | _, _, .of _ _ _ u hc, h => by
      obtain ⟨⟨hA⟩, ⟨hA'⟩⟩ := convT_endpoints hW hΓ hc
      exact ⟨F8EtaK.tyConvT_ctx (envClosed_of_envWfT hW)
        (.assumption (ctxConvT_refl Γ) hA' hA (.symm _ _ _ _ hc)) h⟩
  | _, _, .trans _ _ _ _ d₁ d₂, h => by
      obtain ⟨h₂⟩ := binderTransport hW hΓ d₂ h
      exact binderTransport hW hΓ d₁ h₂

/-- the weak Π row: domain conversion at `Γ`, codomain conversion under
the LEFT binder's context. -/
abbrev PiCompRow (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A B A' B' : Expr Nat) : Prop :=
  Nonempty (TyConvT E n Γ A A') ∧
    Nonempty (TyConvT E n (.assumption A :: Γ) B B')

def piCompRow_refl {Γ : LCtx} {A B : Expr Nat} : PiCompRow E n Γ A B A B :=
  ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩

def piCompRow_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (r : PiCompRow E n Γ A B A' B') :
    PiCompRow E n Γ A' B' A B := by
  obtain ⟨⟨d⟩, ⟨c⟩⟩ := r
  refine ⟨⟨d.symmT⟩, ?_⟩
  exact binderTransport hW hΓ d.symmT c.symmT

/-- transitivity: the second row's codomain chain lives under `A'`, so
it is transported under `A` through the first row's domain chain before
composing — the left-binder convention. -/
def piCompRow_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' A'' B'' : Expr Nat}
    (r₁ : PiCompRow E n Γ A B A' B') (r₂ : PiCompRow E n Γ A' B' A'' B'') :
    PiCompRow E n Γ A B A'' B'' := by
  obtain ⟨⟨d₁⟩, ⟨c₁⟩⟩ := r₁; obtain ⟨⟨d₂⟩, ⟨c₂⟩⟩ := r₂
  refine ⟨⟨.trans _ _ _ _ d₁ d₂⟩, ?_⟩
  obtain ⟨c₂'⟩ := binderTransport hW hΓ d₁ c₂
  exact ⟨.trans _ _ _ _ c₁ c₂'⟩

/-! ## §5.2 — the proof-only leaf and the typed step/star -/

/-- the `PEq` stub realized: a loose proof leaf — `p q : T` both typed,
`T` a `Prop` — the `ConvT.irr` shape as data. `Type`-valued: the fields
are the cited typings. -/
structure ProofLeaf (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (p q T : Expr Nat) where
  hT : HasTyT E n Γ T (.sort .zero)
  hp : HasTyT E n Γ p T
  hq : HasTyT E n Γ q T

/-- one typed parallel step whose `peq` leaf is `ProofLeaf`. -/
abbrev PiStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b T : Expr Nat) : Type :=
  ParRedT (ProofLeaf E n) E n Γ a b T

/-- a star of typed parallel steps whose `peq` leaf is `ProofLeaf`. -/
abbrev PiStar (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b T : Expr Nat) : Type :=
  ParRedTStar (ProofLeaf E n) E n Γ a b T

/-- a `DerivedIotaU` source can never be Π-shaped — both arms put a
`foldApps`-headed (`.app`-headed) expression on the left. The private
sibling in `RcicParRedTPiHead` is not reachable; this is rebuilt from
the public `foldApps_snoc_ne_pi`. -/
private theorem derivedIotaU_pi_source_false {E : ResolvedEnv}
    {lhs rhs A B : Expr Nat} (h : DerivedIotaU E lhs rhs)
    (heq : lhs = .pi A B) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls) (ctorMajor w)
        w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
        w.preMajor heq

/-! ## §5.3 — one-step Π-source projection, all 18 constructors -/

/-- one typed parallel step out of a Π source lands at a Π target whose
components move by the weak row. Recursion only on `conv.h` and
`iotaSpine.hstep`. -/
theorem piStep_project (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → PiStep E n Γ a b T → {A B : Expr Nat} →
      a = .pi A B →
      ∃ (A' B' : Expr Nat), (b = .pi A' B') ∧ PiCompRow E n Γ A B A' B'
  | _, _, _, .refl _ a _ _, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, piCompRow_refl⟩
  | _, _, _, .sortEq _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .pi _ _ A' _ B' u _ _ hc _ hcB _, A, B, heq => by
      obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
      exact ⟨A', B', rfl, ⟨⟨.of _ _ _ u hc⟩, ⟨.of _ _ _ _ hcB⟩⟩⟩
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hI _ _, _, _, heq => by
      obtain ⟨_, _, hhead, _⟩ := piStep_project hW su hΓ hstep heq
      exact False.elim (derivedIotaU_pi_source_false hI hhead)
  | _, _, _, .iotaStarK _ w major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
        _, _, heq => by
      exact absurd heq
        (foldApps_snoc_ne_pi (.const w.recRef w.ls) major w.preMajor)
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _,
        _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .lit _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .eta _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ h, A, B, heq => by
      subst heq
      exact False.elim (F8Measure.SP1.piProofRoot_false hW su hΓ h.hT h.hp)
  | _, _, _, .conv _ _ _ _ _ h _, A, B, heq =>
      piStep_project hW su hΓ h heq

/-! ## §5.4 — star projection and the native valley -/

/-- a star of steps out of a Π source lands at a Π target whose
components move by the composed row. -/
theorem piStar_project (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a c T : Expr Nat}
    (s : PiStar E n Γ a c T) :
    ∀ {A B : Expr Nat}, a = .pi A B →
      ∃ (A' B' : Expr Nat), (c = .pi A' B') ∧ PiCompRow E n Γ A B A' B' := by
  induction s with
  | refl _ _ _ =>
      intro A B heq
      subst heq
      exact ⟨A, B, rfl, piCompRow_refl⟩
  | tail h hs ih =>
      intro A B heq
      obtain ⟨A₁, B₁, hhead, row₁⟩ := piStep_project hW su hΓ h heq
      subst hhead
      obtain ⟨A', B', hhead', row₂⟩ := ih rfl
      exact ⟨A', B', hhead', piCompRow_trans hW hΓ row₁ row₂⟩

/-- a native conversion valley: both sides reach a common centre by
typed parallel stars. -/
structure NativeValley (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b T : Expr Nat) where
  centre : Expr Nat
  left : PiStar E n Γ a centre T
  right : PiStar E n Γ b centre T

/-- the remaining supplier gap, kept explicit (NOT assumed, NOT proved):
every typed conversion in a well-formed context admits a native valley.
The dependent-application alignment this needs is the unresolved wall —
see §5.5 of the spec. -/
def NativeConvValleys (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b T : Expr Nat},
    ConvT E n Γ a b T → Nonempty (NativeValley E n Γ a b T)

/-- a valley between two Π types projects to the weak row: project the
left path, reverse the right row, compose. -/
theorem valley_piCompRow (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T A B A' B' : Expr Nat}
    (v : NativeValley E n Γ a b T)
    (ha : a = .pi A B) (hb : b = .pi A' B') :
    PiCompRow E n Γ A B A' B' := by
  subst ha; subst hb
  obtain ⟨A₁, B₁, hL, rowL⟩ := piStar_project hW su hΓ v.left rfl
  obtain ⟨A₂, B₂, hR, rowR⟩ := piStar_project hW su hΓ v.right rfl
  obtain ⟨rfl, rfl⟩ := Expr.pi.inj (hL.symm.trans hR)
  exact piCompRow_trans hW hΓ rowL (piCompRow_symm hW hΓ rowR)

/-! ## §5.5 — the conditional weak Π row -/

/-- the weak `piRow`, conditional on the explicit `NativeConvValleys`
supplier: a `TyConvT` between Π types yields domain and codomain
conversions (left-binder convention). Equal sources give raw
reflexivities; otherwise DT-009 sorts the first native edge, the
sortUnique collapses the chain at that sort, and the valley projects. -/
theorem weak_piRow_of_nativeValleys (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) (join : NativeConvValleys E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (d : TyConvT E n Γ (.pi A B) (.pi A' B')) :
    Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  rcases TyConvT.firstOf d with heq | ⟨C, u, ⟨hstep⟩, _⟩
  · obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · obtain ⟨⟨hPl⟩, -⟩ := convT_endpoints hW hΓ hstep
    obtain ⟨hc⟩ := F8EtaK.convT_of_tyConvT_sort_of_sortUniq hW (su hW) hΓ hPl d
    obtain ⟨v⟩ := join hΓ hc
    exact valley_piCompRow hW su hΓ v rfl rfl

/-! ## §5.6 — the Loop fixture: finite homogeneous Π unfoldings -/

/-- `X₀ = X` (the recursor application `F t`), `Xₖ₊₁ = Π(Xₖ, lift Xₖ)`. -/
def pinLoopX : Nat → Expr Nat
  | 0 => loopXT
  | k + 1 => .pi (pinLoopX k) (lift 0 1 (pinLoopX k))

/-- `Cₖ : Xₖ ≡ Xₖ₊₁ : Prop`. `C₀` is the real Loop equation
`convT_pinLoop` (`lift 0 1 loopXT` computes to `.app loopFT (.bvar 1)`,
so `pinLoopX 1` IS `loopArrowT`); the step is `ConvT.pi` on `Cₖ` and
its `convTWeaken`, retyped through `eqN_imax00`. -/
def pinLoopX_step {n : Nat} : (k : Nat) →
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (pinLoopX k) (pinLoopX (k + 1))
      (.sort .zero)
  | 0 => convT_pinLoop
  | k + 1 =>
      ConvT.tyConv _ _ _ _ _ _
        (.pi _ _ _ _ _ .zero .zero (pinLoopX_step k)
          (convTWeaken (.assumption (pinLoopX k))
            (envClosed_of_envWfT pinLoopEraseWfT) (c := 0) (pinLoopX_step k)))
        (.sorts _ _ _ eqN_imax00)

/-- `Xₖ ≡ Xₖ₊d` by `d` step compositions. `d = 0` discharges the
reflexive case without needing an `Xₖ` typing (`trans Cₖ (symm Cₖ)`). -/
def pinLoopX_chain {n : Nat} : (d k : Nat) →
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (pinLoopX k) (pinLoopX (k + d))
      (.sort .zero)
  | 0, k =>
      ConvT.trans _ _ _ _ _ (pinLoopX_step k)
        (.symm _ _ _ _ (pinLoopX_step k))
  | d + 1, k =>
      ConvT.trans _ _ _ _ _ (pinLoopX_chain d k) (pinLoopX_step (k + d))

/-- `Xₖ ≡ Xₗ` for any `k l`: chain up on the smaller index, symmetric on
the larger. -/
def pinLoopX_conv {n : Nat} (k l : Nat) :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (pinLoopX k) (pinLoopX l)
      (.sort .zero) :=
  match Nat.decLe k l with
  | isTrue h => by
      have c := pinLoopX_chain (n := n) (l - k) k
      rw [Nat.add_sub_of_le h] at c
      exact c
  | isFalse h => by
      have c := pinLoopX_chain (n := n) (k - l) l
      rw [Nat.add_sub_of_le (Nat.le_of_not_ge h)] at c
      exact .symm _ _ _ _ c

/-- the Loop's finite homogeneous Π unfoldings satisfy the weak-row
component conclusion: every `Xₖ ≡ Xₗ` gives the domain chain, and its
`convTWeaken` under `Xₖ`'s binder gives the codomain chain. This is a
statement about the CONCRETE Loop `X` at `pinLoopEraseWfT` — it does not
establish safety for every Loop-like group. -/
theorem pinLoop_finite_components {n : Nat} : (k l : Nat) →
    Nonempty (TyConvT (eraseEnv pinLoopEnvA) n loopΓ (pinLoopX k)
        (pinLoopX l)) ∧
    Nonempty (TyConvT (eraseEnv pinLoopEnvA) n
        (.assumption (pinLoopX k) :: loopΓ)
      (lift 0 1 (pinLoopX k)) (lift 0 1 (pinLoopX l)))
  | k, l =>
      have c := pinLoopX_conv (n := n) k l
      ⟨⟨.of _ _ _ .zero c⟩,
       ⟨.of _ _ _ .zero
         (convTWeaken (.assumption (pinLoopX k))
           (envClosed_of_envWfT pinLoopEraseWfT) (c := 0) c)⟩⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.binderTransport
#print axioms Rcic.Declarative.piCompRow_symm
#print axioms Rcic.Declarative.piCompRow_trans
#print axioms Rcic.Declarative.piStep_project
#print axioms Rcic.Declarative.piStar_project
#print axioms Rcic.Declarative.valley_piCompRow
#print axioms Rcic.Declarative.weak_piRow_of_nativeValleys
#print axioms Rcic.Declarative.pinLoopX_step
#print axioms Rcic.Declarative.pinLoopX_chain
#print axioms Rcic.Declarative.pinLoopX_conv
#print axioms Rcic.Declarative.pinLoop_finite_components
