import rcic.RcicDeclarative
import rcic.RcicDerivedIotaU
import rcic.RcicInductivePolicy
import rcic.RcicTypedEnv

/-!
# RcicParRedT — all-position TYPED parallel reduction on `Expr Nat` (S1, plain side)

The plain-side twin of `ParRedA` (`RcicParRedA.lean`), re-targeted by the
#6293 ruling after apex3's inventory: the ATR route runs on
`ResolvedEnv`/`EnvWfT` because the annotated elaboration needs `huniq`
(semantic, circular with what the mutual must prove). `ParRedT PEq E n Γ
a b T` reads "`a` parallel-steps to `b`, both endpoints typed at `T`" —
the erased `ParRed` (`RcicParRedCore`) arm-shapes with `ParRedA`'s
premise discipline, all Ann machinery removed (`Expr.pi`/`Expr.lam` are
unannotated here; `HasTyT` takes no iota-interface parameter).

## Design (named free choices — `F-ParRedA-*` twins noted)

* **F-ParRedT-1 (typed index).** `= F-ParRedA-1`: 4-place `Γ a b T`,
  endpoints typed at a common `T` by construction (`parRedT_typed`).
* **F-ParRedT-2 (annotation positions by `ConvT`).** `lam`/`pi`/`letE`
  domains move by `ConvT` at a sort (`ConvT.lam`/`ConvT.pi` convention).
  The unannotated `Expr` has no `eqN`-drift premises — the Ann side's
  `u u'`/`hu` pairs collapse away.
* **F-ParRedT-3 (index typings as bundle members).** On the Ann side
  `lam`/`pi`/`letE` extracted the domain's sort-typing from the `ConvA`
  premise (`convA_hasTy_left`). The plain side has **no**
  `convT_hasTy_left` — it exists only through the `AnnEnvA` bridge
  (`Ann.convT_of_tyConvT_sort`), i.e. semantic territory the route
  exists to avoid (irrpost's crux item). So `hA`/`hB` are carried as
  explicit premises — exactly F-ι★-8 condition 3, "index typings carried
  as bundle members".
* **F-ParRedT-4 (`conv` at the index).** `= F-ParRedA-4`: the shared
  type index moves by `TyConvT`. It is an arm, not a derived lemma:
  `hTy : HasTyT (inst0 …) (sort w)`-shaped premises (the index's own
  well-formedness) cannot be transported premise-free — subject-side
  transport is the semantic lemma. 17 constructors: the 13 erased
  arm-shapes typed + `iotaStarK` + the `peq` leaf + `eta` + this
  index-mover.
* **F-ParRedT-5 (ι at STEPPED endpoints, `DerivedIotaU`).** `= F-ParRedA-5`
  with `I.rel` replaced by `DerivedIotaU` (cc addendum): `iotaSpine`
  fires on the STEPPED redex `lhs'` and its reduct is pinned by a union
  landing — `.ofU` (legacy `IotaWitness`) OR `.ofUS` (`IotaWitnessS`,
  the schema witness) — so frec ι (W types) computes in `ParRedT` by
  construction, discharging R-NoFunRec remainder 1. The Ann side's
  `structIota` has no plain counterpart in the 13-arm set.
* **F-ParRedT-8 (η-contraction).** The Ann side's `eta` arm, ported
  (13:45Z ruling on #6293 — the verifier found `J` false at
  `ConvT.eta`, the same wall `RcicConvChar` documents on the erased
  side where `convRedOnly` excludes `eta`/`irr` from the join's
  domain). `lam A (app (lift 0 1 f) (bvar 0)) ⇒ f'`: the `lift` bakes
  `x ∉ fv f` in structurally; the annotation `A` IS `f`'s Π-domain —
  alignment syntactic by construction (`ConvT.eta`'s trick). `hf` is
  the Tait–Martin–Löf step (the function appears inside the expansion
  AND as the reduct); `hl` carries the left endpoint's typing
  (F-ParRedT-3). `PEqT` gets NO η clause — a union relation later if
  the `irr` route needs it.
* **F-ParRedT-6 (ι★K, the typed K-gate).** `= F-ParRedA-6`: the group
  facts the Ann arm drew from `iotaGroupA`/`IotaGroupA` are carried by a
  plain `IotaWitness w` of the SYNTHESIZED ctor-spine redex
  `iotaLhsOf w` — the synthesized spine IS constructor-headed, so a
  witness exists and `w.famMember`/`w.nMinors`/`w.familyRef`/`w.ctorRef`
  supply the gate. `major` is arbitrary; the typed gate
  `hmajor : HasTyT major Tm` + `hmk : HasTyT (ctorMajor w) Tm` +
  `hfam`/`hTm0` pin `Tm ≡ I ps (idx f⃗)` — the major types at the ctor's
  result instance, indices unified by field values (Loop degenerate,
  `Eq`/`HEq` indexed; index mismatch leaves a neutral). `hsel` gates on
  `EliminationSelection rl w.nMinors afs .anySort` (singleton-Prop:
  `UniformProp rl ∧ w.nMinors = 1 ∧ afs`); `hrl` reads the family's
  result sort off `piBody w.famMember.mtype`. The contraction at the
  synthesized spine is `hι : DerivedIotaU E (iotaLhsOf w) rhs` — the
  same union relation as `iotaSpine`. Steward's `pinEqT` pins (#6421)
  are the intended fixtures.
* **F-ParRedT-7 (the `peq` leaf, stubbed).** The `irr` position carries
  `h : PEq Γ p q T` where `PEq` is a module parameter — instantiated
  with irrpost's `PEqT` (`HasTyT`-evidence-carrying leaf) once it lands.
  Consumers needing endpoint typing take the `hPEq` hypothesis
  (`parRedT_typed`); consumers needing index transport take
  `PEq`-conversion as a premise when it is named.

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative

/-- The body under all leading Π-binders (`piBodyA`'s plain sibling;
    reads the family's result sort for `iotaStarK`'s `hrl`). -/
def piBody : Expr Nat → Expr Nat
  | .pi _ B => piBody B
  | e => e

/-- All-position typed parallel reduction on `Expr Nat`: `a` steps to
    `b`, both typed at `T`. The 13 erased `ParRed` arm-shapes typed
    (`RcicParRedCore.lean:131`), `iotaStarK` (F-ParRedT-6), the `peq`
    leaf (F-ParRedT-7) and the index-mover `conv` (F-ParRedT-4).
    `PEq` is the stubbed proof-irrelevance leaf relation (F-ParRedT-7). -/
inductive ParRedT (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  /-- reflexivity, on typed terms. -/
  | refl (Γ : LCtx) (a A : Expr Nat)
      (h : HasTyT E n Γ a A) :
      ParRedT PEq E n Γ a a A
  /-- `=ₙ`-related sorts step in parallel (the `sortEq` of `ParRed`). -/
  | sortEq (Γ : LCtx) (l₁ l₂ : Level) (T : Expr Nat)
      (h : eqN l₁ l₂)
      (hl : HasTyT E n Γ (.sort l₁) T) (hr : HasTyT E n Γ (.sort l₂) T) :
      ParRedT PEq E n Γ (.sort l₁) (.sort l₂) T
  /-- `=ₙ`-related universe arguments on a constant (the `consts` of
      `ParRed`, endpoint-typed). -/
  | consts (Γ : LCtx) (r : Nat) (ls ls' : List Level) (T : Expr Nat)
      (h : eqNList ls ls')
      (hl : HasTyT E n Γ (.const r ls) T) (hr : HasTyT E n Γ (.const r ls') T) :
      ParRedT PEq E n Γ (.const r ls) (.const r ls') T
  /-- local ζ: a `let`-bound variable steps to a parallel reduct of its
      stored value (the stored decl is `Γ.get?`, the step below at
      `Γ.drop`). -/
  | bvarZeta (Γ : LCtx) (i : Nat) (A v v' T : Expr Nat)
      (h : Γ.get? i = some (.letBinding A v))
      (hv : ParRedT PEq E n (Γ.drop (i + 1)) v v' A)
      (hl : HasTyT E n Γ (.bvar i) T)
      (hr : HasTyT E n Γ (lift 0 (i + 1) v') T) :
      ParRedT PEq E n Γ (.bvar i) (lift 0 (i + 1) v') T
  /-- δ: a transparent constant unfolds (level-instantiated body). -/
  | delta (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
      (b T : Expr Nat)
      (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hl : HasTyT E n Γ (.const r ls) T)
      (hr : HasTyT E n Γ (instantiateLevels ls b) T) :
      ParRedT PEq E n Γ (.const r ls) (instantiateLevels ls b) T
  /-- application congruence: `f` steps at `T₀`, `TyConvT`-isomorphic to
      the `pi` the argument steps at — `ParRedA.app`'s `hc` convention. -/
  | app (Γ : LCtx) (f f' a a' A B T₀ : Expr Nat) (v w : Level)
      (hf : ParRedT PEq E n Γ f f' T₀)
      (hc : TyConvT E n Γ T₀ (.pi A B))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
      (ha : ParRedT PEq E n Γ a a' A)
      (hr : HasTyT E n Γ (.app f' a') (instantiate0 a B)) :
      ParRedT PEq E n Γ (.app f a) (.app f' a') (instantiate0 a B)
  /-- β: body and argument step in parallel; the reduct's typing at the
      left's instantiated codomain is carried (`hred`). -/
  | beta (Γ : LCtx) (A body body' arg arg' B : Expr Nat) (u v w : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w))
      (hb : ParRedT PEq E n (.assumption A :: Γ) body body' B)
      (ha : ParRedT PEq E n Γ arg arg' A)
      (hred : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg B)) :
      ParRedT PEq E n Γ (.app (.lam A body) arg) (instantiate0 arg' body')
        (instantiate0 arg B)
  /-- λ congruence: the domain moves by `ConvT` (F-ParRedT-2), its own
      sort-typing carried (F-ParRedT-3), the body steps under the LEFT
      domain's context. -/
  | lam (Γ : LCtx) (A A' body body' B : Expr Nat) (u v : Level)
      (hc : ConvT E n Γ A A' (.sort u))
      (hA : HasTyT E n Γ A (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hb : ParRedT PEq E n (.assumption A :: Γ) body body' B)
      (hrt : HasTyT E n Γ (.lam A' body') (.pi A B)) :
      ParRedT PEq E n Γ (.lam A body) (.lam A' body') (.pi A B)
  /-- Π congruence: domain and codomain move by `ConvT` at the domain
      sorts (`ConvT.pi` verbatim), endpoint typings carried. -/
  | pi (Γ : LCtx) (A A' B B' : Expr Nat) (u v : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hc : ConvT E n Γ A A' (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
      (hrt : HasTyT E n Γ (.pi A' B') (.sort (.imax u v))) :
      ParRedT PEq E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v))
  /-- `let` congruence: the annotation moves by `ConvT`, value and body
      step by `ParRedT` (the body under the LEFT's binding). -/
  | letE (Γ : LCtx) (A A' value value' body body' B : Expr Nat) (u w : Level)
      (hc : ConvT E n Γ A A' (.sort u))
      (hA : HasTyT E n Γ A (.sort u))
      (hv : ParRedT PEq E n Γ value value' A)
      (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
      (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
      (hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B)
      (hrt : HasTyT E n Γ (.letE A' value' body') (instantiate0 value B)) :
      ParRedT PEq E n Γ (.letE A value body) (.letE A' value' body')
        (instantiate0 value B)
  /-- ζ: the let unfolds, value and body stepping first — `ConvT.zeta`'s
      premises at parallel granularity. -/
  | zeta (Γ : LCtx) (A value value' body body' B : Expr Nat) (u w : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hv : ParRedT PEq E n Γ value value' A)
      (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
      (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
      (hb : ParRedT PEq E n (.letBinding A value :: Γ) body body' B)
      (hred : HasTyT E n Γ (instantiate0 value' body') (instantiate0 value B)) :
      ParRedT PEq E n Γ (.letE A value body) (instantiate0 value' body')
        (instantiate0 value B)
  /-- ι through the union at a stepped redex — the Tait–Martin–Löf
      shape: the redex parallel-steps and ι fires on the STEPPED side.
      `hI : DerivedIotaU` covers both the legacy `IotaWitness` (`.ofU`)
      and the schema `IotaWitnessS` (`.ofUS`, frec ι) landing
      (F-ParRedT-5, the #6293 addendum). -/
  | iotaSpine (Γ : LCtx) (lhs lhs' rhs T : Expr Nat)
      (hstep : ParRedT PEq E n Γ lhs lhs' T)
      (hI : DerivedIotaU E lhs' rhs)
      (hred : HasTyT E n Γ lhs' T)
      (hrhs : HasTyT E n Γ rhs T) :
      ParRedT PEq E n Γ lhs rhs T
  /-- ι★K (F-ParRedT-6, the typed K-gate): singleton-`Prop` ι, the major
      arbitrary. `w` witnesses the SYNTHESIZED ctor-spine redex
      `iotaLhsOf w`; `hrl`/`hsel` gate on the family's singleton-`Prop`
      `EliminationSelection` shape; `fields`/`lsC` ride inside
      `ctorMajor w` (the existential `mk p⃗`); `hmajor` types the major
      at the same `Tm` `mk p⃗` inhabits — the ctor's result instance
      `I ps (idx p⃗)` (`hfam`/`hTm0` pin it: family-headed, Prop-sorted).
      Loop degenerate (no indices), `Eq`/`HEq` covered — an index gap
      fails the gate and leaves the recursor neutral. The reduct is the
      union's computation at the synthesized spine (`hι`); both
      endpoints typed at `T` (ATR). -/
  | iotaStarK (Γ : LCtx) (w : IotaWitness E) (major Tm rhs T : Expr Nat)
      (rl : Level) (afs : Prop)
      (hrl : piBody w.famMember.mtype = .sort rl)
      (hsel : EliminationSelection rl w.nMinors afs .anySort)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hmk : HasTyT E n Γ (ctorMajor w) Tm)
      (hTm0 : HasTyT E n Γ Tm (.sort .zero))
      (hι : DerivedIotaU E (iotaLhsOf w) rhs)
      (hlι : HasTyT E n Γ (iotaLhsOf w) T)
      (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T)
      (hrhs : HasTyT E n Γ rhs T) :
      ParRedT PEq E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major) rhs T
  /-- η-abstracted ι★K (A-2 repair, #6951): when `f` is a partially applied
      singleton-`Prop` recursor spine at type `.pi A B` whose η-expansion body
      `recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) = .app (lift 0 1 f) (.bvar 0)`
      satisfies the typed `iotaStarK` gate in `.assumption A :: Γ`, `f` steps
      directly to `.lam A rhs` at `.pi A B`. -/
  | iotaStarKEta (Γ : LCtx) (w : IotaWitness E)
      (f A B Tm rhs : Expr Nat) (u rl : Level) (afs : Prop)
      (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
        .app (lift 0 1 f) (.bvar 0))
      (hA : HasTyT E n Γ A (.sort u))
      (hf : HasTyT E n Γ f (.pi A B))
      (hrl : piBody w.famMember.mtype = .sort rl)
      (hsel : EliminationSelection rl w.nMinors afs .anySort)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n (.assumption A :: Γ) (.bvar 0) Tm)
      (hmk : HasTyT E n (.assumption A :: Γ) (ctorMajor w) Tm)
      (hTm0 : HasTyT E n (.assumption A :: Γ) Tm (.sort .zero))
      (hι : DerivedIotaU E (iotaLhsOf w) rhs)
      (hlι : HasTyT E n (.assumption A :: Γ) (iotaLhsOf w) B)
      (hlhs : HasTyT E n (.assumption A :: Γ)
        (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) B)
      (hrhs : HasTyT E n (.assumption A :: Γ) rhs B) :
      ParRedT PEq E n Γ f (.lam A rhs) (.pi A B)
  /-- a literal expands — `ConvT.lit`/`ParRed.lit` verbatim. -/
  | lit (Γ : LCtx) (t : Nat) (T : Expr Nat)
      (hexp : HasTyT E n Γ (natExpand t) T) :
      ParRedT PEq E n Γ (.lit t) (natExpand t) T
  /-- η-contraction (F-ParRedT-8): an η-expansion steps to the
      function's reduct — `ConvT.eta`'s shape with the
      Tait–Martin–Löf `hf` step. `x ∉ fv f` is structural (`lift 0 1`
      bakes it); the annotation `A` IS `f`'s Π-domain, so the domain
      alignment is syntactic by construction. `hl` carries the left
      endpoint's typing (F-ParRedT-3). -/
  | eta (Γ : LCtx) (f f' A B : Expr Nat)
      (hf : ParRedT PEq E n Γ f f' (.pi A B))
      (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
      ParRedT PEq E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B)
  /-- the `peq` leaf (F-ParRedT-7): proof-irrelevance at `T`, its
      relation stubbed as the `PEq` parameter until `PEqT` lands. -/
  | peq (Γ : LCtx) (p q T : Expr Nat)
      (h : PEq Γ p q T) :
      ParRedT PEq E n Γ p q T
  /-- the shared type index moves by `TyConvT` (F-ParRedT-4). -/
  | conv (Γ : LCtx) (a b A A' : Expr Nat)
      (h : ParRedT PEq E n Γ a b A) (hc : TyConvT E n Γ A A') :
      ParRedT PEq E n Γ a b A'

/-- Pointwise typed parallel reduction of an argument list — the typed
    `ParRedArgs`. Each element steps at its own type. -/
inductive ParRedArgsT (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) :
    LCtx → List (Expr Nat) → List (Expr Nat) → Type where
  | nil (Γ : LCtx) : ParRedArgsT PEq E n Γ [] []
  | cons {Γ : LCtx} {x y A : Expr Nat} {xs ys : List (Expr Nat)}
      (h : ParRedT PEq E n Γ x y A) (t : ParRedArgsT PEq E n Γ xs ys) :
      ParRedArgsT PEq E n Γ (x :: xs) (y :: ys)

/-- Pointwise typed parallel reduction of a local context — the typed
    `ParRedCtx`. Assumption types step at a sort; let-binding values step
    at the binding's type, both in the tail context. -/
inductive ParRedCtxT (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type where
  | nil : ParRedCtxT PEq E n [] []
  | assumption {Γ Γ' : LCtx} {A A' : Expr Nat} {u : Level}
      (hA : ParRedT PEq E n Γ A A' (.sort u)) (hΓ : ParRedCtxT PEq E n Γ Γ') :
      ParRedCtxT PEq E n (.assumption A :: Γ) (.assumption A' :: Γ')
  | letBinding {Γ Γ' : LCtx} {A A' v v' : Expr Nat} {u : Level}
      (hA : ParRedT PEq E n Γ A A' (.sort u))
      (hv : ParRedT PEq E n Γ v v' A)
      (hΓ : ParRedCtxT PEq E n Γ Γ') :
      ParRedCtxT PEq E n (.letBinding A v :: Γ) (.letBinding A' v' :: Γ')

/-- Multi-step typed parallel reduction at a FIXED type index — the
    typed `ParRedStar`. The type index is constant across the chain;
    `ParRedT.conv` absorbs any per-step drift. -/
inductive ParRedTStar (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | refl (Γ : LCtx) (a A : Expr Nat) (h : HasTyT E n Γ a A) :
      ParRedTStar PEq E n Γ a a A
  | tail {Γ : LCtx} {a b c A : Expr Nat}
      (h : ParRedT PEq E n Γ a b A) (hs : ParRedTStar PEq E n Γ b c A) :
      ParRedTStar PEq E n Γ a c A

section Basics

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat}

private theorem foldApps_app_is_app (hd x : Expr Nat) :
    (xs : List (Expr Nat)) → ∃ g y, foldApps (.app hd x) xs = .app g y
  | [] => ⟨hd, x, rfl⟩
  | z :: zs => foldApps_app_is_app (.app hd x) z zs

private theorem appsSpine_lift_zero_one :
    (e : Expr Nat) →
    (appsSpine (lift 0 1 e)).2 = (appsSpine e).2.map (lift 0 1)
  | .bvar _ => by simp only [lift]; split <;> rfl
  | .sort _ | .const _ _ | .lam _ _ | .pi _ _ | .letE _ _ _ | .lit _ => rfl
  | .app g x => by
      simp only [lift, appsSpine, appsSpine_lift_zero_one g,
        List.map_append, List.map_cons, List.map_nil]

private theorem appsSpine_lift_const_inv {r : Nat} {ls : List Level} :
    (e : Expr Nat) → (appsSpine (lift 0 1 e)).1 = .const r ls →
    (appsSpine e).1 = .const r ls
  | .bvar _, h => by simp only [lift] at h; split at h <;> exact nomatch h
  | .sort _, h => by simp [lift, appsSpine] at h
  | .const _ _, h => by simpa [lift, appsSpine] using h
  | .lam _ _, h => by simp [lift, appsSpine] at h
  | .pi _ _, h => by simp [lift, appsSpine] at h
  | .letE _ _ _, h => by simp [lift, appsSpine] at h
  | .lit _, h => by simp [lift, appsSpine] at h
  | .app g _, h => appsSpine_lift_const_inv g h

/-- Every `iotaStarKEta` source `f` is syntactically an application `f = .app f₀ a₀`
    because `w.preMajor` is non-empty (`w.preMajor.length = w.nparams + 1 + w.nMinors + w.nindices ≥ 2`). -/
theorem iotaStarKEta_appParts {w : IotaWitness E} {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0)) :
    ∃ f₀ a₀, f = .app f₀ a₀ := by
  have h1 : foldApps (.const w.recRef w.ls) w.preMajor = lift 0 1 f := by
    rw [recCall, foldApps_snoc] at happ
    exact (Expr.app.inj happ).1
  have hlen : 0 < w.preMajor.length := by
    have hp := w.hpre
    have hi := w.hidx
    omega
  cases hpm : w.preMajor with
  | nil => rw [hpm] at hlen; exact absurd hlen (Nat.lt_irrefl 0)
  | cons x zs =>
      rw [hpm] at h1
      simp only [foldApps] at h1
      obtain ⟨g, y, hgy⟩ := foldApps_app_is_app (.const w.recRef w.ls) x zs
      rw [hgy] at h1
      cases f with
      | app f₀ a₀ => exact ⟨f₀, a₀, rfl⟩
      | bvar _ => simp only [lift] at h1; split at h1 <;> exact nomatch h1
      | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          exact nomatch h1

/-- `iotaStarKEta` pins `f`'s spine head to `.const w.recRef w.ls`, its lifted
    spine arguments to `w.preMajor`, and its spine arity to
    `w.nparams + 1 + w.nMinors + w.nindices`. -/
theorem iotaStarKEta_head {w : IotaWitness E} {f : Expr Nat}
    (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
      .app (lift 0 1 f) (.bvar 0)) :
    (appsSpine f).1 = .const w.recRef w.ls ∧
    (appsSpine f).2.map (lift 0 1) = w.preMajor ∧
    (appsSpine f).2.length = w.nparams + 1 + w.nMinors + w.nindices := by
  have h1 : foldApps (.const w.recRef w.ls) w.preMajor = lift 0 1 f := by
    rw [recCall, foldApps_snoc] at happ
    exact (Expr.app.inj happ).1
  have hsp := congrArg appsSpine h1
  rw [appsSpine_foldApps_const] at hsp
  have hhd : (appsSpine (lift 0 1 f)).1 = .const w.recRef w.ls :=
    (Prod.mk.inj hsp).1.symm
  have hargs : (appsSpine (lift 0 1 f)).2 = w.preMajor :=
    (Prod.mk.inj hsp).2.symm
  rw [appsSpine_lift_zero_one] at hargs
  refine ⟨appsSpine_lift_const_inv f hhd, hargs, ?_⟩
  have hlen := congrArg List.length hargs
  rw [List.length_map] at hlen
  exact hlen.trans w.hpre

/-- Typing transport across a `TyConvT` chain — each link is a `ConvT`
    at a sort, applied by `HasTyT.conv`; reflexive-transitive closure by
    recursion. -/
def hasTyT_of_tyConvT {Γ : LCtx} {a A A' : Expr Nat}
    (h : HasTyT E n Γ a A) : TyConvT E n Γ A A' → HasTyT E n Γ a A'
  | .refl _ _ => h
  | .of _ _ _ _ hcv => .conv _ _ _ _ _ h hcv
  | .trans _ _ _ _ h1 h2 => hasTyT_of_tyConvT (hasTyT_of_tyConvT h h1) h2

/-- A `ParRedT` step types both endpoints at the shared index — the
    typing is in the relation, not recovered after. Needs no env fronts:
    every endpoint typing is a carried premise (F-ParRedT-3), the
    binder-recursion contexts assemble from the arms' explicit `hA`s,
    and `hPEq` is the `peq` leaf's typing evidence (which `PEqT` will
    supply by construction). -/
def parRedT_typed (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
    PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    HasTyT E n Γ a T × HasTyT E n Γ b T
  | _, _, _, .refl _ _ _ h => ⟨h, h⟩
  | _, _, _, .sortEq _ _ _ _ _ hl hr => ⟨hl, hr⟩
  | _, _, _, .consts _ _ _ _ _ _ hl hr => ⟨hl, hr⟩
  | _, _, _, .bvarZeta _ _ _ _ _ _ _ _ hl hr => ⟨hl, hr⟩
  | _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ hl hr => ⟨hl, hr⟩
  | _, _, _, .app Γ f _ a _ A B _ _ _ hf hc _ _ ha hr =>
      let ⟨hfT, _⟩ := parRedT_typed hPEq hΓ hf
      let ⟨haA, _⟩ := parRedT_typed hPEq hΓ ha
      ⟨.app Γ f a A B (hasTyT_of_tyConvT hfT hc) haA, hr⟩
  | _, _, _, .beta Γ A body _ arg _ B _ _ _ hA _ _ hb ha hred =>
      let ⟨hbody, _⟩ :=
        parRedT_typed hPEq (.assumption Γ A _ hΓ hA) hb
      let ⟨harg, _⟩ := parRedT_typed hPEq hΓ ha
      ⟨.app Γ (.lam A body) arg A B
        (.lam Γ A _ body B hA hbody) harg, hred⟩
  | _, _, _, .lam Γ A _ body _ B _ _ _ hA _ hb hrt =>
      let ⟨hbody, _⟩ :=
        parRedT_typed hPEq (.assumption Γ A _ hΓ hA) hb
      ⟨.lam Γ A _ body B hA hbody, hrt⟩
  | _, _, _, .pi Γ A _ B _ _ _ hA _ hB _ hrt =>
      ⟨.pi Γ A _ B _ hA hB, hrt⟩
  | _, _, _, .letE Γ A _ value _ body _ B u _ _ hA hv _ _ hb hrt =>
      let ⟨hvA, _⟩ := parRedT_typed hPEq hΓ hv
      let ⟨hbody, _⟩ :=
        parRedT_typed hPEq (.letBinding Γ A u value hΓ hA hvA) hb
      ⟨.letE Γ A u value B body hA hvA hbody, hrt⟩
  | _, _, _, .zeta Γ A value _ body _ B u _ hA hv _ _ hb hred =>
      let ⟨hvA, _⟩ := parRedT_typed hPEq hΓ hv
      let ⟨hbody, _⟩ :=
        parRedT_typed hPEq (.letBinding Γ A u value hΓ hA hvA) hb
      ⟨.letE Γ A u value B body hA hvA hbody, hred⟩
  | _, _, _, .iotaSpine _ _ _ _ _ hstep _ _ hrhs =>
      ⟨(parRedT_typed hPEq hΓ hstep).1, hrhs⟩
  | _, _, _, .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlhs hrhs =>
      ⟨hlhs, hrhs⟩
  | _, _, _, .iotaStarKEta Γ _ _ A _ _ rhs u _ _ _ hA hf _ _ _ _ _ _ _ _ _ hrhs =>
      ⟨hf, .lam Γ A u rhs _ hA hrhs⟩
  | _, _, _, .lit Γ t _ hexp => ⟨.lit Γ t _ hexp, hexp⟩
  | _, _, _, .eta _ _ _ _ _ hf hl =>
      ⟨hl, (parRedT_typed hPEq hΓ hf).2⟩
  | _, _, _, .peq _ _ _ _ h => hPEq h
  | _, _, _, .conv _ _ _ _ _ h hc =>
      let ⟨ha, hb⟩ := parRedT_typed hPEq hΓ h
      ⟨hasTyT_of_tyConvT ha hc, hasTyT_of_tyConvT hb hc⟩

/-- Left endpoint typing (the common face). -/
def parRedT_hasTy_left (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
    PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (h : ParRedT PEq E n Γ a b T) : HasTyT E n Γ a T :=
  (parRedT_typed hPEq hΓ h).1

/-- Right endpoint typing — the premise-carried reduct typing, now a
    theorem of the relation. -/
def parRedT_hasTy_right (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
    PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (h : ParRedT PEq E n Γ a b T) : HasTyT E n Γ b T :=
  (parRedT_typed hPEq hΓ h).2

/-- Star transitivity at the fixed index. -/
def parRedTStar_trans {Γ : LCtx} {a b c A : Expr Nat}
    (h1 : ParRedTStar PEq E n Γ a b A) (h2 : ParRedTStar PEq E n Γ b c A) :
    ParRedTStar PEq E n Γ a c A :=
  match h1 with
  | .refl _ _ _ _ => h2
  | .tail h hs => .tail h (parRedTStar_trans hs h2)

/-- One step as a star. -/
def parRedTStar_of (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
    PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (h : ParRedT PEq E n Γ a b A) :
    ParRedTStar PEq E n Γ a b A :=
  .tail h (.refl _ _ _ (parRedT_hasTy_right hPEq hΓ h))

end Basics

end Rcic.Declarative
