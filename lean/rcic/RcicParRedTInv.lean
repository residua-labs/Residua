import rcic.RcicParRedT
import rcic.RcicTypedInvert
import rcic.RcicParRedIota
import rcic.RcicParRedDiamond

/-!
# RcicParRedTInv — `ParRedT` head-former inversions (typed diamond S2 prep)

Per-head inversion of a `ParRedT` step: what a step OUT of `.sort l`,
`.pi A B`, `.lam A body`, or a constant-headed application spine
`foldApps (.const r ls) xs` can be. Every critical pair of the typed
diamond routes through these: the left derivation is inverted by head
former, the right by the same, and the pair table is discharged arm by
arm.

Style follows `RcicTypedInvert` (fording: unconstrained source + a
propositional equation) and the erased `parRed_sort` / `parRed_pi` /
`parRed_foldApps_const` templates (`RcicParRedCore`/`Iota`/`Diamond`).
Two differences the typed relation forces:

* **Indexed result families, not `Σ'` tuples.** `ParRedT` has four
  wildcard arms the erased `ParRed` lacks — `peq` (the stubbed
  proof-irrelevance leaf), `conv` (the type-index mover), `iotaSpine`
  (the `DerivedIotaU` landing), and `iotaStarK` (the typed K-gate) —
  each a real possibility at most head formers. The result is an
  inductive family indexed by `(target, T)` (for const-spines by
  `(r, ls, xs, target, T)`); constructor return types pin the arm's own
  conclusion shape, so `cases` on the family IS the case split.
* **`conv` is peeled recursively.** `.conv` wraps the underlying step's
  inversion and appends one `TyConvT` link — the accumulation is a
  chain, the same discipline `hasTyTInv_*` uses for `HasTyT.conv`.

For `sort` the `refl` arm folds into the `eq` case (`eqN_refl`); for
`pi`/`lam` it folds into `congr` via the `HasTyT` inversions
(`hasTyTInv_pi`/`hasTyTInv_lam` supply the carried `u`/`v`/`B` and the
`TyConvT` residue). For the const-spine, `refl` collapses to `congr`
through `parRedArgsT_refl_spine` — per-element `ParRedT.refl` needs
per-element typings, which the whole-spine typing decomposes through
`hasTyTInv_app` at each snoc step.

## Cases (per head former)

* `sort l`  → `eq` (`=ₙ`-related sort) | `peq` | `iota` | `conv`.
* `pi A B`  → `congr` (domain/codomain `ConvT` + `TyConvT` residue) |
  `peq` | `iota` | `conv`.
* `lam A body` → `congr` (domain `ConvT` + body `ParRedT` + `TyConvT`
  residue) | `peq` | `iota` | `conv`.
* `foldApps (.const r ls) xs` → `congr` (level-drift + `ParRedArgsT`)
  | `deviate` (last-arg congruence, head step opaque) | `delta`
  (bare const) | `iotaStarK` (synthesized recCall spine) | `iota` |
  `peq` | `conv`.

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative

section Inversions

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat}

/-- Pointwise `ParRedArgsT` over an appended singleton — the typed
    `parRedArgs_snoc`. -/
def parRedArgsT_snoc {Γ : LCtx} {xs ys : List (Expr Nat)}
    {x y A : Expr Nat}
    (h : ParRedArgsT PEq E n Γ xs ys)
    (hx : ParRedT PEq E n Γ x y A) :
    ParRedArgsT PEq E n Γ (xs ++ [x]) (ys ++ [y]) :=
  match h with
  | .nil _ => .cons hx (.nil _)
  | .cons hhd htt => .cons hhd (parRedArgsT_snoc htt hx)

/-- Reflexive `ParRedArgsT` off a whole-spine typing: the `app`
    inversion decomposes `foldApps f (ys ++ [y])` into the head typing
    and the last argument's, recursing down the spine. (`ParRedT.refl`
    needs `HasTyT` per element — the spine typing supplies it.) -/
def parRedArgsT_refl_spine {Γ : LCtx} {f T : Expr Nat} :
    (xs : List (Expr Nat)) →
    HasTyT E n Γ (foldApps f xs) T →
    ParRedArgsT PEq E n Γ xs xs
  | [], _ => .nil _
  | x :: xs, h => by
      have ⟨ys, y, hsplit⟩ :=
        list_snoc_of_ne_nil (x :: xs) (by intro hh; cases hh)
      rw [hsplit] at h ⊢
      rw [foldApps_snoc] at h
      let ⟨_, _, hf, ha, _⟩ := hasTyTInv_app h rfl
      exact parRedArgsT_snoc (parRedArgsT_refl_spine ys hf) (.refl _ _ _ ha)
  termination_by xs => xs.length
  decreasing_by
    rw [hsplit]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Inversion result at a `.sort l` source: `eq` (`refl`/`sortEq`
    collapsed — a sort can only land a `=ₙ`-related sort), the `peq`
    leaf, the `iotaSpine` union landing, and the `conv` index-mover
    (recursively peeled). -/
inductive ParRedTInvSort
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    Expr Nat → Expr Nat → Type where
  /-- `refl` and `sortEq`: the target is a `=ₙ`-related sort. -/
  | eq (l₂ : Level) (T : Expr Nat) (h : eqN l l₂) :
      ParRedTInvSort PEq E n Γ l (.sort l₂) T
  /-- the `peq` leaf. -/
  | peq (q T : Expr Nat) (h : PEq Γ (.sort l) q T) :
      ParRedTInvSort PEq E n Γ l q T
  /-- `iotaSpine`: the source parallel-steps and the `DerivedIotaU`
      union fires on the stepped side. -/
  | iota (lhs' rhs T : Expr Nat)
      (hstep : ParRedT PEq E n Γ (.sort l) lhs' T)
      (hI : DerivedIotaU E lhs' rhs)
      (hred : HasTyT E n Γ lhs' T) (hrhs : HasTyT E n Γ rhs T) :
      ParRedTInvSort PEq E n Γ l rhs T
  /-- `conv`: the underlying inversion plus one `TyConvT` link. -/
  | conv (b A A' : Expr Nat)
      (h : ParRedTInvSort PEq E n Γ l b A)
      (hc : TyConvT E n Γ A A') :
      ParRedTInvSort PEq E n Γ l b A'

/-- A `ParRedT` step out of `.sort l` lands a `=ₙ`-related sort, the
    `peq` leaf, an `iotaSpine` union landing, or a `conv` wrap. -/
def parRedT_sort :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {l : Level} → a = .sort l → ParRedTInvSort PEq E n Γ l b T
  | _, _, _, _, .refl _ a A h, l, heq => by
      subst heq
      exact .eq l A (eqN_refl l)
  | _, _, _, _, .sortEq _ l₁ l₂ _ h _ _, l, heq => by
      injection heq with hl
      subst hl
      exact .eq l₂ _ h
  | _, _, _, _, .consts .., _, heq => nomatch heq
  | _, _, _, _, .bvarZeta .., _, heq => nomatch heq
  | _, _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, _, .app .., _, heq => nomatch heq
  | _, _, _, _, .beta .., _, heq => nomatch heq
  | _, _, _, _, .lam .., _, heq => nomatch heq
  | _, _, _, _, .pi .., _, heq => nomatch heq
  | _, _, _, _, .letE .., _, heq => nomatch heq
  | _, _, _, _, .zeta .., _, heq => nomatch heq
  | _, _, _, _, .iotaSpine _ lhs lhs' rhs T hstep hI hred hrhs, l, heq => by
      subst heq
      exact .iota lhs' rhs T hstep hI hred hrhs
  | _, _, _, _, .iotaStarK .., _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, _, .lit .., _, heq => nomatch heq
  | _, _, _, _, .eta .., _, heq => nomatch heq
  | _, _, _, _, .peq _ p q T h, l, heq => by
      subst heq
      exact .peq q T h
  | _, _, _, _, .conv _ _ _ A A' h hc, l, heq =>
      .conv _ A A' (parRedT_sort h heq) hc

/-- Inversion result at a `.pi A B` source. `congr` carries the `pi`
    arm's `ConvT` domain/codomain steps plus a `TyConvT` residue to the
    derivation's `T` (the `pi` arm lands at `.sort (.imax u v)` exactly;
    `refl`'s `T` arrives via `hasTyTInv_pi`). -/
inductive ParRedTInvPi
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) :
    Expr Nat → Expr Nat → Type where
  /-- `pi` congruence (and `refl` through the typing inversion). -/
  | congr (A' B' T : Expr Nat) (u v : Level)
      (hc : ConvT E n Γ A A' (.sort u))
      (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
      (hTy : TyConvT E n Γ (.sort (.imax u v)) T) :
      ParRedTInvPi PEq E n Γ A B (.pi A' B') T
  /-- the `peq` leaf. -/
  | peq (q T : Expr Nat) (h : PEq Γ (.pi A B) q T) :
      ParRedTInvPi PEq E n Γ A B q T
  /-- `iotaSpine` union landing. -/
  | iota (lhs' rhs T : Expr Nat)
      (hstep : ParRedT PEq E n Γ (.pi A B) lhs' T)
      (hI : DerivedIotaU E lhs' rhs)
      (hred : HasTyT E n Γ lhs' T) (hrhs : HasTyT E n Γ rhs T) :
      ParRedTInvPi PEq E n Γ A B rhs T
  /-- `conv` wrap, recursively peeled. -/
  | conv (b T T' : Expr Nat)
      (h : ParRedTInvPi PEq E n Γ A B b T)
      (hc : TyConvT E n Γ T T') :
      ParRedTInvPi PEq E n Γ A B b T'

/-- A `ParRedT` step out of `.pi A B` lands a `pi` congruence (domain
    and codomain moving by `ConvT`, the index at `.sort (.imax u v)`
    modulo `TyConvT`), the `peq` leaf, an `iotaSpine` landing, or a
    `conv` wrap. -/
def parRedT_pi :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {A B : Expr Nat} → a = .pi A B → ParRedTInvPi PEq E n Γ A B b T
  | _, _, _, _, .refl _ a _ h, A, B, heq => by
      subst heq
      let ⟨u, v, hA, hB, hTc⟩ := hasTyTInv_pi h rfl
      exact .congr A B _ u v (.refl _ _ _ hA) (.refl _ _ _ hB) hTc
  | _, _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, _, .lam .., _, _, heq => nomatch heq
  | _, _, _, _, .pi _ A₀ A' B₀ B' u v _ hc _ hcB _, A, B, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      exact .congr A' B' _ u v hc hcB (.refl _ _)
  | _, _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, _, .iotaSpine _ lhs lhs' rhs T hstep hI hred hrhs,
      A, B, heq => by
      subst heq
      exact .iota lhs' rhs T hstep hI hred hrhs
  | _, _, _, _, .iotaStarK .., _, _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, _, .eta .., _, _, heq => nomatch heq
  | _, _, _, _, .peq _ p q T h, A, B, heq => by
      subst heq
      exact .peq q T h
  | _, _, _, _, .conv _ _ _ A₀ A' h hc, A, B, heq =>
      .conv _ A₀ A' (parRedT_pi h heq) hc

/-- Inversion result at a `.lam A body` source. `congr` carries the
    `lam` arm's `ConvT` domain step and `ParRedT` body step plus a
    `TyConvT` residue to `T` (the `lam` arm lands at `.pi A B` exactly;
    `refl`'s `T` arrives via `hasTyTInv_lam`). -/
inductive ParRedTInvLam
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A body : Expr Nat) :
    Expr Nat → Expr Nat → Type where
  /-- `lam` congruence (and `refl` through the typing inversion). -/
  | congr (A' body' B T : Expr Nat) (u : Level)
      (hc : ConvT E n Γ A A' (.sort u))
      (hb : ParRedT PEq E n (.assumption A :: Γ) body body' B)
      (hTy : TyConvT E n Γ (.pi A B) T) :
      ParRedTInvLam PEq E n Γ A body (.lam A' body') T
  /-- the `peq` leaf. -/
  | peq (q T : Expr Nat) (h : PEq Γ (.lam A body) q T) :
      ParRedTInvLam PEq E n Γ A body q T
  /-- `iotaSpine` union landing. -/
  | iota (lhs' rhs T : Expr Nat)
      (hstep : ParRedT PEq E n Γ (.lam A body) lhs' T)
      (hI : DerivedIotaU E lhs' rhs)
      (hred : HasTyT E n Γ lhs' T) (hrhs : HasTyT E n Γ rhs T) :
      ParRedTInvLam PEq E n Γ A body rhs T
  /-- `eta` contraction — `hbody` exposes the expansion's shape
      (`body` is a family index, so the shape arrives as an
      equation); the function parallel-steps `f ⇒ f'` at the shared
      `.pi A B`. -/
  | eta (f f' B : Expr Nat)
      (hbody : body = .app (lift 0 1 f) (.bvar 0))
      (hf : ParRedT PEq E n Γ f f' (.pi A B)) :
      ParRedTInvLam PEq E n Γ A body f' (.pi A B)
  /-- `conv` wrap, recursively peeled. -/
  | conv (b T T' : Expr Nat)
      (h : ParRedTInvLam PEq E n Γ A body b T)
      (hc : TyConvT E n Γ T T') :
      ParRedTInvLam PEq E n Γ A body b T'

/-- A `ParRedT` step out of `.lam A body` lands a `lam` congruence
    (domain by `ConvT`, body by `ParRedT` under the left binder, the
    index `.pi A B` modulo `TyConvT`), the `peq` leaf, an `iotaSpine`
    landing, an `eta` contraction, or a `conv` wrap. -/
def parRedT_lam :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {A body : Expr Nat} → a = .lam A body →
    ParRedTInvLam PEq E n Γ A body b T
  | _, _, _, _, .refl _ a _ h, A, body, heq => by
      subst heq
      let ⟨u, B, hA, hb, hTc⟩ := hasTyTInv_lam h rfl
      exact .congr A body B _ u (.refl _ _ _ hA) (.refl _ _ _ hb) hTc
  | _, _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, _, .lam _ A₀ A' body₀ body' B u _ hc _ _ hb _,
      A, body, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      exact .congr A' body' B _ u hc hb (.refl _ _)
  | _, _, _, _, .pi .., _, _, heq => nomatch heq
  | _, _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, _, .iotaSpine _ lhs lhs' rhs T hstep hI hred hrhs,
      A, body, heq => by
      subst heq
      exact .iota lhs' rhs T hstep hI hred hrhs
  | _, _, _, _, .iotaStarK .., _, _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, _, .eta _ f f' A₀ B hf _, A, body, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      exact .eta f f' B rfl hf
  | _, _, _, _, .peq _ p q T h, A, body, heq => by
      subst heq
      exact .peq q T h
  | _, _, _, _, .conv _ _ _ A₀ A' h hc, A, body, heq =>
      .conv _ A₀ A' (parRedT_lam h heq) hc

/-- Inversion result at a constant-headed application spine
    `foldApps (.const r ls) xs`. Indexed by `(r, ls, xs, target, T)`;
    each constructor pins the index shape its arm determines — `delta`
    only at the bare const (`xs = []`), `iotaStarK` only at the
    synthesized `recCall` spine (the `r`/`ls` indices unify with the
    witness's head; `xs` carries the spine equation since append forms
    do not index-unify). -/
inductive ParRedTInvConst
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Nat → List Level → List (Expr Nat) → Expr Nat → Expr Nat → Type where
  /-- whole-spine componentwise congruence: `refl` (through
      `parRedArgsT_refl_spine`) and `consts` level-drift — the target
      is the same head at `=ₙ`-related levels over pointwise reducts. -/
  | congr (r : Nat) (ls ls' : List Level) (xs xs' : List (Expr Nat))
      (T : Expr Nat)
      (hls : eqNList ls ls') (ha : ParRedArgsT PEq E n Γ xs xs') :
      ParRedTInvConst PEq E n Γ r ls xs (foldApps (.const r ls') xs') T
  /-- last-argument congruence — the `app` arm verbatim at
      `xs = ys ++ [y]`: the head `foldApps (.const r ls) ys` steps by
      ANY route (the exposed `ParRedT` is the recursive handle), the
      argument steps at `A`. -/
  | deviate (r : Nat) (ls : List Level) (xs ys : List (Expr Nat))
      (y y' f' A B T₀ : Expr Nat) (v w : Level)
      (hxs : xs = ys ++ [y])
      (hf : ParRedT PEq E n Γ (foldApps (.const r ls) ys) f' T₀)
      (hc : TyConvT E n Γ T₀ (.pi A B))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyT E n Γ (instantiate0 y B) (.sort w))
      (ha : ParRedT PEq E n Γ y y' A)
      (hr : HasTyT E n Γ (.app f' y') (instantiate0 y B)) :
      ParRedTInvConst PEq E n Γ r ls xs (.app f' y') (instantiate0 y B)
  /-- δ on the bare const (`xs = []` — pinned as an index). -/
  | delta (r : Nat) (ls : List Level) (m : CheckedMember) (b T : Expr Nat)
      (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) :
      ParRedTInvConst PEq E n Γ r ls [] (instantiateLevels ls b) T
  /-- ι★K: the source is the synthesized recCall spine
      `recCall (.const w.recRef w.ls) w.preMajor major` — the head
      indices pin to `w.recRef`/`w.ls`; `hxs` carries the spine split
      (append forms do not index-unify). All K-gate premises verbatim. -/
  | iotaStarK (w : IotaWitness E) (xs : List (Expr Nat))
      (major Tm rhs T : Expr Nat) (rl : Level) (afs : Prop)
      (hxs : xs = w.preMajor ++ [major])
      (hrl : piBody w.famMember.mtype = .sort rl)
      (hsel : EliminationSelection rl w.nMinors afs .anySort)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hmk : HasTyT E n Γ (ctorMajor w) Tm)
      (hTm0 : HasTyT E n Γ Tm (.sort .zero))
      (hι : DerivedIotaU E (iotaLhsOf w) rhs)
      (hlι : HasTyT E n Γ (iotaLhsOf w) T)
      (hlhs : HasTyT E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major) T)
      (hrhs : HasTyT E n Γ rhs T) :
      ParRedTInvConst PEq E n Γ w.recRef w.ls xs rhs T
  /-- `iotaStarKEta`: the source is a partially applied recursor spine
      `foldApps (.const w.recRef w.ls) xs` whose η-expansion body matches
      `recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)`. -/
  | iotaStarKEta (w : IotaWitness E) (xs : List (Expr Nat))
      (A B Tm rhs : Expr Nat) (u rl : Level) (afs : Prop)
      (happ : recCall (.const w.recRef w.ls) w.preMajor (.bvar 0) =
        .app (lift 0 1 (foldApps (.const w.recRef w.ls) xs)) (.bvar 0))
      (hA : HasTyT E n Γ A (.sort u))
      (hf : HasTyT E n Γ (foldApps (.const w.recRef w.ls) xs) (.pi A B))
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
      ParRedTInvConst PEq E n Γ w.recRef w.ls xs (.lam A rhs) (.pi A B)
  /-- `iotaSpine`: the spine parallel-steps by `hstep` and the
      `DerivedIotaU` union fires on the stepped side. -/
  | iota (r : Nat) (ls : List Level) (xs : List (Expr Nat))
      (lhs' rhs T : Expr Nat)
      (hstep : ParRedT PEq E n Γ (foldApps (.const r ls) xs) lhs' T)
      (hI : DerivedIotaU E lhs' rhs)
      (hred : HasTyT E n Γ lhs' T) (hrhs : HasTyT E n Γ rhs T) :
      ParRedTInvConst PEq E n Γ r ls xs rhs T
  /-- the `peq` leaf. -/
  | peq (r : Nat) (ls : List Level) (xs : List (Expr Nat))
      (q T : Expr Nat)
      (h : PEq Γ (foldApps (.const r ls) xs) q T) :
      ParRedTInvConst PEq E n Γ r ls xs q T
  /-- `conv` wrap, recursively peeled. -/
  | conv (r : Nat) (ls : List Level) (xs : List (Expr Nat))
      (b A A' : Expr Nat)
      (h : ParRedTInvConst PEq E n Γ r ls xs b A)
      (hc : TyConvT E n Γ A A') :
      ParRedTInvConst PEq E n Γ r ls xs b A'

/-- Total inversion of a `ParRedT` step out of a constant-headed
    application spine — the typed `parRed_foldApps_const`: every arm
    classifies as componentwise congruence (`congr`), last-argument
    congruence (`deviate`), δ on the bare const (`delta`), the typed
    K-gate (`iotaStarK`), the union landing (`iota`), the `peq` leaf,
    or a `conv` wrap. Member-class refutations (constructor-headed
    spines can't `iotaStarK`, etc.) read the exposed fields; the
    general inversion stays premise-free. -/
def parRedT_foldApps_const :
    {Γ : LCtx} → {a b T : Expr Nat} → ParRedT PEq E n Γ a b T →
    {r : Nat} → {ls : List Level} → {xs : List (Expr Nat)} →
    a = foldApps (.const r ls) xs →
    ParRedTInvConst PEq E n Γ r ls xs b T
  | _, _, _, _, .refl _ a A h, r, ls, xs, heq => by
      subst heq
      exact .congr r ls ls xs xs A (eqNList_refl ls)
        (parRedArgsT_refl_spine xs h)
  | _, _, _, _, .sortEq .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .consts _ r0 ls0 ls' _ h _ _, r, ls, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact .congr r0 ls0 ls' [] [] _ h (.nil _)
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .bvarZeta .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .delta _ r0 ls0 m b0 _ hres hbody htr hlen hwf _ _,
      r, ls, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact .delta r0 ls0 m b0 _ hres hbody htr hlen hwf
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .app _ f f' a a' A B T₀ v w hf hc hB hTy ha hr,
      r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) y := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 ha0
          subst hf0
          subst a
          exact .deviate r ls _ ys y a' f' A B T₀ v w hsplit
            hf hc hB hTy ha hr
  | _, _, _, _, .beta _ A body _ arg _ _ _ _ _ _ _ _ _ _ _,
      r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, y, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) y := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 _
          exact absurd hf0.symm (foldApps_const_ne_lam ys)
  | _, _, _, _, .lam .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .pi .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .letE .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .zeta .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .iotaSpine _ lhs lhs' rhs T hstep hI hred hrhs,
      r, ls, xs, heq => by
      subst heq
      exact .iota r ls xs lhs' rhs T hstep hI hred hrhs
  | _, _, _, _, .iotaStarK _ w major Tm rhs T rl afs
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs,
      r, ls, xs, heq => by
      simp only [recCall] at heq
      let ⟨hrr, hll⟩ := head_eq_of_foldApps_const_eq heq
      subst hrr
      subst hll
      let hxs := (spine_eq_of_foldApps_const_eq heq).symm
      exact .iotaStarK w xs major Tm rhs T rl afs hxs
        hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs
  | _, _, _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs
      happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs,
      r, ls, xs, heq => by
      subst heq
      have hhd := (iotaStarKEta_head happ).1
      rw [appsSpine_foldApps_const] at hhd
      injection hhd with hrr hll
      subst hrr
      subst hll
      exact .iotaStarKEta w xs A B Tm rhs u rl afs
        happ hA hf hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs
  | _, _, _, _, .lit .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .eta .., r, ls, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, _, _, .peq _ p q T h, r, ls, xs, heq => by
      subst heq
      exact .peq r ls xs q T h
  | _, _, _, _, .conv _ _ _ A A' h hc, r, ls, xs, heq =>
      .conv r ls xs _ A A' (parRedT_foldApps_const h heq) hc

end Inversions

end Rcic.Declarative

#print axioms Rcic.Declarative.parRedArgsT_snoc
#print axioms Rcic.Declarative.parRedArgsT_refl_spine
#print axioms Rcic.Declarative.parRedT_sort
#print axioms Rcic.Declarative.parRedT_pi
#print axioms Rcic.Declarative.parRedT_lam
#print axioms Rcic.Declarative.parRedT_foldApps_const
