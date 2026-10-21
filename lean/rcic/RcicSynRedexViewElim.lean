import rcic.RcicSynRedexKind

/-!
# S15 — index-free β/ζ/δ redex-view inversions (ChatGPT #7373)

Spec: `research/rcic/sortrow/S15_REDEX_VIEW_ELIMINATION.md`. `closure_claim = 0`.

T13's wall: `RedexKindView c p` puts the original node `c` and the produced
domain typing `p` in its indices. For β/ζ/δ the types inside `c`/`p` carry
`instantiate0 …` / `instantiateLevels …`, so `cases v` on a view fixed to a
concrete redex forces unification on computed indices. This module adds an
**index-free elimination layer** — `RedexKindView`, `redexDom` and their
producers are untouched (additive only):

- `betaRhsPi`/`zetaRhsPi`/`deltaRhsPi` — thin adapters over the landed
  `instantiate_eq_pi`/`instantiateLevels_eq_pi` (S15 §2).
- `BetaFields`/`ZetaFields`/`DeltaFields`/`IotaFields` — plain records
  carrying the *original* node fields; `.node` rebuilds the constructor by
  rfl (S15 §3 — equations are never downgraded to same-type existence).
- `RootFields` + `inspectRoot` — a root tag read on the packed `CvPAny`
  while its indices are still variables (S15 §3).
- `ViewCase` + `viewFacts` — index-free facts: `f.original` is the packed
  node, `f.produced` the packed producer; both equations come out of the
  original definitions, no Π reader is run twice (S15 §4). ζ-under keeps
  the raw `TyP.lsub` producer exactly.
- `BetaCases`/`ZetaCases`/`DeltaCase` — Type-valued result families whose
  parameters are the plain record and the packed output (S15 §5).
- `redexKindView_beta_inv`/`_zeta_inv`/`_delta_inv` — the six-step recipe:
  `viewFacts` (no computed-index inversion), `cases` on the plain case,
  `inspectRoot` on the `original` equation, cross-tags die by constructor
  disjointness, the same tag yields a whole-record equation, `subst`, then
  the exact `hout` from the `produced` equation.

These inversions do **not** claim that `piInvP`'s output is bounded below
the original `N` — T6/T13's atom-bounded consumers still owe that proof
(S15 §7 / the spec's own limit). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A packed `TyP E n Γ domT (.sort α)` — heterogeneous domain/sort indices
    behind one constructor, the produced side of a `RedexKindView`. -/
inductive SortTyAny where
  | mk {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {domT : Expr Nat} {α : Level}
      (p : TyP E n Γ domT (.sort α)) : SortTyAny

/-! ## §2 — pure syntactic inversion on equation fields first -/

/-- β: the *displayed* rhs `instantiate0 arg body` is read back through
    `instantiate_eq_pi` — an equation field, never an inversion of the
    arbitrary instantiation function. -/
def betaRhsPi {rhs body arg A' B' : Expr Nat}
    (hcalc : rhs = instantiate0 arg body) (hpi : rhs = .pi A' B') :
    InstPi 0 arg body A' B' :=
  instantiate_eq_pi (hcalc.symm.trans hpi)

/-- ζ: same syntax (`instantiate0 value body`); the *typing context* stays
    the original `.letBinding` — the two producers are never merged. -/
def zetaRhsPi {rhs body value A' B' : Expr Nat}
    (hcalc : rhs = instantiate0 value body) (hpi : rhs = .pi A' B') :
    InstPi 0 value body A' B' :=
  instantiate_eq_pi (hcalc.symm.trans hpi)

/-- δ: the displayed rhs `instantiateLevels ls b` read back through
    `instantiateLevels_eq_pi`. -/
def deltaRhsPi {rhs b A' B' : Expr Nat} {ls : List Level}
    (hcalc : rhs = instantiateLevels ls b) (hpi : rhs = .pi A' B') :
    LinstPi ls b A' B' :=
  instantiateLevels_eq_pi (hcalc.symm.trans hpi)

/-! ## §3 — pack the original fields; `.node` is an rfl round-trip -/

/-- The original β node, all fields kept — never rebuilt from equations. -/
structure BetaFields where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  A : Expr Nat
  body : Expr Nat
  arg : Expr Nat
  B : Expr Nat
  u : Level
  hA : TyP E n Γ A (.sort u)
  hbody : TyP E n (.assumption A :: Γ) body B
  harg : TyP E n Γ arg A
  dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)
  dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)

/-- Rebuilds the original `CvP.beta` — an rfl consumer of constructor
    unfolding, never a re-proved equivalence. -/
def BetaFields.node (β : BetaFields) :
    CvP β.E β.n β.Γ (.app (.lam β.A β.body) β.arg)
      (instantiate0 β.arg β.body) (instantiate0 β.arg β.B) :=
  .beta β.E β.n β.Γ β.A β.body β.arg β.B β.u β.hA β.hbody β.harg β.dl β.dr

/-- The original ζ node. -/
structure ZetaFields where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  A : Expr Nat
  value : Expr Nat
  body : Expr Nat
  B : Expr Nat
  u : Level
  hA : TyP E n Γ A (.sort u)
  hv : TyP E n Γ value A
  hb : TyP E n (.letBinding A value :: Γ) body B
  dl : TyP E n Γ (.letE A value body) (instantiate0 value B)
  dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)

/-- Rebuilds the original `CvP.zeta`. -/
def ZetaFields.node (ζ : ZetaFields) :
    CvP ζ.E ζ.n ζ.Γ (.letE ζ.A ζ.value ζ.body)
      (instantiate0 ζ.value ζ.body) (instantiate0 ζ.value ζ.B) :=
  .zeta ζ.E ζ.n ζ.Γ ζ.A ζ.value ζ.body ζ.B ζ.u ζ.hA ζ.hv ζ.hb ζ.dl ζ.dr

/-- The original δ node (the stored body `b` and its member data included —
    the `instantiateLevels` indices stay equations on fields, never solved
    piece by piece). -/
structure DeltaFields where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  r : Nat
  ls : List Level
  m : CheckedMember
  b : Expr Nat
  hres : E.members r = some m
  hbody : m.body = some b
  htr : transparent m.mclass = true
  hlen : ls.length = m.arity
  hwf : levelsBounded n ls = true
  hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)
  dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)
  dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)

/-- Rebuilds the original `CvP.delta`. -/
def DeltaFields.node (δ : DeltaFields) :
    CvP δ.E δ.n δ.Γ (.const δ.r δ.ls)
      (instantiateLevels δ.ls δ.b) (instantiateLevels δ.ls δ.m.mtype) :=
  .delta δ.E δ.n δ.Γ δ.r δ.ls δ.m δ.b δ.hres δ.hbody δ.htr δ.hlen δ.hwf
    δ.hb δ.dl δ.dr

/-- The original ι node (packed for `ViewCase.iotaDirect`; ι's indices are
    already original fields so its direct inversion stays as #7351's). -/
structure IotaFields where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  lhs : Expr Nat
  rhs : Expr Nat
  T : Expr Nat
  h : DerivedIota E lhs rhs
  hlhs : TyP E n Γ lhs T
  hrhs : TyP E n Γ rhs T
  dl : TyP E n Γ lhs T
  dr : TyP E n Γ rhs T

/-- Rebuilds the original `CvP.iota`. -/
def IotaFields.node (ι : IotaFields) :
    CvP ι.E ι.n ι.Γ ι.lhs ι.rhs ι.T :=
  .iota ι.E ι.n ι.Γ ι.lhs ι.rhs ι.T ι.h ι.hlhs ι.hrhs ι.dl ι.dr

/-- §3 rfl round-trips: `.node` is the constructor built from the record's
    own fields — definitional, no semantic-equivalence lemma. -/
theorem betaFields_node (β : BetaFields) :
    β.node = .beta β.E β.n β.Γ β.A β.body β.arg β.B β.u β.hA β.hbody β.harg
      β.dl β.dr := rfl

/-- The ζ round-trip. -/
theorem zetaFields_node (ζ : ZetaFields) :
    ζ.node = .zeta ζ.E ζ.n ζ.Γ ζ.A ζ.value ζ.body ζ.B ζ.u ζ.hA ζ.hv ζ.hb
      ζ.dl ζ.dr := rfl

/-- The δ round-trip. -/
theorem deltaFields_node (δ : DeltaFields) :
    δ.node = .delta δ.E δ.n δ.Γ δ.r δ.ls δ.m δ.b δ.hres δ.hbody δ.htr δ.hlen
      δ.hwf δ.hb δ.dl δ.dr := rfl

/-- The ι round-trip. -/
theorem iotaFields_node (ι : IotaFields) :
    ι.node = .iota ι.E ι.n ι.Γ ι.lhs ι.rhs ι.T ι.h ι.hlhs ι.hrhs ι.dl ι.dr :=
  rfl

/-- A root tag with no dependent result index (S15 §3): the same tag is a
    plain constructor over a plain record, so `RootFields.beta β' = .beta β`
    injects to the whole-record equation `β' = β` — never per-field HEq. -/
inductive RootFields where
  | beta : BetaFields → RootFields
  | zeta : ZetaFields → RootFields
  | delta : DeltaFields → RootFields
  | other : CvPAny → RootFields

/-- `inspectRoot` pattern-matches the original `CvP` **while its indices are
    still variables** (unpacked from `CvPAny` — `cases` on the `c` inside
    `.mk c` gives every constructor its own branch with fresh index
    variables), then packs. Nothing is fixed to β first, so no dependent
    `cases` on computed indices is ever attempted; every other node keeps
    the *original* packing `ca`. -/
def inspectRoot (ca : CvPAny) : RootFields := by
  cases h : ca with
  | mk c =>
    cases c with
    | beta =>
        rename_i E n Γ A body arg B u hA hbody harg dl dr
        exact .beta ⟨E, n, Γ, A, body, arg, B, u, hA, hbody, harg, dl, dr⟩
    | zeta =>
        rename_i E n Γ A value body B u hA hv hb dl dr
        exact .zeta ⟨E, n, Γ, A, value, body, B, u, hA, hv, hb, dl, dr⟩
    | delta =>
        rename_i E n Γ r ls m b hbody htr hlen hres hwf hb dl dr
        exact .delta ⟨E, n, Γ, r, ls, m, b, hres, hbody, htr, hlen, hwf, hb,
          dl, dr⟩
    | _ => exact .other ca

/-- §3 tag equations — each root's `inspectRoot` is the literal tag of the
    record (structure eta: the packed fields are the record itself). -/
theorem inspectRoot_beta (β : BetaFields) :
    inspectRoot (.mk β.node) = .beta β := rfl

/-- The ζ tag equation. -/
theorem inspectRoot_zeta (ζ : ZetaFields) :
    inspectRoot (.mk ζ.node) = .zeta ζ := rfl

/-- The δ tag equation. -/
theorem inspectRoot_delta (δ : DeltaFields) :
    inspectRoot (.mk δ.node) = .delta δ := rfl

/-- Every other node — ι included — is `.other` of its own packing. -/
theorem inspectRoot_other (ι : IotaFields) :
    inspectRoot (.mk ι.node) = .other (.mk ι.node) := rfl

/-! ## §4 — index-free facts about the original view -/

/-- A plain case for an original `RedexKindView`: `c`/`p` are not dependent
    indices; the equation fields relate only original values. -/
inductive ViewCase where
  | betaUnder (β : BetaFields) (A₀ B₀ : Expr Nat) (hbodyEq : β.body = .pi A₀ B₀)
  | betaHit (β : BetaFields) (A' B' : Expr Nat) (hbodyZero : β.body = .bvar 0)
      (hargPi : β.arg = .pi A' B')
  | zetaUnder (ζ : ZetaFields) (A₀ B₀ : Expr Nat) (hbodyEq : ζ.body = .pi A₀ B₀)
  | zetaHit (ζ : ZetaFields) (A' B' : Expr Nat) (hbodyZero : ζ.body = .bvar 0)
      (hvaluePi : ζ.value = .pi A' B')
  | deltaRhs (δ : DeltaFields) (A' B' : Expr Nat)
      (hRhsPi : instantiateLevels δ.ls δ.b = .pi A' B')
  | iotaDirect (ι : IotaFields) (A' B' : Expr Nat) (hRhsPi : ι.rhs = .pi A' B')

/-- The packed original node the case came from. -/
def ViewCase.original : ViewCase → CvPAny
  | .betaUnder β _ _ _ => .mk β.node
  | .betaHit β _ _ _ _ => .mk β.node
  | .zetaUnder ζ _ _ _ => .mk ζ.node
  | .zetaHit ζ _ _ _ _ => .mk ζ.node
  | .deltaRhs δ _ _ _ => .mk δ.node
  | .iotaDirect ι _ _ _ => .mk ι.node

/-- The packed produced domain typing — the **original** producer in each
    branch (S15 §4): β-under keeps `k3DomInst (piInvP … hbody …).hA hA harg`;
    β-hit the `piInvP` domain of the original `harg`; ζ-under the raw
    `TyP.lsub` and its casts (never a swapped `.assumption`/`letSub`); ζ-hit
    the `piInvP` domain of `hv`; δ the `piInvP` domain of the original `hb`
    after the original `hdom` cast — never a second unfolding; ι `hrhs`. -/
def ViewCase.produced : ViewCase → SortTyAny
  | .betaUnder β _ _ hbodyEq =>
      .mk (k3DomInst
        (piInvP (envExt_refl β.E) (tyCast hbodyEq rfl β.hbody) rfl).hA
        β.hA β.harg)
  | .betaHit β _ _ _ hargPi =>
      .mk ((piInvP (envExt_refl β.E) (tyCast hargPi rfl β.harg) rfl).hA)
  | .zetaUnder ζ _ _ hbodyEq =>
      .mk (TyP.lsub ζ.E ζ.n (.letBinding ζ.A ζ.value :: ζ.Γ) _ _ ζ.A ζ.value 0
        ζ.u
        (piInvP (envExt_refl ζ.E) (tyCast hbodyEq rfl ζ.hb) rfl).hA
        List.getElem?_cons_zero
        (tyCast (lift_zero_idx 0 ζ.value).symm (lift_zero_idx 0 ζ.A).symm ζ.hv)
        (tyCast (lift_zero_idx 0 ζ.A).symm rfl ζ.hA))
  | .zetaHit ζ _ _ _ hvaluePi =>
      .mk ((piInvP (envExt_refl ζ.E) (tyCast hvaluePi rfl ζ.hv) rfl).hA)
  | .deltaRhs δ _ _ hRhsPi =>
      .mk ((piInvP (envExt_refl δ.E) (tyCast hRhsPi rfl δ.hb) rfl).hA)
  | .iotaDirect ι _ _ hRhsPi =>
      .mk ((piInvP (envExt_refl ι.E) (tyCast hRhsPi rfl ι.hrhs) rfl).hA)

/-- `viewFacts` (S15 §4): recurses on `v` while `c`/`p` are still variables —
    the returned case's `original` is the packed node and its `produced` the
    packed producer, both by the original definitions. No Π reader runs
    twice, no `hA` is rebuilt, no provenance changes. -/
def viewFacts {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T domT : Expr Nat} {α : Level}
    {c : CvP E n Γ lhs rhs T} {p : TyP E n Γ domT (.sort α)} :
    RedexKindView c p →
    {f : ViewCase // f.original = .mk c ∧ f.produced = .mk p}
  | @RedexKindView.betaUnder _ _ _ A body arg B u A₀ B₀
        hA hbody harg dl dr hdom =>
      ⟨.betaUnder ⟨_, _, _, A, body, arg, B, u, hA, hbody, harg, dl, dr⟩
        A₀ B₀ hdom, rfl, rfl⟩
  | @RedexKindView.betaHit _ _ _ A body arg B u A' B'
        hA hbody harg dl dr hdom hargPi =>
      ⟨.betaHit ⟨_, _, _, A, body, arg, B, u, hA, hbody, harg, dl, dr⟩
        A' B' hdom hargPi, rfl, rfl⟩
  | @RedexKindView.zetaUnder _ _ _ A value body B u A₀ B₀
        hA hv hb dl dr hdom =>
      ⟨.zetaUnder ⟨_, _, _, A, value, body, B, u, hA, hv, hb, dl, dr⟩
        A₀ B₀ hdom, rfl, rfl⟩
  | @RedexKindView.zetaHit _ _ _ A value body B u A' B'
        hA hv hb dl dr hdom hvPi =>
      ⟨.zetaHit ⟨_, _, _, A, value, body, B, u, hA, hv, hb, dl, dr⟩
        A' B' hdom hvPi, rfl, rfl⟩
  | @RedexKindView.deltaRhs _ _ _ r ls m b A' B'
        hres hbody htr hlen hwf hb dl dr hdom =>
      ⟨.deltaRhs ⟨_, _, _, r, ls, m, b, hres, hbody, htr, hlen, hwf, hb, dl,
        dr⟩ A' B' hdom, rfl, rfl⟩
  | @RedexKindView.iotaDirect _ _ _ lhs rhs T A' B' h hlhs hrhs dl dr hdom =>
      ⟨.iotaDirect ⟨_, _, _, lhs, rhs, T, h, hlhs, hrhs, dl, dr⟩
        A' B' hdom, rfl, rfl⟩

/-! ## §5 — the three inversions -/

/-- β case family: the under/hit payloads plus `hout` — the output pack is
    literally the original producer's pack, never an ∃-weakened binding. -/
inductive BetaCases (β : BetaFields) (out : SortTyAny) : Type where
  | under (A₀ B₀ : Expr Nat) (hbodyEq : β.body = .pi A₀ B₀)
      (hout : out = .mk (k3DomInst
        (piInvP (envExt_refl β.E) (tyCast hbodyEq rfl β.hbody) rfl).hA
        β.hA β.harg)) : BetaCases β out
  | hit (A' B' : Expr Nat) (hbodyZero : β.body = .bvar 0)
      (hargPi : β.arg = .pi A' B')
      (hout : out = .mk
        ((piInvP (envExt_refl β.E) (tyCast hargPi rfl β.harg) rfl).hA)) :
      BetaCases β out

/-- ζ case family — under keeps the raw `TyP.lsub` producer exactly. -/
inductive ZetaCases (ζ : ZetaFields) (out : SortTyAny) : Type where
  | under (A₀ B₀ : Expr Nat) (hbodyEq : ζ.body = .pi A₀ B₀)
      (hout : out = .mk (TyP.lsub ζ.E ζ.n
        (.letBinding ζ.A ζ.value :: ζ.Γ) _ _ ζ.A ζ.value 0 ζ.u
        (piInvP (envExt_refl ζ.E) (tyCast hbodyEq rfl ζ.hb) rfl).hA
        List.getElem?_cons_zero
        (tyCast (lift_zero_idx 0 ζ.value).symm (lift_zero_idx 0 ζ.A).symm
          ζ.hv)
        (tyCast (lift_zero_idx 0 ζ.A).symm rfl ζ.hA))) : ZetaCases ζ out
  | hit (A' B' : Expr Nat) (hbodyZero : ζ.body = .bvar 0)
      (hvaluePi : ζ.value = .pi A' B')
      (hout : out = .mk
        ((piInvP (envExt_refl ζ.E) (tyCast hvaluePi rfl ζ.hv) rfl).hA)) :
      ZetaCases ζ out

/-- δ case family — the `piInvP` domain of the original `hb` after the
    original `hdom` cast. -/
inductive DeltaCase (δ : DeltaFields) (out : SortTyAny) : Type where
  | mk (A' B' : Expr Nat)
      (hdom : instantiateLevels δ.ls δ.b = .pi A' B')
      (hout : out = .mk
        ((piInvP (envExt_refl δ.E) (tyCast hdom rfl δ.hb) rfl).hA)) :
      DeltaCase δ out

/-- β inversion (S15 §5): `viewFacts` inverts no computed index; the plain
    `f` is cased; `inspectRoot` reads the `original` equation — a different
    root tag dies by constructor disjointness, the same tag yields the
    whole-record `β' = β`; `subst`; the `produced` equation is the exact
    `hout`. (`def`, not `theorem`: the result family is `Type`-valued.) -/
def redexKindView_beta_inv {β : BetaFields} {domT : Expr Nat} {α : Level}
    {p : TyP β.E β.n β.Γ domT (.sort α)}
    (v : RedexKindView β.node p) : BetaCases β (.mk p) := by
  obtain ⟨f, horig, hprod⟩ := viewFacts v
  cases f with
  | betaUnder β' A₀ B₀ hbodyEq =>
      have h : RootFields.beta β' = RootFields.beta β :=
        congrArg inspectRoot horig
      have hβ : β' = β := RootFields.beta.inj h
      subst hβ
      exact .under A₀ B₀ hbodyEq hprod.symm
  | betaHit β' A' B' hbodyZero hargPi =>
      have h : RootFields.beta β' = RootFields.beta β :=
        congrArg inspectRoot horig
      have hβ : β' = β := RootFields.beta.inj h
      subst hβ
      exact .hit A' B' hbodyZero hargPi hprod.symm
  | zetaUnder ζ _ _ _ =>
      have h : RootFields.zeta ζ = RootFields.beta β :=
        congrArg inspectRoot horig
      cases h
  | zetaHit ζ _ _ _ _ =>
      have h : RootFields.zeta ζ = RootFields.beta β :=
        congrArg inspectRoot horig
      cases h
  | deltaRhs δ _ _ _ =>
      have h : RootFields.delta δ = RootFields.beta β :=
        congrArg inspectRoot horig
      cases h
  | iotaDirect ι _ _ _ =>
      have h : RootFields.other (.mk ι.node) = RootFields.beta β :=
        congrArg inspectRoot horig
      cases h

/-- ζ inversion — same recipe; ζ-under's `hout` keeps the raw `lsub`
    producer. (`def`, not `theorem`: `ZetaCases` is `Type`-valued.) -/
def redexKindView_zeta_inv {ζ : ZetaFields} {domT : Expr Nat} {α : Level}
    {p : TyP ζ.E ζ.n ζ.Γ domT (.sort α)}
    (v : RedexKindView ζ.node p) : ZetaCases ζ (.mk p) := by
  obtain ⟨f, horig, hprod⟩ := viewFacts v
  cases f with
  | betaUnder β _ _ _ =>
      have h : RootFields.beta β = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      cases h
  | betaHit β _ _ _ _ =>
      have h : RootFields.beta β = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      cases h
  | zetaUnder ζ' A₀ B₀ hbodyEq =>
      have h : RootFields.zeta ζ' = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      have hζ : ζ' = ζ := RootFields.zeta.inj h
      subst hζ
      exact .under A₀ B₀ hbodyEq hprod.symm
  | zetaHit ζ' A' B' hbodyZero hvaluePi =>
      have h : RootFields.zeta ζ' = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      have hζ : ζ' = ζ := RootFields.zeta.inj h
      subst hζ
      exact .hit A' B' hbodyZero hvaluePi hprod.symm
  | deltaRhs δ _ _ _ =>
      have h : RootFields.delta δ = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      cases h
  | iotaDirect ι _ _ _ =>
      have h : RootFields.other (.mk ι.node) = RootFields.zeta ζ :=
        congrArg inspectRoot horig
      cases h

/-- δ inversion — same recipe; the produced pack is the original `hb`'s
    `piInvP` domain after the original cast. (`def`, not `theorem`:
    `DeltaCase` is `Type`-valued.) -/
def redexKindView_delta_inv {δ : DeltaFields} {domT : Expr Nat}
    {α : Level} {p : TyP δ.E δ.n δ.Γ domT (.sort α)}
    (v : RedexKindView δ.node p) : DeltaCase δ (.mk p) := by
  obtain ⟨f, horig, hprod⟩ := viewFacts v
  cases f with
  | betaUnder β _ _ _ =>
      have h : RootFields.beta β = RootFields.delta δ :=
        congrArg inspectRoot horig
      cases h
  | betaHit β _ _ _ _ =>
      have h : RootFields.beta β = RootFields.delta δ :=
        congrArg inspectRoot horig
      cases h
  | zetaUnder ζ _ _ _ =>
      have h : RootFields.zeta ζ = RootFields.delta δ :=
        congrArg inspectRoot horig
      cases h
  | zetaHit ζ _ _ _ _ =>
      have h : RootFields.zeta ζ = RootFields.delta δ :=
        congrArg inspectRoot horig
      cases h
  | deltaRhs δ' A' B' hRhsPi =>
      have h : RootFields.delta δ' = RootFields.delta δ :=
        congrArg inspectRoot horig
      have hδ : δ' = δ := RootFields.delta.inj h
      subst hδ
      exact .mk A' B' hRhsPi hprod.symm
  | iotaDirect ι _ _ _ =>
      have h : RootFields.other (.mk ι.node) = RootFields.delta δ :=
        congrArg inspectRoot horig
      cases h

/-! ## §6 — rfl equations into `viewFacts` and the exact-binding control -/

/-- β-under: the view's case is the node's own fields; the produced pack is
    the original `k3DomInst` producer — both by `rfl`. -/
theorem viewFacts_betaUnder {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {A₀ B₀ : Expr Nat}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    (hdom : body = .pi A₀ B₀) :
    viewFacts (@RedexKindView.betaUnder E n Γ A body arg B u A₀ B₀
        hA hbody harg dl dr hdom) =
      ⟨.betaUnder ⟨E, n, Γ, A, body, arg, B, u, hA, hbody, harg, dl, dr⟩
        A₀ B₀ hdom, rfl, rfl⟩ := rfl

/-- β-hit: same rfl read. -/
theorem viewFacts_betaHit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {A' B' : Expr Nat}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    (hdom : body = .bvar 0) (hargPi : arg = .pi A' B') :
    viewFacts (@RedexKindView.betaHit E n Γ A body arg B u A' B'
        hA hbody harg dl dr hdom hargPi) =
      ⟨.betaHit ⟨E, n, Γ, A, body, arg, B, u, hA, hbody, harg, dl, dr⟩
        A' B' hdom hargPi, rfl, rfl⟩ := rfl

/-- ζ-under: same rfl read — `hb` is the `letBinding`-context field. -/
theorem viewFacts_zetaUnder {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} {A₀ B₀ : Expr Nat}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
    {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
    (hdom : body = .pi A₀ B₀) :
    viewFacts (@RedexKindView.zetaUnder E n Γ A value body B u A₀ B₀
        hA hv hb dl dr hdom) =
      ⟨.zetaUnder ⟨E, n, Γ, A, value, body, B, u, hA, hv, hb, dl, dr⟩
        A₀ B₀ hdom, rfl, rfl⟩ := rfl

/-- ζ-hit: same rfl read. -/
theorem viewFacts_zetaHit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} {A' B' : Expr Nat}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {dl : TyP E n Γ (.letE A value body) (instantiate0 value B)}
    {dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)}
    (hdom : body = .bvar 0) (hvPi : value = .pi A' B') :
    viewFacts (@RedexKindView.zetaHit E n Γ A value body B u A' B'
        hA hv hb dl dr hdom hvPi) =
      ⟨.zetaHit ⟨E, n, Γ, A, value, body, B, u, hA, hv, hb, dl, dr⟩
        A' B' hdom hvPi, rfl, rfl⟩ := rfl

/-- δ: same rfl read — the stored body's own `hb`. -/
theorem viewFacts_deltaRhs {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b A' B' : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    (hdom : instantiateLevels ls b = .pi A' B') :
    viewFacts (@RedexKindView.deltaRhs E n Γ r ls m b A' B'
        hres hbody htr hlen hwf hb dl dr hdom) =
      ⟨.deltaRhs ⟨E, n, Γ, r, ls, m, b, hres, hbody, htr, hlen, hwf, hb, dl,
        dr⟩ A' B' hdom, rfl, rfl⟩ := rfl

/-- ι: same rfl read — `hrhs` direct. -/
theorem viewFacts_iotaDirect {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T A' B' : Expr Nat} {h : DerivedIota E lhs rhs}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
    (hdom : rhs = .pi A' B') :
    viewFacts (@RedexKindView.iotaDirect E n Γ lhs rhs T A' B'
        h hlhs hrhs dl dr hdom) =
      ⟨.iotaDirect ⟨E, n, Γ, lhs, rhs, T, h, hlhs, hrhs, dl, dr⟩
        A' B' hdom, rfl, rfl⟩ := rfl

/-- Exact round-trip of the original producer output — β-under. -/
theorem betaUnder_produced (β : BetaFields) {A₀ B₀ : Expr Nat}
    (hdom : β.body = .pi A₀ B₀) :
    ViewCase.produced (.betaUnder β A₀ B₀ hdom) =
      .mk (k3DomInst
        (piInvP (envExt_refl β.E) (tyCast hdom rfl β.hbody) rfl).hA
        β.hA β.harg) := rfl

/-- β-hit: the producer is the `piInvP` domain of the original `harg`. -/
theorem betaHit_produced (β : BetaFields) {A' B' : Expr Nat}
    (hdom : β.body = .bvar 0) (hargPi : β.arg = .pi A' B') :
    ViewCase.produced (.betaHit β A' B' hdom hargPi) =
      .mk ((piInvP (envExt_refl β.E) (tyCast hargPi rfl β.harg) rfl).hA) :=
  rfl

/-- ζ-under: the producer is the raw `TyP.lsub` of the `letBinding`-context
    `hb` — kept exactly. -/
theorem zetaUnder_produced (ζ : ZetaFields) {A₀ B₀ : Expr Nat}
    (hdom : ζ.body = .pi A₀ B₀) :
    ViewCase.produced (.zetaUnder ζ A₀ B₀ hdom) =
      .mk (TyP.lsub ζ.E ζ.n (.letBinding ζ.A ζ.value :: ζ.Γ) _ _ ζ.A ζ.value
        0 ζ.u
        (piInvP (envExt_refl ζ.E) (tyCast hdom rfl ζ.hb) rfl).hA
        List.getElem?_cons_zero
        (tyCast (lift_zero_idx 0 ζ.value).symm (lift_zero_idx 0 ζ.A).symm
          ζ.hv)
        (tyCast (lift_zero_idx 0 ζ.A).symm rfl ζ.hA)) := rfl

/-- ζ-hit: the producer is the `piInvP` domain of the original `hv`. -/
theorem zetaHit_produced (ζ : ZetaFields) {A' B' : Expr Nat}
    (hdom : ζ.body = .bvar 0) (hvaluePi : ζ.value = .pi A' B') :
    ViewCase.produced (.zetaHit ζ A' B' hdom hvaluePi) =
      .mk ((piInvP (envExt_refl ζ.E) (tyCast hvaluePi rfl ζ.hv) rfl).hA) :=
  rfl

/-- δ: the producer is the `piInvP` domain of the original `hb` after the
    original `hdom` cast — the same stored body, never a second unfolding. -/
theorem deltaRhs_produced (δ : DeltaFields) {A' B' : Expr Nat}
    (hdom : instantiateLevels δ.ls δ.b = .pi A' B') :
    ViewCase.produced (.deltaRhs δ A' B' hdom) =
      .mk ((piInvP (envExt_refl δ.E) (tyCast hdom rfl δ.hb) rfl).hA) := rfl

/-- ι: the producer is the `piInvP` domain of the original `hrhs`. -/
theorem iotaDirect_produced (ι : IotaFields) {A' B' : Expr Nat}
    (hdom : ι.rhs = .pi A' B') :
    ViewCase.produced (.iotaDirect ι A' B' hdom) =
      .mk ((piInvP (envExt_refl ι.E) (tyCast hdom rfl ι.hrhs) rfl).hA) := rfl

/-- §6 control — exact output/source binding (a swapped same-judgment
    `hbody`/`hb` is not accepted): for any `RedexKindView` at node `c`,
    `viewFacts` packs *that* node's own fields — `inspectRoot` of the
    returned case's `original` is literally `inspectRoot (.mk c)`, and the
    `produced` pack is literally `.mk p`. A `BetaFields`/`ZetaFields`/
    `DeltaFields` that carried a different derivation of the same judgment
    is a different record: `inspectRoot` tags it `.beta β'`/`.zeta ζ'`/
    `.delta δ'`, and the elimination returns `BetaCases β'`/`ZetaCases ζ'`/
    `DeltaCase δ'` — never `BetaCases β`/`ZetaCases ζ`/`DeltaCase δ`. -/
theorem viewFacts_source_exact {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T domT : Expr Nat} {α : Level}
    {c : CvP E n Γ lhs rhs T} {p : TyP E n Γ domT (.sort α)}
    (v : RedexKindView c p) :
    inspectRoot (viewFacts v).1.original = inspectRoot (.mk c) ∧
      (viewFacts v).1.produced = .mk p :=
  ⟨congrArg inspectRoot (viewFacts v).2.1, (viewFacts v).2.2⟩

/-- The β specialization of the same binding: the returned case's original
    inspects to literally `.beta β` — the whole record (`hbody`, `dl`, `dr`
    included), so a node carrying a *different* same-judgment `hbody` is a
    different record and can never pass this tag. -/
theorem redexKindView_beta_inv_exact_root {β : BetaFields} {domT : Expr Nat}
    {α : Level} {p : TyP β.E β.n β.Γ domT (.sort α)}
    (v : RedexKindView β.node p) :
    inspectRoot (viewFacts v).1.original = .beta β :=
  congrArg inspectRoot (viewFacts v).2.1

/-- The ζ specialization — the whole `letBinding`-context record is the tag. -/
theorem redexKindView_zeta_inv_exact_root {ζ : ZetaFields} {domT : Expr Nat}
    {α : Level} {p : TyP ζ.E ζ.n ζ.Γ domT (.sort α)}
    (v : RedexKindView ζ.node p) :
    inspectRoot (viewFacts v).1.original = .zeta ζ :=
  congrArg inspectRoot (viewFacts v).2.1

/-- The δ specialization — the whole stored-body record is the tag. -/
theorem redexKindView_delta_inv_exact_root {δ : DeltaFields}
    {domT : Expr Nat} {α : Level}
    {p : TyP δ.E δ.n δ.Γ domT (.sort α)}
    (v : RedexKindView δ.node p) :
    inspectRoot (viewFacts v).1.original = .delta δ :=
  congrArg inspectRoot (viewFacts v).2.1

end Rcic.Syn

#print axioms Rcic.Syn.betaRhsPi
#print axioms Rcic.Syn.zetaRhsPi
#print axioms Rcic.Syn.deltaRhsPi
#print axioms Rcic.Syn.BetaFields.node
#print axioms Rcic.Syn.ZetaFields.node
#print axioms Rcic.Syn.DeltaFields.node
#print axioms Rcic.Syn.IotaFields.node
#print axioms Rcic.Syn.betaFields_node
#print axioms Rcic.Syn.zetaFields_node
#print axioms Rcic.Syn.deltaFields_node
#print axioms Rcic.Syn.iotaFields_node
#print axioms Rcic.Syn.inspectRoot
#print axioms Rcic.Syn.inspectRoot_beta
#print axioms Rcic.Syn.inspectRoot_zeta
#print axioms Rcic.Syn.inspectRoot_delta
#print axioms Rcic.Syn.inspectRoot_other
#print axioms Rcic.Syn.ViewCase.original
#print axioms Rcic.Syn.ViewCase.produced
#print axioms Rcic.Syn.viewFacts
#print axioms Rcic.Syn.redexKindView_beta_inv
#print axioms Rcic.Syn.redexKindView_zeta_inv
#print axioms Rcic.Syn.redexKindView_delta_inv
#print axioms Rcic.Syn.viewFacts_betaUnder
#print axioms Rcic.Syn.viewFacts_betaHit
#print axioms Rcic.Syn.viewFacts_zetaUnder
#print axioms Rcic.Syn.viewFacts_zetaHit
#print axioms Rcic.Syn.viewFacts_deltaRhs
#print axioms Rcic.Syn.viewFacts_iotaDirect
#print axioms Rcic.Syn.betaUnder_produced
#print axioms Rcic.Syn.betaHit_produced
#print axioms Rcic.Syn.zetaUnder_produced
#print axioms Rcic.Syn.zetaHit_produced
#print axioms Rcic.Syn.deltaRhs_produced
#print axioms Rcic.Syn.iotaDirect_produced
#print axioms Rcic.Syn.viewFacts_source_exact
#print axioms Rcic.Syn.redexKindView_beta_inv_exact_root
#print axioms Rcic.Syn.redexKindView_zeta_inv_exact_root
#print axioms Rcic.Syn.redexKindView_delta_inv_exact_root
