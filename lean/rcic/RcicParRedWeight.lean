/-
RCIC ParRed, piece 3 of 7: the const-preimage lemmas and the v2
weight measures.

`parRed_const` / `parRed_lam_app` / `parRed_letE` (const preimage of
sorts), `exprSize` and its arithmetic, the mutual `parRedW` /
`parRedArgsW` / `parRedCtxW` derivation weights with their
positivity, `letsCount` / `getLet`.  These are the `termination_by`
measures of `RcicParRedSubst` and of the pairwise diamond, so this
piece is loaded directly after `RcicParRedIota` rather than at its
original position in the middle of the complete-development
narrative: nothing in it mentions any name from the sort-wall piece.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.
-/
import rcic.RcicParRedCore
import rcic.RcicParRedIota

namespace Rcic.Declarative

/-! ### Attempt 16: const preimage of sorts (`def T := Sort u`).

`a` is generalized so iota/iotaSpine do not unify with `const`
during dependent elim (same pattern as `parRed_sort`). -/

/-- Invert ParRed of a constant: stay a constant (levels `=ₙ`), or
one-shot transparent delta.

M-003 (00 §20.6 RULE CHANGES). The delta summand's last component moved
    old:  (e = body)
    new:  (e = instantiateLevels ls body)
because `ParRed.delta` now concludes at `instantiateLevels ls b`. This
is not a weakening: the summand still binds the STORED body (`m.body =
some body`) and then says how the reduct is built from it, which is
strictly more information than the old form asserted; at `ls = []`
`instantiateLevels_nil` recovers the old reading verbatim, and under
`EnvWf` that is the only case (`envWf_body_arity_zero`). -/
def parRed_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {a e : Expr Nat} :
    ParRed E n Γ a e → a = .const r ls →
    (Σ' ls', (e = .const r ls') ×' eqNList ls ls') ⊕'
    (Σ' (m : CheckedMember) (body : Expr Nat),
      (E.members r = some m) ×' (m.body = some body) ×'
        (transparent m.mclass = true) ×' (e = instantiateLevels ls body))
  | .refl _ _, ha => by
      subst ha
      exact .inl ⟨ls, rfl, eqNList_refl ls⟩
  | .consts _ _ _ ls' q, ha => by
      injection ha with hr hls
      subst hr
      subst hls
      exact .inl ⟨ls', rfl, q⟩
  | .delta _ _ _ m body hres hbody htr, ha => by
      injection ha with hr hls
      subst hr
      subst hls
      exact .inr ⟨m, body, hres, hbody, htr, rfl⟩
  | .sortEq _ _ _ _, ha => nomatch ha
  | .bvarZeta _ _ _ _ _ _ _, ha => nomatch ha
  | .app _ _ _ _ _ _ _, ha => nomatch ha
  | .beta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .lam _ _ _ _ _ _ _, ha => nomatch ha
  | .pi _ _ _ _ _ _ _, ha => nomatch ha
  | .letE _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .zeta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, ha =>
      (foldApps_snoc_ne_const (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre ha).elim
  | .lit _ _, ha => nomatch ha

/-- A star from `const r` (any universe args) to a sort, when the
stored body is already a sort: the unique unfold is that universe
(`=ₙ`), READ THROUGH the redex's own level list. `a`/`e` generalized so
`refl` does not hide `const ≠ sort`. Peel consts, then one delta;
`parRed_sort` + `parRedStar_sort_eq`.

M-003 (00 §20.6 RULE CHANGES). The conclusion moved
    old:  eqN u w
    new:  eqN (instLevel ls u) w
because 02 §9's delta reduct of a stored `.sort u` body is
`.sort (instLevel ls u)`, not `.sort u`. The old form is the `ls = []`
instance (`instLevel_nil`), which under `EnvWf` is the only reachable
one (`envWf_body_arity_zero`); as a statement about an arbitrary
`ResolvedEnv` the old form is now FALSE (a stored body `.sort (param 0)`
unfolds to `.sort ls[0]`), so this is a correction, not a weakening.
The const-peel arm now composes the level drift with `instLevel_eqNList`
instead of discarding it. -/
def parRedStar_const_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {a e : Expr Nat} {u w : Level}
    {m : CheckedMember}
    (h : ParRedStar E n Γ a e)
    (ha : a = .const r ls)
    (he : e = .sort w)
    (hres : E.members r = some m)
    (hbody : m.body = some (.sort u))
    (_htr : transparent m.mclass = true) : eqN (instLevel ls u) w :=
  match h with
  | .refl _ _ => nomatch (ha.symm.trans he)
  | .tail h0 hs =>
      match parRed_const h0 ha with
      | .inl ⟨_ls', heq, q⟩ =>
          eqN_trans (instLevel_eqNList q u)
            (parRedStar_const_body_sort hs heq he hres hbody _htr)
      | .inr ⟨m', body, hres', hbody', _htr', heq⟩ => by
          have hm : m' = m := Option.some.inj (hres'.symm.trans hres)
          subst hm
          have hbod : body = .sort u :=
            Option.some.inj (hbody'.symm.trans hbody)
          subst hbod
          subst heq
          subst he
          exact parRedStar_sort_eq hs

/-- Two stars from `const r` to sorts, body a sort: both peels hit the
same stored universe, read through their own level lists.

M-003 (00 §20.6 RULE CHANGES). Premise added:
    old:  (hres) (hbody) (htr) (h1) (h2)               : eqN w w'
    new:  (hres) (hbody) (htr) (hls : eqNList ls ls2)
          (h1) (h2)                                     : eqN w w'
After the rule change the two peels land on `instLevel ls u` and
`instLevel ls2 u`; without `eqNList ls ls2` the conclusion is FALSE
(body `.sort (param 0)`, `ls = [zero]`, `ls2 = [succ zero]` gives
`w = zero`, `w' = succ zero`). The premise is exactly what the join
needs and no more: it is `rfl`-discharged whenever the two stars start
from the same term, and under `EnvWf` both lists are `[]`
(`envWf_body_arity_zero`), so nothing that could use the old form
loses access to it. This is a correction of a now-false statement,
not a weakening of a true one. -/
theorem two_stars_const_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls2 : List Level} {u w w' : Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hbody : m.body = some (.sort u))
    (htr : transparent m.mclass = true)
    (hls : eqNList ls ls2)
    (h1 : ParRedStar E n Γ (.const r ls) (.sort w))
    (h2 : ParRedStar E n Γ (.const r ls2) (.sort w')) : eqN w w' :=
  eqN_trans
    (eqN_symm (parRedStar_const_body_sort h1 rfl rfl hres hbody htr))
    (eqN_trans (instLevel_eqNList hls u)
      (parRedStar_const_body_sort h2 rfl rfl hres hbody htr))

theorem instantiate0_sort (v : Expr Nat) (u : Level) :
    instantiate0 v (.sort u) = .sort u := rfl

/-- Invert ParRed of a lambda-application: stay an app of a lambda
(congruence), or one-shot beta. Iota/iotaSpine are recursor-headed,
never a lambda (`foldApps_const_ne_lam`). -/
def parRed_lam_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg a e : Expr Nat} :
    ParRed E n Γ a e → a = .app (.lam A body) arg →
    (Σ' (A' body' arg' : Expr Nat),
      (e = .app (.lam A' body') arg') ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ arg arg') ⊕'
    (Σ' (A' body' arg' : Expr Nat),
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ arg arg' ×'
      (e = instantiate0 arg' body'))
  | .refl _ _, ha => by
      subst ha
      exact .inl ⟨A, body, arg, rfl, .refl _ _, .refl _ _, .refl _ _⟩
  | .app _ f f' x x' hf hx, ha => by
      injection ha with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      let ⟨A', body', hfeq, hA, hb⟩ := parRed_lam hf rfl
      exact .inl ⟨A', body', x',
        congrArg (fun g => Expr.app g x') hfeq, hA, hb, hx⟩
  | .beta _ A₀ A' body₀ body' arg₀ arg' hA hb hx, ha => by
      injection ha with hf_eq hx_eq
      injection hf_eq with hA_eq hb_eq
      subst hA_eq
      subst hb_eq
      subst hx_eq
      exact .inr ⟨A', body', arg', hA, hb, hx, rfl⟩
  | .sortEq _ _ _ _, ha => nomatch ha
  | .consts _ _ _ _ _, ha => nomatch ha
  | .bvarZeta _ _ _ _ _ _ _, ha => nomatch ha
  | .delta .., ha => nomatch ha
  | .lam _ _ _ _ _ _ _, ha => nomatch ha
  | .pi _ _ _ _ _ _ _, ha => nomatch ha
  | .letE _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .zeta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, ha => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at ha
      injection ha with hf _
      exact (foldApps_const_ne_lam pre hf).elim
  | .lit _ _, ha => nomatch ha

/-- Invert ParRed of an application: congruence, beta, iota, or
iotaSpine. Source is definitionally `.app`, so iota's variable lhs
is transported along `iotaLhsOf_app`. -/
def parRed_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f x a e : Expr Nat} :
    ParRed E n Γ a e → a = .app f x →
    (Σ' (f' x' : Expr Nat),
      (e = .app f' x') ×' ParRed E n Γ f f' ×' ParRed E n Γ x x') ⊕'
    ((Σ' (A body A' body' x' : Expr Nat),
      (f = .lam A body) ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ x x' ×'
      (e = instantiate0 x' body')) ⊕'
    (Σ' (w : IotaWitness E) (lsR lsC : List Level)
        (pre pre' fields fields' : List (Expr Nat)),
      eqNList w.ls lsR ×' eqNList w.lsC lsC ×'
      ParRedArgs E n Γ pre pre' ×'
      ParRedArgs E n Γ fields fields' ×'
      (pre'.length = w.preMajor.length) ×'
      (fields'.length =
        (w.ctorParams ++ w.fields).length) ×'
      (iotaLhsOf w =
        recCall (.const w.recRef w.ls) pre'
          (foldApps (.const w.ctorRef w.lsC) fields')) ×'
      (recCall (.const w.recRef lsR) pre
        (foldApps (.const w.ctorRef lsC) fields) = .app f x) ×'
      (e = iotaRhsOf w)))
  | .refl _ _, ha => by
      subst ha
      exact .inl ⟨f, x, rfl, .refl _ _, .refl _ _⟩
  | .app _ f0 f' x0 x' hf hx, ha => by
      injection ha with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      exact .inl ⟨f', x', rfl, hf, hx⟩
  | .beta _ A A' body body' arg arg' hA hb hx, ha => by
      injection ha with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      exact .inr <| .inl ⟨A, body, A', body', arg', rfl, hA, hb, hx, rfl⟩
  | .iotaSpine _ w lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha0 hpreLen hfieldsLen hlhs, ha =>
      .inr <| .inr
        ⟨w, lsR, lsC, pre, pre', fields, fields', hlsR, hlsC, hf, ha0,
          hpreLen, hfieldsLen, hlhs, ha, rfl⟩
  | .sortEq _ _ _ _, ha => nomatch ha
  | .consts _ _ _ _ _, ha => nomatch ha
  | .bvarZeta _ _ _ _ _ _ _, ha => nomatch ha
  | .delta .., ha => nomatch ha
  | .lam _ _ _ _ _ _ _, ha => nomatch ha
  | .pi _ _ _ _ _ _ _, ha => nomatch ha
  | .letE _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .zeta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .lit _ _, ha => nomatch ha

/-- Star from `app (lam A (sort u)) arg` to a sort: peel congruence,
then beta; instantiate of a sort is that sort. -/
def parRedStar_lam_app_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg a e : Expr Nat} {u w : Level}
    (h : ParRedStar E n Γ a e)
    (ha : a = .app (.lam A body) arg)
    (hbod : body = .sort u)
    (he : e = .sort w) : eqN u w :=
  match h with
  | .refl _ _ => nomatch (ha.symm.trans he)
  | .tail h0 hs =>
      match parRed_lam_app h0 ha with
      | .inl ⟨_A', body', arg', heq, _hA, hb, _hx⟩ =>
          let ⟨_v, hv, q⟩ := parRed_sort hb hbod
          eqN_trans q (parRedStar_lam_app_body_sort hs heq hv he)
      | .inr ⟨_A', body', arg', _hA, hb, _hx, heq⟩ => by
          have ⟨v, hv, q⟩ := parRed_sort hb hbod
          subst hv
          subst heq
          subst he
          exact eqN_trans q
            (parRedStar_sort_eq (instantiate0_sort arg' v ▸ hs))

theorem two_stars_lam_app_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A arg : Expr Nat} {u w w' : Level}
    (h1 : ParRedStar E n Γ (.app (.lam A (.sort u)) arg) (.sort w))
    (h2 : ParRedStar E n Γ (.app (.lam A (.sort u)) arg) (.sort w')) :
    eqN w w' :=
  eqN_trans
    (eqN_symm (parRedStar_lam_app_body_sort h1 rfl rfl rfl))
    (parRedStar_lam_app_body_sort h2 rfl rfl rfl)

/-- Invert ParRed of a let: stay a let (congruence), or one-shot zeta. -/
def parRed_letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v body a e : Expr Nat} :
    ParRed E n Γ a e → a = .letE A v body →
    (Σ' (A' v' body' : Expr Nat),
      (e = .letE A' v' body') ×'
      ParRed E n Γ A A' ×'
      ParRed E n Γ v v' ×'
      ParRed E n (LocalDecl.letBinding A v :: Γ) body body') ⊕'
    (Σ' (A' v' body' : Expr Nat),
      ParRed E n Γ A A' ×'
      ParRed E n Γ v v' ×'
      ParRed E n (LocalDecl.letBinding A v :: Γ) body body' ×'
      (e = instantiate0 v' body'))
  | .refl _ _, ha => by
      subst ha
      exact .inl ⟨A, v, body, rfl, .refl _ _, .refl _ _, .refl _ _⟩
  | .letE _ A₀ A' v₀ v' body₀ body' hA hv hb, ha => by
      injection ha with hA_eq hv_eq hb_eq
      subst hA_eq
      subst hv_eq
      subst hb_eq
      exact .inl ⟨A', v', body', rfl, hA, hv, hb⟩
  | .zeta _ A₀ A' v₀ v' body₀ body' hA hv hb, ha => by
      injection ha with hA_eq hv_eq hb_eq
      subst hA_eq
      subst hv_eq
      subst hb_eq
      exact .inr ⟨A', v', body', hA, hv, hb, rfl⟩
  | .sortEq _ _ _ _, ha => nomatch ha
  | .consts _ _ _ _ _, ha => nomatch ha
  | .bvarZeta _ _ _ _ _ _ _, ha => nomatch ha
  | .delta .., ha => nomatch ha
  | .app _ _ _ _ _ _ _, ha => nomatch ha
  | .beta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .lam _ _ _ _ _ _ _, ha => nomatch ha
  | .pi _ _ _ _ _ _ _, ha => nomatch ha
  | .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, ha => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at ha
      exact nomatch ha
  | .lit _ _, ha => nomatch ha

/-- Star from `letE A v (sort u)` to a sort: peel congruence, then
zeta; instantiate of a sort is that sort. -/
def parRedStar_letE_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v body a e : Expr Nat} {u w : Level}
    (h : ParRedStar E n Γ a e)
    (ha : a = .letE A v body)
    (hbod : body = .sort u)
    (he : e = .sort w) : eqN u w :=
  match h with
  | .refl _ _ => nomatch (ha.symm.trans he)
  | .tail h0 hs =>
      match parRed_letE h0 ha with
      | .inl ⟨_A', v', body', heq, _hA, _hv, hb⟩ =>
          let ⟨_lv, hvs, q⟩ := parRed_sort hb hbod
          eqN_trans q (parRedStar_letE_body_sort hs heq hvs he)
      | .inr ⟨_A', v', body', _hA, _hv, hb, heq⟩ => by
          have ⟨lv, hvs, q⟩ := parRed_sort hb hbod
          subst hvs
          subst heq
          subst he
          exact eqN_trans q
            (parRedStar_sort_eq (instantiate0_sort v' lv ▸ hs))

theorem two_stars_letE_body_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v : Expr Nat} {u w w' : Level}
    (h1 : ParRedStar E n Γ (.letE A v (.sort u)) (.sort w))
    (h2 : ParRedStar E n Γ (.letE A v (.sort u)) (.sort w')) : eqN w w' :=
  eqN_trans
    (eqN_symm (parRedStar_letE_body_sort h1 rfl rfl rfl))
    (parRedStar_letE_body_sort h2 rfl rfl rfl)

/-
Attempt 16: sort-body preimages of two_stars_to_sort.
- const (delta) whose stored body is a sort (`def T := Sort u`)
- lam-app (beta) whose body is a sort (`(fun _ => Sort u) arg`)
- letE (zeta) whose body is a sort (`let _ := v in Sort u`)
General two_stars_to_sort (non-sort bodies, iota/app pairing) still
needs parRed_diamond. Attempt count: 16.
-/

/-! ### Attempt 17: Takahashi `develWf` on EnvWf admission rank.

Architect ruling: one-shot iota/delta is a **measure** failure, not a
ParRed-constructor failure. Outer recursor = `EnvWf` derivation
(`envWf_rank` / `envWf_of_member`). `extendEnv` is a function overlay;
the DERIVATION is cons-shaped (`hfresh` forbids a second extend of
the same ref) — invert succeeds.

DELTA: `m.body` was typed in a strict prefix. `develWf` recurses on
that prefix. Rank strictly decreases.

IOTA failing statement (EnvWf rank does **not** drop; do not inhabit):
  `envWf_rank` of `iotaRhsOf w` is not `<` that of `iotaLhsOf w`.
`w.minor` is a lhs-spine slot (`hminor`), not `recMember.body`
(`EnvWf.indMember` has `hnobody`). DirectRec `recCallField`
reinserts `.const w.recRef`. `iotaRhsOf` can be syntactically
larger than the lhs. Changing `ResolvedEnv` to a list would not
store an iota rhs in a prefix — recursors have no delta body.
Iota arm of `develWf` stays one-shot.

Attempt 20: `star_to_develWf` is total (iota one-shot + delta
prefix via `parRedStarExt`).

Attempt 21: `develWfGo` keeps lookups on the same `hE`; fuel drops
to the admitting prefix rank. Delta triangle hlt is
`parRed_develWf_delta_hlt` (IH at prefix fuel, same env).
`parRed_develWf` total map not yet filled.
-/

/-- Inner measure for `develWf` (lex after `envWf_rank`). -/
def exprSize : Expr Nat → Nat
  | .bvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .lit _ => 1
  | .app f a => exprSize f + exprSize a + 1
  | .lam A b => exprSize A + exprSize b + 1
  | .pi A B => exprSize A + exprSize B + 1
  | .letE A v b => exprSize A + exprSize v + exprSize b + 1

/-- 00 §20.6: level instantiation is size-invariant. Deferred out of
`RcicLevelCalc` in W1 because `exprSize` is defined here, and a file
importing only `RcicDeclarative` cannot state it. The measure that
`develWf` recurses on is therefore unchanged by the new delta arm. -/
theorem exprSize_instantiateLevels (ls : List Level) :
    (e : Expr Nat) → exprSize (instantiateLevels ls e) = exprSize e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lit _ => rfl
  | .app f a => by
      simp only [instantiateLevels, exprSize,
        exprSize_instantiateLevels ls f, exprSize_instantiateLevels ls a]
  | .lam A b => by
      simp only [instantiateLevels, exprSize,
        exprSize_instantiateLevels ls A, exprSize_instantiateLevels ls b]
  | .pi A B => by
      simp only [instantiateLevels, exprSize,
        exprSize_instantiateLevels ls A, exprSize_instantiateLevels ls B]
  | .letE A v b => by
      simp only [instantiateLevels, exprSize,
        exprSize_instantiateLevels ls A, exprSize_instantiateLevels ls v,
        exprSize_instantiateLevels ls b]

theorem exprSize_app_left (f a : Expr Nat) :
    exprSize f < exprSize (.app f a) := by
  have : exprSize (.app f a) = exprSize f + exprSize a + 1 := rfl
  omega
theorem exprSize_app_right (f a : Expr Nat) :
    exprSize a < exprSize (.app f a) := by
  have : exprSize (.app f a) = exprSize f + exprSize a + 1 := rfl
  omega
theorem exprSize_lam_dom (A b : Expr Nat) :
    exprSize A < exprSize (.lam A b) := by
  have : exprSize (.lam A b) = exprSize A + exprSize b + 1 := rfl
  omega
theorem exprSize_lam_body (A b : Expr Nat) :
    exprSize b < exprSize (.lam A b) := by
  have : exprSize (.lam A b) = exprSize A + exprSize b + 1 := rfl
  omega
theorem exprSize_pi_dom (A B : Expr Nat) :
    exprSize A < exprSize (.pi A B) := by
  have : exprSize (.pi A B) = exprSize A + exprSize B + 1 := rfl
  omega
theorem exprSize_pi_body (A B : Expr Nat) :
    exprSize B < exprSize (.pi A B) := by
  have : exprSize (.pi A B) = exprSize A + exprSize B + 1 := rfl
  omega
theorem exprSize_let_ty (A v b : Expr Nat) :
    exprSize A < exprSize (.letE A v b) := by
  have : exprSize (.letE A v b) = exprSize A + exprSize v + exprSize b + 1 :=
    rfl
  omega
theorem exprSize_let_val (A v b : Expr Nat) :
    exprSize v < exprSize (.letE A v b) := by
  have : exprSize (.letE A v b) = exprSize A + exprSize v + exprSize b + 1 :=
    rfl
  omega
theorem exprSize_let_body (A v b : Expr Nat) :
    exprSize b < exprSize (.letE A v b) := by
  have : exprSize (.letE A v b) = exprSize A + exprSize v + exprSize b + 1 :=
    rfl
  omega

-- Diamond measure (single Nat). `refl t` costs `exprSize t + 1` so
-- splitting a let/app is free. Ctx *nodes* cost 0: only let-*values*
-- contribute, so extending Γ does not increase the measure.
--
-- ALSO THE MEASURE FOR STRUCTURAL RECURSION OVER `ParRed` in general,
-- and no second one is to be written (00 §19.4). Every constructor's
-- derivation premises are counted here — `iotaSpine`'s only such
-- premises are its two `ParRedArgs`, and `ParRedArgs.cons` pays for
-- its head — and `parRedW_pos` / `parRedArgsW_pos` below make each
-- summand ≥ 1, so `parRedW` drops strictly at every premise of every
-- arm. A `parRedSR`-shaped recursion therefore terminates on it, and
-- a separate `sizeParRed` would be a duplicate of this def, not a new
-- fact.
-- (Doc-comment cannot precede `mutual` in 4.14.)
mutual
def parRedW {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → ParRed E n Γ a b → Nat
  | _, _, _, .refl _ e => exprSize e + 1
  | _, _, _, .sortEq .. => 1
  | _, _, _, .consts .. => 1
  | _, _, _, .lit .. => 1
  | _, _, _, .delta .. => 1
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => parRedW hv + 1
  | _, _, _, .app _ _ _ _ _ hf ha => parRedW hf + parRedW ha + 1
  | _, _, _, .lam _ _ _ _ _ hA hb => parRedW hA + parRedW hb + 1
  | _, _, _, .pi _ _ _ _ _ hA hB => parRedW hA + parRedW hB + 1
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      parRedW hA + parRedW hv + parRedW hb + 1
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb =>
      parRedW hA + parRedW hv + parRedW hb + 1
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha =>
      parRedW hA + parRedW hb + parRedW ha + 1
  | _, _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ hf ha _ _ _ =>
      parRedArgsW hf + parRedArgsW ha + 1

def parRedArgsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) : Nat :=
  match h with
  | ParRedArgs.nil _ => 1
  | ParRedArgs.cons hx t => parRedW hx + parRedArgsW (h := t)

def parRedCtxW {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → ParRedCtx E n Γ Γ' → Nat
  | _, _, .nil => 0
  | _, _, .assumption _ hΓ => parRedCtxW hΓ
  | _, _, .letBinding _ hv hΓ => parRedW hv + parRedCtxW hΓ
end

theorem parRedCtx_drop_weight {E : ResolvedEnv} {n : Nat}
    {Γ Γ' : LCtx} (k : Nat) (hΓ : ParRedCtx E n Γ Γ') :
    parRedCtxW (parRedCtx_drop k hΓ) ≤ parRedCtxW hΓ := by
  induction k generalizing Γ Γ' hΓ with
  | zero =>
      simp only [parRedCtx_drop]
      exact Nat.le_refl _
  | succ k ih =>
      cases hΓ with
      | nil =>
          simp only [parRedCtx_drop, parRedCtxW]
          exact Nat.le_refl _
      | assumption _hA hΓ =>
          simp only [parRedCtx_drop, parRedCtxW]
          exact ih hΓ
      | letBinding _hA hv hΓ =>
          simp only [parRedCtx_drop, parRedCtxW]
          exact Nat.le_trans (ih hΓ) (Nat.le_add_left _ (parRedW hv))

/-- The stored let-value at `i` plus the dropped tail is paid by `hΓ`.
`parRedCtx_get?_let` is `Σ' A' v', eq ×' ParRed ×' ParRedCtx`, so the
value derivation is `.2.2.2.1`. -/
theorem parRedCtxW_get?_let {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → {i : Nat} → {A v : Expr Nat} →
    (hΓ : ParRedCtx E n Γ Γ') →
    (hlk : Γ.get? i = some (.letBinding A v)) →
    parRedW (parRedCtx_get?_let hΓ hlk).2.2.2.1
      + parRedCtxW (parRedCtx_drop (i + 1) hΓ) ≤ parRedCtxW hΓ
  | _, _, _, _, _, .nil, hlk => nomatch hlk
  | _, _, 0, _, _, .assumption _ _, hlk => nomatch hlk
  | _, _, i + 1, A, v, .assumption _hA hΓ, hlk => by
      simp only [List.get?_cons_succ] at hlk
      have ih := parRedCtxW_get?_let (i := i) hΓ hlk
      simp only [parRedCtx_drop, parRedCtxW, parRedCtx_get?_let]
      exact ih
  | _, _, 0, A, v, .letBinding (A := A0) (v := v0) (A' := A') (v' := v')
        _hA hv hΓ, hlk => by
      simp only [parRedCtx_drop, parRedCtxW, List.drop]
      have hveq : v0 = v := by
        have := Option.some.inj hlk
        injection this
      subst hveq
      exact Nat.le_refl (parRedW hv + parRedCtxW hΓ)
  | _, _, i + 1, A, v, .letBinding _hA hv hΓ, hlk => by
      simp only [List.get?_cons_succ] at hlk
      have ih := parRedCtxW_get?_let (i := i) hΓ hlk
      simp only [parRedCtx_drop, parRedCtxW, parRedCtx_get?_let]
      exact Nat.le_trans ih (Nat.le_add_left _ (parRedW hv))

mutual
theorem parRedW_pos {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (h : ParRed E n Γ a b) → 1 ≤ parRedW h
  | _, _, _, .refl _ e => Nat.succ_le_succ (Nat.zero_le (exprSize e))
  | _, _, _, .sortEq .. => Nat.le_refl 1
  | _, _, _, .consts .. => Nat.le_refl 1
  | _, _, _, .lit .. => Nat.le_refl 1
  | _, _, _, .delta .. => Nat.le_refl 1
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => by
      have := parRedW_pos hv; simp only [parRedW]; omega
  | _, _, _, .app _ _ _ _ _ hf ha => by
      have h1 := parRedW_pos hf; have h2 := parRedW_pos ha
      simp only [parRedW]; omega
  | _, _, _, .lam _ _ _ _ _ hA hb => by
      have h1 := parRedW_pos hA; have h2 := parRedW_pos hb
      simp only [parRedW]; omega
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      have h1 := parRedW_pos hA; have h2 := parRedW_pos hB
      simp only [parRedW]; omega
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => by
      have h1 := parRedW_pos hA; have h2 := parRedW_pos hv
      have h3 := parRedW_pos hb; simp only [parRedW]; omega
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb => by
      have h1 := parRedW_pos hA; have h2 := parRedW_pos hv
      have h3 := parRedW_pos hb; simp only [parRedW]; omega
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha => by
      have h1 := parRedW_pos hA; have h2 := parRedW_pos hb
      have h3 := parRedW_pos ha; simp only [parRedW]; omega
  | _, _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ hf ha _ _ _ => by
      have h1 := parRedArgsW_pos hf; have h2 := parRedArgsW_pos ha
      simp only [parRedW]; omega

theorem parRedArgsW_pos {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) :
    1 ≤ parRedArgsW h :=
  match h with
  | ParRedArgs.nil _ => Nat.le_refl 1
  | ParRedArgs.cons hx t => by
      have h1 := parRedW_pos hx; have h2 := parRedArgsW_pos (h := t)
      simp only [parRedArgsW]; omega
end

/-- Inversion of a λ-redex: both premises are paid by `h`. -/
theorem parRedW_of_lam {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A b : Expr Nat} → (heq : a = .lam A b) →
    parRedW (parRed_lam h heq).2.2.2.1 ≤ parRedW h ∧
    parRedW (parRed_lam h heq).2.2.2.2 ≤ parRedW h
  | _, _, _, .refl _ a, A, b, heq => by
      subst heq
      simp only [parRed_lam, parRedW, exprSize]
      exact ⟨by omega, by omega⟩
  | _, _, _, .lam _ A0 A1 b0 b1 hA hb, A, b, heq => by
      injection heq with hAeq hbeq
      subst hAeq
      subst hbeq
      simp only [parRed_lam, parRedW]
      exact ⟨by omega, by omega⟩
  | _, _, _, .sortEq _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, b, heq =>
      (foldApps_const_ne_lam
        (pre ++ [foldApps (.const w.ctorRef lsC) fields]) heq).elim
  | _, _, _, .lit _ _, _, _, heq => nomatch heq

/-- Inversion of a Π-redex: both premises are paid by `h`. -/
theorem parRedW_of_pi {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A B : Expr Nat} → (heq : a = .pi A B) →
    parRedW (parRed_pi h heq).2.2.2.1 ≤ parRedW h ∧
    parRedW (parRed_pi h heq).2.2.2.2 ≤ parRedW h
  | _, _, _, .refl _ a, A, B, heq => by
      subst heq
      simp only [parRed_pi, parRedW, exprSize]
      exact ⟨by omega, by omega⟩
  | _, _, _, .pi _ A0 A1 B0 B1 hA hB, A, B, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      simp only [parRed_pi, parRedW]
      exact ⟨by omega, by omega⟩
  | _, _, _, .sortEq _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, B, heq =>
      (foldApps_snoc_ne_pi (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim
  | _, _, _, .lit _ _, _, _, heq => nomatch heq

/-- App congruence (inl of `parRed_app`): fun/arg premises are paid
by `h`. Equation-compiler + `a = .app` so iotaSpine does not have
to unify `recCall` with `.app` (dependent elimination). -/
theorem parRedW_of_app_congr {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {f x : Expr Nat} → (heq : a = .app f x) →
    (p : Σ' (f' x' : Expr Nat),
      (e = .app f' x') ×' ParRed E n Γ f f' ×' ParRed E n Γ x x') →
    (hsum : parRed_app h heq = .inl p) →
    parRedW p.2.2.2.1 ≤ parRedW h ∧ parRedW p.2.2.2.2 ≤ parRedW h
  | _, _, _, .refl _ a, f, x, heq, p, hsum => by
      subst heq
      simp only [parRed_app, parRedW, exprSize] at hsum ⊢
      injection hsum with hp
      cases hp
      simp only [parRedW, exprSize]
      exact ⟨by omega, by omega⟩
  | _, _, _, .app _ f0 f1 x0 x1 hf hx, f, x, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_app, parRedW] at hsum ⊢
      injection hsum with hp
      cases hp
      simp only [parRedW]
      exact ⟨by omega, by omega⟩
  | _, _, _, .beta _ A0 A1 body0 body1 arg0 arg1 hA hb ha, f, x, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_app] at hsum
      exact nomatch hsum
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, f, x, heq, p, hsum => by
      simp only [parRed_app] at hsum
      exact nomatch hsum
  | _, _, _, .sortEq _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lit _ _, _, _, heq, _, _ => nomatch heq

/-- Let congruence (inl of `parRed_letE`): A/v/body premises are
paid by `h`. Equation-compiler + `a = .letE` so iotaSpine does not
have to unify `recCall` with `.letE`. -/
theorem parRedW_of_letE_congr {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A v body : Expr Nat} →
    (heq : a = .letE A v body) →
    (p : Σ' (A' v' body' : Expr Nat),
      (e = .letE A' v' body') ×'
      ParRed E n Γ A A' ×'
      ParRed E n Γ v v' ×'
      ParRed E n (LocalDecl.letBinding A v :: Γ) body body') →
    (hsum : parRed_letE h heq = .inl p) →
    parRedW p.2.2.2.2.2.1 + parRedW p.2.2.2.2.2.2 ≤ parRedW h ∧
    parRedW p.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.2 ≤ parRedW h
  | _, _, _, .refl _ a, A, v, body, heq, p, hsum => by
      subst heq
      simp only [parRed_letE, parRedW, exprSize] at hsum ⊢
      injection hsum with hp
      cases hp
      simp only [parRedW, exprSize]
      exact ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩⟩⟩
  | _, _, _, .letE _ A0 A1 v0 v1 b0 b1 hA hv hb, A, v, body, heq, p, hsum => by
      injection heq with hAeq hveq hbeq
      subst hAeq
      subst hveq
      subst hbeq
      simp only [parRed_letE, parRedW] at hsum ⊢
      injection hsum with hp
      cases hp
      simp only [parRedW]
      exact ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩⟩⟩
  | _, _, _, .zeta _ A0 A1 v0 v1 b0 b1 hA hv hb, A, v, body, heq, p, hsum => by
      injection heq with hAeq hveq hbeq
      subst hAeq
      subst hveq
      subst hbeq
      simp only [parRed_letE] at hsum
      exact nomatch hsum
  | _, _, _, .sortEq _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, v, body, heq, p, hsum => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at heq
      exact nomatch heq
  | _, _, _, .lit _ _, _, _, _, heq, _, _ => nomatch heq

/-- Transport along source equality does not change the weight. -/
theorem parRedW_eq_rec {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a a' b : Expr Nat} (heq : a = a') (h : ParRed E n Γ a b) :
    parRedW (Eq.rec (motive := fun t _ => ParRed E n Γ t b) h heq) =
      parRedW h := by
  subst heq
  rfl

theorem parRedArgsW_eq_rec {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs xs' ys : List (Expr Nat)} (heq : xs = xs')
    (h : ParRedArgs E n Γ xs ys) :
    parRedArgsW (Eq.rec (motive := fun t _ => ParRedArgs E n Γ t ys) h heq) =
      parRedArgsW h := by
  subst heq
  rfl

/-- Beta (inr-inl of `parRed_app`): A/body/arg premises are paid by `h`. -/
theorem parRedW_of_app_beta {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {f x : Expr Nat} → (heq : a = .app f x) →
    (p : Σ' (A body A' body' x' : Expr Nat),
      (f = .lam A body) ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ x x' ×'
      (e = instantiate0 x' body')) →
    (hsum : parRed_app h heq = .inr (.inl p)) →
    parRedW p.2.2.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.2.2.2.1 ≤ parRedW h
  | _, _, _, .beta _ A0 A1 body0 body1 arg0 arg1 hA hb ha, f, x, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_app] at hsum
      injection hsum with hrest
      injection hrest with hp
      cases hp
      simp only [parRedW]
      exact ⟨by omega, ⟨by omega, by omega⟩⟩
  | _, _, _, .refl _ a, f, x, heq, p, hsum => by
      subst heq
      simp only [parRed_app] at hsum
      exact nomatch hsum
  | _, _, _, .app _ f0 f1 x0 x1 hf hx, f, x, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_app] at hsum
      exact nomatch hsum
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, f, x, heq, p, hsum => by
      simp only [parRed_app] at hsum
      exact nomatch hsum
  | _, _, _, .sortEq _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lit _ _, _, _, heq, _, _ => nomatch heq

/-- Congruence branch of `parRed_lam_app`. -/
theorem parRedW_of_lam_app_congr {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A body arg : Expr Nat} →
    (heq : a = .app (.lam A body) arg) →
    (p : Σ' (A' body' arg' : Expr Nat),
      (e = .app (.lam A' body') arg') ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ arg arg') →
    (hsum : parRed_lam_app h heq = .inl p) →
    parRedW p.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.2 ≤ parRedW h
  | _, _, _, .refl _ a, A, body, arg, heq, p, hsum => by
      subst heq
      simp only [parRed_lam_app, parRedW, exprSize] at hsum ⊢
      injection hsum with hp
      cases hp
      simp only [parRedW, exprSize]
      exact ⟨by omega, ⟨by omega, by omega⟩⟩
  | _, _, _, .app _ f0 f1 x0 x1 hf hx, A, body, arg, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_lam_app] at hsum
      injection hsum with hp
      cases hp
      have hW := parRedW_of_lam hf rfl
      simp only [parRedW]
      exact ⟨Nat.le_trans hW.1 (by omega),
        ⟨Nat.le_trans hW.2 (by omega), by omega⟩⟩
  | _, _, _, .beta _ A0 A1 body0 body1 arg0 arg1 hA hb ha, A, body, arg, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      injection hf_eq with hAeq hbeq
      subst hAeq
      subst hbeq
      subst hx_eq
      simp only [parRed_lam_app] at hsum
      exact nomatch hsum
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, body, arg, heq, p, hsum => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at heq
      injection heq with hf _
      exact (foldApps_const_ne_lam pre hf).elim
  | _, _, _, .sortEq _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lit _ _, _, _, _, heq, _, _ => nomatch heq

/-- Beta branch of `parRed_lam_app`. -/
theorem parRedW_of_lam_app_beta {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A body arg : Expr Nat} →
    (heq : a = .app (.lam A body) arg) →
    (p : Σ' (A' body' arg' : Expr Nat),
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) body body' ×'
      ParRed E n Γ arg arg' ×'
      (e = instantiate0 arg' body')) →
    (hsum : parRed_lam_app h heq = .inr p) →
    parRedW p.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.1 ≤ parRedW h
  | _, _, _, .beta _ A0 A1 body0 body1 arg0 arg1 hA hb ha, A, body, arg, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      injection hf_eq with hAeq hbeq
      subst hAeq
      subst hbeq
      subst hx_eq
      simp only [parRed_lam_app] at hsum
      injection hsum with hp
      cases hp
      simp only [parRedW]
      exact ⟨by omega, ⟨by omega, by omega⟩⟩
  | _, _, _, .refl _ a, A, body, arg, heq, p, hsum => by
      subst heq
      simp only [parRed_lam_app] at hsum
      exact nomatch hsum
  | _, _, _, .app _ f0 f1 x0 x1 hf hx, A, body, arg, heq, p, hsum => by
      injection heq with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      simp only [parRed_lam_app] at hsum
      exact nomatch hsum
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, body, arg, heq, p, hsum => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at heq
      injection heq with hf _
      exact (foldApps_const_ne_lam pre hf).elim
  | _, _, _, .sortEq _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lit _ _, _, _, _, heq, _, _ => nomatch heq

/-- Zeta (inr of `parRed_letE`): A/v/body premises are paid by `h`. -/
theorem parRedW_of_letE_zeta {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {A v body : Expr Nat} →
    (heq : a = .letE A v body) →
    (p : Σ' (A' v' body' : Expr Nat),
      ParRed E n Γ A A' ×'
      ParRed E n Γ v v' ×'
      ParRed E n (LocalDecl.letBinding A v :: Γ) body body' ×'
      (e = instantiate0 v' body')) →
    (hsum : parRed_letE h heq = .inr p) →
    parRedW p.2.2.2.2.1 + parRedW p.2.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.1 ≤ parRedW h ∧
    parRedW p.2.2.2.2.2.1 ≤ parRedW h
  | _, _, _, .zeta _ A0 A1 v0 v1 b0 b1 hA hv hb, A, v, body, heq, p, hsum => by
      injection heq with hAeq hveq hbeq
      subst hAeq
      subst hveq
      subst hbeq
      simp only [parRed_letE] at hsum
      injection hsum with hp
      cases hp
      simp only [parRedW]
      exact ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩⟩⟩
  | _, _, _, .refl _ a, A, v, body, heq, p, hsum => by
      subst heq
      simp only [parRed_letE] at hsum
      exact nomatch hsum
  | _, _, _, .letE _ A0 A1 v0 v1 b0 b1 hA hv hb, A, v, body, heq, p, hsum => by
      injection heq with hAeq hveq hbeq
      subst hAeq
      subst hveq
      subst hbeq
      simp only [parRed_letE] at hsum
      exact nomatch hsum
  | _, _, _, .sortEq _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, _, heq, _, _ => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, v, body, heq, p, hsum => by
      have happ :
          recCall (.const w.recRef lsR) pre
            (foldApps (.const w.ctorRef lsC) fields) =
          .app (foldApps (.const w.recRef lsR) pre)
            (foldApps (.const w.ctorRef lsC) fields) :=
        foldApps_snoc _ _ pre
      rw [happ] at heq
      exact nomatch heq
  | _, _, _, .lit _ _, _, _, _, heq, _, _ => nomatch heq

/-- `parRed_app` with iota-args paid by `h`, proved on the
`.iotaSpine` constructor (no `IotaWitness` injection). Congruence
and beta summands match `parRed_app`. -/
def parRed_appW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f x a e : Expr Nat} :
    (h : ParRed E n Γ a e) → a = .app f x →
    (Σ' (f' x' : Expr Nat),
      (e = .app f' x') ×' (hf : ParRed E n Γ f f') ×' (hx : ParRed E n Γ x x') ×'
      (parRedW hf ≤ parRedW h ∧ parRedW hx ≤ parRedW h)) ⊕'
    ((Σ' (A body A' body' x' : Expr Nat),
      (f = .lam A body) ×'
      (hA : ParRed E n Γ A A') ×'
      (hb : ParRed E n (LocalDecl.assumption A :: Γ) body body') ×'
      (hx : ParRed E n Γ x x') ×'
      (e = instantiate0 x' body') ×'
      (parRedW hA ≤ parRedW h ∧ parRedW hb ≤ parRedW h ∧ parRedW hx ≤ parRedW h)) ⊕'
    (Σ' (pre pre' fields fields' : List (Expr Nat))
        (hf : ParRedArgs E n Γ pre pre')
        (ha : ParRedArgs E n Γ fields fields'),
      (parRedArgsW hf ≤ parRedW h ∧ parRedArgsW ha ≤ parRedW h) ×'
      (w : IotaWitness E) ×' (lsR : List Level) ×' (lsC : List Level) ×'
      eqNList w.ls lsR ×' eqNList w.lsC lsC ×'
      (pre'.length = w.preMajor.length) ×'
      (fields'.length =
        (w.ctorParams ++ w.fields).length) ×'
      (iotaLhsOf w =
        recCall (.const w.recRef w.ls) pre'
          (foldApps (.const w.ctorRef w.lsC) fields')) ×'
      (recCall (.const w.recRef lsR) pre
        (foldApps (.const w.ctorRef lsC) fields) = .app f x) ×'
      (e = iotaRhsOf w)))
  | .refl _ _, ha => by
      subst ha
      exact .inl ⟨f, x, rfl, .refl _ _, .refl _ _,
        by simp only [parRedW, exprSize]; exact ⟨by omega, by omega⟩⟩
  | .app _ f0 f' x0 x' hf hx, ha => by
      injection ha with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      exact .inl ⟨f', x', rfl, hf, hx,
        by simp only [parRedW]; exact ⟨by omega, by omega⟩⟩
  | .beta _ A A' body body' arg arg' hA hb hx, ha => by
      injection ha with hf_eq hx_eq
      subst hf_eq
      subst hx_eq
      exact .inr <| .inl ⟨A, body, A', body', arg', rfl, hA, hb, hx, rfl,
        by simp only [parRedW]; exact ⟨by omega, ⟨by omega, by omega⟩⟩⟩
  | .iotaSpine Γ w lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha0 hpreLen hfieldsLen hlhs, ha => by
      have hw :
          parRedArgsW hf ≤
            parRedW (.iotaSpine Γ w lsR lsC hlsR hlsC pre pre'
              fields fields' hf ha0 hpreLen hfieldsLen hlhs) ∧
          parRedArgsW ha0 ≤
            parRedW (.iotaSpine Γ w lsR lsC hlsR hlsC pre pre'
              fields fields' hf ha0 hpreLen hfieldsLen hlhs) := by
        simp only [parRedW]
        exact ⟨by omega, by omega⟩
      exact .inr <| .inr
        ⟨pre, pre', fields, fields', hf, ha0, hw,
          w, lsR, lsC, hlsR, hlsC, hpreLen, hfieldsLen, hlhs, ha, rfl⟩
  | .sortEq _ _ _ _, ha => nomatch ha
  | .consts _ _ _ _ _, ha => nomatch ha
  | .bvarZeta _ _ _ _ _ _ _, ha => nomatch ha
  | .delta .., ha => nomatch ha
  | .lam _ _ _ _ _ _ _, ha => nomatch ha
  | .pi _ _ _ _ _ _ _, ha => nomatch ha
  | .letE _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .zeta _ _ _ _ _ _ _ _ _ _, ha => nomatch ha
  | .lit _ _, ha => nomatch ha

theorem exprSize_foldApps (f : Expr Nat) :
    (xs : List (Expr Nat)) →
    exprSize (foldApps f xs) =
      exprSize f + xs.foldr (fun x acc => exprSize x + acc + 1) 0
  | [] => rfl
  | x :: xs => by
      simp only [foldApps, exprSize, List.foldr]
      rw [exprSize_foldApps (.app f x) xs]
      simp only [exprSize]
      let r := xs.foldr (fun x acc => exprSize x + acc + 1) 0
      show exprSize f + exprSize x + 1 + r =
        exprSize f + (exprSize x + r + 1)
      ac_rfl

theorem foldr_exprSize_add (k : Nat) :
    (xs : List (Expr Nat)) → (s : Nat) →
    xs.foldr (fun x acc => exprSize x + acc + 1) (s + k) =
      xs.foldr (fun x acc => exprSize x + acc + 1) s + k
  | [], s => rfl
  | x :: xs, s => by
      simp only [List.foldr]
      rw [foldr_exprSize_add k xs s]
      omega

theorem foldr_exprSize_snoc (xs : List (Expr Nat)) (y : Expr Nat) (s : Nat) :
    (xs ++ [y]).foldr (fun x acc => exprSize x + acc + 1) s =
      xs.foldr (fun x acc => exprSize x + acc + 1) (exprSize y + s + 1) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, List.foldr]
  | cons x xs ih =>
      simp only [List.cons_append, List.foldr]
      change exprSize x +
          (xs ++ [y]).foldr (fun x acc => exprSize x + acc + 1) s + 1 =
        exprSize x +
          xs.foldr (fun x acc => exprSize x + acc + 1)
            (exprSize y + s + 1) + 1
      rw [ih]

theorem parRedArgsW_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} :
    (h : ParRedArgs E n Γ xs ys) → {x y : Expr Nat} →
    (hx : ParRed E n Γ x y) →
    parRedArgsW (parRedArgs_snoc h hx) = parRedArgsW h + parRedW hx
  | ParRedArgs.nil Γ, x, y, hx => by
      simp only [parRedArgs_snoc, parRedArgsW]
      omega
  | ParRedArgs.cons hx0 hs, x, y, hx => by
      simp only [parRedArgs_snoc, parRedArgsW]
      rw [parRedArgsW_snoc (h := hs) hx]
      omega

theorem parRedArgsW_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) →
    parRedArgsW (parRedArgs_refl (E := E) (n := n) (Γ := Γ) xs) =
      xs.foldr (fun x acc => exprSize x + acc + 1) 1
  | [] => rfl
  | x :: xs => by
      simp only [parRedArgs_refl, parRedArgsW, parRedW, List.foldr]
      rw [parRedArgsW_refl (E := E) (n := n) (Γ := Γ) xs]
      ac_rfl

theorem exprSize_lift (c amt : Nat) (e : Expr Nat) :
    exprSize (lift c amt e) = exprSize e := by
  induction e generalizing c with
  | bvar i =>
      simp only [lift]; split <;> rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f x ihf ihx => simp only [lift, exprSize, ihf, ihx]
  | lam A b ihA ihb => simp only [lift, exprSize, ihA, ihb]
  | pi A B ihA ihB => simp only [lift, exprSize, ihA, ihB]
  | letE A v b ihA ihv ihb => simp only [lift, exprSize, ihA, ihv, ihb]

theorem exprSize_foldApps_snoc (f x : Expr Nat) (ys : List (Expr Nat)) :
    exprSize x < exprSize (foldApps f (ys ++ [x])) := by
  induction ys generalizing f with
  | nil =>
      simp only [List.nil_append, foldApps, exprSize]
      omega
  | cons y ys ih =>
      simp only [List.cons_append, foldApps]
      exact ih (.app f y)

def letsCount : LCtx → Nat
  | [] => 0
  | .assumption _ :: Γ => letsCount Γ
  | .letBinding _ _ :: Γ => letsCount Γ + 1

/-- Split `Γ` at a let-binding: stored value and the tail it was typed in. -/
def getLet : LCtx → Nat → Option (Expr Nat × LCtx)
  | [], _ => none
  | .letBinding _ v :: rest, 0 => some (v, rest)
  | .assumption _ :: rest, 0 => none
  | _ :: rest, n + 1 => getLet rest n

theorem getLet_cons_succ (d : LocalDecl) (Γ : LCtx) (i : Nat) :
    getLet (d :: Γ) (Nat.succ i) = getLet Γ i := by
  cases d <;> rfl

theorem getLet_singleton_succ (d : LocalDecl) (i : Nat) :
    getLet [d] (Nat.succ i) = none := by
  cases d <;> rfl

/-- Inserting at `c` shifts later lets by one; stored value and tail
are unchanged (`liftDecl` only rewrites entries below `c`). -/
theorem getLet_insertAt_ge (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    (hi : c ≤ i) :
    getLet (insertAt d c Γ) (i + 1) = getLet Γ i := by
  induction c generalizing i Γ with
  | zero =>
      rw [insertAt_zero]
      exact getLet_cons_succ d Γ i
  | succ c ih =>
      match Γ with
      | [] =>
          match i with
          | 0 => exfalso; omega
          | Nat.succ i' =>
              change getLet [d] (Nat.succ i' + 1) = getLet [] (Nat.succ i')
              have : Nat.succ i' + 1 = Nat.succ (Nat.succ i') := rfl
              rw [this, getLet_singleton_succ]
              rfl
      | x :: Γ' =>
          match i with
          | 0 => exfalso; omega
          | Nat.succ i' =>
              have hi' : c ≤ i' := Nat.le_of_succ_le_succ hi
              rw [insertAt_succ_cons]
              have hidx : Nat.succ i' + 1 = Nat.succ (Nat.succ i') := rfl
              rw [hidx, getLet_cons_succ]
              exact (ih hi').trans (getLet_cons_succ x Γ' i').symm

/-- Below the insertion: the stored let is `liftDecl`'d and the tail
itself carries the insertion. Requires `c ≤ Γ.length` so the insert
is not a dummy cons onto `[]`. -/
theorem getLet_insertAt_lt_none (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    (hlen : c ≤ Γ.length) (hic : i < c)
    (h : getLet Γ i = none) :
    getLet (insertAt d c Γ) i = none := by
  induction c generalizing i Γ with
  | zero => exfalso; omega
  | succ c ih =>
      match Γ with
      | [] =>
          simp only [List.length_nil] at hlen
          exfalso
          omega
      | x :: Γ' =>
          match i with
          | 0 =>
              match x with
              | .assumption A =>
                  simp only [getLet] at h
                  rw [insertAt_succ_cons]
                  simp only [liftDecl, getLet]
              | .letBinding A v =>
                  simp only [getLet] at h
                  nomatch h
          | Nat.succ i' =>
              have hlen' : c ≤ Γ'.length := by
                simp only [List.length_cons] at hlen; omega
              have hic' : i' < c := Nat.lt_of_succ_lt_succ hic
              rw [insertAt_succ_cons, getLet_cons_succ]
              simp only [getLet] at h
              exact ih hlen' hic' h

theorem getLet_insertAt_lt_some (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {stored : Expr Nat} {tail : LCtx}
    (hlen : c ≤ Γ.length) (hic : i < c)
    (h : getLet Γ i = some (stored, tail)) :
    getLet (insertAt d c Γ) i =
      some (lift (c - i - 1) 1 stored, insertAt d (c - i - 1) tail) := by
  induction c generalizing i Γ stored tail with
  | zero => exfalso; omega
  | succ c ih =>
      match Γ with
      | [] =>
          simp only [List.length_nil] at hlen
          exfalso
          omega
      | x :: Γ' =>
          match i with
          | 0 =>
              match x with
              | .assumption A =>
                  simp only [getLet] at h
                  nomatch h
              | .letBinding A v =>
                  simp only [getLet] at h
                  injection h with hpair
                  injection hpair with hv htail
                  subst hv
                  subst htail
                  rw [insertAt_succ_cons]
                  simp only [liftDecl, getLet]
                  rfl
          | Nat.succ i' =>
              have hlen' : c ≤ Γ'.length := by
                simp only [List.length_cons] at hlen; omega
              have hic' : i' < c := Nat.lt_of_succ_lt_succ hic
              rw [insertAt_succ_cons, getLet_cons_succ]
              simp only [getLet] at h
              have ih' := ih hlen' hic' h
              -- (succ c) - (succ i') - 1 = c - i' - 1
              have hcut : (Nat.succ c) - (Nat.succ i') - 1 = c - i' - 1 := by
                omega
              rw [hcut]
              exact ih'

theorem getLet_insertAt_lt_cut_le {c i : Nat} {Γ : LCtx}
    {stored : Expr Nat} {tail : LCtx}
    (hlen : c ≤ Γ.length) (hic : i < c)
    (h : getLet Γ i = some (stored, tail)) :
    c - i - 1 ≤ tail.length := by
  induction Γ generalizing i c with
  | nil => nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero => nomatch h
          | succ i' =>
              simp only [getLet] at h
              cases c with
              | zero => omega
              | succ c' =>
                  have hlen' : c' ≤ rest.length := by
                    simp only [List.length_cons] at hlen; omega
                  have hic' : i' < c' := Nat.lt_of_succ_lt_succ hic
                  have := ih hlen' hic' h
                  simp only [List.length_cons] at hlen
                  omega
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [getLet] at h
              injection h with hpair
              injection hpair with _ htail
              subst htail
              simp only [List.length_cons] at hlen
              omega
          | succ i' =>
              simp only [getLet] at h
              cases c with
              | zero => omega
              | succ c' =>
                  have hlen' : c' ≤ rest.length := by
                    simp only [List.length_cons] at hlen; omega
                  have hic' : i' < c' := Nat.lt_of_succ_lt_succ hic
                  have := ih hlen' hic' h
                  simp only [List.length_cons] at hlen
                  omega

theorem getLet_letsCount {Γ : LCtx} {i : Nat} {v : Expr Nat} {tail : LCtx}
    (h : getLet Γ i = some (v, tail)) : letsCount tail < letsCount Γ := by
  induction Γ generalizing i with
  | nil => nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero => nomatch h
          | succ i' =>
              simp only [getLet] at h
              have := ih h
              simp only [letsCount]
              omega
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [getLet] at h
              injection h with hpair
              cases hpair
              simp only [letsCount]
              omega
          | succ i' =>
              simp only [getLet] at h
              have := ih h
              simp only [letsCount]
              omega

theorem lookupValue_getLet {Γ : LCtx} {i : Nat} {v : Expr Nat} {tail : LCtx}
    (h : getLet Γ i = some (v, tail)) :
    lookupValue Γ i = some (lift 0 (i + 1) v) := by
  induction Γ generalizing i with
  | nil => nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero => nomatch h
          | succ i' =>
              simp only [getLet] at h
              have ih' := ih h
              rw [lookupValue_cons_succ, ih']
              simp only [Option.map_some']
              exact congrArg some
                (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                  (Nat.zero_le _) v)
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [getLet, lookupValue, List.get?_cons_zero] at h ⊢
              injection h with hpair
              cases hpair
              rfl
          | succ i' =>
              simp only [getLet] at h
              have ih' := ih h
              rw [lookupValue_cons_succ, ih']
              simp only [Option.map_some']
              exact congrArg some
                (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                  (Nat.zero_le _) v)

theorem getLet_of_lookup {Γ : LCtx} {i : Nat} {v : Expr Nat}
    (h : lookupValue Γ i = some v) :
    ∃ stored tail, getLet Γ i = some (stored, tail) ∧
      v = lift 0 (i + 1) stored := by
  induction Γ generalizing i v with
  | nil =>
      simp only [lookupValue, List.get?] at h
      nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero =>
              simp only [lookupValue, List.get?_cons_zero] at h
              nomatch h
          | succ i' =>
              rw [lookupValue_cons_succ] at h
              cases hrest : lookupValue rest i' with
              | none =>
                  simp only [hrest, Option.map_none'] at h
                  nomatch h
              | some v0 =>
                  simp only [hrest, Option.map_some'] at h
                  injection h with hv
                  have ⟨stored, tail, hg, heq⟩ := ih hrest
                  refine ⟨stored, tail, ?_, ?_⟩
                  · simp only [getLet]; exact hg
                  · subst hv
                    rw [heq]
                    exact (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                      (Nat.zero_le _) stored)
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [lookupValue, List.get?_cons_zero, getLet] at h ⊢
              injection h with hv
              subst hv
              exact ⟨val, rest, rfl, rfl⟩
          | succ i' =>
              rw [lookupValue_cons_succ] at h
              cases hrest : lookupValue rest i' with
              | none =>
                  simp only [hrest, Option.map_none'] at h
                  nomatch h
              | some v0 =>
                  simp only [hrest, Option.map_some'] at h
                  injection h with hv
                  have ⟨stored, tail, hg, heq⟩ := ih hrest
                  refine ⟨stored, tail, ?_, ?_⟩
                  · simp only [getLet]; exact hg
                  · subst hv
                    rw [heq]
                    exact (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                      (Nat.zero_le _) stored)

/-- Type-level dual of `getLet_of_lookup` (that one is `Exists`/Prop).
bvarZeta of `parRed_develWfGo` matches in Type. -/
noncomputable def getLet_of_lookup_sig {Γ : LCtx} {i : Nat} {v : Expr Nat}
    (h : lookupValue Γ i = some v) :
    Σ' (stored : Expr Nat) (tail : LCtx),
      (getLet Γ i = some (stored, tail)) ×' (v = lift 0 (i + 1) stored) := by
  induction Γ generalizing i v with
  | nil =>
      simp only [lookupValue, List.get?] at h
      nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero =>
              simp only [lookupValue, List.get?_cons_zero] at h
              nomatch h
          | succ i' =>
              rw [lookupValue_cons_succ] at h
              cases hrest : lookupValue rest i' with
              | none =>
                  simp only [hrest, Option.map_none'] at h
                  nomatch h
              | some v0 =>
                  simp only [hrest, Option.map_some'] at h
                  injection h with hv
                  have ⟨stored, tail, hg, heq⟩ := ih hrest
                  refine ⟨stored, tail, ?_, ?_⟩
                  · simp only [getLet]; exact hg
                  · subst hv
                    rw [heq]
                    exact (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                      (Nat.zero_le _) stored)
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [lookupValue, List.get?_cons_zero, getLet] at h ⊢
              injection h with hv
              subst hv
              exact ⟨val, rest, rfl, rfl⟩
          | succ i' =>
              rw [lookupValue_cons_succ] at h
              cases hrest : lookupValue rest i' with
              | none =>
                  simp only [hrest, Option.map_none'] at h
                  nomatch h
              | some v0 =>
                  simp only [hrest, Option.map_some'] at h
                  injection h with hv
                  have ⟨stored, tail, hg, heq⟩ := ih hrest
                  refine ⟨stored, tail, ?_, ?_⟩
                  · simp only [getLet]; exact hg
                  · subst hv
                    rw [heq]
                    exact (lift_lift_merge 1 (i' + 1) 0 0 (Nat.le_refl 0)
                      (Nat.zero_le _) stored)

theorem iotaLhsOf_is_app {E : ResolvedEnv} (w : IotaWitness E) :
    iotaLhsOf w =
      .app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w) :=
  foldApps_snoc (.const w.recRef w.ls) (ctorMajor w) w.preMajor

theorem letsCount_assumption (A : Expr Nat) (Γ : LCtx) :
    letsCount (.assumption A :: Γ) = letsCount Γ := rfl

theorem letsCount_letBinding (A v : Expr Nat) (Γ : LCtx) :
    letsCount (.letBinding A v :: Γ) = letsCount Γ + 1 := rfl

noncomputable def getLet_split {Γ : LCtx} {i : Nat} {v : Expr Nat} {tail : LCtx}
    (h : getLet Γ i = some (v, tail)) :
    Σ' (pre : LCtx) (A : Expr Nat),
      (Γ = pre ++ (.letBinding A v :: tail)) ×' (pre.length = i) := by
  induction Γ generalizing i with
  | nil => nomatch h
  | cons d rest ih =>
      cases d with
      | assumption A =>
          cases i with
          | zero => nomatch h
          | succ i' =>
              simp only [getLet] at h
              have ⟨pre, A', heq, hlen⟩ := ih h
              refine ⟨.assumption A :: pre, A', ?_, ?_⟩
              · simp only [List.cons_append]; exact congrArg _ heq
              · simp only [List.length_cons, hlen]
      | letBinding A val =>
          cases i with
          | zero =>
              simp only [getLet] at h
              injection h with hpair
              cases hpair
              exact ⟨[], A, rfl, rfl⟩
          | succ i' =>
              simp only [getLet] at h
              have ⟨pre, A', heq, hlen⟩ := ih h
              refine ⟨.letBinding A val :: pre, A', ?_, ?_⟩
              · simp only [List.cons_append]; exact congrArg _ heq
              · simp only [List.length_cons, hlen]

end Rcic.Declarative
