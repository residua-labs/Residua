/-
RCIC F-05b — typed conversion characterization on the `RedOnly`
fragment (00 §19.3 F-05b; §19.2 rows SortConvChar / PiConvInj /
FamAppConvInj; §20.2 shape rules; §20.3 diamond conventions).

WHAT IS DISCHARGED HERE. `convRedOnly_join` sends every `Conv`
derivation that uses neither `Conv.eta` nor `Conv.irr` to an EXACT
parallel-reduction join (`Σ' d, a ⇒* d ×' b ⇒* d`), and the three
corollaries `sortConvChar_redOnly` / `piConvInj_redOnly` /
`famAppConvInj_redOnly` read the three §19.2 rows off that join.

THE ROWS STAY OPEN. Each corollary is its §19.2 row MINUS exactly one
premise (`RedOnly`), with `EnvWf` and `CtxWf` kept in the signature
(`CtxWf` is unused on this fragment — it re-enters only with the
`irr` arm), so the successor segment's work is a PREMISE DELETION,
not a re-statement. `RedOnly` is a `Prop`-valued recursion on the
derivation — one arm per constructor, the idiom the (since
discharged and deleted) `StepLevelCoherent` / `StepIndexCoherent`
established — NOT a mirror `Conv` inductive: a mirror would be an M-001 second
authority for the conversion judgment.

WHY `eta` / `irr` are cut by the predicate rather than by a proof.
`ParRed` has no η, so an EXACT join is false at `Conv.eta`
(`etaExpand_ne_sort` records the shape); joining up to an η-residual
needs η-postponement past `⇒*`, whose `eta` case must re-establish
`HasTy Γ c (.pi A' B')` after a step — subject reduction. The `irr`
arm needs "no type is a proof", whose only route on this tree
transports the SUBJECT along a conversion — subject reduction again.
Both land on the same lemma, `parRedSR` — which is NOT DT-010/011:
`Steps` (`RcicDTMeta`) is built from `Step`, which has no congruence
constructors, so `ParRed ⊄ Steps` and DT-011 does not cover a parallel
step under a binder.

`parRedSR` IS NOW LANDED, in `RcicParRedSR.lean`, as a CONDITIONAL
theorem, on the nose:

    parRedSR (hpci : PiConvInj E n) (hfaci : FamAppConvInj E n)
      (hE : EnvWf E n) (hΓ : CtxWf E n Γ)
      (h : HasTy E n Γ e A) (hr : ParRed E n Γ e e') :
      HasTy E n Γ e' A

A THIRD premise this quote once carried is gone for the same reason:
`hLitP : LitPreserve E n`, deleted by segment 7a's O-2 when that row
was discharged VACUOUSLY (00 §19.7 E-LitP — `HasTy` then had no `lit`
rule). TRIPWIRE FIRED (DT-017, 00 §20.11): `HasTy.lit` landed and that
patch took E-LitP's FIRST disjunct — `LitPreserve` is discharged FOR
REAL by the sealed `litPreserve` (`RcicInvertFamily.lean`), which reads
02 §8's typing content off the derivation via `hasTyLitInv` and
transports it with `HasTy.conv`; `hLitP` is re-carried NOWHERE and
this signature is unchanged.

Two premises the earlier projection of this signature carried are gone,
each because its row discharged: `ParRedLevelCoherent hr` (00 §20.6 —
`HasTy.const` now concludes at `instantiateLevels ls m.mtype`, so the
major's constructor universes are forced by typing,
`iotaLhs_ctorParams_levels_conv`) and its index sibling
`ParRedIndexCoherent hr`, which was never built: 00 §19.2 erratum 6
restated the index fact at the conversion layer (`IndexCoherentConv`)
and DISCHARGED it (`iotaLhs_ctorIdx_conv`), so `iotaPreserve` carries
no per-redex premise for the `iotaSpine` arm to supply. Both §19.4
`02 universes ──→ F-05b` edges are deleted with them. Writing
`ParRedIndexCoherent` would additionally have broken the `Prop`-recursion
idiom, being `ConvArgs`- hence `Type`-valued.

WHAT `parRedSR` DOES NOT DO. It does not open the three §19.2 rows. It
consumes `hpci` at two of thirteen arms (`beta`, `iotaSpine`), so the
ring's third edge survives; the corrections that DID come out of
building it are recorded as attempt 54 below.

WALL RECORD (00 §19.3 wall protocol) — attempt 53 in `RcicParRed.lean`'s
global attempt sequence; attempt 15 on the Conv-recursion lane
(11-13 at `RcicParRed.lean`'s header, 14 at its attempt-14 block).

  Failing statement: the typed conversion characterization under
  `EnvWf` + `CtxWf` whose `irr` arm is cut by the subject's typing, by
  any recursion measured on `sizeConv` / `sizeHasTy` over the landed
  judgments.

  Re-diagnosis of attempts 11-14: their recorded cause ("reconstructed
  `trans` is not a subterm") is a TERMINATION reading of what is, for
  the join design landed here, an UNBOUNDED-OUTPUT problem, and for
  the naive typed statement an INVARIANT-PROPAGATION problem.
  (i) In this file `trans` is free — no typing invariant is carried,
  and the middle is joined by star confluence. What does not decrease
  is `parRedSR → PiConvInj`: in the app-congruence arm SR knows
  `Conv Γ (.pi A B) T_f` only as the OUTPUT of its own IH, an object
  with no size bound relative to its input, and no strengthening
  bounds it (`convSubst` / `convSubstLet` build `Conv`s of
  uncontrolled size). `oneStepSR`'s use of `hpci` does decrease
  (`hcv_lam` comes from `hasTyLamInv hf`, a subderivation) — which is
  why head-reduction SR exists today and the parallel one does not.
  [CORRECTED by C-1, attempt 54 below: the app-congruence arm names an
  AVOIDABLE inversion and needs no `PiConvInj` at all. The hop
  survives, but at `beta`, not here.]
  (ii) A typing side condition on the endpoints does not survive an
  induction over `Conv` at all: `Step.beta` carries no typing premises
  and `Conv.refl` holds at every term, so a `Conv` between two types
  passes through UNTYPED middles (`trans`), and the congruence arms do
  not type their components either (`app`, `letE`).

  Consequence recorded so attempt 16 does not re-derive it: the ring
  is `characterization → noTypeIsProof → parRedSR → PiConvInj →
  characterization`; the first two hops decrease on
  `sizeConv`/`sizeHasTy` (`sizeConv_hasTySortInv` is sealed for
  exactly that argument), the `parRedSR → PiConvInj` hop does not.

ROUTE CHANGE (00 §19.3 wall protocol) — attempt 54 in
`RcicParRed.lean`'s global attempt sequence; attempt 16 on the
Conv-recursion lane. NOT a retry of attempt 53: the attempt-53
statement is neither re-attempted nor abandoned; it is re-diagnosed,
and three of its recorded reasons are CORRECTED (O-3; no sealed
statement is touched by the corrections themselves).

  C-1. The app-congruence arm of `parRedSR` needs NO `PiConvInj`.
  Attempt 53's sentence above names an inversion that is AVOIDABLE, not
  a necessity: `hasTyAppInv` returns the function's Π-typing directly,
  `HasTy.conv ∘ Conv.symm` consumes an IH output without inverting it,
  and the argument's movement is absorbed by `conv_instantiate0_value`
  (`RcicDTMeta`), which carries no typing premise. Measured on the
  landed theorem: `hpci` enters at exactly TWO of thirteen arms.
  The ring's third edge SURVIVES, at `beta`, where the Π-conversion is
  `hasTyLamInv`'s — a SUBDERIVATION of the input typing, byte-identical
  to `oneStepSR.beta`'s consumption. C-1 corrects WHERE the row is
  consumed; it does not open it.

  C-2. `parRedSR` is stated ON THE NOSE (`HasTy Γ e' A`), not
  `Σ' B, HasTy e' B ×' Conv A B`. Interderivable, so not a
  strengthening — it is the form `IotaPreserve`, `LitPreserve`
  (discharged FOR REAL by `litPreserve` since segment 10 — 00
  §20.11, §19.7 E-LitP2 / E-LitP3 — not a premise) and four of
  `oneStepSR`'s six arms already have, and it deletes the
  `SortConvChar` consumption the Σ′ form's `lam` / `pi` arms would
  otherwise need to re-establish that the IH's output type IS a
  sort. Recorded honestly, not oversold: the Σ′ form can also avoid
  that consumption, by `HasTy.conv ∘ Conv.symm`; the nose form's
  real merit is uniformity with the landed statements.

  C-3. The three `irr` cuts do NOT factor through one statement — not
  because the candidate is false, but because it is not cheaper. The
  candidate — `NoSortProp`: `CtxWf Γ → Conv Γ (.sort w) P →
  HasTy Γ P (.sort .zero) → False`, instantiated at `w := .succ u`
  (`SortConvChar`), `w := .imax u v` (`PiConvInj`) and the family's
  result universe (`FamAppConvInj`) — is BLOCKED at its `.pi` arm on an
  unlanded row, and the read-out is compiled, not argued:
  `noSortProp_piArm_witness` / `noSortProp_piArm_readout`
  (`RcicParRedSR`). `hasTyPiInv` hands back
  `Conv Γ (.sort (.imax u v)) T`, so all the typing hypothesis yields
  at that arm is the level equation `eqN (.imax u v) .zero` — which is
  TRUE at `v = .zero` (`eqN_imax_zero`); and `Π (Q : Prop). Q : Prop`
  is inhabited at EVERY `E`, `n` and `Γ`, so neither `EnvWf` nor
  `CtxWf` (§19.2 erratum 2 / erratum 3) can cut it. The arm therefore
  rests entirely on `Conv Γ (.sort w) (.pi A B) → False`, "no sort
  converts to a Π" — neither `SortConvChar` (both ends sorts) nor
  `PiConvInj` (both ends Π), not on the §19.2 ledger, NOT introduced
  here (inventing an obligation to save an arm is growing a rule out of
  one's own failure), and a characterization row of the very ring the
  statement was meant to shortcut. Type-④ evidence of NON-CLOSURE BY
  INVERSION PLUS LEVEL ARITHMETIC; NOT a refutation — the artifact
  constructs no `Conv Γ (.sort w) (.pi A B)` and claims none
  (corrected 2026-09-05 after a review finding on #3815: the earlier
  wording "REFUTED" over-claimed). `NoSortProp` itself is deliberately
  not defined, so nothing reads its target from an editable definition.

  RESIDUAL AFTER THIS SEGMENT, NAMED — two items, neither attempted:
  * the `irr` cut ON THE TYPED FRAGMENT. With `NoSortProp` no shortcut
    (C-3) and an untyped `Conv → Join` unavailable (`Conv.irr` is what
    `RedOnly` excises), the cut must be met at INNER `trans` nodes with
    arbitrary endpoints, where `hasTySortInv` is inapplicable.
  * ETA-POSTPONEMENT past `⇒*`: `ParRed` has no η, so an exact join is
    false at `Conv.eta`.
  `closure_claim` stays 0; the three §19.2 rows stay OPEN with
  `RedOnly` still on them.

TWO STATEMENT CORRECTIONS against the segment plan, listed per O-3
(no sealed statement is touched; both are NEW statements):
* `parRedCtx_trans` ("pointwise composition") is NOT available at the
  one-step level: `ParRed` is deliberately not transitive (00 §20.2
  TML shape — a constructor premise carries one step, never a star).
  The transitivity the star confluence needs lives on the context
  STAR and is landed as `parRedCtxStar_trans`.
* `parRedStar_diamond_ctx` is landed with ONE common context star
  (`ParRedCtxStar E n Γ Δ`) instead of two independent ones
  (`Γ →* Γ₁`, `Γ →* Γ₂`). The two-context form at ONE step is
  `parRed_strip_ctx` below (the plan's signature, verbatim); the
  two-context form at STAR level would need cross-context simulation
  (a reduction performed in `Γ₂` replayed in `Γ₁` through the let
  values `ParRed.bvarZeta` reads), which is a new induction with no
  consumer here. The `Conv.letE` arm needs exactly the common-target
  form: both `letBinding A v :: Γ` and `letBinding A' v' :: Γ`
  ctx-star-reduce to `letBinding dA dv :: Γ`.
-/
import rcic.RcicParRed

namespace Rcic.Declarative

set_option maxHeartbeats 1000000

/-! ### C1.3 — the context star and its confluence

`ParRedCtx` (`RcicParRed.lean`) is ONE pointwise parallel step on a
context. The `Conv.letE` arm relates two bodies whose contexts differ
in BOTH the let type and the let value, and the component conversions
deliver STARS on each — so the context transport it needs is the star
closure. -/

/-- Multi-step pointwise parallel reduction of a local context. -/
inductive ParRedCtxStar (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type
  | refl (Γ : LCtx) : ParRedCtxStar E n Γ Γ
  | tail {Γ Δ Θ : LCtx} (h : ParRedCtx E n Γ Δ)
      (hs : ParRedCtxStar E n Δ Θ) : ParRedCtxStar E n Γ Θ

def parRedCtxStar_one {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (h : ParRedCtx E n Γ Δ) : ParRedCtxStar E n Γ Δ :=
  .tail h (.refl _)

/-- Transitivity of the context star. (The one-step `ParRedCtx` is NOT
transitive: `ParRed` carries one step by 00 §20.2.) -/
def parRedCtxStar_trans {E : ResolvedEnv} {n : Nat} :
    {Γ Δ Θ : LCtx} →
    ParRedCtxStar E n Γ Δ → ParRedCtxStar E n Δ Θ → ParRedCtxStar E n Γ Θ
  | _, _, _, .refl _, hs => hs
  | _, _, _, .tail h ht, hs => .tail h (parRedCtxStar_trans ht hs)

/-- Strip lemma over a ONE-STEP context reduction on each side
(`parRed_strip` with `parRedCtx_refl` replaced by the supplied
`ParRedCtx`; the one-step diamond is already ctx-generalized by
00 §20.3, so nothing new is proved about `ParRed`). -/
noncomputable def parRed_strip_ctx {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ Γ₁ Γ₂ : LCtx} :
    {a b c : Expr Nat} →
    ParRed E n Γ a b → ParRedStar E n Γ a c →
    ParRedCtx E n Γ Γ₁ → ParRedCtx E n Γ Γ₂ →
    Σ' (d : Expr Nat),
      ParRedStar E n Γ₁ b d ×' ParRedStar E n Γ₂ c d
  | _, _, _, h, .refl _ _, hΓ1, hΓ2 =>
      let ⟨d, hd1, hd2⟩ := parRed_diamond E n hE h (.refl _ _) hΓ1 hΓ2
      ⟨d, parRedStar_one hd1, parRedStar_one hd2⟩
  | _, _, _, h, .tail h0 hs, hΓ1, hΓ2 =>
      let ⟨_m, hm1, hm2⟩ :=
        parRed_diamond E n hE h h0 hΓ1 (parRedCtx_refl _)
      let ⟨d, hd1, hd2⟩ := parRed_strip_ctx hE hm2 hs hΓ1 hΓ2
      ⟨d, .tail hm1 hd1, hd2⟩

/-- Star diamond over a ONE-STEP context reduction on each side. -/
noncomputable def parRedStar_diamond_ctx1 {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ Γ₁ Γ₂ : LCtx} :
    {a b c : Expr Nat} →
    ParRedStar E n Γ a b → ParRedStar E n Γ a c →
    ParRedCtx E n Γ Γ₁ → ParRedCtx E n Γ Γ₂ →
    Σ' (d : Expr Nat),
      ParRedStar E n Γ₁ b d ×' ParRedStar E n Γ₂ c d
  | _, _, _, .refl _ _, s2, hΓ1, hΓ2 =>
      parRed_strip_ctx hE (.refl _ _) s2 hΓ1 hΓ2
  | _, _, _, .tail h hs, s2, hΓ1, hΓ2 =>
      let ⟨_m, hm1, hm2⟩ :=
        parRed_strip_ctx hE h s2 (parRedCtx_refl _) hΓ2
      let ⟨d, hd1, hd2⟩ := parRedStar_diamond_ctx1 hE hs hm1 hΓ1 hΓ2
      ⟨d, hd1, parRedStar_trans hm2 hd2⟩

/-- Replay a star in a ONE-STEP context reduct: the source and the
target of the star meet again in `Δ`. -/
noncomputable def parRedStar_replay_ctx {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ Δ : LCtx} {a b : Expr Nat}
    (s : ParRedStar E n Γ a b) (hΓ : ParRedCtx E n Γ Δ) :
    Σ' (d : Expr Nat),
      ParRedStar E n Δ a d ×' ParRedStar E n Δ b d :=
  let ⟨d, h1, h2⟩ := parRedStar_diamond_ctx1 hE s (.refl _ _) hΓ hΓ
  ⟨d, h2, h1⟩

/-- Replay a star along a context STAR. -/
noncomputable def parRedStar_replay_ctxStar {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ Δ : LCtx} → ParRedCtxStar E n Γ Δ →
    {a b : Expr Nat} → ParRedStar E n Γ a b →
    Σ' (d : Expr Nat),
      ParRedStar E n Δ a d ×' ParRedStar E n Δ b d
  | _, _, .refl _, _, _, s => ⟨_, s, .refl _ _⟩
  | _, _, .tail hc Cs, _, _, s =>
      let ⟨_m, hx, hy⟩ := parRedStar_replay_ctx hE s hc
      let ⟨_d1, hx1, hm1⟩ := parRedStar_replay_ctxStar hE Cs hx
      let ⟨_d2, hy2, hm2⟩ := parRedStar_replay_ctxStar hE Cs hy
      let ⟨e, he1, he2⟩ := parRedStar_diamond hE hm1 hm2
      ⟨e, parRedStar_trans hx1 he1, parRedStar_trans hy2 he2⟩

/-- Star confluence in a common context-star reduct: the two stars are
joined in `Δ`, not in `Γ`. This is what `Conv.letE` needs — both
`letBinding A v :: Γ` and `letBinding A' v' :: Γ` reduce to
`letBinding dA dv :: Γ`. -/
noncomputable def parRedStar_diamond_ctx {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ Δ : LCtx} {a b c : Expr Nat}
    (s1 : ParRedStar E n Γ a b) (s2 : ParRedStar E n Γ a c)
    (C : ParRedCtxStar E n Γ Δ) :
    Σ' (d : Expr Nat),
      ParRedStar E n Δ b d ×' ParRedStar E n Δ c d :=
  let ⟨_e1, ha1, hb1⟩ := parRedStar_replay_ctxStar hE C s1
  let ⟨_e2, ha2, hc2⟩ := parRedStar_replay_ctxStar hE C s2
  let ⟨d, hd1, hd2⟩ := parRedStar_diamond hE ha1 ha2
  ⟨d, parRedStar_trans hb1 hd1, parRedStar_trans hc2 hd2⟩

/-! ### Context stars at a `letBinding` head -/

def parRedCtxStar_letE_ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Expr Nat} :
    {A A' : Expr Nat} → ParRedStar E n Γ A A' →
    ParRedCtxStar E n (.letBinding A v :: Γ) (.letBinding A' v :: Γ)
  | _, _, .refl _ _ => .refl _
  | _, _, .tail h hs =>
      .tail (.letBinding h (.refl _ _) (parRedCtx_refl Γ))
        (parRedCtxStar_letE_ty hs)

def parRedCtxStar_letE_val {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} :
    {v v' : Expr Nat} → ParRedStar E n Γ v v' →
    ParRedCtxStar E n (.letBinding A v :: Γ) (.letBinding A v' :: Γ)
  | _, _, .refl _ _ => .refl _
  | _, _, .tail h hs =>
      .tail (.letBinding (.refl _ _) h (parRedCtx_refl Γ))
        (parRedCtxStar_letE_val hs)

def parRedCtxStar_letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat}
    (hA : ParRedStar E n Γ A A') (hv : ParRedStar E n Γ v v') :
    ParRedCtxStar E n (.letBinding A v :: Γ) (.letBinding A' v' :: Γ) :=
  parRedCtxStar_trans (parRedCtxStar_letE_ty hA) (parRedCtxStar_letE_val hv)

/-! ### C1.4 — pointwise star on argument lists, and the star closure
of the (total) inductive-family spine inversion -/

/-- Pointwise MULTI-step parallel reduction of an argument list. The
`ParRedArgs` sibling at star level; `ConvArgs` is the consumer, which
is why this carries the reductions and not just the length (the
constructor-headed star inversion drops to `length` because its
consumer is an arity count). Not mutual with `ParRed`, and it appears
in no `ParRed` constructor premise — 00 §20.2 is not in play. -/
inductive ParRedStarArgs (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → Type
  | nil : ParRedStarArgs E n Γ [] []
  | cons {x y : Expr Nat} {xs ys : List (Expr Nat)}
      (h : ParRedStar E n Γ x y) (hs : ParRedStarArgs E n Γ xs ys) :
      ParRedStarArgs E n Γ (x :: xs) (y :: ys)

def parRedStarArgs_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) → ParRedStarArgs E n Γ xs xs
  | [] => .nil
  | _ :: xs => .cons (.refl _ _) (parRedStarArgs_refl xs)

def parRedStarArgs_one {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs ys : List (Expr Nat)} →
    ParRedArgs E n Γ xs ys → ParRedStarArgs E n Γ xs ys
  | _, _, .nil _ => .nil
  | _, _, .cons h t => .cons (parRedStar_one h) (parRedStarArgs_one t)

def parRedStarArgs_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs ys zs : List (Expr Nat)} →
    ParRedStarArgs E n Γ xs ys → ParRedStarArgs E n Γ ys zs →
    ParRedStarArgs E n Γ xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 =>
      .cons (parRedStar_trans h1 h2) (parRedStarArgs_trans t1 t2)

def parRedStarArgs_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs xs' ys ys' : List (Expr Nat)} →
    ParRedStarArgs E n Γ xs xs' → ParRedStarArgs E n Γ ys ys' →
    ParRedStarArgs E n Γ (xs ++ ys) (xs' ++ ys')
  | _, _, _, _, .nil, h2 => h2
  | _, _, _, _, .cons h t, h2 => .cons h (parRedStarArgs_append t h2)

theorem parRedStarArgs_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs ys : List (Expr Nat)} →
    ParRedStarArgs E n Γ xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by
      simp only [List.length_cons, parRedStarArgs_length t]

/-- Star closure of the TOTAL one-step inductive-family spine
inversion (`parRed_foldApps_inductive`). The head is rigid because
`EnvWf.indMember` gives `hnobody` (no delta) and the member is not a
recursor (no iota); `harity` (§19.2 erratum 3) is what makes the row
it feeds true at all. -/
def parRedStar_foldApps_inductive {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM) :
    {e t : Expr Nat} →
    ParRedStar E n Γ e t →
    (xs : List (Expr Nat)) →
    e = foldApps (.const r ls) xs →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        ParRedStarArgs E n Γ xs xs'
  | _, _, .refl _ _, xs, heq => by
      subst heq
      exact ⟨ls, xs, rfl, eqNList_refl ls, parRedStarArgs_refl xs⟩
  | _, _, .tail h0 hs, xs, heq =>
      let ⟨_ls1, xs1, heq1, q1, hargs⟩ :=
        parRed_foldApps_inductive hres hK h0 xs heq
      let ⟨ls2, xs2, heq2, q2, hargs2⟩ :=
        parRedStar_foldApps_inductive hres hK hs xs1 heq1
      ⟨ls2, xs2, heq2, eqNList_trans q1 q2,
        parRedStarArgs_trans (parRedStarArgs_one hargs) hargs2⟩

/-- A const-headed application spine determines its levels and its
arguments. -/
theorem foldApps_const_inj {r r' : Nat} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)}
    (h : foldApps (.const r ls) xs = foldApps (.const r' ls') xs') :
    (Expr.const r ls : Expr Nat) = .const r' ls' ∧ xs = xs' := by
  have h1 := congrArg appsSpine h
  rw [appsSpine_foldApps, appsSpine_foldApps] at h1
  have h2 : ((appsSpine (Expr.const r ls : Expr Nat)).1,
      (appsSpine (Expr.const r ls : Expr Nat)).2 ++ xs) =
      ((appsSpine (Expr.const r' ls' : Expr Nat)).1,
        (appsSpine (Expr.const r' ls' : Expr Nat)).2 ++ xs') := h1
  simp only [appsSpine, List.nil_append] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-! ### C1.5 — a literal's sort reducts factor through its expansion

The plan asked for `parRedStar_lit_ne_sort :
ParRedStar Γ (.lit t) (.sort u) → False`. That statement is NOT
provable on this tree: after the first step the star sits at
`natExpand t`, which is a CONSTANT application (`litZero` / `litSucc`
over `const 1` / `const 2` — 05 §3's member order since 00 §19.7
E-NatRef), and nothing in the landed `EnvWf`
forbids a transparent member at those references from delta-reducing
to a sort. `natExpand_ne_sort` (sealed) is a syntactic
non-equality, not a reduction fact. What IS a theorem — and what the
`.lit` summand of a `Step` inversion actually needs — is that any
such star factors through the expansion. -/
def parRedStar_lit_sort_via_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {u : Level} :
    {a e : Expr Nat} →
    ParRedStar E n Γ a e → a = .lit t → e = .sort u →
    ParRedStar E n Γ (natExpand t) (.sort u)
  | _, _, .refl _ _, ha, he => by
      subst ha
      exact nomatch he
  | _, _, .tail h0 hs, ha, he =>
      match parRed_lit h0 ha with
      | .inl hlit => parRedStar_lit_sort_via_expand hs hlit he
      | .inr hexp => by
          subst he
          subst hexp
          exact hs

/-! ### The `Step` → `ParRed` embedding, total

`step_parRed` (sealed) returns a SUM whose `.lit` summand is dead but
must be matched, and that summand carries no relation between the
step's target and the expansion — so it cannot be discharged by its
consumer. The total form is the same construction with the sum
removed; the `.lit` arm reads `LiteralExpansion.of`, which fixes
`exp = natExpand t`. -/
def step_to_parRed {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} →
    Step E n Γ a b → ParRed E n Γ a b
  | _, _, _, .beta Γ A body arg =>
      .beta Γ A A body body arg arg (.refl _ _) (.refl _ _) (.refl _ _)
  | _, _, _, .zeta Γ A value body =>
      .zeta Γ A A value value body body (.refl _ _) (.refl _ _) (.refl _ _)
  | _, _, _, .zetaLocal Γ i v h =>
      match hg : Γ.get? i with
      | some (.letBinding A v0) =>
          have hv : v = lift 0 (i + 1) v0 := by
            simp only [lookupValue, hg] at h
            exact Option.some.inj h.symm
          hv ▸ .bvarZeta Γ i A v0 v0 hg (.refl _ _)
      | some (.assumption _) => by
          simp only [lookupValue, hg] at h; cases h
      | none => by
          simp only [lookupValue, hg] at h; cases h
  | _, _, _, .delta Γ r ls m b hres hbody htr =>
      .delta Γ r ls m b hres hbody htr
  | _, _, _, .iota Γ _lhs _rhs hι =>
      match hι with
      | .of w =>
          Eq.mpr
            (congrArg (fun e => ParRed E n Γ e (iotaRhsOf w))
              (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]))
            (.iotaSpine Γ w w.ls w.lsC
              (by
                induction w.ls with
                | nil => exact True.intro
                | cons _ _ ih => exact ⟨eqN_refl _, ih⟩)
              (by
                induction w.lsC with
                | nil => exact True.intro
                | cons _ _ ih => exact ⟨eqN_refl _, ih⟩)
              w.preMajor w.preMajor
              (w.ctorParams ++ w.fields)
              (w.ctorParams ++ w.fields)
              (parRedArgs_refl _) (parRedArgs_refl _)
              rfl rfl
              (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]))
  | _, _, _, .lit Γ t _exp h =>
      match h with
      | .of _ => .lit Γ t

/-! ### C2 — the fragment predicate

00 §18.3 rule: this is a `Prop`-valued RECURSION on the derivation
(the idiom the since-deleted `StepLevelCoherent` / `StepIndexCoherent`
established), one arm per `Conv` constructor,
transcribed from `RcicDeclarative.lean`'s `Conv` — none added, none
dropped. `eta` and `irr` are the two arms the join cannot reach; they
map to `False`, so a `RedOnly` derivation is exactly one that uses
neither generator. -/
def RedOnly {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → Conv E n Γ a b → Prop
  | _, _, _, .refl _ _                    => True
  | _, _, _, .symm _ _ _ h                => RedOnly h
  | _, _, _, .trans _ _ _ _ h1 h2         => RedOnly h1 ∧ RedOnly h2
  | _, _, _, .step _ _ _ _                => True
  | _, _, _, .app _ _ _ _ _ h1 h2         => RedOnly h1 ∧ RedOnly h2
  | _, _, _, .lam _ _ _ _ _ hA hb         => RedOnly hA ∧ RedOnly hb
  | _, _, _, .pi _ _ _ _ _ hA hb          => RedOnly hA ∧ RedOnly hb
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      RedOnly hA ∧ RedOnly hv ∧ RedOnly hb
  | _, _, _, .sorts _ _ _ _               => True
  | _, _, _, .consts _ _ _ _ _            => True
  | _, _, _, .eta _ _ _ _ _               => False
  | _, _, _, .irr _ _ _ _ _ _ _           => False

/-! ### C2 — the characterization

No typing invariant is carried, so neither propagation failure of the
attempt-11-14 lane applies: `trans` is discharged by star confluence
and the congruence arms by the sealed star congruences. `CtxWf` is
not a premise. -/
noncomputable def convRedOnly_join {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {a b : Expr Nat} → (c : Conv E n Γ a b) → RedOnly c →
    Σ' (d : Expr Nat),
      ParRedStar E n Γ a d ×' ParRedStar E n Γ b d
  | _, _, _, .refl _ a, _ => ⟨a, .refl _ _, .refl _ _⟩
  | _, _, _, .symm _ _ _ h, hr =>
      let ⟨d, h1, h2⟩ := convRedOnly_join hE h hr
      ⟨d, h2, h1⟩
  | _, _, _, .trans _ _ _ _ h1 h2, hr =>
      let ⟨_d1, ha1, hm1⟩ := convRedOnly_join hE h1 hr.1
      let ⟨_d2, hm2, hc2⟩ := convRedOnly_join hE h2 hr.2
      let ⟨e, he1, he2⟩ := parRedStar_diamond hE hm1 hm2
      ⟨e, parRedStar_trans ha1 he1, parRedStar_trans hc2 he2⟩
  | _, _, _, .step _ _ _ hs, _ =>
      ⟨_, parRedStar_one (step_to_parRed hs), .refl _ _⟩
  | _, _, _, .app _ _ _ _ _ h1 h2, hr =>
      let ⟨_df, hf1, hf2⟩ := convRedOnly_join hE h1 hr.1
      let ⟨_dx, hx1, hx2⟩ := convRedOnly_join hE h2 hr.2
      ⟨_, parRedStar_app_congr hf1 hx1, parRedStar_app_congr hf2 hx2⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, hr =>
      let ⟨_dA, hA1, hA2⟩ := convRedOnly_join hE hA hr.1
      let ⟨_db, hb1, hb2⟩ := convRedOnly_join hE hb hr.2
      ⟨_, parRedStar_lam_congr hA1 hb1,
        parRedStar_lam_congr hA2 (parRedStar_replace_assump hb2)⟩
  | _, _, _, .pi _ _ _ _ _ hA hb, hr =>
      let ⟨_dA, hA1, hA2⟩ := convRedOnly_join hE hA hr.1
      let ⟨_db, hb1, hb2⟩ := convRedOnly_join hE hb hr.2
      ⟨_, parRedStar_pi_congr hA1 hb1,
        parRedStar_pi_congr hA2 (parRedStar_replace_assump hb2)⟩
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb, hr =>
      -- The two bodies are related at the LEFT `letBinding A v :: Γ`
      -- (read the constructor). `parRedStar_replace_let` moves the
      -- TYPE only, and `ParRed.bvarZeta` reads the VALUE — so the
      -- transport is a context STAR: both `letBinding A v :: Γ` and
      -- `letBinding A' v' :: Γ` reduce to `letBinding dA dv :: Γ`,
      -- where the two body stars are re-joined.
      let ⟨_dA, hA1, hA2⟩ := convRedOnly_join hE hA hr.1
      let ⟨_dv, hv1, hv2⟩ := convRedOnly_join hE hv hr.2.1
      let ⟨_db, hb1, hb2⟩ := convRedOnly_join hE hb hr.2.2
      let C := parRedCtxStar_letE hA1 hv1
      let ⟨_e1, hb1Δ, hd1Δ⟩ := parRedStar_replay_ctxStar hE C hb1
      let ⟨_e2, hb2Δ, hd2Δ⟩ := parRedStar_replay_ctxStar hE C hb2
      let ⟨_X, hX1, hX2⟩ := parRedStar_diamond hE hd1Δ hd2Δ
      ⟨_,
        parRedStar_trans (parRedStar_letE_val hv1)
          (parRedStar_trans (parRedStar_letE_ty hA1)
            (parRedStar_letE_body (parRedStar_trans hb1Δ hX1))),
        parRedStar_trans (parRedStar_letE_val hv2)
          (parRedStar_trans (parRedStar_letE_ty hA2)
            (parRedStar_letE_body (parRedStar_trans hb2Δ hX2)))⟩
  | _, _, _, .sorts _ l₁ l₂ h, _ =>
      ⟨.sort l₂, parRedStar_one (.sortEq _ l₁ l₂ h), .refl _ _⟩
  | _, _, _, .consts _ r ls ls' h, _ =>
      ⟨.const r ls', parRedStar_one (.consts _ r ls ls' h), .refl _ _⟩
  | _, _, _, .eta _ _ _ _ _, hr => False.elim hr
  | _, _, _, .irr _ _ _ _ _ _ _, hr => False.elim hr

/-! ### C2 — the three 00 §19.2 rows on the `RedOnly` fragment

Each statement below is its §19.2 row MINUS exactly one premise
(`RedOnly`). `CtxWf` is threaded and UNUSED here (`_hΓ`) on purpose:
it is what cuts the `irr` arm, which this fragment excludes by
hypothesis, so keeping it makes the eventual full discharge a premise
deletion rather than a re-statement. The rows stay open. -/

/-- Pointwise `Conv` from two pointwise stars into a common list. -/
def convArgs_of_parRedStarArgs {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} :
    {xs xs' ys : List (Expr Nat)} →
    ParRedStarArgs E n Γ xs ys → ParRedStarArgs E n Γ xs' ys →
    ConvArgs E n Γ xs xs'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 =>
      .cons
        (.trans _ _ _ _ (parRedStar_to_conv hE h1)
          (.symm _ _ _ (parRedStar_to_conv hE h2)))
        (convArgs_of_parRedStarArgs hE t1 t2)

/-- `SortConvChar` on the `RedOnly` fragment (00 §19.2 row
`SortConvChar`, minus `RedOnly`). -/
theorem sortConvChar_redOnly {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} (_hΓ : CtxWf E n Γ) {u v : Level}
    (c : Conv E n Γ (.sort u) (.sort v)) (hr : RedOnly c) : eqN u v :=
  let ⟨_d, h1, h2⟩ := convRedOnly_join hE c hr
  let ⟨_w1, e1, q1⟩ := parRedStar_sort h1 rfl
  let ⟨_w2, e2, q2⟩ := parRedStar_sort h2 rfl
  by
    have hsort : (Expr.sort _w1 : Expr Nat) = .sort _w2 := e1.symm.trans e2
    injection hsort with hw
    subst hw
    exact eqN_trans q1 (eqN_symm q2)

/-- `PiConvInj` on the `RedOnly` fragment (00 §19.2 row `PiConvInj`,
minus `RedOnly`). The codomain conversion is moved to
`assumption A :: Γ` on the REDUCTION side (`parRedStar_replace_assump`,
`lookupValue`-only) before converting, so no `HasTy` transport across
an assumption-type change is needed. -/
noncomputable def piConvInj_redOnly {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} (_hΓ : CtxWf E n Γ) {A B A' B' : Expr Nat}
    (c : Conv E n Γ (.pi A B) (.pi A' B')) (hr : RedOnly c) :
    Conv E n Γ A A' ×'
      Conv E n (LocalDecl.assumption A :: Γ) B B' :=
  let ⟨_d, h1, h2⟩ := convRedOnly_join hE c hr
  let ⟨_A1, _B1, e1, hA1, hB1⟩ := parRedStar_pi h1 rfl
  let ⟨_A2, _B2, e2, hA2, hB2⟩ := parRedStar_pi h2 rfl
  by
    have hpi : (Expr.pi _A1 _B1 : Expr Nat) = .pi _A2 _B2 := e1.symm.trans e2
    injection hpi with hA hB
    subst hA
    subst hB
    exact ⟨.trans _ _ _ _ (parRedStar_to_conv hE hA1)
        (.symm _ _ _ (parRedStar_to_conv hE hA2)),
      .trans _ _ _ _ (parRedStar_to_conv hE hB1)
        (.symm _ _ _ (parRedStar_to_conv hE
          (parRedStar_replace_assump hB2)))⟩

/-- `FamAppConvInj` on the `RedOnly` fragment (00 §19.2 row
`FamAppConvInj`, minus `RedOnly`). -/
noncomputable def famAppConvInj_redOnly {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} (_hΓ : CtxWf E n Γ)
    {r : Nat} {m : CheckedMember} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM)
    (c : Conv E n Γ (foldApps (.const r ls) xs)
      (foldApps (.const r ls') xs'))
    (hr : RedOnly c) :
    eqNList ls ls' ×' ConvArgs E n Γ xs xs' :=
  let ⟨_d, h1, h2⟩ := convRedOnly_join hE c hr
  let ⟨_ls1, _xs1, e1, q1, ha1⟩ :=
    parRedStar_foldApps_inductive hres hK h1 xs rfl
  let ⟨_ls2, _xs2, e2, q2, ha2⟩ :=
    parRedStar_foldApps_inductive hres hK h2 xs' rfl
  by
    have hfa : foldApps (.const r _ls1) _xs1 = foldApps (.const r _ls2) _xs2 :=
      e1.symm.trans e2
    have hinj := foldApps_const_inj hfa
    have hxs := hinj.2
    injection hinj.1 with _hrr hls
    subst hls
    subst hxs
    exact ⟨eqNList_trans q1 (eqNList_symm q2),
      convArgs_of_parRedStarArgs hE ha1 ha2⟩

/-! ### B-b / R-Norm — `eqExprN`, `Normalizing`, three `_of_normalizing`

00 §19.3 RULING R-Norm (cc, 2026-09-06; #3856). STOP (i) discharged.
Site: this file (clause (3)); NOT `RcicInvertFamily` (S-3 second
disjunct). No O-2 sweep of the 46 `RcicDTMeta` consumers (clause (3)
LIMIT: this site is unreachable from them). Annex 21 §21.4 (e) is
NOT met (clause (4)): `RM014_whnf_typed` / `RM017_join_typed` stay
LANDED AND OPEN under a substituted premise. `closure_claim` stays 0.
S-8: the `irr` arm is not closed; no §19.2 STATUS word of
SortConvChar / PiConvInj / FamAppConvInj moves.

`eqExprN` is B-b's first Lean line. `Normalizing` is R-Norm's SECOND
printed `def` (the `eqExprN` conjunct), not B-b.2's drafted `N' = N`.
-/

/-- Expr equality up to `=ₙ` on the level arguments of `.sort` and
`.const`. 00 §19.3 R-Norm: the drafted normality conjunct `N' = N`
is syntactic and refutable against `ParRed.sortEq` / `ParRed.consts`. -/
inductive eqExprN : Expr Nat → Expr Nat → Prop
  | bvar {i : Nat} : eqExprN (.bvar i) (.bvar i)
  | sort {l₁ l₂ : Level} (h : eqN l₁ l₂) : eqExprN (.sort l₁) (.sort l₂)
  | const {r : Nat} {ls ls' : List Level} (h : eqNList ls ls') :
      eqExprN (.const r ls) (.const r ls')
  | app {f f' a a' : Expr Nat} (hf : eqExprN f f') (ha : eqExprN a a') :
      eqExprN (.app f a) (.app f' a')
  | lam {A A' b b' : Expr Nat} (hA : eqExprN A A') (hb : eqExprN b b') :
      eqExprN (.lam A b) (.lam A' b')
  | pi {A A' B B' : Expr Nat} (hA : eqExprN A A') (hB : eqExprN B B') :
      eqExprN (.pi A B) (.pi A' B')
  | letE {A A' v v' b b' : Expr Nat}
      (hA : eqExprN A A') (hv : eqExprN v v') (hb : eqExprN b b') :
      eqExprN (.letE A v b) (.letE A' v' b')
  | lit {t : Nat} : eqExprN (.lit t) (.lit t)

theorem eqExprN_refl : (e : Expr Nat) → eqExprN e e
  | .bvar _i => .bvar
  | .sort l => .sort (eqN_refl l)
  | .const _r ls => .const (eqNList_refl ls)
  | .app f a => .app (eqExprN_refl f) (eqExprN_refl a)
  | .lam A b => .lam (eqExprN_refl A) (eqExprN_refl b)
  | .pi A B => .pi (eqExprN_refl A) (eqExprN_refl B)
  | .letE A v b => .letE (eqExprN_refl A) (eqExprN_refl v) (eqExprN_refl b)
  | .lit _t => .lit

/-- 00 §19.3 R-Norm, THE ROW'S STATEMENT (second printed `def`).
Owner 02 §14 DT-025. Open; discharged by Annex 22 unit B-a (clause (2)). -/
def Normalizing (E : ResolvedEnv) (n : Nat) : Type :=
  EnvWf E n → ∀ (Γ : LCtx) (e T : Expr Nat),
    CtxWf E n Γ → HasTy E n Γ e T →
    Σ' (N : Expr Nat), ParRedStar E n Γ e N ×'
      (∀ N', ParRed E n Γ N N' → eqExprN N' N)

/-
B-b.5 walls (not landed; no sorry). Attempts against the R-Norm
`eqExprN` `Normalizing` live on `wip/rcic-bb-of-normalizing`
(`6d7db4a0001ecd3a7a58da040ccaac0bc2e48c24`). Unit run 6/6 (two
attempts × three names). `lake env lean lean/rcic/RcicConvChar.lean`
on that SHA: **58 errors / 44 positions**, split 5/5/4/4/20/20.
Binders print `(_hnorm : Normalizing E n)` at all six attempts;
every irr-shaped goal has `_hnorm` in scope and unused. STOP (iii)
not tripped. Categories and last errors on that SHA:

  sortConvChar_of_normalizing attempt 1 — 5 errors (1 type mismatch,
    3 unsolved, 1 missing cases)
    `RcicConvChar.lean:741:33` trans: ⊢ b✝ = Expr.sort v (untyped middle)
    `RcicConvChar.lean:741:71` trans: ⊢ b✝ = Expr.sort u
    `RcicConvChar.lean:741:59` type mismatch: trans fed `u v` to both
      recursive calls
    `RcicConvChar.lean:743:34` missing cases on Step
    `RcicConvChar.lean:752:42` irr: ⊢ eqN u v
      (HasTy Γ (.sort u) P, HasTy Γ (.sort v) P, P : sort 0; _hnorm unused)
  sortConvChar_of_normalizing attempt 2 (irr first) — 5 errors, same
    classes. irr `RcicConvChar.lean:762:42` ⊢ eqN u v (same; _hnorm unused)

  piConvInj_of_normalizing attempt 1 — 4 errors (unknown id, unsolved,
    missing cases, type mismatch)
    `RcicConvChar.lean:793:25` unknown identifier `convConvAssump`
      (tree name is `convConvAssumpAt`)
    `RcicConvChar.lean:795:44` trans: ⊢ b✝ = A'.pi B'
    `RcicConvChar.lean:798:34` missing cases on Step
    `RcicConvChar.lean:812:15` irr after hasTyPiInv: Conv.refl Γ A
      : Conv Γ A A, expected Conv Γ A A' (_hnorm unused)
  piConvInj_of_normalizing attempt 2 (irr first) — 4 errors
    (2 type mismatch, 1 unsolved, 1 missing cases)
    `RcicConvChar.lean:826:15` / `:831:25` irr: Conv.refl Γ A vs
      Conv Γ A A'; symm body context A' vs A (_hnorm unused)

  famAppConvInj_of_normalizing attempt 1 — 20 errors / 13 positions
    (1 unknown id `convArgs_symm` (no such name on the tree),
    6 missing cases, 9 dependent-elim, 2 subst, 1 unsolved, 1
    termination). DID NOT ELABORATE: `.go` structural recursion
    failed `RcicConvChar.lean:854:2`. `foldApps` is not a constructor,
    so subst/cases/nomatch fail on `foldApps (.const r ls) xs = …`.
    The irr goal `RcicConvChar.lean:883:73`
    ⊢ eqNList ls ls' ×' ConvArgs Γ xs xs' is ONE of the 20; it is
    not a well-formed attempt that reached the irr arm.
  famAppConvInj_of_normalizing attempt 2 — 20 errors / 13 positions,
    same classes. Termination `RcicConvChar.lean:892:2`. irr
    `RcicConvChar.lean:899:73` again one of 20, not a well-formed
    irr-arm wall. `convArgs_symm` unknown.

Disposition (R-Norm clause (2), recorded at landing into §19.7):
sort and pi walls STAND, handed to B-a-6. famApp's two attempts are
SPENT but do NOT constitute an irr-arm wall — "没有一次形式良好的
尝试到达其 irr goal" — handed to B-a-6 as that fact. Three STATUS
words unmoved. FALLBACK NONE. S-8: irr arm not closed.
-/

/-! ### M-005 — closed instantiations of the three corollaries

The sort and Π witnesses are closed at `emptyEnv` (`EnvWf.empty`,
`CtxWf.nil`). The family witness leaves the ENVIRONMENT abstract — a
concrete inductive member needs an `EnvWf.indMember` fixture, which is
the §20.5 carrier-pin lane's object — but its DERIVATION is concrete,
which is what M-005 asks of it. -/

theorem m005_sortConvChar_refl (u : Level) : eqN u u :=
  sortConvChar_redOnly (E := emptyEnv) (n := 0) (.empty 0) .nil
    (.refl [] (.sort u)) True.intro

/-- The `Conv.step (.beta …)` witness: the join is taken across an
UNTYPED middle (`Step.beta` carries no typing premises), which is
exactly the configuration a typing invariant cannot survive — and
which this characterization handles because it carries none. -/
theorem m005_sortConvChar_beta (u : Level) (A arg : Expr Nat) : eqN u u :=
  sortConvChar_redOnly (E := emptyEnv) (n := 0) (.empty 0) .nil
    (.trans [] (.sort u) (.app (.lam A (.sort u)) arg) (.sort u)
      (.symm [] (.app (.lam A (.sort u)) arg) (.sort u)
        (.step [] _ _ (.beta [] A (.sort u) arg)))
      (.step [] _ _ (.beta [] A (.sort u) arg)))
    ⟨True.intro, True.intro⟩

noncomputable def m005_piConvInj_refl :
    Conv emptyEnv 0 [] (.sort .zero) (.sort .zero) ×'
      Conv emptyEnv 0 [LocalDecl.assumption (.sort .zero)]
        (.sort (.succ .zero)) (.sort (.succ .zero)) :=
  piConvInj_redOnly (E := emptyEnv) (n := 0) (.empty 0) .nil
    (.refl [] (.pi (.sort .zero) (.sort (.succ .zero)))) True.intro

noncomputable def m005_famAppConvInj_refl {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) {r : Nat} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) :
    eqNList ls ls ×' ConvArgs E n Γ xs xs :=
  famAppConvInj_redOnly hE hΓ hres hK
    (.refl Γ (foldApps (.const r ls) xs)) True.intro

-- DELETED (00 §20.6 DISCHARGE, W7): `ParRedLevelCoherent`, the
-- `iotaSpine` sibling of `StepLevelCoherent`. It existed to carry
-- `LevelCoherent w2` out of a parallel iota step and into `parRedSR`,
-- for the reason its docstring gave: "`HasTy.const` is level-inert
-- while `instantiateLevels` is deferred, so typing does not force the
-- major's constructor universes". That premise of the reason is false
-- as of 00 §20.6 — `HasTy.const` concludes at `instantiateLevels ls
-- m.mtype` — and the fact is now the theorem
-- `iotaLhs_ctorParams_levels_conv` (`RcicDTMeta`), so there is nothing
-- left to carry. `StepLevelCoherent` / `StepsLevelCoherent` and
-- `IotaPreserve`'s `hlc` slot were deleted with it (W6); the §19.4
-- edge `02 universes ──→ F-05b` is deleted in the same patch.
--
-- AND NEITHER IS THE INDEX SIBLING, for the same reason one segment
-- later. 00 §19.2 erratum 6 deleted `StepIndexCoherent` too: the
-- syntactic index equation was strictly stronger than any typing
-- delivers, it is restated at the conversion layer
-- (`IndexCoherentConv`, `RcicInvertFamily`) and DISCHARGED
-- (`iotaLhs_ctorIdx_conv`, `RcicDTMeta`), so `iotaPreserve` carries no
-- per-redex premise and `parRedSR`'s `iotaSpine` arm has none to
-- supply. `ParRedIndexCoherent` was therefore never written — which is
-- the point: writing a predicate whose only consumer does not exist is
-- how the level one came to outlive its reason, and both siblings were
-- discharged before that consumer (`parRedSR`, `RcicParRedSR`) landed.

/-! ### C3 — the assumption-type conversion morphism

`ParRedStar` transports across a change of assumption TYPE for free
(`parRedStar_replace_assump` reads `lookupValue` only). `HasTy` does
NOT: `HasTy.bvar` reads `lookupType`. This is the morphism the
congruence arms of `parRedSR` need, and it is generic infrastructure —
independent of the wall, and reusable by F-03 — so it is built here
regardless of that outcome. Template: `RcicWeaken.lean`
(`stepWeaken` / `convWeaken` / `hasTyWeaken`), with the prefix `Δ`
explicit so the binder arms recurse under one more declaration; the
only non-trivial arm is `HasTy.bvar` at the replaced index, repaired
with `.conv` and the weakened `hc`. `RcicCtxMorph.lean` has the
`insertAt` lookup laws but no DECL-REPLACEMENT law: the three below
are that gap. -/

theorem get?_replace_head_ne :
    (Δ : LCtx) → (d d' : LocalDecl) → (Γ : LCtx) → (i : Nat) →
    i ≠ Δ.length → (Δ ++ d :: Γ).get? i = (Δ ++ d' :: Γ).get? i
  | [], _, _, _, 0, h => absurd rfl h
  | [], _, _, _, _ + 1, _ => rfl
  | _ :: _, _, _, _, 0, _ => rfl
  | _ :: Δ, d, d', Γ, i + 1, h =>
      get?_replace_head_ne Δ d d' Γ i (fun he => h (congrArg (· + 1) he))

theorem get?_replace_head_at :
    (Δ : LCtx) → (d : LocalDecl) → (Γ : LCtx) →
    (Δ ++ d :: Γ).get? Δ.length = some d
  | [], _, _ => rfl
  | _ :: Δ, d, Γ => get?_replace_head_at Δ d Γ

/-- The decl-replacement law `RcicCtxMorph` lacks: at the replaced
index the looked-up TYPE is the replaced annotation, lifted. -/
theorem lookupType_replace_assump_zero (Δ : LCtx) (A : Expr Nat) (Γ : LCtx) :
    lookupType (Δ ++ LocalDecl.assumption A :: Γ) Δ.length =
      some (lift 0 (Δ.length + 1) A) := by
  simp only [lookupType, get?_replace_head_at]

theorem lookupType_replace_assump_ne (Δ : LCtx) (A A' : Expr Nat) (Γ : LCtx)
    (i : Nat) (h : i ≠ Δ.length) :
    lookupType (Δ ++ LocalDecl.assumption A :: Γ) i =
      lookupType (Δ ++ LocalDecl.assumption A' :: Γ) i := by
  simp only [lookupType,
    get?_replace_head_ne Δ (LocalDecl.assumption A)
      (LocalDecl.assumption A') Γ i h]

/-- An assumption carries no value, so `lookupValue` is INSENSITIVE to
the replacement at every index — which is why `Step` transports with
no conversion at all. -/
theorem lookupValue_replace_assump (Δ : LCtx) (A A' : Expr Nat) (Γ : LCtx)
    (i : Nat) :
    lookupValue (Δ ++ LocalDecl.assumption A :: Γ) i =
      lookupValue (Δ ++ LocalDecl.assumption A' :: Γ) i := by
  by_cases h : i = Δ.length
  · subst h
    have e1 := get?_replace_head_at Δ (LocalDecl.assumption A) Γ
    have e2 := get?_replace_head_at Δ (LocalDecl.assumption A') Γ
    simp only [lookupValue, e1, e2]
  · simp only [lookupValue,
      get?_replace_head_ne Δ (LocalDecl.assumption A)
        (LocalDecl.assumption A') Γ i h]

/-- `get?` at a `some` index bounds the index. Written out rather than
taken from `List` lemmas so the `LCtx` uses below do not depend on
which spelling of the accessor is current. -/
theorem get?_lt_length {α : Type} :
    (l : List α) → {i : Nat} → {a : α} → l.get? i = some a → i < l.length
  | [], i, _, h => by cases i <;> exact Option.noConfusion h
  | _ :: t, 0, _, _ => by simp only [List.length_cons]; omega
  | _ :: t, i + 1, a, h => by
      simp only [List.get?_cons_succ] at h
      have := get?_lt_length t (i := i) (a := a) h
      simp only [List.length_cons]
      omega

/-- `lookupType` at a `letBinding` entry, in `Γ.get?` spelling (the one
`ParRed.bvarZeta` and `ctxWfLookupValueAt` use). -/
theorem lookupType_getQ_letBinding {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v)) :
    lookupType Γ i = some (lift 0 (i + 1) A) := by
  simp only [lookupType, h]

theorem lookupType_replace_let_zero (Δ : LCtx) (A v : Expr Nat) (Γ : LCtx) :
    lookupType (Δ ++ LocalDecl.letBinding A v :: Γ) Δ.length =
      some (lift 0 (Δ.length + 1) A) := by
  simp only [lookupType, get?_replace_head_at]

theorem lookupType_replace_let_ne (Δ : LCtx) (A v A' v' : Expr Nat) (Γ : LCtx)
    (i : Nat) (h : i ≠ Δ.length) :
    lookupType (Δ ++ LocalDecl.letBinding A v :: Γ) i =
      lookupType (Δ ++ LocalDecl.letBinding A' v' :: Γ) i := by
  simp only [lookupType,
    get?_replace_head_ne Δ (LocalDecl.letBinding A v)
      (LocalDecl.letBinding A' v') Γ i h]

/-- The law with no assumption-case analogue: at the replaced index the
looked-up VALUE is the replaced value, lifted. This is why the `Step`
half of the letBinding morphism cannot stay a `Step`. -/
theorem lookupValue_replace_let_zero (Δ : LCtx) (A v : Expr Nat) (Γ : LCtx) :
    lookupValue (Δ ++ LocalDecl.letBinding A v :: Γ) Δ.length =
      some (lift 0 (Δ.length + 1) v) := by
  simp only [lookupValue, get?_replace_head_at]

theorem lookupValue_replace_let_ne (Δ : LCtx) (A v A' v' : Expr Nat) (Γ : LCtx)
    (i : Nat) (h : i ≠ Δ.length) :
    lookupValue (Δ ++ LocalDecl.letBinding A v :: Γ) i =
      lookupValue (Δ ++ LocalDecl.letBinding A' v' :: Γ) i := by
  simp only [lookupValue,
    get?_replace_head_ne Δ (LocalDecl.letBinding A v)
      (LocalDecl.letBinding A' v') Γ i h]

/-- `Conv` weakened by a whole prefix ending in one declaration. -/
def convLift_prefix_decl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} (hE : EnvWf E n) (Δ : LCtx) (d : LocalDecl)
    (h : Conv E n Γ a b) :
    Conv E n (Δ ++ d :: Γ)
      (lift 0 (Δ.length + 1) a) (lift 0 (Δ.length + 1) b) := by
  have hw := convWeaken_lctx hE (Δ ++ [d]) h
  have hlen : (Δ ++ [d]).length = Δ.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hctx : (Δ ++ [d]) ++ Γ = Δ ++ d :: Γ := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hlen, hctx] at hw
  exact hw

/-- `Step` under a replaced assumption type: no conversion needed. -/
def stepConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} :
    (Δ : LCtx) → {a b : Expr Nat} →
    Step E n (Δ ++ LocalDecl.assumption A :: Γ) a b →
    Step E n (Δ ++ LocalDecl.assumption A' :: Γ) a b
  | _, _, _, .beta _ A0 body arg => .beta _ A0 body arg
  | _, _, _, .zeta _ A0 value body => .zeta _ A0 value body
  | Δ, _, _, .zetaLocal _ i v hv =>
      .zetaLocal _ i v
        ((lookupValue_replace_assump Δ A A' Γ i).symm.trans hv)
  | _, _, _, .delta _ r ls m b hres hbody htr =>
      .delta _ r ls m b hres hbody htr
  | _, _, _, .iota _ lhs rhs h => .iota _ lhs rhs h
  | _, _, _, .lit _ t exp h => .lit _ t exp h

mutual

def convConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} (hE : EnvWf E n) (hc : Conv E n Γ A' A) :
    (Δ : LCtx) → {a b : Expr Nat} →
    Conv E n (Δ ++ LocalDecl.assumption A :: Γ) a b →
    Conv E n (Δ ++ LocalDecl.assumption A' :: Γ) a b
  | _, _, _, .refl _ a => .refl _ a
  | Δ, _, _, .symm _ _ _ h => .symm _ _ _ (convConvAssumpAt hE hc Δ h)
  | Δ, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (convConvAssumpAt hE hc Δ h1)
        (convConvAssumpAt hE hc Δ h2)
  | Δ, _, _, .step _ _ _ hs => .step _ _ _ (stepConvAssumpAt Δ hs)
  | Δ, _, _, .app _ _ _ _ _ h1 h2 =>
      .app _ _ _ _ _ (convConvAssumpAt hE hc Δ h1)
        (convConvAssumpAt hE hc Δ h2)
  | Δ, _, _, .lam _ A0 _ _ _ hA hb =>
      .lam _ _ _ _ _ (convConvAssumpAt hE hc Δ hA)
        (convConvAssumpAt hE hc (LocalDecl.assumption A0 :: Δ) hb)
  | Δ, _, _, .pi _ A0 _ _ _ hA hb =>
      .pi _ _ _ _ _ (convConvAssumpAt hE hc Δ hA)
        (convConvAssumpAt hE hc (LocalDecl.assumption A0 :: Δ) hb)
  | Δ, _, _, .letE _ A0 _ v0 _ _ _ hA hv hb =>
      .letE _ _ _ _ _ _ _ (convConvAssumpAt hE hc Δ hA)
        (convConvAssumpAt hE hc Δ hv)
        (convConvAssumpAt hE hc (LocalDecl.letBinding A0 v0 :: Δ) hb)
  | _, _, _, .sorts _ l1 l2 h => .sorts _ l1 l2 h
  | _, _, _, .consts _ r ls ls' h => .consts _ r ls ls' h
  | Δ, _, _, .eta _ f A0 B0 hh =>
      .eta _ f A0 B0 (hasTyConvAssumpAt hE hc Δ hh)
  | Δ, _, _, .irr _ P p q hP hp hq =>
      .irr _ P p q (hasTyConvAssumpAt hE hc Δ hP)
        (hasTyConvAssumpAt hE hc Δ hp) (hasTyConvAssumpAt hE hc Δ hq)

def hasTyConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} (hE : EnvWf E n) (hc : Conv E n Γ A' A) :
    (Δ : LCtx) → {e T : Expr Nat} →
    HasTy E n (Δ ++ LocalDecl.assumption A :: Γ) e T →
    HasTy E n (Δ ++ LocalDecl.assumption A' :: Γ) e T
  | _, _, _, .sort _ l => .sort _ l
  | Δ, _, _, .bvar _ i T h => by
      by_cases hi : i = Δ.length
      · subst hi
        have heq : some T = some (lift 0 (Δ.length + 1) A) :=
          h.symm.trans (lookupType_replace_assump_zero Δ A Γ)
        injection heq with hTeq
        subst hTeq
        exact .conv _ _ _ _
          (.bvar _ Δ.length _ (lookupType_replace_assump_zero Δ A' Γ))
          (convLift_prefix_decl hE Δ (LocalDecl.assumption A') hc)
      · exact .bvar _ i T
          ((lookupType_replace_assump_ne Δ A A' Γ i hi).symm.trans h)
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m hres hlen hwf
  | Δ, _, _, .pi _ A0 u B0 v hA hB =>
      .pi _ _ u _ v (hasTyConvAssumpAt hE hc Δ hA)
        (hasTyConvAssumpAt hE hc (LocalDecl.assumption A0 :: Δ) hB)
  | Δ, _, _, .lam _ A0 u body B0 hA hbody =>
      .lam _ _ u _ _ (hasTyConvAssumpAt hE hc Δ hA)
        (hasTyConvAssumpAt hE hc (LocalDecl.assumption A0 :: Δ) hbody)
  | Δ, _, _, .app _ f a A0 B0 hf ha =>
      .app _ _ _ _ _ (hasTyConvAssumpAt hE hc Δ hf)
        (hasTyConvAssumpAt hE hc Δ ha)
  | Δ, _, _, .letE _ A0 u value B0 hA hv hb =>
      .letE _ _ u _ _ (hasTyConvAssumpAt hE hc Δ hA)
        (hasTyConvAssumpAt hE hc Δ hv)
        (hasTyConvAssumpAt hE hc (LocalDecl.letBinding A0 value :: Δ) hb)
  | Δ, _, _, .conv _ e T1 T2 h hcv =>
      .conv _ _ _ _ (hasTyConvAssumpAt hE hc Δ h)
        (convConvAssumpAt hE hc Δ hcv)
  | Δ, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyConvAssumpAt hE hc Δ hexp)

end

/-- The `Δ = []` reading — the statement the segment plan names. -/
def stepConvAssump {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    {a b : Expr Nat}
    (h : Step E n (LocalDecl.assumption A :: Γ) a b) :
    Step E n (LocalDecl.assumption A' :: Γ) a b :=
  stepConvAssumpAt (A := A) (A' := A') [] h

def convConvAssump {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    (hE : EnvWf E n) (hc : Conv E n Γ A' A) {a b : Expr Nat}
    (h : Conv E n (LocalDecl.assumption A :: Γ) a b) :
    Conv E n (LocalDecl.assumption A' :: Γ) a b :=
  convConvAssumpAt hE hc [] h

def hasTyConvAssump {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    (hE : EnvWf E n) (hc : Conv E n Γ A' A) {e T : Expr Nat}
    (h : HasTy E n (LocalDecl.assumption A :: Γ) e T) :
    HasTy E n (LocalDecl.assumption A' :: Γ) e T :=
  hasTyConvAssumpAt hE hc [] h

end Rcic.Declarative
