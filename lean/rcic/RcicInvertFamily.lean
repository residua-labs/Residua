/-
RCIC inversion family — the systematic layer the batch named after
template attempts (DT-021 x4, DT-023 x2, DT-012 x2): one fording
inversion per expression head, mirroring #3690's hasTyLamInv exactly.

AND the honest decomposition the attempts forced out: the six remaining
DT are NOT homogeneous "mechanical work". They split:

* MECHANICAL (this file settles): the six inversions below, plus the
  concrete untypability witness for DT-023 (`hasTyBvarEmptyFalse` — a
  bvar in the empty context has no typing; no deeper theory needed).
  DT-006 stays mechanical too: it is the letBinding-removal variant of
  RcicSubst's construction (same shape, hv := the let value's typing).

* CONFLUENCE-CLASS (named obligations, O-3 restated with EnvWf):
  unconditioned `Conv (pi) (pi) → …` is false (`piIrr_pi_pi`).
  Unconditioned `Conv (sort u) (sort v) → eqN u v` is not a second
  obligation; both rows are EnvWf-conditioned. Remaining hole is
  Conv→Join under wf (do not recurse on Conv). Four failed attempts
  at DT-021 were not missing technique — they were attempts to prove
  confluence's corollary without confluence.

Wrapper map for the batch:
  DT-023 = wrapper over `hasTyBvarEmptyFalse` (NO obligation needed);
  DT-021 = one-line wrapper over a `SortConvChar` premise;
  DT-012 = double inversion + conv accumulation + `SortConvChar`/
           `PiConvInj` premises as the statement's footprint (M-003:
           record the exact footprint, never hide it);
  DT-010/011 = Step cases via stepConstInv/these inversions +
           `PiConvInj` + hasTySubst; multi-step folds DT-010.

00 §20.6 (`instantiateLevels`) SEGMENT. Two sealed statements move in
this file; both are recorded in full, with old and new text and an
M-003 note, at their own declarations:

  * `hasTyConstInv` — conclusion `Conv Γ m.mtype T`
      becomes `Conv Γ (instantiateLevels ls m.mtype) T`.
  * `EnvBodyTyped` — gains a level list and the `hlen` premise 02 §8
      already carries; conclusion becomes
      `HasTy Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)`.

`FamAppConvInj`, `PiConvInj`, `SortConvChar`, `CtxWf`, `ConvArgs` and
the rest of the inversion family are UNCHANGED in shape (their `.const`
arms are arity-only `nomatch` patterns and no judgment constructor
gained a field). `FamAppConvInj` becomes strictly more load-bearing:
§20.6's discharge of `LevelCoherent` runs through its LEVEL half.

00 §20.6 DISCHARGE (O-2, complete). `LevelCoherent`,
`levelCoherentOf` and `StepLevelCoherent` are DELETED, and
`IotaPreserve` loses its `levelCoherentOf` premise: the fact is now
derived, downstream, by `iotaLhs_ctorParams_levels_conv`
(`RcicDTMeta`). W6 kept the `LevelCoherent` def alive one wave longer
because `RcicFixtures`' §20.5 carrier pin and `RcicConvChar`'s
`ParRedLevelCoherent` still named it; W7 removed all three in one
patch, so the name is gone from the tree and cannot be mistaken for a
live obligation.

00 §19.2 ERRATUM 6 (E-idxconv) SEGMENT, O-2 HALF. `IndexCoherent` —
the SYNTACTIC index equation erratum 5 introduced — is REPLACED by the
Γ-dependent, `Type`-valued `IndexCoherentConv` at the conversion
layer, and `indexCoherentOf` / `StepIndexCoherent` are DELETED
together with `IotaPreserve`'s index premise slot. The syntactic form
demanded EQUALITY of two index lists that the redex's typing relates
only up to `Conv`, so `IotaPreserve` / DT-010 / DT-011 were VACUOUS at
every redex whose major indices are convertible without being
syntactically equal.

The O-1 half — `iotaLhs_ctorIdx_conv`, which derives
`IndexCoherentConv` from `PiConvInj` + `FamAppConvInj` + `EnvWf` +
`CtxWf` + the redex's own typing — lands in `RcicDTMeta`, which is
this file's consumer and cannot be edited from here. Between the two
waves `RcicDTMeta` is red at exactly the sites that named the deleted
premise; that is the intended shape of an O-2 deletion whose O-1 lives
downstream, not a broken tree.
-/
import rcic.RcicDeclarative
import rcic.RcicInvert
import rcic.RcicIota
import rcic.RcicEnv

namespace Rcic.Declarative

/-! ### Context well-formedness (DT-003 carrier; 00 §19.2 erratum 2).

`CtxWf` used to live in `RcicDTMeta`. It is here because the
conversion-injectivity obligations below are CONDITIONED on it: the
`EnvWf`-only forms are refutable in a junk LOCAL context over a
well-formed environment (`Step.zetaLocal` relates `bvar i` to the
value of any `letBinding A v` with no relation between `A` and `v`,
and `HasTy.bvar` reads the annotation alone, so `x : Prop := Prop` in
Γ is `piIrrMember` relocated into the context and `Conv.irr` then
identifies any two Prop-typed Π's). The `letBinding` constructor
demands `hv : HasTy Γ v A`, which is exactly what excludes that junk.
Constructors are unchanged by the move. -/

inductive CtxWf (E : ResolvedEnv) (n : Nat) : LCtx → Type
  | nil : CtxWf E n []
  | assumption (Γ : LCtx) (A : Expr Nat) (u : Level)
      (hΓ : CtxWf E n Γ) (hA : HasTy E n Γ A (.sort u)) :
      CtxWf E n (LocalDecl.assumption A :: Γ)
  | letBinding (Γ : LCtx) (A : Expr Nat) (u : Level) (v : Expr Nat)
      (hΓ : CtxWf E n Γ) (hA : HasTy E n Γ A (.sort u)) (hv : HasTy E n Γ v A) :
      CtxWf E n (LocalDecl.letBinding A v :: Γ)

/-! ### Small infrastructure for the `ParRed` subject-reduction wave
(00 §19.4). None of these consumes an open row; each is a projection
of a landed judgment. -/

/-- Tails of a well-formed context are well-formed. Iterated
projection on the three constructors, in `parRedCtx_drop`'s shape
(`RcicParRedCore`). Consumer: `ParRed.bvarZeta`, whose value premise
lives in `Γ.drop (i + 1)`. -/
def ctxWf_drop {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → CtxWf E n Γ → (k : Nat) → CtxWf E n (Γ.drop k)
  | _, h, 0 => by simp only [List.drop]; exact h
  | _, .nil, _k + 1 => .nil
  | _, .assumption _ _ _ hΓ _, k + 1 => ctxWf_drop hΓ k
  | _, .letBinding _ _ _ _ hΓ _ _, k + 1 => ctxWf_drop hΓ k

/-- A stored let-value is typed at its stored type IN THE TAIL BELOW
ITS OWN BINDER — no lifting, no `EnvWf`.

This is deliberately NOT `ctxWfLookupValue` (`RcicDTMeta`), which is
the TRANSPORTED form: that one carries the value up into `Γ` through
`hasTyWeaken` at cutoff 0 and therefore concludes at `lift`ed type and
subject. A consumer whose other premise lives in `Γ.drop (i + 1)` —
`ParRed.bvarZeta`'s value reduction is exactly that — cannot use the
transported form, because the weakening has already been applied and
there is no inverse. The two coexist: this one is the pre-transport
derivation, `ctxWfLookupValue` is `hasTyWeaken` applied to it plus the
`lookupValue`/`lookupType` bookkeeping. -/
def ctxWfLookupValueAt {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {i : Nat} → {A v : Expr Nat} →
    CtxWf E n Γ → Γ.get? i = some (LocalDecl.letBinding A v) →
    HasTy E n (Γ.drop (i + 1)) v A
  | _, _, _, _, .nil, hlk => nomatch hlk
  | _, 0, _, _, .assumption _ _ _ _ _, hlk => nomatch hlk
  | _, i + 1, _, _, .assumption _ _ _ hΓ _, hlk => by
      simp only [List.get?_cons_succ] at hlk
      simp only [List.drop_succ_cons]
      exact ctxWfLookupValueAt (i := i) hΓ hlk
  | _, 0, A, v, .letBinding _ A0 _ v0 _ _ hv, hlk => by
      have hd : LocalDecl.letBinding A0 v0 = LocalDecl.letBinding A v :=
        Option.some.inj hlk
      injection hd with hA hveq
      subst hA
      subst hveq
      simp only [List.drop_succ_cons, List.drop_zero]
      exact hv
  | _, i + 1, _, _, .letBinding _ _ _ _ hΓ _ _, hlk => by
      simp only [List.get?_cons_succ] at hlk
      simp only [List.drop_succ_cons]
      exact ctxWfLookupValueAt (i := i) hΓ hlk

/-- `=ₙ` is a congruence for `succ`: `eval` maps `succ` to `(· + 1)`
pointwise, so the two evaluations agree wherever the arguments do.
Consumer: `ParRed.sortEq`. The `refl`/`symm`/`trans` siblings live
downstream in `RcicParRedCore`; this one is here because its consumer
is upstream of that file. -/
theorem eqN_succ_congr {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    eqN (.succ l₁) (.succ l₂) := fun ρ => by
  simp only [eval, h ρ]

/-! ### Named obligations (confluence-class; discharged by the 05 /
Church-Rosser arc, carried as premises until then). -/

/-- Pi-injectivity of conversion (named obligation, O-3 restated).
Unconditioned `Conv (pi A B) (pi A' B') → …` is false: `piIrr_pi_pi`
inhabits it at junk `T : Prop := Prop` via `Conv.irr`, and
`piConvInj_sortConvChar_false` is the compiled pair-refutation
(00 §19.2 erratum, commit 910087743). Conditioning on `EnvWf` is a
correction, not a weakening — the kernel runs only in wf
environments. Fragment `parRedStar_pi_inj` does not discharge this
row. `devel_pi_inj` is not merged (iota-in-devel).

00 §19.2 ERRATUM 2 (E-ctx): `EnvWf` alone is not enough — the same
junk is constructible in the LOCAL context over a well-formed
environment, so the row is conditioned on `CtxWf E n Γ` as well. The
kernel converts only in well-formed contexts; consumers
(DT-010/011/012, `oneStepSR`) already carry `hΓ : CtxWf`. Correction,
not weakening. -/
def PiConvInj (E : ResolvedEnv) (n : Nat) : Type :=
  EnvWf E n →
  ∀ Γ A B A' B', CtxWf E n Γ → Conv E n Γ (.pi A B) (.pi A' B') →
    Conv E n Γ A A' ×' Conv E n (LocalDecl.assumption A :: Γ) B B'

/-- Sort-conversion characterization (obligation, O-3 restated).
Same kernel context as `PiConvInj`: conditioned on `EnvWf` and — by
00 §19.2 ERRATUM 2 (E-ctx) — on `CtxWf E n Γ`, because `Conv.irr`
over a junk `letBinding` identifies two sorts convertible to
`bvar 0`. The unconditioned form is not a second obligation; it is the
statement `piConvInj_sortConvChar_false` refutes in conjunction with
unconditioned pi-injectivity. DT-021 wraps this. -/
def SortConvChar (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWf E n →
  ∀ Γ u v, CtxWf E n Γ → Conv E n Γ (.sort u) (.sort v) → eqN u v

/-! ### Family-head conversion injectivity (00 §20.5; O-3 row added by
this segment, owner face 02 conv meta). -/

/-- Pointwise `Conv` on argument lists — the `ParRedArgs` sibling.
Type-valued so the `Σ'`/`×'` chain of 00 §18.3 rule 1 never has to
eliminate an `∃`. -/
inductive ConvArgs (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → Type
  | nil : ConvArgs E n Γ [] []
  | cons {x y : Expr Nat} {xs ys : List (Expr Nat)}
      (h : Conv E n Γ x y) (hs : ConvArgs E n Γ xs ys) :
      ConvArgs E n Γ (x :: xs) (y :: ys)

def convArgs_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) → ConvArgs E n Γ xs xs
  | [] => .nil
  | _x :: xs => .cons (.refl _ _) (convArgs_refl xs)

/-- Pointwise `Conv` lists concatenate. -/
def convArgs_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs xs' ys ys' : List (Expr Nat)} →
    ConvArgs E n Γ xs xs' → ConvArgs E n Γ ys ys' →
    ConvArgs E n Γ (xs ++ ys) (xs' ++ ys')
  | [], [], _, _, .nil, h2 => h2
  | _ :: _, _ :: _, _, _, .cons hx hs, h2 => .cons hx (convArgs_append hs h2)

/-- Injectivity of conversion at an INDUCTIVE-FAMILY application head
(00 §20.5; §19.2 row `FamAppConvInj`, owner face 02 conv meta, sibling
of `PiConvInj`). `IotaPreserve`'s n-ary body needs it to relate the
free `ctorParams` to the recursor-side copy `preMajor.take nparams`:
that relation is POINTWISE `Conv`, obtained from
`HasTy Γ (iotaLhsOf w) T` by inverting the major's application typing
— never a syntactic equation (refuted under every carrier: ∀-bundle,
witness field, `DerivedIota` side condition, and typing of the lhs at
a proof-valued family).

The three conditions and why each is there (00 §20.5):
* `EnvWf E n` — now includes family ARITY (§19.2 erratum 3), so a
  family application is a TYPE, never a proof, and the `irr` arm is
  cuttable;
* `CtxWf E n Γ` — excludes context junk (§19.2 erratum 2);
* `m.mclass = inductiveM` — rigidity: `EnvWf.indMember` gives
  `hnobody`, so no delta fires at the head, and the head is not a
  recursor, so no iota fires either.

Sealed type-④ evidence accompanies the unconditioned forms.
Discharge: NOT an untyped `Conv → Join` (its `irr` arm is refutable);
the open ring shared with `PiConvInj` / `SortConvChar` is a TYPED
conversion characterization under `EnvWf` + `CtxWf` whose `irr` arm is
cut by the subject's typing — joint discharge in one F-05b segment. -/
def FamAppConvInj (E : ResolvedEnv) (n : Nat) : Type :=
  EnvWf E n →
  ∀ (Γ : LCtx) (r : Nat) (m : CheckedMember) (ls ls' : List Level)
    (xs xs' : List (Expr Nat)),
    CtxWf E n Γ →
    E.members r = some m →
    m.mclass = MemberClass.inductiveM →
    Conv E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') →
    eqNList ls ls' ×' ConvArgs E n Γ xs xs'

-- ══ DELETED (00 §20.6 DISCHARGE, O-2, complete) ══
-- `LevelCoherent`, `levelCoherentOf` and `StepLevelCoherent` — the
-- proposition "the major's CONSTRUCTOR universes agree with the
-- recursor's" (`eqNList w.lsC (w.ls.take w.famMember.arity)`) and its
-- `DerivedIota` and per-step readings. `StepsLevelCoherent`
-- (`RcicDTMeta`) and `ParRedLevelCoherent` (`RcicConvChar`) went with
-- them, and so did `IotaPreserve`'s / `oneStepSR`'s / DT-010's /
-- DT-011's `hlc` premise slot and `conv_ctorMajorRec`'s.
--
-- The def existed for the reason its docstring gave: "NOT derivable
-- from typing in this tree: `HasTy.const` is level-inert
-- (`instantiateLevels` deferred, 02 DT blocker), so `.const c lsC` and
-- `.const c ls` have the same type for every `lsC`". 00 §20.6 landed
-- `instantiateLevels`, `HasTy.const` concludes at
-- `instantiateLevels ls m.mtype`, and that reason is false: typing sees
-- the level lists, and the proposition is the THEOREM
-- `iotaLhs_ctorParams_levels_conv` (`RcicDTMeta`) — recursor side
-- `hasTy_rec_mtype` + `applyTel_recPrefix_idx_last`, constructor side
-- `hasTy_const_of_ctorMajor` + `ctorSpine_famApp`, joined by
-- `uniqueTy_foldApps` and split by `FamAppConvInj`'s LEVEL half. It is
-- proved THERE and not here because every one of those names lives
-- downstream; this file cannot import its own consumer.
--
-- The erratum-4 truncation is not lost with the name: the theorem's
-- conclusion IS `eqNList w.lsC (w.ls.take w.famMember.arity)`, and
-- `RcicFixtures`' `pin_natU_levels_derived` pins that conclusion at the
-- large-eliminating carrier, where the untruncated form is
-- unsatisfiable (05 §3: the constructor's arity is the family's `nU`;
-- 05 §11: the recursor's is `nU` or `nU+1`; `eqNList` is `False` on
-- unequal lengths).
--
-- ══ DELETED (00 §19.2 ERRATUM 6, O-2) ══
-- `IndexCoherent` — the SYNTACTIC proposition `(applyTel w.fields
-- w.ctorAfterParams).map (familyIdx w.nparams) = some (w.preMajor.drop
-- (w.nparams + 1 + w.nMinors))` — together with `indexCoherentOf` and
-- `StepIndexCoherent`, and `IotaPreserve`'s premise slot for them.
-- `StepsIndexCoherent` (`RcicDTMeta`) goes with them.
--
-- WHY, in one line: a premise written at the wrong strength is a
-- theorem with no instances, not a stronger theorem. The equation is
-- strictly stronger than anything the redex's typing delivers. The
-- discharge route erratum 5 named — the second half of the `ConvArgs`
-- that `iotaLhs_ctorParams_conv` computes — yields POINTWISE `Conv`
-- and never equality, because the two index lists are related only
-- through `FamAppConvInj`, whose right half is `ConvArgs` BY
-- CONSTRUCTION (§20.5). So at every redex whose major indices are
-- convertible without being syntactically equal — the normal case for
-- any family whose indices contain a redex — `IndexCoherent` was
-- unsatisfiable, the premise could not be supplied, and
-- `IotaPreserve` / DT-010 / DT-011 were VACUOUS exactly there. Same
-- shape as erratum 4's defect, where `eqNList` being `False` on
-- unequal lengths made `LevelCoherent` unsatisfiable at every
-- large-eliminating redex.
--
-- The corrected statement is `IndexCoherentConv` below, and it is a
-- premise NOWHERE: its single occurrence is as the CONCLUSION of
-- `iotaLhs_ctorIdx_conv` (`RcicDTMeta`), which derives it from
-- `PiConvInj` + `FamAppConvInj` + `EnvWf` + `CtxWf` and the redex's
-- own typing — a STRICT SUBSET of what `iotaPreserve` already
-- carries, so no consumer gains a premise and no obligation is
-- introduced.

/-! ### Index coherence of an iota redex (00 §20.5; §19.2 erratum 5,
second half — the honest home of the deleted `IotaTyping.hminApply` —
as corrected by §19.2 erratum 6). -/

/-- The major's INDEX arguments are POINTWISE CONVERTIBLE to the
constructor's result indices at the actual fields (00 §19.2 erratum
6). Still 05 §14's `result_indices`, and still NOT a witness fact: no
`IotaWitness` field constrains `preMajor.drop (nparams + 1 + nMinors)`
— `hpre` fixes only length, `hminor` reads slot `nparams+1+ctorIdx`,
`hctorAfter` reads `take nparams` — so a witness may carry junk
indices and kernel iota still fires (it never inspects them). It is a
TYPING fact about the redex (00 §20.5 RULE
FREE-FIELDS-ENTER-THROUGH-TYPING), and now a DERIVED one.

TYPE-VALUED: `ConvArgs` is (00 §18.3 rule 1), and `oneStepSR` is
`Σ'`-valued, so a `Prop`-squashed form could not eliminate into it.

Γ-DEPENDENT, and necessarily so: `Conv` is indexed by a context, and
the only fact relating the two index lists is the typing of the redex,
which lives in a context. The syntactic predecessor demanded EQUALITY
of the two lists, which no typing delivers; see the DELETED block
above for why that made its consumers vacuous.

The telescope endpoint is quantified under `applyTel`'s own equation
rather than packaged as `Σ' U, (… = some U) ×' …`. `applyTel` is a
function, so the two forms are interderivable, and the ∀-form is the
one whose consumer may supply the `U` IT ALREADY HOLDS — the `U` that
`telArgs_fields_rec` produced — instead of receiving a second `U` that
then needs an equality bridge. Totality of `applyTel w.fields
w.ctorAfterParams` is a separate theorem from witness data
(`applyTel_isPiTel`), not part of this statement. -/
def IndexCoherentConv {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) : Type :=
  ∀ (U : Expr Nat),
    applyTel w.fields w.ctorAfterParams = some U →
    ConvArgs E n Γ (familyIdx w.nparams U)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors))

/-- Environment-body typing (04-owned). A stored singleton body
inhabits the stored type in an arbitrary context, at the environment's
admission universe arity n (02 §2 / 04 §6). Inhabited by
`envWf_bodyTyped`. Type-valued.

00 §20.6 SEALED-STATEMENT CHANGE.

    old:  ∀ Γ r m b, E.members r = some m → m.body = some b →
            HasTy E n Γ b m.mtype
    new:  ∀ Γ r m b ls, E.members r = some m → m.body = some b →
            ls.length = m.arity →
            HasTy E n Γ (instantiateLevels ls b)
                        (instantiateLevels ls m.mtype)

M-003 FOOTPRINT: no new named obligation. The added premise `ls.length
= m.arity` is `HasTy.const`'s own `hlen` (02 §8), which every consumer
already holds — `Step.delta` does not carry it, but the consumer types
the redex's lhs and `hasTyConstInv` hands it back. Nothing else is
added, and nothing is weakened: the old statement is the `ls = []`
instance of the new one under `instantiateLevels_nil`.

WHY RESTATED RATHER THAN LEFT ALONE — this is the measurement the wave
asked for, and the answer is "restate", with the reason. Both forms
serve the consumer. `Step.delta` now lands on `instantiateLevels ls b`
and `hasTyConstInv`'s conversion now starts at `instantiateLevels ls
m.mtype`, so `oneStepSR`'s delta arm has to type the instantiated body
against the instantiated stored type; but 02 §9's delta is MONOMORPHIC
under `EnvWf` (`envWf_body_arity_zero`: a member that has a body has
`arity = 0`), so `hlen` forces `ls = []` and either form closes the
arm. The old form is therefore neither false nor too weak — it is
DISPLACED: it makes every consumer of the obligation re-derive `ls =
[]` itself, and it states less than 02 §9 states.

The restated form says what 02 §9 says and confines the monomorphic
step to the single inhabitant `envWf_bodyTyped`, which is exactly
where 00 §20.6 wants the tripwire. The day a polymorphic-definition
constructor is admitted, `envWf_body_arity_zero` stops holding and
`envWf_bodyTyped` stops compiling — it will then demand the real
level-substitution metatheorem, loudly, at one site. Under the old
form that day is invisible at the obligation and shows up as a
scattering of broken consumers instead.

The discharge itself stays monomorphic and introduces NO
level-substitution metatheorem (00 §20.6 MONOMORPHIC DELTA):
`envWf_body_arity_zero` + `hlen` give `ls = []`,
`instantiateLevels_nil` collapses both sides, and the existing
`envWf_bodyTyped` proof applies verbatim underneath. -/
def EnvBodyTyped (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ (Γ : LCtx) (r : Nat) (m : CheckedMember) (b : Expr Nat)
    (ls : List Level),
    E.members r = some m → m.body = some b → ls.length = m.arity →
    HasTy E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)

/-- Iota preservation (05-owned; named obligation). Type-valued.
Premise is `DerivedIota + IotaTyping`: index-position / `mdom =
minorTel` facts are 05 admission, not redex identity.

M-003 (00 §20.6 DISCHARGE, O-2). Premise deleted:
    old:  … (h) → iotaTypingOf h → levelCoherentOf h →
          indexCoherentOf h → CtxWf E n Γ → …
    new:  … (h) → iotaTypingOf h → indexCoherentOf h → CtxWf E n Γ → …
The level premise carried the major's CONSTRUCTOR universes `lsC`
against the recursor's `ls`. With `HasTy.const` level-instantiated it
is forced by the redex's own typing and is proved downstream
(`iotaLhs_ctorParams_levels_conv`, `RcicDTMeta`). Strengthening: the
conclusion is unchanged and one hypothesis is gone.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Second premise deleted:
    old:  … (h) → iotaTypingOf h → indexCoherentOf h →
          CtxWf E n Γ → …
    new:  … (h) → iotaTypingOf h → CtxWf E n Γ → …
The index premise carried the major's INDEX arguments against the
constructor's result indices at the actual fields. It was stated as a
syntactic EQUATION, which is strictly stronger than the redex's typing
delivers and left this statement vacuous wherever the two lists are
convertible without being equal. Restated at the conversion layer
(`IndexCoherentConv`) it is DERIVED, downstream, by
`iotaLhs_ctorIdx_conv` (`RcicDTMeta`), off the same `FamAppConvInj`
application that supplies the parameter half. Strengthening: the
conclusion is unchanged and one hypothesis is gone.

`FamAppConvInj` is now TRIPLY load-bearing per redex — parameters
(`iotaLhs_ctorParams_conv`), levels (§20.6
`iotaLhs_ctorParams_levels_conv`), indices (erratum 6
`iotaLhs_ctorIdx_conv`) — all three reading one family-application
`Conv`. No new obligation; one row carries three chains, and if that
row is later found to need conditioning beyond `EnvWf` + `CtxWf`, all
three move at once.

What still enters at the redex (00 §20.5 O-3):
* `CtxWf E n Γ` — `PiConvInj` / `FamAppConvInj`, which the proof
  consumes, are `CtxWf`-conditioned (§19.2 erratum 2); every consumer
  (`oneStepSR`) already carries it. -/
def IotaPreserve (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ (Γ : LCtx) (lhs rhs T : Expr Nat)
    (h : DerivedIota E lhs rhs),
    iotaTypingOf h →
    CtxWf E n Γ →
    HasTy E n Γ lhs T → HasTy E n Γ rhs T

/-- Literal-expansion preservation (08-owned; named obligation). Type-valued. -/
def LitPreserve (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ (Γ : LCtx) (t : Nat) (exp T : Expr Nat),
    LiteralExpansion t exp →
    HasTy E n Γ (.lit t) T → HasTy E n Γ exp T

/-! ### The mechanical inversion family (fording; conv arm accumulates). -/

/-- Inversion at a sort subject. -/
def hasTySortInv {E : ResolvedEnv} {n : Nat} {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .sort l →
    Conv E n Γ (.sort (.succ l)) T
  | _, _, _, .sort Γ l', heq => by
      injection heq with h1; subst h1; exact .refl _ _
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      .trans _ _ _ _ (hasTySortInv h heq) hc
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Inversion at a bound-variable subject. -/
def hasTyBvarInv {E : ResolvedEnv} {n : Nat} {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .bvar i →
    Σ' (A : Expr Nat), (lookupType Γ i = some A) ×' Conv E n Γ A T
  | _, _, _, .bvar Γ i' A h, heq => by
      injection heq with h1; subst h1; exact ⟨A, h, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨A, hlk, hcv⟩ := hasTyBvarInv h heq
      ⟨A, hlk, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Inversion at a const subject.

00 §20.6 SEALED-STATEMENT CHANGE.

    old:  Conv E n Γ m.mtype T
    new:  Conv E n Γ (instantiateLevels ls m.mtype) T

M-003 FOOTPRINT: unchanged. No premise is added and no obligation is
named; the conclusion index simply follows `HasTy.const`'s, which 00
§20.6 moved to `instantiateLevels ls m.mtype`.

Nothing is weakened. After the rule change the old form was no longer
a statement about the subject's type at all: it asserted a conversion
out of the STORED polymorphic type, which the `.const` rule had
stopped producing, so the `.const` arm could not even hand it out
(`Conv.refl` has the wrong index — the observed failure). The new form
is what that arm produces verbatim, and the `.conv` arm's accumulation
through `Conv.trans` is untouched. At `ls = []` the old reading comes
back exactly, by `instantiateLevels_nil`.

The tuple SHAPE is unchanged — four components in the same order — so
the five call sites (all in `RcicDTMeta`) need no pattern edit; only
what they do with the fourth component may need
`instantiateLevels_nil` inserted, and only where `ls` is known
empty. -/
def hasTyConstInv {E : ResolvedEnv} {n : Nat} {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .const r ls →
    Σ' (m : CheckedMember),
      (E.members r = some m) ×' (ls.length = m.arity) ×'
      Conv E n Γ (instantiateLevels ls m.mtype) T
  | _, _, _, .const Γ r' ls' m hres hlen hwf, heq => by
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨m, hres, hlen, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨m, hres, hlen, hcv⟩ := hasTyConstInv h heq
      ⟨m, hres, hlen, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Inversion at a pi subject. -/
def hasTyPiInv {E : ResolvedEnv} {n : Nat} {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .pi A B →
    Σ' (u : Level) (v : Level),
      HasTy E n Γ A (.sort u) ×'
      HasTy E n (LocalDecl.assumption A :: Γ) B (.sort v) ×'
      Conv E n Γ (.sort (.imax u v)) T
  | _, _, _, .pi Γ A' u B' v hA hB, heq => by
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨u, v, hA, hB, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨u, v, hA, hB, hcv⟩ := hasTyPiInv h heq
      ⟨u, v, hA, hB, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Inversion at an application subject. -/
def hasTyAppInv {E : ResolvedEnv} {n : Nat} {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .app f a →
    Σ' (A : Expr Nat) (B : Expr Nat),
      HasTy E n Γ f (.pi A B) ×'
      HasTy E n Γ a A ×'
      Conv E n Γ (instantiate0 a B) T
  | _, _, _, .app Γ f' a' A B hf ha, heq => by
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨A, B, hf, ha, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨A, B, hf, ha, hcv⟩ := hasTyAppInv h heq
      ⟨A, B, hf, ha, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Typing of the head of a `foldApps` spine (F-05a attempt 3). -/
def hasTyFoldAppsInv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs : List (Expr Nat)} → {T : Expr Nat} →
    HasTy E n Γ (foldApps f xs) T →
    Σ' (Tf : Expr Nat), HasTy E n Γ f Tf
  | [], _, h => ⟨_, h⟩
  | x :: xs, T, h =>
      let ⟨_, hfapp⟩ :=
        hasTyFoldAppsInv (f := Expr.app f x) (xs := xs) (T := T) h
      let ⟨A, B, hf, _, _⟩ := hasTyAppInv hfapp rfl
      ⟨.pi A B, hf⟩

/-- Typing of the argument at index `i` in a `foldApps` spine. -/
def hasTyArgOfFold {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs : List (Expr Nat)} → {T : Expr Nat} →
    HasTy E n Γ (foldApps f xs) T →
    {i : Nat} → {x : Expr Nat} →
    xs[i]? = some x →
    Σ' (A : Expr Nat), HasTy E n Γ x A
  | [], _, _h, _i, _x, hx => by
      simp only [List.getElem?_nil] at hx
      exact Option.noConfusion hx
  | y :: ys, T, h, i, x, hx =>
      match i with
      | 0 => by
          have hyx : y = x := by
            simp only [List.getElem?_cons_zero] at hx
            injection hx
          subst hyx
          let ⟨_, hfapp⟩ :=
            hasTyFoldAppsInv (f := Expr.app f y) (xs := ys) (T := T) h
          let ⟨A, _, _, ha, _⟩ := hasTyAppInv hfapp rfl
          exact ⟨A, ha⟩
      | i' + 1 =>
          hasTyArgOfFold (f := Expr.app f y) (xs := ys) (T := T) h
            (i := i') (x := x) (by
              simp only [List.getElem?_cons_succ] at hx
              exact hx)

/-- Inversion of a `foldApps` typing into a spine of Π-applications. -/
inductive SpineInv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → List (Expr Nat) → Expr Nat → Type
  | nil {f T : Expr Nat} :
      HasTy E n Γ f T → SpineInv E n Γ f [] T
  | cons {f x : Expr Nat} {xs : List (Expr Nat)} {T A B : Expr Nat} :
      HasTy E n Γ f (.pi A B) →
      HasTy E n Γ x A →
      SpineInv E n Γ (.app f x) xs T →
      SpineInv E n Γ f (x :: xs) T

def invertSpine {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs : List (Expr Nat)} → {T : Expr Nat} →
    HasTy E n Γ (foldApps f xs) T → SpineInv E n Γ f xs T
  | [], T, h => .nil h
  | x :: xs, T, h =>
      let ⟨_, hfapp⟩ :=
        hasTyFoldAppsInv (f := Expr.app f x) (xs := xs) (T := T) h
      let ⟨A, B, hf, ha, _⟩ := hasTyAppInv hfapp rfl
      .cons hf ha (invertSpine (f := Expr.app f x) (xs := xs) (T := T) h)

/-- Function typing stored in a spine inversion. -/
def spineInv_fun_ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs : List (Expr Nat)} → {T : Expr Nat} →
    SpineInv E n Γ f xs T →
    Σ' (A : Expr Nat), HasTy E n Γ f A
  | _, _, .nil hf => ⟨_, hf⟩
  | _, _, .cons hf _ _ => ⟨_, hf⟩

/-- Split a spine at a prefix: `xs ++ ys`. -/
def spineInv_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs ys : List (Expr Nat)} → {T : Expr Nat} →
    SpineInv E n Γ f (xs ++ ys) T →
    Σ' (U : Expr Nat),
      SpineInv E n Γ f xs U ×' SpineInv E n Γ (foldApps f xs) ys T
  | [], ys, T, h =>
      let ⟨U, hf⟩ := spineInv_fun_ty h
      ⟨U, .nil hf, h⟩
  | x :: xs, ys, T, .cons hf ha s =>
      let ⟨U, sxs, sys⟩ :=
        spineInv_append (f := Expr.app f x) (xs := xs) (ys := ys) s
      ⟨U, .cons hf ha sxs, by
        simp only [foldApps]
        exact sys⟩

/-- Snoc a typed argument onto a Π-headed spine. -/
def spineInv_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat} :
    {xs : List (Expr Nat)} → {A B : Expr Nat} → {x : Expr Nat} →
    SpineInv E n Γ f xs (.pi A B) →
    HasTy E n Γ x A →
    SpineInv E n Γ f (xs ++ [x]) (instantiate0 x B)
  | [], A, B, x, .nil hf, hx =>
      .cons hf hx (.nil (.app _ _ _ _ _ hf hx))
  | _ :: _, A, B, x, .cons hf ha s, hx =>
      .cons hf ha (spineInv_snoc s hx)

/-- The selected minor of a well-formed iota witness is typed, if the
lhs recursor spine is. Index is inside `preMajor` by 05 §11/§12. -/
def hasTyIotaMinor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (h : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (Mty : Expr Nat), HasTy E n Γ w.minor Mty := by
  have hl : iotaLhsOf w =
      foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) := rfl
  rw [hl] at h
  have hlt : w.nparams + 1 + w.ctorIdx < w.preMajor.length := by
    have := w.hpre
    have := w.hidx
    omega
  have hx : (w.preMajor ++ [ctorMajor w])[w.nparams + 1 + w.ctorIdx]? =
      some w.minor := by
    have happ := List.getElem?_append_left (l₂ := [ctorMajor w]) hlt
    exact happ.trans w.hminor
  exact hasTyArgOfFold (f := .const w.recRef w.ls)
    (xs := w.preMajor ++ [ctorMajor w]) h hx

/-- Inversion at a let subject. -/
def hasTyLetInv {E : ResolvedEnv} {n : Nat} {A value bd : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .letE A value bd →
    Σ' (u : Level) (B : Expr Nat),
      HasTy E n Γ A (.sort u) ×'
      HasTy E n Γ value A ×'
      HasTy E n (LocalDecl.letBinding A value :: Γ) bd B ×'
      Conv E n Γ (instantiate0 value B) T
  | _, _, _, .letE Γ A' u value' B hA hv hb, heq => by
      injection heq with h1 h2 h3; subst h1; subst h2; subst h3
      exact ⟨u, B, hA, hv, hb, .refl _ _⟩
  | _, _, _, .conv Γ e A0 B0 h hc, heq =>
      let ⟨u, B, hA, hv, hb, hcv⟩ := hasTyLetInv h heq
      ⟨u, B, hA, hv, hb, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-! ### DT-023's concrete witness: no obligation needed. -/

/-- A bound variable in the empty context has no typing — the concrete
untypability witness DT-023 wraps (not everything is typable). -/
theorem hasTyBvarEmptyFalse {E : ResolvedEnv} {n : Nat} {T : Expr Nat}
    (h : HasTy E n [] (.bvar 0) T) : False := by
  have ⟨A, hlk, _⟩ := hasTyBvarInv h rfl
  simp [lookupType] at hlk

/-- Inversion at a literal subject — the ninth member of the
    family, `hasTyLetInv`'s shape (`:701-720`). Fording form; the
    `conv` arm peels, the rest are source-disjoint. -/
def hasTyLitInv {E : ResolvedEnv} {n : Nat} {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .lit t →
    Σ' (T' : Expr Nat),
      HasTy E n Γ (natExpand t) T' ×' Conv E n Γ T' T
  | _, _, _, .lit _Γ _t' Te hexp, heq => by
      injection heq with h1; subst h1
      exact ⟨Te, hexp, .refl _ _⟩
  | _, _, _, .conv _Γ _e _A0 _B0 h hc, heq =>
      let ⟨Te, hexp, hcv⟩ := hasTyLitInv h heq
      ⟨Te, hexp, .trans _ _ _ _ hcv hc⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq

/-- `LitPreserve E n` (00 §19.2, owner face "08 profile"),
    DISCHARGED FOR REAL — 00 §19.7 E-LitP's FIRST disjunct.
    `LiteralExpansion.of` pins `exp = natExpand t`; `hasTyLitInv`
    reads 02 §8's typing content off the derivation; `HasTy.conv`
    transports it. Consumes NO 00 §19.2 row, adds no obligation. -/
def litPreserve (E : ResolvedEnv) (n : Nat) : LitPreserve E n :=
  fun _Γ _t _exp _T hexp h =>
    match hexp with
    | .of _ =>
        let ⟨_Te, hty, hcv⟩ := hasTyLitInv h rfl
        .conv _ _ _ _ hty hcv

/-- Prefix of a spine at index `k` is typed at a Π (the next argument's
domain). -/
def spineFunTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {f : Expr Nat} → {xs : List (Expr Nat)} → {T : Expr Nat} →
    SpineInv E n Γ f xs T →
    (k : Nat) → k < xs.length →
    Σ' (A B : Expr Nat),
      HasTy E n Γ (foldApps f (xs.take k)) (.pi A B)
  | _, _, _, .nil hf, k, hk =>
      (Nat.not_lt_zero k hk).elim
  | _, _, _, .cons hf _ha s, 0, _hk =>
      ⟨_, _, by
        simp only [List.take_zero, foldApps]
        exact hf⟩
  | f, x :: xs, T, .cons hf ha s, k + 1, hk =>
      let ⟨A, B, h⟩ :=
        spineFunTy (f := Expr.app f x) (xs := xs) s k
          (Nat.lt_of_succ_lt_succ hk)
      ⟨A, B, by
        simp only [List.take_succ_cons, foldApps] at h ⊢
        exact h⟩

/-- Last application of a snoc spine: the prefix is a Π, the last
argument inhabits the domain, and the result converts from
`instantiate0 x B`. (F-05a attempt 8: inverted last-Π.) -/
def hasTyFoldAppsSnocInv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f : Expr Nat} {ys : List (Expr Nat)} {x T : Expr Nat}
    (h : HasTy E n Γ (foldApps f (ys ++ [x])) T) :
    Σ' (A B : Expr Nat),
      HasTy E n Γ (foldApps f ys) (.pi A B) ×'
      HasTy E n Γ x A ×'
      Conv E n Γ (instantiate0 x B) T := by
  have h' : HasTy E n Γ (.app (foldApps f ys) x) T := by
    rw [foldApps_snoc] at h
    exact h
  exact hasTyAppInv h' rfl

/-- 0-ary IotaPreserve given last-Π / minor-type η-alignment.
`F = foldApps motive indices` from `instTel_hrecBody`.
Equality form; Conv form is `iotaPreserve_nil` (DTMeta, PiConvInj). -/
def iotaPreserve_nil_of_eta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T A B Mty F : Expr Nat}
    (hf : w.fields = [])
    (_hT : HasTy E n Γ (iotaLhsOf w) T)
    (_hpre : HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor)
      (.pi A B))
    (_hctor : HasTy E n Γ (ctorMajor w) A)
    (hcv : Conv E n Γ (instantiate0 (ctorMajor w) B) T)
    (hminor : HasTy E n Γ w.minor Mty)
    (hM : Mty = .app F (ctorMajor w))
    (hB : B = .app (lift 0 1 F) (.bvar 0)) :
    HasTy E n Γ (iotaRhsOf w) T := by
  rw [iotaRhs_nil_fields w hf]
  exact .conv _ _ _ _ hminor
    (.trans _ _ _ _ (conv_of_eta_minor (w := w) hM hB) hcv)

/-- Conv form of the 0-ary η hole: `Mty ≃ F ctor` and last-Π body
`≃ η` compose to `Mty ≃ instantiate0 ctor B`. `convSubst` lives in
DTMeta; this packages the definitional instantiate0_eta step. -/
def conv_of_eta_minor_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {F Mty B : Expr Nat} {w : IotaWitness E}
    (hM : Conv E n Γ Mty (.app F (ctorMajor w)))
    (hinst : Conv E n Γ (instantiate0 (ctorMajor w) B)
      (.app F (ctorMajor w))) :
    Conv E n Γ Mty (instantiate0 (ctorMajor w) B) :=
  .trans _ _ _ _ hM (.symm _ _ _ hinst)

/-- Package: inverted last-Π `(A, B)`, selected-minor type `Mty`,
syntactic last-Π domain `A_syn`, and `F = foldApps motive indices`
with `instTel preMajor recBody = app (lift F) (bvar 0)`.
0-ary IotaPreserve is `iotaPreserve_nil_of_eta` once `B` equals that
η-body and `Mty = app F ctor`. -/
def iotaPreserve_nil_pack {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (A B Mty F A_syn : Expr Nat),
      HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor) (.pi A B) ×'
      HasTy E n Γ (ctorMajor w) A ×'
      Conv E n Γ (instantiate0 (ctorMajor w) B) T ×'
      HasTy E n Γ w.minor Mty ×'
      (applyTel w.preMajor (instantiateLevels w.ls w.recMember.mtype) =
        some (Expr.pi A_syn (instTel w.preMajor w.recBody))) ×'
      (instTel w.preMajor w.recBody =
        .app (lift 0 1 F) (.bvar 0)) := by
  have ⟨Mty, hminor⟩ := hasTyIotaMinor w hT
  have hl : iotaLhsOf w =
      foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) := rfl
  have hT' : HasTy E n Γ
      (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])) T := by
    rw [← hl]; exact hT
  have ⟨A, B, hpre, hctor, hcv⟩ :=
    hasTyFoldAppsSnocInv (f := .const w.recRef w.ls) (ys := w.preMajor)
      (x := ctorMajor w) hT'
  have ⟨A_syn, happ⟩ := recLastPi_inst w w.ls
  have hlen := w.hpre
  have hlt : w.nparams < w.preMajor.length := by omega
  have hmot : w.preMajor[w.nparams]? = some (w.preMajor[w.nparams]'hlt) :=
    List.getElem?_eq_getElem hlt
  have hη := instTel_hrecBody w hmot
  exact ⟨A, B, Mty,
    foldApps (w.preMajor[w.nparams]'hlt)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)),
    A_syn, hpre, hctor, hcv, hminor, happ, hη⟩

end Rcic.Declarative
