import rcic.RcicIota
import rcic.RcicPinEqIotaStarK
import rcic.RcicParRedTPins
import rcic.RcicFixtures

/-!
# `RcicHeadStepT` — the deterministic typed head step (F05b, #6293 item 3)

cc ruling on #6293 (02:25Z, amended 03:40Z), item 3: a
model-independent, deterministic typed head reduction `headStepT`,
needed by every logical relation — with a guarded ι★K arm, a
determinism theorem, and `ParRedT` soundness. MEASURED FIRST:

- `headStep?`/`whnfTy` (`RcicTypedConv.lean`): the machine's head step —
  `Option`-valued over `(hd, args)`, δ at a transparent const and β at a
  `lam`-headed spine, producing `ConvT` witnesses through `liftSpine`.
  Shape template. Its gaps for the LR layer: no ι (the checker never
  contracts recursors) and the `ConvT` target, where the diamond
  consumes `ParRedT`.
- `RcicTypedMachine`/`RcicTypedMachineAccept`: the acceptance layer —
  `typedStep`/`typedRun` wrap the certifiers; no head-reduction surface
  of its own.
- `ParRedT` (`RcicParRedT.lean`): the typed parallel step — `beta`,
  `delta`, `zeta`, `lit`, `iotaSpine`, `iotaStarK` are the soundness
  targets.
- `iotaWitness_deterministic` (`RcicIota.lean`), `appsSpine_recCall`,
  `iotaLhsOf_recCall_inj_full`, `iotaWitness_env_of_same_refs`
  (`RcicParRedIota.lean`): the injectivity surface determinism reuses.

`HeadStepT` is a root-contraction relation `HeadStepT E n Γ e e' T`:
six arms, each a `ParRedT` ctor at refl inner steps. No spine lift:
lifting a `ParRedT` through an argument spine needs a `TyConvT` at
every application node — the type-uniqueness debt the diamond
discharges — so the relation stays at the root; spine composition is
the consumers' side (the `X` debt, already recorded). η stays out: it
contracts a `lam` SHAPE, not a head redex, and it is not in `headStep?`'s
contraction set either.

- `beta`/`delta`/`zeta`/`lit` — the machine's δ/β plus ζ and literal
  expansion, `ParRedT`-premise verbatim.
- `iota` — `iotaLhsOf w ⇒ iotaRhsOf w`: the ctor-headed-major redex.
  The union landing is carried internally (`.ofU w`), so the reduct is
  the witness's OWN `iotaRhsOf` — canonical.
- `iotaStarK` — the guarded K step of the 03:40Z ruling:
  `recCall (const w.recRef w.ls) w.preMajor major ⇒ iotaRhsOf w`.
  The gate is CONVERSION-FORM, per the ruling, and HONEST per the
  05:15Z check-#10 ruling: `hcv` says the major's stored type `Tm`
  converts to the constructor's own index instance —
  `applyTel w.fields w.ctorAfterParams`, the family's ctor type
  instantiated at the recursor-side params (`hctorAfter` supplies
  `ctorAfterParams = applyTel (w.preMajor.take w.nparams)
    (instantiateLevels w.ls w.ctorMember.mtype)`), then at `w.fields`.
  For `Eq.refl` the instance is `Eq α a a`, not the major's `Eq α a b`
  — the vacuous free-`idx` guard it replaces let the caller supply
  `Tm`'s own indices and close by `refl`. `hmk` stays only because
  `ParRedT.iotaStarK`'s soundness leg needs it; it is not the gate.

  Determinism guards:
    * `hnmin1 : w.nMinors = 1` — the "singleton" of the ruling; with
      `hidx` it forces `ctorIdx = 0`, hence `ctorRef = familyRef + 1`:
      the synthesized constructor is member-determined.
    * `hfields0 : w.fields = []` — `rhsArgs` inserts every field into
      the reduct; a stuck major carries none, so the deterministic
      step fires only where the ctor contributes none — `Eq.refl`
      exactly. A field-ful singleton (`Acc.intro`) stays neutral.

- `iotaStarKField` — the CANONICAL-FIELDS K step for Loop-shaped
  singletons (the FIELDFUL_K measurement, #6605): `w.fields = [major]`
  — the one field is the stuck major itself, the canonical choice that
  re-embeds the source (Loop's `mk : Loop → Loop` reads its own
  argument back). The honest `hcv` is unchanged — for `mk`, `applyTel
  [major] (Π Loop Loop)` computes `Loop` — `Tm`'s conversion to the
  ctor's result, no free index.

  ORDER (per the ruling): ordinary ι is checked first — made a REAL
  negative premise here: `hnctor` says the stuck major is not headed
  by the witness's constructor, so where the source IS `iotaLhsOf`-shaped
  (`major = ctorMajor w'`) ι★K cannot fire and `.iota` owns the source.
  At a field-free singleton ctor major `.iota` and `.iotaStarK` both
  exist but JOIN at `iotaRhsOf w`; at a field-ful ctor major
  (`fields = [mk x]` there), `hnctor` fails, so only `.iota` fires —
  deterministic. ι★K's `hcv` is evaluated at the major's STORED `Tm` —
  the head step never reduces the major. The ι-vs-ι★K overlap proof
  reads `familyRef` off `hmajorTy`'s stored recursor view, transports
  `nMinors = 1` and field-freeness across, and lands on the shared
  minor.

  `.ofUS`-landed iotas (`IotaWitnessS`, the frec/W surface) stay out:
  the reduct is the legacy witness's `iotaRhsOf`, whose functionality
  `iotaWitness_deterministic` proves.

`headStepT_sound`: every head step is a `ParRedT` step — at ANY `PEq`
(HeadStepT never invokes proof-irrelevance). `headStepT_det`:
`HeadStepT` is a partial function — the source determines the reduct.
The `T` index is not claimed unique (type uniqueness is the diamond
debt).

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-- THE DETERMINISTIC TYPED HEAD STEP — a root contraction at a shared
    type. Each arm is a `ParRedT` constructor at reflexive inner
    steps; `iotaStarK` carries `ParRedT.iotaStarK`'s gate plus the
    conversion-form guard and the two determinism guards
    (`hnmin1`, `hfields0`). -/
inductive HeadStepT (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  /-- β at the root — `headStep?`'s `.lam` arm at parallel granularity:
      body and argument step by refl inside `ParRedT.beta`. -/
  | beta (Γ : LCtx) (A body arg B : Expr Nat) (u v w : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyT E n Γ (instantiate0 arg B) (.sort w))
      (hbody : HasTyT E n (.assumption A :: Γ) body B)
      (harg : HasTyT E n Γ arg A)
      (hred : HasTyT E n Γ (instantiate0 arg body)
        (instantiate0 arg B)) :
      HeadStepT E n Γ (.app (.lam A body) arg) (instantiate0 arg body)
        (instantiate0 arg B)
  /-- δ at the root — `headStep?`'s `.const` arm, `ParRedT.delta`
      verbatim. -/
  | delta (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
      (b T : Expr Nat)
      (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
      (hl : HasTyT E n Γ (.const r ls) T)
      (hr : HasTyT E n Γ (instantiateLevels ls b) T) :
      HeadStepT E n Γ (.const r ls) (instantiateLevels ls b) T
  /-- ζ at the root — the let unfolds at refl inner steps. -/
  | zeta (Γ : LCtx) (A value body B : Expr Nat) (u w : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hv : HasTyT E n Γ value A)
      (hB : HasTyT E n (.letBinding A value :: Γ) B (.sort w))
      (hTy : HasTyT E n Γ (instantiate0 value B) (.sort w))
      (hbody : HasTyT E n (.letBinding A value :: Γ) body B)
      (hred : HasTyT E n Γ (instantiate0 value body)
        (instantiate0 value B)) :
      HeadStepT E n Γ (.letE A value body) (instantiate0 value body)
        (instantiate0 value B)
  /-- literal expansion — `ParRedT.lit` verbatim. -/
  | lit (Γ : LCtx) (t : Nat) (T : Expr Nat)
      (hexp : HasTyT E n Γ (natExpand t) T) :
      HeadStepT E n Γ (.lit t) (natExpand t) T
  /-- ordinary ι at the root — the constructor-headed major. The
      `.ofU` landing is carried internally, pinning the reduct to the
      witness's own `iotaRhsOf`. Checked FIRST against the source
      shape (a `ctorMajor` major) — the "ι before ι★K" order. -/
  | iota (Γ : LCtx) (w : IotaWitness E) (T : Expr Nat)
      (hlhs : HasTyT E n Γ (iotaLhsOf w) T)
      (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
      HeadStepT E n Γ (iotaLhsOf w) (iotaRhsOf w) T
  /-- ι★K at the root — `ParRedT.iotaStarK`'s gate (`hmk`/`hmajor`/
      `hTm0`/`hfam`/`hrl`/`hsel`) plus the honest conversion-form
      guard `hcv` (the major's stored type converts to the
      constructor's own index instance `applyTel w.fields
      w.ctorAfterParams` — computed from the family's ctor type, not a
      caller-supplied index list) and the determinism guards `hnmin1`
      (singleton — forces `ctorIdx = 0`, hence `ctorRef`) and
      `hfields0` (the reduct reads the constructor's fields; a stuck
      major supplies none). The reduct is the witness's own
      `iotaRhsOf` via `.ofU`. -/
  | iotaStarK (Γ : LCtx) (w : IotaWitness E) (major Tm T : Expr Nat)
      (rl : Level) (afs : Prop)
      (hrl : piBody w.famMember.mtype = .sort rl)
      (hsel : EliminationSelection rl w.nMinors afs .anySort)
      (hnmin1 : w.nMinors = 1)
      (hfields0 : w.fields = [])
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hcv : Σ' (inst : Expr Nat),
          applyTel w.fields w.ctorAfterParams = some inst ×'
          TyConvT E n Γ Tm inst)
      (hmk : HasTyT E n Γ (ctorMajor w) Tm)
      (hTm0 : HasTyT E n Γ Tm (.sort .zero))
      (hlι : HasTyT E n Γ (iotaLhsOf w) T)
      (hlhs : HasTyT E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major) T)
      (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
      HeadStepT E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major)
        (iotaRhsOf w) T
  /-- ι★K at a Loop-shaped field-ful singleton — the canonical-fields
      arm. Same gate as `iotaStarK` (honest `hcv` — `applyTel [major]
      (Π Loop Loop)` computes `Loop`, no free index), plus
      `hfields1 : w.fields = [major]` (the canonical re-embedding of
      the stuck major — FIELDFUL_K's Loop choice) and `hnctor`, the
      REAL ι-before-ι★K negative premise: the major is not headed by
      the witness's own constructor, so this arm cannot overlap an
      `iotaLhsOf`-shaped source — at `mk x` the `.iota` arm owns the
      reduction. -/
  | iotaStarKField (Γ : LCtx) (w : IotaWitness E) (major Tm T : Expr Nat)
      (rl : Level) (afs : Prop)
      (hrl : piBody w.famMember.mtype = .sort rl)
      (hsel : EliminationSelection rl w.nMinors afs .anySort)
      (hnmin1 : w.nMinors = 1)
      (hfields1 : w.fields = [major])
      (hnctor : ∀ (lsC : List Level),
        (appsSpine major).1 ≠ .const w.ctorRef lsC)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hcv : Σ' (inst : Expr Nat),
          applyTel w.fields w.ctorAfterParams = some inst ×'
          TyConvT E n Γ Tm inst)
      (hmk : HasTyT E n Γ (ctorMajor w) Tm)
      (hTm0 : HasTyT E n Γ Tm (.sort .zero))
      (hlι : HasTyT E n Γ (iotaLhsOf w) T)
      (hlhs : HasTyT E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major) T)
      (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
      HeadStepT E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor major)
        (iotaRhsOf w) T

/-- SOUNDNESS — every head step is a typed `ParRedT` step, at any
    `PEq` plug. The conversion guard `hcv` is `HeadStepT`-internal;
    `ParRedT.iotaStarK` needs `hmk`, which is carried. -/
def headStepT_sound
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e e' T : Expr Nat} :
    HeadStepT E n Γ e e' T → ParRedT PEq E n Γ e e' T
  | .beta _ A body arg B u v w hA hB hTy hbody harg hred =>
      .beta _ A body body arg arg B u v w hA hB hTy
        (.refl _ _ _ hbody) (.refl _ _ _ harg) hred
  | .delta _ r ls m b T hres hbody htr hlen hwf hl hr =>
      .delta _ r ls m b T hres hbody htr hlen hwf hl hr
  | .zeta _ A value body B u w hA hv hB hTy hbody hred =>
      .zeta _ A value value body body B u w hA
        (.refl _ _ _ hv) hB hTy (.refl _ _ _ hbody) hred
  | .lit _ t T hexp => .lit _ t T hexp
  | .iota _ w T hlhs hrhs =>
      .iotaSpine _ (iotaLhsOf w) (iotaLhsOf w) (iotaRhsOf w) T
        (.refl _ _ _ hlhs) (.ofU w) hlhs hrhs
  | .iotaStarK _ w major Tm T rl afs hrl hsel _ _ hfam hmajor _ hmk
      hTm0 hlι hlhs hrhs =>
      .iotaStarK _ w major Tm (iotaRhsOf w) T rl afs hrl hsel hfam
        hmajor hmk hTm0 (.ofU w) hlι hlhs hrhs
  | .iotaStarKField _ w major Tm T rl afs hrl hsel _ _ _ hfam hmajor
      _ hmk hTm0 hlι hlhs hrhs =>
      .iotaStarK _ w major Tm (iotaRhsOf w) T rl afs hrl hsel hfam
        hmajor hmk hTm0 (.ofU w) hlι hlhs hrhs

/-! ## determinism support -/

/-- `iotaLhsOf`'s spine, as `appsSpine_recCall` computes it. -/
theorem headStepT_iotaLhs_spine {E : ResolvedEnv} (w : IotaWitness E) :
    appsSpine (iotaLhsOf w) =
      (.const w.recRef w.ls, w.preMajor ++ [ctorMajor w]) := by
  unfold iotaLhsOf
  exact appsSpine_recCall _ _ _ _

/-- `ctorMajor`'s spine head is the constructor constant. -/
theorem headStepT_ctorMajor_spine {E : ResolvedEnv}
    (w : IotaWitness E) :
    (appsSpine (ctorMajor w)).1 = .const w.ctorRef w.lsC := by
  unfold ctorMajor ctorSpine
  rw [appsSpine_foldApps_const]

/-- `appsSpine` on a `lam`-headed application reduces one step. -/
theorem headStepT_appsSpine_app_lam (A b x : Expr Nat) :
    appsSpine (.app (.lam A b) x) = (.lam A b, [x]) := rfl

/-- `appsSpine` on a bare `lam` is the catch-all pair. -/
theorem headStepT_appsSpine_lam (A b : Expr Nat) :
    appsSpine (.lam A b) = (.lam A b, []) := rfl

/-- `appsSpine` on a `letE` is the catch-all pair. -/
theorem headStepT_appsSpine_letE (A v b : Expr Nat) :
    appsSpine (.letE A v b) = (.letE A v b, []) := rfl

/-- `appsSpine` on a `lit` is the catch-all pair. -/
theorem headStepT_appsSpine_lit (t : Nat) :
    appsSpine (.lit t) = (.lit t, []) := rfl

/-- A field-free witness's reduct is its minor: `rhsArgs` reads only
    the field list. -/
theorem headStepT_iotaRhs_fields_nil {E : ResolvedEnv}
    (w : IotaWitness E) (hf : w.fields = []) :
    iotaRhsOf w = w.minor := by
  unfold iotaRhsOf
  rw [hf]
  rfl

/-- A `const`-headed `foldApps` never equals a `lam`. -/
theorem headStepT_foldApps_const_ne_lam {r : Nat} {ls : List Level}
    {xs : List (Expr Nat)} {A b : Expr Nat}
    (h : foldApps (.const r ls) xs = .lam A b) : False := by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const, headStepT_appsSpine_lam] at hs
  exact nomatch (Prod.mk.inj hs).1

/-- The family ref is recursor-member-determined: `hmajorTy` stores the
    major domain's family head inside `recDoms`, and `hpeelRec` peels
    the shared recursor member at the shared prefix length. Two
    witnesses at the same recursor with the same prefix length pin the
    same family. -/
theorem headStepT_iotaWitness_familyRef {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hlen : w₁.preMajor.length = w₂.preMajor.length) :
    w₁.familyRef = w₂.familyRef := by
  have hmemr : w₁.recMember = w₂.recMember := by
    have a := w₁.hrec
    have b := w₂.hrec
    rw [← hrec] at b
    exact Option.some.inj (a.symm.trans b)
  have hL : w₁.nparams + 1 + w₁.nMinors + w₁.nindices + 1 =
      w₂.nparams + 1 + w₂.nMinors + w₂.nindices + 1 := by
    have a := w₁.hpre
    have b := w₂.hpre
    omega
  have hd : w₁.recDoms = w₂.recDoms ∧ w₁.recBody = w₂.recBody := by
    have a := w₁.hpeelRec
    have b := w₂.hpeelRec
    rw [hL, hmemr] at a
    have eq : some (w₁.recDoms, w₁.recBody) =
        some (w₂.recDoms, w₂.recBody) := a.symm.trans b
    exact Prod.mk.inj (Option.some.inj eq)
  have hi : w₁.nparams + 1 + w₁.nMinors + w₁.nindices =
      w₂.nparams + 1 + w₂.nMinors + w₂.nindices := by
    have a := w₁.hpre
    have b := w₂.hpre
    omega
  have m1 := w₁.hmajorTy
  have m2 := w₂.hmajorTy
  rw [hd.1, hi] at m1
  have happ := Option.some.inj (m1.symm.trans m2)
  have hs := congrArg appsSpine happ
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  have hh := (Prod.mk.inj hs).1
  rw [Expr.const.injEq] at hh
  exact hh.1

/-- The shared-recursor `nMinors` transport: `hrecIdx` reads
    `recRef = familyRef + 1 + nMinors` off the shared member. -/
theorem headStepT_iotaWitness_nMinors_eq {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hpm : w₁.preMajor = w₂.preMajor) :
    w₁.nMinors = w₂.nMinors := by
  have hfam := headStepT_iotaWitness_familyRef hrec
    (congrArg List.length hpm)
  have a := w₁.hrecIdx
  have b := w₂.hrecIdx
  rw [← hrec, ← hfam] at b
  omega

/-- A singleton-gated ι★K witness forces field-freeness on ANY witness
    of the same recursor at the same prefix — the ι-vs-ι★K overlap's
    `fields = []` transport. -/
theorem headStepT_iotaStarK_fields_nil {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hpm : w₁.preMajor = w₂.preMajor)
    (hn2 : w₂.nMinors = 1) (hf2 : w₂.fields = []) :
    w₁.fields = [] := by
  have hnm := (headStepT_iotaWitness_nMinors_eq hrec hpm).trans hn2
  have hfam := headStepT_iotaWitness_familyRef hrec
    (congrArg List.length hpm)
  have hidx1 : w₁.ctorIdx = 0 := by have := w₁.hidx; omega
  have hidx2 : w₂.ctorIdx = 0 := by have := w₂.hidx; omega
  have hctor : w₁.ctorRef = w₂.ctorRef := by
    have a := w₁.hctorIdx
    have b := w₂.hctorIdx
    rw [hidx1, hfam] at a
    rw [hidx2] at b
    omega
  have ⟨_, hmemc, _, _, _, hnp, _, _⟩ :=
    iotaWitness_env_of_same_refs hrec hctor (congrArg List.length hpm)
  have hf2len : w₂.fields.length = 0 := congrArg List.length hf2
  have hlen : w₁.fields.length = 0 := by
    have a := w₁.hnpar
    have b := w₂.hnpar
    rw [← hmemc] at b
    omega
  exact List.eq_nil_of_length_eq_zero hlen

/-- The ι★K determinism core: two singleton witnesses at the same
    recursor head and prefix have the same minor — `ctorIdx` is forced
    to `0`, hence `ctorRef`, hence the member data, hence the minor's
    `preMajor` read position. -/
theorem headStepT_iotaStarK_minor_eq {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hpm : w₁.preMajor = w₂.preMajor)
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1) :
    w₁.minor = w₂.minor := by
  have hfam := headStepT_iotaWitness_familyRef hrec
    (congrArg List.length hpm)
  have hidx1 : w₁.ctorIdx = 0 := by have := w₁.hidx; omega
  have hidx2 : w₂.ctorIdx = 0 := by have := w₂.hidx; omega
  have hctor : w₁.ctorRef = w₂.ctorRef := by
    have a := w₁.hctorIdx
    have b := w₂.hctorIdx
    rw [hidx1, hfam] at a
    rw [hidx2] at b
    omega
  have ⟨_, _, _, _, _, hnp, _, _⟩ :=
    iotaWitness_env_of_same_refs hrec hctor (congrArg List.length hpm)
  have m1 := w₁.hminor
  have m2 := w₂.hminor
  rw [hpm, hnp, hidx1] at m1
  rw [hidx2] at m2
  exact Option.some.inj (m1.symm.trans m2)

/-- Two singleton witnesses at the same recursor head share
    `ctorRef`: `ctorIdx = 0` on both, so `ctorRef = familyRef + 1` and
    the family is shared. -/
theorem headStepT_iotaStarK_ctorRef_eq {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hpm : w₁.preMajor = w₂.preMajor)
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1) :
    w₁.ctorRef = w₂.ctorRef := by
  have hfam := headStepT_iotaWitness_familyRef hrec
    (congrArg List.length hpm)
  have hidx1 : w₁.ctorIdx = 0 := by have := w₁.hidx; omega
  have hidx2 : w₂.ctorIdx = 0 := by have := w₂.hidx; omega
  have a := w₁.hctorIdx
  have b := w₂.hctorIdx
  rw [hidx1, hfam] at a
  rw [hidx2] at b
  omega

/-- Two singleton witnesses at the same recursor head and prefix have
    the same field COUNT — `hnpar` reads the field count off the
    shared constructor member. The fields0-vs-field1 overlap's
    contradiction source. -/
theorem headStepT_iotaStarK_fields_len {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E}
    (hrec : w₁.recRef = w₂.recRef)
    (hpm : w₁.preMajor = w₂.preMajor)
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1) :
    w₁.fields.length = w₂.fields.length := by
  have hctor := headStepT_iotaStarK_ctorRef_eq hrec hpm hn1 hn2
  have ⟨_, hmemc, _, _, _, hnp, _, _⟩ :=
    iotaWitness_env_of_same_refs hrec hctor (congrArg List.length hpm)
  have a := w₁.hnpar
  have b := w₂.hnpar
  rw [hnp, hmemc] at a
  omega

/-- The canonical-fields ι★K determinism core: two `[major]`-field
    singleton witnesses at the same recursor head, levels, prefix and
    major have the same reduct — `fields` is `[major]` on both, and
    every other `iotaRhsOf` input is member- or source-determined. -/
theorem headStepT_iotaStarKField_rhs_eq {E : ResolvedEnv}
    {w₁ w₂ : IotaWitness E} {m₁ m₂ : Expr Nat}
    (hrec : w₁.recRef = w₂.recRef) (hls : w₁.ls = w₂.ls)
    (hpm : w₁.preMajor = w₂.preMajor) (hmaj : m₁ = m₂)
    (hf1 : w₁.fields = [m₁]) (hf2 : w₂.fields = [m₂])
    (hn1 : w₁.nMinors = 1) (hn2 : w₂.nMinors = 1) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  have hctor := headStepT_iotaStarK_ctorRef_eq hrec hpm hn1 hn2
  have ⟨_, hmemc, _, hnm, _, hnp, _, hk⟩ :=
    iotaWitness_env_of_same_refs hrec hctor (congrArg List.length hpm)
  have hcap : w₁.ctorAfterParams = w₂.ctorAfterParams := by
    have a := w₁.hctorAfter
    have b := w₂.hctorAfter
    rw [hpm, hnp, hls, hmemc] at a
    exact Option.some.inj (a.symm.trans b)
  have hm := headStepT_iotaStarK_minor_eq hrec hpm hn1 hn2
  unfold iotaRhsOf
  rw [hm, hrec, hls, hpm, hnp, hnm, hf1, hf2, hmaj, hk, hcap]

/-- The app-source classification: a head step out of `app f x` is a
    β (the function is a `lam`), an ordinary ι (the whole term is a
    witness's `iotaLhsOf`), or the guarded ι★K — each exposing the
    premises the refusal pin consumes. -/
inductive HeadStepTInvApp (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f x a T : Expr Nat) : Type where
  | beta (A body B : Expr Nat) (u v w : Level)
      (hf : f = .lam A body) (ha : a = instantiate0 x body) :
      HeadStepTInvApp E n Γ f x a T
  | iota (w : IotaWitness E)
      (heq : .app f x = iotaLhsOf w) (ha : a = iotaRhsOf w) :
      HeadStepTInvApp E n Γ f x a T
  | iotaStarK (w : IotaWitness E) (major Tm : Expr Nat)
      (rl : Level) (afs : Prop)
      (heq : .app f x =
        recCall (.const w.recRef w.ls) w.preMajor major)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hcv : Σ' (inst : Expr Nat),
          applyTel w.fields w.ctorAfterParams = some inst ×'
          TyConvT E n Γ Tm inst)
      (hnmin : w.nMinors = 1) (hfields : w.fields = [])
      (ha : a = iotaRhsOf w) :
      HeadStepTInvApp E n Γ f x a T
  | iotaStarKField (w : IotaWitness E) (major Tm : Expr Nat)
      (rl : Level) (afs : Prop)
      (heq : .app f x =
        recCall (.const w.recRef w.ls) w.preMajor major)
      (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
      (hmajor : HasTyT E n Γ major Tm)
      (hcv : Σ' (inst : Expr Nat),
          applyTel w.fields w.ctorAfterParams = some inst ×'
          TyConvT E n Γ Tm inst)
      (hnmin : w.nMinors = 1) (hfields1 : w.fields = [major])
      (hnctor : ∀ (lsC : List Level),
        (appsSpine major).1 ≠ .const w.ctorRef lsC)
      (ha : a = iotaRhsOf w) :
      HeadStepTInvApp E n Γ f x a T

/-- `app`-source inversion. -/
def headStepT_inv_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e f x a T : Expr Nat}
    (h : HeadStepT E n Γ e a T) (he : e = .app f x) :
    HeadStepTInvApp E n Γ f x a T := by
  cases h with
  | beta A body arg B u v w hA hB hTy hbody harg hred =>
      injection he with hf' hx'
      exact .beta A body B u v w hf'.symm
        (congrArg (fun t => instantiate0 t body) hx')
  | delta => exact nomatch he
  | zeta => exact nomatch he
  | lit => exact nomatch he
  | iota w T₀ hlhs hrhs => exact .iota w he.symm rfl
  | iotaStarK w major Tm T₀ rl afs hrl hsel hnmin hfields hfam
      hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exact .iotaStarK w major Tm rl afs he.symm hfam hmajor hcv
        hnmin hfields rfl
  | iotaStarKField w major Tm T₀ rl afs hrl hsel hnmin hfields1 hnctor
      hfam hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exact .iotaStarKField w major Tm rl afs he.symm hfam hmajor hcv
        hnmin hfields1 hnctor rfl

/-- `const`-source inversion: only δ reaches it. -/
def headStepT_inv_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a T : Expr Nat} {r : Nat} {ls : List Level}
    (h : HeadStepT E n Γ e a T) (he : e = .const r ls) :
    Σ' (m : CheckedMember) (b : Expr Nat),
      E.members r = some m ×' m.body = some b ×'
        a = instantiateLevels ls b := by
  cases h with
  | delta r₀ ls₀ m₀ b₀ T₀ hres hbody htr hlen hwf hl hr =>
      injection he with hr' hls'
      subst hr' hls'
      exact ⟨m₀, b₀, hres, hbody, rfl⟩
  | beta => exact nomatch he
  | zeta => exact nomatch he
  | lit => exact nomatch he
  | iota w T₀ hlhs hrhs =>
      exfalso
      have hs : (appsSpine (iotaLhsOf w)).2 =
          (appsSpine (Expr.const r ls)).2 :=
        congrArg (fun e => (appsSpine e).2) he
      rw [headStepT_iotaLhs_spine, appsSpine_const] at hs
      exact List.cons_ne_nil _ _ (List.append_eq_nil.mp hs).2
  | iotaStarK w major Tm T₀ rl afs hrl hsel hnmin hfields hfam
      hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs : (appsSpine
          (recCall (Expr.const w.recRef w.ls) w.preMajor major)).2 =
          (appsSpine (Expr.const r ls)).2 :=
        congrArg (fun e => (appsSpine e).2) he
      rw [appsSpine_recCall, appsSpine_const] at hs
      exact List.cons_ne_nil _ _ (List.append_eq_nil.mp hs).2
  | iotaStarKField w major Tm T₀ rl afs hrl hsel hnmin hfields1 hnctor
      hfam hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs : (appsSpine
          (recCall (Expr.const w.recRef w.ls) w.preMajor major)).2 =
          (appsSpine (Expr.const r ls)).2 :=
        congrArg (fun e => (appsSpine e).2) he
      rw [appsSpine_recCall, appsSpine_const] at hs
      exact List.cons_ne_nil _ _ (List.append_eq_nil.mp hs).2

/-- `letE`-source inversion: only ζ reaches it. -/
def headStepT_inv_letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a T A v b : Expr Nat}
    (h : HeadStepT E n Γ e a T) (he : e = .letE A v b) :
    a = instantiate0 v b := by
  cases h with
  | zeta A' v' b' B u w hA hv hB hTy hbody hred =>
      injection he with _ hv' hb'
      rw [hv', hb']
  | beta => exact nomatch he
  | delta => exact nomatch he
  | lit => exact nomatch he
  | iota w T₀ hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [headStepT_iotaLhs_spine, headStepT_appsSpine_letE] at hs
      exact nomatch (Prod.mk.inj hs).1
  | iotaStarK w major Tm T₀ rl afs hrl hsel hnmin hfields hfam
      hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [appsSpine_recCall, headStepT_appsSpine_letE] at hs
      exact nomatch (Prod.mk.inj hs).1
  | iotaStarKField w major Tm T₀ rl afs hrl hsel hnmin hfields1 hnctor
      hfam hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [appsSpine_recCall, headStepT_appsSpine_letE] at hs
      exact nomatch (Prod.mk.inj hs).1

/-- `lit`-source inversion: only the literal expansion reaches it. -/
def headStepT_inv_lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a T : Expr Nat} {t : Nat}
    (h : HeadStepT E n Γ e a T) (he : e = .lit t) :
    a = natExpand t := by
  cases h with
  | lit t₀ T₀ hexp =>
      injection he with ht
      rw [ht]
  | beta => exact nomatch he
  | delta => exact nomatch he
  | zeta => exact nomatch he
  | iota w T₀ hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [headStepT_iotaLhs_spine, headStepT_appsSpine_lit] at hs
      exact nomatch (Prod.mk.inj hs).1
  | iotaStarK w major Tm T₀ rl afs hrl hsel hnmin hfields hfam
      hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [appsSpine_recCall, headStepT_appsSpine_lit] at hs
      exact nomatch (Prod.mk.inj hs).1
  | iotaStarKField w major Tm T₀ rl afs hrl hsel hnmin hfields1 hnctor
      hfam hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exfalso
      have hs := congrArg appsSpine he
      rw [appsSpine_recCall, headStepT_appsSpine_lit] at hs
      exact nomatch (Prod.mk.inj hs).1

/-- Rigid sources take no head step. -/
def headStepT_inv_rigid {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a T : Expr Nat}
    (h : HeadStepT E n Γ e a T)
    (happ : ∀ f x, e ≠ .app f x)
    (hc : ∀ r ls, e ≠ .const r ls)
    (hl : ∀ A v b, e ≠ .letE A v b)
    (ht : ∀ t, e ≠ .lit t) : False := by
  cases h with
  | beta A body arg B u v w hA hB hTy hbody harg hred =>
      exact happ _ _ rfl
  | delta r ls m b T₀ hres hbody htr hlen hwf hl' hr =>
      exact hc _ _ rfl
  | zeta A value body B u w hA hv hB hTy hbody hred =>
      exact hl _ _ _ rfl
  | lit t T₀ hexp => exact ht _ rfl
  | iota w T₀ hlhs hrhs =>
      exact happ _ _
        (by unfold iotaLhsOf recCall; rw [foldApps_snoc])
  | iotaStarK w major Tm T₀ rl afs hrl hsel hnmin hfields hfam
      hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exact happ _ _ (by unfold recCall; rw [foldApps_snoc])
  | iotaStarKField w major Tm T₀ rl afs hrl hsel hnmin hfields1 hnctor
      hfam hmajor hcv hmk hTm0 hlι hlhs hrhs =>
      exact happ _ _ (by unfold recCall; rw [foldApps_snoc])

/-- DETERMINISM — `HeadStepT` is a partial function: the source
    determines the reduct. The type index is not claimed unique (type
    uniqueness is the diamond debt). -/
theorem headStepT_det {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e a b T T' : Expr Nat}
    (h₁ : HeadStepT E n Γ e a T) (h₂ : HeadStepT E n Γ e b T') :
    a = b := by
  cases e with
  | app f x =>
      match headStepT_inv_app h₁ rfl, headStepT_inv_app h₂ rfl with
      | .beta A₁ b₁ B₁ u₁ v₁ w₁ hf₁ ha₁,
          .beta A₂ b₂ B₂ u₂ v₂ w₂ hf₂ ha₂ =>
          have heq : Expr.lam A₁ b₁ = Expr.lam A₂ b₂ :=
            hf₁.symm.trans hf₂
          injection heq with _ hb
          subst hb
          exact ha₁.trans ha₂.symm
      | .beta A₁ b₁ B₁ u₁ v₁ w₁ hf₁ ha₁, .iota w₂ heq₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₁ b₁) x = iotaLhsOf w₂ :=
            hf₁ ▸ heq₂
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, headStepT_iotaLhs_spine]
            at hs
          exact nomatch (Prod.mk.inj hs).1
      | .beta A₁ b₁ B₁ u₁ v₁ w₁ hf₁ ha₁,
          .iotaStarK w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₁ b₁) x =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := hf₁ ▸ heq₂
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, appsSpine_recCall] at hs
          exact nomatch (Prod.mk.inj hs).1
      | .iota w₁ heq₁ ha₁, .beta A₂ b₂ B₂ u₂ v₂ w₂ hf₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₂ b₂) x = iotaLhsOf w₁ :=
            hf₂ ▸ heq₁
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, headStepT_iotaLhs_spine]
            at hs
          exact nomatch (Prod.mk.inj hs).1
      | .iota w₁ heq₁ ha₁, .iota w₂ heq₂ ha₂ =>
          have hl : iotaLhsOf w₁ = iotaLhsOf w₂ := heq₁.symm.trans heq₂
          rw [iotaWitness_deterministic hl] at ha₁
          exact ha₁.trans ha₂.symm
      | .iota w₁ heq₁ ha₁,
          .iotaStarK w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields₂ ha₂ =>
          have hl : iotaLhsOf w₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [headStepT_iotaLhs_spine, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, _⟩ := list_snoc_inj hargs
          have hf₁ : w₁.fields = [] :=
            headStepT_iotaStarK_fields_nil hrec hpm hnmin₂ hfields₂
          have hn1 : w₁.nMinors = 1 :=
            (headStepT_iotaWitness_nMinors_eq hrec hpm).trans hnmin₂
          have hm : w₁.minor = w₂.minor :=
            headStepT_iotaStarK_minor_eq hrec hpm hn1 hnmin₂
          rw [headStepT_iotaRhs_fields_nil w₁ hf₁] at ha₁
          rw [headStepT_iotaRhs_fields_nil w₂ hfields₂] at ha₂
          rw [hm] at ha₁
          exact ha₁.trans ha₂.symm
      | .iotaStarK w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields₁ ha₁,
          .beta A₂ b₂ B₂ u₂ v₂ w₂ hf₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₂ b₂) x =
              recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
                major₁ := hf₂ ▸ heq₁
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, appsSpine_recCall] at hs
          exact nomatch (Prod.mk.inj hs).1
      | .iotaStarK w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields₁ ha₁,
          .iota w₂ heq₂ ha₂ =>
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ = iotaLhsOf w₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, headStepT_iotaLhs_spine] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, _⟩ := list_snoc_inj hargs
          have hf₂ : w₂.fields = [] :=
            headStepT_iotaStarK_fields_nil hrec.symm hpm.symm hnmin₁
              hfields₁
          have hn2 : w₂.nMinors = 1 :=
            (headStepT_iotaWitness_nMinors_eq hrec.symm hpm.symm).trans
              hnmin₁
          have hm : w₁.minor = w₂.minor :=
            headStepT_iotaStarK_minor_eq hrec hpm hnmin₁ hn2
          rw [headStepT_iotaRhs_fields_nil w₁ hfields₁] at ha₁
          rw [headStepT_iotaRhs_fields_nil w₂ hf₂] at ha₂
          rw [hm] at ha₁
          exact ha₁.trans ha₂.symm
      | .iotaStarK w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields₁ ha₁,
          .iotaStarK w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields₂ ha₂ =>
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, _⟩ := list_snoc_inj hargs
          have hm : w₁.minor = w₂.minor :=
            headStepT_iotaStarK_minor_eq hrec hpm hnmin₁ hnmin₂
          rw [headStepT_iotaRhs_fields_nil w₁ hfields₁] at ha₁
          rw [headStepT_iotaRhs_fields_nil w₂ hfields₂] at ha₂
          rw [hm] at ha₁
          exact ha₁.trans ha₂.symm
      | .beta A₁ b₁ B₁ u₁ v₁ w₁ hf₁ ha₁,
          .iotaStarKField w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields1₂ hnctor₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₁ b₁) x =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := hf₁ ▸ heq₂
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, appsSpine_recCall] at hs
          exact nomatch (Prod.mk.inj hs).1
      | .iota w₁ heq₁ ha₁,
          .iotaStarKField w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields1₂ hnctor₂ ha₂ =>
          exfalso
          have hl : iotaLhsOf w₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [headStepT_iotaLhs_spine, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
          have hsp : (appsSpine (ctorMajor w₁)).1 =
              (appsSpine major₂).1 :=
            congrArg Prod.fst (congrArg appsSpine hmaj)
          rw [headStepT_ctorMajor_spine] at hsp
          have hn1 : w₁.nMinors = 1 :=
            (headStepT_iotaWitness_nMinors_eq hrec hpm).trans hnmin₂
          have hctor : w₁.ctorRef = w₂.ctorRef :=
            headStepT_iotaStarK_ctorRef_eq hrec hpm hn1 hnmin₂
          rw [hctor] at hsp
          exact hnctor₂ w₁.lsC hsp.symm
      | .iotaStarK w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields₁ ha₁,
          .iotaStarKField w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields1₂ hnctor₂ ha₂ =>
          exfalso
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, _⟩ := list_snoc_inj hargs
          have hlen :=
            headStepT_iotaStarK_fields_len hrec hpm hnmin₁ hnmin₂
          rw [hfields₁, hfields1₂] at hlen
          simp at hlen
      | .iotaStarKField w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields1₁ hnctor₁ ha₁,
          .beta A₂ b₂ B₂ u₂ v₂ w₂ hf₂ ha₂ =>
          have heq : Expr.app (Expr.lam A₂ b₂) x =
              recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
                major₁ := hf₂ ▸ heq₁
          have hs := congrArg appsSpine heq
          rw [headStepT_appsSpine_app_lam, appsSpine_recCall] at hs
          exact nomatch (Prod.mk.inj hs).1
      | .iotaStarKField w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields1₁ hnctor₁ ha₁,
          .iota w₂ heq₂ ha₂ =>
          exfalso
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ = iotaLhsOf w₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, headStepT_iotaLhs_spine] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
          have hsp : (appsSpine (ctorMajor w₂)).1 =
              (appsSpine major₁).1 :=
            congrArg Prod.fst (congrArg appsSpine hmaj.symm)
          rw [headStepT_ctorMajor_spine] at hsp
          have hn2 : w₂.nMinors = 1 :=
            (headStepT_iotaWitness_nMinors_eq hrec.symm hpm.symm).trans
              hnmin₁
          have hctor : w₁.ctorRef = w₂.ctorRef :=
            headStepT_iotaStarK_ctorRef_eq hrec hpm hnmin₁ hn2
          rw [← hctor] at hsp
          exact hnctor₁ w₂.lsC hsp.symm
      | .iotaStarKField w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields1₁ hnctor₁ ha₁,
          .iotaStarK w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields₂ ha₂ =>
          exfalso
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec _
          obtain ⟨hpm, _⟩ := list_snoc_inj hargs
          have hlen :=
            headStepT_iotaStarK_fields_len hrec hpm hnmin₁ hnmin₂
          rw [hfields1₁, hfields₂] at hlen
          simp at hlen
      | .iotaStarKField w₁ major₁ Tm₁ rl₁ afs₁ heq₁ hfam₁ hmaj₁ hcv₁
            hnmin₁ hfields1₁ hnctor₁ ha₁,
          .iotaStarKField w₂ major₂ Tm₂ rl₂ afs₂ heq₂ hfam₂ hmaj₂ hcv₂
            hnmin₂ hfields1₂ hnctor₂ ha₂ =>
          have hl : recCall (Expr.const w₁.recRef w₁.ls) w₁.preMajor
              major₁ =
              recCall (Expr.const w₂.recRef w₂.ls) w₂.preMajor
                major₂ := heq₁.symm.trans heq₂
          have hs := congrArg appsSpine hl
          rw [appsSpine_recCall, appsSpine_recCall] at hs
          injection hs with hh hargs
          injection hh with hrec hls
          obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
          have heq :=
            headStepT_iotaStarKField_rhs_eq hrec hls hpm hmaj
              hfields1₁ hfields1₂ hnmin₁ hnmin₂
          rw [heq] at ha₁
          exact ha₁.trans ha₂.symm
  | const r ls =>
      have ⟨m₁, b₁, hres₁, hbody₁, ha₁⟩ := headStepT_inv_const h₁ rfl
      have ⟨m₂, b₂, hres₂, hbody₂, ha₂⟩ := headStepT_inv_const h₂ rfl
      have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
      have hb : b₁ = b₂ := by
        have hh := hbody₁
        rw [hm] at hh
        exact Option.some.inj (hh.symm.trans hbody₂)
      rw [hb] at ha₁
      exact ha₁.trans ha₂.symm
  | letE A v b =>
      rw [headStepT_inv_letE h₁ rfl, headStepT_inv_letE h₂ rfl]
  | lit t =>
      rw [headStepT_inv_lit h₁ rfl, headStepT_inv_lit h₂ rfl]
  | sort l =>
      exact (headStepT_inv_rigid h₁
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)).elim
  | bvar i =>
      exact (headStepT_inv_rigid h₁
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)).elim
  | pi A B =>
      exact (headStepT_inv_rigid h₁
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)).elim
  | lam A b =>
      exact (headStepT_inv_rigid h₁
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)).elim

/-! ## pins -/

/-- The Nat-fixture β redex `(λ n : N. n) zero`. -/
def pinNatBetaRedex : Expr Nat :=
  .app (.lam (.const 0 []) (.bvar 0)) (.const 1 [])

/-- PIN 1 — a β head step: `(λ n : N. n) zero ⇒ zero` at `N`. All
    instantiations are definitional (`lift`/`instantiate0` are the
    identity on `const`s). -/
def pin_headStepT_beta_nat : HeadStepT natEnvPrefix 1 []
    pinNatBetaRedex (.const 1 []) (.const 0 []) := by
  show HeadStepT natEnvPrefix 1 []
    (.app (.lam (.const 0 []) (.bvar 0)) (.const 1 []))
    (.const 1 []) (.const 0 [])
  refine HeadStepT.beta [] (.const 0 []) (.bvar 0) (.const 1 [])
    (.const 0 []) (.succ .zero) (.succ .zero) (.succ .zero) ?_ ?_ ?_ ?_
    ?_ ?_
  · exact HasTyT.const [] 0 [] natFamMember rfl rfl rfl
  · exact HasTyT.const [.assumption (.const 0 [])] 0 []
      natFamMember rfl rfl rfl
  · exact HasTyT.const [] 0 [] natFamMember rfl rfl rfl
  · exact HasTyT.bvar [.assumption (.const 0 [])] 0 (.const 0 []) rfl
  · exact HasTyT.const [] 1 [] natZeroMember rfl rfl rfl
  · exact HasTyT.const [] 1 [] natZeroMember rfl rfl rfl

/-- PIN 2 — the ordinary ι head step at the `refl`-headed Eq major:
    `rec α a M m a (refl α a) ⇒ m` at `M a (refl α a)`. -/
def pin_headStepT_iota_eq : HeadStepT eqEnvT 1 eqJoinCtx
    (iotaLhsOf eqKWitness) (.bvar 1) eqEqLhs :=
  HeadStepT.iota eqJoinCtx eqKWitness eqEqLhs eqRecLhsTy eqTym

/-- `iotaLhsOf`'s stored type `M a (refl α a)` converts to `M a q` by
    `irr` — the `hlι` transport. -/
def pinEqLhsAtP : HasTyT eqEnvT 1 eqJoinCtx
    (iotaLhsOf eqKWitness) eqMotAp :=
  hasTyT_of_tyConv eqRecLhsTy
    (TyConvT.of eqJoinCtx _ _ (.param 0)
      (ConvT.symm _ _ _ _ eqTyX))

/-- `m : M a p` — the reduct's typing at `eqMotAp`, transported. -/
def pinEqRhsAtP : HasTyT eqEnvT 1 eqJoinCtx (.bvar 1) eqMotAp :=
  hasTyT_of_tyConv eqTym
    (TyConvT.of eqJoinCtx _ _ (.param 0)
      (ConvT.symm _ _ _ _ eqTyX))

/-- `rec α a M m a q : M a q` — the redex's typing. -/
def pinEqLhsStarTy : HasTyT eqEnvT 1 eqJoinCtx
    (.app eqRecFive (.bvar 0)) eqMotAp :=
  HasTyT.app _ _ _ _ _ eqRecTy5 pinEqGate_met

/-- PIN 3 — the GUARDED ι★K head step at `q : Eq α a a`: the major
    types at the constructor's index (the gate, `pinEqGate_met`), the
    conversion guard is refl at `Eq α a a` (`idx := [a]` on the
    canonical spine), the family is singleton `Prop`, the constructor
    is field-free — `rec α a M m a q ⇒ m` at `M a q`. -/
def pin_headStepT_iotaStarK_eq : HeadStepT eqEnvT 1 eqJoinCtx
    (.app eqRecFive (.bvar 0)) (.bvar 1) eqMotAp := by
  show HeadStepT eqEnvT 1 eqJoinCtx
    (recCall (.const 65 [.param 0]) eqRecPreJ (.bvar 0)) _ _
  exact HeadStepT.iotaStarK eqJoinCtx eqKWitness (.bvar 0) eqPTyAt0
    eqMotAp .zero True
    rfl
    (.singletonProp (fun _ => rfl) rfl True.intro)
    rfl rfl
    ⟨[], by
      show (appsSpine (foldApps (.const 63 [])
        [.bvar 4, .bvar 3, .bvar 3])).1 = .const 63 []
      rw [appsSpine_foldApps_const]⟩
    pinEqGate_met
    ⟨eqKWitness.ctorAfterParams, rfl, TyConvT.refl _ _⟩
    eqReflTy2 eqFamTy3 pinEqLhsAtP pinEqLhsStarTy pinEqRhsAtP

/-- PIN 4 — the canonical-fields ι★K step at Loop:
    `rec M m x ⇒ m x (rec M m x)` via `.iotaStarKField` at `wLoopK`.
    The major `x` is stuck — its `appsSpine` head is `.bvar 0`, not the
    `mk` constructor, so `hnctor` holds and this arm owns the source
    (`.iota` requires the `ctorMajor` shape `x` lacks). `fields = [x]`
    is the canonical re-embedding, and the honest `hcv` computes `Loop`
    itself (`applyTel [x] (Π Loop Loop) = Loop` — no free index). -/
def pin_headStepT_iotaStarKField_loop :
    HeadStepT pinLoopEnvT 1 pinLoopCtx
      (recCall pinLoopRecHead [.bvar 2, .bvar 1] (.bvar 0))
      wLoopRhs loopMx :=
  .iotaStarKField pinLoopCtx wLoopK (.bvar 0) (.const 60 []) loopMx
    .zero True
    rfl
    (.singletonProp (fun _ => rfl) rfl True.intro)
    rfl rfl
    (by
      intro lsC h
      have h' : (Expr.bvar 0 : Expr Nat) = .const 61 lsC := h
      exact nomatch h')
    ⟨[], rfl⟩
    loopVarTyT
    ⟨.const 60 [], rfl, TyConvT.refl _ _⟩
    loopMkTyT loopFamTyT loopLhsITyT loopLhsTyT loopRhsTyT

/-- PIN 5 — the neutral-major gate debt: any head step on
    `rec α a M m b p` (`p : Eq α a b`, `b` distinct from `a`) must come
    from the ι★K arm — β is impossible (the function is a `foldApps`
    of a const), ordinary ι is impossible (the major `bvar 0` is not a
    `ctorMajor`, and `.iotaStarKField` is impossible — `fields = [major]`
    forces `nparams = 1`, which `hmajorTy`'s stored index-vector shape
    contradicts). The surviving `.iotaStarK` arm forces a singleton
    field-free witness at rec `65` whose honest conversion guard pays
    `TyConvT (Eq α a b) (Eq α a a)` — the instance is the
    constructor's OWN `ctorAfterParams`, not a caller-chosen index. -/
def pin_headStepT_eqNeut_gate {n : Nat} {rhs T : Expr Nat}
    (h : HeadStepT eqEnvT n eqNeutCtx eqNeutRedex rhs T) :
    Σ' (w : IotaWitness eqEnvT) (inst : Expr Nat),
      w.recRef = 65 ×' w.ls = [.param 0] ×' w.nMinors = 1 ×'
        w.fields = [] ×'
        (inst = foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 4]) ×'
        (∃ lsF, (appsSpine inst).1 = Expr.const 63 lsF) ×'
        TyConvT eqEnvT n eqNeutCtx (lift 0 1 eqNeutPTy) inst := by
  have he : eqNeutRedex =
      .app (foldApps (.const 65 [.param 0])
        [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]) (.bvar 0) := rfl
  match headStepT_inv_app h he with
  | .beta A body B u v w' hf' ha' =>
      exact absurd hf' headStepT_foldApps_const_ne_lam
  | .iota w heq ha =>
      exfalso
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        headStepT_iotaLhs_spine] at hs
      injection hs with _ hargs
      obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
      have hcm : (appsSpine (.bvar 0)).1 =
          (appsSpine (ctorMajor w)).1 :=
        congrArg (fun e => (appsSpine e).1) hmaj
      rw [appsSpine_bvar, headStepT_ctorMajor_spine] at hcm
      have hbc : Expr.bvar 0 = Expr.const w.ctorRef w.lsC := hcm
      exact nomatch hbc
  | .iotaStarK w major Tm rl afs heq hfam hmajor hcv hnmin hfields
      ha =>
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        appsSpine_recCall] at hs
      injection hs with hh hargs
      injection hh with hrec hls
      obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
      have hmajor' : HasTyT eqEnvT n eqNeutCtx (.bvar 0) Tm := by
        rw [← hmaj] at hmajor
        exact hmajor
      obtain ⟨A, hlk, hcv0⟩ := hasTyTInv_bvar hmajor' rfl
      have hA : A = lift 0 1 eqNeutPTy := by
        have hh0 : lookupType eqNeutCtx 0 = some (lift 0 1 eqNeutPTy) :=
          rfl
        exact Option.some.inj (hlk.symm.trans hh0)
      rw [hA] at hcv0
      obtain ⟨inst, hinst, hcvT⟩ := hcv
      have hidx0 : w.ctorIdx = 0 := by have := w.hidx; omega
      have hfam63 : w.familyRef = 63 := by
        have a := w.hrecIdx
        rw [← hrec] at a
        omega
      have hctor64 : w.ctorRef = 64 := by
        have a := w.hctorIdx
        rw [hfam63, hidx0] at a
        omega
      have hmemr : w.recMember = eqRecT := by
        have a := w.hrec
        rw [← hrec] at a
        exact (Option.some.inj a).symm
      have hmemc : w.ctorMember = eqReflT := by
        have a := w.hctor
        rw [hctor64] at a
        exact (Option.some.inj a).symm
      have hnp : w.nparams = 2 := by
        have a := w.hnpar
        rw [hmemc, hfields] at a
        have a2 : w.nparams + 0 = 2 := a
        omega
      have hcap : w.ctorAfterParams =
          foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 4] := by
        have a := w.hctorAfter
        rw [← hpm, hnp, ← hls, hmemc] at a
        have hcomp : applyTel
            ([.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1].take 2)
            (instantiateLevels [.param 0] eqReflT.mtype) =
            some (foldApps (.const 63 [])
              [.bvar 5, .bvar 4, .bvar 4]) := rfl
        exact Option.some.inj (a.symm.trans hcomp)
      rw [hfields] at hinst
      have hinsteq : inst =
          foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 4] :=
        (Option.some.inj hinst).symm.trans hcap
      refine ⟨w, inst, hrec.symm, hls.symm, hnmin, hfields, hinsteq,
        ?_, ?_⟩
      · refine ⟨[], ?_⟩
        rw [hinsteq, appsSpine_foldApps_const]
      · exact TyConvT.trans _ _ _ _ hcv0 hcvT
  | .iotaStarKField w major Tm rl afs heq hfam hmajor hcv hnmin
      hfields1 hnctor ha =>
      exfalso
      have hs := congrArg appsSpine heq
      rw [← foldApps_snoc, appsSpine_foldApps_const,
        appsSpine_recCall] at hs
      injection hs with hh hargs
      injection hh with hrec hls
      obtain ⟨hpm, hmaj⟩ := list_snoc_inj hargs
      have hlen5 : w.preMajor.length = 5 :=
        (congrArg List.length hpm).symm
      have hcnt : w.nparams + 1 + w.nMinors + w.nindices = 5 := by
        have a := w.hpre
        omega
      have hidx0 : w.ctorIdx = 0 := by have := w.hidx; omega
      have hfam63 : w.familyRef = 63 := by
        have a := w.hrecIdx
        rw [← hrec] at a
        omega
      have hctor64 : w.ctorRef = 64 := by
        have a := w.hctorIdx
        rw [hfam63, hidx0] at a
        omega
      have hmemr : w.recMember = eqRecT := by
        have a := w.hrec
        rw [← hrec] at a
        exact (Option.some.inj a).symm
      have hmemc : w.ctorMember = eqReflT := by
        have a := w.hctor
        rw [hctor64] at a
        exact (Option.some.inj a).symm
      have hnp : w.nparams = 1 := by
        have a := w.hnpar
        rw [hmemc, hfields1] at a
        have a2 : w.nparams + 1 = 2 := a
        omega
      have hni : w.nindices = 2 := by omega
      have hpe := w.hpeelRec
      rw [show w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 by omega,
        hmemr] at hpe
      have hcomp : peelPis 6 eqRecT.mtype = some
          ([.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3,
            foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]],
           .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := rfl
      have hrd : w.recDoms = [.sort (.succ .zero), .bvar 0, eqMotT,
          eqMinorT, .bvar 3,
          foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]] :=
        (Prod.mk.inj (Option.some.inj (hcomp.symm.trans hpe))).1.symm
      have hmj := w.hmajorTy
      rw [hrd, hcnt] at hmj
      have hEq63 : foldApps (Expr.const 63 [])
          [Expr.bvar 4, Expr.bvar 3, Expr.bvar 0] =
          foldApps (Expr.const w.familyRef
            ((List.range w.famMember.arity).map Level.param))
            (List.map (fun i => Expr.bvar (i + w.nindices + w.nMinors
                + 1))
              (List.range w.nparams).reverse ++
              List.map (fun i => Expr.bvar i)
                (List.range w.nindices).reverse) :=
        Option.some.inj hmj
      rw [hnp, hni, hnmin] at hEq63
      have hs2 := congrArg appsSpine hEq63
      rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs2
      have hargs2 := (Prod.mk.inj hs2).2
      have hreq : List.map
            (fun i => Expr.bvar (i + 2 + 1 + 1))
            (List.range 1).reverse ++
          List.map (fun i => Expr.bvar i) (List.range 2).reverse =
          ([Expr.bvar 4, Expr.bvar 1, Expr.bvar 0] :
            List (Expr Nat)) := rfl
      rw [hreq] at hargs2
      injection hargs2 with _ hrest
      injection hrest with hbad _
      rw [Expr.bvar.injEq] at hbad
      omega

/-- The contrapositive: the major's stored `Eq α a b` does NOT convert
    to the constructor's index instance `Eq α a a` (the honest guard's
    determined `inst`), so no head step exists — the recursor stays
    neutral. (`→ False`: `HeadStepT` is `Type`-valued.) -/
theorem pin_headStepT_eqNeut_refusal {n : Nat} {rhs T : Expr Nat}
    (hno : TyConvT eqEnvT n eqNeutCtx (lift 0 1 eqNeutPTy)
      (foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 4]) → False)
    (h : HeadStepT eqEnvT n eqNeutCtx eqNeutRedex rhs T) : False := by
  obtain ⟨w, inst, _, _, _, _, hin, hfam63, hcvI⟩ :=
    pin_headStepT_eqNeut_gate h
  rw [hin] at hcvI
  exact hno hcvI

end Rcic.Declarative
