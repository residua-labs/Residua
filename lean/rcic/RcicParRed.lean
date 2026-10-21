/-
RCIC F-05b PiConvInj fragment: `parRedStar_pi_inj` (star).
Full `PiConvInj` stays a named obligation (O-1).

RCIC F-05b attempt 4: iotaSpine joins iota-vs-app without transporting
IotaWitness typing equalities (the minor-application equality is not
ParRed-closed). 00 §19.2 erratum 5 has since DELETED the field that
stated it, `IotaTyping.hminApply` — it mentioned `preMajor.drop
(nparams + 1 + nMinors)`, which no witness field constrains, so it was
a second RULE ∀-BUNDLE hazard. Its content is now `hminTel` plus the
index agreement at the actual fields, which 00 §19.2 erratum 6 moved
to the conversion layer (`IndexCoherentConv`) and DISCHARGED from the
redex's own typing, so it is no longer a premise anywhere. Conv
embedding of iotaSpine still goes through the original redex.

RCIC F-05b attempt 3: fragment characterizations that ARE theorems
about the landed ParRed judgment. SortConvChar / PiConvInj over full
Conv stay open (O-1).

M-001: 02 DT-021 quotes "The theory is noncumulative. There is no rule
turning A : Sort u into A : Sort v merely because u ≤ₙ v." The
InvertFamily `SortConvChar` (`Conv (sort u) (sort v) → eqN u v`) is a
confluence corollary, not that sentence. It is false-shaped while
`LiteralExpansion.intro` inhabits arbitrary middles (lit 0 steps to
sort 0 and sort 1; trans+symm). Do not inhabit it; do not empty
LiteralExpansion (M-002b). Fragment form: `parRedStar_sort_eq`.
PiConvInj over full Conv is the same hole; fragment forms:
`parRed_pi_inj`, `parRedStar_pi_inj`.

Failing statement (unconditioned): SortConvChar / PiConvInj over raw
`Conv`. Attempt count: 15 on Conv-recursion (11-13 here, 14 at
:6066, 15 recorded below). `piIrr_pi_pi` refutes unconditioned
PiConvInj via `Conv.irr` at junk `T : Prop := Prop`;
`piConvInj_sortConvChar_false` is the compiled pair-refutation
(commit 910087743). O-3: both obligations are now EnvWf-conditioned
(correction, not weakening). Ledger rows stay open. `closure_claim`
stays 0.

RCIC F-05b Conv-lane WALL RECORD — attempt 53 in this file's global
attempt sequence, attempt 15 on the Conv-recursion lane.

Failing statement: the typed conversion characterization under
`EnvWf` + `CtxWf` whose `irr` arm is cut by the subject's typing, by
any recursion measured on `sizeConv` / `sizeHasTy` over the landed
judgments.

Re-diagnosis of attempts 11-14 (so attempt 16 does not re-derive it):
their recorded cause, "reconstructed `trans` is not a subterm", is a
TERMINATION reading of two different failures.
(i) For the JOIN design (`convRedOnly_join`, `RcicConvChar.lean`) no
typing invariant is carried, so `trans` is free — it is discharged by
star confluence. What does not decrease is `parRedSR → PiConvInj`: in
the app-congruence arm subject reduction knows `Conv Γ (.pi A B) T_f`
only as the OUTPUT of its own IH, an object with no size bound
relative to its input, and no strengthening bounds it (`convSubst` /
`convSubstLet` build `Conv`s of uncontrolled size). `oneStepSR`'s own
use of `hpci` does decrease (`hcv_lam` comes from `hasTyLamInv hf`, a
subderivation) — which is why the head-reduction SR exists today and
the parallel one does not.
[CORRECTED by C-1 at attempt 54 below: the app-congruence arm names an
AVOIDABLE inversion and consumes no `PiConvInj`. The hop survives, but
at `beta`, where the Π-conversion IS a subderivation.]
(ii) For the naive TYPED statement the failure is invariant
propagation, not termination: `Step.beta` carries no typing premises
and `Conv.refl` holds at every term, so a `Conv` between two types
passes through UNTYPED middles, and the congruence arms do not type
their components either.

The remaining ring is named: `parRedSR` (subject reduction along one
PARALLEL step) ⊃ `noTypeIsProof`. It is NOT DT-010/011: `Steps`
(`RcicDTMeta.lean:203`) is built from `Step`, which has no congruence
constructors, so `ParRed ⊄ Steps` and DT-011 does not cover a
parallel step under a binder. `parRedSR`'s `iotaSpine` arm consumes
`iotaPreserve`, which through 00 §20.6 was discharged only
conditionally on `LevelCoherent` (owner face 02 universes) — so
`instantiateLevels` was a prerequisite of the whole F-05 face
(00 §19.4 edge added by that segment). §20.6 LANDED it: the row is
discharged, the premise is deleted, and BOTH `02 universes →` edges of
§19.4 are gone. 00 §19.2 erratum 6 then removed the second per-redex
premise the same way: the syntactic index equation was too strong to
be supplied, is restated as `IndexCoherentConv`, and is derived by
`iotaLhs_ctorIdx_conv` off the same `FamAppConvInj` application. So
`iotaPreserve` now carries `FamAppConvInj` and `CtxWf` only — no
per-redex coherence premise survives, and no `ParRedIndexCoherent`
sibling has to be written. `RcicConvChar.lean` discharges the fragment
reachable without `parRedSR`: every `Conv` derivation using neither
`eta` nor `irr`.

RCIC F-05b Conv-lane ROUTE CHANGE — attempt 54 in this file's global
attempt sequence, attempt 16 on the Conv-recursion lane. A ROUTE
CHANGE, not a retry: attempt 53's statement is neither re-attempted nor
abandoned; it is re-diagnosed, three of its recorded reasons are
CORRECTED (O-3), and a different, weaker product is landed.

WHAT LANDED: `parRedSR` / `parRedArgsSR` / `parRedStarSR`
(`RcicParRedSR.lean`), subject reduction along one PARALLEL step, on
the nose (`HasTy Γ e' A`), all thirteen `ParRed` arms, CONDITIONAL on
`PiConvInj` + `FamAppConvInj` + `EnvWf` + `CtxWf` — exactly the set
`oneStepSR` together with `iotaPreserve` already carries. No new
obligation. (`LitPreserve` was in that set until segment 7a discharged
it VACUOUSLY — 00 §19.7 E-LitP: `HasTy` then had no `lit` rule — and
O-2 deleted `hLitP` from all three statements. TRIPWIRE FIRED: DT-017
landed `HasTy.lit` and discharged the row FOR REAL, `litPreserve`,
00 §20.11; `hLitP` is re-carried NOWHERE.) Structural on the
`ParRed`/`ParRedArgs`
derivation in `parRed_to_conv`'s idiom; per 00 §19.4 no second measure
was written (`parRedW` remains the one numeric measure).

  C-1. The app-congruence arm needs NO `PiConvInj`. `hasTyAppInv`
  returns the function's Π-typing directly and `HasTy.conv ∘ Conv.symm`
  consumes an IH output without inverting it; the argument's movement
  is absorbed by `conv_instantiate0_value`, which carries no typing
  premise. Measured: `hpci` enters at TWO of thirteen arms — `beta`
  (on `hasTyLamInv`'s Π-conversion, a SUBDERIVATION, byte-identical to
  `oneStepSR.beta`) and `iotaSpine` (through `iotaPreserve`). The ring
  is INTACT; the correction says where its third edge actually is.

  C-2. Nose form, not `Σ'`. Interderivable, hence not a
  strengthening; it is the form `IotaPreserve` / `LitPreserve` (the
  latter discharged FOR REAL by `litPreserve` since segment 10 — 00
  §20.11, §19.7 E-LitP2 / E-LitP3 — not a premise) and four of
  `oneStepSR`'s six arms already have, and it deletes the
  `SortConvChar` consumption a `Σ'`-form `lam` / `pi` arm would need
  to re-establish that the IH's output type IS a sort. (Honest
  caveat: the `Σ'` form can avoid that consumption too, by
  `HasTy.conv ∘ Conv.symm`.)

  C-3. The three `irr` cuts do NOT factor through one statement — not
  because the candidate is false, but because it is not cheaper.
  `NoSortProp` — `CtxWf Γ → Conv Γ (.sort w) P →
  HasTy Γ P (.sort .zero) → False` — is BLOCKED at its `.pi` arm on an
  unlanded row, with a compiled artifact: `noSortProp_piArm_witness` /
  `noSortProp_piArm_readout` (`RcicParRedSR.lean`). `hasTyPiInv`
  yields `Conv Γ (.sort (.imax u v)) T`, so all the typing hypothesis
  gives at that arm is `eqN (.imax u v) .zero`, which is TRUE at
  `v = .zero` (`eqN_imax_zero`); and `Π (Q : Prop). Q : Prop` is
  inhabited at every `E`, `n`, `Γ`, so neither `EnvWf` nor `CtxWf` cuts
  it. The arm rests entirely on `Conv Γ (.sort w) (.pi A B) → False`
  — "no sort converts to a Π" — neither `SortConvChar` nor `PiConvInj`,
  not on the §19.2 ledger, NOT introduced, and a characterization row
  of the very ring the statement was meant to shortcut. Type-④
  evidence of non-closure by inversion plus level arithmetic; NOT a
  refutation (the artifact constructs no `Conv Γ (.sort w) (.pi A B)`;
  corrected 2026-09-05 after a review finding on #3815). `NoSortProp`
  is deliberately not defined anywhere, so the artifact does not read
  its target from an editable def.

RESIDUAL AFTER THIS SEGMENT, NAMED — two items, neither attempted
here: the `irr` cut ON THE TYPED FRAGMENT (no `NoSortProp`, no untyped
`Conv → Join`; the cut must be met at inner `trans` nodes with
arbitrary endpoints, where `hasTySortInv` is inapplicable), and
ETA-POSTPONEMENT past `⇒*`. `parRed_diamond` was NOT re-opened.
`closure_claim` stays 0; the three §19.2 rows stay OPEN with `RedOnly`
still on them.
-/

-- This file is now a thin aggregator.  The development it used to
-- hold in one 13 786-line module lives in the seven pieces below, in
-- dependency order; `import rcic.RcicParRed` still brings in all of
-- it.  Import a single piece instead when that is all you need.
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicParRedWeight
import rcic.RcicParRedSortWall
import rcic.RcicParRedSubst
import rcic.RcicParRedDevel
import rcic.RcicParRedDiamond
