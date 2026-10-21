/-
RCIC F-03 Batch A — M-9 corpus pins.
Each pin: a #eval that transcribes a carrier corpus row through the encoding.
Hand-transcribed per §18.3 rule 4 (no host-language string interpolation).

CARRIER: apps/rcic-whnf-at/rcic_whnf_at_corpus.json (17 rows).
  before/after (M-009): 17 rows → 15 transcribed + 2 EXCLUDED BY LABEL:
  - row 14 "unknown form 1 refuses rcic_whnf_unknown_form" — no `form`
    field exists in any Lean certifier (annex M-9 clause (c)).
  - row 16 "delta on an UNKNOWN transparency tag (transp=7) STAYS
    neutral — registry W1 tooth" — MemberClass is a closed 7-ctor
    inductive; unrepresentable (clause (c)); the tooth moves to the
    ENCODING FUNCTION, not a theorem.
  - row 15 "unknown expr kind 7" is TRANSCRIBED (C-P3-1): Expr kind 7
    has no carrier image but `Expr.lit` IS the Lean-side image; pinned
    against whnfCert's .lit refusal AND machineWhnfDone.

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_whnf_row00 ← "beta identity: app lam x reduces to x (RM-014; mutant agrees)"
  pin_whnf_row01 ← "beta with substitution into body pins expr_inst composition (RM-014; mutant agrees)"
  pin_whnf_row02 ← "multi-arg spine: two args, one head action per fuel unit (RM-014; mutant agrees)"
  pin_whnf_row03 ← "zeta: letE head instantiates body with value (RM-014; mutant agrees)"
  pin_whnf_row04 ← "delta transparent bare const unfolds stored body then lam is whnf (RM-014; mutant agrees)"
  pin_whnf_row05 ← "delta transparent applied: unfold then beta through spine (RM-014; mutant agrees)"
  pin_whnf_row06 ← "delta on theorem STAYS neutral - GM-THEORY-004 primary tooth (mutant unfolds stored body)"
  pin_whnf_row07 ← "delta on opaque STAYS neutral - GM-THEORY-004 (mutant unfolds stored body)"
  pin_whnf_row08 ← "recursor-shaped const head stays neutral - iota not in slice, no RHS (RM-014 sec12; mutant agre…)"
  pin_whnf_row09 ← "lam at head already whnf - no reduction inside lambda bodies - sec12 line 330 (mutant reduces b…)"
  pin_whnf_row10 ← "neutral arguments are not reduced - sec12 line 330; theorem head also trips GM-THEORY-004 mutan…"
  pin_whnf_row11 ← "transparent definition without body stays - no value to unfold (RM-014; mutant agrees)"
  pin_whnf_row12 ← "fuel 0 with head action pending refuses rcic_whnf_fuel (RM-014; mutant agrees)"
  pin_whnf_row13 ← "fuel exhaustion mid-spine after one action refuses rcic_whnf_fuel (RM-014; mutant agrees)"
  pin_whnf_row15 ← "unknown expr kind 7 refuses rcic_whnf_unknown_ctor (RM-014; mutant agrees)"

ENV IMAGE (shared by rows 0-15; ref = the corpus group hash):
  r=0 ← 5f01b2c4d6a8e0f1: transp 0 (definitionM), body lam (sort 0) (bvar 0)
  r=1 ← 7c22d3e5f7a9b1d3: transp 1 (theoremM), body sort 1
  r=2 ← 9d33e4f6a8b0c2e4: transp 2 (opaqueM), body sort 1
  r=3 ← b1e44f5a9c1d3f5a: transp 3 (recursorM), body bvar 0
  r=4 ← c3f55a6b0d2e4a6b: transp 0, NO body
  arity/mtype are not consulted by whnfCert; set to 0 / sort 0.
-/
import rcic.RcicMachine

namespace Rcic.MachinePins
open Rcic.Machine
open Rcic.Declarative

/-- The corpus' shared env image, five members at refs 0-4. -/
def memDef : CheckedMember :=
  ⟨.definitionM, 0, .sort .zero, some (.lam (.sort .zero) (.bvar 0))⟩
def memThm : CheckedMember :=
  ⟨.theoremM, 0, .sort .zero, some (.sort (.succ .zero))⟩
def memOpa : CheckedMember :=
  ⟨.opaqueM, 0, .sort .zero, some (.sort (.succ .zero))⟩
def memRec : CheckedMember :=
  ⟨.recursorM, 0, .sort .zero, some (.bvar 0)⟩
def memNoBody : CheckedMember :=
  ⟨.definitionM, 0, .sort .zero, none⟩

def E1 : ResolvedEnv where
  members := fun r =>
    match r with
    | 0 => some memDef
    | 1 => some memThm
    | 2 => some memOpa
    | 3 => some memRec
    | 4 => some memNoBody
    | _ => none

/-! ## whnf-at rows (fuel 8 unless the row measures fuel) -/

-- row 0: beta identity → sort 0
#eval (if (match whnfCert E1 0 8 []
      (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)) with
    | .ok ⟨.sort .zero, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row00")

-- row 1: beta with substitution → app (const 1) (sort 0)
#eval (if (match whnfCert E1 0 8 []
      (.app (.lam (.sort .zero) (.app (.bvar 0) (.sort .zero)))
        (.const 1 [])) with
    | .ok ⟨.app (.const 1 []) (.sort .zero), _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row01")

-- row 2: two-arg spine, two head actions → sort 0
#eval (if (match whnfCert E1 0 8 []
      (.app (.app (.lam (.sort .zero) (.bvar 0))
        (.lam (.sort .zero) (.bvar 0))) (.sort .zero)) with
    | .ok ⟨.sort .zero, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row02")

-- row 3: zeta → const 1
#eval (if (match whnfCert E1 0 8 []
      (.letE (.sort .zero) (.const 1 []) (.bvar 0)) with
    | .ok ⟨.const 1 _, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row03")

-- row 4: delta transparent bare → lam (sort 0) (bvar 0)
#eval (if (match whnfCert E1 0 8 [] (.const 0 []) with
    | .ok ⟨.lam (.sort .zero) (.bvar 0), _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row04")

-- row 5: delta transparent applied → unfold then beta → sort 0
#eval (if (match whnfCert E1 0 8 []
      (.app (.const 0 []) (.sort .zero)) with
    | .ok ⟨.sort .zero, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row05")

-- row 6: delta on theorem STAYS — app (const 1) (sort 0)
#eval (if (match whnfCert E1 0 8 []
      (.app (.const 1 []) (.sort .zero)) with
    | .ok ⟨.app (.const 1 _) (.sort .zero), _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row06")

-- row 7: delta on opaque STAYS — const 2
#eval (if (match whnfCert E1 0 8 [] (.const 2 []) with
    | .ok ⟨.const 2 _, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row07")

-- row 8: recursor-shaped head STAYS (no iota) — spine unchanged
#eval (if (match whnfCert E1 0 8 []
      (.app (.app (.const 3 []) (.sort .zero)) (.sort .zero)) with
    | .ok ⟨.app (.app (.const 3 _) (.sort .zero)) (.sort .zero), _⟩ => true
    | _ => false)
  then 0 else panic "pin_whnf_row08")

-- row 9: lam at head is whnf; body NOT reduced
#eval (if (match whnfCert E1 0 8 []
      (.lam (.sort .zero)
        (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 1))) with
    | .ok ⟨.lam (.sort .zero)
        (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 1)), _⟩ => true
    | _ => false)
  then 0 else panic "pin_whnf_row09")

-- row 10: neutral arguments NOT reduced
#eval (if (match whnfCert E1 0 8 []
      (.app (.const 1 [])
        (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))) with
    | .ok ⟨.app (.const 1 _)
        (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)), _⟩ => true
    | _ => false)
  then 0 else panic "pin_whnf_row10")

-- row 11: transparent without body STAYS — const 4
#eval (if (match whnfCert E1 0 8 [] (.const 4 []) with
    | .ok ⟨.const 4 _, _⟩ => true | _ => false)
  then 0 else panic "pin_whnf_row11")

-- row 12: fuel 0 with head action pending → [rcic_whnf_fuel]
#eval (if (match whnfCert E1 0 0 []
      (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)) with
    | .no "[rcic_whnf_fuel]" => true | _ => false)
  then 0 else panic "pin_whnf_row12")

-- row 13: fuel exhaustion mid-spine (fuel 1, two actions) → [rcic_whnf_fuel]
#eval (if (match whnfCert E1 0 1 []
      (.app (.app (.lam (.sort .zero) (.bvar 0))
        (.lam (.sort .zero) (.bvar 0))) (.sort .zero)) with
    | .no "[rcic_whnf_fuel]" => true | _ => false)
  then 0 else panic "pin_whnf_row13")

-- row 15: unknown expr kind 7 → the Lean-side .lit image refuses
-- [rcic_whnf_unknown_ctor] (C-P3-1); machineWhnfDone is false too
#eval (if (match whnfCert E1 0 8 [] (.lit 0) with
    | .no "[rcic_whnf_unknown_ctor]" => true | _ => false)
  then 0 else panic "pin_whnf_row15a")
#eval (if machineWhnfDone E1 (.lit 0) = false
  then 0 else panic "pin_whnf_row15b")


/-! ## conv-at rows (carrier: apps/rcic-conv-at/rcic_conv_at_corpus.json)

CARRIER 17 rows → 10 transcribed + 7 EXCLUDED BY LABEL:
  - rows 2, 4, 6, 7, 9, 10 (clause (a) RULING L / (b) D-5): every
    confirm that runs through ρ-relative level equality
    (max(0,succ p0)=succ p0); the Lean convCert compares level lists
    SYNTACTICALLY (Conv.consts over eqNList refl-anchored), so these
    rows REFUSE in Lean where the carrier ACCEPTS — MR-8's permitted
    direction, excluded per annex M-9 clause (a).
  - row 15 "unknown form: form=1" (clause (c)): no form field exists
    in any Lean certifier.
  - (row 14 is PINNED below, directly on the certifier — E-F03 (a):
    the fuel-0 arm restored to M-4's print, the row refuses under the
    same name on both sides, MR-7 10(ii) as written.)

Members reused from E1: r=1 ← 7c22d3e5f7a9b1d3 (theoremM, body),
r=2 ← 9d33e4f6a8b0c2e4 (opaqueM, body).

TRANSCRIPTION TABLE:
  pin_conv_row00 ← "§13 step 1: syntactic-equal pi confirms before any whnf (RM-017; mutant agrees)"
  pin_conv_row01 ← "§13 step 3: whnf does real work — beta on left only, then structural re-check (RM-017; m…)"
  pin_conv_row03 ← "§13 step 5: sort mismatch via level_equal (1 vs 2; RM-011; mutant agrees)"
  pin_conv_row05 ← "§13 step 6 / GM-ID-003 tooth: same ref digest, different level lists -> [rcic_conv_mismatch] (mutant…)"
  pin_conv_row08 ← "§13 step 7: app congruence mismatch — same head, different args -> [rcic_conv_mismatch] (mutant…)"
  pin_conv_row11 ← "§13 step 9: rigid mismatch — bvar head vs const head -> [rcic_conv_mismatch] (mutant agr…)"
  pin_conv_row12 ← "§13 step 8 NAMED out-of-slice: lam/lam, bodies under the binder mismatch -> [rcic_conv_eta…]"
  pin_conv_row13 ← "§13 step 2 NAMED out-of-slice: a_type sort-0 (Prop-sorted model) + steps 1/3 fail -> [rc…]"
  pin_conv_row14 ← "fuel: one action per unit — fuel 0 with the step-1 comparison pending -> [rcic_conv_fuel]"
  pin_conv_row16 ← "§13 step 6 / registry C4 length tooth: same ref digest, level lists [succ zero] vs [] -> [rcic_conv…]"
-/

-- level shorthands used below
private def l1 : Level := .succ .zero
private def l2 : Level := .succ (.succ .zero)

-- row 0: syntactic-equal pi confirms (A = sort 2)
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.pi (.sort l1) (.bvar 0)) (.pi (.sort l1) (.bvar 0)), 40⟩ with
    | .result (.accepted .conversionConfirmed) => true | _ => false)
  then 0 else panic "pin_conv_row00")

-- row 1: beta on left, then structural re-check confirms (A = sort 1)
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l1)
        (.app (.lam (.sort l1) (.bvar 0)) (.sort .zero))
        (.sort .zero), 40⟩ with
    | .result (.accepted .conversionConfirmed) => true | _ => false)
  then 0 else panic "pin_conv_row01")

-- row 3: sort 1 vs sort 2 mismatch (A = sort 2, non-zero → mismatch
-- residue, NOT irrelevance)
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.sort l1) (.sort l2), 40⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_row03")

-- row 5: same ref, level lists [succ 0] vs [0] mismatch (GM-ID-003
-- tooth; row 16 below is the length tooth [succ 0] vs [])
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.const 1 [l1]) (.const 1 [.zero]), 40⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_row05")

-- row 8: app congruence mismatch — args sort 0 vs sort 1
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.app (.const 1 []) (.sort .zero))
        (.app (.const 1 []) (.sort l1)), 40⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_row08")

-- row 9: rigid mismatch — bvar head vs const head
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.bvar 0) (.const 1 []), 40⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_row11")

-- row 12: lam/lam bodies mismatch → eta out-of-slice residue
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.lam (.sort l1) (.bvar 0))
        (.lam (.sort l1) (.app (.const 1 []) (.bvar 0))), 40⟩ with
    | .result (.refused "[rcic_conv_eta_out_of_slice]") => true | _ => false)
  then 0 else panic "pin_conv_row12")

-- row 13: A = sort 0 (Prop) → irrelevance out-of-slice residue
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort .zero) (.const 1 []) (.const 2 []), 40⟩ with
    | .result (.refused "[rcic_conv_irrelevance_out_of_slice]") => true | _ => false)
  then 0 else panic "pin_conv_row13")

-- row 14: fuel 0 → [rcic_conv_fuel] (the step-1 comparison is an
-- action; MR-7 10(ii): same name both sides). Decoded row: a_type =
-- sort 1, l = r = sort 0, fuel 0. Pinned directly on the certifier —
-- kernelStepRaw at budget 0 suspends before the task arm (RM004/
-- RM008's content), so the carrier's fuel-0 premise travels convCert.
#eval (if (match convCert E1 0 0 [] (.sort (.succ .zero))
      (.sort .zero) (.sort .zero) with
    | .no "[rcic_conv_fuel]" => true | _ => false)
  then 0 else panic "pin_conv_row14")

-- row 16: C4 length tooth — level lists [1] vs [] on the same ref
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l2) (.const 1 [l1]) (.const 1 []), 40⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_row16")

/-! ## convCert `.app` arm — sub-call `.no` re-labelling

The `.app`/`.app` congruence arm must only ever turn the match's own
`.no` into `.ok`: a refused sub-call is answered with the pre-arm
catch-all residue `convMismatchResidue A l r` (computed on the TASK
sides), not by forwarding the sub-call's own residue.  Forwarding
flipped `accepted .conversionMismatch` into `.refused` on
`[rcic_conv_eta_out_of_slice]` and `[rcic_conv_fuel]`. -/

-- repro A: the argument sub-call refuses lam/lam (eta out-of-slice);
-- the arm answers the match's residue → accepted .conversionMismatch.
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l1) (.app (.bvar 0) (.lam (.sort .zero) (.bvar 0)))
        (.app (.bvar 0) (.lam (.sort .zero) (.sort .zero))), 8⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_appArm_eta_relable")

-- repro B: the function sub-call hits fuel 0 ([rcic_conv_fuel]);
-- the arm answers the match's residue → accepted .conversionMismatch.
#eval (if (match kernelStepRaw ⟨⟨E1, 0, []⟩,
      .convAt (.sort l1) (.app (.bvar 0) (.sort .zero))
        (.app (.bvar 0) (.sort l1)), 1⟩ with
    | .result (.accepted .conversionMismatch) => true | _ => false)
  then 0 else panic "pin_conv_appArm_fuel_relable")


/-! ## infer-full rows (carrier: apps/rcic-infer-full/rcic_infer_full_corpus.json)

CARRIER 16 rows → 15 transcribed + 1 EXCLUDED BY LABEL:
  - row 13 "form1 unknown form refused" (clause (c)): no form field
    exists in any Lean certifier; the row measures the carrier's
    request boundary.

ENV IMAGE E2 (per-row images unioned; refs chosen disjoint from E1):
  r=10 ← grp-g: opaqueM, mtype c(grp-F)=const 11, NO body
  r=11 ← grp-F: definitionM, mtype sort 1, body Π sort 1. sort 1
  r=12 ← grp-c0: theoremM, mtype sort 0, NO body
  r=13 ← grp-D: definitionM, mtype sort 2, body sort 1
  r=9  ← grp-no: ABSENT (rows 9/15 measure the missing-group path)
  arity is absent in the carrier; Lean pins set arity 0 (the only
  arity inferCert admits).
CTX entries (rows 5, 10): tag 0 = LocalDecl.assumption.

TRANSCRIPTION TABLE:
  pin_inf_row00..12, 14, 15 ← the carrier labels, in corpus order;
  row 11 pins at ambient univs = 1 (param 0 in slice).
-/

private def memG : CheckedMember :=
  ⟨.opaqueM, 0, .const 11 [], none⟩
private def memF : CheckedMember :=
  ⟨.definitionM, 0, .sort l1, some (.pi (.sort l1) (.sort l1))⟩
private def memC0 : CheckedMember :=
  ⟨.theoremM, 0, .sort .zero, none⟩
private def memD : CheckedMember :=
  ⟨.definitionM, 0, .sort l2, some (.sort l1)⟩

def E2 : ResolvedEnv where
  members := fun r =>
    match r with
    | 9 => none
    | 10 => some memG
    | 11 => some memF
    | 12 => some memC0
    | 13 => some memD
    | _ => none

private def ctx5 : LCtx := [.assumption (.pi (.sort l1) (.bvar 0))]
private def ctx10 : LCtx := [.assumption (.sort .zero)]

-- row 0: app of identity lam — beta-free infer → sort 1
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.app (.lam (.sort l1) (.bvar 0)) (.sort .zero)), 120⟩ with
    | .result (.accepted (.inferredType (.sort l1))) => true | _ => false)
  then 0 else panic "pin_inf_row00")

-- row 1: fn type needs DELTA (grp-g : c(grp-F), grp-F unfolds) → sort 1
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.app (.const 10 []) (.sort .zero)), 120⟩ with
    | .result (.accepted (.inferredType (.sort l1))) => true | _ => false)
  then 0 else panic "pin_inf_row01")

-- row 2: arg conversion through transparent grp-D → T = c(grp-D)
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.app (.lam (.const 13 []) (.bvar 0)) (.sort .zero)), 120⟩ with
    | .result (.accepted (.inferredType (.const 13 []))) => true | _ => false)
  then 0 else panic "pin_inf_row02")

-- row 3: arg type pi vs domain sort 1 → refused, the corpus's own
-- residue name (ok=0, code=[rcic_conv_mismatch])
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.app (.lam (.sort l1) (.bvar 0)) (.lam (.sort l1) (.bvar 0))), 120⟩ with
    | .result (.refused "[rcic_conv_mismatch]") => true | _ => false)
  then 0 else panic "pin_inf_row03")

-- row 4: lam infer → the Pi record
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.lam (.sort l1) (.bvar 0)), 120⟩ with
    | .result (.accepted (.inferredType
        (.pi (.sort (Level.succ .zero)) (.sort (Level.succ .zero))))) => true
    | _ => false)
  then 0 else panic "pin_inf_row04")

-- row 5: dependent app through the let variable → sort 0
#eval (if (match kernelStepRaw ⟨⟨E2, 0, ctx5⟩,
      .infer (.letE (.sort l1) (.sort .zero)
        (.app (.bvar 1) (.bvar 0))), 120⟩ with
    | .result (.accepted (.inferredType (.sort .zero))) => true | _ => false)
  then 0 else panic "pin_inf_row05")

-- row 6: letE declared type checked, value converted → sort 1
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.letE (.sort l1) (.sort .zero) (.sort .zero)), 120⟩ with
    | .result (.accepted (.inferredType (.sort l1))) => true | _ => false)
  then 0 else panic "pin_inf_row06")

-- row 7: const resolve → stored type sort 0
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.const 12 []), 120⟩ with
    | .result (.accepted (.inferredType (.sort .zero))) => true | _ => false)
  then 0 else panic "pin_inf_row07")

-- row 8: const with nonempty level list → out of slice
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.const 12 [.zero]), 120⟩ with
    | .result (.refused "[rcic_infer_const_levels_out_of_slice]") => true
    | _ => false)
  then 0 else panic "pin_inf_row08")

-- row 9: missing group → lookup residue, no name fallback
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.const 9 []), 120⟩ with
    | .result (.refused "[rcic_lookup_group_not_found]") => true | _ => false)
  then 0 else panic "pin_inf_row09")

-- row 10: pi infer incl. imax → sort (imax 1 0)
#eval (if (match kernelStepRaw ⟨⟨E2, 0, ctx10⟩,
      .infer (.pi (.sort .zero) (.bvar 0)), 120⟩ with
    | .result (.accepted (.inferredType (.sort (.imax l1 .zero)))) => true
    | _ => false)
  then 0 else panic "pin_inf_row10")

-- row 11: sort (param 0) at n=1 → sort (succ (param 0))
#eval (if (match kernelStepRaw ⟨⟨E2, 1, []⟩,
      .infer (.sort (.param 0)), 120⟩ with
    | .result (.accepted (.inferredType (.sort (.succ (.param 0))))) => true
    | _ => false)
  then 0 else panic "pin_inf_row11")

-- row 12: fuel 1 — lam domain infer exhausts the single budget
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.app (.lam (.sort l1) (.bvar 0)) (.sort .zero)), 1⟩ with
    | .result (.refused "[rcic_infer_fuel]") => true | _ => false)
  then 0 else panic "pin_inf_row12")

-- row 14: unknown expr kind 7 → the .lit image refuses
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.lit 0), 120⟩ with
    | .result (.refused "[rcic_infer_unknown_ctor]") => true | _ => false)
  then 0 else panic "pin_inf_row14")

-- row 15: levels check fires BEFORE group resolution
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.const 9 [.zero]), 120⟩ with
    | .result (.refused "[rcic_infer_const_levels_out_of_slice]") => true
    | _ => false)
  then 0 else panic "pin_inf_row15")


/-! ## pi-check rows (carrier: apps/rcic-pi-check/rcic_pi_check_corpus.json)

CARRIER 12 rows → 7 transcribed + 5 EXCLUDED BY LABEL (the annex's
own split; MR-7 entry 9 is the reason row 6 is excluded, not pinned):
  - row 7 (clause (a)): "form1 Check accept ONLY through conversion:
    succ(param 0) vs max(0,succ(param 0)) equal under rho=[0]" —
    Lean compares levels syntactically; REFUSE-where-carrier-ACCEPTS
    (MR-8 permitted direction).
  - row 8 (clause (d)): "form0 out-of-slice term: app refused by name"
    — the composite routes Expr kind 3 to infer-full's app arm, which
    ACCEPTS; imaged by pin_inf_row00/01/02.
  - row 9 (clause (c)): form=2 — no form field in any Lean certifier.
  - row 10 (clause (d)): "form1 conv out of slice: inferred sort 1 vs
    expected pi" — the conversion-slice boundary.

TRANSCRIPTION TABLE:
  pin_pc_row00 ← "form0 bvar lookup+shift GM-safe: ty pi(bvar 0)(bvar 0) at i=0 -> lift 0 1 (02 §4; 03…)"
  pin_pc_row01 ← "form0 bvar out of bounds: i=2 over 1-entry ctx (03 §3 LookupLocalType bounds)"
  pin_pc_row02 ← "form0 sort infer: sort(succ(param 0)), n=1 -> sort(succ(succ(param 0))) (03 §10 Sort…)"
  pin_pc_row03 ← "form0 pi imax tooth GM-THEORY-002: pi(sort 0)(bvar 0) -> sort(imax 1 0); imax 1 0 = 0 (mutant…) (03 §10 Pi)"
  pin_pc_row04 ← "form0 pi nested: pi(sort 0)(pi(bvar 0)(sort 0)) -> sort(imax 1 (imax 0 1)) (03 §10 Pi)"
  pin_pc_row05 ← "form1 Check accept: sort(param 0) : sort(succ(param 0)) — noncumulative, equal under rho"
  pin_pc_row11 ← "form1 Check order: EnsureSort(expected) fires BEFORE the term infer — expected bvar…"
-/

private def ctxP0 : LCtx :=
  [.assumption (.pi (.bvar 0) (.bvar 0)),
   .letBinding (.sort .zero) (.sort .zero)]
private def ctxP1 : LCtx := [.assumption (.sort .zero)]

-- row 0 (form 0 → inferCert): bvar lookup+shift → lift 0 1 applied
#eval (if (match kernelStepRaw ⟨⟨E2, 0, ctxP0⟩, .infer (.bvar 0), 10⟩ with
    | .result (.accepted (.inferredType (.pi (.bvar 1) (.bvar 0)))) => true
    | _ => false)
  then 0 else panic "pin_pc_row00")

-- row 1 (form 0): bvar out of bounds
#eval (if (match kernelStepRaw ⟨⟨E2, 0, ctxP1⟩, .infer (.bvar 2), 10⟩ with
    | .result (.refused "[rcic_pi_check_bvar_unbound]") => true | _ => false)
  then 0 else panic "pin_pc_row01")

-- row 2 (form 0, n=1): sort(succ p0) → sort(succ succ p0)
#eval (if (match kernelStepRaw ⟨⟨E2, 1, []⟩,
      .infer (.sort (.succ (.param 0))), 10⟩ with
    | .result (.accepted (.inferredType
        (.sort (.succ (.succ (.param 0)))))) => true
    | _ => false)
  then 0 else panic "pin_pc_row02")

-- row 3 (form 0): imax tooth — pi(sort 0)(bvar 0) → sort(imax 1 0)
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.pi (.sort .zero) (.bvar 0)), 10⟩ with
    | .result (.accepted (.inferredType
        (.sort (.imax (Level.succ .zero) .zero)))) => true
    | _ => false)
  then 0 else panic "pin_pc_row03")

-- row 4 (form 0): nested pi → sort(imax 1 (imax 0 1))
#eval (if (match kernelStepRaw ⟨⟨E2, 0, []⟩,
      .infer (.pi (.sort .zero)
        (.pi (.bvar 0) (.sort .zero))), 10⟩ with
    | .result (.accepted (.inferredType (.sort
        (.imax (Level.succ .zero) (.imax .zero (Level.succ .zero)))))) => true
    | _ => false)
  then 0 else panic "pin_pc_row04")

-- row 5 (form 1 → checkCert): Check accept, syntactic at n=1
#eval (if (match kernelStepRaw ⟨⟨E2, 1, []⟩,
      .check (.sort (.param 0)) (.sort (.succ (.param 0))), 10⟩ with
    | .result (.accepted .checked) => true | _ => false)
  then 0 else panic "pin_pc_row05")

-- row 11 (form 1): EnsureSort(expected) BEFORE term infer
#eval (if (match kernelStepRaw ⟨⟨E2, 0, ctxP1⟩,
      .check (.app (.sort .zero) (.sort .zero)) (.bvar 2), 40⟩ with
    | .result (.refused "[rcic_pi_check_bvar_unbound]") => true | _ => false)
  then 0 else panic "pin_pc_row11")


/-! ## lookup rows (carrier: apps/rcic-lookup/rcic_lookup_corpus.json)

CARRIER 10 rows → 2 transcribed + 8 EXCLUDED BY LABEL (M-9(e): the
annex's own row-by-row measurement — ResolvedEnv is a function
`Nat → Option CheckedMember`, not a member list, so the (group,
index) pair, the name field, and list bounds have no image):
  - rows 0, 1 ("exact digest hit member 1/0") — need a member index;
  - row 2 ("missing digest that equals an entry name") — needs the
    authoritative `name` field;
  - rows 3, 4, 5 (GM-REF-002 index == count / beyond count /
    negative) — bounds over a list; `i : Nat` has no negative;
  - row 9 (B2 "empty members index 0") — vacuous-index-0 bounds;
  - row 8 "form 9 unknown form" (clause (c)): no form field in any
    Lean certifier.
  M-007 CONSEQUENCE (stated in the annex): all three mutant arms
  (name fallback, index wrap, vacuous index-0) CANNOT be annotated as
  retired-to-a-theorem — the teeth move to the ENCODING FUNCTION.

ENV IMAGE E3: (3a7c1b90e5d2f4a8, member 1) → ref 20;
(9f01d2c4b6a8e0f7, member 0) → ref 21; both arity 0, mtype sort 0.
Absent digests ("beta", "ffffffffffffffff") map to unresolved refs.

TRANSCRIPTION TABLE:
  pin_lu_row06 ← "EG-016 form 0 empty environment refused by name"
  pin_lu_row07 ← "GM-REF-001 form 0 digest absent from non-empty environment refused no ambient merge"
-/

def E3 : ResolvedEnv where
  members := fun r =>
    match r with
    | 20 => some ⟨.definitionM, 0, .sort .zero, none⟩
    | 21 => some ⟨.definitionM, 0, .sort .zero, none⟩
    | _ => none

-- row 6: EMPTY environment → group-not-found (emptyEnv has no refs)
#eval (if (match kernelStepRaw
      ⟨⟨emptyEnv, 0, []⟩, .lookupDeclaration 20 [], 10⟩ with
    | .result (.refused "[rcic_lookup_group_not_found]") => true | _ => false)
  then 0 else panic "pin_lu_row06")

-- row 7: digest absent from a NON-EMPTY environment → refused
#eval (if (match kernelStepRaw ⟨⟨E3, 0, []⟩, .lookupDeclaration 99 [], 10⟩ with
    | .result (.refused "[rcic_lookup_group_not_found]") => true | _ => false)
  then 0 else panic "pin_lu_row07")

/- H-11 M-002 / M-005 pins: `levelEqual` arm is
`decEqN`. Dummy Ambient. -/

-- m005 param 0 vs param 1 REFUSED
#eval (if (match kernelStepRaw
    ⟨⟨emptyEnv, 0, []⟩,
      .levelEqual (.param 0) (.param 1), 1⟩ with
    | .result (.refused "[rcic_level_not_equal]") =>
        true
    | _ => false)
  then 0 else panic "pin_h11_param")

-- m005 imax 1 0 vs 0 ACCEPTED
#eval (if (match kernelStepRaw
    ⟨⟨emptyEnv, 0, []⟩,
      .levelEqual
        (.imax (.succ .zero) .zero) .zero, 1⟩ with
    | .result (.accepted .conversionConfirmed) =>
        true
    | _ => false)
  then 0 else panic "pin_h11_imax")

-- m005 imax 0 u vs u ACCEPTED
#eval (if (match kernelStepRaw
    ⟨⟨emptyEnv, 0, []⟩,
      .levelEqual
        (.imax .zero (.param 0)) (.param 0), 1⟩ with
    | .result (.accepted .conversionConfirmed) =>
        true
    | _ => false)
  then 0 else panic "pin_h11_unbound")

-- H-11b M-005: imax 1 (param 0) vs param 0 ACCEPTED
#eval (if (match kernelStepRaw
    ⟨⟨emptyEnv, 0, []⟩,
      .levelEqual
        (.imax (.succ .zero) (.param 0))
        (.param 0), 1⟩ with
    | .result (.accepted .conversionConfirmed) =>
        true
    | _ => false)
  then 0 else panic "pin_h11b_imax_param")

end Rcic.MachinePins
