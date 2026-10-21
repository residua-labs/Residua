/-
CG-014 S0 slice A — the landed CG-014 arm is BLIND to the admitted
environment, so over the real admission judgment "accepted ⇒ typed
judgment" is refuted for every byte-faithful env decoder that can represent
an ill-typed environment (S0: `research/rcic/cg/S0_CG014.md`).

The real admission judgment on main is `Rcic.GraphAdmitted.graphAdmitted`,
whose `accepted` path is exactly the CG-014 arm `acceptedCheck`
(`graphAdmitted_accepted_binding`, sealed). The arm reads the admitted
environment ONLY through `refBound` — found, no collision, nonempty bytes —
and reads the typed-judgment object only through its two keys. It runs no
R-CIC typing check (09 §19 stage 3, "replay R-CIC proof checks", is not a
stage of the landed checker). This module proves that as theorems over the
real arm, never over an ad-hoc evaluator:

* `acceptedCheck_env_congr` — the arm's verdict is invariant under any change
  of the store that keeps the judgment record, the assumptions `refBound`,
  the typed-judgment scan and the env `refBound` fixed: the env BYTES do not
  enter.
* `blind_accepts` — at one concrete store family `blindStore b`, the arm
  accepts for EVERY nonempty env image `b`, and the env ref resolves to
  exactly `b` (`blind_env_scan`).
* `cg014_arm_refuted` — for any byte-faithful decoder (`ByteFaithful`) that
  decodes some nonempty `b` to an environment with no `EnvWfT`, the arm
  accepts `blindStore b` and `TypedJudgmentBound` FAILS there.
* `cg014_arm_forces_total_wf` — equivalently: CG-014 over the arm
  (`CG014Arm`) forces the decoder to send EVERY nonempty byte string to a
  well-formed environment. No faithful env-image codec (04 §9) does that.
* Inhabitants (no vacuous premise): `toothDec`/`toothObjects` represent the
  sealed ill-typed `toothEnvU` (`tooth_EG007T_untyped_body`), and
  `pin_cg014_arm_refuted_tooth` instantiates the refutation;
  `pin_blind_accepts_two_images` shows two distinct env images accepted.

Consequence (the WALLs, S0 §4): CG-014 over the REAL judgment needs
(W1) an env-image codec `bytes → ResolvedEnv` (04 §9 `EnvironmentImage`; no
Lean or scm decoder exists — two searches in the S0) and (W2) a typing stage
in the admission checker that consults it. The existing `cg014_of_binding`
discharges neither: its conclusion is its two decode premises repackaged
(`_hb` unused). No sealed statement is changed by this module.

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

import rcic.RcicGraphAdmitted
import rcic.RcicEGTypedBody
import rcic.RcicEGTypedAccept
import rcic.RcicExprSubstTask
import rcic.ScmWireInv
import rcic.ScmBoundCoreTV

namespace Rcic.GraphAdmitted.Blind

open Rcic.BoundObject (StoreEntry storeScan canonPartOk canonBytesOk)
open Rcic.Scm.Embed (partAt keysOf covers EOut eRefuse)
open Rcic.Declarative (Expr Level MemberClass CheckedMember ResolvedEnv
  emptyEnv extendEnv lift exprLevelsBounded EnvWf EnvWfT
  natEnvU natEnvUWfT pinDefEnvU pinDefEnvU_fresh pinDefEnvUWfT
  toothEnvU tooth_EG007T_untyped_body)
open Rcic.Machine (admitState inferSortAcceptedB checkAcceptedB
  EG010T_axiom_accepted EG010T_definition_accepted
  EG010T_theorem_accepted EG010T_opaque_accepted
  pinRunInferSort1 pinRunCheckSort0 pinRunInferNat
  machPropId machPropIdPf pinRunCheckPropId pinRunCheckPropIdPf
  tooth_EG010T_badDef_refused)
open Rcic.ExprSubstTask (LevelWire ExprWire)
open Rcic.Judgment (JudgmentDecision)
open Rcic.GraphAdmitted

/-! ## §1 the arm is env-blind (congruence over the real `acceptedCheck`) -/

/-- The typed-judgment arm reads the store only through the scan at
    `typed_judgment_ref`. -/
theorem typedJudgmentOk_congr {store store' : List StoreEntry} {sb jb : String}
    (ht : storeScan store' (partAt jb "typed_judgment_ref") =
      storeScan store (partAt jb "typed_judgment_ref")) :
    typedJudgmentOk store' sb jb = typedJudgmentOk store sb jb := by
  simp only [typedJudgmentOk, ht]

/-- ENV-BLINDNESS of the CG-014 arm: two stores that agree on the judgment
    record's scan, on the assumptions `refBound`, on the typed-judgment scan,
    and on the env `refBound` (found / no collision / nonempty — NOT the
    bytes) get the same verdict. The admitted environment's content never
    enters `acceptedCheck`. -/
theorem acceptedCheck_env_congr {store store' : List StoreEntry} {sb jref : String}
    (hj : storeScan store' jref = storeScan store jref)
    (he : refBound store' (partAt (storeScan store jref).bytes "admitted_env_ref")
        "[rcic_graph_admitted_env_unbound]" =
      refBound store (partAt (storeScan store jref).bytes "admitted_env_ref")
        "[rcic_graph_admitted_env_unbound]")
    (ha : refBound store' (partAt (storeScan store jref).bytes "assumptions_ref")
        "[rcic_graph_admitted_assumptions_unbound]" =
      refBound store (partAt (storeScan store jref).bytes "assumptions_ref")
        "[rcic_graph_admitted_assumptions_unbound]")
    (ht : storeScan store' (partAt (storeScan store jref).bytes "typed_judgment_ref") =
      storeScan store (partAt (storeScan store jref).bytes "typed_judgment_ref")) :
    acceptedCheck store' sb jref = acceptedCheck store sb jref := by
  have htj := typedJudgmentOk_congr (sb := sb) ht
  simp only [acceptedCheck, hj, he, ha, htj]

/-! ## §2 a concrete store family: every nonempty env image is accepted -/

/-- The judgment record: env `e`, assumptions `a`, coverage `exact`,
    subject bundle `g`, typed judgment `t` (canonical, the five ruled keys). -/
def jBytes : String :=
  "admitted_env_ref:e|assumptions_ref:a|coverage_grade:exact|subject_bundle_ref:g|typed_judgment_ref:t"

/-- The typed-judgment object: the two ruled keys, naming `e` and `g`. -/
def tBytes : String := "env_ref:e|subject_bundle_ref:g"

/-- The statement bytes the arm reads (`closed_graph_bundle_ref` = `g`). -/
def stmtBytes : String :=
  "closed_graph_bundle_ref:g|epoch:0|institutional_basis_refs:i|sequence:0"

/-- The store: judgment, assumptions, typed judgment, and the env image `b`
    at ref `e` — `b` is the ONLY varying entry. -/
def blindStore (b : String) : List StoreEntry :=
  [⟨"j", jBytes⟩, ⟨"a", "x:y"⟩, ⟨"t", tBytes⟩, ⟨"e", b⟩]

set_option maxRecDepth 8000 in
unseal String.splitOnAux in
theorem jBytes_env : partAt jBytes "admitted_env_ref" = "e" := by decide
set_option maxRecDepth 8000 in
unseal String.splitOnAux in
theorem jBytes_assumptions : partAt jBytes "assumptions_ref" = "a" := by decide
set_option maxRecDepth 8000 in
unseal String.splitOnAux in
theorem jBytes_typed : partAt jBytes "typed_judgment_ref" = "t" := by decide

theorem blind_scan_j (b : String) :
    storeScan (blindStore b) "j" = ⟨true, jBytes, false⟩ := by
  simp [storeScan, blindStore]

theorem blind_scan_a (b : String) :
    storeScan (blindStore b) "a" = ⟨true, "x:y", false⟩ := by
  simp [storeScan, blindStore]

theorem blind_scan_t (b : String) :
    storeScan (blindStore b) "t" = ⟨true, tBytes, false⟩ := by
  simp [storeScan, blindStore]

/-- The admitted env ref resolves to EXACTLY the image `b`. -/
theorem blind_env_scan (b : String) :
    storeScan (blindStore b) (partAt jBytes "admitted_env_ref") = ⟨true, b, false⟩ := by
  rw [jBytes_env]; simp [storeScan, blindStore]

/-- A sub-check record with `ok = 1` and empty code IS `codeOk`. -/
theorem codeOut_eq_ok {c : CodeOut} (h1 : c.ok = 1) (h2 : c.code = "") : c = codeOk := by
  cases c; simp_all [codeOk]

set_option maxRecDepth 8000 in
unseal String.splitOnAux in
theorem blind_accepts_ref_ok : (acceptedCheck (blindStore "x:y") stmtBytes "j").ok = 1 := by
  decide

set_option maxRecDepth 8000 in
unseal String.splitOnAux in
theorem blind_accepts_ref_code : (acceptedCheck (blindStore "x:y") stmtBytes "j").code = "" := by
  decide

/-- The reference instance: the arm accepts at env image `x:y` (by evaluation). -/
theorem blind_accepts_ref : acceptedCheck (blindStore "x:y") stmtBytes "j" = codeOk :=
  codeOut_eq_ok blind_accepts_ref_ok blind_accepts_ref_code

/-- The CG-014 arm accepts `blindStore b` for EVERY nonempty env image `b`. -/
theorem blind_accepts (b : String) (hb : b ≠ "") :
    acceptedCheck (blindStore b) stmtBytes "j" = codeOk := by
  rw [← blind_accepts_ref]
  apply acceptedCheck_env_congr
  · rw [blind_scan_j, blind_scan_j]
  · rw [blind_scan_j, jBytes_env]
    simp [refBound, storeScan, blindStore, hb]
  · rw [blind_scan_j, jBytes_assumptions]
    simp [refBound, blind_scan_a]
  · rw [blind_scan_j, jBytes_typed, blind_scan_t, blind_scan_t]

/-- Two distinct env images, both accepted by the arm (non-vacuity of
    `blind_accepts`'s family). -/
theorem pin_blind_accepts_two_images :
    acceptedCheck (blindStore "x:y") stmtBytes "j" = codeOk ∧
    acceptedCheck (blindStore "tooth") stmtBytes "j" = codeOk ∧
    ("x:y" : String) ≠ "tooth" :=
  ⟨blind_accepts_ref, blind_accepts "tooth" (by decide), by decide⟩

/-! ## §3 CG-014 over the arm is refuted for faithful decoders -/

/-- A decoder that reads the env image off the resolved bytes alone — the
    shape every 04 §9 env-image codec has (`envAt` = decode ∘ resolve). -/
def ByteFaithful (O : GraphAdmitObjects) (dec : String → Option ResolvedEnv) : Prop :=
  ∀ store r, O.envAt store r = dec (storeScan store r).bytes

/-- CG-014 stated over the REAL arm: every accepting run of `acceptedCheck`
    yields the typed judgment over the decoded admitted environment. -/
def CG014Arm (O : GraphAdmitObjects) : Prop :=
  ∀ (store : List StoreEntry) (sb jref : String),
    (acceptedCheck store sb jref).ok = 1 →
      TypedJudgmentBound O store (judgmentOfBytes (storeScan store jref).bytes)

theorem judgmentOfBytes_jBytes_env :
    (judgmentOfBytes jBytes).admitted_env_ref = "e" := jBytes_env

/-- REFUTATION over the real arm: whenever a byte-faithful decoder sends some
    nonempty image `b` to an environment with no `EnvWfT`, the arm ACCEPTS
    `blindStore b` and the typed judgment does NOT hold there. -/
theorem cg014_arm_refuted (O : GraphAdmitObjects) (dec : String → Option ResolvedEnv)
    (hO : ByteFaithful O dec) {b : String} (hb : b ≠ "") {E₀ : ResolvedEnv}
    (hdec : dec b = some E₀) (hill : EnvWfT E₀ → False) :
    acceptedCheck (blindStore b) stmtBytes "j" = codeOk ∧
      ¬ TypedJudgmentBound O (blindStore b) (judgmentOfBytes jBytes) := by
  refine ⟨blind_accepts b hb, ?_⟩
  rintro ⟨E, hE, wf, _⟩
  rw [hO, judgmentOfBytes_jBytes_env, ← jBytes_env, blind_env_scan] at hE
  rw [hdec] at hE
  cases hE
  exact hill wf

/-- CG-014 over the arm FORCES the decoder to send every nonempty byte string
    to a well-formed environment — no partial or faithful env-image codec
    satisfies this, so CG-014 needs a typing stage (W2) over a codec (W1). -/
theorem cg014_arm_forces_total_wf (O : GraphAdmitObjects) (dec : String → Option ResolvedEnv)
    (hO : ByteFaithful O dec) (hcg : CG014Arm O) {b : String} (hb : b ≠ "") :
    ∃ E, dec b = some E ∧ Nonempty (EnvWfT E) := by
  have hacc := hcg (blindStore b) stmtBytes "j" (by rw [blind_accepts b hb]; rfl)
  rw [blind_scan_j] at hacc
  obtain ⟨E, hE, wf, _⟩ := hacc
  rw [hO, judgmentOfBytes_jBytes_env, ← jBytes_env, blind_env_scan] at hE
  exact ⟨E, hE, ⟨wf⟩⟩

/-! ## §4 inhabitants: the refutation fires at the sealed ill-typed `toothEnvU` -/

/-- A decoder representing exactly the sealed ill-typed environment
    `toothEnvU` (EG-007T tooth) at image `tooth`. -/
def toothDec (b : String) : Option ResolvedEnv :=
  if b = "tooth" then some toothEnvU else none

/-- The decode seam over `toothDec`; no typed-judgment decoder is needed for
    the refutation (`judgmentAt` returns `none`). -/
def toothObjects : GraphAdmitObjects where
  envAt store r := toothDec (storeScan store r).bytes
  judgmentAt _ _ _ := none

theorem toothObjects_faithful : ByteFaithful toothObjects toothDec := fun _ _ => rfl

/-- PIN: the refutation instantiated — the arm accepts `blindStore "tooth"`,
    whose env image decodes to `toothEnvU`, yet no typed judgment exists. -/
theorem pin_cg014_arm_refuted_tooth :
    acceptedCheck (blindStore "tooth") stmtBytes "j" = codeOk ∧
      ¬ TypedJudgmentBound toothObjects (blindStore "tooth") (judgmentOfBytes jBytes) :=
  cg014_arm_refuted toothObjects toothDec toothObjects_faithful (by decide)
    (by simp [toothDec]) tooth_EG007T_untyped_body

/-- PIN: hence CG-014 over the arm FAILS for `toothObjects`. -/
theorem pin_cg014_arm_fails_tooth : ¬ CG014Arm toothObjects := by
  intro hcg
  obtain ⟨E, hE, ⟨wf⟩⟩ :=
    cg014_arm_forces_total_wf toothObjects toothDec toothObjects_faithful hcg
      (b := "tooth") (by decide)
  simp [toothDec] at hE
  subst hE
  exact tooth_EG007T_untyped_body wf

/-! ## §5 Slice 2: executable singleton typing stage over the real `typedRun` -/

/-- `o.isNone = true` gives `o = none`. -/
theorem isNone_eq_none {α : Type} {o : Option α} (h : o.isNone = true) : o = none := by
  cases o with
  | none => rfl
  | some _ => cases h

/-- One singleton declaration step (04 §6): the four non-group member classes
    (`axiomM`, `definitionM`, `theoremM`, `opaqueM`) together with the machine
    step budgets at which `typedRun` checks their type and body. -/
inductive SingletonDecl where
  | axiomD (r : Nat) (k : Nat) (A : Expr Nat)
  | definitionD (r : Nat) (k k' : Nat) (A v : Expr Nat)
  | theoremD (r : Nat) (k k' : Nat) (A p : Expr Nat)
  | opaqueD (r : Nat) (k k' : Nat) (A v : Expr Nat)
  deriving DecidableEq

/-- Extend `E` by one singleton declaration. -/
def applySingleton (E : ResolvedEnv) : SingletonDecl → ResolvedEnv
  | .axiomD r _ A => extendEnv E r ⟨.axiomM, 0, A, none⟩
  | .definitionD r _ _ A v => extendEnv E r ⟨.definitionM, 0, A, some v⟩
  | .theoremD r _ _ A p => extendEnv E r ⟨.theoremM, 0, A, some p⟩
  | .opaqueD r _ _ A v => extendEnv E r ⟨.opaqueM, 0, A, some v⟩

/-- Extend `E` left-to-right across a telescope of singleton declarations. -/
def applySingletons (E : ResolvedEnv) : List SingletonDecl → ResolvedEnv
  | [] => E
  | d :: ds => applySingletons (applySingleton E d) ds

/-- Executable Bool typing check for one singleton declaration over the REAL
    typed machine (`typedRun` via `inferSortAcceptedB` and `checkAcceptedB`
    from `RcicEGTypedAccept`), plus freshness, closedness (`lift 0 1 X = X`),
    and level bounds (`exprLevelsBounded 0 X`). -/
def admitSingletonB (E : ResolvedEnv) : SingletonDecl → Bool
  | .axiomD r k A =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      decide (lift 0 1 A = A) &&
      exprLevelsBounded 0 A
  | .definitionD r k k' A v =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      checkAcceptedB E k' v A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 v = v) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 v
  | .theoremD r k k' A p =>
      (E.members r).isNone &&
      checkAcceptedB E k A (.sort .zero) &&
      checkAcceptedB E k' p A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 p = p) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 p
  | .opaqueD r k k' A v =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      checkAcceptedB E k' v A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 v = v) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 v

/-- Executable Bool typing stage for a telescope of singleton declarations,
    threading the extended environment left-to-right. -/
def admitSingletonsB : ResolvedEnv → List SingletonDecl → Bool
  | _, [] => true
  | E, d :: ds => admitSingletonB E d && admitSingletonsB (applySingleton E d) ds

/-- Soundness of one singleton step: `admitSingletonB E d = true` constructs
    the `EnvWfT` successor from the machine runs (`EG010T_*_accepted`). -/
def admitSingletonWfT {E : ResolvedEnv} (hE : EnvWfT E) :
    (d : SingletonDecl) → admitSingletonB E d = true →
    EnvWfT (applySingleton E d)
  | .axiomD r k A, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_axiom_accepted hE (isNone_eq_none h.1.1.1) h.1.1.2
        (of_decide_eq_true h.1.2) h.2
  | .definitionD r k k' A v, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_definition_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2
  | .theoremD r k k' A p, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_theorem_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2
  | .opaqueD r k k' A v, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_opaque_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2

/-- Soundness of the telescope typing stage: `admitSingletonsB E ds = true`
    constructs the composite `EnvWfT (applySingletons E ds)`. -/
def admitSingletonsWfT {E : ResolvedEnv} (hE : EnvWfT E) :
    (ds : List SingletonDecl) → admitSingletonsB E ds = true →
    EnvWfT (applySingletons E ds)
  | [], _ => hE
  | d :: ds, h => by
      simp only [admitSingletonsB, Bool.and_eq_true] at h
      exact admitSingletonsWfT (admitSingletonWfT hE d h.1) ds h.2

/-- Prop-level soundness of the singleton typing stage. -/
theorem admitSingletons_sound {E : ResolvedEnv} (hE : EnvWfT E)
    {ds : List SingletonDecl} (h : admitSingletonsB E ds = true) :
    Nonempty (EnvWfT (applySingletons E ds)) :=
  ⟨admitSingletonsWfT hE ds h⟩

/-! ## §6 CG-014 discharged for the singleton fragment (`acceptedCheckTyped`, `graphAdmittedTyped`) -/

/-- The decoded `ResolvedEnv` produced from raw env-image bytes by a
    singleton-telescope decoder `dec`. -/
def envImageOf (E₀ : ResolvedEnv) (dec : String → Option (List SingletonDecl))
    (bytes : String) : Option ResolvedEnv :=
  (dec bytes).map (applySingletons E₀)

/-- The typing stage over the resolved env ref: decode the bytes to a
    singleton telescope `ds` and run `admitSingletonsB E₀ ds`. -/
def envStageOk (E₀ : ResolvedEnv) (dec : String → Option (List SingletonDecl))
    (store : List StoreEntry) (envRef : String) : Bool :=
  match dec (storeScan store envRef).bytes with
  | some ds => admitSingletonsB E₀ ds
  | none => false

theorem envStageOk_iff {E₀ : ResolvedEnv} {dec : String → Option (List SingletonDecl)}
    {store : List StoreEntry} {envRef : String} :
    envStageOk E₀ dec store envRef = true ↔
      ∃ ds, dec (storeScan store envRef).bytes = some ds ∧
        admitSingletonsB E₀ ds = true := by
  unfold envStageOk
  cases h : dec (storeScan store envRef).bytes with
  | none => simp
  | some ds => simp

/-- The CG-014 arm equipped with the singleton typing stage (W2 discharged
    for the singleton fragment): runs the byte-level `acceptedCheck` and then
    requires `envStageOk` on `admitted_env_ref`, refusing at
    `[rcic_cg014_judgment]` (`judgment_untyped`) if decoding or typing fails. -/
def acceptedCheckTyped (E₀ : ResolvedEnv) (dec : String → Option (List SingletonDecl))
    (store : List StoreEntry) (sb jref : String) : CodeOut :=
  let res := acceptedCheck store sb jref
  if res.ok ≠ 1 then res
  else
    let jb := (storeScan store jref).bytes
    if envStageOk E₀ dec store (partAt jb "admitted_env_ref") then codeOk
    else codeRefuse "[rcic_cg014_judgment]"

/-- The full triple validator equipped with the singleton typing stage on its
    `accepted` decision arm. -/
def graphAdmittedTyped (E₀ : ResolvedEnv) (dec : String → Option (List SingletonDecl))
    (store : List StoreEntry) (statementRef receiptRef occurrenceRef occurrence : String)
    (fuel : Int) : EOut :=
  let res := graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel
  if res.ok ≠ 1 then res
  else
    let rb := (storeScan store receiptRef).bytes
    let d := decisionCheck store (partAt rb "decision")
    if d.ctor = "accepted" then
      let sb := (storeScan store statementRef).bytes
      let ja := acceptedCheckTyped E₀ dec store sb d.value
      if ja.ok = 1 then ⟨1, occurrence, ""⟩ else eRefuse ja.code
    else res

/-- Exact characterization of `acceptedCheckTyped` acceptance: both the
    byte-level `acceptedCheck` and the R-CIC singleton typing stage `envStageOk`
    succeeded. -/
theorem acceptedCheckTyped_ok_iff {E₀ : ResolvedEnv}
    {dec : String → Option (List SingletonDecl)}
    {store : List StoreEntry} {sb jref : String} :
    (acceptedCheckTyped E₀ dec store sb jref).ok = 1 ↔
      (acceptedCheck store sb jref).ok = 1 ∧
      envStageOk E₀ dec store (partAt (storeScan store jref).bytes "admitted_env_ref") = true := by
  unfold acceptedCheckTyped
  dsimp only
  by_cases h1 : (acceptedCheck store sb jref).ok = 1
  · rw [if_neg (by omega)]
    cases he : envStageOk E₀ dec store (partAt (storeScan store jref).bytes "admitted_env_ref")
    · simp [h1, codeRefuse]
    · simp [h1, codeOk]
  · rw [if_pos h1]
    simp [h1]

/-- CG-014 for `acceptedCheckTyped` (no pass-through `EnvWfT` premise):
    every accepting run yields all 12 `AcceptedBindingFacts` AND a decoded
    `ResolvedEnv` carrying a machine-checked `EnvWfT`. -/
theorem cg014_acceptedCheckTyped_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    (dec : String → Option (List SingletonDecl))
    {store : List StoreEntry} {sb jref : String}
    (hok : (acceptedCheckTyped E₀ dec store sb jref).ok = 1) :
    (∃ jB tB, AcceptedBindingFacts store sb jref jB tB) ∧
    ∃ E, envImageOf E₀ dec
      (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some E ∧ Nonempty (EnvWfT E) := by
  rw [acceptedCheckTyped_ok_iff] at hok
  obtain ⟨hbyte, hstage⟩ := hok
  rw [envStageOk_iff] at hstage
  obtain ⟨ds, hds, hadm⟩ := hstage
  refine ⟨acceptedCheck_sound hbyte, applySingletons E₀ ds, ?_,
    admitSingletons_sound wf₀ hadm⟩
  simp [envImageOf, hds]

/-- CG-014 for the full triple validator `graphAdmittedTyped` (exact statement
    shape of `S0_CG014.md` §3): an `ok` triple whose receipt decision spells
    `accepted` yields both `AcceptedBindingFacts` and a machine-checked
    `EnvWfT` over the decoded `admitted_env_ref`. -/
theorem cg014_graphAdmittedTyped_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    (dec : String → Option (List SingletonDecl))
    {store : List StoreEntry}
    {statementRef receiptRef occurrenceRef occurrence : String} {fuel : Int}
    {jref : String}
    (hok : graphAdmittedTyped E₀ dec store statementRef receiptRef
      occurrenceRef occurrence fuel = (⟨1, occurrence, ""⟩ : EOut))
    (hdec : decisionCheck store
      (partAt (storeScan store receiptRef).bytes "decision") =
      ⟨1, "", "accepted", jref⟩) :
    (∃ jB tB, AcceptedBindingFacts store (storeScan store statementRef).bytes jref jB tB) ∧
    ∃ E, envImageOf E₀ dec
      (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some E ∧ Nonempty (EnvWfT E) := by
  unfold graphAdmittedTyped at hok
  dsimp only at hok
  obtain ⟨h0, hok⟩ | ⟨_, hok⟩ := ite_eq_of hok
  · have h1 : (graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel).ok = 1 := by
      rw [hok]
    exact absurd h1 h0
  · rw [hdec] at hok
    dsimp only at hok
    rw [if_pos rfl] at hok
    obtain ⟨hja, _⟩ | ⟨_, hok⟩ := ite_eq_of hok
    · exact cg014_acceptedCheckTyped_sound wf₀ dec hja
    · exact absurd hok eRefuse_ne_ok

/-- TOOTH: when the byte-level `acceptedCheck` passes but `envStageOk` fails
    (either the env bytes fail to decode or `typedRun` refuses a declaration),
    `acceptedCheckTyped` refuses at `[rcic_cg014_judgment]`. -/
theorem tooth_acceptedCheckTyped_untyped {E₀ : ResolvedEnv}
    (dec : String → Option (List SingletonDecl))
    {store : List StoreEntry} {sb jref : String}
    (hbyte : (acceptedCheck store sb jref).ok = 1)
    (hbad : envStageOk E₀ dec store
      (partAt (storeScan store jref).bytes "admitted_env_ref") = false) :
    acceptedCheckTyped E₀ dec store sb jref = codeRefuse "[rcic_cg014_judgment]" := by
  unfold acceptedCheckTyped
  dsimp only
  rw [if_neg (by omega), hbad]
  rfl

/-! ## §7 Inhabitants and refusal teeth for the singleton typing stage -/

/-- A 3-declaration singleton telescope over `emptyEnv`:
    - ref 0: `def d0 : Sort 1 := Sort 0`
    - ref 1: `opaque o1 : Sort 1 := Sort 0`
    - ref 2: `theorem t2 : (Π X : Prop, X → X) := λ X x, x` -/
def goodEmptyTele : List SingletonDecl :=
  [ .definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)
  , .opaqueD 1 1 1 (.sort (.succ .zero)) (.sort .zero)
  , .theoremD 2 1 1 machPropId machPropIdPf ]

/-- PIN: `typedRun` accepts all three declarations in `goodEmptyTele` starting
    from `emptyEnv` (by evaluation). -/
theorem pin_admitSingletonsB_goodEmptyTele :
    admitSingletonsB emptyEnv goodEmptyTele = true := rfl

/-- PIN: the composite `EnvWfT` constructed by `admitSingletonsWfT` for
    `goodEmptyTele` over `emptyEnv`. -/
def pin_goodEmptyTele_wfT : EnvWfT (applySingletons emptyEnv goodEmptyTele) :=
  admitSingletonsWfT .empty goodEmptyTele pin_admitSingletonsB_goodEmptyTele

/-- A 4-declaration singleton telescope over `natEnvU` exercising ALL FOUR
    singleton member classes (`axiomM`, `definitionM`, `theoremM`, `opaqueM`)
    at fresh refs 4, 5, 6, 7. -/
def goodNatTele : List SingletonDecl :=
  [ .axiomD 4 1 (.const 0 [])
  , .definitionD 5 1 1 (.sort (.succ .zero)) (.sort .zero)
  , .theoremD 6 1 1 machPropId machPropIdPf
  , .opaqueD 7 1 1 (.sort (.succ .zero)) (.sort .zero) ]

/-- PIN: `typedRun` accepts all four singleton classes in `goodNatTele`
    starting from `natEnvU` (by evaluation). -/
theorem pin_admitSingletonsB_goodNatTele :
    admitSingletonsB natEnvU goodNatTele = true := rfl

/-- PIN: the composite `EnvWfT` constructed by `admitSingletonsWfT` for
    `goodNatTele` over `natEnvU`. -/
def pin_goodNatTele_wfT : EnvWfT (applySingletons natEnvU goodNatTele) :=
  admitSingletonsWfT natEnvUWfT goodNatTele pin_admitSingletonsB_goodNatTele

/-- The ill-typed singleton declaration `def bad : Prop := Type` (admitted by
    legacy `EnvWf`, refused by `typedRun`). -/
def badDefTele : List SingletonDecl :=
  [ .definitionD 0 1 1 (.sort .zero) (.sort (.succ .zero)) ]

/-- TOOTH: `applySingletons emptyEnv badDefTele` is admitted by the legacy
    `EnvWf` (`Ann.envWf_badDef 0`), yet `admitSingletonsB` REFUSES `badDefTele`
    by evaluation of `typedRun`. -/
theorem tooth_admitSingletonsB_badDef_refused :
    Nonempty (EnvWf (applySingletons emptyEnv badDefTele) 0) ∧
    admitSingletonsB emptyEnv badDefTele = false :=
  ⟨⟨Rcic.Declarative.Ann.envWf_badDef 0⟩, rfl⟩

/-- Concrete singleton-telescope decoder mapping `"good"` to `goodEmptyTele`
    and `"bad"` to `badDefTele`. -/
def teleDec (b : String) : Option (List SingletonDecl) :=
  if b = "good" then some goodEmptyTele
  else if b = "bad" then some badDefTele
  else none

/-- PIN: `acceptedCheckTyped` accepts `blindStore "good"`. -/
theorem pin_acceptedCheckTyped_good_accepts :
    acceptedCheckTyped emptyEnv teleDec (blindStore "good") stmtBytes "j" = codeOk := by
  have hbyte := blind_accepts "good" (by decide)
  unfold acceptedCheckTyped
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide)]
  rw [blind_scan_j, jBytes_env]
  have hstage : envStageOk emptyEnv teleDec (blindStore "good") "e" = true := by
    unfold envStageOk
    rw [ ← jBytes_env, blind_env_scan]
    change (match teleDec "good" with | some ds => admitSingletonsB emptyEnv ds | none => false) = true
    exact pin_admitSingletonsB_goodEmptyTele
  rw [hstage]
  rfl

/-- PIN: `cg014_acceptedCheckTyped_sound` instantiated at `blindStore "good"` —
    produces both `AcceptedBindingFacts` and a machine-checked `EnvWfT` over
    the decoded environment without any pass-through `EnvWfT` hypothesis. -/
theorem pin_cg014_good_inhabited :
    (∃ jB tB, AcceptedBindingFacts (blindStore "good") stmtBytes "j" jB tB) ∧
    ∃ E, envImageOf emptyEnv teleDec
      (storeScan (blindStore "good")
        (partAt (storeScan (blindStore "good") "j").bytes "admitted_env_ref")).bytes =
        some E ∧ Nonempty (EnvWfT E) :=
  cg014_acceptedCheckTyped_sound .empty teleDec
    (by rw [pin_acceptedCheckTyped_good_accepts]; rfl)

/-- TOOTH (mutant separation): on the SAME store `blindStore "bad"` (whose
    env ref resolves to `badDefTele`, `def bad : Prop := Type`), the landed
    env-blind `acceptedCheck` WRONGLY ACCEPTS (`= codeOk`), whereas
    `acceptedCheckTyped` REFUSES with `[rcic_cg014_judgment]`. -/
theorem tooth_acceptedCheck_vs_typed_badDef :
    acceptedCheck (blindStore "bad") stmtBytes "j" = codeOk ∧
    acceptedCheckTyped emptyEnv teleDec (blindStore "bad") stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" := by
  have hbyte := blind_accepts "bad" (by decide)
  refine ⟨hbyte, ?_⟩
  apply tooth_acceptedCheckTyped_untyped teleDec (by rw [hbyte]; rfl)
  rw [blind_scan_j, jBytes_env]
  unfold envStageOk
  rw [← jBytes_env, blind_env_scan]
  change (match teleDec "bad" with | some ds => admitSingletonsB emptyEnv ds | none => false) = false
  exact tooth_admitSingletonsB_badDef_refused.2

/-! ## §8 Reusing `ExprWire` (`RcicExprSubstTask.lean:128`) and Annex 26.2a `unbuilt_stage` for groups -/

/-- Parse a non-empty canonical decimal string (`'0'..'9'`, no leading zero
    unless `"0"`) to `Nat`, or `none`. -/
def parseNatRef? (s : String) : Option Nat :=
  let cs := s.toList
  if !cs.isEmpty && cs.all (fun c => '0' ≤ c && c ≤ '9') &&
      (cs = ['0'] || cs.headD ' ' ≠ '0') then
    some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- Decode `LevelWire` (`RcicExprSubstTask.lean:116`) to `Level`, refusing
    negative universe-parameter indices (`param i` with `i < 0`). -/
def decodeLevelWire? : LevelWire → Option Level
  | .zero => some .zero
  | .succ a => (decodeLevelWire? a).map .succ
  | .max a b =>
      match decodeLevelWire? a, decodeLevelWire? b with
      | some a', some b' => some (.max a' b')
      | _, _ => none
  | .imax a b =>
      match decodeLevelWire? a, decodeLevelWire? b with
      | some a', some b' => some (.imax a' b')
      | _, _ => none
  | .param i => if i < 0 then none else some (.param i.toNat)

/-- Decode a list of `LevelWire`s to `List Level`. -/
def decodeLevelWires? : List LevelWire → Option (List Level)
  | [] => some []
  | l :: ls =>
      match decodeLevelWire? l, decodeLevelWires? ls with
      | some l', some ls' => some (l' :: ls')
      | _, _ => none

/-- Decode `ExprWire` (`RcicExprSubstTask.lean:128`, the wire used at the F1.1
    boundary) to `Expr Nat`, refusing negative `bvar` indices, unknown
    constructor tags (`.other k`), negative level parameters, and non-decimal
    `const` references. No new expression wire object is minted. -/
def decodeExprWire? : ExprWire → Option (Expr Nat)
  | .bvar i => if i < 0 then none else some (.bvar i.toNat)
  | .sort l => (decodeLevelWire? l).map .sort
  | .const r ls =>
      match parseNatRef? r, decodeLevelWires? ls with
      | some refN, some ls' => some (.const refN ls')
      | _, _ => none
  | .app f x =>
      match decodeExprWire? f, decodeExprWire? x with
      | some f', some x' => some (.app f' x')
      | _, _ => none
  | .lam a b =>
      match decodeExprWire? a, decodeExprWire? b with
      | some a', some b' => some (.lam a' b')
      | _, _ => none
  | .pi a b =>
      match decodeExprWire? a, decodeExprWire? b with
      | some a', some b' => some (.pi a' b')
      | _, _ => none
  | .letE a v b =>
      match decodeExprWire? a, decodeExprWire? v, decodeExprWire? b with
      | some a', some v', some b' => some (.letE a' v' b')
      | _, _, _ => none
  | .other _ => none

/-- Environment entry at the `ExprWire` layer: either one of the four 04 §6
    singleton declaration classes carrying `ExprWire` payloads, or an
    inductive group (which surfaces `integrityResidue .unbuilt_stage` per
    Annex 26.2a, never acceptance). -/
inductive EnvWireEntry : Type
  | axiomW (ref : Nat) (univs : Nat) (ty : ExprWire)
  | definitionW (ref : Nat) (univs : Nat) (fuel : Nat) (ty body : ExprWire)
  | theoremW (ref : Nat) (univs : Nat) (fuel : Nat) (ty proof : ExprWire)
  | opaqueW (ref : Nat) (univs : Nat) (fuel : Nat) (ty body : ExprWire)
  | inductiveGroupW (groupRef : String)
  deriving DecidableEq

def isInductiveGroupW : EnvWireEntry → Bool
  | .inductiveGroupW _ => true
  | _ => false

def hasInductiveGroupW (es : List EnvWireEntry) : Bool :=
  es.any isInductiveGroupW

/-- Decode one `EnvWireEntry` in the singleton fragment to `SingletonDecl`. -/
def decodeSingletonWire? : EnvWireEntry → Option SingletonDecl
  | .axiomW ref univs ty =>
      (decodeExprWire? ty).map (.axiomD ref univs)
  | .definitionW ref univs fuel ty body =>
      match decodeExprWire? ty, decodeExprWire? body with
      | some ty', some body' => some (.definitionD ref univs fuel ty' body')
      | _, _ => none
  | .theoremW ref univs fuel ty proof =>
      match decodeExprWire? ty, decodeExprWire? proof with
      | some ty', some proof' => some (.theoremD ref univs fuel ty' proof')
      | _, _ => none
  | .opaqueW ref univs fuel ty body =>
      match decodeExprWire? ty, decodeExprWire? body with
      | some ty', some body' => some (.opaqueD ref univs fuel ty' body')
      | _, _ => none
  | .inductiveGroupW _ => none

def decodeSingletonWires? : List EnvWireEntry → Option (List SingletonDecl)
  | [] => some []
  | e :: es =>
      match decodeSingletonWire? e, decodeSingletonWires? es with
      | some d, some ds => some (d :: ds)
      | _, _ => none

/-- Three-way outcome of the S2+S3 environment stage:
    - `.accepted ds`: no inductive groups, every `ExprWire` decoded, and
      `admitSingletonsB E₀ ds = true`;
    - `.refusedJudgmentUntyped`: byte/wire decode failed or `admitSingletonsB`
      refused a singleton declaration (`GraphRefusal.judgment_untyped` /
      `[rcic_cg014_judgment]`);
    - `.integrityUnbuiltStage`: an inductive group is present, surfacing
      `GraphIntegrity.unbuilt_stage` per Annex 26.2a, never acceptance. -/
inductive EnvStageResult : Type
  | accepted (ds : List SingletonDecl)
  | refusedJudgmentUntyped
  | integrityUnbuiltStage
  deriving DecidableEq

/-! ## §9 S3 Byte Spelling — `ScmWire` (`Rcic.Scm.Val`) ⇄ `ExprWire` Bridge & `canonical_group_bytes` Stage (Annex 26.36) -/

/-- Encode a `LevelWire` (`RcicExprSubstTask.lean:116`) as the raw `Rcic.Scm.Val`
    record matching the SCM kernel's level kind-records (`scm/rcic/level_eval.scm:3–37`):
    - `.zero` (`kind = 0`)       ↦ `.r [.i 0]`
    - `.succ a` (`kind = 1`)     ↦ `.r [.i 1, levelWireToVal a]`
    - `.max a b` (`kind = 2`)    ↦ `.r [.i 2, levelWireToVal a, levelWireToVal b]`
    - `.imax a b` (`kind = 3`)   ↦ `.r [.i 3, levelWireToVal a, levelWireToVal b]`
    - `.param i` (`kind = 4`)    ↦ `.r [.i 4, .i i]` -/
def levelWireToVal : LevelWire → Rcic.Scm.Val
  | .zero => .r [.i 0]
  | .succ a => .r [.i 1, levelWireToVal a]
  | .max a b => .r [.i 2, levelWireToVal a, levelWireToVal b]
  | .imax a b => .r [.i 3, levelWireToVal a, levelWireToVal b]
  | .param i => .r [.i 4, .i i]

/-- Decode a raw `Rcic.Scm.Val` record back to `LevelWire`. -/
def valToLevelWire? : Rcic.Scm.Val → Option LevelWire
  | .r [.i 0] => some .zero
  | .r [.i 1, a] => (valToLevelWire? a).map .succ
  | .r [.i 2, a, b] =>
      match valToLevelWire? a, valToLevelWire? b with
      | some a', some b' => some (.max a' b')
      | _, _ => none
  | .r [.i 3, a, b] =>
      match valToLevelWire? a, valToLevelWire? b with
      | some a', some b' => some (.imax a' b')
      | _, _ => none
  | .r [.i 4, .i i] => some (.param i)
  | _ => none

/-- Decode a list of `Rcic.Scm.Val` records to `List LevelWire`. -/
def valsToLevelWires? : List Rcic.Scm.Val → Option (List LevelWire)
  | [] => some []
  | v :: vs =>
      match valToLevelWire? v, valsToLevelWires? vs with
      | some l, some ls => some (l :: ls)
      | _, _ => none

/-- Round-trip law for `LevelWire`: `valToLevelWire? (levelWireToVal l) = some l`. -/
theorem valToLevelWire_levelWireToVal :
    (l : LevelWire) → valToLevelWire? (levelWireToVal l) = some l
  | .zero => rfl
  | .succ a => by
      simp only [levelWireToVal, valToLevelWire?, valToLevelWire_levelWireToVal a, Option.map]
  | .max a b => by
      simp only [levelWireToVal, valToLevelWire?,
        valToLevelWire_levelWireToVal a, valToLevelWire_levelWireToVal b]
  | .imax a b => by
      simp only [levelWireToVal, valToLevelWire?,
        valToLevelWire_levelWireToVal a, valToLevelWire_levelWireToVal b]
  | .param _ => rfl

/-- Round-trip law for `List LevelWire`:
    `valsToLevelWires? (ls.map levelWireToVal) = some ls`. -/
theorem valsToLevelWires_map :
    (ls : List LevelWire) → valsToLevelWires? (ls.map levelWireToVal) = some ls
  | [] => rfl
  | l :: ls => by
      simp only [List.map, valsToLevelWires?,
        valToLevelWire_levelWireToVal l, valsToLevelWires_map ls]

/-- Postcondition of `valToLevelWire? v = some l` for single-step inversion. -/
def valToLevelWirePost (v : Rcic.Scm.Val) : LevelWire → Prop
  | .zero => v = .r [.i 0]
  | .succ a' => ∃ a, v = .r [.i 1, a] ∧ valToLevelWire? a = some a'
  | .max a' b' => ∃ a b, v = .r [.i 2, a, b] ∧ valToLevelWire? a = some a' ∧ valToLevelWire? b = some b'
  | .imax a' b' => ∃ a b, v = .r [.i 3, a, b] ∧ valToLevelWire? a = some a' ∧ valToLevelWire? b = some b'
  | .param i => v = .r [.i 4, .i i]

/-- Helper for `levelWireToVal_of_valToLevelWire`: single-step inversion of
    `valToLevelWire?`. -/
theorem valToLevelWire_eq_some_iff (v : Rcic.Scm.Val) (l : LevelWire) :
    valToLevelWire? v = some l → valToLevelWirePost v l := by
  unfold valToLevelWire?
  split
  · intro h; injection h with h; subst h; rfl
  · rename_i a
    intro h
    cases ha : valToLevelWire? a with
    | none => simp [ha, Option.map] at h
    | some a' =>
        simp [ha, Option.map] at h
        subst h
        exact ⟨a, rfl, ha⟩
  · rename_i a b
    intro h
    cases ha : valToLevelWire? a <;> cases hb : valToLevelWire? b <;>
      simp [ha, hb] at h
    subst h
    exact ⟨a, b, rfl, ha, hb⟩
  · rename_i a b
    intro h
    cases ha : valToLevelWire? a <;> cases hb : valToLevelWire? b <;>
      simp [ha, hb] at h
    subst h
    exact ⟨a, b, rfl, ha, hb⟩
  · intro h; injection h with h; subst h; rfl
  · intro h; cases h

/-- Converse inversion for `LevelWire`: any `v` accepted by `valToLevelWire?`
    is the exact `levelWireToVal` image of the decoded level. -/
theorem levelWireToVal_of_valToLevelWire :
    (l : LevelWire) → ∀ {v : Rcic.Scm.Val},
      valToLevelWire? v = some l → levelWireToVal l = v
  | .zero, _, h => (valToLevelWire_eq_some_iff _ .zero h).symm
  | .succ a', _, h => by
      obtain ⟨a, rfl, ha⟩ := valToLevelWire_eq_some_iff _ (.succ a') h
      simp only [levelWireToVal, levelWireToVal_of_valToLevelWire a' ha]
  | .max a' b', _, h => by
      obtain ⟨a, b, rfl, ha, hb⟩ := valToLevelWire_eq_some_iff _ (.max a' b') h
      simp only [levelWireToVal,
        levelWireToVal_of_valToLevelWire a' ha,
        levelWireToVal_of_valToLevelWire b' hb]
  | .imax a' b', _, h => by
      obtain ⟨a, b, rfl, ha, hb⟩ := valToLevelWire_eq_some_iff _ (.imax a' b') h
      simp only [levelWireToVal,
        levelWireToVal_of_valToLevelWire a' ha,
        levelWireToVal_of_valToLevelWire b' hb]
  | .param i, _, h => (valToLevelWire_eq_some_iff _ (.param i) h).symm

/-- Converse inversion for `List LevelWire`: any `vs` accepted by
    `valsToLevelWires?` is `ls.map levelWireToVal`. -/
theorem map_levelWireToVal_of_valsToLevelWires :
    ∀ {vs : List Rcic.Scm.Val} {ls : List LevelWire},
      valsToLevelWires? vs = some ls → ls.map levelWireToVal = vs
  | [], _, h => by
      injection h with hls; subst hls; rfl
  | v :: vs, _, h => by
      simp only [valsToLevelWires?] at h
      cases hv : valToLevelWire? v <;> cases hvs : valsToLevelWires? vs <;>
        simp [hv, hvs] at h
      subst h
      simp only [List.map,
        levelWireToVal_of_valToLevelWire _ hv,
        map_levelWireToVal_of_valsToLevelWires hvs]

/-- The supported `ExprWire` fragment (`apps/rcic-expr-subst/APP.md:36–45`,
    kinds `0..6`, excluding the `.other k` unknown-constructor slot). -/
def SupportedExprWire : ExprWire → Bool
  | .bvar _ => true
  | .sort _ => true
  | .const _ _ => true
  | .app f x => SupportedExprWire f && SupportedExprWire x
  | .lam a b => SupportedExprWire a && SupportedExprWire b
  | .pi a b => SupportedExprWire a && SupportedExprWire b
  | .letE a v b => SupportedExprWire a && SupportedExprWire v && SupportedExprWire b
  | .other _ => false

/-- Encode an `ExprWire` (`RcicExprSubstTask.lean:128`) as the raw `Rcic.Scm.Val`
    record matching the SCM kernel's expression kind-records
    (`scm/rcic/expr_lift.scm:3–95`, `apps/rcic-expr-subst/APP.md:36–45`):
    - `.bvar i` (`kind = 0`)       ↦ `.r [.i 0, .i i]`
    - `.sort l` (`kind = 1`)       ↦ `.r [.i 1, levelWireToVal l]`
    - `.const r ls` (`kind = 2`)   ↦ `.r [.i 2, .s r, .l (ls.map levelWireToVal)]`
    - `.app f x` (`kind = 3`)      ↦ `.r [.i 3, exprWireToVal f, exprWireToVal x]`
    - `.lam a b` (`kind = 4`)      ↦ `.r [.i 4, exprWireToVal a, exprWireToVal b]`
    - `.pi a b` (`kind = 5`)       ↦ `.r [.i 5, exprWireToVal a, exprWireToVal b]`
    - `.letE a v b` (`kind = 6`)   ↦ `.r [.i 6, exprWireToVal a, exprWireToVal v, exprWireToVal b]`
    - `.other k`                   ↦ `.r [.i k]` -/
def exprWireToVal : ExprWire → Rcic.Scm.Val
  | .bvar i => .r [.i 0, .i i]
  | .sort l => .r [.i 1, levelWireToVal l]
  | .const r ls => .r [.i 2, .s r, .l (ls.map levelWireToVal)]
  | .app f x => .r [.i 3, exprWireToVal f, exprWireToVal x]
  | .lam a b => .r [.i 4, exprWireToVal a, exprWireToVal b]
  | .pi a b => .r [.i 5, exprWireToVal a, exprWireToVal b]
  | .letE a v b => .r [.i 6, exprWireToVal a, exprWireToVal v, exprWireToVal b]
  | .other k => .r [.i k]

/-- Decode a raw `Rcic.Scm.Val` record back to `ExprWire` on the supported
    kinds `0..6`. -/
def valToExprWire? : Rcic.Scm.Val → Option ExprWire
  | .r [.i 0, .i i] => some (.bvar i)
  | .r [.i 1, l] => (valToLevelWire? l).map .sort
  | .r [.i 2, .s r, .l ls] => (valsToLevelWires? ls).map (.const r)
  | .r [.i 3, f, x] =>
      match valToExprWire? f, valToExprWire? x with
      | some f', some x' => some (.app f' x')
      | _, _ => none
  | .r [.i 4, a, b] =>
      match valToExprWire? a, valToExprWire? b with
      | some a', some b' => some (.lam a' b')
      | _, _ => none
  | .r [.i 5, a, b] =>
      match valToExprWire? a, valToExprWire? b with
      | some a', some b' => some (.pi a' b')
      | _, _ => none
  | .r [.i 6, a, v, b] =>
      match valToExprWire? a, valToExprWire? v, valToExprWire? b with
      | some a', some v', some b' => some (.letE a' v' b')
      | _, _, _ => none
  | _ => none

/-- Round-trip theorem on the supported `ExprWire` fragment:
    `SupportedExprWire e = true → valToExprWire? (exprWireToVal e) = some e`. -/
theorem valToExprWire_exprWireToVal :
    (e : ExprWire) → SupportedExprWire e = true →
      valToExprWire? (exprWireToVal e) = some e
  | .bvar _, _ => rfl
  | .sort l, _ => by
      simp only [exprWireToVal, valToExprWire?, valToLevelWire_levelWireToVal l, Option.map]
  | .const _ ls, _ => by
      simp only [exprWireToVal, valToExprWire?, valsToLevelWires_map ls, Option.map]
  | .app f x, h => by
      have ⟨hf, hx⟩ := Bool.and_eq_true_iff.mp h
      simp only [exprWireToVal, valToExprWire?,
        valToExprWire_exprWireToVal f hf, valToExprWire_exprWireToVal x hx]
  | .lam a b, h => by
      have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
      simp only [exprWireToVal, valToExprWire?,
        valToExprWire_exprWireToVal a ha, valToExprWire_exprWireToVal b hb]
  | .pi a b, h => by
      have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
      simp only [exprWireToVal, valToExprWire?,
        valToExprWire_exprWireToVal a ha, valToExprWire_exprWireToVal b hb]
  | .letE a v b, h => by
      have ⟨hav, hb⟩ := Bool.and_eq_true_iff.mp h
      have ⟨ha, hv⟩ := Bool.and_eq_true_iff.mp hav
      simp only [exprWireToVal, valToExprWire?,
        valToExprWire_exprWireToVal a ha, valToExprWire_exprWireToVal v hv,
        valToExprWire_exprWireToVal b hb]
  | .other _, h => by cases h

/-- Postcondition of `valToExprWire? v = some e` for single-step inversion. -/
def valToExprWirePost (v : Rcic.Scm.Val) : ExprWire → Prop
  | .bvar i => v = .r [.i 0, .i i]
  | .sort l' => ∃ l, v = .r [.i 1, l] ∧ valToLevelWire? l = some l'
  | .const r ls' => ∃ ls, v = .r [.i 2, .s r, .l ls] ∧ valsToLevelWires? ls = some ls'
  | .app f' x' => ∃ f x, v = .r [.i 3, f, x] ∧ valToExprWire? f = some f' ∧ valToExprWire? x = some x'
  | .lam a' b' => ∃ a b, v = .r [.i 4, a, b] ∧ valToExprWire? a = some a' ∧ valToExprWire? b = some b'
  | .pi a' b' => ∃ a b, v = .r [.i 5, a, b] ∧ valToExprWire? a = some a' ∧ valToExprWire? b = some b'
  | .letE a' v0' b' =>
      ∃ a v0 b, v = .r [.i 6, a, v0, b] ∧
        valToExprWire? a = some a' ∧ valToExprWire? v0 = some v0' ∧ valToExprWire? b = some b'
  | .other _ => False

/-- Helper for `exprWireToVal_of_valToExprWire`: single-step inversion of
    `valToExprWire?`. -/
theorem valToExprWire_eq_some_iff (v : Rcic.Scm.Val) (e : ExprWire) :
    valToExprWire? v = some e → valToExprWirePost v e := by
  unfold valToExprWire?
  split
  · intro h; injection h with h; subst h; rfl
  · rename_i l
    intro h
    cases hl : valToLevelWire? l with
    | none => simp [hl, Option.map] at h
    | some l' =>
        simp [hl, Option.map] at h
        subst h
        exact ⟨l, rfl, hl⟩
  · rename_i r ls
    intro h
    cases hls : valsToLevelWires? ls with
    | none => simp [hls, Option.map] at h
    | some ls' =>
        simp [hls, Option.map] at h
        subst h
        exact ⟨ls, rfl, hls⟩
  · rename_i f x
    intro h
    cases hf : valToExprWire? f <;> cases hx : valToExprWire? x <;>
      simp [hf, hx] at h
    subst h
    exact ⟨f, x, rfl, hf, hx⟩
  · rename_i a b
    intro h
    cases ha : valToExprWire? a <;> cases hb : valToExprWire? b <;>
      simp [ha, hb] at h
    subst h
    exact ⟨a, b, rfl, ha, hb⟩
  · rename_i a b
    intro h
    cases ha : valToExprWire? a <;> cases hb : valToExprWire? b <;>
      simp [ha, hb] at h
    subst h
    exact ⟨a, b, rfl, ha, hb⟩
  · rename_i a v0 b
    intro h
    cases ha : valToExprWire? a <;> cases hv0 : valToExprWire? v0 <;>
      cases hb : valToExprWire? b <;> simp [ha, hv0, hb] at h
    subst h
    exact ⟨a, v0, b, rfl, ha, hv0, hb⟩
  · intro h; cases h

/-- Converse inversion for `ExprWire`: any `v` accepted by `valToExprWire?`
    is the exact `exprWireToVal` image of a supported `ExprWire`. -/
theorem exprWireToVal_of_valToExprWire :
    (e : ExprWire) → ∀ {v : Rcic.Scm.Val},
      valToExprWire? v = some e →
      exprWireToVal e = v ∧ SupportedExprWire e = true
  | .bvar i, _, h => ⟨(valToExprWire_eq_some_iff _ (.bvar i) h).symm, rfl⟩
  | .sort l', _, h => by
      obtain ⟨l, rfl, hl⟩ := valToExprWire_eq_some_iff _ (.sort l') h
      exact ⟨by simp only [exprWireToVal, levelWireToVal_of_valToLevelWire l' hl], rfl⟩
  | .const r ls', _, h => by
      obtain ⟨ls, rfl, hls⟩ := valToExprWire_eq_some_iff _ (.const r ls') h
      exact ⟨by simp only [exprWireToVal, map_levelWireToVal_of_valsToLevelWires hls], rfl⟩
  | .app f' x', _, h => by
      obtain ⟨f, x, rfl, hf, hx⟩ := valToExprWire_eq_some_iff _ (.app f' x') h
      have ⟨hf1, hf2⟩ := exprWireToVal_of_valToExprWire f' hf
      have ⟨hx1, hx2⟩ := exprWireToVal_of_valToExprWire x' hx
      exact ⟨by simp only [exprWireToVal, hf1, hx1],
             by simp only [SupportedExprWire, hf2, hx2]; rfl⟩
  | .lam a' b', _, h => by
      obtain ⟨a, b, rfl, ha, hb⟩ := valToExprWire_eq_some_iff _ (.lam a' b') h
      have ⟨ha1, ha2⟩ := exprWireToVal_of_valToExprWire a' ha
      have ⟨hb1, hb2⟩ := exprWireToVal_of_valToExprWire b' hb
      exact ⟨by simp only [exprWireToVal, ha1, hb1],
             by simp only [SupportedExprWire, ha2, hb2]; rfl⟩
  | .pi a' b', _, h => by
      obtain ⟨a, b, rfl, ha, hb⟩ := valToExprWire_eq_some_iff _ (.pi a' b') h
      have ⟨ha1, ha2⟩ := exprWireToVal_of_valToExprWire a' ha
      have ⟨hb1, hb2⟩ := exprWireToVal_of_valToExprWire b' hb
      exact ⟨by simp only [exprWireToVal, ha1, hb1],
             by simp only [SupportedExprWire, ha2, hb2]; rfl⟩
  | .letE a' v0' b', _, h => by
      obtain ⟨a, v0, b, rfl, ha, hv0, hb⟩ := valToExprWire_eq_some_iff _ (.letE a' v0' b') h
      have ⟨ha1, ha2⟩ := exprWireToVal_of_valToExprWire a' ha
      have ⟨hv1, hv2⟩ := exprWireToVal_of_valToExprWire v0' hv0
      have ⟨hb1, hb2⟩ := exprWireToVal_of_valToExprWire b' hb
      exact ⟨by simp only [exprWireToVal, ha1, hv1, hb1],
             by simp only [SupportedExprWire, ha2, hv2, hb2]; rfl⟩
  | .other k, _, h => (valToExprWire_eq_some_iff _ (.other k) h).elim

/-- Canonical `ScmWire` encoding of an `ExprWire` via `Rcic.Scm.Wire.encVal`. -/
def encExprWireScm (e : ExprWire) : String :=
  Rcic.Scm.Wire.encVal (exprWireToVal e)

/-- Canonical `ScmWire` expression decode: `Rcic.Scm.BoundTV.valueBytesAt`
    (`dec0 1 bytes.length bytes` with full-input and exact `encVal` re-encode
    checks) followed by `valToExprWire?`. -/
def decExprWireScm? (bytes : String) : Option ExprWire :=
  match Rcic.Scm.BoundTV.valueBytesAt bytes with
  | some v => valToExprWire? v
  | none => none

/-- Any value `v` within `ScmWire`'s `dqV` and `valGas` bounds decodes from its
    canonical encoding `encVal v` via `Rcic.Scm.BoundTV.valueBytesAt`. -/
theorem valueBytesAt_encVal (v : Rcic.Scm.Val)
    (hdq : Rcic.Scm.Wire.dqV v)
    (hg : Rcic.Scm.Wire.valGas v ≤
      Rcic.Scm.Wire.gasFor (↑(Rcic.Scm.Wire.encVal v).length) (Rcic.Scm.Wire.encVal v).length - 1) :
    Rcic.Scm.BoundTV.valueBytesAt (Rcic.Scm.Wire.encVal v) = some v := by
  have hf : (Rcic.Scm.Wire.valFuel v : Int) ≤ (Rcic.Scm.Wire.encVal v).length := by
    have := Rcic.Scm.Wire.valFuel_le_encLen v
    change (Rcic.Scm.Wire.valFuel v : Int) ≤ (Rcic.Scm.Wire.encVal v).toList.length
    omega
  unfold Rcic.Scm.BoundTV.valueBytesAt Rcic.Scm.BoundTV.dec0
  dsimp only
  rw [show ((Rcic.Scm.Wire.encVal v).toList.toArray).size = (Rcic.Scm.Wire.encVal v).length from
        by simp only [Array.size_toArray]; rfl]
  rw [show Rcic.Scm.Wire.gasFor (↑(Rcic.Scm.Wire.encVal v).length) (Rcic.Scm.Wire.encVal v).length =
        (Rcic.Scm.Wire.gasFor (↑(Rcic.Scm.Wire.encVal v).length) (Rcic.Scm.Wire.encVal v).length - 1) + 1 from by
        unfold Rcic.Scm.Wire.gasFor; omega]
  rw [Rcic.Scm.Wire.dec_one ((Rcic.Scm.Wire.encVal v).toList.toArray) _ _ 0 _ (.val v)
        (Rcic.Scm.Wire.decVal_enc v ((Rcic.Scm.Wire.encVal v).toList.toArray) _
          (↑(Rcic.Scm.Wire.encVal v).length) 0 [] (by simp) hg hf hdq)
        (by omega : ¬ (↑(Rcic.Scm.Wire.encVal v).length : Int) < 0)]
  dsimp only
  rw [if_pos ⟨by rw [Nat.zero_add]; rfl, rfl⟩]
  rfl

/-- Any value accepted by `Rcic.Scm.BoundTV.valueBytesAt` re-encodes to `bytes`
    via `Rcic.Scm.Wire.encVal`. -/
theorem valueBytesAt_reencodes {bytes : String} {v : Rcic.Scm.Val}
    (h : Rcic.Scm.BoundTV.valueBytesAt bytes = some v) :
    Rcic.Scm.Wire.encVal v = bytes := by
  unfold Rcic.Scm.BoundTV.valueBytesAt at h
  split at h
  · rename_i it p _
    by_cases hcond : p = bytes.length ∧ Rcic.Scm.Wire.encVal (Rcic.Scm.Wire.asVal it) = bytes
    · rw [if_pos hcond] at h
      injection h with hv
      subst hv
      exact hcond.2
    · rw [if_neg hcond] at h
      cases h
  · cases h

/-- Byte-level round-trip theorem for `encExprWireScm` / `decExprWireScm?`:
    every supported `ExprWire` within the `ScmWire` `dqV`/`valGas` bounds
    round-trips through `Rcic.Scm.Wire.encVal` and `Rcic.Scm.Wire.dec`. -/
theorem decExprWireScm_encExprWireScm (e : ExprWire)
    (hsup : SupportedExprWire e = true)
    (hdq : Rcic.Scm.Wire.dqV (exprWireToVal e))
    (hg : Rcic.Scm.Wire.valGas (exprWireToVal e) ≤
      Rcic.Scm.Wire.gasFor (↑(encExprWireScm e).length) (encExprWireScm e).length - 1) :
    decExprWireScm? (encExprWireScm e) = some e := by
  unfold decExprWireScm? encExprWireScm
  rw [valueBytesAt_encVal (exprWireToVal e) hdq hg]
  exact valToExprWire_exprWireToVal e hsup

/-- Byte-level canonicality theorem: any `bytes` accepted by `decExprWireScm?`
    is the exact canonical `encExprWireScm` encoding of a supported `ExprWire`. -/
theorem decExprWireScm_canonical {bytes : String} {e : ExprWire}
    (h : decExprWireScm? bytes = some e) :
    encExprWireScm e = bytes ∧ SupportedExprWire e = true := by
  unfold decExprWireScm? at h
  cases hv : Rcic.Scm.BoundTV.valueBytesAt bytes with
  | none => simp [hv] at h
  | some v =>
      simp [hv] at h
      have ⟨he1, he2⟩ := exprWireToVal_of_valToExprWire e h
      have hre := valueBytesAt_reencodes hv
      exact ⟨by unfold encExprWireScm; rw [he1, hre], he2⟩

/-- `apps/rcic-group-codec/APP.md:33–37` checked-group wire keys in strictly
    ascending order (`a|b|d|i|m|o|p|r|t|y`). -/
def checkedGroupKeys : List String :=
  ["a", "b", "d", "i", "m", "o", "p", "r", "t", "y"]

/-- Decode one checked-group wire (`canonical_group_bytes`) into `EnvWireEntry`
    using `decExprWireScm?` on `y`, `d`, and `o`, and `fuel` as the `typedRun`
    step budget. Any group with `i ≠ "-"` or `r ≠ "-"` decodes to
    `.inductiveGroupW mStr`, which surfaces `integrityResidue .unbuilt_stage`
    per Annex 26.2a. On the monomorphic singleton fragment (`i = "-"`,
    `r = "-"`), member universe arity `a` and base universe arity `b` must both
    be `0` (`parseNatRef? aStr = some 0` and `parseNatRef? bStr = some 0`,
    matching `applySingleton`'s `CheckedMember.arity = 0` and `EnvWfT`'s
    level-context `0` constructors); nonzero `a` or `b` is refused (`= none`),
    never silently erased to `0`. -/
def decodeCheckedGroupBytes? (fuel : Nat) (gbytes : String) : Option EnvWireEntry :=
  if !canonBytesOk gbytes || keysOf gbytes != checkedGroupKeys then none
  else
    let aStr := partAt gbytes "a"
    let bStr := partAt gbytes "b"
    let dStr := partAt gbytes "d"
    let iStr := partAt gbytes "i"
    let mStr := partAt gbytes "m"
    let oStr := partAt gbytes "o"
    let pStr := partAt gbytes "p"
    let rStr := partAt gbytes "r"
    let tStr := partAt gbytes "t"
    let yStr := partAt gbytes "y"
    if pStr.isEmpty || (parseNatRef? aStr).isNone || (parseNatRef? bStr).isNone then none
    else if iStr != "-" || rStr != "-" then
      some (.inductiveGroupW mStr)
    else if parseNatRef? aStr != some 0 || parseNatRef? bStr != some 0 then
      none
    else
      match parseNatRef? mStr, decExprWireScm? yStr with
      | some refN, some tyW =>
          if tStr == "rigid" && dStr == "-" && oStr == "-" then
            some (.axiomW refN fuel tyW)
          else if tStr == "delta" && dStr != "-" && oStr == "-" then
            (decExprWireScm? dStr).map (.definitionW refN fuel fuel tyW)
          else if tStr == "rigid" && dStr != "-" && oStr == "-" then
            (decExprWireScm? dStr).map (.theoremW refN fuel fuel tyW)
          else if tStr == "rigid" && dStr == "-" && oStr != "-" then
            (decExprWireScm? oStr).map (.opaqueW refN fuel fuel tyW)
          else none
      | _, _ => none

def decodeGroupBytesList? (fuel : Nat) : List String → Option (List EnvWireEntry)
  | [] => some []
  | g :: gs =>
      match decodeCheckedGroupBytes? fuel g, decodeGroupBytesList? fuel gs with
      | some e, some es => some (e :: es)
      | _, _ => none

/-- One `{ref, bytes}` entry of an `EnvironmentImage`
    (`docs/rcic/04_ENVIRONMENT_AND_GROUPS.md` §9, `apps/rcic-env-image/APP.md:20–30`). -/
structure EnvImageEntry where
  ref : String
  bytes : String
  deriving DecidableEq

/-- Exact Lean transcription of the entry fold in `scm/rcic/env_image_join.scm:3–8`:
    each entry appends `ref ++ "~" ++ bytes ++ "~"`. -/
def envImageJoinEntries : List EnvImageEntry → String
  | [] => ""
  | e :: es => e.ref ++ "~" ++ e.bytes ++ "~" ++ envImageJoinEntries es

/-- Exact Lean transcription of `scm/rcic/env_image_join.scm:1–8`:
    `profile ++ "~" ++ schema ++ "~" ++ envImageJoinEntries entries`. -/
def envImageJoin (profile schema : String) (entries : List EnvImageEntry) : String :=
  profile ++ "~" ++ schema ++ "~" ++ envImageJoinEntries entries

/-- Extract the `canonical_group_bytes` payloads from the `ref ~ bytes ~ ...`
    tail of an `env_image_join` preimage (`scm/rcic/env_image_join.scm:1–8`),
    requiring non-empty `ref` (`≤ 2048` codepoints per `env_image_bound.scm`)
    and non-empty `bytes` (`env_image_shaped.scm`) on each entry pair, and a
    single trailing `""` segment after the final `"~"`. -/
def extractEnvImageEntryBytes? : List String → Option (List String)
  | [""] => some []
  | r :: g :: rest =>
      if r.isEmpty || decide (2048 < r.length) || g.isEmpty then none
      else
        match extractEnvImageEntryBytes? rest with
        | some gs => some (g :: gs)
        | none => none
  | _ => none

/-- Parse the `profile ~ schema ~ ref ~ bytes ~` envelope produced by
    `scm/rcic/env_image_join.scm:1–8` into its list of
    `canonical_group_bytes` payloads, including the empty genesis image. Frames with empty `profile`, empty
    `schema`, missing `ref`, missing trailing `"~"`, or bare group bytes
    without an `env_image_join` frame are refused (`= none`). -/
def parseEnvImageEnvelope? (ebytes : String) : Option (List String) :=
  match ebytes.splitOn "~" with
  | profile :: schema :: rest =>
      if profile.isEmpty || schema.isEmpty then none
      else
        extractEnvImageEntryBytes? rest
  | _ => none

/- Envelope parsing checks framing only. Profile/schema compatibility, entry-ref
    ordering/uniqueness and content-hash validation remain separate obligations. -/
/-- Decode an `EnvironmentImage` byte sequence (`profile ~ schema ~ ref ~ bytes ~`
    produced by `scm/rcic/env_image_join.scm:1–8`, `apps/rcic-env-image/APP.md:23–26`)
    into `List EnvWireEntry`. Frame segments (`profile`, `schema`, `ref`) and
    the trailing empty segment are parsed by `parseEnvImageEnvelope?` and never
    treated as groups; a bare group presented without an `env_image_join`
    envelope is refused (`= none`). -/
def decodeEnvImageBytes? (fuel : Nat) (ebytes : String) : Option (List EnvWireEntry) :=
  match parseEnvImageEnvelope? ebytes with
  | some gs => decodeGroupBytesList? fuel gs
  | none => none

/-- Single-entry reduction lemma for `parseEnvImageEnvelope?` on
    `envImageJoin profile schema [⟨ref, gbytes⟩]`. -/
private theorem parseEnvImageEnvelope_single (profile schema ref gbytes : String)
    (hp : (profile.isEmpty || schema.isEmpty) = false)
    (hrg : (ref.isEmpty || decide (2048 < ref.length) || gbytes.isEmpty) = false)
    (hsplit : (envImageJoin profile schema [⟨ref, gbytes⟩]).splitOn "~" =
      [profile, schema, ref, gbytes, ""]) :
    parseEnvImageEnvelope? (envImageJoin profile schema [⟨ref, gbytes⟩]) =
      some [gbytes] := by
  simp only [parseEnvImageEnvelope?, hsplit, hp, extractEnvImageEntryBytes?, hrg,
    Bool.false_eq_true, ↓reduceIte]

/-- Single-entry reduction lemma for `decodeEnvImageBytes?` on
    `envImageJoin profile schema [⟨ref, gbytes⟩]`. -/
private theorem decodeEnvImageBytes_single (fuel : Nat) (profile schema ref gbytes : String)
    (hp : (profile.isEmpty || schema.isEmpty) = false)
    (hrg : (ref.isEmpty || decide (2048 < ref.length) || gbytes.isEmpty) = false)
    (hsplit : (envImageJoin profile schema [⟨ref, gbytes⟩]).splitOn "~" =
      [profile, schema, ref, gbytes, ""]) :
    decodeEnvImageBytes? fuel (envImageJoin profile schema [⟨ref, gbytes⟩]) =
      (decodeCheckedGroupBytes? fuel gbytes).map (· :: []) := by
  unfold decodeEnvImageBytes?
  rw [parseEnvImageEnvelope_single profile schema ref gbytes hp hrg hsplit]
  dsimp only [decodeGroupBytesList?]
  cases decodeCheckedGroupBytes? fuel gbytes <;> rfl

private theorem tooth_bare_group_refused_by_envelope_of_split (fuel : Nat) (gbytes : String)
    (hsplit : gbytes.splitOn "~" = [gbytes]) :
    parseEnvImageEnvelope? gbytes = none ∧
    decodeEnvImageBytes? fuel gbytes = none := by
  have hp : parseEnvImageEnvelope? gbytes = none := by
    unfold parseEnvImageEnvelope?
    rw [hsplit]
  refine ⟨hp, ?_⟩
  unfold decodeEnvImageBytes?
  rw [hp]

/-- Helper unfolding `decodeCheckedGroupBytes?` on a canonical non-group wire. -/
theorem decodeCheckedGroupBytes_of_parts (fuel : Nat) (gbytes : String)
    (hc : (!canonBytesOk gbytes || keysOf gbytes != checkedGroupKeys) = false)
    (hp : ((partAt gbytes "p").isEmpty || (parseNatRef? (partAt gbytes "a")).isNone ||
           (parseNatRef? (partAt gbytes "b")).isNone) = false)
    (hir : (partAt gbytes "i" != "-" || partAt gbytes "r" != "-") = false) :
    decodeCheckedGroupBytes? fuel gbytes =
      if parseNatRef? (partAt gbytes "a") != some 0 ||
         parseNatRef? (partAt gbytes "b") != some 0 then none
      else
        match parseNatRef? (partAt gbytes "m"), decExprWireScm? (partAt gbytes "y") with
        | some refN, some tyW =>
            if partAt gbytes "t" == "rigid" && partAt gbytes "d" == "-" && partAt gbytes "o" == "-" then
              some (.axiomW refN fuel tyW)
            else if partAt gbytes "t" == "delta" && partAt gbytes "d" != "-" && partAt gbytes "o" == "-" then
              (decExprWireScm? (partAt gbytes "d")).map (.definitionW refN fuel fuel tyW)
            else if partAt gbytes "t" == "rigid" && partAt gbytes "d" != "-" && partAt gbytes "o" == "-" then
              (decExprWireScm? (partAt gbytes "d")).map (.theoremW refN fuel fuel tyW)
            else if partAt gbytes "t" == "rigid" && partAt gbytes "d" == "-" && partAt gbytes "o" != "-" then
              (decExprWireScm? (partAt gbytes "o")).map (.opaqueW refN fuel fuel tyW)
            else none
        | _, _ => none := by
  unfold decodeCheckedGroupBytes?
  dsimp only
  rw [hc, if_neg Bool.false_ne_true, hp, if_neg Bool.false_ne_true, hir, if_neg Bool.false_ne_true]

/-- Every singleton entry decoded by `decodeCheckedGroupBytes?` has member
    universe arity `a = 0` and base universe arity `b = 0` (`04` §5, §6),
    matching the monomorphic `CheckedMember.arity = 0` constructed by
    `applySingleton` (`RcicTypedEnv.lean:163–184`). -/
theorem decodeCheckedGroupBytes_singleton_arity_zero
    {fuel : Nat} {gbytes : String} {e : EnvWireEntry}
    (hdec : decodeCheckedGroupBytes? fuel gbytes = some e)
    (hng : isInductiveGroupW e = false) :
    parseNatRef? (partAt gbytes "a") = some 0 ∧
    parseNatRef? (partAt gbytes "b") = some 0 := by
  unfold decodeCheckedGroupBytes? at hdec
  dsimp only at hdec
  split at hdec
  · cases hdec
  · split at hdec
    · cases hdec
    · split at hdec
      · injection hdec with he; subst he; cases hng
      · by_cases hab : (parseNatRef? (partAt gbytes "a") != some 0 ||
                        parseNatRef? (partAt gbytes "b") != some 0) = true
        · rw [if_pos hab] at hdec; cases hdec
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hab
          exact hab

private theorem tooth_decodeCheckedGroupBytes_nonzero_arity_refused_of_parts
    (fuel : Nat) (gbytes : String)
    (hc : (!canonBytesOk gbytes || keysOf gbytes != checkedGroupKeys) = false)
    (hp : ((partAt gbytes "p").isEmpty || (parseNatRef? (partAt gbytes "a")).isNone ||
           (parseNatRef? (partAt gbytes "b")).isNone) = false)
    (hir : (partAt gbytes "i" != "-" || partAt gbytes "r" != "-") = false)
    (hab : (parseNatRef? (partAt gbytes "a") != some 0 ||
            parseNatRef? (partAt gbytes "b") != some 0) = true) :
    decodeCheckedGroupBytes? fuel gbytes = none := by
  rw [decodeCheckedGroupBytes_of_parts fuel gbytes hc hp hir, hab, if_pos rfl]


/-- Entry-list stage on a decoded `List EnvWireEntry`: surfaces
    `.integrityUnbuiltStage` on inductive groups (Annex 26.2a), and otherwise
    decodes singletons via `decodeSingletonWires?` and runs `admitSingletonsB`. -/
def runEnvEntriesStage (E₀ : ResolvedEnv) (es : List EnvWireEntry) :
    EnvStageResult :=
  if hasInductiveGroupW es then .integrityUnbuiltStage
  else
    match decodeSingletonWires? es with
    | none => .refusedJudgmentUntyped
    | some ds =>
        if admitSingletonsB E₀ ds then .accepted ds
        else .refusedJudgmentUntyped

/-- Parameter-free S2+S3 environment stage over real `canonical_group_bytes`
    (`decodeEnvImageBytes?` via `ScmWire` + `ExprWire` + `admitSingletonsB`),
    with no caller-supplied decoder parameter. -/
def runEnvWireStage (E₀ : ResolvedEnv) (fuel : Nat) (bytes : String) :
    EnvStageResult :=
  match decodeEnvImageBytes? fuel bytes with
  | none => .refusedJudgmentUntyped
  | some es => runEnvEntriesStage E₀ es

/-- Mapping `EnvStageResult` onto the 26.2 `GraphAdmitDecision` sum:
    inductive groups map to `.integrityResidue .unbuilt_stage` (26.2a),
    never `.accepted`. -/
def envWireStageDecision (j : AdmittedGraphJudgment) :
    EnvStageResult → GraphAdmitDecision
  | .accepted _ => .accepted j
  | .refusedJudgmentUntyped => .refused .judgment_untyped
  | .integrityUnbuiltStage => .integrityResidue .unbuilt_stage

/-- The CG-014 arm over real `canonical_group_bytes` (`decodeEnvImageBytes?` +
    `ExprWire` + `admitSingletonsB`, no external decoder parameter), refusing
    `[rcic_cg014_judgment]` on decode/typing failure and surfacing
    `[rcic_graph_admitted_unbuilt_stage]` on inductive groups (26.2a). -/
def acceptedCheckWire (E₀ : ResolvedEnv) (fuel : Nat)
    (store : List StoreEntry) (sb jref : String) : CodeOut :=
  let res := acceptedCheck store sb jref
  if res.ok ≠ 1 then res
  else
    let jb := (storeScan store jref).bytes
    let eb := (storeScan store (partAt jb "admitted_env_ref")).bytes
    match runEnvWireStage E₀ fuel eb with
    | .accepted _ => codeOk
    | .refusedJudgmentUntyped => codeRefuse "[rcic_cg014_judgment]"
    | .integrityUnbuiltStage => codeRefuse "[rcic_graph_admitted_unbuilt_stage]"

/-- The full triple validator over real `canonical_group_bytes`
    (`decodeEnvImageBytes?` + `ExprWire` + `admitSingletonsB`, no external
    decoder parameter). -/
def graphAdmittedWire (E₀ : ResolvedEnv)
    (store : List StoreEntry)
    (statementRef receiptRef occurrenceRef occurrence : String)
    (fuel : Int) : EOut :=
  let res := graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel
  if res.ok ≠ 1 then res
  else
    let rb := (storeScan store receiptRef).bytes
    let d := decisionCheck store (partAt rb "decision")
    if d.ctor = "accepted" then
      let sb := (storeScan store statementRef).bytes
      let ja := acceptedCheckWire E₀ fuel.toNat store sb d.value
      if ja.ok = 1 then ⟨1, occurrence, ""⟩ else eRefuse ja.code
    else res

/-- Alias of `acceptedCheckWire` naming the `canonical_group_bytes` stage. -/
def acceptedCheckGroupBytes (E₀ : ResolvedEnv) (fuel : Nat)
    (store : List StoreEntry) (sb jref : String) : CodeOut :=
  acceptedCheckWire E₀ fuel store sb jref

/-- Alias of `graphAdmittedWire` naming the `canonical_group_bytes` stage. -/
def graphAdmittedGroupBytes (E₀ : ResolvedEnv) (store : List StoreEntry)
    (statementRef receiptRef occurrenceRef occurrence : String)
    (fuel : Int) : EOut :=
  graphAdmittedWire E₀ store statementRef receiptRef occurrenceRef occurrence fuel

theorem runEnvWireStage_accepted_iff {E₀ : ResolvedEnv}
    {fuel : Nat} {bytes : String} {ds : List SingletonDecl} :
    runEnvWireStage E₀ fuel bytes = .accepted ds ↔
      ∃ es, decodeEnvImageBytes? fuel bytes = some es ∧
        hasInductiveGroupW es = false ∧
        decodeSingletonWires? es = some ds ∧
        admitSingletonsB E₀ ds = true := by
  unfold runEnvWireStage runEnvEntriesStage
  cases hw : decodeEnvImageBytes? fuel bytes with
  | none => simp
  | some es =>
      cases hg : hasInductiveGroupW es
      · dsimp only
        rw [if_neg (by rw [hg]; decide)]
        cases hd : decodeSingletonWires? es with
        | none =>
            constructor
            · intro h; cases h
            · rintro ⟨_, h1, _, h3, _⟩
              injection h1 with h1; subst h1
              rw [hd] at h3; cases h3
        | some ds' =>
            cases ha : admitSingletonsB E₀ ds'
            · dsimp only
              rw [if_neg (by rw [ha]; decide)]
              constructor
              · intro h; cases h
              · rintro ⟨_, h1, _, h3, h4⟩
                injection h1 with h1; subst h1
                rw [hd] at h3; injection h3 with h3; subst h3
                rw [ha] at h4; cases h4
            · dsimp only
              rw [if_pos ha]
              constructor
              · intro h
                injection h with h; subst h
                exact ⟨es, rfl, hg, hd, ha⟩
              · rintro ⟨_, h1, _, h3, _⟩
                injection h1 with h1; subst h1
                rw [hd] at h3; injection h3 with h3; subst h3
                rfl
      · dsimp only
        rw [if_pos hg]
        constructor
        · intro h; cases h
        · rintro ⟨_, h1, h2, _⟩
          injection h1 with h1; subst h1
          rw [hg] at h2; cases h2

theorem acceptedCheckWire_ok_iff {E₀ : ResolvedEnv} {fuel : Nat}
    {store : List StoreEntry} {sb jref : String} :
    (acceptedCheckWire E₀ fuel store sb jref).ok = 1 ↔
      (acceptedCheck store sb jref).ok = 1 ∧
      ∃ ds, runEnvWireStage E₀ fuel
        (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        .accepted ds := by
  unfold acceptedCheckWire
  dsimp only
  by_cases h1 : (acceptedCheck store sb jref).ok = 1
  · rw [if_neg (by omega)]
    cases hr : runEnvWireStage E₀ fuel
      (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes with
    | accepted ds =>
        simp [h1, codeOk]
    | refusedJudgmentUntyped =>
        simp [h1, codeRefuse]
    | integrityUnbuiltStage =>
        simp [h1, codeRefuse]
  · rw [if_pos h1]
    simp [h1]

/-- **CG-014 Soundness over `canonical_group_bytes` (Arm Level, No External Decoder)**:
    If `acceptedCheckWire` accepts, all 12 `AcceptedBindingFacts` hold,
    `admitted_env_ref`'s bytes decode via `decodeEnvImageBytes?` to a group-free
    `ExprWire` entry list `es` and singleton telescope `ds`, and the extended
    environment `applySingletons E₀ ds` is well-formed (`EnvWfT`). -/
theorem cg014_acceptedCheckWire_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    {fuel : Nat} {store : List StoreEntry} {sb jref : String}
    (hok : (acceptedCheckWire E₀ fuel store sb jref).ok = 1) :
    (∃ jB tB, AcceptedBindingFacts store sb jref jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? fuel
        (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons E₀ ds)) := by
  rw [acceptedCheckWire_ok_iff] at hok
  obtain ⟨hbyte, ds, hstage⟩ := hok
  rw [runEnvWireStage_accepted_iff] at hstage
  obtain ⟨es, hw, hg, hd, hadm⟩ := hstage
  exact ⟨acceptedCheck_sound hbyte, es, ds, hw, hg, hd, admitSingletons_sound wf₀ hadm⟩

/-- **CG-014 Soundness over `canonical_group_bytes` (Full Judgment Level, No External Decoder)**:
    If `graphAdmittedWire` accepts on an `"accepted"` receipt decision,
    all 12 `AcceptedBindingFacts` hold and the decoded singleton telescope
    extends `E₀` to a well-formed environment `EnvWfT (applySingletons E₀ ds)`. -/
theorem cg014_graphAdmittedWire_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    {store : List StoreEntry}
    {statementRef receiptRef occurrenceRef occurrence : String} {fuel : Int}
    {jref : String}
    (hok : graphAdmittedWire E₀ store statementRef receiptRef
      occurrenceRef occurrence fuel = (⟨1, occurrence, ""⟩ : EOut))
    (hdec : decisionCheck store
      (partAt (storeScan store receiptRef).bytes "decision") =
      ⟨1, "", "accepted", jref⟩) :
    (∃ jB tB, AcceptedBindingFacts store (storeScan store statementRef).bytes jref jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? fuel.toNat
        (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons E₀ ds)) := by
  unfold graphAdmittedWire at hok
  dsimp only at hok
  obtain ⟨h0, hok⟩ | ⟨_, hok⟩ := ite_eq_of hok
  · have h1 : (graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel).ok = 1 := by
      rw [hok]
    exact absurd h1 h0
  · rw [hdec] at hok
    dsimp only at hok
    rw [if_pos rfl] at hok
    obtain ⟨hja, _⟩ | ⟨_, hok⟩ := ite_eq_of hok
    · exact cg014_acceptedCheckWire_sound wf₀ hja
    · exact absurd hok eRefuse_ne_ok

theorem cg014_acceptedCheckGroupBytes_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    {fuel : Nat} {store : List StoreEntry} {sb jref : String}
    (hok : (acceptedCheckGroupBytes E₀ fuel store sb jref).ok = 1) :
    (∃ jB tB, AcceptedBindingFacts store sb jref jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? fuel
        (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons E₀ ds)) :=
  cg014_acceptedCheckWire_sound wf₀ hok

theorem cg014_graphAdmittedGroupBytes_sound {E₀ : ResolvedEnv} (wf₀ : EnvWfT E₀)
    {store : List StoreEntry}
    {statementRef receiptRef occurrenceRef occurrence : String}
    {fuel : Int} {jref : String}
    (hok : graphAdmittedGroupBytes E₀ store statementRef receiptRef
      occurrenceRef occurrence fuel = (⟨1, occurrence, ""⟩ : EOut))
    (hdec : decisionCheck store (partAt (storeScan store receiptRef).bytes "decision") =
      ⟨1, "", "accepted", jref⟩) :
    (∃ jB tB, AcceptedBindingFacts store (storeScan store statementRef).bytes jref jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? fuel.toNat
        (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons E₀ ds)) :=
  cg014_graphAdmittedWire_sound wf₀ hok hdec

/-- TOOTH (26.2a): any environment wire carrying an inductive group surfaces
    `EnvStageResult.integrityUnbuiltStage` (`JudgmentDecision.integrityResidue .unbuilt_stage`),
    never `.accepted`. -/
theorem tooth_envWireStage_group_unbuilt_stage (E₀ : ResolvedEnv)
    (fuel : Nat) (bytes : String)
    (j : AdmittedGraphJudgment) {es : List EnvWireEntry}
    (hw : decodeEnvImageBytes? fuel bytes = some es)
    (hg : hasInductiveGroupW es = true) :
    runEnvWireStage E₀ fuel bytes = .integrityUnbuiltStage ∧
    envWireStageDecision j (runEnvWireStage E₀ fuel bytes) =
      .integrityResidue .unbuilt_stage := by
  have hr : runEnvWireStage E₀ fuel bytes = .integrityUnbuiltStage := by
    unfold runEnvWireStage runEnvEntriesStage
    rw [hw]
    dsimp only
    rw [hg, if_pos rfl]
  exact ⟨hr, by rw [hr]; rfl⟩

/-- TOOTH (26.2a at the arm): when the decoded environment contains an
    inductive group, `acceptedCheckWire` returns
    `codeRefuse "[rcic_graph_admitted_unbuilt_stage]"`, never `codeOk`. -/
theorem tooth_acceptedCheckWire_group_never_accepts (E₀ : ResolvedEnv)
    (fuel : Nat) {store : List StoreEntry} {sb jref : String}
    {es : List EnvWireEntry}
    (hbyte : (acceptedCheck store sb jref).ok = 1)
    (hw : decodeEnvImageBytes? fuel
      (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
      some es)
    (hg : hasInductiveGroupW es = true) :
    acceptedCheckWire E₀ fuel store sb jref =
      codeRefuse "[rcic_graph_admitted_unbuilt_stage]" := by
  unfold acceptedCheckWire
  dsimp only
  rw [if_neg (by omega)]
  have hr : runEnvWireStage E₀ fuel
      (storeScan store (partAt (storeScan store jref).bytes "admitted_env_ref")).bytes =
      .integrityUnbuiltStage := by
    unfold runEnvWireStage runEnvEntriesStage
    rw [hw]
    dsimp only
    rw [hg, if_pos rfl]
  rw [hr]

/-- All four singleton classes written in `Rcic.ExprSubstTask.ExprWire` over
    `natEnvU` (refs 4, 5, 6, 7). -/
def goodNatWireTele : List EnvWireEntry :=
  [ .axiomW 4 1 (.const "0" [])
  , .definitionW 5 1 1 (.sort (.succ .zero)) (.sort .zero)
  , .theoremW 6 1 1
      (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1)))
      (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0)))
  , .opaqueW 7 1 1 (.sort (.succ .zero)) (.sort .zero) ]

/-- PIN: `runEnvEntriesStage` decodes `goodNatWireTele` via `decodeExprWire?` and
    accepts it through `admitSingletonsB` (`typedRun`), producing `goodNatTele`. -/
theorem pin_runEnvWireStage_goodNat :
    runEnvEntriesStage natEnvU goodNatWireTele =
      .accepted goodNatTele := rfl

/-- The ill-typed singleton `def bad : Prop := Type` written in `ExprWire`. -/
def badDefWireTele : List EnvWireEntry :=
  [ .definitionW 0 1 1 (.sort .zero) (.sort (.succ .zero)) ]

/-- TOOTH: `runEnvEntriesStage` refuses `badDefWireTele` with
    `.refusedJudgmentUntyped` (`[rcic_cg014_judgment]`). -/
theorem tooth_runEnvWireStage_badDef :
    runEnvEntriesStage emptyEnv badDefWireTele =
      .refusedJudgmentUntyped := rfl

/-- An environment wire containing an inductive group entry. -/
def indGroupWireTele : List EnvWireEntry :=
  [ .axiomW 4 1 (.const "0" [])
  , .inductiveGroupW "natGroup" ]

/-- TOOTH: `runEnvEntriesStage` surfaces `.integrityUnbuiltStage` (26.2a) on
    `indGroupWireTele`, never `.accepted`. -/
theorem tooth_runEnvWireStage_indGroup :
    runEnvEntriesStage natEnvU indGroupWireTele =
      .integrityUnbuiltStage := rfl

/-- Helper for Wall C1: no single `CoreTy` can elaborate both an integer
    (`Val.i n`) and a record (`Val.r xs`) under `Rcic.Scm.toCore`. -/
theorem toCore_int_and_rec_impossible (t : Rcic.Scm.CoreTy)
    (n : Int) (xs : List Rcic.Scm.Val) :
    Rcic.Scm.toCore t (.i n) = none ∨ Rcic.Scm.toCore t (.r xs) = none := by
  cases t <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- TOOTH (Wall C1 on `LevelWire` — `ScmCore.lean:72–80, 235–251`):
    Because `CoreTy` is non-recursive and `levelWireToVal .zero = .r [.i 0]`
    has 1 field while `levelWireToVal (.succ .zero) = .r [.i 1, .r [.i 0]]`
    has 2 fields, NO `t : Rcic.Scm.CoreTy` elaborates both under
    `Rcic.Scm.toCore`. -/
theorem tooth_no_coreTy_for_levelWireToVal (t : Rcic.Scm.CoreTy) :
    Rcic.Scm.toCore t (levelWireToVal .zero) = none ∨
    Rcic.Scm.toCore t (levelWireToVal (.succ .zero)) = none := by
  cases t with
  | i64 | bool | str | bytes | list _ | pair _ _ | sum _ => exact Or.inl rfl
  | record fs =>
      cases fs with
      | nil => exact Or.inl rfl
      | cons f0 fs1 =>
          cases fs1 with
          | nil =>
              right
              simp only [levelWireToVal, Rcic.Scm.toCore, List.map,
                Rcic.Scm.toCoreVals, Option.map]
              cases Rcic.Scm.toCore f0.2 (.i 1) <;> rfl
          | cons f1 fs2 =>
              left
              simp only [levelWireToVal, Rcic.Scm.toCore, List.map,
                Rcic.Scm.toCoreVals, Option.map]
              cases Rcic.Scm.toCore f0.2 (.i 0) <;> rfl

/-- TOOTH (Wall C1 on `ExprWire` — `ScmCore.lean:72–80, 235–251`):
    Even between two 2-field constructors (`exprWireToVal (.bvar 0) = .r [.i 0, .i 0]`
    and `exprWireToVal (.sort .zero) = .r [.i 1, .r [.i 0]]`), their second
    field is an integer vs a record, so NO `t : Rcic.Scm.CoreTy` elaborates
    both under `Rcic.Scm.toCore`. -/
theorem tooth_no_coreTy_for_exprWireToVal (t : Rcic.Scm.CoreTy) :
    Rcic.Scm.toCore t (exprWireToVal (.bvar 0)) = none ∨
    Rcic.Scm.toCore t (exprWireToVal (.sort .zero)) = none := by
  cases t with
  | i64 | bool | str | bytes | list _ | pair _ _ | sum _ => exact Or.inl rfl
  | record fs =>
      cases fs with
      | nil => exact Or.inl rfl
      | cons f0 fs1 =>
          cases fs1 with
          | nil =>
              left
              simp only [exprWireToVal, Rcic.Scm.toCore, List.map,
                Rcic.Scm.toCoreVals, Option.map]
              cases Rcic.Scm.toCore f0.2 (.i 0) <;> rfl
          | cons f1 fs2 =>
              rcases toCore_int_and_rec_impossible f1.2 0 [.i 0] with h1 | h2
              · left
                simp only [exprWireToVal, Rcic.Scm.toCore, List.map,
                  Rcic.Scm.toCoreVals, Option.map, h1]
                cases Rcic.Scm.toCore f0.2 (.i 0) <;> rfl
              · right
                simp only [exprWireToVal, levelWireToVal, Rcic.Scm.toCore, List.map,
                  Rcic.Scm.toCoreVals, Option.map, h2]
                cases Rcic.Scm.toCore f0.2 (.i 1) <;> rfl

set_option maxRecDepth 8000 in
unseal String.splitOnAux in
/-- TOOTH (Wall C3 — `ScmWire` string colon collision with `canonical_group_bytes`):
    Because `Rcic.Scm.Wire.encVal (.s r)` emits `"T" ++ toString r.length ++ ":" ++ r`
    (`ScmWire.lean:56,80`, `scm/rcic/scm_wire_enc_str.scm:1`), encoding
    `ExprWire.const "0" []` via `encExprWireScm` produces `"R3;I2;T1:0L0;"`
    containing a literal `":"`, which `canonPartOk` (`RcicBoundObject.lean:61`,
    `scm/rcic/canon_part_ok.scm:1–2`) refuses inside a `k:v` part `"y:..."`. -/
theorem tooth_scmWire_const_str_colon_collision :
    encExprWireScm (.const "0" []) = "R3;I2;T1:0L0;" ∧
    canonPartOk ("y:" ++ encExprWireScm (.const "0" [])) = false :=
  ⟨rfl, by decide⟩

/-- Exact Lean mirror of SCM `(content-hash s)` on a string value `s`
    (`Residua.SHA256.sha256Hex` over `"StrLit(str:" ++ toString s.length ++ ":" ++ s ++ ")"`),
    matching `rcic.group_codec` form 1 and `rcic.env_image` form 0. -/
def scmContentHashStr (s : String) : String :=
  Residua.SHA256.sha256Hex ("StrLit(str:" ++ toString s.length ++ ":" ++ s ++ ")")

/-- Default `EnvironmentImage` theory profile and checked-group schema frame
    segments (`scm/rcic/env_image_join.scm:1–2`). -/
def envImageDefaultProfile : String := "D-RCIC-0"
def envImageDefaultSchema : String := "checked-group-schema"

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- The producer's empty genesis envelope is parsed as zero groups and accepted
    over the empty environment. Frame fields are never declaration payloads. -/
theorem pin_envImageJoin_empty :
    parseEnvImageEnvelope? (envImageJoin envImageDefaultProfile envImageDefaultSchema []) =
      some [] ∧
    runEnvWireStage emptyEnv 1
      (envImageJoin envImageDefaultProfile envImageDefaultSchema []) = .accepted [] := by
  have hp : parseEnvImageEnvelope?
      (envImageJoin envImageDefaultProfile envImageDefaultSchema []) = some [] := by decide
  refine ⟨hp, ?_⟩
  simp only [runEnvWireStage, decodeEnvImageBytes?, hp, decodeGroupBytesList?]
  rfl

/-- Non-canonical `ScmWire` bytes for `Sort 0`: leading zero in `"R02;"`
    (`"R02;I1;R1;I0;"` vs canonical `"R2;I1;R1;I0;"`). -/
def nonCanonSort0Bytes : String := "R02;I1;R1;I0;"

/-- Bare `canonical_group_bytes` carrying non-canonical `ScmWire` bytes
    `"R02;I1;R1;I0;"` in field `y`, and its `scmContentHashStr` ref and
    `envImageJoin` envelope. -/
def nonCanonGroupBytes : String :=
  "a:0|b:0|d:-|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:rigid|y:R02;I1;R1;I0;"

def nonCanonGroupRef : String :=
  "9aac1c6f6f184b167713a27449fdc85ad122c03b9ffefda6b07dae76f41d34b4"

def nonCanonGroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨nonCanonGroupRef, nonCanonGroupBytes⟩]

/-- Second character of a string, used to distinguish canonical `"R1;"`..`"R4;"`
    prefixes from non-canonical leading-zero `"R0..."` prefixes. -/
def secondChar (s : String) : Option Char :=
  match s.data with
  | _ :: c :: _ => some c
  | _ => none

theorem secondChar_append (p s : String) (hp : p.data.length ≥ 2) :
    secondChar (p ++ s) = secondChar p := by
  unfold secondChar
  rw [String.data_append]
  cases hpdata : p.data with
  | nil => rw [hpdata] at hp; contradiction
  | cons a tl =>
    cases tl with
    | nil => rw [hpdata] at hp; contradiction
    | cons b tl' => rfl

/-- Every `encExprWireScm e` begins with `"R1;"`, `"R2;"`, `"R3;"`, or `"R4;"`,
    so its second character is never `'0'`. -/
theorem secondChar_encExprWireScm (e : ExprWire) :
    secondChar (encExprWireScm e) ≠ some '0' := by
  cases e <;> {
    dsimp only [encExprWireScm, exprWireToVal, Rcic.Scm.Wire.encVal, List.length]
    rw [secondChar_append] <;> decide
  }

/-- Any byte string not in the range of `encExprWireScm` is refused (`= none`)
    by `decExprWireScm?` via `decExprWireScm_canonical`'s re-encode guard. -/
theorem decExprWireScm_eq_none_of_noncanon {bytes : String}
    (hne : ∀ e : ExprWire, encExprWireScm e ≠ bytes) :
    decExprWireScm? bytes = none := by
  cases h : decExprWireScm? bytes with
  | none => rfl
  | some e =>
      exact absurd (decExprWireScm_canonical h).1 (hne e)

/-- TOOTH (Canonical Re-encode Guard): `decExprWireScm?` refuses the
    non-canonical leading-zero encoding `"R02;I1;R1;I0;"` (`= none`). -/
theorem tooth_decExprWireScm_noncanon_refused :
    decExprWireScm? nonCanonSort0Bytes = none := by
  apply decExprWireScm_eq_none_of_noncanon
  intro e he
  have h2 : secondChar (encExprWireScm e) = some '0' := by
    rw [he]; rfl
  exact secondChar_encExprWireScm e h2

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (Canonical Re-encode Guard at the Stage): `runEnvWireStage` refuses
    `nonCanonGroupImageBytes` with `.refusedJudgmentUntyped` because field `y`
    uses non-canonical `ScmWire` bytes `"R02;I1;R1;I0;"`. -/
theorem tooth_runEnvWireStage_noncanon_refused :
    runEnvWireStage emptyEnv 1 nonCanonGroupImageBytes =
      .refusedJudgmentUntyped := by
  have hDec : decodeEnvImageBytes? 1 nonCanonGroupImageBytes = none := by
    unfold nonCanonGroupImageBytes
    rw [decodeEnvImageBytes_single 1 envImageDefaultProfile envImageDefaultSchema
          nonCanonGroupRef nonCanonGroupBytes (by decide) (by decide) (by decide)]
    have hg0 : decodeCheckedGroupBytes? 1 nonCanonGroupBytes = none := by
      rw [decodeCheckedGroupBytes_of_parts 1 nonCanonGroupBytes
            (by decide) (by decide) (by decide)]
      have hab : (parseNatRef? (partAt nonCanonGroupBytes "a") != some 0 ||
                  parseNatRef? (partAt nonCanonGroupBytes "b") != some 0) = false := by decide
      have hm : parseNatRef? (partAt nonCanonGroupBytes "m") = some 0 := by decide
      have hy : partAt nonCanonGroupBytes "y" = nonCanonSort0Bytes := by decide
      rw [hab, if_neg Bool.false_ne_true, hm, hy, tooth_decExprWireScm_noncanon_refused]
    rw [hg0]
    rfl
  unfold runEnvWireStage
  rw [hDec]

/-- Kernel-proved `decExprWireScm?` round-trip on `Sort 0` (`"R2;I1;R1;I0;"`). -/
theorem decExprWireScm_sort0 :
    decExprWireScm? "R2;I1;R1;I0;" = some (.sort .zero) :=
  decExprWireScm_encExprWireScm (.sort .zero) rfl
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.dqV,
          Rcic.Scm.Wire.dqsV, Rcic.Scm.inI64, List.length]; decide)
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.valGas,
          Rcic.Scm.Wire.valsGas]; decide)

/-- Kernel-proved `decExprWireScm?` round-trip on `Sort 1`
    (`"R2;I1;R2;I1;R1;I0;"`). -/
theorem decExprWireScm_sort1 :
    decExprWireScm? "R2;I1;R2;I1;R1;I0;" = some (.sort (.succ .zero)) :=
  decExprWireScm_encExprWireScm (.sort (.succ .zero)) rfl
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.dqV,
          Rcic.Scm.Wire.dqsV, Rcic.Scm.inI64, List.length]; decide)
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.valGas,
          Rcic.Scm.Wire.valsGas]; decide)

/-- Kernel-proved `decExprWireScm?` round-trip on `Π X : Prop, X → X`
    (`"R3;I5;R2;I1;R1;I0;R3;I5;R2;I0;I0;R2;I0;I1;"`). -/
theorem decExprWireScm_machPropId :
    decExprWireScm? "R3;I5;R2;I1;R1;I0;R3;I5;R2;I0;I0;R2;I0;I1;" =
      some (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))) :=
  decExprWireScm_encExprWireScm (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))) rfl
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.dqV,
          Rcic.Scm.Wire.dqsV, Rcic.Scm.inI64, List.length]; decide)
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.valGas,
          Rcic.Scm.Wire.valsGas]; decide)

/-- Kernel-proved `decExprWireScm?` round-trip on `λ X : Prop, λ x : X, x`
    (`"R3;I4;R2;I1;R1;I0;R3;I4;R2;I0;I0;R2;I0;I0;"`). -/
theorem decExprWireScm_machPropIdPf :
    decExprWireScm? "R3;I4;R2;I1;R1;I0;R3;I4;R2;I0;I0;R2;I0;I0;" =
      some (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))) :=
  decExprWireScm_encExprWireScm (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))) rfl
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.dqV,
          Rcic.Scm.Wire.dqsV, Rcic.Scm.inI64, List.length]; decide)
    (by simp only [exprWireToVal, levelWireToVal, Rcic.Scm.Wire.valGas,
          Rcic.Scm.Wire.valsGas]; decide)

/-- Bare `canonical_group_bytes` for the well-typed definition
    `def 0 : Type 0 := Prop` (`a = 0`, `b = 0`, `y = Sort 1`, `d = Sort 0`),
    its `rcic.group_codec` form-1 `content-hash` `goodDefGroupRef`, its
    `env_image_join` complete envelope `goodDefGroupImageBytes`, and its
    `rcic.env_image` form-0 `content-hash` `goodDefEnvImageRef`
    (`"2bd4a913f9e4ddd2621a0515fa590e17366b0c6eddf32993ed2ecf0a998df24c"`). -/
def goodDefGroupBytes : String :=
  "a:0|b:0|d:R2;I1;R1;I0;|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:delta|y:R2;I1;R2;I1;R1;I0;"

def goodDefGroupRef : String :=
  "565f0e566929efb8afc93cd574f570d9c2ee44e2c88eca93d10f6f6c092754d8"

def goodDefEnvImageRef : String :=
  "2bd4a913f9e4ddd2621a0515fa590e17366b0c6eddf32993ed2ecf0a998df24c"

def goodDefGroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨goodDefGroupRef, goodDefGroupBytes⟩]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- PIN: `goodDefGroupRef` is the exact `rcic.group_codec` form-1
    `(content-hash goodDefGroupBytes)`. -/
theorem pin_scmContentHashStr_goodDefGroupBytes :
    scmContentHashStr goodDefGroupBytes = goodDefGroupRef := by decide

/-- PIN: `goodDefEnvImageRef` (`2bd4a913...`) is the exact `rcic.env_image`
    form-0 `(content-hash goodDefGroupImageBytes)` of the `env_image_join`
    producer output. -/
theorem pin_scmContentHashStr_goodDefGroupImageBytes :
    scmContentHashStr goodDefGroupImageBytes = goodDefEnvImageRef := by decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- PIN: `decodeCheckedGroupBytes? 1` decodes `goodDefGroupBytes` to
    `EnvWireEntry.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)`. -/
theorem pin_decodeCheckedGroupBytes_goodDef :
    decodeCheckedGroupBytes? 1 goodDefGroupBytes =
      some (.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)) := by
  rw [decodeCheckedGroupBytes_of_parts 1 goodDefGroupBytes
        (by decide) (by decide) (by decide)]
  have hab : (parseNatRef? (partAt goodDefGroupBytes "a") != some 0 ||
              parseNatRef? (partAt goodDefGroupBytes "b") != some 0) = false := by decide
  have hm : parseNatRef? (partAt goodDefGroupBytes "m") = some 0 := by decide
  have hy : partAt goodDefGroupBytes "y" = "R2;I1;R2;I1;R1;I0;" := by decide
  have hd : partAt goodDefGroupBytes "d" = "R2;I1;R1;I0;" := by decide
  have ht1 : (partAt goodDefGroupBytes "t" == "rigid" &&
    partAt goodDefGroupBytes "d" == "-" &&
    partAt goodDefGroupBytes "o" == "-") = false := by decide
  have ht2 : (partAt goodDefGroupBytes "t" == "delta" &&
    partAt goodDefGroupBytes "d" != "-" &&
    partAt goodDefGroupBytes "o" == "-") = true := by decide
  rw [hab, if_neg Bool.false_ne_true, hm, hy, decExprWireScm_sort1]
  dsimp only
  rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort0]
  rfl

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- PIN: `decodeEnvImageBytes? 1` decodes the producer-framed
    `goodDefGroupImageBytes` (`profile~schema~ref~bytes~`) to
    `[EnvWireEntry.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)]`. -/
theorem pin_decodeEnvImageBytes_goodDef :
    decodeEnvImageBytes? 1 goodDefGroupImageBytes =
      some [.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
  unfold goodDefGroupImageBytes
  rw [decodeEnvImageBytes_single 1 envImageDefaultProfile envImageDefaultSchema
        goodDefGroupRef goodDefGroupBytes (by decide) (by decide) (by decide),
      pin_decodeCheckedGroupBytes_goodDef]
  rfl

/-- PIN: `runEnvWireStage` accepts the producer-framed `goodDefGroupImageBytes`
    (`def 0 : Type 0 := Prop`). -/
theorem pin_runEnvGroupBytes_goodDef :
    runEnvWireStage emptyEnv 1 goodDefGroupImageBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
  unfold runEnvWireStage
  rw [pin_decodeEnvImageBytes_goodDef]
  rfl

/-- Bare `canonical_group_bytes` and `envImageJoin`-framed `EnvironmentImage`
    for the ill-typed definition `def 0 : Prop := Type 0` (`y = Sort 0`,
    `d = Sort 1`). -/
def badDefGroupBytes : String :=
  "a:0|b:0|d:R2;I1;R2;I1;R1;I0;|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:delta|y:R2;I1;R1;I0;"

def badDefGroupRef : String :=
  "7221156cb147cb5a26a059b600beb2007336f3d43cc0dac8d2f8088ce5b9c8fd"

def badDefGroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨badDefGroupRef, badDefGroupBytes⟩]

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH: `runEnvWireStage` decodes the producer-framed `badDefGroupImageBytes`
    and refuses it at `admitSingletonsB` (`def 0 : Prop := Type 0`) with
    `.refusedJudgmentUntyped` (`[rcic_cg014_judgment]`). -/
theorem tooth_runEnvGroupBytes_badDef :
    runEnvWireStage emptyEnv 1 badDefGroupImageBytes =
      .refusedJudgmentUntyped := by
  have hDec :
      decodeEnvImageBytes? 1 badDefGroupImageBytes =
        some [.definitionW 0 1 1 (.sort .zero) (.sort (.succ .zero))] := by
    unfold badDefGroupImageBytes
    rw [decodeEnvImageBytes_single 1 envImageDefaultProfile envImageDefaultSchema
          badDefGroupRef badDefGroupBytes (by decide) (by decide) (by decide)]
    have hg0 :
        decodeCheckedGroupBytes? 1 badDefGroupBytes =
          some (.definitionW 0 1 1 (.sort .zero) (.sort (.succ .zero))) := by
      rw [decodeCheckedGroupBytes_of_parts 1 badDefGroupBytes
            (by decide) (by decide) (by decide)]
      have hab : (parseNatRef? (partAt badDefGroupBytes "a") != some 0 ||
                  parseNatRef? (partAt badDefGroupBytes "b") != some 0) = false := by decide
      have hm : parseNatRef? (partAt badDefGroupBytes "m") = some 0 := by decide
      have hy : partAt badDefGroupBytes "y" = "R2;I1;R1;I0;" := by decide
      have hd : partAt badDefGroupBytes "d" = "R2;I1;R2;I1;R1;I0;" := by decide
      have ht1 : (partAt badDefGroupBytes "t" == "rigid" &&
        partAt badDefGroupBytes "d" == "-" &&
        partAt badDefGroupBytes "o" == "-") = false := by decide
      have ht2 : (partAt badDefGroupBytes "t" == "delta" &&
        partAt badDefGroupBytes "d" != "-" &&
        partAt badDefGroupBytes "o" == "-") = true := by decide
      rw [hab, if_neg Bool.false_ne_true, hm, hy, decExprWireScm_sort0]
      dsimp only
      rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort1]
      rfl
    rw [hg0]
    rfl
  unfold runEnvWireStage
  rw [hDec]
  rfl

/-- Bare `canonical_group_bytes`, `rcic.group_codec` ref, `envImageJoin`
    envelope, and `rcic.env_image` ref for an inductive group (`r:rec0`). -/
def indGroupBytes : String :=
  "a:0|b:0|d:-|i:iota0|m:0|o:-|p:D-RCIC-0|r:rec0|t:rigid|y:R2;I1;R1;I0;"

def indGroupRef : String :=
  "707d86e65b34a173bca49fc6c8a945b873c6d854602f7624ff6ba7aa277b3d25"

def indGroupEnvImageRef : String :=
  "7c184414a3add2ad872ddb30bf19a848d412c92f8f6fbe425153a6537eb31bbd"

def indGroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨indGroupRef, indGroupBytes⟩]

/-- PIN: `indGroupEnvImageRef` is the exact `rcic.env_image` form-0
    `(content-hash indGroupImageBytes)`. -/
theorem pin_scmContentHashStr_indGroupImageBytes :
    scmContentHashStr indGroupImageBytes = indGroupEnvImageRef := by decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (26.2a): `runEnvWireStage` decodes the producer-framed
    `indGroupImageBytes` (`profile~schema~ref~bytes~`) and surfaces
    `.integrityUnbuiltStage`, never `.accepted`. -/
theorem tooth_runEnvGroupBytes_indGroup :
    runEnvWireStage emptyEnv 1 indGroupImageBytes =
      .integrityUnbuiltStage := by
  have hDec :
      decodeEnvImageBytes? 1 indGroupImageBytes =
        some [.inductiveGroupW "0"] := by decide
  unfold runEnvWireStage
  rw [hDec]
  rfl

/-- PIN: `acceptedCheckWire` accepts `blindStore goodDefGroupImageBytes`. -/
theorem pin_acceptedCheckWire_goodDef_accepts :
    acceptedCheckWire emptyEnv 1 (blindStore goodDefGroupImageBytes) stmtBytes "j" =
      codeOk := by
  have hbyte := blind_accepts goodDefGroupImageBytes (by decide)
  unfold acceptedCheckWire
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide), blind_scan_j, blind_env_scan, pin_runEnvGroupBytes_goodDef]

/-- PIN: `cg014_acceptedCheckWire_sound` instantiated at
    `blindStore goodDefGroupImageBytes` — produces both `AcceptedBindingFacts`
    and a machine-checked `EnvWfT` over the decoded `env_image_join` envelope
    without any external decoder parameter. -/
theorem pin_cg014_acceptedCheckWire_goodDef_inhabited :
    (∃ jB tB, AcceptedBindingFacts (blindStore goodDefGroupImageBytes) stmtBytes "j" jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? 1
        (storeScan (blindStore goodDefGroupImageBytes)
          (partAt (storeScan (blindStore goodDefGroupImageBytes) "j").bytes "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons emptyEnv ds)) :=
  cg014_acceptedCheckWire_sound .empty
    (by rw [pin_acceptedCheckWire_goodDef_accepts]; rfl)

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (Opaque-Bytes Refusal): on `blindStore "opaque bytes without an Expr record spelling"`,
    the landed env-blind `acceptedCheck` WRONGLY ACCEPTS (`= codeOk`), whereas
    `acceptedCheckWire` REFUSES with `[rcic_cg014_judgment]`. -/
theorem tooth_acceptedCheckWire_refuses_opaque_bytes :
    acceptedCheck (blindStore "opaque bytes without an Expr record spelling") stmtBytes "j" =
      codeOk ∧
    acceptedCheckWire emptyEnv 1
      (blindStore "opaque bytes without an Expr record spelling") stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" := by
  have hbyte := blind_accepts "opaque bytes without an Expr record spelling" (by decide)
  refine ⟨hbyte, ?_⟩
  unfold acceptedCheckWire
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide), blind_scan_j, blind_env_scan]
  have hDec :
      decodeEnvImageBytes? 1 "opaque bytes without an Expr record spelling" = none := by
    decide
  unfold runEnvWireStage
  rw [hDec]

/-- TOOTH (Non-Canonical Re-encoding Refusal at the Arm): on
    `blindStore nonCanonGroupImageBytes`, the landed `acceptedCheck` WRONGLY
    ACCEPTS (`= codeOk`), whereas `acceptedCheckWire` REFUSES with
    `[rcic_cg014_judgment]`. -/
theorem tooth_acceptedCheckWire_refuses_noncanon :
    acceptedCheck (blindStore nonCanonGroupImageBytes) stmtBytes "j" = codeOk ∧
    acceptedCheckWire emptyEnv 1 (blindStore nonCanonGroupImageBytes) stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" := by
  have hbyte := blind_accepts nonCanonGroupImageBytes (by decide)
  refine ⟨hbyte, ?_⟩
  unfold acceptedCheckWire
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide), blind_scan_j, blind_env_scan,
      tooth_runEnvWireStage_noncanon_refused]

/-- TOOTH (Ill-Typed Body Refusal at the Arm): on
    `blindStore badDefGroupImageBytes` (`def 0 : Prop := Type 0`), the landed
    `acceptedCheck` WRONGLY ACCEPTS (`= codeOk`), whereas `acceptedCheckWire`
    REFUSES with `[rcic_cg014_judgment]`. -/
theorem tooth_acceptedCheckWire_refuses_badDef :
    acceptedCheck (blindStore badDefGroupImageBytes) stmtBytes "j" = codeOk ∧
    acceptedCheckWire emptyEnv 1 (blindStore badDefGroupImageBytes) stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" := by
  have hbyte := blind_accepts badDefGroupImageBytes (by decide)
  refine ⟨hbyte, ?_⟩
  unfold acceptedCheckWire
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide), blind_scan_j, blind_env_scan,
      tooth_runEnvGroupBytes_badDef]

/-- TOOTH (26.2a Inductive Group at the Arm): on `blindStore indGroupImageBytes`,
    the landed `acceptedCheck` WRONGLY ACCEPTS (`= codeOk`), whereas
    `acceptedCheckWire` surfaces `[rcic_graph_admitted_unbuilt_stage]`. -/
theorem tooth_acceptedCheckWire_refuses_indGroup :
    acceptedCheck (blindStore indGroupImageBytes) stmtBytes "j" = codeOk ∧
    acceptedCheckWire emptyEnv 1 (blindStore indGroupImageBytes) stmtBytes "j" =
      codeRefuse "[rcic_graph_admitted_unbuilt_stage]" := by
  have hbyte := blind_accepts indGroupImageBytes (by decide)
  refine ⟨hbyte, ?_⟩
  unfold acceptedCheckWire
  rw [hbyte]
  dsimp only
  rw [if_neg (by decide), blind_scan_j, blind_env_scan,
      tooth_runEnvGroupBytes_indGroup]

/-! ## §10 P1a & P1b Mutant Teeth and Complete Recorded-Triple Producer/Consumer Pins -/

/-- P1a MUTANT: omits `parseEnvImageEnvelope?` (`profile~schema~ref~bytes~` frame)
    and treats every `~`-split segment directly as a group, so it WRONGLY ACCEPTS
    a bare group presented as an `EnvironmentImage` and WRONGLY REFUSES a
    producer-framed `env_image_join` envelope. -/
def decodeEnvImageBytesMutantP1a? (fuel : Nat) (ebytes : String) :
    Option (List EnvWireEntry) :=
  if ebytes.isEmpty then none
  else decodeGroupBytesList? fuel (ebytes.splitOn "~")

def runEnvWireStageMutantP1a (E₀ : ResolvedEnv) (fuel : Nat) (bytes : String) :
    EnvStageResult :=
  match decodeEnvImageBytesMutantP1a? fuel bytes with
  | none => .refusedJudgmentUntyped
  | some es => runEnvEntriesStage E₀ es

def acceptedCheckWireMutantP1a (E₀ : ResolvedEnv) (fuel : Nat)
    (store : List StoreEntry) (sb jref : String) : CodeOut :=
  let res := acceptedCheck store sb jref
  if res.ok ≠ 1 then res
  else
    let jb := (storeScan store jref).bytes
    let eb := (storeScan store (partAt jb "admitted_env_ref")).bytes
    match runEnvWireStageMutantP1a E₀ fuel eb with
    | .accepted _ => codeOk
    | .refusedJudgmentUntyped => codeRefuse "[rcic_cg014_judgment]"
    | .integrityUnbuiltStage => codeRefuse "[rcic_graph_admitted_unbuilt_stage]"

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
private theorem mutantP1a_bare_stage :
    runEnvWireStageMutantP1a emptyEnv 1 goodDefGroupBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
  have hSplit : goodDefGroupBytes.splitOn "~" = [goodDefGroupBytes] := by decide
  have hNotEmpty : goodDefGroupBytes.isEmpty = false := by decide
  unfold runEnvWireStageMutantP1a decodeEnvImageBytesMutantP1a?
  rw [hNotEmpty, hSplit]
  dsimp only [Bool.false_eq_true, ↓reduceIte, decodeGroupBytesList?]
  rw [pin_decodeCheckedGroupBytes_goodDef]
  rfl

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (P1a — Unframed Bare Group Refusal, Zero Premises): for every `fuel`,
    the bare group `goodDefGroupBytes` (without an `env_image_join` frame) is
    refused by `parseEnvImageEnvelope?`, `decodeEnvImageBytes?`, and
    `runEnvWireStage`. -/
theorem tooth_bare_group_refused_by_envelope (fuel : Nat) :
    parseEnvImageEnvelope? goodDefGroupBytes = none ∧
    decodeEnvImageBytes? fuel goodDefGroupBytes = none ∧
    runEnvWireStage emptyEnv fuel goodDefGroupBytes = .refusedJudgmentUntyped := by
  have hsplit : goodDefGroupBytes.splitOn "~" = [goodDefGroupBytes] := by decide
  have ⟨hp, hd⟩ := tooth_bare_group_refused_by_envelope_of_split fuel goodDefGroupBytes hsplit
  refine ⟨hp, hd, ?_⟩
  unfold runEnvWireStage
  rw [hd]

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- PIN (P1a — Producer Envelope Accepted, Zero Premises): `parseEnvImageEnvelope?`
    extracts `[goodDefGroupBytes]` from the `env_image_join`-framed
    `goodDefGroupImageBytes`. -/
theorem pin_parseEnvImageEnvelope_goodDef :
    parseEnvImageEnvelope? goodDefGroupImageBytes = some [goodDefGroupBytes] := by
  unfold goodDefGroupImageBytes
  exact parseEnvImageEnvelope_single envImageDefaultProfile envImageDefaultSchema
    goodDefGroupRef goodDefGroupBytes (by decide) (by decide) (by decide)

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (P1a — Bare Group Presented as Image Refused vs Mutant Acceptance):
    When the bare group `goodDefGroupBytes` (without `profile~schema~ref~bytes~`)
    is presented as an `EnvironmentImage` in `blindStore goodDefGroupBytes`:
    (1) `acceptedCheck` WRONGLY ACCEPTS (`= codeOk`),
    (2) the unframed P1a mutant `acceptedCheckWireMutantP1a` WRONGLY ACCEPTS (`= codeOk`),
    (3) `acceptedCheckWire` REFUSES with `[rcic_cg014_judgment]`, and
    (4) on the genuine producer-framed `goodDefGroupImageBytes`, the P1a mutant
        WRONGLY REFUSES while `acceptedCheckWire` ACCEPTS (`= codeOk`). -/
theorem tooth_acceptedCheckWire_refuses_bare_group :
    acceptedCheck (blindStore goodDefGroupBytes) stmtBytes "j" = codeOk ∧
    acceptedCheckWireMutantP1a emptyEnv 1 (blindStore goodDefGroupBytes) stmtBytes "j" =
      codeOk ∧
    acceptedCheckWire emptyEnv 1 (blindStore goodDefGroupBytes) stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" ∧
    acceptedCheckWireMutantP1a emptyEnv 1 (blindStore goodDefGroupImageBytes) stmtBytes "j" =
      codeRefuse "[rcic_cg014_judgment]" := by
  have hbyteBare := blind_accepts goodDefGroupBytes (by decide)
  have hbyteEnv := blind_accepts goodDefGroupImageBytes (by decide)
  have hMutBare :
      runEnvWireStageMutantP1a emptyEnv 1 goodDefGroupBytes =
        .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := mutantP1a_bare_stage
  have hRealBare :
      runEnvWireStage emptyEnv 1 goodDefGroupBytes = .refusedJudgmentUntyped :=
    (tooth_bare_group_refused_by_envelope 1).2.2
  have hMutEnv :
      runEnvWireStageMutantP1a emptyEnv 1 goodDefGroupImageBytes =
        .refusedJudgmentUntyped := by
    have hDec : decodeEnvImageBytesMutantP1a? 1 goodDefGroupImageBytes = none := by decide
    unfold runEnvWireStageMutantP1a
    rw [hDec]
  refine ⟨hbyteBare, ?_, ?_, ?_⟩
  · unfold acceptedCheckWireMutantP1a
    rw [hbyteBare]
    dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hMutBare]
  · unfold acceptedCheckWire
    rw [hbyteBare]
    dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hRealBare]
  · unfold acceptedCheckWireMutantP1a
    rw [hbyteEnv]
    dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hMutEnv]

/-- P1b MUTANT: parses `a` and `b` via `parseNatRef?` and then erases them
    without checking `a = 0 ∧ b = 0`, silently admitting nonzero-arity groups
    (`1/0`, `0/1`, `1/1`) as the same count-zero (`CheckedMember.arity = 0`)
    declaration. -/
def decodeCheckedGroupBytesMutantP1b? (fuel : Nat) (gbytes : String) :
    Option EnvWireEntry :=
  if !canonBytesOk gbytes || keysOf gbytes != checkedGroupKeys then none
  else
    let aStr := partAt gbytes "a"
    let bStr := partAt gbytes "b"
    let dStr := partAt gbytes "d"
    let iStr := partAt gbytes "i"
    let mStr := partAt gbytes "m"
    let oStr := partAt gbytes "o"
    let pStr := partAt gbytes "p"
    let rStr := partAt gbytes "r"
    let tStr := partAt gbytes "t"
    let yStr := partAt gbytes "y"
    if pStr.isEmpty || (parseNatRef? aStr).isNone || (parseNatRef? bStr).isNone then none
    else if iStr != "-" || rStr != "-" then
      some (.inductiveGroupW mStr)
    else
      match parseNatRef? mStr, decExprWireScm? yStr with
      | some refN, some tyW =>
          if tStr == "rigid" && dStr == "-" && oStr == "-" then
            some (.axiomW refN fuel tyW)
          else if tStr == "delta" && dStr != "-" && oStr == "-" then
            (decExprWireScm? dStr).map (.definitionW refN fuel fuel tyW)
          else if tStr == "rigid" && dStr != "-" && oStr == "-" then
            (decExprWireScm? dStr).map (.theoremW refN fuel fuel tyW)
          else if tStr == "rigid" && dStr == "-" && oStr != "-" then
            (decExprWireScm? oStr).map (.opaqueW refN fuel fuel tyW)
          else none
      | _, _ => none

def decodeGroupBytesListMutantP1b? (fuel : Nat) : List String → Option (List EnvWireEntry)
  | [] => some []
  | g :: gs =>
      match decodeCheckedGroupBytesMutantP1b? fuel g, decodeGroupBytesListMutantP1b? fuel gs with
      | some e, some es => some (e :: es)
      | _, _ => none

def decodeEnvImageBytesMutantP1b? (fuel : Nat) (ebytes : String) :
    Option (List EnvWireEntry) :=
  match parseEnvImageEnvelope? ebytes with
  | some gs => decodeGroupBytesListMutantP1b? fuel gs
  | none => none

def runEnvWireStageMutantP1b (E₀ : ResolvedEnv) (fuel : Nat) (bytes : String) :
    EnvStageResult :=
  match decodeEnvImageBytesMutantP1b? fuel bytes with
  | none => .refusedJudgmentUntyped
  | some es => runEnvEntriesStage E₀ es

def acceptedCheckWireMutantP1b (E₀ : ResolvedEnv) (fuel : Nat)
    (store : List StoreEntry) (sb jref : String) : CodeOut :=
  let res := acceptedCheck store sb jref
  if res.ok ≠ 1 then res
  else
    let jb := (storeScan store jref).bytes
    let eb := (storeScan store (partAt jb "admitted_env_ref")).bytes
    match runEnvWireStageMutantP1b E₀ fuel eb with
    | .accepted _ => codeOk
    | .refusedJudgmentUntyped => codeRefuse "[rcic_cg014_judgment]"
    | .integrityUnbuiltStage => codeRefuse "[rcic_graph_admitted_unbuilt_stage]"

/-- Helper unfolding `decodeCheckedGroupBytesMutantP1b?` on a canonical non-group wire. -/
private theorem decodeCheckedGroupBytesMutantP1b_of_parts (fuel : Nat) (gbytes : String)
    (hc : (!canonBytesOk gbytes || keysOf gbytes != checkedGroupKeys) = false)
    (hp : ((partAt gbytes "p").isEmpty || (parseNatRef? (partAt gbytes "a")).isNone ||
           (parseNatRef? (partAt gbytes "b")).isNone) = false)
    (hir : (partAt gbytes "i" != "-" || partAt gbytes "r" != "-") = false) :
    decodeCheckedGroupBytesMutantP1b? fuel gbytes =
      match parseNatRef? (partAt gbytes "m"), decExprWireScm? (partAt gbytes "y") with
      | some refN, some tyW =>
          if partAt gbytes "t" == "rigid" && partAt gbytes "d" == "-" && partAt gbytes "o" == "-" then
            some (.axiomW refN fuel tyW)
          else if partAt gbytes "t" == "delta" && partAt gbytes "d" != "-" && partAt gbytes "o" == "-" then
            (decExprWireScm? (partAt gbytes "d")).map (.definitionW refN fuel fuel tyW)
          else if partAt gbytes "t" == "rigid" && partAt gbytes "d" != "-" && partAt gbytes "o" == "-" then
            (decExprWireScm? (partAt gbytes "d")).map (.theoremW refN fuel fuel tyW)
          else if partAt gbytes "t" == "rigid" && partAt gbytes "d" == "-" && partAt gbytes "o" != "-" then
            (decExprWireScm? (partAt gbytes "o")).map (.opaqueW refN fuel fuel tyW)
          else none
      | _, _ => none := by
  unfold decodeCheckedGroupBytesMutantP1b?
  dsimp only
  rw [hc, if_neg Bool.false_ne_true, hp, if_neg Bool.false_ne_true, hir, if_neg Bool.false_ne_true]

/-- The three nonzero-arity counterparts (`a/b` = `1/0`, `0/1`, `1/1`) of
    `goodDefGroupBytes` (`a/b` = `0/0`), their distinct `rcic.group_codec`
    form-1 content refs, and their `envImageJoin` complete envelopes. -/
def arity10GroupBytes : String :=
  "a:1|b:0|d:R2;I1;R1;I0;|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:delta|y:R2;I1;R2;I1;R1;I0;"
def arity10GroupRef : String :=
  "75fef5e9b0b47e8ba802c112fff2d7b1116c578ee8d9e6236e0a817e423c0d65"
def arity10GroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨arity10GroupRef, arity10GroupBytes⟩]

def arity01GroupBytes : String :=
  "a:0|b:1|d:R2;I1;R1;I0;|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:delta|y:R2;I1;R2;I1;R1;I0;"
def arity01GroupRef : String :=
  "388df7d1810e7b61f8b3021387dd8adbd366a11439cb89bda653b9566912b27c"
def arity01GroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨arity01GroupRef, arity01GroupBytes⟩]

def arity11GroupBytes : String :=
  "a:1|b:1|d:R2;I1;R1;I0;|i:-|m:0|o:-|p:D-RCIC-0|r:-|t:delta|y:R2;I1;R2;I1;R1;I0;"
def arity11GroupRef : String :=
  "ed1fc78b265cfc7a1e15bf41ad40854553fe92faa4778c1a3c3342ef51590a57"
def arity11GroupImageBytes : String :=
  envImageJoin envImageDefaultProfile envImageDefaultSchema
    [⟨arity11GroupRef, arity11GroupBytes⟩]

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (P1b — Nonzero Arity Refusal, Zero Premises): for every `fuel`,
    the three nonzero-arity singleton group wires (`1/0`, `0/1`, `1/1`) are
    refused by `decodeCheckedGroupBytes?` (`= none`), never silently admitted as
    count-zero. -/
theorem tooth_decodeCheckedGroupBytes_nonzero_arity_refused (fuel : Nat) :
    decodeCheckedGroupBytes? fuel arity10GroupBytes = none ∧
    decodeCheckedGroupBytes? fuel arity01GroupBytes = none ∧
    decodeCheckedGroupBytes? fuel arity11GroupBytes = none :=
  ⟨tooth_decodeCheckedGroupBytes_nonzero_arity_refused_of_parts fuel arity10GroupBytes
      (by decide) (by decide) (by decide) (by decide),
   tooth_decodeCheckedGroupBytes_nonzero_arity_refused_of_parts fuel arity01GroupBytes
      (by decide) (by decide) (by decide) (by decide),
   tooth_decodeCheckedGroupBytes_nonzero_arity_refused_of_parts fuel arity11GroupBytes
      (by decide) (by decide) (by decide) (by decide)⟩

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (P1b — Nonzero Arities Refused at Stage): `runEnvWireStage` refuses
    all three nonzero-arity group images (`1/0`, `0/1`, `1/1`) with
    `.refusedJudgmentUntyped`. -/
theorem tooth_runEnvWireStage_refuses_nonzero_arities :
    runEnvWireStage emptyEnv 1 arity10GroupImageBytes = .refusedJudgmentUntyped ∧
    runEnvWireStage emptyEnv 1 arity01GroupImageBytes = .refusedJudgmentUntyped ∧
    runEnvWireStage emptyEnv 1 arity11GroupImageBytes = .refusedJudgmentUntyped := by
  have h10 : decodeEnvImageBytes? 1 arity10GroupImageBytes = none := by decide
  have h01 : decodeEnvImageBytes? 1 arity01GroupImageBytes = none := by decide
  have h11 : decodeEnvImageBytes? 1 arity11GroupImageBytes = none := by decide
  unfold runEnvWireStage
  rw [h10, h01, h11]
  exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
/-- TOOTH (P1b Mutant — Erases `a/b` and Collapses All Four Groups to Count-Zero):
    The arity-erasing mutant `runEnvWireStageMutantP1b` WRONGLY ACCEPTS all four
    groups (`0/0`, `1/0`, `0/1`, `1/1`) and maps all four to the identical
    count-zero declaration `[.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)]`
    whose derived member has `.arity = 0`. -/
theorem tooth_mutantP1b_accepts_all_four_arities :
    runEnvWireStageMutantP1b emptyEnv 1 goodDefGroupImageBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] ∧
    runEnvWireStageMutantP1b emptyEnv 1 arity10GroupImageBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] ∧
    runEnvWireStageMutantP1b emptyEnv 1 arity01GroupImageBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] ∧
    runEnvWireStageMutantP1b emptyEnv 1 arity11GroupImageBytes =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
  have hg00 :
      decodeCheckedGroupBytesMutantP1b? 1 goodDefGroupBytes =
        some (.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)) := by
    rw [decodeCheckedGroupBytesMutantP1b_of_parts 1 goodDefGroupBytes
          (by decide) (by decide) (by decide)]
    have hm : parseNatRef? (partAt goodDefGroupBytes "m") = some 0 := by decide
    have hy : partAt goodDefGroupBytes "y" = "R2;I1;R2;I1;R1;I0;" := by decide
    have hd : partAt goodDefGroupBytes "d" = "R2;I1;R1;I0;" := by decide
    have ht1 : (partAt goodDefGroupBytes "t" == "rigid" &&
      partAt goodDefGroupBytes "d" == "-" &&
      partAt goodDefGroupBytes "o" == "-") = false := by decide
    have ht2 : (partAt goodDefGroupBytes "t" == "delta" &&
      partAt goodDefGroupBytes "d" != "-" &&
      partAt goodDefGroupBytes "o" == "-") = true := by decide
    rw [hm, hy, decExprWireScm_sort1]
    dsimp only
    rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort0]
    rfl
  have hg10 :
      decodeCheckedGroupBytesMutantP1b? 1 arity10GroupBytes =
        some (.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)) := by
    rw [decodeCheckedGroupBytesMutantP1b_of_parts 1 arity10GroupBytes
          (by decide) (by decide) (by decide)]
    have hm : parseNatRef? (partAt arity10GroupBytes "m") = some 0 := by decide
    have hy : partAt arity10GroupBytes "y" = "R2;I1;R2;I1;R1;I0;" := by decide
    have hd : partAt arity10GroupBytes "d" = "R2;I1;R1;I0;" := by decide
    have ht1 : (partAt arity10GroupBytes "t" == "rigid" &&
      partAt arity10GroupBytes "d" == "-" &&
      partAt arity10GroupBytes "o" == "-") = false := by decide
    have ht2 : (partAt arity10GroupBytes "t" == "delta" &&
      partAt arity10GroupBytes "d" != "-" &&
      partAt arity10GroupBytes "o" == "-") = true := by decide
    rw [hm, hy, decExprWireScm_sort1]
    dsimp only
    rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort0]
    rfl
  have hg01 :
      decodeCheckedGroupBytesMutantP1b? 1 arity01GroupBytes =
        some (.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)) := by
    rw [decodeCheckedGroupBytesMutantP1b_of_parts 1 arity01GroupBytes
          (by decide) (by decide) (by decide)]
    have hm : parseNatRef? (partAt arity01GroupBytes "m") = some 0 := by decide
    have hy : partAt arity01GroupBytes "y" = "R2;I1;R2;I1;R1;I0;" := by decide
    have hd : partAt arity01GroupBytes "d" = "R2;I1;R1;I0;" := by decide
    have ht1 : (partAt arity01GroupBytes "t" == "rigid" &&
      partAt arity01GroupBytes "d" == "-" &&
      partAt arity01GroupBytes "o" == "-") = false := by decide
    have ht2 : (partAt arity01GroupBytes "t" == "delta" &&
      partAt arity01GroupBytes "d" != "-" &&
      partAt arity01GroupBytes "o" == "-") = true := by decide
    rw [hm, hy, decExprWireScm_sort1]
    dsimp only
    rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort0]
    rfl
  have hg11 :
      decodeCheckedGroupBytesMutantP1b? 1 arity11GroupBytes =
        some (.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)) := by
    rw [decodeCheckedGroupBytesMutantP1b_of_parts 1 arity11GroupBytes
          (by decide) (by decide) (by decide)]
    have hm : parseNatRef? (partAt arity11GroupBytes "m") = some 0 := by decide
    have hy : partAt arity11GroupBytes "y" = "R2;I1;R2;I1;R1;I0;" := by decide
    have hd : partAt arity11GroupBytes "d" = "R2;I1;R1;I0;" := by decide
    have ht1 : (partAt arity11GroupBytes "t" == "rigid" &&
      partAt arity11GroupBytes "d" == "-" &&
      partAt arity11GroupBytes "o" == "-") = false := by decide
    have ht2 : (partAt arity11GroupBytes "t" == "delta" &&
      partAt arity11GroupBytes "d" != "-" &&
      partAt arity11GroupBytes "o" == "-") = true := by decide
    rw [hm, hy, decExprWireScm_sort1]
    dsimp only
    rw [ht1, if_neg Bool.false_ne_true, ht2, if_pos rfl, hd, decExprWireScm_sort0]
    rfl
  have hd00 : decodeEnvImageBytesMutantP1b? 1 goodDefGroupImageBytes =
      some [.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
    unfold decodeEnvImageBytesMutantP1b? goodDefGroupImageBytes
    rw [parseEnvImageEnvelope_single envImageDefaultProfile envImageDefaultSchema
          goodDefGroupRef goodDefGroupBytes (by decide) (by decide) (by decide)]
    dsimp only [decodeGroupBytesListMutantP1b?]
    rw [hg00]
  have hd10 : decodeEnvImageBytesMutantP1b? 1 arity10GroupImageBytes =
      some [.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
    unfold decodeEnvImageBytesMutantP1b? arity10GroupImageBytes
    rw [parseEnvImageEnvelope_single envImageDefaultProfile envImageDefaultSchema
          arity10GroupRef arity10GroupBytes (by decide) (by decide) (by decide)]
    dsimp only [decodeGroupBytesListMutantP1b?]
    rw [hg10]
  have hd01 : decodeEnvImageBytesMutantP1b? 1 arity01GroupImageBytes =
      some [.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
    unfold decodeEnvImageBytesMutantP1b? arity01GroupImageBytes
    rw [parseEnvImageEnvelope_single envImageDefaultProfile envImageDefaultSchema
          arity01GroupRef arity01GroupBytes (by decide) (by decide) (by decide)]
    dsimp only [decodeGroupBytesListMutantP1b?]
    rw [hg01]
  have hd11 : decodeEnvImageBytesMutantP1b? 1 arity11GroupImageBytes =
      some [.definitionW 0 1 1 (.sort (.succ .zero)) (.sort .zero)] := by
    unfold decodeEnvImageBytesMutantP1b? arity11GroupImageBytes
    rw [parseEnvImageEnvelope_single envImageDefaultProfile envImageDefaultSchema
          arity11GroupRef arity11GroupBytes (by decide) (by decide) (by decide)]
    dsimp only [decodeGroupBytesListMutantP1b?]
    rw [hg11]
  unfold runEnvWireStageMutantP1b
  rw [hd00, hd10, hd01, hd11]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- TOOTH (P1b at the Arm — Nonzero Arities Refused vs Mutant Acceptance):
    On `blindStore arity10GroupImageBytes`, `blindStore arity01GroupImageBytes`,
    and `blindStore arity11GroupImageBytes`:
    (1) `acceptedCheck` WRONGLY ACCEPTS all three (`= codeOk`),
    (2) the P1b arity-erasing mutant `acceptedCheckWireMutantP1b` WRONGLY ACCEPTS
        all three (`= codeOk`), and
    (3) `acceptedCheckWire` REFUSES all three (`= codeRefuse "[rcic_cg014_judgment]"`). -/
theorem tooth_acceptedCheckWire_refuses_nonzero_arities :
    (acceptedCheck (blindStore arity10GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWireMutantP1b emptyEnv 1 (blindStore arity10GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWire emptyEnv 1 (blindStore arity10GroupImageBytes) stmtBytes "j" =
       codeRefuse "[rcic_cg014_judgment]") ∧
    (acceptedCheck (blindStore arity01GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWireMutantP1b emptyEnv 1 (blindStore arity01GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWire emptyEnv 1 (blindStore arity01GroupImageBytes) stmtBytes "j" =
       codeRefuse "[rcic_cg014_judgment]") ∧
    (acceptedCheck (blindStore arity11GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWireMutantP1b emptyEnv 1 (blindStore arity11GroupImageBytes) stmtBytes "j" = codeOk ∧
     acceptedCheckWire emptyEnv 1 (blindStore arity11GroupImageBytes) stmtBytes "j" =
       codeRefuse "[rcic_cg014_judgment]") := by
  have hb10 := blind_accepts arity10GroupImageBytes (by decide)
  have hb01 := blind_accepts arity01GroupImageBytes (by decide)
  have hb11 := blind_accepts arity11GroupImageBytes (by decide)
  obtain ⟨hr10, hr01, hr11⟩ := tooth_runEnvWireStage_refuses_nonzero_arities
  obtain ⟨_, hm10, hm01, hm11⟩ := tooth_mutantP1b_accepts_all_four_arities
  refine ⟨⟨hb10, ?_, ?_⟩, ⟨hb01, ?_, ?_⟩, ⟨hb11, ?_, ?_⟩⟩
  · unfold acceptedCheckWireMutantP1b; rw [hb10]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hm10]
  · unfold acceptedCheckWire; rw [hb10]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hr10]
  · unfold acceptedCheckWireMutantP1b; rw [hb01]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hm01]
  · unfold acceptedCheckWire; rw [hb01]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hr01]
  · unfold acceptedCheckWireMutantP1b; rw [hb11]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hm11]
  · unfold acceptedCheckWire; rw [hb11]; dsimp only
    rw [if_neg (by decide), blind_scan_j, blind_env_scan, hr11]

/-- Full triple-validator skeleton, with only the CG-014 arm replaced by the
    selected isolated mutant. Store resolution and receipt validation are retained. -/
private def graphAdmittedWireMutantWith
    (arm : ResolvedEnv → Nat → List StoreEntry → String → String → CodeOut)
    (E₀ : ResolvedEnv) (store : List StoreEntry)
    (statementRef receiptRef occurrenceRef occurrence : String) (fuel : Int) : EOut :=
  let res := graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel
  if res.ok ≠ 1 then res
  else
    let rb := (storeScan store receiptRef).bytes
    let d := decisionCheck store (partAt rb "decision")
    if d.ctor = "accepted" then
      let sb := (storeScan store statementRef).bytes
      let ja := arm E₀ fuel.toNat store sb d.value
      if ja.ok = 1 then ⟨1, occurrence, ""⟩ else eRefuse ja.code
    else res

/-- Full-validator P1a mutant: changes only envelope decoding. -/
def graphAdmittedWireMutantP1a := graphAdmittedWireMutantWith acceptedCheckWireMutantP1a

/-- Full-validator P1b mutant: changes only singleton arity checking. -/
def graphAdmittedWireMutantP1b := graphAdmittedWireMutantWith acceptedCheckWireMutantP1b

/-- Complete recorded-triple store modeled on row 0 of
    `apps/rcic-graph-admitted/rcic_graph_admitted_corpus.json` (`:1–258`),
    binding `admitted_env_ref` and `env_ref` to the actual producer-derived
    `goodDefEnvImageRef` (`2bd4a913f9e4ddd2621a0515fa590e17366b0c6eddf32993ed2ecf0a998df24c`)
    and varying only the environment entry bytes `b`. -/
def tripleStmtRef : String :=
  "8c6cffb35ebd4299f5212efe7bd9a2bc189714a95c2f1e400dc37195d95ccacf"
def tripleReceiptRef : String :=
  "1a14a4418d65ceb504cb03c6a049a364752671e1d6b0022da776d3fbe2549598"
def tripleOccurrence : String :=
  "receipt_ref:1a14a4418d65ceb504cb03c6a049a364752671e1d6b0022da776d3fbe2549598|statement_ref:8c6cffb35ebd4299f5212efe7bd9a2bc189714a95c2f1e400dc37195d95ccacf"
def tripleJRef : String :=
  "efea579cf18f481db22d0a8408bb1befb7b7f2f49e45c6f20c3cfbb320323b9c"
def tripleStmtBytes : String :=
  "closed_graph_bundle_ref:ba7edf230822a941c71f9a01310faff025efb9035ffa800ce91ad797f419a170|epoch:0|institutional_basis_refs:ib1|sequence:0"
def tripleJBytes : String :=
  "admitted_env_ref:2bd4a913f9e4ddd2621a0515fa590e17366b0c6eddf32993ed2ecf0a998df24c|assumptions_ref:953c9447c873afd4f4eb84af975b0d5812993f123f88af2420d6881cfc22ce06|coverage_grade:exact|subject_bundle_ref:ba7edf230822a941c71f9a01310faff025efb9035ffa800ce91ad797f419a170|typed_judgment_ref:9c59f7deb56f6e717fae1289e2f69013d8fb25a41214033a3dd52abb9eeebd66"
def tripleTBytes : String :=
  "env_ref:2bd4a913f9e4ddd2621a0515fa590e17366b0c6eddf32993ed2ecf0a998df24c|subject_bundle_ref:ba7edf230822a941c71f9a01310faff025efb9035ffa800ce91ad797f419a170"
def tripleReceiptBytes : String :=
  "decision:cb56bac5fb6cf06262a6d92fbc071033bd2f1c6328395e925ec23312b4bb7d9c|evidence_bundle_ref:60dbd1d374eb374081965a66cd862c861cd670054338f64b548be65daa489dd5|statement_ref:8c6cffb35ebd4299f5212efe7bd9a2bc189714a95c2f1e400dc37195d95ccacf|validator_artifact_ref:b7fcb232a7407a64095d740917e6c72d5c71391f17cce76602bbe05bb562b52d|validator_execution_evidence_ref:3ace04e9a9ecdd176fd88a698771307eef3f71dacd81269389592893ce87a701|validator_spec_ref:9730aa916fa66c40a24712cf545ad3fcc3b64b4c70d43b8eba1195efae9452f2"

def completeTripleStore (b : String) : List StoreEntry :=
  [ ⟨goodDefEnvImageRef, b⟩
  , ⟨"953c9447c873afd4f4eb84af975b0d5812993f123f88af2420d6881cfc22ce06", "kind:assumption_closure"⟩
  , ⟨"ba7edf230822a941c71f9a01310faff025efb9035ffa800ce91ad797f419a170", "kind:closed_graph_bundle"⟩
  , ⟨"60dbd1d374eb374081965a66cd862c861cd670054338f64b548be65daa489dd5", "kind:evidence_bundle"⟩
  , ⟨"b7fcb232a7407a64095d740917e6c72d5c71391f17cce76602bbe05bb562b52d", "kind:validator_artifact"⟩
  , ⟨"3ace04e9a9ecdd176fd88a698771307eef3f71dacd81269389592893ce87a701", "kind:validator_execution_evidence"⟩
  , ⟨"9730aa916fa66c40a24712cf545ad3fcc3b64b4c70d43b8eba1195efae9452f2", "kind:validator_spec"⟩
  , ⟨"9c59f7deb56f6e717fae1289e2f69013d8fb25a41214033a3dd52abb9eeebd66", tripleTBytes⟩
  , ⟨tripleJRef, tripleJBytes⟩
  , ⟨"cb56bac5fb6cf06262a6d92fbc071033bd2f1c6328395e925ec23312b4bb7d9c",
     "accepted:efea579cf18f481db22d0a8408bb1befb7b7f2f49e45c6f20c3cfbb320323b9c"⟩
  , ⟨tripleStmtRef, tripleStmtBytes⟩
  , ⟨tripleReceiptRef, tripleReceiptBytes⟩
  ]

private theorem dOut_eq {d : DOut} {ok : Int} {code ctor value : String}
    (h1 : d.ok = ok) (h2 : d.code = code) (h3 : d.ctor = ctor) (h4 : d.value = value) :
    d = ⟨ok, code, ctor, value⟩ := by
  cases d; simp_all

private theorem eOut_eq {e : EOut} {ok : Int} {q code : String}
    (h1 : e.ok = ok) (h2 : e.q = q) (h3 : e.code = code) :
    e = ⟨ok, q, code⟩ := by
  cases e; simp_all

private theorem storeScan_cons_skip (e : StoreEntry) (store : List StoreEntry) (d : String)
    (h : e.digest ≠ d) :
    storeScan (e :: store) d = storeScan store d := by
  unfold storeScan
  rw [List.foldl_cons, if_neg h]

private theorem completeTriple_scan_ne (b : String) {r : String} (hr : goodDefEnvImageRef ≠ r) :
    storeScan (completeTripleStore b) r = storeScan (completeTripleStore "x:y") r := by
  unfold completeTripleStore
  rw [storeScan_cons_skip ⟨goodDefEnvImageRef, b⟩ _ r hr]
  rw [storeScan_cons_skip ⟨goodDefEnvImageRef, "x:y"⟩ _ r hr]

private theorem completeTriple_refBound_ne (b : String) {r : String} (miss : String)
    (hr : goodDefEnvImageRef ≠ r) :
    refBound (completeTripleStore b) r miss = refBound (completeTripleStore "x:y") r miss := by
  unfold refBound
  rw [completeTriple_scan_ne b hr]

private theorem completeTriple_seamRefBound_ne (b : String) (fuel cls knd : Int) {r : String}
    (miss : String) (hr : goodDefEnvImageRef ≠ r) :
    seamRefBound fuel cls knd r (completeTripleStore b) miss =
      seamRefBound fuel cls knd r (completeTripleStore "x:y") miss := by
  unfold seamRefBound
  rw [completeTriple_scan_ne b hr]

/-- Full-triple-validator reduction law for `graphAdmittedWire`: whenever the
    byte-level `graphAdmitted` accepts on an `"accepted"` receipt decision
    naming `jref`, `graphAdmittedWire` returns `⟨1, occurrence, ""⟩` iff
    `acceptedCheckWire` accepts on `jref`, and otherwise propagates
    `acceptedCheckWire`'s refusal code (`[rcic_cg014_judgment]` or
    `[rcic_graph_admitted_unbuilt_stage]`). -/
theorem graphAdmittedWire_of_accepted (E₀ : ResolvedEnv)
    {store : List StoreEntry}
    {statementRef receiptRef occurrenceRef occurrence : String} {fuel : Int}
    {jref : String}
    (hga : graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel =
      ⟨1, occurrence, ""⟩)
    (hdec : decisionCheck store (partAt (storeScan store receiptRef).bytes "decision") =
      ⟨1, "", "accepted", jref⟩) :
    graphAdmittedWire E₀ store statementRef receiptRef occurrenceRef occurrence fuel =
      let ja := acceptedCheckWire E₀ fuel.toNat store (storeScan store statementRef).bytes jref
      if ja.ok = 1 then ⟨1, occurrence, ""⟩ else eRefuse ja.code := by
  unfold graphAdmittedWire
  rw [hga]
  dsimp only
  rw [if_neg (by decide), hdec]
  dsimp only
  rw [if_pos rfl]

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem tripleJBytes_env : partAt tripleJBytes "admitted_env_ref" = goodDefEnvImageRef := by
  decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem tripleJBytes_assumptions :
    partAt tripleJBytes "assumptions_ref" =
      "953c9447c873afd4f4eb84af975b0d5812993f123f88af2420d6881cfc22ce06" := by
  decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem tripleJBytes_typed :
    partAt tripleJBytes "typed_judgment_ref" =
      "9c59f7deb56f6e717fae1289e2f69013d8fb25a41214033a3dd52abb9eeebd66" := by
  decide

theorem completeTriple_scan_j (b : String) :
    storeScan (completeTripleStore b) tripleJRef = ⟨true, tripleJBytes, false⟩ := by
  simp [storeScan, completeTripleStore, goodDefEnvImageRef, tripleJRef,
        tripleStmtRef, tripleReceiptRef]

theorem completeTriple_scan_stmt (b : String) :
    storeScan (completeTripleStore b) tripleStmtRef = ⟨true, tripleStmtBytes, false⟩ := by
  simp [storeScan, completeTripleStore, goodDefEnvImageRef, tripleJRef,
        tripleStmtRef, tripleReceiptRef]

theorem completeTriple_scan_env (b : String) :
    storeScan (completeTripleStore b) (partAt tripleJBytes "admitted_env_ref") =
      ⟨true, b, false⟩ := by
  rw [tripleJBytes_env]
  simp [storeScan, completeTripleStore, goodDefEnvImageRef, tripleJRef,
        tripleStmtRef, tripleReceiptRef]

private theorem completeTriple_scan_receipt (b : String) :
    storeScan (completeTripleStore b) tripleReceiptRef = ⟨true, tripleReceiptBytes, false⟩ := by
  simp [storeScan, completeTripleStore, goodDefEnvImageRef, tripleJRef,
        tripleStmtRef, tripleReceiptRef, tripleReceiptBytes]

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem completeTriple_acceptedCheck_ref :
    acceptedCheck (completeTripleStore "x:y") tripleStmtBytes tripleJRef = codeOk := by
  apply codeOut_eq_ok
  · decide
  · decide

theorem completeTriple_acceptedCheck (b : String) (hb : b ≠ "") :
    acceptedCheck (completeTripleStore b) tripleStmtBytes tripleJRef = codeOk := by
  rw [← completeTriple_acceptedCheck_ref]
  apply acceptedCheck_env_congr
  · rw [completeTriple_scan_j, completeTriple_scan_j]
  · rw [completeTriple_scan_j, tripleJBytes_env]
    simp [refBound, storeScan, completeTripleStore, goodDefEnvImageRef, tripleJRef,
          tripleStmtRef, tripleReceiptRef, hb]
  · rw [completeTriple_scan_j, tripleJBytes_assumptions]
    exact completeTriple_refBound_ne b _ (by decide)
  · rw [completeTriple_scan_j, tripleJBytes_typed]
    exact completeTriple_scan_ne b (by decide)

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
private theorem completeTriple_decision_ref :
    decisionCheck (completeTripleStore "x:y")
      "cb56bac5fb6cf06262a6d92fbc071033bd2f1c6328395e925ec23312b4bb7d9c" =
      ⟨1, "", "accepted", tripleJRef⟩ := by
  apply dOut_eq <;> decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem completeTriple_decision (b : String) :
    decisionCheck (completeTripleStore b)
      (partAt (storeScan (completeTripleStore b) tripleReceiptRef).bytes "decision") =
      ⟨1, "", "accepted", tripleJRef⟩ := by
  rw [completeTriple_scan_receipt b]
  dsimp only
  have hp : partAt tripleReceiptBytes "decision" =
      "cb56bac5fb6cf06262a6d92fbc071033bd2f1c6328395e925ec23312b4bb7d9c" := by decide
  rw [hp, ← completeTriple_decision_ref]
  unfold decisionCheck
  rw [completeTriple_scan_ne b (by decide)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
unseal String.splitOnAux in
theorem completeTriple_graphAdmitted_ref :
    graphAdmitted (completeTripleStore "x:y")
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ := by
  apply eOut_eq <;> decide

set_option maxRecDepth 20000 in
unseal String.splitOnAux in
theorem completeTriple_graphAdmitted (b : String) (hb : b ≠ "") :
    graphAdmitted (completeTripleStore b)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ := by
  rw [← completeTriple_graphAdmitted_ref]
  unfold graphAdmitted
  have hs := completeTriple_seamRefBound_ne b 1 3 0
    "[rcic_graph_admitted_statement_unbound]" (by decide : goodDefEnvImageRef ≠ tripleStmtRef)
  have hph : historyOk 1 (completeTripleStore b) tripleStmtBytes =
      historyOk 1 (completeTripleStore "x:y") tripleStmtBytes := by
    have hp : partAt tripleStmtBytes "history_parent_ref" = "" := by decide
    simp [historyOk, hp]
  have hbr := completeTriple_seamRefBound_ne b 1 8 0
    "[rcic_graph_admitted_receipt_unbound]" (by decide : goodDefEnvImageRef ≠ tripleReceiptRef)
  have hrr : receiptRefsOk (completeTripleStore b) tripleReceiptBytes =
      receiptRefsOk (completeTripleStore "x:y") tripleReceiptBytes := by
    unfold receiptRefsOk receiptRefKeys
    dsimp only [List.foldl]
    rw [completeTriple_refBound_ne b _ (by decide),
        completeTriple_refBound_ne b _ (by decide),
        completeTriple_refBound_ne b _ (by decide),
        completeTriple_refBound_ne b _ (by decide)]
  have hbb := completeTriple_refBound_ne b "[rcic_graph_admitted_bundle_unbound]"
    (by decide : goodDefEnvImageRef ≠ partAt tripleStmtBytes "closed_graph_bundle_ref")
  have hoi : occurrenceIdentity (completeTripleStore b)
      tripleReceiptRef tripleReceiptRef tripleOccurrence =
      occurrenceIdentity (completeTripleStore "x:y")
      tripleReceiptRef tripleReceiptRef tripleOccurrence := by
    unfold occurrenceIdentity
    rw [completeTriple_seamRefBound_ne b 1 8 0 _ (by decide),
        completeTriple_scan_receipt b, completeTriple_scan_receipt "x:y"]
  have hd : decisionCheck (completeTripleStore b) (partAt tripleReceiptBytes "decision") =
      ⟨1, "", "accepted", tripleJRef⟩ := by
    have h0 := completeTriple_decision b
    rw [completeTriple_scan_receipt b] at h0
    exact h0
  have hd_ref : decisionCheck (completeTripleStore "x:y") (partAt tripleReceiptBytes "decision") =
      ⟨1, "", "accepted", tripleJRef⟩ := by
    have h0 := completeTriple_decision "x:y"
    rw [completeTriple_scan_receipt "x:y"] at h0
    exact h0
  have hja : acceptedCheck (completeTripleStore b) tripleStmtBytes tripleJRef =
      acceptedCheck (completeTripleStore "x:y") tripleStmtBytes tripleJRef := by
    rw [completeTriple_acceptedCheck b hb, completeTriple_acceptedCheck_ref]
  dsimp only
  rw [hs, completeTriple_scan_stmt b, completeTriple_scan_stmt "x:y", hph, hbr,
      completeTriple_scan_receipt b, completeTriple_scan_receipt "x:y",
      hrr, hbb, hoi, hd, hd_ref]
  dsimp only
  rw [hja]

private theorem completeTriple_acceptedCheckWire (E₀ : ResolvedEnv) (fuel : Nat)
    (b : String) (hb : b ≠ "") :
    acceptedCheckWire E₀ fuel (completeTripleStore b) tripleStmtBytes tripleJRef =
      match runEnvWireStage E₀ fuel b with
      | .accepted _ => codeOk
      | .refusedJudgmentUntyped => codeRefuse "[rcic_cg014_judgment]"
      | .integrityUnbuiltStage => codeRefuse "[rcic_graph_admitted_unbuilt_stage]" := by
  unfold acceptedCheckWire
  rw [completeTriple_acceptedCheck b hb]
  dsimp only
  have hok : ¬ (codeOk.ok ≠ 1) := by decide
  rw [if_neg hok, completeTriple_scan_j, completeTriple_scan_env]

private theorem completeTriple_graphAdmittedWire (E₀ : ResolvedEnv)
    (b : String) (hb : b ≠ "") :
    graphAdmittedWire E₀ (completeTripleStore b)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      match runEnvWireStage E₀ 1 b with
      | .accepted _ => ⟨1, tripleOccurrence, ""⟩
      | .refusedJudgmentUntyped => eRefuse "[rcic_cg014_judgment]"
      | .integrityUnbuiltStage => eRefuse "[rcic_graph_admitted_unbuilt_stage]" := by
  rw [graphAdmittedWire_of_accepted E₀
        (completeTriple_graphAdmitted b hb)
        (completeTriple_decision b)]
  dsimp only
  have h1 : (1 : Int).toNat = 1 := rfl
  rw [h1, completeTriple_scan_stmt, completeTriple_acceptedCheckWire E₀ 1 b hb]
  cases runEnvWireStage E₀ 1 b <;> rfl

private theorem completeTriple_mutant_accepts
    (arm : ResolvedEnv → Nat → List StoreEntry → String → String → CodeOut)
    (b : String) (hb : b ≠ "")
    (ha : arm emptyEnv 1 (completeTripleStore b) tripleStmtBytes tripleJRef = codeOk) :
    graphAdmittedWireMutantWith arm emptyEnv (completeTripleStore b)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ := by
  unfold graphAdmittedWireMutantWith
  rw [completeTriple_graphAdmitted b hb]
  dsimp only
  rw [if_neg (by decide), completeTriple_decision b]
  dsimp only
  rw [if_pos rfl, completeTriple_scan_stmt]
  change (if (arm emptyEnv 1 (completeTripleStore b) tripleStmtBytes tripleJRef).ok = 1
    then ⟨1, tripleOccurrence, ""⟩ else
      eRefuse (arm emptyEnv 1 (completeTripleStore b) tripleStmtBytes tripleJRef).code) = _
  rw [ha]
  rfl

private theorem completeTriple_mutantP1b_arm (b : String) (hb : b ≠ "")
    (hs : runEnvWireStageMutantP1b emptyEnv 1 b =
      .accepted [.definitionD 0 1 1 (.sort (.succ .zero)) (.sort .zero)]) :
    acceptedCheckWireMutantP1b emptyEnv 1 (completeTripleStore b)
      tripleStmtBytes tripleJRef = codeOk := by
  unfold acceptedCheckWireMutantP1b
  rw [completeTriple_acceptedCheck b hb]
  dsimp only
  rw [if_neg (by decide), completeTriple_scan_j, completeTriple_scan_env, hs]

/-- Both isolated mutants wrongly accept actual stored environment bytes through
    the complete recorded-triple validator: P1a accepts the bare group, and P1b
    accepts each nonzero member/base arity combination. -/
theorem tooth_graphAdmittedWire_mutants_accept :
    graphAdmittedWireMutantP1a emptyEnv (completeTripleStore goodDefGroupBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ ∧
    graphAdmittedWireMutantP1b emptyEnv (completeTripleStore arity10GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ ∧
    graphAdmittedWireMutantP1b emptyEnv (completeTripleStore arity01GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ ∧
    graphAdmittedWireMutantP1b emptyEnv (completeTripleStore arity11GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ := by
  obtain ⟨_, hm10, hm01, hm11⟩ := tooth_mutantP1b_accepts_all_four_arities
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply completeTriple_mutant_accepts acceptedCheckWireMutantP1a goodDefGroupBytes (by decide)
    unfold acceptedCheckWireMutantP1a
    rw [completeTriple_acceptedCheck goodDefGroupBytes (by decide)]
    dsimp only
    rw [if_neg (by decide), completeTriple_scan_j, completeTriple_scan_env, mutantP1a_bare_stage]
  · exact completeTriple_mutant_accepts acceptedCheckWireMutantP1b arity10GroupImageBytes
      (by decide) (completeTriple_mutantP1b_arm _ (by decide) hm10)
  · exact completeTriple_mutant_accepts acceptedCheckWireMutantP1b arity01GroupImageBytes
      (by decide) (completeTriple_mutantP1b_arm _ (by decide) hm01)
  · exact completeTriple_mutant_accepts acceptedCheckWireMutantP1b arity11GroupImageBytes
      (by decide) (completeTriple_mutantP1b_arm _ (by decide) hm11)

/-- PIN (Complete Recorded Triple — Producer/Consumer Positive):
    With `admitted_env_ref` bound to the actual `rcic.env_image` digest
    `goodDefEnvImageRef` (`2bd4a913...`) and its `env_image_join` preimage
    `goodDefGroupImageBytes`, the complete `graphAdmittedWire` returns
    `⟨1, tripleOccurrence, ""⟩`. -/
theorem pin_graphAdmittedWire_completeTriple_goodDef :
    graphAdmittedWire emptyEnv (completeTripleStore goodDefGroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ := by
  rw [completeTriple_graphAdmittedWire emptyEnv goodDefGroupImageBytes (by decide),
      pin_runEnvGroupBytes_goodDef]

/-- PIN: `cg014_graphAdmittedWire_sound` instantiated at the complete producer-derived
    store `completeTripleStore goodDefGroupImageBytes`. -/
theorem pin_cg014_graphAdmittedWire_completeTriple_inhabited :
    (∃ jB tB, AcceptedBindingFacts (completeTripleStore goodDefGroupImageBytes)
      (storeScan (completeTripleStore goodDefGroupImageBytes) tripleStmtRef).bytes
      tripleJRef jB tB) ∧
    ∃ es ds,
      decodeEnvImageBytes? (1 : Int).toNat
        (storeScan (completeTripleStore goodDefGroupImageBytes)
          (partAt (storeScan (completeTripleStore goodDefGroupImageBytes) tripleJRef).bytes
            "admitted_env_ref")).bytes =
        some es ∧
      hasInductiveGroupW es = false ∧
      decodeSingletonWires? es = some ds ∧
      Nonempty (EnvWfT (applySingletons emptyEnv ds)) :=
  cg014_graphAdmittedWire_sound .empty
    pin_graphAdmittedWire_completeTriple_goodDef
    (completeTriple_decision goodDefGroupImageBytes)

/-- The old environment-blind complete validator accepts all three nonzero
    arity substitutions, complementing the isolated-mutant acceptance tooth. -/
theorem tooth_graphAdmitted_completeTriple_nonzero_arities_accept :
    graphAdmitted (completeTripleStore arity10GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ ∧
    graphAdmitted (completeTripleStore arity01GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ ∧
    graphAdmitted (completeTripleStore arity11GroupImageBytes)
      tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
      ⟨1, tripleOccurrence, ""⟩ :=
  ⟨completeTriple_graphAdmitted _ (by decide),
    completeTriple_graphAdmitted _ (by decide), completeTriple_graphAdmitted _ (by decide)⟩

/-- TOOTH (Complete Recorded Triple — Bare Group Refused, Group-Bearing Image
    Reaches `unbuilt_stage`, and Nonzero Arities Refused):
    Over `completeTripleStore`:
    (1) On the bare group `goodDefGroupBytes`, `graphAdmitted` WRONGLY ACCEPTS
        (`= ⟨1, tripleOccurrence, ""⟩`), whereas `graphAdmittedWire` REFUSES with
        `eRefuse "[rcic_cg014_judgment]"`.
    (2) On the producer-framed inductive-group image `indGroupImageBytes`,
        `graphAdmitted` WRONGLY ACCEPTS, whereas `graphAdmittedWire` surfaces
        `eRefuse "[rcic_graph_admitted_unbuilt_stage]"` (Annex 26.2a).
    (3) On the three nonzero-arity images (`1/0`, `0/1`, `1/1`),
        `graphAdmittedWire` REFUSES all three (old and isolated-mutant acceptance
        are proved in the companion teeth)
        with `eRefuse "[rcic_cg014_judgment]"`. -/
theorem tooth_graphAdmittedWire_completeTriple_bare_and_ind_and_arities :
    (graphAdmitted (completeTripleStore goodDefGroupBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       ⟨1, tripleOccurrence, ""⟩ ∧
     graphAdmittedWire emptyEnv (completeTripleStore goodDefGroupBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       eRefuse "[rcic_cg014_judgment]") ∧
    (graphAdmitted (completeTripleStore indGroupImageBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       ⟨1, tripleOccurrence, ""⟩ ∧
     graphAdmittedWire emptyEnv (completeTripleStore indGroupImageBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       eRefuse "[rcic_graph_admitted_unbuilt_stage]") ∧
    (graphAdmittedWire emptyEnv (completeTripleStore arity10GroupImageBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       eRefuse "[rcic_cg014_judgment]" ∧
     graphAdmittedWire emptyEnv (completeTripleStore arity01GroupImageBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       eRefuse "[rcic_cg014_judgment]" ∧
     graphAdmittedWire emptyEnv (completeTripleStore arity11GroupImageBytes)
       tripleStmtRef tripleReceiptRef tripleReceiptRef tripleOccurrence 1 =
       eRefuse "[rcic_cg014_judgment]") := by
  have hgaBare := completeTriple_graphAdmitted goodDefGroupBytes (by decide)
  have hgaInd := completeTriple_graphAdmitted indGroupImageBytes (by decide)
  obtain ⟨hr10, hr01, hr11⟩ := tooth_runEnvWireStage_refuses_nonzero_arities
  have hBareStage : runEnvWireStage emptyEnv 1 goodDefGroupBytes = .refusedJudgmentUntyped :=
    (tooth_bare_group_refused_by_envelope 1).2.2
  refine ⟨⟨hgaBare, ?_⟩, ⟨hgaInd, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [completeTriple_graphAdmittedWire emptyEnv goodDefGroupBytes (by decide), hBareStage]
  · rw [completeTriple_graphAdmittedWire emptyEnv indGroupImageBytes (by decide),
        tooth_runEnvGroupBytes_indGroup]
  · rw [completeTriple_graphAdmittedWire emptyEnv arity10GroupImageBytes (by decide), hr10]
  · rw [completeTriple_graphAdmittedWire emptyEnv arity01GroupImageBytes (by decide), hr01]
  · rw [completeTriple_graphAdmittedWire emptyEnv arity11GroupImageBytes (by decide), hr11]

end Rcic.GraphAdmitted.Blind

#print axioms Rcic.GraphAdmitted.Blind.typedJudgmentOk_congr
#print axioms Rcic.GraphAdmitted.Blind.acceptedCheck_env_congr
#print axioms Rcic.GraphAdmitted.Blind.jBytes_env
#print axioms Rcic.GraphAdmitted.Blind.blind_scan_j
#print axioms Rcic.GraphAdmitted.Blind.blind_env_scan
#print axioms Rcic.GraphAdmitted.Blind.codeOut_eq_ok
#print axioms Rcic.GraphAdmitted.Blind.blind_accepts_ref_ok
#print axioms Rcic.GraphAdmitted.Blind.blind_accepts_ref_code
#print axioms Rcic.GraphAdmitted.Blind.blind_accepts_ref
#print axioms Rcic.GraphAdmitted.Blind.blind_accepts
#print axioms Rcic.GraphAdmitted.Blind.pin_blind_accepts_two_images
#print axioms Rcic.GraphAdmitted.Blind.cg014_arm_refuted
#print axioms Rcic.GraphAdmitted.Blind.cg014_arm_forces_total_wf
#print axioms Rcic.GraphAdmitted.Blind.pin_cg014_arm_refuted_tooth
#print axioms Rcic.GraphAdmitted.Blind.pin_cg014_arm_fails_tooth
#print axioms Rcic.GraphAdmitted.Blind.isNone_eq_none
#print axioms Rcic.GraphAdmitted.Blind.admitSingletonWfT
#print axioms Rcic.GraphAdmitted.Blind.admitSingletonsWfT
#print axioms Rcic.GraphAdmitted.Blind.admitSingletons_sound
#print axioms Rcic.GraphAdmitted.Blind.envStageOk_iff
#print axioms Rcic.GraphAdmitted.Blind.acceptedCheckTyped_ok_iff
#print axioms Rcic.GraphAdmitted.Blind.cg014_acceptedCheckTyped_sound
#print axioms Rcic.GraphAdmitted.Blind.cg014_graphAdmittedTyped_sound
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckTyped_untyped
#print axioms Rcic.GraphAdmitted.Blind.pin_admitSingletonsB_goodEmptyTele
#print axioms Rcic.GraphAdmitted.Blind.pin_goodEmptyTele_wfT
#print axioms Rcic.GraphAdmitted.Blind.pin_admitSingletonsB_goodNatTele
#print axioms Rcic.GraphAdmitted.Blind.pin_goodNatTele_wfT
#print axioms Rcic.GraphAdmitted.Blind.tooth_admitSingletonsB_badDef_refused
#print axioms Rcic.GraphAdmitted.Blind.pin_acceptedCheckTyped_good_accepts
#print axioms Rcic.GraphAdmitted.Blind.pin_cg014_good_inhabited
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheck_vs_typed_badDef
#print axioms Rcic.GraphAdmitted.Blind.runEnvWireStage_accepted_iff
#print axioms Rcic.GraphAdmitted.Blind.acceptedCheckWire_ok_iff
#print axioms Rcic.GraphAdmitted.Blind.cg014_acceptedCheckWire_sound
#print axioms Rcic.GraphAdmitted.Blind.cg014_graphAdmittedWire_sound
#print axioms Rcic.GraphAdmitted.Blind.tooth_envWireStage_group_unbuilt_stage
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_group_never_accepts
#print axioms Rcic.GraphAdmitted.Blind.pin_runEnvWireStage_goodNat
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvWireStage_badDef
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvWireStage_indGroup
#print axioms Rcic.GraphAdmitted.Blind.valToLevelWire_levelWireToVal
#print axioms Rcic.GraphAdmitted.Blind.valsToLevelWires_map
#print axioms Rcic.GraphAdmitted.Blind.valToLevelWire_eq_some_iff
#print axioms Rcic.GraphAdmitted.Blind.levelWireToVal_of_valToLevelWire
#print axioms Rcic.GraphAdmitted.Blind.map_levelWireToVal_of_valsToLevelWires
#print axioms Rcic.GraphAdmitted.Blind.valToExprWire_exprWireToVal
#print axioms Rcic.GraphAdmitted.Blind.valToExprWire_eq_some_iff
#print axioms Rcic.GraphAdmitted.Blind.exprWireToVal_of_valToExprWire
#print axioms Rcic.GraphAdmitted.Blind.valueBytesAt_encVal
#print axioms Rcic.GraphAdmitted.Blind.valueBytesAt_reencodes
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_encExprWireScm
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_canonical
#print axioms Rcic.GraphAdmitted.Blind.cg014_acceptedCheckGroupBytes_sound
#print axioms Rcic.GraphAdmitted.Blind.cg014_graphAdmittedGroupBytes_sound
#print axioms Rcic.GraphAdmitted.Blind.toCore_int_and_rec_impossible
#print axioms Rcic.GraphAdmitted.Blind.tooth_no_coreTy_for_levelWireToVal
#print axioms Rcic.GraphAdmitted.Blind.tooth_no_coreTy_for_exprWireToVal
#print axioms Rcic.GraphAdmitted.Blind.tooth_scmWire_const_str_colon_collision
#print axioms Rcic.GraphAdmitted.Blind.secondChar_append
#print axioms Rcic.GraphAdmitted.Blind.secondChar_encExprWireScm
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_eq_none_of_noncanon
#print axioms Rcic.GraphAdmitted.Blind.tooth_decExprWireScm_noncanon_refused
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvWireStage_noncanon_refused
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_sort0
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_sort1
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_machPropId
#print axioms Rcic.GraphAdmitted.Blind.decExprWireScm_machPropIdPf
#print axioms Rcic.GraphAdmitted.Blind.decodeCheckedGroupBytes_of_parts
#print axioms Rcic.GraphAdmitted.Blind.tooth_bare_group_refused_by_envelope
#print axioms Rcic.GraphAdmitted.Blind.pin_parseEnvImageEnvelope_goodDef
#print axioms Rcic.GraphAdmitted.Blind.decodeCheckedGroupBytes_singleton_arity_zero
#print axioms Rcic.GraphAdmitted.Blind.tooth_decodeCheckedGroupBytes_nonzero_arity_refused
#print axioms Rcic.GraphAdmitted.Blind.pin_scmContentHashStr_goodDefGroupBytes
#print axioms Rcic.GraphAdmitted.Blind.pin_scmContentHashStr_goodDefGroupImageBytes
#print axioms Rcic.GraphAdmitted.Blind.pin_decodeCheckedGroupBytes_goodDef
#print axioms Rcic.GraphAdmitted.Blind.pin_decodeEnvImageBytes_goodDef
#print axioms Rcic.GraphAdmitted.Blind.pin_runEnvGroupBytes_goodDef
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvGroupBytes_badDef
#print axioms Rcic.GraphAdmitted.Blind.pin_scmContentHashStr_indGroupImageBytes
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvGroupBytes_indGroup
#print axioms Rcic.GraphAdmitted.Blind.pin_acceptedCheckWire_goodDef_accepts
#print axioms Rcic.GraphAdmitted.Blind.pin_cg014_acceptedCheckWire_goodDef_inhabited
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_opaque_bytes
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_noncanon
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_badDef
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_indGroup
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_bare_group
#print axioms Rcic.GraphAdmitted.Blind.tooth_runEnvWireStage_refuses_nonzero_arities
#print axioms Rcic.GraphAdmitted.Blind.tooth_mutantP1b_accepts_all_four_arities
#print axioms Rcic.GraphAdmitted.Blind.tooth_acceptedCheckWire_refuses_nonzero_arities
#print axioms Rcic.GraphAdmitted.Blind.graphAdmittedWire_of_accepted
#print axioms Rcic.GraphAdmitted.Blind.tripleJBytes_env
#print axioms Rcic.GraphAdmitted.Blind.tripleJBytes_assumptions
#print axioms Rcic.GraphAdmitted.Blind.tripleJBytes_typed
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_scan_j
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_scan_stmt
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_scan_env
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_acceptedCheck_ref
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_acceptedCheck
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_decision
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_graphAdmitted_ref
#print axioms Rcic.GraphAdmitted.Blind.completeTriple_graphAdmitted
#print axioms Rcic.GraphAdmitted.Blind.pin_graphAdmittedWire_completeTriple_goodDef
#print axioms Rcic.GraphAdmitted.Blind.pin_cg014_graphAdmittedWire_completeTriple_inhabited
#print axioms Rcic.GraphAdmitted.Blind.tooth_graphAdmittedWire_completeTriple_bare_and_ind_and_arities

#print axioms Rcic.GraphAdmitted.Blind.pin_envImageJoin_empty
#print axioms Rcic.GraphAdmitted.Blind.tooth_graphAdmittedWire_mutants_accept
#print axioms Rcic.GraphAdmitted.Blind.tooth_graphAdmitted_completeTriple_nonzero_arities_accept
