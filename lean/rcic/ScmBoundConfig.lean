/-
RCIC 06 §18 / §13 — the bound configuration, the bound final outcome and
the bound run result as R-CIC propositions over bound refs and canonical
bytes (#6310 M2, the K3c snapshot for kinds 22–24), pinned to the
`apps/rcic-scm-config` carrier that `ScmConfigAt` transcribes.

Owner text (06 §18, `docs/rcic/06_SCM_CORE_SEMANTICS.md:395-396`):

  ConfigAt(program_root_ref, config_ref, bytes) : Prop
  OutcomeAt(program_root_ref, outcome_ref, bytes) : Prop
  RunResultAt(program_root_ref, result_ref, bytes) : Prop

  the wire execution predicates "are R-CIC propositions over bound refs
  and canonical bytes. They never invoke an ambient object store" (06:402).

TRANSCRIPTION TABLE (06 §18 / §13 → Lean):

  CanonicalObjectAt(ref, bytes) at kind 22/23/24 → `CanonicalObjectAt`
        cfgSchema / finSchema / runSchema (01 §6, `RcicBoundObject`; the
        schema decode is `objDec`→`cxDec` at the input's own fuel, the
        `coreTypeSchema` convention of #6029 K3c)
  ConfigAt(P, r, b)   → `ConfigAt`: the bound object at kind 22 ∧ the
        decoded `CfgO` types at its stored result type (`cfgTy` own-fuel)
  OutcomeAt(P, r, b)  → `OutcomeAt`: kind 23 ∧ `finOk` of the `FinO`
  RunResultAt(P, r, b) → `RunResultAt`: kind 24 ∧ `runMemberOk` of the
        run member (a `.fin` under tag 0, a `.cfg` otherwise — `cxDec`
        bounds the tag `< 2`)
  BoundConfig / BoundOutcome / BoundRunResult → structures mirroring
        `BoundCoreType` (field names `config_ref`/`config_bytes`/`config_at`
        etc. verbatim)
  06 §13 raw configuration / §14 outcome reconstruction → `ctlToRaw`,
        `frmToRaw`, `cfgToRaw`, `finToRaw`, `runToRaw` (total over the
        already schema-checked wire forms; `runToRaw` is the kind-24
        member, `Option` because the member's shape is tag-dependent)

`P : RawProg` is the decoded bound program — what `bpProgram` returns as
`.bound p _` (under M1's `BoundCoreProgram` it is `P.prog`; M3 calls
`ConfigAt P.prog …`). `ScmConfigAt` is imported and called, never copied.

PINS (`apps/rcic-scm-config` corpus, 131 rows; bytes and digests are the
corpus' own `bytes3`/`ref3`): `ConfigAt` at rows 0, 23–25 (ret/eval/raise
controls and the three-frame chain), `OutcomeAt` at rows 110/112
(returned / raised), `RunResultAt` at rows 118/119 (done / suspended).
`cfgToRaw` is cross-checked by `rfl` (kernel equality — `Raw.Config` is
data) against the raw configurations the same rows mean in
`apps/rcic-scm-core` terms. Each predicate gets its tooth beside the
pins: a byte string that decodes but fails the carrier condition (row
30's `[rcic_scm_cf_result]`, row 107's wrong kind, row 111's
`[rcic_scm_cf_outcome]`, row 120's ill-typed done member) refutes the
proposition — `tooth_not_configAt` etc. carry the refutation, the
`#guard`s show the bytes satisfy their premises.

AGREEMENT: `configAt_of_cfAt` — an accepting `cfAt` decision at kind 22
and own fuel supplies a program `p` and a `ConfigAt p` at the same ref
and bytes. Agreement at an arbitrary accepting fuel needs the decoder's
and `cfgTy`'s fuel monotonicity — the #6029 K3c caveat, not assumed here.

NOT TRANSCRIBED (M3/M4): the typed/ intrinsic side of §13 (`Config`,
`Cont`, the `cfgToRaw`-to-`erase` agreement), `SCMStepAt`/`SCMRunsAt` and
the §19 bridge directions. `closure_claim` stays 0.
-/
import rcic.ScmConfigAt
import rcic.ScmMachineRaw

namespace Rcic.Scm.BoundCfg
open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.CfgWire Rcic.Scm.CfgAt Rcic.Scm.BoundProg Rcic.BoundObject

/-! ## 06 §13 raw reconstruction (the wire forms, already schema-checked) -/

/-- Wire control → raw control: the stored context item is a typing
    device, not part of the raw record. -/
def ctlToRaw (c : Tagged) : Raw.Ctl :=
  if c.tag = 0 then .evalC (valL (itm c.xs 1)) (asExpr (itm c.xs 2))
  else if c.tag = 1 then .retC (asVal (itm c.xs 1))
  else .raiseC (asStr (itm c.xs 1)) (asVal (itm c.xs 2))

/-- Wire frame → raw frame: tags 0–21 in the `frameKinds` order; the two
    leading type items drop out. A tag outside the schema's range is the
    `retF` default — it cannot satisfy `cfgTy` anyway. -/
def frmToRaw (f : Tagged) : Raw.Frame :=
  let xs := f.xs
  if f.tag = 0 then .letF (valL (itm xs 3)) (asExpr (itm xs 4))
  else if f.tag = 1 then .ifF (valL (itm xs 3)) (asExpr (itm xs 4)) (asExpr (itm xs 5))
  else if f.tag = 2 then .pairL (valL (itm xs 3)) (asExpr (itm xs 4))
  else if f.tag = 3 then .pairR (asVal (itm xs 2))
  else if f.tag = 4 then .fstF
  else if f.tag = 5 then .sndF
  else if f.tag = 6 then .injF (asNum (itm xs 2))
  else if f.tag = 7 then .matchF (valL (itm xs 3)) (exL (itm xs 4))
  else if f.tag = 8 then .recF (valL (itm xs 3)) (valL (itm xs 4)) (exL (itm xs 5))
  else if f.tag = 9 then .fieldF (asNum (itm xs 2))
  else if f.tag = 10 then .consH (valL (itm xs 3)) (asExpr (itm xs 4))
  else if f.tag = 11 then .consT (asVal (itm xs 2))
  else if f.tag = 12 then .foldL (valL (itm xs 3)) (asExpr (itm xs 4)) (asExpr (itm xs 5))
  else if f.tag = 13 then .foldI (valL (itm xs 4)) (valL (itm xs 5)) (asExpr (itm xs 6))
  else if f.tag = 14 then .fixI (valL (itm xs 3)) (asExpr (itm xs 4)) (asExpr (itm xs 5)) (asExpr (itm xs 6))
  else if f.tag = 15 then .fixL (valL (itm xs 3)) (asVal (itm xs 4)) (asExpr (itm xs 5)) (asExpr (itm xs 6))
  else if f.tag = 16 then .fixS (valL (itm xs 3)) (asVal (itm xs 4)) (asNum (itm xs 5)) (asNum (itm xs 6)) (asExpr (itm xs 7)) (asExpr (itm xs 8))
  else if f.tag = 17 then .fixT (valL (itm xs 3)) (asNum (itm xs 4)) (asNum (itm xs 5)) (asExpr (itm xs 6)) (asExpr (itm xs 7))
  else if f.tag = 18 then .argsF (valL (itm xs 3)) (asNum (itm xs 4)) (asStr (itm xs 5)) (asNum (itm xs 6)) (valL (itm xs 7)) (exL (itm xs 8))
  else if f.tag = 19 then .retF
  else if f.tag = 20 then .handleF (asStr (itm xs 2)) (valL (itm xs 4)) (asExpr (itm xs 5))
  else if f.tag = 21 then .raiseF (asStr (itm xs 2))
  else .retF

/-- Wire configuration → raw configuration (06 §13: the stored result
    type is a typing device; the raw record keeps control and frames). -/
def cfgToRaw (c : CfgO) : Raw.Config := ⟨ctlToRaw c.ctl, c.k.map frmToRaw⟩

/-- Wire final outcome → the raw final record `(kind, v, r)`, parallel to
    `ScmRawRelations.finalErase`. -/
def finToRaw (f : FinO) : Int × Val × String :=
  if f.tag = 0 then (1, asVal (itm f.xs 0), "")
  else (2, asVal (itm f.xs 1), asStr (itm f.xs 0))

/-- The kind-24 member reconstructed: a done run holds the raw final
    record, a suspended run the raw configuration. -/
inductive RawRunResult where
  | done (kind : Int) (v : Val) (r : String)
  | suspended (c : Raw.Config)
  deriving BEq

def runToRaw (tag : Int) (m : CX) : Option RawRunResult :=
  if tag = 0 then
    match m with
    | .fin f => some (.done (finToRaw f).1 (finToRaw f).2.1 (finToRaw f).2.2)
    | _ => none
  else
    match m with
    | .cfg c => some (.suspended (cfgToRaw c))
    | _ => none

/-! ## The object schemas (01 §6 over the kinds 22/23/24) -/

/-- Kind 22 (configuration): decode is `objDec`→`cxDec` at the input's
    own fuel; (4) is class 3, kind 22; (5) is whole-input consumption. -/
def cfgSchema : ObjSchema where
  Obj := CfgO
  decode b := match objDec b.length 22 b with
    | .ok (.cx (.cfg c), _) => some c
    | _ => none
  encode c := objEnc (.cx (.cfg c))
  exactFields b := match objDec b.length 22 b with
    | .ok (_, p) => p == b.length
    | _ => false
  consistent c k _ := c == 3 && k == 22

/-- Kind 23 (final outcome). -/
def finSchema : ObjSchema where
  Obj := FinO
  decode b := match objDec b.length 23 b with
    | .ok (.cx (.fin f), _) => some f
    | _ => none
  encode f := objEnc (.cx (.fin f))
  exactFields b := match objDec b.length 23 b with
    | .ok (_, p) => p == b.length
    | _ => false
  consistent c k _ := c == 3 && k == 23

/-- Kind 24 (run result): the object is the run tag and its member `CX`. -/
def runSchema : ObjSchema where
  Obj := Int × CX
  decode b := match objDec b.length 24 b with
    | .ok (.cx (.run tag m), _) => some (tag, m)
    | _ => none
  encode rm := objEnc (.cx (.run rm.1 rm.2))
  exactFields b := match objDec b.length 24 b with
    | .ok (_, p) => p == b.length
    | _ => false
  consistent c k _ := c == 3 && k == 24

/-! ## The §18 propositions -/

/-- 06 §18 `ConfigAt(program_root_ref, config_ref, bytes)` (06:395): the
    bound object at kind 22 (`CanonicalObjectAt`: decode, whole input,
    re-encode, class/kind, derived digest) and the decoded configuration
    typed at its stored result type under the program — `cfgTy` at the
    input's own fuel. `P` is the decoded bound program. -/
def ConfigAt (P : RawProg) (r : Ref) (b : String) : Prop :=
  CanonicalObjectAt cfgSchema r b ∧
  ∃ c : CfgO, cfgSchema.decode b = some c ∧ cfgTy b.length P c = .ok c.t

/-- 06 §18 `OutcomeAt(program_root_ref, outcome_ref, bytes)` (06:396):
    the bound object at kind 23 and `finOk` of the decoded outcome. -/
def OutcomeAt (P : RawProg) (r : Ref) (b : String) : Prop :=
  CanonicalObjectAt finSchema r b ∧
  ∃ f : FinO, finSchema.decode b = some f ∧ finOk P f = true

/-- The kind-24 member condition of `cfCheck`: tag 0 wants a `.fin`
    member that is `finOk`; another tag wants a `.cfg` member that
    `cfgTy`s (the decoder bounds the tag to 0/1). -/
def runMemberOk (P : RawProg) (fuel : Int) (tag : Int) (m : CX) : Prop :=
  match m with
  | .fin f => tag = 0 ∧ finOk P f = true
  | .cfg c => tag ≠ 0 ∧ cfgTy fuel P c = .ok c.t
  | .run _ _ => False

/-- 06 §18 `RunResultAt(program_root_ref, result_ref, bytes)` (06:396):
    the bound object at kind 24 and its member well-formed. -/
def RunResultAt (P : RawProg) (r : Ref) (b : String) : Prop :=
  CanonicalObjectAt runSchema r b ∧
  ∃ tag : Int, ∃ m : CX, runSchema.decode b = some (tag, m) ∧
    runMemberOk P b.length tag m

/-- 06 §18 bound configuration, mirroring `BoundCoreType`. -/
structure BoundConfig (P : RawProg) where
  config_ref : Ref
  config_bytes : String
  config_at : ConfigAt P config_ref config_bytes

/-- 06 §18 bound final outcome. -/
structure BoundOutcome (P : RawProg) where
  outcome_ref : Ref
  outcome_bytes : String
  outcome_at : OutcomeAt P outcome_ref outcome_bytes

/-- 06 §18 bound run result. -/
structure BoundRunResult (P : RawProg) where
  run_result_ref : Ref
  run_result_bytes : String
  run_result_at : RunResultAt P run_result_ref run_result_bytes

/-! ## Executable shadows and their agreement with the propositions

The decoder and the digest are extern-backed, so byte-level claims are
decided natively (`#guard`); the shadows are the executable halves of the
propositions, and the `*_iff` theorems carry the equivalence the pins
exercise. -/

def cfgOkB (P : RawProg) (b : String) : Bool :=
  match cfgSchema.decode b with
  | some c => (cfgTy b.length P c).isOk
  | none => false

def configAtB (P : RawProg) (r : Ref) (b : String) : Bool :=
  decide (CanonicalObjectAt cfgSchema r b) && cfgOkB P b

def finOkB (P : RawProg) (b : String) : Bool :=
  match finSchema.decode b with
  | some f => finOk P f
  | none => false

def outcomeAtB (P : RawProg) (r : Ref) (b : String) : Bool :=
  decide (CanonicalObjectAt finSchema r b) && finOkB P b

def runMemberOkB (P : RawProg) (fuel : Int) (tag : Int) (m : CX) : Bool :=
  match m with
  | .fin f => tag == 0 && finOk P f
  | .cfg c => tag != 0 && (cfgTy fuel P c).isOk
  | .run _ _ => false

def runOkB (P : RawProg) (b : String) : Bool :=
  match runSchema.decode b with
  | some (tag, m) => runMemberOkB P b.length tag m
  | none => false

def runResultAtB (P : RawProg) (r : Ref) (b : String) : Bool :=
  decide (CanonicalObjectAt runSchema r b) && runOkB P b

theorem cfgOkB_iff (P : RawProg) (b : String) :
    cfgOkB P b = true ↔ ∃ c : CfgO, cfgSchema.decode b = some c ∧
      cfgTy b.length P c = .ok c.t := by
  unfold cfgOkB
  cases cfgSchema.decode b with
  | none => dsimp only; simp
  | some c =>
    dsimp only
    constructor
    · intro h
      cases hty : cfgTy b.length P c with
      | error e =>
        rw [hty] at h
        exact absurd (show false = true from h) (by decide)
      | ok t =>
        obtain ⟨ht, -⟩ := cfgTy_ok_result b.length P c t hty
        subst ht
        exact ⟨c, rfl, hty⟩
    · rintro ⟨c', hd', hty'⟩
      injection hd' with hc'
      subst hc'
      rw [hty']
      rfl

theorem configAt_iff (P : RawProg) (r : Ref) (b : String) :
    ConfigAt P r b ↔ configAtB P r b = true := by
  unfold ConfigAt configAtB
  rw [Bool.and_eq_true, decide_eq_true_eq, cfgOkB_iff]

theorem finOkB_iff (P : RawProg) (b : String) :
    finOkB P b = true ↔ ∃ f : FinO, finSchema.decode b = some f ∧
      finOk P f = true := by
  unfold finOkB
  cases finSchema.decode b with
  | none => dsimp only; simp
  | some f =>
    dsimp only
    constructor
    · intro h
      exact ⟨f, rfl, h⟩
    · rintro ⟨f', hd', h⟩
      injection hd' with hf'
      subst hf'
      exact h

theorem outcomeAt_iff (P : RawProg) (r : Ref) (b : String) :
    OutcomeAt P r b ↔ outcomeAtB P r b = true := by
  unfold OutcomeAt outcomeAtB
  rw [Bool.and_eq_true, decide_eq_true_eq, finOkB_iff]

theorem runMemberOkB_iff (P : RawProg) (fuel : Int) (tag : Int) (m : CX) :
    runMemberOkB P fuel tag m = true ↔ runMemberOk P fuel tag m := by
  cases m with
  | cfg c =>
    show (tag != 0 && (cfgTy fuel P c).isOk) = true ↔
      (tag ≠ 0 ∧ cfgTy fuel P c = .ok c.t)
    constructor
    · intro h
      obtain ⟨ht, hty⟩ := Eq.mp (Bool.and_eq_true _ _) h
      refine ⟨?_, ?_⟩
      · intro heq
        rw [heq] at ht
        simp at ht
      · cases h2 : cfgTy fuel P c with
        | error e =>
          rw [h2] at hty
          exact absurd (show false = true from hty) (by decide)
        | ok t =>
          obtain ⟨hc, -⟩ := cfgTy_ok_result fuel P c t h2
          subst hc
          rfl
    · rintro ⟨ht, hty⟩
      refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
      · exact bne_iff_ne.mpr ht
      · rw [hty]
        rfl
  | fin f =>
    show (tag == 0 && finOk P f) = true ↔ (tag = 0 ∧ finOk P f = true)
    constructor
    · intro h
      obtain ⟨ht, hf⟩ := Eq.mp (Bool.and_eq_true _ _) h
      exact ⟨beq_iff_eq.mp ht, hf⟩
    · rintro ⟨ht, hf⟩
      subst ht
      exact Eq.mpr (Bool.and_eq_true _ _) ⟨rfl, hf⟩
  | run t2 m2 =>
    show false = true ↔ False
    simp

theorem runOkB_iff (P : RawProg) (b : String) :
    runOkB P b = true ↔ ∃ tag : Int, ∃ m : CX, runSchema.decode b = some (tag, m) ∧
      runMemberOk P b.length tag m := by
  unfold runOkB
  cases runSchema.decode b with
  | none => dsimp only; simp
  | some v =>
    obtain ⟨tag, m⟩ := v
    dsimp only
    rw [runMemberOkB_iff]
    constructor
    · intro h
      exact ⟨tag, m, rfl, h⟩
    · rintro ⟨t', m', hd', h⟩
      simp at hd'
      obtain ⟨rfl, rfl⟩ := hd'
      exact h

theorem runResultAt_iff (P : RawProg) (r : Ref) (b : String) :
    RunResultAt P r b ↔ runResultAtB P r b = true := by
  unfold RunResultAt runResultAtB
  rw [Bool.and_eq_true, decide_eq_true_eq, runOkB_iff]

/-! ## Teeth: decodable inputs the carrier condition refuses -/

/-- `configAtB = false` refutes `ConfigAt`: a byte string that decodes
    but fails the bound-object or the `cfgTy` condition is not a bound
    configuration — the proposition is not inhabited by every decodable
    input. -/
theorem tooth_not_configAt {P : RawProg} {r : Ref} {b : String}
    (h : configAtB P r b = false) : ¬ ConfigAt P r b :=
  fun hc => absurd ((configAt_iff P r b).mp hc) (by rw [h]; decide)

theorem tooth_not_outcomeAt {P : RawProg} {r : Ref} {b : String}
    (h : outcomeAtB P r b = false) : ¬ OutcomeAt P r b :=
  fun hc => absurd ((outcomeAt_iff P r b).mp hc) (by rw [h]; decide)

theorem tooth_not_runResultAt {P : RawProg} {r : Ref} {b : String}
    (h : runResultAtB P r b = false) : ¬ RunResultAt P r b :=
  fun hc => absurd ((runResultAt_iff P r b).mp hc) (by rw [h]; decide)

/-! ## Agreement with the carrier (at the input's own fuel) -/

/-- `objBind`'s `ok` is 0 or 1: every leaf is `bpOk` or `bpRefuse`. -/
theorem objBind_ok_01 (fuel : Int) (r : Ref) (k : Int) (b : String) :
    (objBind fuel r k b).ok = 0 ∨ (objBind fuel r k b).ok = 1 := by
  unfold objBind
  by_cases h1 : r.cls ≠ 3
  · rw [if_pos h1]
    exact .inl rfl
  · rw [if_neg h1]
    by_cases h2 : r.kind ≠ k
    · rw [if_pos h2]
      exact .inl rfl
    · rw [if_neg h2]
      cases objDec fuel k b with
      | error e => exact .inl rfl
      | ok v =>
        obtain ⟨o, p⟩ := v
        dsimp only
        by_cases h3 : p ≠ b.length
        · rw [if_pos h3]
          exact .inl rfl
        · rw [if_neg h3]
          by_cases h4 : objEnc o ≠ b
          · rw [if_pos h4]
            exact .inl rfl
          · rw [if_neg h4]
            by_cases h5 : Rcic.TypedRef.deriveDigest 3 k b ≠ r.digest
            · rw [if_pos h5]
              exact .inl rfl
            · rw [if_neg h5]
              exact .inr rfl

/-- `objBind_accepts`, plus the result's object field: an accepting
    `objBind` returns `bpOk` of the decoded object. -/
theorem objBind_accepts_x (fuel : Int) (r : Ref) (k : Int) (b : String)
    (h : (objBind fuel r k b).ok = 1) :
    ∃ o q, objDec fuel k b = .ok (o, q) ∧ q = b.length ∧ objEnc o = b ∧
      (objBind fuel r k b).x = o := by
  obtain ⟨hc, hk, ⟨o, q, hd, hq, he⟩, hdg⟩ := objBind_accepts fuel r k b h
  refine ⟨o, q, hd, hq, he, ?_⟩
  unfold objBind
  rw [if_neg (not_not_intro hc), if_neg (not_not_intro hk), hd]
  dsimp only
  rw [if_neg (not_not_intro hq), if_neg (not_not_intro he), if_neg (not_not_intro hdg)]
  rfl

/-- An accepting `cfAt` at kind 22 yields a bound program and a decoded
    configuration typing at its stored result type. -/
theorem cfAt_accepts_cfg (fuel : Int) (profile : String) (rr : Ref) (rb : String)
    (br : Ref) (bb : String) (orf : Ref) (ob : String)
    (h : (cfAt fuel profile rr rb br bb 22 orf ob).ok = 1) :
    ∃ p : RawProg, ∃ c : CfgO, (objBind fuel orf 22 ob).ok = 1 ∧
      objDec fuel 22 ob = .ok (.cx (.cfg c), ob.length) ∧
      objEnc (.cx (.cfg c)) = ob ∧
      cfgTy fuel p c = .ok c.t := by
  unfold cfAt at h
  simp only [] at h
  split at h
  · exact absurd (show (0 : Int) = 1 from h) (by decide)
  · rename_i hpr
    split at h
    · exact absurd (show (0 : Int) = 1 from h) (by decide)
    · rename_i ho
      cases hpx : (bpProgram fuel profile rr rb br bb).x <;>
        cases hox : (objBind fuel orf 22 ob).x <;>
          rw [hpx, hox] at h <;>
          first | (exact absurd (show (0 : Int) = 1 from h) (by decide)) | skip
      rename_i p t x
      have hbind : (objBind fuel orf 22 ob).ok = 1 :=
        (objBind_ok_01 fuel orf 22 ob).resolve_left ho
      change (cfCheck fuel p 22 x).ok = 1 at h
      unfold cfCheck at h
      rw [if_pos rfl] at h
      cases x with
      | cfg c =>
        dsimp only at h
        cases hty : cfgTy fuel p c with
        | error e =>
          rw [hty] at h
          exact absurd (show (0 : Int) = 1 from h) (by decide)
        | ok t' =>
          rw [hty] at h
          obtain ⟨ht, -⟩ := cfgTy_ok_result fuel p c t' hty
          rw [ht] at hty
          obtain ⟨o, q, hd, hq, he, hx⟩ := objBind_accepts_x fuel orf 22 ob hbind
          have hoc : o = .cx (.cfg c) := (hox ▸ hx).symm
          rw [hoc] at hd he
          rw [hq] at hd
          exact ⟨p, c, hbind, hd, he, hty⟩
      | fin f => exact absurd (show (0 : Int) = 1 from h) (by decide)
      | run tag m => exact absurd (show (0 : Int) = 1 from h) (by decide)

/-- `configAt_of_cfAt` (06 §18 / M2): an accepting `cfAt` decision at
    kind 22 at the input's own fuel supplies a decoded bound program `p`
    and `ConfigAt p` at the same ref and bytes — the proposition the
    carrier decides. -/
theorem configAt_of_cfAt (profile : String) (rr : Ref) (rb : String)
    (br : Ref) (bb : String) (r : Ref) (b : String)
    (h : (cfAt b.length profile rr rb br bb 22 r b).ok = 1) :
    ∃ p : RawProg, ConfigAt p r b := by
  obtain ⟨p, c, hbind, hd, he, hty⟩ := cfAt_accepts_cfg _ _ _ _ _ _ _ _ h
  obtain ⟨hc, hk, -, hdg⟩ := objBind_accepts _ _ _ _ hbind
  have hdS : cfgSchema.decode b = some c := by
    show (match objDec b.length 22 b with
      | .ok (.cx (.cfg c'), _) => some c'
      | _ => none) = some c
    rw [hd]
  refine ⟨p, ⟨?_, ?_, ?_⟩, c, hdS, hty⟩
  · rw [hdS]
    dsimp only
    refine ⟨he, ?_⟩
    show (r.cls == 3 && r.kind == 22) = true
    rw [hc, hk]
    rfl
  · show Rcic.TypedRef.deriveDigest r.cls.toNat r.kind b = r.digest
    rw [hc, hk]
    exact hdg
  · show (match objDec b.length 22 b with
        | .ok (_, p') => p' == b.length
        | _ => false) = true
    rw [hd]
    dsimp only
    simp

end Rcic.Scm.BoundCfg

/-! ## Pins: apps/rcic-scm-config/rcic_scm_config_corpus.json

Bytes and digests are the corpus' own `bytes3`/`ref3` (kind-22/23/24
objects and their bound refs); the decoded objects are the hand-built
`CfgO`/`FinO`/`CX` terms the corpus rows mean, linked to the bytes by the
decode `==` checks. The program is `ScmBoundProgram.Pins.PROG` — what
`bpProgram` yields for the corpus' root/bundle pair (the K3b segment's
row-23 pin). The `rfl` cross-checks of `cfgToRaw`/`finToRaw`/`runToRaw`
reduce in the kernel — wire objects and `Raw.Config` are data; the
decoder and the digest are extern-backed, so byte-level claims are
`#guard`s (native evaluation, the #6029 K3c convention). -/

namespace Rcic.Scm.BoundCfg.Pins
open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.CfgWire Rcic.Scm.CfgAt Rcic.Scm.CfgAt.Pins
  Rcic.Scm.BoundProg Rcic.Scm.BoundCfg Rcic.BoundObject

/-- The corpus program (the `fAdd`/`fCall` group, catalog, entry 1). -/
def PROG : RawProg := Rcic.Scm.BoundProg.Pins.PROG

/-- A class-3 ref with the corpus' stated digest — equal by construction
    to `rf b k` (the corpus digests are `rcic.derive` outputs; checked
    row for row against `Rcic.TypedRef.deriveDigest`). -/
def cref (_b : String) (k : Int) (d : String) : Ref := ⟨3, k, d⟩

-- the decoded corpus objects
def cfgO0 : CfgO := ⟨I, ctlRet I (iv 5), [fr 0 I I (nog ++ [E add01])]⟩
def cfgO23 : CfgO := ⟨I, ctlEval [I] [iv 4] add01, []⟩
def cfgO24 : CfgO := ⟨I, ctlRaise I "range_violation" (iv 9),
  [fr 20 I I ([Ss "range_violation"] ++ nog ++ [E (v 0)])]⟩
def cfgO25 : CfgO := ⟨I, ctlRet I (iv 1),
  [fr 2 I (.pair I I) (nog ++ [E (li 2)]), fr 4 (.pair I I) I [], fr 19 I I []]⟩
def finO110 : FinO := ⟨I, 0, [Vv (.i 5)]⟩
def finO112 : FinO := ⟨I, 1, [Ss "range_violation", Vv (.i 9)]⟩

-- the corpus bytes3 / ref3
def B0 : String := "Ci6:1;iI5;1;24:0;ii0;0;f3:add2;10;0I1;i"
def B23 : String := "Ci26:0;1;i1;I4;f3:add2;10;0I1;i0;"
def B24 : String := "Ci24:2;i15:range_violationI9;1;30:20;ii15:range_violation0;0;10;"
def B25 : String := "Ci6:1;iI1;3;15:2;iPii0;0;0I2;i6:4;Piii5:19;ii"
def B30 : String := "Cb6:1;iI5;1;24:0;ii0;0;f3:add2;10;0I1;i"
def B107 : String := "Ci6:1;iI5;1;5:19;ii"
def B110 : String := "Fi0;I5;"
def B111 : String := "Fi0;B1;"
def B112 : String := "Fi1;15:range_violationI9;"
def B118 : String := "D0;7:Fi0;I5;"
def B119 : String := "D1;39:Ci6:1;iI5;1;24:0;ii0;0;f3:add2;10;0I1;i"
def B120 : String := "D0;7:Fi0;B1;"

def R0 : Ref := cref B0 22 "d3b31b1c23303e8fd8ab27cc6ba2f0264cefb1cd50d69dd50d0574a5705b10ef"
def R23 : Ref := cref B23 22 "e84a6bcde6d378e8c72ff334704b26db23d2736c96236f849061abac7a22b0dc"
def R24 : Ref := cref B24 22 "a9162bd580045a30ab454a13b7ad110a085cd92039261f7a03d310f2b4e39eac"
def R25 : Ref := cref B25 22 "413a128a5ffd2c8657e37ac1b12e7673ea2294b517cabf63cc1073cdbd2ae07b"
def R107 : Ref := cref B107 23 "948eb22745dcd72cad33f22a5a4a58e8f3b2810ab4f87b06b04e1c1b07224451"
def R110 : Ref := cref B110 23 "c90dc3ece6c1bf37db6182e391b835bf18927e182da6aa39b4a3791b1d69b168"
def R111 : Ref := cref B111 23 "7b461bc1a13f15ac43f7558274906d2771c5de80153b43ee158b156ca9fa23c9"
def R112 : Ref := cref B112 23 "8fe15a88f0040d93586d5eebb8f93586d3219c7536845e66daf3932e53c278d6"
def R118 : Ref := cref B118 24 "0a7d8b3bb13e29a18535fb974257b96b3c1e2030e331b5a647a8705e5051d735"
def R119 : Ref := cref B119 24 "50bd678fcff004a1146afdf43351d30db4e3aa6e92fdf553e493981e250b1670"
def R120 : Ref := cref B120 24 "23ea4d924a8c53bf0bad0e825f6fb3bbffb1c6eb6f79950aa6c6474e2705084d"

/-- The program root/bundle refs of the corpus rows. -/
def RRB : Ref := CfgAt.Pins.rf CfgAt.Pins.RB 20
def RBB : Ref := CfgAt.Pins.rf CfgAt.Pins.BB 21

/-! ### Decode links: the corpus bytes decode to the hand-built objects -/

-- row 0 a returned value in a let frame (the canonical encoding of `r0`)
#guard (decCfg B0.length B0).toOption == some (cfgO0, B0.length)
#guard cfgSchema.encode cfgO0 == B0
#guard Rcic.TypedRef.deriveDigest 3 22 B0 == R0.digest
-- row 23 an evaluating control
#guard (decCfg B23.length B23).toOption == some (cfgO23, B23.length)
#guard Rcic.TypedRef.deriveDigest 3 22 B23 == R23.digest
-- row 24 a raising control under a matching handle frame
#guard (decCfg B24.length B24).toOption == some (cfgO24, B24.length)
#guard Rcic.TypedRef.deriveDigest 3 22 B24 == R24.digest
-- row 25 a three-frame chain
#guard (decCfg B25.length B25).toOption == some (cfgO25, B25.length)
#guard Rcic.TypedRef.deriveDigest 3 22 B25 == R25.digest
-- row 110 a returned final outcome
#guard (decFin B110.length B110).toOption == some (finO110, B110.length)
#guard Rcic.TypedRef.deriveDigest 3 23 B110 == R110.digest
-- row 112 a raised final outcome with its catalog payload
#guard (decFin B112.length B112).toOption == some (finO112, B112.length)
#guard Rcic.TypedRef.deriveDigest 3 23 B112 == R112.digest
-- row 118 a done run result holding row 110's outcome
#guard (objDec B118.length 24 B118).toOption == some (.cx (.run 0 (.fin finO110)), B118.length)
#guard Rcic.TypedRef.deriveDigest 3 24 B118 == R118.digest
-- row 119 a suspended run result holding row 0's configuration
#guard (objDec B119.length 24 B119).toOption == some (.cx (.run 1 (.cfg cfgO0)), B119.length)
#guard Rcic.TypedRef.deriveDigest 3 24 B119 == R119.digest

/-! ### The propositions at the corpus rows -/

-- row 0's ref/bytes are a bound configuration under the corpus program
#guard decide (CanonicalObjectAt cfgSchema R0 B0)
#guard configAtB PROG R0 B0
-- rows 23–25 likewise (evaluating / raising controls, the frame chain)
#guard configAtB PROG R23 B23
#guard configAtB PROG R24 B24
#guard configAtB PROG R25 B25
-- rows 110/112 are bound final outcomes
#guard decide (CanonicalObjectAt finSchema R110 B110)
#guard outcomeAtB PROG R110 B110
#guard outcomeAtB PROG R112 B112
-- rows 118/119 are bound run results
#guard decide (CanonicalObjectAt runSchema R118 B118)
#guard runResultAtB PROG R118 B118
#guard runResultAtB PROG R119 B119

/-! ### Teeth: one per predicate, beside its pins -/

-- tooth (ConfigAt, carrier condition): row 30's bytes decode and bind at
-- kind 22, but the stored result type is bool while the frame chain
-- types at i64 (`[rcic_scm_cf_result]`) — `ConfigAt` is refuted.
#guard (decCfg B30.length B30).isOk
#guard decide (CanonicalObjectAt cfgSchema (CfgAt.Pins.rf B30 22) B30)
#guard configAtB PROG (CfgAt.Pins.rf B30 22) B30 == false
-- tooth (ConfigAt, wrong kind): row 107's ref names kind 23 for kind-22
-- bytes — the bound-object condition fails even though the bytes decode.
#guard (decCfg B107.length B107).isOk
#guard configAtB PROG R107 B107 == false
-- tooth (OutcomeAt): row 111's returned payload is a bool stored as i64
-- (`[rcic_scm_cf_outcome]`) — `OutcomeAt` refuted.
#guard (decFin B111.length B111).isOk
#guard outcomeAtB PROG R111 B111 == false
-- tooth (RunResultAt): row 120's done member is row 111's ill-typed
-- outcome (`[rcic_scm_cf_outcome]`) — `RunResultAt` refuted.
#guard (objDec B120.length 24 B120).isOk
#guard runResultAtB PROG R120 B120 == false

/-! ### `*ToRaw` cross-checks (kernel `rfl` — the objects are data) -/

-- ctlToRaw: eval / ret / raise controls
theorem ctlToRaw_eval : ctlToRaw (ctlEval [I] [iv 4] add01) = .evalC [.i 4] add01 := rfl
theorem ctlToRaw_ret : ctlToRaw (ctlRet I (iv 5)) = .retC (.i 5) := rfl
theorem ctlToRaw_raise : ctlToRaw (ctlRaise I "bad_input" (bv 1)) = .raiseC "bad_input" (.b 1) := rfl

-- frmToRaw across the frame tags (rows' frames)
theorem frmToRaw_let : frmToRaw (fr 0 I I (nog ++ [E add01])) = .letF [] add01 := rfl
theorem frmToRaw_pairL : frmToRaw (fr 2 I (.pair I I) (nog ++ [E (li 2)])) = .pairL [] (li 2) := rfl
theorem frmToRaw_fst : frmToRaw (fr 4 (.pair I I) I []) = .fstF := rfl
theorem frmToRaw_inj : frmToRaw (fr 6 I (.sum [I, B]) [N 0]) = .injF 0 := rfl
theorem frmToRaw_fixS : frmToRaw (fr 16 B FX (nog ++ [Vv (iv 0), N 3, N 0, E stop, E step])) =
    .fixS [] (.i 0) 3 0 stop step := rfl
theorem frmToRaw_args : frmToRaw (fr 18 I I (nog ++ [N 0, Ss "add", N 0, VL [], EL [li 2]])) =
    .argsF [] 0 "add" 0 [] [li 2] := rfl
theorem frmToRaw_ret : frmToRaw (fr 19 I I []) = .retF := rfl
theorem frmToRaw_handle : frmToRaw (fr 20 I I ([Ss "range_violation"] ++ nog ++ [E (v 0)])) =
    .handleF "range_violation" [] (.var 0) := rfl

-- cfgToRaw against the corpus' decoded configurations
/-- Row 0's configuration is the raw ret-5 under one let frame. -/
theorem cfgToRaw_row0 : cfgToRaw cfgO0 = ⟨.retC (.i 5), [.letF [] add01]⟩ := rfl
/-- Row 23's evaluating control. -/
theorem cfgToRaw_row23 : cfgToRaw cfgO23 = ⟨.evalC [.i 4] add01, []⟩ := rfl
/-- Row 24's raising control under its handle frame. -/
theorem cfgToRaw_row24 : cfgToRaw cfgO24 =
    ⟨.raiseC "range_violation" (.i 9), [.handleF "range_violation" [] (.var 0)]⟩ := rfl
/-- Row 25's three-frame chain. -/
theorem cfgToRaw_row25 : cfgToRaw cfgO25 =
    ⟨.retC (.i 1), [.pairL [] (li 2), .fstF, .retF]⟩ := rfl

-- finToRaw, parallel to `finalErase`
/-- Row 110's returned outcome is the raw final record `(1, 5, "")`. -/
theorem finToRaw_row110 : finToRaw finO110 = (1, .i 5, "") := rfl
/-- Row 112's raised outcome is `(2, 9, "range_violation")`. -/
theorem finToRaw_row112 : finToRaw finO112 = (2, .i 9, "range_violation") := rfl

-- runToRaw, the kind-24 member
/-- Row 118's done result is the raw final record of row 110. -/
theorem runToRaw_row118 : runToRaw 0 (.fin finO110) = some (.done 1 (.i 5) "") := rfl
/-- Row 119's suspended result is row 0's raw configuration. -/
theorem runToRaw_row119 : runToRaw 1 (.cfg cfgO0) =
    some (.suspended ⟨.retC (.i 5), [.letF [] add01]⟩) := rfl

/-! ### `cfAt` at own fuel accepts row 0 (the `configAt_of_cfAt` premise) -/

#guard (cfAt B0.length "SCM-Core-0" RRB CfgAt.Pins.RB RBB CfgAt.Pins.BB 22 R0 B0).ok == 1

end Rcic.Scm.BoundCfg.Pins

#print axioms Rcic.Scm.BoundCfg.cfgOkB_iff
#print axioms Rcic.Scm.BoundCfg.configAt_iff
#print axioms Rcic.Scm.BoundCfg.finOkB_iff
#print axioms Rcic.Scm.BoundCfg.outcomeAt_iff
#print axioms Rcic.Scm.BoundCfg.runMemberOkB_iff
#print axioms Rcic.Scm.BoundCfg.runOkB_iff
#print axioms Rcic.Scm.BoundCfg.runResultAt_iff
#print axioms Rcic.Scm.BoundCfg.tooth_not_configAt
#print axioms Rcic.Scm.BoundCfg.tooth_not_outcomeAt
#print axioms Rcic.Scm.BoundCfg.tooth_not_runResultAt
#print axioms Rcic.Scm.BoundCfg.objBind_ok_01
#print axioms Rcic.Scm.BoundCfg.objBind_accepts_x
#print axioms Rcic.Scm.BoundCfg.cfAt_accepts_cfg
#print axioms Rcic.Scm.BoundCfg.configAt_of_cfAt
#print axioms Rcic.Scm.BoundCfg.Pins.ctlToRaw_eval
#print axioms Rcic.Scm.BoundCfg.Pins.ctlToRaw_ret
#print axioms Rcic.Scm.BoundCfg.Pins.ctlToRaw_raise
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_let
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_pairL
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_fst
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_inj
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_fixS
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_args
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_ret
#print axioms Rcic.Scm.BoundCfg.Pins.frmToRaw_handle
#print axioms Rcic.Scm.BoundCfg.Pins.cfgToRaw_row0
#print axioms Rcic.Scm.BoundCfg.Pins.cfgToRaw_row23
#print axioms Rcic.Scm.BoundCfg.Pins.cfgToRaw_row24
#print axioms Rcic.Scm.BoundCfg.Pins.cfgToRaw_row25
#print axioms Rcic.Scm.BoundCfg.Pins.finToRaw_row110
#print axioms Rcic.Scm.BoundCfg.Pins.finToRaw_row112
#print axioms Rcic.Scm.BoundCfg.Pins.runToRaw_row118
#print axioms Rcic.Scm.BoundCfg.Pins.runToRaw_row119
