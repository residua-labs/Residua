/-
RCIC 07 §2–§5 over 01 §6 — the carrier `apps/rcic-scm-contract` (#6029 K4,
segment 1): the canonical `SemanticContract` and `ProgramContractSubject`
objects and the subject's structure against a bound program.

Owner text:
  07 §2 `ProgramContractSubject { core_program_ref, semantic_contract_ref }`;
      "The entry ABI is: entry(Input, State) → pair(Output, State) raises
      ResidueRow". "Subject well-formedness checks the derived entry
      signature, result type, residue catalog, derived residue row, SCM
      semantics profile, and cost profile against the contract."
  07 §3 the `SemanticContract` fields; "Every predicate ref is an exact R-CIC
      member in a bound predicate environment."
  07 §4 `BoundSemanticContract`, `BoundProgramContractSubject`,
      `entryOf(subject) := resolve(subject.program.program_root_bytes)
      .entry_function_ref`.
  07 §5 "entry derived residue row = contract residue row"; "Each row member
      has exactly one `ResidueCase` in canonical row order, and no extra
      catch-all case exists."

Kinds 25 (`SemanticContract`) and 26 (`ProgramContractSubject`) are
registered in `docs/rcic/SEMANTIC_OBJECT_KIND_REGISTRY.md`.

PIN (M-002): `scmCT` is `rcic.scm_ct form fuel profile sref sbytes cref
cbytes rref rbytes bref bbytes tin tst tout x` (47 rows in `Pins`,
hand-transcribed). Form 0 binds a contract, form 1 a subject object, form 2
checks the subject structure, form 3 encodes an object (the carrier's
`x = {kind, o}` is `xk` / `xo`).

TRANSCRIPTION TABLE (07 → Lean):
  §3 contract fields → `Contract`; profile, type, catalog and footprint refs
      are strings (digests for the type and catalog refs), a predicate ref
      is `MRef` (group digest, member index), a `ResidueCase` is `RCase`
  §2 subject → `Subj`
  01 §6 (1)–(5) for kinds 25, 26 → `ctBind`
  §5 canonical row, one case per member in row order → `ctContract`
  §4 subject_program_seam, subject_contract_seam → `ctSubject` clauses 1, 2
  §4 entryOf from the program root → the entry of `BoundProg.bpProgram`
  §2 profile, residue catalog, entry(Input, State) → pair(Output, State)
      at the contract's bound types (`BoundTV.typeAt`) → `ctSubject`
  §5 derived row = contract row (`RowDerive.scmRows`) → `ctSubject`
NOT TRANSCRIBED (open): the predicate environment (`predicate_environment_
ref/bytes/at`, `all_predicate_refs_resolve`) and predicate typing, so neither
`BoundSemanticContract` nor `BoundProgramContractSubject` is built here; the
cost profile check (no program-side cost profile object exists); guard
partition (§6), adequacy (§11), the outcome relations and every CT row past
the structure checks.
-/
import rcic.ScmConfigAt
import rcic.ScmRowDerive

namespace Rcic.Scm.Contract
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject

structure MRef where
  g : String
  i : Int
  deriving BEq

structure RCase where
  r : String
  g : MRef
  p : MRef
  deriving BEq

structure Contract where
  sprof : String
  eprof : String
  cprof : String
  kprof : String
  tin : String
  tst : String
  tout : String
  cat : String
  row : List String
  pre : MRef
  rg : MRef
  rp : MRef
  cases : List RCase
  bound : MRef
  fprof : String
  funiv : String
  fclaim : String
  deriving BEq

structure Subj where
  prog : String
  con : String
  deriving BEq

/-- The carrier's objects and results. -/
inductive CO where
  | unit
  | con (c : Contract)
  | subj (s : Subj)
  | st (entry : Int) (tin tst tout : CoreTy) (row : List String)
  | enc (b d : String) (o : CO)
  deriving BEq

/-- The carrier's output record `{ok, x, code}`. -/
structure COut where
  ok : Int
  x : CO
  code : String
  deriving BEq

def coOk (x : CO) : COut := ⟨1, x, ""⟩
def coRefuse (c : String) : COut := ⟨0, .unit, c⟩

def itm (xs : List Item) (i : Nat) : Item := xs.getD i default

def contractKinds : List Nat := [4, 4, 4, 4, 4, 4, 4, 4, 14, 4, 5, 4, 5, 4, 5, 14, 4, 5, 4, 4, 4]
def caseKinds : List Nat := [4, 4, 5, 4, 5]

def mref (xs : List Item) (i : Nat) : MRef := ⟨asStr (itm xs i), asNum (itm xs (i + 1))⟩

/-- One residue case, decoded from its embedded bytes. -/
def decCase (fuel : Int) (s : String) : Except String RCase := do
  let cs := s.toList.toArray
  let (ys, _) ← decSeq cs (gasFor fuel cs.size) fuel 0 caseKinds
  pure ⟨asStr (itm ys 0), mref ys 1, mref ys 3⟩

/-- `rcic.scm_ct_dec`: kind 25 is a contract (`N`), any other kind a subject
    (`Q`). -/
def ctDec (fuel kind : Int) (b : String) : Except String (CO × Nat) :=
  let cs := b.toList.toArray
  match charAt cs 0 with
  | none => wErr "truncated"
  | some c =>
    if kind = 25 then
      if c ≠ 'N' then wErr "tag" else do
        let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 contractKinds
        let cases ← ((asList (itm xs 15)).map asStr).mapM (decCase fuel)
        pure (.con ⟨asStr (itm xs 0), asStr (itm xs 1), asStr (itm xs 2), asStr (itm xs 3),
          asStr (itm xs 4), asStr (itm xs 5), asStr (itm xs 6), asStr (itm xs 7),
          (asList (itm xs 8)).map asStr, mref xs 9, mref xs 11, mref xs 13, cases, mref xs 16,
          asStr (itm xs 18), asStr (itm xs 19), asStr (itm xs 20)⟩, q)
    else
      if c ≠ 'Q' then wErr "tag" else do
        let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 [4, 4]
        pure (.subj ⟨asStr (itm xs 0), asStr (itm xs 1)⟩, q)

def encM (m : MRef) : String := encStr m.g ++ encNat m.i

def encCase (cs : RCase) : String :=
  encStr (encStr cs.r ++ encStr cs.g.g ++ encNat cs.g.i ++ encStr cs.p.g ++ encNat cs.p.i)

def encContract (c : Contract) : String :=
  "N" ++ encStr c.sprof ++ encStr c.eprof ++ encStr c.cprof ++ encStr c.kprof ++ encStr c.tin ++
    encStr c.tst ++ encStr c.tout ++ encStr c.cat ++ encNat c.row.length ++ String.join (c.row.map encStr) ++
    encM c.pre ++ encM c.rg ++ encM c.rp ++ encNat c.cases.length ++ String.join (c.cases.map encCase) ++
    encM c.bound ++ encStr c.fprof ++ encStr c.funiv ++ encStr c.fclaim

/-- `rcic.scm_ct_enc`. -/
def ctEnc : CO → String
  | .con c => encContract c
  | .subj s => "Q" ++ encStr s.prog ++ encStr s.con
  | _ => ""

/-- `rcic.scm_ct_bind`: 01 §6 for kinds 25 and 26, in the carrier's order:
    class/kind (4), decode (1), whole input (5), re-encode (2), derived
    digest (3). -/
def ctBind (fuel : Int) (r : Ref) (kind : Int) (b : String) : COut :=
  if r.cls ≠ 3 then coRefuse "[rcic_scm_obj_class_kind]" else
  if r.kind ≠ kind then coRefuse "[rcic_scm_obj_class_kind]" else
  match ctDec fuel kind b with
  | .error c => coRefuse c
  | .ok (o, p) =>
    if p ≠ b.length then coRefuse "[rcic_scm_obj_trailing]" else
    if ctEnc o ≠ b then coRefuse "[rcic_scm_obj_noncanonical]" else
    if Rcic.TypedRef.deriveDigest 3 kind b ≠ r.digest then coRefuse "[rcic_scm_obj_digest]" else
    coOk o

/-- `rcic.scm_ct_contract`: the binding, then 07 §5's row shape. -/
def ctContract (fuel : Int) (r : Ref) (b : String) : COut :=
  let bo := ctBind fuel r 25 b
  if bo.ok = 0 then bo else
  match bo.x with
  | .con c =>
    if Rows.rowCanon c.row ≠ c.row then coRefuse "[rcic_scm_ct_row_canonical]" else
    if c.cases.length ≠ c.row.length then coRefuse "[rcic_scm_ct_cases]" else
    if (c.cases.zip c.row).all (fun (cs, rr) => cs.r == rr) then bo else coRefuse "[rcic_scm_ct_cases]"
  | _ => coRefuse ""

/-- `rcic.scm_ct_subject`: the subject structure. -/
def ctSubject (fuel : Int) (profile : String) (sref : Ref) (sb : String) (cref : Ref) (cb : String)
    (rref : Ref) (rb : String) (bref : Ref) (bb : String) (tin tst tout : String) : COut :=
  let s := ctBind fuel sref 26 sb
  if s.ok = 0 then s else
  match s.x with
  | .subj sj =>
    if sj.prog ≠ rref.digest then coRefuse "[rcic_scm_ct_program_seam]" else
    if sj.con ≠ cref.digest then coRefuse "[rcic_scm_ct_contract_seam]" else
    let c := ctContract fuel cref cb
    if c.ok = 0 then c else
    match c.x with
    | .con k =>
      let pr := BoundProg.bpProgram fuel profile rref rb bref bb
      if pr.ok = 0 then coRefuse pr.code else
      match pr.x with
      | .bound prog _ =>
        if k.sprof ≠ profile then coRefuse "[rcic_scm_ct_profile]" else
        if k.cat ≠ Rcic.TypedRef.deriveDigest 3 18 (BoundProg.objEnc (.catalog prog.catalog)) then
          coRefuse "[rcic_scm_ct_catalog]" else
        let ti := BoundTV.typeAt fuel ⟨3, 16, k.tin⟩ tin
        if ti.ok = 0 then coRefuse ti.code else
        let ts := BoundTV.typeAt fuel ⟨3, 16, k.tst⟩ tst
        if ts.ok = 0 then coRefuse ts.code else
        let to := BoundTV.typeAt fuel ⟨3, 16, k.tout⟩ tout
        if to.ok = 0 then coRefuse to.code else
        let ef := prog.fns.getD prog.entry.toNat ⟨[], .i64, .unknown 0⟩
        if ef.params != [ti.t, ts.t] then coRefuse "[rcic_scm_ct_abi]" else
        if ef.result != .pair to.t ts.t then coRefuse "[rcic_scm_ct_abi]" else
        let rw := RowDerive.scmRows 0 fuel prog []
        if rw.ok = 0 then coRefuse rw.code else
        if rw.row != k.row then coRefuse "[rcic_scm_ct_row]" else
        coOk (.st prog.entry ti.t ts.t to.t rw.row)
      | _ => coRefuse ""
    | _ => coRefuse ""
  | _ => coRefuse ""

/-- `rcic.scm_ct`, the carrier entry point. -/
def scmCT (form fuel : Int) (profile : String) (sref : Ref) (sb : String) (cref : Ref) (cb : String)
    (rref : Ref) (rb : String) (bref : Ref) (bb : String) (tin tst tout : String) (xk : Int) (xo : CO) : COut :=
  if form < 0 then coRefuse "[rcic_scm_ct_unknown_form]" else
  if form > 3 then coRefuse "[rcic_scm_ct_unknown_form]" else
  if form = 0 then ctContract fuel cref cb else
  if form = 1 then ctBind fuel sref 26 sb else
  if form = 2 then ctSubject fuel profile sref sb cref cb rref rb bref bb tin tst tout else
  if xk < 25 then coRefuse "[rcic_scm_ct_unknown_form]" else
  if xk > 26 then coRefuse "[rcic_scm_ct_unknown_form]" else
  let b := ctEnc xo
  let d := Rcic.TypedRef.deriveDigest 3 xk b
  let r := if xk = 25 then ctContract fuel ⟨3, 25, d⟩ b else ctBind fuel ⟨3, 26, d⟩ 26 b
  if r.ok = 0 then r else coOk (.enc b d r.x)

/-! ## What an accepting answer establishes -/

/-- An accepted binding meets 01 §6 (4), (1), (5), (2), (3) for its kind. -/
theorem ctBind_accepts (fuel : Int) (r : Ref) (kind : Int) (b : String) (h : (ctBind fuel r kind b).ok = 1) :
    r.cls = 3 ∧ r.kind = kind ∧ Rcic.TypedRef.deriveDigest 3 kind b = r.digest ∧
      ∃ o p, ctDec fuel kind b = .ok (o, p) ∧ p = b.length ∧ ctEnc o = b := by
  unfold ctBind at h
  by_cases h1 : r.cls = 3
  · by_cases h2 : r.kind = kind
    · cases hd : ctDec fuel kind b with
      | error c => simp [h1, h2, hd, coRefuse] at h
      | ok op =>
        obtain ⟨o, p⟩ := op
        by_cases h3 : p = b.length
        · by_cases h4 : ctEnc o = b
          · by_cases h5 : Rcic.TypedRef.deriveDigest 3 kind b = r.digest
            · exact ⟨h1, h2, h5, o, p, rfl, h3, h4⟩
            · simp [h1, h2, hd, h3, h4, h5, coRefuse] at h
          · simp [h1, h2, hd, h3, h4, coRefuse] at h
        · simp [h1, h2, hd, h3, coRefuse] at h
    · simp [h1, h2, coRefuse] at h
  · simp [h1, coRefuse] at h

end Rcic.Scm.Contract

/-! ## Pins: apps/rcic-scm-contract/rcic_scm_contract_corpus.json, 47 rows

Hand-transcribed (§18.3 rule 4). The programs and contracts are built the way
the corpus generator builds them; bytes and digests are computed here from the
objects, and the corpus' bytes and digests come from the engine. Every row
runs at fuel 64 under `SCM-Core-0`. -/

namespace Rcic.Scm.Contract.Pins
open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.Contract Rcic.BoundObject

def I : CoreTy := .i64
def U : CoreTy := unitTy
def B : CoreTy := .bool
def PIU : CoreTy := .pair I U
def P0 : String := "SCM-Core-0"
def dg (b : String) (k : Int) : String := Rcic.TypedRef.deriveDigest 3 k b
def rf (b : String) (k : Int) (cls : Int := 3) : Ref := ⟨cls, k, dg b k⟩
def NOREF : Ref := ⟨0, 0, ""⟩
def CAT : List CatalogEntry := [⟨"bad_input", unitTy⟩, ⟨"range_violation", .i64⟩]

def F_ROW0 : RawFnDef := ⟨[I, U], PIU, .pair (.var 0) (.var 1)⟩
def F_RAISE : RawFnDef :=
  ⟨[I, U], PIU, .ifE (.prim "lt" [.var 0, .lit (.i 0) .i64]) (.raise "range_violation" (.var 0) PIU) (.pair (.var 0) (.var 1))⟩
def F_ARITY : RawFnDef := ⟨[I], PIU, .pair (.var 0) (.lit (.r []) unitTy)⟩
def F_RES : RawFnDef := ⟨[I, U], I, .var 0⟩
def prog1 (f : RawFnDef) : RawProg := ⟨[f], [], CAT, 0⟩
def PR0 : BoundProg.Pins.Parts := BoundProg.Pins.parts (prog1 F_ROW0)
def PRR : BoundProg.Pins.Parts := BoundProg.Pins.parts (prog1 F_RAISE)
def PRA : BoundProg.Pins.Parts := BoundProg.Pins.parts (prog1 F_ARITY)
def PRS : BoundProg.Pins.Parts := BoundProg.Pins.parts (prog1 F_RES)

def TI : String := encTy I
def TU : String := encTy U
def TB : String := encTy B
def DI : String := dg TI 16
def DU : String := dg TU 16
def DB : String := dg TB 16
def catD (p : BoundProg.Pins.Parts) : String := dg p.cb 18
def OTHER_CAT : String := dg (BoundProg.objEnc (.catalog [⟨"bad_input", unitTy⟩])) 18

def mr (i : Int) : MRef := ⟨"pred-env-group", i⟩
def case (r : String) : RCase := ⟨r, mr 4, mr 5⟩
def contract (tin tst tout cat : String) (row : List String) (cases : List RCase) (sprof : String := P0) : Contract :=
  ⟨sprof, "SCM-Logical-Embedding-0", "SCM-Cost-0", "SCM-Contract-0", tin, tst, tout, cat, row,
    mr 0, mr 1, mr 2, cases, mr 3, "footprint-profile", "footprint-universe", "footprint-claim"⟩
def C0 : Contract := contract DI DU DI (catD PR0) [] []
def C1 : Contract := contract DI DU DI (catD PRR) ["range_violation"] [case "range_violation"]
def cenc (c : Contract) : String := encContract c
def senc (s : Subj) : String := ctEnc (.subj s)
def CB0 : String := cenc C0
def SB0 : String := senc ⟨dg PR0.rb 20, dg CB0 25⟩

def dummy : CO := .unit
def run (form : Int) (sref : Ref := NOREF) (sb : String := "") (cref : Ref := NOREF) (cb : String := "")
    (rref : Ref := NOREF) (rb : String := "") (bref : Ref := NOREF) (bb : String := "")
    (tin tst tout : String := "") (xk : Int := 0) (xo : CO := dummy) : COut :=
  scmCT form 64 P0 sref sb cref cb rref rb bref bb tin tst tout xk xo
def con0 (c : Contract) : COut := run 0 (cref := rf (cenc c) 25) (cb := cenc c)
def okC (c : Contract) : COut := coOk (.con c)
def okS (s : Subj) : COut := coOk (.subj s)
def no (c : String) : COut := coRefuse c

/-- A form-2 row as the generator builds it: the subject names `sprog`'s root
    (or `progD`) and the contract's digest (or `conD`). -/
def subj (c : Contract := C0) (p : BoundProg.Pins.Parts := PR0) (sp : BoundProg.Pins.Parts := PR0)
    (conD : Option String := none) (bb : Option String := none) (tin : String := TI) (tst : String := TU)
    (tout : String := TI) : COut :=
  let cb := cenc c
  let sb := senc ⟨dg sp.rb 20, conD.getD (dg cb 25)⟩
  let b := bb.getD p.bb
  run 2 (sref := rf sb 26) (sb := sb) (cref := rf cb 25) (cb := cb) (rref := rf p.rb 20) (rb := p.rb)
    (bref := rf b 21) (bb := b) (tin := tin) (tst := tst) (tout := tout)
def st (row : List String) : COut := coOk (.st 0 I U I row)

def CBAD : Contract := contract DI DU DI (catD PRR) ["range_violation", "bad_input"] [case "range_violation", case "bad_input"]

-- 0–13 contract binding (form 0)
#guard con0 C0 == okC C0
#guard con0 C1 == okC C1
#guard run 0 (cref := rf CB0 25 (cls := 2)) (cb := CB0) == no "[rcic_scm_obj_class_kind]"
#guard run 0 (cref := rf CB0 26) (cb := CB0) == no "[rcic_scm_obj_class_kind]"
#guard run 0 (cref := rf (cenc C1) 25) (cb := CB0) == no "[rcic_scm_obj_digest]"
#guard run 0 (cref := rf (CB0 ++ "0;") 25) (cb := CB0 ++ "0;") == no "[rcic_scm_obj_trailing]"
#guard run 0 (cref := rf ("N0" ++ CB0.drop 1) 25) (cb := "N0" ++ CB0.drop 1) == no "[rcic_scm_obj_noncanonical]"
#guard run 0 (cref := rf SB0 25) (cb := SB0) == no "[rcic_scm_wire_tag]"
#guard run 0 (cref := rf "" 25) (cb := "") == no "[rcic_scm_wire_truncated]"
#guard con0 CBAD == no "[rcic_scm_ct_row_canonical]"
#guard con0 (contract DI DU DI (catD PRR) ["range_violation", "range_violation"] [case "range_violation", case "range_violation"])
  == no "[rcic_scm_ct_row_canonical]"
#guard con0 (contract DI DU DI (catD PRR) ["bad_input", "range_violation"] [case "bad_input"]) == no "[rcic_scm_ct_cases]"
#guard con0 (contract DI DU DI (catD PRR) ["bad_input", "range_violation"] [case "range_violation", case "bad_input"])
  == no "[rcic_scm_ct_cases]"
#guard con0 (contract DI DU DI (catD PR0) [] [case "range_violation"]) == no "[rcic_scm_ct_cases]"
-- 14–18 subject object (form 1)
#guard run 1 (sref := rf SB0 26) (sb := SB0) == okS ⟨dg PR0.rb 20, dg CB0 25⟩
#guard run 1 (sref := rf SB0 25) (sb := SB0) == no "[rcic_scm_obj_class_kind]"
#guard run 1 (sref := rf CB0 26) (sb := SB0) == no "[rcic_scm_obj_digest]"
#guard run 1 (sref := rf (SB0 ++ "x") 26) (sb := SB0 ++ "x") == no "[rcic_scm_obj_trailing]"
#guard run 1 (sref := rf ("Q0" ++ SB0.drop 1) 26) (sb := "Q0" ++ SB0.drop 1) == no "[rcic_scm_obj_noncanonical]"
-- 19–36 subject structure (form 2)
#guard subj == st []
#guard subj (c := C1) (p := PRR) (sp := PRR) == st ["range_violation"]
#guard subj (sp := PRR) == no "[rcic_scm_ct_program_seam]"
#guard subj (conD := some (dg (cenc C1) 25)) == no "[rcic_scm_ct_contract_seam]"
#guard subj (c := contract DI DU DI (catD PR0) [] [case "range_violation"]) == no "[rcic_scm_ct_cases]"
#guard subj (bb := some PRR.bb) == no "[rcic_scm_bp_root_mismatch]"
#guard subj (c := contract DI DU DI (catD PR0) [] [] (sprof := "SCM-Core-1")) == no "[rcic_scm_ct_profile]"
#guard subj (c := contract DI DU DI OTHER_CAT [] []) == no "[rcic_scm_ct_catalog]"
#guard subj (tin := TB) == no "[rcic_scm_tv_digest]"
#guard subj (c := contract DB DU DI (catD PR0) [] []) (tin := TB) == no "[rcic_scm_ct_abi]"
#guard subj (c := contract DI DU DB (catD PR0) [] []) (tout := TB) == no "[rcic_scm_ct_abi]"
#guard subj (c := contract DI DU DI (catD PRA) [] []) (p := PRA) (sp := PRA) == no "[rcic_scm_ct_abi]"
#guard subj (c := contract DI DU DI (catD PRS) [] []) (p := PRS) (sp := PRS) == no "[rcic_scm_ct_abi]"
#guard subj (c := contract DI DU DI (catD PRR) [] []) (p := PRR) (sp := PRR) == no "[rcic_scm_ct_row]"
#guard subj (c := contract DI DU DI (catD PRR) ["bad_input", "range_violation"] [case "bad_input", case "range_violation"])
    (p := PRR) (sp := PRR) == no "[rcic_scm_ct_row]"
#guard subj (c := contract DI DU DI (catD PR0) ["range_violation"] [case "range_violation"]) == no "[rcic_scm_ct_row]"
#guard subj (c := contract DI (dg "R00;" 16) DI (catD PR0) [] []) (tst := "R00;") == no "[rcic_scm_tv_noncanonical]"
-- 37–42 encode (form 3) and unknown forms
#guard run 3 (xk := 25) (xo := .con C0) == coOk (.enc CB0 (dg CB0 25) (.con C0))
#guard run 3 (xk := 25) (xo := .con CBAD) == no "[rcic_scm_ct_row_canonical]"
#guard run 3 (xk := 26) (xo := .subj ⟨dg PR0.rb 20, dg CB0 25⟩)
  == coOk (.enc SB0 (dg SB0 26) (.subj ⟨dg PR0.rb 20, dg CB0 25⟩))
#guard run 3 (xk := 24) (xo := .con C0) == no "[rcic_scm_ct_unknown_form]"
#guard run 3 (xk := 27) (xo := .con C0) == no "[rcic_scm_ct_unknown_form]"
#guard run 4 == no "[rcic_scm_ct_unknown_form]"
#guard run (-1) == no "[rcic_scm_ct_unknown_form]"
-- 43–46 rows added after the first S4 pass (each closes a zero-divergence probe)
def BADCASE : String := (cenc C1).replace (encCase (case "range_violation")) "2:zz"
#guard run 0 (cref := rf BADCASE 25) (cb := BADCASE) == no "[rcic_scm_wire_truncated]"
def PRE1 : BoundProg.Pins.Parts := BoundProg.Pins.parts ⟨[F_RES, F_ROW0], [], CAT, 1⟩
#guard subj (c := contract DI DU DI (catD PRE1) [] []) (p := PRE1) (sp := PRE1) == coOk (.st 1 I U I [])
#guard subj (tst := TB) == no "[rcic_scm_tv_digest]"
#guard subj (tout := TB) == no "[rcic_scm_tv_digest]"

end Rcic.Scm.Contract.Pins
