/-
RCIC 06 §19 — the intrinsic/wire bridge, per instance (carrier
`apps/rcic-wire-bridge`, SCM-016/017/018 data halves).

Owner text (06:405-417): "Required bidirectional theorems: encode intrinsic
value → ValueAt; ValueAt → unique intrinsic decoded value; intrinsic
program/config/outcome → bound canonical wire object; intrinsic SCMStep →
SCMStepAt; SCMStepAt → intrinsic SCMStep; intrinsic SCMRuns → SCMRunsAt;
SCMRunsAt → intrinsic SCMRuns; entry initialization/final-outcome
correspondence."

The carrier decides the bridge's DATA instances; the ∀ theorems are #6029 K3.
It composes three landed carriers, and so does this model:
`ScmValueAt.valueAt` (value encode/decode/bind), `ScmExec.configAt` (the
frame-chain wire config check), `ScmStepAt.rowOk` / `findRow` (step rows),
and `RcicTypedRef.deriveDigest`.

PIN (M-002): `wireBridge` is `rcic.wire_bridge form subject direction tag …
config config_out table fuel`, 15 rows below.
STAND-IN (#6029 K2 HOLD item 1, K2 decision): this file pins a carrier
stand-in (M-002). It is NOT the 06 §18 / §19 object of the same name: those are
stated over bound refs and canonical core-wire bytes and are NOT TRANSCRIBED
until K3b/K3c (see `ScmRawRelations`). The table below maps the CARRIER's
rules; the 06 sections are those the carrier cites.

CARRIER RULE TABLE (rcic-wire-bridge, cites 06 §19 → Lean):
  encode intrinsic value → ValueAt               → form 0 subject 0
  intrinsic config → bound canonical wire object → form 0 subject 1
  ValueAt → unique intrinsic value (roundtrip, both directions) → form 1
        subject 0, direction 0 / 1
  config wire roundtrip                          → form 1 subject 1
  intrinsic SCMStep ↔ SCMStepAt (one row)        → form 2 subject 0
  SCMRuns / suspension correspondence (a suspended config has no final row)
                                                 → form 2 subject 1
  entry initialization / final-outcome correspondence → not in the
        carrier's forms; the intrinsic entry run is pinned in
        `ScmMachineIPins.lean`
-/
import rcic.ScmValueAt
import rcic.ScmStepAt

namespace Rcic.Scm.WireBridge
open Rcic.Scm.ValueAt Rcic.Scm.Exec Rcic.Scm.StepAt

structure WBOut where
  ok : Int
  form : Int
  subject : Int
  code : String
  deriving BEq

/-- The value-side arguments shared by forms 0 and 1. -/
structure ValArgs where
  tag : Int := 0
  cls : Int := 0
  kind : Int := 0
  digest : String := ""
  iv : Int := 0
  sv : String := ""
  lt : Int := 0
  li : Int := 0
  ls : String := ""
  rt : Int := 0
  ri : Int := 0
  rs : String := ""

def va (form : Int) (a : ValArgs) (wire : String) : VOut :=
  valueAt form a.tag a.cls a.kind a.digest a.iv a.sv a.lt a.li a.ls a.rt a.ri a.rs wire

def configEq (config wire : String) (fuel : Int) : Option String :=
  match configAt config fuel with
  | some c => some c
  | none => if config = wire then none else some "[rcic_wire_encode_mismatch]"

def wireBridge (form subject direction : Int) (a : ValArgs) (config wire configOut : String) (table : List Row)
    (fuel : Int) : WBOut :=
  let ok : WBOut := ⟨1, form, subject, ""⟩
  let no (c : String) : WBOut := ⟨0, form, subject, c⟩
  if form = 0 then
    if subject = 0 then
      let e := va 0 a wire
      if e.ok ≠ 1 then no e.code else
      let b := va 2 a wire
      if b.ok = 1 then ok else no b.code
    else if subject = 1 then
      match configEq config wire fuel with
      | some c => no c
      | none =>
        if a.kind < 0 then no "[typed_ref_unknown_kind]"
        else if !Rcic.BoundObject.classOk a.cls then no "[typed_ref_unknown_class]"
        else if Rcic.TypedRef.deriveDigest a.cls.toNat a.kind wire = a.digest then ok
        else no "[rcic_wire_digest_mismatch]"
    else no "[rcic_wire_unknown_subject]"
  else if form = 1 then
    if subject = 0 then
      if direction = 0 then
        let dc := va 1 a wire
        if dc.ok ≠ 1 then no dc.code
        else if (va 0 a wire).ok = 1 then ok else no "[rcic_wire_roundtrip]"
      else if direction = 1 then
        let ec := va 0 a wire
        if ec.ok ≠ 1 then no ec.code else
        let dc := va 1 a wire
        if dc.ok = 1 then ok else no dc.code
      else no "[rcic_wire_unknown_direction]"
    else if subject = 1 then
      if direction = 0 then
        match configAt wire fuel with
        | some c => no c
        | none => if join (wire.splitOn "~") "~" = wire then ok else no "[rcic_wire_roundtrip]"
      else if direction = 1 then
        match configEq config wire fuel with
        | some c => no c
        | none => match configAt wire fuel with
          | some c => no c
          | none => ok
      else no "[rcic_wire_unknown_direction]"
    else no "[rcic_wire_unknown_subject]"
  else if form = 2 then
    if subject = 0 then
      match findRow table config with
      | some r =>
        if r.kind = 0 ∧ r.configOut = configOut then
          match rowOk ⟨config, r.kind, r.configOut, r.outcome⟩ fuel with
          | none => ok
          | some c => no c
        else no "[rcic_wire_step_mismatch]"
      | none => no "[rcic_wire_step_mismatch]"
    else if subject = 1 then
      match configAt config fuel with
      | some c => no c
      | none => match findRow table config with
        | some r => if r.kind = 1 then no "[rcic_wire_suspension_fabricated]" else ok
        | none => ok
    else no "[rcic_wire_unknown_subject]"
  else no "[rcic_wire_unknown_form]"

/-! ## Pins: apps/rcic-wire-bridge/rcic_wire_bridge_corpus.json, 15 rows -/

namespace Pins
def c3 : String := "t:0|arg:1|fn:f~t:1|val:2~t:2|expr:e"
def c2 : String := "t:1|val:2~t:2|expr:e"
def c1 : String := "t:2|expr:e"
def okR (form subject : Int) : WBOut := ⟨1, form, subject, ""⟩
def noR (form subject : Int) (c : String) : WBOut := ⟨0, form, subject, c⟩
def wb (form subject : Int) (a : ValArgs := {}) (wire : String := "") (direction : Int := 0) (config configOut : String := "")
    (table : List Row := []) : WBOut := wireBridge form subject direction a config wire configOut table 10

-- 0 form0 subject0 int encode ok: i:5 binds canonical+derive (SCM-016 data half, 06 S19 L409 encode-direction)
#guard wb 0 0 { digest := "4e36bce2fed1bcb28834441f17ddc6e0bef43aad07d8bb5e05d152d456d3ea9b", iv := 5 } "i:5" == okR 0 0
-- 1 form0 subject0 str encode ok: s:x binds (SCM-016 data half, 06 S19 L409)
def strArgs : ValArgs := { tag := 1, digest := "0e222d75d725d24bd3092f311d0ceecc3ff5e10ad22dc4ae7809dc37707ef5ca", sv := "x" }
#guard wb 0 0 strArgs "s:x" == okR 0 0
-- 2 form0 subject0 pair encode ok: p:i:1|s:x binds (SCM-016 data half, 06 S19 L409)
def pairArgs : ValArgs :=
  { tag := 2, digest := "7ba4cd40cb4e7fc9b2640b6e6c3fa9a56214b67c1da30345bd57c47099755051", li := 1, rt := 1, rs := "x" }
#guard wb 0 0 pairArgs "p:i:1|s:x" == okR 0 0
-- 3 form0 subject1 frame-chain config encode ok: CFG3 binds derive (SCM-017 data half, 06 S19 L411 config->wire)
#guard wb 0 1 { digest := "284ae159b0606837ca216c82cebd20e5cce7bdbe63ee69317c0faefaccef413d" } c3 0 c3 == okR 0 1
-- 4 form0 subject1 encode mismatch refused: wire bytes differ from intrinsic config (SCM-017 data half)
#guard wb 0 1 { digest := "284ae159b0606837ca216c82cebd20e5cce7bdbe63ee69317c0faefaccef413d" } c2 0 c3
  == noR 0 1 "[rcic_wire_encode_mismatch]"
-- 5 form1 subject0 dir0 wire->intrinsic->wire roundtrip ok int (SCM-016 data half, 06 S19 L409/L410)
#guard wb 1 0 { iv := 5 } "i:5" == okR 1 0
-- 6 form1 subject0 dir1 intrinsic->wire->intrinsic roundtrip ok str
#guard wb 1 0 { tag := 1, sv := "x" } "s:x" 1 == okR 1 0
-- 7 form1 subject0 dir0 wire-outside-image refused: s:x decodes but given intrinsic y re-encodes differently
#guard wb 1 0 { tag := 1, sv := "y" } "s:x" == noR 1 0 "[rcic_wire_roundtrip]"
-- 8 form1 subject0 dir0 re-encode-divergent refused: p:i:1|s:x decodes but intrinsic left-int 2 re-encodes differently
#guard wb 1 0 { tag := 2, li := 2, rt := 1, rs := "x" } "p:i:1|s:x" == noR 1 0 "[rcic_wire_roundtrip]"
-- 9 form1 subject1 dir0 config roundtrip ok: CFG1 decodes and re-joins byte-identical (SCM-017 data half, 06 S19 L411)
#guard wb 1 1 {} c1 0 c1 == okR 1 1
-- 10 form2 subject0 step correspondence ok: intrinsic step CFG3->CFG2 matches the wire row exactly
#guard wb 2 0 {} "" 0 c3 c2 [⟨c3, 0, c2, ""⟩] == okR 2 0
-- 11 form2 subject0 step mismatch refused: intrinsic config_out differs from the row's stored wire form
#guard wb 2 0 {} "" 0 c3 "t:1|val:9~t:2|expr:e" [⟨c3, 0, c2, ""⟩] == noR 2 0 "[rcic_wire_step_mismatch]"
-- 12 form2 subject1 suspended run ok: CFG2 suspended, only a step row exists (run may continue; GM-OUT-004, 06 S19 L416)
#guard wb 2 1 {} "" 0 c2 "" [⟨c2, 0, c1, ""⟩] == okR 2 1
-- 13 form2 subject1 suspended-with-fabricated-outcome refused: final row answers the suspended config
#guard wb 2 1 {} "" 0 c2 "" [⟨c2, 1, "", "output:9|post:s"⟩] == noR 2 1 "[rcic_wire_suspension_fabricated]"
-- 14 unknown form refused (06 S19 bridge word, closure_claim=0)
#guard wb 3 0 == noR 3 0 "[rcic_wire_unknown_form]"
end Pins

end Rcic.Scm.WireBridge
