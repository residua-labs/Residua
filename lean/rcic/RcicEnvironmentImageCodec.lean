import rcic.RcicSingletonAdmission
import rcic.RcicExprSubstTask
import rcic.ScmWire
import rcic.ScmBoundCoreTV
import rcic.RcicBoundObject
import rcic.ScmEmbed
import Residua.SHA256

/-!
Executable EnvironmentImage codec, moved without changing definitions from
RcicGraphAdmittedBlind. Qualified names remain Rcic.GraphAdmitted.Blind.
The graph admission proofs and concrete fixtures remain in that module and
import this single shared implementation. No schema or encoding changes.
closure_claim = 0.
-/
namespace Rcic.GraphAdmitted.Blind

open Rcic.BoundObject (canonBytesOk)
open Rcic.Scm.Embed (partAt keysOf)
open Rcic.Declarative (Expr Level)
open Rcic.ExprSubstTask (LevelWire ExprWire)

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


/-- Exact Lean mirror of SCM `(content-hash s)` on a string value `s`
    (`Residua.SHA256.sha256Hex` over `"StrLit(str:" ++ toString s.length ++ ":" ++ s ++ ")"`),
    matching `rcic.group_codec` form 1 and `rcic.env_image` form 0. -/
def scmContentHashStr (s : String) : String :=
  Residua.SHA256.sha256Hex ("StrLit(str:" ++ toString s.length ++ ":" ++ s ++ ")")

/-- Default `EnvironmentImage` theory profile and checked-group schema frame
    segments (`scm/rcic/env_image_join.scm:1–2`). -/
def envImageDefaultProfile : String := "D-RCIC-0"
def envImageDefaultSchema : String := "checked-group-schema"


end Rcic.GraphAdmitted.Blind
