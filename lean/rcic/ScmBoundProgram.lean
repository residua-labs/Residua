/-
RCIC 06 §7 / §17 / §18 (bound program) over 01 §6 — the carrier
`apps/rcic-scm-bound-program` (#6029 K3b, segment 2).

Owner text:
  06 §7: `CoreFunctionGroupCandidate { scm_semantics_profile_ref, signatures,
      bodies }`; `CoreProgramRoot { scm_semantics_profile_ref,
      residue_catalog_ref, entry_function_ref }`; "A closed core-program bundle
      contains the root, residue catalog, and the exact transitive closure of
      function groups and profiles."
  06 §6: `ResidueCatalog := canonical sorted list CatalogEntry`.
  06 §18 "Bound program": `BoundCoreProgram { program_root_ref,
      program_root_bytes, program_root_at, program_bundle_ref,
      program_bundle_bytes, program_bundle_at, bundle_root_exact }`; "The
      bundle witness is mandatory because execution needs all transitive
      function groups, the residue catalog, and profiles."
  01 §4: `FunctionRef { group_ref, member_index }`, "Member indices are
      bounds-checked; there is no modulo or member-zero fallback."
  01 §6 `CanonicalObjectAt` (1)–(5); 00 §19.7 E-06Wire (the core wire of
      `apps/rcic-scm-wire`: `ScmWire.decSeq` and its encoders, called).

PIN (M-002): `scmBP` is `rcic.scm_bp form fuel profile ref bytes ref2 bytes2
prog` (47 rows in `Pins`, hand-transcribed). Objects are class 3 with the
kinds 18 catalog, 19 group, 20 root, 21 bundle registered in
`docs/rcic/SEMANTIC_OBJECT_KIND_REGISTRY.md` (`[spec_ambiguity]`).
  form 0  CanonicalObjectAt of a residue catalog (plus 06 §6 order);
  form 1  CanonicalObjectAt of a function group under a profile;
  form 2  CanonicalObjectAt of a program root under a profile;
  form 3  the bound program: root and bundle bound, `bundle_root_exact`, the
          catalog and group members bound at the refs the root names, the
          one-group closure, the entry member in range, and the assembled
          program typed by `progCheck` (the model of `rcic.scm_ty_prog`);
  form 4  build: encode the four objects of a one-group program and re-check
          them through form 3.
`objSchema k profile` is the schema whose `CanonicalObjectAt` forms 0–2
decide; conjunct (4) checks the decoded object's profile against the
schema's (the #6029 re-audit carried item 2, `ObjSchema.consistent` sees the
object). Its decode runs with fuel equal to the input length.

NOT TRANSCRIBED here (#6029 K3c): `BoundCoreProgram` and `ProgramBundleAt`
as R-CIC propositions, and "intrinsic program → bound canonical wire object"
(06 §19). NOT DECIDED by the carrier: closures over further groups
(external `FunctionRef`s), profile objects, and the derived residue rows and
checked group refs of 06 §17 steps 5–6 (`apps/rcic-scm-rows` derives rows).
-/
import rcic.ScmBoundTV
import rcic.ScmConfigWire

namespace Rcic.Scm.BoundProg
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject

/-- The carrier's decoded objects and results. -/
inductive Obj where
  | unit
  | catalog (c : List CatalogEntry)
  | group (profile : String) (ext : List ExtSig) (fns : List RawFnDef)
  | root (profile cat grp : String) (member : Int)
  | bundle (root cat : String) (groups : List String)
  | bound (p : RawProg) (t : CoreTy)
  | built (rd rb bd bb : String) (p : RawProg) (t : CoreTy)
  | cx (x : CfgWire.CX)
  deriving BEq

/-- The carrier's output record `{ok, x, code}`. -/
structure BPOut where
  ok : Int
  x : Obj
  code : String
  deriving BEq

def bpOk (x : Obj) : BPOut := ⟨1, x, ""⟩
def bpRefuse (c : String) : BPOut := ⟨0, .unit, c⟩

/-- The object tag and the `decSeq` element kinds of each object
    (`rcic.scm_obj_dec`). -/
def kindTag (kind : Int) : Char :=
  if kind = 18 then 'K' else if kind = 19 then 'G' else if kind = 20 then 'O' else 'U'
def kindSeq (kind : Int) : List Nat :=
  if kind = 18 then [15] else if kind = 19 then [4, 16, 17] else if kind = 20 then [4, 4, 4, 5] else [4, 4, 14]

def asCat : Item → CatalogEntry | .cat c => c | _ => ⟨"", .i64⟩
def asExt : Item → ExtSig | .ext e => e | _ => ⟨"", [], .i64⟩
def asFn : Item → RawFnDef | .fn f => f | _ => ⟨[], .i64, .unknown 0⟩

def objOf (kind : Int) (xs : List Item) : Obj :=
  let x0 := xs.headD default
  let x1 := (xs.drop 1).headD default
  let x2 := (xs.drop 2).headD default
  let x3 := (xs.drop 3).headD default
  if kind = 18 then .catalog ((asList x0).map asCat)
  else if kind = 19 then .group (asStr x0) ((asList x1).map asExt) ((asList x2).map asFn)
  else if kind = 20 then .root (asStr x0) (asStr x1) (asStr x2) (asNum x3)
  else .bundle (asStr x0) (asStr x1) ((asList x2).map asStr)

/-- `rcic.scm_obj_dec`: the object and its end position. Kinds above 21
    (configuration, final outcome, run result) are `CfgWire.cxDec`. -/
def objDec (fuel kind : Int) (b : String) : Except String (Obj × Nat) :=
  if kind > 21 then (CfgWire.cxDec kind b fuel).map (fun (x, q) => (.cx x, q)) else
  let cs := b.toList.toArray
  match charAt cs 0 with
  | none => wErr "truncated"
  | some c =>
    if c ≠ kindTag kind then wErr "tag" else
    match decSeq cs (gasFor fuel cs.size) fuel 1 (kindSeq kind) with
    | .error e => .error e
    | .ok (xs, q) => .ok (objOf kind xs, q)

def encCat (c : CatalogEntry) : String := encStr c.ref ++ encTy c.pt
def encExt (e : ExtSig) : String := encStr e.ref ++ encNat e.params.length ++ encTys e.params ++ encTy e.result

/-- `rcic.scm_obj_enc`. -/
def objEnc : Obj → String
  | .catalog c => "K" ++ encNat c.length ++ String.join (c.map encCat)
  | .group pr ext fns =>
      "G" ++ encStr pr ++ encNat ext.length ++ String.join (ext.map encExt) ++ encNat fns.length ++ encFns fns
  | .root pr cat grp m => "O" ++ encStr pr ++ encStr cat ++ encStr grp ++ encNat m
  | .bundle r cat gs => "U" ++ encStr r ++ encStr cat ++ encNat gs.length ++ String.join (gs.map encStr)
  | .cx x => CfgWire.cxEnc x
  | _ => ""

/-- `rcic.scm_obj_bind`: 01 §6 for an SCM program object, in the carrier's
    order: class/kind (4), decode (1), whole input (5), re-encode (2),
    derived digest (3). -/
def objBind (fuel : Int) (r : Ref) (kind : Int) (b : String) : BPOut :=
  if r.cls ≠ 3 then bpRefuse "[rcic_scm_obj_class_kind]" else
  if r.kind ≠ kind then bpRefuse "[rcic_scm_obj_class_kind]" else
  match objDec fuel kind b with
  | .error c => bpRefuse c
  | .ok (o, p) =>
    if p ≠ b.length then bpRefuse "[rcic_scm_obj_trailing]" else
    if objEnc o ≠ b then bpRefuse "[rcic_scm_obj_noncanonical]" else
    if Rcic.TypedRef.deriveDigest 3 kind b ≠ r.digest then bpRefuse "[rcic_scm_obj_digest]" else
    bpOk o

def objCatalog : Obj → List CatalogEntry | .catalog c => c | _ => []
def objProfile : Obj → String | .group pr _ _ => pr | .root pr _ _ _ => pr | _ => ""

/-- `rcic.scm_bp_catalog`: a bound catalog in 06 §6 canonical order. -/
def bpCatalog (fuel : Int) (r : Ref) (b : String) : BPOut :=
  let o := objBind fuel r 18 b
  if o.ok = 0 then o
  else if catalogCanonical (objCatalog o.x) then o
  else bpRefuse "[rcic_scm_bp_catalog_order]"

/-- `rcic.scm_bp_member`: a bound group or root under `profile`. -/
def bpMember (fuel : Int) (profile : String) (r : Ref) (kind : Int) (b : String) : BPOut :=
  let o := objBind fuel r kind b
  if o.ok = 0 then o
  else if objProfile o.x = profile then o
  else bpRefuse "[rcic_scm_bp_profile]"

/-- `rcic.scm_bp_program`: the bound program (root, bundle). -/
def bpProgram (fuel : Int) (profile : String) (rr : Ref) (rb : String) (br : Ref) (bb : String) : BPOut :=
  let r := bpMember fuel profile rr 20 rb
  if r.ok = 0 then r else
  let b := objBind fuel br 21 bb
  if b.ok = 0 then b else
  match r.x, b.x with
  | .root _ cat grp m, .bundle broot bcat gs =>
    if broot ≠ rb then bpRefuse "[rcic_scm_bp_root_mismatch]" else
    let c := bpCatalog fuel ⟨3, 18, cat⟩ bcat
    if c.ok = 0 then c else
    if gs.length ≠ 1 then bpRefuse "[rcic_scm_bp_closure]" else
    let g := bpMember fuel profile ⟨3, 19, grp⟩ 19 (gs.headD "")
    if g.ok = 0 then g else
    match g.x with
    | .group _ ext fns =>
      if ext.length ≠ 0 then bpRefuse "[rcic_scm_bp_external]" else
      if ¬ (m < fns.length) then bpRefuse "[rcic_scm_bp_entry]" else
      let p : RawProg := ⟨fns, [], objCatalog c.x, m⟩
      match progCheck fuel p with
      | .error e => bpRefuse e
      | .ok ⟨_, t⟩ => bpOk (.bound p t)
    | _ => bpRefuse ""
  | _, _ => bpRefuse ""

/-- `rcic.scm_bp_build`: the four objects of a one-group program, re-checked
    through `bpProgram`. -/
def bpBuild (fuel : Int) (profile : String) (p : RawProg) : BPOut :=
  let cb := objEnc (.catalog p.catalog)
  let gb := objEnc (.group profile p.ext p.fns)
  let rb := objEnc (.root profile (Rcic.TypedRef.deriveDigest 3 18 cb) (Rcic.TypedRef.deriveDigest 3 19 gb) p.entry)
  let bb := objEnc (.bundle rb cb [gb])
  let rd := Rcic.TypedRef.deriveDigest 3 20 rb
  let bd := Rcic.TypedRef.deriveDigest 3 21 bb
  let o := bpProgram fuel profile ⟨3, 20, rd⟩ rb ⟨3, 21, bd⟩ bb
  if o.ok = 0 then o else
  match o.x with
  | .bound q t => bpOk (.built rd rb bd bb q t)
  | _ => bpRefuse ""

/-- `rcic.scm_bp`, the carrier entry point. -/
def scmBP (form fuel : Int) (profile : String) (r : Ref) (b : String) (r2 : Ref) (b2 : String)
    (p : RawProg) : BPOut :=
  if form < 0 then bpRefuse "[rcic_scm_bp_unknown_form]" else
  if form > 4 then bpRefuse "[rcic_scm_bp_unknown_form]" else
  if form = 0 then bpCatalog fuel r b else
  if form = 1 then bpMember fuel profile r 19 b else
  if form = 2 then bpMember fuel profile r 20 b else
  if form = 3 then bpProgram fuel profile r b r2 b2 else
  bpBuild fuel profile p

/-! ## The schemas forms 0–2 decide (01 §6 over the core-wire object grammar) -/

/-- Kind 18 (catalog), 19 (group) or 20 (root) under a semantics profile.
    A catalog decodes only in 06 §6 order; conjunct (4) checks class, kind
    and, for a group or root, the decoded object's profile. -/
def objSchema (kind : Int) (profile : String) : ObjSchema where
  Obj := Obj
  decode b :=
    match objDec b.length kind b with
    | .ok (o, _) => if kind = 18 ∧ !catalogCanonical (objCatalog o) then none else some o
    | .error _ => none
  encode := objEnc
  exactFields b :=
    match objDec b.length kind b with
    | .ok (_, p) => p == b.length
    | .error _ => false
  consistent c k o := c == 3 && k == kind && (kind == 18 || objProfile o == profile)

/-! ## What an accepting answer establishes -/

/-- An accepting object binding establishes 01 §6 (4) (class 3 and the
    object's kind), (1) and (5) (the carrier decoder consumes all of `b`),
    (2) (exact re-encode) and (3) (the digest is derived from `b`). -/
theorem objBind_accepts (fuel : Int) (r : Ref) (kind : Int) (b : String)
    (h : (objBind fuel r kind b).ok = 1) :
    r.cls = 3 ∧ r.kind = kind ∧
    (∃ o p, objDec fuel kind b = .ok (o, p) ∧ p = b.length ∧ objEnc o = b) ∧
    Rcic.TypedRef.deriveDigest 3 kind b = r.digest := by
  unfold objBind at h
  by_cases h1 : r.cls ≠ 3
  · rw [if_pos h1] at h
    have h' : (0 : Int) = 1 := h
    exact absurd h' (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : r.kind ≠ kind
    · rw [if_pos h2] at h
      have h' : (0 : Int) = 1 := h
      exact absurd h' (by decide)
    · rw [if_neg h2] at h
      cases hd : objDec fuel kind b with
      | error c =>
        rw [hd] at h
        have h' : (0 : Int) = 1 := h
        exact absurd h' (by decide)
      | ok v =>
        obtain ⟨o, p⟩ := v
        rw [hd] at h
        dsimp only at h
        by_cases h3 : p ≠ b.length
        · rw [if_pos h3] at h
          have h' : (0 : Int) = 1 := h
          exact absurd h' (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : objEnc o ≠ b
          · rw [if_pos h4] at h
            have h' : (0 : Int) = 1 := h
            exact absurd h' (by decide)
          · rw [if_neg h4] at h
            by_cases h5 : Rcic.TypedRef.deriveDigest 3 kind b ≠ r.digest
            · rw [if_pos h5] at h
              have h' : (0 : Int) = 1 := h
              exact absurd h' (by decide)
            · exact ⟨Decidable.of_not_not h1, Decidable.of_not_not h2,
                ⟨o, p, rfl, Decidable.of_not_not h3, Decidable.of_not_not h4⟩, Decidable.of_not_not h5⟩

end Rcic.Scm.BoundProg

/-! ## Pins: apps/rcic-scm-bound-program/rcic_scm_bound_program_corpus.json, 47 rows

Hand-transcribed (§18.3 rule 4). The programs and byte strings are built
the way the corpus builds them: `parts p` encodes a program's catalog,
group, root and bundle with `objEnc`, the refs the root names carry
`deriveDigest`, and `rf b k` is a class-3 ref with the digest of `b` at kind
`k` (always derived at class 3, also for the refs of another class in rows
2 and 22). The corpus' bytes and digests come from the engine (`rcic.scm_obj_enc`,
`rcic.derive`); the two are compared row for row. Every row runs at fuel 64
under profile `SCM-Core-0` except row 39 (fuel 1). -/

namespace Rcic.Scm.BoundProg.Pins
open Rcic.Scm Rcic.Scm.BoundProg Rcic.BoundObject

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def li (n : Int) : RawExpr := .lit (.i n) .i64
def lb (b : Int) : RawExpr := .lit (.b b) .bool
def ls (s : String) : RawExpr := .lit (.s s) .str
def v (i : Int) : RawExpr := .var i
def P0 : String := "SCM-Core-0"
def P1 : String := "SCM-Core-1"
def dg (b : String) (k : Int) : String := Rcic.TypedRef.deriveDigest 3 k b
def rf (b : String) (k : Int) (c : Int := 3) : Ref := ⟨c, k, Rcic.TypedRef.deriveDigest 3 k b⟩
def noRef : Ref := ⟨0, 0, ""⟩
def emptyProg : RawProg := ⟨[], [], [], 0⟩
def no (c : String) : BPOut := bpRefuse c

def CAT : List CatalogEntry := [⟨"bad_input", unitTy⟩, ⟨"range_violation", I⟩]
def fAdd : RawFnDef := ⟨[I, I], I, .prim "add" [v 0, v 1]⟩
def fCall : RawFnDef := ⟨[], I, .call (.local 0) [li 1, li 2]⟩
def PROG : RawProg := ⟨[fAdd, fCall], [], CAT, 1⟩
def FIXREC : CoreTy := .record [("converged", B), ("state", I), ("steps", I)]
def tAll : CoreTy := .record [("s", I), ("f", FIXREC)]
def fAll : RawFnDef := ⟨[.list I], tAll,
  .letE (.fold (v 0) (li 0) (.prim "add" [v 0, v 1]))
    (.recordE ["s", "f"] [
      .handle "range_violation"
        (.ifE (.prim "lt" [v 0, li 0]) (.raise "range_violation" (v 0) I)
          (.fst (.pair (v 0) (.matchE (.inj 0 [I, B] (li 1)) [v 0, li 0]))))
        (v 0),
      .fix (.snd (.pair (lb 1) (li 0))) (.field (.recordE ["n"] [li 3]) 0) (.prim "lt" [li 2, v 0])
        (.prim "add" [v 0, .call (.local 1) [.cons (li 1) (.nil I)]])])⟩
def fLen : RawFnDef := ⟨[.list I], I, .fold (v 0) (li 0) (.prim "add" [v 1, li 1])⟩
def PROG_ALL : RawProg := ⟨[fAll, fLen], [], CAT, 0⟩
def EXT : List ExtSig := [⟨"ext.len", [Str], I⟩]
def PROG_EXT : RawProg := ⟨[⟨[], I, .call (.ext "ext.len") [ls "a"]⟩], EXT, CAT, 0⟩
def PROG_BAD : RawProg := ⟨[⟨[], B, li 1⟩], [], CAT, 0⟩
def PROG_RAISE : RawProg := ⟨[⟨[], I, .raise "zz_missing" (.lit (.r []) unitTy) I⟩], [], CAT, 0⟩

structure Parts where
  cb : String
  gb : String
  rb : String
  bb : String

def parts (p : RawProg) (profile : String := P0) (gprofile : String := profile) (member : Int := p.entry)
    (cat : List CatalogEntry := p.catalog) : Parts :=
  let cb := objEnc (.catalog cat)
  let gb := objEnc (.group gprofile p.ext p.fns)
  let rb := objEnc (.root profile (dg cb 18) (dg gb 19) member)
  ⟨cb, gb, rb, objEnc (.bundle rb cb [gb])⟩

def Pp : Parts := parts PROG
def cb : String := Pp.cb
def gb : String := Pp.gb
def rb : String := Pp.rb
def bb : String := Pp.bb
def GX : String := (parts PROG_EXT).gb
def G1 : String := (parts PROG P1).gb
def R1 : String := (parts PROG P1).rb
def UNS : String := objEnc (.catalog CAT.reverse)
def DUP : String := objEnc (.catalog [⟨"bad_input", unitTy⟩, ⟨"bad_input", unitTy⟩])
def GNC : String := "G010:SCM-Core-0" ++ gb.drop "G10:SCM-Core-0".length
def RNC : String := rb.dropRight 2 ++ "01;"
def PA : Parts := parts PROG_ALL

def f0 (r : Ref) (b : String) : BPOut := scmBP 0 64 P0 r b noRef "" emptyProg
def f1 (r : Ref) (b : String) : BPOut := scmBP 1 64 P0 r b noRef "" emptyProg
def f2 (r : Ref) (b : String) : BPOut := scmBP 2 64 P0 r b noRef "" emptyProg
def f3 (rbytes bbytes : String) (rr : Ref := rf rbytes 20) (br : Ref := rf bbytes 21) (fuel : Int := 64) : BPOut :=
  scmBP 3 fuel P0 rr rbytes br bbytes emptyProg
def f3p (q : Parts) : BPOut := f3 q.rb q.bb
def f4 (p : RawProg) : BPOut := scmBP 4 64 P0 noRef "" noRef "" p

-- 0 a residue catalog object binds at its canonical bytes
#guard f0 (rf cb 18) cb == bpOk (.catalog CAT)
-- 1 the empty residue catalog binds
#guard f0 (rf "K0;" 18) "K0;" == bpOk (.catalog [])
-- 2 a catalog ref of another class refused
#guard f0 (rf cb 18 2) cb == no "[rcic_scm_obj_class_kind]"
-- 3 a catalog ref of another kind refused
#guard f0 (rf cb 19) cb == no "[rcic_scm_obj_class_kind]"
-- 4 a catalog digest derived from other bytes refused
#guard f0 (rf "K0;" 18) cb == no "[rcic_scm_obj_digest]"
-- 5 trailing bytes after a catalog refused
#guard f0 (rf "K0;K0;" 18) "K0;K0;" == no "[rcic_scm_obj_trailing]"
-- 6 a catalog count written with a leading zero is not canonical
#guard f0 (rf "K00;" 18) "K00;" == no "[rcic_scm_obj_noncanonical]"
-- 7 group bytes under a catalog ref refused by the object tag
#guard f0 (rf gb 18) gb == no "[rcic_scm_wire_tag]"
-- 8 empty catalog bytes refused as truncated
#guard f0 (rf "" 18) "" == no "[rcic_scm_wire_truncated]"
-- 9 06 s6 a catalog whose entries are not in ascending ref order refused
#guard f0 (rf UNS 18) UNS == no "[rcic_scm_bp_catalog_order]"
-- 10 06 s6 a catalog with a duplicate ref refused
#guard f0 (rf DUP 18) DUP == no "[rcic_scm_bp_catalog_order]"
-- 11 a function group object binds at its canonical bytes under its profile
#guard f1 (rf gb 19) gb == bpOk (.group P0 [] PROG.fns)
-- 12 a function group with external signatures binds as an object
#guard f1 (rf GX 19) GX == bpOk (.group P0 EXT PROG_EXT.fns)
-- 13 01 s6 a group under another semantics profile refused
#guard f1 (rf G1 19) G1 == no "[rcic_scm_bp_profile]"
-- 14 a group ref of another kind refused
#guard f1 (rf gb 20) gb == no "[rcic_scm_obj_class_kind]"
-- 15 a group digest derived from other bytes refused
#guard f1 (rf GX 19) gb == no "[rcic_scm_obj_digest]"
-- 16 trailing bytes after a group refused
#guard f1 (rf (gb ++ "0;") 19) (gb ++ "0;") == no "[rcic_scm_obj_trailing]"
-- 17 a group profile length written with a leading zero is not canonical
#guard f1 (rf GNC 19) GNC == no "[rcic_scm_obj_noncanonical]"
-- 18 a program root object binds at its canonical bytes under its profile
#guard f2 (rf rb 20) rb == bpOk (.root P0 (dg cb 18) (dg gb 19) 1)
-- 19 01 s6 a root under another semantics profile refused
#guard f2 (rf R1 20) R1 == no "[rcic_scm_bp_profile]"
-- 20 a root member index written with a leading zero is not canonical
#guard f2 (rf RNC 20) RNC == no "[rcic_scm_obj_noncanonical]"
-- 21 a root digest derived from other bytes refused
#guard f2 (rf R1 20) rb == no "[rcic_scm_obj_digest]"
-- 22 a root ref of another class refused
#guard f2 (rf rb 20 4) rb == no "[rcic_scm_obj_class_kind]"
-- 23 a bound program root and bundle give the typed one-group program
#guard f3p Pp == bpOk (.bound PROG I)
-- 24 a root ref with a digest of other bytes refused
#guard f3 rb bb (rr := rf R1 20) == no "[rcic_scm_obj_digest]"
-- 25 a bundle ref with a digest of other bytes refused
#guard f3 rb bb (br := rf rb 21) == no "[rcic_scm_obj_digest]"
-- 26 bundle_root_exact a bundle whose root is another root refused
#guard f3 rb (parts { PROG with entry := 0 }).bb == no "[rcic_scm_bp_root_mismatch]"
-- 27 a bundle whose catalog member is not the root's catalog refused
#guard f3 rb (objEnc (.bundle rb (parts PROG (cat := [⟨"bad_input", unitTy⟩])).cb [gb])) == no "[rcic_scm_obj_digest]"
-- 28 a bundle whose group member is not the root's group refused
#guard f3 rb (objEnc (.bundle rb cb [GX])) == no "[rcic_scm_obj_digest]"
-- 29 a bundle with a group beyond the one-group closure refused
#guard f3 rb (objEnc (.bundle rb cb [gb, gb])) == no "[rcic_scm_bp_closure]"
-- 30 a bundle without the entry group refused
#guard f3 rb (objEnc (.bundle rb cb [])) == no "[rcic_scm_bp_closure]"
-- 31 a group with external signatures has no one-group closure refused
#guard f3p (parts PROG_EXT) == no "[rcic_scm_bp_external]"
-- 32 a root whose entry member is outside the group refused
#guard f3p (parts PROG (member := 5)) == no "[rcic_scm_bp_entry]"
-- 33 06 s7 a bundle whose group does not type refused by typing
#guard f3p (parts PROG_BAD) == no "[rcic_scm_typing_mismatch]"
-- 34 06 s7 a group raising a ref outside the catalog refused by typing
#guard f3p (parts PROG_RAISE) == no "[rcic_scm_typing_residue_ref]"
-- 35 01 s6 a program under another semantics profile refused at the root
#guard f3p (parts PROG P1) == no "[rcic_scm_bp_profile]"
-- 36 01 s6 a group profile that differs from the root profile refused
#guard f3p (parts PROG (gprofile := P1)) == no "[rcic_scm_bp_profile]"
-- 37 06 s6 a bundle whose catalog is not in ascending order refused
#guard f3p (parts PROG (cat := CAT.reverse)) == no "[rcic_scm_bp_catalog_order]"
-- 38 trailing bytes after a bundle refused
#guard f3 rb (bb ++ "0;") == no "[rcic_scm_obj_trailing]"
-- 39 a bundle nested deeper than the fuel refused not decided  (fuel 1)
#guard f3 rb bb (fuel := 1) == no "[rcic_scm_wire_fuel]"
-- 40 building a bound program gives root and bundle bytes that bind
#guard f4 PROG == bpOk (.built (dg rb 20) rb (dg bb 21) bb PROG I)
-- 41 building a program with every expression family round-trips through the bundle
#guard f4 PROG_ALL == bpOk (.built (dg PA.rb 20) PA.rb (dg PA.bb 21) PA.bb PROG_ALL tAll)
-- 42 building a program with external signatures refused
#guard f4 PROG_EXT == no "[rcic_scm_bp_external]"
-- 43 building an ill-typed program refused by typing
#guard f4 PROG_BAD == no "[rcic_scm_typing_mismatch]"
-- 44 building a program whose entry is outside the group refused
#guard f4 { PROG with entry := 5 } == no "[rcic_scm_bp_entry]"
-- 45 unknown form 5 refused
#guard scmBP 5 64 P0 noRef "" noRef "" emptyProg == no "[rcic_scm_bp_unknown_form]"
-- 46 unknown form -1 refused
#guard scmBP (-1) 64 P0 noRef "" noRef "" emptyProg == no "[rcic_scm_bp_unknown_form]"

/-! `CanonicalObjectAt (objSchema k P0)` agrees with the carrier's form 0–2
    decisions on every form 0–2 row, and is inhabited at rows 0, 11 and 18
    (M-005). Decided by evaluation (SHA-256 does not reduce in the kernel;
    no `native_decide`, no extra axiom). -/
def agrees (form k : Int) (r : Ref) (b : String) : Bool :=
  decide (CanonicalObjectAt (objSchema k P0) r b) == ((scmBP form 64 P0 r b noRef "" emptyProg).ok == 1)
#guard decide (CanonicalObjectAt (objSchema 18 P0) (rf cb 18) cb)
#guard decide (CanonicalObjectAt (objSchema 19 P0) (rf gb 19) gb)
#guard decide (CanonicalObjectAt (objSchema 20 P0) (rf rb 20) rb)
#guard agrees 0 18 (rf cb 18) cb
#guard agrees 0 18 (rf "K0;" 18) "K0;"
#guard agrees 0 18 (rf cb 18 2) cb
#guard agrees 0 18 (rf cb 19) cb
#guard agrees 0 18 (rf "K0;" 18) cb
#guard agrees 0 18 (rf "K0;K0;" 18) "K0;K0;"
#guard agrees 0 18 (rf "K00;" 18) "K00;"
#guard agrees 0 18 (rf gb 18) gb
#guard agrees 0 18 (rf "" 18) ""
#guard agrees 0 18 (rf UNS 18) UNS
#guard agrees 0 18 (rf DUP 18) DUP
#guard agrees 1 19 (rf gb 19) gb
#guard agrees 1 19 (rf GX 19) GX
#guard agrees 1 19 (rf G1 19) G1
#guard agrees 1 19 (rf gb 20) gb
#guard agrees 1 19 (rf GX 19) gb
#guard agrees 1 19 (rf (gb ++ "0;") 19) (gb ++ "0;")
#guard agrees 1 19 (rf GNC 19) GNC
#guard agrees 2 20 (rf rb 20) rb
#guard agrees 2 20 (rf R1 20) R1
#guard agrees 2 20 (rf RNC 20) RNC
#guard agrees 2 20 (rf R1 20) rb
#guard agrees 2 20 (rf rb 20 4) rb

end Rcic.Scm.BoundProg.Pins
