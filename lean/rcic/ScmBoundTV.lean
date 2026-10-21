/-
RCIC 06 §18 (bound core type, semantic value) over 01 §6 — the carrier
`apps/rcic-scm-type-value` (#6029 K3b, segment 1).

Owner text:
  06 §18 "Bound core type": `BoundCoreType { type_ref, type_bytes, type_at :
      CanonicalCoreTypeAt(type_ref,type_bytes) }`; "Semantic value":
      `SemanticValue(T : BoundCoreType) := Σ value_bytes : Bytes,
      ValueAt(T,value_bytes)`; the predicates "are R-CIC propositions over
      bound refs and canonical bytes" (06:402).
  01 §6 `CanonicalObjectAt(ref, bytes)`: (1) canonical decode under the ref's
      schema; (2) exact re-encode; (3) derived address equality; (4)
      class/kind/profile consistency; (5) no trailing or unknown fields.
  00 §19.7 E-06Wire: the §18 objects use the §17 core wire as
      `apps/rcic-scm-wire` encodes it (here: `ScmWire`'s `dec`, `encTy`,
      `encVal`, called, not restated).

PIN (M-002): `scmTV` is `rcic.scm_tv form fuel ref bytes tref tbytes x`
(43 rows in `Pins`, hand-transcribed, §18.3 rule 4). Form 0 decides
CanonicalCoreTypeAt at the registered kind code (class 3, kind 16;
`docs/rcic/SEMANTIC_OBJECT_KIND_REGISTRY.md`, a `[spec_ambiguity]`: 01 §2
enumerates no semanticObject kinds);
form 1 decides ValueAt(T, bytes) after binding T; forms 2 / 3 construct a
bound type / a value's canonical bytes and re-check them through forms 0 / 1.
The carrier's `x` is a type record in form 2 and a value record in form 3:
here two arguments, `xt` and `xv`.

`coreTypeSchema` is the schema whose `CanonicalObjectAt` form 0 decides. Its
decode runs the carrier decoder with fuel equal to the input length (every
nesting level consumes a character); the carrier's own `fuel` refusal is
"input beyond the bound is refused, not decided", so the agreement pins
below skip the fuel row.

The §18 structures `BoundCoreType`, `CanonicalCoreTypeAt`, `ValueAt`,
`SemanticValue` as R-CIC propositions are transcribed in
`ScmBoundCoreTV` (#6029 K3c snapshot, pinned to this carrier). Still NOT
TRANSCRIBED: the §19 directions (encode intrinsic value → ValueAt,
ValueAt → unique intrinsic value). The wire's
bounds (lists of at most 1024 elements, numbers within 24 characters) are a
premise any encode → ValueAt statement needs: rows 36 and 39 show objects
beyond the list bound have no canonical bytes.
-/
import rcic.ScmWire
import rcic.RcicBoundObject

namespace Rcic.Scm.BoundTV
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject

/-- The recorded kind code of a core type (class 3, `semanticObject`). -/
def coreTypeKind : Int := 16

/-- The carrier's output record `{ok, t, v, bytes, digest, code}`. -/
structure TVOut where
  ok : Int
  t : CoreTy
  v : Val
  bytes : String
  digest : String
  code : String
  deriving BEq

def unitVal : Val := .r []
def tvOk (t : CoreTy) (v : Val) (b d : String) : TVOut := ⟨1, t, v, b, d, ""⟩
def tvRefuse (c : String) : TVOut := ⟨0, unitTy, unitVal, "", "", c⟩

/-- `rcic.scm_wire_dec kind bytes 0 fuel`: the decoded item and its end
    position. -/
def dec0 (kind : Nat) (fuel : Int) (s : String) : Except String (Item × Nat) :=
  let cs := s.toList.toArray
  dec cs (gasFor fuel cs.size) kind fuel 0

/-- `rcic.scm_tv_type_at`: CanonicalCoreTypeAt(ref, bytes), in the carrier's
    order: class/kind (4), decode (1), whole input (5), re-encode (2),
    derived digest (3). -/
def typeAt (fuel : Int) (r : Ref) (bytes : String) : TVOut :=
  if r.cls ≠ 3 then tvRefuse "[rcic_scm_tv_class_kind]" else
  if r.kind ≠ coreTypeKind then tvRefuse "[rcic_scm_tv_class_kind]" else
  match dec0 0 fuel bytes with
  | .error c => tvRefuse c
  | .ok (it, p) =>
    if p ≠ bytes.length then tvRefuse "[rcic_scm_tv_trailing]" else
    if encTy (asTy it) ≠ bytes then tvRefuse "[rcic_scm_tv_noncanonical]" else
    if Rcic.TypedRef.deriveDigest 3 16 bytes ≠ r.digest then tvRefuse "[rcic_scm_tv_digest]" else
    tvOk (asTy it) unitVal bytes r.digest

/-- `rcic.scm_tv_value_at`: ValueAt(T, bytes) for a bound `T` (`tt`, an
    accepting `typeAt` record): decode, whole input, re-encode, value of
    type (`toCore`, the model of `rcic.scm_val_of_ty` pinned in K2). -/
def valueAt (fuel : Int) (tt : TVOut) (bytes : String) : TVOut :=
  match dec0 1 fuel bytes with
  | .error c => tvRefuse c
  | .ok (it, p) =>
    if p ≠ bytes.length then tvRefuse "[rcic_scm_tv_trailing]" else
    if encVal (asVal it) ≠ bytes then tvRefuse "[rcic_scm_tv_noncanonical]" else
    if (toCore tt.t (asVal it)).isNone then tvRefuse "[rcic_scm_tv_value_type]" else
    tvOk tt.t (asVal it) bytes tt.digest

/-- `rcic.scm_tv`, the carrier entry point. -/
def scmTV (form fuel : Int) (r : Ref) (bytes : String) (tr : Ref) (tbytes : String)
    (xt : CoreTy) (xv : Val) : TVOut :=
  if form < 0 then tvRefuse "[rcic_scm_tv_unknown_form]" else
  if form > 3 then tvRefuse "[rcic_scm_tv_unknown_form]" else
  if form = 0 then typeAt fuel r bytes else
  if form = 2 then
    let b := encTy xt
    typeAt fuel ⟨3, 16, Rcic.TypedRef.deriveDigest 3 16 b⟩ b
  else
    let tt := typeAt fuel tr tbytes
    if tt.ok = 0 then tt
    else if form = 1 then valueAt fuel tt bytes
    else valueAt fuel tt (encVal xv)

/-! ## The schema form 0 decides (01 §6 over the core-wire type grammar) -/

/-- The type a prefix of `b` decodes to, and where it ends. -/
def prefixTy (b : String) : Option (CoreTy × Nat) :=
  match dec0 0 b.length b with
  | .ok (it, p) => some (asTy it, p)
  | .error _ => none

def coreTypeSchema : ObjSchema where
  Obj := CoreTy
  decode b := (prefixTy b).map Prod.fst
  encode := encTy
  exactFields b :=
    match prefixTy b with
    | some (_, p) => p == b.length
    | none => false
  consistent c k _ := c == 3 && k == coreTypeKind

/-! ## What an accepting answer establishes -/

/-- An accepting form-0 decision establishes 01 §6 (4) (class 3, kind 16),
    (1) and (5) (the carrier decoder consumes all of `b` at the given fuel),
    (2) (the decoded type re-encodes to exactly `b`) and (3) (the digest is
    derived from `b`). -/
theorem typeAt_accepts (fuel : Int) (r : Ref) (b : String) (h : (typeAt fuel r b).ok = 1) :
    r.cls = 3 ∧ r.kind = coreTypeKind ∧
    (∃ it p, dec0 0 fuel b = .ok (it, p) ∧ p = b.length ∧ encTy (asTy it) = b) ∧
    Rcic.TypedRef.deriveDigest 3 16 b = r.digest := by
  unfold typeAt at h
  by_cases h1 : r.cls ≠ 3
  · rw [if_pos h1] at h
    have h' : (0 : Int) = 1 := h
    exact absurd h' (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : r.kind ≠ coreTypeKind
    · rw [if_pos h2] at h
      have h' : (0 : Int) = 1 := h
      exact absurd h' (by decide)
    · rw [if_neg h2] at h
      cases hd : dec0 0 fuel b with
      | error c =>
        rw [hd] at h
        have h' : (0 : Int) = 1 := h
        exact absurd h' (by decide)
      | ok v =>
        obtain ⟨it, p⟩ := v
        rw [hd] at h
        dsimp only at h
        by_cases h3 : p ≠ b.length
        · rw [if_pos h3] at h
          have h' : (0 : Int) = 1 := h
          exact absurd h' (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : encTy (asTy it) ≠ b
          · rw [if_pos h4] at h
            have h' : (0 : Int) = 1 := h
            exact absurd h' (by decide)
          · rw [if_neg h4] at h
            by_cases h5 : Rcic.TypedRef.deriveDigest 3 16 b ≠ r.digest
            · rw [if_pos h5] at h
              have h' : (0 : Int) = 1 := h
              exact absurd h' (by decide)
            · exact ⟨Decidable.of_not_not h1, Decidable.of_not_not h2,
                ⟨it, p, rfl, Decidable.of_not_not h3, Decidable.of_not_not h4⟩, Decidable.of_not_not h5⟩

end Rcic.Scm.BoundTV

/-! ## Pins: apps/rcic-scm-type-value/rcic_scm_type_value_corpus.json, 43 rows

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with its prefix
("SCM-013 06 s18 ", "SCM-014 06 s18 " or "SCM-001 06 s4 ") dropped. Every row
runs at fuel 64 except rows 13 (fuel 2) and 33 (fuel 0). A ref built by
`rf b` carries the digest `deriveDigest 3 16 b` (the corpus' refs carry the
digest the engine's `rcic.derive 3 16 b` returned; the two are compared row
for row). `ok …` / `no code` are the carrier's two record shapes. -/

namespace Rcic.Scm.BoundTV.Pins
open Rcic.Scm Rcic.Scm.BoundTV Rcic.BoundObject

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def Y : CoreTy := .bytes
def rf (b : String) (c : Int := 3) (k : Int := 16) : Ref := ⟨c, k, Rcic.TypedRef.deriveDigest c.toNat k b⟩
def noRef : Ref := ⟨0, 0, ""⟩
def T : CoreTy := .record [("a", .list (.pair I (.sum [B, Str]))), ("b", Y)]
def TB : String := "R2;1:aLPiS2;bs1:by"
def V : Val := .r [.l [.p (.i 1) (.j 1 (.s "x"))], .y [0, 255]]
def VB : String := "R2;L1;PI1;J1;T1:xY2;0;255;"
def ok (t : CoreTy) (v : Val) (b : String) (tb : String := b) : TVOut := tvOk t v b (rf tb).digest
def no (c : String) : TVOut := tvRefuse c
def form0 (r : Ref) (b : String) (fuel : Int := 64) : TVOut := scmTV 0 fuel r b noRef "" unitTy unitVal
def form1 (b : String) (tr : Ref) (tb : String) (fuel : Int := 64) : TVOut := scmTV 1 fuel noRef b tr tb unitTy unitVal

-- 0 the i64 type binds at its canonical bytes
#guard form0 (rf "i") "i" == ok I unitVal "i"
-- 1 the bool type binds at its canonical bytes
#guard form0 (rf "b") "b" == ok B unitVal "b"
-- 2 the str type binds at its canonical bytes
#guard form0 (rf "s") "s" == ok Str unitVal "s"
-- 3 the bytes type binds at its canonical bytes
#guard form0 (rf "y") "y" == ok Y unitVal "y"
-- 4 a record of a list of pairs with a sum and bytes binds at its canonical bytes
#guard form0 (rf TB) TB == ok T unitVal TB
-- 5 a type ref of another class refused
#guard form0 (rf "i" 2) "i" == no "[rcic_scm_tv_class_kind]"
-- 6 a type ref of another kind refused
#guard form0 (rf "i" 3 0) "i" == no "[rcic_scm_tv_class_kind]"
-- 7 a digest derived from other bytes refused
#guard form0 (rf "b") "i" == no "[rcic_scm_tv_digest]"
-- 8 an unknown type tag refused
#guard form0 (rf "q") "q" == no "[rcic_scm_wire_tag]"
-- 9 truncated type bytes refused
#guard form0 (rf "L") "L" == no "[rcic_scm_wire_truncated]"
-- 10 trailing bytes after a type refused
#guard form0 (rf "ii") "ii" == no "[rcic_scm_tv_trailing]"
-- 11 a sum count written with a leading zero is not canonical
#guard form0 (rf "S02;ib") "S02;ib" == no "[rcic_scm_tv_noncanonical]"
-- 12 a record key length written with a leading zero is not canonical
#guard form0 (rf "R1;01:ai") "R1;01:ai" == no "[rcic_scm_tv_noncanonical]"
-- 13 a type nested deeper than the fuel refused not decided  (fuel 2)
#guard form0 (rf "LLLLi") "LLLLi" 2 == no "[rcic_scm_wire_fuel]"
-- 14 an i64 value under the bound i64 type
#guard form1 "I42;" (rf "i") "i" == ok I (.i 42) "I42;" "i"
-- 15 a negative i64 value under the bound i64 type
#guard form1 "I-7;" (rf "i") "i" == ok I (.i (-7)) "I-7;" "i"
-- 16 a bool value under the bound bool type
#guard form1 "B1;" (rf "b") "b" == ok B (.b 1) "B1;" "b"
-- 17 a str value under the bound str type
#guard form1 "T3:abc" (rf "s") "s" == ok Str (.s "abc") "T3:abc" "s"
-- 18 a bytes value under the bound bytes type
#guard form1 "Y2;1;255;" (rf "y") "y" == ok Y (.y [1, 255]) "Y2;1;255;" "y"
-- 19 the empty list under a bound list type
#guard form1 "L0;" (rf "Li") "Li" == ok (.list I) (.l []) "L0;" "Li"
-- 20 a nested record list pair sum bytes value under its bound type
#guard form1 VB (rf TB) TB == ok T V VB TB
-- 21 a sum value under a bound sum type
#guard form1 "J1;T1:x" (rf "S2;is") "S2;is" == ok (.sum [I, Str]) (.j 1 (.s "x")) "J1;T1:x" "S2;is"
-- 22 a bool value under the i64 type refused
#guard form1 "B1;" (rf "i") "i" == no "[rcic_scm_tv_value_type]"
-- 23 a one-field record value under a two-field record type refused
#guard form1 "R1;I1;" (rf "R2;1:ai1:bb") "R2;1:ai1:bb" == no "[rcic_scm_tv_value_type]"
-- 24 a sum value with an index outside the sum refused
#guard form1 "J5;I1;" (rf "S2;ib") "S2;ib" == no "[rcic_scm_tv_value_type]"
-- 25 a bool value other than 0 or 1 refused
#guard form1 "B2;" (rf "b") "b" == no "[rcic_scm_tv_value_type]"
-- 26 a bytes element above 255 refused
#guard form1 "Y1;256;" (rf "y") "y" == no "[rcic_scm_tv_value_type]"
-- 27 an i64 written with leading zeros is not canonical
#guard form1 "I007;" (rf "i") "i" == no "[rcic_scm_tv_noncanonical]"
-- 28 trailing bytes after a value refused
#guard form1 "I1;I2;" (rf "i") "i" == no "[rcic_scm_tv_trailing]"
-- 29 truncated value bytes refused
#guard form1 "PI1;" (rf "Pii") "Pii" == no "[rcic_scm_wire_truncated]"
-- 30 an i64 value beyond the i64 range refused
#guard form1 "I9223372036854775808;" (rf "i") "i" == no "[rcic_scm_wire_number]"
-- 31 a value under noncanonical type bytes refused by the type binding
#guard form1 "J0;I1;" (rf "S02;ib") "S02;ib" == no "[rcic_scm_tv_noncanonical]"
-- 32 a value under a type ref of another class refused by the type binding
#guard form1 "I1;" (rf "i" 2) "i" == no "[rcic_scm_tv_class_kind]"
-- 33 a value nested deeper than the fuel refused not decided  (fuel 0)
#guard form1 "Y1;1;" (rf "y") "y" 0 == no "[rcic_scm_wire_fuel]"
-- 34 encoding a nested type gives its canonical bytes and a binding ref
#guard scmTV 2 64 noRef "" noRef "" T unitVal == ok T unitVal TB
-- 35 encoding the i64 type gives its canonical bytes
#guard scmTV 2 64 noRef "" noRef "" I unitVal == ok I unitVal "i"
-- 36 a sum of 1025 summands has no bound object beyond the wire list bound
#guard scmTV 2 64 noRef "" noRef "" (.sum (List.replicate 1025 I)) unitVal == no "[rcic_scm_wire_bound]"
-- 37 encoding a value of a bound type gives its canonical bytes
#guard scmTV 3 64 noRef "" (rf TB) TB unitTy V == ok T V VB TB
-- 38 encoding a value not of the bound type refused
#guard scmTV 3 64 noRef "" (rf "i") "i" unitTy (.b 1) == no "[rcic_scm_tv_value_type]"
-- 39 a list of 1025 elements has no canonical value beyond the wire list bound
#guard scmTV 3 64 noRef "" (rf "Li") "Li" unitTy (.l (List.replicate 1025 (.i 1))) == no "[rcic_scm_wire_bound]"
-- 40 encoding under a type ref with another digest refused by the type binding
#guard scmTV 3 64 noRef "" (rf "b") "i" unitTy (.i 1) == no "[rcic_scm_tv_digest]"
-- 41 unknown form 4 refused
#guard scmTV 4 64 noRef "" noRef "" unitTy unitVal == no "[rcic_scm_tv_unknown_form]"
-- 42 unknown form -1 refused
#guard scmTV (-1) 64 noRef "" noRef "" unitTy unitVal == no "[rcic_scm_tv_unknown_form]"

/-! `CanonicalObjectAt coreTypeSchema` agrees with the carrier's form-0
    decision on every form-0 row but row 13 (the fuel row: the carrier
    refuses for lack of fuel, the schema decodes with enough), and it is
    inhabited at rows 0–4 (M-005). Decided by evaluation (SHA-256 does not
    reduce in the kernel; no `native_decide`, no extra axiom). -/
def agreesForm0 (r : Ref) (b : String) : Bool :=
  decide (CanonicalObjectAt coreTypeSchema r b) == ((form0 r b).ok == 1)
#guard decide (CanonicalObjectAt coreTypeSchema (rf TB) TB)
#guard agreesForm0 (rf "i") "i"
#guard agreesForm0 (rf "b") "b"
#guard agreesForm0 (rf "s") "s"
#guard agreesForm0 (rf "y") "y"
#guard agreesForm0 (rf TB) TB
#guard agreesForm0 (rf "i" 2) "i"
#guard agreesForm0 (rf "i" 3 0) "i"
#guard agreesForm0 (rf "b") "i"
#guard agreesForm0 (rf "q") "q"
#guard agreesForm0 (rf "L") "L"
#guard agreesForm0 (rf "ii") "ii"
#guard agreesForm0 (rf "S02;ib") "S02;ib"
#guard agreesForm0 (rf "R1;01:ai") "R1;01:ai"
#guard decide (CanonicalObjectAt coreTypeSchema (rf "LLLLi") "LLLLi") && (form0 (rf "LLLLi") "LLLLi" 2).ok == 0

end Rcic.Scm.BoundTV.Pins
