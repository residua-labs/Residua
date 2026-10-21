/-
RCIC 06 §4 / §18 — canonical value wire and `ValueAt` (carrier
`apps/rcic-value-at`, SCM-014).

Owner text: 06 §4 "Every type has canonical wire functions: `encodeValue :
CoreVal T → Bytes`, `decodeValue : Bytes → Option (CoreVal T)` with roundtrip
and accepted-byte canonicality. Record values encode in schema order, sum
values encode constructor index plus payload, and strings reject invalid or
noncanonical UTF-8." 06 §18 "`SemanticValue(T) := Σ value_bytes, ValueAt(T,
value_bytes)`"; `ValueAt` is an R-CIC proposition over bound refs and
canonical bytes.

This carrier's value fragment (its APP.md): tag 0 a u32 int `i:<dec>`, tag 1 a
string `s:<str>`, tag 2 an int/str pair `p:<k:v>|<k:v>` in key order.

PIN (M-002): `valueAt` is `rcic.value_at form tag class kind digest int_val
str_val left_tag left_int left_str right_tag right_int right_str wire`, 26
rows below; the bind form uses `RcicTypedRef.deriveDigest` and
`RcicBoundObject.canonBytesOk` / `canonPartOk` (landed, pinned).
STAND-IN (#6029 K2 HOLD item 1, K2 decision): this file pins a carrier
stand-in (M-002). It is NOT the 06 §18 / §19 object of the same name: those are
stated over bound refs and canonical core-wire bytes and are NOT TRANSCRIBED
until K3b/K3c (see `ScmRawRelations`). The table below maps the CARRIER's
rules; the 06 sections are those the carrier cites.

CARRIER RULE TABLE (rcic-value-at → Lean):
  §4 encodeValue (per instance: the wire IS the encoding of the presented
        value)                                   → form 0 `encodeCheck`
  §4 decodeValue, accepted-byte canonicality (no duplicate / unknown field,
        no trailing bytes, minimal decimal, key order) → form 1 `decode`
  the carrier's form 2 bind (cites §18 ValueAt; is the `k:v` stand-in,
        "THIS slice's stand-in, not a checked codec" per its APP.md)
                                                 → form 2 `bind` (decode +
        re-derived typed-ref digest)
  record / sum / bytes / UTF-8 clauses           → outside the carrier's
        three-tag fragment (its DOES NOT DECIDE); the full value grammar is
        the core wire `ScmWire` (06 §17)
-/
import rcic.RcicBoundObject

namespace Rcic.Scm.ValueAt
open Rcic.BoundObject

def keyOf (p : String) : String := (p.splitOn ":").headD ""
def valOf (p : String) : String := ((p.splitOn ":").drop 1).headD ""
def u32Fit (x : Int) : Bool := 0 ≤ x && x < 4294967296
def digitsOk (s : String) : Bool := 0 < s.length && s.length ≤ 64 && s.toList.all Char.isDigit
def decCanonical (d : String) : Bool :=
  d.length ≤ 63 && d.length > 0 && digitsOk d && (d = "0" || d.get 0 ≠ '0')
def decParsed (d : String) : Int := if d.length ≤ 10 then d.toInt?.getD 0 else -1
def decInRange (d : String) : Bool := u32Fit (decParsed d)
def emptyPart (ps : List String) : Bool := ps.any (· = "")
def partsShaped (ps : List String) : Bool := ps.all canonPartOk
def dupKey (ps : List String) : Bool :=
  let rec go : List String → List String → Bool
    | [], _ => false
    | p :: rest, seen => if seen.contains (keyOf p) then true else go rest (seen ++ [keyOf p])
  go ps []
def unknownKey (ps : List String) (a b : String) : Bool := ps.any (fun p => keyOf p ≠ a && keyOf p ≠ b)
def intFieldOk (p : String) (n : Int) : Bool := keyOf p = "i" && decCanonical (valOf p) && decParsed (valOf p) = n
def strFieldOk (p : String) (s : String) : Bool := keyOf p = "s" && valOf p = s
def leafFieldOk (tag n : Int) (s p : String) : Bool :=
  if tag = 0 then intFieldOk p n else if tag = 1 then strFieldOk p s else false
def tagKey (t : Int) : String := if t = 0 then "i" else if t = 1 then "s" else ""

def pairRestOk (lt li : Int) (ls : String) (rt ri : Int) (rs : String) (rest : String) : Bool :=
  match rest.splitOn "|" with
  | [p1, p2] =>
    if emptyPart [p1, p2] || !partsShaped [p1, p2] then false else
    let k1 := keyOf p1
    let k2 := keyOf p2
    if !(decide (k1 < k2)) then false
    else if k1 = tagKey lt then k2 = tagKey rt && leafFieldOk lt li ls p1 && leafFieldOk rt ri rs p2
    else if k1 = tagKey rt then k2 = tagKey lt && leafFieldOk rt ri rs p1 && leafFieldOk lt li ls p2
    else false
  | _ => false

structure VOut where
  ok : Int
  form : Int
  tag : Int
  digest : String
  wire : String
  code : String
  deriving BEq

def vOk (form tag : Int) (d w : String) : VOut := ⟨1, form, tag, d, w, ""⟩
def vNo (form tag : Int) (d w code : String) : VOut := ⟨0, form, tag, d, w, code⟩

def leafEncode (form tag : Int) (wire : String) (fieldOk : String → Bool) : VOut :=
  match wire.splitOn "|" with
  | [p] =>
    if emptyPart [p] then vNo form tag "" wire "[rcic_value_at_encode_mismatch]"
    else if partsShaped [p] && fieldOk p then vOk form tag "" wire
    else vNo form tag "" wire "[rcic_value_at_encode_mismatch]"
  | _ => vNo form tag "" wire "[rcic_value_at_encode_mismatch]"

/-- Form 0: the wire is the canonical encoding of the presented value. -/
def encodeCheck (form tag iv : Int) (sv : String) (lt li : Int) (ls : String) (rt ri : Int) (rs wire : String) : VOut :=
  if tag = 0 then
    if !u32Fit iv then vNo form tag "" wire "[rcic_value_at_range]"
    else leafEncode form tag wire (fun p => intFieldOk p iv)
  else if tag = 1 then leafEncode form tag wire (fun p => strFieldOk p sv)
  else if tag = 2 then
    if !(lt = 0 || lt = 1) || !(rt = 0 || rt = 1) then vNo form tag "" wire "[rcic_value_at_unknown_tag]"
    else if !(if lt = 0 then u32Fit li else true) then vNo form tag "" wire "[rcic_value_at_range]"
    else if !(if rt = 0 then u32Fit ri else true) then vNo form tag "" wire "[rcic_value_at_range]"
    else if wire.take 2 = "p:" && pairRestOk lt li ls rt ri rs (wire.drop 2) then vOk form tag "" wire
    else vNo form tag "" wire "[rcic_value_at_encode_mismatch]"
  else vNo form tag "" wire "[rcic_value_at_unknown_tag]"

def decodeLeaf (form tag : Int) (key wire : String) : VOut :=
  let ps := wire.splitOn "|"
  if emptyPart ps then vNo form tag "" wire "[rcic_value_at_trailing_bytes]"
  else if !partsShaped ps then vNo form tag "" wire "[rcic_value_at_trailing_bytes]"
  else if dupKey ps then vNo form tag "" wire "[rcic_value_at_duplicate_field]"
  else if unknownKey ps key key then vNo form tag "" wire "[rcic_value_at_unknown_field]"
  else if !canonBytesOk wire then vNo form tag "" wire "[rcic_value_at_roundtrip]"
  else if key = "i" then
    let d := valOf (ps.getLastD "")
    if !decCanonical d then vNo form tag "" wire "[rcic_value_at_roundtrip]"
    else if decInRange d then vOk form tag "" wire
    else vNo form tag "" wire "[rcic_value_at_range]"
  else vOk form tag "" wire

def decodePair (form tag : Int) (wire : String) : VOut :=
  if wire.take 2 ≠ "p:" then vNo form tag "" wire "[rcic_value_at_unknown_field]" else
  let rest := wire.drop 2
  let ps := rest.splitOn "|"
  if emptyPart ps then vNo form tag "" wire "[rcic_value_at_trailing_bytes]"
  else if !partsShaped ps then vNo form tag "" wire "[rcic_value_at_trailing_bytes]"
  else if dupKey ps then vNo form tag "" wire "[rcic_value_at_duplicate_field]"
  else if unknownKey ps "i" "s" then vNo form tag "" wire "[rcic_value_at_unknown_field]"
  else if ps.length ≠ 2 || !canonBytesOk rest then vNo form tag "" wire "[rcic_value_at_roundtrip]"
  else
    let d := valOf (ps.headD "")
    if !decCanonical d then vNo form tag "" wire "[rcic_value_at_roundtrip]"
    else if decInRange d then vOk form tag "" wire
    else vNo form tag "" wire "[rcic_value_at_range]"

/-- Form 1: decode with accepted-byte canonicality. -/
def decode (form tag : Int) (wire : String) : VOut :=
  if tag = 0 then decodeLeaf form tag "i" wire
  else if tag = 1 then decodeLeaf form tag "s" wire
  else if tag = 2 then decodePair form tag wire
  else vNo form tag "" wire "[rcic_value_at_unknown_tag]"

/-- Form 2: `ValueAt` over a bound ref — decoded, and the typed-ref digest
    re-derived from the complete wire. -/
def bind (form tag cls kind : Int) (digest wire : String) : VOut :=
  let dc := decode form tag wire
  if dc.ok ≠ 1 then dc
  else if kind < 0 then vNo form tag "" wire "[typed_ref_unknown_kind]"
  else if !classOk cls then vNo form tag "" wire "[typed_ref_unknown_class]"
  else if Rcic.TypedRef.deriveDigest cls.toNat kind wire = digest then vOk form tag digest wire
  else vNo form tag digest wire "[rcic_value_at_digest_mismatch]"

def valueAt (form tag cls kind : Int) (digest : String) (iv : Int) (sv : String) (lt li : Int) (ls : String)
    (rt ri : Int) (rs wire : String) : VOut :=
  if form = 0 then encodeCheck form tag iv sv lt li ls rt ri rs wire
  else if form = 1 then decode form tag wire
  else if form = 2 then bind form tag cls kind digest wire
  else vNo form tag digest wire "[rcic_value_at_unknown_form]"

/-! ## Pins: apps/rcic-value-at/rcic_value_at_corpus.json, 26 rows -/

namespace Pins
/-- `enc tag wire iv sv lt li ls rt ri rs` with the corpus' zero defaults. -/
def enc (tag : Int) (wire : String) (iv : Int := 0) (sv : String := "") (lt li : Int := 0) (ls : String := "")
    (rt ri : Int := 0) (rs : String := "") : VOut := valueAt 0 tag 0 0 "" iv sv lt li ls rt ri rs wire
def dec (tag : Int) (wire : String) : VOut := valueAt 1 tag 0 0 "" 0 "" 0 0 "" 0 0 "" wire

-- 0 SCM-014 soundness encode int ok roundtrip (06 section 4)
#guard enc 0 "i:5" 5 == vOk 0 0 "" "i:5"
-- 1 SCM-014 encode int zero ok (06 section 4)
#guard enc 0 "i:0" 0 == vOk 0 0 "" "i:0"
-- 2 SCM-014 encode int u32 max ok (06 section 4)
#guard enc 0 "i:4294967295" 4294967295 == vOk 0 0 "" "i:4294967295"
-- 3 SCM-014 encode str ok (06 section 4)
#guard enc 1 "s:hi" 0 "hi" == vOk 0 1 "" "s:hi"
-- 4 SCM-014 encode pair int-str ok (06 section 4)
#guard enc 2 "p:i:5|s:hi" 0 "" 0 5 "" 1 0 "hi" == vOk 0 2 "" "p:i:5|s:hi"
-- 5 SCM-014 encode pair str-int component order resolved ascending (06 section 4)
#guard enc 2 "p:i:5|s:hi" 0 "" 1 0 "hi" 0 5 "" == vOk 0 2 "" "p:i:5|s:hi"
-- 6 SCM-014 encode int out of u32 range refused (06 section 4)
#guard enc 0 "i:4294967296" 4294967296 == vNo 0 0 "" "i:4294967296" "[rcic_value_at_range]"
-- 7 SCM-014 encode int mismatch refused (06 section 4)
#guard enc 0 "i:6" 5 == vNo 0 0 "" "i:6" "[rcic_value_at_encode_mismatch]"
-- 8 SCM-014 encode str mismatch refused (06 section 4)
#guard enc 1 "s:bye" 0 "hi" == vNo 0 1 "" "s:bye" "[rcic_value_at_encode_mismatch]"
-- 9 SCM-014 encode pair component mismatch refused (06 section 4)
#guard enc 2 "p:i:6|s:hi" 0 "" 0 5 "" 1 0 "hi" == vNo 0 2 "" "p:i:6|s:hi" "[rcic_value_at_encode_mismatch]"
-- 10 SCM-014 encode unknown tag refused (06 section 4)
#guard enc 7 "i:5" == vNo 0 7 "" "i:5" "[rcic_value_at_unknown_tag]"
-- 11 SCM-014 decode int ok roundtrip (06 section 4 / 19 L409 per-instance)
#guard dec 0 "i:5" == vOk 1 0 "" "i:5"
-- 12 SCM-014 decode str ok (06 section 4)
#guard dec 1 "s:hi" == vOk 1 1 "" "s:hi"
-- 13 SCM-014 decode pair ok (06 section 4)
#guard dec 2 "p:i:5|s:hi" == vOk 1 2 "" "p:i:5|s:hi"
-- 14 GM-CODEC-002 decode duplicate field refused never last-wins deduped (06 section 4)
#guard dec 0 "i:5|i:7" == vNo 1 0 "" "i:5|i:7" "[rcic_value_at_duplicate_field]"
-- 15 GM-CODEC-003 decode trailing separator refused never trimmed (06 section 4)
#guard dec 0 "i:5|" == vNo 1 0 "" "i:5|" "[rcic_value_at_trailing_bytes]"
-- 16 GM-CODEC-001 decode unknown field refused (06 section 4)
#guard dec 0 "u:1" == vNo 1 0 "" "u:1" "[rcic_value_at_unknown_field]"
-- 17 SCM-014 decode nonminimal decimal refused no repair accepted-byte canonicality (06 section 4)
#guard dec 0 "i:007" == vNo 1 0 "" "i:007" "[rcic_value_at_roundtrip]"
-- 18 SCM-014 decode pair unsorted inner refused re-encode differs (06 section 4)
#guard dec 2 "p:s:hi|i:5" == vNo 1 2 "" "p:s:hi|i:5" "[rcic_value_at_roundtrip]"
-- 19 SCM-014 decode int above u32 refused (06 section 4)
#guard dec 0 "i:99999999999" == vNo 1 0 "" "i:99999999999" "[rcic_value_at_range]"
-- 20 SCM-014 decode nondigit value refused no repair (06 section 4)
#guard dec 0 "i:1x3" == vNo 1 0 "" "i:1x3" "[rcic_value_at_roundtrip]"
-- 21 GM-CODEC-002 decode pair inner duplicate refused (06 section 4)
#guard dec 2 "p:i:5|i:7" == vNo 1 2 "" "p:i:5|i:7" "[rcic_value_at_duplicate_field]"
-- 22 SCM-014 section 18 bind ok sigma carries ValueAt witness (06 section 18)
#guard valueAt 2 0 0 0 "4e36bce2fed1bcb28834441f17ddc6e0bef43aad07d8bb5e05d152d456d3ea9b" 0 "" 0 0 "" 0 0 "" "i:5"
  == vOk 2 0 "4e36bce2fed1bcb28834441f17ddc6e0bef43aad07d8bb5e05d152d456d3ea9b" "i:5"
-- 23 SCM-014 section 18 bind digest mismatch refused (06 section 18)
#guard valueAt 2 0 0 0 "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" 0 "" 0 0 "" 0 0 "" "i:5"
  == vNo 2 0 "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" "i:5" "[rcic_value_at_digest_mismatch]"
-- 24 unknown form refused
#guard valueAt 9 0 0 0 "" 0 "" 0 0 "" 0 0 "" "i:5" == vNo 9 0 "" "i:5" "[rcic_value_at_unknown_form]"
-- 25 V3b decode two-colon part s:a:b refused never admits trailing segment (RED-set 2026-08-29 06 section 4)
#guard dec 1 "s:a:b" == vNo 1 1 "" "s:a:b" "[rcic_value_at_trailing_bytes]"
end Pins

end Rcic.Scm.ValueAt
