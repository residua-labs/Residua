/-
RCIC 01 §6 — canonical object binding (K2 prerequisite, per K0 sign-off).

Owner text (01 §6, quoted by 06 §18 "Generic binding"):
  `CanonicalObjectAt(ref, bytes) : Prop`
  `BoundObject(ref) := Σ bytes, CanonicalObjectAt(ref, bytes)`
The decision procedure is the carrier `apps/rcic-bound-object`
(`rcic.bound_object fuel form class kind left right digest store bytes`):
form 0 decides CanonicalObjectAt (class/kind validity, canonical k:v bytes,
the typed-ref digest re-derived from the complete preimage), form 1 exact
object equality over an EXPLICIT store (collision-aware: both refs resolve,
unanimously, to the witness bytes, and both are canonical at the witness),
form 2 refuses a bare digest.

The digest is `RcicTypedRef.deriveDigest` (the landed, pinned model of
`rcic.derive`), called, not restated. No hash-injectivity premise: every
statement here is about the decision procedure over complete preimages
(00 M-003).

PIN (M-002): all 15 rows of apps/rcic-bound-object/rcic_bound_object_corpus.json
below; the `kvSchema` instance of `CanonicalObjectAt` is pinned against the
carrier's form-0 decision on rows 0–6 (M-002a).

TRANSCRIPTION TABLE (01 §6 / 06 §18 → Lean):
  CanonicalObjectAt(ref, bytes) : Prop  → `CanonicalObjectAt σ ref bytes`,
    parametrized by the ref's schema `σ : ObjSchema` (property side, M-002c;
    #6029 K2 HOLD item 4); its five conjuncts are 01 §6's (1)–(5) verbatim
  BoundObject(ref) := Σ bytes, CanonicalObjectAt(ref,bytes) → `BoundObject σ`
  the carrier's `k:v` convention  → the stand-in schema `kvSchema`, NOT 01 §6's
    schema notion itself; the carrier's decision `canonicalAt` (keys
    strictly ascending, no empty key/value, no trailing separator,
    `canonBytesOk`) is pinned below and agrees with `CanonicalObjectAt
    kvSchema` on every form-0 row
  digest re-derived from the complete preimage → `canonicalAt` via
    `RcicTypedRef.deriveDigest`
  exact object equality over an explicit store (01 §5) → `exactEq`
  no ambient lookup / bare digest refused (01 §6) → form 2 of `boundObject`
-/
import rcic.RcicTypedRef

namespace Rcic.BoundObject

structure StoreEntry where
  digest : String
  bytes : String

/-- The carrier's output record `{ok, class, kind, digest, bytes, code}`. -/
structure BOut where
  ok : Int
  cls : Int
  kind : Int
  digest : String
  bytes : String
  code : String
  deriving BEq

def boundOk (c k : Int) (d b : String) : BOut := ⟨1, c, k, d, b, ""⟩
def boundRefuse (c k : Int) (d b code : String) : BOut := ⟨0, c, k, d, b, code⟩

/-- `rcic.canon_part_ok`: exactly one `:` with a nonempty key and value. -/
def canonPartOk (part : String) : Bool :=
  match part.splitOn ":" with
  | [k, v] => k.length > 0 && v.length > 0
  | _ => false

/-- `rcic.canon_bytes_ok`: every `|`-part canonical, keys strictly ascending. -/
def canonBytesOk (bytes : String) : Bool :=
  let rec go : List String → Option String → Bool
    | [], _ => true
    | p :: ps, prev =>
      if !canonPartOk p then false else
      let k := (p.splitOn ":").headD ""
      match prev with
      | none => go ps (some k)
      | some q => decide (q < k) && go ps (some k)
  go (bytes.splitOn "|") none

def classOk (c : Int) : Bool := 0 ≤ c && c ≤ 11

/-- 01 §6 decision: CanonicalObjectAt over (class, kind, digest, bytes). -/
def canonicalAt (fuel c k : Int) (digest bytes : String) : BOut :=
  if fuel < 0 then boundRefuse c k digest bytes "[rcic_bound_object_fuel]"
  else if k < 0 then boundRefuse c k digest bytes "[rcic_bound_object_unknown_kind]"
  else if !classOk c then boundRefuse c k digest bytes "[rcic_bound_object_unknown_class]"
  else if !canonBytesOk bytes then boundRefuse c k digest bytes "[rcic_bound_object_noncanonical_bytes]"
  else if Rcic.TypedRef.deriveDigest c.toNat k bytes = digest then boundOk c k digest bytes
  else boundRefuse c k digest bytes "[rcic_bound_object_digest_mismatch]"

/-- `rcic.store_scan`: found / collision over an explicit store. -/
structure Scan where
  found : Bool
  bytes : String
  collision : Bool

def storeScan (store : List StoreEntry) (d : String) : Scan :=
  store.foldl (fun acc e =>
    if e.digest = d then
      if acc.found then (if acc.bytes = e.bytes then acc else ⟨true, acc.bytes, true⟩)
      else ⟨true, e.bytes, false⟩
    else acc) ⟨false, "", false⟩

/-- 01 §5 exact object equality, collision-aware. -/
def exactEq (fuel c k : Int) (left right : String) (store : List StoreEntry) (bytes : String) : BOut :=
  if fuel < 0 then boundRefuse c k left bytes "[rcic_bound_object_fuel]" else
  let sl := storeScan store left
  if sl.collision then boundRefuse c k left bytes "[rcic_bound_object_address_collision]"
  else if !sl.found then boundRefuse c k left bytes "[rcic_bound_object_ref_not_in_store]"
  else if sl.bytes ≠ bytes then boundRefuse c k left bytes "[rcic_bound_object_address_collision]"
  else
  let sr := storeScan store right
  if sr.collision then boundRefuse c k right bytes "[rcic_bound_object_address_collision]"
  else if !sr.found then boundRefuse c k right bytes "[rcic_bound_object_ref_not_in_store]"
  else if sr.bytes ≠ bytes then boundRefuse c k right bytes "[rcic_bound_object_address_collision]"
  else
  let cl := canonicalAt (fuel - 1) c k left bytes
  if cl.ok = 0 then cl else canonicalAt (fuel - 2) c k right bytes

def boundObject (fuel form c k : Int) (left right digest : String) (store : List StoreEntry)
    (bytes : String) : BOut :=
  if form = 2 then boundRefuse c k digest "" "[rcic_bound_object_bare_q_refused]"
  else if form = 0 then canonicalAt fuel c k digest bytes
  else if form = 1 then exactEq fuel c k left right store bytes
  else boundRefuse c k digest "" "[rcic_bound_object_unknown_form]"

/-! ## 01 §6 statements -/

/-- A typed reference: class, kind, digest. -/
structure Ref where
  cls : Int
  kind : Int
  digest : String

/-- An object schema (01 §6 "the ref's schema"): its canonical decode, its
    encode, its no-trailing/unknown-field check, and the class/kind/profile
    consistency it requires of a ref. -/
structure ObjSchema where
  Obj : Type
  decode : String → Option Obj
  encode : Obj → String
  exactFields : String → Bool
  /-- (4) class/kind/profile consistency. It sees the DECODED object, so a
      schema whose objects carry a profile can check it against the ref
      (#6029 K1–K3 re-audit, carried item 2: 01 §6 says
      "class/kind/profile consistency"). -/
  consistent : Int → Int → Obj → Bool

/-- 01 §6 `CanonicalObjectAt(ref, bytes)`, the five conjuncts:
    (1) canonical decode under the ref's schema; (2) exact re-encode;
    (3) derived address equality; (4) class/kind/profile consistency;
    (5) no trailing or unknown fields. (1), (2) and (4) are one `match`:
    the decoded object re-encodes to exactly the bytes and is consistent
    with the ref's class and kind. -/
def CanonicalObjectAt (σ : ObjSchema) (r : Ref) (bytes : String) : Prop :=
  (match σ.decode bytes with
   | some o => σ.encode o = bytes ∧ σ.consistent r.cls r.kind o = true
   | none => False) ∧
  Rcic.TypedRef.deriveDigest r.cls.toNat r.kind bytes = r.digest ∧
  σ.exactFields bytes = true

instance (σ : ObjSchema) (r : Ref) (bytes : String) : Decidable (CanonicalObjectAt σ r bytes) := by
  unfold CanonicalObjectAt
  cases σ.decode bytes with
  | some o => exact inferInstanceAs (Decidable ((_ ∧ _) ∧ _))
  | none => exact inferInstanceAs (Decidable (False ∧ _))

/-- `BoundObject(ref) := Σ bytes, CanonicalObjectAt(ref, bytes)`. -/
def BoundObject (σ : ObjSchema) (r : Ref) : Type := { bytes : String // CanonicalObjectAt σ r bytes }

/-- The carrier's stand-in schema (`apps/rcic-bound-object`: "DOES NOT DECIDE
    decode under a per-schema grammar beyond the k:v|k:v convention"): an
    object is its list of `k:v` parts, canonical when `canonBytesOk`; a ref's
    class must be one of the 12 RefClasses and its kind nonnegative. -/
def kvSchema : ObjSchema where
  Obj := List String
  decode b := if canonBytesOk b then some (b.splitOn "|") else none
  encode ps := "|".intercalate ps
  exactFields b := canonBytesOk b
  consistent c k _ := classOk c && decide (0 ≤ k)

/-! ## Pins: apps/rcic-bound-object/rcic_bound_object_corpus.json, 15 rows -/

namespace Pins
def D12 : String := "1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4"
def D34 : String := "bbdce295ecb0b39fccad12af2187d61105446aa3ff1f63d06540368570985379"
def ab : String := "a:1|b:2"

-- 0 GT-ID-005 form 0 canonical accept derive reproduces digest (01 section 6)
#guard boundObject 32 0 0 0 "" "" D12 [] ab == boundOk 0 0 D12 ab
-- 1 GM-ID-003 form 0 duplicate key refused with correctly derived digest (01 section 5/6)
#guard boundObject 32 0 0 0 "" "" "7432a6d09838fca877480f4cd7066d6f508ca1b3af66d33cb125ede3c2f074cf" [] "k:1|k:2"
  == boundRefuse 0 0 "7432a6d09838fca877480f4cd7066d6f508ca1b3af66d33cb125ede3c2f074cf" "k:1|k:2"
       "[rcic_bound_object_noncanonical_bytes]"
-- 2 GT-ID-005 form 0 trailing separator refused with correctly derived digest (01 section 6 conjunct 5)
#guard boundObject 32 0 0 0 "" "" "f031ec684a0d5bf45d52fac4a2655aec267ecd3bd19222023a57481f9567dc9e" [] "a:1|"
  == boundRefuse 0 0 "f031ec684a0d5bf45d52fac4a2655aec267ecd3bd19222023a57481f9567dc9e" "a:1|"
       "[rcic_bound_object_noncanonical_bytes]"
-- 3 GT-ID-005 form 0 unsorted keys refused with correctly derived digest (01 section 6)
#guard boundObject 32 0 0 0 "" "" "d614f5a4bbd95f722a0f36b2c86e2a6d3e83d0ed6437bfa7b21fc9f2399c65aa" [] "b:2|a:1"
  == boundRefuse 0 0 "d614f5a4bbd95f722a0f36b2c86e2a6d3e83d0ed6437bfa7b21fc9f2399c65aa" "b:2|a:1"
       "[rcic_bound_object_noncanonical_bytes]"
-- 4 GT-ID-005 form 0 digest mismatch refused (01 section 6 conjunct 3)
#guard boundObject 32 0 0 0 "" "" "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" [] ab
  == boundRefuse 0 0 "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" ab
       "[rcic_bound_object_digest_mismatch]"
-- 5 GT-ID-005 form 0 unknown class refused (01 section 6 conjunct 4)
#guard boundObject 32 0 12 0 "" "" "" [] ab == boundRefuse 12 0 "" ab "[rcic_bound_object_unknown_class]"
-- 6 GT-ID-005 form 0 unknown kind refused (01 section 6 conjunct 4)
#guard boundObject 32 0 0 (-1) "" "" "" [] ab == boundRefuse 0 (-1) "" ab "[rcic_bound_object_unknown_kind]"
-- 7 GT-ID-004 form 1 exact equality both resolve both canonical accept (01 section 5)
#guard boundObject 32 1 0 0 D12 D12 "" [⟨D12, ab⟩] ab == boundOk 0 0 D12 ab
-- 8 GM-ID-003 form 1 same digest stored bytes differ from witness collision (01 section 5)
#guard boundObject 32 1 0 0 D12 D12 "" [⟨D12, "x:9|y:8"⟩] ab
  == boundRefuse 0 0 D12 ab "[rcic_bound_object_address_collision]"
-- 9 GT-ID-003 form 1 in-store same digest two byte values collision (01 section 3/5)
#guard boundObject 32 1 0 0 D12 D12 "" [⟨D12, ab⟩, ⟨D12, "x:9|y:8"⟩] ab
  == boundRefuse 0 0 D12 ab "[rcic_bound_object_address_collision]"
-- 10 GT-ID-004 form 1 left digest missing in store refused (01 section 5)
#guard boundObject 32 1 0 0 D34 D34 "" [⟨D12, ab⟩] "c:3|d:4"
  == boundRefuse 0 0 D34 "c:3|d:4" "[rcic_bound_object_ref_not_in_store]"
-- 11 GT-ID-004 form 1 right digest missing in store refused (01 section 5)
#guard boundObject 32 1 0 0 D12 D34 "" [⟨D12, ab⟩] ab
  == boundRefuse 0 0 D34 ab "[rcic_bound_object_ref_not_in_store]"
-- 12 GM-ID-004 form 2 bare q refused though store resolves it (01 section 6)
#guard boundObject 32 2 0 0 "" "" D12 [⟨D12, ab⟩] "" == boundRefuse 0 0 D12 "" "[rcic_bound_object_bare_q_refused]"
-- 13 form 9 unknown form refused
#guard boundObject 32 9 0 0 "" "" "" [] "" == boundRefuse 0 0 "" "" "[rcic_bound_object_unknown_form]"
-- 14 GT-ID-003 form 1 right resolves to other canonical bytes refused witness-vs-left-only mutant admits (B1 01 section 5)
#guard boundObject 32 1 0 0 D12 D34 "" [⟨D12, ab⟩, ⟨D34, "c:3|d:4"⟩] ab
  == boundRefuse 0 0 D34 ab "[rcic_bound_object_address_collision]"

/-! The `kvSchema` instance of `CanonicalObjectAt` agrees with the carrier's
    form-0 decision on every form-0 row (rows 0–6), and is inhabited at row
    0's object, so `BoundObject kvSchema ⟨0, 0, D12⟩` is inhabited (M-005).
    Decided by evaluation (SHA-256 does not reduce in the kernel; no
    `native_decide`, no extra axiom). -/
def agreesForm0 (c k : Int) (d b : String) : Bool :=
  decide (CanonicalObjectAt kvSchema ⟨c, k, d⟩ b) == ((boundObject 32 0 c k "" "" d [] b).ok == 1)
#guard decide (CanonicalObjectAt kvSchema ⟨0, 0, D12⟩ ab)
#guard agreesForm0 0 0 D12 ab
#guard agreesForm0 0 0 "7432a6d09838fca877480f4cd7066d6f508ca1b3af66d33cb125ede3c2f074cf" "k:1|k:2"
#guard agreesForm0 0 0 "f031ec684a0d5bf45d52fac4a2655aec267ecd3bd19222023a57481f9567dc9e" "a:1|"
#guard agreesForm0 0 0 "d614f5a4bbd95f722a0f36b2c86e2a6d3e83d0ed6437bfa7b21fc9f2399c65aa" "b:2|a:1"
#guard agreesForm0 0 0 "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" ab
#guard agreesForm0 12 0 "" ab
#guard agreesForm0 0 (-1) "" ab
end Pins

end Rcic.BoundObject
