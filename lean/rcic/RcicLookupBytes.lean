/-
Annex 23 unit H-10 — RM-013 byte half: addressed-store
rehash and canonical decode/re-encode.

MEASUREMENT (2) first, `grep -nE 'Bytes|Digest|sha256'
lean/rcic/*.lean`:
  no `Bytes` / `Digest` type in lean/rcic. String is the
  byte model (`RcicTypedRef.deriveDigest`, `RcicWireDecode`
  `|`-split, `RcicReach.evBytes`). Digest is String
  (`Residua.SHA256.sha256Hex` at
  `lean/Residua/SHA256.lean`). REUSED: String as Bytes
  and as Digest. `h : String → String` is a parameter
  (as ρ₀ is). SHA256 is a concrete instantiation, not
  a second hash in this leaf.

STATEMENTS QUOTED BEFORE THE LEAN (23.H.0 (3)):

  04 §11:
    lookupMember(handle, MemberRef(group,index))
    performs:
    1. group membership lookup in the environment image;
    2. addressed-store rehash;
    3. canonical decode/re-encode;
    4. theory-profile check;
    5. member-index bounds check;
    6. local-reference closure;
    7. return a closed MemberView.

  04 §8 four-line law:
    stored bytes rehash to requested ref
    canonical decode succeeds
    reencode equals stored bytes
    kind/schema/theory profile match

  EG-016 lookup rehash/decode/reencode exact

  03 §14:
    group present
    stored bytes rehash to requested ref
    canonical decode/re-encode
    member index in bounds
    local refs closed

This leaf is 04 §11 steps 2–3 plus the four-line law
over a store slot. Resolution (steps 1/5/7) is the
landed `RM013_lookupDeclaration_resolved` /
`RM013_lookupDeclaration_hasTy` (`RcicMachine` — NOT
edited). Decimal helpers `decCanonical` /
`parseNat` are CALLED from `RcicWireDecode` (C3 /
ValueAt), not rewritten.

closure_claim stays 0.
-/
import rcic.RcicWireDecode

namespace Rcic.LookupBytes
open Rcic.WireDecode (decCanonical parseNat)

/-- Slice encoding (recorded, not law): two-field
`k:<kind>|p:<payload>` wire. Canonical key ascent.
List Char is the kernel-reducible encoding of the
String byte model (E-D: `splitOn` is not
kernel-reducible; theorems pin the split parts). -/
structure LookupMember where
  kind : Nat
  payload : List Char
  deriving Repr, DecidableEq

structure StoreEntry where
  ref : List Char
  p0 : List Char
  p1 : List Char
  kind : Nat
  deriving Repr, DecidableEq

def bytesOf (e : StoreEntry) : List Char :=
  e.p0 ++ ['|'] ++ e.p1

inductive LookupBytesResult where
  | accepted : LookupMember → LookupBytesResult
  | refused : String → LookupBytesResult
  deriving Repr, DecidableEq

def residueRehash : String :=
  "[rcic_lookup_rehash_mismatch]"
def residueDecode : String :=
  "[rcic_lookup_decode_failed]"
def residueReencode : String :=
  "[rcic_lookup_reencode_mismatch]"
def residueProfile : String :=
  "[rcic_lookup_profile_mismatch]"

/-- 06 §4 encodeValue stand-in: key ascent `k` then
`p`. Kind digits 0..3 reduce; others unused. -/
def kindDigits : Nat → List Char
  | 0 => ['0']
  | 1 => ['1']
  | 2 => ['2']
  | 3 => ['3']
  | _ => ['9']

def encodeMember (m : LookupMember) : List Char :=
  ['k', ':'] ++ kindDigits m.kind ++
    ['|', 'p', ':'] ++ m.payload

def splitKV : List Char → Option (Char × List Char)
  | k :: ':' :: v =>
    if v == [] then none else some (k, v)
  | _ => none

def decInRange (cs : List Char) : Bool :=
  cs.length ≤ 10 &&
    decide (parseNat cs < 4294967296)

/-- 06 §4 decodeValue stand-in over already-split
parts. Does NOT require key ascent (re-encode). -/
def decodeTwo (p0 p1 : List Char) :
    Option LookupMember :=
  match splitKV p0, splitKV p1 with
  | some (k0, v0), some (k1, v1) =>
    if k0 == k1 then none
    else if (k0 != 'k' && k0 != 'p') ||
            (k1 != 'k' && k1 != 'p') then none
    else
      let kval := if k0 == 'k' then v0 else v1
      let pval := if k0 == 'p' then v0 else v1
      if !decCanonical kval then none
      else if !decInRange kval then none
      else some ⟨parseNat kval, pval⟩
  | _, _ => none

/-- First store slot whose declared ref equals the
requested digest. -/
def lookupEntry : List StoreEntry → List Char →
    Option StoreEntry
  | [], _ => none
  | e :: rest, ref =>
    if e.ref == ref then some e else lookupEntry rest ref

theorem lookupEntry_mem
    (store : List StoreEntry) (ref : List Char)
    (e : StoreEntry)
    (h : lookupEntry store ref = some e) :
    e ∈ store ∧ e.ref = ref := by
  induction store with
  | nil => exact nomatch h
  | cons x xs ih =>
    unfold lookupEntry at h
    cases hcmp : (x.ref == ref) with
    | true =>
      rw [hcmp] at h
      injection h with heq
      subst heq
      exact ⟨List.mem_cons.mpr (Or.inl rfl), eq_of_beq hcmp⟩
    | false =>
      rw [hcmp] at h
      have ⟨hm, hr⟩ := ih h
      exact ⟨List.mem_cons.mpr (Or.inr hm), hr⟩

/-- Slot check, split out so `lookupBytes` reduces
to this after `lookupEntry` (E-D shape). -/
def lookupBytesFrom (h : List Char → List Char)
    (e : StoreEntry) (ref : List Char) :
    LookupBytesResult :=
  if h (bytesOf e) == ref then
    match decodeTwo e.p0 e.p1 with
    | none => .refused residueDecode
    | some m =>
      if encodeMember m == bytesOf e then
        if m.kind == e.kind then .accepted m
        else .refused residueProfile
      else .refused residueReencode
  else .refused residueRehash

/-- 04 §11 steps 2–3 and 04 §8's four lines over one
slot. `h` is the digest function (a parameter). -/
def lookupBytes (h : List Char → List Char)
    (store : List StoreEntry) (ref : List Char) :
    LookupBytesResult :=
  match lookupEntry store ref with
  | none => .refused "missing"
  | some e => lookupBytesFrom h e ref

/-- 04 §11 steps 2–3, 04 §8 four lines, EG-016,
03 §14 rehash + canonical decode/re-encode.
Accepted ⇒ rehash ∧ decode ∧ reencode ∧ profile.
`def` not `theorem`: the statement is Σ' (Type),
§18.3 rule 1. -/
def RM013_lookupBytes_accepted
    (h : List Char → List Char) (store : List StoreEntry)
    (ref : List Char) (m : LookupMember)
    (hacc : lookupBytes h store ref = .accepted m) :
    Σ' (e : StoreEntry),
      (e ∈ store) ×' (e.ref = ref) ×'
      (h (bytesOf e) = ref) ×'
      (decodeTwo e.p0 e.p1 = some m) ×'
      (encodeMember m = bytesOf e) ×'
      (m.kind = e.kind) := by
  cases hfind : lookupEntry store ref with
  | none =>
    simp only [lookupBytes, hfind] at hacc
    exact nomatch hacc
  | some e =>
    simp only [lookupBytes, hfind] at hacc
    have ⟨hmem, href⟩ := lookupEntry_mem store ref e hfind
    unfold lookupBytesFrom at hacc
    cases hr : (h (bytesOf e) == ref) with
    | false =>
      simp only [hr] at hacc
      exact nomatch hacc
    | true =>
      simp only [hr] at hacc
      cases hdec : decodeTwo e.p0 e.p1 with
      | none =>
        simp only [hdec] at hacc
        exact nomatch hacc
      | some m' =>
        simp only [hdec] at hacc
        cases he : (encodeMember m' == bytesOf e) with
        | false =>
          simp only [he] at hacc
          exact nomatch hacc
        | true =>
          simp only [he] at hacc
          cases hk : (m'.kind == e.kind) with
          | false =>
            simp only [hk] at hacc
            exact nomatch hacc
          | true =>
            simp only [hk] at hacc
            injection hacc with hm
            subst hm
            exact ⟨e, hmem, href, eq_of_beq hr, hdec,
              eq_of_beq he, eq_of_beq hk⟩

/-- 04 §8 / 03 §14: stored bytes rehash to requested
ref. Accepted ⇒ the matched slot's bytes hash to
`ref` under `h`. -/
def RM013_lookupBytes_rehash
    (h : List Char → List Char) (store : List StoreEntry)
    (ref : List Char) (m : LookupMember)
    (hacc : lookupBytes h store ref = .accepted m) :
    Σ' (e : StoreEntry),
      (e ∈ store) ×' (e.ref = ref) ×'
      (h (bytesOf e) = ref) :=
  match RM013_lookupBytes_accepted h store ref m hacc with
  | ⟨e, mem, href, hh, _, _, _⟩ => ⟨e, mem, href, hh⟩

/-- 04 §8 / 03 §14: canonical decode/re-encode.
Accepted ⇒ decode of the matched bytes is `m` and
re-encode equals the stored bytes. -/
def RM013_lookupBytes_reencode
    (h : List Char → List Char) (store : List StoreEntry)
    (ref : List Char) (m : LookupMember)
    (hacc : lookupBytes h store ref = .accepted m) :
    Σ' (e : StoreEntry),
      (e ∈ store) ×' (e.ref = ref) ×'
      (decodeTwo e.p0 e.p1 = some m) ×'
      (encodeMember m = bytesOf e) :=
  match RM013_lookupBytes_accepted h store ref m hacc with
  | ⟨e, mem, href, _, hdec, henc, _⟩ =>
    ⟨e, mem, href, hdec, henc⟩

/-! ### M-002 pins (two-entry store) and M-005 -/

def k0 : List Char := ['k', ':', '0']
def pSort : List Char := ['p', ':', 's', 'o', 'r', 't']
def k1 : List Char := ['k', ':', '1']
def pBody : List Char := ['p', ':', 'b', 'o', 'd', 'y']
def canonRef : List Char := k0 ++ ['|'] ++ pSort
def otherRef : List Char := k1 ++ ['|'] ++ pBody
def nonRef : List Char := pSort ++ ['|'] ++ k0

def store2 : List StoreEntry :=
  [⟨canonRef, k0, pSort, 0⟩,
   ⟨otherRef, k1, pBody, 1⟩]

def storeNon : List StoreEntry :=
  [⟨nonRef, pSort, k0, 0⟩,
   ⟨otherRef, k1, pBody, 1⟩]

def storeRehash : List StoreEntry :=
  [⟨canonRef, k1, pBody, 0⟩,
   ⟨otherRef, k1, pBody, 1⟩]

-- pin_lb_row00 ← "EG-016 canonical accept k:0|p:sort"
#eval
  (if lookupBytes id store2 canonRef
      == .accepted ⟨0, ['s', 'o', 'r', 't']⟩ then 0
    else panic "pin_lb_row00")
-- pin_lb_row01 ← "EG-016 second slot canonical k:1|p:body"
#eval
  (if lookupBytes id store2 otherRef
      == .accepted ⟨1, ['b', 'o', 'd', 'y']⟩ then 1
    else panic "pin_lb_row01")
-- pin_lb_row02 ← "EG-016 reencode tooth unsorted p|k"
#eval
  (if lookupBytes id storeNon nonRef
      == .refused residueReencode then 2
    else panic "pin_lb_row02")
-- pin_lb_row03 ← "04 §8 rehash mismatch"
#eval
  (if lookupBytes id storeRehash canonRef
      == .refused residueRehash then 3
    else panic "pin_lb_row03")
-- pin_lb_row04 ← "04 §8 profile mismatch kind 1 vs 0"
#eval
  (if lookupBytes id
        [⟨canonRef, k0, pSort, 1⟩]
        canonRef
      == .refused residueProfile then 4
    else panic "pin_lb_row04")
-- pin_lb_row05 ← "04 §11 decode failed garbage"
#eval
  (if lookupBytes id
        [⟨['x', '|', 'y'], ['x'], ['y'], 0⟩]
        ['x', '|', 'y']
      == .refused residueDecode then 5
    else panic "pin_lb_row05")

/-- M-005 non-trivial instance: canonical row
accepted. Degeneracy tooth's agreeing side. -/
theorem witness_lookupBytes_canonical :
    lookupBytes id store2 canonRef
      = .accepted ⟨0, ['s', 'o', 'r', 't']⟩ := rfl

/-- M-005 refusal instance: non-canonical-but-
decodable row refused with its name. -/
theorem witness_lookupBytes_noncanonical :
    lookupBytes id storeNon nonRef
      = .refused residueReencode := rfl

end Rcic.LookupBytes
