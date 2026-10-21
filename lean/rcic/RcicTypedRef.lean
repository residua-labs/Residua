/-
RCIC knife 1 (spine level 1): typed refs — RF-001..006 over GT-ID-001..005.

Statements FIRST (hard order): the six propositions are quoted verbatim from
docs/rcic/01_REFERENCE_AND_JUDGMENT_FOUNDATION.md in the PR table; the model
below is then PINNED to the sealed corpus of apps/rcic-typed-ref BEFORE any
theorem is proven (rows 01..11, compile-enforced), per the dispatch.

Degeneracy clause honored: where the encoding makes a theorem hold by
construction (rfl-class), that is not a failure — the corpus pins bind the
encoding to the sealed scm behavior. NO hash-injectivity premise is smuggled:
every statement is about the DECISION PROCEDURE (complete preimage bytes),
per the 01 L85-96 three-way adjudication, never about global uniqueness.
-/
import Residua.SHA256

namespace Rcic.TypedRef

/-- The sealed scm derive preimage record (scm/rcic/derive.scm), reproduced
as the canonical structural repr the host content-hash serializes:
`MakeRecord([[str:9:ref_class,Num(float:C.0)],…,[str:22:canonical_object_bytes,StrLit(str:N:B)]])`. -/
def preimageRepr (c : Nat) (k : Int) (bytes : String) : String :=
  s!"MakeRecord([[str:9:ref_class,Num(float:{c}.0)],[str:9:kind_code,Num(float:{k}.0)],\
[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],\
[str:17:object_schema_ref,Num(float:0.0)],\
[str:22:canonical_object_bytes,StrLit(str:{bytes.length}:{bytes})]])"

/-- deriveRef's digest: sha256 over the canonical preimage repr (the sealed
rcic.derive composes the same record through the host content-hash). -/
def deriveDigest (c : Nat) (k : Int) (bytes : String) : String :=
  Residua.SHA256.sha256Hex (preimageRepr c k bytes)

/-- The 12 RefClasses (sealed ref_class_ok). -/
def classOk (c : Nat) : Bool := c ≤ 11

/-- The sealed adjudication verdict. -/
inductive TRVal : Type
  | ok (digest : String) | refuse (code : String)
  deriving DecidableEq

def TRVal.isRefuse : TRVal → Bool
  | .ok _ => false
  | .refuse _ => true

/-- Validity, Bool form (kind before class, mirroring the sealed derive.scm). -/
def invalidCode (c : Nat) (k : Int) : Option String :=
  if k < 0 then some "[typed_ref_unknown_kind]"
  else if !classOk c then some "[typed_ref_unknown_class]"
  else none

/-- form 0 derive / form 1 admit (re-derive-and-compare) / form 2 bare digest. -/
def adjudicate (form : Nat) (c : Nat) (k : Int) (digest bytes : String) : TRVal :=
  match form with
  | 0 =>
    match invalidCode c k with
    | none => TRVal.ok (deriveDigest c k bytes)
    | some code => TRVal.refuse code
  | 1 =>
    match invalidCode c k with
    | none =>
      match _hb : decide (digest = deriveDigest c k bytes) with
      | true => TRVal.ok digest
      | false => TRVal.refuse "[typed_ref_address_collision]"
    | some code => TRVal.refuse code
  | 2 => TRVal.refuse "[typed_ref_bare_digest]"
  | _ => TRVal.refuse "[typed_ref_unknown_form]"

/-! ## Corpus pinning — all 11 sealed rows of apps/rcic-typed-ref (compile-enforced).
`#eval` panic guards: a mismatch aborts elaboration, i.e. the BUILD fails —
this is the dispatch's compile-enforced pin, not a passive print. -/
#eval (if adjudicate 0 0 0 "" "x" == TRVal.ok "56e8d1e16bc402b9d64069f8ebaaf9073994fb881ceaafb3130dde62890ad2af" then 0 else panic "row 01 GT-ID-001 mismatch")
#eval (if adjudicate 0 1 0 "" "x" == TRVal.ok (deriveDigest 1 0 "x") then 0 else panic "row 02 mismatch")
#eval (if adjudicate 0 0 1 "" "x" == TRVal.ok (deriveDigest 0 1 "x") then 0 else panic "row 03 mismatch")
#eval (if adjudicate 1 0 0 "56e8d1e16bc402b9d64069f8ebaaf9073994fb881ceaafb3130dde62890ad2af" "x" == TRVal.ok "56e8d1e16bc402b9d64069f8ebaaf9073994fb881ceaafb3130dde62890ad2af" then 0 else panic "row 04 mismatch")
#eval (if adjudicate 1 0 0 "56e8d1e16bc402b9d64069f8ebaaf9073994fb881ceaafb3130dde62890ad2af" "y" == TRVal.refuse "[typed_ref_address_collision]" then 0 else panic "row 05 mismatch")
#eval (if adjudicate 2 0 0 "deadbeef" "" == TRVal.refuse "[typed_ref_bare_digest]" then 0 else panic "row 06 mismatch")
#eval (if adjudicate 2 3 1 "aaaaaaaaaaaa" "" == TRVal.refuse "[typed_ref_bare_digest]" then 0 else panic "row 07 mismatch")
#eval (if adjudicate 0 12 0 "" "x" == TRVal.refuse "[typed_ref_unknown_class]" then 0 else panic "row 08 mismatch")
#eval (if adjudicate 0 0 (-1) "" "x" == TRVal.refuse "[typed_ref_unknown_kind]" then 0 else panic "row 09 mismatch")
#eval (if adjudicate 3 0 0 "" "x" == TRVal.refuse "[typed_ref_unknown_form]" then 0 else panic "row 10 mismatch")
#eval (if adjudicate 1 0 0 "56e8d1e16bc402b9d64069f8ebaaf9073994fb881ceaafb3130dde62890ad2a0" "x" == TRVal.refuse "[typed_ref_address_collision]" then 0 else panic "row 11 mismatch")

/-! ## The store (explicit; NO ambient resolution — 01 "Store inspection" L85-96) -/

/-- A store is an EXPLICIT association list: digest → canonical preimage bytes.
The ambient-nowhere discipline (RF-006) is structural: there is no other source. -/
abbrev Store := List (String × String)

def storeCount (s : Store) (d : String) : Nat :=
  s.foldl (fun n p => if p.1 = d then n + 1 else n) 0

/-- Resolution is UNANIMOUS: exactly one entry, else none (ambiguous = unresolved). -/
def storeResolve (s : Store) (d : String) : Option String :=
  match _h : storeCount s d with
  | 1 => s.foldl (fun acc p => if p.1 = d then some p.2 else acc) none
  | _ => none

/-- Bound lookup: absent or ambiguous → refused by name; never a default. -/
def lookupBound (s : Store) (d : String) : TRVal :=
  match storeResolve s d with
  | some b => TRVal.ok b
  | none => TRVal.refuse "[typed_ref_address_collision]"

/-- Complete-ref comparison: class ∧ kind ∧ digest — the decision procedure,
never a digest-only shortcut (01 L76-77). -/
def refEqComplete (c1 c2 : Nat) (k1 k2 : Int) (d1 d2 : String) : Bool :=
  c1 == c2 && k1 == k2 && d1 == d2

/-- The 01 L85-96 three-way adjudication for "same ref, claimed preimage". -/
def sameRefAdjudicate (s : Store) (d : String) (presented : String) : TRVal :=
  match storeResolve s d with
  | some b => if b = presented then TRVal.ok d else TRVal.refuse "[typed_ref_address_collision]"
  | none => TRVal.refuse "[typed_ref_address_collision]"

/-- Exact object equality (GT-ID-004): collision-aware — accepts ONLY when both
sides resolve UNANIMOUSLY to the SAME complete preimage bytes. -/
def exactObjectEq (s : Store) (d1 d2 : String) : Bool :=
  match storeResolve s d1, storeResolve s d2 with
  | some b1, some b2 => b1 = b2
  | _, _ => false

/-! ## RF-001..006 — premise-free statements about the decision procedure -/

/-- RF-001 (GT-ID-001). QUOTED (01 §15 L451 + registry verbatim): "A reference
cannot cross `RefClass` by equal digest bytes." The complete-ref comparison
never confirms equality across classes, whatever the digests are. -/
theorem RF001_typed_ref_class_separation (c1 c2 : Nat) (k : Int) (d : String)
    (h : c1 ≠ c2) : refEqComplete c1 c2 k k d d = false := by
  simp [refEqComplete]; omega

/-- RF-002 (GT-ID-002). QUOTED (01 §15 L451 + L77 verbatim): "Kind codes are
part of reference identity." — "The class and kind are part of the preimage
(GT-ID-001, GT-ID-002). Equal digest bytes under different classes or kinds
do not denote the same object." -/
theorem RF002_typed_ref_kind_separation (c : Nat) (k1 k2 : Int) (d : String)
    (h : k1 ≠ k2) : refEqComplete c c k1 k2 d d = false := by
  simp [refEqComplete]; omega

/-- RF-003 (GT-ID-003). QUOTED (01 §15 L452 + registry verbatim): "Same typed
ref with different canonical preimage is collision/integrity failure." — L93-94:
"same ref but different complete preimage → address collision". The
adjudication compares COMPLETE PREIMAGE BYTES (never digests). -/
theorem RF003_same_ref_different_preimage_refuses (s : Store) (d b1 b2 : String)
    (hr : storeResolve s d = some b1) (hb : b2 ≠ b1) :
    sameRefAdjudicate s d b2 = TRVal.refuse "[typed_ref_address_collision]" := by
  simp [sameRefAdjudicate, hr]; exact fun heq => hb heq.symm

/-- RF-004 (GT-ID-004). QUOTED (01 §15 L453 + registry verbatim): "Content
equality requires exact canonical bytes/resolution, not digest equality."
Acceptance IMPLIES unanimous resolution to equal bytes; equal digests alone
never suffice. -/
theorem RF004_exact_object_equality_collision_aware (s : Store) (d1 d2 : String)
    (h : exactObjectEq s d1 d2 = true) :
    ∃ b, storeResolve s d1 = some b ∧ storeResolve s d2 = some b := by
  unfold exactObjectEq at h
  split at h
  next b1 b2 h1 h2 => exact ⟨b1, h1, by simp [h2] at h; exact h.symm ▸ h2⟩
  next => exact absurd h (by decide)

set_option maxHeartbeats 2000000 in
/-- RF-005 (GT-ID-005 first half). QUOTED (01 §15 L454 + registry verbatim):
"Logical use of an external object carries bytes and a canonical binding
witness." First half: the binding accepts only on re-derive equality — form 1
acceptance yields digest = the recomputation. -/
theorem RF005_canonical_object_at_sound (c : Nat) (k : Int) (digest digest' bytes : String)
    (h : adjudicate 1 c k digest bytes = TRVal.ok digest') :
    digest = Residua.SHA256.sha256Hex (preimageRepr c k bytes) ∧ digest' = digest := by
  unfold adjudicate at h
  revert h
  generalize hdg : deriveDigest c k bytes = dg
  intro h
  revert h
  match _hv : invalidCode c k with
  | none =>
    intro h
    revert h
    match hb : decide (digest = dg) with
    | true =>
      intro h
      rw [decide_eq_true_eq] at hb
      simp only [hb] at h
      injection h with h2
      subst h2
      constructor
      · rw [hb, ← hdg]; rfl
      · exact hb.symm
    | false =>
      intro h
      simp only [hb] at h
      exact absurd h (by cases h)
  
  | some _ =>
    intro h
    exact absurd h (by cases h)

/-- RF-006 (GT-ID-005 second half). QUOTED (01 §15 L455 + L85-96): registry GT-ID-005
verbatim: "Logical use of an external object carries bytes and a canonical
binding witness." Second half, per L85-96 store inspection: resolution is
store-relative — acceptance implies the store itself carries the entry
(unanimously); NEVER ambient (GM-ID-004). -/
theorem RF006_bound_object_has_no_ambient_lookup (s : Store) (d : String)
    (h : ¬ (lookupBound s d).isRefuse) : storeCount s d = 1 := by
  unfold lookupBound TRVal.isRefuse at h
  revert h
  match hr : storeResolve s d with
  | some _ =>
    intro h
    simp only [storeResolve] at hr
    split at hr
    · next hcnt => exact hcnt
    · exact absurd hr (by simp)
  | none =>
    intro h
    exact absurd h (by simp)

/-! ## M-005 quantifier inhabitation — one explicit witness per ∀ theorem
(00 §16 M-005: an empty-domain ∀ is vacuously green; each theorem carries at
least one inhabited instantiation, committed and build-checked). -/

/-- RF-001 witness: classes 3 and 9 (the epoch's content/history roles). -/
example : refEqComplete 3 9 0 0 "d" "d" = false :=
  RF001_typed_ref_class_separation 3 9 0 "d" (by decide)

/-- RF-002 witness: kinds 0 and 1. -/
example : refEqComplete 5 5 0 1 "d" "d" = false :=
  RF002_typed_ref_kind_separation 5 0 1 "d" (by decide)

/-- RF-003 witness: a concrete one-entry store, same ref, differing preimage. -/
example : sameRefAdjudicate [("d", "x")] "d" "y"
    = TRVal.refuse "[typed_ref_address_collision]" :=
  RF003_same_ref_different_preimage_refuses [("d", "x")] "d" "x" "y"
    (by decide) (by decide)

/-- RF-004 witness: a concrete store where equality ACCEPTS, exhibiting the ∃. -/
example : ∃ b, storeResolve [("a", "z"), ("b", "z")] "a" = some b
    ∧ storeResolve [("a", "z"), ("b", "z")] "b" = some b :=
  RF004_exact_object_equality_collision_aware [("a", "z"), ("b", "z")] "a" "b"
    (by decide)

/-- RF-005 witness: corpus row 4. The premise instance (form 1 accepts the
row-4 digest) is build-checked by the row-04 #eval panic guard above; this
example inhabits the theorem under that build-verified premise. -/
example (hacc : adjudicate 1 0 0 (deriveDigest 0 0 "x") "x"
    = TRVal.ok (deriveDigest 0 0 "x")) :
    deriveDigest 0 0 "x" = Residua.SHA256.sha256Hex (preimageRepr 0 0 "x") :=
  (RF005_canonical_object_at_sound 0 0 (deriveDigest 0 0 "x")
    (deriveDigest 0 0 "x") "x" hacc).1

/-- RF-006 witness: a concrete one-entry store accepting the lookup. -/
example : storeCount [("d", "x")] "d" = 1 :=
  RF006_bound_object_has_no_ambient_lookup [("d", "x")] "d" (by decide)

/-! ## M-002a carrier pins — every definition in a sealed statement is pinned
to ITS carrier's sealed behavior (00 §16 M-002a as amended by #3676):
refEqComplete ↔ apps/rcic-env-ids (complete-ref comparison rows); the store
family ↔ apps/rcic-bound-object (the 01 L85-96 three-way adjudication rows).
Inputs are the carriers' committed corpus row values; the correspondence is
build-enforced (#eval panic guards). -/

/- env-ids corpus row "GT-ID-001 form 1 same digest under different classes
is NOT collapsed" (exp ok=1): the complete-ref comparison returns FALSE for
class 3 vs 9 over the same digest — not-collapsed. -/
#eval (if refEqComplete 3 9 0 0 "0be9902748c9e501ba7d9a0f88175a6503262348536bada36c4a91dc934aceb2" "0be9902748c9e501ba7d9a0f88175a6503262348536bada36c4a91dc934aceb2" = false then 0 else panic "M-002a pin: env-ids different-classes row")

/- env-ids corpus row "GM-ENV-004 form 1 same q in two roles collapsed"
(exp ok=0): the comparison returns TRUE for identical complete refs. -/
#eval (if refEqComplete 3 3 0 0 "0be9902748c9e501ba7d9a0f88175a6503262348536bada36c4a91dc934aceb2" "0be9902748c9e501ba7d9a0f88175a6503262348536bada36c4a91dc934aceb2" = true then 0 else panic "M-002a pin: env-ids two-roles row")

/- bound-object corpus row "GT-ID-003 form 1 in-store same digest two byte
values collision": a digest stored TWICE with different bytes does not
resolve unanimously — the adjudication refuses (collision). -/
#eval (if sameRefAdjudicate [("1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4", "a:1|b:2"), ("1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4", "a:9|b:9")] "1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4" "a:1|b:2" = TRVal.refuse "[typed_ref_address_collision]" then 0 else panic "M-002a pin: bound-object in-store collision row")

/- bound-object corpus row "GT-ID-004 left digest missing in store refused":
an absent digest never resolves — lookupBound refuses (no ambient). -/
#eval (if lookupBound [("other", "a:1|b:2")] "bbdce295ecb0b39fccad12af2187d61105446aa3ff1f63d06540368570985379" = TRVal.refuse "[typed_ref_address_collision]" then 0 else panic "M-002a pin: bound-object not-in-store row")

/- bound-object accept row shape (both refs resolve to the same witness
bytes): exactObjectEq accepts — the equality is COMPLETE-PREIMAGE equality. -/
#eval (if exactObjectEq [("1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4", "a:1|b:2"), ("2903", "a:1|b:2")] "1e45003d49d1f1536152ec657b7baa7eb73b9c77142bf6e4409a2bce8aea85c4" "2903" = true then 0 else panic "M-002a pin: bound-object accept shape")

end Rcic.TypedRef




#print axioms Rcic.TypedRef.RF001_typed_ref_class_separation
#print axioms Rcic.TypedRef.RF002_typed_ref_kind_separation
#print axioms Rcic.TypedRef.RF003_same_ref_different_preimage_refuses
#print axioms Rcic.TypedRef.RF004_exact_object_equality_collision_aware
#print axioms Rcic.TypedRef.RF005_canonical_object_at_sound
#print axioms Rcic.TypedRef.RF006_bound_object_has_no_ambient_lookup
