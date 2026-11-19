-- Bootstrap 1b RED (R-13). Adversary-authored BEFORE Bundle.lean.
-- Does not implement the BootExpr codec. Freezes the five ADR anti-models:
--   overlong LEB, junk suffix, dual-leaf (i64 vs bytes), kind-flip, manifest mismatch.
-- Law* = what 1b encode/decode/validate MUST do.
-- Mutant* = the decoders that ACCEPT those bytes (1b MUST exhibit and refuse).
-- 1b closes BundleCodecDischarge with ITS codec, not by renaming law*.
-- 0 sorry, 0 axiom. closure_claim = 0.
-- Frozen contract: lean/Residua/Bootstrap/bundle_red_contract_v1.json
-- contract_q = 4c527603adf317fbafb0cd461f1dda27e6a4851d4641ba8c79144d73c66cc469

import Residua.SHA256

namespace Residua.Bootstrap.BundleRed

def bundleRedContractV1Q : String :=
  "4c527603adf317fbafb0cd461f1dda27e6a4851d4641ba8c79144d73c66cc469"

abbrev Bytes := List UInt8

def tagI64Leaf : UInt8 := 0
def tagBytesLeaf : UInt8 := 1
def kindCode : UInt8 := 0
def kindProof : UInt8 := 1

def residueOverlongLeb : String := "bundle_overlong_leb"
def residueJunkSuffix : String := "bundle_junk_suffix"
def residueDualLeaf : String := "bundle_dual_leaf"
def residueKindProof : String := "bundle_proof_kind_reserved"
def residueManifestMismatch : String := "bundle_manifest_derivation_mismatch"

-- Unsigned LEB128, shortest form (Wasm unsigned LEB, non-shortest refused).
def uLebEncode (n : Nat) : Bytes :=
  if h : n < 128 then [UInt8.ofNat n]
  else
    have : n / 128 < n := by
      apply Nat.div_lt_self
      · omega
      · decide
    UInt8.ofNat (n % 128 + 128) :: uLebEncode (n / 128)
termination_by n

def uLebDecodeGo : Nat → Nat → Nat → Bytes → Option (Nat × Bytes)
  | 0, _acc, _shift, _ => none
  | _+1, _acc, _shift, [] => none
  | fuel+1, acc, shift, b :: rest =>
    let v := (b.toNat % 128) <<< shift
    if b.toNat < 128 then some (acc + v, rest)
    else uLebDecodeGo fuel (acc + v) (shift + 7) rest

-- Law: decode then demand the consumed prefix equals uLebEncode n (shortest).
def uLebDecode (bs : Bytes) : Option (Nat × Bytes) :=
  match uLebDecodeGo 16 0 0 bs with
  | none => none
  | some (n, rest) =>
    let consumed := bs.length - rest.length
    let enc := uLebEncode n
    if enc.length = consumed ∧ enc = bs.take consumed then some (n, rest) else none

-- Mutant: accepts overlong (any 7-bit continuation that yields n).
def uLebDecodeMut (bs : Bytes) : Option (Nat × Bytes) :=
  uLebDecodeGo 16 0 0 bs

def two64 : Int := 18446744073709551616
def i64Min : Int := -9223372036854775808
def i64Max : Int := 9223372036854775807

def inI64Range (n : Int) : Bool := i64Min ≤ n ∧ n ≤ i64Max

def i64ToU64 (n : Int) : Nat :=
  if n ≥ 0 then n.toNat else (n + two64).toNat

def u64Byte (u : Nat) (i : Nat) : UInt8 :=
  UInt8.ofNat ((u >>> (8 * i)) % 256)

def i64Le8 (n : Int) : Bytes :=
  let u := i64ToU64 n
  [u64Byte u 0, u64Byte u 1, u64Byte u 2, u64Byte u 3,
   u64Byte u 4, u64Byte u 5, u64Byte u 6, u64Byte u 7]

inductive Wire where
  | i64 : Int → Wire
  | bytes : Bytes → Wire
  deriving DecidableEq, Repr

def lawEncode : Wire → Bytes
  | .i64 n => tagI64Leaf :: i64Le8 n
  | .bytes bs => tagBytesLeaf :: (uLebEncode bs.length ++ bs)

def lawDecode (bs : Bytes) : Option Wire :=
  match bs with
  | [] => none
  | t :: rest =>
    if t = tagI64Leaf then
      match rest with
      | b0::b1::b2::b3::b4::b5::b6::b7::more =>
          if more.isEmpty then
            let u :=
              b0.toNat + b1.toNat <<< 8 + b2.toNat <<< 16 + b3.toNat <<< 24
              + b4.toNat <<< 32 + b5.toNat <<< 40 + b6.toNat <<< 48 + b7.toNat <<< 56
            let n : Int := if u < 9223372036854775808 then Int.ofNat u else Int.ofNat u - two64
            some (.i64 n)
          else none
      | _ => none
    else if t = tagBytesLeaf then
      match uLebDecode rest with
      | none => none
      | some (len, payload) =>
          if payload.length = len then some (.bytes payload) else none
    else none

-- Mutant decode: overlong LEB ok; junk suffix ok; bytes-of-8 as i64.
def mutantDecode (bs : Bytes) : Option Wire :=
  match bs with
  | [] => none
  | t :: rest =>
    if t = tagI64Leaf then
      match rest with
      | b0::b1::b2::b3::b4::b5::b6::b7::_more =>
          let u :=
            b0.toNat + b1.toNat <<< 8 + b2.toNat <<< 16 + b3.toNat <<< 24
            + b4.toNat <<< 32 + b5.toNat <<< 40 + b6.toNat <<< 48 + b7.toNat <<< 56
          let n : Int := if u < 9223372036854775808 then Int.ofNat u else Int.ofNat u - two64
          some (.i64 n)
      | _ => none
    else if t = tagBytesLeaf then
      match uLebDecodeMut rest with
      | none => none
      | some (len, payload) =>
          let take := payload.take len
          -- dual-leaf: 8-byte payload also read as i64 (no recursive decode)
          if take.length = 8 then
            match take with
            | b0::b1::b2::b3::b4::b5::b6::b7::[] =>
                let u :=
                  b0.toNat + b1.toNat <<< 8 + b2.toNat <<< 16 + b3.toNat <<< 24
                  + b4.toNat <<< 32 + b5.toNat <<< 40 + b6.toNat <<< 48 + b7.toNat <<< 56
                let n : Int := if u < 9223372036854775808 then Int.ofNat u else Int.ofNat u - two64
                some (.i64 n)
            | _ => some (.bytes take)
          else some (.bytes take)
    else none

def lawAdmitKind (k : UInt8) : Bool := k == kindCode
def mutantAdmitKind (_k : UInt8) : Bool := true

def sha256Raw (msg : Bytes) : Bytes :=
  let padded := Residua.SHA256.pad msg
  let blocks := Residua.SHA256.chunk64 padded
  let hash := Residua.SHA256.processBlocks blocks Residua.SHA256.hInit
  let words :=
    hash.getD 0 0 :: hash.getD 1 0 :: hash.getD 2 0 :: hash.getD 3 0 ::
    hash.getD 4 0 :: hash.getD 5 0 :: hash.getD 6 0 :: hash.getD 7 0 :: []
  words.flatMap (fun w =>
    [ (w >>> (24 : UInt32)).toUInt8, (w >>> (16 : UInt32)).toUInt8
    , (w >>> (8 : UInt32)).toUInt8, w.toUInt8 ])

def lawManifestOk (declared : Bytes) (encodedDef : Bytes) : Bool :=
  declared = sha256Raw encodedDef

def mutantManifestOk (_declared : Bytes) (_encodedDef : Bytes) : Bool := true

-- Fixtures
def overlongLen1 : Bytes := [0x81, 0x00]
def overlongBytes : Bytes := tagBytesLeaf :: (overlongLen1 ++ [0xAA])
def canonBytes1 : Bytes := lawEncode (.bytes [0xAA])
def junkI64 : Bytes := lawEncode (.i64 1) ++ [0]
def dualLeaf : Bytes := tagBytesLeaf :: (uLebEncode 8 ++ i64Le8 0)
def spoofDeclared : Bytes := List.replicate 32 (0 : UInt8)
def oneDefBytes : Bytes := lawEncode (.i64 1)

-- Law pins
theorem pin_leb_1 : uLebEncode 1 = [1] := by decide!
theorem pin_overlong_law : uLebDecode overlongLen1 = none := by decide!
theorem pin_junk_law : lawDecode junkI64 = none := by decide!
theorem pin_dual_not_i64 : lawDecode dualLeaf ≠ some (.i64 0) := by decide!
theorem pin_kind_proof_law : lawAdmitKind kindProof = false := by decide!
theorem pin_manifest_spoof_law : lawManifestOk spoofDeclared oneDefBytes = false := by decide!
theorem pin_roundtrip_i64 :
    lawDecode (lawEncode (.i64 1)) = some (.i64 1) := by decide!
theorem pin_roundtrip_bytes :
    lawDecode (lawEncode (.bytes [0xAA])) = some (.bytes [0xAA]) := by decide!
theorem pin_tags_disjoint : tagI64Leaf ≠ tagBytesLeaf := by decide!

-- Mutant pins (the RED: these ACCEPT)
theorem mut_overlong : uLebDecodeMut overlongLen1 = some (1, []) := by decide!
theorem mut_junk : mutantDecode junkI64 = some (.i64 1) := by decide!
theorem mut_dual : mutantDecode dualLeaf = some (.i64 0) := by decide!
theorem mut_kind_proof : mutantAdmitKind kindProof = true := by decide!
theorem mut_manifest_spoof : mutantManifestOk spoofDeclared oneDefBytes = true := by decide!

-- Teeth
theorem tooth_overlong : uLebDecode overlongLen1 ≠ uLebDecodeMut overlongLen1 := by
  rw [pin_overlong_law, mut_overlong]; decide
theorem tooth_junk : lawDecode junkI64 ≠ mutantDecode junkI64 := by
  rw [pin_junk_law, mut_junk]; decide
theorem tooth_dual : lawDecode dualLeaf ≠ mutantDecode dualLeaf := by decide!
theorem tooth_kind : lawAdmitKind kindProof ≠ mutantAdmitKind kindProof := by
  rw [pin_kind_proof_law, mut_kind_proof]; decide
theorem tooth_manifest :
    lawManifestOk spoofDeclared oneDefBytes ≠
    mutantManifestOk spoofDeclared oneDefBytes := by
  rw [pin_manifest_spoof_law, mut_manifest_spoof]; decide

-- Non-tooth: shortest encoding of 0 is a single zero byte; both decoders agree.
theorem coincident_leb0 :
    uLebDecode [0] = uLebDecodeMut [0] ∧ uLebDecode [0] = some (0, []) := by
  decide!

-- 1b MUST inhabit this with ITS encode/decode/validate, routing each
-- fixture through the real codec (not by renaming law*).
class BundleCodecDischarge where
  decode : Bytes → Option Wire
  encode : Wire → Bytes
  admitKind : UInt8 → Bool
  manifestOk : Bytes → Bytes → Bool
  pin_overlong : decode overlongBytes = none
  pin_junk : decode junkI64 = none
  pin_dual : decode dualLeaf ≠ some (.i64 0)
  pin_kind : admitKind kindProof = false
  pin_manifest : manifestOk spoofDeclared oneDefBytes = false
  pin_rt_i64 : decode (encode (.i64 1)) = some (.i64 1)
  decode' : Bytes → Option Wire
  admitKind' : UInt8 → Bool
  manifestOk' : Bytes → Bytes → Bool
  mut_overlong : decode' overlongBytes ≠ none
  mut_junk : decode' junkI64 = some (.i64 1)
  mut_dual : decode' dualLeaf = some (.i64 0)
  mut_kind : admitKind' kindProof = true
  mut_manifest : manifestOk' spoofDeclared oneDefBytes = true

namespace BundleCodecDischarge
variable (D : BundleCodecDischarge)
theorem tooth_overlong : D.decode overlongBytes ≠ D.decode' overlongBytes := by
  intro h
  have m := D.mut_overlong
  rw [← h, D.pin_overlong] at m
  exact m rfl
theorem tooth_kind : D.admitKind kindProof ≠ D.admitKind' kindProof := by
  rw [D.pin_kind, D.mut_kind]; decide
end BundleCodecDischarge

end Residua.Bootstrap.BundleRed
