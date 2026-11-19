-- Bootstrap 1b: the bundle codec, inhabiting BundleCodecDischarge (#3563 RED, R-13).
--
-- NOT a rename of law*. The architecture is deliberately different:
-- lawDecode refuses each anti-model with a hand-written case check (overlong
-- inside the LEB decoder, junk at the tail). This codec refuses them all with
-- ONE canonicality law: decode = loose-parse then require
-- `encode (parsed) == input` byte-for-byte. A Wire value has exactly one byte
-- representation (the repo's founding claim, q = content hash is the unique
-- quotient, made mechanical): any non-canonical input — overlong LEB, junk
-- suffix, wrong length — fails re-encode equality and is refused by the same
-- clause. The mutant side is grok's own anti-model decoders (BundleRed), as
-- the RED intends: the adversary supplies the weakened arms, 1b supplies the
-- codec that diverges from them on every fixture.
--
-- closure_claim = 0.

import Residua.Bootstrap.BundleRed

namespace Residua.Bootstrap.Bundle

open Residua.Bootstrap.BundleRed

abbrev Bytes := Residua.Bootstrap.BundleRed.Bytes

/-! ## Format primitives — written here, not imported from law*.
    The wire format is frozen by the contract (tags i64=0 bytes=1, i64 leaf =
    tag + 8-byte LE, lengths = shortest unsigned LEB), so the ENCODERS of both
    sides necessarily agree; the judgement lives in decode. -/

def lebEnc (n : Nat) : Bytes :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: lebEnc (n / 128)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def natLe8 (u : Nat) (i : Nat) : UInt8 :=
  UInt8.ofNat ((u >>> (8 * i)) % 256)

def i64Bytes (n : Int) : Bytes :=
  let u := (if n < 0 then n + two64 else n).toNat
  [natLe8 u 0, natLe8 u 1, natLe8 u 2, natLe8 u 3,
   natLe8 u 4, natLe8 u 5, natLe8 u 6, natLe8 u 7]

def bEncode : Wire → Bytes
  | .i64 n => tagI64Leaf :: i64Bytes n
  | .bytes p => tagBytesLeaf :: (lebEnc p.length ++ p)

/-! ## Loose parse — accepts overlong LEB on purpose; the canonicality law
    in `bDecode` is what refuses it. -/

def lebLoose : Nat → Nat → Nat → Bytes → Option (Nat × Bytes)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, acc, shift, b :: rest =>
      let v := b.toNat
      let acc' := acc + (v % 128) * (2 ^ shift)
      if v < 128 then some (acc', rest)
      else lebLoose fuel acc' (shift + 7) rest

def le8ToNat (bs : Bytes) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

def u64ToI64 (u : Nat) : Int :=
  if u < 9223372036854775808 then (u : Int) else (u : Int) - two64

def bDecodeLoose (bs : Bytes) : Option Wire :=
  match bs with
  | [] => none
  | t :: rest =>
    if t == tagI64Leaf then
      match rest with
      | [b0, b1, b2, b3, b4, b5, b6, b7] =>
          some (.i64 (u64ToI64 (le8ToNat [b0, b1, b2, b3, b4, b5, b6, b7])))
      | _ => none
    else if t == tagBytesLeaf then
      match lebLoose (rest.length + 1) 0 0 rest with
      | some (len, payload) => if payload.length == len then some (.bytes payload) else none
      | none => none
    else none

/-- The codec's single refusal law: parse loosely, then the parse stands only
    if re-encoding it reproduces the input exactly. One canonical form per
    value; everything else is refused by this clause, not by per-case checks. -/
def bDecode (bs : Bytes) : Option Wire :=
  match bDecodeLoose bs with
  | some w => if bEncode w == bs then some w else none
  | none => none

def bAdmitKind (k : UInt8) : Bool := k == kindCode

def bManifestOk (declared : Bytes) (encodedDef : Bytes) : Bool :=
  declared == sha256Raw encodedDef

/-! ## Discharge — the codec routes every RED fixture; the mutant arms are
    grok's anti-models, exactly as the RED supplies them. -/

instance dischargeV1 : BundleCodecDischarge where
  decode := bDecode
  encode := bEncode
  admitKind := bAdmitKind
  manifestOk := bManifestOk
  pin_overlong := by decide!
  pin_junk := by decide!
  pin_dual := by decide!
  pin_kind := by decide!
  pin_manifest := by decide!
  pin_rt_i64 := by decide!
  decode' := mutantDecode
  admitKind' := mutantAdmitKind
  manifestOk' := mutantManifestOk
  mut_overlong := by decide!
  mut_junk := by decide!
  mut_dual := by decide!
  mut_kind := by decide!
  mut_manifest := by decide!

/-! ## Beyond the contract: pins the RED could not state about its own law*.
    These are the canonicality law's own teeth — properties specific to THIS
    architecture, not requirements copied from the class. -/

-- Round-trip on the bytes leaf, negative i64, and the i64 boundary values.
theorem rt_bytes : bDecode (bEncode (.bytes [0xAA])) = some (.bytes [0xAA]) := by
  decide!
theorem rt_i64_neg : bDecode (bEncode (.i64 (-1))) = some (.i64 (-1)) := by
  decide!
theorem rt_i64_min : bDecode (bEncode (.i64 i64Min)) = some (.i64 i64Min) := by
  decide!
theorem rt_i64_max : bDecode (bEncode (.i64 i64Max)) = some (.i64 i64Max) := by
  decide!

-- The canonicality law refuses a SECOND overlong shape the contract does not
-- fixture (three-byte encoding of 1): no per-case check exists for it here —
-- the same single clause refuses it. This is the pin that a hand-ported
-- rename of lawDecode would also pass, but for a different reason; stated to
-- record that the refusal generalises past the fixtures.
theorem overlong3_refused :
    bDecode (tagBytesLeaf :: ([0x81, 0x80, 0x00] ++ [0xAA])) = none := by
  decide!

-- Agreement with the RED's law on every contract fixture (four-eyes on the
-- fixtures themselves: two independently-written decoders, same verdicts).
theorem agrees_overlong : bDecode overlongBytes = lawDecode overlongBytes := by
  decide!
theorem agrees_junk : bDecode junkI64 = lawDecode junkI64 := by decide!
theorem agrees_dual : bDecode dualLeaf = lawDecode dualLeaf := by decide!
theorem agrees_canon1 : bDecode canonBytes1 = lawDecode canonBytes1 := by
  decide!

end Residua.Bootstrap.Bundle
