import Effect.ProcTrace
import Lib.Receipt

namespace Effect.Format

/-! The FORMAT q1 type controls each value's representation. Receipt's leaves
and SHA-256 are shared with the pinned opening and pair vectors. -/

mutual
  inductive Schema where
    | i64 | bool | str | bytes
    | list (item : Schema)
    | pair (first second : Schema)
    | sum (branches : Branches)
    | record (fields : Fields)
    | option (item : Schema)
    | residue (item : Schema)

  inductive Fields where
    | nil
    | cons (name : String) (field : Schema) (rest : Fields)

  inductive Branches where
    | nil
    | cons (branch : Schema) (rest : Branches)
end

def Schema.sum2 (left right : Schema) : Schema := .sum (.cons left (.cons right .nil))

def record (fields : List (String × Schema)) : Schema :=
  .record (fields.foldr (fun (name, field) rest => .cons name field rest) .nil)

/-- Two's-complement carrier of a representable mathematical i64. -/
abbrev I64 := UInt64

def signed (n : I64) : Int :=
  if n.toNat < 2^63 then Int.ofNat n.toNat else Int.ofNat n.toNat - 2^64

def checkedI64 (n : Int) : Option I64 :=
  if -(2^63) ≤ n && n < 2^63 then some (UInt64.ofNat (n % 2^64).toNat) else none

mutual
  def Schema.Value : Schema → Type
    | .i64 => I64
    | .bool => Bool
    | .str => String
    | .bytes => Bytes
    | .list item => List item.Value
    | .pair a b => a.Value × b.Value
    | .sum branches => branches.Value
    | .record fields => fields.Value
    | .option item => Option item.Value
    | .residue item => Sum item.Value I64

  def Fields.Value : Fields → Type
    | .nil => Unit
    | .cons _ field rest => field.Value × rest.Value

  def Branches.Value : Branches → Type
    | .nil => Empty
    | .cons branch .nil => branch.Value
    | .cons branch (.cons next rest) => Sum branch.Value (Branches.cons next rest).Value
end

def Fields.length : Fields → Nat
  | .nil => 0
  | .cons _ _ rest => rest.length + 1

def Branches.length : Branches → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

private def fromNats : List Nat → Bytes := List.map UInt8.ofNat

private def leb (n : Nat) : Bytes := fromNats (Lib.leb n)

private def byteLeaf (b : Bytes) : Bytes := fromNats (Lib.bytesLeaf (b.map UInt8.toNat))

private def intLeaf (n : I64) : Bytes := fromNats (Lib.i64Leaf n.toNat)

mutual
  def Schema.typeBytes : Schema → Bytes
    | .i64 => [0]
    | .bool => [1]
    | .str => [2]
    | .bytes => [3]
    | .list item => 4 :: item.typeBytes
    | .pair a b => 5 :: a.typeBytes ++ b.typeBytes
    | .sum branches => 6 :: leb branches.length ++ branches.typeBytes
    | .record fields => 7 :: leb fields.length ++ fields.typeBytes
    | .option item => 8 :: item.typeBytes
    | .residue item => 9 :: item.typeBytes

  def Fields.typeBytes : Fields → Bytes
    | .nil => []
    | .cons name field rest => byteLeaf (ascii name) ++ field.typeBytes ++ rest.typeBytes

  def Branches.typeBytes : Branches → Bytes
    | .nil => []
    | .cons branch rest => branch.typeBytes ++ rest.typeBytes
end

mutual
  def Schema.valueBytes : (schema : Schema) → schema.Value → Bytes
    | .i64, n => intLeaf n
    | .bool, b => [if (show Bool from b) then 1 else 0]
    | .str, v => byteLeaf (ascii v)
    | .bytes, v => byteLeaf v
    | .list item, vs => leb vs.length ++ vs.flatMap item.valueBytes
    | .pair a b, (x, y) => a.valueBytes x ++ b.valueBytes y
    | .sum branches, v => branches.valueBytes 0 v
    | .record fields, v => fields.valueBytes v
    | .option _, none => [0]
    | .option item, some v => 1 :: item.valueBytes v
    | .residue item, .inl v => 0 :: item.valueBytes v
    | .residue _, .inr n => 1 :: intLeaf n

  def Fields.valueBytes : (fields : Fields) → fields.Value → Bytes
    | .nil, _ => []
    | .cons _ field rest, (v, vs) => field.valueBytes v ++ rest.valueBytes vs

  def Branches.valueBytes : (branches : Branches) → Nat → branches.Value → Bytes
    | .nil, _, v => nomatch v
    | .cons branch .nil, n, v => leb n ++ branch.valueBytes v
    | .cons branch (.cons _ _), n, .inl v => leb n ++ branch.valueBytes v
    | .cons _ (.cons next rest), n, .inr v => (Branches.cons next rest).valueBytes (n + 1) v
end

def canonical (schema : Schema) (value : schema.Value) : Bytes :=
  fromNats Lib.valHeader ++ schema.typeBytes ++ schema.valueBytes value

def hashCanonical (preimage : Bytes) : Bytes :=
  let length := preimage.length
  -- FIPS 180-4 §5.1.1. Add 64 before subtraction to avoid Nat saturation.
  let zeroCount := (119 - length % 64) % 64
  let bitLength := 8 * length
  let lengthField := (List.range 8).reverse.map fun i => bitLength / 256^i % 256
  let padded := preimage.map UInt8.toNat ++ [128] ++ List.replicate zeroCount 0 ++ lengthField
  let s := Lib.blocks Lib.initH padded
  fromNats ([s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].flatMap Lib.bytes4)

def q (schema : Schema) (value : schema.Value) : Bytes := hashCanonical (canonical schema value)

def contextSchema : Schema := .record
  (.cons "abi" .str (.cons "ns" .bytes (.cons "profile" .bytes (.cons "plan" .bytes .nil))))

def openingSchema : Schema := record
  [("abi", .str), ("ns", .bytes), ("profile", .bytes), ("msize", .i64), ("plan", .bytes)]

def opening (abi : String) (ns profile : Bytes) (offer : I64) (plan : Bytes) : Bytes :=
  q openingSchema (abi, ns, profile, offer, plan, ())

def pairSchema : Schema := record [("prev", .bytes), ("t", .bytes), ("r", .bytes)]

def pair (prev t r : Bytes) : Bytes := q pairSchema (prev, t, r, ())

def lowerHex (bytes : Bytes) : Bytes :=
  bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)]
where
  digit (n : Nat) := UInt8.ofNat (if n < 10 then 48 + n else 87 + n)

end Effect.Format
