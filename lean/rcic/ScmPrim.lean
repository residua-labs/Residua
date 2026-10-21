/-
RCIC 06 §11 — primitive laws and micro-step charging (K2 statement layer).

Owner text (06:222-234): "`PrimOp` is a closed enum. Each op has exact
argument/result types, direct residue row, mathematical law, and explicit
machine implementation." The laws are stated on INTRINSIC values
(`CoreVals (primSig op).ps → LawResult (primSig op).rt`), as the
mathematical result: checked arithmetic returns the mathematical value when
it is in the i64 range and raises `signed_overflow` otherwise.

PIN (M-002): `scmPrim` is the carrier entry `rcic.scm_prim form op args
budget` of `apps/rcic-scm-prim` (#6036, #6039). It elaborates the raw
arguments with `toCore`, applies `primLaw` on the intrinsic values and erases
the result, so `primSig`, `primLaw`, `toCore`, `CoreVal` and `erase` are all
reachable from the 58 pinned rows (M-002a). A failing row fails the build
(`#guard`).

TRANSCRIPTION TABLE (06 §11 rule → Lean):
  "PrimOp is a closed enum"                       → `PrimOp` (14 ctors: the
        ops §11 names; the enum reading is the carrier's recorded
        `[spec_ambiguity]`)
  "exact argument/result types"                   → `primSig`
  "direct residue row"                            → `primRow`
  "Checked add/sub/mul/neg return the mathematical result when in range
   and SCM-raise signed_overflow otherwise"       → `checkedI64`, arms add/sub/mul/neg
  "Exact division distinguishes zero, MIN div -1 overflow, and nonexact
   division"                                      → arm div
  "Floor modulo has the divisor's sign and is not Wasm rem_s"
                                                  → arm mod (`Int.fmod`)
  "String length and slicing use Unicode scalar positions"
                                                  → arms str_len, str_slice
  "Empty split separators raise an exact residue" → arm str_split
  "String-to-i64 accepts the frozen ASCII grammar and distinguishes
   malformed input from overflow"                 → `parseI64`
  "Byte packing rejects values outside [0,255]"   → arm bytes_pack
  "Content hashing is raw SHA-256 …", structural equality, canonical
   encoding, parsing micro-machines               → NOT TRANSCRIBED: outside
        the carrier's enum (06 §11 DOES NOT DECIDE of the carrier); no
        carrier, M-002b
  "Variable-size work … explicit primitive micro-machines"
                                                  → `primCost` + form 1 of
        `scmPrim` (one step per element plus a completing step; budget
        exhaustion is suspension, never a residue)
-/
import rcic.ScmCore

namespace Rcic.Scm

/-! ## The closed enum and signatures -/

inductive PrimOp where
  | add | sub | mul | neg | div | mod | lt | eq
  | strLen | strSlice | strSplit | strToI64 | bytesPack | bytesLen
  deriving DecidableEq, Repr

def primOfString : String → Option PrimOp
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "neg" => some .neg
  | "div" => some .div
  | "mod" => some .mod
  | "lt" => some .lt
  | "eq" => some .eq
  | "str_len" => some .strLen
  | "str_slice" => some .strSlice
  | "str_split" => some .strSplit
  | "str_to_i64" => some .strToI64
  | "bytes_pack" => some .bytesPack
  | "bytes_len" => some .bytesLen
  | _ => none

/-- Exact argument types, result type, and whether the op is variable-size. -/
structure PrimSig where
  ps : List CoreTy
  rt : CoreTy
  varSize : Bool

def primSig : PrimOp → PrimSig
  | .add => ⟨[.i64, .i64], .i64, false⟩
  | .sub => ⟨[.i64, .i64], .i64, false⟩
  | .mul => ⟨[.i64, .i64], .i64, false⟩
  | .div => ⟨[.i64, .i64], .i64, false⟩
  | .mod => ⟨[.i64, .i64], .i64, false⟩
  | .neg => ⟨[.i64], .i64, false⟩
  | .lt => ⟨[.i64, .i64], .bool, false⟩
  | .eq => ⟨[.i64, .i64], .bool, false⟩
  | .strLen => ⟨[.str], .i64, true⟩
  | .strSlice => ⟨[.str, .i64, .i64], .str, true⟩
  | .strSplit => ⟨[.str, .str], .list .str, true⟩
  | .strToI64 => ⟨[.str], .i64, true⟩
  | .bytesPack => ⟨[.list .i64], .bytes, true⟩
  | .bytesLen => ⟨[.bytes], .i64, true⟩

/-- 06 §11 "direct residue row": the residues each op can raise, canonical
    sorted unique (06 §6). `str_len` / `bytes_len` follow §11's checked
    convention and raise `signed_overflow` for a length outside `i64`
    (E-06LenRows, 00 §19.7). -/
def primRow : PrimOp → ResidueRow
  | .add | .sub | .mul | .neg | .strLen | .bytesLen => ["signed_overflow"]
  | .div => ["division_by_zero", "nonexact_division", "signed_overflow"]
  | .mod => ["division_by_zero"]
  | .lt | .eq => []
  | .strSlice => ["index_out_of_range"]
  | .strSplit => ["empty_separator"]
  | .strToI64 => ["malformed_integer", "signed_overflow"]
  | .bytesPack => ["byte_out_of_range"]

/-! ## The mathematical laws -/

/-- Return the mathematical value when it is in range, else `signed_overflow`. -/
def checkedI64 (n : Int) : LawResult .i64 :=
  if h : inI64 n then .returned (.i64V n h) else .raised "signed_overflow"

def boolResult (b : Bool) : LawResult .bool := .returned (.boolV b)

/-- The frozen ASCII grammar `-?[0-9]+` (the carrier's recorded reading);
    malformed input and overflow are different residues. -/
def parseI64 (s : String) : LawResult .i64 :=
  let cs := s.toList
  let neg := cs.head? == some '-'
  let ds := if neg then cs.drop 1 else cs
  if ds.isEmpty || !(ds.all Char.isDigit) then .raised "malformed_integer"
  else
    let v : Int := ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) 0
    checkedI64 (if neg then -v else v)

def strList : List String → CoreList .str
  | [] => .nil
  | x :: xs => .cons (.strV x) (strList xs)

def packBytes : CoreList .i64 → Option (List UInt8)
  | .nil => some []
  | .cons (.i64V n _) xs =>
      if 0 ≤ n ∧ n ≤ 255 then (packBytes xs).map (fun r => UInt8.ofNat n.toNat :: r) else none

def primLaw : (op : PrimOp) → CoreVals (primSig op).ps → LawResult (primSig op).rt
  | .add, .cons (.i64V a _) (.cons (.i64V b _) .nil) => checkedI64 (a + b)
  | .sub, .cons (.i64V a _) (.cons (.i64V b _) .nil) => checkedI64 (a - b)
  | .mul, .cons (.i64V a _) (.cons (.i64V b _) .nil) => checkedI64 (a * b)
  | .neg, .cons (.i64V a _) .nil => checkedI64 (-a)
  | .div, .cons (.i64V a _) (.cons (.i64V b _) .nil) =>
      if b = 0 then .raised "division_by_zero"
      else if a % b ≠ 0 then .raised "nonexact_division"
      else checkedI64 (a / b)
  | .mod, .cons (.i64V a _) (.cons (.i64V b _) .nil) =>
      if b = 0 then .raised "division_by_zero" else checkedI64 (Int.fmod a b)
  | .lt, .cons (.i64V a _) (.cons (.i64V b _) .nil) => boolResult (decide (a < b))
  | .eq, .cons (.i64V a _) (.cons (.i64V b _) .nil) => boolResult (decide (a = b))
  | .strLen, .cons (.strV s) .nil => checkedI64 s.length
  | .strSlice, .cons (.strV s) (.cons (.i64V a _) (.cons (.i64V b _) .nil)) =>
      if 0 ≤ a ∧ a ≤ b ∧ b ≤ s.length then
        .returned (.strV (String.mk ((s.toList.drop a.toNat).take (b - a).toNat)))
      else .raised "index_out_of_range"
  | .strSplit, .cons (.strV s) (.cons (.strV sep) .nil) =>
      if sep = "" then .raised "empty_separator"
      else .returned (.listV (strList (s.splitOn sep)))
  | .strToI64, .cons (.strV s) .nil => parseI64 s
  | .bytesPack, .cons (.listV xs) .nil =>
      match packBytes xs with
      | some bs => .returned (.bytesV bs)
      | none => .raised "byte_out_of_range"
  | .bytesLen, .cons (.bytesV bs) .nil => checkedI64 bs.length

/-! ## Micro-step charging -/

/-- A constant-size op costs one step; a variable-size op costs one step per
    element of its first argument plus a completing step. -/
def primCost (varSize : Bool) (args : List Val) : Int :=
  if !varSize then 1 else
  match args with
  | .s s :: _ => s.length + 1
  | .y bs :: _ => bs.length + 1
  | .l xs :: _ => xs.length + 1
  | _ => 1

/-- The string-argument bound of the carrier: 2048 Unicode scalars. -/
def primBound : Nat := 2048

def firstStrLen : List Val → Nat
  | .s s :: _ => s.length
  | _ => 0

/-! ## The carrier entry point (raw) -/

structure PrimOut where
  ok : Int
  kind : Int
  v : Val
  r : String
  steps : Int
  code : String
  deriving BEq, Repr

def PrimOut.refuse (code : String) : PrimOut := ⟨0, 0, unitRaw, "", 0, code⟩

def PrimOut.ofLaw {t : CoreTy} (res : LawResult t) (steps : Int) : PrimOut :=
  match res with
  | .returned v => ⟨1, 0, v.erase, "", steps, ""⟩
  | .raised r => ⟨1, 1, unitRaw, r, steps, ""⟩

def scmPrim (form : Int) (op : String) (args : List Val) (budget : Int) : PrimOut :=
  if form ≠ 0 ∧ form ≠ 1 then .refuse "[rcic_scm_prim_unknown_form]" else
  match primOfString op with
  | none => .refuse "[rcic_scm_prim_unknown_op]"
  | some o =>
    match toCoreVals (primSig o).ps args with
    | none => .refuse "[rcic_scm_prim_ill_typed]"
    | some xs =>
      if firstStrLen args > primBound then .refuse "[rcic_scm_prim_bound]" else
      let cost := primCost (primSig o).varSize args
      if form = 1 then
        if budget < 0 then .refuse "[rcic_scm_prim_budget]"
        else if budget < cost then ⟨1, 2, unitRaw, "", budget, ""⟩
        else .ofLaw (primLaw o xs) cost
      else .ofLaw (primLaw o xs) cost

/-! ## Pins: apps/rcic-scm-prim/rcic_scm_prim_corpus.json, 58 rows

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with the prefix
"SCM-008 06 s11 " dropped. Expected values: `ret v steps`, `rai r steps`,
`susp steps`, `ref code` are the four record shapes of the carrier. -/

namespace PrimPins
def ret (v : Val) (steps : Int) : PrimOut := ⟨1, 0, v, "", steps, ""⟩
def rai (r : String) (steps : Int) : PrimOut := ⟨1, 1, unitRaw, r, steps, ""⟩
def susp (steps : Int) : PrimOut := ⟨1, 2, unitRaw, "", steps, ""⟩
def ref (code : String) : PrimOut := PrimOut.refuse code
def rep (n : Nat) (c : Char) : String := String.mk (List.replicate n c)
def MAX : Int := 9223372036854775807
def MIN : Int := -9223372036854775808

-- 0 checked add in range returns the sum
#guard scmPrim 0 "add" [.i 40, .i 2] 0 == ret (.i 42) 1
-- 1 checked add MAX+1 raises signed_overflow
#guard scmPrim 0 "add" [.i MAX, .i 1] 0 == rai "signed_overflow" 1
-- 2 checked add MIN+(-1) raises signed_overflow
#guard scmPrim 0 "add" [.i MIN, .i (-1)] 0 == rai "signed_overflow" 1
-- 3 checked sub in range returns the difference
#guard scmPrim 0 "sub" [.i 5, .i 9] 0 == ret (.i (-4)) 1
-- 4 checked sub MIN-1 raises signed_overflow
#guard scmPrim 0 "sub" [.i MIN, .i 1] 0 == rai "signed_overflow" 1
-- 5 checked sub MAX-(-1) raises signed_overflow
#guard scmPrim 0 "sub" [.i MAX, .i (-1)] 0 == rai "signed_overflow" 1
-- 6 checked mul in range returns the product
#guard scmPrim 0 "mul" [.i 6, .i (-7)] 0 == ret (.i (-42)) 1
-- 7 checked mul 2^32*2^32 raises signed_overflow
#guard scmPrim 0 "mul" [.i 4294967296, .i 4294967296] 0 == rai "signed_overflow" 1
-- 8 checked mul -2^62*2 = MIN is in range
#guard scmPrim 0 "mul" [.i (-4611686018427387904), .i 2] 0 == ret (.i MIN) 1
-- 9 checked mul 2^62*2 raises signed_overflow
#guard scmPrim 0 "mul" [.i 4611686018427387904, .i 2] 0 == rai "signed_overflow" 1
-- 10 checked mul MIN*-1 raises signed_overflow
#guard scmPrim 0 "mul" [.i MIN, .i (-1)] 0 == rai "signed_overflow" 1
-- 11 checked neg returns the negation
#guard scmPrim 0 "neg" [.i 5] 0 == ret (.i (-5)) 1
-- 12 checked neg MIN raises signed_overflow
#guard scmPrim 0 "neg" [.i MIN] 0 == rai "signed_overflow" 1
-- 13 exact division returns the exact quotient
#guard scmPrim 0 "div" [.i (-7), .i 7] 0 == ret (.i (-1)) 1
-- 14 exact division by zero raises division_by_zero
#guard scmPrim 0 "div" [.i 7, .i 0] 0 == rai "division_by_zero" 1
-- 15 exact division MIN div -1 raises signed_overflow
#guard scmPrim 0 "div" [.i MIN, .i (-1)] 0 == rai "signed_overflow" 1
-- 16 exact division 7/2 raises nonexact_division
#guard scmPrim 0 "div" [.i 7, .i 2] 0 == rai "nonexact_division" 1
-- 17 floor modulo 7 mod -3 has the divisor sign -2
#guard scmPrim 0 "mod" [.i 7, .i (-3)] 0 == ret (.i (-2)) 1
-- 18 floor modulo -7 mod 3 has the divisor sign 2
#guard scmPrim 0 "mod" [.i (-7), .i 3] 0 == ret (.i 2) 1
-- 19 floor modulo -7 mod -3 is -1
#guard scmPrim 0 "mod" [.i (-7), .i (-3)] 0 == ret (.i (-1)) 1
-- 20 floor modulo 7 mod 3 is 1
#guard scmPrim 0 "mod" [.i 7, .i 3] 0 == ret (.i 1) 1
-- 21 floor modulo by zero raises division_by_zero
#guard scmPrim 0 "mod" [.i 7, .i 0] 0 == rai "division_by_zero" 1
-- 22 lt compares i64
#guard scmPrim 0 "lt" [.i (-1), .i 1] 0 == ret (.b 1) 1
-- 23 eq compares i64
#guard scmPrim 0 "eq" [.i 3, .i 4] 0 == ret (.b 0) 1
-- 24 string length counts Unicode scalars
#guard scmPrim 0 "str_len" [.s "héé"] 0 == ret (.i 3) 4
-- 25 string slice uses scalar positions
#guard scmPrim 0 "str_slice" [.s "héllo", .i 1, .i 3] 0 == ret (.s "él") 6
-- 26 string slice end past length raises index_out_of_range
#guard scmPrim 0 "str_slice" [.s "abc", .i 1, .i 4] 0 == rai "index_out_of_range" 4
-- 27 string slice start after end raises index_out_of_range
#guard scmPrim 0 "str_slice" [.s "abc", .i 2, .i 1] 0 == rai "index_out_of_range" 4
-- 28 string slice negative start raises index_out_of_range
#guard scmPrim 0 "str_slice" [.s "abc", .i (-1), .i 1] 0 == rai "index_out_of_range" 4
-- 29 string split returns the parts
#guard scmPrim 0 "str_split" [.s "a,,b", .s ","] 0 == ret (.l [.s "a", .s "", .s "b"]) 5
-- 30 string split with empty separator raises empty_separator
#guard scmPrim 0 "str_split" [.s "abc", .s ""] 0 == rai "empty_separator" 4
-- 31 string to i64 parses the ASCII grammar
#guard scmPrim 0 "str_to_i64" [.s "-42"] 0 == ret (.i (-42)) 4
-- 32 string to i64 parses MIN exactly
#guard scmPrim 0 "str_to_i64" [.s "-9223372036854775808"] 0 == ret (.i MIN) 21
-- 33 string to i64 leading zeros are digits  (72 × '0' then '7')
#guard scmPrim 0 "str_to_i64" [.s (rep 72 '0' ++ "7")] 0 == ret (.i 7) 74
-- 34 string to i64 malformed 4a raises malformed_integer
#guard scmPrim 0 "str_to_i64" [.s "4a"] 0 == rai "malformed_integer" 3
-- 35 string to i64 plus sign raises malformed_integer
#guard scmPrim 0 "str_to_i64" [.s "+1"] 0 == rai "malformed_integer" 3
-- 36 string to i64 empty raises malformed_integer
#guard scmPrim 0 "str_to_i64" [.s ""] 0 == rai "malformed_integer" 1
-- 37 string to i64 lone minus raises malformed_integer
#guard scmPrim 0 "str_to_i64" [.s "-"] 0 == rai "malformed_integer" 2
-- 38 string to i64 digit past position 64 checked raises malformed_integer  (64 × '1' then 'a')
#guard scmPrim 0 "str_to_i64" [.s (rep 64 '1' ++ "a")] 0 == rai "malformed_integer" 66
-- 39 string to i64 MAX+1 raises signed_overflow not malformed
#guard scmPrim 0 "str_to_i64" [.s "9223372036854775808"] 0 == rai "signed_overflow" 20
-- 40 string to i64 twenty digits raises signed_overflow
#guard scmPrim 0 "str_to_i64" [.s "12345678901234567890"] 0 == rai "signed_overflow" 21
-- 41 string over the 2048 scalar bound refused not decided  (2049 × '1')
#guard scmPrim 0 "str_to_i64" [.s (rep 2049 '1')] 0 == ref "[rcic_scm_prim_bound]"
-- 42 byte packing returns bytes
#guard scmPrim 0 "bytes_pack" [.l [.i 0, .i 255, .i 7]] 0 == ret (.y [0, 255, 7]) 4
-- 43 byte packing 256 raises byte_out_of_range
#guard scmPrim 0 "bytes_pack" [.l [.i 1, .i 256]] 0 == rai "byte_out_of_range" 3
-- 44 byte packing -1 raises byte_out_of_range
#guard scmPrim 0 "bytes_pack" [.l [.i (-1)]] 0 == rai "byte_out_of_range" 2
-- 45 bytes length
#guard scmPrim 0 "bytes_len" [.y [1, 2, 3]] 0 == ret (.i 3) 4
-- 46 micro-machine budget exactly the cost completes
#guard scmPrim 1 "str_len" [.s "abcd"] 5 == ret (.i 4) 5
-- 47 micro-machine budget one short suspends never a residue
#guard scmPrim 1 "str_len" [.s "abcd"] 4 == susp 4
-- 48 micro-machine raising op completes within budget
#guard scmPrim 1 "str_to_i64" [.s "4a"] 3 == rai "malformed_integer" 3
-- 49 micro-machine raising op one short suspends
#guard scmPrim 1 "str_to_i64" [.s "4a"] 2 == susp 2
-- 50 constant op in micro form costs one step
#guard scmPrim 1 "add" [.i 1, .i 2] 1 == ret (.i 3) 1
-- 51 negative micro budget refused
#guard scmPrim 1 "add" [.i 1, .i 2] (-1) == ref "[rcic_scm_prim_budget]"
-- 52 ill-typed argument refused as integrity not a residue
#guard scmPrim 0 "add" [.i 1, .s "2"] 0 == ref "[rcic_scm_prim_ill_typed]"
-- 53 wrong arity refused as integrity
#guard scmPrim 0 "neg" [.i 1, .i 2] 0 == ref "[rcic_scm_prim_ill_typed]"
-- 54 byte value outside the bytes type refused as ill-typed
#guard scmPrim 0 "bytes_len" [.y [300]] 0 == ref "[rcic_scm_prim_ill_typed]"
-- 55 unknown op refused
#guard scmPrim 0 "sha256" [.y []] 0 == ref "[rcic_scm_prim_unknown_op]"
-- 56 unknown form refused
#guard scmPrim 2 "add" [.i 1, .i 2] 0 == ref "[rcic_scm_prim_unknown_form]"
-- 57 string to i64 2048 digits then x is past the bound refused not decided  (2048 × '1' then 'x')
#guard scmPrim 0 "str_to_i64" [.s (rep 2048 '1' ++ "x")] 0 == ref "[rcic_scm_prim_bound]"
end PrimPins

/-! ## Instance witnesses (M-005) -/

example : (primLaw .add (.cons (.i64V 1 ⟨by decide, by decide⟩) (.cons (.i64V 2 ⟨by decide, by decide⟩) .nil))
    matches .returned (.i64V 3 _)) = true := rfl

end Rcic.Scm
