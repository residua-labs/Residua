import Residua.Bootstrap.IR
import Residua.Bootstrap.Semantics

/-!
# Bootstrap 1c r2 (S4 revision 2, UINT64-0) — independent SCM target semantics

Revision 2 of `Residua.Bootstrap.SCM` (a frozen spec is never edited in place): the same
syntax and evaluator plus the fourteen width-64 word operators of docs/EMITTER.md
"RSCM revision UINT64-0 (W row)" (wire tags 64 to 77; their meaning on `Nat` mod `2^64`,
Lean's `UInt64` functions). Everything else is the file `SCM.lean` byte for byte.

This module freezes the target side of the 1c lowering boundary.  The target
keeps the source type indices and de Bruijn scope shapes, but it has its own
syntax, program tables, runtime values, and evaluator.  In particular, bytes,
pairs, and sums are represented by ordinary target lists/records rather than
hidden runtime constructors.

Record keys remain ordered `String`s in the semantic model.  Identifier
validation is a separate, explicit serialization audit, so lowering remains
total for every already-frozen `BootTy.record` key.

No proof holes or added axioms.  `closure_claim = 0`.
-/

namespace Residua.Bootstrap.R2.SCM

open Residua.Bootstrap.IR

/-- Runtime values visible after lowering.  Bytes and pairs are lists; sums
    are ordered records. -/
inductive SCMVal where
  | int    (n : Int)
  | bool   (b : Bool)
  | str    (s : String)
  | list   (vs : List SCMVal)
  | record (fs : List (String × SCMVal))
  | someV  (v : SCMVal)
  | noneV
  | ok     (v : SCMVal)
  | res    (code : Int)
  deriving Repr

abbrev SCMEnv := List SCMVal

mutual

/-- Intrinsically typed, scope-indexed target expressions. -/
inductive SCMExpr : SigTable → Ctx → BootTy → Type where
  | litI  : Int → SCMExpr S G .i64
  | litB  : Bool → SCMExpr S G .bool
  | litS  : String → SCMExpr S G .str
  | var   : (i : Fin G.length) → SCMExpr S G (G.get i)
  | let1  : SCMExpr S G a → SCMExpr S (a :: G) b → SCMExpr S G b
  | ifE   : SCMExpr S G .bool → SCMExpr S G t → SCMExpr S G t → SCMExpr S G t

  | add   : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | sub   : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | mul   : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | neg   : SCMExpr S G .i64 → SCMExpr S G .i64
  | divE  : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | modE  : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64

  | lt    : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .bool
  | gt    : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .bool
  | eqE   : SCMExpr S G t → SCMExpr S G t → SCMExpr S G .bool
  | andE  : SCMExpr S G .bool → SCMExpr S G .bool → SCMExpr S G .bool
  | orE   : SCMExpr S G .bool → SCMExpr S G .bool → SCMExpr S G .bool
  | notE  : SCMExpr S G .bool → SCMExpr S G .bool

  | strLen       : SCMExpr S G .str → SCMExpr S G .i64
  | strSplit     : SCMExpr S G .str → SCMExpr S G .str → SCMExpr S G (.list .str)
  | strSubstring : SCMExpr S G .str → SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .str
  | strToInt     : SCMExpr S G .str → SCMExpr S G .i64

  | emptyList     : SCMExpr S G (.list t)
  | listSingleton : SCMExpr S G t → SCMExpr S G (.list t)
  | listLen       : SCMExpr S G (.list t) → SCMExpr S G .i64
  | listFirst     : SCMExpr S G (.list t) → SCMExpr S G (.option t)
  | listAppend    : SCMExpr S G (.list t) → SCMExpr S G (.list t) → SCMExpr S G (.list t)
  | listDrop      : SCMExpr S G .i64 → SCMExpr S G (.list t) → SCMExpr S G (.list t)

  /-- A target pair is represented by exactly `.list [a, b]`. -/
  | pairE : SCMExpr S G a → SCMExpr S G b → SCMExpr S G (.pair a b)
  | fstE  : SCMExpr S G (.pair a b) → SCMExpr S G a
  | sndE  : SCMExpr S G (.pair a b) → SCMExpr S G b

  /-- A target sum is `[('tag', i64 i), ('val', payload)]` in this order. -/
  | inj    : (i : Fin ts.length) → SCMExpr S G (ts.get i) → SCMExpr S G (.sum ts)
  | matchE : SCMExpr S G (.sum ts) → SCMBranches S G ts r → SCMExpr S G r

  | recNil  : SCMExpr S G (.record [])
  | recCons : (name : String) → SCMExpr S G t → SCMExpr S G (.record fs) →
              SCMExpr S G (.record ((name, t) :: fs))
  | field   : SCMExpr S G (.record fs) → (i : Fin fs.length) →
              SCMExpr S G (fs.get i).2

  | someE      : SCMExpr S G t → SCMExpr S G (.option t)
  | noneE      : SCMExpr S G (.option t)
  | isSomeE    : SCMExpr S G (.option t) → SCMExpr S G .bool
  | unwrapSome : SCMExpr S G (.option t) → SCMExpr S G t

  | okE        : SCMExpr S G t → SCMExpr S G (.residue t)
  | residueE   : Int → SCMExpr S G (.residue t)
  | isResidueE : SCMExpr S G (.residue t) → SCMExpr S G .bool
  | getResidue : SCMExpr S G (.residue t) → SCMExpr S G .i64
  | getOk      : SCMExpr S G (.residue t) → SCMExpr S G t

  /-- Bytes stay in the checked list-of-i64 representation at every node. -/
  | packBytes   : SCMExpr S G (.list .i64) → SCMExpr S G .bytes
  | bytesLen    : SCMExpr S G .bytes → SCMExpr S G .i64
  | bytesConcat : SCMExpr S G .bytes → SCMExpr S G .bytes → SCMExpr S G .bytes
  | bytesSlice  : SCMExpr S G .bytes → SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .bytes
  | contentHash : SCMExpr S G .bytes → SCMExpr S G .bytes

  /-- One target fold node; body binds element at 0 and accumulator at 1. -/
  | boundedFold : SCMExpr S G (.list a) → SCMExpr S G b →
                  SCMExpr S (a :: b :: G) b → SCMExpr S G b
  /-- One target fix node; stop and step each bind the state at 0. -/
  | boundedFix  : SCMExpr S (s :: G) .bool → SCMExpr S (s :: G) s →
                  SCMExpr S G s → SCMExpr S G .i64 →
                  SCMExpr S G (fixResultTy s)
  /-- Calls retain the ordered signature-table index. -/
  | call : (f : Fin S.length) → SCMArgs S G (S.get f).1 → SCMExpr S G (S.get f).2

  /-- Revision 2: width-64 words. A value is an `int` with `0 ≤ n < 2^64`; the type stays `.i64`. -/
  | litW : UInt64 → SCMExpr S G .i64
  | wAdd : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wSub : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wMul : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wDiv : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wMod : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wLt  : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .bool
  | wLe  : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .bool
  | wAnd : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wOr  : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wXor : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wNot : SCMExpr S G .i64 → SCMExpr S G .i64
  | wShl : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64
  | wShr : SCMExpr S G .i64 → SCMExpr S G .i64 → SCMExpr S G .i64

/-- Fresh target argument vectors. -/
inductive SCMArgs : SigTable → Ctx → List BootTy → Type where
  | nil  : SCMArgs S G []
  | cons : SCMExpr S G t → SCMArgs S G ts → SCMArgs S G (t :: ts)

/-- Fresh target branch vectors; each branch binds its payload at index 0. -/
inductive SCMBranches : SigTable → Ctx → List BootTy → BootTy → Type where
  | nil  : SCMBranches S G [] r
  | cons : SCMExpr S (t :: G) r → SCMBranches S G ts r → SCMBranches S G (t :: ts) r

end

/-- A target program table, independent of `IR.Programs`. -/
inductive SCMPrograms : SigTable → SigTable → Type where
  | nil  : SCMPrograms S []
  | cons : SCMExpr S sig.1 sig.2 → SCMPrograms S rest → SCMPrograms S (sig :: rest)

/-! ## Runtime representation helpers -/

mutual

/-- Structural equality on target values. -/
def scmValEq : SCMVal → SCMVal → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .list xs, .list ys => scmValEqList xs ys
  | .record fs, .record gs => scmValEqFields fs gs
  | .someV a, .someV b => scmValEq a b
  | .noneV, .noneV => true
  | .ok a, .ok b => scmValEq a b
  | .res a, .res b => a == b
  | _, _ => false

def scmValEqList : List SCMVal → List SCMVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => scmValEq x y && scmValEqList xs ys
  | _, _ => false

def scmValEqFields : List (String × SCMVal) → List (String × SCMVal) → Bool
  | [], [] => true
  | (n, x) :: xs, (m, y) :: ys => n == m && scmValEq x y && scmValEqFields xs ys
  | _, _ => false

end

mutual

/-- `scmValEq` has no false positives. -/
theorem scmValEq_sound : ∀ a b, scmValEq a b = true → a = b
  | .int a, .int b, h => by
      have : a = b := LawfulBEq.eq_of_beq h
      cases this
      rfl
  | .bool a, .bool b, h => by
      have : a = b := LawfulBEq.eq_of_beq h
      cases this
      rfl
  | .str a, .str b, h => by
      have : a = b := LawfulBEq.eq_of_beq h
      cases this
      rfl
  | .list xs, .list ys, h => by
      have : xs = ys := scmValEqList_sound xs ys h
      cases this
      rfl
  | .record fs, .record gs, h => by
      have : fs = gs := scmValEqFields_sound fs gs h
      cases this
      rfl
  | .someV a, .someV b, h => by
      have : a = b := scmValEq_sound a b h
      cases this
      rfl
  | .noneV, .noneV, _ => rfl
  | .ok a, .ok b, h => by
      have : a = b := scmValEq_sound a b h
      cases this
      rfl
  | .res a, .res b, h => by
      have : a = b := LawfulBEq.eq_of_beq h
      cases this
      rfl
  | a, b, h => by
      cases a <;> cases b <;> simp [scmValEq] at h
      case int.int => cases h; rfl
      case bool.bool => cases h; rfl
      case str.str => cases h; rfl
      case list.list xs ys =>
        have : xs = ys := scmValEqList_sound xs ys h
        cases this
        rfl
      case record.record fs gs =>
        have : fs = gs := scmValEqFields_sound fs gs h
        cases this
        rfl
      case someV.someV a b =>
        have : a = b := scmValEq_sound a b h
        cases this
        rfl
      case noneV.noneV => rfl
      case ok.ok a b =>
        have : a = b := scmValEq_sound a b h
        cases this
        rfl
      case res.res => cases h; rfl

theorem scmValEqList_sound : ∀ xs ys, scmValEqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      have hs : scmValEq x y = true ∧ scmValEqList xs ys = true := by
        simpa only [scmValEqList, Bool.and_eq_true] using h
      have hxy : x = y := scmValEq_sound x y hs.1
      have hrest : xs = ys := scmValEqList_sound xs ys hs.2
      cases hxy
      cases hrest
      rfl
  | [], _ :: _, h => by simp [scmValEqList] at h
  | _ :: _, [], h => by simp [scmValEqList] at h

theorem scmValEqFields_sound : ∀ fs gs, scmValEqFields fs gs = true → fs = gs
  | [], [], _ => rfl
  | (n, x) :: fs, (m, y) :: gs, h => by
      have hs : ((n == m) = true ∧ scmValEq x y = true) ∧
          scmValEqFields fs gs = true := by
        simpa only [scmValEqFields, Bool.and_eq_true] using h
      have hn : n = m := LawfulBEq.eq_of_beq hs.1.1
      have hv : x = y := scmValEq_sound x y hs.1.2
      have hrest : fs = gs := scmValEqFields_sound fs gs hs.2
      cases hn
      cases hv
      cases hrest
      rfl
  | [], _ :: _, h => by simp [scmValEqFields] at h
  | _ :: _, [], h => by simp [scmValEqFields] at h

end

/-- Boolean output check for executable target pins. -/
def scmOutEq (o : Option SCMVal) (v : SCMVal) : Bool :=
  match o with
  | some w => scmValEq w v
  | none => false

/-- One checked list entry at the byte boundary. -/
def restoreByte : SCMVal → Option UInt8
  | .int n =>
      if 0 ≤ n ∧ n ≤ 255 then some (UInt8.ofNat n.toNat) else none
  | _ => none

/-- Checked restoration of the entries of a byte-representation list. -/
def restoreByteList : List SCMVal → Option (List UInt8)
  | [] => some []
  | v :: vs =>
      match restoreByte v, restoreByteList vs with
      | some b, some bs => some (b :: bs)
      | _, _ => none

/-- Stack-bounded execution of the checked byte boundary. The original
    definition remains the kernel-facing specification. -/
def restoreByteListTR (vs : List SCMVal) : Option (List UInt8) :=
  go vs []
where
  go : List SCMVal → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | v :: vs, acc =>
        match restoreByte v with
        | none => none
        | some b => go vs (b :: acc)

/-! Checked byte length without materializing the restored byte list.  This
has exactly the same acceptance boundary as `restoreByteListTR`; the counter
is only used by the length-only `bytesLen` evaluator case below. -/
def restoreByteLengthTR (vs : List SCMVal) : Option Nat :=
  go vs 0
where
  go : List SCMVal → Nat → Option Nat
    | [], count => some count
    | v :: vs, count =>
        match restoreByte v with
        | none => none
        | some _ => go vs (count + 1)

theorem restoreByteLengthTR_eq_restoreByteList (vs : List SCMVal) :
    restoreByteLengthTR vs = (restoreByteList vs).map List.length := by
  have go_eq : ∀ (xs : List SCMVal) (count : Nat),
      restoreByteLengthTR.go xs count =
        (restoreByteList xs).map (fun bs => bs.length + count) := by
    intro xs
    induction xs with
    | nil => intro count; simp [restoreByteLengthTR.go, restoreByteList]
    | cons v vs ih =>
        intro count
        cases h : restoreByte v with
        | none => simp [restoreByteLengthTR.go, restoreByteList, h]
        | some b =>
            cases hs : restoreByteList vs with
            | none =>
                simp only [restoreByteLengthTR.go, h]
                rw [ih (count + 1), hs]
                simp [restoreByteList, h, hs]
            | some bs =>
                simp only [restoreByteLengthTR.go, h]
                rw [ih (count + 1), hs]
                simp [restoreByteList, h, hs, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm]
  simpa [restoreByteLengthTR] using go_eq vs 0

private theorem restoreByteListTR_go (vs : List SCMVal) (acc : List UInt8) :
    restoreByteListTR.go vs acc =
      (restoreByteList vs).map (fun bs => acc.reverse ++ bs) := by
  induction vs generalizing acc with
  | nil => simp [restoreByteListTR.go, restoreByteList]
  | cons v vs ih =>
      cases hb : restoreByte v with
      | none => simp [restoreByteListTR.go, restoreByteList, hb]
      | some b =>
          simp only [restoreByteListTR.go, hb]
          rw [ih]
          cases hs : restoreByteList vs <;>
            simp [restoreByteList, hb, hs, List.reverse_cons, List.append_assoc]

/-- Compiler optimization justified for every byte list, including malformed
    entries; no alternate acceptance condition or unchecked implementation. -/
@[csimp] theorem restoreByteList_eq_restoreByteListTR :
    restoreByteList = restoreByteListTR := by
  funext vs
  simp [restoreByteListTR, restoreByteListTR_go]

theorem restoreByteLengthTR_eq_restoreByteListTR (vs : List SCMVal) :
    restoreByteLengthTR vs = (restoreByteListTR vs).map List.length := by
  rw [← restoreByteList_eq_restoreByteListTR]
  exact restoreByteLengthTR_eq_restoreByteList vs

/-- Restore raw bytes only from a list of i64 entries in `0..255`. -/
def restoreBytes : SCMVal → Option (List UInt8)
  | .list vs => restoreByteList vs
  | _ => none

/- The specification-shaped bytes-length operation is kept as the evaluator
   interface.  Its csimp image below avoids materializing the byte list. -/
abbrev bytesLenEval (v : SCMVal) : Option SCMVal :=
  (restoreBytes v).map (fun raw => .int (raw.length : Int))

private def bytesLenEvalFast (v : SCMVal) : Option SCMVal :=
  match v with
  | .list vs => (restoreByteLengthTR vs).map (fun n => .int (n : Int))
  | _ => none

@[csimp] theorem bytesLenEval_eq_bytesLenEvalFast :
    bytesLenEval = bytesLenEvalFast := by
  funext v
  cases v with
  | list vs =>
      simp only [bytesLenEval, bytesLenEvalFast, restoreBytes]
      rw [restoreByteLengthTR_eq_restoreByteList]
      cases h : restoreByteList vs <;>
        simp [h]
  | _ => simp [bytesLenEval, bytesLenEvalFast, restoreBytes]

/-- The sole target representation of raw bytes. -/
def bytesToSCM (bs : List UInt8) : SCMVal :=
  .list (bs.map (fun b => .int (b.toNat : Int)))

private theorem restoreByte_ofUInt8 (b : UInt8) :
    restoreByte (.int (b.toNat : Int)) = some b := by
  have hRange : (0 : Int) ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ 255 := by
    have h : b.toNat < 256 := by
      simpa [UInt8.size] using UInt8.toNat_lt_size b
    constructor <;> omega
  have hRound : UInt8.ofNat b.toNat = b := by
    apply UInt8.toNat.inj
    rw [UInt8.toNat_ofNat_of_lt (UInt8.toNat_lt_size b)]
  simp [restoreByte, hRange, hRound]

theorem restoreByteList_bytes (bs : List UInt8) :
    restoreByteList (bs.map (fun b => .int (b.toNat : Int))) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [restoreByteList, restoreByte_ofUInt8, ih]

/-- General checked-representation round trip. -/
@[simp] theorem restoreBytes_bytesToSCM (bs : List UInt8) :
    restoreBytes (bytesToSCM bs) = some bs := by
  simp [restoreBytes, bytesToSCM, restoreByteList_bytes]

theorem restoreBytes_hi :
    restoreBytes (.list [.int 104, .int 105]) = some [104, 105] := by
  decide

theorem restoreBytes_negative :
    restoreBytes (.list [.int (-1)]) = none := by
  decide

theorem restoreBytes_too_large :
    restoreBytes (.list [.int 256]) = none := by
  decide

/-- ContentHash's target value boundary.  The only hash preimage is the raw
    byte list returned by `restoreBytes`. -/
def contentHashValue (v : SCMVal) : Option SCMVal :=
  (restoreBytes v).map (fun raw => bytesToSCM (Semantics.sha256Raw raw))

/-- Definition-level q alignment: represented raw bytes are restored first,
    then passed unchanged to the bundle's raw SHA-256 function. -/
theorem contentHashValue_bytes (raw : List UInt8) :
    contentHashValue (bytesToSCM raw) =
      some (bytesToSCM (Semantics.sha256Raw raw)) := by
  simp [contentHashValue]

/-! ## Serialization identifier audit -/

/-! The from-zero bootstrap tree deliberately has no dependency on the old
    host-side `Residua.SCMEmission` module.  Keep the record-key boundary
    self-contained while preserving that module's frozen identifier grammar. -/

inductive SCMIdentifierError
  | empty
  | tooLong
  | numeric
  | boolean
  | reserved
  | forbiddenChar (value : Char)
  deriving DecidableEq, Repr

@[reducible] def reservedSCMIdentifierHeads : List String :=
  ["call", "field", "and", "not", "=", "record", "if", "let", "fold"]

@[reducible] def firstForbiddenSCMIdentifierChar : List Char → Option Char
  | [] => none
  | char :: chars =>
      if char.isWhitespace || char == '"' || char == '\\' || char == ';' ||
          char == '(' || char == ')' then
        some char
      else
        firstForbiddenSCMIdentifierChar chars

/-- Frozen decimal alphabet, shared by the host audit and emitted source checker. -/
@[reducible] def scmDecimalRanges : List (Nat × Nat) :=
  [(0x0030, 0x0039), (0x0660, 0x0669), (0x06f0, 0x06f9),
   (0x07c0, 0x07c9), (0x0966, 0x096f), (0x09e6, 0x09ef),
   (0x0a66, 0x0a6f), (0x0ae6, 0x0aef), (0x0b66, 0x0b6f),
   (0x0be6, 0x0bef), (0x0c66, 0x0c6f), (0x0ce6, 0x0cef),
   (0x0d66, 0x0d6f), (0x0de6, 0x0def), (0x0e50, 0x0e59),
   (0x0ed0, 0x0ed9), (0x0f20, 0x0f29), (0x1040, 0x1049),
   (0x1090, 0x1099), (0x17e0, 0x17e9), (0x1810, 0x1819),
   (0x1946, 0x194f), (0x19d0, 0x19d9), (0x1a80, 0x1a89),
   (0x1a90, 0x1a99), (0x1b50, 0x1b59), (0x1bb0, 0x1bb9),
   (0x1c40, 0x1c49), (0x1c50, 0x1c59), (0xa620, 0xa629),
   (0xa8d0, 0xa8d9), (0xa900, 0xa909), (0xa9d0, 0xa9d9),
   (0xa9f0, 0xa9f9), (0xaa50, 0xaa59), (0xabf0, 0xabf9),
   (0xff10, 0xff19), (0x104a0, 0x104a9), (0x10d30, 0x10d39),
   (0x10d40, 0x10d49), (0x11066, 0x1106f), (0x110f0, 0x110f9),
   (0x11136, 0x1113f), (0x111d0, 0x111d9), (0x112f0, 0x112f9),
   (0x11450, 0x11459), (0x114d0, 0x114d9), (0x11650, 0x11659),
   (0x116c0, 0x116c9), (0x116d0, 0x116e3), (0x11730, 0x11739),
   (0x118e0, 0x118e9), (0x11950, 0x11959), (0x11bf0, 0x11bf9),
   (0x11c50, 0x11c59), (0x11d50, 0x11d59), (0x11da0, 0x11da9),
   (0x11f50, 0x11f59), (0x16130, 0x16139), (0x16a60, 0x16a69),
   (0x16ac0, 0x16ac9), (0x16b50, 0x16b59), (0x16d70, 0x16d79),
   (0x1ccf0, 0x1ccf9), (0x1d7ce, 0x1d7ff), (0x1e140, 0x1e149),
   (0x1e2f0, 0x1e2f9), (0x1e4f0, 0x1e4f9), (0x1e5f1, 0x1e5fa),
   (0x1e950, 0x1e959), (0x1fbf0, 0x1fbf9)]

@[reducible] def isSCMDecimalDigit (char : Char) : Bool :=
  scmDecimalRanges.any fun (first, last) => first <= char.toNat && char.toNat <= last

@[reducible] def isSCMNumericBody : List Char → Bool → Bool
  | [], sawDigit => sawDigit
  | char :: chars, sawDigit =>
      if isSCMDecimalDigit char then
        isSCMNumericBody chars true
      else if char == '_' then
        isSCMNumericBody chars sawDigit
      else
        false

@[reducible] def isSCMNumericLike (value : String) : Bool :=
  match value.toList with
  | '+' :: chars => isSCMNumericBody chars false
  | '-' :: chars => isSCMNumericBody chars false
  | chars => isSCMNumericBody chars false

@[reducible] def scmIdentifierError? (value : String) : Option SCMIdentifierError :=
  if value.isEmpty then
    some .empty
  else if value.length > 1024 then
    some .tooLong
  else if isSCMNumericLike value then
    some .numeric
  else if value == "#t" || value == "#f" then
    some .boolean
  else if reservedSCMIdentifierHeads.contains value then
    some .reserved
  else
    match firstForbiddenSCMIdentifierChar value.toList with
    | some char => some (.forbiddenChar char)
    | none => none

abbrev isValidSCMIdentifier (value : String) : Bool :=
  (scmIdentifierError? value).isNone

/-- A record key that can cross the SCM serialization boundary unchanged. -/
structure SCMRecordKey where
  private mk ::
  value : String
  valid : isValidSCMIdentifier value = true

def SCMRecordKey.ofString (value : String) :
    Except SCMIdentifierError SCMRecordKey :=
  match h : scmIdentifierError? value with
  | none => .ok ⟨value, by
      change (scmIdentifierError? value).isNone = true
      rw [h]
      rfl⟩
  | some error => .error error

/-- Fast preflight for the serialization boundary. -/
abbrev isSerializableRecordKey (key : String) : Bool :=
  isValidSCMIdentifier key

/-- Parse a semantic string as a record-key identifier without sanitizing it. -/
def parseRecordKey (key : String) :
    Except SCMIdentifierError SCMRecordKey :=
  SCMRecordKey.ofString key

/-- Audit one key, preserving validation errors from `SCMRecordKey.ofString`. -/
def auditRecordKey (key : String) :
    Except SCMIdentifierError Unit :=
  (parseRecordKey key).map (fun _ => ())

private def auditBoth
    (a b : Except SCMIdentifierError Unit) :
    Except SCMIdentifierError Unit :=
  match a with
  | .error e => .error e
  | .ok _ => b

mutual

/-- Recursively audit every record key in a type, including nested schemas. -/
def auditBootTy : BootTy →
    Except SCMIdentifierError Unit
  | .i64 | .bool | .str | .bytes => .ok ()
  | .list t | .option t | .residue t => auditBootTy t
  | .pair a b => auditBoth (auditBootTy a) (auditBootTy b)
  | .sum ts => auditBootTys ts
  | .record fs => auditRecordSchema fs

/-- Audit an ordered list of types from left to right. -/
def auditBootTys : List BootTy →
    Except SCMIdentifierError Unit
  | [] => .ok ()
  | t :: ts => auditBoth (auditBootTy t) (auditBootTys ts)

/-- Audit an ordered record schema, preserving its first validation error. -/
def auditRecordSchema : List (String × BootTy) →
    Except SCMIdentifierError Unit
  | [] => .ok ()
  | (key, t) :: fs =>
      auditBoth (auditRecordKey key)
        (auditBoth (auditBootTy t) (auditRecordSchema fs))

end

/-! The public audits include their complete intrinsic type contract.  This is
    deliberate: record schemas may occur only in indices and need not survive
    as explicit target nodes. -/

/-- Audit a typing context from de Bruijn index 0 onward. -/
def auditCtx (G : Ctx) :
    Except SCMIdentifierError Unit :=
  auditBootTys G

/-- Audit a complete ordered program signature table. -/
def auditSigTable : SigTable →
    Except SCMIdentifierError Unit
  | [] => .ok ()
  | (params, result) :: rest =>
      auditBoth (auditCtx params)
        (auditBoth (auditBootTy result) (auditSigTable rest))

mutual

/-- Audit every semantic record key in an expression, including keys present
    only in its signature, context, result type, or nested subexpression
    indices. -/
def auditSCMExpr (e : SCMExpr S G t) :
    Except SCMIdentifierError Unit :=
  auditBoth (auditSigTable S)
    (auditBoth (auditCtx G)
      (auditBoth (auditBootTy t) (match e with
        | .litI _ | .litB _ | .litS _ | .var _ | .emptyList | .recNil |
            .noneE | .residueE _ | .litW _ => .ok ()
        | .wNot a => auditSCMExpr a
        | .neg a | .notE a | .strLen a | .strToInt a | .listSingleton a |
            .listLen a | .listFirst a | .fstE a | .sndE a | .someE a |
            .isSomeE a | .unwrapSome a | .okE a | .isResidueE a |
            .getResidue a | .getOk a | .packBytes a | .bytesLen a |
            .contentHash a => auditSCMExpr a
        | .let1 a b | .add a b | .sub a b | .mul a b | .divE a b |
            .modE a b | .lt a b | .gt a b | .eqE a b | .andE a b |
            .orE a b | .strSplit a b | .listAppend a b | .listDrop a b |
            .pairE a b | .bytesConcat a b | .wAdd a b | .wSub a b | .wMul a b |
            .wDiv a b | .wMod a b | .wLt a b | .wLe a b | .wAnd a b | .wOr a b |
            .wXor a b | .wShl a b | .wShr a b =>
            auditBoth (auditSCMExpr a) (auditSCMExpr b)
        | .ifE a b c | .strSubstring a b c | .bytesSlice a b c |
            .boundedFold a b c =>
            auditBoth (auditSCMExpr a)
              (auditBoth (auditSCMExpr b) (auditSCMExpr c))
        | .boundedFix stop step init bound =>
            auditBoth (auditSCMExpr stop)
              (auditBoth (auditSCMExpr step)
                (auditBoth (auditSCMExpr init) (auditSCMExpr bound)))
        | .inj _ a => auditSCMExpr a
        | .matchE a bs => auditBoth (auditSCMExpr a) (auditSCMBranches bs)
        | .recCons key a rest =>
            auditBoth (auditRecordKey key)
              (auditBoth (auditSCMExpr a) (auditSCMExpr rest))
        | .field (fs := fs) a i =>
            auditBoth (auditRecordKey (fs.get i).1) (auditSCMExpr a)
        | .call _ args => auditSCMArgs args)))

/-- Audit an argument vector and its complete intrinsic type contract. -/
def auditSCMArgs (args : SCMArgs S G ts) :
    Except SCMIdentifierError Unit :=
  auditBoth (auditSigTable S)
    (auditBoth (auditCtx G)
      (auditBoth (auditBootTys ts) (match args with
        | .nil => .ok ()
        | .cons a rest =>
            auditBoth (auditSCMExpr a) (auditSCMArgs rest))))

/-- Audit a branch vector and its complete intrinsic type contract. -/
def auditSCMBranches (branches : SCMBranches S G ts r) :
    Except SCMIdentifierError Unit :=
  auditBoth (auditSigTable S)
    (auditBoth (auditCtx G)
      (auditBoth (auditBootTys ts)
        (auditBoth (auditBootTy r) (match branches with
          | .nil => .ok ()
          | .cons b rest =>
              auditBoth (auditSCMExpr b) (auditSCMBranches rest)))))

end

private def auditSCMProgramBodies : SCMPrograms S T →
    Except SCMIdentifierError Unit
  | .nil => .ok ()
  | .cons body rest =>
      auditBoth (auditSCMExpr body) (auditSCMProgramBodies rest)

/-- Audit both complete signature indices before auditing any program body. -/
def auditSCMPrograms (programs : SCMPrograms S T) :
    Except SCMIdentifierError Unit :=
  auditBoth (auditSigTable S)
    (auditBoth (auditSigTable T) (auditSCMProgramBodies programs))

theorem auditRecordKey_valid : (auditRecordKey "field-name").isOk = true := by
  decide

theorem auditRecordKey_invalid : (auditRecordKey "bad key").isOk = false := by
  decide

/-- A field access cannot hide an invalid key in its indexed record schema. -/
theorem auditSCMExpr_field_invalid :
    (auditSCMExpr
      (@SCMExpr.field [] []
        [("bad key", .i64)]
        (.recCons "bad key" (.litI 0) .recNil)
        ⟨0, Nat.zero_lt_succ 0⟩)).isOk = false := by
  decide

/-! ## Independent target evaluator -/

/-- Target arithmetic helper. -/
def scmArith2 (oa ob : Option SCMVal) (law : Int → Int → Option Int) :
    Option SCMVal :=
  match oa, ob with
  | some (.int x), some (.int y) => (law x y).map .int
  | _, _ => none

/-! ## Revision 2: width-64 words -/

/-- The modulus of the width-64 word. -/
def w64Mod : Int := 18446744073709551616

/-- A width-64 value is an integer in `[0, 2^64)`. -/
def inW64 (x : Int) : Bool := decide (0 ≤ x) && decide (x < w64Mod)

/-- Target helper of the word operators: both operands in the word domain, else `none`. -/
def scmW2 (oa ob : Option SCMVal) (law : Int → Int → Int) : Option SCMVal :=
  match oa, ob with
  | some (.int x), some (.int y) => if inW64 x && inW64 y then some (.int (law x y)) else none
  | _, _ => none

/-- The Bool operators of the word domain. -/
def scmW2b (oa ob : Option SCMVal) (law : Int → Int → Bool) : Option SCMVal :=
  match oa, ob with
  | some (.int x), some (.int y) => if inW64 x && inW64 y then some (.bool (law x y)) else none
  | _, _ => none

/-- Lean's `UInt64` functions on the integer representatives (`Nat` mod `2^64`). -/
def wAddL (x y : Int) : Int := (x + y) % w64Mod
def wSubL (x y : Int) : Int := (x + w64Mod - y) % w64Mod
def wMulL (x y : Int) : Int := (x * y) % w64Mod
def wDivL (x y : Int) : Int := if y = 0 then 0 else x / y
def wModL (x y : Int) : Int := if y = 0 then x else x % y
def wAndL (x y : Int) : Int := ((x.toNat &&& y.toNat : Nat) : Int)
def wOrL  (x y : Int) : Int := ((x.toNat ||| y.toNat : Nat) : Int)
def wXorL (x y : Int) : Int := ((x.toNat ^^^ y.toNat : Nat) : Int)
def wShlL (x n : Int) : Int := (x * 2 ^ (n % 64).toNat) % w64Mod
def wShrL (x n : Int) : Int := x / 2 ^ (n % 64).toNat

/-- Target program lookup by ordered signature-table index. -/
def getSCMProgram : SCMPrograms S T → (i : Fin T.length) →
    SCMExpr S (T.get i).1 (T.get i).2
  | .cons body _, ⟨0, _⟩ => body
  | .cons _ rest, ⟨n+1, h⟩ =>
      getSCMProgram rest ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Every target expression has positive structural size. -/
theorem scmExprSizePos {S : SigTable} {G : Ctx} {t : BootTy}
    (e : SCMExpr S G t) : 0 < sizeOf e := by
  cases e
  case var i => rw [SCMExpr.var.sizeOf_spec]; omega
  case field a i => rw [SCMExpr.field.sizeOf_spec]; omega
  case call f args => rw [SCMExpr.call.sizeOf_spec]; omega
  case inj i a => rw [SCMExpr.inj.sizeOf_spec]; omega
  case matchE a bs => rw [SCMExpr.matchE.sizeOf_spec]; omega
  all_goals simp_arith

set_option maxHeartbeats 1600000 in
mutual

/-- Independent target evaluator.  Every node checks nonzero fuel; only
    `.call` passes predecessor fuel to another expression. -/
def evalSCM (progs : SCMPrograms S S) :
    (fuel : Nat) → SCMEnv → SCMExpr S G t → Option SCMVal
  | 0, _, _ => none
  | _+1, _, .litI n => (Semantics.lawSub n 0).map .int
  | _+1, _, .litB b => some (.bool b)
  | _+1, _, .litS s => some (.str s)
  | _+1, env, .var i => env.get? i.val
  | f+1, env, .let1 a b =>
      match evalSCM progs (f+1) env a with
      | some v => evalSCM progs (f+1) (v :: env) b
      | none => none
  | f+1, env, .ifE c a b =>
      match evalSCM progs (f+1) env c with
      | some (.bool true) => evalSCM progs (f+1) env a
      | some (.bool false) => evalSCM progs (f+1) env b
      | _ => none
  | f+1, env, .add a b =>
      scmArith2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b)
        Semantics.lawsA.addF
  | f+1, env, .sub a b =>
      scmArith2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b)
        Semantics.lawSub
  | f+1, env, .mul a b =>
      scmArith2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b)
        Semantics.lawMul
  | f+1, env, .neg a =>
      match evalSCM progs (f+1) env a with
      | some (.int x) => (Semantics.lawNeg x).map .int
      | _ => none
  | f+1, env, .divE a b =>
      scmArith2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b)
        Semantics.lawsA.divF
  | f+1, env, .modE a b =>
      scmArith2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b)
        Semantics.lawsA.modF
  | f+1, env, .lt a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some (.int x), some (.int y) => some (.bool (decide (x < y)))
      | _, _ => none
  | f+1, env, .gt a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some (.int x), some (.int y) => some (.bool (decide (y < x)))
      | _, _ => none
  | f+1, env, .eqE a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some va, some vb => some (.bool (scmValEq va vb))
      | _, _ => none
  | f+1, env, .andE a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some (.bool x), some (.bool y) => some (.bool (x && y))
      | _, _ => none
  | f+1, env, .orE a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _ => none
  | f+1, env, .notE a =>
      match evalSCM progs (f+1) env a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
  | f+1, env, .strLen a =>
      match evalSCM progs (f+1) env a with
      | some (.str s) => some (.int (s.length : Int))
      | _ => none
  | f+1, env, .strSplit a sep =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env sep with
      | some (.str s), some (.str p) =>
          if p.isEmpty then none else some (.list ((s.splitOn p).map .str))
      | _, _ => none
  | f+1, env, .strSubstring a lo hi =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env lo,
          evalSCM progs (f+1) env hi with
      | some (.str s), some (.int x), some (.int y) =>
          some (.str (Semantics.strSub s x y))
      | _, _, _ => none
  | f+1, env, .strToInt a =>
      match evalSCM progs (f+1) env a with
      | some (.str s) => (Semantics.strToIntI s).map .int
      | _ => none
  | _+1, _, .emptyList => some (.list [])
  | f+1, env, .listSingleton a =>
      (evalSCM progs (f+1) env a).map (fun v => .list [v])
  | f+1, env, .listLen a =>
      match evalSCM progs (f+1) env a with
      | some (.list vs) => some (.int (vs.length : Int))
      | _ => none
  | f+1, env, .listFirst a =>
      match evalSCM progs (f+1) env a with
      | some (.list []) => some .noneV
      | some (.list (v :: _)) => some (.someV v)
      | _ => none
  | f+1, env, .listAppend a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some (.list xs), some (.list ys) => some (.list (xs ++ ys))
      | _, _ => none
  | f+1, env, .listDrop n a =>
      match evalSCM progs (f+1) env n, evalSCM progs (f+1) env a with
      | some (.int k), some (.list vs) => some (.list (vs.drop k.toNat))
      | _, _ => none
  | f+1, env, .pairE a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some x, some y => some (.list [x, y])
      | _, _ => none
  | f+1, env, .fstE a =>
      match evalSCM progs (f+1) env a with
      | some (.list [x, _]) => some x
      | _ => none
  | f+1, env, .sndE a =>
      match evalSCM progs (f+1) env a with
      | some (.list [_, y]) => some y
      | _ => none
  | f+1, env, .inj i a =>
      (evalSCM progs (f+1) env a).map (fun v =>
        .record [("tag", .int (i.val : Int)), ("val", v)])
  | f+1, env, .matchE a branches =>
      match evalSCM progs (f+1) env a with
      | some (.record [("tag", .int i), ("val", v)]) =>
          if i < 0 then none else evalSCMMatch progs (f+1) env i.toNat v branches
      | _ => none
  | _+1, _, .recNil => some (.record [])
  | f+1, env, .recCons name a rest =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env rest with
      | some v, some (.record fs) => some (.record ((name, v) :: fs))
      | _, _ => none
  | f+1, env, .field a i =>
      match evalSCM progs (f+1) env a with
      | some (.record fs) =>
          match fs.get? i.val with
          | some (_, v) => some v
          | none => none
      | _ => none
  | f+1, env, .someE a => (evalSCM progs (f+1) env a).map .someV
  | _+1, _, .noneE => some .noneV
  | f+1, env, .isSomeE a =>
      match evalSCM progs (f+1) env a with
      | some (.someV _) => some (.bool true)
      | some .noneV => some (.bool false)
      | _ => none
  | f+1, env, .unwrapSome a =>
      match evalSCM progs (f+1) env a with
      | some (.someV v) => some v
      | _ => none
  | f+1, env, .okE a => (evalSCM progs (f+1) env a).map .ok
  | _+1, _, .residueE code => some (.res code)
  | f+1, env, .isResidueE a =>
      match evalSCM progs (f+1) env a with
      | some (.res _) => some (.bool true)
      | some (.ok _) => some (.bool false)
      | _ => none
  | f+1, env, .getResidue a =>
      match evalSCM progs (f+1) env a with
      | some (.res code) => some (.int code)
      | _ => none
  | f+1, env, .getOk a =>
      match evalSCM progs (f+1) env a with
      | some (.ok v) => some v
      | _ => none
  | f+1, env, .packBytes a =>
      match evalSCM progs (f+1) env a with
      | some v => (restoreBytes v).map bytesToSCM
      | none => none
  | f+1, env, .bytesLen a =>
      match evalSCM progs (f+1) env a with
      | some v => bytesLenEval v
      | none => none
  | f+1, env, .bytesConcat a b =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env b with
      | some x, some y =>
          match restoreBytes x, restoreBytes y with
          | some xs, some ys => some (bytesToSCM (xs ++ ys))
          | _, _ => none
      | _, _ => none
  | f+1, env, .bytesSlice a lo hi =>
      match evalSCM progs (f+1) env a, evalSCM progs (f+1) env lo,
          evalSCM progs (f+1) env hi with
      | some v, some (.int x), some (.int y) =>
          match restoreBytes v with
          | some raw =>
              if x < 0 || y < x || y > (raw.length : Int) then none
              else some (bytesToSCM ((raw.drop x.toNat).take (y - x).toNat))
          | none => none
      | _, _, _ => none
  | f+1, env, .contentHash a =>
      match evalSCM progs (f+1) env a with
      | some v => contentHashValue v
      | none => none
  | f+1, env, .boundedFold xs init body =>
      match evalSCM progs (f+1) env xs, evalSCM progs (f+1) env init with
      | some (.list vs), some acc0 => evalSCMFold progs (f+1) env body vs acc0
      | _, _ => none
  | f+1, env, .boundedFix stop step init bound =>
      match evalSCM progs (f+1) env init, evalSCM progs (f+1) env bound with
      | some state0, some (.int b) =>
          if b < 0 then none else evalSCMFix progs (f+1) env stop step state0 0 b.toNat
      | _, _ => none
  | f+1, env, .call callee args =>
      match evalSCMArgs progs (f+1) env args with
      | some values => evalSCM progs f values (getSCMProgram progs callee)
      | none => none
  | _+1, _, .litW n => some (.int (n.toNat : Int))
  | f+1, env, .wAdd a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wAddL
  | f+1, env, .wSub a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wSubL
  | f+1, env, .wMul a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wMulL
  | f+1, env, .wDiv a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wDivL
  | f+1, env, .wMod a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wModL
  | f+1, env, .wLt a b =>
      scmW2b (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) (fun x y => decide (x < y))
  | f+1, env, .wLe a b =>
      scmW2b (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) (fun x y => decide (x ≤ y))
  | f+1, env, .wAnd a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wAndL
  | f+1, env, .wOr a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wOrL
  | f+1, env, .wXor a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wXorL
  | f+1, env, .wNot a =>
      match evalSCM progs (f+1) env a with
      | some (.int x) => if inW64 x then some (.int (w64Mod - 1 - x)) else none
      | _ => none
  | f+1, env, .wShl a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wShlL
  | f+1, env, .wShr a b =>
      scmW2 (evalSCM progs (f+1) env a) (evalSCM progs (f+1) env b) wShrL
termination_by fuel _ e => (fuel, sizeOf e, 0, 0)
decreasing_by all_goals first
  | decreasing_tactic
  | (simp only [SCMExpr.field.sizeOf_spec, SCMExpr.boundedFix.sizeOf_spec,
       SCMExpr.boundedFold.sizeOf_spec, SCMExpr.matchE.sizeOf_spec,
       SCMExpr.call.sizeOf_spec]
     first
       | decreasing_tactic
       | (apply Prod.Lex.right
          apply Prod.Lex.left
          have h1 := scmExprSizePos init
          omega))

/-- Left-to-right target argument evaluation at unchanged fuel. -/
def evalSCMArgs (progs : SCMPrograms S S) :
    (fuel : Nat) → SCMEnv → SCMArgs S G ts → Option (List SCMVal)
  | 0, _, _ => none
  | _+1, _, .nil => some []
  | f+1, env, .cons a rest =>
      match evalSCM progs (f+1) env a, evalSCMArgs progs (f+1) env rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none
termination_by fuel _ args => (fuel, sizeOf args, 0, 0)

/-- Target sum branch selection; binds payload at index 0. -/
def evalSCMMatch (progs : SCMPrograms S S) :
    (fuel : Nat) → SCMEnv → Nat → SCMVal → SCMBranches S G ts r → Option SCMVal
  | 0, _, _, _, _ => none
  | _+1, _, _, _, .nil => none
  | f+1, env, 0, v, .cons branch _ => evalSCM progs (f+1) (v :: env) branch
  | f+1, env, i+1, v, .cons _ rest => evalSCMMatch progs (f+1) env i v rest
termination_by fuel _ _ _ branches => (fuel, sizeOf branches, 0, 0)

/-- Target fold iteration; every body and iteration keeps the same fuel. -/
def evalSCMFold (progs : SCMPrograms S S) :
    (fuel : Nat) → SCMEnv → SCMExpr S (a :: b :: G) b →
    List SCMVal → SCMVal → Option SCMVal
  | 0, _, _, _, _ => none
  | _+1, _, _, [], acc => some acc
  | f+1, env, body, v :: vs, acc =>
      match evalSCM progs (f+1) (v :: acc :: env) body with
      | some acc' => evalSCMFold progs (f+1) env body vs acc'
      | none => none
termination_by fuel _ body vs _ => (fuel, sizeOf body, 1, vs.length)

/-- Target fix iteration; every predicate, step, and iteration keeps the same
    fuel.  Result keys retain their semantic source order. -/
def evalSCMFix (progs : SCMPrograms S S) :
    (fuel : Nat) → SCMEnv → SCMExpr S (s :: G) .bool → SCMExpr S (s :: G) s →
    SCMVal → Nat → Nat → Option SCMVal
  | 0, _, _, _, _, _, _ => none
  | f+1, env, stop, step, state, steps, bound =>
      match evalSCM progs (f+1) (state :: env) stop with
      | some (.bool true) =>
          some (.record [("converged", .bool true), ("state", state),
            ("steps", .int steps)])
      | some (.bool false) =>
          match bound with
          | 0 => some (.record [("converged", .bool false), ("state", state),
              ("steps", .int steps)])
          | b+1 =>
              match evalSCM progs (f+1) (state :: env) step with
              | some state' => evalSCMFix progs (f+1) env stop step state' (steps+1) b
              | none => none
      | _ => none
termination_by fuel _ stop step _ _ bound =>
  (fuel, sizeOf stop + sizeOf step + 1, 1, bound)

end

/-! ## Direct target teeth -/

set_option maxHeartbeats 4000000 in
/-- Floor modulo separation point on the independent target evaluator. -/
theorem pin_scm_mod_7_m3 :
    evalSCM (.nil : SCMPrograms [] []) 1 []
      (.modE (.litI 7) (.litI (-3)) : SCMExpr [] [] .i64) =
      some (.int (-2)) := by
  have hmod : Semantics.lawsA.modF 7 (-3) = some (-2) := by
    decide
  simp [evalSCM.eq_13, evalSCM.eq_2, scmArith2, Semantics.lawSub,
    EvalBootSeparators.inI64Range, EvalBootSeparators.i64Min,
    EvalBootSeparators.i64Max, hmod]

def scmSig42 : SigTable := [([], .i64)]
def scmProg42 : SCMPrograms scmSig42 scmSig42 := .cons (.litI 42) .nil

set_option maxHeartbeats 4000000 in
theorem pin_scm_call_fuel2 :
    scmOutEq
      (evalSCM scmProg42 2 []
        (.call ⟨0, by decide⟩ .nil : SCMExpr scmSig42 [] .i64))
      (.int 42) = true := by
  simp [evalSCM.eq_54, evalSCMArgs.eq_2, getSCMProgram, evalSCM.eq_2,
    Semantics.lawSub, EvalBootSeparators.inI64Range,
    EvalBootSeparators.i64Min, EvalBootSeparators.i64Max, scmOutEq, scmValEq]

set_option maxHeartbeats 4000000 in
theorem pin_scm_call_fuel1 :
    (evalSCM scmProg42 1 []
      (.call ⟨0, by decide⟩ .nil : SCMExpr scmSig42 [] .i64)).isNone = true := by
  simp only [evalSCM.eq_54, evalSCMArgs.eq_2, getSCMProgram, evalSCM.eq_1,
    Option.isNone]

set_option maxHeartbeats 4000000 in
theorem pin_scm_fold_fuel1 :
    scmOutEq
      (evalSCM (.nil : SCMPrograms [] []) 1 []
        (.boundedFold
          (.listAppend (.listSingleton (.litI 1)) (.listSingleton (.litI 2)))
          (.litI 0)
          (.add (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)) :
          SCMExpr [] [] .i64))
      (.int 3) = true := by
  simp [evalSCM.eq_52, evalSCM.eq_28, evalSCM.eq_25, evalSCM.eq_2,
    evalSCMFold.eq_3, evalSCMFold.eq_2, evalSCM.eq_8, evalSCM.eq_5,
    scmArith2, Semantics.lawSub, Semantics.lawsA, EvalBootSeparators.lawAdd,
    EvalBootSeparators.inI64Range, EvalBootSeparators.i64Min,
    EvalBootSeparators.i64Max, scmOutEq, scmValEq]

set_option maxHeartbeats 4000000 in
theorem pin_scm_fix_fuel1 :
    scmOutEq
      (evalSCM (.nil : SCMPrograms [] []) 1 []
        (.boundedFix
          (.gt (.var ⟨0, by decide⟩) (.litI 2))
          (.add (.var ⟨0, by decide⟩) (.litI 1))
          (.litI 0) (.litI 10) :
          SCMExpr [] [] (fixResultTy .i64)))
      (.record [("converged", .bool true), ("state", .int 3),
        ("steps", .int 3)]) = true := by
  let stop : SCMExpr [] [.i64] .bool :=
    .gt (.var ⟨0, by decide⟩) (.litI 2)
  let step : SCMExpr [] [.i64] .i64 :=
    .add (.var ⟨0, by decide⟩) (.litI 1)
  have hinit : evalSCM (.nil : SCMPrograms [] []) 1 []
      (.litI 0 : SCMExpr [] [] .i64) = some (.int 0) := by
    simp [evalSCM.eq_2, Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hbound : evalSCM (.nil : SCMPrograms [] []) 1 []
      (.litI 10 : SCMExpr [] [] .i64) = some (.int 10) := by
    simp [evalSCM.eq_2, Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hstop0 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 0] stop =
      some (.bool false) := by
    simp [stop, evalSCM.eq_15, evalSCM.eq_5, evalSCM.eq_2,
      Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hstop1 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 1] stop =
      some (.bool false) := by
    simp [stop, evalSCM.eq_15, evalSCM.eq_5, evalSCM.eq_2,
      Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hstop2 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 2] stop =
      some (.bool false) := by
    simp [stop, evalSCM.eq_15, evalSCM.eq_5, evalSCM.eq_2,
      Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hstop3 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 3] stop =
      some (.bool true) := by
    simp [stop, evalSCM.eq_15, evalSCM.eq_5, evalSCM.eq_2,
      Semantics.lawSub, EvalBootSeparators.inI64Range,
      EvalBootSeparators.i64Min, EvalBootSeparators.i64Max]
  have hstep0 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 0] step =
      some (.int 1) := by
    simp [step, evalSCM.eq_8, evalSCM.eq_5, evalSCM.eq_2, scmArith2,
      Semantics.lawSub, Semantics.lawsA, EvalBootSeparators.lawAdd,
      EvalBootSeparators.inI64Range, EvalBootSeparators.i64Min,
      EvalBootSeparators.i64Max]
  have hstep1 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 1] step =
      some (.int 2) := by
    simp [step, evalSCM.eq_8, evalSCM.eq_5, evalSCM.eq_2, scmArith2,
      Semantics.lawSub, Semantics.lawsA, EvalBootSeparators.lawAdd,
      EvalBootSeparators.inI64Range, EvalBootSeparators.i64Min,
      EvalBootSeparators.i64Max]
  have hstep2 : evalSCM (.nil : SCMPrograms [] []) 1 [.int 2] step =
      some (.int 3) := by
    simp [step, evalSCM.eq_8, evalSCM.eq_5, evalSCM.eq_2, scmArith2,
      Semantics.lawSub, Semantics.lawsA, EvalBootSeparators.lawAdd,
      EvalBootSeparators.inI64Range, EvalBootSeparators.i64Min,
      EvalBootSeparators.i64Max]
  change scmOutEq
      (evalSCM (.nil : SCMPrograms [] []) 1 []
        (.boundedFix stop step (.litI 0) (.litI 10))) _ = true
  rw [evalSCM.eq_53, hinit, hbound]
  simp only [Int.reduceLT, Bool.false_eq_true, ↓reduceIte]
  change scmOutEq
      (evalSCMFix (.nil : SCMPrograms [] []) 1 [] stop step (.int 0) 0 10)
      _ = true
  rw [evalSCMFix.eq_3, hstop0, hstep0]
  change scmOutEq
      (evalSCMFix (.nil : SCMPrograms [] []) 1 [] stop step (.int 1) 1 9)
      _ = true
  rw [evalSCMFix.eq_3, hstop1, hstep1]
  change scmOutEq
      (evalSCMFix (.nil : SCMPrograms [] []) 1 [] stop step (.int 2) 2 8)
      _ = true
  rw [evalSCMFix.eq_3, hstop2, hstep2]
  change scmOutEq
      (evalSCMFix (.nil : SCMPrograms [] []) 1 [] stop step (.int 3) 3 7)
      _ = true
  rw [evalSCMFix.eq_3, hstop3]
  decide

end Residua.Bootstrap.R2.SCM
