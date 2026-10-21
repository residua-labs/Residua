/-
RCIC 06 (SCM core semantics) — K2 statement layer, part 1: §3 core types,
§4 typed values, §5 outcome namespace, §6 residue catalog and rows.

Two faces, kept apart (00 §16 M-001 / M-002 / M-002a):

* the INTRINSIC face quotes 06: `CoreTy` (§3), `CoreVal : CoreTy → Type`
  (§4, type-indexed constructors), the catalog/row shapes (§6);
* the RAW face `Val` is the carrier record encoding of a value
  (`apps/rcic-scm-prim/APP.md` Encoding: `{k 0 n}`, `{k 1 b}`, `{k 2 s}`,
  `{k 3 bs}`, `{k 4 xs}`, `{k 5 a b}`, `{k 6 i v}`, `{k 7 fs}`).

`toCore` elaborates a raw value at a type into an intrinsic value, `erase`
goes back. Every carrier entry point modelled in K2 passes its arguments
through `toCore`, so the intrinsic definitions are reachable from the pins
(M-002a). `valOfTy` is the carrier's `rcic.scm_val_of_ty`: it holds exactly
when `toCore` succeeds.

TRANSCRIPTION TABLE (06 rule → Lean):
  §3 CoreTy := i64 | bool | str | bytes | list | pair | sum | record
        → `CoreTy` (8 ctors, same order)
  §3 "i64 is the mathematical signed 64-bit range"  → `inI64` carried by
        `CoreVal.i64V`'s proof field
  §3 "str is a finite sequence of Unicode scalar values" → `String`
        (Lean `Char` is a Unicode scalar value, so every value is valid by
        construction)
  §3 "… with canonical UTF-8 wire encoding" and §4 "strings reject invalid
        or noncanonical UTF-8" → NOT TRANSCRIBED: the K2 wire model
        (`ScmWire`) is over `String`, not raw bytes, so invalid UTF-8 is
        unrepresentable there and the byte-level rejection is not modelled;
        it belongs to the byte codec of the bound canonical wire objects
        (#6029 K3b, M-002b)
  §3 "bytes is a finite byte sequence"               → `List UInt8`
  §3 "record field order is schema order and field keys are unique"
        → `CoreTy.record (List (String × CoreTy))` (order = list order);
        uniqueness is the typing check `keysUnique` (ScmExpr)
  §3 Unit / Option / Result are aliases            → `unitTy` (empty record)
  §4 CoreVal : CoreTy → Type, ctors i64V boolV strV bytesV listV pairV injV
        recordV → `CoreVal` (8 ctors, same names); `CoreList` / `CoreVals`
        are the list / field-tuple spines the nested ctors need
  §5 outcome namespace (six classes):
        ReportedResidueValue (an ordinary sum/data value) → an ordinary
          `CoreVal`, returned through `Final.returned` (ScmMachine);
          "a reported-residue value never triggers handlers" →
          `Theorems.returned_passes_handler` (a returned value pops a
          `handleF` frame without entering it)
        SCMRaisedResidue (exact ResidueRef + typed payload) → `RaisedRef`,
          `LawResult.raised`, `Control.raiseC` / `Final.raised` (payload
          typed by the catalog proof)
        IntegrityResidue → `StepResult.integrity` / `RunI.integrity`, and the
          `code` channel of every raw entry point
        Suspension → `RunI.suspended`
        WasmTrap (target-machine trap) → NOT TRANSCRIBED: no target machine
          in SCM-Core-0 (08's object)
        OpenResidue (institutional obligation) → NOT TRANSCRIBED: not an
          outcome of the SCM machine
        "Only the `raise` expression produces an SCMRaisedResidue" →
          read by E-06RaiseSources (00 §19.7): the sentence separates values
          from raises (no value, a reported-residue value included, becomes
          a raised residue); raised residues come from the `raise`
          expression and from the SCM-raise outcomes of §11's primitive laws
          and §12's bounded fix. The model follows that reading: primitive
          and loop residues are raised controls, as the carriers decide
  §6 ResidueCatalog entries {residue_ref, payload_type} → `CatalogEntry`
  §6 ResidueRow := canonical sorted unique list ResidueRef → `ResidueRow`
-/

namespace Rcic.Scm

/-! ## §3 Core types -/

inductive CoreTy where
  | i64
  | bool
  | str
  | bytes
  | list (t : CoreTy)
  | pair (a b : CoreTy)
  | sum (ts : List CoreTy)
  | record (fs : List (String × CoreTy))
  deriving Inhabited, Repr

/-- 06 §3: `Unit` is the empty record. -/
def unitTy : CoreTy := .record []

mutual
/-- Structural type equality (the carrier's `rcic.scm_ty_eq`). -/
def CoreTy.beq : CoreTy → CoreTy → Bool
  | .i64, .i64 => true
  | .bool, .bool => true
  | .str, .str => true
  | .bytes, .bytes => true
  | .list a, .list b => CoreTy.beq a b
  | .pair a b, .pair c d => CoreTy.beq a c && CoreTy.beq b d
  | .sum xs, .sum ys => CoreTy.beqList xs ys
  | .record xs, .record ys => CoreTy.beqFields xs ys
  | _, _ => false
def CoreTy.beqList : List CoreTy → List CoreTy → Bool
  | [], [] => true
  | x :: xs, y :: ys => CoreTy.beq x y && CoreTy.beqList xs ys
  | _, _ => false
def CoreTy.beqFields : List (String × CoreTy) → List (String × CoreTy) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => k == l && CoreTy.beq x y && CoreTy.beqFields xs ys
  | _, _ => false
end

mutual
theorem CoreTy.eq_of_beq : (a b : CoreTy) → CoreTy.beq a b = true → a = b
  | .i64, .i64, _ => rfl
  | .bool, .bool, _ => rfl
  | .str, .str, _ => rfl
  | .bytes, .bytes, _ => rfl
  | .list a, .list b, h => congrArg CoreTy.list (CoreTy.eq_of_beq a b h)
  | .pair a b, .pair c d, h =>
      have hh := (Bool.and_eq_true _ _).mp h
      (CoreTy.eq_of_beq a c hh.1) ▸ (CoreTy.eq_of_beq b d hh.2) ▸ rfl
  | .sum xs, .sum ys, h => congrArg CoreTy.sum (CoreTy.eq_of_beqList xs ys h)
  | .record xs, .record ys, h => congrArg CoreTy.record (CoreTy.eq_of_beqFields xs ys h)
  | .i64, .bool, h | .i64, .str, h | .i64, .bytes, h | .i64, .list _, h | .i64, .pair _ _, h | .i64, .sum _, h | .i64, .record _, h => nomatch h
  | .bool, .i64, h | .bool, .str, h | .bool, .bytes, h | .bool, .list _, h | .bool, .pair _ _, h | .bool, .sum _, h | .bool, .record _, h => nomatch h
  | .str, .i64, h | .str, .bool, h | .str, .bytes, h | .str, .list _, h | .str, .pair _ _, h | .str, .sum _, h | .str, .record _, h => nomatch h
  | .bytes, .i64, h | .bytes, .bool, h | .bytes, .str, h | .bytes, .list _, h | .bytes, .pair _ _, h | .bytes, .sum _, h | .bytes, .record _, h => nomatch h
  | .list _, .i64, h | .list _, .bool, h | .list _, .str, h | .list _, .bytes, h | .list _, .pair _ _, h | .list _, .sum _, h | .list _, .record _, h => nomatch h
  | .pair _ _, .i64, h | .pair _ _, .bool, h | .pair _ _, .str, h | .pair _ _, .bytes, h | .pair _ _, .list _, h | .pair _ _, .sum _, h | .pair _ _, .record _, h => nomatch h
  | .sum _, .i64, h | .sum _, .bool, h | .sum _, .str, h | .sum _, .bytes, h | .sum _, .list _, h | .sum _, .pair _ _, h | .sum _, .record _, h => nomatch h
  | .record _, .i64, h | .record _, .bool, h | .record _, .str, h | .record _, .bytes, h | .record _, .list _, h | .record _, .pair _ _, h | .record _, .sum _, h => nomatch h
theorem CoreTy.eq_of_beqList : (xs ys : List CoreTy) → CoreTy.beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h =>
      have hh := (Bool.and_eq_true _ _).mp h
      (CoreTy.eq_of_beq x y hh.1) ▸ (CoreTy.eq_of_beqList xs ys hh.2) ▸ rfl
  | [], _ :: _, h | _ :: _, [], h => nomatch h
theorem CoreTy.eq_of_beqFields : (xs ys : List (String × CoreTy)) → CoreTy.beqFields xs ys = true → xs = ys
  | [], [], _ => rfl
  | (_, x) :: xs, (_, y) :: ys, h =>
      have hh := (Bool.and_eq_true _ _).mp h
      have h1 := (Bool.and_eq_true _ _).mp hh.1
      (LawfulBEq.eq_of_beq h1.1) ▸ (CoreTy.eq_of_beq x y h1.2) ▸ (CoreTy.eq_of_beqFields xs ys hh.2) ▸ rfl
  | [], _ :: _, h | _ :: _, [], h => nomatch h
end

mutual
theorem CoreTy.beq_refl : (a : CoreTy) → CoreTy.beq a a = true
  | .i64 => rfl
  | .bool => rfl
  | .str => rfl
  | .bytes => rfl
  | .list a => CoreTy.beq_refl a
  | .pair a b => (Bool.and_eq_true _ _).mpr ⟨CoreTy.beq_refl a, CoreTy.beq_refl b⟩
  | .sum xs => CoreTy.beqList_refl xs
  | .record xs => CoreTy.beqFields_refl xs
theorem CoreTy.beqList_refl : (xs : List CoreTy) → CoreTy.beqList xs xs = true
  | [] => rfl
  | x :: xs => (Bool.and_eq_true _ _).mpr ⟨CoreTy.beq_refl x, CoreTy.beqList_refl xs⟩
theorem CoreTy.beqFields_refl : (xs : List (String × CoreTy)) → CoreTy.beqFields xs xs = true
  | [] => rfl
  | (k, x) :: xs => (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨beq_self_eq_true k, CoreTy.beq_refl x⟩, CoreTy.beqFields_refl xs⟩
end

instance : DecidableEq CoreTy := fun a b =>
  if h : CoreTy.beq a b = true then isTrue (CoreTy.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ CoreTy.beq_refl a))

instance : BEq CoreTy := ⟨CoreTy.beq⟩

/-- 06 §3: `i64` is the mathematical signed 64-bit range. -/
def i64Min : Int := -9223372036854775808
def i64Max : Int := 9223372036854775807
def inI64 (n : Int) : Prop := i64Min ≤ n ∧ n ≤ i64Max
instance (n : Int) : Decidable (inI64 n) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## §4 Typed values (intrinsic) -/

mutual
inductive CoreVal : CoreTy → Type where
  | i64V (n : Int) (h : inI64 n) : CoreVal .i64
  | boolV (b : Bool) : CoreVal .bool
  | strV (s : String) : CoreVal .str
  | bytesV (bs : List UInt8) : CoreVal .bytes
  | listV {t : CoreTy} (xs : CoreList t) : CoreVal (.list t)
  | pairV {a b : CoreTy} (x : CoreVal a) (y : CoreVal b) : CoreVal (.pair a b)
  | injV {ts : List CoreTy} (i : Nat) (t : CoreTy) (h : ts.get? i = some t) (x : CoreVal t) :
      CoreVal (.sum ts)
  | recordV {fs : List (String × CoreTy)} (xs : CoreVals (fs.map Prod.snd)) : CoreVal (.record fs)
inductive CoreList : CoreTy → Type where
  | nil {t : CoreTy} : CoreList t
  | cons {t : CoreTy} (x : CoreVal t) (xs : CoreList t) : CoreList t
inductive CoreVals : List CoreTy → Type where
  | nil : CoreVals []
  | cons {t : CoreTy} {ts : List CoreTy} (x : CoreVal t) (xs : CoreVals ts) : CoreVals (t :: ts)
end

/-- The unit value (06 §3 alias): the empty record. -/
def unitV : CoreVal unitTy := .recordV .nil

/-! ## Raw values: the carrier record encoding -/

inductive Val where
  | i (n : Int)
  | b (b : Int)
  | s (s : String)
  | y (bs : List Int)
  | l (xs : List Val)
  | p (a b : Val)
  | j (i : Int) (v : Val)
  | r (fs : List Val)
  deriving Inhabited, Repr

mutual
def Val.beq : Val → Val → Bool
  | .i u, .i w => u == w
  | .b u, .b w => u == w
  | .s u, .s w => u == w
  | .y u, .y w => u == w
  | .l xs, .l ys => Val.beqList xs ys
  | .p x1 x2, .p y1 y2 => Val.beq x1 y1 && Val.beq x2 y2
  | .j m v, .j n w => m == n && Val.beq v w
  | .r xs, .r ys => Val.beqList xs ys
  | _, _ => false
def Val.beqList : List Val → List Val → Bool
  | [], [] => true
  | v :: vs, w :: ws => Val.beq v w && Val.beqList vs ws
  | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

/-- The raw unit value `{k 7 fs []}`. -/
def unitRaw : Val := .r []

/-! ## Elaboration raw → intrinsic, and erasure -/

mutual
def toCore : (t : CoreTy) → Val → Option (CoreVal t)
  | .i64, .i n => if h : inI64 n then some (.i64V n h) else none
  | .bool, .b b => if b = 0 then some (.boolV false) else if b = 1 then some (.boolV true) else none
  | .str, .s s => some (.strV s)
  | .bytes, .y bs => (toBytes bs).map CoreVal.bytesV
  | .list t, .l xs => (toCoreList t xs).map CoreVal.listV
  | .pair a b, .p x y =>
      match toCore a x, toCore b y with
      | some x', some y' => some (.pairV x' y')
      | _, _ => none
  | .sum ts, .j i v =>
      if i < 0 then none else
      match h : ts.get? i.toNat with
      | some t => (toCore t v).map (CoreVal.injV i.toNat t h)
      | none => none
  | .record fs, .r xs => (toCoreVals (fs.map Prod.snd) xs).map CoreVal.recordV
  | _, _ => none
def toCoreList (t : CoreTy) : List Val → Option (CoreList t)
  | [] => some .nil
  | x :: xs =>
      match toCore t x, toCoreList t xs with
      | some x', some xs' => some (.cons x' xs')
      | _, _ => none
def toCoreVals : (ts : List CoreTy) → List Val → Option (CoreVals ts)
  | [], [] => some .nil
  | t :: ts, x :: xs =>
      match toCore t x, toCoreVals ts xs with
      | some x', some xs' => some (.cons x' xs')
      | _, _ => none
  | _, _ => none
def toBytes : List Int → Option (List UInt8)
  | [] => some []
  | b :: bs =>
      if 0 ≤ b ∧ b ≤ 255 then (toBytes bs).map (fun r => (UInt8.ofNat b.toNat) :: r) else none
end

mutual
def CoreVal.erase : {t : CoreTy} → CoreVal t → Val
  | _, .i64V n _ => .i n
  | _, .boolV b => .b (if b then 1 else 0)
  | _, .strV s => .s s
  | _, .bytesV bs => .y (bs.map (fun x => (x.toNat : Int)))
  | _, .listV xs => .l xs.erase
  | _, .pairV x y => .p x.erase y.erase
  | _, .injV i _ _ x => .j i x.erase
  | _, .recordV xs => .r xs.erase
def CoreList.erase : {t : CoreTy} → CoreList t → List Val
  | _, .nil => []
  | _, .cons x xs => x.erase :: xs.erase
def CoreVals.erase : {ts : List CoreTy} → CoreVals ts → List Val
  | _, .nil => []
  | _, .cons x xs => x.erase :: xs.erase
end

/-- The carrier's `rcic.scm_val_of_ty v t`: `v` elaborates at `t`. -/
def valOfTy (v : Val) (t : CoreTy) : Bool := (toCore t v).isSome

/-- The carrier's `rcic.scm_vals_of_tys vs ts`. -/
def valsOfTys (vs : List Val) (ts : List CoreTy) : Bool := (toCoreVals ts vs).isSome

/-! ## §5 Outcomes of a law, §6 catalog and rows -/

/-- A residue ref (06 §6: `ResidueRef`); compared as a complete ref. -/
abbrev RaisedRef := String

/-- A law either returns a value of the result type or SCM-raises a residue
    (06 §5: an SCM-raised residue is a control outcome, not a value). The
    primitive residues of 06 §11 carry the unit payload. -/
inductive LawResult (t : CoreTy) where
  | returned (v : CoreVal t)
  | raised (r : RaisedRef)

/-- 06 §6 catalog entry `{residue_ref, payload_type}`. -/
structure CatalogEntry where
  ref : RaisedRef
  pt : CoreTy

/-- 06 §6: `ResidueRow := canonical sorted unique list ResidueRef`. -/
abbrev ResidueRow := List RaisedRef

/-- Canonical sorted unique: strictly ascending. -/
def strictlyAscending : List String → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && strictlyAscending (b :: rest)

/-- 06 §6: "Each residue ref has exactly one payload type" — the catalog is
    strictly ascending by ref, hence each ref occurs once. -/
def catalogCanonical (c : List CatalogEntry) : Bool := strictlyAscending (c.map CatalogEntry.ref)

/-- The payload type of a ref in a catalog. -/
def catalogPt (c : List CatalogEntry) (r : RaisedRef) : Option CoreTy :=
  (c.find? (fun e => e.ref == r)).map CatalogEntry.pt

/-! ## Instance witnesses (M-005) -/

example : CoreVal .i64 := .i64V 42 ⟨by decide, by decide⟩
example : CoreVal (.sum [.i64, .bool]) := .injV 1 .bool rfl (.boolV true)
example : CoreVal (.record [("a", .i64), ("b", .bool)]) :=
  .recordV (.cons (.i64V 1 ⟨by decide, by decide⟩) (.cons (.boolV false) .nil))

/-- M-005: the ∀-statements `CoreTy.eq_of_beq` / `CoreTy.beq_refl` instantiated. -/
example : CoreTy.sum [.i64, .record [("a", .bool)]] = .sum [.i64, .record [("a", .bool)]] :=
  CoreTy.eq_of_beq _ _ (CoreTy.beq_refl _)
example : CoreTy.beq (.list .str) (.list .str) = true := CoreTy.beq_refl _

#guard valOfTy (.y [0, 255]) .bytes
#guard !valOfTy (.y [300]) .bytes
#guard valOfTy (.j 1 (.b 1)) (.sum [.i64, .bool])
#guard !valOfTy (.j 2 (.b 1)) (.sum [.i64, .bool])
#guard ((toCore (.record [("a", .i64)]) (.r [.i 7])).map CoreVal.erase) == some (.r [.i 7])
#guard catalogCanonical [⟨"a", .i64⟩, ⟨"b", unitTy⟩]
#guard !catalogCanonical [⟨"b", .i64⟩, ⟨"a", unitTy⟩]

end Rcic.Scm
