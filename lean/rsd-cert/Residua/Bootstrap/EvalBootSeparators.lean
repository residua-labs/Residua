-- Bootstrap 1a RED (R-13). Adversary-authored BEFORE IR.lean and Semantics.lean.
-- Does not implement evalBoot. Freezes the five ADR separator points
-- (WP0.5 census, choice_on_mod = A):
--   law*     = what evalBoot MUST return
--   mutant*  = trunc-mod, wrap-add, trunc-div, i64-compare
--              (evalBoot' 1a MUST exhibit; MUST diverge from law*)
-- 1a closes EvalBootSeparatorDischarge (instance in Semantics.lean).
-- Copying law* into evalBoot is allowed (the law is the contract).
-- Copying mutant* into evalBoot is the failure this RED exists to catch.
-- Coincident mod(-7,-3)=-1 under BOTH floor and trunc is a NON-tooth.
-- 0 sorry, 0 axiom. closure_claim = 0.

namespace Residua.Bootstrap.EvalBootSeparators

def i64Min : Int := -9223372036854775808
def i64Max : Int :=  9223372036854775807
def two64  : Int :=  18446744073709551616

def inI64Range (n : Int) : Bool := i64Min ≤ n ∧ n ≤ i64Max

/-- Law A add: overflow-refuse, not wrap. -/
def lawAdd (x y : Int) : Option Int :=
  let s := x + y
  if inI64Range s then some s else none

/-- Mutant wrap-add (wasm i64.add). One-wrap is enough at the named points. -/
def mutantAdd (x y : Int) : Option Int :=
  let s := x + y
  if s > i64Max then some (s - two64)
  else if s < i64Min then some (s + two64)
  else some s

/-- Law A mod: floor (`Int.fmod` = Python `%` = evalLF). Div0 → none. -/
def lawMod (x y : Int) : Option Int :=
  if y = 0 then none else some (Int.fmod x y)

/-- Mutant trunc-rem (wasm `rem_s`). Sign follows dividend. -/
def mutantMod (x y : Int) : Option Int :=
  if y = 0 then none else some (Int.tmod x y)

/-- Law A div: exact-only; non-exact or out of i64 → none. -/
def lawDiv (x y : Int) : Option Int :=
  if y = 0 then none
  else if x % y = 0 then
    let q := x / y
    if inI64Range q then some q else none
  else none

-- Mutant trunc-div (wasm div_s without the MIN over -1 trap: wrap the
-- unrepresentable quotient). Non-exact still returns a value.
def mutantDiv (x y : Int) : Option Int :=
  if y = 0 then none
  else
    let q := Int.tdiv x y
    if q > i64Max then some (q - two64)
    else if q < i64Min then some (q + two64)
    else some q

/-- Law A compare: Bool constructor, not i64 0/1. -/
inductive CmpResult where
  | bool : Bool → CmpResult
  | i64  : Int → CmpResult
  deriving DecidableEq, Repr

def lawLt (x y : Int) : CmpResult := .bool (decide (x < y))
def mutantLt (x y : Int) : CmpResult := .i64 (if x < y then 1 else 0)

/-! ## Separator pins (law) — 1a evalBoot MUST match these. -/

theorem pin_mod_7_m3 : lawMod 7 (-3) = some (-2) := by decide
theorem pin_div_7_m3 : lawDiv 7 (-3) = none := by decide
theorem pin_add_min_m1 : lawAdd i64Min (-1) = none := by decide
theorem pin_div_min_m1 : lawDiv i64Min (-1) = none := by decide
theorem pin_lt_m1_1 : lawLt (-1) 1 = .bool true := by decide

/-! ## Mutant pins — 1a evalBoot' MUST match these (and therefore diverge). -/

theorem mut_mod_7_m3 : mutantMod 7 (-3) = some 1 := by decide
theorem mut_div_7_m3 : mutantDiv 7 (-3) = some (-2) := by decide
theorem mut_add_min_m1 : mutantAdd i64Min (-1) = some i64Max := by decide
theorem mut_div_min_m1 : mutantDiv i64Min (-1) = some i64Min := by decide
theorem mut_lt_m1_1 : mutantLt (-1) 1 = .i64 1 := by decide

/-! ## Teeth: law ≠ mutant at every named separator. -/

theorem tooth_mod : lawMod 7 (-3) ≠ mutantMod 7 (-3) := by
  rw [pin_mod_7_m3, mut_mod_7_m3]; decide
theorem tooth_div : lawDiv 7 (-3) ≠ mutantDiv 7 (-3) := by
  rw [pin_div_7_m3, mut_div_7_m3]; decide
theorem tooth_add : lawAdd i64Min (-1) ≠ mutantAdd i64Min (-1) := by
  rw [pin_add_min_m1, mut_add_min_m1]; decide
theorem tooth_div_min : lawDiv i64Min (-1) ≠ mutantDiv i64Min (-1) := by
  rw [pin_div_min_m1, mut_div_min_m1]; decide
theorem tooth_lt : lawLt (-1) 1 ≠ mutantLt (-1) 1 := by
  rw [pin_lt_m1_1, mut_lt_m1_1]; decide

/-! ## Non-tooth (census warning): coincident under floor and trunc.
    A 1a corpus that only uses this point cannot separate the two laws. -/

theorem coincident_mod_m7_m3 :
    lawMod (-7) (-3) = mutantMod (-7) (-3) ∧
    lawMod (-7) (-3) = some (-1) := by decide

-- ContentHash and source_q value domain (r5-thin 1a pin).
-- 32-byte raw digest of the empty preimage; hex is display-only.
-- Frozen contract file: lean/Residua/Bootstrap/separators_contract_v1.json
-- contract_q = sha256 of that file's bytes (AuthFact freeze; 1a pins this q).

def sha256EmptyRaw : List UInt8 := [
  0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
  0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
  0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
  0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
]

theorem sha256EmptyRaw_len32 : sha256EmptyRaw.length = 32 := by decide

def separatorsContractV1Q : String :=
  "84c06f8c6bd099a35fab94f18c90b96a654b05f4f9233dc490a70e2119633656"

-- 1a discharge class. Semantics.lean must provide an instance
-- whose eval* are evalBoot's ops and eval*' are evalBoot'.

class EvalBootSeparatorDischarge where
  evalMod : Int → Int → Option Int
  evalDiv : Int → Int → Option Int
  evalAdd : Int → Int → Option Int
  evalLt  : Int → Int → CmpResult
  pin_mod : evalMod 7 (-3) = some (-2)
  pin_div : evalDiv 7 (-3) = none
  pin_add : evalAdd i64Min (-1) = none
  pin_div_min : evalDiv i64Min (-1) = none
  pin_lt  : evalLt (-1) 1 = .bool true
  evalMod' : Int → Int → Option Int
  evalDiv' : Int → Int → Option Int
  evalAdd' : Int → Int → Option Int
  evalLt'  : Int → Int → CmpResult
  mut_mod : evalMod' 7 (-3) = some 1
  mut_div : evalDiv' 7 (-3) = some (-2)
  mut_add : evalAdd' i64Min (-1) = some i64Max
  mut_div_min : evalDiv' i64Min (-1) = some i64Min
  mut_lt  : evalLt' (-1) 1 = .i64 1

namespace EvalBootSeparatorDischarge
variable (D : EvalBootSeparatorDischarge)

theorem tooth_mod : D.evalMod 7 (-3) ≠ D.evalMod' 7 (-3) := by
  rw [D.pin_mod, D.mut_mod]; decide
theorem tooth_div : D.evalDiv 7 (-3) ≠ D.evalDiv' 7 (-3) := by
  rw [D.pin_div, D.mut_div]; decide
theorem tooth_add : D.evalAdd i64Min (-1) ≠ D.evalAdd' i64Min (-1) := by
  rw [D.pin_add, D.mut_add]; decide
theorem tooth_div_min : D.evalDiv i64Min (-1) ≠ D.evalDiv' i64Min (-1) := by
  rw [D.pin_div_min, D.mut_div_min]; decide
theorem tooth_lt : D.evalLt (-1) 1 ≠ D.evalLt' (-1) 1 := by
  rw [D.pin_lt, D.mut_lt]; decide

end EvalBootSeparatorDischarge

-- No instance here. 1a Semantics.lean must inhabit EvalBootSeparatorDischarge
-- with evalBoot and evalBoot'. Re-exporting law* and mutant* under new names
-- is not the interpreter and does not discharge 1a.

end Residua.Bootstrap.EvalBootSeparators
