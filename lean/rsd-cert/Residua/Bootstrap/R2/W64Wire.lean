import Residua.Bootstrap.SCMSourceWire
import Residua.Bootstrap.R2.SCMSourceWire
import Residua.EvalLean.R2.RscmDecode

/-!
# UINT64-0 wire rows (S4 revision 2)

1. an image without a width-64 operator is byte-identical to the one the frozen S4 writes (`SCMSourceWire.encode`);
2. a program with the operators encodes to the tags of docs/EMITTER.md (litW = 64 and 8 bytes little endian, wAdd 65 ...),
   decodes by the revision-2 decoder (`Residua.EvalLean.R2.rscmD`) to a program that re-encodes byte-equal and evaluates
   to the same value as stock Lean's `UInt64`.
`lean --run W64Wire.lean` prints `w64wire ok=<n>/<n>`. `closure_claim = 0`.
-/

open Residua.Bootstrap

def oldSig : IR.SigTable := [([], .i64)]
def oldProg : SCM.SCMPrograms oldSig oldSig :=
  .cons (.add (.litI 40) (.mul (.litI 1) (.litI 2))) .nil
def oldProgR2 : R2.SCM.SCMPrograms oldSig oldSig :=
  .cons (.add (.litI 40) (.mul (.litI 1) (.litI 2))) .nil

def newBody (a b : UInt64) : R2.SCM.SCMExpr oldSig [] .i64 :=
  .wShr (.wAdd (.wMul (.litW a) (.litW b)) (.wNot (.litW a))) (.litW 3)
def newProg (a b : UInt64) : R2.SCM.SCMPrograms oldSig oldSig := .cons (newBody a b) .nil

def refVal (a b : UInt64) : UInt64 := ((a * b) + (~~~a)) >>> 3

def evalNew (p : R2.SCM.SCMPrograms oldSig oldSig) : Option R2.SCM.SCMVal :=
  R2.SCM.evalSCM p 1 [] (R2.SCM.getSCMProgram p ⟨0, by decide⟩)

def cases : List (UInt64 × UInt64) :=
  [(0x8000000000000001, 2), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF), (0x7FFFFFFFFFFFFFFF, 3), (5, 0x8000000000000000)]

def row (a b : UInt64) : Bool :=
  match R2.SCMSourceWire.encode (newProg a b) with
  | none => false
  | some bytes =>
    let tagOk := bytes.contains 65 && bytes.contains 67 && bytes.contains 75 && bytes.contains 77 && bytes.contains 64
    match Residua.EvalLean.R2.rscmD bytes.toArray with
    | .error _ => false
    | .ok ⟨S, p⟩ =>
      let again := R2.SCMSourceWire.encode p
      let value : Option R2.SCM.SCMVal :=
        match S, p with
        | _ :: _, p => R2.SCM.evalSCM p 1 [] (R2.SCM.getSCMProgram p ⟨0, Nat.zero_lt_succ _⟩)
        | [], _ => none
      tagOk && (again == some bytes) && R2.SCM.scmOutEq value (.int (refVal a b).toNat)

def fProg : R2.SCM.SCMPrograms oldSig oldSig :=
  .cons (.fToW (.fBits (.fAdd (.fSqrt (.fOfW (.litW 9))) (.fRound (.litW 0x4004000000000000))))) .nil

def aProg : R2.SCM.SCMPrograms oldSig oldSig :=
  .cons (.aGet (.aSlice (.aAppend (.aPush (.aEmpty (.litW 0)) (.litW 10)) (.aMk (.wToN (.litW 2) : R2.SCM.SCMExpr oldSig [] R2.SCM.natMagTy) (.litW 25))) (.litW 0) (.litW 3)) (.litW 1)) .nil

def roundTripI (p : R2.SCM.SCMPrograms oldSig oldSig) (expected : Int) : Bool :=
  match R2.SCMSourceWire.encode p with
  | none => false
  | some bytes =>
    match Residua.EvalLean.R2.rscmD bytes.toArray with
    | .error _ => false
    | .ok ⟨S, p'⟩ =>
      let again := R2.SCMSourceWire.encode p'
      let value : Option R2.SCM.SCMVal :=
        match S, p' with
        | _ :: _, p' => R2.SCM.evalSCM p' 2 [] (R2.SCM.getSCMProgram p' ⟨0, Nat.zero_lt_succ _⟩)
        | [], _ => none
      (again == some bytes) && R2.SCM.scmOutEq value (.int expected)

def main : IO UInt32 := do
  let sameOld := SCMSourceWire.encode oldProg == R2.SCMSourceWire.encode oldProgR2
  IO.println s!"old image byte-identical: {sameOld}"
  let rs := (cases.map fun (a, b) => row a b) ++ [roundTripI fProg 6, roundTripI aProg 25]
  let ok := (rs.filter id).length + (if sameOld then 1 else 0)
  let tot := rs.length + 1
  IO.println s!"w64wire ok={ok}/{tot}"
  return (if ok == tot then 0 else 1)
