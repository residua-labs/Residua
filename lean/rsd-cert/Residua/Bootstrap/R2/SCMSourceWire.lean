import Residua.Bootstrap.R2.SCM
import Residua.Bootstrap.R2.SCMAuditCached
import Residua.Bootstrap.BootTypeWire

/-! Candidate L1 source serialization of Bootstrap.R2.SCM (S4 revision 2, UINT64-0).
The expression tags 0 to 52 are those of `SCMSourceWire.lean`; the width-64 operators take 64 to 77
(docs/EMITTER.md "RSCM revision UINT64-0 (W row)"); a literal `litW` is the tag and 8 bytes, little endian.
This structurally visits SCMExpr/SCMArgs/SCMBranches/SCMPrograms, never the
unrelated SCMEmission AST, an evaluator, or BootExprWire. Its expression tags
follow SCM declaration order. Sharing scalar/type leaf formats is intentional.
The versioned envelope is distinct from a BootExpr body and from future UTF-8
SCM source (L2). This is initial seed/oracle serialization, not yet a compiled
source encoder, a uniqueness theorem, genesis, or authority handoff. -/

namespace Residua.Bootstrap.R2.SCMSourceWire

open IR R2.SCM R2
abbrev Bytes := List UInt8

/-- Refuse nonrepresentable literals instead of silently reducing modulo 2^64. -/
def signedLeaf (n : Int) : Option Bytes :=
  if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then
    some (Bundle.bEncode (.i64 n))
  else none

def nameLeaf (s : String) : Bytes := Bundle.bEncode (.bytes s.toUTF8.data.toList)

mutual
  def expr : SCMExpr S G t → Option Bytes
    | .litI n => do return [0] ++ (← signedLeaf n)
    | .litB b => some [1, if b then 1 else 0]
    | .litS s => some (2 :: nameLeaf s)
    | .var i => some (3 :: Bundle.lebEnc i.val)
    | .let1 (a := a) v b => do
        return [4] ++ BootTypeWire.encode a ++ (← expr v) ++ (← expr b)
    | .ifE c a b => do return [5] ++ (← expr c) ++ (← expr a) ++ (← expr b)
    | .add a b => do return [6] ++ (← expr a) ++ (← expr b)
    | .sub a b => do return [7] ++ (← expr a) ++ (← expr b)
    | .mul a b => do return [8] ++ (← expr a) ++ (← expr b)
    | .neg a => do return 9 :: (← expr a)
    | .divE a b => do return [10] ++ (← expr a) ++ (← expr b)
    | .modE a b => do return [11] ++ (← expr a) ++ (← expr b)
    | .lt a b => do return [12] ++ (← expr a) ++ (← expr b)
    | .gt a b => do return [13] ++ (← expr a) ++ (← expr b)
    | .eqE (t := t) a b => do
        return [14] ++ BootTypeWire.encode t ++ (← expr a) ++ (← expr b)
    | .andE a b => do return [15] ++ (← expr a) ++ (← expr b)
    | .orE a b => do return [16] ++ (← expr a) ++ (← expr b)
    | .notE a => do return 17 :: (← expr a)
    | .strLen a => do return 18 :: (← expr a)
    | .strSplit a b => do return [19] ++ (← expr a) ++ (← expr b)
    | .strSubstring a b c => do return [20] ++ (← expr a) ++ (← expr b) ++ (← expr c)
    | .strToInt a => do return 21 :: (← expr a)
    | .emptyList => some [22]
    | .listSingleton a => do return 23 :: (← expr a)
    | .listLen (t := t) a => do
        return [24] ++ BootTypeWire.encode (.list t) ++ (← expr a)
    | .listFirst a => do return 25 :: (← expr a)
    | .listAppend a b => do return [26] ++ (← expr a) ++ (← expr b)
    | .listDrop a b => do return [27] ++ (← expr a) ++ (← expr b)
    | .pairE a b => do return [28] ++ (← expr a) ++ (← expr b)
    | .fstE (a := a) (b := b) p => do
        return [29] ++ BootTypeWire.encode (.pair a b) ++ (← expr p)
    | .sndE (a := a) (b := b) p => do
        return [30] ++ BootTypeWire.encode (.pair a b) ++ (← expr p)
    | .inj i a => do return [31] ++ Bundle.lebEnc i.val ++ (← expr a)
    | .matchE (ts := ts) a bs => do
        return [32] ++ BootTypeWire.encode (.sum ts) ++ (← expr a) ++ (← branches bs)
    | .recNil => some [33]
    | .recCons n a b => do return [34] ++ nameLeaf n ++ (← expr a) ++ (← expr b)
    | .field (fs := fs) a i => do
        return [35] ++ BootTypeWire.encode (.record fs) ++ Bundle.lebEnc i.val ++ (← expr a)
    | .someE a => do return 36 :: (← expr a)
    | .noneE => some [37]
    | .isSomeE (t := t) a => do
        return [38] ++ BootTypeWire.encode (.option t) ++ (← expr a)
    | .unwrapSome a => do return 39 :: (← expr a)
    | .okE a => do return 40 :: (← expr a)
    | .residueE n => do return [41] ++ (← signedLeaf n)
    | .isResidueE (t := t) a => do
        return [42] ++ BootTypeWire.encode (.residue t) ++ (← expr a)
    | .getResidue (t := t) a => do
        return [43] ++ BootTypeWire.encode (.residue t) ++ (← expr a)
    | .getOk a => do return 44 :: (← expr a)
    | .packBytes a => do return 45 :: (← expr a)
    | .bytesLen a => do return 46 :: (← expr a)
    | .bytesConcat a b => do return [47] ++ (← expr a) ++ (← expr b)
    | .bytesSlice a b c => do return [48] ++ (← expr a) ++ (← expr b) ++ (← expr c)
    | .contentHash a => do return 49 :: (← expr a)
    | .boundedFold (a := a) xs z b => do
        return [50] ++ BootTypeWire.encode (.list a) ++ (← expr xs) ++ (← expr z) ++ (← expr b)
    | .boundedFix (s := s) c b z n => do
        return [51] ++ BootTypeWire.encode s ++ (← expr c) ++ (← expr b) ++ (← expr z) ++ (← expr n)
    | .call i as => do return [52] ++ Bundle.lebEnc i.val ++ (← args as)
    | .litW n => some (64 :: ((List.range 8).map (fun i => ((n.toNat >>> (8 * i)) % 256).toUInt8)))
    | .wAdd a b => do return [65] ++ (← expr a) ++ (← expr b)
    | .wSub a b => do return [66] ++ (← expr a) ++ (← expr b)
    | .wMul a b => do return [67] ++ (← expr a) ++ (← expr b)
    | .wDiv a b => do return [68] ++ (← expr a) ++ (← expr b)
    | .wMod a b => do return [69] ++ (← expr a) ++ (← expr b)
    | .wLt a b => do return [70] ++ (← expr a) ++ (← expr b)
    | .wLe a b => do return [71] ++ (← expr a) ++ (← expr b)
    | .wAnd a b => do return [72] ++ (← expr a) ++ (← expr b)
    | .wOr a b => do return [73] ++ (← expr a) ++ (← expr b)
    | .wXor a b => do return [74] ++ (← expr a) ++ (← expr b)
    | .wNot a => do return 75 :: (← expr a)
    | .wShl a b => do return [76] ++ (← expr a) ++ (← expr b)
    | .wShr a b => do return [77] ++ (← expr a) ++ (← expr b)
    | .fAdd a b => do return [78] ++ (← expr a) ++ (← expr b)
    | .fSub a b => do return [79] ++ (← expr a) ++ (← expr b)
    | .fMul a b => do return [80] ++ (← expr a) ++ (← expr b)
    | .fDiv a b => do return [81] ++ (← expr a) ++ (← expr b)
    | .fLt a b => do return [82] ++ (← expr a) ++ (← expr b)
    | .fLe a b => do return [83] ++ (← expr a) ++ (← expr b)
    | .fEq a b => do return [84] ++ (← expr a) ++ (← expr b)
    | .fNeg a => do return 85 :: (← expr a)
    | .fAbs a => do return 86 :: (← expr a)
    | .fSqrt a => do return 87 :: (← expr a)
    | .fFloor a => do return 88 :: (← expr a)
    | .fCeil a => do return 89 :: (← expr a)
    | .fRound a => do return 90 :: (← expr a)
    | .fOfW a => do return 91 :: (← expr a)
    | .fOfI a => do return 92 :: (← expr a)
    | .fToW a => do return 93 :: (← expr a)
    | .fBits a => do return 94 :: (← expr a)
    | .aUSize (a := a) arr => do
        return [55] ++ BootTypeWire.encode (.list a) ++ (← expr arr)
    | .wToN w => do return 56 :: (← expr w)
    | .aEmpty (a := a) c => do
        return [57] ++ BootTypeWire.encode (.list a) ++ (← expr c)
    | .aMk (a := a) n v => do
        return [58] ++ BootTypeWire.encode (.list a) ++ (← expr n) ++ (← expr v)
    | .aOfList (a := a) xs => do
        return [59] ++ BootTypeWire.encode (.list a) ++ (← expr xs)
    | .aToList (a := a) arr => do
        return [60] ++ BootTypeWire.encode (.list a) ++ (← expr arr)
    | .aSize (a := a) arr => do
        return [61] ++ BootTypeWire.encode (.list a) ++ (← expr arr)
    | .aGet (a := a) arr i => do
        return [62] ++ BootTypeWire.encode (.list a) ++ (← expr arr) ++ (← expr i)
    | .aSet (a := a) arr i v => do
        return [63] ++ BootTypeWire.encode (.list a) ++ (← expr arr) ++ (← expr i) ++ (← expr v)
    | .aPush (a := a) arr v => do
        return [95] ++ BootTypeWire.encode (.list a) ++ (← expr arr) ++ (← expr v)
    | .aPop (a := a) arr => do
        return [96] ++ BootTypeWire.encode (.list a) ++ (← expr arr)
    | .aSlice (a := a) arr i j => do
        return [97] ++ BootTypeWire.encode (.list a) ++ (← expr arr) ++ (← expr i) ++ (← expr j)
    | .aAppend (a := a) a1 a2 => do
        return [98] ++ BootTypeWire.encode (.list a) ++ (← expr a1) ++ (← expr a2)

  def args : SCMArgs S G ts → Option Bytes
    | .nil => some [0]
    | .cons a as => do return [1] ++ (← expr a) ++ (← args as)

  def branches : SCMBranches S G ts t → Option Bytes
    | .nil => some [0]
    | .cons b bs => do return [1] ++ (← expr b) ++ (← branches bs)
end

/-- Ordered program bodies. The envelope binds their entire signature table. -/
def programs : SCMPrograms S R → Option Bytes
  | .nil => some [0]
  | .cons body rest => do return [1] ++ (← expr body) ++ (← programs rest)

/-- Candidate source-container discriminator RSCM, version 1; not bundle kind. -/
def header : Bytes := [0x52, 0x53, 0x43, 0x4d, 1]

/-- The persisted object includes the complete call-signature environment.
Only closed program tables are accepted. Audit includes keys hidden in types,
unused signatures and binders; failures never sanitize the source. -/
def encode (source : SCMPrograms S S) : Option Bytes := do
  match auditProgramsCached source with
  | .error _ => none
  | .ok _ => return header ++ BootTypeWire.encodeSignatures S ++ (← programs source)

/-- The cached signature audit preserves the complete encoded byte result. -/
theorem encode_eq_uncached (source : SCMPrograms S S) :
    encode source =
      (do
        match auditSCMPrograms source with
        | .error _ => none
        | .ok _ => return header ++ BootTypeWire.encodeSignatures S ++
            (← programs source)) := by
  simp only [encode, auditProgramsCached_eq]

end Residua.Bootstrap.R2.SCMSourceWire
