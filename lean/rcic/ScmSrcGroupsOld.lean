/-
K3c regroup stage 1a — carried V2/V3 member definitions, verbatim
(unchanged bytes of the definition bodies; refs are the OLD numbering).
Sources: d5b49d0b9f:lean/rcic/ScmSrcTV2.lean (§Extra term builders …
§Exemplar members) and d5b49d0b9f:lean/rcic/ScmSrcTV3.lean
(§Expression helpers … §Members: exemplar byte constants and proof rows).
V1 helpers come from `rcic.RcicSrcEnvV1` (`Rcic.Scm.SrcTV`) — none needed
copying: `nE`/`cst`/`bytesLit`/`mDef`/`mThm`/`mkRefE`/`daE`/`cctE`/`mkBoundE`/
`vaE`/`mRefD`/`mBoundD` are all present there.
Omitted per spec: deleted members (old 90–95, 113–118) and the 7
①-replaced members (old 98, 99, 122, 124, 125, 139, 140).
-/
import rcic.RcicSrcEnvV1

namespace Rcic.Scm.SrcG.Old
open Rcic.Declarative
open Rcic.Scm.SrcTV

/-! ## V2 term builders (verbatim) -/

/-- de Bruijn variable. -/
def bv (i : Nat) : Expr Nat := .bvar i

/-- `succ` applied `k` times to `e` (`succ` is ref 2 of the literal
    profile). -/
def succK : Nat → Expr Nat → Expr Nat
  | 0, e => e
  | k + 1, e => succK k (.app (cst 2) e)

/-- `bcons x xs` — Bytes cons is ref 5. -/
def bconsE (h t : Expr Nat) : Expr Nat := .app (.app (cst 5) h) t

/-- `blCons x xs` — BytesList cons is ref 52. -/
def blconsE (h t : Expr Nat) : Expr Nat := .app (.app (cst 52) h) t

/-- `ftCons k t fs` — field-type cons is ref 55. -/
def ftconsE (k t fs : Expr Nat) : Expr Nat :=
  .app (.app (.app (cst 55) k) t) fs

/-- `iPos n` (ref 48) / `iNegS n` (ref 49). -/
def iposE (n : Expr Nat) : Expr Nat := .app (cst 48) n

def inegE (n : Expr Nat) : Expr Nat := .app (cst 49) n

/-- A singleton byte chain `[c]`. -/
def tB (c : Nat) : Expr Nat := bconsE (nE c) (cst 4)

/-- Relation applications (family refs below). -/
def ltE (a b : Expr Nat) : Expr Nat := .app (.app (cst 56) a) b

def bcE (a b c : Expr Nat) : Expr Nat := .app (.app (.app (cst 59) a) b) c

def dmE (n q r : Expr Nat) : Expr Nat := .app (.app (.app (cst 62) n) q) r

def ndE (n b : Expr Nat) : Expr Nat := .app (.app (cst 65) n) b

def neaE (n b : Expr Nat) : Expr Nat := .app (.app (cst 68) n) b

def ieaE (i b : Expr Nat) : Expr Nat := .app (.app (cst 70) i) b

def slE (b n : Expr Nat) : Expr Nat := .app (.app (cst 73) b) n

def bllE (l n : Expr Nat) : Expr Nat := .app (.app (cst 76) l) n

def ftlE (l n : Expr Nat) : Expr Nat := .app (.app (cst 79) l) n

def blcE (l b : Expr Nat) : Expr Nat := .app (.app (cst 82) l) b

def seaE (s b : Expr Nat) : Expr Nat := .app (.app (cst 85) s) b

def fteE (f b : Expr Nat) : Expr Nat := .app (.app (cst 87) f) b

/-- An inductive family member (`Type`-valued or `Prop`-valued). -/
def indM (ty : Expr Nat) : CheckedMember := ⟨.inductiveM, 0, ty, none⟩

/-- A constructor member with the given stored type. -/
def ctorM (ty : Expr Nat) : CheckedMember := ⟨.constructorM, 0, ty, none⟩

/-! ## V2 members: data layer … composite `CCT` (verbatim) -/

/-- `I : Type` — the i64 integer layer (V2b's `I<n>;` values). -/
def mIF : CheckedMember := indM (.sort (.succ .zero))

/-- `iPos : N → I`. -/
def mIPos : CheckedMember := ctorM (.pi (cst 0) (cst 47))

/-- `iNegS : N → I` — denotes `−(n+1)`. -/
def mINeg : CheckedMember := ctorM (.pi (cst 0) (cst 47))

/-- `BL : Type` — `Seq Bytes`, lists of byte strings. -/
def mBLF : CheckedMember := indM (.sort (.succ .zero))

def mBLNil : CheckedMember := ctorM (cst 50)

/-- `blCons : Bytes → BL → BL`. -/
def mBLCons : CheckedMember := ctorM (.pi (cst 3) (.pi (cst 50) (cst 50)))

/-- `FT : Type` — field-type list: key bytes paired with type bytes. -/
def mFTF : CheckedMember := indM (.sort (.succ .zero))

def mFTNil : CheckedMember := ctorM (cst 53)

/-- `ftCons : Bytes → Bytes → FT → FT` — `(keyBytes, tyBytes)` cons. -/
def mFTCons : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 3) (.pi (cst 53) (cst 53))))

/-- `Lt : N → N → Prop`. -/
def mLtF : CheckedMember := indM (.pi (cst 0) (.pi (cst 0) (.sort .zero)))

/-- `ltBase : Π n:N, Lt n (succ n)`. -/
def mLtB : CheckedMember :=
  ctorM (.pi (cst 0) (ltE (bv 0) (.app (cst 2) (bv 0))))

/-- `ltStep : Π a b:N, Lt a b → Lt a (succ b)`. -/
def mLtS : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 0)
    (.pi (ltE (bv 1) (bv 0)) (ltE (bv 2) (.app (cst 2) (bv 1))))))

/-- `ByteCat : Bytes → Bytes → Bytes → Prop` — `c = a ++ b`. -/
def mBCF : CheckedMember :=
  indM (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.sort .zero))))

/-- `catNil : Π b:Bytes, BC bnil b b`. -/
def mCatNil : CheckedMember := ctorM (.pi (cst 3) (bcE (cst 4) (bv 0) (bv 0)))

/-- `catCons : Π n:N, Π a b c:Bytes, BC a b c → BC (n::a) b (n::c)`. -/
def mCatCons : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
    (.pi (bcE (bv 2) (bv 1) (bv 0))
      (bcE (bconsE (bv 4) (bv 3)) (bv 2) (bconsE (bv 4) (bv 1))))))))

/-- `DM10 : N → N → N → Prop` — `n = 10·q + r` with `r < 10`. -/
def mDM10F : CheckedMember :=
  indM (.pi (cst 0) (.pi (cst 0) (.pi (cst 0) (.sort .zero))))

/-- `dmBase : Π r:N, Lt r 10 → DM10 r 0 r`. -/
def mDmBase : CheckedMember :=
  ctorM (.pi (cst 0)
    (.pi (ltE (bv 0) (nE 10)) (dmE (bv 1) (nE 0) (bv 1))))

/-- `dmStep : Π n q r:N, DM10 n q r → DM10 (10+n) (1+q) r`. -/
def mDmStep : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 0) (.pi (cst 0)
    (.pi (dmE (bv 2) (bv 1) (bv 0))
      (dmE (succK 10 (bv 3)) (.app (cst 2) (bv 2)) (bv 1))))))

/-- `NatDec : N → Bytes → Prop` — the decimal ASCII digit sequence
    of `n` (most significant first). -/
def mNDF : CheckedMember := indM (.pi (cst 0) (.pi (cst 3) (.sort .zero)))

/-- `ndBase : Π d:N, Lt d 10 → ND d [48+d]`. -/
def mNdBase : CheckedMember :=
  ctorM (.pi (cst 0)
    (.pi (ltE (bv 0) (nE 10))
      (ndE (bv 1) (bconsE (succK 48 (bv 1)) (cst 4)))))

/-- `ndStep : Π n q r:N, DM10 n q r → Lt 0 q → Π ds ds':Bytes,
    ND q ds → BC ds [48+r] ds' → ND n ds'`. The `Lt 0 q` premise
    blocks the leading-zero reading (`n = r` when `q = 0` is `ndBase`'s
    case, and `digits(q)` there would wrongly prepend `0`). -/
def mNdStep : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 0) (.pi (cst 0)
    (.pi (dmE (bv 2) (bv 1) (bv 0))
      (.pi (ltE (nE 0) (bv 2))
        (.pi (cst 3) (.pi (cst 3)
          (.pi (ndE (bv 5) (bv 1))
            (.pi (bcE (bv 2) (bconsE (succK 48 (bv 5)) (cst 4)) (bv 1))
              (ndE (bv 8) (bv 2)))))))))))

/-- `NatEncAt : N → Bytes → Prop` — `b = encNat n`'s bytes
    (`digits ++ ";"`). -/
def mNEAF : CheckedMember := indM (.pi (cst 0) (.pi (cst 3) (.sort .zero)))

/-- `neIntro : Π n:N, Π ds b:Bytes, ND n ds → BC ds [59] b → NEA n b`. -/
def mNeIntro : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3) (.pi (cst 3)
    (.pi (ndE (bv 2) (bv 1))
      (.pi (bcE (bv 2) (tB 59) (bv 1)) (neaE (bv 4) (bv 2)))))))

/-- `IntEncAt : I → Bytes → Prop` — `b = encNat n`'s bytes for the
    signed layer (`-` = 45). -/
def mIEAF : CheckedMember := indM (.pi (cst 47) (.pi (cst 3) (.sort .zero)))

/-- `iePos : Π n:N, Π b:Bytes, NEA n b → IEA (iPos n) b`. -/
def mIePos : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3)
    (.pi (neaE (bv 1) (bv 0)) (ieaE (iposE (bv 2)) (bv 1)))))

/-- `ieNeg : Π n:N, Π b' b:Bytes, NEA (succ n) b' → BC [45] b' b →
    IEA (iNegS n) b`. -/
def mIeNeg : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3) (.pi (cst 3)
    (.pi (neaE (.app (cst 2) (bv 2)) (bv 1))
      (.pi (bcE (tB 45) (bv 2) (bv 1)) (ieaE (inegE (bv 4)) (bv 2)))))))

/-- `SeqLen : Bytes → N → Prop` — cons-chain length. -/
def mSLF : CheckedMember := indM (.pi (cst 3) (.pi (cst 0) (.sort .zero)))

/-- `slNil : SL bnil 0`. -/
def mSlNil : CheckedMember := ctorM (slE (cst 4) (nE 0))

/-- `slCons : Π n:N, Π b:Bytes, Π k:N, SL b k → SL (n::b) (succ k)`. -/
def mSlCons : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3) (.pi (cst 0)
    (.pi (slE (bv 1) (bv 0))
      (slE (bconsE (bv 3) (bv 2)) (.app (cst 2) (bv 1)))))))

/-- `BListLen : BL → N → Prop`. -/
def mBLLF : CheckedMember := indM (.pi (cst 50) (.pi (cst 0) (.sort .zero)))

/-- `bllNil : BLL blNil 0`. -/
def mBllNil : CheckedMember := ctorM (bllE (cst 51) (nE 0))

/-- `bllCons : Π b:Bytes, Π bs:BL, Π n:N, BLL bs n →
    BLL (blCons b bs) (succ n)`. -/
def mBllCons : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 50) (.pi (cst 0)
    (.pi (bllE (bv 1) (bv 0))
      (bllE (blconsE (bv 3) (bv 2)) (.app (cst 2) (bv 1)))))))

/-- `FTLen : FT → N → Prop`. -/
def mFTLF : CheckedMember := indM (.pi (cst 53) (.pi (cst 0) (.sort .zero)))

/-- `ftlNil : FTL ftNil 0`. -/
def mFtlNil : CheckedMember := ctorM (ftlE (cst 54) (nE 0))

/-- `ftlCons : Π kb tb:Bytes, Π fs:FT, Π n:N, FTL fs n →
    FTL (ftCons kb tb fs) (succ n)`. -/
def mFtlCons : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 3) (.pi (cst 53) (.pi (cst 0)
    (.pi (ftlE (bv 1) (bv 0))
      (ftlE (ftconsE (bv 4) (bv 3) (bv 2)) (.app (cst 2) (bv 1))))))))

/-- `BListCat : BL → Bytes → Prop` — `b = concat bs`. -/
def mBLCF : CheckedMember := indM (.pi (cst 50) (.pi (cst 3) (.sort .zero)))

/-- `blcNil : BLC blNil bnil`. -/
def mBlcNil : CheckedMember := ctorM (blcE (cst 51) (cst 4))

/-- `blcCons : Π b:Bytes, Π bs:BL, Π rest acc:Bytes, BC b rest acc →
    BLC bs rest → BLC (blCons b bs) acc`. -/
def mBlcCons : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 50) (.pi (cst 3) (.pi (cst 3)
    (.pi (bcE (bv 3) (bv 1) (bv 0))
      (.pi (blcE (bv 3) (bv 2))
        (blcE (blconsE (bv 5) (bv 4)) (bv 2))))))))

/-- `StrEncAt : Bytes → Bytes → Prop` — `b = encStr s`'s bytes
    (`encNat(#s) ++ ":" ++ s`). `#s` counts the scalar sequence, per
    V1's `Char.toNat` convention. -/
def mSEAF : CheckedMember := indM (.pi (cst 3) (.pi (cst 3) (.sort .zero)))

/-- `seIntro : Π s:Bytes, Π k:N, Π nb b1 b:Bytes, SL s k → NEA k nb →
    BC nb [58] b1 → BC b1 s b → SEA s b`. -/
def mSeIntro : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 0) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
    (.pi (slE (bv 4) (bv 3))
      (.pi (neaE (bv 4) (bv 3))
        (.pi (bcE (bv 4) (tB 58) (bv 3))
          (.pi (bcE (bv 4) (bv 7) (bv 3))
            (seaE (bv 8) (bv 4)))))))))))

/-- `FTListEnc : FT → Bytes → Prop` — `b = concat over fields of
    (encStr k ++ tyBytes)`. -/
def mFTEF : CheckedMember := indM (.pi (cst 53) (.pi (cst 3) (.sort .zero)))

/-- `fteNil : FTE ftNil bnil`. -/
def mFteNil : CheckedMember := ctorM (fteE (cst 54) (cst 4))

/-- `fteCons : Π kb tb:Bytes, Π fs:FT, Π sek fb rest acc:Bytes,
    SEA kb sek → BC sek tb fb → BC fb rest acc → FTE fs rest →
    FTE (ftCons kb tb fs) acc`. -/
def mFteCons : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 3) (.pi (cst 53)
    (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
      (.pi (seaE (bv 6) (bv 3))
        (.pi (bcE (bv 4) (bv 6) (bv 3))
          (.pi (bcE (bv 4) (bv 3) (bv 2))
            (.pi (fteE (bv 7) (bv 4))
              (fteE (ftconsE (bv 10) (bv 9) (bv 8)) (bv 4)))))))))))))

/-- `cctL : Π re:RefT, Π tb b d:Bytes, BC [76] tb b → DA 3 16 b d →
    CCT re tb → CCT (mkRef 3 16 d) b` — `encTy (list t)`. -/
def mCctL : CheckedMember :=
  ctorM (.pi (cst 6) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
    (.pi (bcE (tB 76) (bv 2) (bv 1))
      (.pi (daE 3 16 (bv 2) (bv 1))
        (.pi (cctE (bv 5) (bv 4))
          (cctE (mkRefE 3 16 (bv 3)) (bv 4)))))))))

/-- `cctP : Π ra rb:RefT, Π ta tb ab b d:Bytes, BC [80] ta ab →
    BC ab tb b → DA 3 16 b d → CCT ra ta → CCT rb tb →
    CCT (mkRef 3 16 d) b` — `encTy (pair a b)`. -/
def mCctP : CheckedMember :=
  ctorM (.pi (cst 6) (.pi (cst 6) (.pi (cst 3) (.pi (cst 3)
    (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
      (.pi (bcE (tB 80) (bv 4) (bv 2))
        (.pi (bcE (bv 3) (bv 4) (bv 2))
          (.pi (daE 3 16 (bv 3) (bv 2))
            (.pi (cctE (bv 9) (bv 7))
              (.pi (cctE (bv 10) (bv 8))
                (cctE (mkRefE 3 16 (bv 5)) (bv 6))))))))))))))

/-- sha256 of the 01 §3 preimage of `"Lb"` — pinned below. -/
def digestLBHex : String :=
  "1f488e9537746b1fa18c83eb92a16f4aa37dc167ca3a275083a66d32cc9d6539"

/-- `"Lb"` — the `list bool` type's canonical wire bytes. -/
def mBytesLB : CheckedMember := mDef (cst 3) (bytesLit "Lb")

/-- `"Lb"`'s derived-address digest. -/
def mDigestLB : CheckedMember := mDef (cst 3) (bytesLit digestLBHex)

/-- `daLB : DA 3 16 bytesLB digestLB` — the declared crypto row for
    `list bool`. -/
def mDaLB : CheckedMember :=
  ⟨.constructorM, 0, daE 3 16 (cst 100) (cst 101), none⟩

/-- `bcLB : BC [76] bytesB bytesLB` — `"Lb" = 'L' ∷ "b"`, proved
    `catCons 76 bnil bytesB bytesB (catNil bytesB)` up to delta on the
    byte constants. -/
def mBcLB : CheckedMember :=
  mThm (bcE (tB 76) (cst 13) (cst 100))
    (.app (.app (.app (.app (.app (cst 61) (nE 76)) (cst 4)) (cst 13))
      (cst 13)) (.app (cst 60) (cst 13)))

/-- `lbRef = mkRef 3 16 digestLB`. -/
def mLbRef : CheckedMember := mRefD 101

/-- `cctLbPf : CCT lbRef bytesLB` — `cctL` applied to the bool
    binding's evidence. -/
def mCctLbPf : CheckedMember :=
  mThm (cctE (cst 104) (cst 100))
    (.app (.app (.app (.app (.app (.app (.app (cst 96) (cst 32))
      (cst 13)) (cst 100)) (cst 101)) (cst 103)) (cst 102)) (cst 36))

/-- `boundListBool = mkBound lbRef bytesLB cctLbPf`. -/
def mBoundListBool : CheckedMember := mBoundD 104 100 105

/-! ## V3 expression helpers (verbatim) -/

/-- `NEncList bs b` applied. -/
def nelE (s b : Expr Nat) : Expr Nat := .app (.app (cst 107) s) b

/-- `NthBound ts i b` applied. -/
def ntbE (ts i b : Expr Nat) : Expr Nat :=
  .app (.app (.app (cst 110) ts) i) b

/-- `ltStep`-chain: `ltProofE a k` is an `Expr` proving `Lt a (a+k+1)`. -/
def ltProofE : (a k : Nat) → Expr Nat
  | a, 0 => .app (cst 57) (nE a)
  | a, k + 1 =>
      .app (.app (.app (cst 58) (nE a)) (nE (a + k + 1)))
        (ltProofE a k)

/-! ## V3 members (verbatim) -/

/-- `NEncList : Bytes → Bytes → Prop` — `b` is the concatenation of
    `encNat bᵢ` over the byte list `bs`. -/
def mNELF : CheckedMember :=
  indM (.pi (cst 3) (.pi (cst 3) (.sort .zero)))

/-- `nelNil : NEL bnil bnil`. -/
def mNelNil : CheckedMember := ctorM (nelE (cst 4) (cst 4))

/-- `nelCons : Π n:N, Π ns nb eb b:Bytes, NEA n nb → NEL ns eb →
    BC nb eb b → NEL (n::ns) b`. -/
def mNelCons : CheckedMember :=
  ctorM (.pi (cst 0) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
    (.pi (cst 3)
      (.pi (neaE (bv 4) (bv 2))
        (.pi (nelE (bv 4) (bv 2))
          (.pi (bcE (bv 4) (bv 3) (bv 2))
            (nelE (bconsE (bv 7) (bv 6)) (bv 3))))))))))

/-- `NthBound : Π BL, Π N, Π BCT, Prop` — `ts`'s i-th byte string is
    bound by `b` (the bound carries its own `CCT` certificate). -/
def mNTBF : CheckedMember :=
  indM (.pi (cst 50) (.pi (cst 0) (.pi (cst 10) (.sort .zero))))

/-- `ntbHere : Π tb:Bytes, Π ts:BL, Π r:RefT, Π ct:(CCT r tb),
    NTB (blCons tb ts) 0 (mkBound r tb ct)`. -/
def mNtbHere : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 50) (.pi (cst 6)
    (.pi (cctE (bv 0) (bv 2))
      (ntbE (blconsE (bv 3) (bv 2)) (nE 0)
        (mkBoundE (bv 1) (bv 3) (bv 0)))))))

/-- `ntbNext : Π t0:Bytes, Π ts:BL, Π i:N, Π b:BCT,
    NTB ts i b → NTB (blCons t0 ts) (succ i) b`. -/
def mNtbNext : CheckedMember :=
  ctorM (.pi (cst 3) (.pi (cst 50) (.pi (cst 0) (.pi (cst 10)
    (.pi (ntbE (bv 2) (bv 1) (bv 0))
      (ntbE (blconsE (bv 4) (bv 3)) (.app (cst 2) (bv 2)) (bv 1)))))))

/-- `vaI64 : Π r:RefT, Π a:(CCT r "i"), Π n:I, Π b vb:Bytes,
    IEA n b → BC [73] b vb → VA (mkBound r "i" a) vb` —
    `encVal (.i n) = "I" ++ encNat n`. -/
def mVaI64 : CheckedMember :=
  ctorM (.pi (cst 6)
    (.pi (cctE (bv 0) (cst 12))
      (.pi (cst 47) (.pi (cst 3) (.pi (cst 3)
        (.pi (ieaE (bv 2) (bv 1))
          (.pi (bcE (tB 73) (bv 2) (bv 1))
            (vaE (mkBoundE (bv 6) (cst 12) (bv 5)) (bv 2)))))))))

/-- `vaStr : Π r:RefT, Π a:(CCT r "s"), Π s b vb:Bytes,
    SEA s b → BC [84] b vb → VA (mkBound r "s" a) vb` —
    `encVal (.s s) = "T" ++ encStr s`. -/
def mVaStr : CheckedMember :=
  ctorM (.pi (cst 6)
    (.pi (cctE (bv 0) (cst 14))
      (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
        (.pi (seaE (bv 2) (bv 1))
          (.pi (bcE (tB 84) (bv 2) (bv 1))
            (vaE (mkBoundE (bv 6) (cst 14) (bv 5)) (bv 2)))))))))

/-- `vaY : Π r:RefT, Π a:(CCT r "y"), Π bs:Bytes, Π l:N,
    Π l0 nb eb vb:Bytes, SL bs l → NEA l nb → NEL bs eb →
    BC [89] nb l0 → BC l0 eb vb → VA (mkBound r "y" a) vb` —
    `encVal (.y bs) = "Y" ++ encNat #bs ++ concat(encNat bs)`. -/
def mVaY : CheckedMember :=
  ctorM (.pi (cst 6)
    (.pi (cctE (bv 0) (cst 15))
      (.pi (cst 3) (.pi (cst 0)
        (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
          (.pi (slE (bv 5) (bv 4))
            (.pi (neaE (bv 5) (bv 3))
              (.pi (nelE (bv 7) (bv 3))
                (.pi (bcE (tB 89) (bv 5) (bv 6))
                  (.pi (bcE (bv 7) (bv 5) (bv 4))
                    (vaE (mkBoundE (bv 12) (cst 15) (bv 11))
                      (bv 5)))))))))))))))

/-- `vaPair : Π ra rb:RefT, Π ta tb ab b d va vb lv vp:Bytes,
    BC [80] ta ab → BC ab tb b → DA 3 16 b d →
    CCT ra ta → CCT rb tb →
    VA (mkBound ra ta ca) va → VA (mkBound rb tb cb) vb →
    BC [80] va lv → BC lv vb vp →
    VA (mkBound (mkRef 3 16 d) b (cctP ra rb ta tb ab b d …)) vp` —
    `encVal (.p a b) = "P" ++ encVal a ++ encVal b`. -/
def mVaPair : CheckedMember :=
  ctorM (.pi (cst 6) (.pi (cst 6)                      -- ra rb
    (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
      (.pi (cst 3) (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
        (.pi (bcE (tB 80) (bv 8) (bv 6))               -- cat1
          (.pi (bcE (bv 7) (bv 8) (bv 6))              -- cat2
            (.pi (daE 3 16 (bv 7) (bv 6))              -- da
              (.pi (cctE (bv 13) (bv 11))              -- ca
                (.pi (cctE (bv 13) (bv 11))            -- cb
                  (.pi (vaE (mkBoundE (bv 15) (bv 13) (bv 1)) (bv 8))
                    (.pi (vaE (mkBoundE (bv 15) (bv 13) (bv 1)) (bv 8))
                      (.pi (bcE (tB 80) (bv 10) (bv 8))
                        (.pi (bcE (bv 9) (bv 10) (bv 8))
                          (vaE
                            (mkBoundE (mkRefE 3 16 (bv 13)) (bv 14)
                              (.app (.app (.app (.app (.app (.app
                                (.app (.app (.app (.app (.app (.app
                                  (cst 97) (bv 19)) (bv 18)) (bv 17))
                                  (bv 16)) (bv 15)) (bv 14)) (bv 13))
                                  (bv 8)) (bv 7)) (bv 6)) (bv 5))
                                  (bv 4)))
                            (bv 9))))))))))))))))))))))


def mBytesSemi : CheckedMember := mDef (cst 3) (bytesLit ";")

def mBytesD0   : CheckedMember := mDef (cst 3) (bytesLit "0")

def mBytesNat0 : CheckedMember := mDef (cst 3) (bytesLit "0;")

def mBytesVLB0 : CheckedMember := mDef (cst 3) (bytesLit "L0;")

def mBytesI5   : CheckedMember := mDef (cst 3) (bytesLit "I5;")

def mBytesD5   : CheckedMember := mDef (cst 3) (bytesLit "5")

def mBytesNat5 : CheckedMember := mDef (cst 3) (bytesLit "5;")

/-- `lt010 : Lt 0 10` — the `ndBase` guard at digit 0. -/
def mLt010 : CheckedMember :=
  mThm (ltE (nE 0) (nE 10)) (ltProofE 0 9)

/-- `nd0 : ND 0 "0"` — `ndBase 0 lt010`; the digit byte is the
    `succK 48 (lit 0)` form, convertible to the `lit 48` const by the
    `lit`-expansion steps in `cnvNd0`. -/
def mNd0 : CheckedMember :=
  mThm (ndE (nE 0) (cst 127)) (.app (.app (cst 66) (nE 0)) (cst 133))

/-- `bc48S : BC "0" ";" "0;"`. -/
def mBc48S : CheckedMember :=
  mThm (bcE (cst 127) (tB 59) (cst 128))
    (.app (.app (.app (.app (.app (cst 61) (nE 48)) (cst 4))
      (tB 59)) (tB 59)) (.app (cst 60) (tB 59)))

/-- `nea0 : NEA 0 "0;"`. -/
def mNea0 : CheckedMember :=
  mThm (neaE (nE 0) (cst 128))
    (.app (.app (.app (.app (.app (cst 69) (nE 0)) (cst 127))
      (cst 128)) (cst 134)) (cst 135))

/-- `bcLN0 : BC [76] "0;" "L0;"` — `encNat` tagged with `L`. -/
def mBcLN0 : CheckedMember :=
  mThm (bcE (tB 76) (cst 128) (cst 129))
    (.app (.app (.app (.app (.app (cst 61) (nE 76)) (cst 4))
      (cst 128)) (cst 128)) (.app (cst 60) (cst 128)))

/-- `bcL0Nil : BC "L0;" bnil "L0;"` — concat with the empty
    element-string. -/
def mBcL0Nil : CheckedMember :=
  mThm (bcE (cst 129) (cst 4) (cst 129))
    (.app (.app (.app (.app (.app (cst 61) (nE 76)) (cst 128))
      (cst 4)) (cst 128))
      (.app (.app (.app (.app (.app (cst 61) (nE 48)) (tB 59))
        (cst 4)) (tB 59))
        (.app (.app (.app (.app (.app (cst 61) (nE 59)) (cst 4))
          (cst 4)) (cst 4)) (.app (cst 60) (cst 4)))))

/-- `lt510 : Lt 5 10`. -/
def mLt510 : CheckedMember :=
  mThm (ltE (nE 5) (nE 10)) (ltProofE 5 4)

/-- `nd5 : ND 5 "5"`. -/
def mNd5 : CheckedMember :=
  mThm (ndE (nE 5) (cst 131)) (.app (.app (cst 66) (nE 5)) (cst 141))

/-- `bc53S : BC "5" ";" "5;"`. -/
def mBc53S : CheckedMember :=
  mThm (bcE (cst 131) (tB 59) (cst 132))
    (.app (.app (.app (.app (.app (cst 61) (nE 53)) (cst 4))
      (tB 59)) (tB 59)) (.app (cst 60) (tB 59)))

/-- `nea5 : NEA 5 "5;"`. -/
def mNea5 : CheckedMember :=
  mThm (neaE (nE 5) (cst 132))
    (.app (.app (.app (.app (.app (cst 69) (nE 5)) (cst 131))
      (cst 132)) (cst 142)) (cst 143))

/-- `ieaP5 : IEA (iPos 5) "5;"` — the positive `I` encoding. -/
def mIeaP5 : CheckedMember :=
  mThm (ieaE (iposE (nE 5)) (cst 132))
    (.app (.app (.app (cst 71) (nE 5)) (cst 132)) (cst 144))

/-- `bcI5 : BC [73] "5;" "I5;"`. -/
def mBcI5 : CheckedMember :=
  mThm (bcE (tB 73) (cst 132) (cst 130))
    (.app (.app (.app (.app (.app (cst 61) (nE 73)) (cst 4))
      (cst 132)) (cst 132)) (.app (cst 60) (cst 132)))

/-- `vI64_5 : ValueAt boundI64 "I5;"` — the i64 value exemplar. -/
def mVI5 : CheckedMember :=
  mThm (vaE (cst 39) (cst 130))
    (.app (.app (.app (.app (.app (.app (.app (cst 119) (cst 31))
      (cst 35)) (iposE (nE 5))) (cst 132)) (cst 130)) (cst 145))
      (cst 146))

end Rcic.Scm.SrcG.Old
