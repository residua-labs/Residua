/-
Original member table of `srcEnvV1` from `babd0a56e3:lean/rcic/ScmSrcTV.lean`.
Copied, not retyped. The table does not use `ScmBoundCoreTV`.
-/
import rcic.RcicDeclarative

namespace Rcic.Scm.SrcTV
open Rcic.Declarative


/-! ## Host-side term builders -/

/-- `.lit` numeral (the literal profile pins N at 0/1/2). -/
def nE (t : Nat) : Expr Nat := .lit t

/-- `Seq N` cons-chain of naturals. -/
def seqE : List Nat → Expr Nat
  | [] => .const 4 []
  | n :: ns => .app (.app (.const 5 []) (nE n)) (seqE ns)

/-- The String→bytes representation relation fixed for the source
    interface (A1's `scalars` convention: byte = `Char.toNat`). -/
def quoteBytes (s : String) : Expr Nat := seqE (s.toList.map Char.toNat)

/-- `const` shorthand used only in this file's table comments. -/
def cst (r : Nat) : Expr Nat := .const r []

/-- `N`-valued literal application chain. -/
def appsN : Expr Nat → List (Expr Nat) → Expr Nat := List.foldl .app

/-- Bytes literal term for a string. -/
def bytesLit (s : String) : Expr Nat := quoteBytes s

/-- `mkRef cls kind digest` applied. -/
def mkRefE (cls kind : Nat) (d : Expr Nat) : Expr Nat :=
  .app (.app (.app (cst 7) (nE cls)) (nE kind)) d

/-- `DA cls kind bytes digest` applied. -/
def daE (cls kind : Nat) (b d : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (cst 8) (nE cls)) (nE kind)) b) d

/-- `CCT r b` applied. -/
def cctE (r b : Expr Nat) : Expr Nat := .app (.app (cst 9) r) b

/-- `mkBound r b a` applied. -/
def mkBoundE (r b a : Expr Nat) : Expr Nat :=
  .app (.app (.app (cst 30) r) b) a

/-- `ValueAt T b` applied. -/
def vaE (t b : Expr Nat) : Expr Nat := .app (.app (cst 11) t) b

/-! ## Members -/

def mNatF  : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def mZero  : CheckedMember := ⟨.constructorM, 0, cst 0, none⟩
def mSucc  : CheckedMember := ⟨.constructorM, 0, .pi (cst 0) (cst 0), none⟩
def mBytesF : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def mBNil  : CheckedMember := ⟨.constructorM, 0, cst 3, none⟩
def mBCons : CheckedMember :=
  ⟨.constructorM, 0, .pi (cst 0) (.pi (cst 3) (cst 3)), none⟩
def mRefF  : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def mMkRef : CheckedMember :=
  ⟨.constructorM, 0, .pi (cst 0) (.pi (cst 0) (.pi (cst 3) (cst 6))), none⟩
/-- `DerivedAddr : Π (_ : N), Π (_ : N), Π (_ : Bytes), Π (_ : Bytes),
    Prop`. -/
def mDA    : CheckedMember :=
  ⟨.inductiveM, 0, .pi (cst 0) (.pi (cst 0) (.pi (cst 3)
    (.pi (cst 3) (.sort .zero)))), none⟩
/-- `CCT : Π (_ : RefT), Π (_ : Bytes), Prop`. -/
def mCCT   : CheckedMember :=
  ⟨.inductiveM, 0, .pi (cst 6) (.pi (cst 3) (.sort .zero)), none⟩
/-- `BCT : Type`. -/
def mBCT   : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
/-- `ValueAt : Π (_ : BCT), Π (_ : Bytes), Prop`. -/
def mVA    : CheckedMember :=
  ⟨.inductiveM, 0, .pi (cst 10) (.pi (cst 3) (.sort .zero)), none⟩

def mDef (ty v : Expr Nat) : CheckedMember := ⟨.definitionM, 0, ty, some v⟩

/-- `"i"`. -/
def mBytesI : CheckedMember := mDef (cst 3) (bytesLit "i")
/-- `"b"`. -/
def mBytesB : CheckedMember := mDef (cst 3) (bytesLit "b")
/-- `"s"`. -/
def mBytesS : CheckedMember := mDef (cst 3) (bytesLit "s")
/-- `"y"`. -/
def mBytesY : CheckedMember := mDef (cst 3) (bytesLit "y")
/-- `"B0;"`. -/
def mBytesB0 : CheckedMember := mDef (cst 3) (bytesLit "B0;")
/-- `"B1;"`. -/
def mBytesB1 : CheckedMember := mDef (cst 3) (bytesLit "B1;")

/-- sha256 of the 01 §3 preimage of the i64 core type — pinned below. -/
def digestIHex : String :=
  "99da79cca2f69fd05c4ea282bf9528564a11549f5753fcd1107585f5bdd3620f"
def digestBHex : String :=
  "d6c3be8edbc2d95b67f5868ca6a9517c326a49d190d6e39fd8e8d334b4cad174"
def digestSHex : String :=
  "bc5cdd70625db476253408a839e2f2518fb8106d10f4bb07664fd43725f83aa9"
def digestYHex : String :=
  "136d9cdd2bea603ddfa4c84b123ae672a8fbef549bc8d8e5f8e672813e183acd"

def mDigestI : CheckedMember := mDef (cst 3) (bytesLit digestIHex)
def mDigestB : CheckedMember := mDef (cst 3) (bytesLit digestBHex)
def mDigestS : CheckedMember := mDef (cst 3) (bytesLit digestSHex)
def mDigestY : CheckedMember := mDef (cst 3) (bytesLit digestYHex)

/-- A `DerivedAddr` row: `DA 3 16 <typeBytes> <digest>`. The four rows
    are the whole V1 crypto table. -/
def mDa (bRef dRef : Nat) : CheckedMember :=
  ⟨.constructorM, 0, daE 3 16 (cst bRef) (cst dRef), none⟩
def mDaI : CheckedMember := mDa 12 18
def mDaB : CheckedMember := mDa 13 19
def mDaS : CheckedMember := mDa 14 20
def mDaY : CheckedMember := mDa 15 21

/-- A ground-type `CCT` constructor:
    `∀ (d : Bytes), DA 3 16 <tb> d → CCT (mkRef 3 16 d) <tb>`. -/
def mCct (bRef : Nat) : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (cst 3)
      (.pi (daE 3 16 (cst bRef) (.bvar 0))
        (cctE (mkRefE 3 16 (.bvar 1)) (cst bRef))), none⟩
def mCctI : CheckedMember := mCct 12
def mCctB : CheckedMember := mCct 13
def mCctS : CheckedMember := mCct 14
def mCctY : CheckedMember := mCct 15

/-- `mkBound : ∀ (r : RefT)(b : Bytes), CCT r b → BCT`. -/
def mMkBound : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (cst 6) (.pi (cst 3)
      (.pi (cctE (.bvar 1) (.bvar 0)) (cst 10))), none⟩

/-- A ref definition: `mkRef 3 16 <digestConst>`. -/
def mRefD (dRef : Nat) : CheckedMember :=
  mDef (cst 6) (mkRefE 3 16 (cst dRef))
def mI64Ref   : CheckedMember := mRefD 18
def mBoolRef  : CheckedMember := mRefD 19
def mStrRef   : CheckedMember := mRefD 20
def mBytesRef : CheckedMember := mRefD 21

/-- The `CCT` proof for a ground type: `cct<g> <digestConst> <daConst>`
    has type `CCT (mkRef 3 16 <digestConst>) <bytesConst>`; the member
    type states it via the ref const, so `theoremM` admission needs one
    delta step (`boolRef`/`i64Ref`/… unfold to the `mkRef` application). -/
def mThm (ty v : Expr Nat) : CheckedMember := ⟨.theoremM, 0, ty, some v⟩

def mCctPf (rRef cctRef bRef daRef dRef : Nat) : CheckedMember :=
  mThm (cctE (cst rRef) (cst bRef))
    (.app (.app (cst cctRef) (cst dRef)) (cst daRef))
def mCctI64Pf   : CheckedMember := mCctPf 31 26 12 22 18
def mCctBoolPf  : CheckedMember := mCctPf 32 27 13 23 19
def mCctStrPf   : CheckedMember := mCctPf 33 28 14 24 20
def mCctBytesPf : CheckedMember := mCctPf 34 29 15 25 21

/-- `boundBool` & friends: `mkBound <refConst> <bytesConst> <cctPfConst>`. -/
def mBoundD (rRef bRef pfRef : Nat) : CheckedMember :=
  mDef (cst 10) (mkBoundE (cst rRef) (cst bRef) (cst pfRef))
def mBoundI64   : CheckedMember := mBoundD 31 12 35
def mBoundBool  : CheckedMember := mBoundD 32 13 36
def mBoundStr   : CheckedMember := mBoundD 33 14 37
def mBoundBytes : CheckedMember := mBoundD 34 15 38

/-- A bool-value `ValueAt` constructor:
    `∀ (r : RefT)(a : CCT r bytesB), ValueAt (mkBound r bytesB a) <vb>`.
    The type index `bytesB` pins the bound type to the bool binding:
    any `r` with `CCT r "b"` is the bool type's ref (the `DerivedAddr`
    premise inside `cctB` is what carries the digest clause). -/
def mVa (vRef : Nat) : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (cst 6)
      (.pi (cctE (.bvar 0) (cst 13))
        (vaE (mkBoundE (.bvar 1) (cst 13) (.bvar 0)) (cst vRef))), none⟩
def mVaB0 : CheckedMember := mVa 16
def mVaB1 : CheckedMember := mVa 17

/-- `vb<i> : ValueAt boundBool bytesB<i>` — inhabited: the constructor
    applied to the bool ref and its `CCT` proof; the `boundBool`
    definition unfolds to exactly that `mkBound` application. -/
def mVb (vaRef vRef : Nat) : CheckedMember :=
  mThm (vaE (cst 40) (cst vRef))
    (.app (.app (cst vaRef) (cst 32)) (cst 36))
def mVb0 : CheckedMember := mVb 43 16
def mVb1 : CheckedMember := mVb 44 17

/-- The V1 member table, in slot order. -/
def srcMembersV1 : List (Nat × CheckedMember) :=
  [ (0, mNatF), (1, mZero), (2, mSucc), (3, mBytesF), (4, mBNil),
    (5, mBCons), (6, mRefF), (7, mMkRef), (8, mDA), (9, mCCT),
    (10, mBCT), (11, mVA), (12, mBytesI), (13, mBytesB),
    (14, mBytesS), (15, mBytesY), (16, mBytesB0), (17, mBytesB1),
    (18, mDigestI), (19, mDigestB), (20, mDigestS), (21, mDigestY),
    (22, mDaI), (23, mDaB), (24, mDaS), (25, mDaY),
    (26, mCctI), (27, mCctB), (28, mCctS), (29, mCctY), (30, mMkBound),
    (31, mI64Ref), (32, mBoolRef), (33, mStrRef), (34, mBytesRef),
    (35, mCctI64Pf), (36, mCctBoolPf), (37, mCctStrPf),
    (38, mCctBytesPf), (39, mBoundI64), (40, mBoundBool),
    (41, mBoundStr), (42, mBoundBytes), (43, mVaB0), (44, mVaB1),
    (45, mVb0), (46, mVb1) ]

/-- The V1 source environment: fold the table left over `emptyEnv`. -/
def srcEnvV1 : ResolvedEnv :=
  srcMembersV1.foldl (fun E (r, m) => extendEnv E r m) emptyEnv


end Rcic.Scm.SrcTV
