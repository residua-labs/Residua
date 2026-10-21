import rcic.ScmSrcGroupsEnvWfT17
import rcic.RcicTypedScopeCheck

/-!
# InScope re-measure — post-`.lit`-transparency (#6557 item 3, scratch)

For every `.group` step of the `ScmSrcGroups` env chain (envPre 0 → 143),
compute: skeleton built? `groupCheckB` verdict? field-class census
(`plain`/`drec`/`drecD`)? `.lit` leaf count in the ctor member types.

Verdict rule: a group's ScopeCheck premise is `∃ C sk, groupCheckB ... = true
∧ ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false` — i.e., the check
passes AND no `drecD` (R-NoDeltaRec) field appears.
-/

open Rcic.Declarative Rcic.Scm.SrcG

def countDrecD (fs : List FieldT) : Nat :=
  (fs.filter (·.isDrecD)).length

def countDrec (fs : List FieldT) : Nat :=
  (fs.filter fun d => match d with | .drec _ => true | _ => false).length

def countPlain (fs : List FieldT) : Nat :=
  (fs.filter fun d => match d with | .plain _ _ => true | _ => false).length

def countLit : Expr Nat → Nat
  | .lit _ => 1
  | .app f a => countLit f + countLit a
  | .lam A b => countLit A + countLit b
  | .pi A b => countLit A + countLit b
  | .letE A v b => countLit A + countLit v + countLit b
  | _ => 0

/-- (skel built, groupCheckB, nfields, nplain, ndrec, ndrecD, lit leaves). -/
def grpMeasure (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) :
    Bool × Bool × Nat × Nat × Nat × Nat × Nat :=
  match groupSkel? synChecker E 96 f fm ctors rm 0 with
  | none => (false, false, 0, 0, 0, 0, 0)
  | some sk =>
      (true, groupCheckB synChecker E f fm ctors rr rm sk,
        sk.ctors.foldl (fun a k => a + k.fields.length) 0,
        sk.ctors.foldl (fun a k => a + countPlain k.fields) 0,
        sk.ctors.foldl (fun a k => a + countDrec k.fields) 0,
        sk.ctors.foldl (fun a k => a + countDrecD k.fields) 0,
        ctors.foldl (fun a c => a + countLit c.2.mtype) 0)

-- the 26 groups of the chain
#eval grpMeasure (envPre 0) 0 mN [(1, mZero), (2, mSucc)] 3 recN
#eval grpMeasure (envPre 4) 4 mBytes [(5, mBnil), (6, mBcons)] 7 recBytes
#eval grpMeasure (envPre 8) 8 mRefT [(9, mMkRef)] 10 recRefT
#eval grpMeasure (envPre 23) 23 mDA [(24, mDaI), (25, mDaB), (26, mDaS), (27, mDaY), (28, mDaLB)] 29 recDA
#eval grpMeasure (envPre 30) 30 mI [(31, mIPos), (32, mINegS)] 33 recI
#eval grpMeasure (envPre 34) 34 mBL [(35, mBlNil), (36, mBlCons)] 37 recBL
#eval grpMeasure (envPre 38) 38 mFT [(39, mFtNil), (40, mFtCons)] 41 recFT
#eval grpMeasure (envPre 42) 42 mLt [(43, mLtBase), (44, mLtStep)] 45 recLt
#eval grpMeasure (envPre 46) 46 mBC [(47, mCatNil), (48, mCatCons)] 49 recBC
#eval grpMeasure (envPre 50) 50 mDM10 [(51, mDmBase), (52, mDmStep)] 53 recDM10
#eval grpMeasure (envPre 54) 54 mND [(55, mNdBase), (56, mNdStep)] 57 recND
#eval grpMeasure (envPre 58) 58 mNEA [(59, mNeIntro)] 60 recNEA
#eval grpMeasure (envPre 61) 61 mIEA [(62, mIePos), (63, mIeNeg)] 64 recIEA
#eval grpMeasure (envPre 65) 65 mSL [(66, mSlNil), (67, mSlCons)] 68 recSL
#eval grpMeasure (envPre 69) 69 mBLL [(70, mBllNil), (71, mBllCons)] 72 recBLL
#eval grpMeasure (envPre 73) 73 mFTL [(74, mFtlNil), (75, mFtlCons)] 76 recFTL
#eval grpMeasure (envPre 77) 77 mBLC [(78, mBlcNil), (79, mBlcCons)] 80 recBLC
#eval grpMeasure (envPre 81) 81 mSEA [(82, mSeIntro)] 83 recSEA
#eval grpMeasure (envPre 84) 84 mFTE [(85, mFteNil), (86, mFteCons)] 87 recFTE
#eval grpMeasure (envPre 88) 88 mNthB [(89, mNthBHere), (90, mNthBNext)] 91 recNthB
#eval grpMeasure (envPre 92) 92 mNthF [(93, mNthFHere), (94, mNthFNext)] 95 recNthF
#eval grpMeasure (envPre 96) 96 mCCT [(97, mCctI), (98, mCctB), (99, mCctStr), (100, mCctY), (101, mCctL), (102, mCctP), (103, mCctSum), (104, mCctRec)] 105 recCCT
#eval grpMeasure (envPre 106) 106 mBCT [(107, mMkBound)] 108 recBCT
#eval grpMeasure (envPre 125) 125 mNEL [(126, mNelNil), (127, mNelCons)] 128 recNEL
#eval grpMeasure (envPre 129) 129 mNTB [(130, mNtbHere), (131, mNtbNext)] 132 recNTB
#eval grpMeasure (envPre 133) 133 mValueAt [(134, mVaB0), (135, mVaB1), (136, mVaI64), (137, mVaStr), (138, mVaY), (139, mVaList), (140, mVaPair), (141, mVaJ), (142, mVaR)] 143 recValueAt

-- the {1,2} spot-check: a literal can only ever report refs 1/2
#eval containsFamilyFuel (envPre 96) 96 8 (.lit 83)   -- fam 96 → unchanged (false)
#eval containsFamilyFuel (envPre 96) 1 8 (.lit 0)    -- fam 1  → now visible (true)
#eval containsFamilyFuel (envPre 96) 2 8 (.lit 5)    -- fam 2  → now visible (true)
#eval containsFamilyFuel (envPre 96) 5 8 (.lit 0)    -- fam 5  → still false

-- stage-level decomposition for the two failing groups
#eval match (peelPisAll mCCT.mtype).2 with        -- family's result — expect "sort"
      | .sort _ => "sort" | .bvar _ => "bvar" | .const r _ => s!"const {r}"
      | .app _ _ => "app" | .lam _ _ => "lam" | .pi _ _ => "pi"
      | .letE _ _ _ => "letE" | .lit n => s!"lit {n}"
#eval (telLevels? synChecker (envPre 96) mCCT.arity [] (peelPisAll mCCT.mtype).1).isSome
#eval [mCctI, mCctB, mCctStr, mCctY, mCctL, mCctP, mCctSum, mCctRec].map fun c =>
      (ctorSkel? synChecker (envPre 96) 96 96 mCCT [] c).isSome
#eval (synChecker.sortOf (groupEnvT (envPre 96) 96 mCCT [(97, mCctI), (98, mCctB), (99, mCctStr), (100, mCctY), (101, mCctL), (102, mCctP), (103, mCctSum), (104, mCctRec)].reverse) recCCT.arity [] recCCT.mtype).isSome
#eval [mVaB0, mVaB1, mVaI64, mVaStr, mVaY, mVaList, mVaPair, mVaJ, mVaR].map fun c =>
      (ctorSkel? synChecker (envPre 133) 96 133 mValueAt [] c).isSome

-- ctorSkel? internals for mCctSum: fieldsOf? / sortOf / result-unshift
#eval (fieldsOf? synChecker (envPre 96) mCCT.arity 96 (canonLevels mCCT.arity) 0 96 (telCtxT []) []
        ((peelPisAll mCctSum.mtype).1)).isSome
#eval (synChecker.sortOf (extendEnv (envPre 96) 96 mCCT) mCctSum.arity [] mCctSum.mtype).isSome
#eval match fieldsOf? synChecker (envPre 96) mCCT.arity 96 (canonLevels mCCT.arity) 0 96 (telCtxT []) []
        ((peelPisAll mCctSum.mtype).1) with
      | some fs => ((appsSpine (peelPisAll mCctSum.mtype).2).2).mapM
          (unshift? (fs.reverse.map FieldT.isRec) 0) |>.isSome
      | none => false
#eval (fieldsOf? synChecker (envPre 96) mCCT.arity 96 (canonLevels mCCT.arity) 0 96 (telCtxT []) []
        ((peelPisAll mVaList.mtype).1)).isSome
#eval (synChecker.sortOf (extendEnv (envPre 133) 133 mValueAt) mVaList.arity [] mVaList.mtype).isSome

-- per-domain bisect on mCctSum + mCctRec: which domain kills fieldsOf?
#eval ((peelPisAll mCctSum.mtype).1).length
#eval (List.range ((peelPisAll mCctSum.mtype).1).length).map fun k =>
        (fieldsOf? synChecker (envPre 96) mCCT.arity 96 (canonLevels mCCT.arity) 0 96 (telCtxT []) []
          (((peelPisAll mCctSum.mtype).1).take (k+1))).isSome
#eval (List.range ((peelPisAll mCctRec.mtype).1).length).map fun k =>
        (fieldsOf? synChecker (envPre 96) mCCT.arity 96 (canonLevels mCCT.arity) 0 96 (telCtxT []) []
          (((peelPisAll mCctRec.mtype).1).take (k+1))).isSome
#eval (List.range ((peelPisAll mVaList.mtype).1).length).map fun k =>
        (fieldsOf? synChecker (envPre 133) mValueAt.arity 133 (canonLevels mValueAt.arity) 0 96 (telCtxT []) []
          (((peelPisAll mVaList.mtype).1).take (k+1))).isSome
#eval (List.range ((peelPisAll mVaR.mtype).1).length).map fun k =>
        (fieldsOf? synChecker (envPre 133) mValueAt.arity 133 (canonLevels mValueAt.arity) 0 96 (telCtxT []) []
          (((peelPisAll mVaR.mtype).1).take (k+1))).isSome

-- the failing domain itself (mCctSum, idx 14): which sub-check fails?
#eval (recIdx? 96 (canonLevels mCCT.arity) 0 0 ((peelPisAll mCctSum.mtype).1.drop 14 |>.headD (.const 0 []))).isSome
#eval (unshift? [] 0 ((peelPisAll mCctSum.mtype).1.drop 14 |>.headD (.const 0 []))).isSome
#eval (whnfFuel (envPre 96) 96 ((peelPisAll mCctSum.mtype).1.drop 14 |>.headD (.const 0 []))).isSome
#eval match unshift? [] 0 ((peelPisAll mCctSum.mtype).1.drop 14 |>.headD (.const 0 [])) with
      | some D' => (synChecker.sortOf (envPre 96) mCCT.arity [] D').isSome
      | none => false
-- mVaList failing domain idx 13
#eval (recIdx? 133 (canonLevels mValueAt.arity) 0 0 ((peelPisAll mVaList.mtype).1.drop 13 |>.headD (.const 0 []))).isSome
#eval (unshift? [] 0 ((peelPisAll mVaList.mtype).1.drop 13 |>.headD (.const 0 []))).isSome
#eval (whnfFuel (envPre 133) 96 ((peelPisAll mVaList.mtype).1.drop 13 |>.headD (.const 0 []))).isSome

-- lit-leaf census over ctor mtypes, unconditional (the failing groups' lits live
-- inside daE/tB-style defs — surface lits + a direct per-ctor count)
#eval [mCctI, mCctB, mCctStr, mCctY, mCctL, mCctP, mCctSum, mCctRec].map (countLit ·.mtype)
#eval [mVaB0, mVaB1, mVaI64, mVaStr, mVaY, mVaList, mVaPair, mVaJ, mVaR].map (countLit ·.mtype)
