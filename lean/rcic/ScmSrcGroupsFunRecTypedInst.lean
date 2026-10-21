import rcic.ScmSrcGroupsFunRecTyped
import rcic.ScmSrcGroupsKernelRfl

/-! K3c under B2 — instance-level computations for the four function-recursive
constructors.

Step 2 (canonical coverage): `adm.covered` supplies the canonical
`IotaWitnessS` for each constructor; its `schema`/`shapes`/`preMajor`/`fields`
are tied to the `rhsLit`/`shapesLit` literals of `ScmSrcGroupsFunRecEntry` by
the already-checked `rhs…`/`shapes…_eq` kernel facts — no `iotaSchemaAt`
evaluation is repeated here.  `iotaLhsOfS`/`iotaRhsOfS` compute at the
canonical arguments (the `canonLhs…` literal and `rhsLit…` itself: the
canonical `instPrefix` is the identity, checked by `instCanon…`).

Step 3 (closed instances): each `wClosed…` is the covered witness with the
redex arguments replaced by closed `.lit` atoms (`closedPM…`: motive, minors,
indices; `closedF…`: fields).  The lists have the same lengths as the
canonical bvar lists, so every analysis field and premise is reused unchanged
by definitional equality.  `expectedRhs…` is written as data — an independent
by-hand substitution of the closed arguments into `rhsLit…` (no `instPrefix`
in the statement) — and `wClosed…_rhs` proves `iotaRhsOfS` computes to it.
`step…` is the typed ι step `DerivedIotaT.of`.

Step 5: `boundCctSum` instantiates `RecursorGroupIdxAdmittedT.bound` at the
closed cctSum witness (in the recursor's own extended environment, so the
extension premise is the identity). -/

open Rcic.Declarative Rcic.Scm.SrcG Rcic.Scm.SrcG.FunRecEntry
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecTyped


/-! ### CctSum (constructor 6 of aRecCCT, 15 fields) -/

/-- The canonical shape witness for CctSum: the one `covered` builds in the
recursor's derivation scope. -/
def wCctSum : IotaWitnessS (extendEnv (envPre 105) 105 recCCT) :=
  (cctRecIdxAdmittedT.covered ⟨6, by decide⟩).1

theorem covCctSum_recRef : wCctSum.recRef = 105 :=
  (cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.1

theorem covCctSum_ctorIdx : wCctSum.ctorIdx = 6 :=
  (cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.2.2.1

theorem covCctSum_preMajor :
    wCctSum.preMajor = preMajorBvars 0 8 2 15 :=
  (cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.2.2.2.1

theorem covCctSum_fields : wCctSum.fields = fieldBvars 15 :=
  (cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.2.2.2.2.1

/-- The covered witness's field analysis is admission's literal shape list. -/
theorem covCctSum_shapes : wCctSum.shapes = shapesLitCctSum :=
  ((cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.2.2.2.2.2.1 :
    wCctSum.shapes = shapesCctSum).trans shapesCctSum_eq

/-- The covered witness's schema is admission's canonical right-hand side. -/
theorem covCctSum_schema : wCctSum.schema = rhsLitCctSum :=
  Option.some.inj
    ((cctRecIdxAdmittedT.covered ⟨6, by decide⟩).2.2.2.2.2.2.2.symm.trans rhsCctSum)

/-- Closed redex arguments: motive, the 8 minors and the 2 indices as
`.lit` atoms — an honest instance, not a schematic context. -/
def closedPMCctSum : List (Expr Nat) :=
  [.lit 900, .lit 901, .lit 902, .lit 903, .lit 904, .lit 905, .lit 906, .lit 907, .lit 908, .lit 909, .lit 910]

/-- Closed field arguments, one `.lit` atom per field. -/
def closedFCctSum : List (Expr Nat) :=
  [.lit 800, .lit 801, .lit 802, .lit 803, .lit 804, .lit 805, .lit 806, .lit 807, .lit 808, .lit 809, .lit 810, .lit 811, .lit 812, .lit 813, .lit 814]

/-- The independently authored expected reduct: `rhsLit` with the closed
arguments substituted by hand (no `instPrefix` in the statement). -/
def expectedRhsCctSum : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.lit 907) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814)) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.lit 800)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.app (.lit 813) (.bvar 2))) (.bvar 1)) (.app (.app (.app (.lit 814) (.bvar 2)) (.bvar 1)) (.bvar 0))))))

/-- The closed redex as data. -/
def expectedLhsCctSum : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.lit 910)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 103 []) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814))

/-- The canonical redex as data: `rec` applied to the pre-major bvars then
the constructor applied to the field bvars. -/
def canonLhsCctSum : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 103 []) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)) (.bvar 10)) (.bvar 9)) (.bvar 8)) (.bvar 7)) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

kernel_rfl_theorem covCctSum_lhs :
  iotaLhsOfS wCctSum = canonLhsCctSum

-- At the canonical arguments `instPrefix` is the identity on the schema.
kernel_rfl_theorem instCanonCctSum :
  instPrefix (preMajorBvars 0 8 2 15 ++ fieldBvars 15)
    (instantiateLevels [] rhsLitCctSum) = rhsLitCctSum

/-- The canonical computation: the covered redex's reduct is `rhsLit`. -/
theorem covCctSum_rhs : iotaRhsOfS wCctSum = rhsLitCctSum := by
  show instPrefix (wCctSum.preMajor ++ wCctSum.fields)
      (instantiateLevels wCctSum.ls wCctSum.schema) = _
  rw [covCctSum_preMajor, covCctSum_fields, covCctSum_schema]
  exact instCanonCctSum

/-- The closed witness: the covered analysis at the closed arguments.  Only
`preMajor`/`fields` change, and only to equal-length lists, so every premise
is reused by definitional equality. -/
def wClosedCctSum : IotaWitnessS (extendEnv (envPre 105) 105 recCCT) :=
  { wCctSum with
      preMajor := closedPMCctSum
      fields := closedFCctSum
      hpre := by
        show closedPMCctSum.length = wCctSum.nparams + 1 + wCctSum.nMinors + wCctSum.nindices
        rfl
      hnpar := by
        show wCctSum.nparams + closedFCctSum.length = piCount wCctSum.ctorMember.mtype
        rfl }

kernel_rfl_theorem wClosedCctSum_lhs : iotaLhsOfS wClosedCctSum = expectedLhsCctSum

-- `instPrefix` of the closed arguments into the literal schema.
kernel_rfl_theorem instClosedCctSum :
  instPrefix (closedPMCctSum ++ closedFCctSum)
    (instantiateLevels [] rhsLitCctSum) = expectedRhsCctSum

/-- The closed computation: the reduct at the closed arguments is the
independently written `expectedRhs` literal. -/
theorem wClosedCctSum_rhs : iotaRhsOfS wClosedCctSum = expectedRhsCctSum := by
  show instPrefix (wClosedCctSum.preMajor ++ wClosedCctSum.fields)
      (instantiateLevels wClosedCctSum.ls wClosedCctSum.schema) = _
  rw [show wClosedCctSum.preMajor = closedPMCctSum from rfl,
      show wClosedCctSum.fields = closedFCctSum from rfl,
      show wClosedCctSum.schema = rhsLitCctSum from covCctSum_schema]
  exact instClosedCctSum

/-- The typed ι step at the closed redex. -/
def stepCctSum :
    DerivedIotaT (extendEnv (envPre 105) 105 recCCT) expectedLhsCctSum expectedRhsCctSum := by
  rw [← wClosedCctSum_lhs, ← wClosedCctSum_rhs]
  exact .of wClosedCctSum


/-! ### CctRec (constructor 7 of aRecCCT, 15 fields) -/

/-- The canonical shape witness for CctRec: the one `covered` builds in the
recursor's derivation scope. -/
def wCctRec : IotaWitnessS (extendEnv (envPre 105) 105 recCCT) :=
  (cctRecIdxAdmittedT.covered ⟨7, by decide⟩).1

theorem covCctRec_recRef : wCctRec.recRef = 105 :=
  (cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.1

theorem covCctRec_ctorIdx : wCctRec.ctorIdx = 7 :=
  (cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.2.2.1

theorem covCctRec_preMajor :
    wCctRec.preMajor = preMajorBvars 0 8 2 15 :=
  (cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.2.2.2.1

theorem covCctRec_fields : wCctRec.fields = fieldBvars 15 :=
  (cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.2.2.2.2.1

/-- The covered witness's field analysis is admission's literal shape list. -/
theorem covCctRec_shapes : wCctRec.shapes = shapesLitCctRec :=
  ((cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.2.2.2.2.2.1 :
    wCctRec.shapes = shapesCctRec).trans shapesCctRec_eq

/-- The covered witness's schema is admission's canonical right-hand side. -/
theorem covCctRec_schema : wCctRec.schema = rhsLitCctRec :=
  Option.some.inj
    ((cctRecIdxAdmittedT.covered ⟨7, by decide⟩).2.2.2.2.2.2.2.symm.trans rhsCctRec)

/-- Closed redex arguments: motive, the 8 minors and the 2 indices as
`.lit` atoms — an honest instance, not a schematic context. -/
def closedPMCctRec : List (Expr Nat) :=
  [.lit 900, .lit 901, .lit 902, .lit 903, .lit 904, .lit 905, .lit 906, .lit 907, .lit 908, .lit 909, .lit 910]

/-- Closed field arguments, one `.lit` atom per field. -/
def closedFCctRec : List (Expr Nat) :=
  [.lit 800, .lit 801, .lit 802, .lit 803, .lit 804, .lit 805, .lit 806, .lit 807, .lit 808, .lit 809, .lit 810, .lit 811, .lit 812, .lit 813, .lit 814]

/-- The independently authored expected reduct: `rhsLit` with the closed
arguments substituted by hand (no `instPrefix` in the statement). -/
def expectedRhsCctRec : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.lit 908) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814)) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.app (.const 92 []) (.lit 800)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.app (.lit 813) (.bvar 3))) (.bvar 1)) (.app (.app (.app (.app (.lit 814) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)))))))

/-- The closed redex as data. -/
def expectedLhsCctRec : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.lit 910)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 104 []) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814))

/-- The canonical redex as data: `rec` applied to the pre-major bvars then
the constructor applied to the field bvars. -/
def canonLhsCctRec : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 105 []) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 104 []) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)) (.bvar 10)) (.bvar 9)) (.bvar 8)) (.bvar 7)) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

kernel_rfl_theorem covCctRec_lhs :
  iotaLhsOfS wCctRec = canonLhsCctRec

-- At the canonical arguments `instPrefix` is the identity on the schema.
kernel_rfl_theorem instCanonCctRec :
  instPrefix (preMajorBvars 0 8 2 15 ++ fieldBvars 15)
    (instantiateLevels [] rhsLitCctRec) = rhsLitCctRec

/-- The canonical computation: the covered redex's reduct is `rhsLit`. -/
theorem covCctRec_rhs : iotaRhsOfS wCctRec = rhsLitCctRec := by
  show instPrefix (wCctRec.preMajor ++ wCctRec.fields)
      (instantiateLevels wCctRec.ls wCctRec.schema) = _
  rw [covCctRec_preMajor, covCctRec_fields, covCctRec_schema]
  exact instCanonCctRec

/-- The closed witness: the covered analysis at the closed arguments.  Only
`preMajor`/`fields` change, and only to equal-length lists, so every premise
is reused by definitional equality. -/
def wClosedCctRec : IotaWitnessS (extendEnv (envPre 105) 105 recCCT) :=
  { wCctRec with
      preMajor := closedPMCctRec
      fields := closedFCctRec
      hpre := by
        show closedPMCctRec.length = wCctRec.nparams + 1 + wCctRec.nMinors + wCctRec.nindices
        rfl
      hnpar := by
        show wCctRec.nparams + closedFCctRec.length = piCount wCctRec.ctorMember.mtype
        rfl }

kernel_rfl_theorem wClosedCctRec_lhs : iotaLhsOfS wClosedCctRec = expectedLhsCctRec

-- `instPrefix` of the closed arguments into the literal schema.
kernel_rfl_theorem instClosedCctRec :
  instPrefix (closedPMCctRec ++ closedFCctRec)
    (instantiateLevels [] rhsLitCctRec) = expectedRhsCctRec

/-- The closed computation: the reduct at the closed arguments is the
independently written `expectedRhs` literal. -/
theorem wClosedCctRec_rhs : iotaRhsOfS wClosedCctRec = expectedRhsCctRec := by
  show instPrefix (wClosedCctRec.preMajor ++ wClosedCctRec.fields)
      (instantiateLevels wClosedCctRec.ls wClosedCctRec.schema) = _
  rw [show wClosedCctRec.preMajor = closedPMCctRec from rfl,
      show wClosedCctRec.fields = closedFCctRec from rfl,
      show wClosedCctRec.schema = rhsLitCctRec from covCctRec_schema]
  exact instClosedCctRec

/-- The typed ι step at the closed redex. -/
def stepCctRec :
    DerivedIotaT (extendEnv (envPre 105) 105 recCCT) expectedLhsCctRec expectedRhsCctRec := by
  rw [← wClosedCctRec_lhs, ← wClosedCctRec_rhs]
  exact .of wClosedCctRec


/-! ### VaList (constructor 5 of aRecValueAt, 19 fields) -/

/-- The canonical shape witness for VaList: the one `covered` builds in the
recursor's derivation scope. -/
def wVaList : IotaWitnessS (extendEnv (envPre 143) 143 recValueAt) :=
  (vaRecIdxAdmittedT.covered ⟨5, by decide⟩).1

theorem covVaList_recRef : wVaList.recRef = 143 :=
  (vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.1

theorem covVaList_ctorIdx : wVaList.ctorIdx = 5 :=
  (vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.2.2.1

theorem covVaList_preMajor :
    wVaList.preMajor = preMajorBvars 0 9 2 19 :=
  (vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.2.2.2.1

theorem covVaList_fields : wVaList.fields = fieldBvars 19 :=
  (vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.2.2.2.2.1

/-- The covered witness's field analysis is admission's literal shape list. -/
theorem covVaList_shapes : wVaList.shapes = shapesLitVaList :=
  ((vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.2.2.2.2.2.1 :
    wVaList.shapes = shapesVaList).trans shapesVaList_eq

/-- The covered witness's schema is admission's canonical right-hand side. -/
theorem covVaList_schema : wVaList.schema = rhsLitVaList :=
  Option.some.inj
    ((vaRecIdxAdmittedT.covered ⟨5, by decide⟩).2.2.2.2.2.2.2.symm.trans rhsVaList)

/-- Closed redex arguments: motive, the 9 minors and the 2 indices as
`.lit` atoms — an honest instance, not a schematic context. -/
def closedPMVaList : List (Expr Nat) :=
  [.lit 900, .lit 901, .lit 902, .lit 903, .lit 904, .lit 905, .lit 906, .lit 907, .lit 908, .lit 909, .lit 910, .lit 911]

/-- Closed field arguments, one `.lit` atom per field. -/
def closedFVaList : List (Expr Nat) :=
  [.lit 800, .lit 801, .lit 802, .lit 803, .lit 804, .lit 805, .lit 806, .lit 807, .lit 808, .lit 809, .lit 810, .lit 811, .lit 812, .lit 813, .lit 814, .lit 815, .lit 816, .lit 817, .lit 818]

/-- The independently authored expected reduct: `rhsLit` with the closed
arguments substituted by hand (no `instPrefix` in the statement). -/
def expectedRhsVaList : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.lit 906) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.lit 804)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.app (.app (.app (.const 107 []) (.lit 800)) (.lit 801)) (.lit 812))) (.bvar 1)) (.app (.app (.app (.lit 813) (.bvar 2)) (.bvar 1)) (.bvar 0))))))) (.lit 814)) (.lit 815)) (.lit 816)) (.lit 817)) (.lit 818)

/-- The closed redex as data. -/
def expectedLhsVaList : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.lit 910)) (.lit 911)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 139 []) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814)) (.lit 815)) (.lit 816)) (.lit 817)) (.lit 818))

/-- The canonical redex as data: `rec` applied to the pre-major bvars then
the constructor applied to the field bvars. -/
def canonLhsVaList : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.bvar 30)) (.bvar 29)) (.bvar 28)) (.bvar 27)) (.bvar 26)) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 139 []) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)) (.bvar 10)) (.bvar 9)) (.bvar 8)) (.bvar 7)) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

kernel_rfl_theorem covVaList_lhs :
  iotaLhsOfS wVaList = canonLhsVaList

-- At the canonical arguments `instPrefix` is the identity on the schema.
kernel_rfl_theorem instCanonVaList :
  instPrefix (preMajorBvars 0 9 2 19 ++ fieldBvars 19)
    (instantiateLevels [] rhsLitVaList) = rhsLitVaList

/-- The canonical computation: the covered redex's reduct is `rhsLit`. -/
theorem covVaList_rhs : iotaRhsOfS wVaList = rhsLitVaList := by
  show instPrefix (wVaList.preMajor ++ wVaList.fields)
      (instantiateLevels wVaList.ls wVaList.schema) = _
  rw [covVaList_preMajor, covVaList_fields, covVaList_schema]
  exact instCanonVaList

/-- The closed witness: the covered analysis at the closed arguments.  Only
`preMajor`/`fields` change, and only to equal-length lists, so every premise
is reused by definitional equality. -/
def wClosedVaList : IotaWitnessS (extendEnv (envPre 143) 143 recValueAt) :=
  { wVaList with
      preMajor := closedPMVaList
      fields := closedFVaList
      hpre := by
        show closedPMVaList.length = wVaList.nparams + 1 + wVaList.nMinors + wVaList.nindices
        rfl
      hnpar := by
        show wVaList.nparams + closedFVaList.length = piCount wVaList.ctorMember.mtype
        rfl }

kernel_rfl_theorem wClosedVaList_lhs : iotaLhsOfS wClosedVaList = expectedLhsVaList

-- `instPrefix` of the closed arguments into the literal schema.
kernel_rfl_theorem instClosedVaList :
  instPrefix (closedPMVaList ++ closedFVaList)
    (instantiateLevels [] rhsLitVaList) = expectedRhsVaList

/-- The closed computation: the reduct at the closed arguments is the
independently written `expectedRhs` literal. -/
theorem wClosedVaList_rhs : iotaRhsOfS wClosedVaList = expectedRhsVaList := by
  show instPrefix (wClosedVaList.preMajor ++ wClosedVaList.fields)
      (instantiateLevels wClosedVaList.ls wClosedVaList.schema) = _
  rw [show wClosedVaList.preMajor = closedPMVaList from rfl,
      show wClosedVaList.fields = closedFVaList from rfl,
      show wClosedVaList.schema = rhsLitVaList from covVaList_schema]
  exact instClosedVaList

/-- The typed ι step at the closed redex. -/
def stepVaList :
    DerivedIotaT (extendEnv (envPre 143) 143 recValueAt) expectedLhsVaList expectedRhsVaList := by
  rw [← wClosedVaList_lhs, ← wClosedVaList_rhs]
  exact .of wClosedVaList


/-! ### VaR (constructor 8 of aRecValueAt, 26 fields) -/

/-- The canonical shape witness for VaR: the one `covered` builds in the
recursor's derivation scope. -/
def wVaR : IotaWitnessS (extendEnv (envPre 143) 143 recValueAt) :=
  (vaRecIdxAdmittedT.covered ⟨8, by decide⟩).1

theorem covVaR_recRef : wVaR.recRef = 143 :=
  (vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.1

theorem covVaR_ctorIdx : wVaR.ctorIdx = 8 :=
  (vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.2.2.1

theorem covVaR_preMajor :
    wVaR.preMajor = preMajorBvars 0 9 2 26 :=
  (vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.2.2.2.1

theorem covVaR_fields : wVaR.fields = fieldBvars 26 :=
  (vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.2.2.2.2.1

/-- The covered witness's field analysis is admission's literal shape list. -/
theorem covVaR_shapes : wVaR.shapes = shapesLitVaR :=
  ((vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.2.2.2.2.2.1 :
    wVaR.shapes = shapesVaR).trans shapesVaR_eq

/-- The covered witness's schema is admission's canonical right-hand side. -/
theorem covVaR_schema : wVaR.schema = rhsLitVaR :=
  Option.some.inj
    ((vaRecIdxAdmittedT.covered ⟨8, by decide⟩).2.2.2.2.2.2.2.symm.trans rhsVaR)

/-- Closed redex arguments: motive, the 9 minors and the 2 indices as
`.lit` atoms — an honest instance, not a schematic context. -/
def closedPMVaR : List (Expr Nat) :=
  [.lit 900, .lit 901, .lit 902, .lit 903, .lit 904, .lit 905, .lit 906, .lit 907, .lit 908, .lit 909, .lit 910, .lit 911]

/-- Closed field arguments, one `.lit` atom per field. -/
def closedFVaR : List (Expr Nat) :=
  [.lit 800, .lit 801, .lit 802, .lit 803, .lit 804, .lit 805, .lit 806, .lit 807, .lit 808, .lit 809, .lit 810, .lit 811, .lit 812, .lit 813, .lit 814, .lit 815, .lit 816, .lit 817, .lit 818, .lit 819, .lit 820, .lit 821, .lit 822, .lit 823, .lit 824, .lit 825]

/-- The independently authored expected reduct: `rhsLit` with the closed
arguments substituted by hand (no `instPrefix` in the statement). -/
def expectedRhsVaR : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.lit 909) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814)) (.lit 815)) (.lit 816)) (.lit 817)) (.lit 818)) (.lit 819)) (.lit 820)) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.app (.const 92 []) (.lit 800)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.lit 815)) (.bvar 4)) (.bvar 0)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.app (.app (.app (.const 107 []) (.app (.lit 813) (.bvar 5))) (.bvar 3)) (.app (.app (.app (.app (.lit 814) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)))) (.bvar 1)) (.app (.app (.app (.app (.app (.app (.lit 820) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)))))))))) (.lit 821)) (.lit 822)) (.lit 823)) (.lit 824)) (.lit 825)

/-- The closed redex as data. -/
def expectedLhsVaR : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.lit 900)) (.lit 901)) (.lit 902)) (.lit 903)) (.lit 904)) (.lit 905)) (.lit 906)) (.lit 907)) (.lit 908)) (.lit 909)) (.lit 910)) (.lit 911)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 142 []) (.lit 800)) (.lit 801)) (.lit 802)) (.lit 803)) (.lit 804)) (.lit 805)) (.lit 806)) (.lit 807)) (.lit 808)) (.lit 809)) (.lit 810)) (.lit 811)) (.lit 812)) (.lit 813)) (.lit 814)) (.lit 815)) (.lit 816)) (.lit 817)) (.lit 818)) (.lit 819)) (.lit 820)) (.lit 821)) (.lit 822)) (.lit 823)) (.lit 824)) (.lit 825))

/-- The canonical redex as data: `rec` applied to the pre-major bvars then
the constructor applied to the field bvars. -/
def canonLhsVaR : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 143 []) (.bvar 37)) (.bvar 36)) (.bvar 35)) (.bvar 34)) (.bvar 33)) (.bvar 32)) (.bvar 31)) (.bvar 30)) (.bvar 29)) (.bvar 28)) (.bvar 27)) (.bvar 26)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 142 []) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)) (.bvar 10)) (.bvar 9)) (.bvar 8)) (.bvar 7)) (.bvar 6)) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

kernel_rfl_theorem covVaR_lhs :
  iotaLhsOfS wVaR = canonLhsVaR

-- At the canonical arguments `instPrefix` is the identity on the schema.
kernel_rfl_theorem instCanonVaR :
  instPrefix (preMajorBvars 0 9 2 26 ++ fieldBvars 26)
    (instantiateLevels [] rhsLitVaR) = rhsLitVaR

/-- The canonical computation: the covered redex's reduct is `rhsLit`. -/
theorem covVaR_rhs : iotaRhsOfS wVaR = rhsLitVaR := by
  show instPrefix (wVaR.preMajor ++ wVaR.fields)
      (instantiateLevels wVaR.ls wVaR.schema) = _
  rw [covVaR_preMajor, covVaR_fields, covVaR_schema]
  exact instCanonVaR

/-- The closed witness: the covered analysis at the closed arguments.  Only
`preMajor`/`fields` change, and only to equal-length lists, so every premise
is reused by definitional equality. -/
def wClosedVaR : IotaWitnessS (extendEnv (envPre 143) 143 recValueAt) :=
  { wVaR with
      preMajor := closedPMVaR
      fields := closedFVaR
      hpre := by
        show closedPMVaR.length = wVaR.nparams + 1 + wVaR.nMinors + wVaR.nindices
        rfl
      hnpar := by
        show wVaR.nparams + closedFVaR.length = piCount wVaR.ctorMember.mtype
        rfl }

kernel_rfl_theorem wClosedVaR_lhs : iotaLhsOfS wClosedVaR = expectedLhsVaR

-- `instPrefix` of the closed arguments into the literal schema.
kernel_rfl_theorem instClosedVaR :
  instPrefix (closedPMVaR ++ closedFVaR)
    (instantiateLevels [] rhsLitVaR) = expectedRhsVaR

/-- The closed computation: the reduct at the closed arguments is the
independently written `expectedRhs` literal. -/
theorem wClosedVaR_rhs : iotaRhsOfS wClosedVaR = expectedRhsVaR := by
  show instPrefix (wClosedVaR.preMajor ++ wClosedVaR.fields)
      (instantiateLevels wClosedVaR.ls wClosedVaR.schema) = _
  rw [show wClosedVaR.preMajor = closedPMVaR from rfl,
      show wClosedVaR.fields = closedFVaR from rfl,
      show wClosedVaR.schema = rhsLitVaR from covVaR_schema]
  exact instClosedVaR

/-- The typed ι step at the closed redex. -/
def stepVaR :
    DerivedIotaT (extendEnv (envPre 143) 143 recValueAt) expectedLhsVaR expectedRhsVaR := by
  rw [← wClosedVaR_lhs, ← wClosedVaR_rhs]
  exact .of wClosedVaR


/-! ### Step 5 — `bound` at a closed witness -/

/-- `RecursorGroupIdxAdmittedT.bound` instantiated at the closed cctSum
witness in the recursor's own extended environment.  It recovers the
constructor index (6), the literal field analysis, and the canonical schema
equation for the witness. -/
theorem boundCctSum :
    ∃ i : Fin aRecCCT.constructors.length, wClosedCctSum.ctorIdx = i.val ∧
      wClosedCctSum.shapes = cctIotaClause.shapesAt i ∧
      iotaSchemaAt aRecCCT i (cctIotaClause.fuelAt i) (cctIotaClause.shapesAt i) =
        some wClosedCctSum.schema :=
  cctRecIdxAdmittedT.bound (fun _ _ h => h) wClosedCctSum rfl rfl

/-- The recovered index is cctSum's (`Exists.choose` would need
`Classical.choice`; eliminating into `Prop` does not). -/
theorem boundCctSum_idx :
    ∃ i : Fin aRecCCT.constructors.length, i.val = 6 ∧
      wClosedCctSum.shapes = cctIotaClause.shapesAt i ∧
      iotaSchemaAt aRecCCT i (cctIotaClause.fuelAt i) (cctIotaClause.shapesAt i) =
        some wClosedCctSum.schema := by
  rcases boundCctSum with ⟨i, hi, hs, hsc⟩
  exact ⟨i, hi.symm, hs, hsc⟩

end Rcic.Scm.SrcG.FunRecTyped
