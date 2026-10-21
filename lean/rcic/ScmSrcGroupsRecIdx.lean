import rcic.ScmSrcGroupsRec
import rcic.ScmSrcGroupsRecVA

/-! The 19 indexed recursors, admitted in the judgment's own form.

#6160 (`b2221de20f`) changed `iotaLhsType` (RcicIndGroupJudgment) to state each ι equation's type as the motive at the constructor's RESULT INDICES. With no parameters that is exactly the 05 §14 type `iotaLhsType05` (`iotaLhsType_eq_05`): lifting the result indices into the equation's context is the identity, because they mention only fields. So each `RecursorAdmitted05` already carries the judgment's `IotaDescriptorClause`. Its `typed` derivations are retyped by an equation between the two type expressions, with no `HasTy.conv` step and nothing from `RcicUntypedConvCollapse`, which is not in this module's import closure. Before #6160 the judgment's clause put the index binders in that slot and could be met only through the collapsed `Conv` (defect 1; `daI_judgmentForm_mismatch`, retired). -/

open Rcic.Declarative Rcic.Machine
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

theorem iotaLhsType_eq_05 {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {i : Fin a.constructors.length}
    (hp : a.family.parameters = [])
    (hres : (a.constructorViews i).resultIndices.map
        (lift (a.constructorViews i).fields.length
          (1 + a.constructors.length + a.family.indices.length)) =
      (a.constructorViews i).resultIndices) :
    iotaLhsType (a.family.ref + 1 + i.val) (policyFamilyLevels a.family)
        a.family.parameters.length a.constructors.length a.family.indices.length
        (a.constructorViews i).fields.length (a.constructorViews i).resultIndices =
      iotaLhsType05 a i := by
  unfold iotaLhsType iotaLhsType05
  simp only [hp, List.length_nil, policyParameterLocals, List.range_zero,
    List.reverse_nil, List.map_nil, List.nil_append, hres]

def IotaDescriptorClause05.toJudgment {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    (c : IotaDescriptorClause05 E a)
    (heq : ∀ i, iotaLhsType (a.family.ref + 1 + i.val)
        (policyFamilyLevels a.family) a.family.parameters.length
        a.constructors.length a.family.indices.length
        (a.constructorViews i).fields.length (a.constructorViews i).resultIndices =
      iotaLhsType05 a i) : IotaDescriptorClause E a where
  signatureOnly := c.signatureOnly
  shapesAt := c.shapesAt
  fuelAt := c.fuelAt
  analyzed := c.analyzed
  typed := fun i => by
    simpa only [IotaEquationTyped, IotaEquationTyped05, iotaEquationType, heq i] using c.typed i

def RecursorAdmitted05.toJudgment {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (R : RecursorAdmitted05 E r m)
    (heq : ∀ i, iotaLhsType (R.a.family.ref + 1 + i.val)
        (policyFamilyLevels R.a.family) R.a.family.parameters.length
        R.a.constructors.length R.a.family.indices.length
        (R.a.constructorViews i).fields.length
        (R.a.constructorViews i).resultIndices = iotaLhsType05 R.a i) :
    IndGroupAdmitted E r m :=
  .recursor R.a R.hfresh R.h04 R.h07 R.h08 R.h12
    (R.h14.toJudgment heq)

private theorem hresDA (i : Fin aRecDA.constructors.length) :
    (aRecDA.constructorViews i).resultIndices.map
      (lift (aRecDA.constructorViews i).fields.length
        (1 + aRecDA.constructors.length + aRecDA.family.indices.length)) =
    (aRecDA.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨k+5, h⟩ => exact absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega)

def admRecDA : IndGroupAdmitted (envPre 29) 29 recDA :=
  admRecDA05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresDA i)

private theorem hresLt (i : Fin aRecLt.constructors.length) :
    (aRecLt.constructorViews i).resultIndices.map
      (lift (aRecLt.constructorViews i).fields.length
        (1 + aRecLt.constructors.length + aRecLt.family.indices.length)) =
    (aRecLt.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega)

def admRecLt : IndGroupAdmitted (envPre 45) 45 recLt :=
  admRecLt05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresLt i)

private theorem hresBC (i : Fin aRecBC.constructors.length) :
    (aRecBC.constructorViews i).resultIndices.map
      (lift (aRecBC.constructorViews i).fields.length
        (1 + aRecBC.constructors.length + aRecBC.family.indices.length)) =
    (aRecBC.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega)

def admRecBC : IndGroupAdmitted (envPre 49) 49 recBC :=
  admRecBC05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresBC i)

private theorem hresDM10 (i : Fin aRecDM10.constructors.length) :
    (aRecDM10.constructorViews i).resultIndices.map
      (lift (aRecDM10.constructorViews i).fields.length
        (1 + aRecDM10.constructors.length + aRecDM10.family.indices.length)) =
    (aRecDM10.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega)

def admRecDM10 : IndGroupAdmitted (envPre 53) 53 recDM10 :=
  admRecDM1005.toJudgment fun i => iotaLhsType_eq_05 rfl (hresDM10 i)

private theorem hresND (i : Fin aRecND.constructors.length) :
    (aRecND.constructorViews i).resultIndices.map
      (lift (aRecND.constructorViews i).fields.length
        (1 + aRecND.constructors.length + aRecND.family.indices.length)) =
    (aRecND.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecND.constructors.length = 2 := rfl; omega)

def admRecND : IndGroupAdmitted (envPre 57) 57 recND :=
  admRecND05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresND i)

private theorem hresNEA (i : Fin aRecNEA.constructors.length) :
    (aRecNEA.constructorViews i).resultIndices.map
      (lift (aRecNEA.constructorViews i).fields.length
        (1 + aRecNEA.constructors.length + aRecNEA.family.indices.length)) =
    (aRecNEA.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨k+1, h⟩ => exact absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega)

def admRecNEA : IndGroupAdmitted (envPre 60) 60 recNEA :=
  admRecNEA05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresNEA i)

private theorem hresIEA (i : Fin aRecIEA.constructors.length) :
    (aRecIEA.constructorViews i).resultIndices.map
      (lift (aRecIEA.constructorViews i).fields.length
        (1 + aRecIEA.constructors.length + aRecIEA.family.indices.length)) =
    (aRecIEA.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega)

def admRecIEA : IndGroupAdmitted (envPre 64) 64 recIEA :=
  admRecIEA05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresIEA i)

private theorem hresSL (i : Fin aRecSL.constructors.length) :
    (aRecSL.constructorViews i).resultIndices.map
      (lift (aRecSL.constructorViews i).fields.length
        (1 + aRecSL.constructors.length + aRecSL.family.indices.length)) =
    (aRecSL.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega)

def admRecSL : IndGroupAdmitted (envPre 68) 68 recSL :=
  admRecSL05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresSL i)

private theorem hresBLL (i : Fin aRecBLL.constructors.length) :
    (aRecBLL.constructorViews i).resultIndices.map
      (lift (aRecBLL.constructorViews i).fields.length
        (1 + aRecBLL.constructors.length + aRecBLL.family.indices.length)) =
    (aRecBLL.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega)

def admRecBLL : IndGroupAdmitted (envPre 72) 72 recBLL :=
  admRecBLL05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresBLL i)

private theorem hresFTL (i : Fin aRecFTL.constructors.length) :
    (aRecFTL.constructorViews i).resultIndices.map
      (lift (aRecFTL.constructorViews i).fields.length
        (1 + aRecFTL.constructors.length + aRecFTL.family.indices.length)) =
    (aRecFTL.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega)

def admRecFTL : IndGroupAdmitted (envPre 76) 76 recFTL :=
  admRecFTL05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresFTL i)

private theorem hresBLC (i : Fin aRecBLC.constructors.length) :
    (aRecBLC.constructorViews i).resultIndices.map
      (lift (aRecBLC.constructorViews i).fields.length
        (1 + aRecBLC.constructors.length + aRecBLC.family.indices.length)) =
    (aRecBLC.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega)

def admRecBLC : IndGroupAdmitted (envPre 80) 80 recBLC :=
  admRecBLC05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresBLC i)

private theorem hresSEA (i : Fin aRecSEA.constructors.length) :
    (aRecSEA.constructorViews i).resultIndices.map
      (lift (aRecSEA.constructorViews i).fields.length
        (1 + aRecSEA.constructors.length + aRecSEA.family.indices.length)) =
    (aRecSEA.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨k+1, h⟩ => exact absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega)

def admRecSEA : IndGroupAdmitted (envPre 83) 83 recSEA :=
  admRecSEA05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresSEA i)

private theorem hresFTE (i : Fin aRecFTE.constructors.length) :
    (aRecFTE.constructorViews i).resultIndices.map
      (lift (aRecFTE.constructorViews i).fields.length
        (1 + aRecFTE.constructors.length + aRecFTE.family.indices.length)) =
    (aRecFTE.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega)

def admRecFTE : IndGroupAdmitted (envPre 87) 87 recFTE :=
  admRecFTE05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresFTE i)

private theorem hresNthB (i : Fin aRecNthB.constructors.length) :
    (aRecNthB.constructorViews i).resultIndices.map
      (lift (aRecNthB.constructorViews i).fields.length
        (1 + aRecNthB.constructors.length + aRecNthB.family.indices.length)) =
    (aRecNthB.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega)

def admRecNthB : IndGroupAdmitted (envPre 91) 91 recNthB :=
  admRecNthB05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresNthB i)

private theorem hresNthF (i : Fin aRecNthF.constructors.length) :
    (aRecNthF.constructorViews i).resultIndices.map
      (lift (aRecNthF.constructorViews i).fields.length
        (1 + aRecNthF.constructors.length + aRecNthF.family.indices.length)) =
    (aRecNthF.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega)

def admRecNthF : IndGroupAdmitted (envPre 95) 95 recNthF :=
  admRecNthF05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresNthF i)

private theorem hresCCT (i : Fin aRecCCT.constructors.length) :
    (aRecCCT.constructorViews i).resultIndices.map
      (lift (aRecCCT.constructorViews i).fields.length
        (1 + aRecCCT.constructors.length + aRecCCT.family.indices.length)) =
    (aRecCCT.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨k+8, h⟩ => exact absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)

def admRecCCT : IndGroupAdmitted (envPre 105) 105 recCCT :=
  admRecCCT05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresCCT i)

private theorem hresNEL (i : Fin aRecNEL.constructors.length) :
    (aRecNEL.constructorViews i).resultIndices.map
      (lift (aRecNEL.constructorViews i).fields.length
        (1 + aRecNEL.constructors.length + aRecNEL.family.indices.length)) =
    (aRecNEL.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega)

def admRecNEL : IndGroupAdmitted (envPre 128) 128 recNEL :=
  admRecNEL05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresNEL i)

private theorem hresNTB (i : Fin aRecNTB.constructors.length) :
    (aRecNTB.constructorViews i).resultIndices.map
      (lift (aRecNTB.constructorViews i).fields.length
        (1 + aRecNTB.constructors.length + aRecNTB.family.indices.length)) =
    (aRecNTB.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨k+2, h⟩ => exact absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega)

def admRecNTB : IndGroupAdmitted (envPre 132) 132 recNTB :=
  admRecNTB05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresNTB i)

private theorem hresValueAt (i : Fin aRecValueAt.constructors.length) :
    (aRecValueAt.constructorViews i).resultIndices.map
      (lift (aRecValueAt.constructorViews i).fields.length
        (1 + aRecValueAt.constructors.length + aRecValueAt.family.indices.length)) =
    (aRecValueAt.constructorViews i).resultIndices := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl
  | ⟨k+9, h⟩ => exact absurd h (by have : aRecValueAt.constructors.length = 9 := rfl; omega)

def admRecValueAt : IndGroupAdmitted (envPre 143) 143 recValueAt :=
  admRecValueAt05.toJudgment fun i => iotaLhsType_eq_05 rfl (hresValueAt i)

#print axioms Rcic.Scm.SrcG.iotaLhsType_eq_05
#print axioms Rcic.Scm.SrcG.IotaDescriptorClause05.toJudgment
#print axioms Rcic.Scm.SrcG.RecursorAdmitted05.toJudgment
#print axioms Rcic.Scm.SrcG.admRecDA
#print axioms Rcic.Scm.SrcG.admRecLt
#print axioms Rcic.Scm.SrcG.admRecBC
#print axioms Rcic.Scm.SrcG.admRecDM10
#print axioms Rcic.Scm.SrcG.admRecND
#print axioms Rcic.Scm.SrcG.admRecNEA
#print axioms Rcic.Scm.SrcG.admRecIEA
#print axioms Rcic.Scm.SrcG.admRecSL
#print axioms Rcic.Scm.SrcG.admRecBLL
#print axioms Rcic.Scm.SrcG.admRecFTL
#print axioms Rcic.Scm.SrcG.admRecBLC
#print axioms Rcic.Scm.SrcG.admRecSEA
#print axioms Rcic.Scm.SrcG.admRecFTE
#print axioms Rcic.Scm.SrcG.admRecNthB
#print axioms Rcic.Scm.SrcG.admRecNthF
#print axioms Rcic.Scm.SrcG.admRecCCT
#print axioms Rcic.Scm.SrcG.admRecNEL
#print axioms Rcic.Scm.SrcG.admRecNTB
#print axioms Rcic.Scm.SrcG.admRecValueAt

end Rcic.Scm.SrcG
