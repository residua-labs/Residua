import rcic.ScmSrcGroupsFunRecEntry
import rcic.ScmSrcGroupsRecIdx

/-! The `FunRecEntry` literals are the judgment's own objects: for each of the four constructors, `equationDoms` and `iotaSchemaAt` at the real recursor admission give `eqDomsLit…` and `rhsLit…`, and the #6160 `iotaLhsType` gives `lhsLit…`. The typings referred to here are the existing 05 §14 evidence (`admRecCCT05`, `admRecValueAt05`) in the judgment's form, through `iotaLhsType_eq_05` (no conversion step). They type the derived equation. They say nothing about main's ι computing it: that is R-NoFunRec (#6151). The typings of these four equations are the `typed` fields at constructors 6/7 of `admRecCCT05` / `admRecCCT` and 5/8 of `admRecValueAt05` / `admRecValueAt` (`ScmSrcGroupsRec`, `ScmSrcGroupsRecVA`, `ScmSrcGroupsRecIdx`); they are not re-exposed here. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecEntry

private abbrev iCctSum : Fin aRecCCT.constructors.length := ⟨6, by decide⟩
private abbrev iCctRec : Fin aRecCCT.constructors.length := ⟨7, by decide⟩
private abbrev iVaList : Fin aRecValueAt.constructors.length := ⟨5, by decide⟩
private abbrev iVaR : Fin aRecValueAt.constructors.length := ⟨8, by decide⟩

kernel_rfl_theorem eqDomsCctSum :
  equationDoms aRecCCT iCctSum = some eqDomsLitCctSum

kernel_rfl_theorem rhsCctSum :
  iotaSchemaAt aRecCCT iCctSum 96 shapesCctSum = some rhsLitCctSum

kernel_rfl_theorem lhsCctSum :
  iotaLhsType (aRecCCT.family.ref + 1 + iCctSum.val)
      (policyFamilyLevels aRecCCT.family) aRecCCT.family.parameters.length
      aRecCCT.constructors.length aRecCCT.family.indices.length
      (aRecCCT.constructorViews iCctSum).fields.length
      (aRecCCT.constructorViews iCctSum).resultIndices = lhsLitCctSum

kernel_rfl_theorem eqDomsCctRec :
  equationDoms aRecCCT iCctRec = some eqDomsLitCctRec

kernel_rfl_theorem rhsCctRec :
  iotaSchemaAt aRecCCT iCctRec 96 shapesCctRec = some rhsLitCctRec

kernel_rfl_theorem lhsCctRec :
  iotaLhsType (aRecCCT.family.ref + 1 + iCctRec.val)
      (policyFamilyLevels aRecCCT.family) aRecCCT.family.parameters.length
      aRecCCT.constructors.length aRecCCT.family.indices.length
      (aRecCCT.constructorViews iCctRec).fields.length
      (aRecCCT.constructorViews iCctRec).resultIndices = lhsLitCctRec

kernel_rfl_theorem eqDomsVaList :
  equationDoms aRecValueAt iVaList = some eqDomsLitVaList

kernel_rfl_theorem rhsVaList :
  iotaSchemaAt aRecValueAt iVaList 96 shapesVaList = some rhsLitVaList

kernel_rfl_theorem lhsVaList :
  iotaLhsType (aRecValueAt.family.ref + 1 + iVaList.val)
      (policyFamilyLevels aRecValueAt.family) aRecValueAt.family.parameters.length
      aRecValueAt.constructors.length aRecValueAt.family.indices.length
      (aRecValueAt.constructorViews iVaList).fields.length
      (aRecValueAt.constructorViews iVaList).resultIndices = lhsLitVaList

kernel_rfl_theorem eqDomsVaR :
  equationDoms aRecValueAt iVaR = some eqDomsLitVaR

kernel_rfl_theorem rhsVaR :
  iotaSchemaAt aRecValueAt iVaR 96 shapesVaR = some rhsLitVaR

kernel_rfl_theorem lhsVaR :
  iotaLhsType (aRecValueAt.family.ref + 1 + iVaR.val)
      (policyFamilyLevels aRecValueAt.family) aRecValueAt.family.parameters.length
      aRecValueAt.constructors.length aRecValueAt.family.indices.length
      (aRecValueAt.constructorViews iVaR).fields.length
      (aRecValueAt.constructorViews iVaR).resultIndices = lhsLitVaR

#print axioms eqDomsCctSum
#print axioms rhsCctSum
#print axioms lhsCctSum
#print axioms eqDomsCctRec
#print axioms rhsCctRec
#print axioms lhsCctRec
#print axioms eqDomsVaList
#print axioms rhsVaList
#print axioms lhsVaList
#print axioms eqDomsVaR
#print axioms rhsVaR
#print axioms lhsVaR

end Rcic.Scm.SrcG.FunRecEntry
