import rcic.ScmSrcGroupsFunRecTypedInst
import rcic.ScmSrcGroupsKernelRfl

/-! K3c under B2 — the typed checked ι equations for the four
function-recursive constructors.

Step 4: `IotaEquationTypedT` asks for the schema reduct to be typed, in the
typed judgment `HasTyT`, at the equation type `iotaEquationType` (the motive
at the constructor's result indices and the constructor application), in the
equation's context `assumptionCtx (equationDoms a i)` and the derivation scope
`extendEnv E r m`.  Admission's own clause carries the same typing in the
legacy untyped `HasTy`; here the certified syntactic checker `synCheck`
produces the `HasTyT` derivation itself.

Each constructor contributes:

- `synTypedCheck…` — a kernel-checked `isSome` fact for `synCheck` at the
  literal context/reduct/type (the evaluation is the checker's structural
  traversal of `rhsLit…`; it runs once, in the kernel);
- `synTyped…` — the extracted `HasTyT` derivation, as data;
- `eqTyped…` — `IotaEquationTypedT` for the constructor, stated at the
  literal fuel `96` and shape list (equal to the clause's `fuelAt`/`shapesAt`
  by definition), discharged by rewriting the scrutinees with the already
  checked `eqDoms…`/`rhs…` facts — the elaborator never evaluates
  `iotaSchemaAt`;
- `eqTyped…Clause` — the same fact under the clause's `fuelAt`/`shapesAt`
  selectors, the form `IndGroupTypedT` consumes. -/

open Rcic.Declarative Rcic.Scm.SrcG Rcic.Scm.SrcG.FunRecEntry
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecTyped

/-! ### cctSum -/

kernel_rfl_theorem synTypedCheckCctSum :
  (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity
    (assumptionCtx eqDomsLitCctSum) rhsLitCctSum
    (iotaEquationType aRecCCT ⟨6, by decide⟩)).isSome = true

/-- The certified `HasTyT` derivation for cctSum's ι equation. -/
def synTypedCctSum :
    HasTyT (extendEnv (envPre 105) 105 recCCT) recCCT.arity
      (assumptionCtx eqDomsLitCctSum) rhsLitCctSum
      (iotaEquationType aRecCCT ⟨6, by decide⟩) :=
  (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity
    (assumptionCtx eqDomsLitCctSum) rhsLitCctSum
    (iotaEquationType aRecCCT ⟨6, by decide⟩)).get synTypedCheckCctSum

/-- The typed ι equation for cctSum: the schema reduct carries a `HasTyT`
derivation at the equation type. -/
theorem eqTypedCctSum :
    IotaEquationTypedT aRecCCT ⟨6, by decide⟩ 96 shapesCctSum := by
  unfold IotaEquationTypedT
  rw [eqDomsCctSum, rhsCctSum]
  exact ⟨synTypedCctSum⟩

/-- … under the descriptor clause's selectors. -/
theorem eqTypedCctSumClause :
    IotaEquationTypedT aRecCCT ⟨6, by decide⟩
      (cctIotaClause.fuelAt ⟨6, by decide⟩) (cctIotaClause.shapesAt ⟨6, by decide⟩) :=
  eqTypedCctSum

/-! ### cctRec -/

kernel_rfl_theorem synTypedCheckCctRec :
  (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity
    (assumptionCtx eqDomsLitCctRec) rhsLitCctRec
    (iotaEquationType aRecCCT ⟨7, by decide⟩)).isSome = true

/-- The certified `HasTyT` derivation for cctRec's ι equation. -/
def synTypedCctRec :
    HasTyT (extendEnv (envPre 105) 105 recCCT) recCCT.arity
      (assumptionCtx eqDomsLitCctRec) rhsLitCctRec
      (iotaEquationType aRecCCT ⟨7, by decide⟩) :=
  (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity
    (assumptionCtx eqDomsLitCctRec) rhsLitCctRec
    (iotaEquationType aRecCCT ⟨7, by decide⟩)).get synTypedCheckCctRec

/-- The typed ι equation for cctRec. -/
theorem eqTypedCctRec :
    IotaEquationTypedT aRecCCT ⟨7, by decide⟩ 96 shapesCctRec := by
  unfold IotaEquationTypedT
  rw [eqDomsCctRec, rhsCctRec]
  exact ⟨synTypedCctRec⟩

/-- … under the descriptor clause's selectors. -/
theorem eqTypedCctRecClause :
    IotaEquationTypedT aRecCCT ⟨7, by decide⟩
      (cctIotaClause.fuelAt ⟨7, by decide⟩) (cctIotaClause.shapesAt ⟨7, by decide⟩) :=
  eqTypedCctRec

/-! ### vaList -/

kernel_rfl_theorem synTypedCheckVaList :
  (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
    (assumptionCtx eqDomsLitVaList) rhsLitVaList
    (iotaEquationType aRecValueAt ⟨5, by decide⟩)).isSome = true

/-- The certified `HasTyT` derivation for vaList's ι equation. -/
def synTypedVaList :
    HasTyT (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
      (assumptionCtx eqDomsLitVaList) rhsLitVaList
      (iotaEquationType aRecValueAt ⟨5, by decide⟩) :=
  (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
    (assumptionCtx eqDomsLitVaList) rhsLitVaList
    (iotaEquationType aRecValueAt ⟨5, by decide⟩)).get synTypedCheckVaList

/-- The typed ι equation for vaList. -/
theorem eqTypedVaList :
    IotaEquationTypedT aRecValueAt ⟨5, by decide⟩ 96 shapesVaList := by
  unfold IotaEquationTypedT
  rw [eqDomsVaList, rhsVaList]
  exact ⟨synTypedVaList⟩

/-- … under the descriptor clause's selectors. -/
theorem eqTypedVaListClause :
    IotaEquationTypedT aRecValueAt ⟨5, by decide⟩
      (vaIotaClause.fuelAt ⟨5, by decide⟩) (vaIotaClause.shapesAt ⟨5, by decide⟩) :=
  eqTypedVaList

/-! ### vaR -/

kernel_rfl_theorem synTypedCheckVaR :
  (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
    (assumptionCtx eqDomsLitVaR) rhsLitVaR
    (iotaEquationType aRecValueAt ⟨8, by decide⟩)).isSome = true

/-- The certified `HasTyT` derivation for vaR's ι equation. -/
def synTypedVaR :
    HasTyT (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
      (assumptionCtx eqDomsLitVaR) rhsLitVaR
      (iotaEquationType aRecValueAt ⟨8, by decide⟩) :=
  (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity
    (assumptionCtx eqDomsLitVaR) rhsLitVaR
    (iotaEquationType aRecValueAt ⟨8, by decide⟩)).get synTypedCheckVaR

/-- The typed ι equation for vaR. -/
theorem eqTypedVaR :
    IotaEquationTypedT aRecValueAt ⟨8, by decide⟩ 96 shapesVaR := by
  unfold IotaEquationTypedT
  rw [eqDomsVaR, rhsVaR]
  exact ⟨synTypedVaR⟩

/-- … under the descriptor clause's selectors. -/
theorem eqTypedVaRClause :
    IotaEquationTypedT aRecValueAt ⟨8, by decide⟩
      (vaIotaClause.fuelAt ⟨8, by decide⟩) (vaIotaClause.shapesAt ⟨8, by decide⟩) :=
  eqTypedVaR

end Rcic.Scm.SrcG.FunRecTyped
