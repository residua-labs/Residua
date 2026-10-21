import rcic.ScmSrcGroupsFunRecTypedVA

/-! Kernel-evaluated leaves for the ValueAt `recIdxAdmittedTB` check,
constructors 7–8.

The kernel's deterministic evaluation budget is cumulative per module, so
the leaves are split across `…VA0`/`…VA1`/`…VA2` by constructor group.
Only the pieces that cannot be rewritten need `kernel_rfl_theorem`: the
constructor-type closure, the field-domain `constsMemberFuel` sweep, the
result-index sweep, and the schema scope check.  `fieldBvars_all`,
`policyParameterLocals_all`, and `constsMemberFuel_famConst` discharge the
bare-bvar and family-head sweeps once for all constructors. -/

open Rcic.Declarative Rcic.Scm.SrcG Rcic.Scm.SrcG.FunRecEntry
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecTyped


kernel_rfl_theorem vaClosed7 :
  exprClosedAt 0 aRecValueAt.constructors[7].mtype = true

kernel_rfl_theorem vaF7E :
  (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI7E :
  (aRecValueAt.constructorViews ⟨7, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF7X :
  (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI7X :
  (aRecValueAt.constructorViews ⟨7, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope7 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨7, by decide⟩) = true

kernel_rfl_theorem vaClosed8 :
  exprClosedAt 0 aRecValueAt.constructors[8].mtype = true

kernel_rfl_theorem vaF8E :
  (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI8E :
  (aRecValueAt.constructorViews ⟨8, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF8X :
  (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI8X :
  (aRecValueAt.constructorViews ⟨8, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope8 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨8, by decide⟩) = true

theorem vaRes7E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨7, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨7, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI7E⟩

theorem vaRes7X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨7, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨7, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI7X⟩

theorem vaCtorB7 : vaCtorCheckB ⟨7, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel7, vaTel7]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed7, ⟨⟨vaF7E, fieldBvars_all _ _ _⟩, ⟨vaF7E, vaRes7E⟩⟩⟩,
      ⟨⟨vaF7X, fieldBvars_all _ _ _⟩, ⟨vaF7X, vaRes7X⟩⟩⟩,
    vaScope7⟩

theorem vaRes8E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨8, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨8, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI8E⟩

theorem vaRes8X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨8, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨8, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI8X⟩

theorem vaCtorB8 : vaCtorCheckB ⟨8, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel8, vaTel8]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed8, ⟨⟨vaF8E, fieldBvars_all _ _ _⟩, ⟨vaF8E, vaRes8E⟩⟩⟩,
      ⟨⟨vaF8X, fieldBvars_all _ _ _⟩, ⟨vaF8X, vaRes8X⟩⟩⟩,
    vaScope8⟩

end Rcic.Scm.SrcG.FunRecTyped
