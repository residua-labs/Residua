import rcic.ScmSrcGroupsFunRecTypedVA

/-! Kernel-evaluated leaves for the ValueAt `recIdxAdmittedTB` check,
constructors 4–6.

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


kernel_rfl_theorem vaClosed4 :
  exprClosedAt 0 aRecValueAt.constructors[4].mtype = true

kernel_rfl_theorem vaF4E :
  (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI4E :
  (aRecValueAt.constructorViews ⟨4, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF4X :
  (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI4X :
  (aRecValueAt.constructorViews ⟨4, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope4 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨4, by decide⟩) = true

kernel_rfl_theorem vaClosed5 :
  exprClosedAt 0 aRecValueAt.constructors[5].mtype = true

kernel_rfl_theorem vaF5E :
  (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI5E :
  (aRecValueAt.constructorViews ⟨5, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF5X :
  (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI5X :
  (aRecValueAt.constructorViews ⟨5, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope5 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨5, by decide⟩) = true

kernel_rfl_theorem vaClosed6 :
  exprClosedAt 0 aRecValueAt.constructors[6].mtype = true

kernel_rfl_theorem vaF6E :
  (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI6E :
  (aRecValueAt.constructorViews ⟨6, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF6X :
  (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI6X :
  (aRecValueAt.constructorViews ⟨6, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope6 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨6, by decide⟩) = true

theorem vaRes4E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨4, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨4, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI4E⟩

theorem vaRes4X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨4, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨4, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI4X⟩

theorem vaCtorB4 : vaCtorCheckB ⟨4, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel4, vaTel4]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed4, ⟨⟨vaF4E, fieldBvars_all _ _ _⟩, ⟨vaF4E, vaRes4E⟩⟩⟩,
      ⟨⟨vaF4X, fieldBvars_all _ _ _⟩, ⟨vaF4X, vaRes4X⟩⟩⟩,
    vaScope4⟩

theorem vaRes5E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨5, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨5, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI5E⟩

theorem vaRes5X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨5, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨5, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI5X⟩

theorem vaCtorB5 : vaCtorCheckB ⟨5, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel5, vaTel5]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed5, ⟨⟨vaF5E, fieldBvars_all _ _ _⟩, ⟨vaF5E, vaRes5E⟩⟩⟩,
      ⟨⟨vaF5X, fieldBvars_all _ _ _⟩, ⟨vaF5X, vaRes5X⟩⟩⟩,
    vaScope5⟩

theorem vaRes6E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨6, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨6, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI6E⟩

theorem vaRes6X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨6, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨6, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI6X⟩

theorem vaCtorB6 : vaCtorCheckB ⟨6, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel6, vaTel6]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed6, ⟨⟨vaF6E, fieldBvars_all _ _ _⟩, ⟨vaF6E, vaRes6E⟩⟩⟩,
      ⟨⟨vaF6X, fieldBvars_all _ _ _⟩, ⟨vaF6X, vaRes6X⟩⟩⟩,
    vaScope6⟩

end Rcic.Scm.SrcG.FunRecTyped
