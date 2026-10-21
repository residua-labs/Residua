import rcic.ScmSrcGroupsFunRecTypedVA

/-! Kernel-evaluated leaves for the ValueAt `recIdxAdmittedTB` check,
constructors 0–3.

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


kernel_rfl_theorem vaClosed0 :
  exprClosedAt 0 aRecValueAt.constructors[0].mtype = true

kernel_rfl_theorem vaF0E :
  (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI0E :
  (aRecValueAt.constructorViews ⟨0, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF0X :
  (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI0X :
  (aRecValueAt.constructorViews ⟨0, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope0 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨0, by decide⟩) = true

kernel_rfl_theorem vaClosed1 :
  exprClosedAt 0 aRecValueAt.constructors[1].mtype = true

kernel_rfl_theorem vaF1E :
  (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI1E :
  (aRecValueAt.constructorViews ⟨1, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF1X :
  (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI1X :
  (aRecValueAt.constructorViews ⟨1, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope1 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨1, by decide⟩) = true

kernel_rfl_theorem vaClosed2 :
  exprClosedAt 0 aRecValueAt.constructors[2].mtype = true

kernel_rfl_theorem vaF2E :
  (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI2E :
  (aRecValueAt.constructorViews ⟨2, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF2X :
  (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI2X :
  (aRecValueAt.constructorViews ⟨2, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope2 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨2, by decide⟩) = true

kernel_rfl_theorem vaClosed3 :
  exprClosedAt 0 aRecValueAt.constructors[3].mtype = true

kernel_rfl_theorem vaF3E :
  (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI3E :
  (aRecValueAt.constructorViews ⟨3, by decide⟩).resultIndices.all
    (constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)) = true

kernel_rfl_theorem vaF3X :
  (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)) = true

kernel_rfl_theorem vaRI3X :
  (aRecValueAt.constructorViews ⟨3, by decide⟩).resultIndices.all
    (constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)) = true

kernel_rfl_theorem vaScope3 :
  exprClosedAt (aRecValueAt.family.parameters.length + 1 +
      aRecValueAt.constructors.length + aRecValueAt.family.indices.length +
      (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.length)
    (descriptorSchema aRecValueAt vaIotaClause ⟨3, by decide⟩) = true

theorem vaRes0E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨0, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨0, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI0E⟩

theorem vaRes0X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨0, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨0, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI0X⟩

theorem vaCtorB0 : vaCtorCheckB ⟨0, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel0, vaTel0]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed0, ⟨⟨vaF0E, fieldBvars_all _ _ _⟩, ⟨vaF0E, vaRes0E⟩⟩⟩,
      ⟨⟨vaF0X, fieldBvars_all _ _ _⟩, ⟨vaF0X, vaRes0X⟩⟩⟩,
    vaScope0⟩

theorem vaRes1E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨1, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨1, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI1E⟩

theorem vaRes1X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨1, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨1, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI1X⟩

theorem vaCtorB1 : vaCtorCheckB ⟨1, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel1, vaTel1]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed1, ⟨⟨vaF1E, fieldBvars_all _ _ _⟩, ⟨vaF1E, vaRes1E⟩⟩⟩,
      ⟨⟨vaF1X, fieldBvars_all _ _ _⟩, ⟨vaF1X, vaRes1X⟩⟩⟩,
    vaScope1⟩

theorem vaRes2E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨2, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨2, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI2E⟩

theorem vaRes2X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨2, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨2, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI2X⟩

theorem vaCtorB2 : vaCtorCheckB ⟨2, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel2, vaTel2]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed2, ⟨⟨vaF2E, fieldBvars_all _ _ _⟩, ⟨vaF2E, vaRes2E⟩⟩⟩,
      ⟨⟨vaF2X, fieldBvars_all _ _ _⟩, ⟨vaF2X, vaRes2X⟩⟩⟩,
    vaScope2⟩

theorem vaRes3E :
    constsMemberFuel (envPre 143) (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨3, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨3, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt aRecValueAt.family.present _ _,
    policyParameterLocals_all _ _ _ _, vaRI3E⟩

theorem vaRes3X :
    constsMemberFuel (extendEnv (envPre 143) 143 recValueAt)
      (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)
      (foldApps (.const aRecValueAt.family.ref (policyFamilyLevels aRecValueAt.family))
        (policyParameterLocals (aRecValueAt.constructorViews ⟨3, by decide⟩).parameters.length (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.length ++
          (aRecValueAt.constructorViews ⟨3, by decide⟩).resultIndices)) = true := by
  rw [constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨constsMemberFuel_famConst aRecValueAt vaFamMemX _ _,
    policyParameterLocals_all _ _ _ _, vaRI3X⟩

theorem vaCtorB3 : vaCtorCheckB ⟨3, by decide⟩ = true := by
  unfold vaCtorCheckB recIdxCtorB iotaWitnessStableB
  rw [vaTel3, vaTel3]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨vaClosed3, ⟨⟨vaF3E, fieldBvars_all _ _ _⟩, ⟨vaF3E, vaRes3E⟩⟩⟩,
      ⟨⟨vaF3X, fieldBvars_all _ _ _⟩, ⟨vaF3X, vaRes3X⟩⟩⟩,
    vaScope3⟩

end Rcic.Scm.SrcG.FunRecTyped
