import rcic.RcicIotaWitnessTyped
import rcic.RcicRecursorCellHT

/-!
# DT-019 S1 — package B, gate-free

`iotaWitnessS_schema_eq_iotaSchemaAt` (`RcicIotaWitnessTyped`) carries two
env-transfer gates: the constructor's fields and field telescope must pass
`constsMemberFuel` in the cell prefix `E0` at the descriptor's own bound. Here
the gates are `ConstsMemberClosed` certificates instead — which every admitted
environment supplies for every stored type (`membersClosed_of_envWfT`, carried
by `RecursorCellHT.closed`) — and the fuel mismatch is absorbed by
`constsMemberFuel_complete` plus the analysis-fuel monotonicity
(`fieldShapesFuel_mono`, `iotaOpenRhs_mono`): the transfer is run at a bound
above both the descriptor's and the certificate's, and the cross-fuel agreement
(`*_agree`) lands it on the witness's own analysis. The sealed package B
declarations are untouched; this is their gate-free sibling.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-- the constructor's stored field domains and its field telescope are closed in the cell
    prefix: the member is present there (`constructorsPresent`) and every stored type of
    the prefix is closed (`RecursorCellHT.closed`). -/
theorem RecursorCellHT.ctorFields_closed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellHT E r m) (i : Fin c.cell.adm.constructors.length) :
    (∀ T ∈ (c.cell.adm.constructorViews i).fields, ConstsMemberClosed c.cell.E0 T) ∧
      ConstsMemberClosed c.cell.E0 (ctorFieldTelescope (c.cell.adm.constructorViews i)) := by
  have hp := c.cell.adm.constructorsPresent i
  have hc := c.closed _ _ hp
  rw [(c.cell.adm.constructorViews i).storedType] at hc
  obtain ⟨hds, hb⟩ := constsMemberClosed_policyPi_inv _ hc
  refine ⟨fun T hT => hds T (List.mem_append_right _ hT), ?_⟩
  exact constsMemberClosed_policyPi _ (fun T hT => hds T (List.mem_append_right _ hT)) hb

/-- package B core, gate-free: the witness's open ι schema is admission's schema at
    constructor `i`, from closure certificates in `E0`. -/
def iotaWitnessS_schema_eq_iotaSchemaAt_closed {E : ResolvedEnv}
    (w : IotaWitnessS E) (c : RecursorCellT E w.recRef w.recMember)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx)
    (hgF : ∀ T ∈ (c.adm.constructorViews i).fields, ConstsMemberClosed c.E0 T)
    (hgT : ConstsMemberClosed c.E0 (ctorFieldTelescope (c.adm.constructorViews i))) :
    iotaSchemaAt c.adm i (c.clause.fuelAt i) (c.clause.shapesAt i) = some w.schema := by
  obtain ⟨href, hmem, hnp, hni, hnm⟩ :=
    IotaWitnessS.recData_admitted c.adm c.sub w rfl rfl
  have hcm := c.ctorMember_eq w href i hi
  obtain ⟨hdoms, hres⟩ := c.ctorData_eq w i hcm
  have hnp' : w.nparams = (c.adm.constructorViews i).parameters.length := by
    rw [hnp, ← (c.adm.constructorViews i).parameterCount]
  have hfl : w.fields.length = (c.adm.constructorViews i).fields.length := by
    have hst : w.ctorMember.mtype =
        policyPi ((c.adm.constructorViews i).parameters ++
          (c.adm.constructorViews i).fields)
          (foldApps (.const c.adm.family.ref (policyFamilyLevels c.adm.family))
            (policyParameterLocals (c.adm.constructorViews i).parameters.length
              (c.adm.constructorViews i).fields.length ++
              (c.adm.constructorViews i).resultIndices)) := by
      rw [hcm]
      exact (c.adm.constructorViews i).storedType
    have hpc : piCount w.ctorMember.mtype =
        ((c.adm.constructorViews i).parameters ++
          (c.adm.constructorViews i).fields).length := by
      rw [hst, piCount_policyPi,
        piCount_foldApps_of_zero
          (.const c.adm.family.ref (policyFamilyLevels c.adm.family)) _ rfl,
        Nat.add_zero]
    have hnpar := w.hnpar
    rw [hpc] at hnpar
    simp only [List.length_append] at hnpar
    rw [hnp'] at hnpar
    omega
  have hdrop : w.ctorDoms.drop w.nparams = (c.adm.constructorViews i).fields := by
    rw [hdoms, hnp', List.drop_left]
  have htel : ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult =
      ctorFieldTelescope (c.adm.constructorViews i) := by
    simp only [ctorFieldTelRaw, ctorFieldTelescope]
    rw [hdoms, hnp', List.drop_left, ← policyPi_eq_foldr, hres]
  have hlevels : canonRecLevels w.recMember.arity =
      policyRecursorLevels c.adm.family.member.arity c.adm.policy := by
    simp only [canonRecLevels, policyRecursorLevels, c.adm.recursorArity]
  -- the shapes: transfer at a bound above both the descriptor's and the certificate's
  obtain ⟨F, hF⟩ := constsMemberFuel_complete_list c.E0 _ hgF
  have han : fieldShapesFuel E (max (c.clause.fuelAt i) F) c.adm.family.ref
      c.adm.family.member.arity c.adm.family.parameters.length
      c.adm.family.indices.length c.adm.family.parameters.length
      (c.adm.constructorViews i).fields = some (c.clause.shapesAt i) := by
    rw [fieldShapesFuel_ext c.env_extends
      (fun T hT => constsMemberFuel_mono _ _ _ (hF T hT) _ (by omega))]
    exact fieldShapesFuel_mono c.E0 (Nat.le_max_left _ _) (c.clause.analyzed i)
  have hsh : w.shapes = c.clause.shapesAt i := by
    have hw := w.hshapes
    rw [href, hmem, hdrop, hnp, hni] at hw
    exact fieldShapesFuel_agree E hw han
  -- admission's equation supplies the schema and its typing
  have ht := c.typed i
  unfold IotaEquationTypedT at ht
  cases hd : equationDoms c.adm i with
  | none => rw [hd] at ht; cases ht
  | some doms =>
      cases hs : iotaSchemaAt c.adm i (c.clause.fuelAt i)
          (c.clause.shapesAt i) with
      | none => rw [hd, hs] at ht; cases ht
      | some rhs =>
          clear ht
          simp only [iotaSchemaAt] at hs
          obtain ⟨FT, hFT⟩ := constsMemberFuel_complete hgT
          have htl : constsMemberFuel c.E0 (max (c.clause.fuelAt i) FT + 1)
              (lift 0 ((c.adm.constructorViews i).fields.length + 1 + c.adm.constructors.length + c.adm.family.indices.length)
                (ctorFieldTelescope (c.adm.constructorViews i))) = true := by
            rw [constsMemberFuel_lift]
            exact constsMemberFuel_mono _ _ _ hFT _ (by omega)
          have hE : iotaOpenRhs E (max (c.clause.fuelAt i) FT)
              (.const w.recRef (policyRecursorLevels c.adm.family.member.arity
                c.adm.policy))
              (.bvar ((c.adm.constructorViews i).fields.length +
                c.adm.family.indices.length +
                (c.adm.constructors.length - 1 - i.val)))
              (preMajorBvars c.adm.family.parameters.length
                c.adm.constructors.length c.adm.family.indices.length
                (c.adm.constructorViews i).fields.length)
              c.adm.family.parameters.length c.adm.constructors.length
              (c.clause.shapesAt i)
              (fieldBvars (c.adm.constructorViews i).fields.length)
              (lift 0 ((c.adm.constructorViews i).fields.length + 1 + c.adm.constructors.length + c.adm.family.indices.length)
                (ctorFieldTelescope (c.adm.constructorViews i))) = some rhs := by
            rw [iotaOpenRhs_ext c.env_extends _ _ _ _ _ _ _ _ _
              (constsMemberFuel_fieldBvars _ _) htl]
            exact iotaOpenRhs_mono c.E0 (Nat.le_max_left _ _) hs
          have hw := w.hschema
          rw [hlevels, hfl, hni, hnm, ← hi, htel, hsh, hnp] at hw
          have hsc : w.schema = rhs := iotaOpenRhs_agree E hw hE
          rw [hsc]

/-- package B typed form, gate-free. -/
def iotaWitnessS_rhs_typed_closed {E : ResolvedEnv}
    (w : IotaWitnessS E) (c : RecursorCellT E w.recRef w.recMember)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx)
    (hgF : ∀ T ∈ (c.adm.constructorViews i).fields, ConstsMemberClosed c.E0 T)
    (hgT : ConstsMemberClosed c.E0 (ctorFieldTelescope (c.adm.constructorViews i))) :
    ∃ (doms : List (Expr Nat)), equationDoms c.adm i = some doms ∧
      Nonempty (HasTyT E w.recMember.arity (assumptionCtx doms)
        w.schema (iotaEquationType c.adm i)) := by
  have heq := iotaWitnessS_schema_eq_iotaSchemaAt_closed w c i hi hgF hgT
  have ht := c.typed i
  unfold IotaEquationTypedT at ht
  rw [heq] at ht
  cases hd : equationDoms c.adm i with
  | none => rw [hd] at ht; cases ht
  | some doms =>
      rw [hd] at ht
      obtain ⟨t⟩ := ht
      exact ⟨doms, rfl, ⟨hasTyTExt c.sub t⟩⟩

/-- the cell-level wrapper: at a `RecursorCellHT`, every `IotaWitnessS` at its recursor
    has admission's typed equation at the witness's own constructor index. -/
theorem iotaWitnessS_schema_typed_cellHT {E : ResolvedEnv} (w : IotaWitnessS E)
    (c : RecursorCellHT E w.recRef w.recMember) :
    ∃ (i : Fin c.cell.adm.constructors.length), i.val = w.ctorIdx ∧
      ∃ (doms : List (Expr Nat)), equationDoms c.cell.adm i = some doms ∧
        Nonempty (HasTyT E w.recMember.arity (assumptionCtx doms)
          w.schema (iotaEquationType c.cell.adm i)) := by
  obtain ⟨_, _, _, _, hnm⟩ :=
    IotaWitnessS.recData_admitted c.cell.adm c.cell.sub w rfl rfl
  have hi : w.ctorIdx < c.cell.adm.constructors.length := by
    rw [← hnm]; exact w.hidx
  obtain ⟨hgF, hgT⟩ := c.ctorFields_closed ⟨w.ctorIdx, hi⟩
  exact ⟨⟨w.ctorIdx, hi⟩, rfl,
    iotaWitnessS_rhs_typed_closed w c.cell ⟨w.ctorIdx, hi⟩ rfl hgF hgT⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.iotaWitnessS_schema_eq_iotaSchemaAt_closed
#print axioms Rcic.Declarative.iotaWitnessS_schema_typed_cellHT
