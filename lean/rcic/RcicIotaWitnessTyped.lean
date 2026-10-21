import rcic.RcicIATypedIota

/-!
# DT-019 package B: `iotaOpenRhs` computes the admission-typed schema

An `IotaWitnessS` carries its own field analysis (`hshapes`) and open schema (`hschema`),
computed at the WITNESS environment `E` and bound `w.fuel`. Admission's recursor cell
computes the same artifacts at the derivation prefix `E0` and the descriptor's own bound —
through `iotaSchemaAt`, with every ι equation typed (`RecursorCellT.typed`). This module
bridges them: **the witness's `iotaOpenRhs` output IS the admission-typed schema**,
so the schema is `HasTyT` at the equation type in the equation context.

The bridge is three transports, each unconditional except its stated gate:

- `RecursorCellT.env_extends`: `E0 ⊆ E` from the cell's `fresh` + `sub`.
- `fieldShapesFuel_ext` + `fieldShapesFuel_agree`: the shape analysis is a function of
  the constructor's fields, stable across the prefix extension and across fuel bounds;
  gate `hgF` is the `constsMemberFuel` closure of the fields in `E0` — the measured
  env-transfer gate of `DT019_DT011_PLAN.md`, kept explicit.
- `iotaOpenRhs_ext` + `iotaOpenRhs_agree`: the schema is likewise env-stable and
  fuel-irrelevant; gate `hgT` closes the lifted constructor field telescope in `E0`
  (its `fieldBvars` half is bvars, closure-free).

The full argument alignment (`familyRef`, `famMember`, `nparams`, `nindices`, `nMinors`,
`ctorMember`, `ctorDoms`, `ctorResult`, `fields.length`) is read off the witness's own
`hpeel`/`hnpar`/`hnidx`/`hnmin`/`hmajorTy`/`hrecBody` pins via
`IotaWitnessS.recData_admitted` plus the constructor view's `storedType` and a
`peelPis` determinism argument. The recursor-level vector aligns through
`recursorArity`; `ctorFieldTelRaw` is the view's `ctorFieldTelescope` by the same peel.

`closure_claim` 0. DT-019 proper stays blocked on `PiRowInjT` / telescope-level
injectivity as measured in #6373; this pays only the schema-computation package.
-/

namespace Rcic.Declarative

/-- the derivation prefix of a cell sits inside the environment: `fresh` keeps
    `extendEnv` a pure extension, `sub` lands it in `E`. -/
theorem RecursorCellT.env_extends {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) :
    ∀ r' m', c.E0.members r' = some m' → E.members r' = some m' := by
  intro r' m' h
  apply c.sub r' m'
  have hne : r' ≠ r := by
    intro heq
    subst heq
    rw [c.fresh] at h
    cases h
  simp only [extendEnv]
  rw [if_neg hne]
  exact h

/-- the witness's constructor is admission's `i`-th constructor: `constructorsPresent`
    lands in `E` through `env_extends`, and the witness's `hctorIdx`/`hctor` pin the
    same reference. -/
theorem RecursorCellT.ctorMember_eq {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) (w : IotaWitnessS E)
    (hf : w.familyRef = c.adm.family.ref)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx) :
    w.ctorMember = c.adm.constructors[i] := by
  have hp := c.adm.constructorsPresent i
  have he := c.env_extends _ _ hp
  have hcref : w.ctorRef = c.adm.family.ref + 1 + i.val := by
    rw [w.hctorIdx, hf, ← hi]
  have hc := w.hctor
  rw [hcref] at hc
  exact Option.some.inj (hc.symm.trans he)

/-- the witness's peeled domains and result are the constructor view's
    `parameters ++ fields` and its result application: `peelPis` is deterministic and
    the view's `storedType` exposes the same stored type as a `policyPi`. -/
theorem RecursorCellT.ctorData_eq {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (c : RecursorCellT E r m) (w : IotaWitnessS E)
    (i : Fin c.adm.constructors.length)
    (hcm : w.ctorMember = c.adm.constructors[i]) :
    w.ctorDoms = (c.adm.constructorViews i).parameters ++
        (c.adm.constructorViews i).fields ∧
      w.ctorResult =
        foldApps (.const c.adm.family.ref (policyFamilyLevels c.adm.family))
          (policyParameterLocals (c.adm.constructorViews i).parameters.length
            (c.adm.constructorViews i).fields.length ++
            (c.adm.constructorViews i).resultIndices) := by
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
  have hpeel := w.hpeel
  rw [w.hnpar, hpc, hst, peelPis_policyPi] at hpeel
  have hpair := Option.some.inj hpeel
  exact ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

/-- every `fieldBvars` entry is a bound variable: the closure check is free. -/
theorem constsMemberFuel_fieldBvars {E : ResolvedEnv} (fuel n : Nat) :
    ∀ f ∈ fieldBvars n, constsMemberFuel E (fuel + 1) f = true := by
  intro f hf
  simp only [fieldBvars, List.mem_map, List.mem_reverse, List.mem_range] at hf
  obtain ⟨j, -, rfl⟩ := hf
  simp only [constsMemberFuel]

/-- package B core: the witness's open ι schema is admission's schema at constructor
    `i`. `hgF` closes the fields and `hgT` the whole field telescope in `E0` at the
    descriptor's bound — the explicit env-transfer gates of the measured design. -/
def iotaWitnessS_schema_eq_iotaSchemaAt {E : ResolvedEnv}
    (w : IotaWitnessS E) (c : RecursorCellT E w.recRef w.recMember)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx)
    (hgF : ∀ T ∈ (c.adm.constructorViews i).fields,
      constsMemberFuel c.E0 (c.clause.fuelAt i + 1) T = true)
    (hgT : constsMemberFuel c.E0 (c.clause.fuelAt i + 1)
      (ctorFieldTelescope (c.adm.constructorViews i)) = true) :
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
  -- the shapes are a function of the fields: env-extends then fuel-agree
  have han : fieldShapesFuel E (c.clause.fuelAt i) c.adm.family.ref
      c.adm.family.member.arity c.adm.family.parameters.length
      c.adm.family.indices.length c.adm.family.parameters.length
      (c.adm.constructorViews i).fields = some (c.clause.shapesAt i) := by
    rw [fieldShapesFuel_ext c.env_extends hgF]
    exact c.clause.analyzed i
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
          -- the same computation at `E`: env-transfer on the telescope gate
          have htl : constsMemberFuel c.E0 (c.clause.fuelAt i + 1)
              (lift 0 ((c.adm.constructorViews i).fields.length + 1 + c.adm.constructors.length + c.adm.family.indices.length)
                (ctorFieldTelescope (c.adm.constructorViews i))) = true := by
            rw [constsMemberFuel_lift]
            exact hgT
          have hE : iotaOpenRhs E (c.clause.fuelAt i)
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
            exact hs
          -- the witness's own `hschema`, transported to the same arguments
          have hw := w.hschema
          rw [hlevels, hfl, hni, hnm, ← hi, htel, hsh, hnp] at hw
          have hsc : w.schema = rhs := iotaOpenRhs_agree E hw hE
          rw [hsc]

/-- package B typed form: the schema is `HasTyT` at the equation type in the equation
    context, moved into `E` — admission's own equation typing at `w.schema`. -/
def iotaWitnessS_rhs_typed {E : ResolvedEnv}
    (w : IotaWitnessS E) (c : RecursorCellT E w.recRef w.recMember)
    (i : Fin c.adm.constructors.length) (hi : i.val = w.ctorIdx)
    (hgF : ∀ T ∈ (c.adm.constructorViews i).fields,
      constsMemberFuel c.E0 (c.clause.fuelAt i + 1) T = true)
    (hgT : constsMemberFuel c.E0 (c.clause.fuelAt i + 1)
      (ctorFieldTelescope (c.adm.constructorViews i)) = true) :
    ∃ (doms : List (Expr Nat)), equationDoms c.adm i = some doms ∧
      Nonempty (HasTyT E w.recMember.arity (assumptionCtx doms)
        w.schema (iotaEquationType c.adm i)) := by
  have heq := iotaWitnessS_schema_eq_iotaSchemaAt w c i hi hgF hgT
  have ht := c.typed i
  unfold IotaEquationTypedT at ht
  rw [heq] at ht
  cases hd : equationDoms c.adm i with
  | none => rw [hd] at ht; cases ht
  | some doms =>
      rw [hd] at ht
      obtain ⟨t⟩ := ht
      exact ⟨doms, rfl, ⟨hasTyTExt c.sub t⟩⟩

/-- the cell-free wrapper: `envWfT_recursorCell` supplies the admission cell and
    `w.hidx` supplies the constructor bound. The env-transfer gates are stated over
    the derived cell's own data, universally over the constructor index. -/
def iotaWitnessS_schema_typed_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E)
    (hgF : ∀ (i : Fin (envWfT_recursorCell hW w.hrec w.hrecK).adm.constructors.length),
      i.val = w.ctorIdx →
      ∀ T ∈ ((envWfT_recursorCell hW w.hrec w.hrecK).adm.constructorViews i).fields,
        constsMemberFuel (envWfT_recursorCell hW w.hrec w.hrecK).E0
          ((envWfT_recursorCell hW w.hrec w.hrecK).clause.fuelAt i + 1) T = true)
    (hgT : ∀ (i : Fin (envWfT_recursorCell hW w.hrec w.hrecK).adm.constructors.length),
      i.val = w.ctorIdx →
      constsMemberFuel (envWfT_recursorCell hW w.hrec w.hrecK).E0
        ((envWfT_recursorCell hW w.hrec w.hrecK).clause.fuelAt i + 1)
        (ctorFieldTelescope
          ((envWfT_recursorCell hW w.hrec w.hrecK).adm.constructorViews i)) = true) :
    ∃ (i : Fin (envWfT_recursorCell hW w.hrec w.hrecK).adm.constructors.length)
      (doms : List (Expr Nat)),
      equationDoms (envWfT_recursorCell hW w.hrec w.hrecK).adm i = some doms ∧
        Nonempty (HasTyT E w.recMember.arity (assumptionCtx doms)
          w.schema (iotaEquationType (envWfT_recursorCell hW w.hrec w.hrecK).adm i)) := by
  let c := envWfT_recursorCell hW w.hrec w.hrecK
  obtain ⟨href, hmem, hnp, hni, hnm⟩ :=
    IotaWitnessS.recData_admitted c.adm c.sub w rfl rfl
  have hi : w.ctorIdx < c.adm.constructors.length := by
    rw [← hnm]; exact w.hidx
  exact ⟨⟨w.ctorIdx, hi⟩,
    iotaWitnessS_rhs_typed w c ⟨w.ctorIdx, hi⟩ rfl
      (hgF ⟨w.ctorIdx, hi⟩ rfl) (hgT ⟨w.ctorIdx, hi⟩ rfl)⟩

#print axioms Rcic.Declarative.iotaWitnessS_schema_eq_iotaSchemaAt
#print axioms Rcic.Declarative.iotaWitnessS_rhs_typed
#print axioms Rcic.Declarative.iotaWitnessS_schema_typed_of_envWfT

end Rcic.Declarative
