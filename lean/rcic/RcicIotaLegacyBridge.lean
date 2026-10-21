import rcic.RcicIotaLegacyAdm
import rcic.RcicIotaLegacyFamFree
import rcic.RcicIotaLegacySigma
import rcic.RcicIotaWitnessTypedClosed
import rcic.RcicIotaSRRowsCtor
import rcic.RcicIotaSRRows
import rcic.RcicDT1011Rows
import rcic.RcicDTMetaTypedSR

/-!
# DT-019 S2 — the legacy `DerivedIota` has a typed counterpart at every `EnvWfT`

`derivedIotaT_of_derivedIota_envWfT`: at a well-formed environment, every legacy ι
step (`DerivedIota`, the syntactic `rhsArgs` reduct) is a typed-root step
(`DerivedIotaT`, admission's instantiated schema) at the same endpoints — with no
certificate. The witness is built from the legacy one: its structural fields are
copied, admission's own field shapes and open schema (read at the recursor's cell,
`RcicIotaLegacyFamFree`) supply `fuel`/`shapes`/`schema`, closure of the stored
types in the derivation prefix supplies the stability clause, and admission's typed
equation supplies the scope certificate. The reduct is the legacy one by the
σ-correspondence (`RcicIotaLegacySigma`) once admission's shapes are shown to be the
legacy kinds (`RcicIotaLegacyShapes`, from the prefix's fam-free bodies).

Consequences:
* `iotaSRTN_of_typedRowsWf : EnvWfT E → TypedRowsWf E n → IotaSRTN E n` — DT-010/DT-011's
  `hiota` front is discharged by the rows; `DT010T_one_step_subject_reduction_rows` /
  `DT011T_multi_step_subject_reduction_rows` are the census-facing forms with the rows as
  the only premise beyond `EnvWfT`.
* `iotaPreserveT_rows_legacy` / `iotaPreserveU_rows`: the certificate-free ι-SR of
  `RcicIotaSRRows` on legacy and on union evidence.
* `pin_iotaSRTN_rows_natEnvU` / `pin_legacy_iota_sr_natEnvU`: the premises are jointly
  inhabited on `natEnvU` and the theorem fires on the successor redex `wSuccU1`.

Not claimed: `TypedRowsWf` itself (W-F05b-PiRow, the X tile). `closure_claim` 0.
-/

namespace Rcic.Declarative

/-- **the bridge at a witness**: a legacy ι witness at an admitted recursor adapts to the
    typed root's witness, at the same left-hand side and the same reduct. -/
theorem derivedIotaT_of_iotaWitness_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) : Nonempty (DerivedIotaT E (iotaLhsOf w) (iotaRhsOf w)) := by
  have c : RecursorCellHF E w.recRef w.recMember := envWfT_cellHF hW w.hrec w.hrecK
  obtain ⟨href, hmem, hnp, hni, hnm⟩ :=
    IotaWitness.recData_admitted c.cell.cell.adm c.cell.cell.sub w rfl rfl
  have hi : w.ctorIdx < c.cell.cell.adm.constructors.length := by rw [← hnm]; exact w.hidx
  let i : Fin c.cell.cell.adm.constructors.length := ⟨w.ctorIdx, hi⟩
  have hcm := c.cell.cell.ctorMember_eqL w href i rfl
  obtain ⟨hdoms, hres⟩ := c.cell.cell.ctorData_eqL w i hcm
  have hnp' : w.nparams = (c.cell.cell.adm.constructorViews i).parameters.length := by
    rw [hnp, ← (c.cell.cell.adm.constructorViews i).parameterCount]
  have hfl : w.fields.length = (c.cell.cell.adm.constructorViews i).fields.length := by
    have hdl : w.ctorDoms.length = w.nparams + w.fields.length := peelPis_length _ _ w.hpeel
    rw [hdoms, List.length_append, ← hnp'] at hdl
    omega
  have hdrop : w.ctorDoms.drop w.nparams = (c.cell.cell.adm.constructorViews i).fields := by
    rw [hdoms, hnp', List.drop_left]
  have htel : ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult =
      ctorFieldTelescope (c.cell.cell.adm.constructorViews i) := by
    simp only [ctorFieldTelRaw, ctorFieldTelescope]
    rw [hdoms, hnp', List.drop_left, ← policyPi_eq_foldr, hres]
  have hlevels : canonRecLevels w.recMember.arity =
      policyRecursorLevels c.cell.cell.adm.family.member.arity c.cell.cell.adm.policy := by
    simp only [canonRecLevels, policyRecursorLevels, c.cell.cell.adm.recursorArity]
  -- closure certificates in the prefix, and the bound they resolve at
  obtain ⟨hgF, hgT⟩ := c.cell.ctorFields_closed i
  obtain ⟨F, hF⟩ := constsMemberFuel_complete_list c.cell.cell.E0 _ hgF
  obtain ⟨FT, hFT⟩ := constsMemberFuel_complete hgT
  let fuel := max (c.cell.cell.clause.fuelAt i) (max F FT)
  have hfuelA : c.cell.cell.clause.fuelAt i ≤ fuel := Nat.le_max_left _ _
  have hfuelF : F ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hfuelT : FT ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hgF' : ∀ T ∈ (c.cell.cell.adm.constructorViews i).fields,
      constsMemberFuel c.cell.cell.E0 (fuel + 1) T = true :=
    fun T hT => constsMemberFuel_mono _ _ _ (hF T hT) _ (by omega)
  have hgT' : constsMemberFuel c.cell.cell.E0 (fuel + 1)
      (lift 0 ((c.cell.cell.adm.constructorViews i).fields.length + 1 +
        c.cell.cell.adm.constructors.length + c.cell.cell.adm.family.indices.length)
        (ctorFieldTelescope (c.cell.cell.adm.constructorViews i))) = true := by
    rw [constsMemberFuel_lift]
    exact constsMemberFuel_mono _ _ _ hFT _ (by omega)
  -- the shapes, in every extension of the prefix
  have hshapesE : ∀ E', (∀ r m, c.cell.cell.E0.members r = some m → E'.members r = some m) →
      fieldShapesFuel E' fuel c.cell.cell.adm.family.ref c.cell.cell.adm.family.member.arity
        c.cell.cell.adm.family.parameters.length c.cell.cell.adm.family.indices.length
        c.cell.cell.adm.family.parameters.length (c.cell.cell.adm.constructorViews i).fields =
        some (c.cell.cell.clause.shapesAt i) := by
    intro E' hext
    rw [fieldShapesFuel_ext hext hgF']
    exact fieldShapesFuel_mono c.cell.cell.E0 hfuelA (c.cell.cell.clause.analyzed i)
  -- admission's equation: the schema and its typing
  have ht := c.cell.cell.typed i
  unfold IotaEquationTypedT at ht
  cases hd : equationDoms c.cell.cell.adm i with
  | none => rw [hd] at ht; cases ht
  | some doms =>
  cases hs : iotaSchemaAt c.cell.cell.adm i (c.cell.cell.clause.fuelAt i)
      (c.cell.cell.clause.shapesAt i) with
  | none => rw [hd, hs] at ht; cases ht
  | some schema =>
  rw [hd, hs] at ht
  obtain ⟨t⟩ := ht
  simp only [iotaSchemaAt] at hs
  have hschemaE : ∀ E', (∀ r m, c.cell.cell.E0.members r = some m → E'.members r = some m) →
      iotaOpenRhs E' fuel
        (.const w.recRef (policyRecursorLevels c.cell.cell.adm.family.member.arity
          c.cell.cell.adm.policy))
        (.bvar ((c.cell.cell.adm.constructorViews i).fields.length +
          c.cell.cell.adm.family.indices.length +
          (c.cell.cell.adm.constructors.length - 1 - i.val)))
        (preMajorBvars c.cell.cell.adm.family.parameters.length
          c.cell.cell.adm.constructors.length c.cell.cell.adm.family.indices.length
          (c.cell.cell.adm.constructorViews i).fields.length)
        c.cell.cell.adm.family.parameters.length c.cell.cell.adm.constructors.length
        (c.cell.cell.clause.shapesAt i)
        (fieldBvars (c.cell.cell.adm.constructorViews i).fields.length)
        (lift 0 ((c.cell.cell.adm.constructorViews i).fields.length + 1 +
          c.cell.cell.adm.constructors.length + c.cell.cell.adm.family.indices.length)
          (ctorFieldTelescope (c.cell.cell.adm.constructorViews i))) = some schema := by
    intro E' hext
    rw [iotaOpenRhs_ext hext _ _ _ _ _ _ _ _ _ (constsMemberFuel_fieldBvars _ _) hgT']
    exact iotaOpenRhs_mono c.cell.cell.E0 hfuelA hs
  -- the scope: the schema is typed in the equation context
  have hscope : exprClosedAt (w.nparams + 1 + w.nMinors + w.nindices + w.fields.length)
      schema = true := by
    have hc := hasTyT_exprClosedAt t
    have hlen : (assumptionCtx doms).length =
        w.nparams + 1 + w.nMinors + w.nindices + w.fields.length := by
      simp only [assumptionCtx, List.length_map, List.length_reverse]
      simp only [equationDoms] at hd
      cases hp : peelPis (piCount w.recMember.mtype) w.recMember.mtype with
      | none => rw [hp] at hd; cases hd
      | some p =>
          obtain ⟨doms0, _⟩ := p
          rw [hp] at hd
          simp only [Option.some.injEq] at hd
          have hl0 : doms0.length = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
            rw [peelPis_length _ _ hp, ← w.hnmin]
          rw [← hd, List.length_append, List.length_dropLast, liftFields_length, hl0, hfl]
          omega
    rw [hlen] at hc
    exact hc
  -- admission's shapes are the legacy kinds
  have hfam0 : ∀ ls, transparentBody c.cell.cell.E0 w.familyRef ls = none := by
    intro ls
    rw [href]
    exact transparentBody_family c.cell.cell.adm.family ls
  have hff0 : FamFreeBodies c.cell.cell.E0 w.familyRef := by
    intro r ls b h
    rw [href]
    exact c.famFree r ls b h
  have hk : analyzeFields w.familyRef (c.cell.cell.adm.constructorViews i).fields = some w.kinds := by
    rw [← hdrop]
    exact w.hkinds
  have hsh : c.cell.cell.clause.shapesAt i = w.kinds.map shapeOfKind := by
    have ha := c.cell.cell.clause.analyzed i
    rw [← href] at ha
    exact fieldShapesFuel_eq_kinds hff0 hfam0 _ _ hk ha
  -- the typed witness
  let w' : IotaWitnessS E :=
    { recRef := w.recRef, ctorRef := w.ctorRef, ls := w.ls, lsC := w.lsC
      recMember := w.recMember, ctorMember := w.ctorMember
      hrec := w.hrec, hctor := w.hctor, hrecK := w.hrecK, hctorK := w.hctorK
      preMajor := w.preMajor, fields := w.fields, ctorParams := w.ctorParams
      familyRef := w.familyRef, famMember := w.famMember, hfam := w.hfam, hfamK := w.hfamK
      nparams := w.nparams, nindices := w.nindices, nMinors := w.nMinors, ctorIdx := w.ctorIdx
      hctorParams := w.hctorParams, hnpar := w.hnpar, hnidx := w.hnidx, hnmin := w.hnmin
      hidx := w.hidx, hctorIdx := w.hctorIdx, hrecIdx := w.hrecIdx, hpre := w.hpre
      ctorDoms := w.ctorDoms, ctorResult := w.ctorResult, hpeel := w.hpeel
      hfamApp := w.hfamApp, recDoms := w.recDoms, recBody := w.recBody
      hpeelRec := w.hpeelRec, hrecBody := w.hrecBody, hmajorTy := w.hmajorTy
      hrecClosed := w.hrecClosed, hctorClosed := w.hctorClosed, hlsLen := w.hlsLen
      fuel := fuel
      shapes := c.cell.cell.clause.shapesAt i
      hshapes := by
        rw [href, hmem, hdrop, hnp, hni]
        exact hshapesE E c.cell.cell.env_extends
      schema := schema
      hschema := by
        rw [hlevels, hfl, hni, hnm, htel, hnp]
        exact hschemaE E c.cell.cell.env_extends
      hstable := by
        intro E' hext
        constructor
        · rw [href, hmem, hdrop, hnp, hni]
          exact hshapesE E' (fun r m h => hext r m (c.cell.cell.env_extends r m h))
        · rw [hlevels, hfl, hni, hnm, htel, hnp]
          exact hschemaE E' (fun r m h => hext r m (c.cell.cell.env_extends r m h))
      hschemaScope := hscope }
  have hrhs : iotaRhsOfS w' = iotaRhsOf w := by
    show instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls schema) = iotaRhsOf w
    apply iotaRhsOf_eq_sigma w (fuel := fuel)
    rw [← hsh, hlevels, hfl, hni, hnm, htel, hnp]
    exact hschemaE E c.cell.cell.env_extends
  have hlhs : iotaLhsOfS w' = iotaLhsOf w := rfl
  rw [← hlhs, ← hrhs]
  exact ⟨.of w'⟩

/-- **the bridge**: at `EnvWfT`, legacy ι evidence has typed-root ι evidence at the same
    endpoints — no certificate. -/
theorem derivedIotaT_of_derivedIota_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {lhs rhs : Expr Nat} : DerivedIota E lhs rhs → Nonempty (DerivedIotaT E lhs rhs)
  | .of w => derivedIotaT_of_iotaWitness_envWfT hW w

/-- ι subject reduction modulo the rows, on LEGACY evidence: `iotaPreserveT_rows` through
    the bridge. -/
theorem iotaPreserveT_rows_legacy {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  (derivedIotaT_of_derivedIota_envWfT hW hd).elim fun hd' =>
    iotaPreserveT_rows hW hrows hΓ hd' hlhs

/-- ι subject reduction modulo the rows, on union evidence. -/
theorem iotaPreserveU_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  match hd with
  | .ofU w => iotaPreserveT_rows_legacy hW hrows hΓ (.of w) hlhs
  | .ofUS w => iotaPreserveT_rows hW hrows hΓ (.of w) hlhs

/-- **DT-019's front from the rows**: `IotaSRTN E n` — DT-010/DT-011's `hiota` premise —
    holds at every `EnvWfT` with `TypedRowsWf`. -/
theorem iotaSRTN_of_typedRowsWf {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) : IotaSRTN E n :=
  fun {_} hΓ {_ _ S} hd h =>
    (iotaPreserveT_rows_legacy hW hrows hΓ hd h).elim fun h' => ⟨S, h', .refl _ _⟩

/-- DT-010 modulo the rows alone: `step_srT_rows` with `hiota` discharged. -/
def step_srT_rows' {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) :=
  step_srT_rows hW hrows (iotaSRTN_of_typedRowsWf hW hrows) hΓ h hs

/-- DT-011 modulo the rows alone. -/
def steps_srT_rows' {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) :=
  steps_srT_rows hW hrows (iotaSRTN_of_typedRowsWf hW hrows) hΓ h hs

/-- DT-010, census-facing, with `TypedRowsWf` as the only premise beyond `EnvWfT`. -/
theorem DT010T_one_step_subject_reduction_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_of_typedRowsWf hW hrows (iotaSRTN_of_typedRowsWf hW hrows)
    hΓ h hs

/-- DT-011, census-facing, with `TypedRowsWf` as the only premise beyond `EnvWfT`. -/
theorem DT011T_multi_step_subject_reduction_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_of_typedRowsWf hW hrows (iotaSRTN_of_typedRowsWf hW hrows)
    hΓ h hs

/-! ## non-vacuity: `natEnvU`, the successor redex -/

/-- the front is inhabited on `natEnvU` (rows from `InScope`). -/
theorem pin_iotaSRTN_rows_natEnvU : IotaSRTN natEnvU 1 :=
  iotaSRTN_of_typedRowsWf natEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1)

/-- the legacy successor redex `rec P mz ms (succ n)` reduces to a term typed at `N`,
    through the bridge, with no certificate and no `InScope` entering the ι step. -/
theorem pin_legacy_iota_sr_natEnvU :
    Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 [])) :=
  iotaPreserveT_rows_legacy natEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1) CtxWfT.nil
    (.of wSuccU1) pinIotaLhsTy

/-- the bridge fires on the successor redex: a typed-root witness at the legacy endpoints. -/
theorem pin_bridge_natEnvU :
    Nonempty (DerivedIotaT natEnvU (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1)) :=
  derivedIotaT_of_iotaWitness_envWfT natEnvUWfT wSuccU1

end Rcic.Declarative

#print axioms Rcic.Declarative.derivedIotaT_of_derivedIota_envWfT
#print axioms Rcic.Declarative.iotaSRTN_of_typedRowsWf
#print axioms Rcic.Declarative.DT010T_one_step_subject_reduction_rows
#print axioms Rcic.Declarative.DT011T_multi_step_subject_reduction_rows
#print axioms Rcic.Declarative.iotaPreserveU_rows
#print axioms Rcic.Declarative.pin_legacy_iota_sr_natEnvU
