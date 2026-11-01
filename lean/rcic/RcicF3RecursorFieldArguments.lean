import rcic.RcicF3RecArguments
import rcic.RcicF3MinorInputsFromNonempty
import rcic.RcicIotaLegacyShapes

/-!
# Original fields from every actual nonempty legacy recursor redex

The selected admitted row is aligned with the legacy witness through the
existing fieldShapesFuel_eq_kinds theorem. The executable stored minor then
recovers its original constructor fields through every inserted direct IH.
All raw arguments come from the actual witness; no plain-field, NoFunRec,
source-context, or field-fitting callback is assumed.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.RecursorFieldArguments
open Rcic.Declarative Rcic.Model.PS
open MinorInputsFromNonempty

private theorem legacyShapes_eq_map (ks : List RecKind) :
    legacyShapes ks = ks.map Rcic.Declarative.shapeOfKind := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      cases k <;> simp only [legacyShapes, List.map_cons, Rcic.Declarative.shapeOfKind, ih]

/-- Exact alignment at the constructor selected by the actual witness.
The family is opaque because it is the admitted inductive member. -/
theorem selected_row {E E' S : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (w : IotaWitness S) (hwr : w.recRef = rr) (hm : w.recMember = rm)
    (j : Fin node.a.constructors.length)
    (hcm : w.ctorMember = node.a.constructors[j.val]) :
    node.h14.shapesAt j = legacyShapes w.kinds := by
  obtain ⟨hnp, _, _, hfr⟩ := iota_align node.a w hwr hm
  have hfl : w.fields.length = (node.a.constructorViews j).fields.length :=
    witness_fields_length node.a w hwr hm j hcm
  have hcpl := (node.a.constructorViews j).parameterCount
  have hctm : w.ctorMember.mtype =
      policyPi ((node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields)
        (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
          (policyParameterLocals (node.a.constructorViews j).parameters.length
            (node.a.constructorViews j).fields.length ++
              (node.a.constructorViews j).resultIndices)) := by
    rw [hcm]
    exact (node.a.constructorViews j).storedType
  have hpeel := w.hpeel
  rw [hctm, show w.nparams + w.fields.length =
      ((node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields).length by
        rw [List.length_append]; omega, peelPis_policyPi] at hpeel
  have hdoms : w.ctorDoms =
      (node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields :=
    (congrArg Prod.fst (Option.some.inj hpeel)).symm
  have hkinds := w.hkinds
  rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
  have hop : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by
    intro ls
    unfold transparentBody
    rw [node.a.family.present]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have heq := fieldShapesFuel_eq_kinds hFF hop
    (node.a.constructorViews j).fields node.a.family.parameters.length
    hkinds (node.h14.analyzed j)
  exact heq.trans (legacyShapes_eq_map w.kinds).symm

/-- Recover the selected actual minor from the complete produced split. -/
theorem minor_read (M : Interp.{4}) (p : EvalPlan.Plan)
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    {ps : List PSet.{4}} {mo : PSet.{4}} {ms is : List PSet.{4}}
    (ha : RecArguments.Arguments M p w σ ρ ps mo ms is) :
    ms.getD j.val pempty = den M σ ρ w.minor := by
  obtain ⟨hnp, _, _, _⟩ := iota_align p.node.a w hwr hm
  have hpsl := ha.parameters_length
  have hmsl := ha.minors_length
  have hjk := j.isLt
  have hm1 := w.hminor
  rw [hnp, hj] at hm1
  have hm2 : (w.preMajor.map (den M σ ρ))[
      p.node.a.family.parameters.length + 1 + j.val]? =
      some (den M σ ρ w.minor) := by
    rw [List.getElem?_map, hm1]
    rfl
  rw [ha.split, List.getElem?_append_right (by omega),
    show p.node.a.family.parameters.length + 1 + j.val - ps.length = j.val + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_left (by omega)] at hm2
  rw [List.getD_eq_getElem?_getD, hm2]
  rfl

/-- Original fields are produced for the actual selected legacy row,
including direct recursive fields and their inserted IH arguments. -/
theorem fields_of_arguments (M : Interp.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    {ps : List PSet.{4}} {mo : PSet.{4}} {ms is : List PSet.{4}}
    (ha : RecArguments.Arguments M p w σ ρ ps mo ms is)
    (hneR : ¬ Equiv (den M σ ρ (iotaRhsOf w)) pempty) :
    TelFits M (RecArguments.valuation w σ) (p.node.a.constructorViews j).fields
      (push ps ρ0) (w.fields.map (den M σ ρ)) := by
  let a := p.node.a
  let c := a.constructorViews j
  let τ := RecArguments.valuation w σ
  have hshape := selected_row p.node (NormDPlanBridge.bodies_of_group hE hmem p.node)
    w hwr hm j hcm
  obtain ⟨shapes, fuel, hfs, hd⟩ := p.node.h12 j
  have hsh : shapes = p.node.h14.shapesAt j :=
    fieldShapesFuel_unique hfs (p.node.h14.analyzed j)
  subst shapes
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hjm : j.val < a.minorTypes.length := by rw [hk]; exact j.isLt
  let R := a.minorTypes[j.val]'hjm
  have hderived : derivedMinor a j fuel (legacyShapes w.kinds) = some R := by
    rw [← hshape]
    exact hd.trans (List.getElem?_eq_getElem hjm)
  have hmin := minor_read M p w hwr hm j hj σ ρ ha
  have hg := TelFits_get a.minorTypes _ ms ha.minors_fit j.val hjm
  rw [hmin] at hg
  have hprefix : (mo :: ms.take j.val).length = 1 + j.val := by
    rw [List.length_cons, List.length_take,
      Nat.min_eq_left (show j.val ≤ ms.length by
        rw [ha.minors_length]; exact Nat.le_of_lt j.isLt)]
    exact Nat.add_comm _ _
  let Tend := foldApps (.const a.family.ref (policyFamilyLevels a.family))
    (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices)
  have hT : Rcic.Declarative.lift 0 (1 + j.val) (ctorFieldTelescope c) =
      policyPi (liftFields (1 + j.val) c.fields 0)
        (Rcic.Declarative.lift c.fields.length (1 + j.val) Tend) := by
    change Rcic.Declarative.lift 0 (1 + j.val) (policyPi c.fields Tend) = _
    rw [lift_policyPi, Nat.zero_add]
  have hlen : (liftFields (1 + j.val) c.fields 0).length =
      (legacyShapes w.kinds).length := by
    rw [liftFields_length', ← hshape]
    exact (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs).symm
  have hfields := original_fields_of_witness M τ σ p.node.E0 fuel
    a.family.parameters.length w ρ (push (mo :: ms.take j.val) (push ps ρ0))
    (Mx := .bvar j.val)
    (acc := foldApps (.const (a.family.ref + 1 + j.val) (policyFamilyLevels a.family))
      (policyParameterLocals a.family.parameters.length (1 + j.val)))
    (T := Rcic.Declarative.lift 0 (1 + j.val) (ctorFieldTelescope c))
    (R := R) hderived hg hneR (liftFields (1 + j.val) c.fields 0)
    (Rcic.Declarative.lift c.fields.length (1 + j.val) Tend) hT hlen
  apply (TelFits_liftFields M τ (mo :: ms.take j.val) (push ps ρ0)
    c.fields [] (w.fields.map (den M σ ρ))).mp
  rw [hprefix]
  exact hfields

/-- All argument and original-field premises are now produced from the
installed left application and the two literal same-target memberships. -/
theorem arguments_with_fields_of_nonempty (M : Interp.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hRec : ∀ vs, Equiv (M.μ p.rr vs)
      (EvalPlanValue.memberValue M (σOf vs) p p.rm))
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {X : PSet.{4}}
    (ml : den M σ ρ (iotaLhsOf w) ∈ Ed M X)
    (mr : den M σ ρ (iotaRhsOf w) ∈ Ed M X)
    (hne : ¬ Equiv (den M σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, RecArguments.Arguments M p w σ ρ ps mo ms is ∧
      TelFits M (RecArguments.valuation w σ) (p.node.a.constructorViews j).fields
        (push ps ρ0) (w.fields.map (den M σ ρ)) := by
  obtain ⟨ps, mo, ms, is, ha⟩ := RecArguments.of_nonempty M p hRec w hwr hm σ ρ hne
  have hneR : ¬ Equiv (den M σ ρ (iotaRhsOf w)) pempty := by
    intro he
    exact hne ((rhs_eq_ed_pempty mr ml he).symm.trans he)
  exact ⟨ps, mo, ms, is, ha,
    fields_of_arguments M p fm ctors hE hmem w hwr hm j hj hcm σ ρ ha hneR⟩

end Rcic.F3.PSet.RecursorFieldArguments

#print axioms Rcic.F3.PSet.RecursorFieldArguments.selected_row
#print axioms Rcic.F3.PSet.RecursorFieldArguments.minor_read
#print axioms Rcic.F3.PSet.RecursorFieldArguments.fields_of_arguments
#print axioms Rcic.F3.PSet.RecursorFieldArguments.arguments_with_fields_of_nonempty
