import rcic.ScmSrcGroupsFunRecEntryCheck
import rcic.RcicTypedIdxAdmitted
import rcic.RcicIotaShapeStable
import rcic.ScmSrcGroupsKernelRfl

/-! Base module for the ValueAt half of `ScmSrcGroupsFunRecTyped`:
the judgment-form ι descriptor clause at slot 143 plus the structural
lemmas that let the nine-constructor `recIdxAdmittedTB` check be decomposed
into small per-constructor `kernel_rfl_theorem` leaves.

The whole-`recIdxAdmittedTB` evaluation for the ValueAt admission exceeds
Lean 4.14's deterministic kernel budget in one pass — and a file containing
all ~70 component evaluations exceeds the cumulative budget the kernel
spends on one module.  The conjunct structure is therefore evaluated
componentwise: `iotaWitnessStableB`'s three factors are

* `fields.all (constsMemberFuel E (fuel+1))` — the field-domain sweep,
* `(fieldBvars nf).all (constsMemberFuel E (fuel+1))` — a bare-bvar sweep,
  proven once for all constructors by `fieldBvars_all`,
* `constsMemberFuel E (fuel+1) (lift … (ctorFieldTelescope c))` — the lifted
  telescope, decomposed by `Rcic.Declarative.constsMemberFuel_lift`,
  `Rcic.Declarative.policyPi_eq_foldr`, and
  `constsMemberFuel_foldr_pi` into the field sweep (already proven) plus a
  small family-application result check (`constsMemberFuel_foldApps` splits
  the spine into the family const, the parameter bvars, and the result
  indices).

Only the field-domain sweep and the result-index sweep need per-constructor
kernel evaluation; the rest is rewriting. -/

open Rcic.Declarative Rcic.Scm.SrcG Rcic.Scm.SrcG.FunRecEntry
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecTyped

private theorem hresValueAt' (i : Fin aRecValueAt.constructors.length) :
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
  | ⟨k+9, h⟩ =>
      exact absurd h (by have : aRecValueAt.constructors.length = 9 := rfl; omega)

/-- ValueAt's ι descriptor clause, judgment form. -/
def vaIotaClause : IotaDescriptorClause (envPre 143) aRecValueAt :=
  admRecValueAt05.h14.toJudgment fun i => iotaLhsType_eq_05 rfl (hresValueAt' i)

/-! ### Structural helpers -/

-- `constsMemberFuel_lift` (lift is invisible to the closure check) and
-- `policyPi_eq_foldr` (`policyPi` is a right fold of `Expr.pi`) are NOT
-- restated here: both live in `Rcic.Declarative`
-- (`RcicIotaShapeStable`/`RcicTypedIdxAdmitted`) and reach this file via
-- `open Rcic.Declarative`.

/-- `constsMemberFuel` over a Π telescope is the domain sweep and the body. -/
theorem constsMemberFuel_foldr_pi (E : ResolvedEnv) (n : Nat) :
    ∀ (xs : List (Expr Nat)) (b : Expr Nat),
      constsMemberFuel E n (xs.foldr Expr.pi b) =
        (xs.all (constsMemberFuel E n) && constsMemberFuel E n b) := by
  intro xs b
  induction xs with
  | nil => cases n <;> simp [constsMemberFuel]
  | cons x xs ih =>
      cases n with
      | zero => simp [constsMemberFuel]
      | succ n =>
          simp only [List.foldr_cons, constsMemberFuel, ih, List.all_cons,
            Bool.and_assoc]

/-- `constsMemberFuel` over an application spine is the head check and the
argument sweep. -/
theorem constsMemberFuel_foldApps (E : ResolvedEnv) (n : Nat) :
    ∀ (xs : List (Expr Nat)) (f : Expr Nat),
      constsMemberFuel E (n + 1) (foldApps f xs) =
        (constsMemberFuel E (n + 1) f && xs.all (constsMemberFuel E (n + 1))) := by
  intro xs f
  induction xs generalizing f with
  | nil => simp [foldApps]
  | cons x xs ih =>
      simp only [foldApps, ih, constsMemberFuel, List.all_cons, Bool.and_assoc]

/-- A `List` of bare bound variables sweeps clean at any positive fuel. -/
theorem constsMemberFuel_bvarMap (E : ResolvedEnv) (n : Nat) (g : Nat → Nat) :
    ∀ (l : List Nat), (l.map fun i => Expr.bvar (g i)).all
      (constsMemberFuel E (n + 1)) = true := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.map_cons, List.all_cons, constsMemberFuel, ih]

/-- `fieldBvars nf` is a `.bvar` list, so its closure sweep needs no
evaluation. -/
theorem fieldBvars_all (E : ResolvedEnv) (n nf : Nat) :
    (fieldBvars nf).all (constsMemberFuel E (n + 1)) = true := by
  unfold fieldBvars
  exact constsMemberFuel_bvarMap E n id ((List.range nf).reverse)

/-- `policyParameterLocals np nf` is a `.bvar` list. -/
theorem policyParameterLocals_all (E : ResolvedEnv) (n np nf : Nat) :
    (policyParameterLocals np nf).all (constsMemberFuel E (n + 1)) = true := by
  unfold policyParameterLocals
  exact constsMemberFuel_bvarMap E n (· + nf) ((List.range np).reverse)

/-- The family-head constant closes at any positive fuel once membership is
known: the family member is inductive, hence not transparent. -/
theorem constsMemberFuel_famConst {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) {E' : ResolvedEnv}
    (hm : E'.members a.family.ref = some a.family.member) (n : Nat)
    (ls : List Level) :
    constsMemberFuel E' (n + 1) (.const a.family.ref ls) = true := by
  simp only [constsMemberFuel, hm, a.family.hasClass, transparent]
  exact if_neg (by decide)

/-- `(extendEnv E r m).members r'` at an unrelated key is `E.members r'`. -/
theorem extendEnv_members_ne {E : ResolvedEnv} {r r' : Nat} {m : CheckedMember}
    (hne : r' ≠ r) :
    (extendEnv E r m).members r' = E.members r' :=
  if_neg hne

-- The recursor member's closure conjuncts of `recIdxAdmittedTB` at ValueAt:
-- freshness, the recursor class, and the member's own type closure.
kernel_rfl_theorem vaFresh143 : (envPre 143).members 143 = none

kernel_rfl_theorem vaRecClosed :
  exprClosedAt 0 recValueAt.mtype = true

/-- The recursor member of `aRecValueAt` sits at 143 ≠ 133, so the extended
environment still finds the family member. -/
theorem vaFamMemX :
    (extendEnv (envPre 143) 143 recValueAt).members aRecValueAt.family.ref =
      some aRecValueAt.family.member := by
  rw [extendEnv_members_ne (by decide : aRecValueAt.family.ref ≠ 143)]
  exact aRecValueAt.family.present

/-- The field-domain telescope conjunct at each ValueAt constructor, reduced
to the field sweep and the small family-application result.  Parameterized
over the check environment so one statement serves both the base and the
extended environment. -/
theorem vaTel0 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨0, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨0, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨0, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨0, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨0, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨0, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨0, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel1 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨1, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨1, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨1, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨1, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨1, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨1, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨1, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel2 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨2, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨2, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨2, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨2, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨2, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨2, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨2, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel3 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨3, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨3, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨3, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨3, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨3, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨3, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨3, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel4 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨4, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨4, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨4, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨4, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨4, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨4, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨4, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel5 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨5, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨5, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨5, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨5, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨5, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨5, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨5, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel6 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨6, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨6, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨6, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨6, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨6, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨6, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨6, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel7 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨7, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨7, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨7, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨7, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨7, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨7, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨7, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

theorem vaTel8 (E' : ResolvedEnv) :
    constsMemberFuel E' (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)
      (lift 0 ((aRecValueAt.constructorViews ⟨8, by decide⟩).fields.length + 1 +
          aRecValueAt.constructors.length + aRecValueAt.family.indices.length)
        (ctorFieldTelescope (aRecValueAt.constructorViews ⟨8, by decide⟩))) =
    ((aRecValueAt.constructorViews ⟨8, by decide⟩).fields.all
      (constsMemberFuel E' (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)) &&
      constsMemberFuel E' (vaIotaClause.fuelAt ⟨8, by decide⟩ + 1)
        (foldApps (.const aRecValueAt.family.ref
            (policyFamilyLevels aRecValueAt.family))
          (policyParameterLocals
            (aRecValueAt.constructorViews ⟨8, by decide⟩).parameters.length
            (aRecValueAt.constructorViews ⟨8, by decide⟩).fields.length ++
            (aRecValueAt.constructorViews ⟨8, by decide⟩).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, constsMemberFuel_foldr_pi]

/-- `Rcic.Declarative.recIdxCtorB` (`recIdxAdmittedTB`'s per-constructor
conjunct, public in `RcicTypedIdxAdmitted`) specialized to
`aRecValueAt`/`vaIotaClause`, spelled as a public Boolean so each
constructor's check can be assembled from kernel-evaluated leaves. -/
def vaCtorCheckB (i : Fin aRecValueAt.constructors.length) : Bool :=
  recIdxCtorB aRecValueAt vaIotaClause i

end Rcic.Scm.SrcG.FunRecTyped
