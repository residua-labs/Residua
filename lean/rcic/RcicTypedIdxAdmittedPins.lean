import rcic.RcicTypedIdxAdmitted
import rcic.RcicTypedGroupPins
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec
import rcic.RcicTypedDeltaRecPins

namespace Rcic.Declarative

/-- Nat's descriptor satisfies the typed recursor/index obligation. -/
def natRecIdxAdmittedT : RecursorGroupIdxAdmittedT natGroupAdmitted natIotaClause :=
  .ofCheck natGroupAdmitted natIotaClause (by with_unfolding_all rfl)

/-- List's descriptor satisfies the typed recursor/index obligation. -/
def listRecIdxAdmittedT : RecursorGroupIdxAdmittedT listGroupU listIotaClauseU :=
  .ofCheck listGroupU listIotaClauseU (by with_unfolding_all rfl)

/-- Vec's descriptor satisfies the typed recursor/index obligation. -/
def vecRecIdxAdmittedT : RecursorGroupIdxAdmittedT vecGroupU vecIotaClauseU :=
  .ofCheck vecGroupU vecIotaClauseU (by with_unfolding_all rfl)

/-- The δ-reached `Id F` field satisfies the typed recursor/index obligation. -/
def drRecIdxAdmittedT : RecursorGroupIdxAdmittedT drGroupAdmitted drIotaClause :=
  .ofCheck drGroupAdmitted drIotaClause (by with_unfolding_all rfl)

private def natSuccFin : Fin natGroupAdmitted.constructors.length := ⟨1, by decide⟩

def natSuccShapeWitness : IotaWitnessS (extendEnv natEnvPrefix 3 natRecMemberU) :=
  (natRecIdxAdmittedT.covered natSuccFin).1

/-- `bound` identifies the canonical Nat successor witness with constructor one
and Nat's admitted successor schema. -/
theorem natSuccShapeWitness_bound :
    ∃ i : Fin natGroupAdmitted.constructors.length,
      i.val = 1 ∧ natSuccShapeWitness.ctorIdx = i.val ∧
      natSuccShapeWitness.shapes = natIotaClause.shapesAt i ∧
      iotaSchemaAt natGroupAdmitted i (natIotaClause.fuelAt i)
        (natIotaClause.shapesAt i) = some natSuccShapeWitness.schema := by
  have hc := (natRecIdxAdmittedT.covered natSuccFin).2
  have hb := natRecIdxAdmittedT.bound (fun _ _ h => h) natSuccShapeWitness
    hc.1 hc.2.1
  rcases hb with ⟨i, hi, hshapes, hschema⟩
  refine ⟨i, ?_, hi, hshapes, hschema⟩
  have hctor : natSuccShapeWitness.ctorIdx = 1 := hc.2.2.1
  omega

/-! ## (bad-group) a field whose head is not a member of the recursor's group

`BadS : Sort 1 := .const 99 []` at `0` — a transparent definition declared before
the group whose δ body names ref `99`, a declaration absent from the
environment — then `G : Sort 1` at `1`, `mk : BadS → G` at `2`, `G.rec` at `3`.
The field `BadS` as stored is typable (its signature is `Sort 1`; `HasTy` never
consults the body), positivity-permitted as `.nonrecursive` (δ leaves a
non-family head), the minor is the canonical `Π (x : BadS), motive (mk x)`, and
the ι equation `G.rec motive minor (mk x) = minor x` is typed — every
declarative admission clause accepts the group.

The one check that refuses is `iotaWitnessStableB`'s `constsMemberFuel`
conjunct inside `recIdxCtorB`: it unfolds `BadS`'s transparent body, meets
`.const 99`, and `badMkEnv.members 99 = none` fails the closure check —
`recIdxAdmittedTB` returns `false`. This is the malformed-group negative
control for `RecursorGroupIdxAdmittedT.ofCheck`'s hypothesis: a bare non-member
field cannot be written (the view's `domainsTyped` would demand a typing of the
head), so the counterexample reaches the non-member through δ, exactly as
`RcicIotaShapeStablePins.missingHeadField` does at the `constsMemberFuel`
level. -/

/-- `BadS : Sort 1 := .const 99 []` — a transparent definition whose δ body names
    a declaration absent from every environment below. -/
def badHeadMember : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ .zero), some (.const 99 [])⟩

/-- `G : Sort 1` — the malformed group's family. -/
def badFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- the field `BadS`, whose stored head is a declaration outside the group. -/
def badField : Expr Nat := .const 0 []

/-- `mk : BadS → G` — the group's one constructor. -/
def badMkMember : CheckedMember := ⟨.constructorM, 0, .pi badField (.const 1 []), none⟩

/-- the motive's type, `G → Sort u`. -/
def badMotTy : Expr Nat := .pi (.const 1 []) (.sort (.param 0))

/-- the canonical nonrecursive minor, `Π (x : BadS), motive (mk x)`, under the motive. -/
def badMinorTy : Expr Nat :=
  .pi badField (.app (.bvar 1) (.app (.const 2 []) (.bvar 0)))

/-- `G.rec`'s stored type, `Π (P : G → Sort u) (m : Π x : BadS, P (mk x)) (t : G), P t`. -/
def badRecTy : Expr Nat :=
  .pi badMotTy (.pi badMinorTy (.pi (.const 1 []) (.app (.bvar 2) (.bvar 0))))

def badRecMember : CheckedMember := ⟨.recursorM, 1, badRecTy, none⟩

def badBase : ResolvedEnv := extendEnv emptyEnv 0 badHeadMember
def badFamEnv : ResolvedEnv := extendEnv badBase 1 badFamMember
def badMkEnv : ResolvedEnv := extendEnv badFamEnv 2 badMkMember
def badRecEnv : ResolvedEnv := extendEnv badMkEnv 3 badRecMember

def badFamView : PolicyFamilyView badMkEnv where
  ref := 1
  member := badFamMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the field at `Sort 1`: `BadS`'s stored signature, its body not consulted. -/
def badFieldTy : HasTy badMkEnv 0 [] badField (.sort (.succ .zero)) :=
  HasTy.const [] 0 [] badHeadMember rfl rfl (fun _ hx => nomatch hx)

def badMkView : PolicyConstructorView badMkEnv badFamView badMkMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [badField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlt : j.val < 1 := j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simpa [hj, policyPrefixContext] using badFieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- the malformed group as a recursor elimination admission: same shape as
    `drGroupAdmitted`, one nonrecursive field. -/
def badGroupAdmitted : RecursorEliminationAdmitted badMkEnv 3 badRecMember where
  family := badFamView
  constructors := [badMkMember]
  constructorViews
    | ⟨0, _⟩ => badMkView
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [badMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

/-- the stored minor IS the derived one: the descriptor is canonical except for
    the field's closure failure. -/
theorem badMinorMatch : MinorPremisesMatch badGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- the equation's context: `x : BadS`, the minor, the motive. -/
def badIotaCtx : LCtx := [.assumption badField, .assumption badMinorTy, .assumption badMotTy]

/-- the schema admission derives: `minor x`. -/
def badSchema : Expr Nat := .app (.bvar 1) (.bvar 0)

/-- the equation's type: `motive (mk x)`. -/
def badEqTy : Expr Nat := .app (.bvar 2) (.app (.const 2 []) (.bvar 0))

theorem badSchema_derived :
    iotaSchemaAt badGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] = some badSchema := rfl

theorem badEquation_shape :
    equationDoms badGroupAdmitted ⟨0, by decide⟩ = some [badMotTy, badMinorTy, badField] ∧
    iotaEquationType badGroupAdmitted ⟨0, by decide⟩ = badEqTy := ⟨rfl, rfl⟩

/-- `minor x` at `motive (mk x)` in the derivation scope: the malformed head is
    never unfolded — `HasTy` reads stored types only. -/
def badIotaTy : HasTy badRecEnv 1 badIotaCtx badSchema badEqTy := by
  have hMin : HasTy badRecEnv 1 badIotaCtx (.bvar 1) (lift 0 2 badMinorTy) :=
    HasTy.bvar _ 1 _ rfl
  have hX : HasTy badRecEnv 1 badIotaCtx (.bvar 0) badField := HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _ hMin hX

def badIota : IotaEquationTyped badGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  unfold IotaEquationTyped
  rw [badEquation_shape.1, badSchema_derived]
  exact badIotaTy

def badIotaClause : IotaDescriptorClause badMkEnv badGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => badIota

/-- the failing conjunct, isolated: `BadS`'s δ body is not `badMkEnv`-closed. -/
theorem badField_constsMemberFuel_false :
    constsMemberFuel badMkEnv 9 badField = false := by
  simp [constsMemberFuel, badField, badMkEnv, badFamEnv, badBase, emptyEnv,
    extendEnv, badHeadMember, transparent, instantiateLevels]

/-- NEGATIVE pin: `recIdxAdmittedTB` refuses the malformed group. Every clause of
    the declarative admission accepts it — the family is present, `mk`'s stored
    type is the canonical `BadS → G`, the minor is the derived one, and the ι
    equation is typed — but `recIdxCtorB`'s `iotaWitnessStableB` unfolds `BadS`
    to `.const 99`, a declaration with no member, so the field-analysis and
    schema inputs are not closed under the environment and the group's
    recursor/index obligation cannot be constructed by `ofCheck`. -/
theorem pin_recIdxAdmittedTB_badGroup :
    recIdxAdmittedTB badGroupAdmitted badIotaClause = false := by
  with_unfolding_all rfl

end Rcic.Declarative
