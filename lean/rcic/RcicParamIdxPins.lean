import rcic.RcicAnnIotaCorrW

/-!
# S4/S5 — parameter-referencing family indices: the `iotaOpenRhs` lift, found then fixed

**S4 found the defect; R6a (this file's post-fix state) repaired it.**  `iotaOpenRhs`
(05 §14) instantiates the canonical field telescope and emits the schema in `instPrefix`
space — where the field markers `fbᵢ = .bvar (fl-1-i)` occupy the lowest `fl` slots and
`preMajorBvars` counts the pre-major entries past them (`bvar (fl + count - 1 - i)`).  The
telescope was introduced with `lift 0 (1 + nMinors + nindices)` (`lift 0 C`): a parameter
reference `bvar (j + np-1-p)` in domain `j` became `bvar (count-1-p)` after the
field-binder instantiations — **`fl` short of `bvar (fl + count-1-p)`, the marker the
`instPrefix`/`preMajorBvars` convention requires.**  Anything `familyIdx` keeps — the
index arguments of a `.recursive` field — mis-instantiated every param-reference it
contained: emitted `bvar (count-1-p)` landed on `pm[fl+p]` instead of `pm[p]`.  The fix
lifts by `fields.length + 1 + nMinors + nindices` at the generator and every view-level
sibling (`iotaSchemaAt`, `iotaSchemaAtIn`, the fuel-stability statement replicas).

The pin env `piEnv` exercises the repaired class end-to-end.  `N` at `0` (axiom),
`g : Π (_ : Sort 1), N` at `1` (axiom), and the one-constructor group

```
I2   : Π (P : Sort 1) (i : N), Sort 1                    at 2
mk   : Π (P : Sort 1) (a : I2 P (g P)), I2 P (g P)       at 3
I2.rec                                                   at 4
```

`mk`'s single field is `.recursive 0` (`pi_fieldAnalyze`), and its family index `g P`
**mentions the constructor parameter**.  Post-fix:

* **admission's own equation types** (`piSchema_derived`, `piIota_correct_conv`,
  `piIota_correct_syn`): `iotaSchemaAt` now derives
  `m a (I2.rec P M m (g P) a)` — the recursive call's index is `g` of the **parameter**
  (`bvar 4` in the equation context) — and `tyAtC`/`synCheck` accept it.
* **the group is admissible — `EnvWfT piEnv`** (`pin_envWfT_piEnv`): `piIotaTy`
  discharges `IotaEquationTyped` in the legacy judgment (a `HasTy` app-chain whose
  `instantiate0` decrements re-mark the lifted param slots), `piRecTyped` discharges
  `IotaEquationTypedT` through `tyAtC`, and `piMembersT` carries the group through
  `GroupMembersT`.  This is the **positive pin** R6a asked for: the class the defective
  lift excluded is now inside `EnvWfT`.
* **every recognizer arm passes** (`pin_iotaWitnessSAnnB_piEnv`,
  `pin_iotaWitnessSAnnDArm_piEnv`, `pin_iotaWitnessSAnnDArmW_piEnv`,
  `pin_iotaWitnessSAnnDB_piEnv`, `pin_iotaWitnessSAnnDW_piEnv`): `iotaRhsOfS wPi` is now
  the typed schema (`piRhs_is_schemaCorrect`), and each arm's `rhsEq` agrees with the
  `familyIdx`-of-instantiated walk (`g pm[0]`).  `wPi.shapes = [.recursive 0]` — outside
  S6's `.frec` gate.
* **the historical emission is retained as a diagnostic** (`piIota_conv_refused`,
  `piIota_syn_refused`): `piSchemaEq` — `g` of the **motive** (`bvar 3`), what the
  `fl`-short lift produced — is still refused by both checkers, measuring exactly the
  defect removed.
* **the per-env universal discharges** (`envCorrAnnB_piEnv`, `envCorrAnnDW_piEnv`):
  EVERY `IotaWitnessS` of `piEnv` annotates — the recognizer verdicts at `wPi` lift
  to `∀ w, iotaWitnessSAnnB piEnv w = true`, hence `EnvCorrAnnCert` and a fortiori
  `EnvCorrAnnDW`.  The enumeration pins `np = ni = 1` through `hmajorTy` (the
  family's one index slot refuses the `np ∈ {0, 2}` readings), then the B-arm
  computes through literally: the repaired schema instantiated by `instPrefix`
  and the `familyIdx`-of-`applyTel` walk meet at `g pm[0]`.  The generic
  `EnvWfT → EnvCorrAnnDW` universal still rests on the admissible-side
  σ-correspondence (`iotaArgs = rhsArgsS` against `iotaOpenRhs`) — batch 22's
  in-flight 3b-2b in the glm-nofunrec lane — but the env whose class the lift
  excluded is now a discharged instance.
-/

namespace Rcic.Declarative.Ann
open Rcic.Declarative

/-! ## (1) the environment -/

def axNMember : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩
def axGMember : CheckedMember :=
  ⟨.axiomM, 0, .pi (.sort (.succ .zero)) (.const 0 []), none⟩

def i2App (p i : Nat) : Expr Nat :=
  .app (.app (.const 2 []) (.bvar p)) (.bvar i)
def gApp (k : Nat) : Expr Nat := .app (.const 1 []) (.bvar k)
def i2AppG (p i : Nat) : Expr Nat :=
  .app (.app (.const 2 []) (.bvar p)) (gApp i)

/-- `I2 : Π (P : Sort 1) (i : N), Sort 1`. -/
def piFamType : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.const 0 []) (.sort (.succ .zero)))

/-- `mk : Π (P : Sort 1) (a : I2 P (g P)), I2 P (g P)`. -/
def piMkType : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (i2AppG 0 0) (i2AppG 1 1))

/-- the derived minor: `Π (a : I2 P (g P)) (ih : M (g P) a), M (g P) (mk P a)`. -/
def piMinorTy : Expr Nat :=
  .pi (.app (.app (.const 2 []) (.bvar 1)) (gApp 1))
    (.pi (.app (.app (.bvar 1) (gApp 2)) (.bvar 0))
      (.app (.app (.bvar 2) (gApp 3))
           (.app (.app (.const 3 []) (.bvar 3)) (.bvar 1))))

/-- `I2.rec : Π (P) (M : Π (i : N) (x : I2 P i), Sort p₀)
    (m : Π (a : I2 P (g P)) (ih : M (g P) a), M (g P) (mk P a))
    (i : N) (x : I2 P i), M i x` — the canonical
  `policyRecursorType` at one parameter, one index, one minor. -/
def piRecType : Expr Nat :=
  .pi (.sort (.succ .zero))
   (.pi (.pi (.const 0 [])
          (.pi (i2App 1 0) (.sort (.param 0))))
    (.pi piMinorTy
      (.pi (.const 0 [])
       (.pi (i2App 3 0)
        (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))

def piFamMember : CheckedMember := ⟨.inductiveM, 0, piFamType, none⟩
def piMkMember  : CheckedMember := ⟨.constructorM, 0, piMkType, none⟩
def piRecMember : CheckedMember := ⟨.recursorM, 1, piRecType, none⟩

def piB0 : ResolvedEnv := extendEnv emptyEnv 0 axNMember
def piB1 : ResolvedEnv := extendEnv piB0 1 axGMember
def piFamEnv : ResolvedEnv := extendEnv piB1 2 piFamMember
def piMkEnv : ResolvedEnv := extendEnv piFamEnv 3 piMkMember
def piEnv : ResolvedEnv := extendEnv piMkEnv 4 piRecMember

theorem piFamEnv_members (c : Nat) :
    piFamEnv.members c = if c = 2 then some piFamMember
      else if c = 1 then some axGMember else if c = 0 then some axNMember
      else none := rfl

theorem piMkEnv_members (c : Nat) :
    piMkEnv.members c = if c = 3 then some piMkMember
      else if c = 2 then some piFamMember
      else if c = 1 then some axGMember else if c = 0 then some axNMember
      else none := rfl

/-- the field is `.recursive 0`, and `familyIdx` keeps `g P` — an index argument
    mentioning the constructor parameter. -/
theorem pi_fieldAnalyze :
    fieldAnalyze piFamEnv 8 2 0 1 1 1
      (.app (.app (.const 2 []) (.bvar 0)) (gApp 0)) =
      .permitted (.recursive 0) [gApp 0] := rfl

/-! ## (2) the admission views -/

def piNTy (E : ResolvedEnv) (h0 : E.members 0 = some axNMember) (Γ : LCtx) :
    HasTy E 0 Γ (.const 0 []) (.sort (.succ .zero)) :=
  HasTy.const Γ 0 [] axNMember h0 rfl (fun _ h => nomatch h)

def piGTy (E : ResolvedEnv) (h1 : E.members 1 = some axGMember) (Γ : LCtx) :
    HasTy E 0 Γ (.const 1 []) (.pi (.sort (.succ .zero)) (.const 0 [])) :=
  HasTy.const Γ 1 [] axGMember h1 rfl (fun _ h => nomatch h)

def piI2Ty (E : ResolvedEnv) (h2 : E.members 2 = some piFamMember) (Γ : LCtx) :
    HasTy E 0 Γ (.const 2 [])
      (.pi (.sort (.succ .zero)) (.pi (.const 0 []) (.sort (.succ .zero)))) :=
  HasTy.const Γ 2 [] piFamMember h2 rfl (fun _ h => nomatch h)

/-- `I2 (bvar 0) (g (bvar 0)) : Sort 1` under `[P : Sort 1]`. -/
def piFieldTy (E : ResolvedEnv) (_h0 : E.members 0 = some axNMember)
    (h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember) :
    HasTy E 0 [LocalDecl.assumption (.sort (.succ .zero))]
      (.app (.app (.const 2 []) (.bvar 0)) (gApp 0)) (.sort (.succ .zero)) :=
  HasTy.app _ (.app (.const 2 []) (.bvar 0)) (gApp 0) (.const 0 [])
    (.sort (.succ .zero))
    (HasTy.app _ (.const 2 []) (.bvar 0) (.sort (.succ .zero))
      (.pi (.const 0 []) (.sort (.succ .zero))) (piI2Ty E h2 _)
      (HasTy.bvar _ 0 _ rfl))
    (HasTy.app _ (.const 1 []) (.bvar 0) (.sort (.succ .zero)) (.const 0 [])
      (piGTy E h1 _) (HasTy.bvar _ 0 _ rfl))

def piFamView (E : ResolvedEnv) (h0 : E.members 0 = some axNMember)
    (_h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember) :
    PolicyFamilyView E where
  ref := 2
  member := piFamMember
  present := h2
  hasClass := rfl
  parameters := [.sort (.succ .zero)]
  indices := [.const 0 []]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i with
      | ⟨0, _⟩ => .succ (.succ .zero)
      | ⟨1, _⟩ => .succ .zero
      | ⟨k+2, h⟩ => absurd h (by simp at h; omega)
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => exact rfl
      | ⟨1, _⟩ => exact rfl
      | ⟨k+2, h⟩ => exact absurd h (by simp at h; omega)
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ =>
          show HasTy E 0 [] (.sort (.succ .zero))
            (.sort (.succ (.succ .zero)))
          exact HasTy.sort _ _
      | ⟨1, _⟩ =>
          show HasTy E 0 [LocalDecl.assumption (.sort (.succ .zero))]
            (.const 0 []) (.sort (.succ .zero))
          exact piNTy E h0 _
      | ⟨k+2, h⟩ => exact absurd h (by simp at h; omega)
  }

def piMkView (E : ResolvedEnv) (h0 : E.members 0 = some axNMember)
    (h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember) :
    PolicyConstructorView E (piFamView E h0 h1 h2) piMkMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero)]
  fields := [.app (.app (.const 2 []) (.bvar 0)) (gApp 0)]
  resultIndices := [gApp 1]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i with
      | ⟨0, _⟩ => .succ (.succ .zero)
      | ⟨1, _⟩ => .succ .zero
      | ⟨k+2, h⟩ => absurd h (by simp at h; omega)
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => exact rfl
      | ⟨1, _⟩ => exact rfl
      | ⟨k+2, h⟩ => exact absurd h (by simp at h; omega)
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ =>
          show HasTy E 0 [] (.sort (.succ .zero))
            (.sort (.succ (.succ .zero)))
          exact HasTy.sort _ _
      | ⟨1, _⟩ =>
          show HasTy E 0 [LocalDecl.assumption (.sort (.succ .zero))]
            (.app (.app (.const 2 []) (.bvar 0)) (gApp 0)) (.sort (.succ .zero))
          exact piFieldTy E h0 h1 h2
      | ⟨k+2, h⟩ => exact absurd h (by simp at h; omega)
  }
  parameterMirrors := fun i => by
    match i with
    | ⟨0, _⟩ =>
        show Conv E 0 [] (.sort (.succ .zero)) (.sort (.succ .zero))
        exact Conv.refl _ _
    | ⟨k+1, h⟩ => exact absurd h (by simp at h)
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    rw [he]; rfl

theorem piMkBefore : CtorBeforeRecursors piFamEnv piMkMember := by
  refine ⟨2, rfl, ?_⟩
  intro rr rm hm hk _
  rw [piFamEnv_members] at hm
  by_cases h2 : rr = 2
  · rw [if_pos h2] at hm
    cases hm
    exact absurd hk (by decide)
  · by_cases h1 : rr = 1
    · rw [if_neg h2, if_pos h1] at hm
      cases hm
      exact absurd hk (by decide)
    · by_cases h0 : rr = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hm
        cases hm
        exact absurd hk (by decide)
      · rw [if_neg h2, if_neg h1, if_neg h0] at hm
        cases hm

theorem piMkContig : CtorContiguous piFamEnv 3 piMkMember := by
  refine ⟨2, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd hr (by omega)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [piFamEnv_members] at hm
    by_cases h2 : c = 2
    · rw [if_pos h2] at hm
      cases hm
      exact absurd hc (by decide)
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hm
        cases hm
        exact absurd hc (by decide)
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hm
          cases hm
          exact absurd hc (by decide)
        · rw [if_neg h2, if_neg h1, if_neg h0] at hm
          cases hm

theorem piMkUniverse : FieldUniverseAdmitted (piMkView piFamEnv rfl rfl rfl) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem piMkFields :
    CtorFieldsPermitted (piMkView piFamEnv rfl rfl rfl) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 8, [gApp 0], pi_fieldAnalyze⟩

/-- the same field analysis at `piMkEnv` (the recursor-admission reads the
    view in the env it will extend). -/
theorem pi_fieldAnalyzeMkEnv :
    fieldAnalyze piMkEnv 8 2 0 1 1 1
      (.app (.app (.const 2 []) (.bvar 0)) (gApp 0)) =
      .permitted (.recursive 0) [gApp 0] := rfl

theorem piMkUniverseMk : FieldUniverseAdmitted (piMkView piMkEnv rfl rfl rfl) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem piMkFieldsMk :
    CtorFieldsPermitted (piMkView piMkEnv rfl rfl rfl) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 8, [gApp 0], pi_fieldAnalyzeMkEnv⟩

def piFamAdmitted : IndGroupAdmitted piB1 2 piFamMember :=
  .family rfl (piFamView piFamEnv rfl rfl rfl) rfl rfl
    (Or.inr uniformType_succ_zero)

def piMkAdmitted : IndGroupAdmitted piFamEnv 3 piMkMember :=
  .constructor (piFamView piFamEnv rfl rfl rfl)
    (piMkView piFamEnv rfl rfl rfl) rfl piMkBefore piMkContig
    piMkUniverse piMkFields

/-- the recursor-elimination record: every field discharges, including the
    `IotaDescriptorClause`'s `typed` obligation, which the corrected equation's
    right-hand side meets (`piIotaTy`/`piIotaClause` below). -/
def piGroupAdmitted : RecursorEliminationAdmitted piMkEnv 4 piRecMember where
  family := piFamView piMkEnv rfl rfl rfl
  constructors := [piMkMember]
  constructorViews
    | ⟨0, _⟩ => piMkView piMkEnv rfl rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [piMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := by decide
  recursorType := by decide
  recursorMclass := rfl

/-! ## (3) admission's own derived equation is ill-typed -/

/-- `peelPis`-of-`piRecType` minus the major, plus the lifted field — the
    equation context's domains, `[P, M, m, i, a]`. -/
def piDoms : List (Expr Nat) :=
  [.sort (.succ .zero),
   .pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))),
   piMinorTy, .const 0 [], i2AppG 3 3]

def piCtx : LCtx := assumptionCtx piDoms

/-- the equation's type: `M (g P) (mk P a)` in `[a, i, m, M, P]` context. -/
def piEqTy : Expr Nat :=
  .app (.app (.bvar 3) (gApp 4))
    (.app (.app (.const 3 []) (.bvar 4)) (.bvar 0))

/-- the schema the defective lift derived for `mk` (kept as a diagnostic):
    `m a (rec P M m (g M) a)` — the recursive call's index is `g` of the
    **motive** (`bvar 3`), where the parameter `bvar 4` belongs. -/
def piSchemaEq : Expr Nat :=
  .app (.app (.bvar 2) (.bvar 0))
    (.app (.app (.app (.app (.app (.const 4 [.param 0])
        (.bvar 4)) (.bvar 3)) (.bvar 2))
        (.app (.const 1 []) (.bvar 3))) (.bvar 0))

/-- the `fl`-shifted equation `iotaSchemaAt` now derives: `g P` (`bvar 4`),
    the marker `lift 0 (fields.length + C)` produces. -/
def piSchemaCorrect : Expr Nat :=
  .app (.app (.bvar 2) (.bvar 0))
    (.app (.app (.app (.app (.app (.const 4 [.param 0])
        (.bvar 4)) (.bvar 3)) (.bvar 2))
        (.app (.const 1 []) (.bvar 4))) (.bvar 0))

theorem piSchema_derived :
    iotaSchemaAt piGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 0] =
      some piSchemaCorrect := rfl

theorem piDoms_derived :
    equationDoms piGroupAdmitted ⟨0, by decide⟩ = some piDoms := rfl

theorem piEqTy_derived :
    iotaEquationType piGroupAdmitted ⟨0, by decide⟩ = piEqTy := rfl

/-- the conversion checker refuses the OLD emitted equation — `g` applied to
    the motive where `g P` belongs — retained to measure the removed defect. -/
theorem piIota_conv_refused :
    (tyAtC piEnv 1 8 piCtx piSchemaEq piEqTy).isSome = false := rfl

theorem piIota_syn_refused :
    (synCheck piEnv 1 piCtx piSchemaEq piEqTy).isSome = false := rfl

/-- the `fl`-shifted equation types at both checkers — and is what the
    generator now derives. -/
theorem piIota_correct_conv :
    (tyAtC piEnv 1 8 piCtx piSchemaCorrect piEqTy).isSome = true := rfl

theorem piIota_correct_syn :
    (synCheck piEnv 1 piCtx piSchemaCorrect piEqTy).isSome = true := rfl

/-! ## (4) the witness exists; every arm now passes it -/

/-- the canonical `IotaWitnessS` at `I2.rec`/`mk` over `piEnv`.  `hschema` pins
    `iotaOpenRhs`'s corrected output — its `iotaRhsOfS` is the typed schema, so
    `DerivedIotaT.of wPi` states the equation whose recursive call's index is
    `g` of the parameter. -/
def wPi : IotaWitnessS piEnv where
  recRef := 4
  ctorRef := 3
  ls := [.param 0]
  lsC := []
  recMember := piRecMember
  ctorMember := piMkMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := preMajorBvars 1 1 1 1
  fields := fieldBvars 1
  ctorParams := [.bvar 4]
  familyRef := 2
  famMember := piFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.sort (.succ .zero),
    .app (.app (.const 2 []) (.bvar 0)) (gApp 0)]
  ctorResult := .app (.app (.const 2 []) (.bvar 1)) (gApp 1)
  hpeel := rfl
  hfamApp := rfl
  recDoms := [.sort (.succ .zero),
    .pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))),
    piMinorTy, .const 0 [], i2App 3 0]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.recursive 0]
  hshapes := rfl
  schema := piSchemaCorrect
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : piEnv.members 0 = some axNMember := rfl
    have hmem1 : piEnv.members 1 = some axGMember := rfl
    have hmem2 : piEnv.members 2 = some piFamMember := rfl
    show iotaWitnessStableB piEnv 8
      [.app (.app (.const 2 []) (.bvar 0)) (gApp 0)] (fieldBvars 1)
      (lift 0 4 (ctorFieldTelRaw 1
        [.sort (.succ .zero),
         .app (.app (.const 2 []) (.bvar 0)) (gApp 0)]
        (.app (.app (.const 2 []) (.bvar 1)) (gApp 1)))) = true
    simp [iotaWitnessStableB, gApp, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem0, hmem1, hmem2, axNMember, axGMember,
      piFamMember, transparent, instantiateLevels])
  hschemaScope := rfl

/-- `iotaRhsOfS` now produces the typed schema: the S-witness's reduct is
    `m a (rec P M m (g P) a)` — the recursive call's index is `g` of the
    parameter, as `familyIdx` reads it. -/
theorem piRhs_is_schemaCorrect : iotaRhsOfS wPi = piSchemaCorrect := rfl

/-- outside S6's `.frec` gate: no `.recursive (_+1)` shape. -/
theorem wPi_not_frec :
    (wPi.shapes.any fun s => match s with | .recursive (_+1) => true | _ => false) = false := rfl

theorem pin_iotaWitnessSAnnB_piEnv : iotaWitnessSAnnB piEnv wPi = true := rfl

/-- the S3 arm (normalization at `domsFuelBound`) passes. -/
theorem pin_iotaWitnessSAnnDArm_piEnv :
    iotaWitnessSAnnDArm piEnv wPi = true := rfl

/-- the R5a W-arm (normalization at `w.fuel`) passes. -/
theorem pin_iotaWitnessSAnnDArmW_piEnv :
    iotaWitnessSAnnDArmW piEnv wPi = true := rfl

theorem pin_iotaWitnessSAnnDB_piEnv :
    iotaWitnessSAnnDB piEnv wPi = true := rfl

theorem pin_iotaWitnessSAnnDW_piEnv :
    iotaWitnessSAnnDW piEnv wPi = true := rfl

/-! ## (5) post-fix: `piEnv` is admissible — `EnvWfT piEnv`

The corrected schema is exactly the `fl`-shifted equation the checkers already
accepted, so `IotaDescriptorClause.typed` now discharges and the group is
admissible.  The `HasTy` tree below mirrors `fgIotaTyLegacy`'s: `lookupType`
lifts each stored domain by `i+1`, and each `.app`'s `instantiate0` decrement
re-marks the parameter references to `bvar 4` — ambient `P` in `piCtx`. -/

/-- the corrected equation in the legacy judgment:
    `m a (I2.rec P M m (g P) a) : M (g P) (mk P a)` in `[P, M, m, i, a]`. -/
def piIotaTy : HasTy piEnv 1 piCtx piSchemaCorrect piEqTy := by
  have hP : HasTy piEnv 1 piCtx (.bvar 4) (.sort (.succ .zero)) :=
    HasTy.bvar _ 4 _ rfl
  have hM : HasTy piEnv 1 piCtx (.bvar 3)
      (lift 0 4 (.pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))))) :=
    HasTy.bvar _ 3 _ rfl
  have hm : HasTy piEnv 1 piCtx (.bvar 2) (lift 0 3 piMinorTy) :=
    HasTy.bvar _ 2 _ rfl
  have ha : HasTy piEnv 1 piCtx (.bvar 0) (lift 0 1 (i2AppG 3 3)) :=
    HasTy.bvar _ 0 _ rfl
  have hG : HasTy piEnv 1 piCtx (.const 1 [])
      (.pi (.sort (.succ .zero)) (.const 0 [])) :=
    HasTy.const _ 1 [] axGMember rfl rfl (fun _ h => nomatch h)
  have hgP := HasTy.app _ _ _ _ _ hG hP
  have hRec : HasTy piEnv 1 piCtx (.const 4 [.param 0])
      (instantiateLevels [.param 0] piRecType) :=
    HasTy.const _ 4 [.param 0] piRecMember rfl rfl (by
      intro l hl
      have hl' : l = .param 0 := by simpa using hl
      subst hl'
      exact ⟨0, Or.inl rfl⟩)
  have h1 := HasTy.app _ _ _ _ _ hRec hP
  have h2 := HasTy.app _ _ _ _ _ h1 hM
  have h3 := HasTy.app _ _ _ _ _ h2 hm
  have h4 := HasTy.app _ _ _ _ _ h3 hgP
  have h5 := HasTy.app _ _ _ _ _ h4 ha
  have h6 := HasTy.app _ _ _ _ _ hm ha
  exact HasTy.app _ _ _ _ _ h6 h5

def piIotaLegacy : IotaEquationTyped piGroupAdmitted ⟨0, by decide⟩ 8
    [.recursive 0] := by
  unfold IotaEquationTyped
  rw [piDoms_derived, piSchema_derived]
  exact piIotaTy

theorem piCensus : CtorCensus piMkEnv 2 4 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [piMkEnv_members] at hc
    by_cases h3 : c = 3
    · exact ⟨by omega, by omega⟩
    · by_cases h2 : c = 2
      · rw [if_neg h3, if_pos h2] at hc
        cases hc
        exact absurd hk (by decide)
      · by_cases h1 : c = 1
        · rw [if_neg h3, if_neg h2, if_pos h1] at hc
          cases hc
          exact absurd hk (by decide)
        · by_cases h0 : c = 0
          · rw [if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hc
            cases hc
            exact absurd hk (by decide)
          · rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hc
            cases hc
  · intro h
    have hc : c = 3 := by omega
    subst hc
    exact ⟨piMkMember, rfl, rfl, rfl⟩

theorem piMinorMatch : MinorPremisesMatch piGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.recursive 0], 8, rfl, rfl⟩

def piIotaClause : IotaDescriptorClause piMkEnv piGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 0]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => piIotaLegacy

def piGroupRecursor : IndGroupAdmitted piMkEnv 4 piRecMember :=
  .recursor piGroupAdmitted rfl piCensus
    (fun i => match i with | ⟨0, _⟩ => piMkUniverseMk)
    (fun i => match i with | ⟨0, _⟩ => piMkFieldsMk)
    piMinorMatch piIotaClause

/-! ### the typed-environment chain -/

def piB0WfT : EnvWfT piB0 :=
  .axiom emptyEnv 0 (.sort (.succ .zero)) (.succ (.succ .zero)) .empty rfl
    (.sort [] _) (fun _ => rfl) rfl

def piB1WfT : EnvWfT piB1 :=
  .axiom piB0 1 (.pi (.sort (.succ .zero)) (.const 0 []))
    (.imax (.succ (.succ .zero)) (.succ .zero)) piB0WfT rfl
    (.pi [] _ _ _ _ (.sort [] _) (.const _ 0 [] axNMember rfl rfl rfl))
    (fun _ => rfl) rfl

def piFamTyT : HasTyT piB1 0 [] piFamType
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ (.succ .zero))))) :=
  .pi [] _ _ _ _ (.sort [] _)
    (.pi _ _ _ _ _ (.const _ 0 [] axNMember rfl rfl rfl) (.sort _ _))

/-- `I2 P (g P) : Sort 1` under a context with `P` at `bvar k`. -/
def piI2GTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    (h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember)
    (hP : HasTyT E n Γ (.bvar k) (.sort (.succ .zero))) :
    HasTyT E n Γ (.app (.app (.const 2 []) (.bvar k)) (gApp k))
      (.sort (.succ .zero)) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 2 [] piFamMember h2 rfl rfl) hP)
    (.app _ _ _ _ _ (.const _ 1 [] axGMember h1 rfl rfl) hP)

def piMkTyT : HasTyT piFamEnv 0 [] piMkType
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] _ _ _ _ (.sort [] _)
    (.pi _ _ _ _ _
      (piI2GTyT rfl rfl (.bvar _ 0 _ rfl))
      (piI2GTyT rfl rfl (.bvar _ 1 _ rfl)))

/-- the recursor type's sort, as the conversion checker reads it (normalized
    `imax`/`max` nest over the motive's `param 0`). -/
def piRecSortU : Level :=
  .imax (.succ (.succ .zero))
    (.imax (.succ (.max (.succ .zero) (.param 0)))
      (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0)))
        (.imax (.succ .zero) (.imax (.succ .zero) (.param 0)))))

theorem piRecTy_check :
    (tyAtC piMkEnv 1 16 [] piRecType (.sort piRecSortU)).isSome = true := rfl

def piRecTyT : HasTyT piMkEnv 1 [] piRecType (.sort piRecSortU) :=
  (tyAtC piMkEnv 1 16 [] piRecType (.sort piRecSortU)).get rfl

theorem piMkTypedE (E : ResolvedEnv) (h0 : E.members 0 = some axNMember)
    (h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember) :
    CtorTypedT (piMkView E h0 h1 h2) :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨HasTyT.sort _ _⟩
    | ⟨1, _⟩ => ⟨piI2GTyT h1 h2 (.bvar _ 0 _ rfl)⟩
    | ⟨k+2, h⟩ => absurd h (by simp [piMkView] at h; omega),
   fun i => match i with
    | ⟨0, _⟩ => ⟨TyConvT.refl _ _⟩⟩

theorem piFamTypedE (E : ResolvedEnv) (h0 : E.members 0 = some axNMember)
    (_h1 : E.members 1 = some axGMember) (h2 : E.members 2 = some piFamMember) :
    FamilyTypedT (piFamView E h0 _h1 h2) := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨HasTyT.sort _ _⟩
  | ⟨1, _⟩ => ⟨HasTyT.const _ 0 [] axNMember h0 rfl rfl⟩
  | ⟨k+2, h⟩ => absurd h (by simp [piFamView] at h; omega)

theorem piFamTyped : IndGroupTypedT piFamAdmitted := piFamTypedE piFamEnv rfl rfl rfl

theorem piMkTyped : IndGroupTypedT piMkAdmitted :=
  ⟨piFamTyped, piMkTypedE _ rfl rfl rfl⟩

/-- the recursor's typed content, with its ι equation typed in `HasTyT` by the
    conversion checker at the corrected schema. -/
theorem piRecTyped : IndGroupTypedT piGroupRecursor :=
  ⟨piFamTypedE piMkEnv rfl rfl rfl,
   fun i => match i with | ⟨0, _⟩ => piMkTypedE _ rfl rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 16 Γ e T) rfl⟩

def piMembersT :
    GroupMembersT piFamEnv piB1 [(2, piFamMember), (3, piMkMember), (4, piRecMember)]
      piEnv :=
  .cons _ 2 piFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    piFamAdmitted PUnit.unit _ piFamTyT (fun h => absurd h (by decide))
    piFamTyped
    (.cons _ 3 piMkMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
      rfl rfl rfl
      piMkAdmitted PUnit.unit _ piMkTyT (fun _ => ⟨piMkTyT⟩) piMkTyped
      (.cons _ 4 piRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
        rfl rfl rfl
        piGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ piRecTyT
        (fun h => absurd h (by decide)) piRecTyped (.nil _)))

/-- `N`, `g`, then `I2`, `mk`, `I2.rec` as one group step: the typed environment
    judgment now admits a group whose recursive field's family index mentions a
    constructor parameter — the class the defective lift excluded. -/
def piEnvWfT : EnvWfT piEnv :=
  .group piB1 2 piFamMember [(3, piMkMember)] 4 piRecMember piEnv piB1WfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl piMembersT

theorem pin_envWfT_piEnv : Nonempty (EnvWfT piEnv) := ⟨piEnvWfT⟩

/-! ## (6) the per-env correspondence discharge -/

/-- `piEnv`'s member table: membership pins ref AND member. -/
theorem piEnv_members {r : Nat} {m : CheckedMember}
    (h : piEnv.members r = some m) :
    (r = 0 ∧ m = axNMember) ∨ (r = 1 ∧ m = axGMember) ∨
      (r = 2 ∧ m = piFamMember) ∨ (r = 3 ∧ m = piMkMember) ∨
      (r = 4 ∧ m = piRecMember) := by
  match r with
  | 0 =>
      left
      rw [show piEnv.members 0 = some axNMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 1 =>
      right; left
      rw [show piEnv.members 1 = some axGMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 2 =>
      right; right; left
      rw [show piEnv.members 2 = some piFamMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 3 =>
      right; right; right; left
      rw [show piEnv.members 3 = some piMkMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 4 =>
      right; right; right; right
      rw [show piEnv.members 4 = some piRecMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | r + 5 =>
      rw [show piEnv.members (r + 5) = none from rfl] at h
      exact Option.noConfusion h

theorem list_quad_of_length_four {α : Type} {xs : List α}
    (h : xs.length = 4) : ∃ a b c d, xs = [a, b, c, d] := by
  match xs with
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => simp at h
  | [a, b, c] => simp at h
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | a :: b :: c :: d :: e :: _ => simp at h

/-- `∀ w, iotaWitnessSAnnB piEnv w = true` — `EnvCorrAnnCert piEnv`.  The
    stored field `I2 P (g P)` is δ-free, so the un-normalized `applyTel`
    telescope is already the walk's reading; the `hmajorTy` pin forces the
    `np = 1`/`ni = 1` reading of the `Π (P) (i : N)` family. -/
theorem envCorrAnnB_piEnv : EnvCorrAnnCert piEnv := by
  intro w
  have hfam : w.familyRef = 2 ∧ w.famMember = piFamMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      piEnv_members w.hfam
    · exact absurd (hm ▸ w.hfamK) (by decide)
    · exact absurd (hm ▸ w.hfamK) (by decide)
    · exact ⟨hr, hm⟩
    · exact absurd (hm ▸ w.hfamK) (by decide)
    · exact absurd (hm ▸ w.hfamK) (by decide)
  have hctor : w.ctorRef = 3 ∧ w.ctorMember = piMkMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      piEnv_members w.hctor
    · exact absurd (hm ▸ w.hctorK) (by decide)
    · exact absurd (hm ▸ w.hctorK) (by decide)
    · exact absurd (hm ▸ w.hctorK) (by decide)
    · exact ⟨hr, hm⟩
    · exact absurd (hm ▸ w.hctorK) (by decide)
  have hrec : w.recRef = 4 ∧ w.recMember = piRecMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      piEnv_members w.hrec
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact ⟨hr, hm⟩
  obtain ⟨hfR, hfM⟩ := hfam
  obtain ⟨hcR, hcM⟩ := hctor
  obtain ⟨hrR, hrM⟩ := hrec
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx
    rw [hrR, hfR] at h
    omega
  have hci : w.ctorIdx = 0 := by
    have h := w.hctorIdx
    rw [hcR, hfR] at h
    omega
  have hsum : w.nparams + w.nindices = 2 := by
    have h := w.hnidx
    rw [hfM] at h
    have hp : piCount piFamMember.mtype = 2 := rfl
    rw [hp] at h
    exact h
  have hflsum : w.nparams + w.fields.length = 2 := by
    have h := w.hnpar
    rw [hcM] at h
    have hp : piCount piMkMember.mtype = 2 := rfl
    rw [hp] at h
    exact h
  -- the recursor peel: `np + 1 + nM + ni + 1 = 5` doms
  have hrd : w.recDoms = [.sort (.succ .zero),
      .pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))),
      piMinorTy, .const 0 [], i2App 3 0] := by
    have h := w.hpeelRec
    rw [hrM] at h
    rw [show w.nparams + 1 + w.nMinors + w.nindices + 1 = 5 from by omega] at h
    have hp : peelPis 5 piRecMember.mtype = some
        ([.sort (.succ .zero),
          .pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))),
          piMinorTy, .const 0 [], i2App 3 0],
         .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := rfl
    rw [hp] at h
    exact (congrArg Prod.fst (Option.some.inj h)).symm
  -- hmajorTy at index np+1+nM+ni = 4 forces np = 1
  have hnp1 : w.nparams = 1 := by
    have hmaj := w.hmajorTy
    rw [show w.nparams + 1 + w.nMinors + w.nindices = 4 from by omega,
        hrd, hnM, hfR, hfM] at hmaj
    have hmaj' : i2App 3 0 = foldApps (Expr.const 2 [])
        ((List.range w.nparams).reverse.map
          (fun i => Expr.bvar (i + w.nindices + 1 + 1)) ++
          (List.range w.nindices).reverse.map Expr.bvar) := by
      have hp4 : ([Expr.sort (.succ .zero),
          .pi (.const 0 []) (.pi (i2App 1 0) (.sort (.param 0))),
          piMinorTy, .const 0 [], i2App 3 0] : List (Expr Nat))[4]? =
          some (i2App 3 0) := rfl
      rw [hp4] at hmaj
      exact Option.some.inj hmaj
    -- hmaj : i2App 3 0 = foldApps (const 2 (range 0).map param) (args)
    have hargs : ((List.range w.nparams).reverse.map
        (fun i => (Expr.bvar (i + w.nindices + 1 + 1) : Expr Nat)) ++
        (List.range w.nindices).reverse.map (Expr.bvar (R := Nat))) =
        [.bvar 3, .bvar 0] := by
      have hsp := congrArg appsSpine hmaj'
      rw [appsSpine_foldApps] at hsp
      simp only [i2App, appsSpine] at hsp
      rw [Prod.mk.injEq] at hsp
      exact hsp.2.symm
    -- case-split np ∈ {0,1,2}
    rcases (by omega :
        w.nparams = 0 ∨ w.nparams = 1 ∨ w.nparams = 2) with h0 | h1 | h2
    · have hni : w.nindices = 2 := by omega
      rw [h0, hni] at hargs
      simp only [List.range_zero, List.range, List.reverse, List.map,
        List.append] at hargs
      exact absurd hargs (by decide)
    · exact h1
    · have hni : w.nindices = 0 := by omega
      rw [h2, hni] at hargs
      simp only [List.range, List.range_zero, List.reverse_nil, List.map_nil,
        List.append_nil, List.map_cons, List.reverse_cons, List.reverse_reverse,
        List.map_append, List.map_map] at hargs
      exact absurd hargs (by decide)
  have hni1 : w.nindices = 1 := by omega
  have hfl1 : w.fields.length = 1 := by omega
  have hcd : w.ctorDoms = [.sort (.succ .zero), i2AppG 0 0] ∧
      w.ctorResult = i2AppG 1 1 := by
    have h := w.hpeel
    rw [hcM, show w.nparams + w.fields.length = 2 from by omega] at h
    have hp : peelPis 2 piMkMember.mtype =
        some ([.sort (.succ .zero), i2AppG 0 0], i2AppG 1 1) := rfl
    rw [hp] at h
    exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,
      (congrArg Prod.snd (Option.some.inj h)).symm⟩
  obtain ⟨pa, pb, pc, pd, hpm'⟩ := list_quad_of_length_four (by
    have h := w.hpre
    rw [hnp1, hnM, hni1] at h
    exact h)
  obtain ⟨f, hfl'⟩ := List.length_eq_one.mp hfl1
  obtain ⟨l, hls'⟩ := List.length_eq_one.mp (by
    have h := w.hlsLen
    rw [hrM] at h
    have ha : piRecMember.arity = 1 := rfl
    rw [ha] at h
    exact h)
  have hsh : w.shapes = [.recursive 0] := by
    have h := w.hshapes
    rw [hfR, hfM, hnp1, hni1, hcd.1] at h
    have hconc : fieldShapesFuel piEnv 8 2 piFamMember.arity 1 1 1
        [i2AppG 0 0] = some [.recursive 0] := wPi.hshapes
    exact fieldShapesFuel_agree piEnv h hconc
  have hsc : w.schema = piSchemaCorrect := by
    have h := w.hschema
    rw [hrR, hrM, hnp1, hnM, hni1, hci, hfl', hcd.1, hcd.2, hsh] at h
    have hconc : iotaOpenRhs piEnv 8
        (.const 4 (canonRecLevels piRecMember.arity))
        (.bvar (1 + 1 + (1 - 1 - 0)))
        (preMajorBvars 1 1 1 1) 1 1
        [.recursive 0] (fieldBvars 1)
        (lift 0 (1 + 1 + 1 + 1)
          (ctorFieldTelRaw 1 [.sort (.succ .zero), i2AppG 0 0]
            (i2AppG 1 1))) = some piSchemaCorrect := wPi.hschema
    exact iotaOpenRhs_agree piEnv h hconc
  -- the recognizer
  show iotaWitnessSAnnB piEnv w = true
  unfold iotaWitnessSAnnB
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- directFragCheck on [i2AppG 0 0]: the field is a literal direct fragment
    rw [hfR, hfM, hnp1, hni1, hcd.1]
    decide
  · -- applyTel on stored, then the walk
    have happ : applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take piMkMember.arity) piMkMember.mtype) =
        some (.pi (.app (.app (.const 2 []) pa) (.app (.const 1 []) pa))
            (.app (.app (.const 2 []) (lift 0 1 pa))
              (.app (.const 1 []) (lift 0 1 pa)))) := by
      rw [hnp1, hpm', hls']
      show applyTel ([pa, pb, pc, pd].take 1)
          (instantiateLevels ([l].take piMkMember.arity) piMkType) = _
      rfl
    rw [hcM]
    rw [happ]
    simp only
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- fieldsTelS [f] [.recursive 0] (Π (a : I2 pa (g pa)), ...)
      rw [hfl', hsh]
      rfl
    · -- the minor is preMajor[2] = pc
      have hmin' : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some pc := by
        rw [hnp1, hci, hpm']; rfl
      rw [hmin']
      simp only
      rw [decide_eq_true_eq]
      rw [hrR, hpm', hnp1, hnM, hfl', hsh]
      -- the walk's rhsArgsS is [f, rec pa pb pc (g pa) f]
      have hrhs : rhsArgsS (.const 4 [l]) [pa, pb, pc, pd] 1 1 [f] [.recursive 0]
          (.pi (.app (.app (.const 2 []) pa) (.app (.const 1 []) pa))
            (.app (.app (.const 2 []) (lift 0 1 pa))
              (.app (.const 1 []) (lift 0 1 pa)))) =
          [f, foldApps (.const 4 [l]) [pa, pb, pc,
            .app (.const 1 []) pa, f]] := by
        simp only [rhsArgsS, recCallsS, recCallField, recPrefix, familyIdx,
          appsSpine, List.take, List.drop, List.append, List.cons_append,
          List.nil_append]
      rw [hls', hrhs]
      -- iotaRhsOfS: instPrefix over [pa,pb,pc,pd,f] of the [l]-instantiated schema
      unfold iotaRhsOfS
      rw [hpm', hfl', hsc, hls']
      have hIL : instantiateLevels [l] piSchemaCorrect =
          foldApps (.bvar 2)
            [.bvar 0, foldApps (.const 4 [l])
              [.bvar 4, .bvar 3, .bvar 2,
                foldApps (.const 1 []) [.bvar 4], .bvar 0]] := rfl
      rw [hIL]
      show instPrefix [pa, pb, pc, pd, f]
          (foldApps (.bvar 2)
            [.bvar 0, foldApps (.const 4 [l])
              [.bvar 4, .bvar 3, .bvar 2,
                foldApps (.const 1 []) [.bvar 4], .bvar 0]]) =
        foldApps pc [f, foldApps (.const 4 [l])
          [pa, pb, pc, .app (.const 1 []) pa, f]]
      rw [instPrefix_foldApps]
      simp only [List.map_cons, List.map_nil]
      rw [instPrefix_bvar_lt (j := 2) (a := pc) (by simp) rfl]
      rw [instPrefix_bvar_lt (j := 0) (a := f) (by simp) rfl]
      rw [instPrefix_foldApps]
      simp only [List.map_cons, List.map_nil]
      rw [instPrefix_const [pa, pb, pc, pd, f] 4 [l],
        instPrefix_bvar_lt (j := 4) (a := pa) (by simp) rfl,
        instPrefix_bvar_lt (j := 3) (a := pb) (by simp) rfl,
        instPrefix_bvar_lt (j := 2) (a := pc) (by simp) rfl,
        instPrefix_bvar_lt (j := 0) (a := f) (by simp) rfl]
      rw [instPrefix_foldApps]
      simp only [List.map_cons, List.map_nil]
      rw [instPrefix_const [pa, pb, pc, pd, f] 1 [],
        instPrefix_bvar_lt (j := 4) (a := pa) (by simp) rfl]
      rfl


/-- `EnvCorrAnnDW piEnv` — every S-witness of `piEnv` annotates on the DW
    union.  The discharge goes through the B-arm (`envCorrAnnB_piEnv`):
    `piEnv`'s stored field `I2 P (g P)` is δ-free, so `applyTel`'s raw output
    is already the walk's reading and the stronger `EnvCorrAnnCert` holds.
    This is the env the lift fix unmasked: pre-fix no `IotaWitnessS` could be
    well-formed here (the admission's own equation was ill-typed), post-fix
    the repaired schema is exactly the reduct `rhsArgsS` computes. -/
theorem envCorrAnnDW_piEnv : EnvCorrAnnDW piEnv :=
  envCorrAnnDW_of_annCert envCorrAnnB_piEnv

/-! ## (7) the packaged measurement -/

/-- the sealed measurement, post-fix: for a `.recursive 0` field whose
    `familyIdx` index mentions a constructor parameter, `iotaSchemaAt` now
    derives the `fl`-shifted equation — `g` of the parameter — which both
    checkers accept, every recognizer arm passes the S-witness, and the
    env is inside `EnvWfT` with the per-env DW universal discharged.  The
    historical emission (`piSchemaEq`, `g` of the motive) is retained as a
    diagnostic: `tyAtC` still refuses it, measuring exactly the defect the
    lift repair removed. -/
theorem paramIdx_admitted :
    iotaSchemaAt piGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 0] = some piSchemaCorrect ∧
    (tyAtC piEnv 1 8 piCtx piSchemaCorrect piEqTy).isSome = true ∧
    (tyAtC piEnv 1 8 piCtx piSchemaEq piEqTy).isSome = false ∧
    wPi.shapes = [.recursive 0] ∧
    iotaWitnessSAnnDW piEnv wPi = true ∧
    Nonempty (EnvWfT piEnv) ∧ EnvCorrAnnDW piEnv :=
  ⟨piSchema_derived, piIota_correct_conv, piIota_conv_refused, rfl,
    pin_iotaWitnessSAnnDW_piEnv, pin_envWfT_piEnv, envCorrAnnDW_piEnv⟩

end Rcic.Declarative.Ann
