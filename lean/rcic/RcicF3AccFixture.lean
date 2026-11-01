import rcic.RcicF3KTWFixtureA
import rcic.RcicF3Rec

/-!
# F3 AGPropAny: the Acc fixture — `anySort` at a Prop family with a function-recursive field

The AGPropAny corner (session-28 measurement, PR #8251): a uniform-`Prop` family whose
elimination is `.anySort` and whose constructor carries a FUNCTION-RECURSIVE field.  Lean's
`Acc.rec`-into-`Type` shape.  `recEnd_mem`'s level-0 `anySort` branch
(`RcicF3Rec.lean:217-249`) closes only through `hsafeFree` → `ihArgs_free` (the minor's
`ihArgs` collapses to the field values); a function-recursive field mentions the family by
construction, so `hsafeFree` is refutable at every such group — this file exhibits one and
proves the refutation, then names the residual minor obligation as `AccMinorCell`.

Both landed membership wrappers are inapplicable here by their own premises: the Type
route (`recVal_mem_rec_KTA`) needs a `UniformType` family (`acc_notUniformType`), the
Prop route (`recVal_mem_recP_KTA`) needs `policy = .propOnly` (`acc_policy_ne_propOnly`).
The corner is live, not vacuous: `acc_selected_anySort` is the singleton-Prop admission
(all fields safe: the field's level is `imax 0 0`), and `accMinor_derived` shows the policy
DERIVES the function-IH minor at this group.

The fixture (all refs on `emptyEnv`):
* `AccR : Prop → Prop` at 0;
* `intro : Π (P : Prop), (P → AccR P) → AccR P` at 1 — one field, `P → AccR P`,
  function-recursive at inner = 1 (`accField_analyze`, the W-line reading);
* the recursor at 2, eliminating into any sort.

Residue: `[rcic-f3-agpropany-acc-cell]` = `AccMinorCell` below.  The corner's
checked-side-condition form (audit sign-off follow-up): the branch's three dead legs
(`hsafeFree`, `hsafe`, arity — `acc_hsafeFree_refuted`, `acc_hsafe_shape`,
`acc_propEnd_arity`) reduce to (cell ∧ end bridge) via `accRecEnd_of_endBridge` —
`propRecEnd` untouched.

closure_claim = 0.
-/

set_option autoImplicit false

universe u

namespace Rcic.F3

open Rcic.Declarative

/-! ## (1) the members -/

/-- `AccR : Prop → Prop` at 0. -/
def accFamMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩

/-- `AccR x`. -/
abbrev accApp (x : Expr Nat) : Expr Nat := .app (.const 0 []) x

/-- the function-recursive field `P → AccR P` (the type in the constructor's telescope,
    under the parameter binder `P`). -/
def accField : Expr Nat := .pi (.bvar 0) (accApp (.bvar 1))

/-- `intro : Π (P : Prop), (P → AccR P) → AccR P` at 1. -/
def accIntroMember : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort .zero) (.pi accField (accApp (.bvar 1))), none⟩

/-- the family alone, then with its constructor, then with the recursor. -/
def accFamOnly : ResolvedEnv := extendEnv emptyEnv 0 accFamMember
def accPrefix : ResolvedEnv := extendEnv accFamOnly 1 accIntroMember

/-! ## (2) the recursor's stored type -/

/-- the motive's type, `AccR P → Sort (param 0)`, under `P`. -/
abbrev accMotTy : Expr Nat := .pi (accApp (.bvar 0)) (.sort (.param 0))

/-- the minor's field: `f : P → AccR P`, under `P` and the motive. -/
def accFieldMinor : Expr Nat := .pi (.bvar 1) (accApp (.bvar 2))

/-- the minor's induction hypothesis, `∀ x : P, motive (f x)`, under `P`, the motive, `f`. -/
def accIhTy : Expr Nat :=
  .pi (.bvar 2) (.app (.bvar 2) (.app (.bvar 1) (.bvar 0)))

/-- the minor: `Π (f : P → AccR P), (∀ x, motive (f x)) → motive (intro P f)`. -/
def accMinorTy : Expr Nat :=
  .pi accFieldMinor (.pi accIhTy
    (.app (.bvar 2) (.app (.app (.const 1 []) (.bvar 3)) (.bvar 1))))

/-- `AccRrec` at 2, eliminating into any sort. -/
def accRecTy : Expr Nat :=
  .pi (.sort .zero) (.pi accMotTy (.pi accMinorTy
    (.pi (accApp (.bvar 2)) (.app (.bvar 2) (.bvar 0)))))

def accRecMember : CheckedMember := ⟨.recursorM, 1, accRecTy, none⟩

def accEnv : ResolvedEnv := extendEnv accPrefix 2 accRecMember

theorem accEnv_members (c : Nat) :
    accEnv.members c =
      if c = 2 then some accRecMember else if c = 1 then some accIntroMember
      else if c = 0 then some accFamMember else none := rfl

/-! ## (3) the views -/

/-- L-K1's family view of `AccR`: a `Prop` family with one parameter. -/
def accFamilyView (E : ResolvedEnv) (h : E.members 0 = some accFamMember) : PolicyFamilyView E where
  ref := 0
  member := accFamMember
  present := h
  hasClass := rfl
  parameters := [.sort .zero]
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
    bounded := fun j =>
      match j with
      | ⟨0, _⟩ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero }

/-- L-K1's constructor view of `intro`: one mirrored parameter, one function-recursive
    field, the field's typing row INLINE (the bvar premises compute at the concrete
    prefix context). -/
def accIntroView (E : ResolvedEnv) (h : E.members 0 = some accFamMember) :
    PolicyConstructorView E (accFamilyView E h) accIntroMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero]
  fields := [accField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .imax .zero .zero
    bounded := fun j =>
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero
      | ⟨1, _⟩ => HasTy.pi _ (.bvar 0) .zero (accApp (.bvar 1)) .zero
          (HasTy.bvar _ 0 (.sort .zero) rfl)
          (HasTy.app _ (.const 0 []) (.bvar 1) (.sort .zero) (.sort .zero)
            (HasTy.const _ 0 [] accFamMember h rfl (fun _ hx => nomatch hx))
            (HasTy.bvar _ 1 (.sort .zero) rfl))
  }
  parameterMirrors := fun _ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

/-! ## (4) the PendA evidence — the field is function-recursive -/

/-- the analysis: `P → AccR P` is function-recursive at `inner = 1` (the W-line reading,
    `fieldAnalyze` over the Π telescope; depth = parameters.length + field index = 1). -/
theorem accField_analyze_famOnly :
    fieldAnalyze accFamOnly 8 0 0 1 0 1 accField = .permitted (.recursive 1) [] := rfl

theorem accField_analyze :
    fieldAnalyze accPrefix 8 0 0 1 0 1 accField = .permitted (.recursive 1) [] := rfl

/-- the shapes list the descriptor reads off the single field. -/
theorem accShapes :
    fieldShapesFuel accEnv 8 0 0 1 0 1 [accField] = some [.recursive 1] := rfl

/-- the field is function-recursive wherever the family is present. -/
theorem accIntroFields (E : ResolvedEnv) (h : E.members 0 = some accFamMember)
    (hfa : fieldAnalyze E 8 0 0 1 0 1 accField = .permitted (.recursive 1) []) :
    CtorFieldsPermitted (accIntroView E h) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.recursive 1, 8, [], hfa⟩

/-! ## (5) the admissions -/

/-- the field's level `imax 0 0` is uniformly `Prop`. -/
theorem accImaxZero_prop : UniformProp (.imax .zero .zero) := fun _ => rfl

def accFamAdmitted : IndGroupAdmitted emptyEnv 0 accFamMember :=
  .family rfl (accFamilyView accFamOnly rfl) rfl rfl (Or.inl falseSort_prop)

def accIntroAdmitted : IndGroupAdmitted accFamOnly 1 accIntroMember :=
  .constructor (accFamilyView accFamOnly rfl) (accIntroView accFamOnly rfl)
    rfl (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl)
    (fun _ => Or.inl falseSort_prop)
    (accIntroFields accFamOnly rfl accField_analyze_famOnly)

/-- L-K1's recursor admission: ONE constructor whose single field is a proof (level
    `imax 0 0`), `anySort` by `EliminationSelection.singletonProp`. -/
def accGroupAdmitted : RecursorEliminationAdmitted accPrefix 2 accRecMember where
  family := accFamilyView accPrefix rfl
  constructors := [accIntroMember]
  constructorViews
    | ⟨0, _⟩ => accIntroView accPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [accMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp falseSort_prop rfl
    (fun ⟨0, _⟩ j => match j with
      | ⟨0, _⟩ => Or.inl accImaxZero_prop)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

/-- the corner is LIVE: the group's own admission selects `anySort` through the
    singleton-Prop path (not `hiddenDataProp`) — the field is a proof by level `imax 0 0`. -/
theorem acc_selected_anySort :
    EliminationSelection .zero 1 (∀ i, (accGroupAdmitted.constructorViews i).AllFieldsSafe)
      .anySort := accGroupAdmitted.selected

/-- THE DERIVED MINOR reads `f` through its Π telescope: its induction hypothesis is
    `∀ x : P, motive (f x)` — the function IH, exactly the W fixture's shape. -/
theorem accMinor_derived :
    derivedMinor accGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 1] = some accMinorTy := rfl

theorem accMinorMatch : MinorPremisesMatch accGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.recursive 1], 8, rfl, rfl⟩

/-! ## (6) the interpreter-side rows — the corner, refuted and named -/

section

open PSet

/-- the group's `FamData`: one constructor whose field list is the function-recursive field. -/
theorem acc_fd_ctors :
    (famDataOf accGroupAdmitted).ctors = [([accField], [])] := rfl

theorem acc_fref : (famDataOf accGroupAdmitted).fref = 0 := rfl

theorem acc_resLevel : (famDataOf accGroupAdmitted).resLevel = .zero := rfl

theorem acc_policy : (famDataOf accGroupAdmitted).policy = .anySort := rfl

theorem acc_ctorFieldsOf : ctorFieldsOf (famDataOf accGroupAdmitted) 0 = [accField] := rfl

theorem acc_nfOf : nfOf (famDataOf accGroupAdmitted) 0 = 1 := rfl

/-- **THE CORNER THEOREM (1): `hsafeFree` is REFUTED at the fixture.**  The field mentions
    the family (`accApp` under the Π codomain), so `recEnd_mem`'s singleton-`anySort`
    premise `∀ A ∈ c.1, occursConst fd.fref A = false` is false at this group — the branch
    that would collapse `ihArgs` to the field values is dead here. -/
theorem acc_hsafeFree_refuted :
    ¬ (∀ c, (famDataOf accGroupAdmitted).ctors = [c] →
        ∀ A, A ∈ c.1 → occursConst (famDataOf accGroupAdmitted).fref A = false) := by
  intro h
  have hA := h ([accField], []) acc_fd_ctors accField (by simp)
  have hocc : occursConst (famDataOf accGroupAdmitted).fref accField = true := rfl
  rw [hocc] at hA
  exact Bool.noConfusion hA

/-- the singleton shortcut's `ihArgs`-identity is dead at the field: the recursive
    position is `g`-filled (`ihAt`), so the minor takes the field AND its IH. -/
theorem acc_ihArgs_inserts (g : PSet.{u} → PSet.{u}) (x : PSet.{u}) :
    ihArgs 0 g [accField] [x] = [x, ihAt g accField x] := rfl

/-- **THE NAMED CELL `[rcic-f3-agpropany-acc-cell]`**: the residual minor-ok obligation at
    the Acc fixture — `recEnd_mem`'s `hmin` instance for the single constructor, with the
    `g`-filled `ihArgs`.  The singleton-`anySort` branch cannot discharge it
    (`acc_hsafeFree_refuted` kills `hsafeFree`, `acc_ihArgs_inserts` shows the collapse is
    false); carrying the `g`-filled recursive position into `Ed M (fapps mo (is ++ [ctorV …]))`
    at the large `anySort` motive (`policyMotiveLevel .anySort = .param baseArity`) is the
    model's soundness counterpart of Lean's large elimination for `Acc` — the same wall as
    grok class (c) (`pinPropAcc_noGroupRecT`: `FieldT` has no frec arm) and RK-03's apex
    ("function-recursive fields have no view kind"). -/
def AccMinorCell (M : Interp.{u}) (σ : Nat → Nat) (mo : PSet.{u})
    (ms is : List (PSet.{u})) (g : PSet.{u} → PSet.{u}) (xs : List (PSet.{u})) : Prop :=
  fapps (ms.getD 0 pempty)
      (ihArgs (famDataOf accGroupAdmitted).fref g
        (ctorFieldsOf (famDataOf accGroupAdmitted) 0) xs) ∈
    Ed M (fapps mo (is ++ [ctorV M σ (famDataOf accGroupAdmitted) 0 xs]))

/-! ### both landed wrappers are inapplicable at the fixture -/

/-- the Type route's universe premise fails: the family is uniformly `Prop`. -/
theorem acc_notUniformType : ¬ UniformType (famDataOf accGroupAdmitted).resLevel :=
  fun h => Nat.lt_irrefl 0 (h (fun _ => 0))

/-- the Prop route's policy premise fails: the group eliminates into any sort. -/
theorem acc_policy_ne_propOnly : (famDataOf accGroupAdmitted).policy ≠ .propOnly := by
  intro h
  rw [acc_policy] at h
  exact EliminationPolicy.noConfusion h

/-! ### the Prop-end face: the arity mismatch is part of the wall -/

/-- `recon` at the fixture: every field is unrevealed (no result indices), so each
    reconstructs to `pempty` — ONE argument. -/
theorem acc_recon_length : (recon ([accField], []) []).length = 1 := rfl

/-- the `g`-filled minor application at the same field: TWO arguments (field + IH). -/
theorem acc_ihArgs_length (g : PSet.{u} → PSet.{u}) (x : PSet.{u}) :
    (ihArgs 0 g [accField] [x]).length = 2 := rfl

/-- the two application arities differ: the model's Prop-end face (`propRecEnd`) applies
    the minor to `recon c is` (one argument here), while the minor's stored type is a
    2-Π (field, function IH). The arity bridge between the two faces is part of
    `[rcic-f3-agpropany-acc-cell]`, recorded here as data, not discharged. -/
theorem acc_propEnd_arity (g : PSet.{u} → PSet.{u}) (x : PSet.{u}) :
    ihArgs 0 g [accField] [x] ≠ recon ([accField], []) [] := by
  intro h
  have h1 := acc_ihArgs_length g x
  rw [h, acc_recon_length] at h1
  omega

/-- `recEnd`'s Prop value at the fixture: the minor applied to `[pempty]`. -/
theorem acc_propRecEnd_shape (minor0 : PSet.{u}) :
    propRecEnd (famDataOf accGroupAdmitted) minor0 [] = fapps minor0 [pempty] := rfl

/-! ### the third dead leg: `hsafe` reduces to "field values ≈ `pempty`"

Independent audit finding (m3 sign-off on PR #8275): the singleton branch's `hsafe`
premise dies INDEPENDENTLY of `hsafeFree` and of the arity count — the reconstructed
argument is `pempty` (no result indices reveal the field), so `LEq xs (recon c is)`
demands field values ≈ `pempty`. -/

/-- `hsafe` at the fixture: `LEq [x] [pempty]` holds exactly when `x ≈ pempty` —
    satisfiable only by a field value that IS `pempty`-equivalent, which a
    function-into-family value is not. The branch's congruence transport
    (`fapps_congr_args _ hrec`) is dead before element-wise questions arise. -/
theorem acc_hsafe_shape (x : PSet.{u}) :
    LEq [x] (recon ([accField], []) []) ↔ Equiv x pempty :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-! ### the packaging: the corner as a checked side condition (cell ∧ end bridge) -/

/-- `recEnd_mem`'s level-0 `anySort`-singleton conclusion at the Acc fixture, with the
    branch's three dead legs (`hsafeFree` → `acc_hsafeFree_refuted`; `hsafe` →
    `acc_hsafe_shape`; arity → `acc_propEnd_arity`) replaced by ONE named premise: the
    **end bridge** — a different end computation that feeds the minor the `g`-filled
    `ihArgs` instead of `recon c is`.  Under it the conclusion follows from
    `AccMinorCell` (the `hmin` face) and `z ≈ pempty` alone.  `propRecEnd` itself is
    untouched: this is the checked-side-condition packaging of
    `[rcic-f3-agpropany-acc-cell]`, not a patch — the corner reduces to
    (cell ∧ end bridge). -/
theorem accRecEnd_of_endBridge (M : Interp.{u}) (σ : Nat → Nat)
    (mo : PSet.{u}) (ms : List (PSet.{u})) (z : PSet.{u}) (ρ : Nat → PSet.{u})
    (g : PSet.{u} → PSet.{u}) (xs : List (PSet.{u}))
    (hms : ms.length = 1)
    (hz0 : Equiv z pempty)
    (hcell : AccMinorCell M σ mo ms [] g xs)
    (hend : propRecEnd (famDataOf accGroupAdmitted) (ms.getD 0 pempty) []
        = fapps (ms.getD 0 pempty) (ihArgs 0 g [accField] xs)) :
    recEnd M σ (famDataOf accGroupAdmitted)
        (push ([] ++ mo :: ms ++ ([] ++ [z])) ρ) ∈ Ed M (fapps mo ([] ++ [z])) := by
  have h0lt : 0 < ms.length := by rw [hms]; omega
  have hm0 : push ([] ++ mo :: (ms ++ ([] ++ [z]))) ρ 1 = ms.getD 0 pempty := by
    have h := recEnv_minor [] mo ms [] z ρ 0 h0lt
    rw [hms] at h
    simp only [List.length_nil, Nat.zero_add, Nat.sub_zero] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0lt]
    exact h
  unfold recEnd PSet.cond
  cases hd : M.dec (evalTotal σ (famDataOf accGroupAdmitted).resLevel = 0) with
  | isTrue _ =>
      show propRecEnd (famDataOf accGroupAdmitted)
          (push ([] ++ mo :: (ms ++ ([] ++ [z]))) ρ 1) [] ∈ _
      rw [hm0, hend]
      have hcv : ctorV M σ (famDataOf accGroupAdmitted) 0 xs = pempty := by
        unfold ctorV
        exact cond_pos (rfl : evalTotal σ (famDataOf accGroupAdmitted).resLevel = 0) _ _
      have he : Equiv (fapps mo ([] ++ [ctorV M σ (famDataOf accGroupAdmitted) 0 xs]))
          (fapps mo ([] ++ [z])) :=
        fapps_congr_args mo (LEq_append (LEq.refl []) ⟨by rw [hcv]; exact hz0.symm, trivial⟩)
      exact mem_congr_right (ed_congr M he) hcell
  | isFalse hn => exact absurd rfl hn

end

end Rcic.F3

#print axioms Rcic.F3.accField_analyze
#print axioms Rcic.F3.accShapes
#print axioms Rcic.F3.acc_selected_anySort
#print axioms Rcic.F3.accMinor_derived
#print axioms Rcic.F3.accMinorMatch
#print axioms Rcic.F3.acc_hsafeFree_refuted
#print axioms Rcic.F3.acc_ihArgs_inserts
#print axioms Rcic.F3.acc_notUniformType
#print axioms Rcic.F3.acc_policy_ne_propOnly
#print axioms Rcic.F3.acc_propEnd_arity
#print axioms Rcic.F3.acc_propRecEnd_shape
#print axioms Rcic.F3.acc_hsafe_shape
#print axioms Rcic.F3.accRecEnd_of_endBridge
