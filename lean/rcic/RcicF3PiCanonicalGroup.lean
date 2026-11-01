import rcic.RcicF3PiCanonicalParams
/-! Canonical family-parameter signatures for the complete admitted constructor
list. Original constructor types are retained. This is a proof-family component;
universal group invariants and recursor typing remain open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCanonicalGroup
open Rcic.Declarative PiValueRule PiValueExtract

/-- Replace only the parameter prefix of an admitted syntax slot. -/
def slot {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (fuel : Fin a.constructors.length → Nat) (i : Fin a.constructors.length) : Constructor where
  fields := a.family.parameters.map FieldSpec.plain ++
    (PiGroupSyntax.slot a fuel i).fields.drop (a.constructorViews i).parameters.length
  result := (PiGroupSyntax.slot a fuel i).result

/-- Complete admission order, including the empty list. -/
def constructors {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (fuel : Fin a.constructors.length → Nat) : List Constructor :=
  (List.range a.constructors.length).map (fun j =>
    if hj : j < a.constructors.length then slot a fuel ⟨j, hj⟩ else ⟨[], []⟩)

/-- Elementary list length computation. -/
theorem count {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat) :
    (constructors a fuel).length = a.constructors.length := by
  simp only [constructors, List.length_map, List.length_range]

/-- Original admission position, with no reordering. -/
def index {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat)
    (i : Fin (constructors a fuel).length) : Fin a.constructors.length :=
  ⟨i.val, by simpa only [count] using i.isLt⟩

/-- Elementary exact lookup computation. -/
theorem lookup {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat)
    (i : Fin (constructors a fuel).length) :
    (constructors a fuel)[i.val] = slot a fuel (index a fuel i) := by
  simp only [constructors, List.getElem_map, List.getElem_range]
  have hi : i.val < a.constructors.length := (index a fuel i).isLt
  rw [dif_pos hi]
  rfl

/-- Elementary extraction from the existing whole-admission reader. -/
theorem slot_spec {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) :
    ∃ fs, Views E (h.fuelAt i) a.family.ref a.family.member.arity
        (a.family.parameters ++ a.family.indices).length (a.constructorViews i).fields fs ∧
      (slot a h.fuelAt i).fields = a.family.parameters.map FieldSpec.plain ++ fs := by
  obtain ⟨fs, _, hv, hf, _, _⟩ := PiGroupSyntax.slot_spec a h i
  refine ⟨fs, hv, ?_⟩
  change _ ++ (PiGroupSyntax.slot a h.fuelAt i).fields.drop _ = _
  rw [hf, List.drop_left' (List.length_map (a.constructorViews i).parameters FieldSpec.plain)]

/-- Each original stored constructor abstraction belongs to its full declared
type under the positive predicate of the complete extracted signature. Ordinary
soundness/body conditions and original bounded typing remain explicit. -/
theorem constructor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r n : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (hfree : ∀ A ∈ a.family.parameters, occursConst a.family.ref A = false)
    (vs : List Nat) (hvs : vs.length = a.family.member.arity) (K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))) (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hR : PiHereditary.BodiesRegular (mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))) (σOf vs) K E)
    (i : Fin (constructors a h.fuelAt).length) {u : Level}
    (d : HasTyT E n [] a.constructors[(index a h.fuelAt i).val].mtype (.sort u))
    (hd : LOKt (σOf vs) 4 K d) :
    let M := mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))
    let T := a.constructors[(index a h.fuelAt i).val].mtype
    piLam M (σOf vs) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf vs) ρ0 T) := by
  let j := index a h.fuelAt i
  let cv := a.constructorViews j
  obtain ⟨fs, hv, hf⟩ := slot_spec a h j
  have hv' : Views E (h.fuelAt j) a.family.ref vs.length
      (a.family.parameters ++ a.family.indices).length cv.fields fs := by
    rw [hvs]
    exact hv
  have hc : ((constructors a h.fuelAt)[i.val]).fields =
      a.family.parameters.map FieldSpec.plain ++ fs := (congrArg Constructor.fields
        (lookup a h.fuelAt i)).trans hf
  have hr : ((constructors a h.fuelAt)[i.val]).result =
      policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices := by
    rw [lookup]
    rfl
  have hresult : ∀ e ∈ policyParameterLocals cv.parameters.length cv.fields.length ++
      cv.resultIndices, occursConst a.family.ref e = false := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [policyParameterLocals, List.mem_map] at he
      obtain ⟨k, _, rfl⟩ := he
      rfl
    · exact cv.noFamilyInIndices e he
  have ht : a.constructors[j.val].mtype = policyPi (cv.parameters ++ cv.fields)
      (foldApps (.const a.family.ref ((List.range vs.length).map Level.param))
        (policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices)) := by
    rw [cv.storedType]
    simp only [policyFamilyLevels, hvs]
  generalize he : a.constructors[j.val].mtype = T at d hd ⊢
  rw [he] at ht
  cases ht
  exact PiCanonicalParams.constructor_mem P μ a.family.ref a.family.parameters
    a.family.indices (constructors a h.fuelAt) vs i cv.parameters cv.fields
    cv.resultIndices fs cv.parameterCount cv.indexCount hfree hv' hc hr hresult
    K hE hb hR d hd

end Rcic.F3.PSet.PiCanonicalGroup
