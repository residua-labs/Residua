import rcic.RcicF3PiTupleExact
/-! Whole constructor syntax extracted from actual admission. Each slot keeps
its own parameter syntax and admission fuel. This proof-family component
supplies no universal group invariant or raw recursor typing. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiGroupSyntax
open Rcic.Declarative PiValueRule PiValueExtract

/-- Total syntax extraction; admission proves the fallback is unused. -/
def slot {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (fuel : Fin a.constructors.length → Nat) (i : Fin a.constructors.length) : Constructor where
  fields := (a.constructorViews i).parameters.map FieldSpec.plain ++
    (fields E (fuel i) a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length a.family.parameters.length
      (a.constructorViews i).fields).getD []
  result := policyParameterLocals (a.constructorViews i).parameters.length
    (a.constructorViews i).fields.length ++ (a.constructorViews i).resultIndices

/-- Constructor order is admission order, including an empty constructor list. -/
def constructors {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (fuel : Fin a.constructors.length → Nat) : List Constructor :=
  (List.range a.constructors.length).map (fun j =>
    if hj : j < a.constructors.length then slot a fuel ⟨j, hj⟩ else ⟨[], []⟩)

/-- Actual admission produces every slot's normalized fields, with no caller
signature, successful-reader premise or common-fuel assumption. -/
theorem slot_spec {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) :
    ∃ fs, fields E (h.fuelAt i) a.family.ref a.family.member.arity
      (a.constructorViews i).parameters.length a.family.indices.length
      (a.constructorViews i).parameters.length (a.constructorViews i).fields = some fs ∧
      Views E (h.fuelAt i) a.family.ref a.family.member.arity
        (a.family.parameters ++ a.family.indices).length (a.constructorViews i).fields fs ∧
      (slot a h.fuelAt i).fields = (a.constructorViews i).parameters.map FieldSpec.plain ++ fs ∧
      a.constructors[i.val].mtype = policyPi
        ((a.constructorViews i).parameters ++ (a.constructorViews i).fields)
        (foldApps (.const a.family.ref (policyFamilyLevels a.family)) (slot a h.fuelAt i).result) ∧
      (slot a h.fuelAt i).result.length = (a.family.parameters ++ a.family.indices).length := by
  have ha := h.analyzed i
  rw [← (a.constructorViews i).parameterCount] at ha
  obtain ⟨fs, hf, hv⟩ := fields_of_admitted (a.constructorViews i).fields
    (a.constructorViews i).parameters.length (h.shapesAt i) ha (Nat.le_refl _)
  refine ⟨fs, hf, ?_, ?_, (a.constructorViews i).storedType, ?_⟩
  · simpa only [List.length_append, (a.constructorViews i).parameterCount] using hv
  · simp only [slot, (a.constructorViews i).parameterCount] at hf ⊢
    rw [hf]
    rfl
  · simp only [slot, List.length_append, policyParameterLocals_length,
      (a.constructorViews i).parameterCount, (a.constructorViews i).indexCount]

/-- The finite syntax list has exactly the admitted constructor count.
Elementary list bookkeeping. -/
theorem count {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat) :
    (constructors a fuel).length = a.constructors.length := by
  simp only [constructors, List.length_map, List.length_range]

/-- Recover the admission index without choosing a representative or reordering. -/
def index {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat)
    (i : Fin (constructors a fuel).length) : Fin a.constructors.length :=
  ⟨i.val, by simpa only [count] using i.isLt⟩

/-- Exact list lookup; no constructor can be lost to extraction failure.
Elementary index bookkeeping. -/
theorem lookup {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (fuel : Fin a.constructors.length → Nat)
    (i : Fin (constructors a fuel).length) :
    (constructors a fuel)[i.val] = slot a fuel (index a fuel i) := by
  simp only [constructors, List.getElem_map, List.getElem_range]
  have hi : i.val < a.constructors.length := (index a fuel i).isLt
  rw [dif_pos hi]
  rfl

/-- Leave each original parameter domain unchanged while normalizing fields.
This permits arbitrary convertible parameter presentations; no raw parameter
family-freeness or literal parameter equality is assumed. -/
theorem prefix_fits_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n fuel f nu ar : Nat}
    (hE : EnvSound (mkM P μ) σ K E n) (hb : BodiesOK E σ K)
    (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E)
    {As : List (Expr Nat)} {fs : List FieldSpec} (hv : Views E fuel f nu ar As fs) :
    ∀ (Ps : List (Expr Nat)) {Γ : LCtx} {b : Expr Nat} {l : Level}
      (d : HasTyT E n Γ (policyPi (Ps ++ As) b) (.sort l)), LOKt σ 4 K d →
      ∀ ρ xs, Fits (mkM P μ) σ Γ ρ →
      (TelFits (mkM P μ) σ (Ps ++ fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs ↔
        TelFits (mkM P μ) σ (Ps ++ As) ρ xs) := by
  intro Ps
  induction Ps with
  | nil =>
      intro Γ b l d hd ρ xs hρ
      exact PiTupleExact.fits_iff P μ σ K hE hb hR hv d hd ρ xs hρ
  | cons A Ps ih =>
      intro Γ b l d hd ρ xs hρ
      obtain ⟨u, v, dA, dB, hdA, hdB⟩ := pi_inv_lokt σ 4 K d hd
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs =>
          change (_ ∧ _) ↔ (_ ∧ _)
          constructor
          · intro hx
            exact ⟨hx.1, (ih dB hdB (vcons x ρ) xs ⟨hρ, hx.1⟩).mp hx.2⟩
          · intro hx
            exact ⟨hx.1, (ih dB hdB (vcons x ρ) xs ⟨hρ, hx.1⟩).mpr hx.2⟩

/-- The complete assembled constructor tuple is exactly the original stored
constructor tuple at a sound bounded interpretation. All syntax is extracted
from admission. Parameters are preserved literally, not assumed family-free. -/
theorem tuple_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {r n : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (hE : EnvSound (mkM P μ) σ K E n) (hb : BodiesOK E σ K)
    (hR : PiHereditary.BodiesRegular (mkM P μ) σ K E)
    (c : Fin (constructors a h.fuelAt).length) {l : Level}
    (d : HasTyT E n [] a.constructors[(index a h.fuelAt c).val].mtype (.sort l))
    (hd : LOKt σ 4 K d) (xs : List PSet.{4}) :
    TelFits (mkM P μ) σ
        (((constructors a h.fuelAt)[c.val]).fields.map
          (fieldExpr a.family.ref (policyFamilyLevels a.family))) ρ0 xs ↔
      TelFits (mkM P μ) σ ((a.constructorViews (index a h.fuelAt c)).parameters ++
        (a.constructorViews (index a h.fuelAt c)).fields) ρ0 xs := by
  obtain ⟨fs, _, hv, hf, _, _⟩ := slot_spec a h (index a h.fuelAt c)
  rw [lookup, hf]
  simp only [List.map_append, List.map_map, Function.comp_def, fieldExpr, List.map_id']
  change TelFits (mkM P μ) σ
    ((a.constructorViews (index a h.fuelAt c)).parameters ++
      fs.map (fieldExpr a.family.ref (policyFamilyLevels a.family))) ρ0 xs ↔ _
  have ht := (a.constructorViews (index a h.fuelAt c)).storedType
  generalize he : a.constructors[(index a h.fuelAt c).val].mtype = T at d hd
  rw [he] at ht
  cases ht
  exact prefix_fits_iff P μ σ K hE hb hR hv
    (a.constructorViews (index a h.fuelAt c)).parameters d hd ρ0 xs True.intro

end Rcic.F3.PSet.PiGroupSyntax
