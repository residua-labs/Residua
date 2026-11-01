import rcic.RcicF3PiRecExtract
import rcic.RcicF3PiRawCtorAttack
/-! Operational unfolding on paid original dependent fields. This does not
claim motive/minor typing or a group invariant. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRecExtractAttack
open Rcic.Declarative PiRawCtorAttack RecPlan

/-- Actual fitting raw fields, rather than a supplied semantic telescope,
produce the recursor equation for every numeric family reference. -/
theorem param_unfold (P : Premises4) (f : Nat) (ms : List PSet.{4}) :
    let M := mkM P (paramTable P f)
    TelFits M (σOf []) [paramField f] (vcons (tyv pempty) ρ0) [pempty] ∧
    Equiv (core M f [[.recursive 1]] ms (dataVal 0 [pempty]))
      (fapps (ms.getD 0 pempty)
        (args (core M f [[.recursive 1]] ms) [.recursive 1] [pempty])) := by
  have hx := (param_inhabited P f).1.2
  obtain ⟨_, ha, hI, hb, _⟩ := param_checks f
  refine ⟨hx, ?_⟩
  exact core_data_of_fits (mkM P (paramTable P f)) (σOf []) (fun _ => 0)
    (paramSound P f (σOf []) (fun _ => 0)) hb [[.recursive 1]] ms rfl
    [paramField f] ha
    (fun A hA => hI A (List.mem_append.mpr (Or.inr hA)))
    (vcons (tyv pempty) ρ0) [pempty] hx

def hiddenField (f : Nat) : Expr Nat :=
  .letE (.sort .zero) (paramField f) (.bvar 0)

/-- Elementary readback attack: the raw let hides the Pi, but admission
retains exactly one IH binder; changing that depth is refused. -/
theorem hidden_plan (f : Nat) :
    ihDepth (hiddenField f) = 0 ∧
    fieldShapesFuel (paramEnv f) 8 f 0 1 0 1 [hiddenField f] =
      some [.recursive 1] ∧
    fieldShapesFuel (paramEnv f) 8 f 0 1 0 1 [hiddenField f] ≠
      some [.recursive 0] := by
  have ha : fieldShapesFuel (paramEnv f) 8 f 0 1 0 1 [hiddenField f] =
      some [.recursive 1] := by
    simp [hiddenField, fieldShapesFuel, fieldAnalyze, paramField,
      piTelescopeFuel, whnfFuel, appsSpine, transparentBody, paramEnv,
      members_extend_eq, paramMember, transparent, domainsContainFuel,
      containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
      familyIdx, instantiate0, instantiate, lift, foldApps]
  refine ⟨rfl, ha, ?_⟩
  rw [ha]
  intro h
  cases h

/-- The hidden original field is actually inhabited and unfolds with the
normalized IH depth, for all family labels and arbitrary minors. -/
theorem hidden_unfold (P : Premises4) (f : Nat) (ms : List PSet.{4}) :
    let M := mkM P (paramTable P f)
    TelFits M (σOf []) [hiddenField f] (vcons (tyv pempty) ρ0) [pempty] ∧
    Equiv (core M f [[.recursive 1]] ms (dataVal 0 [pempty]))
      (fapps (ms.getD 0 pempty)
        (args (core M f [[.recursive 1]] ms) [.recursive 1] [pempty])) := by
  have hx : TelFits (mkM P (paramTable P f)) (σOf []) [hiddenField f]
      (vcons (tyv pempty) ρ0) [pempty] := (param_inhabited P f).1.2
  obtain ⟨_, _, hI, hb, _⟩ := param_checks f
  have hIh : ∀ A ∈ [hiddenField f], InstOK (paramEnv f) (σOf []) (fun _ => 0) A := by
    intro A hA
    have hA' := List.mem_singleton.mp hA
    subst A
    intro r ls hr
    apply hI (paramField f) (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) r ls
    simpa only [hiddenField, constInsts, List.nil_append, List.append_nil] using hr
  refine ⟨hx, ?_⟩
  exact core_data_of_fits (mkM P (paramTable P f)) (σOf []) (fun _ => 0)
    (paramSound P f (σOf []) (fun _ => 0)) hb [[.recursive 1]] ms rfl
    [hiddenField f] (hidden_plan f).2.1 hIh
    (vcons (tyv pempty) ρ0) [pempty] hx

end Rcic.F3.PSet.PiRecExtractAttack
