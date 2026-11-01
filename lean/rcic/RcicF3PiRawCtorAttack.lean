import rcic.RcicF3PiRawCtor
import rcic.RcicF3PiValueExtractAttack
/-! Actual raw constructor abstractions at typed dependent fixtures.
Admission, ordinary environment soundness and derivation bounds are paid
internally. This is not a full raw group invariant. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawCtorAttack
open Rcic.Declarative PiValueRule PiValueExtract PiValueExtractAttack

/-- Elementary bound computation for the typed fixture. -/
theorem local_bounded (f : Nat) :
    LOKt (σOf []) 4 (fun _ => 0) (local_typed f) := by
  simp [local_typed, LOKt, LevelsOK, evalTotal]

/-- Full actual raw abstraction membership, with every component premise paid.
The numeric family reference is universally quantified. -/
theorem local_constructor (P : Premises4) (f : Nat) :
    let M := mkM P (localTable P f)
    let T := policyPi (localFields f) (.const f [])
    piLam M (σOf []) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf []) ρ0 T) := by
  obtain ⟨hf, ha, hI, hb⟩ := local_checks f (σOf []) (fun _ => 0)
  exact PiRawCtor.constructor_mem P PiValueRuleAttack.emptyBase f [] [localCtor] []
    ⟨0, Nat.zero_lt_succ 0⟩ [] (localFields f) localCtor.fields
    (fun _ h => (List.not_mem_nil _ h).elim) ha rfl hf rfl
    (fun _ h => (List.not_mem_nil _ h).elim) rfl (fun _ => 0)
    (localSound P f (σOf []) (fun _ => 0)) hb hI (local_typed f) (local_bounded f)

def params : List (Expr Nat) := [.sort .zero]
def paramField (f : Nat) : Expr Nat :=
  .pi (.bvar 0) (.app (.const f []) (.bvar 1))
def paramCtor : Constructor :=
  ⟨[.plain (.sort .zero), .recursive [.bvar 0] [.bvar 1]], [.bvar 1]⟩
def paramMember : CheckedMember := ⟨.inductiveM, 0, policyPi params (.sort .zero), none⟩
def paramEnv (f : Nat) : ResolvedEnv := extendEnv emptyEnv f paramMember
def paramPred (P : Premises4) := predicate P PiValueRuleAttack.emptyBase params [paramCtor]
def paramTable (P : Premises4) (f : Nat) :=
  upd PiValueRuleAttack.emptyBase f
    (PiValue.table P PiValueRuleAttack.emptyBase (paramPred P) params)

/-- A genuine parameterized constructor type, not just a semantic signature. -/
def param_typed (f : Nat) :
    HasTyT (paramEnv f) 0 []
      (policyPi (params ++ [paramField f]) (.app (.const f []) (.bvar 1)))
      (.sort (.imax (.succ .zero) (.imax (.imax .zero .zero) .zero))) := by
  apply HasTyT.pi [] _ _ _ _ (.sort [] .zero)
  · apply HasTyT.pi _ _ (.imax .zero .zero) _ .zero
    · apply HasTyT.pi _ _ .zero _ .zero
        (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)
      exact .app _ _ _ (.sort .zero) (.sort .zero)
        (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
        (.bvar _ 1 (.sort .zero) rfl)
    · exact .app _ _ _ (.sort .zero) (.sort .zero)
        (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
        (.bvar _ 1 (.sort .zero) rfl)

/-- The parameterized family supplies ordinary soundness at every reference. -/
theorem paramSound (P : Premises4) (f : Nat) (σ K : Nat → Nat) :
    EnvSound (mkM P (paramTable P f)) σ K (paramEnv f) 0 := by
  have shape : ∀ r m, (paramEnv f).members r = some m → r = f ∧ m = paramMember := by
    intro r m hm
    by_cases hr : r = f
    · subst r
      change (extendEnv emptyEnv f paramMember).members f = some m at hm
      rw [members_extend_eq] at hm
      exact ⟨rfl, (Option.some.inj hm).symm⟩
    · change (extendEnv emptyEnv f paramMember).members r = some m at hm
      rw [members_extend_ne emptyEnv f paramMember r hr] at hm
      cases hm
  apply envSound_of_allSound P (K := K) (μ := paramTable P f) (E := paramEnv f) ?_ ?_ σ 0
  · intro r m hm
    obtain ⟨hr, hm⟩ := shape r m hm
    subst r
    subst m
    apply PiValue.member_sound P (paramTable P f) K f paramMember (paramPred P) params
      (fun _ => rfl) rfl rfl rfl
    intro vs
    change Equiv ((upd PiValueRuleAttack.emptyBase f
      (PiValue.table P PiValueRuleAttack.emptyBase (paramPred P) params)) f vs) _
    rw [upd_eq]
    exact Equiv.rfl
  · intro r m hm
    obtain ⟨_, hm⟩ := shape r m hm
    subst m
    exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩

/-- Executable admission, ordinary instance bounds and a bounded raw derivation. -/
theorem param_checks (f : Nat) :
    fields (paramEnv f) 8 f 0 1 0 1 [paramField f] =
      some [.recursive [.bvar 0] [.bvar 1]] ∧
    fieldShapesFuel (paramEnv f) 8 f 0 1 0 1 [paramField f] = some [.recursive 1] ∧
    (∀ A ∈ params ++ [paramField f], InstOK (paramEnv f) (σOf []) (fun _ => 0) A) ∧
    BodiesOK (paramEnv f) (σOf []) (fun _ => 0) ∧
    LOKt (σOf []) 4 (fun _ => 0) (param_typed f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [fields, field, fieldAnalyze, paramField,
      piTelescopeFuel, whnfFuel, appsSpine, transparentBody, paramEnv,
      members_extend_eq, paramMember, transparent, domainsContainFuel,
      containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
      familyIdx]
  · simp [fieldShapesFuel, fieldAnalyze, paramField,
      piTelescopeFuel, whnfFuel, appsSpine, transparentBody, paramEnv,
      members_extend_eq, paramMember, transparent, domainsContainFuel,
      containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
      familyIdx]
  · intro A hA r ls hr
    simp only [params, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · cases hr
    · change (r, ls) ∈ [] ++ [(f, [])] ++ [] at hr
      have he := List.mem_singleton.mp hr
      cases he
      exact ⟨paramMember, members_extend_eq _ _ _, rfl,
        fun _ h => (List.not_mem_nil _ h).elim⟩
  · intro r m b ls hm hbody
    by_cases hr : r = f
    · subst r
      change (extendEnv emptyEnv f paramMember).members f = some m at hm
      rw [members_extend_eq] at hm
      cases hm
      cases hbody
    · change (extendEnv emptyEnv f paramMember).members r = some m at hm
      rw [members_extend_ne emptyEnv f paramMember r hr] at hm
      cases hm
  · simp [param_typed, LOKt, LevelsOK, evalTotal]

/-- Full parameterized raw constructor membership at every numeric family label. -/
theorem param_constructor (P : Premises4) (f : Nat) :
    let M := mkM P (paramTable P f)
    let T := policyPi (params ++ [paramField f]) (.app (.const f []) (.bvar 1))
    piLam M (σOf []) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf []) ρ0 T) := by
  obtain ⟨hf, ha, hI, hb, hbd⟩ := param_checks f
  exact PiRawCtor.constructor_mem P PiValueRuleAttack.emptyBase f params [paramCtor] []
    ⟨0, Nat.zero_lt_succ 0⟩ params [paramField f] [.recursive [.bvar 0] [.bvar 1]]
    (fun A h => by have he := List.mem_singleton.mp h; subst A; rfl)
    ha rfl hf rfl
    (fun A h => by have he := List.mem_singleton.mp h; subst A; rfl)
    rfl (fun _ => 0) (paramSound P f (σOf []) (fun _ => 0)) hb hI
    (param_typed f) hbd

/-- The parameterized constructor has actual fitting arguments and produces
its exact parameter fibre; membership is not witnessed by an empty premise. -/
theorem param_inhabited (P : Premises4) (f : Nat) :
    TelFits (mkM P (paramTable P f)) (σOf []) (params ++ [paramField f]) ρ0
      [tyv pempty, pempty] ∧
    paramPred P [] (PiIndex.key [tyv pempty]) := by
  have hd : ∀ e ∈ ([.bvar 0] : List (Expr Nat)), occursConst f e = false := by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    rfl
  have ha : ∀ e ∈ ([.bvar 1] : List (Expr Nat)), occursConst f e = false := by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    rfl
  have hx : TelFits (mkM P (paramTable P f)) (σOf [])
      (params ++ [paramField f]) ρ0 [tyv pempty, pempty] := by
    refine ⟨tyv_pempty_mem_sort P (paramTable P f) (σOf []) ρ0 .zero, ?_, True.intro⟩
    apply (recursive_mem_iff P PiValueRuleAttack.emptyBase f (paramPred P) params
      (σOf []) [] [.bvar 0] [.bvar 1] hd ha rfl (vcons (tyv pempty) ρ0) pempty).mpr
    refine ⟨Equiv.rfl, ?_⟩
    intro p
    have hp := PiCompile.classValue_mem
      (Ed (mkM P PiValueRuleAttack.emptyBase) (tyv (pempty : PSet.{4}))) p.1
    exact (not_mem_pempty (mem_congr_right
      (ed_tyv (mkM P PiValueRuleAttack.emptyBase)
        (Or.inl (fun _ h => (not_mem_pempty h).elim))) hp)).elim
  refine ⟨hx, ?_⟩
  have hc : Clean f params.length paramCtor.fields := ⟨rfl, hd, ha, rfl, True.intro⟩
  exact close_tuple P PiValueRuleAttack.emptyBase f params [paramCtor] []
    ⟨0, Nat.zero_lt_succ 0⟩ hc [tyv pempty, pempty] hx

end Rcic.F3.PSet.PiRawCtorAttack
