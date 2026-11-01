import rcic.RcicF3PiValueExtract

import rcic.RcicF3PiValueRuleAttack
import rcic.RcicF3PiIndependentAttack
/-! Executable extraction attacks and an inhabited typed raw constructor.
The positive constructor supplies EnvSound, bounds and actual original
field membership internally; this is not a complete Acc group model or
a universal producer. Computation pins are elementary. `closure_claim = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Rcic.F3.PSet.PiValueExtractAttack
open Rcic.Declarative PiValueRule PiValueExtract

def accSpec : FieldSpec := .recursive RoleAttacks.accDomains [.bvar 1]

/-- Exact extraction pins for the typed original and hidden Acc field presentations. -/
theorem acc_extract :
    ∀ T ∈ [Rcic.Declarative.Ann.paFieldDom, PiSyntaxAttack.betaField,
      PiSyntaxAttack.deltaField, PiSyntaxAttack.zetaField],
    field PiSyntaxAttack.env 65 10 0 0 1 1 T = some accSpec := by
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · simp only [field, RoleAttacks.accAnalyze, RoleAttacks.accRead]
    rfl
  · simp only [field, RoleAttacks.betaAnalyze, RoleAttacks.betaRead]
    rfl
  · simp only [field, RoleAttacks.deltaAnalyze, RoleAttacks.deltaRead]
    rfl
  · simp only [field, RoleAttacks.zetaAnalyze, RoleAttacks.zetaRead]
    rfl

/-- The full three dependent arguments survive extraction at aliases and a distant label. -/
theorem triple_extract : ∀ f ∈ [1, 2, 987],
    fields emptyEnv 32 f 0 0 3 0 [PiIndependentAttack.triType f] =
      some [.recursive PiIndependentAttack.triDomains PiIndependentAttack.triArgs] := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

def localField (f : Nat) : Expr Nat := .pi (.bvar 0) (.const f [])
def localFields (f : Nat) : List (Expr Nat) := [.sort .zero, localField f]
def localCtor : Constructor := ⟨[.plain (.sort .zero), .recursive [.bvar 0] []], []⟩
def localMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def localEnv (f : Nat) : ResolvedEnv := extendEnv emptyEnv f localMember
def localPred (P : Premises4) := predicate P PiValueRuleAttack.emptyBase [] [localCtor]
def localTable (P : Premises4) (f : Nat) :=
  upd PiValueRuleAttack.emptyBase f (PiValue.table P PiValueRuleAttack.emptyBase (localPred P) [])

/-- The raw tuple fixture supplies ordinary EnvSound, for every family reference. -/
theorem localSound (P : Premises4) (f : Nat) (σ K : Nat → Nat) :
    EnvSound (mkM P (localTable P f)) σ K (localEnv f) 0 := by
  have shape : ∀ r m, (localEnv f).members r = some m → r = f ∧ m = localMember := by
    intro r m hm
    by_cases hr : r = f
    · subst r
      change (extendEnv emptyEnv f localMember).members f = some m at hm
      rw [members_extend_eq] at hm
      exact ⟨rfl, (Option.some.inj hm).symm⟩
    · change (extendEnv emptyEnv f localMember).members r = some m at hm
      rw [members_extend_ne emptyEnv f localMember r hr] at hm
      cases hm
  apply envSound_of_allSound P (K := K) (μ := localTable P f) (E := localEnv f) ?_ ?_ σ 0
  · intro r m hm
    obtain ⟨hr, hm⟩ := shape r m hm
    subst r
    subst m
    apply PiValue.member_sound P (localTable P f) K f localMember (localPred P) []
      (fun _ => rfl) rfl rfl rfl
    intro vs
    change Equiv ((upd PiValueRuleAttack.emptyBase f
      (PiValue.table P PiValueRuleAttack.emptyBase (localPred P) [])) f vs) _
    rw [upd_eq]
    exact Equiv.rfl
  · intro r m hm
    obtain ⟨_, hm⟩ := shape r m hm
    subst m
    exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩

/-- Literal bounds and executable admission for a dependent empty-domain constructor. -/
theorem local_checks (f : Nat) (σ K : Nat → Nat) :
    fields (localEnv f) 8 f 0 0 0 0 (localFields f) = some localCtor.fields ∧
    fieldShapesFuel (localEnv f) 8 f 0 0 0 0 (localFields f) =
      some [.nonrecursive, .recursive 1] ∧
    (∀ A ∈ localFields f, InstOK (localEnv f) σ K A) ∧
      BodiesOK (localEnv f) σ K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [fields, field, fieldAnalyze, localFields, localField, localCtor,
      piTelescopeFuel, whnfFuel, appsSpine, transparentBody, localEnv,
      members_extend_eq, localMember, transparent, domainsContainFuel,
      containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
      familyIdx]
  · simp [fieldShapesFuel, fieldAnalyze, localFields, localField,
      piTelescopeFuel, whnfFuel, appsSpine, transparentBody, localEnv,
      members_extend_eq, localMember, transparent, domainsContainFuel,
      containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
      familyIdx]
  · intro A hA r ls hr
    simp only [localFields, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · cases hr
    · change (r, ls) ∈ [] ++ [(f, [])] at hr
      have he := List.mem_singleton.mp hr
      cases he
      exact ⟨localMember, members_extend_eq _ _ _, rfl,
        fun _ h => (List.not_mem_nil _ h).elim⟩
  · intro r m b ls hm hbody
    by_cases hr : r = f
    · subst r
      change (extendEnv emptyEnv f localMember).members f = some m at hm
      rw [members_extend_eq] at hm
      cases hm
      cases hbody
    · change (extendEnv emptyEnv f localMember).members r = some m at hm
      rw [members_extend_ne emptyEnv f localMember r hr] at hm
      cases hm

/-- An actual raw dependent tuple inhabits the admitted constructor fields. -/
theorem local_tuple (P : Premises4) (f : Nat) :
    TelFits (mkM P (localTable P f)) (σOf []) (localFields f) ρ0
      [tyv pempty, pempty] := by
  refine ⟨tyv_pempty_mem_sort P (localTable P f) (σOf []) ρ0 .zero, ?_, True.intro⟩
  have hd : ∀ e ∈ ([.bvar 0] : List (Expr Nat)), occursConst f e = false := by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    rfl
  have ha : ∀ e ∈ ([] : List (Expr Nat)), occursConst f e = false :=
    fun _ h => (List.not_mem_nil _ h).elim
  apply (recursive_mem_iff P PiValueRuleAttack.emptyBase f (localPred P) []
    (σOf []) [] [.bvar 0] [] hd ha rfl (vcons (tyv pempty) ρ0) pempty).mpr
  refine ⟨Equiv.rfl, ?_⟩
  intro p
  have hp := PiCompile.classValue_mem
    (Ed (mkM P PiValueRuleAttack.emptyBase) (tyv (pempty : PSet.{4}))) p.1
  exact (not_mem_pempty (mem_congr_right
    (ed_tyv (mkM P PiValueRuleAttack.emptyBase)
      (Or.inl (fun _ h => (not_mem_pempty h).elim))) hp)).elim

/-- End-to-end raw admission closure with all environment and tuple premises supplied. -/
theorem local_closed (P : Premises4) (f : Nat) :
    localPred P [] (PiIndex.key []) ∧
      pempty ∈ Ed (mkM P (localTable P f))
        (den (mkM P (localTable P f)) (σOf []) ρ0 (.const f [])) := by
  obtain ⟨hf, ha, hI, hb⟩ := local_checks f (σOf []) (fun _ => 0)
  have hp := close_admitted_tuple P PiValueRuleAttack.emptyBase f [] [localCtor] []
    ⟨0, Nat.zero_lt_succ 0⟩ ha (Nat.zero_le _) rfl hf (fun _ => 0)
    (localSound P f (σOf []) (fun _ => 0)) hb hI
    [tyv pempty, pempty] (local_tuple P f)
  change localPred P [] (PiIndex.key []) at hp
  refine ⟨hp, ?_⟩
  have he := PiIndependent.leaf_read P PiValueRuleAttack.emptyBase f
    (PiValue.table P PiValueRuleAttack.emptyBase (localPred P) []) (σOf []) [] []
    (fun _ h => (List.not_mem_nil _ h).elim) ρ0
  change pempty ∈ Ed (mkM P (localTable P f))
    (den (mkM P (localTable P f)) (σOf []) ρ0 (foldApps (.const f []) []))
  unfold localTable
  rw [he]
  exact (PiValue.apply_mem_iff (mkM P PiValueRuleAttack.emptyBase) (σOf [])
    (localPred P []) [] ρ0 [] rfl pempty).mpr ⟨True.intro, hp, Equiv.rfl⟩

/-- Malformed dependent index arity refuses rather than truncating the tuple. -/
theorem wrong_arity_refused : ∀ f ∈ [1, 2, 987],
    fields emptyEnv 32 f 0 0 2 0 [PiIndependentAttack.triType f] = none := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

/-- The positive fixture is typed raw syntax, rather than an unconstrained semantic signature. -/
def local_typed (f : Nat) :
    HasTyT (localEnv f) 0 [] (policyPi (localFields f) (.const f []))
      (.sort (.imax (.succ .zero) (.imax (.imax .zero .zero) .zero))) := by
  apply HasTyT.pi [] _ _ _ _ (.sort [] .zero)
  · apply HasTyT.pi _ _ (.imax .zero .zero) _ .zero
    · exact .pi _ _ .zero _ .zero (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)
        (.const _ f [] localMember (members_extend_eq _ _ _) rfl rfl)
    · exact .const _ f [] localMember (members_extend_eq _ _ _) rfl rfl

end Rcic.F3.PSet.PiValueExtractAttack
