import rcic.RcicF3PiRawRename
import rcic.RcicF3PiRawParamsAttack
/-! Original-admission binder insertion and context-offset self-attacks.
The semantic fixture pays a parameterized table, motive and field at every
numeric family label. It retains empty domains; data contexts below separately
attack indices and insertion within preceding locals. Hidden delta is a reader
computation, not a claim that its alias environment is typed.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawRenameAttack
open Rcic.Declarative PiRawCtorAttack

def original (f : Nat) : Expr Nat := policyPi [.bvar 0, .bvar 1, .bvar 2]
  (.app (.const f []) (.bvar 3))
/-- Elementary relation between the original field and the motive-shifted field. -/
theorem shifted (f : Nat) :
    Rcic.Declarative.lift 0 1 (original f) = PiRawParamsAttack.field f := by rfl
/-- Existing ordinary stored-type facts are paid without an apex hypothesis. -/
theorem type_facts (f : Nat) : TypeFacts (paramEnv f) := by
  apply typeFacts_extend (typeFacts_of_envWfT .empty)
  exact ⟨fun _ => rfl, rfl, fun _ h => nomatch h⟩
/-- Elementary admission at the ORIGINAL constructor-field depth. -/
theorem admission (f : Nat) :
    fieldAnalyze (paramEnv f) 16 f 0 1 0 1 (original f) =
      .permitted (.recursive 3) [] := by
  simp [fieldAnalyze, original, policyPi, piTelescopeFuel,
    whnfFuel, appsSpine, transparentBody, paramEnv, members_extend_eq,
    paramMember, transparent, domainsContainFuel, containsFamilyFuel,
    properFamilyFuel, exactParamLocals, indicesCleanFuel, familyIdx]
/-- Every premise of the original-admission bridge is paid at a real
parameterized field and actual shifted context, at every numeric label. -/
theorem inhabited (P : Premises4) (f : Nat) :
    let M := PiRawParamsAttack.model P f
    let ρ := PiRawParamsAttack.context P f
    TelFits M (σOf []) params ρ0 [tyv pempty] ∧
    PiRawParamsAttack.motive P f ∈ Ed M (den M (σOf []) (push [tyv pempty] ρ0)
      (policyPi [PiRawParamsAttack.major f] (.sort .zero))) ∧
    ρ 0 ∈ Ed M (den M (σOf []) ρ
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 (original f)))) ∧
    ∃ ds args ih, ds.length = 3 ∧ args.length = 1 ∧
      piTelescopeFuel (paramEnv f) 15
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 (original f))) =
        some (ds, foldApps (.const f []) args) ∧
      funIHType (paramEnv f) 15 1 (Rcic.Declarative.lift 0 1 (original f))
        (.bvar 0) 3 = some ih ∧
      Equiv ((PiIndex.tel M (σOf []) ds args ρ).erasedIHType M
        (PiRawMotive.guarded M (σOf []) (M.μ f []) (PiRawParamsAttack.motive P f)
          [tyv pempty] [] (push [tyv pempty] ρ0)) (ρ 0))
        (den M (σOf []) ρ ih) := by
  dsimp only
  let M := PiRawParamsAttack.model P f
  have hmo : PiRawParamsAttack.motive P f ∈ Ed M
      (den M (σOf []) (push [tyv pempty] ρ0)
        (policyPi [PiRawParamsAttack.major f] (.sort .zero))) :=
    PiValue.value_mem P (paramTable P f) (σOf []) (fun _ => True)
      [PiRawParamsAttack.major f] (push [tyv pempty] ρ0)
  obtain ⟨_, _, _, hb, _⟩ := param_checks f
  have he := PiRawRename.builder_original M rfl (σOf []) (fun _ => 0)
    f 0 (paramPred P []) params [] [tyv pempty] [PiRawParamsAttack.motive P f]
    rfl (PiRawParamsAttack.family P f) (PiRawParamsAttack.motive P f)
    (PiRawParamsAttack.value P f) hmo (type_facts f)
    (paramSound P f (σOf []) (fun _ => 0)) hb
    16 3 0 0 1 (original f) (.bvar 0) [] (Nat.le_refl 0) rfl (admission f)
    (PiRawParamsAttack.checks f).2 rfl (PiRawParamsAttack.field_mem P f)
  exact ⟨⟨tyv_pempty_mem_sort P (paramTable P f) (σOf []) ρ0 .zero, True.intro⟩,
    hmo, PiRawParamsAttack.field_mem P f, he⟩

def beta (f : Nat) : Expr Nat := .app (.lam (.sort .zero) (.bvar 0)) (original f)
def zeta (f : Nat) : Expr Nat := .letE (.sort .zero) (original f) (.bvar 0)
def delta (f : Nat) : Expr Nat := .app (.const (f + 1) []) (.bvar 0)
/-- Elementary hidden-redex and relabelling pins. Original admission has one
parameter and no preceding local; the raw builder receives the inserted motive.
The existing alias body is closed and parameterized. Delta is computation only. -/
theorem hidden_checks : ∀ f ∈ [1, 2, 987],
    ∀ T ∈ [original f, beta f, delta f, zeta f],
      fieldAnalyze (PiRawParamsAttack.env f) 32 f 0 1 0 1 T =
        .permitted (.recursive 3) [] ∧
      funIHType (PiRawParamsAttack.env f) 31 1
        (Rcic.Declarative.lift 0 1 T) (.bvar 0) 3 =
      funIHType (PiRawParamsAttack.env f) 31 1 (PiRawParamsAttack.field f) (.bvar 0) 3 := by
  decide

/-- Three dependent domains and an index reading the innermost argument;
two preceding locals sit between the parameter and recursive telescope. -/
def indexed (f : Nat) : Expr Nat := policyPi [.bvar 0, .bvar 1, .bvar 2]
  (foldApps (.const f []) [.bvar 5, .bvar 0])
/-- Elementary actual admission, arbitrary-block insertion within preceding
locals, and retained dependent index. This is a reader/context fixture, not
an additional full raw-group inhabitation. -/
theorem indexed_insertion : ∀ f ∈ [1, 2, 987],
    fieldAnalyze (paramEnv f) 32 f 0 1 1 3 (indexed f) =
      .permitted (.recursive 3) [.bvar 0] ∧
    piTelescopeFuel (paramEnv f) 31
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 3 (indexed f))) =
        some ([.bvar 1, .bvar 2, .bvar 3],
          foldApps (.const f []) [.bvar 9, .bvar 0]) ∧
    piTelescopeFuel (paramEnv f) 31
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 3 3 (indexed f))) =
        some ([.bvar 1, .bvar 2, .bvar 3],
          foldApps (.const f []) [.bvar 6, .bvar 0]) := by
  decide
/-- Every context block contains actual data. The parameter and dependent
index remain distinct after insertion. No semantic data equality is assumed. -/
theorem indexed_values (M : Interp.{4}) (σ : Nat → Nat) :
    let ρ := push [dataVal 20 [], dataVal 21 [], dataVal 22 []]
      (vcons (dataVal 13 []) (push [dataVal 8 [], dataVal 9 [], dataVal 10 [],
        dataVal 11 [], dataVal 12 []] (push [dataVal 7 []] ρ0)))
    [Expr.bvar 9, .bvar 0].map (den M σ ρ) = [dataVal 7 [], dataVal 22 []] := by
  rfl
/-- Insertion beyond the preceding-local cutoff would move the parameter
into a genuinely different, inhabited data context. The cutoff is necessary. -/
theorem wrong_cutoff (M : Interp.{4}) (σ : Nat → Nat) :
    let ρ := push [dataVal 20 [], dataVal 21 [], dataVal 22 []]
      (vcons (dataVal 13 []) (push [dataVal 8 [], dataVal 9 [], dataVal 10 [],
        dataVal 11 [], dataVal 12 []] (push [dataVal 7 []] ρ0)))
    ¬ Equiv (den M σ ρ (.bvar 6)) (dataVal 7 []) := by
  change ¬ Equiv (dataVal 10 []) (dataVal 7 [])
  intro h
  have ht : 10 = 7 := (dataVal_inj rfl h).1
  cases ht
end Rcic.F3.PSet.PiRawRenameAttack
