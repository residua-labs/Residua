import rcic.RcicF3PiRawParams
import rcic.RcicF3PiRawCtorAttack
/-! Parameterized raw-IH non-vacuity and parameter-offset attacks.
The raw fixture pays ordinary environment soundness at every family label;
its recursive domain is empty. Separate depth-three data fixtures retain
nonempty domains. Hidden delta pins assert computation only.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawParamsAttack
open Rcic.Declarative PiRawCtorAttack

def model (P : Premises4) (f : Nat) := mkM P (paramTable P f)
def major (f : Nat) : Expr Nat := .app (.const f []) (.bvar 0)
def motive (P : Premises4) (f : Nat) :=
  PiValue.value (model P f) (σOf []) (fun _ => True) [major f] (push [tyv pempty] ρ0)
def field (f : Nat) : Expr Nat := policyPi [.bvar 1, .bvar 2, .bvar 3]
  (.app (.const f []) (.bvar 4))
def before (P : Premises4) (f : Nat) := vcons (motive P f) (push [tyv pempty] ρ0)
def value (P : Premises4) (f : Nat) :=
  piLam (model P f) (σOf []) (fun _ => pempty) (before P f) (field f)
def pre (P : Premises4) (f : Nat) := [motive P f, value P f]
def context (P : Premises4) (f : Nat) := push (pre P f) (push [tyv pempty] ρ0)

/-- The actual parameterized table agrees with its complete value. -/
theorem family (P : Premises4) (f : Nat) :
    Equiv ((model P f).μ f [])
      (PiValue.value (model P f) (σOf []) (paramPred P []) params ρ0) := by
  have he := PiValue.value_free P PiValueRuleAttack.emptyBase f
    (PiValue.table P PiValueRuleAttack.emptyBase (paramPred P) params)
    (PiValueRuleAttack.emptyBase f) (σOf []) (paramPred P []) params
    (fun A hA => by have ha := List.mem_singleton.mp hA; subst A; rfl) ρ0
  rw [PiIndependent.upd_self] at he
  change Equiv ((upd PiValueRuleAttack.emptyBase f
    (PiValue.table P PiValueRuleAttack.emptyBase (paramPred P) params)) f []) _
  rw [upd_eq]
  exact he.symm ▸ Equiv.rfl
/-- A real raw field member in its lifted, parameterized context. The empty
domain is retained, rather than turned into a nonemptiness premise. -/
theorem field_mem (P : Premises4) (f : Nat) :
    context P f 0 ∈ Ed (model P f) (den (model P f) (σOf []) (context P f)
      (Rcic.Declarative.lift 0 1 (field f))) := by
  change value P f ∈ Ed (model P f) (den (model P f) (σOf [])
    (push [value P f] (before P f)) (Rcic.Declarative.lift 0 1 (field f)))
  have he : den (model P f) (σOf []) (push [value P f] (before P f))
      (Rcic.Declarative.lift 0 1 (field f)) =
      den (model P f) (σOf []) (before P f) (field f) :=
    den_lift0_push (model P f) (σOf []) [value P f] (before P f) (field f)
  rw [he]
  apply piLam_mem (model P f) (σOf []) (envResp_const pempty)
  intro x hx
  change x ∈ Ed (model P f) (tyv pempty) at hx
  exact (not_mem_pempty (mem_congr_right (ed_tyv (model P f)
    (Or.inl (fun _ h => (not_mem_pempty h).elim))) hx)).elim
/-- Elementary exact admission and bounded constant-instance pins. -/
theorem checks (f : Nat) :
    fieldAnalyze (paramEnv f) 16 f 0 1 0 3 (Rcic.Declarative.lift 0 1 (field f)) =
      .permitted (.recursive 3) [] ∧
    InstOK (paramEnv f) (σOf []) (fun _ => 0) (Rcic.Declarative.lift 0 1 (field f)) := by
  refine ⟨?_, ?_⟩
  · simp [fieldAnalyze, field, policyPi, Rcic.Declarative.lift, piTelescopeFuel,
      whnfFuel, appsSpine, transparentBody, paramEnv, members_extend_eq,
      paramMember, transparent, domainsContainFuel, containsFamilyFuel,
      properFamilyFuel, exactParamLocals, indicesCleanFuel, familyIdx]
  · intro r ls hr
    change (r, ls) ∈ ([] ++ [] ++ [] ++ ([(f, [])] ++ [])) at hr
    simp only [List.nil_append, List.append_nil] at hr
    have he := List.mem_singleton.mp hr
    cases he
    exact ⟨paramMember, members_extend_eq _ _ _, rfl,
      fun _ h => (List.not_mem_nil _ h).elim⟩
/-- All premises of the parameterized raw-IH composition are paid at this
actual table, context, motive and field, for every numeric family reference. -/
theorem inhabited (P : Premises4) (f : Nat) :
    let M := model P f
    let ρ := context P f
    TelFits M (σOf []) params ρ0 [tyv pempty] ∧
    motive P f ∈ Ed M (den M (σOf []) (push [tyv pempty] ρ0)
      (policyPi [major f] (.sort .zero))) ∧
    ρ 0 ∈ Ed M (den M (σOf []) ρ (Rcic.Declarative.lift 0 1 (field f))) ∧
    ∃ ds args ih, ds.length = 3 ∧ args.length = 1 ∧
      piTelescopeFuel (paramEnv f) 15 (Rcic.Declarative.lift 0 1 (field f)) =
        some (ds, foldApps (.const f []) args) ∧
      funIHType (paramEnv f) 15 1 (field f) (.bvar 0) 3 = some ih ∧
      Equiv ((PiIndex.tel M (σOf []) ds args ρ).erasedIHType M
        (PiRawMotive.guarded M (σOf []) (M.μ f []) (motive P f) [tyv pempty] []
          (push [tyv pempty] ρ0)) (ρ 0))
        (den M (σOf []) ρ ih) := by
  dsimp only
  let M := model P f
  have hmo : motive P f ∈ Ed M (den M (σOf []) (push [tyv pempty] ρ0)
      (policyPi [major f] (.sort .zero))) :=
    PiValue.value_mem P (paramTable P f) (σOf []) (fun _ => True)
      [major f] (push [tyv pempty] ρ0)
  obtain ⟨_, _, _, hb, _⟩ := param_checks f
  have he := PiRawParams.admitted_builder_spec M rfl (σOf []) (fun _ => 0)
    f 0 (paramPred P []) params [] [tyv pempty] (pre P f) rfl (family P f)
    (motive P f) hmo (paramSound P f (σOf []) (fun _ => 0)) hb
    16 3 (field f) (.bvar 0) [] (checks f).1 (checks f).2 rfl (field_mem P f)
  exact ⟨⟨tyv_pempty_mem_sort P (paramTable P f) (σOf []) ρ0 .zero, True.intro⟩,
    hmo, field_mem P f, he⟩
def beta (f : Nat) : Expr Nat := .app (.lam (.sort .zero) (.bvar 0)) (field f)
def zeta (f : Nat) : Expr Nat := .letE (.sort .zero) (field f) (.bvar 0)
def aliasBody (f : Nat) : Expr Nat := .lam (.sort .zero)
  (policyPi [.bvar 0, .bvar 1, .bvar 2] (.app (.const f []) (.bvar 3)))
def aliasMember (f : Nat) : CheckedMember :=
  ⟨.definitionM, 0, .pi (.sort .zero) (.sort .zero), some (aliasBody f)⟩
def env (f : Nat) := extendEnv (paramEnv f) (f + 1) (aliasMember f)
def delta (f : Nat) : Expr Nat := .app (.const (f + 1) []) (.bvar 1)
def bad (f k : Nat) : Expr Nat := policyPi [.bvar 2, .bvar 3, .bvar 4]
  (.app (.const f []) (.bvar k))

/-- Elementary reader/builder computations; the delta pin supplies no typed
alias-environment claim. Its body is parameterized, rather than an open alias. -/
theorem hidden_checks : ∀ f ∈ [1, 2, 987], ∀ A ∈ [field f, beta f, delta f, zeta f],
    fieldAnalyze (env f) 32 f 0 1 0 3 (Rcic.Declarative.lift 0 1 A) =
      .permitted (.recursive 3) [] ∧
    funIHType (env f) 31 1 A (.bvar 0) 3 =
      funIHType (env f) 31 1 (field f) (.bvar 0) 3 := by
  decide
/-- Elementary off-by-one and distant parameter-offset refusals. -/
theorem bad_offsets : ∀ f ∈ [1, 2, 987], ∀ k ∈ [0, 1, 2, 3, 4, 6, 7, 99],
    fieldAnalyze (env f) 32 f 0 1 0 3 (bad f k) ≠ .permitted (.recursive 3) [] := by
  decide
/-- A wrong parameter offset reads genuinely different data, even when
every binder block is inhabited. This is a context computation, not a raw group. -/
theorem wrong_context_refuted (M : Interp.{4}) (σ : Nat → Nat) :
    ¬ Equiv (den M σ (push [dataVal 7 [], dataVal 7 [], dataVal 7 []]
      (push [dataVal 8 [], dataVal 8 []] (push [dataVal 7 []] ρ0))) (.bvar 4))
      (dataVal 7 []) := by
  change ¬ Equiv (dataVal 8 []) (dataVal 7 [])
  intro h
  have ht : 8 = 7 := (dataVal_inj rfl h).1
  cases ht
end Rcic.F3.PSet.PiRawParamsAttack
