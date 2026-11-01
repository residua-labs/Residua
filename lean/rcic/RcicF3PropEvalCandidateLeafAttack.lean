import rcic.RcicF3PropEvalCandidateAttack
import rcic.RcicF3PropEvalIHAttack
import rcic.RcicF3RawFamilyLevels

/-!
# Inhabited depth-three extraction from actual guarded-candidate membership

This auxiliary normalized proof field has three inhabited proposition-code
domains and reaches the complete empty-parameter key of the admitted AccR
fixture. Its membership is produced from the actual closed candidate. The
generic leaf extraction then produces a nonempty evaluated result at its
fitting argument list. This field is a semantic component witness, not the
stored AccR constructor field. Universal StepAG remains open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateLeafAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)

def domains : List (Expr Nat) := [.sort .zero, .sort .zero, .sort .zero]
def arguments : List (Expr Nat) := [.bvar 3]
def assignment : Nat → PSet.{4} := vcons parameter ρ0
def field : Expr Nat := policyPi domains (foldApps (.const 0 []) arguments)

noncomputable def model (P : Premises4) : Interp.{4} :=
  mkM P (table P (installed P) fd (X P))

theorem parameters_free :
    ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false := by
  intro e he
  change e ∈ [(.sort .zero : Expr Nat)] at he
  have heq := List.mem_singleton.mp he
  subst e
  rfl

theorem domains_free : ∀ e ∈ domains, occursConst fd.fref e = false := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  have heq : e = .sort .zero := List.mem_singleton.mp he
  subst e
  rfl

theorem arguments_free : ∀ e ∈ arguments, occursConst fd.fref e = false := by
  intro e he
  have heq : e = .bvar 3 := List.mem_singleton.mp he
  subst e
  rfl

/-- The argument keeps the outer parameter after all three normalized binders. -/
theorem reached_arguments (M : Interp.{4}) (σ : Nat → Nat)
    (zs : List PSet.{4}) (hzs : TelFits M σ domains assignment zs) :
    arguments.map (den M σ (push zs assignment)) = [parameter] := by
  cases zs with
  | nil => exact False.elim hzs
  | cons a zs =>
    cases zs with
    | nil => exact False.elim hzs.2
    | cons b zs =>
      cases zs with
      | nil => exact False.elim hzs.2.2
      | cons c zs =>
        cases zs with
        | nil => rfl
        | cons d zs => exact False.elim hzs.2.2.2

theorem inhabited_domain (P : Premises4) :
    TelFits (ctx P).M (ctx P).σ domains assignment
      [parameter, parameter, parameter] := by
  have hm : parameter ∈ Ed (ctx P).M (tyv (U W4 0)) :=
    mem_congr_right (ed_tyv (ctx P).M (U4_dich 0)).symm (parameter_mem P)
  exact ⟨hm, hm, hm, True.intro⟩

/-- The actual restricted raw frame supplies the reached proof fibre. -/
theorem fitted_leaf (P : Premises4) :
    pempty ∈ fitFrame P (installed P) fd (X P) [] (key [parameter]) := by
  have hp : TelFits (model P) (σOf []) (fd.params ++ fd.indices) ρ0 [parameter] := by
    exact ⟨mem_congr_right (ed_tyv (model P) (U4_dich 0)).symm
      (parameter_mem P), True.intro⟩
  have hx : pempty ∈ X P [] (key [parameter]) :=
    (PropEvalCandidateAttack.component_witness P).2.2.2.1
  obtain ⟨j, hj⟩ := hx
  exact mem_sep.mpr ⟨j, hp, hj⟩

/-- This is actual candidate-field membership, with no child-evaluation premise. -/
theorem normalized_member (P : Premises4) :
    pempty ∈ Ed (model P) (den (model P) (ctx P).σ assignment field) := by
  let M := model P
  let t := tel M (ctx P).σ domains arguments assignment
  let F := fitFrame P (installed P) fd (X P) []
  have ht : t.DomainsDich :=
    PiSyntaxCompile.compile_domains M (ctx P).σ _ domains assignment
  have htrue : pempty ∈ Ed M (t.erasedType M (fun _ => tv True)) :=
    (PiPropField.member_iff M t ht (fun _ => True) pempty).mpr
      ⟨Equiv.rfl, fun _ => True.intro⟩
  have hreach : ∀ p, t.result p = key [parameter] := by
    intro p
    obtain ⟨zs, hzs, he⟩ := PiSyntaxCompile.result_fits M (ctx P).σ
      (read M (ctx P).σ arguments) domains assignment p
    exact he.trans (congrArg key (reached_arguments M (ctx P).σ zs hzs))
  have hx : pempty ∈ Ed M (t.erasedType M F) :=
    t.erasedType_mono_on M ht (fun _ => tv True) F (fun _ => dich_tv True)
      (fitFrame_dich P (installed P) fd (X P)
        (PropEvalCandidateAttack.candidate_admissible P) [])
      (fun p y hy => by
        change y ∈ F (t.result p)
        rw [hreach p]
        exact mem_congr_left (mem_tv.mp hy).2.symm (fitted_leaf P)) pempty htrue
  exact mem_congr_right (recursiveField_ed_at P (installed P) fd (X P)
    (PropEvalCandidateAttack.candidate_admissible P) parameters_free [] (ctx P).σ [] rfl
    domains arguments rfl assignment) hx

/-- Generic extraction is exercised on an inhabited depth-three argument domain. -/
theorem children (P : Premises4) (zs : List PSet.{4})
    (hzs : TelFits (ctx P).M (ctx P).σ domains assignment zs) :
    ∃ z, PropEval.Eval (ctx P)
      (key (arguments.map (den (ctx P).M (ctx P).σ (push zs assignment)))) z := by
  exact PropEvalCandidate.leaf_eval P (installed P) (ctx P) rfl
    (RawFamilyPropAttack.acc_closed P (installed P)).1 parameters_free
    domains arguments domains_free arguments_free rfl assignment pempty
    (fun ys hys => by
      change LEq (arguments.map (den (ctx P).M (ctx P).σ (push ys assignment))) [parameter]
      rw [reached_arguments (ctx P).M (ctx P).σ ys hys]
      exact LEq.refl _) (normalized_member P) zs hzs

def Witness (P : Premises4) : Prop :=
  domains.length = 3 ∧
  TelFits (ctx P).M (ctx P).σ domains assignment [parameter, parameter, parameter] ∧
  pempty ∈ Ed (model P) (den (model P) (ctx P).σ assignment field) ∧
  ∃ z, PropEval.Eval (ctx P) (key [parameter]) z ∧ z ∈ domain ∧ ¬ Equiv z pempty

theorem component_witness (P : Premises4) : Witness P := by
  have hz := children P [parameter, parameter, parameter] (inhabited_domain P)
  rw [reached_arguments (ctx P).M (ctx P).σ _ (inhabited_domain P)] at hz
  obtain ⟨z, he⟩ := hz
  have ht := PropEvalAttack.eval_typed P he
  refine ⟨rfl, inhabited_domain P, normalized_member P, z, he, ht, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

/-- Closure, the inhabited normalized field and extraction concern one candidate. -/
theorem composed_witness (P : Premises4) :
    PropEvalCandidateAttack.Witness P ∧ Witness P :=
  ⟨PropEvalCandidateAttack.component_witness P, component_witness P⟩

theorem composed_nonrefutable (P : Premises4) :
    ¬ ((PropEvalCandidateAttack.Witness P ∧ Witness P) → (Premises4 → False)) :=
  fun h => h (composed_witness P) P

end Rcic.F3.PSet.PropEvalCandidateLeafAttack
