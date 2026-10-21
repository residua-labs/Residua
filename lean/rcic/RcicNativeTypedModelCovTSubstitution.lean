import rcic.RcicNativeTypedModelK
import rcic.RcicNativeTypedModelSubst
import rcic.RcicNativeTypedModelCovSSubstitutionData
import rcic.RcicNativeTypedModelCovTView

/-!
# A bounded forward substitution supplier for observed rows

The result below keeps the actual demand observations and the actual body
observation. It forgets them to the landed `ApproxT` carrier, applies its
forward substitution theorem, and returns to `ApproxTK` only when the
instantiated body is in the transitive K-free fragment. The fragment
condition is explicit; this is not substitution for arbitrary guarded K
observations, a view supplier, or a semantic interpretation theorem.
The staged version preserves the body's information budget because its
output compact is unchanged; native arity and stage remain separate.

The concrete control uses the already inhabited polymorphic type argument
from `CovSSubstitutionData`. Its singleton demand, body, beta source, and
substituted result all retain the same deep nonbottom compact. Native beta
typing and CK2 readback are supplied independently. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit ReadbackCK2Audit
open TypedModelCovSAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- Forward realization of an actual finite row. Only the instantiated
body is required to be K-free; no unproved K substitution port is used. -/
theorem covT_approxTK_subst0_of_kFree {D a B : Expr Nat}
    {ds : List CptT} {c : CptT}
    (hfree : KFreeT E (instantiate0 a B))
    (ha : ∀ u ∈ ds, ApproxTK E n Γ ρ a u)
    (hb : ApproxTK E n (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) B c) :
    ApproxTK E n Γ ρ (instantiate0 a B) c := by
  apply ApproxTK.free hfree
  apply (approxT_subst0_iff E ρ a B c).mpr
  apply approxT_mono_env ?_ (approxTK_forget hb)
  intro i u hu
  cases i with
  | zero => exact approxTK_forget (ha u hu)
  | succ i => exact hu

/-- Environments with no indexed proposition recursor discharge the
fragment condition by the existing transitive-fragment supplier. -/
theorem covT_approxTK_subst0_of_no_indexed
    (hE : ∀ r, ¬ IndexedPropRecT E r) {D a B : Expr Nat}
    {ds : List CptT} {c : CptT}
    (ha : ∀ u ∈ ds, ApproxTK E n Γ ρ a u)
    (hb : ApproxTK E n (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) B c) :
    ApproxTK E n Γ ρ (instantiate0 a B) c :=
  covT_approxTK_subst0_of_kFree
    (kFreeT_of_no_indexed hE (instantiate0 a B)) ha hb

/-- The admitted Nat environment is an unconditional instance of the
bounded result; its recursive recursor schemas are already K-free. -/
theorem covT_approxTK_subst0_nat {D a B : Expr Nat}
    {ds : List CptT} {c : CptT}
    (ha : ∀ u ∈ ds, ApproxTK natEnvU n Γ ρ a u)
    (hb : ApproxTK natEnvU n (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) B c) :
    ApproxTK natEnvU n Γ ρ (instantiate0 a B) c :=
  covT_approxTK_subst0_of_kFree
    (kFreeT_natEnvU (instantiate0 a B)) ha hb

/-- The same actual compact is retained at the same information stage.
The stage is not a bound on beta steps or derivation height. -/
theorem covT_approxTKStage_subst0_of_kFree {stage : Nat}
    {D a B : Expr Nat} {ds : List CptT} {c : CptT}
    (hfree : KFreeT E (instantiate0 a B))
    (ha : ∀ u ∈ ds, ApproxTKStage E n stage Γ ρ a u)
    (hb : ApproxTKStage E n stage (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) B c) :
    ApproxTKStage E n stage Γ ρ (instantiate0 a B) c :=
  ⟨covT_approxTK_subst0_of_kFree hfree (fun u hu => (ha u hu).1) hb.1,
    hb.2⟩

/-- The view's fixed-argument admissibility supplies exactly the demand
observations consumed above. Native typing is retained in that premise. -/
theorem covT_admissible_subst0_of_kFree {stage : Nat}
    {D a B : Expr Nat} {ds : List CptT} {c : CptT}
    (hfree : KFreeT E (instantiate0 a B))
    (ha : CovTAdmissible E n stage Γ ρ D a ds)
    (hb : ApproxTKStage E n stage (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) B c) :
    ApproxTKStage E n stage Γ ρ (instantiate0 a B) c :=
  covT_approxTKStage_subst0_of_kFree hfree ha.observed hb

/-- The closed argument used by the concrete substitution measurement
has a direct structural K-free witness in every environment. -/
theorem covT_substitution_argument_kFree (E : ResolvedEnv) :
    KFreeT E cexPolyIdTy :=
  kFreeT_pi (kFreeT_sort E (.succ .zero))
    (kFreeT_pi (kFreeT_bvar E 0) (kFreeT_bvar E 1))

/-- This observation is obtained by the forward theorem above, retaining
the very same finite demand and compact as the binder-body observation. -/
theorem covT_substitution_deep_result (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n [] EnvT.bot (instantiate0 cexPolyIdTy (.bvar 0))
      covSSubstitutionDeep := by
  apply covT_approxTK_subst0_of_kFree
    (D := .sort (.succ (.succ .zero)))
    (a := cexPolyIdTy) (B := .bvar 0)
    (ds := [covSSubstitutionDeep]) (covT_substitution_argument_kFree E)
  · intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact covSSubstitution_deep_observed E n [] EnvT.bot
  · exact covSSubstitution_body_observed E n

/-- An explicitly annotated native beta source for that same row. -/
def covTSubstitutionBeta : Expr Nat :=
  .app (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) cexPolyIdTy

/-- The function table uses the actual deep argument compact as its
singleton demand and its output; this is not an empty-row control. -/
def covTSubstitutionBetaTable : CptT :=
  .lam [([covSSubstitutionDeep], covSSubstitutionDeep)]

def covT_substitution_beta_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ covTSubstitutionBeta (.sort (.succ (.succ .zero))) :=
  .app Γ (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) cexPolyIdTy
    (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero)))
    (.lam Γ (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
      (.bvar 0) (.sort (.succ (.succ .zero)))
      (.sort Γ (.succ (.succ .zero))) (.bvar _ 0 _ rfl))
    (covSSubstitution_argument_hasTy E n Γ)

def covT_substitution_beta_conv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ covTSubstitutionBeta cexPolyIdTy
      (.sort (.succ (.succ .zero))) :=
  .beta Γ (.sort (.succ (.succ .zero))) (.bvar 0) cexPolyIdTy
    (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
    (.sort Γ (.succ (.succ .zero))) (.bvar _ 0 _ rfl)
    (covSSubstitution_argument_hasTy E n Γ)

theorem covT_substitution_beta_read (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    RedR (WhStepCK2 E n) Γ covTSubstitutionBeta cexPolyIdTy :=
  .step (.ctx (.beta (.sort (.succ (.succ .zero))) (.bvar 0) cexPolyIdTy))
    (.refl _)

theorem covT_substitution_beta_function_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
      covTSubstitutionBetaTable := by
  refine .lam (a := .sort) ?_ ?_ ?_ ?_
  · simpa only [sortCode_succ] using
      approxTK_sort_code E n Γ ρ (.succ (.succ .zero))
  · intro row hrow u hu
    rcases List.mem_singleton.mp hrow with rfl
    rcases List.mem_singleton.mp hu with rfl
    rw [CTyS]
    exact Or.inr covSSubstitutionDeep_tyCode
  · exact ⟨([covSSubstitutionDeep], covSSubstitutionDeep),
      List.mem_singleton_self _, CptT.noConfusion⟩
  · intro row hrow
    rcases List.mem_singleton.mp hrow with rfl
    exact .free (kFreeT_bvar E 0) (.bvar (List.mem_singleton_self _))

theorem covT_substitution_beta_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ covTSubstitutionBeta covSSubstitutionDeep := by
  refine .app (covT_substitution_beta_function_observed E n Γ ρ)
    (List.mem_singleton_self _) ?_
  intro u hu
  rcases List.mem_singleton.mp hu with rfl
  exact covSSubstitution_deep_observed E n Γ ρ

/-- A fully inhabited native/model control. The retained landed data
contain both context well-formedness proofs, finite-joint environment
typing, coherence, and the actual argument/body observations. The fresh
result uses the forward theorem, and the fresh beta source has independent
native typing, conversion, and CK2 readback. -/
theorem covT_substitution_native_control (n : Nat) :
    CovSSubstitutionNativeData n ∧
    Nonempty (HasTyT emptyEnv n [] covTSubstitutionBeta
      (.sort (.succ (.succ .zero)))) ∧
    Nonempty (ConvT emptyEnv n [] covTSubstitutionBeta cexPolyIdTy
      (.sort (.succ (.succ .zero)))) ∧
    RedR (WhStepCK2 emptyEnv n) [] covTSubstitutionBeta cexPolyIdTy ∧
    NormalR (WhStepCK2 emptyEnv n) [] cexPolyIdTy ∧
    ApproxTK emptyEnv n [] EnvT.bot covTSubstitutionBeta covSSubstitutionDeep ∧
    ApproxTK emptyEnv n [] EnvT.bot
      (instantiate0 cexPolyIdTy (.bvar 0)) covSSubstitutionDeep ∧
    covSSubstitutionDeep ≠ .bot :=
  ⟨covSSubstitution_native_data n,
    ⟨covT_substitution_beta_hasTy emptyEnv n []⟩,
    ⟨covT_substitution_beta_conv emptyEnv n []⟩,
    covT_substitution_beta_read emptyEnv n [], normalR_piCK2 [] _ _,
    covT_substitution_beta_observed emptyEnv n [] EnvT.bot,
    covT_substitution_deep_result emptyEnv n, CptT.noConfusion⟩

/-- The same nonempty row is admissible and realized at one explicit
common stage. This uses the staged forward theorem, not an independent
shallow observation of the substituted result. -/
theorem covT_substitution_staged_control (n : Nat) :
    CovSSubstitutionNativeData n ∧
    ∃ stage,
      CovTAdmissible emptyEnv n stage [] EnvT.bot
        (.sort (.succ (.succ .zero))) cexPolyIdTy [covSSubstitutionDeep] ∧
      ApproxTKStage emptyEnv n stage covSSubstitutionCtx covSSubstitutionEnv
        (.bvar 0) covSSubstitutionDeep ∧
      ApproxTKStage emptyEnv n stage [] EnvT.bot
        covTSubstitutionBeta covSSubstitutionDeep ∧
      ApproxTKStage emptyEnv n stage [] EnvT.bot
        (instantiate0 cexPolyIdTy (.bvar 0)) covSSubstitutionDeep ∧
      covSSubstitutionDeep ≠ .bot := by
  let stage := covTObservationBudget covSSubstitutionDeep
  have ha : CovTAdmissible emptyEnv n stage [] EnvT.bot
      (.sort (.succ (.succ .zero))) cexPolyIdTy [covSSubstitutionDeep] := by
    constructor
    · exact ⟨covSSubstitution_argument_hasTy emptyEnv n []⟩
    · intro u hu
      rcases List.mem_singleton.mp hu with rfl
      exact approxTKStage_at_budget
        (covSSubstitution_deep_observed emptyEnv n [] EnvT.bot)
  have hb : ApproxTKStage emptyEnv n stage covSSubstitutionCtx covSSubstitutionEnv
      (.bvar 0) covSSubstitutionDeep :=
    approxTKStage_at_budget (covSSubstitution_body_observed emptyEnv n)
  have hr := covT_admissible_subst0_of_kFree
    (a := cexPolyIdTy) (B := .bvar 0)
    (covT_substitution_argument_kFree emptyEnv) ha hb
  exact ⟨covSSubstitution_native_data n, stage, ha, hb,
    approxTKStage_at_budget (covT_substitution_beta_observed emptyEnv n [] EnvT.bot),
    hr, CptT.noConfusion⟩

/-- The fixed native argument Prop cannot observe the Sort compact,
at any information stage. This does not quantify over arbitrary terms
whose native type is Prop. -/
theorem covT_prop_not_admissible_sort (E : ResolvedEnv) (arity stage : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ¬ CovTAdmissible E arity stage Γ ρ
      (.sort (.succ .zero)) (.sort .zero) [.sort] := by
  intro h
  have ho := (h.observed .sort (List.mem_singleton_self _)).1
  rcases approxTK_sort_inv ho with hbot | hcode
  · exact CptT.noConfusion hbot
  · rw [sortCode_zero] at hcode
    exact CptT.noConfusion hcode

/-- Prop is an actual native argument at Sort 1 and admits its actual
`.prop` observation at stage one. -/
theorem covT_prop_admissible_prop (E : ResolvedEnv) (arity : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    CovTAdmissible E arity 1 Γ ρ
      (.sort (.succ .zero)) (.sort .zero) [.prop] := by
  constructor
  · exact ⟨.sort Γ .zero⟩
  · intro u hu
    rcases List.mem_singleton.mp hu with rfl
    refine ⟨?_, by simp [covTObservationBudget]⟩
    simpa only [sortCode_zero] using approxTK_sort_code E arity Γ ρ .zero

/-- The negative demand test has inhabited environment, context, native
typing, finite-joint valuation, coherence, and a nonbottom observation.
Only the false Sort demand is rejected. -/
theorem covT_prop_demand_control (arity : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv arity []) ∧
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv arity []) [] EnvT.bot ∧
    CtxEnvM (ctxModelT_approxTK emptyEnv arity []) [] EnvT.bot ∧
    Nonempty (HasTyT emptyEnv arity [] (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTKStage emptyEnv arity 1 [] EnvT.bot (.sort .zero) .prop ∧
    CovTAdmissible emptyEnv arity 1 [] EnvT.bot
      (.sort (.succ .zero)) (.sort .zero) [.prop] ∧
    (¬ CovTAdmissible emptyEnv arity 1 [] EnvT.bot
      (.sort (.succ .zero)) (.sort .zero) [.sort]) ∧
    CptT.prop ≠ .bot := by
  have ha := covT_prop_admissible_prop emptyEnv arity [] EnvT.bot
  refine ⟨⟨.empty⟩, ⟨.nil⟩, envTypedFinAtT_nil _ EnvT.bot, ?_,
    ha.typing, ha.observed .prop (List.mem_singleton_self _), ha,
    covT_prop_not_admissible_sort emptyEnv arity 1 [] EnvT.bot,
    CptT.noConfusion⟩
  intro i v hv
  simp [lookupValue] at hv

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_SUBSTITUTION_ROOTS
#print axioms covT_approxTK_subst0_of_kFree
#print axioms covT_approxTK_subst0_of_no_indexed
#print axioms covT_approxTK_subst0_nat
#print axioms covT_approxTKStage_subst0_of_kFree
#print axioms covT_admissible_subst0_of_kFree
#print axioms covT_substitution_argument_kFree
#print axioms covT_substitution_deep_result
#print axioms covTSubstitutionBeta
#print axioms covTSubstitutionBetaTable
#print axioms covT_substitution_beta_hasTy
#print axioms covT_substitution_beta_conv
#print axioms covT_substitution_beta_read
#print axioms covT_substitution_beta_function_observed
#print axioms covT_substitution_beta_observed
#print axioms covT_substitution_native_control
#print axioms covT_substitution_staged_control
#print axioms covT_prop_not_admissible_sort
#print axioms covT_prop_admissible_prop
#print axioms covT_prop_demand_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_SUBSTITUTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
