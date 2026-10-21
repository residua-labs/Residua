import rcic.RcicNativeTypedModelCovNormSubst
import rcic.RcicNativeTypedModelCovRelWitness

/-!
# A concrete declared-constant supplier

The exact input separates constant observations, readback normality, and
the native member class.  All rigid constructors satisfy it in the actual
saturated model.  It is not asserted for transparent definitions or for
recursor compacts, whose declaration semantics remain separate obligations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelKAudit
open TypedModelCovRelAudit TypedModelCovNormSubstAudit
open TypedModelKFragmentAudit ReadbackCKAudit ReadbackCK2Audit
open TypedModelKTypedBetaAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- An exact observation/readback input for the rigid-spine part of the
constant row.  No logical-relation conclusion is a field. -/
structure CovConstSpineInput (M : CtxModelT E) (R : Readback)
    (r : Nat) (ls : List Level) (m : CheckedMember) : Prop where
  observation : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.const r ls) c →
    c = .bot ∨ c = .spine r []
  normal : ∀ Δ : LCtx, NormalR R Δ (.const r ls)
  nonFamily : m.mclass ≠ .inductiveM

/-- The imported spine clause closes directly from these three concrete
inputs.  Every source valuation and substitution remains quantified. -/
theorem fundCov_const_of_spineInput {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : E.members r = some m)
    (hInput : CovConstSpineInput M R r ls m) :
    FundTyAtCov C M R n Γ (.const r ls) (instantiateLevels ls m.mtype) := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  rcases hc.elim hInput.observation hInput.observation with rfl | rfl
  · exact lrSCoreCov_bot C _ _ _ _
  · rw [lrSCoreCov_spine_iff]
    refine ⟨m, ls, ls, [], [], hres, .refl _, .refl _,
      hInput.normal Δ, hInput.normal Δ, eqNList_refl ls,
      by decide, by decide, .nil _, ?_⟩
    intro _ hFamily
    exact (hInput.nonFamily hFamily).elim

theorem fundCov_const_step_of_spineInput {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hInput : CovConstSpineInput M R r ls m) :
    FundTyCovStep C M R n (HasTyT.const Γ r ls m hres hlen hwf) := by
  intro _ _ Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_const_of_spineInput hres hInput hΔ hSub c hc

/-- Actual constructor admission supplies all fields; the observation
inversion retains the saturated model's `free` arm through forgetting. -/
theorem covConstSpineInput_ctor (hW : EnvWfT E) {Ξ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hCtor : m.mclass = .constructorM)
    (hRigid : RigidConst E r) :
    CovConstSpineInput (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) r ls m := by
  refine ⟨fun h => approxT_rigid_const_inv hRigid (approxTK_forget h),
    fun Δ => normalR_ctorSpineCK2 hW hres hCtor Δ ls [], ?_⟩
  intro hFamily
  exact MemberClass.noConfusion (hCtor.symm.trans hFamily)

/-- The complete exact input and native constant motive are inhabited in
the real Nat model at a non-bottom constructor compact. -/
theorem covConst_native_control (C : CovTyping natEnvU) (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovConstSpineInput (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n)
      1 [] natZeroMember ∧
    Nonempty (HasTyT natEnvU n [] (.const 1 []) (.const 0 [])) ∧
    RelSubstAtCov C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n
      [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    LRSCoreCov C (WhStepCK2 natEnvU n) n [] (.const 1 []) (.const 1 [])
      (.const 0 []) (.spine 1 []) ∧ (.spine 1 [] : CptT) ≠ .bot := by
  have hInput := covConstSpineInput_ctor (n := n) (Ξ := []) natEnvUWfT
    (ls := []) (rfl : natEnvU.members 1 = some natZeroMember) rfl rigidConst_natEnvU_zero
  have hSub := relSubstAtCov_nil C (ctxModelT_approxTK natEnvU n [])
    (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hObs : ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) :=
    .free (kFreeT_natEnvU _) (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero)
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, hInput, ⟨hasTyT_natEnvU_zero n []⟩,
    hSub, hObs, ?_, fun h => CptT.noConfusion h⟩
  simpa only [substT_id] using
    fundCov_const_of_spineInput (C := C)
      (rfl : natEnvU.members 1 = some natZeroMember) hInput .nil hSub (.spine 1 []) (Or.inl hObs)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_CONST_CASES_ROOTS
#print axioms CovConstSpineInput
#print axioms fundCov_const_of_spineInput
#print axioms fundCov_const_step_of_spineInput
#print axioms covConstSpineInput_ctor
#print axioms covConst_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_CONST_CASES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit
