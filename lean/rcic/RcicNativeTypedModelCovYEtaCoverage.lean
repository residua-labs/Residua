import rcic.RcicNativeTypedModelCovYCore
import rcic.RcicNativeTypedModelCovYEtaCode
import rcic.RcicNativeTypedModelCovXEtaFactor

/-!
# Measured successor row coverage

The ordinary `[Nat] -> Nat` type-code observation is real and types the
successor compact, but it does not cover successor's action on the typed
bottom demand. Thus the new coverage conjunct cannot be inferred from C2.
The actual empty-demand Nat row supplies coverage for every compact observed
at either eta endpoint, including left-only lambda tables. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovNormAppAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit

/-- For lambda compacts the existing covariant typing rows already cover
every application action. The distinct rigid-spine branch is deliberately
outside this theorem, as the actual counterexample below demonstrates. -/
theorem covYActionCoverage_lam_of_typing {E : ResolvedEnv} (C : CovTyping E)
    {f g : List (List CptT × CptT)} {d : CptT}
    (ht : C.ty (.lam f) (.pi d g)) : CovYActionCoverage C (.lam f) d g := by
  rcases C.pi_inv ht with hb | ⟨f', he, _, hrows⟩ | ⟨r, args, he⟩
  · exact CptT.noConfusion hb
  · cases he
    intro ds out ha hd
    cases ha with
    | bot => exact Or.inl rfl
    | @app f' s arg hs hu =>
        rcases hrows s hs with hb | ⟨row, hr, hsub, hout⟩
        · exact Or.inl hb
        · refine Or.inr ⟨row, hr, ?_, hout⟩
          intro u humem
          exact approxT_bvar_inv (hu u (hsub u humem))
  · exact CptT.noConfusion he

/-- An actual successor action whose argument is a typed bottom demand. -/
theorem covY_natSucc_bot_action :
    CovXCompactAction natEnvU (.spine 2 []) [.bot] (.spine 2 [.bot]) :=
  AppCptT.appSpine (.bot _ _)

/-- The standard observed type code has no compatible row for this actual
non-bottom output. The demand list satisfies the new domain typing gate. -/
theorem not_covYActionCoverage_natNatCovCode :
    ¬ CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 [])
      [([.spine 0 []], .spine 0 [])] := by
  intro h
  have hd : ∀ u ∈ ([.bot] : List CptT), (C2 natEnvU).ty u (.spine 0 []) := by
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact (C2 natEnvU).bot _
  rcases h [.bot] (.spine 2 [.bot]) covY_natSucc_bot_action hd with hb |
    ⟨row, hrow, hsel⟩
  · exact CptT.noConfusion hb
  · obtain rfl := List.mem_singleton.mp hrow
    rcases hsel.1 (.spine 0 []) (List.mem_singleton.mpr rfl) with hb | hm
    · exact CptT.noConfusion hb
    · exact CptT.noConfusion (List.mem_singleton.mp hm)

/-- No endpoints can supply a successor relation at that uncovered code.
This is a code-specific obstruction, not a refutation of a different code. -/
theorem not_lrSCoreCovY_natSucc_standard_code (n : Nat) (Γ : LCtx)
    (x y A : Expr Nat) :
    ¬ LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ x y A
      (.spine 2 []) natNatCovCode := by
  intro h
  exact not_covYActionCoverage_natNatCovCode
    (lrSCoreCovY_pi_coverage (C2 natEnvU) h)

/-- The coverage obstruction keeps actual native endpoints, a typed actual
argument, a real type observation, and the rigid C2 typing gate inhabited. -/
theorem covY_natSucc_standard_code_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 1 []) (.const 0 [])) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) natNatCovCode ∧
    (C2 natEnvU).ty (.spine 2 []) natNatCovCode ∧
    (C2 natEnvU).ty .bot (.spine 0 []) ∧
    CovXCompactAction natEnvU (.spine 2 []) [.bot] (.spine 2 [.bot]) ∧
    ¬ CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 [])
      [([.spine 0 []], .spine 0 [])] := by
  obtain ⟨hW, hΓ, _, hsucc, _, _, hobs, _, hzobs, _⟩ := covX_natSucc_eta_control n
  exact ⟨hW, hΓ, hsucc, ⟨hasTyT_natEnvU_zero n []⟩, hobs, hzobs,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natNat_covCode EnvT.bot),
    ctyCov2_natSucc_spine (approxT_natNat_covCode EnvT.bot)
      not_isPropCT_natNatCovCode,
    (C2 natEnvU).bot _, covY_natSucc_bot_action,
    not_covYActionCoverage_natNatCovCode⟩

/-- Every successor action is covered by the uniform empty-demand Nat row.
The proof even holds without restricting the incoming demand list. -/
theorem covY_natSucc_uniform_coverage :
    CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 [])
      [([], .spine 0 [])] := by
  intro ds out hact hd
  cases hact with
  | bot => exact Or.inl rfl
  | @appSpine r args arg u hu =>
      refine Or.inr ⟨([], .spine 0 []), List.mem_singleton.mpr rfl, ?_, ?_⟩
      · intro v hv
        exact (List.not_mem_nil _ hv).elim
      · change CTyCov2 natEnvU (.spine 2 [u]) (.spine 0 [])
        rw [CTyCov2]
        exact Or.inr ⟨⟨2, [u], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- Imported model action factorization transports uniform coverage to all
eta-left compact tables. No relation or Fundamental premise is assumed. -/
theorem covY_natSucc_eta_uniform_coverage {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    CovYActionCoverage (C2 natEnvU) c (.spine 0 []) [([], .spine 0 [])] := by
  intro ds out ha hd
  exact covY_natSucc_uniform_coverage ds out
    (covX_natSucc_eta_action_covers h ds out ha) hd

/-- The same actual type code covers every endpoint-OR observation. -/
theorem covY_natSucc_eta_or_uniform_coverage (n : Nat) (Γ : LCtx) (ρ ρ' : EnvT)
    (c : CptT)
    (h : ApproxTK natEnvU n Γ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Γ ρ' (.const 2 []) c) :
    CovYActionCoverage (C2 natEnvU) c (.spine 0 []) [([], .spine 0 [])] := by
  rcases h with h | h
  · exact covY_natSucc_eta_uniform_coverage h
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ
        (approxTK_forget h) with rfl | rfl
    · intro ds out ha hd
      cases ha with
      | bot => exact Or.inl rfl
    · exact covY_natSucc_uniform_coverage

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_COVERAGE_ROOTS
#print axioms covYActionCoverage_lam_of_typing
#print axioms covY_natSucc_bot_action
#print axioms not_covYActionCoverage_natNatCovCode
#print axioms not_lrSCoreCovY_natSucc_standard_code
#print axioms covY_natSucc_standard_code_control
#print axioms covY_natSucc_uniform_coverage
#print axioms covY_natSucc_eta_uniform_coverage
#print axioms covY_natSucc_eta_or_uniform_coverage
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_COVERAGE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit
