import rcic.RcicNativeTypedModelCovSInterpret
import rcic.RcicNativeTypedModelCovSSubstitutionData

/-!
# An actually observed boundary for the origin-erased decoder

The term, argument type, variable body, and substituted type below all have
their displayed native typings and actual ApproxTK observations. The target
type observation `pi sort []` and the deep source/argument observations are
nonbottom. Their interpretations disagree at the same actual nonbottom
observation of the native polymorphic identity.

The failure uses no selection of an outer observed row. The sort-domain
operator tests an actual compact action at actual native Prop and an actual
candidate. Its origin-erased output constraint decodes the observed inner
domain as a function candidate. The ordinary strict arrow then requires
the identity's stored `.prop` demand to have that functional shape, which
is impossible.

This refutes the independently observed substitution test for the particular
raw decoder and interpretation defined in Template/Interpret. It does not
refute a bridge equipped with coupled observations, a supplied native-origin
certificate, or a different origin-enriched template. It is not a universal
impossibility of row synthesis or impredicative candidates.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovXAudit TypedModelCovRAudit

theorem covSSubstitution_domain_template :
    templateOfObs polyIdDom1 = .allSort [([.prop], .sort)] := by
  rw [polyIdDom1, templateOfObs]
  change CovSObsSyntax.allSort [([.prop], templateOfObs .sort)] = _
  rw [templateOfObs_sort]

theorem covSSubstitution_codomain_template :
    templateOfObs polyIdTyCod1 =
      .ordinary (templateOfObs polyIdDom1)
        [([polyIdWitness1], templateOfObs polyIdDom1)] := by
  rw [polyIdTyCod1, templateOfObs]
  · rfl
  all_goals simp [polyIdDom1]

theorem covSSubstitution_deep_template :
    templateOfObs covSSubstitutionDeep =
      .allSort [([polyIdDom1], templateOfObs polyIdTyCod1)] := by
  rw [covSSubstitutionDeep, templateOfObs]
  rfl

/-- Project a particular finite output constraint. No action-dependent
row choice, compact ordering, or choice principle is involved. -/
theorem covSSubstitution_rows_elim {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {rows : List (List CptT × CovSObsSyntax)}
    {F : ∀ row, row ∈ rows → CovSDataCandidate E n Γ}
    {x y : Expr Nat} {c : CptT}
    (h : (covSBuildRows rows F).relation x y c)
    (row : List CptT × CovSObsSyntax) (hrow : row ∈ rows) :
    (F row hrow).relation x y c := by
  exact h ⟨(row.1, F row hrow),
    List.mem_map.mpr ⟨⟨row, hrow⟩, by simp, rfl⟩⟩

theorem covSSubstitution_allSort_rejects_prop (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (v : Nat → CovSDataCandidate E n Γ)
    (rows : List (List CptT × CovSObsSyntax)) (x y : Expr Nat) :
    ¬ (interpretObsTemplate E n Γ v (.allSort rows)).relation x y .prop := by
  intro h
  rw [interpretObsTemplate] at h
  have hs := covSForall_shape (h ⟨.succ .zero, rfl⟩)
  rcases hs with he | ⟨f, he⟩ | ⟨r, us, he⟩
  · exact CptT.noConfusion he
  · exact CptT.noConfusion he
  · exact CptT.noConfusion he

/-- The supplied candidate may be total; the failure is the erased body's
strict stored-domain support obligation, not positive proof collapse. -/
theorem covSSubstitution_deep_rejects_identity (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (v : Nat → CovSDataCandidate E n Γ) (x y : Expr Nat) :
    ¬ covSObsInterp E n Γ v covSSubstitutionDeep x y polyIdCpt0 := by
  intro h
  unfold covSObsInterp at h
  rw [covSSubstitution_deep_template, interpretObsTemplate] at h
  have hout := covSForall_apply (h ⟨.succ .zero, rfl⟩)
    (covRPolyIdCpt0_action E) (.sort .zero) (.sort Γ .zero)
    covSTotalRel (covSTotal_isCandidate E (WhStepCK2 E n) Γ false)
  have hinner := covSSubstitution_rows_elim hout
    ([polyIdDom1], templateOfObs polyIdTyCod1) (List.mem_singleton_self _)
  change (interpretObsTemplate E n Γ v (templateOfObs polyIdTyCod1)).relation
    (.app x (.sort .zero)) (.app y (.sort .zero)) polyIdOut0 at hinner
  rw [covSSubstitution_codomain_template, interpretObsTemplate] at hinner
  have hrows := covRArrow_rows (hinner (.sort .zero))
  obtain ⟨a, b, hab⟩ :=
    (hrows ([.prop], .prop) (List.mem_singleton_self _)).1
      .prop (List.mem_singleton_self _)
  change (interpretObsTemplate E n Γ v (templateOfObs polyIdDom1)).relation a b .prop at hab
  rw [covSSubstitution_domain_template] at hab
  exact covSSubstitution_allSort_rejects_prop E n Γ v _ a b hab

/-- The shallower, still nonbottom observation retains the Sort binder.
Its empty family of output constraints admits every function-shaped compact. -/
theorem covSSubstitution_sort_nil_accepts (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (v : Nat → CovSDataCandidate E n Γ)
    (x y : Expr Nat) (c : CptT) (hs : CovRFunctionShape c) :
    covSObsInterp E n Γ v (.pi .sort []) x y c := by
  unfold covSObsInterp
  rw [templateOfObs]
  change (interpretObsTemplate E n Γ v (.allSort [])).relation x y c
  rw [interpretObsTemplate]
  intro l
  apply covSForall_intro hs
  intro ds out ha T hT S hS row
  exact (List.not_mem_nil _ row.property).elim

/-- The semantic valuation performs the actual variable update with the
candidate computed from the argument observation. Raw decoded observations
contain no variable constructors, so this cannot restore their lost origin. -/
def covSSubstitutionVal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a : CptT) :
    Nat → CovSDataCandidate E n Γ
  | 0 => interpretObsTemplate E n Γ (covSBaseVal E n Γ) (templateOfObs a)
  | i + 1 => covSBaseVal E n Γ i

theorem covSSubstitution_observed_not_iff (n : Nat) :
    ¬ (covSObsInterp emptyEnv n [] (covSBaseVal emptyEnv n []) (.pi .sort [])
        cexPolyId cexPolyId polyIdCpt0 ↔
      covSObsInterp emptyEnv n []
        (covSSubstitutionVal emptyEnv n [] covSSubstitutionDeep) covSSubstitutionDeep
        cexPolyId cexPolyId polyIdCpt0) := by
  intro h
  exact covSSubstitution_deep_rejects_identity emptyEnv n [] _ _ _
    (h.mp (covSSubstitution_sort_nil_accepts emptyEnv n [] _ _ _ _
      (Or.inr (Or.inl ⟨[([.sort], polyIdOut0)], rfl⟩))))

theorem covSSubstitution_bot_not_iff (n : Nat) :
    ¬ (covSObsInterp emptyEnv n [] (covSBaseVal emptyEnv n []) .bot
        cexPolyId cexPolyId polyIdCpt0 ↔
      covSObsInterp emptyEnv n []
        (covSSubstitutionVal emptyEnv n [] covSSubstitutionDeep) covSSubstitutionDeep
        cexPolyId cexPolyId polyIdCpt0) := by
  intro h
  exact covSSubstitution_deep_rejects_identity emptyEnv n [] _ _ _
    (h.mp (covS_unknown_accepts_all emptyEnv n [] _ _ _ _))

/-- A restricted test of the proposed independent-observation substitution
principle at ONE fixed, inhabited native substitution. The extended model
valuation must still be finite-joint typed and let-coherent. -/
def CovSIndependentVariableSubstitution (n : Nat) : Prop :=
  ∀ aObs bObs resultObs c : CptT,
    let ρ := EnvT.cons (demandT [aObs]) EnvT.bot
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSSubstitutionCtx)
      covSSubstitutionCtx ρ →
    CtxEnvM (ctxModelT_approxTK emptyEnv n covSSubstitutionCtx)
      covSSubstitutionCtx ρ →
    ApproxTK emptyEnv n [] EnvT.bot cexPolyIdTy aObs →
    ApproxTK emptyEnv n covSSubstitutionCtx ρ (.bvar 0) bObs →
    ApproxTK emptyEnv n [] EnvT.bot (instantiate0 cexPolyIdTy (.bvar 0)) resultObs →
    ApproxTK emptyEnv n [] EnvT.bot cexPolyId c →
    (covSObsInterp emptyEnv n [] (covSBaseVal emptyEnv n []) resultObs
        cexPolyId cexPolyId c ↔
      covSObsInterp emptyEnv n [] (covSSubstitutionVal emptyEnv n [] aObs) bObs
        cexPolyId cexPolyId c)

theorem covSSubstitution_no_independent_bridge (n : Nat) :
    ¬ CovSIndependentVariableSubstitution n := by
  intro h
  have hd := covSSubstitution_native_data n
  exact covSSubstitution_observed_not_iff n
    (h covSSubstitutionDeep covSSubstitutionDeep (.pi .sort []) polyIdCpt0
      hd.extended_env_typed hd.extended_ctx_coherent hd.argument_observed
      hd.body_observed hd.result_sort_nil_observed hd.term_observed)

/-- All native, model, candidate and action premises are supplied. The
positive edge is a fresh S joint at the actual shallow observation; its
failure to agree with the deep interpretation is also exhibited. -/
theorem covSSubstitution_observed_control (n : Nat) :
    CovSSubstitutionNativeData n ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covSObsInterp emptyEnv n [] (covSBaseVal emptyEnv n []) (.pi .sort [])) ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covSObsInterp emptyEnv n []
        (covSSubstitutionVal emptyEnv n [] covSSubstitutionDeep) covSSubstitutionDeep) ∧
    Nonempty (HasTyT emptyEnv n [] (.sort .zero) (.sort (.succ .zero))) ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] false covSTotalRel ∧
    CovXCompactAction emptyEnv polyIdCpt0 [.sort] polyIdOut0 ∧
    CovSJoint emptyEnv n [] (covSBaseVal emptyEnv n []) false (.pi .sort [])
      cexPolyId cexPolyId polyIdCpt0 ∧
    ¬ covSObsInterp emptyEnv n []
      (covSSubstitutionVal emptyEnv n [] covSSubstitutionDeep) covSSubstitutionDeep
      cexPolyId cexPolyId polyIdCpt0 ∧
    ¬ CovSIndependentVariableSubstitution n := by
  have hs := covSSubstitution_sort_nil_accepts emptyEnv n []
    (covSBaseVal emptyEnv n []) cexPolyId cexPolyId polyIdCpt0
    (Or.inr (Or.inl ⟨[([.sort], polyIdOut0)], rfl⟩))
  exact ⟨covSSubstitution_native_data n,
    covSObsInterp_isCandidate emptyEnv n [] _ _,
    covSObsInterp_isCandidate emptyEnv n [] _ _,
    ⟨.sort [] .zero⟩, covSTotal_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [] false,
    covRPolyIdCpt0_action emptyEnv, covSJoint_of_related (p := false) hs,
    covSSubstitution_deep_rejects_identity emptyEnv n [] _ _ _,
    covSSubstitution_no_independent_bridge n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_SUBSTITUTION_BOUNDARY_ROOTS
#print axioms covSSubstitution_domain_template
#print axioms covSSubstitution_codomain_template
#print axioms covSSubstitution_deep_template
#print axioms covSSubstitution_rows_elim
#print axioms covSSubstitution_allSort_rejects_prop
#print axioms covSSubstitution_deep_rejects_identity
#print axioms covSSubstitution_sort_nil_accepts
#print axioms covSSubstitutionVal
#print axioms covSSubstitution_observed_not_iff
#print axioms covSSubstitution_bot_not_iff
#print axioms CovSIndependentVariableSubstitution
#print axioms covSSubstitution_no_independent_bridge
#print axioms covSSubstitution_observed_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_SUBSTITUTION_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
