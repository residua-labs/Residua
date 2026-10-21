import rcic.RcicNativeTypedModelCovSProofControls
import rcic.RcicNativeTypedModelCovRArrow

/-!
# An actual nonbottom proof demand in an unchanged neutral arrow

The old bottom-demand application consumer cannot be reused on the demand
below. We supply a different, explicit candidate consumer and inhabit it:
`p : True`, `f : True → Prop`, native proof irrelevance, a nonbottom observed
proof demand, and the observed neutral result `f p` are all present. The
ordinary R arrow and its output predicate are unchanged. Only the positive
argument relation is total. This is one supplied application, not a generic
native application theorem. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovPAudit TypedModelCovRAudit

def covSProofFnTy : Expr Nat := .pi (.const 0 []) (.sort .zero)

def covSProofFnMember : CheckedMember := ⟨.axiomM, 0, covSProofFnTy, none⟩

def covSProofFnEnv : ResolvedEnv := extendEnv covPProofEnv 4 covSProofFnMember

def covSProofFnEnvWfT : EnvWfT covSProofFnEnv :=
  .axiom covPProofEnv 4 covSProofFnTy (.imax .zero (.succ .zero))
    covPProofEnvWfT rfl
    (.pi [] (.const 0 []) .zero (.sort .zero) (.succ .zero)
      (trueConstTyT rfl) (.sort _ .zero))
    (fun _ => rfl) rfl

theorem covSProofFn_neutral : NeutralHeadP covSProofFnEnv 4 :=
  ⟨covSProofFnMember, rfl, rfl, Or.inl rfl⟩

theorem covSProofFn_argument_neutral : NeutralHeadP covSProofFnEnv 3 :=
  ⟨covPProofMember, rfl, rfl, Or.inl rfl⟩

theorem covSProofFn_true_positive : IsPropCTP covSProofFnEnv (.spine 0 []) :=
  .spine (m := trueFamMember) rfl rfl

def covSProofFn_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covSProofFnEnv n Γ (.const 4 []) covSProofFnTy := by
  simpa [covSProofFnMember, covSProofFnTy, instantiateLevels_nil] using
    (HasTyT.const (E := covSProofFnEnv) (n := n) Γ 4 []
      covSProofFnMember rfl rfl rfl)

def covSProofFn_argument_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covSProofFnEnv n Γ (.const 3 []) (.const 0 []) :=
  .const Γ 3 [] covPProofMember rfl rfl rfl

def covSProofFn_intro_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covSProofFnEnv n Γ (.const 1 []) (.const 0 []) :=
  .const Γ 1 [] trueIntroMember rfl rfl rfl

/-- A neutral's actual nonbottom observation uses the unchanged model. -/
theorem covS_neutral_observed {E : ResolvedEnv} {r : Nat}
    (hh : NeutralHeadP E r) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ (.const r []) (.spine r []) := by
  have hn : ¬ PropCtorT E r := by
    rintro ⟨m, fam, fm, hm, hctor, _⟩
    exact neutralHeadP_not_constructor hh hm hctor
  exact .free (kFreeT_rigid_const (neutralHeadP_rigid hh) [])
    (.const ρ r [] (neutralHeadP_rigid hh) hn)

theorem covSProofFn_application_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) :=
  .appSpine (covS_neutral_observed covSProofFn_neutral n Γ ρ)
    (covS_neutral_observed covSProofFn_argument_neutral n Γ ρ)

theorem covSProofFn_action :
    CovXCompactAction covSProofFnEnv (.spine 4 []) [.spine 3 []]
      (.spine 4 [.spine 3 []]) :=
  AppCptT.appSpine (.bvar (List.mem_singleton_self _))

theorem covSProofFn_demand_not_bottom : ¬ BotDemandT [.spine 3 []] := by
  intro h
  exact CptT.noConfusion (h _ (List.mem_singleton_self _))

/-- The replacement consumer accepts every actual demand through totality
of a positive S candidate. The arrow/result relation is literally the R
operator; no bottom-demand conclusion or old core result is assumed. -/
theorem covS_positive_argument_action {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {positive : Bool} {Dty x y N N' : Expr Nat} {D B : CovSRel}
    {c out : CptT} {ds : List CptT}
    (hD : CandidateCovS E (WhStepCK2 E n) Γ true D)
    (h : covRArrow E n Γ positive Dty D B x y c)
    (ha : CovXCompactAction E c ds out)
    (hN : HasTyT E n Γ N Dty) (hN' : HasTyT E n Γ N' Dty)
    (hconv : Nonempty (ConvT E n Γ N N' Dty)) :
    B (.app x N) (.app y N') out :=
  covRArrow_apply h ha N N' hN hN' hconv
    (fun u _ => hD.positive_total rfl N N' u)

def covSProofFnArrow (n : Nat) (Γ : LCtx) : CovSRel :=
  covRArrow covSProofFnEnv n Γ false (.const 0 []) covSTotalRel
    (covRCodeRel covSProofFnEnv .prop)

theorem covSProofFnArrow_isCandidate (n : Nat) (Γ : LCtx) :
    CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) Γ false
      (covSProofFnArrow n Γ) :=
  candidateCovS_of_R_false (covRArrow_isCandidate
    (candidateCovR_of_S_false (covSTotal_isCandidate covSProofFnEnv _ Γ false))
    (covRProp_isCandidate covSProofFnEnv _ Γ))

theorem covSProofFnArrow_member (n : Nat) (Γ : LCtx) :
    covSProofFnArrow n Γ (.const 4 []) (.const 4 []) (.spine 4 []) :=
  covRArrow_neutral (covRProp_isCandidate covSProofFnEnv _ Γ)
    (.const 4 []) (.const 4 []) 4 [] covSProofFn_neutral

/-- All native, model, positive-candidate, arrow, and application premises
are inhabited. The demand is nonempty and nonbottom, and the output remains
a nonbottom neutral at the unchanged false-tag Prop-universe leaf. -/
theorem covSProofFn_nonbottom_demand_control (n : Nat) :
    Nonempty (EnvWfT covSProofFnEnv) ∧ Nonempty (CtxWfT covSProofFnEnv n []) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 4 []) covSProofFnTy) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.sort .zero)) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 1 []))
      (.sort .zero)) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero)) ∧
    IsPropCTP covSProofFnEnv (.spine 0 []) ∧
    ApproxTK covSProofFnEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTK covSProofFnEnv n [] EnvT.bot (.const 4 []) (.spine 4 []) ∧
    ApproxTK covSProofFnEnv n [] EnvT.bot (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) ∧
    CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) [] true covSTotalRel ∧
    covSTotalRel (.const 3 []) (.const 1 []) (.spine 3 []) ∧
    CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) [] false
      (covSProofFnArrow n []) ∧
    covSProofFnArrow n [] (.const 4 []) (.const 4 []) (.spine 4 []) ∧
    CovXCompactAction covSProofFnEnv (.spine 4 []) [.spine 3 []]
      (.spine 4 [.spine 3 []]) ∧
    covRCodeRel covSProofFnEnv .prop (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.spine 4 [.spine 3 []]) ∧
    (.spine 3 [] : CptT) ≠ .bot ∧ (.spine 4 [.spine 3 []] : CptT) ≠ .bot ∧
    ¬ BotDemandT [.spine 3 []] := by
  have hp := covSProofFn_argument_hasTy n []
  have hq := covSProofFn_intro_hasTy n []
  have hf := covSProofFn_hasTy n []
  have hi : ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 []) :=
    .irr [] (.const 0 []) (.const 3 []) (.const 1 []) (trueConstTyT rfl) hp hq
  have hfp : HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.sort .zero) := .app [] _ _ (.const 0 []) (.sort .zero) hf hp
  have hfq : HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 1 []))
      (.sort .zero) := .app [] _ _ (.const 0 []) (.sort .zero) hf hq
  have hfc : ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero) :=
    .app [] _ _ _ _ (.const 0 []) (.sort .zero) (.refl _ _ _ hf) hi
  have hD := covSTotal_isCandidate covSProofFnEnv (WhStepCK2 covSProofFnEnv n) [] true
  have hArrow := covSProofFnArrow_member n []
  have hout := covS_positive_argument_action hD hArrow covSProofFn_action hp hq ⟨hi⟩
  exact ⟨⟨covSProofFnEnvWfT⟩, ⟨.nil⟩, ⟨trueConstTyT rfl⟩, ⟨hf⟩, ⟨hp⟩, ⟨hq⟩,
    ⟨hi⟩, ⟨hfp⟩, ⟨hfq⟩, ⟨hfc⟩, covSProofFn_true_positive,
    covS_neutral_observed covSProofFn_argument_neutral n [] EnvT.bot,
    covS_neutral_observed covSProofFn_neutral n [] EnvT.bot,
    covSProofFn_application_observed n [] EnvT.bot, hD, trivial,
    covSProofFnArrow_isCandidate n [], hArrow, covSProofFn_action, hout,
    CptT.noConfusion, CptT.noConfusion, covSProofFn_demand_not_bottom⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_PROOF_ACTION_ROOTS
#print axioms covSProofFnTy
#print axioms covSProofFnMember
#print axioms covSProofFnEnv
#print axioms covSProofFnEnvWfT
#print axioms covSProofFn_neutral
#print axioms covSProofFn_argument_neutral
#print axioms covSProofFn_true_positive
#print axioms covSProofFn_hasTy
#print axioms covSProofFn_argument_hasTy
#print axioms covSProofFn_intro_hasTy
#print axioms covS_neutral_observed
#print axioms covSProofFn_application_observed
#print axioms covSProofFn_action
#print axioms covSProofFn_demand_not_bottom
#print axioms covS_positive_argument_action
#print axioms covSProofFnArrow
#print axioms covSProofFnArrow_isCandidate
#print axioms covSProofFnArrow_member
#print axioms covSProofFn_nonbottom_demand_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_PROOF_ACTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
