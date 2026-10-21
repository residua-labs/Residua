import rcic.RcicNativeTypedModelCovXInterface
import rcic.RcicNativeTypedModelCovRelEscape

/-!
# Eager hereditary views and native type transport: exact boundaries

A finite view supplies weak-head normalization, but that is not its only
cost. Its codomain child at every natively typed argument is already too
strong for the closed impredicative proposition `idPiProp = Pi X:Prop, X`.
Applying that child to `idPiProp` itself asks for the same view again. The
inductive elimination below refutes this demand with an actual native type.

The resulting typed-lambda control has a real non-bottom model observation
and the empty coherent semantic context. It refutes global completeness of
this eager-view candidate, not the extensional application equation itself.

Readback transport is proved; native conversion transport is separately
named and has a nondegenerate Eq-alias control. The two are not identified.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- A finite view always contains an actual normal head readback. -/
theorem covXTypeView_has_normal_head (hL : ReadbackLaws E R)
    {Γ : LCtx} {A : Expr Nat} (v : CovXTypeView E R n Γ A) :
    ∃ Z, RedR R Γ A Z ∧ NormalR R Γ Z := by
  cases v with
  | sort l hr => exact ⟨.sort l, hr, hL.sort_normal Γ l⟩
  | base Z hr hn hs hp => exact ⟨Z, hr, hn⟩
  | pi D B hr dom body cod => exact ⟨.pi D B, hr, hL.pi_normal Γ D B⟩

/-- The unproved eager-view supply, with both native admission premises
retained. This file subsequently refutes it on the admitted Eq environment. -/
def CovXTypedViews (E : ResolvedEnv) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A : Expr Nat} {l : Level},
    CtxWfT E n Γ → HasTyT E n Γ A (.sort l) →
    Nonempty (CovXTypeView E R n Γ A)

theorem covXTypedViews_implies_type_normalization (hL : ReadbackLaws E R)
    (hV : CovXTypedViews E R n) {Γ : LCtx} {A : Expr Nat} {l : Level}
    (hΓ : CtxWfT E n Γ) (hA : HasTyT E n Γ A (.sort l)) :
    ∃ Z, RedR R Γ A Z ∧ NormalR R Γ Z := by
  obtain ⟨v⟩ := hV hΓ hA
  exact covXTypeView_has_normal_head hL v

/-- Every eager view of the impredicative proposition would contain itself
as a genuine codomain child. Structural induction rules that out. -/
theorem covXTypeView_impredicative_false (hL : ReadbackLaws E R)
    (hP : ∀ Γ, HasTyT E n Γ idPiProp (.sort .zero))
    {Γ : LCtx} {A : Expr Nat} (v : CovXTypeView E R n Γ A)
    (hA : A = idPiProp) : False := by
  induction v with
  | sort l hr =>
      rw [hA] at hr
      exact Expr.noConfusion
        (redR_of_normal (hL.pi_normal _ (.sort .zero) (.bvar 0)) hr)
  | base Z hr hn hs hp =>
      rw [hA] at hp
      exact hp ⟨.sort .zero, .bvar 0, .refl _⟩
  | pi D B hr dom body cod ihdom ihbody ihcod =>
      rw [hA] at hr
      have he := redR_of_normal (hL.pi_normal _ (.sort .zero) (.bvar 0)) hr
      change Expr.pi D B = .pi (.sort .zero) (.bvar 0) at he
      obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
      exact ihcod idPiProp (hP _) rfl

theorem not_covXTypeView_idPiProp_eq (n : Nat) (Γ : LCtx) :
    ¬ Nonempty (CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n Γ idPiProp) := by
  rintro ⟨v⟩
  exact covXTypeView_impredicative_false (readbackLaws_whStepCK2 eqEnvT n)
    (apartLeft_ty n) v rfl

/-- The failure is at an already normal, natively typed, closed proposition. -/
theorem not_covXTypedViews_eqEnv (n : Nat) :
    ¬ CovXTypedViews eqEnvT (WhStepCK2 eqEnvT n) n := by
  intro hv
  exact not_covXTypeView_idPiProp_eq n [] (hv .nil (apartLeft_ty n []))

theorem not_covXTypeView_pi_idPiProp (n : Nat) (Γ : LCtx) (B : Expr Nat) :
    ¬ Nonempty (CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n Γ (.pi idPiProp B)) := by
  rintro ⟨v⟩
  cases v with
  | sort l hr =>
      exact Expr.noConfusion (redR_of_normal (normalR_piCK2 Γ idPiProp B) hr)
  | base Z hr hn hs hp => exact hp ⟨idPiProp, B, .refl _⟩
  | pi D B' hr dom body cod =>
      have he := redR_of_normal (normalR_piCK2 Γ idPiProp B) hr
      obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
      exact not_covXTypeView_idPiProp_eq n Γ ⟨dom⟩

/-- A concrete native lambda with no requirement for an inhabitant of its
empty proposition domain. Its body is the inhabited type expression Prop. -/
def covXPolyPropLam : Expr Nat := .lam idPiProp (.sort .zero)

def covXPolyPropLamTy : Expr Nat := .pi idPiProp (.sort (.succ .zero))

def covXPolyPropLam_typed (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ covXPolyPropLam covXPolyPropLamTy :=
  .lam Γ idPiProp .zero (.sort .zero) (.sort (.succ .zero))
    (apartLeft_ty n Γ) (.sort _ _)

/-- The row is nonempty with an actual non-bottom output; this is not the
unavailable empty lambda compact. The argument demand itself is empty. -/
theorem covXPolyPropLam_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ covXPolyPropLam (.lam [([], .prop)]) := by
  refine .lam (a := .bot) (.bot _ _ _) ?_ ?_ ?_
  · intro s hs u hu
    simp only [List.mem_singleton] at hs
    subst s
    exact (List.not_mem_nil _ hu).elim
  · exact ⟨([], .prop), List.mem_singleton_self _, fun h => CptT.noConfusion h⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    simpa only [sortCode_zero] using approxTK_sort_code eqEnvT n
      (.assumption idPiProp :: Γ) (EnvT.cons (demandT []) ρ) .zero

theorem not_lrSCoreCovX_polyPropLam (C : CovTyping eqEnvT) (n : Nat) (Γ : LCtx) :
    ¬ LRSCoreCovX C (WhStepCK2 eqEnvT n) n Γ covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy (.lam [([], .prop)]) := by
  rintro (hb | ⟨v, hv⟩)
  · exact CptT.noConfusion hb
  · exact not_covXTypeView_pi_idPiProp n Γ (.sort (.succ .zero)) ⟨v⟩

/-- Admission, native typing, both coherent semantic environments, and the
actual non-bottom source observation all coexist with the relation failure. -/
theorem covX_eager_view_typed_counterexample (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    Nonempty (HasTyT eqEnvT n [] covXPolyPropLam covXPolyPropLamTy) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    ApproxTK eqEnvT n [] EnvT.bot covXPolyPropLam (.lam [([], .prop)]) ∧
    (.lam [([], .prop)] : CptT) ≠ .bot ∧
    ¬ LRSCoreCovX C (WhStepCK2 eqEnvT n) n [] covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy (.lam [([], .prop)]) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩, ⟨covXPolyPropLam_typed n []⟩,
    envTypedCovAtP_nil C _ EnvT.bot, envTypedCovAtP_nil C _ EnvT.bot,
    covXPolyPropLam_observed n [] EnvT.bot, fun h => CptT.noConfusion h,
    not_lrSCoreCovX_polyPropLam C n []⟩

/-- The complete typing motive is false at the concrete lambda, with the
empty related substitution supplied by the unchanged native/environment laws. -/
theorem not_fundTyAtCovX_polyPropLam (C : CovTyping eqEnvT) (n : Nat) :
    ¬ FundTyAtCovX C (ctxModelT_approxTK eqEnvT n []) (WhStepCK2 eqEnvT n) n []
      covXPolyPropLam covXPolyPropLamTy := by
  intro h
  have hs := relSubstAtCovX_nil C (ctxModelT_approxTK eqEnvT n [])
    (WhStepCK2 eqEnvT n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hr := h (.nil : CtxWfT eqEnvT n []) hs (.lam [([], .prop)])
    (Or.inl (covXPolyPropLam_observed n [] EnvT.bot))
  exact not_lrSCoreCovX_polyPropLam C n []
    (by simpa only [SubstT.id, substT_id] using hr)

theorem not_fundamentalCovXAt_eqEnv (C : CovTyping eqEnvT) (n : Nat) :
    ¬ FundamentalCovXAt C (ctxModelT_approxTK eqEnvT n []) (WhStepCK2 eqEnvT n) n := by
  intro h
  exact not_fundTyAtCovX_polyPropLam C n (h.1 .nil (covXPolyPropLam_typed n []))

/-- Compact Pi typing is not the failing input at this lambda. -/
theorem covXPolyPropLam_piGate (C : CovTyping eqEnvT) (hS : CovTypingIncludesS C) :
    CovXPiGate C (.lam [([], .prop)]) := by
  refine ⟨.bot, [([], .sort)], hS _ _ ?_⟩
  exact ctyS_lam_singleton (fun h => by cases h)
    (fun _ h => (List.not_mem_nil _ h).elim) (ctyS_prop_sort eqEnvT)

/-- Every actual compact application action of the same lambda is valid at
its codomain. This positive one-layer control does not ask for a view of P;
it isolates the eager domain view as the excess requirement. -/
theorem covXPolyPropLam_one_layer_action (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx)
    (ds : List CptT) (out : CptT)
    (ha : CovXCompactAction eqEnvT (.lam [([], .prop)]) ds out)
    (N N' : Expr Nat) :
    LRSCoreCovX C (WhStepCK2 eqEnvT n) n Γ
      (.app covXPolyPropLam N) (.app covXPolyPropLam N') (.sort (.succ .zero)) out := by
  cases ha with
  | bot => exact lrSCoreCovX_bot C _ _ _ _
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      refine lrSCoreCovX_of_view C (.sort (.succ .zero) (.refl _)) ⟨?_, ?_⟩
      · simpa only [TypingFin.sortCode_succ] using hS .sort .prop (ctyS_prop_sort eqEnvT)
      · apply (lrSCoreCov_prop_iff C _ _ _ _).mpr
        refine ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, ?_, ?_⟩
        · exact .step ((readbackLaws_whStepCK2 eqEnvT n).beta Γ
            idPiProp (.sort .zero) N) (.refl _)
        · exact .step ((readbackLaws_whStepCK2 eqEnvT n).beta Γ
            idPiProp (.sort .zero) N') (.refl _)

/-- All premises of the one-layer action coexist at the actual variable
`p : P`. The compact demand is empty, so this successful action requires no
domain realization, while the eager candidate still requests the false view. -/
theorem covXPolyPropLam_typed_action_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧
    Nonempty (CtxWfT eqEnvT n [.assumption idPiProp]) ∧
    Nonempty (HasTyT eqEnvT n [.assumption idPiProp] (.bvar 0) idPiProp) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n [.assumption idPiProp])
      [.assumption idPiProp] EnvT.bot ∧
    CovXPiGate C (.lam [([], .prop)]) ∧
    CovXCompactAction eqEnvT (.lam [([], .prop)]) [] .prop ∧
    Nonempty (HasTyT eqEnvT n [.assumption idPiProp]
      (.app covXPolyPropLam (.bvar 0)) (.sort (.succ .zero))) ∧
    ApproxTK eqEnvT n [.assumption idPiProp] EnvT.bot
      (.app covXPolyPropLam (.bvar 0)) .prop ∧
    LRSCoreCovX C (WhStepCK2 eqEnvT n) n [.assumption idPiProp]
      (.app covXPolyPropLam (.bvar 0)) (.app covXPolyPropLam (.bvar 0))
      (.sort (.succ .zero)) .prop ∧
    ¬ Nonempty (CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n
      [.assumption idPiProp] idPiProp) := by
  have hΓ : CtxWfT eqEnvT n [.assumption idPiProp] :=
    .assumption [] idPiProp .zero .nil (apartLeft_ty n [])
  have hp : HasTyT eqEnvT n [.assumption idPiProp] (.bvar 0) idPiProp :=
    .bvar _ 0 _ rfl
  have ha : CovXCompactAction eqEnvT (.lam [([], .prop)]) [] .prop :=
    .app (List.mem_singleton_self _) (fun _ h => (List.not_mem_nil _ h).elim)
  have hρ : EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n [.assumption idPiProp])
      [.assumption idPiProp] EnvT.bot :=
    envTypedCovAtP_bot_of_no_values C (fun A => ApproxTK.bot _ _ A)
      (fun i => by cases i <;> rfl)
  have ht : HasTyT eqEnvT n [.assumption idPiProp]
      (.app covXPolyPropLam (.bvar 0)) (.sort (.succ .zero)) :=
    .app _ _ _ _ _ (covXPolyPropLam_typed n [.assumption idPiProp]) hp
  have hm : ApproxTK eqEnvT n [.assumption idPiProp] EnvT.bot
      (.app covXPolyPropLam (.bvar 0)) .prop :=
    .app (covXPolyPropLam_observed n [.assumption idPiProp] EnvT.bot)
      (List.mem_singleton_self _) (fun _ h => (List.not_mem_nil _ h).elim)
  exact ⟨⟨pinEqGroupWfT⟩, ⟨hΓ⟩, ⟨hp⟩, hρ, covXPolyPropLam_piGate C hS,
    ha, ⟨ht⟩, hm,
    covXPolyPropLam_one_layer_action C hS n [.assumption idPiProp] [] .prop ha _ _,
    not_covXTypeView_idPiProp_eq n [.assumption idPiProp]⟩

/-- The exact one-way type-transport port. It transports this relation,
not model observations. Native conversion is not asserted to supply it. -/
def CovXTypeTransportAt (C : CovTyping E) (R : Readback) (n : Nat)
    (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ x y c, LRSCoreCovX C R n Γ x y A c → LRSCoreCovX C R n Γ x y B c

theorem covXTypeTransportAt_of_readback (C : CovTyping E)
    (hL : ReadbackLaws E R) (hD : DetR R)
    {Γ : LCtx} {A B : Expr Nat} (hr : RedR R Γ A B) :
    CovXTypeTransportAt C R n Γ A B ∧ CovXTypeTransportAt C R n Γ B A :=
  ⟨fun _ _ c h => (lrSCoreCovX_type_readback_iff C hL hD hr c).mp h,
    fun _ _ c h => (lrSCoreCovX_type_readback_iff C hL hD hr c).mpr h⟩

/-- Both directions of relation transport are supplied on the actual Eq
alias, even though raw observation transport fails there. -/
theorem covXTypeTransportAt_eqGapAlias (C : CovTyping eqEnvT) (n : Nat)
    (A B : Expr Nat) :
    CovXTypeTransportAt C (WhStepCK2 eqEnvT n) n eqGapCtx
      (eqGapDirectAlias A B) (.sort .zero) ∧
    CovXTypeTransportAt C (WhStepCK2 eqEnvT n) n eqGapCtx
      (.sort .zero) (eqGapDirectAlias A B) :=
  covXTypeTransportAt_of_readback C (readbackLaws_whStepCK2 eqEnvT n)
    (detR_whStepCK2 pinEqGroupWfT) (eqGapAlias_type_read n A B)

/-- The type-transport supplier is exercised at a non-bottom related Pi
probe, with an actual native conversion, typing and coherent environment. -/
theorem covXTypeTransportAt_eqGapAlias_native_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (ConvT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort .zero)
        (.sort (.succ .zero))) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      LRSCoreCovX C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) ∧
      (.pi .bot [] : CptT) ≠ .bot ∧
      CovXTypeTransportAt C (WhStepCK2 eqEnvT n) n eqGapCtx
        (eqGapDirectAlias A B) (.sort .zero) ∧
      CovXTypeTransportAt C (WhStepCK2 eqEnvT n) n eqGapCtx
        (.sort .zero) (eqGapDirectAlias A B) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨A, B, _, ⟨hβ⟩, _⟩ := eqGapDirectAlias_native_beta_control n
  obtain ⟨hg⟩ := eqGap_conv n
  have hc : ConvT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort .zero)
      (.sort (.succ .zero)) :=
    .trans _ _ _ _ _ hβ (.symm _ _ _ _ hg)
  have ht : HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B) :=
    .conv _ _ _ _ _ (apartLeft_ty n eqGapCtx) (.symm _ _ _ _ hc)
  have hgated : C.ty (.pi .bot []) .prop := by
    apply hS
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  have hr : LRSCoreCovX C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (eqGapDirectAlias A B) (.pi .bot []) :=
    lrSCoreCovX_of_view C (.sort .zero (eqGapAlias_type_read n A B))
      ⟨hgated, idPiProp_covRel_at_alias C n A B⟩
  exact ⟨⟨pinEqGroupWfT⟩, ⟨hΓ⟩, envTypedCovAtP_eqGap_bot C n,
    A, B, ⟨hc⟩, ⟨ht⟩, approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot _ _,
    hr, fun h => CptT.noConfusion h, covXTypeTransportAt_eqGapAlias C n A B⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_BOUNDARY_ROOTS
#print axioms covXTypeView_has_normal_head
#print axioms CovXTypedViews
#print axioms covXTypedViews_implies_type_normalization
#print axioms covXTypeView_impredicative_false
#print axioms not_covXTypeView_idPiProp_eq
#print axioms not_covXTypedViews_eqEnv
#print axioms not_covXTypeView_pi_idPiProp
#print axioms covXPolyPropLam
#print axioms covXPolyPropLamTy
#print axioms covXPolyPropLam_typed
#print axioms covXPolyPropLam_observed
#print axioms not_lrSCoreCovX_polyPropLam
#print axioms covX_eager_view_typed_counterexample
#print axioms not_fundTyAtCovX_polyPropLam
#print axioms not_fundamentalCovXAt_eqEnv
#print axioms covXPolyPropLam_piGate
#print axioms covXPolyPropLam_one_layer_action
#print axioms covXPolyPropLam_typed_action_control
#print axioms CovXTypeTransportAt
#print axioms covXTypeTransportAt_of_readback
#print axioms covXTypeTransportAt_eqGapAlias
#print axioms covXTypeTransportAt_eqGapAlias_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
