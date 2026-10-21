import rcic.RcicNativeTypedModelCovXCore
import rcic.RcicNativeTypedModelCovXTypePosition
import rcic.RcicNativeTypedModelCovRelApp

/-!
# Hereditary realization along the explicit native type view

The Pi clause visits the domain for the actual related argument demands.
It visits the codomain twice: once in its binder context with the finite
demand valuation, and once at each native argument instantiation with the
original valuation. These are distinct recursive children of the supplied
type view; no model-substitution identification is built into the definition.

Only non-bottom applications expose such observations. At bottom output no
type position is demanded. Sort and base leaves compose the landed normalized
realization. Consequently neither a global base-realization theorem nor a
global binder/instantiation theorem is obtained by defining this target.

The actual normal-Pi alias fixture positively realizes this target, including
all demanded arguments of every compact application. Its old normalized and
raw realizations remain refuted. The recursive relation is the new view-indexed
candidate, not a renamed instance of the old lambda clause.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovPropagationAudit TypedModelCovRelAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormEscapeAudit TypedModelCovNormBoundaryAudit
open TypedModelCovNormCov2Audit TypedModelCovXAudit
open TypedModelCovXTypePositionAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Hereditary type realization follows the supplied type view. It retains
the argument-demand realization as a conclusion, not as an assumed input.
The binder valuation and the two native instantiation valuations are separate. -/
def HereditaryCovRealizationXAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    (ρ : EnvT) (c : CptT) : Prop :=
  match view with
  | .sort _ _ => NormalizedCovRealization C (Q Γ) R Γ ρ A c
  | .base _ _ _ _ _ => NormalizedCovRealization C (Q Γ) R Γ ρ A c
  | .pi D B _ dom body cod =>
      CovXPiGate C c ∧
      ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out → out ≠ .bot →
      ∀ (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D),
      Nonempty (ConvT E n Γ N N' D) →
      (∀ u ∈ ds, LRSCoreCovXAt C dom N N' u) →
        (∀ u ∈ ds, HereditaryCovRealizationXAt C Q dom ρ u) ∧
        HereditaryCovRealizationXAt C Q body (EnvT.cons (demandT ds) ρ) out ∧
        HereditaryCovRealizationXAt C Q (cod N hN) ρ out ∧
        HereditaryCovRealizationXAt C Q (cod N' hN') ρ out

/-- The normalized sort typing gate supplies genuine hereditary escape at
each sort leaf, for every related compact and every valuation. -/
theorem hereditaryCovRealizationXAt_sort_of_related (C : CovTyping E)
    (n : Nat) {Γ : LCtx} {A x y : Expr Nat} (l : Level)
    (hr : RedR (WhStepCK2 E n) Γ A (.sort l)) (ρ : EnvT) (c : CptT)
    (h : LRSCoreCovXAt (n := n) C (.sort l hr) x y c) :
    HereditaryCovRealizationXAt (n := n) C (ctxModelT_approxTK E n)
      (.sort l hr) ρ c := by
  exact ⟨.sort l, sortCode l, hr, normalR_sortCK2 Γ l,
    approxTK_sort_code E n Γ ρ l, h.1⟩

/-- A uniform bottom inhabitant follows genuine view children. No universal
normalization assumption is needed because the view provides its readbacks. -/
theorem hereditaryCovRealizationXAt_bot (C : CovTyping E) (n : Nat)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E (WhStepCK2 E n) n Γ A)
    (ρ : EnvT) :
    HereditaryCovRealizationXAt C (ctxModelT_approxTK E n) view ρ .bot := by
  cases view with
  | sort l hr =>
      exact ⟨.sort l, .bot, hr, normalR_sortCK2 _ l, ApproxTK.bot _ _ _, C.bot _⟩
  | base Z hr hn hs hp =>
      exact ⟨Z, .bot, hr, hn, ApproxTK.bot _ _ _, C.bot _⟩
  | pi D B hr dom body cod =>
      refine ⟨covXPiGate_bot C, ?_⟩
      intro ds out ha hnb
      cases ha with
      | bot => exact (hnb rfl).elim

/-- The alias has a concrete finite type view. The binder and all native
instantiated codomains are independently sort views. -/
def covXAliasPiView (n : Nat) (A B : Expr Nat) :
    CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx (covNormAliasPi A B) :=
  .pi (eqGapDirectAlias A B) (.sort .zero) (.refl _)
    (.sort .zero (eqGapAlias_type_read n A B))
    (.sort .zero (.refl _))
    (fun _ _ => .sort .zero (.refl _))

/-- The exact non-bottom identity row passes the Pi gate at a semantic Pi
code built from its readback domain. No raw alias observation is requested. -/
theorem covXAliasIdentity_piGate (C : CovTyping E) (hS : CovTypingIncludesS C) :
    CovXPiGate C covNormAliasIdentityCpt := by
  refine ⟨.prop, [([], .prop)], hS _ _ ?_⟩
  change CTyS E (.lam [([.pi .bot []], .pi .bot [])]) (.pi .prop [([], .prop)])
  rw [CTyS]
  refine Or.inr ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · intro hp
    cases hp with
    | pi _ ho => exact not_isPropCT_prop E (ho ([], .prop) (List.mem_singleton.mpr rfl))
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  · intro s hs t ht _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp ht
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  · intro s hs
    exact Or.inr ⟨([], .prop), List.mem_singleton.mpr rfl,
      fun _ hs => (List.not_mem_nil _ hs).elim⟩

private theorem covX_pi_bot_typed_prop (C : CovTyping E) (hS : CovTypingIncludesS C) :
    C.ty (.pi .bot []) .prop := by
  apply hS
  rw [CTyS]
  exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

private theorem covX_sort0_realizes_pi_bot (C : CovTyping E)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    NormalizedCovRealization C (ctxModelT_approxTK E n Γ) (WhStepCK2 E n)
      Γ ρ (.sort .zero) (.pi .bot []) := by
  refine ⟨.sort .zero, .prop, .refl _, normalR_sortCK2 Γ .zero, ?_,
    covX_pi_bot_typed_prop C hS⟩
  simpa only [sortCode_zero] using approxTK_sort_code E n Γ ρ .zero

/-- Full extensional self-relatedness at the concrete alias view. Compact
application inversion extracts the original singleton row by composition. -/
theorem covXAliasIdentity_related (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (A B : Expr Nat)
    (hD : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort (.succ .zero))) :
    LRSCoreCovXAt C (covXAliasPiView n A B)
      covNormAliasIdentity covNormAliasIdentity covNormAliasIdentityCpt := by
  refine ⟨covXAliasIdentity_piGate C hS, ?_⟩
  intro ds out ha N N' hN hN' hc hd
  cases ha with
  | bot =>
      exact ⟨lrSCoreCovXAt_bot C _ _ _, lrSCoreCovXAt_bot C _ _ _⟩
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      have hmem : (.pi .bot [] : CptT) ∈ ds := by
        rcases approxT_bvar_inv (hx (.pi .bot []) (List.mem_singleton.mpr rfl)) with hb | hm
        · cases hb
        · exact hm
      have hargs : ∀ u ∈ [(.pi .bot [] : CptT)],
          LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx N N'
            (eqGapDirectAlias A B) u := by
        intro u hu
        obtain rfl := List.mem_singleton.mp hu
        exact (hd (.pi .bot []) hmem).2
      have hresult := lrSCoreCov_app C (readbackLaws_whStepCK2 eqEnvT n)
        (covNormAliasIdentity_core C n A B hD) (List.mem_singleton.mpr rfl)
        hN hN' hc hargs
      have hty : C.ty (.pi .bot []) (sortCode .zero) := by
        simpa only [sortCode_zero] using covX_pi_bot_typed_prop C hS
      exact ⟨⟨hty, hresult⟩, ⟨hty, hresult⟩⟩

/-- The complete hereditary target is positive at the formerly obstructed
Pi. It realizes every related demand, the binder body in the extended
valuation, and both codomain instances in the original valuation. -/
theorem hereditaryCovRealizationXAt_covNormAliasPi (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    HereditaryCovRealizationXAt C (ctxModelT_approxTK eqEnvT n)
      (covXAliasPiView n A B) ρ covNormAliasIdentityCpt := by
  refine ⟨covXAliasIdentity_piGate C hS, ?_⟩
  intro ds out ha hnb N N' hN hN' hc hd
  cases ha with
  | bot => exact (hnb rfl).elim
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu
        exact hereditaryCovRealizationXAt_sort_of_related C n .zero
          (eqGapAlias_type_read n A B) ρ u (hd u hu)
      · exact covX_sort0_realizes_pi_bot C hS n
          (.assumption (eqGapDirectAlias A B) :: eqGapCtx) (EnvT.cons (demandT ds) ρ)
      · exact covX_sort0_realizes_pi_bot C hS n eqGapCtx ρ
      · exact covX_sort0_realizes_pi_bot C hS n eqGapCtx ρ

/-- All former counterexample guards remain inhabited, now with a positive
hereditary target and the new extensional relation at the same actual compact. -/
theorem covXAlias_hereditary_native_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity (covNormAliasPi A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot covNormAliasIdentity covNormAliasIdentityCpt ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot (covNormAliasPi A B) (.pi .bot []) ∧
      LRSCoreCovXAt C (covXAliasPiView n A B)
        covNormAliasIdentity covNormAliasIdentity covNormAliasIdentityCpt ∧
      HereditaryCovRealizationXAt C (ctxModelT_approxTK eqEnvT n)
        (covXAliasPiView n A B) EnvT.bot covNormAliasIdentityCpt ∧
      (¬ NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
        (WhStepCK2 eqEnvT n) eqGapCtx EnvT.bot (covNormAliasPi A B)
        covNormAliasIdentityCpt) ∧ covNormAliasIdentityCpt ≠ .bot := by
  obtain ⟨A, B, ⟨hD⟩, hx⟩ := covNormAliasIdentity_native n
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovAtP_eqGap_bot C n,
    A, B, hx, covNormAliasIdentity_approxTK eqEnvT n eqGapCtx EnvT.bot,
    approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot (eqGapDirectAlias A B) (.sort .zero),
    covXAliasIdentity_related C hS n A B hD,
    hereditaryCovRealizationXAt_covNormAliasPi C hS n EnvT.bot A B,
    not_normalizedCovRealization_covNormAliasPi C n EnvT.bot A B,
    fun h => CptT.noConfusion h⟩

/-- Hereditary positivity cannot supply the old raw source observation port.
The two conclusions concern exactly the same domain alias and native view. -/
theorem hereditary_alias_does_not_supply_raw_type_port (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    HereditaryCovRealizationXAt C (ctxModelT_approxTK eqEnvT n)
      (covXAliasPiView n A B) ρ covNormAliasIdentityCpt ∧
    (¬ ElTCovP C (ctxModelT_approxTK eqEnvT n eqGapCtx) ρ
      (covNormAliasPi A B) covNormAliasIdentityCpt) ∧
    ¬ TypePositionReadbackAtTK eqEnvT n eqGapCtx (eqGapDirectAlias A B) :=
  ⟨hereditaryCovRealizationXAt_covNormAliasPi C hS n ρ A B,
    not_elTCovP_covNormAliasPi C n eqGapCtx ρ A B,
    not_typePositionReadbackAtTK_eqGapAlias n A B⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_ROOTS
#print axioms HereditaryCovRealizationXAt
#print axioms hereditaryCovRealizationXAt_sort_of_related
#print axioms hereditaryCovRealizationXAt_bot
#print axioms covXAliasPiView
#print axioms covXAliasIdentity_piGate
#print axioms covXAliasIdentity_related
#print axioms hereditaryCovRealizationXAt_covNormAliasPi
#print axioms covXAlias_hereditary_native_control
#print axioms hereditary_alias_does_not_supply_raw_type_port
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit
