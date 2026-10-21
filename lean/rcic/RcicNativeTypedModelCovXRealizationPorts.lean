import rcic.RcicNativeTypedModelCovXRealizationNat

/-!
# Atomic supplies for hereditary escape

This conditional assembler does not assume hereditary realization. Its base
input is an actual non-proposition spine code observed at the base view's
normal form. Its Pi input supplies relation evidence in the binder context,
separately from the two instantiated codomain relations supplied by the core.
The latter is the precise reabstraction gap: the original core's application
conclusion lives in the unextended context and does not contain that evidence.

All recursive calls visit genuine children of the native type view. The
same supply is inhabited at the actual Eq-alias identity row and at rigid
successor, with the native premises of both controls retained separately.
The assembler is conditional; it is not a global supply of either input.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormCov2Audit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovXRealizationAudit TypedModelCovXRealizationNatAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- At a base leaf only a genuine normal-form code is requested. At a Pi
node the additional binder evidence is a relation witness, not an instance
of the desired hereditary-realization conclusion. -/
def CovXHereditarySupplyAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A) (c : CptT) : Prop :=
  match view with
  | .sort _ _ => True
  | .base Z _ _ _ _ =>
      c ≠ .bot → ∀ ρ, ∃ r args,
        (Q Γ).Ap ρ Z (.spine r args) ∧ ¬ IsPropCT E (.spine r args)
  | .pi D B _ dom body cod =>
      ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out → out ≠ .bot →
      ∀ (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D),
      Nonempty (ConvT E n Γ N N' D) →
      (∀ u ∈ ds, LRSCoreCovXAt C dom N N' u) →
        (∀ u ∈ ds, CovXHereditarySupplyAt C Q dom u) ∧
        (∃ z z', Nonempty (HasTyT E n (.assumption D :: Γ) z B) ∧
          Nonempty (HasTyT E n (.assumption D :: Γ) z' B) ∧
          LRSCoreCovXAt C body z z' out ∧
          CovXHereditarySupplyAt C Q body out) ∧
        CovXHereditarySupplyAt C Q (cod N hN) out ∧
        CovXHereditarySupplyAt C Q (cod N' hN') out

/-- Structural composition of the explicit atomic supplies. Native
instantiation results come from the relation; the body result comes from the
separate binder witness. Their model valuations remain distinct. -/
theorem hereditaryCovRealizationXAt_of_supply (C : CovTyping E)
    (hS : CovTypingIncludesS C) (n : Nat) {Γ : LCtx} {A : Expr Nat}
    (view : CovXTypeView E (WhStepCK2 E n) n Γ A)
    (hs : CovXHereditarySupplyAt C (ctxModelT_approxTK E n) view c)
    (h : LRSCoreCovXAt C view x y c) (ρ : EnvT) :
    HereditaryCovRealizationXAt C (ctxModelT_approxTK E n) view ρ c := by
  induction view generalizing x y c ρ with
  | sort l hr => exact hereditaryCovRealizationXAt_sort_of_related C n l hr ρ c h
  | base Z hr hn hns hnp =>
      rcases covX_base_related_compact_shape C hns hnp h with rfl | ⟨r, args, rfl⟩
      · exact ⟨Z, .bot, hr, hn, ApproxTK.bot _ _ _, C.bot _⟩
      · obtain ⟨r', args', hm, hnp'⟩ := hs (fun h => CptT.noConfusion h) ρ
        refine ⟨Z, .spine r' args', hr, hn, hm, hS _ _ ?_⟩
        rw [CTyS]
        exact Or.inr ⟨⟨r, args, rfl⟩, hnp'⟩
  | pi D B hr dom body cod ihdom ihbody ihcod =>
      refine ⟨h.1, ?_⟩
      intro ds out ha hnb N N' hN hN' hc hd
      obtain ⟨hsdom, ⟨z, z', _, _, hbody, hsbody⟩, hsleft, hsright⟩ :=
        hs ds out ha hnb N N' hN hN' hc hd
      obtain ⟨hleft, hright⟩ := h.2 ds out ha N N' hN hN' hc hd
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu
        exact ihdom (hsdom u hu) (hd u hu) ρ
      · exact ihbody hsbody hbody (EnvT.cons (demandT ds) ρ)
      · exact ihcod N hN hsleft hleft ρ
      · exact ihcod N' hN' hsright hright ρ

/-- The same concrete supply realizes both model valuations. No equality
between the left and right environments is assumed. -/
theorem hereditaryCovRealizationXAt_escape_pair (C : CovTyping E)
    (hS : CovTypingIncludesS C) (n : Nat) {Γ : LCtx} {A : Expr Nat}
    (view : CovXTypeView E (WhStepCK2 E n) n Γ A)
    (hs : CovXHereditarySupplyAt C (ctxModelT_approxTK E n) view c)
    (h : LRSCoreCovXAt C view x y c) (ρ ρ' : EnvT) :
    HereditaryCovRealizationXAt C (ctxModelT_approxTK E n) view ρ c ∧
    HereditaryCovRealizationXAt C (ctxModelT_approxTK E n) view ρ' c :=
  ⟨hereditaryCovRealizationXAt_of_supply C hS n view hs h ρ,
    hereditaryCovRealizationXAt_of_supply C hS n view hs h ρ'⟩

/-- Every Nat base leaf has the required actual non-proposition code. This
supplies all compact instances of the base input, not just the zero row. -/
theorem covXHereditarySupplyAt_nat (n : Nat) (Γ : LCtx) (c : CptT) :
    CovXHereditarySupplyAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatView n Γ) c := by
  intro hne ρ
  exact ⟨0, [], ApproxTK.free (kFreeT_natEnvU _)
    (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat),
    not_isPropCT_natEnvU_nat_spine []⟩

/-- Successor's exact supply includes a non-bottom body relation in the
extended native context. The chosen body endpoints are actual applications
of successor to zero; arbitrary compact argument labels are allowed by the
imported base spine clause. -/
theorem covXHereditarySupplyAt_natSucc (n : Nat) (Γ : LCtx) :
    CovXHereditarySupplyAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatArrowView n Γ) (.spine 2 []) := by
  intro ds out ha hnb N N' hN hN' hc hd
  cases ha with
  | bot => exact (hnb rfl).elim
  | @appSpine r args arg u hu =>
      refine ⟨fun c _ => covXHereditarySupplyAt_nat n Γ c, ?_,
        covXHereditarySupplyAt_nat n Γ _, covXHereditarySupplyAt_nat n Γ _⟩
      let Δ := .assumption (.const 0 []) :: Γ
      have hz : HasTyT natEnvU n Δ (.app (.const 2 []) (.const 1 [])) (.const 0 []) :=
        .app _ _ _ _ _ (hasTyT_natEnvU_succ n Δ) (hasTyT_natEnvU_zero n Δ)
      refine ⟨.app (.const 2 []) (.const 1 []), .app (.const 2 []) (.const 1 []),
        ⟨hz⟩, ⟨hz⟩, ?_, covXHereditarySupplyAt_nat n Δ _⟩
      exact (lrSCoreCov_spine_iff (C2 natEnvU) Δ _ _ _ 2 [u]).mpr
        (covX_natSucc_spine_action n Δ (.const 1 []) (.const 1 []) u
          (.refl Δ (.const 1 []) (.const 0 []) (hasTyT_natEnvU_zero n Δ)))

private theorem covX_pi_bot_sort_body (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) {Γ : LCtx} (hΓ : CtxWfT eqEnvT n Γ) :
    LRSCoreCovXAt (n := n) (R := WhStepCK2 eqEnvT n) (Γ := Γ)
      C (.sort .zero (.refl (.sort .zero)))
      idPiProp idPiProp
      (.pi .bot []) := by
  refine ⟨?_, ?_⟩
  · rw [sortCode_zero]
    apply hS
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  · rw [LRSCoreCov.eq_def]
    refine ⟨⟨.zero, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0,
      .refl _, .refl _, ⟨.assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort _ _)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.zero, lrSCoreCov_bot C _ _ _ _⟩, ?_⟩
    intro s hs
    exact (List.not_mem_nil _ hs).elim

/-- The exact Eq-alias supply is inhabited on its actual native typing
premise. Its binder witness is a native normal Pi type at the demanded
compact, in the actual extended context. No model reflection of the raw
alias is assumed. -/
theorem covXHereditarySupplyAt_alias (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (A B : Expr Nat)
    (hD : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort (.succ .zero))) :
    CovXHereditarySupplyAt C (ctxModelT_approxTK eqEnvT n)
      (covXAliasPiView n A B) covNormAliasIdentityCpt := by
  intro ds out ha hnb N N' hN hN' hc hd
  cases ha with
  | bot => exact (hnb rfl).elim
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      obtain ⟨hΓ⟩ := eqGapCtx_wf n
      have hΔ := CtxWfT.assumption eqGapCtx (eqGapDirectAlias A B) (.succ .zero) hΓ hD
      exact ⟨fun _ _ => True.intro,
        ⟨idPiProp, idPiProp, ⟨apartLeft_ty n _⟩, ⟨apartLeft_ty n _⟩,
          covX_pi_bot_sort_body C hS n hΔ, True.intro⟩,
        True.intro, True.intro⟩

/-- The general conditional assembler has an inhabited non-bottom Eq
instance. This is a supply of the local ports at this fixture only. -/
theorem covXHereditarySupplyAt_alias_native_control (n : Nat) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity (covNormAliasPi A B)) ∧
      CovXHereditarySupplyAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (covXAliasPiView n A B) covNormAliasIdentityCpt ∧
      LRSCoreCovXAt (C2 eqEnvT) (covXAliasPiView n A B)
        covNormAliasIdentity covNormAliasIdentity covNormAliasIdentityCpt ∧
      HereditaryCovRealizationXAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (covXAliasPiView n A B) EnvT.bot covNormAliasIdentityCpt := by
  obtain ⟨A, B, ⟨hD⟩, hx⟩ := covNormAliasIdentity_native n
  have hs := covXHereditarySupplyAt_alias (C2 eqEnvT) (C2_includesS eqEnvT) n A B hD
  have hr := covXAliasIdentity_related (C2 eqEnvT) (C2_includesS eqEnvT) n A B hD
  exact ⟨A, B, hx, hs, hr,
    hereditaryCovRealizationXAt_of_supply (C2 eqEnvT) (C2_includesS eqEnvT) n
      (covXAliasPiView n A B) hs hr EnvT.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_PORTS_ROOTS
#print axioms CovXHereditarySupplyAt
#print axioms hereditaryCovRealizationXAt_of_supply
#print axioms hereditaryCovRealizationXAt_escape_pair
#print axioms covXHereditarySupplyAt_nat
#print axioms covXHereditarySupplyAt_natSucc
#print axioms covXHereditarySupplyAt_alias
#print axioms covXHereditarySupplyAt_alias_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_PORTS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit
