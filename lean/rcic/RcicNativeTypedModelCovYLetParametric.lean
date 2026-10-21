import rcic.RcicNativeTypedModelCovYLetControl

/-!
# Compact-typing transport of the actual nonempty let control

Every actual observation of the let value or its variable is bottom or prop.
At those two term compacts the imported relation payload is independent of
the compact typing predicate. Consequently the checked CovY package transports
to any `CovTyping` containing strict typing, including CTyCov2, without a
general relation monotonicity or code-coherence assumption.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKAudit TypedModelKControlAudit ReadbackCK2Audit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

private theorem covY_prop_payload_transport (C C' : CovTyping E)
    {Γ : LCtx} {x y A : Expr Nat} {a : CptT}
    (h : LRSCoreCovY C R n Γ x y A .prop a) : LRSCoreCov C' R n Γ x y A .prop := by
  rw [LRSCoreCovY.eq_def] at h
  cases a with
  | bot => exact (CptT.noConfusion (C.bot_inv h.1) : False).elim
  | pi d g =>
      rcases C.pi_inv h.1 with hb | ⟨f, he, _⟩ | ⟨r, args, he⟩
      · cases hb
      · cases he
      · cases he
  | prop | sort | lam g | spine r args =>
      exact (lrSCoreCov_prop_iff C' Γ x y A).mpr
        ((lrSCoreCov_prop_iff C Γ x y A).mp h.2)

private theorem covY_small_square_transport (C C' : CovTyping E)
    (hS : CovTypingIncludesS C') {Γ : LCtx} {x x' y y' A A' : Expr Nat} {c : CptT}
    (hc : c = .bot ∨ c = .prop)
    (h : CovYSquare C R n Γ x x' y y' A A' c) :
    CovYSquare C' R n Γ x x' y y' A A' c := by
  rcases hc with rfl | rfl
  · exact covYSquare_bot C' R n Γ x x' y y' A A'
  · obtain ⟨a, h₁, h₂, h₃, h₄⟩ := h
    have move : ∀ {x y A}, LRSCoreCovY C R n Γ x y A .prop a →
        LRSCoreCovY C' R n Γ x y A .prop .sort := fun h =>
      lrSCoreCovY_of_old_leaf C' (fun _ _ he => CptT.noConfusion he)
        (hS _ _ (ctyS_prop_sort E)) (covY_prop_payload_transport C C' h)
    exact ⟨.sort, move h₁, move h₂, move h₃, move h₄⟩

private theorem covY_let_entry_shape (i : Nat) {c : CptT}
    (h : ctxEnvT E zetaLocalSortCtx i c) : c = .bot ∨ c = .prop := by
  cases i with
  | zero => exact (approxT_sort_inv h).imp_right (fun he => he.trans sortCode_zero)
  | succ i => exact Or.inl h

/-- The complete checked nonempty let package transports to any admissible
compact typing predicate. Its native substitution and let equations are reused. -/
theorem relSubstAtCovY_zetaLocalSortCtx_parametric (C : CovTyping E)
    (hS : CovTypingIncludesS C) (hW : EnvWfT E) (n : Nat) :
    RelSubstAtCovY C (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx := by
  have old := relSubstAtCovY_zetaLocalSortCtx_approxTK hW n
  have he : EnvTypedCovYAt C (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) := by
    refine ⟨?_, old.envL.2⟩
    intro i A hA c hc
    rcases covY_let_entry_shape i hc with rfl | rfl
    · exact hereditaryCovRealizationY_bot C _ _ n _ _ A
    · cases i with
      | zero =>
          have hEq : .sort (.succ .zero) = A := Option.some.inj hA
          subst A
          refine ⟨sortCode (.succ .zero), hereditaryCovRealizationYAt_sort C n
            (.succ .zero) (.refl _) ?_⟩
          simpa only [TypingFin.sortCode_succ] using hS _ _ (ctyS_prop_sort E)
      | succ i => simp [zetaLocalSortCtx, lookupType] at hA
  refine ⟨old.typedL, old.typedR, old.conv, he, he, ?_, ?_⟩
  · intro i A hA c hc
    exact covY_small_square_transport _ C hS
      (covY_let_entry_shape i (hc.elim id id)) (old.vars i A hA c hc)
  · intro i v A hv hA c hc
    have hs : c = .bot ∨ c = .prop := by
      rcases hc with hm | hm | hm | hm
      · exact covY_let_entry_shape i hm
      · exact covY_let_entry_shape i hm
      · exact (approxTK_bvar_inv ((old.ctxEnvs.1 i v hv c).mpr hm)).elim
          Or.inl (covY_let_entry_shape i)
      · exact (approxTK_bvar_inv ((old.ctxEnvs.2 i v hv c).mpr hm)).elim
          Or.inl (covY_let_entry_shape i)
    exact covY_small_square_transport _ C hS hs (old.lets i v A hv hA c hc)

/-- The nondegenerate let witness now includes CTyCov2 by direct
instantiation; it retains both hereditary environment/coherence fields. -/
theorem covY_zetaLocalSortCtx_parametric_control (C : CovTyping E)
    (hS : CovTypingIncludesS C) (hW : EnvWfT E) (n : Nat) :
    Nonempty (CtxWfT E n zetaLocalSortCtx) ∧
    Nonempty (HasTyT E n zetaLocalSortCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero))) ∧
    RelSubstAtCovY C (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx ∧
    ctxEnvT E zetaLocalSortCtx 0 .prop ∧
    ApproxTK E n zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (.bvar 0) .prop ∧
    ApproxTK E n zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (.sort .zero) .prop ∧
    (.prop : CptT) ≠ .bot := by
  obtain ⟨hΓ, ht, hc, _, _, _, hm, hx, hv, _, hnb⟩ := covY_zetaLocalSortCtx_control hW n
  exact ⟨hΓ, ht, hc, relSubstAtCovY_zetaLocalSortCtx_parametric C hS hW n, hm, hx, hv, hnb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_LET_PARAMETRIC_ROOTS
#print axioms relSubstAtCovY_zetaLocalSortCtx_parametric
#print axioms covY_zetaLocalSortCtx_parametric_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_LET_PARAMETRIC_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
