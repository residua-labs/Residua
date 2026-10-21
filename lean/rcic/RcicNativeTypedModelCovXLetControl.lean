import rcic.RcicNativeTypedModelCovXInterface

/-!
# A nonempty let-context package for the extensional relation

All native substitution evidence, both covariant environments, and the four
old variable/let relations come from the landed let-context package. The
only additional work is the normalized sort gate: environment realization
at Sort 1 supplies that gate by the imported sort observation inversion.
Let-value observations first return to the variable through the actual
`CtxEnvM` coherence field, so no coherence guard is erased.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovRelAudit TypedModelCovXAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

private theorem covX_sort_gate_of_realization (C : CovTyping E)
    {Ξ : LCtx} {ρ : EnvT} {l : Level} {c : CptT}
    (h : ElTCovP C (ctxModelT_approxTK E n Ξ) ρ (.sort l) c) :
    C.ty c (sortCode l) := by
  obtain ⟨a, ha, ht⟩ := h
  rcases approxTK_sort_inv ha with rfl | rfl
  · rw [C.bot_inv ht]
    exact C.bot _
  · exact ht

private theorem covX_square_of_sort_edges (C : CovTyping E)
    {Δ : LCtx} {x x' y y' : Expr Nat} {c : CptT} (l : Level)
    (hc : C.ty c (sortCode l))
    (h : LRSCoreCov C R n Δ x y' (.sort l) c ∧
      LRSCoreCov C R n Δ x' y (.sort l) c ∧
      LRSCoreCov C R n Δ x y (.sort l) c ∧
      LRSCoreCov C R n Δ x' y' (.sort l) c) :
    CovXSquare C R n Δ x x' y y' (.sort l) (.sort l) c :=
  ⟨lrSCoreCovX_of_view C (.sort l (.refl _)) ⟨hc, h.1⟩,
    lrSCoreCovX_of_view C (.sort l (.refl _)) ⟨hc, h.2.1⟩,
    lrSCoreCovX_of_view C (.sort l (.refl _)) ⟨hc, h.2.2.1⟩,
    lrSCoreCovX_of_view C (.sort l (.refl _)) ⟨hc, h.2.2.2⟩⟩

/-- The full nonempty new package is obtained by transporting the landed
let package's edges into a sort view. Its environments and native evidence
are reused without modification. -/
theorem relSubstAtCovX_zetaLocalSortCtx_approxTK (hW : EnvWfT E)
    (n : Nat) (Ξ : LCtx) :
    RelSubstAtCovX (covTypingCTyCov E) (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx := by
  have old := relSubstAtCov_zetaLocalSortCtx_approxTK hW n Ξ
  refine ⟨old.typedL, old.typedR, old.conv, old.envL, old.envR, ?_, ?_⟩
  · intro i A hA c hc
    have hedges := old.vars i A hA c hc
    have hreal := old.envL.1 i A hA c (hc.elim id id)
    cases i with
    | zero =>
        change some (.sort (.succ .zero)) = some A at hA
        cases Option.some.inj hA
        simp only [SubstT.id, substT_id] at hedges ⊢
        exact covX_square_of_sort_edges (covTypingCTyCov E) (.succ .zero)
          (covX_sort_gate_of_realization (covTypingCTyCov E) hreal) hedges
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA
  · intro i v A hv hA c hc
    have hedges := old.lets i v A hv hA c hc
    have hvar : c = .bot ∨ ctxEnvT E zetaLocalSortCtx i c := by
      rcases hc with ho | ho | ho | ho
      · exact Or.inr ho
      · exact Or.inr ho
      · exact approxTK_bvar_inv ((old.envL.2 i v hv c).mpr ho)
      · exact approxTK_bvar_inv ((old.envR.2 i v hv c).mpr ho)
    cases i with
    | zero =>
        change some (.sort (.succ .zero)) = some A at hA
        cases Option.some.inj hA
        have hgate : (covTypingCTyCov E).ty c (sortCode (.succ .zero)) := by
          rcases hvar with rfl | hm
          · exact (covTypingCTyCov E).bot _
          · exact covX_sort_gate_of_realization (covTypingCTyCov E)
              (old.envL.1 0 (.sort (.succ .zero)) hA c hm)
        simp only [SubstT.id, substT_id] at hedges ⊢
        exact covX_square_of_sort_edges (covTypingCTyCov E) (.succ .zero) hgate hedges
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA

/-- Native local zeta, both actual coherence guards, the full related
substitution package, and a shared prop observation coexist in a nonempty
let context. The old native/observation control is composed directly. -/
theorem covX_zetaLocalSortCtx_control (hW : EnvWfT E) (n : Nat) (Ξ : LCtx) :
    Nonempty (CtxWfT E n zetaLocalSortCtx) ∧
    Nonempty (HasTyT E n zetaLocalSortCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero))) ∧
    CtxEnvM (ctxModelT_approxTK E n Ξ) zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) ∧
    CtxEnvM (ctxModelT_approxTK E n Ξ) zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) ∧
    RelSubstAtCovX (covTypingCTyCov E) (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx ∧
    ctxEnvT E zetaLocalSortCtx 0 .prop ∧
    ApproxTK E n Ξ (ctxEnvT E zetaLocalSortCtx) (.bvar 0) .prop ∧
    ApproxTK E n Ξ (ctxEnvT E zetaLocalSortCtx) (.sort .zero) .prop ∧
    LRSCoreCovX (covTypingCTyCov E) (WhStepCK2 E n) n zetaLocalSortCtx
      (.bvar 0) (.sort .zero) (.sort (.succ .zero)) .prop ∧
    (.prop : CptT) ≠ .bot := by
  obtain ⟨hΓ, ht, hconv, _, c, hnb, hm, hx, hv, _⟩ :=
    zetaLocalSortCtx_cov_related_control hW n Ξ
  have he : c = .prop := by
    rcases approxTK_sort_inv hv with hb | he
    · exact (hnb hb).elim
    · simpa only [sortCode_zero] using he
  subst c
  have hs := relSubstAtCovX_zetaLocalSortCtx_approxTK hW n Ξ
  refine ⟨hΓ, ht, hconv, hs.ctxEnvs.1, hs.ctxEnvs.2, hs, hm, hx, hv, ?_, hnb⟩
  simpa only [SubstT.id, substT_id] using
    (hs.lets 0 (.sort .zero) (.sort (.succ .zero)) rfl rfl .prop (Or.inl hm)).1

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_LET_CONTROL_ROOTS
#print axioms relSubstAtCovX_zetaLocalSortCtx_approxTK
#print axioms covX_zetaLocalSortCtx_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_LET_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit
