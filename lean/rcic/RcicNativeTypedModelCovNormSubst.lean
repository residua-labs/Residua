import rcic.RcicNativeTypedModelCovRelFundApp
import rcic.RcicNativeTypedModelCovRelPER

/-!
# Realized assumption extension for the covariant relation

The domain code is an actual observation in the environment being extended.
Every demanded compact is typed at that code.  Those two facts establish the
new head's environment guard; the existing lift law transports all tail
types and both sides of every let-value equation.

The native substitution evidence is built independently of the relation.
The new typed PER produces the four required head relations.  No old
fundamental theorem, model-typing escape, or generated-derivation IH is used.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormSubstAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The empty source context has the complete related package for arbitrary
source valuations and substitutions.  The model itself is unrestricted. -/
theorem relSubstAtCov_nil (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) :
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' [] :=
  ⟨⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
    ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
    (fun _ _ h => Option.noConfusion h), envTypedCovAtP_nil C M ρ,
    envTypedCovAtP_nil C M ρ', (fun _ _ h => Option.noConfusion h),
    fun _ _ _ h => Option.noConfusion h⟩

/-- Only weakening observations and the variable side of let coherence are
needed for the semantic part of assumption extension. -/
structure CovLiftModelLaws (M : CtxModelT E) : Prop where
  lift : ∀ (ρ : EnvT) (S : CptT → Prop) (e : Expr Nat) (c : CptT),
    M.Ap (EnvT.cons S ρ) (lift 0 1 e) c ↔ M.Ap ρ e c
  bvar_succ : ∀ (ρ : EnvT) (S : CptT → Prop) (i : Nat) (c : CptT),
    M.Ap (EnvT.cons S ρ) (.bvar (i + 1)) c ↔ M.Ap ρ (.bvar i) c

theorem covLiftModelLaws_approxT (E : ResolvedEnv) :
    CovLiftModelLaws (ctxModelT_approxT E) := by
  refine ⟨fun ρ S e c => approxT_cons_lift0_iff E ρ S e c, ?_⟩
  intro ρ S i c
  change ApproxT E (EnvT.cons S ρ) (.bvar (i + 1)) c ↔ ApproxT E ρ (.bvar i) c
  rw [approxT_bvar_iff, approxT_bvar_iff]
  rfl

private theorem cov_lookupType_tail {Γ : LCtx} {d : LocalDecl} {i : Nat}
    {T : Expr Nat} (h : lookupType (d :: Γ) (i + 1) = some T) :
    ∃ A, lookupType Γ i = some A ∧ T = lift 0 1 A := by
  rw [lookupType_cons_succ] at h
  cases ht : lookupType Γ i with
  | none => rw [ht] at h; exact Option.noConfusion h
  | some A =>
      rw [ht] at h
      exact ⟨A, rfl, (Option.some.inj h).symm⟩

private theorem cov_lookupValue_tail {Γ : LCtx} {d : LocalDecl} {i : Nat}
    {v : Expr Nat} (h : lookupValue (d :: Γ) (i + 1) = some v) :
    ∃ w, lookupValue Γ i = some w ∧ v = lift 0 1 w := by
  rw [lookupValue_cons_succ] at h
  cases hv : lookupValue Γ i with
  | none => rw [hv] at h; exact Option.noConfusion h
  | some w =>
      rw [hv] at h
      exact ⟨w, rfl, (Option.some.inj h).symm⟩

/-- Native substitution typing under an assumption uses only the new
argument's native typing and the old native substitution. -/
theorem cov_typedSubst_cons {Δ Γ : LCtx} {σ : SubstT} {A N : Expr Nat}
    (hσ : TypedSubstT E n Δ σ Γ) (hN : HasTyT E n Δ N (substT σ A)) :
    TypedSubstT E n Δ (SubstT.cons N σ) (.assumption A :: Γ) := by
  constructor
  · intro i T hT
    cases i with
    | zero =>
        have h : lift 0 1 A = T := Option.some.inj hT
        subst T
        simpa only [SubstT.cons_zero, substT_cons_lift] using Nonempty.intro hN
    | succ i =>
        obtain ⟨B, hB, rfl⟩ := cov_lookupType_tail hT
        simpa only [SubstT.cons_succ, substT_cons_lift] using hσ.1 i B hB
  · intro i v hv
    cases i with
    | zero => simp [lookupValue] at hv
    | succ i =>
        obtain ⟨w, hw, rfl⟩ := cov_lookupValue_tail hv
        obtain ⟨B, hB, hconv⟩ := hσ.2 i w hw
        refine ⟨lift 0 1 B, ?_, ?_⟩
        · rw [lookupType_cons_succ, hB]; rfl
        · simpa only [SubstT.cons_succ, substT_cons_lift] using hconv

/-- The native pointwise conversion extends at the common left domain. -/
theorem cov_convSubst_cons {Δ Γ : LCtx} {σ σ' : SubstT} {A N N' : Expr Nat}
    (hσ : ConvSubstT E n Δ σ σ' Γ)
    (hN : ConvT E n Δ N N' (substT σ A)) :
    ConvSubstT E n Δ (SubstT.cons N σ) (SubstT.cons N' σ') (.assumption A :: Γ) := by
  intro i T hT
  cases i with
  | zero =>
      have h : lift 0 1 A = T := Option.some.inj hT
      subst T
      simpa only [SubstT.cons_zero, substT_cons_lift] using Nonempty.intro hN
  | succ i =>
      obtain ⟨B, hB, rfl⟩ := cov_lookupType_tail hT
      simpa only [SubstT.cons_succ, substT_cons_lift] using hσ i B hB

/-- A real observed domain code types every member of the new demand
valuation; the tail retains all original model guards and let equations. -/
theorem envTypedCovAtP_cons_assumption (hM : CovLiftModelLaws M)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {a : CptT} {d : List CptT}
    (hρ : EnvTypedCovAtP C M Γ ρ) (hA : M.Ap ρ A a)
    (hd : ∀ u ∈ d, C.ty u a) :
    EnvTypedCovAtP C M (.assumption A :: Γ) (EnvT.cons (demandT d) ρ) := by
  constructor
  · intro i T hT u hu
    cases i with
    | zero =>
        have h : lift 0 1 A = T := Option.some.inj hT
        subst T
        exact ⟨a, (hM.lift ρ (demandT d) A a).mpr hA, hd u hu⟩
    | succ i =>
        obtain ⟨B, hB, rfl⟩ := cov_lookupType_tail hT
        obtain ⟨b, hb, hub⟩ := hρ.1 i B hB u hu
        exact ⟨b, (hM.lift ρ (demandT d) B b).mpr hb, hub⟩
  · intro i v hv c
    cases i with
    | zero => simp [lookupValue] at hv
    | succ i =>
        obtain ⟨w, hw, rfl⟩ := cov_lookupValue_tail hv
        exact (hM.bvar_succ ρ (demandT d) i c).trans
          ((hρ.2 i w hw c).trans (hM.lift ρ (demandT d) w c).symm)

/-- Complete related assumption extension in one observed environment.
The caller may first re-pair the two source environments to select the
side that supplies the Pi/lambda constructor's domain observation. -/
theorem relSubstAtCov_cons_realized (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hM : CovLiftModelLaws M) {Δ Γ : LCtx} {ρ : EnvT} {σ σ' : SubstT}
    (hΔ : CtxWfT E n Δ) (hSub : RelSubstAtCov C M R n Δ ρ ρ σ σ' Γ)
    {A : Expr Nat} {a : CptT} {d : List CptT} {u w : Level}
    (hAa : M.Ap ρ A a) (hd : ∀ c ∈ d, C.ty c a)
    (hAA' : LRSCoreCov C R n Δ (substT σ A) (substT σ' A) (.sort w) a)
    (hAA : LRSCoreCov C R n Δ (substT σ A) (substT σ A) (.sort w) a)
    (hAc : ConvT E n Δ (substT σ A) (substT σ' A) (.sort u))
    {N N' : Expr Nat} (hN : HasTyT E n Δ N (substT σ A))
    (hN' : HasTyT E n Δ N' (substT σ A))
    (hcN : ConvT E n Δ N N' (substT σ A))
    (hrel : ∀ c ∈ d, LRSCoreCov C R n Δ N N' (substT σ A) c) :
    RelSubstAtCov C M R n Δ (EnvT.cons (demandT d) ρ) (EnvT.cons (demandT d) ρ)
      (SubstT.cons N σ) (SubstT.cons N' σ') (.assumption A :: Γ) := by
  have hρ := envTypedCovAtP_cons_assumption hM hSub.envL hAa hd
  refine ⟨cov_typedSubst_cons hSub.typedL hN,
    cov_typedSubst_cons hSub.typedR (.conv _ _ _ _ u hN' hAc),
    cov_convSubst_cons hSub.conv hcN, hρ, hρ, ?_, ?_⟩
  · intro i B hB c hc
    cases i with
    | zero =>
        have he : lift 0 1 A = B := Option.some.inj hB
        subst B
        have hm : c ∈ d := hc.elim id id
        have hcTy := hd c hm
        have hxy := hrel c hm
        have hyx := lrSCoreCov_symm_tm C hL hNU hW hS hT a c hΔ hAA hcTy hxy
        have move : ∀ {x y : Expr Nat},
            LRSCoreCov C R n Δ x y (substT σ A) c →
              LRSCoreCov C R n Δ x y (substT σ' A) c :=
          fun h => lrSCoreCov_irrel C hL hNU hW hS hT a c hΔ hAA' hcTy h
        have comp : ∀ {x y z : Expr Nat},
            LRSCoreCov C R n Δ x y (substT σ A) c →
              LRSCoreCov C R n Δ y z (substT σ A) c →
                LRSCoreCov C R n Δ x z (substT σ A) c :=
          fun hxy hyz => lrSCoreCov_trans_tm C hL hNU hW hS hT a c hΔ hAA hcTy hxy hyz
        simpa only [SubstT.cons_zero, substT_cons_lift] using
          And.intro hxy (And.intro (move hyx) (And.intro (comp hxy hyx) (move (comp hyx hxy))))
    | succ i =>
        obtain ⟨B₀, hB₀, rfl⟩ := cov_lookupType_tail hB
        simpa only [SubstT.cons_succ, substT_cons_lift] using hSub.vars i B₀ hB₀ c hc
  · intro i v B hv hB c hc
    cases i with
    | zero => simp [lookupValue] at hv
    | succ i =>
        obtain ⟨v₀, hv₀, rfl⟩ := cov_lookupValue_tail hv
        obtain ⟨B₀, hB₀, rfl⟩ := cov_lookupType_tail hB
        have hm : ρ i c ∨ ρ i c ∨ M.Ap ρ v₀ c ∨ M.Ap ρ v₀ c := by
          rcases hc with hc | hc | hc | hc
          · exact Or.inl hc
          · exact Or.inr (Or.inl hc)
          · exact Or.inr (Or.inr (Or.inl ((hM.lift ρ _ v₀ c).mp hc)))
          · exact Or.inr (Or.inr (Or.inr ((hM.lift ρ _ v₀ c).mp hc)))
        simpa only [SubstT.cons_succ, substT_cons_lift] using hSub.lets i v₀ B₀ hv₀ hB₀ c hm

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_SUBST_ROOTS
#print axioms relSubstAtCov_nil
#print axioms CovLiftModelLaws
#print axioms covLiftModelLaws_approxT
#print axioms cov_typedSubst_cons
#print axioms cov_convSubst_cons
#print axioms envTypedCovAtP_cons_assumption
#print axioms relSubstAtCov_cons_realized
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_SUBST_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormSubstAudit
