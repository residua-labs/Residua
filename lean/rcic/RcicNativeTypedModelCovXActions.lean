import rcic.RcicNativeTypedModelCovXInterface

/-!
# Ordinary application and atomic case supplies for the extensional candidate

The application theorem consumes a function edge at its actual Pi type.
Compact lambda and rigid-spine applications share this one clause. The
target views come from that edge, not from an unproved global view supplier.
Saturated model computations are not compact applications and remain outside
this theorem. Native alignment of substituted argument types is explicit.

The computation adapter uses a supplied contractum motive. It is not a
claim that a generated contractum derivation is a smaller native child.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelCovRelAudit TypedModelCovNormSubstAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The actual function edge supplies both instantiated codomain views.
No rigid-head test is made on either endpoint. -/
theorem lrSCoreCovX_app_action (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {f f' D B : Expr Nat} {c out : CptT}
    {ds : List CptT} (hf : LRSCoreCovX C R n Γ f f' (.pi D B) c)
    (ha : CovXCompactAction E c ds out)
    (N N' : Expr Nat) (hN : HasTyT E n Γ N D) (hN' : HasTyT E n Γ N' D)
    (hc : Nonempty (ConvT E n Γ N N' D))
    (hd : ∀ u ∈ ds, LRSCoreCovX C R n Γ N N' D u) :
    LRSCoreCovX C R n Γ (.app f N) (.app f' N') (instantiate0 N B) out ∧
    LRSCoreCovX C R n Γ (.app f N) (.app f' N') (instantiate0 N' B) out := by
  rcases hf with hb | ⟨v, hv⟩
  · subst c
    cases ha with
    | bot => exact ⟨lrSCoreCovX_bot C _ _ _ _, lrSCoreCovX_bot C _ _ _ _⟩
  · cases v with
    | sort l hr =>
        exact Expr.noConfusion (redR_of_normal (hL.pi_normal Γ D B) hr)
    | base Z hr hn hs hp => exact (hp ⟨D, B, .refl _⟩).elim
    | pi D' B' hr dom body cod =>
        have he := redR_of_normal (hL.pi_normal Γ D B) hr
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
        have had : ∀ u ∈ ds, LRSCoreCovXAt C dom N N' u :=
          fun u hu => (lrSCoreCovX_iff_at_view C hL hNU dom u).mp (hd u hu)
        obtain ⟨ho, ho'⟩ := hv.2 ds out ha N N' hN hN' hc had
        exact ⟨lrSCoreCovX_of_view C (cod N hN) ho,
          lrSCoreCovX_of_view C (cod N' hN') ho'⟩

/-- A sort leaf may be transported directly from the landed relation once
its normalized compact typing gate has actually been proved. -/
theorem lrSCoreCovX_of_old_sort (C : CovTyping E)
    {Γ : LCtx} {A x y : Expr Nat} {l : Level} {c : CptT}
    (hr : RedR R Γ A (.sort l)) (ht : C.ty c (sortCode l))
    (h : LRSCoreCov C R n Γ x y A c) : LRSCoreCovX C R n Γ x y A c :=
  lrSCoreCovX_of_view C (.sort l hr) ⟨ht, h⟩

/-- At a supplied base view, the old and new relations agree exactly.
This is a local transport, not a global K-free relation equivalence. -/
theorem lrSCoreCovX_base_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A Z x y : Expr Nat} {c : CptT}
    (hr : RedR R Γ A Z) (hn : NormalR R Γ Z)
    (hs : ¬ ∃ l, RedR R Γ A (.sort l))
    (hp : ¬ ∃ D B, RedR R Γ A (.pi D B)) :
    LRSCoreCovX C R n Γ x y A c ↔ LRSCoreCov C R n Γ x y A c :=
  lrSCoreCovX_iff_at_view C hL hNU (.base Z hr hn hs hp) c

private theorem covX_sort_gate (C : CovTyping E) (hS : CovTypingIncludesS C)
    (l : Level) : C.ty (sortCode l) (sortCode (.succ l)) := by
  rw [sortCode_succ]
  rcases sortCode_prop_or_sort l with h | h
  · rw [h]; exact hS _ _ (ctyS_prop_sort E)
  · rw [h]; exact hS _ _ (ctyS_sort_sort E)

/-- Sort is a genuine supply, by composition with the landed sort case in
an empty source context and the supplied normalized sort typing gate. -/
theorem fundCovX_sort (hM : CovAtomicModelLaws M) (hS : CovTypingIncludesS C)
    {Γ : LCtx} (l : Level) : FundTyAtCovX C M R n Γ (.sort l) (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' hΔ _ c hc
  have old := fundCov_sort (C := C) hM (Γ := []) l hΔ
    (relSubstAtCov_nil C M R n Δ ρ ρ' σ σ') c hc
  rcases hc.elim hM.sort_inv hM.sort_inv with rfl | rfl
  · exact lrSCoreCovX_bot C _ _ _ _
  · exact lrSCoreCovX_of_old_sort C (.refl _) (covX_sort_gate C hS l) old

/-- The universe conversion base case also reuses its landed sort clause. -/
theorem fundCovX_sorts (hM : CovAtomicModelLaws M) (hS : CovTypingIncludesS C)
    {Γ : LCtx} (l l' : Level) :
    FundConvAtCovX C M R n Γ (.sort l) (.sort l') (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' hΔ _ c hc
  have old := fundCov_sorts (C := C) hM (Γ := []) l l' hΔ
    (relSubstAtCov_nil C M R n Δ ρ ρ' σ σ') c hc
  have gate : C.ty c (sortCode (.succ l)) := by
    rw [sortCode_succ]
    rcases hc with ho | ho
    · rcases hM.sort_inv ho with rfl | rfl
      · exact C.bot _
      · simpa only [sortCode_succ] using covX_sort_gate C hS l
    · rcases hM.sort_inv ho with rfl | rfl
      · exact C.bot _
      · simpa only [sortCode_succ] using covX_sort_gate C hS l'
  exact lrSCoreCovX_of_old_sort C (.refl _) gate old

/-- Relation-side expansion consumes only forward model contraction.
The full target motive is explicit and is not called a recursive child. -/
theorem fundConvAtCovX_of_model_contract (hL : ReadbackLaws E R)
    {Γ : LCtx} {src dst A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ src c → M.Ap ρ dst c)
    (hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ src) (substT σ dst))
    (htarget : FundTyAtCovX C M R n Γ dst A) : FundConvAtCovX C M R n Γ src dst A := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact lrSCoreCovX_expand_red_both C hL (hread hΔ hSub) (.refl _)
    (htarget hΔ hSub c (hc.elim (fun h => Or.inl (hpres ρ c h)) Or.inr))

/-- The beta readback itself is supplied by the landed readback laws.
Forward model contraction and a complete contractum motive remain inputs. -/
theorem fundConvAtCovX_beta_of_model_contract (hL : ReadbackLaws E R)
    {Γ : LCtx} {D body arg A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ (.app (.lam D body) arg) c →
      M.Ap ρ (instantiate0 arg body) c)
    (htarget : FundTyAtCovX C M R n Γ (instantiate0 arg body) A) :
    FundConvAtCovX C M R n Γ (.app (.lam D body) arg) (instantiate0 arg body) A := by
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ (.app (.lam D body) arg))
        (substT σ (instantiate0 arg body)) := by
    intro Δ ρ ρ' σ σ' _ _
    simpa only [substT, substT_instantiate0] using
      redR_single (hL.beta Δ (substT σ D) (substT σ.up body) (substT σ arg))
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundConvAtCovX_of_model_contract hL hpres hread htarget hΔ hSub c hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ACTIONS_ROOTS
#print axioms lrSCoreCovX_app_action
#print axioms lrSCoreCovX_of_old_sort
#print axioms lrSCoreCovX_base_iff
#print axioms fundCovX_sort
#print axioms fundCovX_sorts
#print axioms fundConvAtCovX_of_model_contract
#print axioms fundConvAtCovX_beta_of_model_contract
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ACTIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
