import rcic.RcicNativeTypedModelCovYRealization

/-!
# A normal neutral type with no non-bottom observation has no realizing code

This is an ALL-code statement, not failure at one caller-chosen code. A Pi
code would require the normal neutral to read back to Pi; a non-Pi code
would require an actual non-bottom observation of that neutral. Bottom's
typing gate admits only bottom values. The proof only composes the landed
realization definition, readback normality, and model inversion.

The empty-demand binder instance identifies the precise obligation that a
rigid empty-demand action can expose. Concrete typed witnesses are supplied
separately; this generic lemma is not a global model counterexample by itself.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit ReadbackCK2Audit
open TypedModelCovRelAudit TypedModelCovYAudit

/-- Every possible compact code is excluded for a non-bottom value at a
normal non-Pi native type whose only model observation is bottom. -/
theorem covZ_hereditary_normal_bot_only (C : CovTyping E)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (hn : NormalR R Γ A) (hnp : ∀ D B, A ≠ .pi D B)
    (hm : ∀ b, (Q Γ).Ap ρ A b → b = .bot) :
    ∀ b, HereditaryCovRealizationYAt C Q R n Γ ρ A c b → c = .bot := by
  intro b h
  rw [HereditaryCovRealizationYAt.eq_def] at h
  cases b with
  | bot => exact C.bot_inv h.1
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, _⟩
      · exact hb
      · exact (hnp D B (redR_of_normal hn hr).symm).elim
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
      · exact hb
      · have he := redR_of_normal hn hr
        subst A₀
        have he := hm _ ho
        cases he

/-- The neutral-variable instance uses the unchanged CK2 readback and
ApproxTK inversion. Its environment premise is about actual observations. -/
theorem covZ_hereditary_bvar_bot_only (C : CovTyping E) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {i : Nat} {c : CptT}
    (hv : lookupValue Γ i = none) (hρ : ∀ b, ρ i b → b = .bot) :
    ∀ b, HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.bvar i) c b → c = .bot := by
  apply covZ_hereditary_normal_bot_only C (ctxModelT_approxTK E n)
    (WhStepCK2 E n) n (normalR_bvarCK2 hv)
    (fun _ _ he => Expr.noConfusion he)
  intro b ho
  rcases approxTK_bvar_inv ho with hb | hb
  · exact hb
  · exact hρ b hb

/-- In particular, extending by an empty demand supplies no realizing
code for a non-bottom output at the binder variable itself. -/
theorem covZ_not_hereditary_empty_head (C : CovTyping E) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (D : Expr Nat) (c : CptT) (hc : c ≠ .bot) :
    ∀ b, ¬ HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n (.assumption D :: Γ)
      (EnvT.cons (demandT []) ρ) (.bvar 0) c b := by
  intro b hb
  apply hc
  exact covZ_hereditary_bvar_bot_only C n (by rfl)
    (fun u hu => (List.not_mem_nil u hu).elim) b hb

/-- A rigid empty-demand action at `Pi (Sort 1) (bvar 0)` forces precisely
the impossible binder-body realization above. This excludes ALL type codes,
not just Pi codes or codes reached by a particular synthesis algorithm. -/
theorem covZ_not_hereditary_poly_result_spine (C : CovTyping E) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ b, ¬ HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi (.sort (.succ .zero)) (.bvar 0))
      (.spine r us) b := by
  intro b h
  rw [HereditaryCovRealizationYAt.eq_def] at h
  cases b with
  | bot => exact CptT.noConfusion (C.bot_inv h.1)
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, hcover, hact⟩
      · exact CptT.noConfusion hb
      · have he := redR_of_normal
          (normalR_piCK2 (E := E) (n := n) Γ (.sort (.succ .zero)) (.bvar 0)) hr
        obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
        have ha : TypedModelCovXAudit.CovXCompactAction E (.spine r us) []
            (.spine r (us ++ [.bot])) := AppCptT.appSpine (.bot _ _)
        have hnb : (CptT.spine r (us ++ [.bot])) ≠ .bot :=
          fun he => CptT.noConfusion he
        rcases hcover [] _ ha (fun u hu => (List.not_mem_nil u hu).elim) with
          hb | ⟨row, hrow, hs⟩
        · exact hnb hb
        · have ht : HasTyT E n Γ (.sort .zero) (.sort (.succ .zero)) :=
            .sort Γ .zero
          have hb := hact [] _ ha hnb row hrow hs (.sort .zero) (.sort .zero)
            ht ht ⟨.refl _ _ _ ht⟩ (fun u hu => (List.not_mem_nil u hu).elim)
          exact covZ_not_hereditary_empty_head C n Γ ρ (.sort (.succ .zero))
            (.spine r (us ++ [.bot])) hnb row.2 hb.2.1
  | prop | sort | lam g | spine s vs =>
      rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
      · exact CptT.noConfusion hb
      · have he := redR_of_normal
          (normalR_piCK2 (E := E) (n := n) Γ (.sort (.succ .zero)) (.bvar 0)) hr
        subst A₀
        rcases approxTK_pi_inv ho with hb | ⟨a, f, he, _⟩
        · cases hb
        · cases he

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_NEUTRAL_BODY_ROOTS
#print axioms covZ_hereditary_normal_bot_only
#print axioms covZ_hereditary_bvar_bot_only
#print axioms covZ_not_hereditary_empty_head
#print axioms covZ_not_hereditary_poly_result_spine
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_NEUTRAL_BODY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit
