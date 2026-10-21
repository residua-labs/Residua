import rcic.RcicNativeTypedModelCovPRealization
import rcic.RcicNativeTypedModelCovZNeutralBody

/-!
# The exact-leaf and empty-action boundary after a typing repair

These are eliminations of the new, typing-parametric hereditary target.
Only the bottom inversion law of the supplied typing is used. In particular,
changing proposition evidence or adding rigid reflection cannot remove this
boundary while the native readback, exact leaves and empty actions stay fixed.
No new relation, native derivation, model rule or axiom is postulated.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit ReadbackCK2Audit
open TypedModelCovXAudit

variable {E : ResolvedEnv} {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}

/-- The normal neutral obstruction uses only bottom inversion and the exact
native leaf observation, independently of proposition classification. -/
theorem covP_hereditary_normal_bot_only
    (hbot : ∀ {u}, T u .bot → u = .bot)
    (Q : LCtx → CtxModelT E) (R : Readback) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (hn : NormalR R Γ A) (hnp : ∀ D B, A ≠ .pi D B)
    (hm : ∀ b, (Q Γ).Ap ρ A b → b = .bot) :
    ∀ b, HereditaryCovRealizationPAt T Rel Q R n Γ ρ A c b → c = .bot := by
  intro b h
  rw [HereditaryCovRealizationPAt.eq_def] at h
  cases b with
  | bot => exact hbot h.1
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

theorem covP_hereditary_bvar_bot_only
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {i : Nat} {c : CptT}
    (hv : lookupValue Γ i = none) (hρ : ∀ b, ρ i b → b = .bot) :
    ∀ b, HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.bvar i) c b → c = .bot := by
  apply covP_hereditary_normal_bot_only hbot (ctxModelT_approxTK E n)
    (WhStepCK2 E n) n (normalR_bvarCK2 hv)
    (fun _ _ he => Expr.noConfusion he)
  intro b ho
  rcases approxTK_bvar_inv ho with hb | hb
  · exact hb
  · exact hρ b hb

theorem covP_not_hereditary_empty_head
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (D : Expr Nat) (c : CptT) (hc : c ≠ .bot) :
    ∀ b, ¬ HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n (.assumption D :: Γ)
      (EnvT.cons (demandT []) ρ) (.bvar 0) c b := by
  intro b hb
  apply hc
  exact covP_hereditary_bvar_bot_only hbot n (by rfl)
    (fun u hu => (List.not_mem_nil u hu).elim) b hb

/-- A non-bottom value at a syntactic native Pi must use a Pi type code. -/
theorem covP_hereditary_pi_code
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {D B : Expr Nat} {c a : CptT}
    (hc : c ≠ .bot)
    (h : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi D B) c a) :
    ∃ d g, a = .pi d g := by
  rw [HereditaryCovRealizationPAt.eq_def] at h
  cases a with
  | bot => exact (hc (hbot h.1)).elim
  | pi d g => exact ⟨d, g, rfl⟩
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
      · exact (hc hb).elim
      · have he := redR_of_normal (normalR_piCK2 Γ D B) hr
        subst A₀
        rcases approxTK_pi_inv ho with hb | ⟨d, g, he, _⟩
        · cases hb
        · cases he

/-- Exact observation fixes the code at the native universe Prop. -/
theorem covP_hereditary_sort_zero_code
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {c a : CptT} (hc : c ≠ .bot)
    (h : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.sort .zero) c a) : a = .prop := by
  rw [HereditaryCovRealizationPAt.eq_def] at h
  cases a with
  | bot => exact (hc (hbot h.1)).elim
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, hr, _⟩
      · exact (hc hb).elim
      · have he := redR_of_normal (normalR_sortCK2 Γ .zero) hr
        exact Expr.noConfusion he
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
      · exact (hc hb).elim
      · have he := redR_of_normal (normalR_sortCK2 Γ .zero) hr
        subst A₀
        rcases approxTK_sort_inv ho with hb | he
        · cases hb
        · simpa only [sortCode_zero] using he

/-- The same code cannot be an exact leaf at Sort 0 and a Pi code at a
normal native function type. No proposition-collapse law occurs here. -/
theorem covP_not_hereditary_sort_pi_same_code
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {D B : Expr Nat} {c a : CptT} (hc : c ≠ .bot)
    (hs : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.sort .zero) c a)
    (hp : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi D B) c a) : False := by
  have he := covP_hereditary_sort_zero_code hbot n hc hs
  obtain ⟨d, g, hg⟩ := covP_hereditary_pi_code hbot n hc hp
  rw [he] at hg
  exact CptT.noConfusion hg

/-- Empty-demand coverage chooses one row before the native argument is
chosen. Every actual native inhabitant then has the same result code. Both
the binder-body and instantiated-codomain obligations are retained. -/
theorem covP_hereditary_empty_pi_step
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {D B : Expr Nat} {r : Nat} {us : List CptT} {a : CptT}
    (h : HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi D B) (.spine r us) a) :
    ∃ b, ∀ N, HasTyT E n Γ N D →
      HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
        (WhStepCK2 E n) n (.assumption D :: Γ)
        (EnvT.cons (demandT []) ρ) B (.spine r (us ++ [.bot])) b ∧
      HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
        (WhStepCK2 E n) n Γ ρ (instantiate0 N B) (.spine r (us ++ [.bot])) b := by
  obtain ⟨d, g, rfl⟩ := covP_hereditary_pi_code hbot n
    (fun he => CptT.noConfusion he) h
  rw [HereditaryCovRealizationPAt.eq_def] at h
  rcases h.2 with hb | ⟨D', B', hr, hcover, hact⟩
  · exact CptT.noConfusion hb
  · have he := redR_of_normal (normalR_piCK2 Γ D B) hr
    obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
    have ha : CovXCompactAction E (.spine r us) []
        (.spine r (us ++ [.bot])) := AppCptT.appSpine (.bot _ _)
    have hnb : (CptT.spine r (us ++ [.bot])) ≠ .bot :=
      fun he => CptT.noConfusion he
    rcases hcover [] _ ha (fun u hu => (List.not_mem_nil u hu).elim) with
      hb | ⟨row, hrow, hs⟩
    · exact (hnb hb).elim
    · refine ⟨row.2, ?_⟩
      intro N hN
      have hx := hact [] _ ha hnb row hrow hs N N hN hN
        ⟨.refl _ _ _ hN⟩ (fun u hu => (List.not_mem_nil u hu).elim)
      exact ⟨hx.2.1, hx.2.2.1⟩

/-- The landed NeutralBody argument replays for arbitrary repaired typing
and demand relations. Its only typing hypothesis is bottom inversion. -/
theorem covP_not_hereditary_poly_result_spine
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ b, ¬ HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (.pi (.sort (.succ .zero)) (.bvar 0))
      (.spine r us) b := by
  intro b h
  obtain ⟨a, ha⟩ := covP_hereditary_empty_pi_step hbot n h
  have hx := (ha (.sort .zero) (.sort Γ .zero)).1
  exact covP_not_hereditary_empty_head hbot n Γ ρ (.sort (.succ .zero))
    (.spine r (us ++ [.bot])) (fun he => CptT.noConfusion he) a hx

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_NEUTRAL_ROOTS
#print axioms covP_hereditary_normal_bot_only
#print axioms covP_hereditary_bvar_bot_only
#print axioms covP_not_hereditary_empty_head
#print axioms covP_hereditary_pi_code
#print axioms covP_hereditary_sort_zero_code
#print axioms covP_not_hereditary_sort_pi_same_code
#print axioms covP_hereditary_empty_pi_step
#print axioms covP_not_hereditary_poly_result_spine
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_NEUTRAL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
