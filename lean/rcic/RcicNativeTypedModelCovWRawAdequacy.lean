import rcic.RcicNativeTypedModelCovWAligned
import rcic.RcicNativeTypedModelCovWValueActions
import rcic.RcicNativeTypedModelCovWArity

/-!
# Operational adequacy of strict raw observations

The induction below follows every constructor of the finite `ApproxTW`
derivation. Its syntactic arity premise is supplied by native typing, and
`EnvWfT` supplies that premise for hidden delta bodies and recursor schemas.
Actual argument expressions enter through parallel substitution and finite
compact demands; no general head or value supplier is assumed.

This module concerns the strict raw relation. It does not assert transport
of guarded K certificates under arbitrary action arguments.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovVAudit

theorem covW_normal_reduct_after_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e e' N : Expr Nat} (hs : WhStepCK2 E n Γ e e')
    (hr : RedR (WhStepCK2 E n) Γ e N) (hn : NormalR (WhStepCK2 E n) Γ N) :
    RedR (WhStepCK2 E n) Γ e' N := by
  cases hr with
  | refl => exact (hn _ hs).elim
  | step ht hr =>
      have he := detR_whStepCK2 hW Γ hs ht
      cases he
      exact hr

theorem covW_normal_reduct_forward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e e' N : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ e e')
    (hN : RedR (WhStepCK2 E n) Γ e N) (hn : NormalR (WhStepCK2 E n) Γ N) :
    RedR (WhStepCK2 E n) Γ e' N := by
  induction hr with
  | refl => exact hN
  | step hs _ ih => exact ih (covW_normal_reduct_after_step hW hs hN hn)

/-- Deterministic transport retains the same normal spine and actual fields. -/
theorem covW_value_action_forward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) (c : CptT) {e e' : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ e e')
    (h : CovWValueAction E n Γ c e) : CovWValueAction E n Γ c e' := by
  cases hc : c with
  | bot => rw [CovWValueAction]; trivial
  | lam rows =>
      simp only [hc, CovWValueAction] at h ⊢
      refine ⟨covV_native_head_forward hW hr h.1, ?_⟩
      intro s hs a ha
      exact covW_value_action_forward hW s.2
        (redR_appHead (readbackLaws_whStepCK2 E n) hr) (h.2 s hs a ha)
  | spine r us =>
      simp only [hc] at h ⊢
      obtain ⟨ls, xs, hh, hn, hx⟩ := covW_value_action_spine_iff.mp h
      exact covW_value_action_spine_iff.mpr
        ⟨ls, xs, covW_normal_reduct_forward hW hr hh (hn xs), hn, hx⟩
  | prop =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨l, hl, hh⟩ := h
      exact ⟨l, hl, covW_normal_reduct_forward hW hr hh (normalR_sortCK2 Γ l)⟩
  | sort =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨l, hl, hh⟩ := h
      exact ⟨l, hl, covW_normal_reduct_forward hW hr hh (normalR_sortCK2 Γ l)⟩
  | pi a rows =>
      simp only [hc, CovWValueAction] at h ⊢
      obtain ⟨D, B, hh⟩ := h
      exact ⟨D, B, covW_normal_reduct_forward hW hr hh (normalR_piCK2 Γ D B)⟩
termination_by sizeOf c
decreasing_by
  simp_wf
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := sizeOfT_snd_lt s
  simp only [hc, CptT.lam.sizeOf_spec]
  omega

theorem CovWListDemands.append {R : CptT → Expr Nat → Prop} :
    ∀ {xs ys : List (Expr Nat)} {uss vss : List (List CptT)},
      CovWListDemands R xs uss → CovWListDemands R ys vss →
      CovWListDemands R (xs ++ ys) (uss ++ vss)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hxs, h => .cons hx (CovWListDemands.append hxs h)

theorem covW_envT_pushArgs_ge (L : List (CptT → Prop)) (ρ : EnvT) {i : Nat}
    (h : L.length ≤ i) : EnvT.pushArgs L ρ i = ρ (i - L.length) := by
  induction L generalizing ρ i with
  | nil => simp only [List.length_nil, Nat.sub_zero]; rfl
  | cons S Ss ih =>
      simp only [EnvT.pushArgs, List.length_cons] at h ⊢
      rw [ih (EnvT.cons S ρ) (Nat.le_trans (Nat.le_succ Ss.length) h)]
      have hj : i - Ss.length = (i - (Ss.length + 1)) + 1 := by omega
      rw [hj]
      rfl

/-- Demand lookup identifies the actual native argument at the same index. -/
theorem covW_demands_push_lookup {R : CptT → Expr Nat → Prop}
    {xs : List (Expr Nat)} {uss : List (List CptT)} (h : CovWListDemands R xs uss) :
    ∀ (ρ : EnvT) (i : Nat), i < xs.length → ∀ u : CptT,
      EnvT.pushArgs (uss.map demandT) ρ i u →
      ∃ x, xs[xs.length - 1 - i]? = some x ∧ R u x := by
  induction h with
  | nil => intro _ i hi; cases hi
  | @cons x xs us uss hx hxs ih =>
      intro ρ i hi u hu
      by_cases hit : i < xs.length
      · obtain ⟨a, hget, ha⟩ := ih (EnvT.cons (demandT us) ρ) i hit u hu
        refine ⟨a, ?_, ha⟩
        have hind : (x :: xs).length - 1 - i = (xs.length - 1 - i) + 1 := by
          simp only [List.length_cons]
          omega
        rw [hind]
        simpa only [List.getElem?_cons_succ] using hget
      · have hie : i = xs.length := by
          simp only [List.length_cons] at hi
          omega
        subst i
        change EnvT.pushArgs (uss.map demandT) (EnvT.cons (demandT us) ρ) xs.length u at hu
        rw [covW_envT_pushArgs_ge _ _ (by
          simpa only [List.length_map] using Nat.le_of_eq hxs.length_eq.symm)] at hu
        simp only [List.length_map, hxs.length_eq, Nat.sub_self] at hu
        exact ⟨x, by simp, hx u hu⟩

/-- The native schema substitution is supplied from its finite argument list. -/
theorem covW_demands_instPrefix_images {R : CptT → Expr Nat → Prop}
    (hbot : ∀ e, R .bot e) {xs : List (Expr Nat)} {uss : List (List CptT)}
    (h : CovWListDemands R xs uss) :
    ∀ i u, EnvT.pushArgs (uss.map demandT) EnvT.bot i u →
      R u (instPrefixSubst xs i) := by
  intro i u hu
  by_cases hi : i < xs.length
  · obtain ⟨x, hget, hx⟩ := covW_demands_push_lookup h EnvT.bot i hi u hu
    have he : instPrefixSubst xs i = x := by
      have he := instPrefix_bvar_lt hi hget
      rw [instPrefix_eq_substT] at he
      exact he
    rw [he]
    exact hx
  · rw [covW_envT_pushArgs_ge _ _ (by
      simpa only [List.length_map, ← h.length_eq] using Nat.le_of_not_gt hi)] at hu
    cases hu
    exact hbot _

/-- Every strict raw observation has its finite operational action, provided
the source constants have their native universe arities. -/
theorem covW_raw_actions {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTW E ρ e c) : CovWConstsArity E e →
    ∀ σ : SubstT,
      (∀ i u, ρ i u → CovWValueAction E n Γ u (σ i)) →
      CovWValueAction E n Γ c (substT σ e) := by
  induction h with
  | bot => intro _ σ _; rw [CovWValueAction]; trivial
  | bvar h => intro _ σ hσ; exact hσ _ _ h
  | sort ρ l =>
      intro _ σ _
      rcases sortCode_prop_or_sort l with hc | hc <;>
        rw [hc, CovWValueAction] <;>
        exact ⟨l, hc, .refl _⟩
  | pi _ _ _ _ _ =>
      intro _ σ _
      rw [CovWValueAction]
      exact ⟨_, _, .refl _⟩
  | @lam ρ A b a rows hA ht hne hb ihA ihb =>
      intro hp σ hσ
      apply covW_value_action_lambda
      intro s hs x hx
      rw [instantiate0_substT_up]
      apply ihb s hs hp.2 (SubstT.cons x σ)
      intro i u hu
      cases i with
      | zero => exact hx u hu
      | succ i => exact hσ i u hu
  | app _ hs _ ihf iha =>
      intro hp σ hσ
      exact covW_value_action_app (ihf hp.1 σ hσ) hs (fun u hu => iha u hu hp.2 σ hσ)
  | const ρ r ls hr hn =>
      intro hp σ _
      obtain ⟨m, hm, _⟩ := hp
      exact covW_value_action_rigid_const hW hm hr ls
  | @delta ρ r ls m b c hd h ih =>
      intro _ σ _
      have hb := ih (covW_consts_arity_levels ls (covW_body_consts_arity hW r m b hd.1 hd.2.1))
        SubstT.id (fun _ u hu => by cases hu; rw [CovWValueAction]; trivial)
      rw [substT_id] at hb
      exact covW_value_action_backward c (redR_single (.ctx (.delta hd.1 hd.2.1))) hb
  | @recursor ρ w ls hnp us_pre us_fields c hpre hflds h ih =>
      intro hp σ _
      obtain ⟨m, hm, hls⟩ := hp
      have hm' : m = w.recMember := Option.some.inj (hm.symm.trans w.hrec)
      subst m
      apply covW_value_action_recursor hW w ls hls hnp hpre hflds
      intro pre fields hps hfs
      have hs := ih (covW_schema_consts_arity hW w ls) (instPrefixSubst (pre ++ fields))
        (covW_demands_instPrefix_images
          (fun _ => by rw [CovWValueAction]; trivial) (hps.append hfs))
      rw [← instPrefix_eq_substT] at hs
      exact hs
  | appSpine _ _ ihf iha =>
      intro hp σ hσ
      exact covW_value_action_app_spine (ihf hp.1 σ hσ) (iha hp.2 σ hσ)
  | @letE ρ A v b c happ ih =>
      intro hp σ hσ
      have ha := ih ⟨⟨hp.1, hp.2.2⟩, hp.2.1⟩ σ hσ
      have hb := covW_value_action_forward hW c
        (redR_single (WhStepCK2.ctx (WhStepCtx.beta
          (substT σ A) (substT σ.up b) (substT σ v)))) ha
      exact covW_value_action_backward c
        (redR_single (.ctx (.zeta (substT σ A) (substT σ v) (substT σ.up b)))) hb
  | @lit ρ t c h ih =>
      intro hp σ hσ
      have hn := ih ((covW_consts_arity_natExpand_iff E t).mpr hp) σ hσ
      rw [Rcic.Declarative.substT_natExpand] at hn
      exact covW_value_action_backward c (redR_single (.ctx (.lit t))) hn

/-- Native typing discharges the only syntax premise of the raw induction. -/
theorem covW_raw_typed_actions {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {ρ : EnvT} {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E ρ e c) (σ : SubstT)
    (hσ : ∀ i u, ρ i u → CovWValueAction E n Δ u (σ i)) :
    CovWValueAction E n Δ c (substT σ e) :=
  covW_raw_actions hW ho (covW_hasTy_consts_arity ht) σ hσ

/-- Bottom-valuation observations require no native image-action hypothesis. -/
theorem covW_raw_closed_actions {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c) :
    CovWValueAction E n Δ c e := by
  have h := covW_raw_typed_actions (Δ := Δ) hW ht ho SubstT.id
    (fun _ u hu => by cases hu; rw [CovWValueAction]; trivial)
  rw [substT_id] at h
  exact h

theorem covW_raw_closed_head {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c) (hc : c ≠ .bot) :
    CovVNativeHead E n Δ e :=
  covW_value_action_head (covW_raw_closed_actions hW ht ho) hc

/-- A universe observation identifies its native sort and its exact code. -/
theorem covW_raw_closed_sort_head {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c)
    (hc : c = .prop ∨ c = .sort) :
    ∃ l : Level, sortCode l = c ∧
      RedR (WhStepCK2 E n) Δ e (.sort l) ∧
      NormalR (WhStepCK2 E n) Δ (.sort l) := by
  have h := covW_raw_closed_actions (Δ := Δ) hW ht ho
  rcases hc with hc | hc <;> subst c
  · rw [CovWValueAction] at h
    obtain ⟨l, hl, hr⟩ := h
    exact ⟨l, hl, hr, normalR_sortCK2 Δ l⟩
  · rw [CovWValueAction] at h
    obtain ⟨l, hl, hr⟩ := h
    exact ⟨l, hl, hr, normalR_sortCK2 Δ l⟩

/-- A Pi observation identifies an actual normal native Pi head. -/
theorem covW_raw_closed_pi_head {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {a : CptT} {rows : List (List CptT × CptT)}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e (.pi a rows)) :
    ∃ D B : Expr Nat, RedR (WhStepCK2 E n) Δ e (.pi D B) ∧
      NormalR (WhStepCK2 E n) Δ (.pi D B) := by
  have h := covW_raw_closed_actions (Δ := Δ) hW ht ho
  rw [CovWValueAction] at h
  obtain ⟨D, B, hr⟩ := h
  exact ⟨D, B, hr, normalR_piCK2 Δ D B⟩

/-- The actual source typing and raw observations supply one constructor
spine, with the demanded actions on that spine's actual fields. -/
theorem covW_raw_closed_ctor_fields {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {r nparams : Nat} {uss : List (List CptT)}
    (ht : HasTyT E n Γ e A)
    (ho : ∀ c ∈ ctorDemandT r nparams uss, ApproxTW E EnvT.bot e c) :
    ∃ (ls : List Level) (params fields : List (Expr Nat)),
      RedR (WhStepCK2 E n) Δ e (foldApps (.const r ls) (params ++ fields)) ∧
      NormalR (WhStepCK2 E n) Δ (foldApps (.const r ls) (params ++ fields)) ∧
      params.length = nparams ∧ fields.length = uss.length ∧
      CovWListDemands (CovWValueAction E n Δ) fields uss :=
  covW_ctor_demand_actual_fields hW
    (fun c hc => covW_raw_closed_actions hW ht (ho c hc))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_RAW_ADEQUACY_ROOTS
#print axioms covW_normal_reduct_after_step
#print axioms covW_normal_reduct_forward
#print axioms covW_value_action_forward
#print axioms CovWListDemands.append
#print axioms covW_envT_pushArgs_ge
#print axioms covW_demands_push_lookup
#print axioms covW_demands_instPrefix_images
#print axioms covW_raw_actions
#print axioms covW_raw_typed_actions
#print axioms covW_raw_closed_actions
#print axioms covW_raw_closed_head
#print axioms covW_raw_closed_sort_head
#print axioms covW_raw_closed_pi_head
#print axioms covW_raw_closed_ctor_fields
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_RAW_ADEQUACY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
