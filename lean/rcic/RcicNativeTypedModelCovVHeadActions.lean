import rcic.RcicNativeTypedModelCovVRealized

/-!
# Finite operational actions and the lambda fragment of head soundness

The operational relation recurses on the observed compact. A lambda row is
tested against actual native arguments satisfying its finite demands. A spine
records head normalization under arbitrary future arguments. This last property
is deliberately weaker than constructor-field provenance, so the theorem in
this module is confined to the displayed literal lambda/Π/sort/application/let
fragment. It does not assert the general recursor head supplier.

All interpretations and argument quantifiers are Prop-valued. Native reduction
transport uses the landed CK2 laws and determinism. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit ReadbackCK2Audit

def CovVNativeHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∃ N, RedR (WhStepCK2 E n) Γ e N ∧ NormalR (WhStepCK2 E n) Γ N

/-- The finite recursion is paid only by row demands and row outputs. Native
application results are parameters, never recursive measures. -/
def CovVActionRealization (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e : Expr Nat) : Prop :=
  match c with
  | .bot => True
  | .lam rows => CovVNativeHead E n Γ e ∧
      ∀ s ∈ rows, ∀ a : Expr Nat,
        (∀ u ∈ s.1, CovVActionRealization E n Γ u a) →
        CovVActionRealization E n Γ s.2 (.app e a)
  | .spine _ _ => ∀ args : List (Expr Nat),
      CovVNativeHead E n Γ (foldApps e args)
  | .prop => CovVNativeHead E n Γ e
  | .sort => CovVNativeHead E n Γ e
  | .pi _ _ => CovVNativeHead E n Γ e
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    first
    | (have hu := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have hd := sizeOfT_fst_lt s
       omega)
    | (have ho := sizeOfT_snd_lt s
       omega)

theorem covV_native_head_backward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' : Expr Nat} (hred : RedR (WhStepCK2 E n) Γ e e')
    (h : CovVNativeHead E n Γ e') : CovVNativeHead E n Γ e := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N, redR_trans hred hr, hn⟩

theorem covV_native_head_after_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' : Expr Nat} (hW : EnvWfT E) (hs : WhStepCK2 E n Γ e e')
    (h : CovVNativeHead E n Γ e) : CovVNativeHead E n Γ e' := by
  obtain ⟨N, hr, hn⟩ := h
  cases hr with
  | refl => exact (hn _ hs).elim
  | step hs' hr =>
      have he := detR_whStepCK2 hW Γ hs hs'
      cases he
      exact ⟨N, hr, hn⟩

theorem covV_native_head_forward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' : Expr Nat} (hW : EnvWfT E)
    (hred : RedR (WhStepCK2 E n) Γ e e')
    (h : CovVNativeHead E n Γ e) : CovVNativeHead E n Γ e' := by
  induction hred with
  | refl => exact h
  | step hs _ ih => exact ih (covV_native_head_after_step hW hs h)

theorem covV_redR_foldApps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' : Expr Nat} (hred : RedR (WhStepCK2 E n) Γ e e')
    (args : List (Expr Nat)) :
    RedR (WhStepCK2 E n) Γ (foldApps e args) (foldApps e' args) := by
  induction args generalizing e e' with
  | nil => exact hred
  | cons a args ih => exact ih (redR_appHead (readbackLaws_whStepCK2 E n) hred)

theorem covV_action_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e : Expr Nat} (h : CovVActionRealization E n Γ c e)
    (hc : c ≠ .bot) : CovVNativeHead E n Γ e := by
  cases c with
  | bot => exact (hc rfl).elim
  | lam rows => rw [CovVActionRealization] at h; exact h.1
  | spine r us => rw [CovVActionRealization] at h; exact h []
  | prop => rw [CovVActionRealization] at h; exact h
  | sort => rw [CovVActionRealization] at h; exact h
  | pi a rows => rw [CovVActionRealization] at h; exact h

theorem covV_action_backward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (c : CptT) {e e' : Expr Nat} (hred : RedR (WhStepCK2 E n) Γ e e')
    (h : CovVActionRealization E n Γ c e') : CovVActionRealization E n Γ c e := by
  cases hc : c with
  | bot => rw [CovVActionRealization]; trivial
  | lam rows =>
      simp only [hc, CovVActionRealization] at h ⊢
      refine ⟨covV_native_head_backward hred h.1, ?_⟩
      intro s hs a ha
      exact covV_action_backward s.2
        (redR_appHead (readbackLaws_whStepCK2 E n) hred) (h.2 s hs a ha)
  | spine r us =>
      simp only [hc, CovVActionRealization] at h ⊢
      intro args
      exact covV_native_head_backward (covV_redR_foldApps hred args) (h args)
  | prop => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_backward hred h
  | sort => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_backward hred h
  | pi a rows => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_backward hred h
termination_by sizeOf c
decreasing_by
  simp_wf
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := sizeOfT_snd_lt s
  simp only [hc, CptT.lam.sizeOf_spec]
  omega

theorem covV_action_forward {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) (c : CptT) {e e' : Expr Nat}
    (hred : RedR (WhStepCK2 E n) Γ e e')
    (h : CovVActionRealization E n Γ c e) : CovVActionRealization E n Γ c e' := by
  cases hc : c with
  | bot => rw [CovVActionRealization]; trivial
  | lam rows =>
      simp only [hc, CovVActionRealization] at h ⊢
      refine ⟨covV_native_head_forward hW hred h.1, ?_⟩
      intro s hs a ha
      exact covV_action_forward hW s.2
        (redR_appHead (readbackLaws_whStepCK2 E n) hred) (h.2 s hs a ha)
  | spine r us =>
      simp only [hc, CovVActionRealization] at h ⊢
      intro args
      exact covV_native_head_forward hW (covV_redR_foldApps hred args) (h args)
  | prop => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_forward hW hred h
  | sort => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_forward hW hred h
  | pi a rows => simp only [hc, CovVActionRealization] at h ⊢; exact covV_native_head_forward hW hred h
termination_by sizeOf c
decreasing_by
  simp_wf
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := sizeOfT_snd_lt s
  simp only [hc, CptT.lam.sizeOf_spec]
  omega

/-- A lambda action is supplied by actual beta steps, for every native argument
whose finite row demands are realized. -/
theorem covV_action_lambda {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b : Expr Nat} {rows : List (List CptT × CptT)}
    (hb : ∀ s ∈ rows, ∀ a : Expr Nat,
      (∀ u ∈ s.1, CovVActionRealization E n Γ u a) →
      CovVActionRealization E n Γ s.2 (instantiate0 a b)) :
    CovVActionRealization E n Γ (.lam rows) (.lam A b) := by
  rw [CovVActionRealization]
  refine ⟨⟨_, .refl _, normalR_lamCK2 Γ A b⟩, ?_⟩
  intro s hs a ha
  exact covV_action_backward s.2 (redR_single (.ctx (.beta A b a))) (hb s hs a ha)

theorem covV_action_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {rows : List (List CptT × CptT)} {s : List CptT × CptT}
    (hf : CovVActionRealization E n Γ (.lam rows) f) (hs : s ∈ rows)
    (ha : ∀ u ∈ s.1, CovVActionRealization E n Γ u a) :
    CovVActionRealization E n Γ s.2 (.app f a) := by
  rw [CovVActionRealization] at hf
  exact hf.2 s hs a ha

theorem covV_action_app_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
    (hf : CovVActionRealization E n Γ (.spine r args) f) :
    CovVActionRealization E n Γ (.spine r (args ++ [u])) (.app f a) := by
  rw [CovVActionRealization] at hf ⊢
  intro xs
  exact hf (a :: xs)

/-- A declared body-free non-recursor has native normal spines at every arity. -/
theorem covV_body_free_spine_normal {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    (hb : m.body = none) (hnr : m.mclass ≠ .recursorM)
    (ls : List Level) (args : List (Expr Nat)) :
    NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args) := by
  intro e hs
  rcases whStepCK2_ctx_or_saturated hs with hc | hc
  · exact whStepRecCtx_rigidNonRec_false hm hb hnr ls args
      (whStepCtx_to_whStepRecCtx hc)
  · exact hnr (saturatedRecSource_spine hm hc).1

/-- This supplies the operational constant case for every actual rigid member,
including constructors. The declaration and environment evidence are explicit. -/
theorem covV_action_rigid_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : RigidConst E r) (ls : List Level) :
    CovVActionRealization E n Γ (.spine r []) (.const r ls) := by
  obtain ⟨hb, hnr⟩ := hr m hm
  have hb' : m.body = none := by
    rcases hb with hb | hc
    · exact hb
    · exact ctorNoBody_of_envWfT hW r m hm hc
  rw [CovVActionRealization]
  intro args
  exact ⟨_, .refl _, covV_body_free_spine_normal hm hb' hnr ls args⟩

/-- A finite curried table ending at bottom needs native heads only at proper
argument prefixes. Its final action imposes no normalization on the body. -/
theorem covV_action_curry_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (uss : List (List CptT)) (f : Expr Nat)
    (hp : ∀ args : List (Expr Nat), args.length < uss.length →
      CovVNativeHead E n Γ (foldApps f args)) :
    CovVActionRealization E n Γ (curryStepT uss .bot) f := by
  induction uss generalizing f with
  | nil => rw [curryStepT, CovVActionRealization]; trivial
  | cons us uss ih =>
      rw [curryStepT, CovVActionRealization]
      refine ⟨hp [] (by simp), ?_⟩
      intro s hs a _
      have he : s = (us, curryStepT uss .bot) := List.mem_singleton.mp hs
      subst s
      apply ih (Expr.app f a)
      intro args hlen
      exact hp (a :: args) (by simpa only [List.length_cons] using Nat.succ_lt_succ hlen)

/-- The proper prefixes of an actual recursor supply this action realization
without any K guard, canon typing, or normalization hypothesis for its major. -/
theorem covV_action_recursor_bottom {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .recursorM)
    (ls : List Level) (uss : List (List CptT))
    (hlen : uss.length = piCount m.mtype) :
    CovVActionRealization E n Γ (curryStepT uss .bot) (.const r ls) := by
  apply covV_action_curry_bot
  intro args hp
  exact ⟨_, .refl _, normalR_recPrefixCK2 hW hm hr Γ ls args (by rw [← hlen]; omega)⟩

/-- Literal weak-head syntax handled without any recursor simulation port.
Annotations and literal Π children are inert for native head reduction. -/
def CovVLambdaFragment : Expr Nat → Prop
  | .bvar _ | .sort _ | .pi _ _ => True
  | .lam _ b => CovVLambdaFragment b
  | .app f a => CovVLambdaFragment f ∧ CovVLambdaFragment a
  | .letE _ v b => CovVLambdaFragment v ∧ CovVLambdaFragment b
  | .const _ _ | .lit _ => False

/-- The strengthened induction carries actual native images of all semantic
demands. It supplies action realization throughout the literal lambda fragment,
not merely head existence for a selected fixture. -/
theorem covV_lambda_fragment_actions {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTN E ρ e c) : CovVLambdaFragment e →
    ∀ σ : SubstT,
      (∀ i u, ρ i u → CovVActionRealization E n Γ u (σ i)) →
      CovVActionRealization E n Γ c (substT σ e) := by
  induction h with
  | bot => intro _ σ _; rw [CovVActionRealization]; trivial
  | bvar h => intro _ σ hσ; exact hσ _ _ h
  | sort ρ l =>
      intro _ σ _
      rcases sortCode_prop_or_sort l with hc | hc <;>
        rw [hc, CovVActionRealization] <;>
        exact ⟨_, .refl _, normalR_sortCK2 Γ l⟩
  | pi _ _ _ _ _ =>
      intro _ σ _
      rw [CovVActionRealization]
      exact ⟨_, .refl _, normalR_piCK2 Γ _ _⟩
  | @lam ρ A b a rows hA ht hne hb ihA ihb =>
      intro hp σ hσ
      apply covV_action_lambda
      intro s hs x hx
      rw [instantiate0_substT_up]
      apply ihb s hs hp (SubstT.cons x σ)
      intro i u hu
      cases i with
      | zero => exact hx u hu
      | succ i => exact hσ i u hu
  | app _ hs _ ihf iha =>
      intro hp σ hσ
      exact covV_action_app (ihf hp.1 σ hσ) hs (fun u hu => iha u hu hp.2 σ hσ)
  | const => intro hp; cases hp
  | delta => intro hp; cases hp
  | recursor => intro hp; cases hp
  | recursorProp => intro hp; cases hp
  | appSpine _ _ ihf iha =>
      intro hp σ hσ
      exact covV_action_app_spine (ihf hp.1 σ hσ)
  | @letE ρ A v b c happ ih =>
      intro hp σ hσ
      have ha := ih ⟨hp.2, hp.1⟩ σ hσ
      have hb := covV_action_forward hW c
        (redR_single (WhStepCK2.ctx (WhStepCtx.beta
          (substT σ A) (substT σ.up b) (substT σ v)))) ha
      exact covV_action_backward c
        (redR_single (.ctx (.zeta (substT σ A) (substT σ v) (substT σ.up b)))) hb
  | lit => intro hp; cases hp

/-- Closed bottom-valuation observations in this fragment have actual native
heads. This is an unconditional fragment supplier; arbitrary recursors are
outside its syntax premise. -/
theorem covV_lambda_fragment_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e : Expr Nat} {c : CptT}
    (hp : CovVLambdaFragment e) (h : ApproxTN E EnvT.bot e c) (hc : c ≠ .bot) :
    CovVNativeHead E n Γ e := by
  have hr := covV_lambda_fragment_actions (n := n) (Γ := Γ) hW h hp SubstT.id
    (fun _ u hu => by cases hu; rw [CovVActionRealization]; trivial)
  rw [substT_id] at hr
  exact covV_action_head hr hc

/-- This is the corresponding realized-instance head supplier, with the exact
remaining syntax restriction exposed. Original observations are transported
through the actual aligned realizer before the finite action induction. -/
theorem covV_realized_lambda_fragment_head {E : ResolvedEnv} {n stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} (hW : EnvWfT E)
    (hσ : CovVRealized E n stage Γ ρ σ) {A : Expr Nat} {c : CptT}
    (hp : CovVLambdaFragment (substT σ A))
    (ho : ApproxTKN E n Γ ρ A c) (hc : c ≠ .bot) :
    CovVNativeHead E n [] (substT σ A) :=
  covV_lambda_fragment_head hW hp (hσ.approxTN (approxTKN_forgetN ho)) hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_HEAD_ACTIONS_ROOTS
#print axioms CovVNativeHead
#print axioms CovVActionRealization
#print axioms covV_native_head_backward
#print axioms covV_native_head_after_step
#print axioms covV_native_head_forward
#print axioms covV_redR_foldApps
#print axioms covV_action_head
#print axioms covV_action_backward
#print axioms covV_action_forward
#print axioms covV_action_lambda
#print axioms covV_action_app
#print axioms covV_action_app_spine
#print axioms covV_body_free_spine_normal
#print axioms covV_action_rigid_const
#print axioms covV_action_curry_bot
#print axioms covV_action_recursor_bottom
#print axioms CovVLambdaFragment
#print axioms covV_lambda_fragment_actions
#print axioms covV_lambda_fragment_head
#print axioms covV_realized_lambda_fragment_head
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_HEAD_ACTIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
