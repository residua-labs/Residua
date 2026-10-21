import rcic.RcicNativeTypedModelCovWRawAdequacy

/-!
# Native typed tests for finite CovW actions

`CovWTypedAction` is a type-indexed interface.  Every action retains the
actual native typing of its term.  At a lambda compact, a test supplies an
actual native Pi typing of that same term, an actual raw observation of its
native domain, compact typing at that domain code, and a native argument
typed at that domain.  Its demanded argument actions are recursively the new
actions.  A native value head is never treated as evidence for a Pi type.

`covWTyped_rawAction` is a separate, bounded interface: its negative argument
premises remain the stronger landed `CovWValueAction` premises.  The positive
outputs and spine fields use its new finite recursion.  The constructive
adapter from landed actions applies only to this bounded interface.  Replacing
its negative premises by the exact recursive action is a contravariant change
and is not justified by that adapter.

The domain observation in a test is an observation of the actual native
domain expression, under the bottom valuation.  The definitions do not claim
that an arbitrary lambda compact supplies either a Pi type or a domain code.
When the indexed native type is already a Pi, the application theorems use
the stored source typing to discharge the Pi-typing premise directly.

Only the exact interface's elimination laws and the bounded interface's raw
supplier are proved here.  General raw adequacy for the exact interface and
guarded adequacy are not claimed.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovVAudit TypedModelCovWAudit

/-- The exact recursive action.  Native typing is required at every lambda
test; the outer type index is retained separately by `CovWTypedAction`. -/
def covWTyped_actionCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e : Expr Nat) : Prop :=
  match c with
  | .bot => True
  | .lam rows => CovVNativeHead E n Γ e ∧
      ∀ D B : Expr Nat, HasTyT E n Γ e (.pi D B) →
        ∀ d : CptT, ApproxTW E EnvT.bot D d →
          ∀ s ∈ rows, (∀ u ∈ s.1, CTyS E u d) →
            ∀ x : Expr Nat, HasTyT E n Γ x D →
              (∀ u ∈ s.1, covWTyped_actionCore E n Γ u x) →
              covWTyped_actionCore E n Γ s.2 (.app e x)
  | .spine r us => ∃ (ls : List Level) (xs : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
      (∀ args : List (Expr Nat),
        NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args)) ∧
      xs.length = us.length ∧
      ∀ i (hi : i < us.length),
        covWTyped_actionCore E n Γ us[i] (xs.getD i (.bvar 0))
  | .prop => ∃ l : Level, sortCode l = .prop ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .sort => ∃ l : Level, sortCode l = .sort ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .pi _ _ => ∃ D B : Expr Nat,
      RedR (WhStepCK2 E n) Γ e (.pi D B)
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  · have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    have hu := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have hd := sizeOfT_fst_lt s
    omega
  · have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    have ho := sizeOfT_snd_lt s
    omega
  · have hu := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›)
    omega

/-- The exact action retains the term's actual native type. -/
def CovWTypedAction (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e A : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ e A) ∧ covWTyped_actionCore E n Γ c e

theorem covWTyped_action_typing {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e A : Expr Nat} (h : CovWTypedAction E n Γ c e A) :
    Nonempty (HasTyT E n Γ e A) := h.1

theorem covWTyped_action_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (ht : HasTyT E n Γ e A) :
    CovWTypedAction E n Γ .bot e A := by
  exact ⟨⟨ht⟩, by rw [covWTyped_actionCore]; trivial⟩

/-- The indexed Pi type supplies the native domain used by the test.  The
argument's native type and demanded actions refer to that same domain. -/
theorem covWTyped_action_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f x D B : Expr Nat} {rows : List (List CptT × CptT)}
    {s : List CptT × CptT} {d : CptT}
    (hf : CovWTypedAction E n Γ (.lam rows) f (.pi D B))
    (hD : ApproxTW E EnvT.bot D d) (hs : s ∈ rows)
    (hd : ∀ u ∈ s.1, CTyS E u d)
    (hx : HasTyT E n Γ x D)
    (ha : ∀ u ∈ s.1, CovWTypedAction E n Γ u x D) :
    CovWTypedAction E n Γ s.2 (.app f x) (instantiate0 x B) := by
  obtain ⟨ht, hf⟩ := hf
  obtain ⟨ht⟩ := ht
  rw [covWTyped_actionCore] at hf
  exact ⟨⟨.app Γ f x D B ht hx⟩,
    hf.2 D B ht d hD s hs hd x hx (fun u hu => (ha u hu).2)⟩

theorem covWTyped_action_core_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e : Expr Nat} (h : covWTyped_actionCore E n Γ c e)
    (hc : c ≠ .bot) : CovVNativeHead E n Γ e := by
  cases c with
  | bot => exact (hc rfl).elim
  | lam rows => rw [covWTyped_actionCore] at h; exact h.1
  | spine r us =>
      rw [covWTyped_actionCore] at h
      obtain ⟨ls, xs, hr, hn, _⟩ := h
      exact ⟨_, hr, hn xs⟩
  | prop =>
      rw [covWTyped_actionCore] at h
      obtain ⟨l, _, hr⟩ := h
      exact ⟨_, hr, normalR_sortCK2 Γ l⟩
  | sort =>
      rw [covWTyped_actionCore] at h
      obtain ⟨l, _, hr⟩ := h
      exact ⟨_, hr, normalR_sortCK2 Γ l⟩
  | pi a rows =>
      rw [covWTyped_actionCore] at h
      obtain ⟨D, B, hr⟩ := h
      exact ⟨_, hr, normalR_piCK2 Γ D B⟩

theorem covWTyped_action_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e A : Expr Nat} (h : CovWTypedAction E n Γ c e A)
    (hc : c ≠ .bot) : CovVNativeHead E n Γ e :=
  covWTyped_action_core_head h.2 hc

/-- A bounded variant retaining the landed operational realization at
negative argument occurrences.  Its output and field recursion is new. -/
def covWTyped_rawCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e : Expr Nat) : Prop :=
  match c with
  | .bot => True
  | .lam rows => CovVNativeHead E n Γ e ∧
      ∀ D B : Expr Nat, HasTyT E n Γ e (.pi D B) →
        ∀ d : CptT, ApproxTW E EnvT.bot D d →
          ∀ s ∈ rows, (∀ u ∈ s.1, CTyS E u d) →
            ∀ x : Expr Nat, HasTyT E n Γ x D →
              (∀ u ∈ s.1, CovWValueAction E n Γ u x) →
              covWTyped_rawCore E n Γ s.2 (.app e x)
  | .spine r us => ∃ (ls : List Level) (xs : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
      (∀ args : List (Expr Nat),
        NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args)) ∧
      xs.length = us.length ∧
      ∀ i (hi : i < us.length),
        covWTyped_rawCore E n Γ us[i] (xs.getD i (.bvar 0))
  | .prop => ∃ l : Level, sortCode l = .prop ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .sort => ∃ l : Level, sortCode l = .sort ∧
      RedR (WhStepCK2 E n) Γ e (.sort l)
  | .pi _ _ => ∃ D B : Expr Nat,
      RedR (WhStepCK2 E n) Γ e (.pi D B)
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  · have hs := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
    have ho := sizeOfT_snd_lt s
    omega
  · have hu := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›)
    omega

/-- The bounded action also retains the actual native type; it is not an
alias for the exact recursively typed action. -/
def covWTyped_rawAction (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e A : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ e A) ∧ covWTyped_rawCore E n Γ c e

/-- The landed stronger actions constructively supply only the bounded
variant.  The native Pi and domain-code guards narrow its row tests. -/
theorem covWTyped_raw_core_of_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (c : CptT) {e : Expr Nat} (h : CovWValueAction E n Γ c e) :
    covWTyped_rawCore E n Γ c e := by
  suffices hrec : ∀ k (d : CptT), sizeOf d ≤ k →
      ∀ v, CovWValueAction E n Γ d v → covWTyped_rawCore E n Γ d v from
    hrec (sizeOf c) c (Nat.le_refl _) e h
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro d hd v hv
      have rec : ∀ d', sizeOf d' < sizeOf d →
          ∀ x, CovWValueAction E n Γ d' x → covWTyped_rawCore E n Γ d' x := by
        intro d' hlt
        exact ih (sizeOf d') (Nat.lt_of_lt_of_le hlt hd) d' (Nat.le_refl _)
      cases d with
      | bot => rw [covWTyped_rawCore]; trivial
      | lam rows =>
          rw [CovWValueAction] at hv
          rw [covWTyped_rawCore]
          refine ⟨hv.1, ?_⟩
          intro D B ht a hD s hs hct x hx ha
          apply rec s.2 ?_ (.app v x) (hv.2 s hs x ha)
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := sizeOfT_snd_lt s
          simp only [CptT.lam.sizeOf_spec]
          omega
      | spine r us =>
          rw [CovWValueAction] at hv
          rw [covWTyped_rawCore]
          obtain ⟨ls, xs, hr, hn, hl, hx⟩ := hv
          refine ⟨ls, xs, hr, hn, hl, ?_⟩
          intro i hi
          apply rec us[i] ?_ (xs.getD i (.bvar 0)) (hx i hi)
          have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem hi)
          simp only [CptT.spine.sizeOf_spec]
          omega
      | prop => simpa only [CovWValueAction, covWTyped_rawCore] using hv
      | sort => simpa only [CovWValueAction, covWTyped_rawCore] using hv
      | pi a rows => simpa only [CovWValueAction, covWTyped_rawCore] using hv

theorem covWTyped_raw_action_of_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e A : Expr Nat} (ht : HasTyT E n Γ e A)
    (h : CovWValueAction E n Γ c e) : covWTyped_rawAction E n Γ c e A :=
  ⟨⟨ht⟩, covWTyped_raw_core_of_value c h⟩

theorem covWTyped_raw_action_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f x D B : Expr Nat} {rows : List (List CptT × CptT)}
    {s : List CptT × CptT} {d : CptT}
    (hf : covWTyped_rawAction E n Γ (.lam rows) f (.pi D B))
    (hD : ApproxTW E EnvT.bot D d) (hs : s ∈ rows)
    (hd : ∀ u ∈ s.1, CTyS E u d)
    (hx : HasTyT E n Γ x D)
    (ha : ∀ u ∈ s.1, CovWValueAction E n Γ u x) :
    covWTyped_rawAction E n Γ s.2 (.app f x) (instantiate0 x B) := by
  obtain ⟨ht, hf⟩ := hf
  obtain ⟨ht⟩ := ht
  rw [covWTyped_rawCore] at hf
  exact ⟨⟨.app Γ f x D B ht hx⟩, hf.2 D B ht d hD s hs hd x hx ha⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_ACTIONS_ROOTS
#print axioms covWTyped_actionCore
#print axioms CovWTypedAction
#print axioms covWTyped_action_typing
#print axioms covWTyped_action_bot
#print axioms covWTyped_action_app
#print axioms covWTyped_action_core_head
#print axioms covWTyped_action_head
#print axioms covWTyped_rawCore
#print axioms covWTyped_rawAction
#print axioms covWTyped_raw_core_of_value
#print axioms covWTyped_raw_action_of_value
#print axioms covWTyped_raw_action_app
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_ACTIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit
