import rcic.RcicNativeTypedModelCovWRawAdequacy

/-!
# Raw extensional graph actions with a constructive supplier

The lambda-compact clause below tests applications of the observed function;
it requires neither a lambda readback nor any native head for that function.
Every test retains the function's actual native Pi typing, an actual raw
observation of that native domain, strict compact typing of the row demands,
and an argument natively typed at that domain. Its argument demands are
actual `ApproxTW` observations under the bottom valuation.

This is explicitly a raw extensional interface. The negative argument
premises are not recursively weakened actions. The positive row outputs and
the actual fields of observed rigid spines recurse through the new finite
action. Sort and Pi observations retain their matching native heads.

The constructive adapter uses the landed raw supplier to turn each actual
raw argument observation into the operational action needed by the old row
test. Strong induction on compact size then translates its positive output.
Consequently the general raw supplier is proved, with no assumed head,
normalization, Pi-readback, or value supplier. An instantiated version keeps
the actual native typing of the substituted source explicit.

Neither a fully guarded eta adequacy theorem nor observation preservation
under native conversion is claimed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit FamModelAudit FamModelLRSAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovVAudit TypedModelCovWAudit

/-- A graph tests actual typed raw arguments and makes no head demand on
the function. Positive outputs and actual rigid fields recurse finitely. -/
def covWEtaRawActionCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e : Expr Nat) : Prop :=
  match c with
  | .bot => True
  | .lam rows =>
      ∀ D B : Expr Nat, HasTyT E n Γ e (.pi D B) →
        ∀ d : CptT, ApproxTW E EnvT.bot D d →
          ∀ s ∈ rows, (∀ u ∈ s.1, CTyS E u d) →
            ∀ x : Expr Nat, HasTyT E n Γ x D →
              (∀ u ∈ s.1, ApproxTW E EnvT.bot x u) →
              covWEtaRawActionCore E n Γ s.2 (.app e x)
  | .spine r us => ∃ (ls : List Level) (xs : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
      (∀ args : List (Expr Nat),
        NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) args)) ∧
      xs.length = us.length ∧
      ∀ i (hi : i < us.length),
        covWEtaRawActionCore E n Γ us[i] (xs.getD i (.bvar 0))
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

/-- The raw extensional action retains the source's actual native type. -/
def CovWEtaRawAction (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (c : CptT) (e A : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ e A) ∧ covWEtaRawActionCore E n Γ c e

theorem covWEtaRaw_action_typing {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {c : CptT} {e A : Expr Nat} (h : CovWEtaRawAction E n Γ c e A) :
    Nonempty (HasTyT E n Γ e A) := h.1

theorem covWEtaRaw_action_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (ht : HasTyT E n Γ e A) :
    CovWEtaRawAction E n Γ .bot e A :=
  ⟨⟨ht⟩, by rw [covWEtaRawActionCore]; trivial⟩

/-- A native Pi index supplies the graph test's actual function typing.
Every demanded raw observation belongs to the same typed argument. -/
theorem covWEtaRaw_action_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f x D B : Expr Nat} {rows : List (List CptT × CptT)}
    {s : List CptT × CptT} {d : CptT}
    (hf : CovWEtaRawAction E n Γ (.lam rows) f (.pi D B))
    (hD : ApproxTW E EnvT.bot D d) (hs : s ∈ rows)
    (hd : ∀ u ∈ s.1, CTyS E u d)
    (hx : HasTyT E n Γ x D)
    (ha : ∀ u ∈ s.1, ApproxTW E EnvT.bot x u) :
    CovWEtaRawAction E n Γ s.2 (.app f x) (instantiate0 x B) := by
  obtain ⟨⟨ht⟩, hf⟩ := hf
  rw [covWEtaRawActionCore] at hf
  exact ⟨⟨.app Γ f x D B ht hx⟩, hf D B ht d hD s hs hd x hx ha⟩

/-- Actual raw argument observations supply the stronger old argument
actions constructively; only positive subcompacts use the induction. -/
theorem covWEtaRaw_core_of_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) (c : CptT) {e : Expr Nat}
    (h : CovWValueAction E n Γ c e) : covWEtaRawActionCore E n Γ c e := by
  suffices hrec : ∀ k (d : CptT), sizeOf d ≤ k →
      ∀ v, CovWValueAction E n Γ d v → covWEtaRawActionCore E n Γ d v from
    hrec (sizeOf c) c (Nat.le_refl _) e h
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro d hd v hv
      have rec : ∀ d', sizeOf d' < sizeOf d →
          ∀ x, CovWValueAction E n Γ d' x → covWEtaRawActionCore E n Γ d' x := by
        intro d' hlt
        exact ih (sizeOf d') (Nat.lt_of_lt_of_le hlt hd) d' (Nat.le_refl _)
      cases d with
      | bot => rw [covWEtaRawActionCore]; trivial
      | lam rows =>
          rw [CovWValueAction] at hv
          rw [covWEtaRawActionCore]
          intro D B _ht a _hD s hs _hct x hx ha
          apply rec s.2 ?_ (.app v x)
            (hv.2 s hs x (fun u hu =>
              covW_raw_closed_actions (Δ := Γ) hW hx (ha u hu)))
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := sizeOfT_snd_lt s
          simp only [CptT.lam.sizeOf_spec]
          omega
      | spine r us =>
          rw [CovWValueAction] at hv
          rw [covWEtaRawActionCore]
          obtain ⟨ls, xs, hr, hn, hl, hx⟩ := hv
          refine ⟨ls, xs, hr, hn, hl, ?_⟩
          intro i hi
          apply rec us[i] ?_ (xs.getD i (.bvar 0)) (hx i hi)
          have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem hi)
          simp only [CptT.spine.sizeOf_spec]
          omega
      | prop => simpa only [CovWValueAction, covWEtaRawActionCore] using hv
      | sort => simpa only [CovWValueAction, covWEtaRawActionCore] using hv
      | pi a rows => simpa only [CovWValueAction, covWEtaRawActionCore] using hv

theorem covWEtaRaw_action_of_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {c : CptT} {e A : Expr Nat}
    (ht : HasTyT E n Γ e A) (h : CovWValueAction E n Γ c e) :
    CovWEtaRawAction E n Γ c e A :=
  ⟨⟨ht⟩, covWEtaRaw_core_of_value hW c h⟩

/-- Every actual typed bottom-valuation raw observation supplies the new
extensional action. No operational supplier is an additional premise. -/
theorem covWEtaRaw_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c) :
    CovWEtaRawAction E n Γ c e A :=
  covWEtaRaw_action_of_value hW ht (covW_raw_closed_actions hW ht ho)

/-- The instantiated source keeps its actual native type; source typing
alone does not discharge the substituted typing premise. -/
theorem covWEtaRaw_instantiated {E : ResolvedEnv} {n : Nat} {Γ Δ : LCtx}
    (hW : EnvWfT E) {ρ : EnvT} {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E ρ e c) (σ : SubstT)
    (hti : HasTyT E n Δ (substT σ e) (substT σ A))
    (hσ : ∀ i u, ρ i u → CovWValueAction E n Δ u (σ i)) :
    CovWEtaRawAction E n Δ c (substT σ e) (substT σ A) :=
  covWEtaRaw_action_of_value hW hti (covW_raw_typed_actions hW ht ho σ hσ)

/-- A concrete raw function observation can be tested at each actually
observed native argument without any recursive argument-action assumption. -/
theorem covWEtaRaw_closed_row {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {f x D B : Expr Nat}
    {rows : List (List CptT × CptT)} {s : List CptT × CptT} {d : CptT}
    (hf : HasTyT E n Γ f (.pi D B))
    (hof : ApproxTW E EnvT.bot f (.lam rows))
    (hD : ApproxTW E EnvT.bot D d) (hs : s ∈ rows)
    (hd : ∀ u ∈ s.1, CTyS E u d) (hx : HasTyT E n Γ x D)
    (hox : ∀ u ∈ s.1, ApproxTW E EnvT.bot x u) :
    CovWEtaRawAction E n Γ s.2 (.app f x) (instantiate0 x B) :=
  covWEtaRaw_action_app (covWEtaRaw_closed hW hf hof) hD hs hd hx hox

/-- Universe-code actions still supply the matching native sort and its
normality, including the exact Prop/Sort compact distinction. -/
theorem covWEtaRaw_sort_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {c : CptT} (h : CovWEtaRawAction E n Γ c e A)
    (hc : c = .prop ∨ c = .sort) :
    ∃ l : Level, sortCode l = c ∧
      RedR (WhStepCK2 E n) Γ e (.sort l) ∧
      NormalR (WhStepCK2 E n) Γ (.sort l) := by
  have hcore := h.2
  rcases hc with rfl | rfl <;> rw [covWEtaRawActionCore] at hcore
  · obtain ⟨l, hl, hr⟩ := hcore
    exact ⟨l, hl, hr, normalR_sortCK2 Γ l⟩
  · obtain ⟨l, hl, hr⟩ := hcore
    exact ⟨l, hl, hr, normalR_sortCK2 Γ l⟩

/-- A Pi compact remains evidence for an actual native Pi term head. -/
theorem covWEtaRaw_pi_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : CptT} {rows : List (List CptT × CptT)}
    (h : CovWEtaRawAction E n Γ (.pi d rows) e A) :
    ∃ D B : Expr Nat, RedR (WhStepCK2 E n) Γ e (.pi D B) ∧
      NormalR (WhStepCK2 E n) Γ (.pi D B) := by
  have hcore := h.2
  rw [covWEtaRawActionCore] at hcore
  obtain ⟨D, B, hr⟩ := hcore
  exact ⟨D, B, hr, normalR_piCK2 Γ D B⟩

/-- Rigid spines retain their actual native fields and each field's new
finite action. The graph-clause change does not erase this evidence. -/
theorem covWEtaRaw_spine_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {r : Nat} {us : List CptT}
    (h : CovWEtaRawAction E n Γ (.spine r us) e A) :
    ∃ (ls : List Level) (xs : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) xs) ∧
      NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) xs) ∧
      xs.length = us.length ∧
      ∀ i (hi : i < us.length),
        covWEtaRawActionCore E n Γ us[i] (xs.getD i (.bvar 0)) := by
  have hcore := h.2
  rw [covWEtaRawActionCore] at hcore
  obtain ⟨ls, xs, hr, hn, hl, hx⟩ := hcore
  exact ⟨ls, xs, hr, hn xs, hl, hx⟩

/-- Sort readback is constructively supplied for every actual typed raw
sort observation; it is not a field assumed by the adequacy theorem. -/
theorem covWEtaRaw_closed_sort_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {c : CptT}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e c)
    (hc : c = .prop ∨ c = .sort) :
    ∃ l : Level, sortCode l = c ∧
      RedR (WhStepCK2 E n) Γ e (.sort l) ∧
      NormalR (WhStepCK2 E n) Γ (.sort l) :=
  covWEtaRaw_sort_head (covWEtaRaw_closed hW ht ho) hc

theorem covWEtaRaw_closed_pi_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {d : CptT}
    {rows : List (List CptT × CptT)}
    (ht : HasTyT E n Γ e A) (ho : ApproxTW E EnvT.bot e (.pi d rows)) :
    ∃ D B : Expr Nat, RedR (WhStepCK2 E n) Γ e (.pi D B) ∧
      NormalR (WhStepCK2 E n) Γ (.pi D B) :=
  covWEtaRaw_pi_head (covWEtaRaw_closed hW ht ho)

/-- The adapter preserves every demand on each actual native field. -/
theorem covWEtaRaw_demands_of_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {xs : List (Expr Nat)} {uss : List (List CptT)}
    (h : CovWListDemands (CovWValueAction E n Γ) xs uss) :
    CovWListDemands (covWEtaRawActionCore E n Γ) xs uss := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (fun u hu => covWEtaRaw_core_of_value hW u (hx u hu)) ih

/-- All demand vectors agree on one actual constructor spine, with the
new actions attached to that spine's actual fields. -/
theorem covWEtaRaw_closed_ctor_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hW : EnvWfT E) {e A : Expr Nat} {r nparams : Nat} {uss : List (List CptT)}
    (ht : HasTyT E n Γ e A)
    (ho : ∀ c ∈ ctorDemandT r nparams uss, ApproxTW E EnvT.bot e c) :
    ∃ (ls : List Level) (params fields : List (Expr Nat)),
      RedR (WhStepCK2 E n) Γ e (foldApps (.const r ls) (params ++ fields)) ∧
      NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) (params ++ fields)) ∧
      params.length = nparams ∧ fields.length = uss.length ∧
      CovWListDemands (covWEtaRawActionCore E n Γ) fields uss := by
  obtain ⟨ls, params, fields, hr, hn, hp, hf, hfields⟩ :=
    covW_raw_closed_ctor_fields (Δ := Γ) hW ht ho
  exact ⟨ls, params, fields, hr, hn, hp, hf, covWEtaRaw_demands_of_value hW hfields⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ACTIONS_ROOTS
#print axioms covWEtaRawActionCore
#print axioms CovWEtaRawAction
#print axioms covWEtaRaw_action_typing
#print axioms covWEtaRaw_action_bot
#print axioms covWEtaRaw_action_app
#print axioms covWEtaRaw_core_of_value
#print axioms covWEtaRaw_action_of_value
#print axioms covWEtaRaw_closed
#print axioms covWEtaRaw_instantiated
#print axioms covWEtaRaw_closed_row
#print axioms covWEtaRaw_sort_head
#print axioms covWEtaRaw_pi_head
#print axioms covWEtaRaw_spine_fields
#print axioms covWEtaRaw_closed_sort_head
#print axioms covWEtaRaw_closed_pi_head
#print axioms covWEtaRaw_demands_of_value
#print axioms covWEtaRaw_closed_ctor_fields
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_ACTIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
