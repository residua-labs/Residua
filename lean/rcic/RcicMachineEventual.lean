/-
RM-025 Carrier 1 — Positive eventuality interface over the resumable reference
machine (`runRaw` / `runRawR`, `RcicMachineResume`), inner-budget monotonicity
for `whnfCert` / `convCert` / `inferCert` / `checkCert`, uniqueness and refusal
exclusion laws, and two-way eventuality characterizations with non-vacuity
accepting and refused controls (`docs/rcic/03_REFERENCE_MACHINE.md:391, 401-408`,
`research/rcic/rm/S0_RM024_025.md`, cc ruling on #7058):
  - All 8 refusable `RawTask` constructors (`whnfAt`, `levelEqual`, `lookupLocal`,
    `lookupDeclaration`, `convAt`, `infer`, `check`, `convType`) carry genuine
    all-budget refused-input controls (`TaskAlwaysRefused` / `TaskRefusesFrom`
    plus `∀ b m p, runRawR m ⟨amb, t, b⟩ ≠ .done (.accepted p)`).
  - Structural exception for `.syntaxEqual` (`RcicMachine.lean:452-454`): every
    `.syntaxEqual a b` input accepts `.conversionConfirmed` (when `a = b`) or
    `.conversionMismatch` (when `a ≠ b`) at every positive budget and never
    returns `.refused` (`syntaxEqual_always_accepts_confirmed_or_mismatch`,
    `syntaxEqual_never_refused`, `not_taskRefusesFrom_syntaxEqual`). Its
    negative control is therefore payload-negative (`pin_syntaxEqual_payload_negative_control`),
    sealing the accepting `.conversionConfirmed` run, the accepting
    `.conversionMismatch` run, and the opposite-tag exclusions.

`closure_claim = 0`.
-/
import rcic.RcicMachineResume
import rcic.RcicScmRefinement

namespace Rcic.Machine.Eventual

open Rcic.Declarative
open Rcic.Machine
open Rcic.ScmRefinement

/-! ## 1. Positive eventuality definitions over `runRawR` / `runRaw` -/

/-- State-level positive eventuality over the resumable runner `runRawR`:
    starting from `s`, some finite outer step budget `m` reaches
    `.done (.accepted p)`. -/
def EventuallyAccepts (s : RawState) (p : AcceptedPayload) : Prop :=
  ∃ m : Nat, runRawR m s = .done (.accepted p)

/-- Task-level positive eventuality ("completeness up to fuel", `03:391, 401-408`):
    for ambient `amb` and task `t`, there exist inner certifier budget `b` and
    outer runner budget `m` such that `runRawR m ⟨amb, t, b⟩ = .done (.accepted p)`. -/
def TaskEventuallyAccepts (amb : Ambient) (t : RawTask) (p : AcceptedPayload) : Prop :=
  ∃ b : Nat, EventuallyAccepts ⟨amb, t, b⟩ p

/-- Strong threshold form of task eventuality: from inner budget threshold `B`
    onward, every inner budget `b ≥ B` and positive outer budget `m ≥ 1`
    accepts with `p`. -/
def TaskAcceptsFrom (amb : Ambient) (t : RawTask) (p : AcceptedPayload) (B : Nat) : Prop :=
  ∀ b : Nat, B ≤ b → ∀ m : Nat, 1 ≤ m →
    runRawR m ⟨amb, t, b⟩ = .done (.accepted p)

/-- Task-level permanent refusal from inner budget threshold `B` onward:
    every inner budget `b ≥ B` and outer budget `m ≥ 1` refuses with `r`. -/
def TaskRefusesFrom (amb : Ambient) (t : RawTask) (r : String) (B : Nat) : Prop :=
  ∀ b : Nat, B ≤ b → ∀ m : Nat, 1 ≤ m →
    runRawR m ⟨amb, t, b⟩ = .done (.refused r)

/-- Task-level permanent refusal at all positive budgets `b ≥ 1`. -/
def TaskAlwaysRefused (amb : Ambient) (t : RawTask) (r : String) : Prop :=
  TaskRefusesFrom amb t r 1

/-- Tasks and payloads whose acceptance is backed by a positive certifier
    derivation (all task/payload pairs except `.convAt`'s negative
    `.conversionMismatch` fallback, where `convCert`'s `.app` congruence arm
    re-labels a subcall `[rcic_conv_fuel]` into `[rcic_conv_mismatch]`). -/
def PositiveTaskPayload : RawTask → AcceptedPayload → Prop
  | .convAt _ _ _, .conversionMismatch => False
  | _, _ => True

/-- Tasks and refusal residues that are upward-monotone in the inner budget `b`
    from any single refusing budget onward. -/
def RefusalMonotoneTask : RawTask → String → Prop
  | .whnfAt _ _, r => r ≠ "[rcic_whnf_fuel]"
  | .levelEqual _ _, _ => True
  | .lookupLocal _, _ => True
  | .lookupDeclaration _ _, _ => True
  | .convType _ _, _ => True
  | _, _ => False

/-! ## 2. One-shot runner characterizations and outer-step monotonicity -/

/-- Because `kernelStepRaw` is one-shot (`kernelStepRaw_never_step`), any
    positive outer step budget `k + 1` immediately wraps `kernelStepRaw s`
    when `kernelStepRaw s = .result r`. -/
theorem runRawR_pos_eq_of_result {s : RawState} {r : RunResult}
    (h : kernelStepRaw s = .result r) {m : Nat} (hm : 1 ≤ m) :
    runRawR m s = .done r := by
  cases m with
  | zero => exact absurd hm (Nat.not_succ_le_zero 0)
  | succ k => exact runRawR_succ_result k h

/-- Conversely, `runRawR m s = .done r` implies `1 ≤ m` and
    `kernelStepRaw s = .result r`. -/
theorem kernelStepRaw_of_runRawR_done {m : Nat} {s : RawState} {r : RunResult}
    (h : runRawR m s = .done r) :
    1 ≤ m ∧ kernelStepRaw s = .result r := by
  cases m with
  | zero =>
      simp only [runRawR] at h
      exact nomatch h
  | succ k =>
      refine ⟨Nat.succ_le_succ (Nat.zero_le k), ?_⟩
      simp only [runRawR] at h
      cases hkr : kernelStepRaw s with
      | step s' =>
          exact (kernelStepRaw_never_step s s' hkr).elim
      | result r' =>
          rw [hkr] at h
          injection h with hr'
          subst hr'
          rfl

/-- Outer-step monotonicity for `.done (.accepted p)`. -/
theorem runRawR_accepted_step_mono {m m' : Nat} {s : RawState} {p : AcceptedPayload}
    (h : runRawR m s = .done (.accepted p)) (hle : m ≤ m') :
    runRawR m' s = .done (.accepted p) := by
  have ⟨hm, hkr⟩ := kernelStepRaw_of_runRawR_done h
  exact runRawR_pos_eq_of_result hkr (Nat.le_trans hm hle)

/-- Outer-step monotonicity for `.done (.refused r)`. -/
theorem runRawR_refused_step_mono {m m' : Nat} {s : RawState} {r : String}
    (h : runRawR m s = .done (.refused r)) (hle : m ≤ m') :
    runRawR m' s = .done (.refused r) := by
  have ⟨hm, hkr⟩ := kernelStepRaw_of_runRawR_done h
  exact runRawR_pos_eq_of_result hkr (Nat.le_trans hm hle)

/-- `EventuallyAccepts` is equivalent to `kernelStepRaw` returning
    `.result (.accepted p)`. -/
theorem eventuallyAccepts_iff_kernelStepRaw (s : RawState) (p : AcceptedPayload) :
    EventuallyAccepts s p ↔ kernelStepRaw s = .result (.accepted p) := by
  constructor
  · rintro ⟨m, hm⟩
    exact (kernelStepRaw_of_runRawR_done hm).2
  · intro hkr
    exact ⟨1, runRawR_pos_eq_of_result hkr (Nat.le_refl 1)⟩

/-- `EventuallyAccepts` over `runRawR` is equivalent to eventual acceptance
    over the landed `runRaw`. -/
theorem eventuallyAccepts_iff_runRaw (s : RawState) (p : AcceptedPayload) :
    EventuallyAccepts s p ↔ ∃ m : Nat, runRaw m s = .accepted p := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, runRaw_of_runRawR_done m s (.accepted p) hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, runRawR_of_runRaw hm (fun h => nomatch h)⟩

/-- Resumption preserves positive eventuality: if `runRawR m s` suspends at `s'`
    and `s'` eventually accepts `p`, then `s` eventually accepts `p`. -/
theorem eventuallyAccepts_of_continue {m : Nat} {s s' : RawState} {p : AcceptedPayload}
    (hsusp : runRawR m s = .suspended s') (hev : EventuallyAccepts s' p) :
    EventuallyAccepts s p := by
  rcases hev with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  rw [← RM008_suspension_resumes m n s s' hsusp]
  exact hn

/-- State-level eventual acceptance is deterministic across all outer budgets. -/
theorem eventuallyAccepts_unique {s : RawState} {p₁ p₂ : AcceptedPayload}
    (h₁ : EventuallyAccepts s p₁) (h₂ : EventuallyAccepts s p₂) :
    p₁ = p₂ := by
  rcases h₁ with ⟨m₁, hm₁⟩
  rcases h₂ with ⟨m₂, hm₂⟩
  have heq := runRawR_done_unique hm₁ hm₂
  injection heq

/-- Any outer-budget refusal at state `s` rules out `EventuallyAccepts s p`
    for every payload `p`. -/
theorem not_eventuallyAccepts_of_refused {m : Nat} {s : RawState} {r : String}
    (href : runRawR m s = .done (.refused r)) (p : AcceptedPayload) :
    ¬ EventuallyAccepts s p := by
  rintro ⟨m', hm'⟩
  have heq := runRawR_done_unique href hm'
  exact nomatch heq

/-- At inner budget `0`, `kernelStepRaw` returns `.result .suspended`, so no
    outer budget ever accepts. -/
theorem not_eventuallyAccepts_budget_zero (amb : Ambient) (t : RawTask)
    (p : AcceptedPayload) :
    ¬ EventuallyAccepts ⟨amb, t, 0⟩ p := by
  rw [eventuallyAccepts_iff_kernelStepRaw]
  intro h
  simp only [kernelStepRaw] at h
  exact nomatch h

/-! ## 3. Inner-fuel monotonicity of `whnfCert`, `convCert`, `inferCert`, `checkCert` -/

/-- When `machineWhnfDone E e = true`, `whnfCert` immediately returns
    `.ok ⟨e, .refl Γ e⟩` at every fuel `f`. -/
theorem whnfCert_of_machineWhnfDone (E : ResolvedEnv) (n : Nat) (f : Nat)
    (Γ : LCtx) (e : Expr Nat) (hdone : machineWhnfDone E e = true) :
    whnfCert E n f Γ e = .ok ⟨e, .refl Γ e⟩ := by
  cases f with
  | zero =>
      rw [whnfCert]
      split
      · next t rest hsp =>
          simp only [machineWhnfDone, hsp] at hdone
          exact nomatch hdone
      · rw [if_pos hdone]
  | succ f₀ =>
      rw [whnfCert]
      split
      · next A body arg rest hsp =>
          simp only [machineWhnfDone, hsp] at hdone
          exact nomatch hdone
      · next A value body rest hsp =>
          simp only [machineWhnfDone, hsp] at hdone
          exact nomatch hdone
      · next t rest hsp =>
          simp only [machineWhnfDone, hsp] at hdone
          exact nomatch hdone
      · next r ls rest hsp =>
          split
          · rfl
          · next m hm =>
              split
              · next b hb htr =>
                  simp only [machineWhnfDone, hsp, hm, hb, htr,
                    Option.isSome_some, Bool.and_self, Bool.not_true] at hdone
                  exact nomatch hdone
              · rfl
      · rfl

/-- `whnfCert` positive monotonicity in fuel: if `whnfCert` succeeds at `f`,
    it succeeds at every `f' ≥ f` with the exact same WHNF term `c.1`. -/
theorem whnfCert_mono {E : ResolvedEnv} {n f f' : Nat} {Γ : LCtx} {e : Expr Nat}
    {c : Σ' (w : Expr Nat), MachineRed E n Γ e w}
    (hok : whnfCert E n f Γ e = .ok c) (hle : f ≤ f') :
    ∃ c', whnfCert E n f' Γ e = .ok c' ∧ c'.1 = c.1 := by
  induction f generalizing f' Γ e c with
  | zero =>
      have hdone := whnfCert_ok_done E n 0 Γ e c hok
      rw [whnfCert] at hok
      split at hok
      · cases hok
      · split at hok
        · next hdoneE =>
            have hc1 : c.1 = e := by cases hok; rfl
            exact ⟨⟨e, .refl Γ e⟩, whnfCert_of_machineWhnfDone E n f' Γ e hdoneE, hc1.symm⟩
        · cases hok
  | succ f₀ ih =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          rw [whnfCert] at hok
          rw [whnfCert]
          split at hok
          · next A body arg rest hsp =>
              split at hok
              · cases hok
              · next w k hin =>
                  have hc1 : c.1 = w := by cases hok; rfl
                  rcases ih hin hle₀ with ⟨⟨w', k'⟩, hin', hw'⟩
                  simp only at hw'
                  subst hw'
                  simp only [hin']
                  exact ⟨_, rfl, hc1.symm⟩
          · next A value body rest hsp =>
              split at hok
              · cases hok
              · next w k hin =>
                  have hc1 : c.1 = w := by cases hok; rfl
                  rcases ih hin hle₀ with ⟨⟨w', k'⟩, hin', hw'⟩
                  simp only at hw'
                  subst hw'
                  simp only [hin']
                  exact ⟨_, rfl, hc1.symm⟩
          · cases hok
          · next r ls rest hsp =>
              split at hok
              · next hm =>
                  have hc1 : c.1 = e := by cases hok; rfl
                  exact ⟨_, rfl, hc1.symm⟩
              · next m hm =>
                  split at hok
                  · next b hb htr =>
                      split at hok
                      · cases hok
                      · next w k hin =>
                          have hc1 : c.1 = w := by cases hok; rfl
                          rcases ih hin hle₀ with ⟨⟨w', k'⟩, hin', hw'⟩
                          simp only at hw'
                          subst hw'
                          simp only [hin']
                          exact ⟨_, rfl, hc1.symm⟩
                  · next hnot =>
                      have hc1 : c.1 = e := by cases hok; rfl
                      exact ⟨_, rfl, hc1.symm⟩
          · next hd args dlam dlet dlit dconst hsp =>
              have hc1 : c.1 = e := by cases hok; rfl
              exact ⟨_, rfl, hc1.symm⟩

/-- `whnfCert` non-fuel refusal monotonicity: if `whnfCert` refuses with a
    residue `r ≠ "[rcic_whnf_fuel]"` at fuel `f`, it refuses with `r` at every
    `f' ≥ f`. -/
theorem whnfCert_refused_mono {E : ResolvedEnv} {n f f' : Nat} {Γ : LCtx}
    {e : Expr Nat} {r : String}
    (hno : whnfCert E n f Γ e = .no r) (hne : r ≠ "[rcic_whnf_fuel]")
    (hle : f ≤ f') :
    whnfCert E n f' Γ e = .no r := by
  induction f generalizing f' Γ e with
  | zero =>
      cases f' with
      | zero => exact hno
      | succ f'₀ =>
          rw [whnfCert] at hno
          split at hno
          · next t rest hsp =>
              injection hno with hmsg
              subst hmsg
              rw [whnfCert]
              split
              · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
              · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
              · rfl
              · next _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
              · next _ _ _ _ dlit _ hsp' =>
                  rw [hsp] at hsp'
                  injection hsp' with h1 _
                  exact (dlit t h1.symm).elim
          · split at hno
            · cases hno
            · injection hno with h'
              exact (hne h'.symm).elim
  | succ f₀ ih =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          rw [whnfCert] at hno
          rw [whnfCert]
          split at hno
          · next A body arg rest hsp =>
              split at hno
              · next msg hin =>
                  injection hno with hmsg
                  subst hmsg
                  rw [ih hin hle₀]
              · cases hno
          · next A value body rest hsp =>
              split at hno
              · next msg hin =>
                  injection hno with hmsg
                  subst hmsg
                  rw [ih hin hle₀]
              · cases hno
          · next t rest hsp =>
              exact hno
          · next r₀ ls rest hsp =>
              split at hno
              · cases hno
              · next m hm =>
                  split at hno
                  · next b hb htr =>
                      split at hno
                      · next msg hin =>
                          injection hno with hmsg
                          subst hmsg
                          rw [ih hin hle₀]
                      · cases hno
                  · cases hno
          · cases hno

/-- `convCert` positive monotonicity in fuel: if `convCert` succeeds at `f`,
    it succeeds at every `f' ≥ f`. -/
theorem convCert_mono {E : ResolvedEnv} {n f f' : Nat} {Γ : LCtx}
    {A l r : Expr Nat} {c : Conv E n Γ l r}
    (hok : convCert E n f Γ A l r = .ok c) (hle : f ≤ f') :
    ∃ c', convCert E n f' Γ A l r = .ok c' := by
  induction f generalizing f' Γ A l r c with
  | zero =>
      rw [convCert] at hok
      cases hok
  | succ f₀ ih =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          simp only [convCert] at hok ⊢
          split at hok
          · next hlr =>
              subst hlr
              simp only [dif_pos rfl]
              exact ⟨_, rfl⟩
          · next hlr =>
              rw [dif_neg hlr]
              split at hok
              · cases hok
              · next wl kl hwl =>
                  rcases whnfCert_mono hwl hle₀ with ⟨⟨wl', kl'⟩, hwl', hwl_eq⟩
                  simp only at hwl_eq
                  subst hwl_eq
                  split
                  · next msg hno => rw [hwl'] at hno; nomatch hno
                  · next wl₂ kl₂ hwl₂ =>
                      have hwl₂_eq : wl₂ = wl' := by
                        rw [hwl'] at hwl₂
                        injection hwl₂ with h1
                        exact (congrArg PSigma.fst h1).symm
                      subst hwl₂_eq
                      split at hok
                      · cases hok
                      · next wr kr hwr =>
                          rcases whnfCert_mono hwr hle₀ with ⟨⟨wr', kr'⟩, hwr', hwr_eq⟩
                          simp only at hwr_eq
                          subst hwr_eq
                          split
                          · next msg hno => rw [hwr'] at hno; nomatch hno
                          · next wr₂ kr₂ hwr₂ =>
                              have hwr₂_eq : wr₂ = wr' := by
                                rw [hwr'] at hwr₂
                                injection hwr₂ with h1
                                exact (congrArg PSigma.fst h1).symm
                              subst hwr₂_eq
                              split at hok
                              · next hwleq =>
                                  subst hwleq
                                  simp only [dif_pos rfl]
                                  exact ⟨_, rfl⟩
                              · next hwleq =>
                                  simp only [dif_neg hwleq]
                                  split at hok
                                  · next u v _ _ _ _ _ =>
                                      split at hok
                                      · next huv =>
                                          subst huv
                                          simp only [dif_pos rfl]
                                          exact ⟨_, rfl⟩
                                      · cases hok
                                  · next r₁ ls₁ r₂ ls₂ _ _ _ _ _ =>
                                      split at hok
                                      · next hconj =>
                                          rcases hconj with ⟨hr₁₂, hls₁₂⟩
                                          subst hr₁₂ hls₁₂
                                          simp only [and_self, dif_pos True.intro]
                                          exact ⟨_, rfl⟩
                                      · cases hok
                                  · next f₁ a₁ f₂ a₂ _ _ _ _ _ =>
                                      split at hok
                                      · cases hok
                                      · next hf hcf =>
                                          split at hok
                                          · cases hok
                                          · next ha hca =>
                                              rcases ih hcf hle₀ with ⟨hf', hcf'⟩
                                              rcases ih hca hle₀ with ⟨ha', hca'⟩
                                              simp only [hcf', hca']
                                              exact ⟨_, rfl⟩
                                  · cases hok

/-- `inferCert` positive monotonicity in fuel: if `inferCert` succeeds at `f`,
    it succeeds at every `f' ≥ f` with the exact same inferred type `c.1`. -/
theorem inferCert_mono {E : ResolvedEnv} {n f f' : Nat} {Γ : LCtx}
    {e : Expr Nat} {c : Σ' (T : Expr Nat), HasTy E n Γ e T}
    (hok : inferCert E n f Γ e = .ok c) (hle : f ≤ f') :
    ∃ c', inferCert E n f' Γ e = .ok c' ∧ c'.1 = c.1 := by
  induction f generalizing f' Γ e c with
  | zero =>
      cases e <;> simp only [inferCert] at hok <;> nomatch hok
  | succ f₀ ih =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          cases e with
          | lit t =>
              simp only [inferCert] at hok
              nomatch hok
          | bvar i =>
              rw [inferCert] at hok ⊢
              exact ⟨c, hok, rfl⟩
          | sort l =>
              rw [inferCert] at hok ⊢
              exact ⟨c, hok, rfl⟩
          | const r ls =>
              rw [inferCert] at hok ⊢
              exact ⟨c, hok, rfl⟩
          | pi A B =>
              simp only [inferCert] at hok ⊢
              split at hok
              · cases hok
              · next TA hA hinfA =>
                  rcases ih hinfA hle₀ with ⟨⟨TA', hA'⟩, hinfA', hTA_eq⟩
                  simp only at hTA_eq
                  subst hTA_eq
                  simp only [hinfA']
                  cases TA' with
                  | sort u =>
                      simp only at hok ⊢
                      split at hok
                      · cases hok
                      · next TB hB hinfB =>
                          rcases ih hinfB hle₀ with ⟨⟨TB', hB'⟩, hinfB', hTB_eq⟩
                          simp only at hTB_eq
                          subst hTB_eq
                          simp only [hinfB']
                          cases TB' with
                          | sort v =>
                              simp only at hok ⊢
                              have hc1 : c.1 = .sort (.imax u v) := by cases hok; rfl
                              exact ⟨_, rfl, hc1.symm⟩
                          | _ => simp only at hok; nomatch hok
                  | _ => simp only at hok; nomatch hok
          | lam A body =>
              simp only [inferCert] at hok ⊢
              split at hok
              · cases hok
              · next TA hA hinfA =>
                  rcases ih hinfA hle₀ with ⟨⟨TA', hA'⟩, hinfA', hTA_eq⟩
                  simp only at hTA_eq
                  subst hTA_eq
                  simp only [hinfA']
                  cases TA' with
                  | sort u =>
                      simp only at hok ⊢
                      split at hok
                      · cases hok
                      · next Tbody hbody hinfBody =>
                          rcases ih hinfBody hle₀ with ⟨⟨Tbody', hbody'⟩, hinfBody', hTb_eq⟩
                          simp only at hTb_eq
                          subst hTb_eq
                          simp only [hinfBody']
                          have hc1 : c.1 = .pi A Tbody' := by cases hok; rfl
                          exact ⟨_, rfl, hc1.symm⟩
                  | _ => simp only at hok; nomatch hok
          | app fn arg =>
              simp only [inferCert] at hok ⊢
              split at hok
              · cases hok
              · next Tf hfn hinfFn =>
                  rcases ih hinfFn hle₀ with ⟨⟨Tf', hfn'⟩, hinfFn', hTf_eq⟩
                  simp only at hTf_eq
                  subst hTf_eq
                  simp only [hinfFn']
                  split at hok
                  · cases hok
                  · next Tfw kfn hwhnf =>
                      rcases whnfCert_mono hwhnf hle₀ with ⟨⟨Tfw', kfn'⟩, hwhnf', hTfw_eq⟩
                      simp only at hTfw_eq
                      subst hTfw_eq
                      simp only [hwhnf']
                      split at hok
                      · cases hok
                      · next Targ harg hinfArg =>
                          rcases ih hinfArg hle₀ with ⟨⟨Targ', harg'⟩, hinfArg', hTarg_eq⟩
                          simp only at hTarg_eq
                          subst hTarg_eq
                          simp only [hinfArg']
                          cases Tfw' with
                          | pi A B =>
                              simp only [inferCert.inferCert_app] at hok ⊢
                              split at hok
                              · cases hok
                              · next hc hconv =>
                                  rcases convCert_mono hconv hle₀ with ⟨hc', hconv'⟩
                                  simp only [hconv']
                                  have hc1 : c.1 = instantiate0 arg B := by cases hok; rfl
                                  exact ⟨_, rfl, hc1.symm⟩
                          | _ => simp only [inferCert.inferCert_app] at hok; nomatch hok
          | letE A value body =>
              simp only [inferCert] at hok ⊢
              split at hok
              · cases hok
              · next TA hA hinfA =>
                  rcases ih hinfA hle₀ with ⟨⟨TA', hA'⟩, hinfA', hTA_eq⟩
                  simp only at hTA_eq
                  subst hTA_eq
                  simp only [hinfA']
                  cases TA' with
                  | sort u =>
                      simp only at hok ⊢
                      split at hok
                      · cases hok
                      · next Tval hval hinfVal =>
                          rcases ih hinfVal hle₀ with ⟨⟨Tval', hval'⟩, hinfVal', hTval_eq⟩
                          simp only at hTval_eq
                          subst hTval_eq
                          simp only [hinfVal']
                          split at hok
                          · cases hok
                          · next hc hconv =>
                              rcases convCert_mono hconv hle₀ with ⟨hc', hconv'⟩
                              simp only [hconv']
                              split at hok
                              · cases hok
                              · next Tbody hbody hinfBody =>
                                  rcases ih hinfBody hle₀ with ⟨⟨Tbody', hbody'⟩, hinfBody', hTb_eq⟩
                                  simp only at hTb_eq
                                  subst hTb_eq
                                  simp only [hinfBody']
                                  have hc1 : c.1 = instantiate0 value Tbody' := by cases hok; rfl
                                  exact ⟨_, rfl, hc1.symm⟩
                  | _ => simp only at hok; nomatch hok

/-- `checkCert` positive monotonicity in fuel: if `checkCert` succeeds at `f`,
    it succeeds at every `f' ≥ f`. -/
theorem checkCert_mono {E : ResolvedEnv} {n f f' : Nat} {Γ : LCtx}
    {e A : Expr Nat} {c : HasTy E n Γ e A}
    (hok : checkCert E n f Γ e A = .ok c) (hle : f ≤ f') :
    ∃ c', checkCert E n f' Γ e A = .ok c' := by
  cases f with
  | zero =>
      rw [checkCert] at hok
      cases hok
  | succ f₀ =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          simp only [checkCert] at hok ⊢
          split at hok
          · cases hok
          · next TA hA hinfA =>
              rcases inferCert_mono hinfA hle₀ with ⟨⟨TA', hA'⟩, hinfA', hTA_eq⟩
              simp only at hTA_eq
              subst hTA_eq
              simp only [hinfA']
              cases TA' with
              | sort u =>
                  simp only at hok ⊢
                  split at hok
                  · cases hok
                  · next Te he hinfE =>
                      rcases inferCert_mono hinfE hle₀ with ⟨⟨Te', he'⟩, hinfE', hTe_eq⟩
                      simp only at hTe_eq
                      subst hTe_eq
                      simp only [hinfE']
                      split at hok
                      · cases hok
                      · next hc hconv =>
                          rcases convCert_mono hconv hle₀ with ⟨hc', hconv'⟩
                          simp only [hconv']
                          exact ⟨_, rfl⟩
              | _ => simp only at hok; nomatch hok

/-! ## 4. Inner-budget monotonicity of `runRawR` and threshold stabilization -/

/-- At positive fuel `f + 1`, `inferCert` on `.const r ls` is independent of `f`. -/
theorem inferCert_const_succ_eq (E : ResolvedEnv) (n f f' : Nat) (Γ : LCtx)
    (r : Nat) (ls : List Level) :
    inferCert E n (f + 1) Γ (.const r ls) =
      inferCert E n (f' + 1) Γ (.const r ls) :=
  rfl

/-- At positive budget `f + 1`, `kernelStepRaw` on `.lookupDeclaration r ls` is
    independent of `f`. -/
theorem kernelStepRaw_lookupDeclaration_succ_eq (amb : Ambient) (f f' : Nat)
    (r : Nat) (ls : List Level) :
    kernelStepRaw ⟨amb, .lookupDeclaration r ls, f + 1⟩ =
      kernelStepRaw ⟨amb, .lookupDeclaration r ls, f' + 1⟩ := by
  simp only [kernelStepRaw]
  rw [inferCert_const_succ_eq amb.env amb.univs f f' amb.ctx r ls]
  cases inferCert amb.env amb.univs (f' + 1) amb.ctx (.const r ls) <;> rfl

/-- Inner-budget monotonicity for accepted runs on `PositiveTaskPayload`:
    if `runRawR m ⟨amb, t, b⟩ = .done (.accepted p)` and `b ≤ b'`, `1 ≤ m'`,
    then `runRawR m' ⟨amb, t, b'⟩ = .done (.accepted p)`. -/
theorem runRawR_accepted_budget_mono {amb : Ambient} {t : RawTask} {p : AcceptedPayload}
    {m m' b b' : Nat} (hpos : PositiveTaskPayload t p)
    (hacc : runRawR m ⟨amb, t, b⟩ = .done (.accepted p))
    (hb : b ≤ b') (hm' : 1 ≤ m') :
    runRawR m' ⟨amb, t, b'⟩ = .done (.accepted p) := by
  have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hacc
  apply runRawR_pos_eq_of_result _ hm'
  cases b with
  | zero =>
      simp only [kernelStepRaw] at hkr
      exact nomatch hkr
  | succ f =>
      cases b' with
      | zero => exact absurd hb (Nat.not_succ_le_zero f)
      | succ f' =>
          have hff' : f + 1 ≤ f' + 1 := hb
          cases t with
          | syntaxEqual a₁ a₂ =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | levelEqual l₁ l₂ =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | lookupLocal i =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | lookupDeclaration r ls =>
              rw [← kernelStepRaw_lookupDeclaration_succ_eq amb f f' r ls]
              exact hkr
          | whnfAt A e =>
              simp only [kernelStepRaw] at hkr ⊢
              split at hkr
              · next w kred heq =>
                  rcases whnfCert_mono heq hff' with ⟨⟨w', kred'⟩, heq', hw_eq⟩
                  simp only at hw_eq
                  subst hw_eq
                  rw [heq']
                  exact hkr
              · exact nomatch hkr
          | convAt A l r =>
              simp only [kernelStepRaw] at hkr ⊢
              split at hkr
              · next hc heq =>
                  rcases convCert_mono heq hff' with ⟨hc', heq'⟩
                  rw [heq']
                  exact hkr
              · next msg heq =>
                  split at hkr
                  · injection hkr with h1
                    injection h1 with h2
                    subst h2
                    exact False.elim hpos
                  · exact nomatch hkr
          | infer e =>
              simp only [kernelStepRaw] at hkr ⊢
              split at hkr
              · next T hty heq =>
                  rcases inferCert_mono heq hff' with ⟨⟨T', hty'⟩, heq', hT_eq⟩
                  simp only at hT_eq
                  subst hT_eq
                  rw [heq']
                  exact hkr
              · exact nomatch hkr
          | check e A =>
              simp only [kernelStepRaw] at hkr ⊢
              split at hkr
              · next hty heq =>
                  rcases checkCert_mono heq hff' with ⟨hty', heq'⟩
                  rw [heq']
                  exact hkr
              · exact nomatch hkr
          | convType A B =>
              simp only [kernelStepRaw] at hkr
              exact nomatch hkr

/-- Inner-budget monotonicity for non-fuel refusals on `RefusalMonotoneTask`. -/
theorem runRawR_refused_budget_mono {amb : Ambient} {t : RawTask} {r : String}
    {m m' b b' : Nat} (hrm : RefusalMonotoneTask t r)
    (href : runRawR m ⟨amb, t, b⟩ = .done (.refused r))
    (hb : b ≤ b') (hm' : 1 ≤ m') :
    runRawR m' ⟨amb, t, b'⟩ = .done (.refused r) := by
  have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done href
  apply runRawR_pos_eq_of_result _ hm'
  cases b with
  | zero =>
      simp only [kernelStepRaw] at hkr
      exact nomatch hkr
  | succ f =>
      cases b' with
      | zero => exact absurd hb (Nat.not_succ_le_zero f)
      | succ f' =>
          have hff' : f + 1 ≤ f' + 1 := hb
          cases t with
          | whnfAt A e =>
              simp only [RefusalMonotoneTask] at hrm
              simp only [kernelStepRaw] at hkr ⊢
              split at hkr
              · exact nomatch hkr
              · next msg hno =>
                  injection hkr with h1
                  injection h1 with hmsg
                  subst hmsg
                  rw [whnfCert_refused_mono hno hrm hff']
          | levelEqual l₁ l₂ =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | lookupLocal i =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | lookupDeclaration r₀ ls =>
              rw [← kernelStepRaw_lookupDeclaration_succ_eq amb f f' r₀ ls]
              exact hkr
          | convType A B =>
              simp only [kernelStepRaw] at hkr ⊢
              exact hkr
          | syntaxEqual _ _ => exact False.elim hrm
          | convAt _ _ _ => exact False.elim hrm
          | infer _ => exact False.elim hrm
          | check _ _ => exact False.elim hrm

/-- Threshold acceptance implies `TaskEventuallyAccepts`. -/
theorem taskAcceptsFrom_imp_eventuallyAccepts {amb : Ambient} {t : RawTask}
    {p : AcceptedPayload} {B : Nat} (h : TaskAcceptsFrom amb t p B) :
    TaskEventuallyAccepts amb t p :=
  ⟨B, 1, h B (Nat.le_refl B) 1 (Nat.le_refl 1)⟩

/-- For any positive task/payload pair, existential acceptance (`TaskEventuallyAccepts`)
    is equivalent to threshold acceptance (`∃ B, TaskAcceptsFrom amb t p B`). -/
theorem taskEventuallyAccepts_iff_acceptsFrom {amb : Ambient} {t : RawTask}
    {p : AcceptedPayload} (hpos : PositiveTaskPayload t p) :
    TaskEventuallyAccepts amb t p ↔ ∃ B : Nat, TaskAcceptsFrom amb t p B := by
  constructor
  · rintro ⟨B, m, hm⟩
    refine ⟨B, fun b hb m' hm' => ?_⟩
    exact runRawR_accepted_budget_mono hpos hm hb hm'
  · rintro ⟨B, hB⟩
    exact taskAcceptsFrom_imp_eventuallyAccepts hB

/-- Threshold acceptance is unique across all budgets (for ALL tasks and payloads). -/
theorem taskAcceptsFrom_unique {amb : Ambient} {t : RawTask}
    {p₁ p₂ : AcceptedPayload} {B₁ B₂ : Nat}
    (h₁ : TaskAcceptsFrom amb t p₁ B₁) (h₂ : TaskAcceptsFrom amb t p₂ B₂) :
    p₁ = p₂ := by
  have e₁ := h₁ (Nat.max B₁ B₂) (Nat.le_max_left B₁ B₂) 1 (Nat.le_refl 1)
  have e₂ := h₂ (Nat.max B₁ B₂) (Nat.le_max_right B₁ B₂) 1 (Nat.le_refl 1)
  have heq := runRawR_done_unique e₁ e₂
  injection heq

/-- Task-level eventual acceptance is deterministic across all budgets. -/
theorem taskEventuallyAccepts_unique {amb : Ambient} {t : RawTask}
    {p₁ p₂ : AcceptedPayload}
    (hpos₁ : PositiveTaskPayload t p₁) (hpos₂ : PositiveTaskPayload t p₂)
    (h₁ : TaskEventuallyAccepts amb t p₁) (h₂ : TaskEventuallyAccepts amb t p₂) :
    p₁ = p₂ := by
  rcases (taskEventuallyAccepts_iff_acceptsFrom hpos₁).mp h₁ with ⟨B₁, hB₁⟩
  rcases (taskEventuallyAccepts_iff_acceptsFrom hpos₂).mp h₂ with ⟨B₂, hB₂⟩
  exact taskAcceptsFrom_unique hB₁ hB₂

/-- Any task refused from threshold `B` onward never accepts any `PositiveTaskPayload`. -/
theorem not_taskEventuallyAccepts_of_refusesFrom {amb : Ambient} {t : RawTask}
    {r : String} {B : Nat} (href : TaskRefusesFrom amb t r B)
    {p : AcceptedPayload} (hpos : PositiveTaskPayload t p) :
    ¬ TaskEventuallyAccepts amb t p := by
  intro hev
  rcases (taskEventuallyAccepts_iff_acceptsFrom hpos).mp hev with ⟨B', hB'⟩
  have e₁ := href (Nat.max B B') (Nat.le_max_left B B') 1 (Nat.le_refl 1)
  have e₂ := hB' (Nat.max B B') (Nat.le_max_right B B') 1 (Nat.le_refl 1)
  have heq := runRawR_done_unique e₁ e₂
  exact nomatch heq

/-- Any task that is `TaskAlwaysRefused` (refused at every inner budget `b ≥ 1`)
    never eventually accepts ANY payload `p`. -/
theorem not_taskEventuallyAccepts_of_alwaysRefused {amb : Ambient} {t : RawTask}
    {r : String} (href : TaskAlwaysRefused amb t r) (p : AcceptedPayload) :
    ¬ TaskEventuallyAccepts amb t p := by
  rintro ⟨b, m, hm⟩
  cases b with
  | zero =>
      exact not_eventuallyAccepts_budget_zero amb t p ⟨m, hm⟩
  | succ f =>
      have e_ref := href (f + 1) (Nat.succ_le_succ (Nat.zero_le f)) 1 (Nat.le_refl 1)
      have heq := runRawR_done_unique e_ref hm
      exact nomatch heq

/-- Every `RefusalMonotoneTask` task satisfies `PositiveTaskPayload` for all `p`. -/
theorem positiveTaskPayload_of_refusalMonotone {t : RawTask} {r : String}
    (hrm : RefusalMonotoneTask t r) (p : AcceptedPayload) :
    PositiveTaskPayload t p := by
  cases t <;> first | trivial | exact False.elim hrm

/-- Any finite-budget refusal on a `RefusalMonotoneTask` permanently rules out
    `TaskEventuallyAccepts amb t p` across all budgets `b` and payloads `p`. -/
theorem not_taskEventuallyAccepts_of_refused {amb : Ambient} {t : RawTask}
    {r : String} {m b : Nat} (hrm : RefusalMonotoneTask t r)
    (href : runRawR m ⟨amb, t, b⟩ = .done (.refused r)) (p : AcceptedPayload) :
    ¬ TaskEventuallyAccepts amb t p := by
  have hfrom : TaskRefusesFrom amb t r b := fun b' hb' m' hm' =>
    runRawR_refused_budget_mono hrm href hb' hm'
  exact not_taskEventuallyAccepts_of_refusesFrom hfrom
    (positiveTaskPayload_of_refusalMonotone hrm p)

/-! ## 5. Two-way WHNF eventuality (`RM025_whnf_eventual` & `RM025_whnf_eventual_iff`) -/

/-- Exact head-reduction step count of a `MachineRed` derivation. -/
def machineRedSteps {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → MachineRed E n Γ a b → Nat
  | _, _, _, .refl _ _ => 0
  | _, _, _, .headBeta _ _ _ _ _ k => machineRedSteps k + 1
  | _, _, _, .headZeta _ _ _ _ _ k => machineRedSteps k + 1
  | _, _, _, .headDelta _ _ _ _ _ _ _ _ _ k => machineRedSteps k + 1

/-- Spine helper for `MachineRed.headBeta`. -/
theorem appsSpine_foldApps_beta (A body arg : Expr Nat) (rest : List (Expr Nat)) :
    appsSpine (foldApps (.app (.lam A body) arg) rest) = (.lam A body, arg :: rest) := by
  simp only [appsSpine_foldApps, appsSpine, List.nil_append, List.singleton_append]

/-- Spine helper for `MachineRed.headZeta`. -/
theorem appsSpine_foldApps_zeta (A value body : Expr Nat) (rest : List (Expr Nat)) :
    appsSpine (foldApps (.letE A value body) rest) = (.letE A value body, rest) := by
  simp only [appsSpine_foldApps, appsSpine, List.nil_append]

/-- `whnfCert` completeness along `MachineRed`: if `k : MachineRed E n Γ e w`
    and `machineWhnfDone E w = true`, then for every fuel `f ≥ machineRedSteps k`,
    `whnfCert E n f Γ e` returns `.ok c` with `c.1 = w`. -/
theorem whnfCert_complete_of_machineRed {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e w : Expr Nat} → (k : MachineRed E n Γ e w) →
    machineWhnfDone E w = true →
    ∀ f : Nat, machineRedSteps k ≤ f →
      ∃ c : Σ' (w' : Expr Nat), MachineRed E n Γ e w',
        whnfCert E n f Γ e = .ok c ∧ c.1 = w
  | Γ, e, _, .refl _ _, hdone, f, _ =>
      ⟨⟨e, .refl Γ e⟩, whnfCert_of_machineWhnfDone E n f Γ e hdone, rfl⟩
  | Γ, _, w, .headBeta _ A body arg rest k, hdone, f, hf => by
      cases f with
      | zero => simp only [machineRedSteps] at hf; exact absurd hf (Nat.not_succ_le_zero _)
      | succ f₀ =>
          simp only [machineRedSteps] at hf
          rcases whnfCert_complete_of_machineRed k hdone f₀ (Nat.le_of_succ_le_succ hf) with
            ⟨⟨w', k'⟩, hin, hw'⟩
          simp only at hw'
          subst hw'
          have hsp := appsSpine_foldApps_beta A body arg rest
          rw [whnfCert]
          split
          · next A' body' arg' rest' hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 h2
              injection h1 with hA hbody
              injection h2 with harg hrest
              subst hA hbody harg hrest
              simp only [hin]
              exact ⟨_, rfl, rfl⟩
          · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ dlam _ _ _ hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 h2
              exact (dlam A body arg rest h1.symm h2.symm).elim
  | Γ, _, w, .headZeta _ A value body rest k, hdone, f, hf => by
      cases f with
      | zero => simp only [machineRedSteps] at hf; exact absurd hf (Nat.not_succ_le_zero _)
      | succ f₀ =>
          simp only [machineRedSteps] at hf
          rcases whnfCert_complete_of_machineRed k hdone f₀ (Nat.le_of_succ_le_succ hf) with
            ⟨⟨w', k'⟩, hin, hw'⟩
          simp only at hw'
          subst hw'
          have hsp := appsSpine_foldApps_zeta A value body rest
          rw [whnfCert]
          split
          · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next A' value' body' rest' hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 hrest
              injection h1 with hA hval hbody
              subst hA hval hbody hrest
              simp only [hin]
              exact ⟨_, rfl, rfl⟩
          · next _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ _ dlet _ _ hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 _
              exact (dlet A value body h1.symm).elim
  | Γ, _, w, .headDelta _ r ls m b rest hres hbody htr k, hdone, f, hf => by
      cases f with
      | zero => simp only [machineRedSteps] at hf; exact absurd hf (Nat.not_succ_le_zero _)
      | succ f₀ =>
          simp only [machineRedSteps] at hf
          rcases whnfCert_complete_of_machineRed k hdone f₀ (Nat.le_of_succ_le_succ hf) with
            ⟨⟨w', k'⟩, hin, hw'⟩
          simp only at hw'
          subst hw'
          have hsp := appsSpine_foldApps_const r ls rest
          rw [whnfCert]
          split
          · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next _ _ hsp' => rw [hsp] at hsp'; injection hsp' with h1 _; nomatch h1
          · next r' ls' rest' hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 hrest
              injection h1 with hr hls
              subst hr hls hrest
              split
              · next hm => rw [hres] at hm; nomatch hm
              · next m' hm' =>
                  have hm_eq : m' = m := by
                    rw [hres] at hm'
                    injection hm' with h1
                    exact h1.symm
                  subst hm_eq
                  split
                  · next b' hb' htr' =>
                      have hb_eq : b' = b := by
                        rw [hbody] at hb'
                        injection hb' with h1
                        exact h1.symm
                      subst hb_eq
                      simp only [hin]
                      exact ⟨_, rfl, rfl⟩
                  · next hnot => exact (hnot b hbody htr).elim
          · next _ _ _ _ _ dconst hsp' =>
              rw [hsp] at hsp'
              injection hsp' with h1 _
              exact (dconst r ls h1.symm).elim

/-- RM-025 positive WHNF eventuality (`RM025_whnf_eventual`): any `MachineRed`
    chain to a head-normal form `w` is accepted by `.whnfAt A e` from inner
    budget `Nat.max 1 (machineRedSteps k)` onward. -/
theorem RM025_whnf_eventual {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A : Expr Nat) {e w : Expr Nat} (k : MachineRed E n Γ e w)
    (hdone : machineWhnfDone E w = true) :
    TaskAcceptsFrom ⟨E, n, Γ⟩ (.whnfAt A e) (.inferredWhnf A w)
      (Nat.max 1 (machineRedSteps k)) := by
  intro b hb m hm
  apply runRawR_pos_eq_of_result _ hm
  have hb1 : 1 ≤ b := Nat.le_trans (Nat.le_max_left 1 (machineRedSteps k)) hb
  have hbs : machineRedSteps k ≤ b :=
    Nat.le_trans (Nat.le_max_right 1 (machineRedSteps k)) hb
  cases b with
  | zero => exact absurd hb1 (Nat.not_succ_le_zero 0)
  | succ f =>
      rcases whnfCert_complete_of_machineRed k hdone (f + 1) hbs with
        ⟨⟨w', k'⟩, hok, hw'⟩
      simp only at hw'
      subst hw'
      simp only [kernelStepRaw, hok]

/-- RM-025 two-way WHNF characterization (`RM025_whnf_eventual_iff`):
    `TaskEventuallyAccepts ⟨E, n, Γ⟩ (.whnfAt A e) (.inferredWhnf A w)` holds
    if and only if `e` reduces via `MachineRed` to `w` and `machineWhnfDone E w = true`. -/
theorem RM025_whnf_eventual_iff (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A e w : Expr Nat) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.whnfAt A e) (.inferredWhnf A w) ↔
      Nonempty (MachineRed E n Γ e w) ∧ machineWhnfDone E w = true := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    exact ⟨⟨RM014_whnf_reduces ⟨⟨E, n, Γ⟩, .whnfAt A e, b⟩ A e w rfl hkr⟩,
      RM014_whnf_head_normal ⟨⟨E, n, Γ⟩, .whnfAt A e, b⟩ A e w rfl hkr⟩
  · rintro ⟨⟨k⟩, hdone⟩
    exact taskAcceptsFrom_imp_eventuallyAccepts (RM025_whnf_eventual A k hdone)

/-! ## 6. Two-way characterizations for `levelEqual`, `lookupLocal`, `lookupDeclaration`, `syntaxEqual`, `convAt`, `infer`, `check` -/

/-- `eqN l1 l2` implies `TaskAcceptsFrom amb (.levelEqual l1 l2) .conversionConfirmed 1`. -/
theorem RM025_levelEqual_acceptsFrom (amb : Ambient) (l1 l2 : Level)
    (heq : eqN l1 l2) :
    TaskAcceptsFrom amb (.levelEqual l1 l2) .conversionConfirmed 1 := by
  intro b hb m hm
  cases b with
  | zero => exact absurd hb (Nat.not_succ_le_zero 0)
  | succ f =>
      exact runRawR_pos_eq_of_result (RM011_levelEqual_complete amb l1 l2 f heq) hm

/-- Two-way eventuality characterization for `.levelEqual`:
    `TaskEventuallyAccepts amb (.levelEqual l1 l2) .conversionConfirmed ↔ eqN l1 l2`. -/
theorem RM025_levelEqual_iff_eventual (amb : Ambient) (l1 l2 : Level) :
    TaskEventuallyAccepts amb (.levelEqual l1 l2) .conversionConfirmed ↔ eqN l1 l2 := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    exact RM011_levelEqual_sound amb l1 l2 b hkr
  · intro heq
    exact taskAcceptsFrom_imp_eventuallyAccepts
      (RM025_levelEqual_acceptsFrom amb l1 l2 heq)

/-- `lookupType amb.ctx i = some A` implies
    `TaskAcceptsFrom amb (.lookupLocal i) (.inferredType A) 1`. -/
theorem RM025_lookupLocal_acceptsFrom (amb : Ambient) (i : Nat) (A : Expr Nat)
    (hlk : lookupType amb.ctx i = some A) :
    TaskAcceptsFrom amb (.lookupLocal i) (.inferredType A) 1 := by
  intro b hb m hm
  cases b with
  | zero => exact absurd hb (Nat.not_succ_le_zero 0)
  | succ f =>
      apply runRawR_pos_eq_of_result _ hm
      simp only [kernelStepRaw, hlk]

/-- Two-way eventuality characterization for `.lookupLocal`:
    `TaskEventuallyAccepts amb (.lookupLocal i) (.inferredType A) ↔ lookupType amb.ctx i = some A`. -/
theorem RM025_lookupLocal_iff_eventual (amb : Ambient) (i : Nat) (A : Expr Nat) :
    TaskEventuallyAccepts amb (.lookupLocal i) (.inferredType A) ↔
      lookupType amb.ctx i = some A := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    exact (RM012_lookupLocal_accepted ⟨amb, .lookupLocal i, b⟩ i A rfl hkr).1
  · intro hlk
    exact taskAcceptsFrom_imp_eventuallyAccepts
      (RM025_lookupLocal_acceptsFrom amb i A hlk)

/-- Helper: `inferCert` at `.const r []` when `E.members r = some m` and `0 = m.arity`. -/
theorem inferCert_const_nil_ok {E : ResolvedEnv} {n f : Nat} {Γ : LCtx}
    {r : Nat} {m : CheckedMember}
    (hmemb : E.members r = some m) (har : 0 = m.arity) :
    ∃ c, inferCert E n (f + 1) Γ (.const r []) = .ok c ∧
      c.1 = instantiateLevels [] m.mtype := by
  rw [inferCert]
  split
  · next hls =>
      split
      · next m' hm' =>
          have hm_eq : m' = m := by
            rw [hmemb] at hm'
            injection hm' with h1
            exact h1.symm
          subst hm_eq
          split
          · exact ⟨_, rfl, rfl⟩
          · next h0 => exact (h0 har).elim
      · next hm' =>
          rw [hmemb] at hm'
          nomatch hm'
  · next hls => exact (hls rfl).elim

/-- Two-way eventuality characterization for `.lookupDeclaration`:
    `TaskEventuallyAccepts amb (.lookupDeclaration r ls) (.inferredType T)` holds
    iff `ls = []` and `amb.env.members r = some m` with `0 = m.arity` and
    `T = instantiateLevels ls m.mtype`. -/
theorem RM025_lookupDeclaration_iff_eventual (amb : Ambient) (r : Nat)
    (ls : List Level) (T : Expr Nat) :
    TaskEventuallyAccepts amb (.lookupDeclaration r ls) (.inferredType T) ↔
      ∃ m : CheckedMember,
        ls = [] ∧ amb.env.members r = some m ∧ 0 = m.arity ∧
          T = instantiateLevels ls m.mtype := by
  constructor
  · rintro ⟨b, m_step, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    have ⟨m, hls, hmemb, har, hT⟩ :=
      RM013_lookupDeclaration_resolved ⟨amb, .lookupDeclaration r ls, b⟩ r ls T rfl hkr
    exact ⟨m, hls, hmemb, har, hT⟩
  · rintro ⟨m, hls, hmemb, har, hT⟩
    subst hls hT
    rcases inferCert_const_nil_ok (n := amb.univs) (f := 0) (Γ := amb.ctx) hmemb har with
      ⟨⟨T', hty⟩, hok, hT'⟩
    simp only at hT'
    subst hT'
    refine ⟨1, 1, ?_⟩
    apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
    simp only [kernelStepRaw, hok]

/-- Two-way eventuality characterization for `.syntaxEqual` (confirmed). -/
theorem RM025_syntaxEqual_iff_eventual (amb : Ambient) (a b : Expr Nat) :
    TaskEventuallyAccepts amb (.syntaxEqual a b) .conversionConfirmed ↔ a = b := by
  constructor
  · rintro ⟨f, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases f with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw] at hkr
        by_cases hab : a = b
        · exact hab
        · rw [if_neg hab] at hkr
          exact nomatch hkr
  · intro hab
    refine ⟨1, 1, ?_⟩
    apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
    simp only [kernelStepRaw, if_pos hab]

/-- Two-way eventuality characterization for `.syntaxEqual` (mismatch). -/
theorem RM025_syntaxEqual_mismatch_iff_eventual (amb : Ambient) (a b : Expr Nat) :
    TaskEventuallyAccepts amb (.syntaxEqual a b) .conversionMismatch ↔ a ≠ b := by
  constructor
  · rintro ⟨f, m, hm⟩ hab
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases f with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw, if_pos hab] at hkr
        exact nomatch hkr
  · intro hab
    refine ⟨1, 1, ?_⟩
    apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
    simp only [kernelStepRaw, if_neg hab]

/-- Two-way eventuality characterization for `.convAt` (`.conversionConfirmed`):
    `TaskEventuallyAccepts ⟨E, n, Γ⟩ (.convAt A l r) .conversionConfirmed` holds
    iff some finite fuel `f` produces `convCert E n f Γ A l r = .ok c`. -/
theorem RM025_convAt_confirmed_iff_eventual (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A l r : Expr Nat) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.convAt A l r) .conversionConfirmed ↔
      ∃ (f : Nat) (c : Conv E n Γ l r), convCert E n f Γ A l r = .ok c := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases b with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw] at hkr
        split at hkr
        · next c hc => exact ⟨f₀ + 1, c, hc⟩
        · split at hkr <;> exact nomatch hkr
  · rintro ⟨f, c, hc⟩
    cases f with
    | zero =>
        rw [convCert] at hc
        cases hc
    | succ f₀ =>
        refine ⟨f₀ + 1, 1, ?_⟩
        apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
        simp only [kernelStepRaw, hc]

/-- Soundness of eventual `.convAt` confirmation: yields `Nonempty (Conv E n Γ l r)`. -/
theorem RM025_convAt_eventual_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A l r : Expr Nat}
    (hev : TaskEventuallyAccepts ⟨E, n, Γ⟩ (.convAt A l r) .conversionConfirmed) :
    Nonempty (Conv E n Γ l r) := by
  rcases (RM025_convAt_confirmed_iff_eventual E n Γ A l r).mp hev with ⟨_, c, _⟩
  exact ⟨c⟩

/-- Two-way eventuality characterization for `.infer`:
    `TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType T)` holds
    iff some finite fuel `f` produces `inferCert E n f Γ e = .ok ⟨T, h⟩`. -/
theorem RM025_infer_eventual_iff (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e T : Expr Nat) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType T) ↔
      ∃ (f : Nat) (c : Σ' (T' : Expr Nat), HasTy E n Γ e T'),
        inferCert E n f Γ e = .ok c ∧ c.1 = T := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases b with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw] at hkr
        split at hkr
        · next T' hty hc =>
            injection hkr with h1
            injection h1 with h2
            injection h2 with h3
            exact ⟨f₀ + 1, ⟨T', hty⟩, hc, h3⟩
        · exact nomatch hkr
  · rintro ⟨f, ⟨T', hty⟩, hc, hT⟩
    simp only at hT
    subst hT
    cases f with
    | zero =>
        cases e <;> simp only [inferCert] at hc <;> nomatch hc
    | succ f₀ =>
        refine ⟨f₀ + 1, 1, ?_⟩
        apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
        simp only [kernelStepRaw, hc]

/-- Soundness + eventuality characterization for `.infer`. -/
theorem RM025_infer_sound_and_eventual_iff (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (e T : Expr Nat) :
    (TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType T) ↔
      ∃ (f : Nat) (c : Σ' (T' : Expr Nat), HasTy E n Γ e T'),
        inferCert E n f Γ e = .ok c ∧ c.1 = T) ∧
    (TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType T) →
      Nonempty (HasTy E n Γ e T)) := by
  refine ⟨RM025_infer_eventual_iff E n Γ e T, fun hev => ?_⟩
  rcases (RM025_infer_eventual_iff E n Γ e T).mp hev with ⟨_, ⟨T', hty⟩, _, hT⟩
  simp only at hT
  subst hT
  exact ⟨hty⟩

/-- Two-way eventuality characterization for `.check`:
    `TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked` holds
    iff some finite fuel `f` produces `checkCert E n f Γ e A = .ok c`. -/
theorem RM025_check_eventual_iff (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e A : Expr Nat) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked ↔
      ∃ (f : Nat) (c : HasTy E n Γ e A), checkCert E n f Γ e A = .ok c := by
  constructor
  · rintro ⟨b, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases b with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw] at hkr
        split at hkr
        · next c hc => exact ⟨f₀ + 1, c, hc⟩
        · exact nomatch hkr
  · rintro ⟨f, c, hc⟩
    cases f with
    | zero =>
        rw [checkCert] at hc
        cases hc
    | succ f₀ =>
        refine ⟨f₀ + 1, 1, ?_⟩
        apply runRawR_pos_eq_of_result _ (Nat.le_refl 1)
        simp only [kernelStepRaw, hc]

/-- Soundness + eventuality characterization for `.check`:
    eventual acceptance of `.check e A` is equivalent to `checkCert` succeeding at
    some finite fuel `f`, and implies `Nonempty (HasTy E n Γ e A)`. -/
theorem RM025_check_sound_and_eventual_iff (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (e A : Expr Nat) :
    (TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked ↔
      ∃ (f : Nat) (c : HasTy E n Γ e A), checkCert E n f Γ e A = .ok c) ∧
    (TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked →
      Nonempty (HasTy E n Γ e A)) := by
  refine ⟨RM025_check_eventual_iff E n Γ e A, fun hev => ?_⟩
  rcases (RM025_check_eventual_iff E n Γ e A).mp hev with ⟨_, c, _⟩
  exact ⟨c⟩

/-! ## 7. Concrete Accepting and Refused Pins (and `.syntaxEqual` Payload-Negative Exception) -/

/-- Helper 1-member environment for `.lookupDeclaration` pin:
    member `0` is an axiom of arity `0` and type `Sort 0`. -/
def declPinMember : CheckedMember where
  mclass := .axiomM
  arity := 0
  mtype := .sort .zero
  body := none

def declPinEnv : ResolvedEnv := extendEnv emptyEnv 0 declPinMember

/-- **WHNF Accepting Pin:** 2-step β-chain `(λx:Sort 0. (λy:Sort 0. y)) (Sort 0) (Sort 0)`
    suspends at outer budget `0`, refuses `[rcic_whnf_fuel]` at inner budget `1`,
    and is accepted with `.inferredWhnf (Sort 0) (Sort 0)` for all inner budgets `b ≥ 2`
    (`TaskAcceptsFrom ... 2` and `TaskEventuallyAccepts`). -/
def whnfAcceptExpr : Expr Nat :=
  .app (.app (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 0))) (.sort .zero)) (.sort .zero)

theorem pin_whnf_eventual_accepts :
    runRawR 0 ⟨⟨emptyEnv, 0, []⟩, .whnfAt (.sort .zero) whnfAcceptExpr, 2⟩ =
      .suspended ⟨⟨emptyEnv, 0, []⟩, .whnfAt (.sort .zero) whnfAcceptExpr, 2⟩ ∧
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .whnfAt (.sort .zero) whnfAcceptExpr, 1⟩ =
      .done (.refused "[rcic_whnf_fuel]") ∧
    TaskAcceptsFrom ⟨emptyEnv, 0, []⟩
      (.whnfAt (.sort .zero) whnfAcceptExpr)
      (.inferredWhnf (.sort .zero) (.sort .zero)) 2 ∧
    TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩
      (.whnfAt (.sort .zero) whnfAcceptExpr)
      (.inferredWhnf (.sort .zero) (.sort .zero)) := by
  have h2 : runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .whnfAt (.sort .zero) whnfAcceptExpr, 2⟩ =
      .done (.accepted (.inferredWhnf (.sort .zero) (.sort .zero))) := rfl
  have hfrom : TaskAcceptsFrom ⟨emptyEnv, 0, []⟩
      (.whnfAt (.sort .zero) whnfAcceptExpr)
      (.inferredWhnf (.sort .zero) (.sort .zero)) 2 :=
    fun _ hb _ hm => runRawR_accepted_budget_mono trivial h2 hb hm
  exact ⟨rfl, rfl, hfrom, taskAcceptsFrom_imp_eventuallyAccepts hfrom⟩

/-- **WHNF `MachineRed` Pin:** explicit `MachineRed` witness driving `RM025_whnf_eventual`
    and `RM025_whnf_eventual_iff` on `whnfAcceptExpr`. -/
theorem pin_whnf_eventual_from_machineRed :
    ∃ k : MachineRed emptyEnv 0 [] whnfAcceptExpr (.sort .zero),
      machineWhnfDone emptyEnv (.sort .zero) = true ∧
      TaskAcceptsFrom ⟨emptyEnv, 0, []⟩
        (.whnfAt (.sort .zero) whnfAcceptExpr)
        (.inferredWhnf (.sort .zero) (.sort .zero))
        (Nat.max 1 (machineRedSteps k)) ∧
      TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩
        (.whnfAt (.sort .zero) whnfAcceptExpr)
        (.inferredWhnf (.sort .zero) (.sort .zero)) := by
  have hk : MachineRed emptyEnv 0 [] whnfAcceptExpr (.sort .zero) :=
    .headBeta [] (.sort .zero) (.lam (.sort .zero) (.bvar 0)) (.sort .zero) [.sort .zero]
      (.headBeta [] (.sort .zero) (.bvar 0) (.sort .zero) []
        (.refl [] (.sort .zero)))
  exact ⟨hk, rfl, RM025_whnf_eventual (.sort .zero) hk rfl,
    (RM025_whnf_eventual_iff emptyEnv 0 [] (.sort .zero) whnfAcceptExpr (.sort .zero)).mpr
      ⟨⟨hk⟩, rfl⟩⟩

/-- **WHNF Refused Pin:** `.whnfAt (Sort 0) (.lit t)` refuses `[rcic_whnf_unknown_ctor]`
    and never eventually accepts any payload `p` at any budget. -/
theorem pin_whnf_eventual_refused (amb : Ambient) (t : Nat) :
    runRawR 1 ⟨amb, .whnfAt (.sort .zero) (.lit t), 1⟩ =
      .done (.refused "[rcic_whnf_unknown_ctor]") ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts amb (.whnfAt (.sort .zero) (.lit t)) p := by
  have href : runRawR 1 ⟨amb, .whnfAt (.sort .zero) (.lit t), 1⟩ =
      .done (.refused "[rcic_whnf_unknown_ctor]") := rfl
  refine ⟨href, fun p => ?_⟩
  apply not_taskEventuallyAccepts_of_refused (r := "[rcic_whnf_unknown_ctor]") _ href p
  simp only [RefusalMonotoneTask]
  intro h
  nomatch h

/-- **Level Equality Accepting Pin:** nontrivial `imax 1 (param 0) =ₙ param 0`
    accepts from budget `1` onward (`TaskEventuallyAccepts`). -/
theorem pin_levelEqual_eventual_accepts (amb : Ambient) :
    TaskAcceptsFrom amb
      (.levelEqual (.imax (.succ .zero) (.param 0)) (.param 0))
      .conversionConfirmed 1 ∧
    TaskEventuallyAccepts amb
      (.levelEqual (.imax (.succ .zero) (.param 0)) (.param 0))
      .conversionConfirmed := by
  have heq : eqN (.imax (.succ .zero) (.param 0)) (.param 0) :=
    RM011_levelEqual_sound amb _ _ 1 (RM011_imax_param_accepted amb)
  have hfrom := RM025_levelEqual_acceptsFrom amb _ _ heq
  exact ⟨hfrom, taskAcceptsFrom_imp_eventuallyAccepts hfrom⟩

/-- **Level Equality Refused Pin:** `param 0` vs `param 1` refuses at budget `1`
    and never eventually accepts any payload `p` at any budget. -/
theorem pin_levelEqual_eventual_refused (amb : Ambient) :
    runRawR 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
      .done (.refused "[rcic_level_not_equal]") ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts amb (.levelEqual (.param 0) (.param 1)) p := by
  have href : runRawR 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
      .done (.refused "[rcic_level_not_equal]") :=
    runRawR_succ_result 0 (RM011_param0_param1_refused amb)
  exact ⟨href, not_taskEventuallyAccepts_of_refused trivial href⟩

/-- **Local Lookup Accepting Pin:** bound variable `0` in `[.assumption (Sort 0)]`
    accepts `.inferredType (Sort 0)` from budget `1` onward. -/
theorem pin_lookupLocal_eventual_accepts :
    TaskAcceptsFrom ⟨emptyEnv, 0, [.assumption (.sort .zero)]⟩
      (.lookupLocal 0) (.inferredType (.sort .zero)) 1 ∧
    TaskEventuallyAccepts ⟨emptyEnv, 0, [.assumption (.sort .zero)]⟩
      (.lookupLocal 0) (.inferredType (.sort .zero)) := by
  have hfrom := RM025_lookupLocal_acceptsFrom
    ⟨emptyEnv, 0, [.assumption (.sort .zero)]⟩ 0 (.sort .zero) rfl
  exact ⟨hfrom, taskAcceptsFrom_imp_eventuallyAccepts hfrom⟩

/-- **Local Lookup Refused Pin:** unbound variable `0` in `[]` refuses
    `[rcic_pi_check_bvar_unbound]` and never eventually accepts any payload `p`. -/
theorem pin_lookupLocal_eventual_refused :
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .lookupLocal 0, 1⟩ =
      .done (.refused "[rcic_pi_check_bvar_unbound]") ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩ (.lookupLocal 0) p := by
  have href : runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .lookupLocal 0, 1⟩ =
      .done (.refused "[rcic_pi_check_bvar_unbound]") := rfl
  exact ⟨href, not_taskEventuallyAccepts_of_refused trivial href⟩

/-- **Declaration Lookup Accepting Pin:** member `0` in `declPinEnv` accepts
    `.inferredType (Sort 0)`. -/
theorem pin_lookupDeclaration_eventual_accepts :
    TaskEventuallyAccepts ⟨declPinEnv, 0, []⟩
      (.lookupDeclaration 0 []) (.inferredType (.sort .zero)) := by
  rw [RM025_lookupDeclaration_iff_eventual]
  exact ⟨declPinMember, rfl, rfl, rfl, rfl⟩

/-- **Declaration Lookup Refused Pin:** missing declaration `0` in `emptyEnv`
    refuses `[rcic_lookup_group_not_found]` and never eventually accepts any `p`. -/
theorem pin_lookupDeclaration_eventual_refused :
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .lookupDeclaration 0 [], 1⟩ =
      .done (.refused "[rcic_lookup_group_not_found]") ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩ (.lookupDeclaration 0 []) p := by
  have href : runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .lookupDeclaration 0 [], 1⟩ =
      .done (.refused "[rcic_lookup_group_not_found]") := rfl
  exact ⟨href, not_taskEventuallyAccepts_of_refused trivial href⟩

/-- **Syntax Equality Accepting & Opposite-Tag Pins (NOT a refused-input pin;
    `.syntaxEqual` is never refused, see §8):** equal sorts eventually
    accept `.conversionConfirmed` (and never `.conversionMismatch`), while
    distinct sorts never accept `.conversionConfirmed` (and at budget `0` never
    accept any payload). -/
theorem pin_syntaxEqual_eventual_confirmed_and_opposite_tag (amb : Ambient) :
    TaskEventuallyAccepts amb (.syntaxEqual (.sort .zero) (.sort .zero))
      .conversionConfirmed ∧
    ¬ TaskEventuallyAccepts amb
      (.syntaxEqual (.sort .zero) (.sort (.succ .zero)))
      .conversionConfirmed ∧
    ∀ p : AcceptedPayload,
      ¬ EventuallyAccepts ⟨amb, .syntaxEqual (.sort .zero) (.sort .zero), 0⟩ p := by
  refine ⟨(RM025_syntaxEqual_iff_eventual amb _ _).mpr rfl, ?_,
    not_eventuallyAccepts_budget_zero amb _⟩
  rw [RM025_syntaxEqual_iff_eventual]
  intro h
  nomatch h

/-- **Conversion Accepting Pin:** 2-step β-conversion `whnfAcceptExpr ≡ Sort 0`
    at `Sort 1` refuses `[rcic_whnf_fuel]` at inner budgets `1` and `2`, and
    accepts `.conversionConfirmed` from inner budget `3` onward. -/
theorem pin_convAt_eventual_accepts (amb : Ambient) :
    runRawR 1 ⟨amb, .convAt (.sort (.succ .zero)) whnfAcceptExpr (.sort .zero), 1⟩ =
      .done (.refused "[rcic_whnf_fuel]") ∧
    runRawR 1 ⟨amb, .convAt (.sort (.succ .zero)) whnfAcceptExpr (.sort .zero), 2⟩ =
      .done (.refused "[rcic_whnf_fuel]") ∧
    runRawR 1 ⟨amb, .convAt (.sort (.succ .zero)) whnfAcceptExpr (.sort .zero), 3⟩ =
      .done (.accepted .conversionConfirmed) ∧
    TaskEventuallyAccepts amb
      (.convAt (.sort (.succ .zero)) whnfAcceptExpr (.sort .zero))
      .conversionConfirmed :=
  ⟨rfl, rfl, rfl, ⟨3, 1, rfl⟩⟩

/-- **Conversion Refused Pin (`RM025_irr_not_eventual`):** proof-irrelevance
    conversion (`Sort 1` vs `Sort 2` at `Sort 0`) is `TaskAlwaysRefused` with
    `"[rcic_conv_irrelevance_out_of_slice]"` and never eventually accepts any `p`. -/
theorem RM025_irr_not_eventual (amb : Ambient) :
    TaskAlwaysRefused amb
      (.convAt (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero))))
      "[rcic_conv_irrelevance_out_of_slice]" ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts amb
        (.convAt (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))) p := by
  have halw : TaskAlwaysRefused amb
      (.convAt (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero))))
      "[rcic_conv_irrelevance_out_of_slice]" := by
    intro b hb m hm
    cases b with
    | zero => exact absurd hb (Nat.not_succ_le_zero 0)
    | succ k =>
        exact runRawR_pos_eq_of_result (RM018_irr_branch_refused amb k) hm
  exact ⟨halw, not_taskEventuallyAccepts_of_alwaysRefused halw⟩

/-- **Boundary Tooth (`pin_convAt_mismatch_not_budget_mono`):** exhibits an
    `.app`-congruence conversion task that accepts `.conversionMismatch` at
    inner budget `1` (because the `.app` congruence arm re-labels a subcall
    `[rcic_conv_fuel]` into `[rcic_conv_mismatch]`) and accepts
    `.conversionConfirmed` at inner budget `3`. This proves `PositiveTaskPayload`
    is the exact mathematical boundary of inner-budget monotonicity. -/
def convAppLeft : Expr Nat := .app (.sort .zero) (.sort .zero)
def convAppRight : Expr Nat :=
  .app (.sort .zero) (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))

theorem pin_convAt_mismatch_not_budget_mono (amb : Ambient) :
    runRawR 1 ⟨amb, .convAt (.sort (.succ .zero)) convAppLeft convAppRight, 1⟩ =
      .done (.accepted .conversionMismatch) ∧
    runRawR 1 ⟨amb, .convAt (.sort (.succ .zero)) convAppLeft convAppRight, 3⟩ =
      .done (.accepted .conversionConfirmed) :=
  ⟨rfl, rfl⟩

/-- **Inference Accepting Pin:** `(λx:Sort 1. x) (Sort 0)` refuses
    `[rcic_infer_fuel]` at inner budgets `1` and `2`, and accepts
    `.inferredType (Sort 1)` from inner budget `3` onward. -/
def inferAcceptExpr : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)

theorem pin_infer_eventual_accepts (E : ResolvedEnv) (n : Nat) :
    runRawR 1 ⟨⟨E, n, []⟩, .infer inferAcceptExpr, 1⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    runRawR 1 ⟨⟨E, n, []⟩, .infer inferAcceptExpr, 2⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    runRawR 1 ⟨⟨E, n, []⟩, .infer inferAcceptExpr, 3⟩ =
      .done (.accepted (.inferredType (.sort (.succ .zero)))) ∧
    TaskEventuallyAccepts ⟨E, n, []⟩
      (.infer inferAcceptExpr) (.inferredType (.sort (.succ .zero))) :=
  ⟨rfl, rfl, rfl, ⟨3, 1, rfl⟩⟩

/-- **Inference Refused Pin (`RM025_lit_infer_not_eventual`):** `.infer (.lit t)`
    is `TaskAlwaysRefused` with `"[rcic_infer_unknown_ctor]"` and never
    eventually accepts any payload `p` at any budget. -/
theorem RM025_lit_infer_not_eventual (amb : Ambient) (t : Nat) :
    TaskAlwaysRefused amb (.infer (.lit t)) "[rcic_infer_unknown_ctor]" ∧
    ∀ p : AcceptedPayload, ¬ TaskEventuallyAccepts amb (.infer (.lit t)) p := by
  have halw : TaskAlwaysRefused amb (.infer (.lit t)) "[rcic_infer_unknown_ctor]" := by
    intro b hb m hm
    cases b with
    | zero => exact absurd hb (Nat.not_succ_le_zero 0)
    | succ k =>
        exact runRawR_pos_eq_of_result (RM025_lit_infer_refused amb t k) hm
  exact ⟨halw, not_taskEventuallyAccepts_of_alwaysRefused halw⟩

/-- **Check Accepting Pin:** checking `inferAcceptExpr` against `Sort 1`
    suspends at outer budget `0`, resumes via `«continue» 1` to `.done (.accepted .checked)`
    at inner budget `4`, refuses with fuel exhaustion at inner budgets `1..3`,
    and satisfies `TaskAcceptsFrom ... 4`, `TaskEventuallyAccepts`, and `HasTy`. -/
theorem pin_check_eventual_accepts :
    runRawR 0 ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 4⟩ =
      .suspended ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 4⟩ ∧
    «continue» 1
      (runRawR 0 ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 4⟩) =
      .done (.accepted .checked) ∧
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 1⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 3⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    TaskAcceptsFrom ⟨emptyEnv, 0, []⟩
      (.check inferAcceptExpr (.sort (.succ .zero))) .checked 4 ∧
    TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩
      (.check inferAcceptExpr (.sort (.succ .zero))) .checked ∧
    Nonempty (HasTy emptyEnv 0 [] inferAcceptExpr (.sort (.succ .zero))) := by
  have hacc4 : runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .check inferAcceptExpr (.sort (.succ .zero)), 4⟩ =
      .done (.accepted .checked) := rfl
  have hev : TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩
      (.check inferAcceptExpr (.sort (.succ .zero))) .checked := ⟨4, 1, hacc4⟩
  have hfrom : TaskAcceptsFrom ⟨emptyEnv, 0, []⟩
      (.check inferAcceptExpr (.sort (.succ .zero))) .checked 4 :=
    fun b hb m hm => runRawR_accepted_budget_mono trivial hacc4 hb hm
  have hty := (RM025_check_sound_and_eventual_iff emptyEnv 0 []
    inferAcceptExpr (.sort (.succ .zero))).2 hev
  exact ⟨rfl, rfl, rfl, rfl, hfrom, hev, hty⟩

/-- **Check Refused Pin (literal-free ill-typed term):** checking `Sort 0 : Sort 0`
    refuses `[rcic_infer_fuel]` at budget `1`, refuses `[rcic_conv_irrelevance_out_of_slice]`
    at budget `2`, and `[rcic_conv_irrelevance_out_of_slice]` for all `b ≥ 3`
    (`TaskRefusesFrom ... 3`), and never eventually accepts any payload `p`. -/
theorem pin_check_eventual_refused (amb : Ambient) :
    TaskRefusesFrom amb (.check (.sort .zero) (.sort .zero))
      "[rcic_conv_irrelevance_out_of_slice]" 3 ∧
    ∀ p : AcceptedPayload,
      ¬ TaskEventuallyAccepts amb (.check (.sort .zero) (.sort .zero)) p := by
  have hfrom : TaskRefusesFrom amb (.check (.sort .zero) (.sort .zero))
      "[rcic_conv_irrelevance_out_of_slice]" 3 := by
    intro b hb m hm
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 3 := ⟨b - 3, (Nat.sub_add_cancel hb).symm⟩
    apply runRawR_pos_eq_of_result _ hm
    cases k with
    | zero => rfl
    | succ k' => rfl
  refine ⟨hfrom, fun p => ?_⟩
  exact not_taskEventuallyAccepts_of_refusesFrom hfrom trivial

/-! ## 8. `.syntaxEqual` Structural Boundary, Payload-Negative Control, and Universal All-Budget Refusal Controls -/

/-- Any task `t` with `∀ p, ¬ TaskEventuallyAccepts amb t p` never reaches
    `.done (.accepted p)` at ANY inner budget `b` and outer budget `m`
    (including `0`). -/
theorem runRawR_ne_accepted_of_not_taskEventuallyAccepts {amb : Ambient} {t : RawTask}
    (hno : ∀ p : AcceptedPayload, ¬ TaskEventuallyAccepts amb t p)
    (b m : Nat) (p : AcceptedPayload) :
    runRawR m ⟨amb, t, b⟩ ≠ .done (.accepted p) :=
  fun h => hno p ⟨b, m, h⟩

/-- When `a = b`, `.syntaxEqual a b` accepts `.conversionConfirmed` at every
    positive inner/outer budget (`TaskAcceptsFrom ... 1`). -/
theorem syntaxEqual_acceptsFrom_confirmed (amb : Ambient) {a b : Expr Nat}
    (hab : a = b) :
    TaskAcceptsFrom amb (.syntaxEqual a b) .conversionConfirmed 1 := by
  intro f hf m hm
  cases f with
  | zero => exact absurd hf (Nat.not_succ_le_zero 0)
  | succ f₀ =>
      apply runRawR_pos_eq_of_result _ hm
      simp only [kernelStepRaw, if_pos hab]

/-- When `a ≠ b`, `.syntaxEqual a b` accepts `.conversionMismatch` at every
    positive inner/outer budget (`TaskAcceptsFrom ... 1`). -/
theorem syntaxEqual_acceptsFrom_mismatch (amb : Ambient) {a b : Expr Nat}
    (hab : a ≠ b) :
    TaskAcceptsFrom amb (.syntaxEqual a b) .conversionMismatch 1 := by
  intro f hf m hm
  cases f with
  | zero => exact absurd hf (Nat.not_succ_le_zero 0)
  | succ f₀ =>
      apply runRawR_pos_eq_of_result _ hm
      simp only [kernelStepRaw, if_neg hab]

/-- Universal structural boundary for `.syntaxEqual` (`RcicMachine.lean:452-454`):
    every `.syntaxEqual a b` input at every positive inner budget `f ≥ 1` and
    outer budget `m ≥ 1` returns `.done (.accepted .conversionConfirmed)` (if `a = b`)
    or `.done (.accepted .conversionMismatch)` (if `a ≠ b`). -/
theorem syntaxEqual_always_accepts_confirmed_or_mismatch (amb : Ambient)
    (a b : Expr Nat) {f m : Nat} (hf : 1 ≤ f) (hm : 1 ≤ m) :
    runRawR m ⟨amb, .syntaxEqual a b, f⟩ =
      .done (.accepted (if a = b then .conversionConfirmed else .conversionMismatch)) := by
  by_cases hab : a = b
  · rw [if_pos hab]
    exact syntaxEqual_acceptsFrom_confirmed amb hab f hf m hm
  · rw [if_neg hab]
    exact syntaxEqual_acceptsFrom_mismatch amb hab f hf m hm

/-- `.syntaxEqual a b` never produces `.done (.refused r)` at ANY inner budget `f`
    or outer budget `m`. -/
theorem syntaxEqual_never_refused (amb : Ambient) (a b : Expr Nat)
    (f m : Nat) (r : String) :
    runRawR m ⟨amb, .syntaxEqual a b, f⟩ ≠ .done (.refused r) := by
  intro h
  have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done h
  cases f with
  | zero =>
      simp only [kernelStepRaw] at hkr
      exact nomatch hkr
  | succ f₀ =>
      simp only [kernelStepRaw] at hkr
      by_cases hab : a = b
      · rw [if_pos hab] at hkr
        exact nomatch hkr
      · rw [if_neg hab] at hkr
        exact nomatch hkr

/-- No `.syntaxEqual a b` task has a `TaskRefusesFrom` threshold `B` for any
    refusal residue `r`. -/
theorem not_taskRefusesFrom_syntaxEqual (amb : Ambient) (a b : Expr Nat)
    (r : String) (B : Nat) :
    ¬ TaskRefusesFrom amb (.syntaxEqual a b) r B := by
  intro hfrom
  have href := hfrom (B + 1) (Nat.le_succ B) 1 (Nat.le_refl 1)
  exact syntaxEqual_never_refused amb a b (B + 1) 1 r href

/-- Exact payload dichotomy for `.syntaxEqual a b`:
    `TaskEventuallyAccepts amb (.syntaxEqual a b) p` holds iff either
    `p = .conversionConfirmed ∧ a = b` or `p = .conversionMismatch ∧ a ≠ b`. -/
theorem syntaxEqual_payload_dichotomy (amb : Ambient) (a b : Expr Nat)
    (p : AcceptedPayload) :
    TaskEventuallyAccepts amb (.syntaxEqual a b) p ↔
      (p = .conversionConfirmed ∧ a = b) ∨ (p = .conversionMismatch ∧ a ≠ b) := by
  constructor
  · rintro ⟨f, m, hm⟩
    have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done hm
    cases f with
    | zero =>
        simp only [kernelStepRaw] at hkr
        exact nomatch hkr
    | succ f₀ =>
        simp only [kernelStepRaw] at hkr
        by_cases hab : a = b
        · rw [if_pos hab] at hkr
          injection hkr with h1
          injection h1 with hp
          exact Or.inl ⟨hp.symm, hab⟩
        · rw [if_neg hab] at hkr
          injection hkr with h1
          injection h1 with hp
          exact Or.inr ⟨hp.symm, hab⟩
  · rintro (⟨rfl, hab⟩ | ⟨rfl, hab⟩)
    · exact (RM025_syntaxEqual_iff_eventual amb a b).mpr hab
    · exact (RM025_syntaxEqual_mismatch_iff_eventual amb a b).mpr hab

/-- **Syntax Equality Payload-Negative Control Pin:** seals both the real
    accepting `.conversionConfirmed` run on equal sorts, the real accepting
    `.conversionMismatch` run on unequal sorts, the opposite-tag exclusions,
    and the universal absence of any `TaskRefusesFrom` threshold. -/
theorem pin_syntaxEqual_payload_negative_control (amb : Ambient) :
    TaskAcceptsFrom amb (.syntaxEqual (.sort .zero) (.sort .zero))
      .conversionConfirmed 1 ∧
    TaskEventuallyAccepts amb (.syntaxEqual (.sort .zero) (.sort .zero))
      .conversionConfirmed ∧
    ¬ TaskEventuallyAccepts amb (.syntaxEqual (.sort .zero) (.sort .zero))
      .conversionMismatch ∧
    TaskAcceptsFrom amb (.syntaxEqual (.sort .zero) (.sort (.succ .zero)))
      .conversionMismatch 1 ∧
    TaskEventuallyAccepts amb (.syntaxEqual (.sort .zero) (.sort (.succ .zero)))
      .conversionMismatch ∧
    ¬ TaskEventuallyAccepts amb (.syntaxEqual (.sort .zero) (.sort (.succ .zero)))
      .conversionConfirmed ∧
    (∀ a b : Expr Nat, ∀ r : String, ∀ B : Nat,
      ¬ TaskRefusesFrom amb (.syntaxEqual a b) r B) := by
  have heq : (Expr.sort .zero : Expr Nat) = .sort .zero := rfl
  have hne : (Expr.sort .zero : Expr Nat) ≠ .sort (.succ .zero) := by
    intro h
    nomatch h
  refine ⟨syntaxEqual_acceptsFrom_confirmed amb heq,
    (RM025_syntaxEqual_iff_eventual amb _ _).mpr heq,
    fun hm => ((RM025_syntaxEqual_mismatch_iff_eventual amb _ _).mp hm) heq,
    syntaxEqual_acceptsFrom_mismatch amb hne,
    (RM025_syntaxEqual_mismatch_iff_eventual amb _ _).mpr hne,
    fun hc => hne ((RM025_syntaxEqual_iff_eventual amb _ _).mp hc),
    not_taskRefusesFrom_syntaxEqual amb⟩

/-- **`.convType` Refusal Characterization (`RM025_convType_always_refused`):**
    `.convType A B` is `TaskAlwaysRefused` with `"[machine_task_not_implemented]"`
    and never eventually accepts any payload `p` at any budget. -/
theorem RM025_convType_always_refused (amb : Ambient) (A B : Expr Nat) :
    TaskAlwaysRefused amb (.convType A B) "[machine_task_not_implemented]" ∧
    (∀ p : AcceptedPayload, ¬ TaskEventuallyAccepts amb (.convType A B) p) ∧
    (∀ b m : Nat, ∀ p : AcceptedPayload,
      runRawR m ⟨amb, .convType A B, b⟩ ≠ .done (.accepted p)) := by
  have halw : TaskAlwaysRefused amb (.convType A B) "[machine_task_not_implemented]" := by
    intro b hb m hm
    cases b with
    | zero => exact absurd hb (Nat.not_succ_le_zero 0)
    | succ f =>
        apply runRawR_pos_eq_of_result _ hm
        rfl
  have hno : ∀ p : AcceptedPayload, ¬ TaskEventuallyAccepts amb (.convType A B) p :=
    not_taskEventuallyAccepts_of_alwaysRefused halw
  exact ⟨halw, hno, runRawR_ne_accepted_of_not_taskEventuallyAccepts hno⟩

/-- **All-Budget Refusal Pin (`pin_all_budgets_refused_tasks`):** proves for all
    8 refusable `RawTask` constructors (`whnfAt`, `levelEqual`, `lookupLocal`,
    `lookupDeclaration`, `convAt`, `infer`, `check`, `convType`) that:
    1. every positive budget `b ≥ 1, m ≥ 1` returns `.done (.refused _)`
       (`TaskAlwaysRefused` for the first 7 and `.convType`, and explicit
       refusal at `b = 1`, `b = 2`, and `TaskRefusesFrom ... 3` for `.check`), and
    2. at EVERY inner/outer budget `(b, m) : Nat × Nat` (all budgets `0..∞`),
       `runRawR m ⟨amb, t, b⟩ ≠ .done (.accepted p)`. -/
theorem pin_all_budgets_refused_tasks (amb : Ambient) :
    (TaskAlwaysRefused amb (.whnfAt (.sort .zero) (.lit 0)) "[rcic_whnf_unknown_ctor]" ∧
      ∀ b m p, runRawR m ⟨amb, .whnfAt (.sort .zero) (.lit 0), b⟩ ≠ .done (.accepted p)) ∧
    (TaskAlwaysRefused amb (.levelEqual (.param 0) (.param 1)) "[rcic_level_not_equal]" ∧
      ∀ b m p, runRawR m ⟨amb, .levelEqual (.param 0) (.param 1), b⟩ ≠ .done (.accepted p)) ∧
    (TaskAlwaysRefused ⟨emptyEnv, 0, []⟩ (.lookupLocal 0) "[rcic_pi_check_bvar_unbound]" ∧
      ∀ b m p, runRawR m ⟨⟨emptyEnv, 0, []⟩, .lookupLocal 0, b⟩ ≠ .done (.accepted p)) ∧
    (TaskAlwaysRefused ⟨emptyEnv, 0, []⟩ (.lookupDeclaration 0 []) "[rcic_lookup_group_not_found]" ∧
      ∀ b m p, runRawR m ⟨⟨emptyEnv, 0, []⟩, .lookupDeclaration 0 [], b⟩ ≠ .done (.accepted p)) ∧
    (TaskAlwaysRefused amb
        (.convAt (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero))))
        "[rcic_conv_irrelevance_out_of_slice]" ∧
      ∀ b m p,
        runRawR m ⟨amb, .convAt (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero))), b⟩ ≠
          .done (.accepted p)) ∧
    (TaskAlwaysRefused amb (.infer (.lit 0)) "[rcic_infer_unknown_ctor]" ∧
      ∀ b m p, runRawR m ⟨amb, .infer (.lit 0), b⟩ ≠ .done (.accepted p)) ∧
    ((∀ b m : Nat, 1 ≤ b → 1 ≤ m →
        ∃ r : String, runRawR m ⟨amb, .check (.sort .zero) (.sort .zero), b⟩ = .done (.refused r)) ∧
      TaskRefusesFrom amb (.check (.sort .zero) (.sort .zero))
        "[rcic_conv_irrelevance_out_of_slice]" 3 ∧
      ∀ b m p, runRawR m ⟨amb, .check (.sort .zero) (.sort .zero), b⟩ ≠ .done (.accepted p)) ∧
    (TaskAlwaysRefused amb (.convType (.sort .zero) (.sort .zero)) "[machine_task_not_implemented]" ∧
      ∀ b m p, runRawR m ⟨amb, .convType (.sort .zero) (.sort .zero), b⟩ ≠ .done (.accepted p)) := by
  have hwhnf_alw : TaskAlwaysRefused amb (.whnfAt (.sort .zero) (.lit 0)) "[rcic_whnf_unknown_ctor]" := by
    intro b hb m hm
    have h1 := (pin_whnf_eventual_refused amb 0).1
    exact runRawR_refused_budget_mono (by simp only [RefusalMonotoneTask]; intro h; nomatch h) h1 hb hm
  have hlvl_alw : TaskAlwaysRefused amb (.levelEqual (.param 0) (.param 1)) "[rcic_level_not_equal]" := by
    intro b hb m hm
    exact runRawR_refused_budget_mono trivial (pin_levelEqual_eventual_refused amb).1 hb hm
  have hloc_alw : TaskAlwaysRefused ⟨emptyEnv, 0, []⟩ (.lookupLocal 0) "[rcic_pi_check_bvar_unbound]" := by
    intro b hb m hm
    exact runRawR_refused_budget_mono trivial pin_lookupLocal_eventual_refused.1 hb hm
  have hdecl_alw : TaskAlwaysRefused ⟨emptyEnv, 0, []⟩ (.lookupDeclaration 0 []) "[rcic_lookup_group_not_found]" := by
    intro b hb m hm
    exact runRawR_refused_budget_mono trivial pin_lookupDeclaration_eventual_refused.1 hb hm
  have hchk_all_pos : ∀ b m : Nat, 1 ≤ b → 1 ≤ m →
      ∃ r : String, runRawR m ⟨amb, .check (.sort .zero) (.sort .zero), b⟩ = .done (.refused r) := by
    intro b m hb hm
    cases b with
    | zero => exact absurd hb (Nat.not_succ_le_zero 0)
    | succ b₀ =>
        cases b₀ with
        | zero =>
            have hkr1 : kernelStepRaw ⟨amb, .check (.sort .zero) (.sort .zero), 1⟩ =
                .result (.refused "[rcic_infer_fuel]") := rfl
            exact ⟨"[rcic_infer_fuel]", runRawR_pos_eq_of_result hkr1 hm⟩
        | succ b₁ =>
            cases b₁ with
            | zero =>
                have hkr2 : kernelStepRaw ⟨amb, .check (.sort .zero) (.sort .zero), 2⟩ =
                    .result (.refused "[rcic_conv_irrelevance_out_of_slice]") := rfl
                exact ⟨"[rcic_conv_irrelevance_out_of_slice]", runRawR_pos_eq_of_result hkr2 hm⟩
            | succ b₂ =>
                have hb3 : 3 ≤ b₂ + 3 := Nat.le_add_left 3 b₂
                exact ⟨"[rcic_conv_irrelevance_out_of_slice]",
                  (pin_check_eventual_refused amb).1 (b₂ + 3) hb3 m hm⟩
  exact ⟨
    ⟨hwhnf_alw, runRawR_ne_accepted_of_not_taskEventuallyAccepts (pin_whnf_eventual_refused amb 0).2⟩,
    ⟨hlvl_alw, runRawR_ne_accepted_of_not_taskEventuallyAccepts (pin_levelEqual_eventual_refused amb).2⟩,
    ⟨hloc_alw, runRawR_ne_accepted_of_not_taskEventuallyAccepts pin_lookupLocal_eventual_refused.2⟩,
    ⟨hdecl_alw, runRawR_ne_accepted_of_not_taskEventuallyAccepts pin_lookupDeclaration_eventual_refused.2⟩,
    ⟨(RM025_irr_not_eventual amb).1,
      runRawR_ne_accepted_of_not_taskEventuallyAccepts (RM025_irr_not_eventual amb).2⟩,
    ⟨(RM025_lit_infer_not_eventual amb 0).1,
      runRawR_ne_accepted_of_not_taskEventuallyAccepts (RM025_lit_infer_not_eventual amb 0).2⟩,
    ⟨hchk_all_pos, (pin_check_eventual_refused amb).1,
      runRawR_ne_accepted_of_not_taskEventuallyAccepts (pin_check_eventual_refused amb).2⟩,
    ⟨(RM025_convType_always_refused amb (.sort .zero) (.sort .zero)).1,
      (RM025_convType_always_refused amb (.sort .zero) (.sort .zero)).2.2⟩⟩

end Rcic.Machine.Eventual
