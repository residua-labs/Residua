/-

# `RcicRM025Restated` — the restated RM-025 as ONE census-facing theorem

#6546 ruling (17:17Z, Annex-26.18 pattern): RM-025's row — positive
eventuality `⊢ e : A → ∃f, run(f, Check) = accepted` (03 §15) — is **false
as stated**; the true content is the package below.

* **The refutation (Loop, Abel–Coquand).** At `pinLoopEnvT`, the term
  `Ω_X = (λx:X. x x)(λx:X. x x)` IS well-typed at `X`
  (`omegaT_pinLoop_typed` transported by `eraseEnv_pinLoopEnvA`), yet the
  typed machine **never accepts** `checkT2 X Ω_X` at any budget/fuel:
  `typedRun_check_omega_never`. The failure is structural, not
  fuel-bounded — and the machine's irrelevance-first conversion does NOT
  rescue it:

  - `checkWith`'s app arm exposes the function's type as a Π via `toPi?`
    → `whnfTy` → `headStep?`, which fires only δ on `transparent`
    (`definitionM`-only) constants or β on λ-heads. `X`'s spine is
    `const 62`-headed (recursor class) at a `bvar` major → `headStep?`
    is `none` at **every** fuel → `toPi? (lift 0 1 X) = none` →
    `checkWith (x x) = none` → `checkWith ω = none` → `checkWith Ω =
    none` → `tyAtC Ω X = none`, independently of `conv`.
  - `irrAt?` is never reached: it lives inside `convAt?`/`tyConv?`, but
    the `X`-as-Π exposure goes through `whnfTy` (head steps only). The
    declarative `X ≡ X → X` (`convT_pinLoop`) went through `ConvT.irr` on
    `t ≡ mk t : Loop` — the machine has no arm that manufactures a
    `mk`-headed major from an irr-equal one. Abel–Coquand, confirmed.

* **The positive part on the 26.18 cone.** `hopFacesA_of_envWf` — the
  normalization content 03 §15 deferred completeness to — on its exact
  cone (`AnnEnvA` + `PropStuckChainsA` + `PiHeadStepTypedA`).

* **The unconditional soundness floor.** `RM016T_check_sound` /
  `RM016T_run_check_sound` — acceptance carries the derivation in its
  payload; soundness never invokes completeness.

No `sorry`. `closure_claim` stays 0.
-/

import rcic.RcicNormalizingFalsePinLoop
import rcic.RcicPinLoopEraseWf
import rcic.RcicAnnLRChainG
import rcic.RcicTypedMachineAccept
import rcic.RcicTypedConv

namespace Rcic

open Declarative Declarative.Ann Machine

/-! ## (1) the structural refusal — `headStep?`/`whnfTy`/`toPi?` at `X` -/

/-- `headStep?` refuses any `const 62` spine: the recursor member is
    `recursorM`-class and `transparent` is `definitionM`-only — the match
    never reaches the args. -/
theorem headStep_pinLoopRec_none {n : Nat} {Γ : LCtx} {ls : List Level}
    {args : List (Expr Nat)} :
    headStep? pinLoopEnvT n Γ (.const 62 ls) args = none := rfl

/-- `whnfTy` returns `lift 0 1 X` unchanged at every fuel — the first
    `headStep?` probe already refuses. -/
theorem whnfTy_liftXT {n : Nat} {Γ : LCtx} (fuel : Nat) :
    (whnfTy pinLoopEnvT n Γ fuel (lift 0 1 loopXT)).1 = lift 0 1 loopXT := by
  cases fuel <;> rfl

/-- `lift 0 1 X` — `x`'s stored type read back in `[x : X]` — never
    exposes a Π, at every fuel. -/
theorem toPi_liftXT_none {n : Nat} {Γ : LCtx} (fuel : Nat) :
    toPi? pinLoopEnvT n fuel Γ (lift 0 1 loopXT) = none := by
  cases fuel <;> rfl

/-! ## (2) the refusal propagated — `checkWith` at `x x`, `ω`, `Ω` -/

/-- `x` under `[x : X]` infers its stored type back, lifted — the
    `checkWith` bvar arm, computed. -/
theorem checkWith_bvar0_liftXT {n : Nat} (fuel : Nat) (conv) {Γ : LCtx} :
    checkWith pinLoopEnvT n fuel conv (.assumption loopXT :: Γ) (.bvar 0)
      = some ⟨lift 0 1 loopXT, .bvar _ _ _ rfl⟩ := rfl

/-- the app arm dies at `toPi?` when the function's inferred type never
    exposes a Π — the generic propagation step. -/
theorem checkWith_app_none_of_toPi {E : ResolvedEnv} {n fuel : Nat}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {Γ : LCtx} {f a Tf Ta : Expr Nat} {df da} :
    checkWith E n fuel conv Γ f = some ⟨Tf, df⟩ →
    checkWith E n fuel conv Γ a = some ⟨Ta, da⟩ →
    toPi? E n fuel Γ Tf = none →
    checkWith E n fuel conv Γ (.app f a) = none := by
  intro hf ha hpi
  unfold checkWith
  simp only [hf, ha, hpi]

/-- a lam never checks when its body never checks. -/
theorem checkWith_lam_none_of_body {E : ResolvedEnv} {n fuel : Nat}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {Γ : LCtx} {A b : Expr Nat} :
    checkWith E n fuel conv (.assumption A :: Γ) b = none →
    checkWith E n fuel conv Γ (.lam A b) = none := by
  intro h
  unfold checkWith
  rw [h]
  cases checkWith E n fuel conv Γ A <;> rfl

/-- an app never checks when its function side never checks. -/
theorem checkWith_app_none_of_fun {E : ResolvedEnv} {n fuel : Nat}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {Γ : LCtx} {f a : Expr Nat} :
    checkWith E n fuel conv Γ f = none →
    checkWith E n fuel conv Γ (.app f a) = none := by
  intro h
  unfold checkWith
  rw [h]

/-- the ω body `x x` under `[x : X]` never checks: `x` infers `lift 0 1 X`,
    whose `toPi?` is `none` at every fuel — independently of `conv`. -/
theorem checkWith_omegaBody_none {n : Nat} (fuel : Nat) (conv) {Γ : LCtx} :
    checkWith pinLoopEnvT n fuel conv (.assumption loopXT :: Γ)
      (.app (.bvar 0) (.bvar 0)) = none :=
  checkWith_app_none_of_toPi rfl rfl (toPi_liftXT_none fuel)

/-- `ω = λx:X. x x` never checks: its body's check is `none`. -/
theorem checkWith_omegaLam_none {n : Nat} (fuel : Nat) (conv) {Γ : LCtx} :
    checkWith pinLoopEnvT n fuel conv Γ
      (.lam loopXT (.app (.bvar 0) (.bvar 0))) = none :=
  checkWith_lam_none_of_body (checkWith_omegaBody_none fuel conv)

/-- `Ω = ω ω` never checks: its function side's check is `none`. -/
theorem checkWith_omegaXT_none {n : Nat} (fuel : Nat) (conv) {Γ : LCtx} :
    checkWith pinLoopEnvT n fuel conv Γ omegaXT = none :=
  checkWith_app_none_of_fun (checkWith_omegaLam_none fuel conv)

/-! ## (3) certifier and machine non-acceptance -/

/-- `tyAtC` on `Ω : X` at `pinLoopEnvT` is `none` at EVERY fuel — the
    inference side already fails, so the asked-type conversion is never
    consulted. -/
theorem tyAtC_omegaXT_none {n : Nat} (fuel : Nat) :
    tyAtC pinLoopEnvT n fuel loopΓ omegaXT loopXT = none := by
  unfold tyAtC tyAtWith
  rw [checkWith_omegaXT_none]

/-- the machine-level refusal: at `pinLoopEnvT` on `checkT2 X Ω`, the
    typed machine's run NEVER accepts — suspended at fuel `0`, refused at
    `fuel + 1`, at every budget. Abel–Coquand at the typed machine. -/
theorem typedRun_check_omega_never {n : Nat} (s : TypedState)
    (hamb : s.ambient = ⟨pinLoopEnvT, n, loopΓ⟩)
    (htask : s.task = .checkT2 loopXT omegaXT) (f : Nat) :
    ∀ p : TypedAccepted s.ambient, typedRun f s ≠ .accepted p := by
  intro p hp
  obtain ⟨amb, task, budget⟩ := s
  obtain ⟨E', nu', Γ'⟩ := amb
  injection hamb with hE hu hctx
  subst E' nu' Γ' htask
  cases f with
  | zero => exact nomatch hp
  | succ k =>
      simp only [typedRun] at hp
      cases budget with
      | zero =>
          simp only [typedStep] at hp
          exact nomatch hp
      | succ b =>
          have hnone := tyAtC_omegaXT_none (n := n) (b + 1)
          simp only [typedStep] at hp
          rw [hnone] at hp
          exact nomatch hp

/-! ## (4) the restated row -/

/-- **RM-025, restated** (#6546, Annex-26.18 pattern): the conjunction a
    census anchors to — unrestricted per-profile completeness is false
    (a well-typed term the typed machine never accepts at any fuel); the
    positive part is the 26.18 cone package (the normalization content
    03 §15 deferred completeness to); and the unconditional soundness
    floor stands. -/
theorem RM025_restated :
    (∀ {n : Nat},
        Nonempty (HasTyT pinLoopEnvT n loopΓ omegaXT loopXT)
        ∧ ∀ (s : TypedState) (f : Nat),
            s.ambient = ⟨pinLoopEnvT, n, loopΓ⟩ →
            s.task = .checkT2 loopXT omegaXT →
            ∀ p : TypedAccepted s.ambient, typedRun f s ≠ .accepted p)
    ∧ (∀ {E : ResolvedEnvA} {n : Nat}, AnnEnvA E →
        PropStuckChainsA E (iotaIfaceA E) n →
        PiHeadStepTypedA E (iotaIfaceA E) n →
        HopFacesA E (iotaIfaceA E) n)
    ∧ (∀ (s : TypedState) (e A : Expr Nat)
        (_htask : s.task = .checkT2 A e)
        (_hacc : Σ' d, typedStep s = .accepted (.checked e A d)),
        Nonempty (HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A))
    ∧ (∀ (k : Nat) (s : TypedState) (e A : Expr Nat)
        (_htask : s.task = .checkT2 A e)
        (_hacc : Σ' d, typedRun (k + 1) s = .accepted (.checked e A d)),
        Nonempty (HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A)) :=
  ⟨fun {_n} => ⟨eraseEnv_pinLoopEnvA ▸ ⟨omegaT_pinLoop_typed⟩,
    fun s f hamb htask => typedRun_check_omega_never s hamb htask f⟩,
   fun C => hopFacesA_of_envWf C,
   fun _ _ _ ht hd => ⟨RM016T_check_sound _ _ _ ht hd⟩,
   fun _ _ _ _ ht hd => ⟨RM016T_run_check_sound _ _ _ _ ht hd⟩⟩

end Rcic

#print axioms Rcic.headStep_pinLoopRec_none
#print axioms Rcic.tyAtC_omegaXT_none
#print axioms Rcic.typedRun_check_omega_never
#print axioms Rcic.RM025_restated
