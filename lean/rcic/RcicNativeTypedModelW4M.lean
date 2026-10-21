import rcic.RcicNativeTypedModelCovNormEscape
import rcic.RcicNativeTypedModelCovRelEscape
import rcic.RcicNativeReadbackCK2Measurement
import rcic.RcicNativeReadbackCK2Index
import rcic.RcicNativeTypedModelKPositive
import rcic.RcicAbelCoquandPin

/-!
# WALL 4, model side (SWE-A) — `ApproxTKR`: the Eq-gap alias observed at its CK2 readback

`ApproxTK` observes the type-position redex `eqGapDirectAlias A B` only as `.bot`
(`approxTK_eqGapPrefix_bot`); the saturated `Eq.rec` (`eqGapRedex`) is gated by
`KIndexGuardAt`/`KCommonAt`, so `covNormAliasPi A B = .pi (alias) (.sort 0)` admits only
`.pi .bot f` observations (`covNormAliasPi_observation_shape`) and `ElTCovP` fails
(`not_elTCovP_covNormAliasPi`).

**The smallest change.**  `ApproxTKR` carries the same eleven constructors as `ApproxTK`
with `ApproxTKR` in the recursive positions, plus one additional clause:

    | ck2 (hred : RedR (WhStepCK2 E n) Γ e N) (hnorm : NormalR (WhStepCK2 E n) Γ N)
        (h : ApproxTKR E n Γ ρ N c) : ApproxTKR E n Γ ρ e c

Any term whose CK2 readback reaches a normal form is observed at that form.  The task's
stated instance — *a `recursorPropK` call that reads back to a normal form is observed
at that form* — is the specialization `e = recCall (.const w.recRef w.ls) w.preMajor x`,
recorded as `approxTKR_recursorPropK_read`.  The CK2 stepper reaches the normal form
*through* the saturated `Eq.rec` (`WhStepCK2.native`, which is gated by the same
`KIndexGuardAt`/`KCommonAt` certificates as `recursorPropK`), so the clause adds no
un-guarded recursor observation.

**Measured boundary (kernel terms below).**

* `approxTKR_eqGapDirectAlias_prop`: the alias is now observed at `.prop`, the code of
  its CK2 normal form `Sort 0` — the `.bot`-domain collapse is gone.
* `approxTKR_covNormAliasPi_piProp` / `covNormAliasPi_positiveApproxTKR`:
  `covNormAliasPi A B` admits the `.pi .prop [([.pi .bot []], .bot)]` observation, whose
  demanded domain row `.pi .bot []` is `CTyS`-legal at `.prop` (impredicative Π code).
  The demanded argument `covNormAliasIdentity` remains natively typed at the Pi
  (`covNormAliasIdentity_native`) — the positive result is stated with that demand.
* K-soundness controls: every old positive lifts verbatim (`approxTKR_of_approxTK`).
  The landed refutation `not_typedNativeKForwardTK_eqEnv` does **not** port: its
  counterexample term `etaIndexRedex` CK2-reads back to `Sort 0`
  (`native_controls_readback`), so `ApproxTKR etaIndexRedex .prop` is derivable
  (`approxTKR_etaIndexRedex_prop`) and the bot-lemma it depended on is refuted
  (`not_approxTKR_etaIndexRedex_allBot`).  The variant repairs the forward port at
  exactly that kernel-checked instance: this is the measured boundary.
* Abel–Coquand guard: `AbelCoquand.delta` is still never observed at the
  Prop-collapsed code `.prop` (`not_approxTKR_abelCoquandDelta_prop`) — `ck2` cannot
  force a normal-form observation: `δ` is itself CK2-normal, so uniqueness of normal
  forms collapses every `ck2` premise to `N = δ`.

Axioms: `{propext, Quot.sound}` only.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelW4MAudit

open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit
open Rcic.Declarative.NativeValleys.TypedModelKFailureAudit
open Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit
open Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit
open Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit
open Rcic.Declarative.NativeValleys.TypedModelCovNormEscapeAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit
open Rcic.Declarative.AbelCoquand

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- The wall-4 model variant: `ApproxTK`'s eleven constructors plus `ck2`, the
readback observation.  Every `ApproxTK` derivation lifts verbatim
(`approxTKR_of_approxTK`); the new clause is the only way to observe a term at the
compact of its CK2 normal form rather than at its own syntax. -/
inductive ApproxTKR (E : ResolvedEnv) (n : Nat) : LCtx → EnvT → Expr Nat → CptT → Prop
  | bot (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) : ApproxTKR E n Γ ρ e .bot
  | free {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
      (hfree : KFreeT E e) (h : ApproxT E ρ e c) : ApproxTKR E n Γ ρ e c
  | pi {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} {a : CptT}
      {f : List (List CptT × CptT)}
      (hA : ApproxTKR E n Γ ρ A a)
      (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hb : ∀ s ∈ f, ApproxTKR E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTKR E n Γ ρ (.pi A B) (.pi a f)
  | lam {Γ : LCtx} {ρ : EnvT} {A b : Expr Nat} {a : CptT}
      {g : List (List CptT × CptT)}
      (hA : ApproxTKR E n Γ ρ A a)
      (ht : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hne : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTKR E n (.assumption A :: Γ)
        (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTKR E n Γ ρ (.lam A b) (.lam g)
  | app {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat}
      {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTKR E n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTKR E n Γ ρ a u) :
      ApproxTKR E n Γ ρ (.app f a) s.2
  | appSpine {Γ : LCtx} {ρ : EnvT} {f a : Expr Nat} {r : Nat}
      {args : List CptT} {u : CptT}
      (hf : ApproxTKR E n Γ ρ f (.spine r args))
      (ha : ApproxTKR E n Γ ρ a u) :
      ApproxTKR E n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | delta {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember}
      {b : Expr Nat} {c : CptT} (hd : DeltaConst E r m b)
      (h : ApproxTKR E n [] EnvT.bot (instantiateLevels ls b) c) :
      ApproxTKR E n Γ ρ (.const r ls) c
  | letE {Γ : LCtx} {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTKR E n Γ ρ (.app (.lam A b) v) c) :
      ApproxTKR E n Γ ρ (.letE A v b) c
  | lit {Γ : LCtx} {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTKR E n Γ ρ (natExpand t) c) :
      ApproxTKR E n Γ ρ (.lit t) c
  | iota {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitnessS E)
      (hsource : ApproxT E ρ (iotaLhsOfS w) c)
      (hrhs : ApproxTKR E n Γ ρ (iotaRhsOfS w) c) :
      ApproxTKR E n Γ ρ (iotaLhsOfS w) c
  | recursorPropK {Γ : LCtx} {ρ : EnvT} {c : CptT} (w : IotaWitness E) (x : Expr Nat)
      (hcanon : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexGuardAt E n Γ w) (hcommon : KCommonAt E n Γ w x)
      (hsource : ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c)
      (hrhs : ApproxTKR E n Γ ρ (iotaRhsOf w) c) :
      ApproxTKR E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c
  | ck2 {Γ : LCtx} {ρ : EnvT} {e N : Expr Nat} {c : CptT}
      (hred : RedR (WhStepCK2 E n) Γ e N)
      (hnorm : NormalR (WhStepCK2 E n) Γ N)
      (h : ApproxTKR E n Γ ρ N c) : ApproxTKR E n Γ ρ e c

/-- The model packaged as a `CtxModelT`, for relation-side consumers. -/
def ctxModelT_approxTKR (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CtxModelT E :=
  ⟨ApproxTKR E n Γ⟩

/-- Every `ApproxTK` derivation is an `ApproxTKR` derivation: the variant only adds
observations, so all landed positive controls lift. -/
theorem approxTKR_of_approxTK {e : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ e c) : ApproxTKR E n Γ ρ e c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hfree h => exact .free hfree h
  | pi _ ht _ ihA ihb => exact .pi ihA ht ihb
  | lam _ ht hne _ ihA ihb => exact .lam ihA ht hne ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | delta _ _ ih => exact .delta ‹_› ih
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih
  | iota w hsource _ ihrhs => exact .iota w hsource ihrhs
  | recursorPropK w x hcanon hnc hindex hcommon hsource _ ihrhs =>
      exact .recursorPropK w x hcanon hnc hindex hcommon hsource ihrhs

/-- Sorts keep their code compact. -/
theorem approxTKR_sort_code (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (l : Level) : ApproxTKR E n Γ ρ (.sort l) (sortCode l) :=
  .free (kFreeT_sort E l) (approxT_sort_code E ρ l)

/-- The task's stated instance: a `recursorPropK` call that CK2-reads back to a normal
form is observed at that form.  This is the `ck2` clause specialized to the
`recCall` shape. -/
theorem approxTKR_recursorPropK_read (w : IotaWitness E) (x N : Expr Nat) {c : CptT}
    (hred : RedR (WhStepCK2 E n) Γ (recCall (.const w.recRef w.ls) w.preMajor x) N)
    (hnorm : NormalR (WhStepCK2 E n) Γ N) (h : ApproxTKR E n Γ ρ N c) :
    ApproxTKR E n Γ ρ (recCall (.const w.recRef w.ls) w.preMajor x) c :=
  .ck2 hred hnorm h

/-- **The change matters:** the Eq-gap alias — `.bot`-only under `ApproxTK` — is
observed at `.prop`, the code of its CK2 normal form `Sort 0`
(`eqGapAlias_type_read`: alias ⟶β `eqGapRedex` ⟶native `Sort 0`). -/
theorem approxTKR_eqGapDirectAlias_prop (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    ApproxTKR eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop := by
  simpa only [sortCode_zero] using
    ApproxTKR.ck2 (eqGapAlias_type_read n A B) (normalR_sortCK2 eqGapCtx .zero)
      (approxTKR_sort_code eqEnvT n eqGapCtx ρ .zero)

/-- The demanded domain compact is `CTyS`-legal at `.prop`: `.pi .bot []` is an
impredicative proposition code (`IsPropCT` via `TyCodeCT.bot`).  Under `ApproxTK`
the observed domain was `.bot`, forcing `CTyS _ (.pi .bot []) .bot`, i.e.
`.pi .bot [] = .bot` — impossible. -/
theorem ctyS_piBotNil_prop : CTyS E (.pi .bot []) .prop := by
  rw [CTyS]
  exact Or.inr (.pi .bot (fun t ht => (List.not_mem_nil _ ht).elim))

/-- **`covNormAliasPi` is positive under `ApproxTKR`:** the normal Pi is observed at
`.pi .prop [([.pi .bot []], .bot)]` — non-bottom domain, and the demanded input row
`.pi .bot []` is `CTyS`-legal at `.prop`. -/
theorem approxTKR_covNormAliasPi_piProp (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    ApproxTKR eqEnvT n eqGapCtx ρ (covNormAliasPi A B)
      (.pi .prop [([.pi .bot []], .bot)]) := by
  refine .pi (approxTKR_eqGapDirectAlias_prop n ρ A B) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_piBotNil_prop
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .bot _ _ _

/-- The positive statement packaged with the demanded argument's native typing:
`covNormAliasIdentity` (the relation's `x`) is typed at `covNormAliasPi A B`
(`covNormAliasIdentity_native`), and its demanded row compact is `CTyS`-legal at the
new `.prop` domain. -/
theorem covNormAliasPi_positiveApproxTKR (n : Nat) (ρ : EnvT) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B)
        (.sort (.succ .zero))) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity
        (covNormAliasPi A B)) ∧
      ApproxTKR eqEnvT n eqGapCtx ρ (covNormAliasPi A B)
        (.pi .prop [([.pi .bot []], .bot)]) ∧
      CTyS eqEnvT (.pi .bot []) .prop := by
  obtain ⟨A, B, hA, hI⟩ := covNormAliasIdentity_native n
  exact ⟨A, B, hA, hI, approxTKR_covNormAliasPi_piProp n ρ A B, ctyS_piBotNil_prop⟩

/-- The forward-port Prop, restated for `ApproxTKR`: a native K head step transports
the target's observations back to the source. -/
def TypedNativeKForwardTKR (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {src dst A : Expr Nat}, EnvWfT E → CtxWfT E n Γ →
    HasTyT E n Γ src A → HasTyT E n Γ dst A → KNativeHead E n Γ src dst →
      ∀ {ρ : EnvT} {c : CptT}, ApproxTKR E n Γ ρ dst c → ApproxTKR E n Γ ρ src c

/-- The eta instance of `TypedNativeKForwardTK` — the landed counterexample to the
port under `ApproxTK` (`not_typedNativeKForwardTK_eqEnv`) — is **derivable** under
`ApproxTKR`: `etaIndexRedex` CK2-steps natively to `Sort 0`. -/
theorem typedNativeKForwardTKR_eta (n : Nat) (ρ : EnvT) {c : CptT}
    (h : ApproxTKR eqEnvT n etaEqCtx ρ (.sort .zero) c) :
    ApproxTKR eqEnvT n etaEqCtx ρ etaIndexRedex c :=
  .ck2 (native_controls_readback n).2.1 (normalR_sortCK2 _ _) h

/-- The exact term of the landed refutation now admits a non-bottom observation. -/
theorem approxTKR_etaIndexRedex_prop (n : Nat) (ρ : EnvT) :
    ApproxTKR eqEnvT n etaEqCtx ρ etaIndexRedex .prop := by
  simpa only [sortCode_zero] using
    typedNativeKForwardTKR_eta n ρ (approxTKR_sort_code eqEnvT n etaEqCtx ρ .zero)

/-- The old refutation's last step is false under `ApproxTKR`: `etaIndexRedex` does
not have only the bottom observation.  This is the measured model-side boundary of
the `ck2` clause. -/
theorem not_approxTKR_etaIndexRedex_allBot (n : Nat) :
    ¬ (∀ (ρ : EnvT) {c : CptT}, ApproxTKR eqEnvT n etaEqCtx ρ etaIndexRedex c →
        c = .bot) :=
  fun h => CptT.noConfusion (h EnvT.bot (approxTKR_etaIndexRedex_prop n EnvT.bot))

/-- **Abel–Coquand guard.**  The pinned self-application term `δ : ⊤` is a λ, hence
CK2-normal; uniqueness of CK2 normal forms collapses every `ck2` premise on `δ` to
`N = δ`, so `.prop` — the Prop-collapsed code — is still not an observation of `δ`.
The variant does not force a normal-form observation on the Abel–Coquand term. -/
private theorem abelCoquand_delta_unfold :
    AbelCoquand.delta =
      .lam AbelCoquand.bot (.app (.app (.bvar 0) AbelCoquand.top) (.bvar 0)) := rfl

theorem not_approxTKR_abelCoquandDelta_prop {n : Nat} {Γ : LCtx} {ρ : EnvT} :
    ¬ ApproxTKR emptyEnv n Γ ρ AbelCoquand.delta .prop := by
  intro h
  generalize he : AbelCoquand.delta = e at h
  generalize hc : (.prop : CptT) = c at h
  induction h with
  | bot => exact CptT.noConfusion hc
  | free _ hT =>
      subst he
      subst hc
      rw [abelCoquand_delta_unfold] at hT
      rcases approxT_lam_inv hT with hbot | ⟨_, _, hlam, _, _⟩
      · exact CptT.noConfusion hbot
      · exact CptT.noConfusion hlam
  | pi _ _ _ _ _ => exact CptT.noConfusion hc
  | lam _ _ _ _ _ => exact CptT.noConfusion hc
  | app _ _ _ _ _ =>
      rw [abelCoquand_delta_unfold] at he
      exact Expr.noConfusion he
  | appSpine _ _ _ _ => exact CptT.noConfusion hc
  | delta _ _ _ =>
      rw [abelCoquand_delta_unfold] at he
      exact Expr.noConfusion he
  | letE _ _ =>
      rw [abelCoquand_delta_unfold] at he
      exact Expr.noConfusion he
  | lit _ _ =>
      rw [abelCoquand_delta_unfold] at he
      exact Expr.noConfusion he
  | iota _ _ _ _ =>
      rw [abelCoquand_delta_unfold] at he
      unfold iotaLhsOfS at he
      rw [recCall_eq_app] at he
      exact Expr.noConfusion he
  | recursorPropK _ _ _ _ _ _ _ _ _ =>
      rw [abelCoquand_delta_unfold] at he
      rw [recCall_eq_app] at he
      exact Expr.noConfusion he
  | ck2 hred hnorm _ ih =>
      subst he
      subst hc
      exact ih ((normalUniqueR_whStepCK2 EnvWfT.empty _ hred hnorm
        (RedR.refl AbelCoquand.delta) (normalR_lamCK2 _ _ _)).symm) rfl

/-! ### §4 — No-read-to-sort at guard-blocked K redexes (narrowed SWE-A, cc 12:10Z)

ChatGPT's #7774 (`RcicNativeTypedModelCovXTypePosition`,
`TypeReadbackObservationTK`) already shows the auxiliary type-position
observation is `.prop` iff CK2 reads the term back to `Sort 0` — an iff with
neither side supplied — and that reflection into raw `ApproxTK` is refuted at
the Eq-gap alias.  The open side of that iff is whether the premise is ever
inhabited at a *guard-blocked* `recursorPropK` position.  This section decides
the native no-read-to-sort premise in general (over any admitted `E`, hence
`eqEnvT` in particular):

**proved side.**  "Guard-blocked" is read as the *native* gate —
`KCanonW ∧ ¬ IsCtorSpine ∧ KIndexConvAt ∧ KCommonAt`, the exact premise
package of `KNativeHead.intro` — failing at every `IotaWitness` whose ι-lhs is
the call.  Then `normalR_kRec_of_no_native` (landed) makes the call
CK2-normal and `normalUniqueR_whStepCK2` pins its only normal reduct to the
call itself, which is an application, never `.sort u`.  So the auxiliary
observation adds no `.prop` at natively guard-blocked positions — it is
K-safe in exactly this sense.

**named residual.**  The model-side guard `KIndexGuardAt` is strictly stronger
than the native gate: it adds `IndexAgreementDI` on top of `KIndexConvAt`.  A
call blocked only through `IndexAgreementDI` (with `KIndexConvAt` still
holding) is model-guard-blocked but *not* natively blocked — `WhStepCK2.native`
still fires there.  `GuardBlockedModelOnly` names exactly those positions; it
is stated as a boundary, not discharged. -/

/-- `e` is natively guard-blocked: every ι-witness whose lhs is `e` fails the
    native K gate (the premise package of `KNativeHead.intro`). -/
def NativeGateBlockedAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∀ (w : IotaWitness E) (x : Expr Nat),
    recCall (.const w.recRef w.ls) w.preMajor x = e →
    ¬ (KCanonW w x ∧ ¬ IsCtorSpine E x ∧ KIndexConvAt E n Γ w ∧ KCommonAt E n Γ w x)

/-- Inversion of `KNativeHead` through a `recCall` equality: some realising
    witness carries the whole gate, and the target is its ι-rhs. -/
theorem kNativeHead_gate {w : IotaWitness E} {x b : Expr Nat}
    (h : KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) b) :
    ∃ w' x', w'.recRef = w.recRef ∧ w'.ls = w.ls ∧ w'.preMajor = w.preMajor ∧
      x' = x ∧ KCanonW w' x' ∧ ¬ IsCtorSpine E x' ∧ KIndexConvAt E n Γ w' ∧
      KCommonAt E n Γ w' x' ∧ b = iotaRhsOf w' := by
  generalize he : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at h
  cases h with
  | intro hK hnc hi hc =>
      rename_i w' x'
      obtain ⟨hr, hls, hpre, hx⟩ := recCall_const_inj he
      exact ⟨w', x', hr.symm, hls.symm, hpre.symm, hx.symm, hK, hnc, hi, hc, rfl⟩

/-- A natively guard-blocked, K-eligible recursor call at a non-constructor
    major is CK2-normal. -/
theorem normalR_of_nativeGateBlocked {w : IotaWitness E} {x : Expr Nat}
    (hW : EnvWfT E) (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
    (hb : NativeGateBlockedAt E n Γ (recCall (.const w.recRef w.ls) w.preMajor x)) :
    NormalR (WhStepCK2 E n) Γ (recCall (.const w.recRef w.ls) w.preMajor x) :=
  normalR_kRec_of_no_native hW hK hnc (fun _ h => by
    obtain ⟨w', x', hr, hls, hpre, hx, hKc, hnc', hi', hc', _⟩ := kNativeHead_gate h
    have hmatch : recCall (.const w'.recRef w'.ls) w'.preMajor x' =
        recCall (.const w.recRef w.ls) w.preMajor x := by
      rw [← hr, ← hls, ← hpre, ← hx]
    exact hb w' x' hmatch ⟨hKc, hnc', hi', hc'⟩)

/-- **The general no-read-to-sort theorem.**  A K-eligible `recursorPropK`-shaped
    call whose native gate is blocked at every realising witness has no CK2
    readback to a sort: the call is already normal, and normal forms are unique. -/
theorem guardBlocked_recCall_no_sort_readback {w : IotaWitness E} {x N : Expr Nat}
    (hW : EnvWfT E) (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
    (hb : NativeGateBlockedAt E n Γ (recCall (.const w.recRef w.ls) w.preMajor x))
    (hred : RedR (WhStepCK2 E n) Γ (recCall (.const w.recRef w.ls) w.preMajor x) N)
    (hnorm : NormalR (WhStepCK2 E n) Γ N) :
    ∀ u : Level, N ≠ .sort u := by
  intro u hN
  have hEq : N = recCall (.const w.recRef w.ls) w.preMajor x :=
    normalUniqueR_whStepCK2 hW _ hred hnorm (.refl _)
      (normalR_of_nativeGateBlocked hW hK hnc hb)
  have happ : (.sort u : Expr Nat) =
      .app (foldApps (.const w.recRef w.ls) w.preMajor) x := by
    rw [recCall_eq_app] at hEq
    exact hN ▸ hEq
  exact Expr.noConfusion happ

/-- The index-conversion check is the strongest sufficient blocker: the native
    step needs `KIndexConvAt`, so if every realising witness fails it, the call
    is natively guard-blocked. -/
theorem nativeGateBlocked_of_all_kIndexConvAt_false {e : Expr Nat}
    (h : ∀ (w : IotaWitness E) (x : Expr Nat),
      recCall (.const w.recRef w.ls) w.preMajor x = e → ¬ KIndexConvAt E n Γ w) :
    NativeGateBlockedAt E n Γ e :=
  fun w x he ⟨_, _, hi, _⟩ => h w x he hi

/-- The residual boundary, named as a Prop (not supplied): a realising witness
    can in principle fail the model-side `KIndexGuardAt` solely through
    `IndexAgreementDI` while `KIndexConvAt` still holds; there the native step
    fires anyway, so model-guard-blocking alone does not imply "no sort
    readback".  This is the precise sense in which the auxiliary observation is
    not automatically K-safe at DI-only-blocked positions. -/
def GuardBlockedModelOnly (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∃ (w : IotaWitness E) (x : Expr Nat),
    recCall (.const w.recRef w.ls) w.preMajor x = e ∧
    ¬ KIndexGuardAt E n Γ w ∧
    (KCanonW w x ∧ ¬ IsCtorSpine E x ∧ KIndexConvAt E n Γ w ∧ KCommonAt E n Γ w x)

/-- K-safety corollary for the auxiliary type-position observation (#7774
    `TypeReadbackObservationTK`, cited by name): at a natively guard-blocked
    `recursorPropK` call, `ApproxTKR.ck2`'s premises `(hred, hnorm)` cannot be
    jointly inhabited with `N = .sort u` — so the clause adds no `.prop`
    observation there. -/
theorem ck2_adds_no_prop_at_blocked {w : IotaWitness E} {x N : Expr Nat}
    (hW : EnvWfT E) (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
    (hb : NativeGateBlockedAt E n Γ (recCall (.const w.recRef w.ls) w.preMajor x))
    (hred : RedR (WhStepCK2 E n) Γ (recCall (.const w.recRef w.ls) w.preMajor x) N)
    (hnorm : NormalR (WhStepCK2 E n) Γ N) :
    ∀ u : Level, N ≠ .sort u :=
  guardBlocked_recCall_no_sort_readback hW hK hnc hb hred hnorm

end Rcic.Declarative.NativeValleys.TypedModelW4MAudit
