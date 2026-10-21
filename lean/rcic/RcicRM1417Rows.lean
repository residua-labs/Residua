import rcic.RcicTypedMachineAccept
import rcic.RcicDT0709EnvWf

/-!
# RM-014/RM-017 at the native π row — `InScope`-free adapters

The sealed halves (`RcicMachineSoundTyped:machineRedSRT`,
`RM014T_whnf_typed`; `RcicTypedConvTerm:machineRed_toConvT`,
`convCert_convT`; `RcicTypedMachineAccept:RM017T_conversion_confirmed`)
all ask `hP : hW.InScope` because β needs the typed Π row and ζ needed
the conditional endpoint theorem, both supplied through the scope
bridge (`typedRowsWf_of_envWfT_semPrefix`, `DT009T_endpoints_inScope`).
`DT009T_endpoints_envWfT` (#6425, RcicDT0709EnvWf) discharges the
endpoints unconditionally at `EnvWfT`, so the ONLY remaining consumer
of the bridge inside these rows is `TypedRowsWf.piRow`. This module
restates the chain with that one row taken as an explicit hypothesis —
named exactly as `TypedRowsWf.piRow`'s statement

```lean
∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
  TyConvT E n Γ (.pi A B) (.pi A' B') →
  Nonempty (TyConvT E n Γ A A') ∧
    Nonempty (TyConvT E n (.assumption A :: Γ) B B')
```

— and nothing else (no `InScope`, no `ScopeCheck`, no `AnnEnvA`/
`EnvSemA`/`IotaSRA`, no `TypedRowsWf` packaging). Per the recovery spec
(`research/rcic/sortrow/CENSUS_WALLS_MAINLINE_AUTHORITY_RECOVERY.md`
§I.7–8):

* `machineBetaStepT_rows` — the β head step at a FIXED type `S`: app/λ
  inversion, `piRow` on the λ's type chain for the domain conversion
  `hBdom` and the codomain chain `hBcod` under the left domain, the
  argument retyped by `hBdom.symmT`, the body by `hBcod`, typed
  substitution, and the inversion's own chain landing `S`.
* `machineZetaStepT_rows` — ζ through `ConvT.zeta` with
  `DT009T_endpoints_envWfT` (the native endpoint theorem; `EnvWfT`
  only, no `piRow`).
* δ is `EnvWfT`-only and is reused as-is (`machineDeltaStepT`).
* `machineRedSRT_rows` — `HasTyT` preserved along `MachineRed`, the
  three-case head induction under `hasTyTFoldAppsHeadT`.
* `RM014T_whnf_typed_rows` — the whnf acceptance's reduct is typed,
  the same `kernelStepRaw` arm unfolding riding `machineRedSRT_rows`.
* `machineBetaConvT_rows` — the β head CONVERSION at `S`: the same
  retyping (`ha'` by `hBdom.symmT`), `ConvT.beta` at the λ's own
  codomain, the codomain chain lifted through the argument's
  substitution (`tyConvT_subst0_of_envWfT`), `convT_of_tyConv` landing
  `S`. ζ/δ conversions are reused (`machineZetaConvT` takes no premise;
  `machineDeltaConvT` is `EnvWfT`-only).
* `machineRed_toConvT_rows` — `MachineRed` carries a `ConvT` chain at
  the source's type, arm by arm.
* `CertTrace` — the certifier's trace grammar extracted from the
  success equation (replaces `convCert_convT`'s arbitrary-`ParRedStar`
  transport): `refl` / an original `MachineRed` chain / `trans` /
  application congruence. `convCert_trace` replays `convCert`'s own
  case structure — syntactic equality, two whnf chains meeting at one
  whnf, sort/constant head equality, `.app`/`.app` congruence — and
  returns BOTH sides' traces to one common endpoint.
* `certTrace_convT_rows` — the trace induction to `ConvT` at the
  source's type: `refl` by `ConvT.refl`; `red` by
  `machineRed_toConvT_rows`; `trans` by endpoint typing
  (`DT009T_endpoints_envWfT`) and `ConvT.trans`; `app` by
  app-inversion, the function's trace at its Π type, the argument's at
  its domain, `ConvT.app`, and `convT_of_tyConv` through the
  inversion's chain — no type-uniqueness assumption.
* `convCert_convT_rows` — both traces end at the same `d`; `l`'s chain
  at `T` trans'd with the symm of `r`'s gives `ConvT l r T`.
* `RM017T_conversion_confirmed_rows` — the `convAt` arm's acceptance
  equation unfolded as in `RM017T_conversion_confirmed`, riding
  `convCert_convT_rows`.

Premise disclosure: every `_rows` statement takes ONLY `EnvWfT`,
`CtxWfT`, the `piRow` hypothesis (verbatim `TypedRowsWf.piRow`'s type),
and the row's own subject matter. `CertTrace`/`convCert_trace` are
data/extraction and take no premises; `Conv` appears only as
`convCert`'s own return type (the acceptance's payload), matching
`convCert_chains`. Consumption pins run the real fixtures through the
LANDED supplier `typedRowsWf_of_envWfT_semPrefix` — the hypothesis is
inhabited at `natEnvU`, not vacuous.

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## the certifier's trace grammar -/

/-- The certifier's conversion trace: `refl`, an original `MachineRed`
    chain, transitivity, or application congruence — the language a
    `convCert` acceptance actually speaks (extracted from the success
    equation by `convCert_trace`). -/
inductive CertTrace (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (e : Expr Nat) : CertTrace E n Γ e e
  | red (Γ : LCtx) {a b : Expr Nat} (k : MachineRed E n Γ a b) :
      CertTrace E n Γ a b
  | trans (Γ : LCtx) {a b c : Expr Nat}
      (t₁ : CertTrace E n Γ a b) (t₂ : CertTrace E n Γ b c) :
      CertTrace E n Γ a c
  | app (Γ : LCtx) {f₁ f₂ a₁ a₂ : Expr Nat}
      (tf : CertTrace E n Γ f₁ f₂) (ta : CertTrace E n Γ a₁ a₂) :
      CertTrace E n Γ (.app f₁ a₁) (.app f₂ a₂)

/-! ## the three typed head steps — β at `piRow`, ζ at the native
    endpoint theorem, δ unchanged -/

/-- one typed beta head step at the FIXED type `S`, the native-`piRow`
    form: app/λ inversion, `piRow` on the λ's type chain for `hBdom`
    and `hBcod`, the argument retyped by `hBdom.symmT`, the body by
    `hBcod`, `hasTyT_subst0_of_envWfT` through the binder, and the
    inversion's chain landing `S`. No scope premise. -/
theorem machineBetaStepT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B'))
    (A body arg : Expr Nat) :
    (S : Expr Nat) → HasTyT E n Γ (.app (.lam A body) arg) S →
    Nonempty (HasTyT E n Γ (instantiate0 arg body) S) := by
  intro S h
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := piRow hΓ hcv_lam
  have ha' := hasTyT_of_tyConv ha hBdom.symmT
  have hbody' := hasTyT_of_tyConv hbody hBcod
  exact ⟨hasTyT_of_tyConv (hasTyT_subst0_of_envWfT hW hbody' ha') hcv⟩

/-- one typed zeta head step at the FIXED type `S` — letE inversion,
    `ConvT.zeta`, the NATIVE endpoint theorem
    (`DT009T_endpoints_envWfT`, `EnvWfT` only), the chain landing `S`.
    No `piRow`, no scope premise. -/
theorem machineZetaStepT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A value body : Expr Nat) :
    (S : Expr Nat) → HasTyT E n Γ (.letE A value body) S →
    Nonempty (HasTyT E n Γ (instantiate0 value body) S) := by
  intro S h
  obtain ⟨u, B_let, hAty, hv, hb, hcv⟩ := hasTyTInv_letE h rfl
  have hz := ConvT.zeta _ A value body B_let u hAty hv hb
  obtain ⟨_, ⟨hr⟩⟩ := DT009T_endpoints_envWfT hW hΓ hz
  exact ⟨hasTyT_of_tyConv hr hcv⟩

/-! ## the typed slice subject reduction at `piRow` -/

/-- `HasTyT` is preserved along `MachineRed` at the native `piRow` —
    `machineRedSRT` with the Π row hypothesis instead of the scope
    bridge. -/
theorem machineRedSRT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B')) :
    {e A e' : Expr Nat} → HasTyT E n Γ e A → MachineRed E n Γ e e' →
    Nonempty (HasTyT E n Γ e' A) := by
  intro e A e' h k
  induction k with
  | refl e₀ => exact ⟨h⟩
  | headBeta A body arg rest k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineBetaStepT_rows hW hΓ piRow A body arg)
          rest h
      exact ih h'
  | headZeta A value body rest k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineZetaStepT_rows hW hΓ A value body)
          rest h
      exact ih h'
  | headDelta r ls m b rest hres hbody htr k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineDeltaStepT hW r ls m b hres hbody)
          rest h
      exact ih h'

/-! ## RM014T — the whnf acceptance's reduct is typed, at `piRow` -/

/-- `RM014T_whnf_typed` at the native `piRow`: the same
    `kernelStepRaw` whnfAt-arm unfolding, the extracted `MachineRed`
    chain riding `machineRedSRT_rows`. -/
theorem RM014T_whnf_typed_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B'))
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A e w : Expr Nat) (htask : s.task = .whnfAt A e)
    (hty : HasTyT E n Γ e A)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    Nonempty (HasTyT E n Γ w A) := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next w' kred _heq =>
          have hw : w' = w := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredWhnf.injEq] at hacc
            exact hacc.2
          subst hw
          rw [hamb] at kred
          exact machineRedSRT_rows hW hΓ piRow hty kred
      · nomatch hacc

/-! ## the typed head conversions — β at `piRow`, ζ/δ reused -/

/-- one typed beta head conversion at the FIXED type `S`, the
    native-`piRow` form: the same retyping as `machineBetaStepT_rows`
    (`ha'` by `hBdom.symmT`), `ConvT.beta` at the λ's own codomain, the
    codomain chain lifted through the argument's substitution
    (`tyConvT_subst0_of_envWfT`), `convT_of_tyConv` landing `S`. -/
theorem machineBetaConvT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B'))
    (A body arg : Expr Nat) :
    (S : Expr Nat) → HasTyT E n Γ (.app (.lam A body) arg) S →
    Nonempty (ConvT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) S) := by
  intro S h
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := piRow hΓ hcv_lam
  have ha' := hasTyT_of_tyConv ha hBdom.symmT
  exact ⟨convT_of_tyConv
    (ConvT.beta Γ A body arg B_lam u hA0ty hbody ha')
    (TyConvT.trans Γ _ _ _
      (tyConvT_subst0_of_envWfT hW ha' hBcod) hcv)⟩

/-! ## the typed `MachineRed → ConvT` map at `piRow` -/

/-- `machineRed_toConvT` at the native `piRow`: each head step's
    conversion closes over the spine by `convTFoldAppsHeadT`, the
    middle is typed by the spine transport over the `_rows` step
    lemmas, the tail rides the induction. -/
theorem machineRed_toConvT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B')) :
    {a b T : Expr Nat} → MachineRed E n Γ a b → HasTyT E n Γ a T →
    Nonempty (ConvT E n Γ a b T) := by
  intro a b T k h
  induction k with
  | refl e => exact ⟨.refl Γ e T h⟩
  | headBeta A body arg rest k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineBetaStepT_rows hW hΓ piRow A body arg)
          rest h
      obtain ⟨c₁⟩ :=
        convTFoldAppsHeadT (machineBetaConvT_rows hW hΓ piRow A body arg)
          rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩
  | headZeta A value body rest k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineZetaStepT_rows hW hΓ A value body)
          rest h
      obtain ⟨c₁⟩ := convTFoldAppsHeadT (machineZetaConvT A value body)
        rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩
  | headDelta r ls m b rest hres hbody htr k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineDeltaStepT hW r ls m b hres hbody)
          rest h
      obtain ⟨c₁⟩ :=
        convTFoldAppsHeadT (machineDeltaConvT hW r ls m b hres hbody htr)
          rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩

/-! ## the certifier's trace extraction -/

/-- Every `convCert` acceptance carries `CertTrace`s of BOTH sides to
    one common endpoint — `convCert_chains`'s replay of the
    certifier's own case structure, emitting the trace grammar instead
    of arbitrary `ParRedStar`s: syntactic equality (`refl`), two whnf
    chains at one whnf (`.red`), sort/constant head equality (`.red`),
    `.app`/`.app` congruence (`.trans` of the head `.red` and the
    subtraces' `.app`). -/
def convCert_trace {E : ResolvedEnv} {n : Nat} :
    (fuel : Nat) → (Γ : LCtx) → (A l r : Expr Nat) → (c : Conv E n Γ l r) →
    convCert E n fuel Γ A l r = .ok c →
    Σ' (d : Expr Nat), CertTrace E n Γ l d ×' CertTrace E n Γ r d := by
  intro fuel Γ A l r c h
  induction fuel generalizing Γ A l r c with
  | zero =>
      rw [convCert] at h
      nomatch h
  | succ f ih =>
      simp only [convCert] at h
      split at h
      · rename_i hlr
        subst hlr
        exact ⟨l, .refl Γ l, .refl Γ l⟩
      · split at h
        · nomatch h
        · split at h
          · nomatch h
          · next wl kl heql wr kr heqr =>
              split at h
              · rename_i hwleq
                subst hwleq
                exact ⟨wl, .red Γ kl, .red Γ kr⟩
              · split at h
                · next _ _ u v kleft kright _ =>
                    split at h
                    · rename_i huv
                      subst huv
                      exact ⟨_, .red Γ kleft, .red Γ kright⟩
                    · nomatch h
                · next _ _ r₁ ls₁ r₂ ls₂ kleft kright _ =>
                    split at h
                    · rename_i hconj
                      obtain ⟨h1, h2⟩ := hconj
                      subst h1
                      subst h2
                      exact ⟨_, .red Γ kleft, .red Γ kright⟩
                    · nomatch h
                · next _ _ f₁ a₁ f₂ a₂ kleft kright _ =>
                    split at h
                    · nomatch h
                    · next hf =>
                        split at h
                        · nomatch h
                        · next ha =>
                            have ⟨df, tf₁, tf₂⟩ := ih Γ A f₁ f₂ _ hf
                            have ⟨da, ta₁, ta₂⟩ := ih Γ A a₁ a₂ _ ha
                            exact ⟨.app df da,
                              .trans Γ (.red Γ kleft) (.app Γ tf₁ ta₁),
                              .trans Γ (.red Γ kright) (.app Γ tf₂ ta₂)⟩
                · nomatch h

/-! ## the trace induction to `ConvT` -/

/-- A `CertTrace` carries a `ConvT` chain at the source's type — under
    `EnvWfT`, `CtxWfT` and the native `piRow`: `refl` by `ConvT.refl`;
    `red` by `machineRed_toConvT_rows`; `trans` by the native endpoint
    theorem for the middle typing and `ConvT.trans`; `app` by
    app-inversion, the function's trace at its Π type, the argument's
    at its domain, `ConvT.app`, transport through the inversion's
    chain. No type-uniqueness assumption. -/
theorem certTrace_convT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B')) :
    {a b T : Expr Nat} → CertTrace E n Γ a b → HasTyT E n Γ a T →
    Nonempty (ConvT E n Γ a b T) := by
  intro a b T t h
  induction t generalizing T with
  | refl e => exact ⟨.refl _ _ _ h⟩
  | red k => exact machineRed_toConvT_rows hW hΓ piRow k h
  | trans t₁ t₂ ih₁ ih₂ =>
      obtain ⟨c₁⟩ := ih₁ h
      obtain ⟨_, ⟨hmid⟩⟩ := DT009T_endpoints_envWfT hW hΓ c₁
      obtain ⟨c₂⟩ := ih₂ hmid
      exact ⟨.trans _ _ _ _ _ c₁ c₂⟩
  | app tf ta ihf iha =>
      obtain ⟨A0, B0, hf, ha, hcv⟩ := hasTyTInv_app h rfl
      obtain ⟨cf⟩ := ihf hf
      obtain ⟨ca⟩ := iha ha
      exact ⟨convT_of_tyConv (ConvT.app _ _ _ _ _ _ _ cf ca) hcv⟩

/-! ## RM017T — conversion of two terms at a type, at `piRow` -/

/-- `convCert_convT` at the native `piRow`: the acceptance's two
    `CertTrace`s (extracted by `convCert_trace`) map through
    `certTrace_convT_rows` at the common type; the join is the left
    trace trans'd with the symm of the right. -/
theorem convCert_convT_rows {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B'))
    (fuel : Nat) (A l r T : Expr Nat)
    (htyl : HasTyT E n Γ l T) (htyr : HasTyT E n Γ r T)
    (hacc : ∃ c, convCert E n fuel Γ A l r = .ok c) :
    Nonempty (ConvT E n Γ l r T) := by
  obtain ⟨c, hc⟩ := hacc
  obtain ⟨d, t₁, t₂⟩ := convCert_trace fuel Γ A l r c hc
  obtain ⟨c₁⟩ := certTrace_convT_rows hW hΓ piRow t₁ htyl
  obtain ⟨c₂⟩ := certTrace_convT_rows hW hΓ piRow t₂ htyr
  exact ⟨.trans Γ l d r T c₁ (.symm Γ r d T c₂)⟩

/-- `RM017T_conversion_confirmed` at the native `piRow`: the convAt
    arm's acceptance equation unfolded as in the sealed half, the
    extracted certifier acceptance riding `convCert_convT_rows`. -/
theorem RM017T_conversion_confirmed_rows {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (piRow : ∀ {Γ' : LCtx}, CtxWfT E n Γ' → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ' (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ' A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ') B B'))
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A l r T : Expr Nat) (htask : s.task = .convAt A l r)
    (htyl : HasTyT E n Γ l T) (htyr : HasTyT E n Γ r T)
    (hacc : kernelStepRaw s = .result (.accepted .conversionConfirmed)) :
    Nonempty (ConvT E n Γ l r T) := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next c heq =>
          have hex : ∃ c', convCert s.ambient.env s.ambient.univs (b + 1)
              s.ambient.ctx A l r = Cert.ok c' := ⟨c, heq⟩
          rw [hamb] at hex
          exact convCert_convT_rows hW hΓ piRow _ A l r T htyl htyr hex
      · split at hacc
        · nomatch hacc
        · nomatch hacc

/-! ## consumption pins — the `piRow` hypothesis inhabited by the
    LANDED supplier at real fixtures -/

/-- PIN: `machineRedSRT_rows` consumed at a beta head step on
    `natEnvU`, the `piRow` hypothesis supplied by the landed
    semantic-prefix supplier — the hypothesis is inhabited, not
    vacuous. -/
theorem pin_machineRedSRT_beta_rows :
    Nonempty (HasTyT natEnvU 1 []
      (foldApps (instantiate0 (.sort .zero) (.bvar 0)) [])
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  machineRedSRT_rows natEnvUWfT CtxWfT.nil
    (typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1).piRow
    (pinBetaApp natEnvU 1)
    (MachineRed.headBeta [] (.sort (.succ .zero)) (.bvar 0)
      (.sort .zero) [] (.refl [] _))

/-- PIN: `RM014T_whnf_typed_rows` consumed at the real
    `pinWhnfState`/`pin_RM014T_acceptance` run. -/
theorem pin_RM014T_whnf_rows :
    Nonempty (HasTyT natEnvU 1 [] (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM014T_whnf_typed_rows natEnvUWfT CtxWfT.nil
    (typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1).piRow
    pinWhnfState rfl (.sort (.succ .zero)) pinBetaRedex pinBetaReduct rfl
    (pinBetaApp natEnvU 1) pin_RM014T_acceptance

/-- PIN: `RM017T_conversion_confirmed_rows` consumed at the real
    `pinConvAtState`/`pin_convAt_acceptance` run (the β pair). -/
theorem pin_RM017T_conv_rows :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM017T_conversion_confirmed_rows natEnvUWfT CtxWfT.nil
    (typedRowsWf_of_envWfT_semPrefix natEnvUWfT natEnvUWfT_inScope 1).piRow
    pinConvAtState rfl _ _ _ _ rfl (pinBetaApp natEnvU 1) pinBetaReductTy
    pin_convAt_acceptance

end Rcic.Machine

#print axioms Rcic.Machine.CertTrace
#print axioms Rcic.Machine.machineBetaStepT_rows
#print axioms Rcic.Machine.machineZetaStepT_rows
#print axioms Rcic.Machine.machineRedSRT_rows
#print axioms Rcic.Machine.RM014T_whnf_typed_rows
#print axioms Rcic.Machine.machineBetaConvT_rows
#print axioms Rcic.Machine.machineRed_toConvT_rows
#print axioms Rcic.Machine.convCert_trace
#print axioms Rcic.Machine.certTrace_convT_rows
#print axioms Rcic.Machine.convCert_convT_rows
#print axioms Rcic.Machine.RM017T_conversion_confirmed_rows
#print axioms Rcic.Machine.pin_machineRedSRT_beta_rows
#print axioms Rcic.Machine.pin_RM014T_whnf_rows
#print axioms Rcic.Machine.pin_RM017T_conv_rows
