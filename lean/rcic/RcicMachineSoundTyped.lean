import rcic.RcicMachine
import rcic.RcicParRedDevel
import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedConv
import rcic.RcicParRedSRTyped

/-!
# O2S segment iv — RM014/RM017's typed-result rows, in scope (00 §19.1 O-2)

The two F-03 (e) CONDITIONAL rows (`RM014_whnf_typed`, `RM017_join_typed`)
still conclude the LEGACY judgment. Their counterparts here run everything
through the typed judgment and the `MachineRed`/`ParRedStar` spines, as the
hard order prescribes:

* `machineRedSRT` — `HasTyT` is preserved along `MachineRed`, by iterated head
  steps under `hasTyTFoldAppsHeadT`; the three head steps are the segment-1
  β/ζ/δ arguments restated at a FIXED type `S` (`machineBetaStepT` through the
  Π row and typed substitution, `machineZetaStepT` through `ConvT.zeta` and
  the endpoints theorem, `machineDeltaStepT` through `envWfT_bodyTyped`);
* `parRedStarSRT`/`parRedStarConvT` — the same transports iterated along a
  `ParRedStar` chain (`parRedSRT`/`parRedConvT` per step), gated by the
  chain's `starLevelsIn` witness;
* `RM014T_whnf_typed` — the whnf acceptance's reduct is typed, by unfolding
  `kernelStepRaw`'s whnfAt arm and applying `machineRedSRT`;
* `convCert_chains` — every `convCert` acceptance carries `ParRedStar` chains
  of both sides to one common reduct, plus their `starLevelsIn` witnesses
  (extracted by replaying the certifier's own case structure; no `Conv` value
  is consumed beyond the acceptance). The chain language is `ParRedStar`
  rather than `MachineRed`: `convCert`'s `.app`/`.app` congruence arm joins
  stuck whnfs whose convertible arguments sit BELOW the spine head — a join
  that head steps alone cannot express (the same reason `convRedOnly_join`
  answers at `ParRedStar` level);
* `RM017T_join_typed` — the join of an accepted conversion is typed: the
  chains come out at `ParRedStar` directly and the typing rides the LEFT
  chain through `parRedStarSRT`. NO `parRedStarSR`, no confluence diamond,
  no legacy join machinery.

Premise disclosure (the degeneracy tooth): every counterpart below takes only
`EnvWfT`, `hW.InScope`, `CtxWfT`, and the row's own subject matter (the
machine acceptance equations). No premise names a row, `TypedRowsWf`,
`AnnEnvA`, `EnvSemA` or `IotaSRA`; no STATEMENT below mentions the legacy
`HasTy` or `CtxWf` (`RM017T_join_typed` quantifies the certifier's
conversion value existentially, so the legacy `Conv` type is not named
either; grep quoted in the PR). The rows enter only inside proofs, through
the scope bridge.

The conclusions are `Nonempty`-wrapped where the scope supply is
`Nonempty`-valued: the typed rows (`piConvInjT_scopeCheck` and successors)
supply conversions as `Nonempty`, so data-valued conclusions would need
choice. δ's step is pure data throughout.

Consumption pins, no supply parameter: `pin_machineRedSRT_beta` (a beta head
step on `natEnvU`), `pin_RM017T_convCert` (a real `convCert` acceptance of a
beta redex against its reduct, run by `rfl`), `pin_RM014T_whnf` (a real
`kernelStepRaw` whnf run on `natEnvU`, acceptance by `rfl`).

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## the spine transport and the three typed head steps -/

/-- Annex 21 M-3's spine transport, typed and `Nonempty`-valued: a head
    typing transfer closes over the spine by app-inversion and chain
    retyping. -/
theorem hasTyTFoldAppsHeadT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat}
    (hstep : (S : Expr Nat) → HasTyT E n Γ f S →
      Nonempty (HasTyT E n Γ f' S)) :
    (xs : List (Expr Nat)) → {T : Expr Nat}→
    HasTyT E n Γ (foldApps f xs) T →
    Nonempty (HasTyT E n Γ (foldApps f' xs) T)
  | [], _, h => hstep _ h
  | x :: xs, _, h =>
      hasTyTFoldAppsHeadT (f := .app f x) (f' := .app f' x)
        (fun S hS =>
          have inv := hasTyTInv_app hS rfl
          have ⟨A0, B0, hf, ha, hcv⟩ := inv
          (hstep (.pi A0 B0) hf).elim fun hf' =>
            ⟨hasTyT_of_tyConv (HasTyT.app _ _ _ _ _ hf' ha) hcv⟩) xs h

/-- one typed beta head step at the FIXED type `S` (the segment-1 β argument:
    app/lam inversion, the Π row in scope, the domain conversion collapsed at
    the domain's own sort, the codomain chain retyping the body, typed
    substitution of the argument, and the app inversion's chain landing at
    `S`). -/
theorem machineBetaStepT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A body arg : Expr Nat) :
    (S : Expr Nat) → HasTyT E n Γ (.app (.lam A body) arg) S →
    Nonempty (HasTyT E n Γ (instantiate0 arg body) S) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  intro S h
  have hrows := typedRowsWf_of_envWfT_semPrefix hW hP n
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
  obtain ⟨cdom⟩ := convT_of_tyConvT_sort C hn hΓ hA0ty hBdom
  have hbody' := hasTyT_of_tyConv hbody hBcod
  have ha' := HasTyT.conv _ _ _ _ u ha (ConvT.symm _ _ _ _ cdom)
  exact ⟨hasTyT_of_tyConv (hasTyT_subst0_of_envWfT hW hbody' ha') hcv⟩

/-- one typed zeta head step at the FIXED type `S` (letE inversion,
    `ConvT.zeta`, the endpoints theorem, the chain landing at `S`). -/
theorem machineZetaStepT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A value body : Expr Nat) :
    (S : Expr Nat) → HasTyT E n Γ (.letE A value body) S →
    Nonempty (HasTyT E n Γ (instantiate0 value body) S) := by
  intro S h
  obtain ⟨u, B_let, hAty, hv, hb, hcv⟩ := hasTyTInv_letE h rfl
  have hz := ConvT.zeta _ A value body B_let u hAty hv hb
  obtain ⟨_, ⟨hr⟩⟩ := DT009T_endpoints_inScope hW hP hΓ hz
  exact ⟨hasTyT_of_tyConv hr hcv⟩

/-- one typed delta head step at the FIXED type `S` — pure data: const
    inversion plus `envWfT_bodyTyped`, the chain landing at `S`. -/
theorem machineDeltaStepT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat)
    (hres : E.members r = some m) (hbody : m.body = some b) :
    (S : Expr Nat) → HasTyT E n Γ (.const r ls) S →
    Nonempty (HasTyT E n Γ (instantiateLevels ls b) S) := by
  intro S h
  obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const h rfl
  have hmeq : some m = some m' := hres.symm.trans hres'
  injection hmeq with hmeq'
  subst hmeq'
  exact ⟨hasTyT_of_tyConv (envWfT_bodyTyped hW hres hbody hlen) hcv⟩

/-! ## the typed slice subject reduction -/

/-- `HasTyT` is preserved along `MachineRed` (the machine's slice), by
    iterated head steps under `hasTyTFoldAppsHeadT`. -/
theorem machineRedSRT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {e A e' : Expr Nat}→ HasTyT E n Γ e A → MachineRed E n Γ e e' →
    Nonempty (HasTyT E n Γ e' A) := by
  intro e A e' h k
  induction k with
  | refl e₀ => exact ⟨h⟩
  | headBeta A body arg rest k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineBetaStepT hW hP hΓ A body arg) rest h
      exact ih h'
  | headZeta A value body rest k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineZetaStepT hW hP hΓ A value body) rest h
      exact ih h'
  | headDelta r ls m b rest hres hbody htr k' ih =>
      obtain ⟨h'⟩ :=
        hasTyTFoldAppsHeadT (machineDeltaStepT hW r ls m b hres hbody) rest h
      exact ih h'

/-! ## RM014T — the whnf acceptance's reduct is typed -/

/-- F-03 (e)'s first conditional row, typed: an accepted whnf run preserves
    the type. Mirrors the legacy unfolding of `kernelStepRaw`'s whnfAt arm;
    the extracted `MachineRed` chain rides `machineRedSRT`. -/
theorem RM014T_whnf_typed {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
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
          exact machineRedSRT hW hP hΓ hty kred
      · nomatch hacc

/-! ## the certifier's chains -/

/-- R-1″'s per-step predicate lifted to a chain: every `ParRed` step of the
    star satisfies `levelsIn`. The typed transports (`parRedSRT`,
    `parRedConvT`) are gated stepwise, so a chain that feeds them carries
    this witness. -/
def starLevelsIn {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → ParRedStar E n Γ a b → Bool
  | _, _, _, .refl _ _ => true
  | _, _, _, .tail h hs => levelsIn h && starLevelsIn hs

theorem starLevelsIn_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c : Expr Nat} (k1 : ParRedStar E n Γ a b)
    (k2 : ParRedStar E n Γ b c) :
    starLevelsIn (parRedStar_trans k1 k2) =
      (starLevelsIn k1 && starLevelsIn k2) := by
  induction k1 with
  | refl => simp only [parRedStar_trans, starLevelsIn, Bool.true_and]
  | tail h hs ih =>
      simp only [parRedStar_trans, starLevelsIn, ih, Bool.and_assoc]

theorem starLevelsIn_app_fun {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' a : Expr Nat} (k : ParRedStar E n Γ f f') :
    starLevelsIn (parRedStar_app_fun (a := a) k) = starLevelsIn k := by
  induction k with
  | refl => simp only [parRedStar_app_fun, starLevelsIn]
  | tail h hs ih =>
      simp only [parRedStar_app_fun, starLevelsIn, ih, levelsIn,
        Bool.and_true]

theorem starLevelsIn_app_arg {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a a' : Expr Nat} (k : ParRedStar E n Γ a a') :
    starLevelsIn (parRedStar_app_arg (f := f) k) = starLevelsIn k := by
  induction k with
  | refl => simp only [parRedStar_app_arg, starLevelsIn]
  | tail h hs ih =>
      simp only [parRedStar_app_arg, starLevelsIn, ih, levelsIn,
        Bool.true_and]

theorem starLevelsIn_app_congr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' a a' : Expr Nat} (kf : ParRedStar E n Γ f f')
    (ka : ParRedStar E n Γ a a') :
    starLevelsIn (parRedStar_app_congr kf ka) =
      (starLevelsIn kf && starLevelsIn ka) := by
  simp only [parRedStar_app_congr, starLevelsIn_trans,
    starLevelsIn_app_fun, starLevelsIn_app_arg]

/-- `levelsIn` of a spine congruence at refl arguments reduces to the
    head step's. -/
theorem levelsIn_foldApps_congr_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat} (hf : ParRed E n Γ f f') (xs : List (Expr Nat)) :
    levelsIn (parRed_foldApps_congr (parRedArgs_refl xs) hf) =
      levelsIn hf := by
  induction xs generalizing f f' with
  | nil => rfl
  | cons x xs ih =>
      simp only [parRedArgs_refl, parRed_foldApps_congr, ih, levelsIn,
        Bool.and_true]

/-- every step `machineRed_toParRedStar` emits is `levelsIn`: the three
    head steps map to β/ζ/δ single steps with refl premises under a
    refl-args spine congruence. -/
theorem starLevelsIn_machineRed_toParRedStar {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (k : MachineRed E n Γ a b) →
    starLevelsIn (machineRed_toParRedStar k) = true := by
  intro Γ a b k
  induction k with
  | refl => simp only [machineRed_toParRedStar, starLevelsIn]
  | headBeta A body arg rest k ih =>
      simp only [machineRed_toParRedStar, starLevelsIn,
        levelsIn_foldApps_congr_refl, ih, levelsIn, Bool.and_true]
  | headZeta A value body rest k ih =>
      simp only [machineRed_toParRedStar, starLevelsIn,
        levelsIn_foldApps_congr_refl, ih, levelsIn, Bool.and_true]
  | headDelta r ls m b rest hres hbody htr k ih =>
      simp only [machineRed_toParRedStar, starLevelsIn,
        levelsIn_foldApps_congr_refl, ih, levelsIn, Bool.and_true]

/-- every `convCert` acceptance carries `ParRedStar` chains of BOTH sides to
    one common reduct — extracted by replaying the certifier's own case
    structure (syntax-equality; whnf both sides; whnf agreement; head
    equality for sorts and constants; the `.app`/`.app` congruence arm
    recursing into both parts and joining under `parRedStar_app_congr`).

    The chain language is `ParRedStar`, not `MachineRed`: the app arm's
    sub-joins sit inside a stuck whnf's arguments, which head steps cannot
    reach — the same reason `convRedOnly_join` answers at `ParRedStar`
    level. Each chain carries its `starLevelsIn` witness so the typed
    transports can consume it. -/
def convCert_chains {E : ResolvedEnv} {n : Nat} :
    (fuel : Nat) → (Γ : LCtx) → (A l r : Expr Nat) → (c : Conv E n Γ l r) →
    convCert E n fuel Γ A l r = .ok c →
    Σ' (d : Expr Nat), (k1 : ParRedStar E n Γ l d) ×'
      (k2 : ParRedStar E n Γ r d) ×'
      (starLevelsIn k1 = true ∧ starLevelsIn k2 = true) := by
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
        exact ⟨l, .refl _ _, .refl _ _, by simp only [starLevelsIn],
          by simp only [starLevelsIn]⟩
      · split at h
        · nomatch h
        · split at h
          · nomatch h
          · next wl kl heql wr kr heqr =>
              split at h
              · rename_i hwleq
                subst hwleq
                exact ⟨wl, machineRed_toParRedStar kl,
                  machineRed_toParRedStar kr,
                  starLevelsIn_machineRed_toParRedStar _,
                  starLevelsIn_machineRed_toParRedStar _⟩
              · split at h
                · next _ _ u v kleft kright _ =>
                    split at h
                    · rename_i huv
                      subst huv
                      exact ⟨_, machineRed_toParRedStar kleft,
                        machineRed_toParRedStar kright,
                        starLevelsIn_machineRed_toParRedStar _,
                        starLevelsIn_machineRed_toParRedStar _⟩
                    · nomatch h
                · next _ _ r₁ ls₁ r₂ ls₂ kleft kright _ =>
                    split at h
                    · rename_i hconj
                      obtain ⟨h1, h2⟩ := hconj
                      subst h1
                      subst h2
                      exact ⟨_, machineRed_toParRedStar kleft,
                        machineRed_toParRedStar kright,
                        starLevelsIn_machineRed_toParRedStar _,
                        starLevelsIn_machineRed_toParRedStar _⟩
                    · nomatch h
                · next _ _ f₁ a₁ f₂ a₂ kleft kright _ =>
                    split at h
                    · nomatch h
                    · next hf =>
                        split at h
                        · nomatch h
                        · next ha =>
                            have ⟨df, kf1, kf2, hlf1, hlf2⟩ :=
                              ih Γ A f₁ f₂ _ hf
                            have ⟨da, ka1, ka2, hla1, hla2⟩ :=
                              ih Γ A a₁ a₂ _ ha
                            exact ⟨.app df da,
                              parRedStar_trans (machineRed_toParRedStar kleft)
                                (parRedStar_app_congr kf1 ka1),
                              parRedStar_trans (machineRed_toParRedStar kright)
                                (parRedStar_app_congr kf2 ka2),
                              by
                                rw [starLevelsIn_trans,
                                  starLevelsIn_machineRed_toParRedStar,
                                  starLevelsIn_app_congr, hlf1, hla1]
                                decide,
                              by
                                rw [starLevelsIn_trans,
                                  starLevelsIn_machineRed_toParRedStar,
                                  starLevelsIn_app_congr, hlf2, hla2]
                                decide⟩
                · nomatch h

/-- `HasTyT` iterated along a `ParRedStar` chain — `parRedSRT` per step;
    the chain's own `starLevelsIn` witness discharges each step's gate. -/
theorem parRedStarSRT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (k : ParRedStar E n Γ a b) :
    HasTyT E n Γ a A → starLevelsIn k = true →
    Nonempty (HasTyT E n Γ b A) := by
  induction k with
  | refl =>
      intro hty _
      exact ⟨hty⟩
  | tail h hs ih =>
      intro hty hl
      simp only [starLevelsIn, Bool.and_eq_true] at hl
      exact (parRedSRT hW hP hΓ hty h hl.1).elim fun hty' => ih hty' hl.2

/-- `parRedConvT` iterated along a `ParRedStar` chain — one `ConvT` per step
    (the middle typing by the endpoints theorem), trans-composed into the
    chain's conversion at the FIXED type `T`. The conv counterpart of
    `parRedStarSRT`. -/
theorem parRedStarConvT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (k : ParRedStar E n Γ a b) :
    HasTyT E n Γ a T → starLevelsIn k = true →
    Nonempty (ConvT E n Γ a b T) := by
  induction k with
  | refl =>
      intro hty _
      exact ⟨.refl _ _ _ hty⟩
  | tail h hs ih =>
      intro hty hl
      simp only [starLevelsIn, Bool.and_eq_true] at hl
      obtain ⟨c⟩ := parRedConvT hW hP hΓ hty h hl.1
      obtain ⟨hty'⟩ := (DT009T_endpoints_inScope hW hP hΓ c).2
      obtain ⟨c'⟩ := ih hty' hl.2
      exact ⟨.trans _ _ _ _ _ c c'⟩

/-! ## RM017T — the join of an accepted conversion is typed -/

/-- F-03 (e)'s second conditional row, typed: the join of an accepted
    conversion is typed. The chains come out at `ParRedStar` directly and
    the typing rides the LEFT chain through `parRedStarSRT` — NO
    `parRedStarSR`, no confluence diamond, no legacy join machinery. The
    certifier's conversion value is quantified existentially, so no legacy
    judgment type is named. -/
theorem RM017T_join_typed {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (fuel : Nat) (A l r T : Expr Nat)
    (hacc : ∃ c, convCert E n fuel Γ A l r = .ok c)
    (hty : HasTyT E n Γ l T) :
    Nonempty (Σ' (d : Expr Nat), ParRedStar E n Γ l d ×' ParRedStar E n Γ r d ×'
      Nonempty (HasTyT E n Γ d T)) := by
  obtain ⟨c, hc⟩ := hacc
  obtain ⟨d, k1, k2, hl1, -⟩ := convCert_chains fuel Γ A l r c hc
  exact ⟨d, k1, k2, parRedStarSRT hW hP hΓ k1 hty hl1⟩

/-! ## consumption pins (real machine runs, no supply parameter) -/

/-- PIN: `machineRedSRT` consumed at a beta head step on `natEnvU`. -/
theorem pin_machineRedSRT_beta :
    Nonempty (HasTyT natEnvU 1 []
      (foldApps (instantiate0 (.sort .zero) (.bvar 0)) [])
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  machineRedSRT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    (pinBetaApp natEnvU 1)
    (MachineRed.headBeta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero) []
      (.refl [] _))

/-- PIN: a real `convCert` acceptance — the beta redex against its reduct on
    `natEnvU` — the certifier's own output witness, run by `rfl`. -/
def pinBetaRedex : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)

def pinBetaReduct : Expr Nat := instantiate0 (.sort .zero) (.bvar 0)

def pinConvKl : MachineRed natEnvU 1 [] pinBetaRedex pinBetaReduct :=
  MachineRed.headBeta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero) []
    (.refl [] _)

def pinConvC : Conv natEnvU 1 [] pinBetaRedex pinBetaReduct :=
  .trans [] _ _ _ (machineRed_toConv pinConvKl)
    (.trans [] _ _ _ (.refl [] pinBetaReduct)
      (.symm [] _ _ (machineRed_toConv (.refl [] pinBetaReduct))))

theorem pin_RM017T_convCert :
    ∃ c, convCert natEnvU 1 2 [] (.sort (.succ (.succ .zero)))
      pinBetaRedex pinBetaReduct = .ok c := ⟨pinConvC, rfl⟩

/-- PIN: `RM017T_join_typed` consumed at that acceptance. -/
theorem pin_RM017T_join :
    Nonempty (Σ' (d : Expr Nat),
      ParRedStar natEnvU 1 []
        (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)) d ×'
      ParRedStar natEnvU 1 [] (.sort .zero) d ×'
      Nonempty (HasTyT natEnvU 1 [] d
        (instantiate0 (.sort .zero) (.sort (.succ .zero))))) :=
  RM017T_join_typed natEnvUWfT natEnvUWfT_inScope CtxWfT.nil 2
    (.sort (.succ (.succ .zero))) pinBetaRedex pinBetaReduct
    (instantiate0 (.sort .zero) (.sort (.succ .zero)))
    pin_RM017T_convCert (pinBetaApp natEnvU 1)

/-- PIN: a real `kernelStepRaw` whnf run on `natEnvU`, acceptance by `rfl`. -/
def pinWhnfState : RawState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .whnfAt (.sort (.succ .zero)) pinBetaRedex
  budget := 2

theorem pin_RM014T_acceptance :
    kernelStepRaw pinWhnfState = .result (.accepted
      (.inferredWhnf (.sort (.succ .zero)) (instantiate0 (.sort .zero) (.bvar 0)))) := rfl

/-- PIN: `RM014T_whnf_typed` consumed at that run. -/
theorem pin_RM014T_whnf :
    Nonempty (HasTyT natEnvU 1 [] (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM014T_whnf_typed natEnvUWfT natEnvUWfT_inScope CtxWfT.nil pinWhnfState rfl
    (.sort (.succ .zero)) pinBetaRedex pinBetaReduct rfl
    (pinBetaApp natEnvU 1) pin_RM014T_acceptance

end Rcic.Machine

#print axioms Rcic.Machine.hasTyTFoldAppsHeadT
#print axioms Rcic.Machine.machineBetaStepT
#print axioms Rcic.Machine.machineZetaStepT
#print axioms Rcic.Machine.machineDeltaStepT
#print axioms Rcic.Machine.machineRedSRT
#print axioms Rcic.Machine.RM014T_whnf_typed
#print axioms Rcic.Machine.starLevelsIn
#print axioms Rcic.Machine.starLevelsIn_trans
#print axioms Rcic.Machine.starLevelsIn_app_fun
#print axioms Rcic.Machine.starLevelsIn_app_arg
#print axioms Rcic.Machine.starLevelsIn_app_congr
#print axioms Rcic.Machine.levelsIn_foldApps_congr_refl
#print axioms Rcic.Machine.starLevelsIn_machineRed_toParRedStar
#print axioms Rcic.Machine.convCert_chains
#print axioms Rcic.Machine.parRedStarSRT
#print axioms Rcic.Machine.parRedStarConvT
#print axioms Rcic.Machine.RM017T_join_typed
#print axioms Rcic.Machine.pin_machineRedSRT_beta
#print axioms Rcic.Machine.pin_RM017T_convCert
#print axioms Rcic.Machine.pin_RM017T_join
#print axioms Rcic.Machine.pin_RM014T_acceptance
#print axioms Rcic.Machine.pin_RM014T_whnf
