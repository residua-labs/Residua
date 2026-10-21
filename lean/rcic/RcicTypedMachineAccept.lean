import rcic.RcicTypedConvTerm
import rcic.RcicTypedMachine

/-!
# T1-T segments (ii)+(iii)+(iv) — the typed machine's ACCEPTANCE rows

RULING R-3 (cc as architect, 2026-10-09) — recorded here because it
restates this module's infer/check rows. The finding it addresses: the
previous `RM016T_run_check_sound` took BOTH the raw machine's run
acceptance (`runRaw`, computed into `_hstep` and UNUSED) and the
certifier's acceptance (`tyAtC ... .isSome`), so deleting the machine
premise still proved the row; `RM015T_infer_sound`/`RM016T_check_sound`
were `inferC`/`tyAtC`'s own types restated. What T1-T §2/§3(ii) asks
is a TYPED machine whose arms are built over the typed certifiers, so
the ACCEPTANCE ITSELF carries the derivation. That machine is
`RcicTypedMachine.lean` (beside the legacy one, `RcicMachine.lean`
untouched); this module's rows now read:

* `RM012T_lookupLocal_hasTy` / `RM013T_lookupDeclaration_hasTy` —
  STEP-LEVEL, against `kernelStepRaw`, UNCHANGED (R-3 clause 1: the
  raw machine's lookup arms' own data suffices; the lookupLocal arm's
  `lookupType` equation IS the typed `bvar` rule's premise, the
  lookupDeclaration extraction reads only member data and discards the
  arm's legacy derivation as `_hty`).
* `RM015T_infer_sound` / `RM016T_check_sound` (step) /
  `RM016T_run_check_sound` (run) — RESTATED against the TYPED machine
  (R-3 clauses 2-3): the acceptance premise is the typed machine's own
  step/run equation with the DERIVATION IN THE PAYLOAD (the
  `Σ'` binder carries the payload's derivation; there is no other
  acceptance premise — no `inferC`/`tyAtC`/`.isSome` anywhere). The
  proof unfolds the machine's arm, splits the certifier call, and
  reads the payload off the equation — the acceptance carries the
  judgment, which is the point. The degenerate hacc+hchk shape is
  GONE (old versions deleted, not weakened).
* `RM017T_conversion_confirmed` — STEP-LEVEL, against `kernelStepRaw`,
  UNCHANGED (R-3 clause 1): the convAt arm's acceptance equation, plus
  the two typings and the scope bridge, rides segment (i)'s
  `convCert_convT`.

Premise disclosure (the degeneracy tooth): the typed-machine rows take
ONLY the task shape and the machine's own acceptance — no row, no
`EnvWfT`, no `CtxWfT`, no `hW.InScope`, no certifier premise (the
payload carries everything; the scope bridge is not needed at all on
these rows). `RM017T` keeps its `EnvWfT`/`InScope`/`CtxWfT` premises
where the judgment side needs them, consumed only inside its proof
through the scope bridge, never by name here. No statement mentions
either legacy judgment type as a bare token (word-boundary grep 0 over
this file).

THE REFUSAL TOOTH (R-3 clause 4): the pin is a RUN of the typed
machine on `check (sort 0) (sort 0)` at the empty environment
returning its named refusal, by `rfl`. The typed checker finds
`Sort 1` for `Sort 0` and is asked for `Sort 0`; no typed conversion
closes that gap. The legacy JUDGMENT's conclusion holds there
(`propSelfTyped`, `RcicUntypedConvCollapse.lean:84` — proof irrelevance
through equal sorts); a comment suffices, no legacy proof is given.
Measured, not assumed: the raw machine's own check arm REFUSES this
pair too, with `[rcic_conv_irrelevance_out_of_slice]` (its conversion
runs expected-against-found, `RcicMachine.lean:386`) — so the
divergence at this pair is judgment-versus-certifier, not
raw-versus-typed.

Consumption pins: step-level lookups on `natEnvU`-shaped ambients
(kept); `whnfAt` of the β-redex at fuel 2 through segment (i)'s
`RM014T_whnf_conv` (kept); `convAt` of the β pair and of a δ pair on
`pinDefEnvU` (kept). The infer/check pins are RUNS of the typed
machine (R-3 clause 4: runs, not bare certifier calls): check of the
zero constructor at its family, infer of the application
`succ zero`, each consumed through the restated rows — the run row
consumed with the run acceptance as its ONLY premise.

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-! ## step-level rows — the arms whose own data suffices (R-3 clause 1: unchanged) -/

/-- RM-012 restated on the typed judgment: an accepted `lookupLocal` run
    carries the local's typing. The arm's own `lookupType` equation IS the
    typed `bvar` rule's premise — the legacy row's structure replayed. -/
def RM012T_lookupLocal_hasTy (s : RawState) (i : Nat)
    (A : Expr Nat) (htask : s.task = .lookupLocal i)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType A))) :
    HasTyT s.ambient.env s.ambient.univs s.ambient.ctx (.bvar i) A := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next A' heq =>
          simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
            AcceptedPayload.inferredType.injEq] at hacc
          exact hacc ▸ HasTyT.bvar s.ambient.ctx i A' heq
      · nomatch hacc

/-- RM-013 restated on the typed judgment: an accepted `lookupDeclaration`
    run carries the constant's typing. The extraction replays the arm's own
    case structure and reads only the MEMBER DATA (empty levels, the
    member, arity zero, the payload type equation); the arm's internal
    legacy-returning derivation is bound as `_hty` and discarded — machine
    surface only, never consumed. -/
def RM013T_lookupDeclaration_hasTy (s : RawState) (r : Nat)
    (ls : List Level) (T : Expr Nat)
    (htask : s.task = .lookupDeclaration r ls)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredType T))) :
    HasTyT s.ambient.env s.ambient.univs s.ambient.ctx (.const r ls) T := by
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      exact nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb, inferCert] at hacc
      split at hacc
      · next T' _hty heq =>
          have hT : T' = T := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredType.injEq] at hacc
            exact hacc
          split at heq
          · next hls =>
              split at heq
              · next m hm =>
                  split at heq
                  · next h0 =>
                      simp only [Cert.ok.injEq] at heq
                      have hTm : instantiateLevels ls m.mtype = T' := by
                        cases heq; rfl
                      have hlen : ls.length = m.arity := by
                        subst hls; simp only [List.length_nil]; exact h0
                      have hwf : levelsBounded s.ambient.univs ls = true := by
                        subst hls; rfl
                      exact (hTm.trans hT) ▸
                        HasTyT.const s.ambient.ctx r ls m hm hlen hwf
                  · nomatch heq
              · nomatch heq
          · nomatch heq
      · nomatch hacc

/-! ## typed-machine rows — infer / check (R-3 clauses 2-3: the
    acceptance carries the derivation) -/

/-- RM-015 restated against the TYPED machine's infer arm (R-3): the
    acceptance is the machine's own step equation with the derivation
    IN the payload (the sigma binds it — `Σ'`, not `∃`: the payload is
    Type-valued data, the `Nonempty`-free wrapper); the judgment is read off
    the arm by unfolding the step, splitting the certifier call, and
    taking the payload's injectivity. No certifier premise exists to
    delete — the old shape (raw acceptance computed and unused beside
    `inferC`'s own type) is gone. -/
def RM015T_infer_sound (s : TypedState) (e T : Expr Nat)
    (htask : s.task = .inferT e)
    (hacc : Σ' d, typedStep s = .accepted (.inferred e T d)) :
    HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e T := by
  obtain ⟨d, hd⟩ := hacc
  cases hb : s.budget with
  | zero =>
      simp only [typedStep, htask, hb] at hd
      nomatch hd
  | succ b =>
      simp only [typedStep, htask, hb] at hd
      split at hd
      · rename_i _ hderiv _
        simp only [TypedResult.accepted.injEq, TypedAccepted.inferred.injEq] at hd
        exact hd.2.1 ▸ hderiv
      · nomatch hd

/-- RM-016 restated against the TYPED machine's check arm (R-3): the
    acceptance is the machine's own step equation with the derivation
    IN the payload — the same read-off as the infer row, at the asked
    type. The old `.isSome`-premised shape is gone. -/
def RM016T_check_sound (s : TypedState) (e A : Expr Nat)
    (htask : s.task = .checkT2 A e)
    (hacc : Σ' d, typedStep s = .accepted (.checked e A d)) :
    HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A := by
  obtain ⟨d, hd⟩ := hacc
  cases hb : s.budget with
  | zero =>
      simp only [typedStep, htask, hb] at hd
      nomatch hd
  | succ b =>
      simp only [typedStep, htask, hb] at hd
      split at hd
      · rename_i hderiv _
        simp only [TypedResult.accepted.injEq, TypedAccepted.checked.injEq] at hd
        exact hderiv
      · nomatch hd

/-- RM-016's run level (R-3 clause 3): the ONLY acceptance premise is
    the typed machine's RUN acceptance — the run equation with the
    derivation in its payload (a `Σ'`-bound payload, read off into the
    Type-valued judgment) — and the `HasTyT` is read off that
    payload. The run unfolds to the step (the typed machine is
    one-shot, mirroring `kernelStepRaw_never_step`), then the step row
    applies; the raw `runRaw` premise and the `tyAtC` premise of the
    degenerate predecessor are both gone. -/
def RM016T_run_check_sound (k : Nat) (s : TypedState) (e A : Expr Nat)
    (htask : s.task = .checkT2 A e)
    (hacc : Σ' d, typedRun (k + 1) s = .accepted (.checked e A d)) :
    HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A := by
  obtain ⟨d, hd⟩ := hacc
  simp only [typedRun] at hd
  exact RM016T_check_sound s e A htask ⟨d, hd⟩

/-! ## the conversion row (step-level through segment (i)) -/

/-- RM-017 restated on the typed judgment: an accepted `convAt` run carries
    a typed conversion chain between the two terms at their common type.
    The acceptance equation over the arm, plus the two typings and the
    scope bridge, rides segment (i)'s `convCert_convT` (whose acceptance
    premise is exactly the existential this arm's extraction produces); the
    arm's internal certifier payload is bound and not consumed. -/
theorem RM017T_conversion_confirmed {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
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
          -- the payload's type is indexed by the ambient, so the raw
          -- equation cannot be rewritten along `hamb` directly (the motive
          -- goes ill-typed); the existential absorbs the dependency and
          -- transports as a whole
          have hex : ∃ c', convCert s.ambient.env s.ambient.univs (b + 1)
              s.ambient.ctx A l r = Cert.ok c' := ⟨c, heq⟩
          rw [hamb] at hex
          exact convCert_convT hW hP hΓ _ A l r T htyl htyr hex
      · split at hacc
        · nomatch hacc
        · nomatch hacc

/-! ## the refusal tooth (R-3 clause 4: a RUN of the typed machine) -/

/-- PIN (refusal): the typed machine's RUN on `check (sort 0) (sort 0)`
    at the empty environment REFUSES with the arm's named residue — by
    `rfl`. The typed checker finds `Sort 1` for `Sort 0` and is asked
    for `Sort 0`, and no typed conversion closes the gap (the sorts
    conversion needs level equality `1 = 0`, decided false). The legacy
    judgment's conclusion would hold there (`propSelfTyped`,
    `RcicUntypedConvCollapse.lean:84`, proof irrelevance through equal
    sorts) — noted as a comment per the dispatch, no legacy proof given.
    The raw machine's own check arm also refuses this pair, with
    `[rcic_conv_irrelevance_out_of_slice]` (its conversion runs
    expected-against-found, `RcicMachine.lean:386`). -/
def pinTypedRefusalState : TypedState where
  ambient := ⟨emptyEnv, 1, []⟩
  task := .checkT2 (.sort .zero) (.sort .zero)
  budget := 2

theorem pin_refusal_typedRun_sortSelf :
    typedRun 2 pinTypedRefusalState = .refused "[rcic_typed_check_refused]" := rfl

/-! ## acceptance pins — step-level lookups on real ambients -/

/-- PIN: a real `lookupLocal` acceptance at a nonempty context over
    `natEnvU`'s family — run by `rfl`. -/
def pinLookupLocalState : RawState where
  ambient := ⟨natEnvU, 1, [LocalDecl.assumption (.const 0 [])]⟩
  task := .lookupLocal 0
  budget := 1

theorem pin_RM012T_lookupLocal_acceptance :
    kernelStepRaw pinLookupLocalState
      = .result (.accepted (.inferredType (.const 0 []))) := rfl

/-- PIN: `RM012T_lookupLocal_hasTy` consumed at that run. -/
def pin_RM012T_lookupLocal :
    HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])] (.bvar 0) (.const 0 []) :=
  RM012T_lookupLocal_hasTy pinLookupLocalState 0 (.const 0 []) rfl
    pin_RM012T_lookupLocal_acceptance

/-- PIN: a real `lookupDeclaration` acceptance on `natEnvU` — the zero
    constructor at its family, run by `rfl` (the payload's type witness is
    the family itself). -/
def pinLookupDeclState : RawState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .lookupDeclaration 1 []
  budget := 2

theorem pin_RM013T_lookupDeclaration_acceptance :
    kernelStepRaw pinLookupDeclState
      = .result (.accepted (.inferredType (.const 0 []))) := rfl

/-- PIN: `RM013T_lookupDeclaration_hasTy` consumed at that run — the
    constructor typed AT ITS FAMILY through the machine's own arm. -/
def pin_RM013T_lookupDeclaration :
    HasTyT natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  RM013T_lookupDeclaration_hasTy pinLookupDeclState 1 [] (.const 0 []) rfl
    pin_RM013T_lookupDeclaration_acceptance

/-! ## acceptance pins — RUNS of the typed machine (R-3 clause 4) -/

/-- PIN (acceptance, check): the typed machine's RUN of `check` on the
    zero constructor at its family `N` on `natEnvU` — accepted, the
    payload carrying the derivation (bound by the `Σ'`; the run is
    `rfl`). -/
def pinTypedCheckZeroState : TypedState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .checkT2 (.const 0 []) (.const 1 [])
  budget := 2

def pin_typedRun_check_zero :
    Σ' d, typedRun 2 pinTypedCheckZeroState
      = .accepted (.checked (.const 1 []) (.const 0 []) d) := ⟨_, rfl⟩

/-- PIN: `RM016T_check_sound` consumed at that run — `typedRun 2 s` is
    definitionally `typedStep s` (the one-shot shape), so the run
    acceptance IS the step acceptance. -/
def pin_RM016T_check_zero :
    HasTyT natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  RM016T_check_sound pinTypedCheckZeroState (.const 1 []) (.const 0 []) rfl
    pin_typedRun_check_zero

/-- PIN: `RM016T_run_check_sound` consumed at the same run — the run
    acceptance is the ONLY premise. -/
def pin_RM016T_run_check_zero :
    HasTyT natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  RM016T_run_check_sound 1 pinTypedCheckZeroState (.const 1 []) (.const 0 []) rfl
    pin_typedRun_check_zero

/-- PIN (acceptance, infer): the typed machine's RUN of `infer` on an
    application — `succ zero` at `natEnvU` — accepted at the family `N`,
    the payload carrying the derivation (run by `rfl`, `Σ'`-bound). -/
def pinTypedInferAppState : TypedState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .inferT (.app (.const 2 []) (.const 1 []))
  budget := 2

def pin_typedRun_infer_succ_zero :
    Σ' d, typedRun 2 pinTypedInferAppState
      = .accepted (.inferred (.app (.const 2 []) (.const 1 []))
          (.const 0 []) d) := ⟨_, rfl⟩

/-- PIN: `RM015T_infer_sound` consumed at that run. -/
def pin_RM015T_succ_zero :
    HasTyT natEnvU 1 [] (.app (.const 2 []) (.const 1 [])) (.const 0 []) :=
  RM015T_infer_sound pinTypedInferAppState (.app (.const 2 []) (.const 1 []))
    (.const 0 []) rfl pin_typedRun_infer_succ_zero

/-! ## acceptance pins — whnfAt of the β-redex (fuel 2) -/

/-- PIN: a real `whnfAt` acceptance of the β-redex on `natEnvU` at fuel 2 —
    the reduct named in the payload (`pinBetaReduct`, the same witness the
    certifier-level `pinWhnfOut` of segment (i) carries), run by `rfl`. -/
def pinWhnfAtState : RawState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .whnfAt (.sort (.succ .zero)) pinBetaRedex
  budget := 2

theorem pin_whnfAt_acceptance :
    kernelStepRaw pinWhnfAtState = .result (.accepted
      (.inferredWhnf (.sort (.succ .zero)) pinBetaReduct)) := rfl

/-- PIN: that acceptance consumed through segment (i)'s step-level row —
    a typed conversion chain from the redex to its reduct at the term's
    own type. -/
def pin_whnfAt_conv :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM014T_whnf_conv natEnvUWfT natEnvUWfT_inScope CtxWfT.nil pinWhnfAtState rfl
    (.sort (.succ .zero)) pinBetaRedex pinBetaReduct
    (instantiate0 (.sort .zero) (.sort (.succ .zero))) rfl
    (pinBetaApp natEnvU 1) pin_whnfAt_acceptance

/-! ## acceptance pins — convAt of β- and δ-convertible terms -/

/-- PIN: a real `convAt` acceptance of the β pair (the same pair as
    `pin_RM017T_convCert`'s certifier-level acceptance), run by `rfl`. -/
def pinConvAtState : RawState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .convAt (.sort (.succ (.succ .zero))) pinBetaRedex pinBetaReduct
  budget := 2

theorem pin_convAt_acceptance :
    kernelStepRaw pinConvAtState = .result (.accepted .conversionConfirmed) := rfl

/-- PIN: `RM017T_conversion_confirmed` consumed at that run. -/
def pin_RM017T_conv :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  RM017T_conversion_confirmed natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    pinConvAtState rfl _ _ _ _ rfl (pinBetaApp natEnvU 1) pinBetaReductTy
    pin_convAt_acceptance

/-- PIN (δ): a real `convAt` acceptance of the definition constant against
    its body on `pinDefEnvU` (the δ-redex `Sort 0` at ref 4 unfolding to
    `Sort 0`), run by `rfl`. -/
def pinConvAtDeltaState : RawState where
  ambient := ⟨pinDefEnvU, 1, []⟩
  task := .convAt (.sort (.succ (.succ .zero))) (.const 4 []) (.sort .zero)
  budget := 2

theorem pin_convAt_delta_acceptance :
    kernelStepRaw pinConvAtDeltaState = .result (.accepted .conversionConfirmed) := rfl

end Rcic.Machine

#print axioms Rcic.Machine.RM012T_lookupLocal_hasTy
#print axioms Rcic.Machine.RM013T_lookupDeclaration_hasTy
#print axioms Rcic.Machine.RM015T_infer_sound
#print axioms Rcic.Machine.RM016T_check_sound
#print axioms Rcic.Machine.RM016T_run_check_sound
#print axioms Rcic.Machine.RM017T_conversion_confirmed
#print axioms Rcic.Machine.pinTypedRefusalState
#print axioms Rcic.Machine.pin_refusal_typedRun_sortSelf
#print axioms Rcic.Machine.pinLookupLocalState
#print axioms Rcic.Machine.pin_RM012T_lookupLocal_acceptance
#print axioms Rcic.Machine.pin_RM012T_lookupLocal
#print axioms Rcic.Machine.pinLookupDeclState
#print axioms Rcic.Machine.pin_RM013T_lookupDeclaration_acceptance
#print axioms Rcic.Machine.pin_RM013T_lookupDeclaration
#print axioms Rcic.Machine.pinTypedCheckZeroState
#print axioms Rcic.Machine.pin_typedRun_check_zero
#print axioms Rcic.Machine.pin_RM016T_check_zero
#print axioms Rcic.Machine.pin_RM016T_run_check_zero
#print axioms Rcic.Machine.pinTypedInferAppState
#print axioms Rcic.Machine.pin_typedRun_infer_succ_zero
#print axioms Rcic.Machine.pin_RM015T_succ_zero
#print axioms Rcic.Machine.pinWhnfAtState
#print axioms Rcic.Machine.pin_whnfAt_acceptance
#print axioms Rcic.Machine.pin_whnfAt_conv
#print axioms Rcic.Machine.pinConvAtState
#print axioms Rcic.Machine.pin_convAt_acceptance
#print axioms Rcic.Machine.pin_RM017T_conv
#print axioms Rcic.Machine.pinConvAtDeltaState
#print axioms Rcic.Machine.pin_convAt_delta_acceptance
