import rcic.RcicMachineSoundTyped
import rcic.RcicTypedEnvEntry

/-!
# T1-T segment (i) — the TERM-LEVEL typed certifier wrappers

The type-LEVEL checkers (`RcicTypedScopeCheck` / `RcicTypedConv`) and the typed
result rows (`RcicMachineSoundTyped`) are on main; this module adds the two
term-level certifier wrappers that ride them, per the T1-T hard order:

* `tyConvT_subst0_of_envWfT` — the one NEW judgment-side tool: a `TyConvT`
  chain under head substitution (the chain side of `convT_subst0_of_envWfT`);
  each `.of` step rides the typed substitution at its own sort, because
  `instantiate0 v (.sort u)` is `(.sort u)` definitionally. This is the piece
  that un-walls the known pain point — the app-spine congruence landing
  `instantiate0 v B` conversions (the β head conversion's landing type is the
  λ's OWN codomain `B_lam`, while the spine asks at the inversion's
  `instantiate0 arg B1`; the codomain chain `hBcod` bridges the two once
  lifted through the substitution).
* `machineZetaConvT` / `machineDeltaConvT` / `machineBetaConvT` — the three
  typed head CONVERSIONS at a fixed type `S` (the conv counterparts of
  `machineZetaStepT` / `machineDeltaStepT` / `machineBetaStepT`): zeta is
  direct (`ConvT.zeta` carries its own premises), delta through
  `envWfT_bodyTyped`, beta through the Π row, the domain conversion collapsed
  at the domain's own sort, and the codomain chain lifted by the new lemma.
* `convTFoldAppsHeadT` — the conv-side spine transport (the counterpart of
  `hasTyTFoldAppsHeadT`): a head conversion closes over the spine by
  app-inversion, `ConvT.app` congruence with a reflexive argument leg, and
  `convT_of_tyConv` landing the inversion's chain at `S`.
* `machineRed_toConvT` — the typed `MachineRed → ConvT` map, arm by arm
  (the conv counterpart of `machineRedSRT`; `machineRed_toConv` in
  `RcicMachine` is the SHAPE, the typing premises come from the spine via the
  two transports, the middle typing via `machineRedSRT`'s own step lemmas).
* ITEM 1, whnf of a TERM at its type: `whnfCert_convT` runs the machine's
  `whnfCert`; on acceptance the payload IS the `MachineRed` chain (extraction
  is `c.2`, proved by the certifier's own return type — nothing assumed), and
  the chain maps to `Nonempty (ConvT E n Γ e w T)` at the source's type.
  `RM014T_whnf_conv` is the same through `kernelStepRaw`'s whnfAt arm,
  mirroring `RM014T_whnf_typed`'s unfolding.
* ITEM 2, conversion of two TERMS at a type: `convCert_convT` runs the
  machine's `convCert`; on acceptance `convCert_chains` extracts both sides'
  `MachineRed` chains to a common reduct (already on main), each maps through
  `machineRed_toConvT`, and the join is `ConvT.trans` of the left chain and
  the symm of the right — no `ParRedStar`, no confluence, no legacy join.

Premise disclosure (the degeneracy tooth): every statement below takes only
`EnvWfT`, `hW.InScope`, `CtxWfT`, and the wrapper's own subject matter (the
certifier acceptance equation, the typings). No premise names a row,
`TypedRowsWf`, `AnnEnvA`, `EnvSemA` or `IotaSRA`; no statement names either
legacy judgment type (typing or conversion) as a bare token — whole-file
grep 0 on word boundaries; the certifier's
conversion output is quantified existentially, the whnf output is the
`MachineRed` sigma the certifier itself returns). Machine-interface surface,
kept minimal and documented: `MachineRed` appears only as `whnfCert`'s own
result type (`whnfCert_convT`'s premise, `pinWhnfOut`); `whnfCert`,
`convCert`, `kernelStepRaw`, `RawState` are the machine entry points the
wrappers are about. The rows enter only inside `machineBetaConvT`'s proof,
through the scope bridge.

The conclusions are `Nonempty`-valued where the scope rows supply
`Nonempty` (the Π row's codomain), matching `RcicMachineSoundTyped`.

Consumption pins, no supply parameter: `pin_whnfCert_conv` (whnf-at-type of a
real β-redex on `natEnvU`, the certifier's output witness `pinWhnfOut` named
and the acceptance run by `rfl`) and `pin_convCert_conv` (conv-at-type
acceptance of that redex against its reduct at the same type, riding
`pin_RM017T_convCert`/`pinConvC`; `convCert` needs fuel ≥ 2 for a one-step
redex because it passes fuel-1 to `whnfCert`).

Segment (i) only: no typed machine arms, no acceptance rows (segments ii/iii).
closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## the chain-lifting lemma (the pain-point un-wall) -/

/-- a type-conversion chain under head substitution — the chain side of
    `convT_subst0_of_envWfT`: each `.of` step rides the typed substitution at
    its own sort (`instantiate0 v (.sort u)` is `(.sort u)` definitionally,
    so `convT_subst0_of_envWfT`'s output is already at `(.sort u)`). -/
def tyConvT_subst0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {v t : Expr Nat}
    {n : Nat} {Γ : LCtx} (hv : HasTyT E n Γ v t) :
    {A B : Expr Nat}→ TyConvT E n (LocalDecl.assumption t :: Γ) A B →
    TyConvT E n Γ (instantiate0 v A) (instantiate0 v B)
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ u c =>
      .of _ _ _ u (convT_subst0_of_envWfT hW c hv)
  | _, _, .trans _ _ _ _ c₁ c₂ =>
      .trans _ _ _ _ (tyConvT_subst0_of_envWfT hW hv c₁)
        (tyConvT_subst0_of_envWfT hW hv c₂)

end Rcic.Declarative

namespace Rcic.Machine

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## the three typed head conversions -/

/-- one typed zeta head conversion at the FIXED type `S` — direct: the letE
    inversion supplies every premise `ConvT.zeta` asks for, and the inversion's
    own chain lands `S`. -/
theorem machineZetaConvT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A value body : Expr Nat) :
    (S : Expr Nat)→ HasTyT E n Γ (.letE A value body) S →
    Nonempty (ConvT E n Γ (.letE A value body) (instantiate0 value body) S) := by
  intro S h
  obtain ⟨u, B_let, hAty, hv, hb, hcv⟩ := hasTyTInv_letE h rfl
  exact ⟨convT_of_tyConv
    (ConvT.zeta Γ A value body B_let u hAty hv hb) hcv⟩

/-- one typed delta head conversion at the FIXED type `S` — the conv
    counterpart of `machineDeltaStepT`: const inversion plus
    `envWfT_bodyTyped`, `ConvT.delta` at the stored type, the inversion's own
    chain landing `S`. -/
theorem machineDeltaConvT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat)
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    (S : Expr Nat)→ HasTyT E n Γ (.const r ls) S →
    Nonempty (ConvT E n Γ (.const r ls) (instantiateLevels ls b) S) := by
  intro S h
  obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const h rfl
  have hmeq : some m = some m' := hres.symm.trans hres'
  injection hmeq with hmeq'
  subst hmeq'
  exact ⟨convT_of_tyConv
    (ConvT.delta Γ r ls m b hres hbody htr hlen hwf
      (envWfT_bodyTyped hW hres hbody hlen)) hcv⟩

/-- one typed beta head conversion at the FIXED type `S` — the conv
    counterpart of `machineBetaStepT`: app/lam inversion, the Π row in scope
    for the domain conversion (collapsed at the domain's own sort) and the
    codomain chain, `ConvT.beta` at the λ's OWN codomain, the codomain chain
    lifted through the argument's substitution (`tyConvT_subst0_of_envWfT`)
    to bridge `instantiate0 arg B_lam` to `instantiate0 arg B1`, and the
    inversion's chain landing `S`. -/
theorem machineBetaConvT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A body arg : Expr Nat) :
    (S : Expr Nat)→ HasTyT E n Γ (.app (.lam A body) arg) S →
    Nonempty (ConvT E n Γ (.app (.lam A body) arg) (instantiate0 arg body) S) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  intro S h
  have hrows := typedRowsWf_of_envWfT_semPrefix hW hP n
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
  obtain ⟨cdom⟩ := convT_of_tyConvT_sort C hn hΓ hA0ty hBdom
  have ha' := HasTyT.conv _ _ _ _ u ha (ConvT.symm _ _ _ _ cdom)
  exact ⟨convT_of_tyConv
    (ConvT.beta Γ A body arg B_lam u hA0ty hbody ha')
    (TyConvT.trans Γ _ _ _
      (tyConvT_subst0_of_envWfT hW ha' hBcod) hcv)⟩

/-! ## the conv-side spine transport -/

/-- a head conversion closes over the spine — the conv counterpart of
    `hasTyTFoldAppsHeadT`: app-inversion reads the Π type, `ConvT.app`
    congruence takes the head conversion with a reflexive argument leg, and
    `convT_of_tyConv` lands the inversion's chain at the asked type. -/
theorem convTFoldAppsHeadT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f f' : Expr Nat}
    (hstep : (S : Expr Nat)→ HasTyT E n Γ f S → Nonempty (ConvT E n Γ f f' S)) :
    (xs : List (Expr Nat))→ {T : Expr Nat}→
    HasTyT E n Γ (foldApps f xs) T →
    Nonempty (ConvT E n Γ (foldApps f xs) (foldApps f' xs) T)
  | [], _, h => hstep _ h
  | x :: xs, _, h =>
      convTFoldAppsHeadT (f := .app f x) (f' := .app f' x)
        (fun S hS => by
          obtain ⟨A0, B0, hf, ha, hcv⟩ := hasTyTInv_app hS rfl
          exact (hstep (.pi A0 B0) hf).elim fun hcvf =>
            ⟨convT_of_tyConv
              (ConvT.app Γ f f' x x A0 B0 hcvf (.refl Γ x A0 ha)) hcv⟩) xs h

/-! ## the typed MachineRed → ConvT map -/

/-- `MachineRed` carries a `ConvT` chain at the source's type — the conv
    counterpart of `machineRedSRT`, arm by arm (`machineRed_toConv` in
    `RcicMachine` is the shape): each head step's conversion closes over the
    spine by `convTFoldAppsHeadT`, the middle is typed by the spine transport
    over the STEP lemmas on main, and the tail rides the induction. -/
theorem machineRed_toConvT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat}→ MachineRed E n Γ a b → HasTyT E n Γ a T →
    Nonempty (ConvT E n Γ a b T) := by
  intro a b T k h
  induction k with
  | refl e => exact ⟨.refl Γ e T h⟩
  | headBeta A body arg rest k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineBetaStepT hW hP hΓ A body arg) rest h
      obtain ⟨c₁⟩ := convTFoldAppsHeadT (machineBetaConvT hW hP hΓ A body arg) rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩
  | headZeta A value body rest k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineZetaStepT hW hP hΓ A value body) rest h
      obtain ⟨c₁⟩ := convTFoldAppsHeadT (machineZetaConvT A value body) rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩
  | headDelta r ls m b rest hres hbody htr k' ih =>
      obtain ⟨hmid⟩ :=
        hasTyTFoldAppsHeadT (machineDeltaStepT hW r ls m b hres hbody) rest h
      obtain ⟨c₁⟩ :=
        convTFoldAppsHeadT (machineDeltaConvT hW r ls m b hres hbody htr) rest h
      obtain ⟨c₂⟩ := ih hmid
      exact ⟨.trans Γ _ _ _ T c₁ c₂⟩

/-! ## ITEM 1 — whnf of a term at its type -/

/-- the whnf certifier's acceptance carries a `ConvT` chain from the term to
    its whnf at the term's own type. The extraction is proved, not assumed:
    the acceptance equation is read (`Cert.ok`'s payload must be `c` itself),
    the payload IS the `MachineRed` chain (`c.2`, the certifier's own return
    type), and `machineRed_toConvT` maps it. `MachineRed` appears only as
    `whnfCert`'s result type — the minimal machine surface. -/
theorem whnfCert_convT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (fuel : Nat) (e T : Expr Nat)
    (c : Σ' (w : Expr Nat), MachineRed E n Γ e w)
    (hacc : whnfCert E n fuel Γ e = .ok c)
    (hty : HasTyT E n Γ e T) :
    Nonempty (ConvT E n Γ e c.1 T) := by
  cases hb : whnfCert E n fuel Γ e with
  | ok c' =>
      rw [hb] at hacc
      injection hacc with hc'
      subst hc'
      exact machineRed_toConvT hW hP hΓ c'.2 hty
  | no msg =>
      rw [hb] at hacc
      nomatch hacc

/-- the same through `kernelStepRaw`'s whnfAt arm — the conv counterpart of
    `RM014T_whnf_typed`: the `MachineRed` is extracted by unfolding the arm
    exactly as that theorem does; no machine data type is named in the
    statement. -/
theorem RM014T_whnf_conv {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A e w T : Expr Nat) (htask : s.task = .whnfAt A e)
    (hty : HasTyT E n Γ e T)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    Nonempty (ConvT E n Γ e w T) := by
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
          exact machineRed_toConvT hW hP hΓ kred hty
      · nomatch hacc

/-! ## ITEM 2 — conversion of two terms at a type -/

/-- the conversion certifier's acceptance carries a `ConvT` chain between the
    two terms at their common type. `convCert_chains` extracts both sides'
    `ParRedStar` chains to a common reduct (with their `starLevelsIn`
    witnesses) by replaying the certifier's own cases; each maps through
    `parRedStarConvT`, and the join is trans of the left chain and the symm
    of the right. The certifier's conversion output is quantified
    existentially, so the legacy conversion type is not named. -/
theorem convCert_convT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (fuel : Nat) (A l r T : Expr Nat)
    (htyl : HasTyT E n Γ l T) (htyr : HasTyT E n Γ r T)
    (hacc : ∃ c, convCert E n fuel Γ A l r = .ok c) :
    Nonempty (ConvT E n Γ l r T) := by
  obtain ⟨c, hc⟩ := hacc
  obtain ⟨d, k1, k2, hl1, hl2⟩ := convCert_chains fuel Γ A l r c hc
  obtain ⟨c1⟩ := parRedStarConvT hW hP hΓ k1 htyl hl1
  obtain ⟨c2⟩ := parRedStarConvT hW hP hΓ k2 htyr hl2
  exact ⟨.trans Γ l d r T c1 (.symm Γ r d T c2)⟩

/-! ## consumption pins (real machine runs on `natEnvU`, no supply parameter) -/

/-- the whnf certifier's own output witness for the beta redex — `pinConvKl`
    is the head-beta chain, `pinBetaReduct` the whnf. -/
def pinWhnfOut : Σ' (w : Expr Nat), MachineRed natEnvU 1 [] pinBetaRedex w :=
  ⟨pinBetaReduct, pinConvKl⟩

/-- PIN: a real `whnfCert` acceptance — the certifier's own output witness
    named, the run by `rfl`. -/
theorem pin_whnfCert_acceptance :
    whnfCert natEnvU 1 2 [] pinBetaRedex = .ok pinWhnfOut := rfl

/-- the reduct's typing at the same type, through the typed entry only:
    substituting `Sort 0` into the body variable's typing under the λ's
    binder. -/
def pinBetaReductTy :
    HasTyT natEnvU 1 [] pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) :=
  hasTyT_subst0_of_envWfT natEnvUWfT
    (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0
      (.sort (.succ .zero)) rfl)
    (HasTyT.sort [] .zero)

/-- PIN (dispatch): ITEM 1 consumed at a real β-redex on `natEnvU` —
    whnf-at-type through the acceptance above and the `pinBetaApp natEnvU 1`
    typing. -/
theorem pin_whnfCert_conv :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  whnfCert_convT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil 2 pinBetaRedex
    (instantiate0 (.sort .zero) (.sort (.succ .zero)))
    pinWhnfOut pin_whnfCert_acceptance (pinBetaApp natEnvU 1)

/-- PIN (dispatch): ITEM 2 consumed — a conv-at-type acceptance of the redex
    against its reduct at the same type, riding the named-witness `rfl`
    acceptance `pin_RM017T_convCert` (fuel 2: `convCert` passes fuel-1 to
    `whnfCert`). -/
theorem pin_convCert_conv :
    Nonempty (ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  convCert_convT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil 2
    (.sort (.succ (.succ .zero))) pinBetaRedex pinBetaReduct
    (instantiate0 (.sort .zero) (.sort (.succ .zero)))
    (pinBetaApp natEnvU 1) pinBetaReductTy pin_RM017T_convCert

end Rcic.Machine

#print axioms Rcic.Declarative.tyConvT_subst0_of_envWfT
#print axioms Rcic.Machine.machineZetaConvT
#print axioms Rcic.Machine.machineDeltaConvT
#print axioms Rcic.Machine.machineBetaConvT
#print axioms Rcic.Machine.convTFoldAppsHeadT
#print axioms Rcic.Machine.machineRed_toConvT
#print axioms Rcic.Machine.whnfCert_convT
#print axioms Rcic.Machine.RM014T_whnf_conv
#print axioms Rcic.Machine.convCert_convT
#print axioms Rcic.Machine.pinWhnfOut
#print axioms Rcic.Machine.pin_whnfCert_acceptance
#print axioms Rcic.Machine.pinBetaReductTy
#print axioms Rcic.Machine.pin_whnfCert_conv
#print axioms Rcic.Machine.pin_convCert_conv
