import rcic.RcicNativePiModelIdeal
import rcic.RcicNativePiModelLR
import rcic.RcicNativePiModelLRCases
import rcic.RcicNativePiModelIrr
import rcic.RcicNativePiModelLRTerm
import rcic.RcicNativePiModelK
import rcic.RcicNativePiModelTermIrr
import rcic.RcicNativePiModelFundCases
import rcic.RcicIotaShape
import rcic.RcicIotaLegacyBridge
import rcic.RcicWitnessFuelStable

/-!
# RcicNativePiModelDeltaIota — Concrete δ and ι Semantics in the Lower-Ideal Model

This module extends the lower-ideal approximation model (`RcicNativePiModelIdeal` /
`RcicNativePiModelLR` / `RcicNativePiModelLRCases` / `RcicNativePiModelIrr` /
`RcicNativePiModelLRTerm`, #7632/#7635/#7639/#7645) with **concrete compositional δ (definition)
and ι (recursor) semantics for admitted families**:

1. **Admitted Obstructions on Raw `ApproxI` (§1)**:
   - `delta_unsound_raw_approxI`: raw `ApproxI` interprets every `.const r ls` as `.spine r []`
     (`approxI_const_inv`), refuting `SemEqI` on any definition `.const r ls ≡ .sort l` (such as
     `defSortEnvWfT` where `ConvT.delta` and `WhStep.delta` hold).
   - `iota_unsound_raw_approxI_sort` / `wZero_unsound_raw_approxI`: raw `ApproxI` interprets every
     recursor application `foldApps (.const recRef ls) args` as `.bot` or `.spine recRef ...`,
     refuting `SemEqI` on `wZero` / `wZeroS` in `natEnv` (`iotaRhsOf wZero = .const 1 []` has
     approximation `.spine 1 []`, which `iotaLhsOf wZero` at head `recRef = 3` lacks).

2. **Concrete δ/ι Lower-Ideal Model `ApproxDI E ρ e c` (§2)**:
   - Reuses `CptI`, `EnvI`, `EnvI.bot`, and `demand` from `RcicNativePiModelIdeal` /
     `RcicNativePiModelLR`, with identical clauses for `.bvar`, `.sort`, `.pi`, `.lam`, `.app`,
     `.appSpine`, `.letE`, and `.lit`.
   - Partitions `.const r ls` into three mutually exclusive, `ρ`-independent cases determined
     statically by `(E, r)`:
     * `ApproxDI.const` (`RigidConst E r`): rigid constants (constructors, inductive families,
       axioms, theorems/opaques without transparent body) denote `.spine r []`.
     * `ApproxDI.delta` (`DeltaConst E r m b`): definitions with admitted body `b` inherit every
       compact `c` approximating `instantiateLevels ls b` at `EnvI.bot`.
     * `ApproxDI.recursor` (`w : IotaWitnessS E`): recursors denote curried bounded step
       functions `curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c` for every
       compact `c` approximating the admitted computation schema `instantiateLevels ls w.schema`
       under the pushed argument demands `EnvI.pushArgs ((us_pre ++ us_fields).map demand) EnvI.bot`.
   - At `emptyEnv`, `ApproxDI emptyEnv ρ e c ↔ ApproxI ρ e c` (`approxDI_emptyEnv_iff`).

3. **Full Lower-Ideal Algebra on `ApproxDI` (§3–§4)**:
   - Monotonicity (`approxDI_mono_env`), closed-term environment invariance
     (`approxDI_closedAt_env`), universe-level invariance (`approxDI_instantiateLevels_swap`,
     `approxDI_instantiateLevels_iff`, `semEqDI_const_levels` / `ConvT.consts` soundness),
     finite-demand factorization (`approxDI_factor`), two-way lifting
     (`approxDI_lift_intro`/`_elim`, `approxDI_liftN_intro`/`_elim`), and two-way substitution
     (`approxDI_subst_intro`/`_elim`, `approxDI_subst_iff`, `approxDI_subst_demand_iff`).
   - Iterated prefix substitution (`EnvI.pushArgs`, `ApproxArgsDemand`,
     `approxDI_instPrefix_demand_iff`, `approxDI_instPrefix_closed_iff`).
   - Unconditional β-soundness (`approxDI_beta`), ζ-soundness (`approxDI_zeta`), and literal
     soundness (`approxDI_lit`).

4. **Soundness of δ (`ConvT.delta` and `WhStep.delta`) (§5)**:
   - `semEqDI_delta_bot`: `SemEqDI E EnvI.bot (.const r ls) (instantiateLevels ls b)` for every
     `DeltaConst E r m b`.
   - `semEqDI_delta`: `SemEqDI E ρ (.const r ls) (instantiateLevels ls b)` for every `ρ : EnvI`
     when `exprClosedAt 0 b = true`.
   - `envWfT_member_body_closed`: in any `EnvWfT E`, every member `m` with `m.body = some b`
     satisfies `DeltaConst E r m b ∧ exprClosedAt 0 b = true`.
   - `semEqDI_of_convT_delta` and `semEqDI_of_whStep_delta`: full `SemEqDI E ρ` soundness of
     `ConvT.delta` and `WhStep.delta`.

5. **Branch Uniqueness, `IotaDetT`/`IotaDetU`, and Legacy Open Schema (§6)**:
   - `iotaWitnessS_same_branch`: any two `w₁, w₂ : IotaWitnessS E` with `w₁.recRef = w₂.recRef`
     and `w₁.ctorRef = w₂.ctorRef` agree on `nparams`, `nindices`, `nMinors`, `ctorIdx`,
     `preMajor.length`, `fields.length`, `shapes`, and `schema` (via `fieldShapesFuel_agree` and
     `iotaOpenRhs_agree`).
   - `iotaDetT`: `DerivedIotaT E lhs rhs₁ → DerivedIotaT E lhs rhs₂ → rhs₁ = rhs₂`.
   - `iotaDetU_of_envWfT`: `EnvWfT E → IotaDetU E` (discharging the `IotaDetU` front of
     `RcicNativeValleyFronts` across both `.ofU` and `.ofUS` arms at every `EnvWfT E`).
   - `legacySchemaOf` and `iotaRhsOf_eq_instPrefix_legacySchema`: every legacy `w : IotaWitness E`
     satisfies `instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls (legacySchemaOf w)) =
     iotaRhsOf w` unconditionally.

6. **Soundness of ι (`DerivedIotaT`, `DerivedIota`, `DerivedIotaU`, `ConvT.iota`, `WhStep.iota`) (§7)**:
   - `approxDI_iotaS`: `SemEqDI E ρ (iotaLhsOfS w) (iotaRhsOfS w)` **unconditionally** for every
     `E : ResolvedEnv`, `w : IotaWitnessS E`, and `ρ : EnvI`.
   - `approxDI_iotaT`: `DerivedIotaT E lhs rhs → SemEqDI E ρ lhs rhs`.
   - `approxDI_iota_of_envWfT`, `approxDI_iotaU_of_envWfT`, `semEqDI_of_convT_iota`: full
     `SemEqDI E ρ` soundness of legacy `DerivedIota`, union `DerivedIotaU`, `ConvT.iota`, and
     `WhStep.iota` at every `EnvWfT E`.

7. **Congruences, `WhStep`/`WhRed` Soundness, Model Π-Injectivity, and Non-Vacuity Pins (§8)**:
   - Full `SemEqDI` congruences (`semEqDI_app`, `semEqDI_lam`, `semEqDI_pi`, `semEqDI_letE`,
     `semEqDI_sorts`, `semEqDI_const_levels`), `semEqDI_whStep`, `semEqDI_whRed`.
   - Model Π-injectivity (`semEqDI_pi_inj`) and Π/Sort disjointness (`semEqDI_pi_sort_disjoint`).
   - Non-vacuity pins across `defSortEnv`, `natEnv` (`wZero`, `wZeroS`, `wSuccS`), `listEnv`
     (`wNilS`, `wConsS`), `vecEnv` (`wVconsS`), and `natEnvU` (`wSuccU1`, `pin_iotaDetU_natEnvU`).

8. **Discharging `WhDet`, `WhApproxInvCore`/`WhApproxInv`, and Spine-Freedom `(O3)` (`RcicNativePiModelLRCases`, `RcicNativePiModelIrr`, `RcicNativePiModelLRTerm`) (§9)**:
   - `whDet_of_envWfT`: `EnvWfT E → WhDet E` (discharging the weak-head determinism hypothesis of
     `RcicNativePiModelLRCases` and `RcicNativePiModelLRTerm` via `iotaDetU_of_envWfT`,
     `not_deltaConst_of_recursor`, and `not_whStep_recursor_prefix`).
   - Refutation teeth on raw `ApproxI`: `not_whApproxInvCore_defSortEnv`,
     `not_whApproxInv_defSortEnv`, `not_whApproxInvCore_natEnv`, `not_whApproxInv_natEnv`, and
     `not_noSpine_foldApps_const_approxI`.
   - Unconditional discharge of `WhApproxInvCoreDI` and `WhApproxInvDI` in `ApproxDI`
     (`whApproxInvCoreDI_of_envWfT`, `whApproxInvDI_of_envWfT`, `approxDI_whRed_back`,
     `approxDI_sort_of_whRed`), and unconditional spine-freedom (`NoSpine`) of recursor constants
     and partial applications up to `preMajor.length` (`noSpine_recursor_prefix_approxDI`,
     `noSpine_recursor_elim_approxDI`), together with projected equality `PEqDI` and K/ι reduction
     (`pEqDI_delta`, `pEqDI_iotaS`, `pEqDI_iotaU_of_envWfT`, `pEqDI_k_of_domTyped_iotaS`).

9. **Logical-Relation Consumers over `ApproxDI` without External `WhDet` or `WhApproxInv` Hypotheses (§10)**:
   - `fundamentalLRINT_DI_of_fundamentalTermDI`, `piRow_of_fundamentalLRINT_DI`,
     `adequacyPiDI_of_fundamentalTermDI`, `fundTermDI_sorts`, `fundConvDI_of_whStep`,
     `fundConvDI_of_whRed`, `fundConvDI_delta`, `fundConvDI_iota`, `lrTypeIN_delta_DI`, and
     `lrTypeIN_iota_DI`.

10. **Two-Way Lift-0 Invariance and Discharging `RcicNativePiModelK`'s Open `(O3)` Remainders Under a Binder (§11)**:
    - `approxDI_lift0_one_iff`, `denDI_lift0_one_eq`, `semEqDI_lift0_one_iff`, `semEqDI_lam_congrK`.
    - `EtaSoundAtDI`, `LamIrrAtDI`, `LamIotaAtDI`, `IotaClauseUnderDI`, `iotaClauseUnderDI_iff_semEqDI`.
    - Unconditional discharge of `IotaClauseUnderDI` and `LamIotaAtDI` for every `w : IotaWitnessS E`
      (`iotaClauseUnderDI_of_iotaWitnessS`, `lamIotaAtDI_of_iotaWitnessS`) and for every
      `DerivedIotaU` at `EnvWfT E` (`iotaClauseUnderDI_of_derivedIotaU`,
      `lamIotaAtDI_of_derivedIotaU`).
    - Unconditional discharge of `NoSpine` under a binder (`noSpine_lift0_recursor_elim_approxDI`),
      `lamIrrAtDI_of_domTyped`, `lamIrrAtDI_of_domTyped_recursor`, and `pEqDI_etaK_of_eta_dom_iotaS`.

11. **Admitted Obstructions on Un-Restricted Π-Demands and Untyped `TypeSoundness`, and the Repaired `BotPiCpt` / `LRTypeINBiDI` Layer (§12)**:
    - Unconditional refutation of `FundamentalLRI`, `FundamentalLRIN`, `FundamentalLRINT`,
      `FundamentalTermI`, `FundamentalLRINT_DI`, and `FundamentalTermDI` for every `E : ResolvedEnv`
      and `n : Nat` at `idPiProp = .pi (.sort .zero) (.bvar 0)` and
      `idPiPropSortStep = .pi .bot [([.sort], .sort)]` (`not_fundamentalLRI`, `not_fundamentalLRIN`,
      `not_fundamentalLRINT`, `not_fundamentalTermI`, `not_fundamentalLRINT_DI`,
      `not_fundamentalTermDI`).
    - Unconditional refutation of `TypeSoundnessI` and `TypeSoundnessDI` for every `E : ResolvedEnv`
      and `n : Nat`, both via `ConvT.zetaLocal` (`not_typeSoundnessI`, `not_typeSoundnessDI`) and on
      closed types in `Γ = []` via `ConvT.irr` under `ConvT.pi` (`closedIrrPi_conv`,
      `not_semEqI_closedIrrPi`, `not_semEqDI_closedIrrPi`).
    - Repaired `BotDemand` / `BotPiCpt` / `LRTypeINBiDI` / `FundamentalLRINBotDI` layer:
      * `approxDI_of_lrTypeIN_botPiCpt`: on `BotPiCpt` compacts at `EnvWfT E`, `LRTypeIN E n Γ A B c`
        implies `ApproxDI E EnvI.bot A c ∧ ApproxDI E EnvI.bot B c` without `TypeSoundness`.
      * Positive repair of both counterexamples (`lrTypeINBiDI_idPiProp`, `lrTypeINBiDI_closedIrrPi`).
      * Unconditional cases of `LRTypeINBiDI` (`bvar`, `sort`, `sorts`, `rigidConst`, `rigidConsts`,
        `pi`, `symm`, `trans`, `tyConv`, `beta`, `zeta`, `delta`, `iota`, `lit`, `letE`, `deltaConst`)
        and `fundamentalLRINBotDI_of_links` / `piRow_of_fundamentalLRINBotDI` without `WhDet E` or
        `TypeSoundnessDI E n`.

12. **Discharging `RcicNativePiModelK` Interfaces & Unconditional Refutations of `IrrCaseT` and `EtaCaseT` (`RcicNativePiModelTermIrr`, Batch 179) (§13)**:
    - Refutation of raw `PiModelKAudit.IotaClauseUnder` and `PiModelKAudit.IotaSoundAt` on `wZero` in
      `natEnv` (`not_iotaClauseUnder_wZero`, `not_iotaSoundAt_wZero`), and concrete `ApproxDI`
      discharge of `MajorStableDI` and `IotaSoundAtDI` (`iotaSoundAtDI_of_iotaWitnessS`,
      `iotaSoundAtDI_of_derivedIotaU`, `majorStableDI_of_domTyped`,
      `majorStableDI_of_domTyped_recursor`, `pEqDI_K`, `pEqDI_K_of_domTyped`).
    - Positive η-calculus on λ-abstractions and δ-definitions (`approxDI_eta_lam_intro`,
      `semEqI_eta_lam`, `semEqDI_eta_lam`, `etaSoundAt_lam`, `etaSoundAtDI_lam`,
      `semEqDI_eta_delta_lam`, `etaSoundAtDI_delta_lam`, alongside `eta_unsound_bot_DI`).
    - **Unconditional refutations of `PiModelTermAudit.IrrCaseT` and `PiModelTermAudit.EtaCaseT`**
      (and `IrrCaseT_DI`, `EtaCaseT_DI`) in `Γ = []` for **every** `E : ResolvedEnv` and `n : Nat`
      (removing the `pi_member` hypothesis of `RcicNativePiModelTermIrr.not_irrCaseT_of_pi_member`
      and refuting `EtaCaseT`, which `RcicNativePiModelTermIrr` left open):
      `not_irrCaseT`, `not_irrCaseT_DI`, `not_etaCaseT`, `not_etaCaseT_DI`.

13. **Weakening, Substitution, and `TyConvT`-Chain Context Conversion for `WhStep`/`WhRed`, `HasTyT`/`ConvT`/`TyConvT`, `LRTypeIN` on `BotPiCpt`, and `LRTypeINBiDI` (§14)**:
    - Unconditional `WhStep.iota` lifting and substitution (`whStep_iota_lift`,
      `whStep_iota_instantiate`) and `WhStep`/`WhRed` commutation with `lift` and `instantiate`
      at `EnvClosed E` / `EnvWfT E` (`whStep_lift_of_envClosed`, `whRed_lift_of_envClosed`,
      `whStep_instantiate_of_envClosed`, `whRed_instantiate_of_envClosed`,
      `whRed_instantiate_sort_of_envClosed`, `whRed_instantiate_pi_of_envClosed`).
    - Context conversion along a `TyConvT E n Γ A₁ A₂` chain (`tyConvT_ctx`,
      `ctxConvT_append_same`, `hasTyT_tyConvT_assumption`, `convT_tyConvT_assumption`,
      `tyConvT_tyConvT_assumption`, `hasTyT_tyConvT_head`, `convT_tyConvT_head`,
      `tyConvT_tyConvT_head`, and `codomain_transport_of_tyConvT`), directly discharging the
      codomain-typing-in-moved-context step.
    - Weakening and substitution stability of `LRTypeIN` on `BotPiCpt` compacts and `LRTypeINBiDI`
      (`lrTypeIN_weaken_botPiCpt`, `lrTypeIN_weaken0_botPiCpt`, `lrTypeINBiDI_weaken0`,
      `lrTypeIN_subst_botPiCpt`, `lrTypeIN_subst0_botPiCpt`, `lrTypeIN_substLet_botPiCpt`,
      `lrTypeIN_substLet0_botPiCpt`).

`closure_claim = 0`. No `sorry`, no new axiom, no structure or hypothesis predicate assuming soundness.
-/

namespace Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-! ## §1. Admitted Obstructions on Raw `ApproxI` (`RcicNativePiModelIdeal`) -/

/-- Raw `ApproxI` refutes `SemEqI ρ (.const r ls) (.sort l)` for every constant `r` and sort `l`,
    because `ApproxI.const` assigns only `.bot` and `.spine r []` to `.const r ls`. -/
theorem delta_unsound_raw_approxI (ρ : EnvI) (r : Nat) (ls : List Level) (l : Level) :
    ¬ SemEqI ρ (.const r ls) (.sort l) := by
  intro h
  have hsort : ApproxI ρ (.const r ls) .sort := (h .sort).mpr (.sort ρ l)
  rcases approxI_const_inv hsort with h0 | h0 <;> cases h0

/-- Concrete well-formed environment with a transparent definition `const 0 : Sort 1 := Sort 0`. -/
def defSortEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩

/-- `defSortEnv` is well-formed in `EnvWfT`. -/
def defSortEnvWfT : EnvWfT defSortEnv :=
  .definition emptyEnv 0 (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
    .empty rfl (.sort [] (.succ .zero)) (.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- In `defSortEnv`, `ConvT.delta` and `WhStep.delta` step `.const 0 []` to `.sort .zero`,
    yet raw `SemEqI` refutes their semantic equality. -/
theorem defSortEnv_delta_step_and_raw_refuted (n : Nat) (ρ : EnvI) :
    Nonempty (ConvT defSortEnv n [] (.const 0 []) (.sort .zero) (.sort (.succ .zero))) ∧
      WhStep defSortEnv (.const 0 []) (.sort .zero) ∧
      ¬ SemEqI ρ (.const 0 []) (.sort .zero) :=
  ⟨⟨.delta [] 0 [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ (.sort .zero)
      rfl rfl rfl rfl rfl (.sort [] .zero)⟩,
   .delta (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl,
   delta_unsound_raw_approxI ρ 0 [] .zero⟩

/-- Raw `ApproxI` on any application spine headed by `.const r ls` yields only `.bot` or
    `.spine r args`. -/
theorem approxI_foldApps_const_inv {ρ : EnvI} {r : Nat} :
    (xs : List (Expr Nat)) → {f : Expr Nat} → {c : CptI} →
    (∀ d, ApproxI ρ f d → d = .bot ∨ ∃ args, d = .spine r args) →
    ApproxI ρ (foldApps f xs) c → c = .bot ∨ ∃ args, c = .spine r args
  | [], _, _, hf, h => hf _ h
  | x :: xs, f, c, hf, h =>
      approxI_foldApps_const_inv xs (f := .app f x)
        (fun d hd => by
          rcases approxI_app_inv hd with h0 | ⟨g, _, _, hfg, _, _⟩ | ⟨r', args, u, heq, hfs, _⟩
          · exact Or.inl h0
          · rcases hf _ hfg with h1 | ⟨_, h1⟩ <;> cases h1
          · rcases hf _ hfs with h1 | ⟨args₀, h1⟩
            · cases h1
            · cases h1
              exact Or.inr ⟨args ++ [u], heq⟩)
        h

/-- Raw `ApproxI` on `foldApps (.const r ls) xs` produces only `.bot` or `.spine r args`. -/
theorem approxI_foldApps_const_head_inv {ρ : EnvI} {r : Nat} {ls : List Level}
    {xs : List (Expr Nat)} {c : CptI} (h : ApproxI ρ (foldApps (.const r ls) xs) c) :
    c = .bot ∨ ∃ args, c = .spine r args :=
  approxI_foldApps_const_inv xs
    (fun d hd => by
      rcases approxI_const_inv hd with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨[], h0⟩)
    h

/-- Raw `ApproxI` never approximates any recursor redex `iotaLhsOf w` by `.sort` or `.pi a f`. -/
theorem iota_unsound_raw_approxI_sort {E : ResolvedEnv} (ρ : EnvI) (w : IotaWitness E) :
    ¬ ApproxI ρ (iotaLhsOf w) .sort ∧ ∀ a f, ¬ ApproxI ρ (iotaLhsOf w) (.pi a f) := by
  refine ⟨fun h => ?_, fun a f h => ?_⟩
  · rcases approxI_foldApps_const_head_inv h with h0 | ⟨_, h0⟩ <;> cases h0
  · rcases approxI_foldApps_const_head_inv h with h0 | ⟨_, h0⟩ <;> cases h0

/-- Raw `ApproxI` refutes `SemEqI` on the admitted Nat zero witness `wZero` (`wZeroS`) in `natEnv`:
    `iotaRhsOf wZero = .const 1 []` has approximation `.spine 1 []`, whereas `iotaLhsOf wZero`
    is headed by `.const 3 []` (`wZero.recRef = 3`). -/
theorem wZero_unsound_raw_approxI (ρ : EnvI) :
    ¬ SemEqI ρ (iotaLhsOf wZero) (iotaRhsOf wZero) ∧
      ¬ SemEqI ρ (iotaLhsOfS wZeroS) (iotaRhsOfS wZeroS) := by
  have hrhs : ApproxI ρ (iotaRhsOf wZero) (.spine 1 []) := by
    change ApproxI ρ (.const 1 []) (.spine 1 [])
    exact .const ρ 1 []
  have hnot : ¬ ApproxI ρ (iotaLhsOf wZero) (.spine 1 []) := by
    intro h
    rcases approxI_foldApps_const_head_inv h with h0 | ⟨args, h0⟩ <;> cases h0
  refine ⟨fun h => hnot ((h (.spine 1 [])).mpr hrhs), fun h => ?_⟩
  have hlhsEq : iotaLhsOfS wZeroS = iotaLhsOf wZero :=
    iotaLhsOfS_iotaWitnessSOf wZero 64 pin_iotaWitnessSB_wZero
  rw [hlhsEq, pin_wZeroS_rhs] at h
  exact hnot ((h (.spine 1 [])).mpr hrhs)

/-! ## §2. Concrete δ/ι Lower-Ideal Model (`ApproxDI`, `denDI`, `SemEqDI`) -/

/-- A constant reference `r` is rigid in `E` when any member at `r` is neither a recursor nor a
    non-constructor with a body. In particular, constructors (`.constructorM`), inductive families
    (`.inductiveM`), axioms (`.axiomM`), and body-free members are rigid. -/
def RigidConst (E : ResolvedEnv) (r : Nat) : Prop :=
  ∀ m, E.members r = some m → (m.body = none ∨ m.mclass = .constructorM) ∧ m.mclass ≠ .recursorM

/-- A constant reference `r` is a definition with body `b` in `E` when `E.members r = some m`,
    `m.body = some b`, and `m` is neither a recursor nor a constructor. -/
def DeltaConst (E : ResolvedEnv) (r : Nat) (m : CheckedMember) (b : Expr Nat) : Prop :=
  E.members r = some m ∧ m.body = some b ∧ m.mclass ≠ .recursorM ∧ m.mclass ≠ .constructorM

theorem not_rigidConst_of_deltaConst {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hd : DeltaConst E r m b) : ¬ RigidConst E r := by
  intro hr
  obtain ⟨hbody_or_ctor, _⟩ := hr m hd.1
  rcases hbody_or_ctor with hnone | hctor
  · rw [hd.2.1] at hnone; cases hnone
  · exact hd.2.2.2 hctor

theorem not_rigidConst_of_recursor {E : ResolvedEnv} (w : IotaWitnessS E) :
    ¬ RigidConst E w.recRef := by
  intro hr
  exact (hr w.recMember w.hrec).2 w.hrecK

theorem not_deltaConst_of_recursor {E : ResolvedEnv} (w : IotaWitnessS E)
    {m : CheckedMember} {b : Expr Nat} : ¬ DeltaConst E w.recRef m b := by
  intro hd
  have hm : m = w.recMember := Option.some.inj (hd.1.symm.trans w.hrec)
  subst hm
  exact hd.2.2.1 w.hrecK

theorem rigidConst_of_ctor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hctor : m.mclass = .constructorM) :
    RigidConst E r := by
  intro m' hm'
  have heq : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst heq
  rw [hctor]
  exact ⟨Or.inr rfl, by decide⟩

theorem rigidConst_emptyEnv (r : Nat) : RigidConst emptyEnv r :=
  fun _ h => Option.noConfusion h

theorem deltaConst_of_transparent {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (htr : transparent m.mclass = true) :
    DeltaConst E r m b := by
  have hdef : m.mclass = .definitionM := by
    cases hcls : m.mclass <;> simp [transparent, hcls] at htr <;> rfl
  refine ⟨hres, hbody, ?_, ?_⟩ <;> rw [hdef] <;> decide

/-- Curried step compact: wraps a sequence of argument demands `[us₀, …, us_{k-1}]` and an output
    compact `c` into `.lam [(us₀, .lam [(us₁, … c)])]`. -/
def curryStep : List (List CptI) → CptI → CptI
  | [], c => c
  | us :: uss, c => .lam [(us, curryStep uss c)]

/-- Per-field spine demand vectors for a constructor's field demand lists `us_fields`:
    for each field slot `k` and each `u ∈ us_fields[k]`, a vector of length `us_fields.length`
    with `u` at position `k` and `.bot` at all other positions. -/
def fieldDemandVectors : List (List CptI) → List (List CptI)
  | [] => []
  | us :: uss =>
      us.map (fun u => u :: List.replicate uss.length .bot) ++
        (fieldDemandVectors uss).map (fun vec => .bot :: vec)

/-- The compact demand placed on the major premise of a recursor for constructor `ctorRef` with
    `nparams` parameters and field demand lists `us_fields`. Includes a head-tag spine of `.bot`s
    so the constructor identity `ctorRef` is always observed even when all `us ∈ us_fields` are
    empty. -/
def ctorDemand (ctorRef nparams : Nat) (us_fields : List (List CptI)) : List CptI :=
  .spine ctorRef (List.replicate nparams .bot ++ List.replicate us_fields.length .bot) ::
    (fieldDemandVectors us_fields).map
      (fun vec => .spine ctorRef (List.replicate nparams .bot ++ vec))

/-- Push a list of variable interpretations onto `ρ` in `instPrefix` order (outermost argument
    first, so the last element of `Ss` sits at de Bruijn index `0`). -/
def EnvI.pushArgs : List (CptI → Prop) → EnvI → EnvI
  | [], ρ => ρ
  | S :: Ss, ρ => EnvI.pushArgs Ss (EnvI.cons S ρ)

/-- `ApproxDI E ρ e c`: concrete lower-ideal approximation relation with δ (definition unfolding)
    and ι (admitted recursor computation schema) semantics. -/
inductive ApproxDI (E : ResolvedEnv) : EnvI → Expr Nat → CptI → Prop
  | bot (ρ : EnvI) (e : Expr Nat) : ApproxDI E ρ e .bot
  | bvar {ρ : EnvI} {i : Nat} {c : CptI} (h : ρ i c) : ApproxDI E ρ (.bvar i) c
  | sort (ρ : EnvI) (l : Level) : ApproxDI E ρ (.sort l) .sort
  | pi {ρ : EnvI} {A B : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (hA : ApproxDI E ρ A a)
      (hB : ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) ρ) B s.2) :
      ApproxDI E ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvI} {A b : Expr Nat} {f : List (List CptI × CptI)}
      (hb : ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) ρ) b s.2) :
      ApproxDI E ρ (.lam A b) (.lam f)
  | app {ρ : EnvI} {f a : Expr Nat} {g : List (List CptI × CptI)} {s : List CptI × CptI}
      (hf : ApproxDI E ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxDI E ρ a u) :
      ApproxDI E ρ (.app f a) s.2
  | const (ρ : EnvI) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) :
      ApproxDI E ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvI} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptI}
      (hdelta : DeltaConst E r m b)
      (h : ApproxDI E EnvI.bot (instantiateLevels ls b) c) :
      ApproxDI E ρ (.const r ls) c
  | recursor {ρ : EnvI} {w : IotaWitnessS E} (ls : List Level)
      {us_pre : List (List CptI)} {us_fields : List (List CptI)} {c : CptI}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxDI E (EnvI.pushArgs ((us_pre ++ us_fields).map demand) EnvI.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxDI E ρ (.const w.recRef ls)
        (curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c)
  | appSpine {ρ : EnvI} {f a : Expr Nat} {r : Nat} {args : List CptI} {u : CptI}
      (hf : ApproxDI E ρ f (.spine r args)) (ha : ApproxDI E ρ a u) :
      ApproxDI E ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvI} {A v b : Expr Nat} {c : CptI}
      (h : ApproxDI E ρ (.app (.lam A b) v) c) :
      ApproxDI E ρ (.letE A v b) c
  | lit {ρ : EnvI} {t : Nat} {c : CptI}
      (h : ApproxDI E ρ (natExpand t) c) :
      ApproxDI E ρ (.lit t) c

/-- The δ/ι lower-ideal denotation of `e` at environment `E` and variable valuation `ρ`. -/
def denDI (E : ResolvedEnv) (ρ : EnvI) (e : Expr Nat) : CptI → Prop :=
  fun c => ApproxDI E ρ e c

/-- Semantic equality in the δ/ι lower-ideal model. -/
def SemEqDI (E : ResolvedEnv) (ρ : EnvI) (a b : Expr Nat) : Prop :=
  ∀ c, ApproxDI E ρ a c ↔ ApproxDI E ρ b c

theorem semEqDI_refl (E : ResolvedEnv) (ρ : EnvI) (a : Expr Nat) : SemEqDI E ρ a a :=
  fun _ => Iff.rfl

theorem semEqDI_symm {E : ResolvedEnv} {ρ : EnvI} {a b : Expr Nat}
    (h : SemEqDI E ρ a b) : SemEqDI E ρ b a :=
  fun c => (h c).symm

theorem semEqDI_trans {E : ResolvedEnv} {ρ : EnvI} {a b d : Expr Nat}
    (h₁ : SemEqDI E ρ a b) (h₂ : SemEqDI E ρ b d) : SemEqDI E ρ a d :=
  fun c => (h₁ c).trans (h₂ c)

/-- At `emptyEnv`, `ApproxDI` coincides with `RcicNativePiModelIdeal.ApproxI`. -/
theorem approxDI_emptyEnv_iff (ρ : EnvI) (e : Expr Nat) (c : CptI) :
    ApproxDI emptyEnv ρ e c ↔ ApproxI ρ e c := by
  constructor
  · intro h
    induction h with
    | bot => exact .bot _ _
    | bvar h => exact .bvar h
    | sort => exact .sort _ _
    | pi _ _ ihA ihB => exact .pi ihA ihB
    | lam _ ihb => exact .lam ihb
    | app _ hs _ ihf iha => exact .app ihf hs iha
    | const => exact .const _ _ _
    | delta hdelta => exact Option.noConfusion hdelta.1
    | @recursor _ w => exact Option.noConfusion w.hrec
    | appSpine _ _ ihf iha => exact .appSpine ihf iha
    | letE _ ih => exact .letE ih
    | lit _ ih => exact .lit ih
  · intro h
    induction h with
    | bot => exact .bot _ _
    | bvar h => exact .bvar h
    | sort => exact .sort _ _
    | pi _ _ ihA ihB => exact .pi ihA ihB
    | lam _ ihb => exact .lam ihb
    | app _ hs _ ihf iha => exact .app ihf hs iha
    | const ρ r ls => exact .const ρ r ls (rigidConst_emptyEnv r)
    | appSpine _ _ ihf iha => exact .appSpine ihf iha
    | letE _ ih => exact .letE ih
    | lit _ ih => exact .lit ih

/-! ## §3. Inversions, Environment Monotonicity, Closed-Term & Level Invariance -/

theorem approxDI_const_env {E : ResolvedEnv} (ρ ρ' : EnvI) {r : Nat} {ls : List Level} {c : CptI}
    (h : ApproxDI E ρ (.const r ls) c) : ApproxDI E ρ' (.const r ls) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact .const _ _ _ hrigid
  | delta hdelta h => exact .delta hdelta h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h

theorem approxDI_mono_env {E : ResolvedEnv} {ρ ρ' : EnvI} (hle : EnvI.le ρ ρ')
    {e : Expr Nat} {c : CptI} (h : ApproxDI E ρ e c) : ApproxDI E ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | bvar h => exact .bvar (hle _ _ h)
  | sort => exact .sort _ _
  | pi _ _ ihA ihB => exact .pi (ihA hle) (fun s hs => ihB s hs (EnvI.le_cons hle _))
  | lam _ ihb => exact .lam (fun s hs => ihb s hs (EnvI.le_cons hle _))
  | app _ hs _ ihf iha => exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const _ _ _ hrigid => exact .const _ _ _ hrigid
  | delta hdelta h => exact .delta hdelta h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

theorem approxDI_bvar_inv {E : ResolvedEnv} {ρ : EnvI} {i : Nat} {c : CptI}
    (h : ApproxDI E ρ (.bvar i) c) : c = .bot ∨ ρ i c := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar h => exact Or.inr h

theorem approxDI_sort_inv {E : ResolvedEnv} {ρ : EnvI} {l : Level} {c : CptI}
    (h : ApproxDI E ρ (.sort l) c) : c = .bot ∨ c = .sort := by
  cases h with
  | bot => exact Or.inl rfl
  | sort => exact Or.inr rfl

theorem approxDI_rigid_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    (hrigid : RigidConst E r) {c : CptI} (h : ApproxDI E ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r [] := by
  cases h with
  | bot => exact Or.inl rfl
  | const => exact Or.inr rfl
  | delta hdelta => exact (not_rigidConst_of_deltaConst hdelta hrigid).elim
  | @recursor _ w => exact (not_rigidConst_of_recursor w hrigid).elim

theorem approxDI_delta_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) {c : CptI}
    (h : ApproxDI E ρ (.const r ls) c) :
    ApproxDI E EnvI.bot (instantiateLevels ls b) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact (not_rigidConst_of_deltaConst hdelta hrigid).elim
  | delta hdelta' h' =>
      have hm : m = _ := Option.some.inj (hdelta.1.symm.trans hdelta'.1)
      subst hm
      have hb : b = _ := Option.some.inj (hdelta.2.1.symm.trans hdelta'.2.1)
      subst hb
      exact h'
  | @recursor _ w => exact (not_deltaConst_of_recursor w hdelta).elim

theorem approxDI_recursor_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hrec : E.members r = some m) (hrecK : m.mclass = .recursorM) {c : CptI}
    (h : ApproxDI E ρ (.const r ls) c) :
    c = .bot ∨
      ∃ (w : IotaWitnessS E) (us_pre us_fields : List (List CptI)) (c₀ : CptI),
        w.recRef = r ∧ us_pre.length = w.preMajor.length ∧ us_fields.length = w.fields.length ∧
        ApproxDI E (EnvI.pushArgs ((us_pre ++ us_fields).map demand) EnvI.bot)
          (instantiateLevels ls w.schema) c₀ ∧
        c = curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c₀ := by
  cases h with
  | bot => exact Or.inl rfl
  | const _ _ _ hrigid => exact ((hrigid m hrec).2 hrecK).elim
  | delta hdelta =>
      have hm : m = _ := Option.some.inj (hrec.symm.trans hdelta.1)
      subst hm
      exact (hdelta.2.2.1 hrecK).elim
  | @recursor _ w _ us_pre us_fields c₀ hpre hflds h' =>
      exact Or.inr ⟨w, us_pre, us_fields, c₀, rfl, hpre, hflds, h', rfl⟩

theorem approxDI_pi_inv {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxDI E ρ A a ∧
      ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) ρ) B s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | pi hA hB => exact Or.inr ⟨_, _, rfl, hA, hB⟩

theorem approxDI_lam_inv {E : ResolvedEnv} {ρ : EnvI} {A b : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ (.lam A b) c) :
    c = .bot ∨ ∃ f, c = .lam f ∧ ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) ρ) b s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lam hb => exact Or.inr ⟨_, rfl, hb⟩

theorem approxDI_app_inv {E : ResolvedEnv} {ρ : EnvI} {f a : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ (.app f a) c) :
    c = .bot ∨
      (∃ g s, c = s.2 ∧ ApproxDI E ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, ApproxDI E ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxDI E ρ f (.spine r args) ∧ ApproxDI E ρ a u) := by
  cases h with
  | bot => exact Or.inl rfl
  | app hf hs ha => exact Or.inr (Or.inl ⟨_, _, rfl, hf, hs, ha⟩)
  | appSpine hf ha => exact Or.inr (Or.inr ⟨_, _, _, rfl, hf, ha⟩)

theorem approxDI_letE_inv {E : ResolvedEnv} {ρ : EnvI} {A v b : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ (.letE A v b) c) :
    c = .bot ∨ ApproxDI E ρ (.app (.lam A b) v) c := by
  cases h with
  | bot => exact Or.inl rfl
  | letE h => exact Or.inr h

theorem approxDI_lit_inv {E : ResolvedEnv} {ρ : EnvI} {t : Nat} {c : CptI}
    (h : ApproxDI E ρ (.lit t) c) :
    c = .bot ∨ ApproxDI E ρ (natExpand t) c := by
  cases h with
  | bot => exact Or.inl rfl
  | lit h => exact Or.inr h

theorem exprClosedAt_natExpand (k : Nat) : (t : Nat) → exprClosedAt k (natExpand t) = true
  | 0 => rfl
  | t + 1 => by
      simp only [natExpand, litSucc, exprClosedAt, Bool.true_and]
      exact exprClosedAt_natExpand k t

/-- If `exprClosedAt k e = true` and `ρ` agrees with `ρ'` on all variables `< k`, then
    `ApproxDI E ρ e c → ApproxDI E ρ' e c`. -/
theorem approxDI_closedAt_env {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) :
    ∀ {k : Nat} {ρ' : EnvI}, exprClosedAt k e = true → (∀ i < k, ρ i = ρ' i) →
      ApproxDI E ρ' e c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, decide_eq_true_eq] at hcl
      exact .bvar (heq i hcl ▸ h)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .pi (ihA hcl.1 heq) (fun s hs => ihB s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | lam _ ihb =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .lam (fun s hs => ihb s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | app _ hs _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .app (ihf hcl.1 heq) hs (fun u hu => iha u hu hcl.2 heq)
  | const _ _ _ hrigid => intro _ _ _ _; exact .const _ _ _ hrigid
  | delta hdelta h => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hpre hflds h => intro _ _ _ _; exact .recursor ls hpre hflds h
  | appSpine _ _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .appSpine (ihf hcl.1 heq) (iha hcl.2 heq)
  | @letE _ A v b _ _ ih =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      have hcl' : exprClosedAt k (.app (.lam A b) v) = true := by
        simp only [exprClosedAt, Bool.and_eq_true]
        exact ⟨⟨hcl.1.1, hcl.2⟩, hcl.1.2⟩
      exact .letE (ih hcl' heq)
  | @lit _ t _ _ ih =>
      intro k ρ' _ heq
      exact .lit (ih (exprClosedAt_natExpand k t) heq)

/-- Closed terms (`exprClosedAt 0 e = true`) have environment-independent approximations. -/
theorem approxDI_closed0_env {E : ResolvedEnv} (ρ ρ' : EnvI) {e : Expr Nat}
    (hcl : exprClosedAt 0 e = true) {c : CptI}
    (h : ApproxDI E ρ e c) : ApproxDI E ρ' e c :=
  approxDI_closedAt_env h hcl (fun _ hi => (Nat.not_lt_zero _ hi).elim)

theorem approxDI_natExpand_env {E : ResolvedEnv} (ρ ρ' : EnvI) (t : Nat) {c : CptI}
    (h : ApproxDI E ρ (natExpand t) c) : ApproxDI E ρ' (natExpand t) c :=
  approxDI_closed0_env ρ ρ' (exprClosedAt_natExpand 0 t) h

theorem instantiateLevels_natExpand (ls : List Level) :
    (t : Nat) → instantiateLevels ls (natExpand t) = natExpand t
  | 0 => rfl
  | t + 1 => by
      simp only [natExpand, litSucc, instantiateLevels, List.map_nil,
        instantiateLevels_natExpand ls t]

/-- `ApproxDI` is invariant under swapping universe-level instantiations `ls₁` and `ls₂`. -/
theorem approxDI_instantiateLevels_swap {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) :
    ∀ {e₀ : Expr Nat} (ls₁ ls₂ : List Level),
      e = instantiateLevels ls₁ e₀ → ApproxDI E ρ (instantiateLevels ls₂ e₀) c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .bvar h
  | sort =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .sort _ _
  | pi _ _ ihA ihB =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .pi (ihA ls₁ ls₂ rfl) (fun s hs => ihB s hs ls₁ ls₂ rfl)
  | lam _ ihb =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .lam (fun s hs => ihb s hs ls₁ ls₂ rfl)
  | app _ hs _ ihf iha =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .app (ihf ls₁ ls₂ rfl) hs (fun u hu => iha u hu ls₁ ls₂ rfl)
  | const _ r _ hrigid =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .const _ r _ hrigid
  | @delta ρ r ls m b c hdelta _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | const r₀ ls₀ =>
          cases heq
          exact .delta hdelta (ih _ (ls₀.map (instLevel ls₂)) rfl)
      | _ => cases heq
  | @recursor ρ w ls us_pre us_fields c hpre hflds _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | const r₀ ls₀ =>
          injection heq with hr₀ hls₀
          subst hr₀
          exact .recursor (ls₀.map (instLevel ls₂)) hpre hflds
            (ih ls (ls₀.map (instLevel ls₂)) rfl)
      | _ => cases heq
  | appSpine _ _ ihf iha =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .appSpine (ihf ls₁ ls₂ rfl) (iha ls₁ ls₂ rfl)
  | letE _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | letE A₀ v₀ b₀ =>
          cases heq
          exact .letE (ih (e₀ := .app (.lam A₀ b₀) v₀) ls₁ ls₂ rfl)
      | _ => cases heq
  | @lit _ t _ _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | lit t₀ =>
          cases heq
          exact .lit (by
            have := ih (e₀ := natExpand t) ls₁ ls₂ (instantiateLevels_natExpand ls₁ t).symm
            rwa [instantiateLevels_natExpand ls₂ t] at this)
      | _ => cases heq

/-- `ApproxDI` is invariant under `instantiateLevels ls`. -/
theorem approxDI_instantiateLevels_iff (E : ResolvedEnv) (ρ : EnvI) (ls : List Level)
    (e : Expr Nat) (c : CptI) :
    ApproxDI E ρ (instantiateLevels ls e) c ↔ ApproxDI E ρ e c := by
  constructor
  · intro h
    have := approxDI_instantiateLevels_swap h ls [] rfl
    rwa [instantiateLevels_nil] at this
  · intro h
    exact approxDI_instantiateLevels_swap h [] ls (instantiateLevels_nil e).symm

theorem approxDI_const_levels {E : ResolvedEnv} {ρ : EnvI} {r : Nat} (ls₁ ls₂ : List Level)
    {c : CptI} (h : ApproxDI E ρ (.const r ls₁) c) : ApproxDI E ρ (.const r ls₂) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact .const _ r ls₂ hrigid
  | delta hdelta h => exact .delta hdelta (approxDI_instantiateLevels_swap h ls₁ ls₂ rfl)
  | recursor _ hpre hflds h =>
      exact .recursor ls₂ hpre hflds (approxDI_instantiateLevels_swap h ls₁ ls₂ rfl)

/-- Any two universe-level instantiations of the same constant `r` are semantically equal in
    `ApproxDI` (`ConvT.consts` soundness). -/
theorem semEqDI_const_levels (E : ResolvedEnv) (ρ : EnvI) (r : Nat) (ls₁ ls₂ : List Level) :
    SemEqDI E ρ (.const r ls₁) (.const r ls₂) :=
  fun _ => ⟨approxDI_const_levels ls₁ ls₂, approxDI_const_levels ls₂ ls₁⟩

/-! ## §4. Finite Demand, Lifting, Substitution, `instPrefix`, β, ζ, and Literals -/

theorem approxDI_mono_update {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {e : Expr Nat} {c : CptI}
    (us us' : List CptI) (hsub : ∀ u ∈ us, u ∈ us')
    (h : ApproxDI E (EnvI.update ρ j (demand us)) e c) :
    ApproxDI E (EnvI.update ρ j (demand us')) e c :=
  approxDI_mono_env (fun i d hd => by
    by_cases hij : i = j
    · subst hij
      rw [EnvI.update_self] at hd ⊢
      exact hsub d hd
    · rw [EnvI.update_ne _ hij] at hd ⊢
      exact hd) h

theorem approxDI_factor_list {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {B : Expr Nat} :
    (f : List (List CptI × CptI)) →
    (∀ s ∈ f, ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ApproxDI E (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2) →
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | s :: rest, ih => by
      obtain ⟨us₁, h₁, hs⟩ := ih s (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxDI_factor_list rest (fun s' hs' => ih s' (List.mem_cons_of_mem _ hs'))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun s' hs' => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact h₁ u hu
        · exact h₂ u hu
      · cases List.mem_cons.mp hs' with
        | inl heq =>
            subst heq
            rw [EnvI.cons_update] at hs ⊢
            exact approxDI_mono_update us₁ _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hs
        | inr hs'' =>
            have := hrest s' hs''
            rw [EnvI.cons_update] at this ⊢
            exact approxDI_mono_update us₂ _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this

theorem approxDI_factor_args {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {a : Expr Nat} :
    (us0 : List CptI) →
    (∀ u ∈ us0, ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧
      ApproxDI E (EnvI.update ρ j (demand us)) a u) →
    ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧
      ∀ u ∈ us0, ApproxDI E (EnvI.update ρ j (demand us)) a u
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | u :: rest, ih => by
      obtain ⟨us₁, h₁, hu⟩ := ih u (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxDI_factor_args rest (fun u' hu' => ih u' (List.mem_cons_of_mem _ hu'))
      refine ⟨us₁ ++ us₂, fun w hw => ?_, fun u' hu' => ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact h₁ w hw
        · exact h₂ w hw
      · cases List.mem_cons.mp hu' with
        | inl heq =>
            subst heq
            exact approxDI_mono_update us₁ _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hu
        | inr hu'' =>
            exact approxDI_mono_update us₂ _ (fun w hw => List.mem_append.mpr (Or.inr hw))
              (hrest u' hu'')

/-- Finite demand on `ApproxDI`: every derivation uses only finitely many compacts of any one
    variable `j`. Because `const`, `delta`, and `recursor` do not read `ρ`, their demand on `j`
    is `[]`. -/
theorem approxDI_factor {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) (j : Nat) :
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧ ApproxDI E (EnvI.update ρ j (demand us)) e c := by
  induction h generalizing j with
  | bot => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bot _ _⟩
  | @bvar ρ i c h =>
      by_cases hij : i = j
      · subst hij
        refine ⟨[c], fun u hu => ?_, .bvar ?_⟩
        · have heq := List.mem_singleton.mp hu; subst heq; exact h
        · rw [EnvI.update_self]; exact List.mem_singleton.mpr rfl
      · exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim,
          .bvar (by rw [EnvI.update_ne _ hij]; exact h)⟩
  | sort => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .sort _ _⟩
  | @pi ρ A B a f _ _ ihA ihB =>
      obtain ⟨usA, hA₁, hA₂⟩ := ihA j
      obtain ⟨usB, hB₁, hB₂⟩ := approxDI_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihB s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .pi ?_ ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hA₁ u hu
        · exact hB₁ u hu
      · exact approxDI_mono_update usA _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hA₂
      · intro s hs
        have := hB₂ s hs
        rw [EnvI.cons_update] at this ⊢
        exact approxDI_mono_update usB _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this
  | @lam ρ A b f _ ihb =>
      obtain ⟨usb, hb₁, hb₂⟩ := approxDI_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihb s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      exact ⟨usb, hb₁, .lam hb₂⟩
  | @app ρ f a g s _ hs _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := approxDI_factor_args s.1 (fun u hu => iha u hu j)
      refine ⟨usf ++ usa, fun w hw => ?_, .app ?_ hs ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxDI_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact fun u hu => approxDI_mono_update usa _
          (fun w hw => List.mem_append.mpr (Or.inr hw)) (ha₂ u hu)
  | const _ _ _ hrigid =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .const _ _ _ hrigid⟩
  | delta hdelta h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .delta hdelta h⟩
  | recursor ls hpre hflds h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursor ls hpre hflds h⟩
  | appSpine _ _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := iha j
      refine ⟨usf ++ usa, fun w hw => ?_, .appSpine ?_ ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxDI_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact approxDI_mono_update usa _ (fun w hw => List.mem_append.mpr (Or.inr hw)) ha₂
  | letE _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .letE h₂⟩
  | lit _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .lit h₂⟩

theorem approxDI_lift_intro {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) :
    ∀ (k : Nat) (S : CptI → Prop), ApproxDI E (EnvI.insert ρ k S) (lift k 1 e) c := by
  induction h with
  | bot => intro k S; exact .bot _ _
  | @bvar ρ i c h =>
      intro k S
      simp only [lift]
      by_cases hk : k ≤ i
      · rw [if_pos hk]
        exact .bvar (by rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)]; simpa using h)
      · rw [if_neg hk]
        exact .bvar (by rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)]; exact h)
  | sort => intro k S; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k S
      simp only [lift]
      exact .pi (ihA k S) (fun s hs => by rw [EnvI.cons_insert]; exact ihB s hs (k + 1) S)
  | lam _ ihb =>
      intro k S
      simp only [lift]
      exact .lam (fun s hs => by rw [EnvI.cons_insert]; exact ihb s hs (k + 1) S)
  | app _ hs _ ihf iha =>
      intro k S
      simp only [lift]
      exact .app (ihf k S) hs (fun u hu => iha u hu k S)
  | const _ _ _ hrigid => intro k S; exact .const _ _ _ hrigid
  | delta hdelta h => intro k S; exact .delta hdelta h
  | recursor ls hpre hflds h => intro k S; exact .recursor ls hpre hflds h
  | appSpine _ _ ihf iha =>
      intro k S
      simp only [lift]
      exact .appSpine (ihf k S) (iha k S)
  | letE _ ih =>
      intro k S
      simp only [lift]
      exact .letE (ih k S)
  | lit _ ih =>
      intro k S
      simp only [lift]
      exact .lit (by have := ih k S; rwa [natExpand_lift] at this)

theorem approxDI_lift_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvI} {k : Nat} {S : CptI → Prop} {c : CptI},
      ApproxDI E (EnvI.insert ρ k S) (lift k 1 e) c → ApproxDI E ρ e c
  | .bvar i, ρ, k, S, c, h => by
      simp only [lift] at h
      by_cases hk : k ≤ i
      · rw [if_pos hk] at h
        rcases approxDI_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)] at h0
          exact .bvar (by simpa using h0)
      · rw [if_neg hk] at h
        rcases approxDI_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)] at h0
          exact .bvar h0
  | .sort l, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const r ls, ρ, k, S, c, h => by
      simp only [lift] at h
      exact approxDI_const_env (EnvI.insert ρ k S) ρ h
  | .app f a, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxDI_lift_elim f hf) hs (fun u hu => approxDI_lift_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxDI_lift_elim f hf) (approxDI_lift_elim a ha)
  | .lam A b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => approxDI_lift_elim b (by
          have := hb s hs; rw [EnvI.cons_insert] at this; exact this))
  | .pi A B, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxDI_lift_elim A hA) (fun s hs => approxDI_lift_elim B (by
          have := hB s hs; rw [EnvI.cons_insert] at this; exact this))
  | .letE A v b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxDI_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxDI_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            exact .letE (.app (.lam (fun s' hs' => approxDI_lift_elim b (by
              have := hb s' hs'; rw [EnvI.cons_insert] at this; exact this))) hs
              (fun u hu => approxDI_lift_elim v (ha u hu)))
        · rcases approxDI_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDI_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxDI_natExpand_env _ _ t h')

theorem approxDI_liftN_intro {E : ResolvedEnv} {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxDI E (EnvI.drop ρ j) e c → ApproxDI E ρ (lift 0 j e) c
  | ρ, 0, h => by rw [EnvI.drop_zero] at h; rw [lift_zero_idx]; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx]
      rw [EnvI.drop_succ] at h
      have := approxDI_lift_intro (approxDI_liftN_intro (EnvI.drop ρ 1) j h) 0 (ρ 0)
      rwa [EnvI.insert_drop_one] at this

theorem approxDI_liftN_elim {E : ResolvedEnv} {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxDI E ρ (lift 0 j e) c → ApproxDI E (EnvI.drop ρ j) e c
  | ρ, 0, h => by rw [EnvI.drop_zero]; rw [lift_zero_idx] at h; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx] at h
      rw [EnvI.drop_succ]
      have h' : ApproxDI E (EnvI.insert (EnvI.drop ρ 1) 0 (ρ 0)) (lift 0 1 (lift 0 j e)) c := by
        rwa [EnvI.insert_drop_one]
      exact approxDI_liftN_elim (EnvI.drop ρ 1) j (approxDI_lift_elim (lift 0 j e) h')

theorem approxDI_subst_intro {E : ResolvedEnv} {ρ' : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ' e c) :
    ∀ (ρ : EnvI) (j : Nat) (r : Expr Nat),
      ρ' = EnvI.insert ρ j (denDI E (EnvI.drop ρ j) r) →
      ApproxDI E ρ (instantiate j (lift 0 j r) e) c := by
  induction h with
  | bot => intro ρ j r _; exact .bot _ _
  | @bvar ρ' i c h =>
      intro ρ j r hρ
      subst hρ
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [EnvI.insert_self] at h
        exact approxDI_liftN_intro ρ i h
      · rw [if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]
          rw [EnvI.insert_gt _ hlt] at h
          exact .bvar h
        · rw [if_neg hlt]
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rw [EnvI.insert_lt _ hil] at h
          exact .bvar h
  | sort => intro ρ j r _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .pi (ihA ρ j r hρ) (fun s hs => ihB s hs _ (j + 1) r
        (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | lam _ ihb =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .lam (fun s hs => ihb s hs _ (j + 1) r (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | app _ hs _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .app (ihf ρ j r hρ) hs (fun u hu => iha u hu ρ j r hρ)
  | const _ _ _ hrigid => intro _ _ _ _; exact .const _ _ _ hrigid
  | delta hdelta h => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hpre hflds h => intro _ _ _ _; exact .recursor ls hpre hflds h
  | appSpine _ _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .appSpine (ihf ρ j r hρ) (iha ρ j r hρ)
  | letE _ ih =>
      intro ρ j r hρ
      have := ih ρ j r hρ
      simp only [instantiate] at this ⊢
      exact .letE this
  | lit _ ih =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .lit (by have := ih ρ j r hρ; rwa [natExpand_instantiate] at this)

theorem approxDI_subst_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvI} {j : Nat} {r : Expr Nat} {c : CptI},
      ApproxDI E ρ (instantiate j (lift 0 j r) e) c →
      ApproxDI E (EnvI.insert ρ j (denDI E (EnvI.drop ρ j) r)) e c
  | .bvar i, ρ, j, r, c, h => by
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact .bvar (by rw [EnvI.insert_self]; exact approxDI_liftN_elim ρ i h)
      · rw [if_neg hij] at h
        by_cases hlt : j < i
        · rw [if_pos hlt] at h
          rcases approxDI_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_gt _ hlt]; exact h0)
        · rw [if_neg hlt] at h
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rcases approxDI_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_lt _ hil]; exact h0)
  | .sort l, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDI_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const k ls, ρ, j, r, c, h => by
      simp only [instantiate] at h
      exact approxDI_const_env ρ _ h
  | .app f a, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxDI_subst_elim f hf) hs (fun u hu => approxDI_subst_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxDI_subst_elim f hf) (approxDI_subst_elim a ha)
  | .lam A b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxDI_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxDI_subst_elim b (hb s hs))
  | .pi A B, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxDI_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxDI_subst_elim A hA) (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxDI_subst_elim B (hB s hs))
  | .letE A v b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDI_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxDI_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxDI_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            rw [lift_shift_comp_idx] at hb
            exact .letE (.app (.lam (fun s' hs' => by
              rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s'.1) ρ j]
              exact approxDI_subst_elim b (hb s' hs'))) hs
              (fun u hu => approxDI_subst_elim v (ha u hu)))
        · rcases approxDI_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDI_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxDI_natExpand_env _ _ t h')

theorem approxDI_subst_iff (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (a e : Expr Nat) (c : CptI) :
    ApproxDI E ρ (instantiate j (lift 0 j a) e) c ↔
      ApproxDI E (EnvI.insert ρ j (denDI E (EnvI.drop ρ j) a)) e c :=
  ⟨approxDI_subst_elim e, fun h => approxDI_subst_intro h ρ j a rfl⟩

theorem EnvI.update_insert_self (ρ : EnvI) (j : Nat) (S T : CptI → Prop) :
    EnvI.update (EnvI.insert ρ j S) j T = EnvI.insert ρ j T := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [EnvI.update_self, EnvI.insert_self]
  · rw [EnvI.update_ne _ hij]
    by_cases hlt : i < j
    · rw [EnvI.insert_lt _ hlt, EnvI.insert_lt _ hlt]
    · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
      rw [EnvI.insert_gt _ hgt, EnvI.insert_gt _ hgt]

/-- Substitution factored through finite demand: `instantiate j (lift 0 j a) e` approximates `c`
    at `ρ` iff there is a finite demand `us` on `a` at `EnvI.drop ρ j` such that `e` approximates
    `c` at `EnvI.insert ρ j (demand us)`. -/
theorem approxDI_subst_demand_iff (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (a e : Expr Nat)
    (c : CptI) :
    ApproxDI E ρ (instantiate j (lift 0 j a) e) c ↔
      ∃ us : List CptI, (∀ u ∈ us, ApproxDI E (EnvI.drop ρ j) a u) ∧
        ApproxDI E (EnvI.insert ρ j (demand us)) e c := by
  rw [approxDI_subst_iff]
  constructor
  · intro h
    obtain ⟨us, hus, hup⟩ := approxDI_factor h j
    rw [EnvI.update_insert_self] at hup
    exact ⟨us, fun u hu => by have := hus u hu; rwa [EnvI.insert_self] at this, hup⟩
  · rintro ⟨us, hus, hins⟩
    refine approxDI_mono_env (fun i d hd => ?_) hins
    by_cases hij : i = j
    · subst hij
      rw [EnvI.insert_self] at hd ⊢
      exact hus d hd
    · by_cases hlt : i < j
      · rw [EnvI.insert_lt _ hlt] at hd ⊢; exact hd
      · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
        rw [EnvI.insert_gt _ hgt] at hd ⊢; exact hd

theorem EnvI.pushArgs_append (Ss₁ Ss₂ : List (CptI → Prop)) (ρ : EnvI) :
    EnvI.pushArgs (Ss₁ ++ Ss₂) ρ = EnvI.pushArgs Ss₂ (EnvI.pushArgs Ss₁ ρ) := by
  induction Ss₁ generalizing ρ with
  | nil => rfl
  | cons S Ss₁ ih => exact ih (EnvI.cons S ρ)

theorem EnvI.pushArgs_insert (Ts : List (CptI → Prop)) (ρ : EnvI) (k : Nat) (S : CptI → Prop) :
    EnvI.insert (EnvI.pushArgs Ts ρ) (Ts.length + k) S =
      EnvI.pushArgs Ts (EnvI.insert ρ k S) := by
  induction Ts generalizing ρ k with
  | nil =>
      simp only [EnvI.pushArgs, List.length_nil, Nat.zero_add]
  | cons T Ts ih =>
      simp only [EnvI.pushArgs, List.length_cons]
      have hadd : Ts.length + 1 + k = Ts.length + (k + 1) := by omega
      rw [hadd, ih (EnvI.cons T ρ) (k + 1), EnvI.cons_insert]

theorem EnvI.insert_pushArgs_self (Ts : List (CptI → Prop)) (ρ : EnvI) (S : CptI → Prop) :
    EnvI.insert (EnvI.pushArgs Ts ρ) Ts.length S = EnvI.pushArgs (S :: Ts) ρ := by
  have h := EnvI.pushArgs_insert Ts ρ 0 S
  rw [Nat.add_zero, EnvI.insert_zero] at h
  exact h

theorem EnvI.drop_pushArgs (Ts : List (CptI → Prop)) (ρ : EnvI) (k : Nat) :
    EnvI.drop (EnvI.pushArgs Ts ρ) (Ts.length + k) = EnvI.drop ρ k := by
  induction Ts generalizing ρ k with
  | nil => simp only [EnvI.pushArgs, List.length_nil, Nat.zero_add]
  | cons T Ts ih =>
      simp only [EnvI.pushArgs, List.length_cons]
      have hadd : Ts.length + 1 + k = Ts.length + (k + 1) := by omega
      rw [hadd, ih (EnvI.cons T ρ) (k + 1), EnvI.drop_cons]

theorem EnvI.drop_pushArgs_self (Ts : List (CptI → Prop)) (ρ : EnvI) :
    EnvI.drop (EnvI.pushArgs Ts ρ) Ts.length = ρ := by
  have h := EnvI.drop_pushArgs Ts ρ 0
  rw [Nat.add_zero, EnvI.drop_zero] at h
  exact h

private theorem EnvI.pushArgs_congr_lt (Ts : List (CptI → Prop)) :
    ∀ {ρ ρ' : EnvI} {k : Nat}, (∀ i < k, ρ i = ρ' i) →
      ∀ {i : Nat}, i < Ts.length + k → EnvI.pushArgs Ts ρ i = EnvI.pushArgs Ts ρ' i := by
  induction Ts with
  | nil =>
      intro ρ ρ' k h i hi
      simp only [List.length_nil, Nat.zero_add] at hi
      exact h i hi
  | cons T Ts ih =>
      intro ρ ρ' k h i hi
      simp only [EnvI.pushArgs]
      apply ih (k := k + 1)
      · intro j hj
        cases j with
        | zero => rfl
        | succ j => exact h j (Nat.lt_of_succ_lt_succ hj)
      · simp only [List.length_cons] at hi
        omega

theorem EnvI.pushArgs_lt (Ts : List (CptI → Prop)) (ρ ρ' : EnvI) {i : Nat}
    (hi : i < Ts.length) : EnvI.pushArgs Ts ρ i = EnvI.pushArgs Ts ρ' i :=
  EnvI.pushArgs_congr_lt Ts (k := 0) (fun _ h => (Nat.not_lt_zero _ h).elim) (by omega)

/-- Pointwise finite-demand approximation of a list of arguments `args` by a list of demand lists
    `uss`. -/
inductive ApproxArgsDemand (E : ResolvedEnv) (ρ : EnvI) :
    List (Expr Nat) → List (List CptI) → Prop
  | nil : ApproxArgsDemand E ρ [] []
  | cons {a : Expr Nat} {as : List (Expr Nat)} {us : List CptI} {uss : List (List CptI)}
      (ha : ∀ u ∈ us, ApproxDI E ρ a u)
      (has : ApproxArgsDemand E ρ as uss) :
      ApproxArgsDemand E ρ (a :: as) (us :: uss)

theorem ApproxArgsDemand.length_eq {E : ResolvedEnv} {ρ : EnvI}
    {args : List (Expr Nat)} {uss : List (List CptI)}
    (h : ApproxArgsDemand E ρ args uss) : uss.length = args.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ApproxArgsDemand.append_iff {E : ResolvedEnv} {ρ : EnvI}
    (xs ys : List (Expr Nat)) (uss : List (List CptI)) :
    ApproxArgsDemand E ρ (xs ++ ys) uss ↔
      ∃ uss₁ uss₂, uss = uss₁ ++ uss₂ ∧
        ApproxArgsDemand E ρ xs uss₁ ∧ ApproxArgsDemand E ρ ys uss₂ := by
  induction xs generalizing uss with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h; exact ⟨[], uss, rfl, .nil, h⟩
      · rintro ⟨uss₁, uss₂, rfl, h₁, h₂⟩
        cases h₁
        exact h₂
  | cons x xs ih =>
      simp only [List.cons_append]
      constructor
      · intro h
        cases h with
        | cons hx hrest =>
            obtain ⟨uss₁, uss₂, rfl, h₁, h₂⟩ := (ih _).mp hrest
            exact ⟨_ :: uss₁, uss₂, rfl, .cons hx h₁, h₂⟩
      · rintro ⟨uss₁, uss₂, rfl, h₁, h₂⟩
        cases h₁ with
        | cons hx h₁' =>
            exact .cons hx ((ih _).mpr ⟨_, _, rfl, h₁', h₂⟩)

/-- Exact finite-demand characterization of `instPrefix args e` in `ApproxDI`. -/
theorem approxDI_instPrefix_demand_iff (E : ResolvedEnv) (ρ : EnvI)
    (args : List (Expr Nat)) (e : Expr Nat) (c : CptI) :
    ApproxDI E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemand E ρ args uss ∧
        ApproxDI E (EnvI.pushArgs (uss.map demand) ρ) e c := by
  induction args generalizing e with
  | nil =>
      simp only [instPrefix]
      constructor
      · intro h; exact ⟨[], .nil, h⟩
      · rintro ⟨uss, hargs, h⟩
        cases hargs
        exact h
  | cons a as ih =>
      simp only [instPrefix]
      rw [ih]
      constructor
      · rintro ⟨uss, has, hsub⟩
        have hlen : (uss.map demand).length = as.length := by
          rw [List.length_map, has.length_eq]
        rw [← hlen, approxDI_subst_demand_iff, EnvI.drop_pushArgs_self] at hsub
        obtain ⟨us, ha, he⟩ := hsub
        rw [EnvI.insert_pushArgs_self] at he
        exact ⟨us :: uss, .cons ha has, he⟩
      · rintro ⟨uss₀, hargs, he⟩
        cases hargs with
        | @cons _ _ us uss ha has =>
            refine ⟨uss, has, ?_⟩
            have hlen : (uss.map demand).length = as.length := by
              rw [List.length_map, has.length_eq]
            rw [← hlen, approxDI_subst_demand_iff, EnvI.drop_pushArgs_self]
            refine ⟨us, ha, ?_⟩
            rw [EnvI.insert_pushArgs_self]
            exact he

/-- When `exprClosedAt args.length e = true`, the tail environment in
    `approxDI_instPrefix_demand_iff` can be replaced by `EnvI.bot`. -/
theorem approxDI_instPrefix_closed_iff (E : ResolvedEnv) (ρ : EnvI)
    (args : List (Expr Nat)) (e : Expr Nat) (hcl : exprClosedAt args.length e = true)
    (c : CptI) :
    ApproxDI E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemand E ρ args uss ∧
        ApproxDI E (EnvI.pushArgs (uss.map demand) EnvI.bot) e c := by
  rw [approxDI_instPrefix_demand_iff]
  constructor
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demand).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs,
      approxDI_closedAt_env h hcl' (fun i hi => EnvI.pushArgs_lt _ ρ EnvI.bot hi)⟩
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demand).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs,
      approxDI_closedAt_env h hcl' (fun i hi => EnvI.pushArgs_lt _ EnvI.bot ρ hi)⟩

/-- β-soundness in `ApproxDI`: the redex and the contractum have identical approximations. -/
theorem approxDI_beta (E : ResolvedEnv) (ρ : EnvI) (A b a : Expr Nat) :
    SemEqDI E ρ (.app (.lam A b) a) (instantiate0 a b) := by
  intro c
  constructor
  · intro h
    rcases approxDI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
    · subst h0; exact .bot _ _
    · subst heq
      rcases approxDI_lam_inv hf with h1 | ⟨f', heq', hb⟩
      · cases h1
      · cases heq'
        have h₁ : ApproxDI E (EnvI.cons (denDI E ρ a) ρ) b s.2 :=
          approxDI_mono_env (fun i d hd => by
            cases i with
            | zero => exact ha d hd
            | succ i => exact hd) (hb s hs)
        have h₂ := approxDI_subst_intro h₁ ρ 0 a (by rw [EnvI.insert_zero, EnvI.drop_zero])
        rwa [lift_zero_idx] at h₂
    · rcases approxDI_lam_inv hf with h1 | ⟨f', heq', _⟩
      · cases h1
      · cases heq'
  · intro h
    have h₁ : ApproxDI E ρ (instantiate 0 (lift 0 0 a) b) c := by rwa [lift_zero_idx]
    have h₂ := approxDI_subst_elim b h₁
    rw [EnvI.insert_zero, EnvI.drop_zero] at h₂
    obtain ⟨us, hus, h₃⟩ := approxDI_factor h₂ 0
    have h₄ : ApproxDI E (EnvI.cons (demand us) ρ) b c := by
      refine approxDI_mono_env (fun i d hd => ?_) h₃
      cases i with
      | zero => rw [EnvI.update_self] at hd; exact hd
      | succ i => rw [EnvI.update_ne _ (Nat.succ_ne_zero i)] at hd; exact hd
    exact .app (s := (us, c)) (.lam (f := [(us, c)]) (fun s hs => by
      have heq := List.mem_singleton.mp hs
      subst heq
      exact h₄)) (List.mem_singleton.mpr rfl)
      (fun u hu => hus u hu)

/-- ζ-soundness in `ApproxDI`: `letE` and its contractum have identical approximations. -/
theorem approxDI_zeta (E : ResolvedEnv) (ρ : EnvI) (A v b : Expr Nat) :
    SemEqDI E ρ (.letE A v b) (instantiate0 v b) := by
  intro c
  constructor
  · intro h
    rcases approxDI_letE_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact (approxDI_beta E ρ A b v c).mp h'
  · intro h
    exact .letE ((approxDI_beta E ρ A b v c).mpr h)

/-- Literal expansion soundness in `ApproxDI`. -/
theorem approxDI_lit (E : ResolvedEnv) (ρ : EnvI) (t : Nat) :
    SemEqDI E ρ (.lit t) (natExpand t) := by
  intro c
  constructor
  · intro h
    rcases approxDI_lit_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact h'
  · intro h
    exact .lit h

/-! ## §5. Soundness of δ (`ConvT.delta` and `WhStep.delta`) -/

/-- Exact characterization of `ApproxDI` at a definition `.const r ls`: for every valuation `ρ`,
    `.const r ls` has the same approximations as `instantiateLevels ls b` at `EnvI.bot`. -/
theorem approxDI_delta_bot {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) (c : CptI) :
    ApproxDI E ρ (.const r ls) c ↔ ApproxDI E EnvI.bot (instantiateLevels ls b) c :=
  ⟨approxDI_delta_const_inv hdelta, .delta hdelta⟩

/-- At `EnvI.bot`, every `DeltaConst` satisfies `SemEqDI` with no closedness premise. -/
theorem semEqDI_delta_bot {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) :
    SemEqDI E EnvI.bot (.const r ls) (instantiateLevels ls b) :=
  approxDI_delta_bot hdelta

/-- For any closed definition body (`exprClosedAt 0 b = true`), `.const r ls` and
    `instantiateLevels ls b` are semantically equal at EVERY valuation `ρ : EnvI`. -/
theorem semEqDI_delta {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b)
    (hcl : exprClosedAt 0 b = true) :
    SemEqDI E ρ (.const r ls) (instantiateLevels ls b) := by
  intro c
  have hcl_inst : exprClosedAt 0 (instantiateLevels ls b) = true := by
    rw [exprClosedAt_instantiateLevels]
    exact hcl
  rw [approxDI_delta_bot hdelta]
  exact ⟨approxDI_closed0_env EnvI.bot ρ hcl_inst, approxDI_closed0_env ρ EnvI.bot hcl_inst⟩

/-- In any `GroupMembersT` chain, every member with a `some` body already existed in the base
    environment (group members always have `body = none`). -/
theorem groupMembersT_body_some {S E E' : ResolvedEnv} {l : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E l E')
    (hE : ∀ r m b, E.members r = some m → m.body = some b →
      DeltaConst E r m b ∧ exprClosedAt 0 b = true) :
    ∀ r m b, E'.members r = some m → m.body = some b →
      DeltaConst E' r m b ∧ exprClosedAt 0 b = true := by
  induction hmem with
  | nil _ => exact hE
  | @cons E₀ r₀ m₀ _ _ hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      refine ih (fun r m b hm hb => ?_)
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        rw [hnobody] at hb
        cases hb
      · rw [members_extend_ne E₀ r₀ m₀ r hrr] at hm
        obtain ⟨hd, hcl⟩ := hE r m b hm hb
        exact ⟨⟨members_extend_preserved hfresh r m hd.1, hd.2⟩, hcl⟩

/-- In any well-formed environment `EnvWfT E`, every member `m` with `m.body = some b` is a
    closed `DeltaConst`. -/
theorem envWfT_member_body_closed {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ r m b, E.members r = some m → m.body = some b →
      DeltaConst E r m b ∧ exprClosedAt 0 b = true := by
  induction hW with
  | empty => intro _ _ _ hm _; exact Option.noConfusion hm
  | @«axiom» _ E₀ r₀ A _ _ hfresh _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        cases hb
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm
        obtain ⟨hd, hcl⟩ := ih r m b hm hb
        exact ⟨⟨members_extend_preserved hfresh r m hd.1, hd.2⟩, hcl⟩
  | @definition E₀ r₀ A v _ _ hfresh _ hv _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        have hm' := hm
        rw [members_extend_eq] at hm'
        cases hm'
        cases hb
        exact ⟨⟨hm, rfl, (by rintro ⟨⟩), (by rintro ⟨⟩)⟩, hasTyT_exprClosedAt hv⟩
      · have hm' := hm
        rw [members_extend_ne E₀ r₀ _ r hrr] at hm'
        obtain ⟨hd, hcl⟩ := ih r m b hm' hb
        exact ⟨⟨hm, hd.2⟩, hcl⟩
  | @thm E₀ r₀ A p _ hfresh _ hp _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        have hm' := hm
        rw [members_extend_eq] at hm'
        cases hm'
        cases hb
        exact ⟨⟨hm, rfl, (by rintro ⟨⟩), (by rintro ⟨⟩)⟩, hasTyT_exprClosedAt hp⟩
      · have hm' := hm
        rw [members_extend_ne E₀ r₀ _ r hrr] at hm'
        obtain ⟨hd, hcl⟩ := ih r m b hm' hb
        exact ⟨⟨hm, hd.2⟩, hcl⟩
  | @«opaque» E₀ r₀ A v _ _ hfresh _ hv _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        have hm' := hm
        rw [members_extend_eq] at hm'
        cases hm'
        cases hb
        exact ⟨⟨hm, rfl, (by rintro ⟨⟩), (by rintro ⟨⟩)⟩, hasTyT_exprClosedAt hv⟩
      · have hm' := hm
        rw [members_extend_ne E₀ r₀ _ r hrr] at hm'
        obtain ⟨hd, hcl⟩ := ih r m b hm' hb
        exact ⟨⟨hm, hd.2⟩, hcl⟩
  | group _ _ _ _ _ _ _ _ _ _ _ hmem ih =>
      exact groupMembersT_body_some hmem ih

/-- Soundness of `WhStep.delta` in `ApproxDI` at every `EnvWfT E` and every valuation `ρ : EnvI`. -/
theorem semEqDI_of_whStep_delta {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m) (hbody : m.body = some b)
    (ρ : EnvI) :
    SemEqDI E ρ (.const r ls) (instantiateLevels ls b) := by
  obtain ⟨hdelta, hcl⟩ := envWfT_member_body_closed hW r m b hres hbody
  exact semEqDI_delta hdelta hcl

/-- Soundness of `ConvT.delta` at `EnvI.bot` without any environment well-formedness premise
    (using `htr : transparent m.mclass = true` directly). -/
theorem semEqDI_of_convT_delta_bot {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (htr : transparent m.mclass = true) :
    SemEqDI E EnvI.bot (.const r ls) (instantiateLevels ls b) :=
  semEqDI_delta_bot (deltaConst_of_transparent hres hbody htr)

/-- Soundness of `ConvT.delta` at every valuation `ρ : EnvI` under `EnvWfT E`. -/
theorem semEqDI_of_convT_delta {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (ρ : EnvI) :
    SemEqDI E ρ (.const r ls) (instantiateLevels ls b) :=
  semEqDI_of_whStep_delta hW hres hbody ρ

/-! ## §6. Branch Uniqueness, `IotaDetT` / `IotaDetU`, and Legacy Open Schema -/

/-- Any two `IotaWitnessS` witnesses for the same recursor `recRef` have the same `recMember`
    and the same `preMajor.length`. -/
theorem iotaWitnessS_preMajor_length_eq {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E)
    (hrec : w₁.recRef = w₂.recRef) :
    w₁.recMember = w₂.recMember ∧ w₁.preMajor.length = w₂.preMajor.length := by
  have hm : w₁.recMember = w₂.recMember := by
    have a := w₁.hrec
    have b := w₂.hrec
    rw [← hrec] at b
    exact Option.some.inj (a.symm.trans b)
  refine ⟨hm, ?_⟩
  have h₁ := w₁.hpre
  have h₂ := w₂.hpre
  have hn₁ := w₁.hnmin
  have hn₂ := w₂.hnmin
  rw [hm] at hn₁
  omega

/-- Branch uniqueness for `IotaWitnessS`: any two witnesses `w₁, w₂ : IotaWitnessS E` at the same
    `(recRef, ctorRef)` pair agree on all declaration-determined counts, field shapes, and open
    computation schema (`w₁.schema = w₂.schema`). -/
theorem iotaWitnessS_same_branch {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E)
    (hrec : w₁.recRef = w₂.recRef) (hctor : w₁.ctorRef = w₂.ctorRef) :
    w₁.nparams = w₂.nparams ∧ w₁.nindices = w₂.nindices ∧ w₁.nMinors = w₂.nMinors ∧
      w₁.ctorIdx = w₂.ctorIdx ∧ w₁.preMajor.length = w₂.preMajor.length ∧
      w₁.fields.length = w₂.fields.length ∧ w₁.shapes = w₂.shapes ∧ w₁.schema = w₂.schema := by
  obtain ⟨hmemr, hpreLen⟩ := iotaWitnessS_preMajor_length_eq w₁ w₂ hrec
  have hmemc : w₁.ctorMember = w₂.ctorMember := by
    have a := w₁.hctor
    have b := w₂.hctor
    rw [← hctor] at b
    exact Option.some.inj (a.symm.trans b)
  have hpeelEq : w₁.ctorDoms = w₂.ctorDoms ∧ w₁.ctorResult = w₂.ctorResult := by
    have a := w₁.hpeel
    have b := w₂.hpeel
    rw [w₁.hnpar] at a
    rw [w₂.hnpar, ← hmemc] at b
    have eq := Option.some.inj (a.symm.trans b)
    exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  have hfam : w₁.familyRef = w₂.familyRef := by
    have hf₁ := w₁.hfamApp
    have hf₂ := w₂.hfamApp
    rw [← hpeelEq.2] at hf₂
    unfold isFamilyApp at hf₁ hf₂
    split at hf₁
    · rename_i r ls' args heq
      rw [heq] at hf₂
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf₁ hf₂
      exact hf₁.1.symm.trans hf₂.1
    · cases hf₁
  have hmemf : w₁.famMember = w₂.famMember := by
    have a := w₁.hfam
    have b := w₂.hfam
    rw [← hfam] at b
    exact Option.some.inj (a.symm.trans b)
  have hnmin : w₁.nMinors = w₂.nMinors := by
    have a := w₁.hrecIdx
    have b := w₂.hrecIdx
    rw [← hrec, ← hfam] at b
    have := a.symm.trans b
    omega
  have hrecBodyEq : w₁.recBody = w₂.recBody := by
    have a := w₁.hpeelRec
    have b := w₂.hpeelRec
    rw [w₁.hnmin] at a
    rw [w₂.hnmin, ← hmemr] at b
    exact congrArg Prod.snd (Option.some.inj (a.symm.trans b))
  have hnidx : w₁.nindices = w₂.nindices := by
    have eq := w₁.hrecBody.symm.trans (hrecBodyEq.trans w₂.hrecBody)
    have s₁ := appsSpine_foldApps
      (.bvar (w₁.nMinors + w₁.nindices + 1) : Expr Nat)
      ((List.range w₁.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
    have s₂ := appsSpine_foldApps
      (.bvar (w₂.nMinors + w₂.nindices + 1) : Expr Nat)
      ((List.range w₂.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
    simp only [appsSpine_bvar, List.nil_append] at s₁ s₂
    have hs := congrArg appsSpine eq
    rw [s₁, s₂] at hs
    injection hs with hhead _
    injection hhead with hidx
    omega
  have hnpar : w₁.nparams = w₂.nparams := by
    have a := w₁.hnidx
    have b := w₂.hnidx
    rw [hmemf] at a
    omega
  have hfldsLen : w₁.fields.length = w₂.fields.length := by
    have a := w₁.hnpar
    have b := w₂.hnpar
    rw [hmemc] at a
    omega
  have hidx : w₁.ctorIdx = w₂.ctorIdx := by
    have a := w₁.hctorIdx
    have b := w₂.hctorIdx
    rw [← hctor, ← hfam] at b
    have := a.symm.trans b
    omega
  have hshapes : w₁.shapes = w₂.shapes := by
    have a := w₁.hshapes
    have b := w₂.hshapes
    rw [← hfam, ← hmemf, ← hnpar, ← hnidx, ← hpeelEq.1] at b
    exact fieldShapesFuel_agree E a b
  have hschema : w₁.schema = w₂.schema := by
    have a := w₁.hschema
    have b := w₂.hschema
    rw [← hrec, ← hmemr, ← hfldsLen, ← hnidx, ← hnmin, ← hidx, ← hnpar, ← hshapes,
      ← hpeelEq.1, ← hpeelEq.2] at b
    exact iotaOpenRhs_agree E a b
  exact ⟨hnpar, hnidx, hnmin, hidx, hpreLen, hfldsLen, hshapes, hschema⟩

/-- Determinism of `DerivedIotaT`: any two typed-root ι witnesses with the same left-hand side
    have the same right-hand side. -/
theorem iotaDetT {E : ResolvedEnv} {lhs rhs₁ rhs₂ : Expr Nat}
    (h₁ : DerivedIotaT E lhs rhs₁) (h₂ : DerivedIotaT E lhs rhs₂) : rhs₁ = rhs₂ := by
  have unpack : ∀ {l r : Expr Nat}, DerivedIotaT E l r →
      ∃ w : IotaWitnessS E, l = iotaLhsOfS w ∧ r = iotaRhsOfS w := by
    intro l r h
    cases h with
    | of w => exact ⟨w, rfl, rfl⟩
  obtain ⟨w₁, hl₁, hr₁⟩ := unpack h₁
  obtain ⟨w₂, hl₂, hr₂⟩ := unpack h₂
  subst hr₁; subst hr₂
  have hL : iotaLhsOfS w₁ = iotaLhsOfS w₂ := hl₁.symm.trans hl₂
  unfold iotaLhsOfS recCall at hL
  have s₁ := appsSpine_foldApps (.const w₁.recRef w₁.ls)
    (w₁.preMajor ++ [foldApps (.const w₁.ctorRef w₁.lsC) (w₁.ctorParams ++ w₁.fields)])
  have s₂ := appsSpine_foldApps (.const w₂.recRef w₂.ls)
    (w₂.preMajor ++ [foldApps (.const w₂.ctorRef w₂.lsC) (w₂.ctorParams ++ w₂.fields)])
  simp only [appsSpine_const, List.nil_append] at s₁ s₂
  have hs := congrArg appsSpine hL
  rw [s₁, s₂] at hs
  injection hs with hhead hargs
  injection hhead with hrec hls
  obtain ⟨hpre, hmaj⟩ := list_snoc_inj hargs
  have sc₁ := appsSpine_foldApps (.const w₁.ctorRef w₁.lsC) (w₁.ctorParams ++ w₁.fields)
  have sc₂ := appsSpine_foldApps (.const w₂.ctorRef w₂.lsC) (w₂.ctorParams ++ w₂.fields)
  simp only [appsSpine_const, List.nil_append] at sc₁ sc₂
  have hmajS := congrArg appsSpine hmaj
  rw [sc₁, sc₂] at hmajS
  injection hmajS with hchead hctorArgs
  injection hchead with hctor _
  obtain ⟨hnpar, _, _, _, _, _, _, hschema⟩ := iotaWitnessS_same_branch w₁ w₂ hrec hctor
  have hfields : w₁.fields = w₂.fields := by
    have hlen : w₁.ctorParams.length = w₂.ctorParams.length := by
      rw [w₁.hctorParams, w₂.hctorParams, hnpar]
    exact (List.append_inj hctorArgs hlen).2
  unfold iotaRhsOfS
  rw [hpre, hfields, hls, hschema]

/-- At any well-formed environment `EnvWfT E`, every union ι step `DerivedIotaU E lhs rhs`
    lifts to a `DerivedIotaT E lhs rhs` step at the same endpoints. -/
theorem derivedIotaT_of_derivedIotaU_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {lhs rhs : Expr Nat} (h : DerivedIotaU E lhs rhs) :
    Nonempty (DerivedIotaT E lhs rhs) :=
  match h with
  | .ofU w => derivedIotaT_of_iotaWitness_envWfT hW w
  | .ofUS w => ⟨.of w⟩

/-- Discharge of the `IotaDetU E` front (`RcicNativeValleyFronts`) at every `EnvWfT E`:
    the union ι relation is deterministic across both `.ofU` and `.ofUS` arms. -/
theorem iotaDetU_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : IotaDetU E := by
  intro l r₁ r₂ h₁ h₂
  obtain ⟨t₁⟩ := derivedIotaT_of_derivedIotaU_envWfT hW h₁
  obtain ⟨t₂⟩ := derivedIotaT_of_derivedIotaU_envWfT hW h₂
  exact iotaDetT t₁ t₂

/-- The open legacy computation schema before redex-level argument instantiation. -/
def legacyOpenRhs (rec minor : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (fields : List (Expr Nat)) (kinds : List RecKind)
    (tel : Expr Nat) : Expr Nat :=
  foldApps minor (rhsArgs rec preMajor nparams nMinors fields kinds tel)

/-- The canonical open legacy schema of a legacy `IotaWitness E` in the equation context
    `preMajorBvars ++ fieldBvars`. -/
def legacySchemaOf {E : ResolvedEnv} (w : IotaWitness E) : Expr Nat :=
  legacyOpenRhs (.const w.recRef (canonRecLevels w.recMember.arity))
    (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
    (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
    w.nparams w.nMinors (fieldBvars w.fields.length) w.kinds
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))

/-- `rhsArgs` commutes with `sigmaInst` along any telescope satisfying `isPiTel` and
    `DirectFamHead`. -/
theorem rhsArgs_sigma {fam np nMinors : Nat} (ls : List Level) (L : List (Expr Nat))
    {R R' : Expr Nat} {P P' : List (Expr Nat)}
    (hR : sigmaInst ls L R = R') (hP : P.map (sigmaInst ls L) = P') :
    (ks : List RecKind) → (fs : List (Expr Nat)) → (tel : Expr Nat) →
    fs.length = ks.length → isPiTel ks.length tel = true → DirectFamHead fam ks tel →
    (rhsArgs R P np nMinors fs ks tel).map (sigmaInst ls L) =
      rhsArgs R' P' np nMinors (fs.map (sigmaInst ls L)) ks (sigmaInst ls L tel)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, hlen, _, _ => by cases hlen
  | _ :: _, [], _, hlen, _, _ => by cases hlen
  | .plain :: ks, f :: fs, .pi A B, hlen, htel, hd => by
      simp only [List.length_cons] at hlen
      simp only [List.length_cons, isPiTel] at htel
      simp only [rhsArgs, List.map_cons, sigmaInst_pi]
      congr 1
      rw [← sigmaInst_instantiate0]
      exact rhsArgs_sigma ls L hR hP ks fs (instantiate0 f B) (Nat.succ.inj hlen)
        (isPiTel_instantiate 0 f ks.length B htel)
        (directFamHead_instantiate fam 0 f ks B htel hd)
  | .directRec :: ks, f :: fs, .pi A B, hlen, htel, hd => by
      simp only [List.length_cons] at hlen
      simp only [List.length_cons, isPiTel] at htel
      obtain ⟨⟨ls'', hA⟩, hB⟩ := hd
      simp only [rhsArgs, List.map_cons, sigmaInst_pi]
      congr 1
      rw [sigmaInst_recCallField ls L hR hP np nMinors f A hA, ← sigmaInst_instantiate0]
      congr 1
      exact rhsArgs_sigma ls L hR hP ks fs (instantiate0 f B) (Nat.succ.inj hlen)
        (isPiTel_instantiate 0 f ks.length B htel)
        (directFamHead_instantiate fam 0 f ks B htel hB)
  | _ :: _, _ :: _, .bvar _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .sort _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .const _ _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .app _ _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .lam _ _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .letE _ _ _, _, htel, _ => by cases htel
  | _ :: _, _ :: _, .lit _, _, htel, _ => by cases htel

/-- Every legacy `IotaWitness E` reduct `iotaRhsOf w` is the `instPrefix (w.preMajor ++ w.fields)`
    instance of `instantiateLevels w.ls (legacySchemaOf w)` — unconditionally for every `E`. -/
theorem iotaRhsOf_eq_instPrefix_legacySchema {E : ResolvedEnv} (w : IotaWitness E) :
    instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls (legacySchemaOf w)) =
      iotaRhsOf w := by
  change sigmaInst w.ls (w.preMajor ++ w.fields) (legacySchemaOf w) = iotaRhsOf w
  unfold legacySchemaOf legacyOpenRhs iotaRhsOf
  have hdl : w.ctorDoms.length = w.nparams + w.fields.length := peelPis_length _ _ w.hpeel
  have hkl : w.kinds.length = (w.ctorDoms.drop w.nparams).length := by
    rw [List.length_drop, hdl, w.hlen]; omega
  have htel0 : isPiTel w.kinds.length
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
    apply isPiTel_lift
    rw [ctorFieldTelRaw, ← policyPi_eq_foldr, hkl]
    exact isPiTel_policyPi _ _
  have hdfh : DirectFamHead w.familyRef w.kinds
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) := by
    apply directFamHead_lift
    · rw [ctorFieldTelRaw, ← policyPi_eq_foldr, hkl]
      exact isPiTel_policyPi _ _
    · rw [ctorFieldTelRaw, ← policyPi_eq_foldr]
      exact directFamHead_of_analyzeFields w.familyRef _ _ w.hkinds
  have hfbLen : (fieldBvars w.fields.length).length = w.kinds.length := by
    simp only [fieldBvars, List.length_map, List.length_reverse, List.length_range, w.hlen]
  rw [sigmaInst_foldApps, sigmaInst_minor w.ls w.preMajor w.fields w.hpre w.hidx w.hminor,
    rhsArgs_sigma w.ls (w.preMajor ++ w.fields)
      (sigmaInst_recHead w.ls _ w.recRef w.recMember.arity w.hlsLen)
      (sigmaInst_preMajorBvars w.ls w.preMajor w.fields w.nparams w.nMinors w.nindices w.hpre)
      w.kinds (fieldBvars w.fields.length) _ hfbLen htel0 hdfh,
    sigmaInst_fieldBvars, sigmaInst_tel0]

/-! ## §7. Soundness of ι (`DerivedIotaT`, `DerivedIota`, `DerivedIotaU`, `ConvT.iota`) -/

/-- One-step compact application: how a function compact `d` applies to an argument expression `x`
    to produce an output compact `c`. -/
inductive AppCpt (E : ResolvedEnv) (ρ : EnvI) : CptI → Expr Nat → CptI → Prop
  | bot (d : CptI) (x : Expr Nat) : AppCpt E ρ d x .bot
  | app {g : List (List CptI × CptI)} {s : List CptI × CptI} {x : Expr Nat}
      (hs : s ∈ g) (hx : ∀ u ∈ s.1, ApproxDI E ρ x u) :
      AppCpt E ρ (.lam g) x s.2
  | appSpine {r : Nat} {args : List CptI} {x : Expr Nat} {u : CptI}
      (hx : ApproxDI E ρ x u) :
      AppCpt E ρ (.spine r args) x (.spine r (args ++ [u]))

theorem approxDI_app_iff_appCpt (E : ResolvedEnv) (ρ : EnvI) (f x : Expr Nat) (c : CptI) :
    ApproxDI E ρ (.app f x) c ↔ ∃ d, ApproxDI E ρ f d ∧ AppCpt E ρ d x c := by
  constructor
  · intro h
    rcases approxDI_app_inv h with rfl | ⟨g, s, rfl, hf, hs, hx⟩ | ⟨r, args, u, rfl, hf, hx⟩
    · exact ⟨.bot, .bot ρ f, .bot .bot x⟩
    · exact ⟨.lam g, hf, .app hs hx⟩
    · exact ⟨.spine r args, hf, .appSpine hx⟩
  · rintro ⟨d, hf, hstep⟩
    cases hstep with
    | bot => exact .bot ρ (.app f x)
    | app hs hx => exact .app hf hs hx
    | appSpine hx => exact .appSpine hf hx

/-- Multi-step compact application along an argument list `xs : List (Expr Nat)`. -/
inductive FoldAppCpt (E : ResolvedEnv) (ρ : EnvI) : CptI → List (Expr Nat) → CptI → Prop
  | bot (d : CptI) (xs : List (Expr Nat)) : FoldAppCpt E ρ d xs .bot
  | nil (c : CptI) : FoldAppCpt E ρ c [] c
  | cons {d d' c : CptI} {x : Expr Nat} {xs : List (Expr Nat)}
      (hstep : AppCpt E ρ d x d') (hrest : FoldAppCpt E ρ d' xs c) :
      FoldAppCpt E ρ d (x :: xs) c

/-- `ApproxDI` on `foldApps f xs` factors into a single compact `d` for `f` followed by
    `FoldAppCpt E ρ d xs c`. -/
theorem approxDI_foldApps_iff (E : ResolvedEnv) (ρ : EnvI) (f : Expr Nat)
    (xs : List (Expr Nat)) (c : CptI) :
    ApproxDI E ρ (foldApps f xs) c ↔ ∃ d, ApproxDI E ρ f d ∧ FoldAppCpt E ρ d xs c := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps]
      constructor
      · intro h; exact ⟨c, h, .nil c⟩
      · rintro ⟨d, hd, hfold⟩
        cases hfold with
        | bot => exact .bot ρ f
        | nil => exact hd
  | cons x xs ih =>
      simp only [foldApps]
      rw [ih]
      constructor
      · rintro ⟨d', hfx, hrest⟩
        rw [approxDI_app_iff_appCpt] at hfx
        obtain ⟨d, hf, hstep⟩ := hfx
        exact ⟨d, hf, .cons hstep hrest⟩
      · rintro ⟨d, hf, hfold⟩
        cases hfold with
        | bot => exact ⟨.bot, .bot ρ (.app f x), .bot .bot xs⟩
        | cons hstep hrest =>
            exact ⟨_, (approxDI_app_iff_appCpt E ρ f x _).mpr ⟨d, hf, hstep⟩, hrest⟩

theorem foldAppCpt_bot_inv {E : ResolvedEnv} {ρ : EnvI} {xs : List (Expr Nat)} {c : CptI}
    (h : FoldAppCpt E ρ .bot xs c) : c = .bot := by
  induction xs with
  | nil =>
      cases h <;> rfl
  | cons x xs ih =>
      cases h with
      | bot => rfl
      | cons hstep hrest =>
          cases hstep with
          | bot => exact ih hrest

/-- Peeling `curryStep uss c₀` across an argument spine `xs` of equal length. -/
theorem foldAppCpt_curryStep_iff {E : ResolvedEnv} {ρ : EnvI}
    {uss : List (List CptI)} {xs : List (Expr Nat)}
    (hlen : uss.length = xs.length) {c₀ c : CptI} :
    FoldAppCpt E ρ (curryStep uss c₀) xs c ↔
      c = .bot ∨ (ApproxArgsDemand E ρ xs uss ∧ c = c₀) := by
  induction uss generalizing xs c₀ c with
  | nil =>
      cases xs with
      | nil =>
          simp only [curryStep]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | nil => exact Or.inr ⟨.nil, rfl⟩
          · rintro (rfl | ⟨_, rfl⟩)
            · exact .bot _ []
            · exact .nil _
      | cons _ _ => cases hlen
  | cons us uss ih =>
      cases xs with
      | nil => cases hlen
      | cons x xs =>
          simp only [List.length_cons] at hlen
          simp only [curryStep]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | cons hstep hrest =>
                cases hstep with
                | bot => exact Or.inl (foldAppCpt_bot_inv hrest)
                | app hs hx =>
                    have hs' : _ = (us, curryStep uss c₀) := List.mem_singleton.mp hs
                    cases hs'
                    rcases (ih (Nat.succ.inj hlen)).mp hrest with rfl | ⟨hxs, rfl⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨.cons hx hxs, rfl⟩
          · rintro (rfl | ⟨hargs, rfl⟩)
            · exact .bot _ _
            · cases hargs with
              | cons hx hxs =>
                  exact .cons (.app (List.mem_singleton.mpr rfl) hx)
                    ((ih (Nat.succ.inj hlen)).mpr (Or.inr ⟨hxs, rfl⟩))

/-- Pointwise single-compact approximation of an argument spine `xs` by a compact vector `us`. -/
inductive ApproxSpineArgs (E : ResolvedEnv) (ρ : EnvI) :
    List (Expr Nat) → List CptI → Prop
  | nil : ApproxSpineArgs E ρ [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {u : CptI} {us : List CptI}
      (hx : ApproxDI E ρ x u) (hxs : ApproxSpineArgs E ρ xs us) :
      ApproxSpineArgs E ρ (x :: xs) (u :: us)

theorem ApproxSpineArgs.length_eq {E : ResolvedEnv} {ρ : EnvI}
    {xs : List (Expr Nat)} {us : List CptI} (h : ApproxSpineArgs E ρ xs us) :
    us.length = xs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem approxSpineArgs_cons_iff {E : ResolvedEnv} {ρ : EnvI}
    (x : Expr Nat) (xs : List (Expr Nat)) (u : CptI) (us : List CptI) :
    ApproxSpineArgs E ρ (x :: xs) (u :: us) ↔
      ApproxDI E ρ x u ∧ ApproxSpineArgs E ρ xs us := by
  constructor
  · intro h; cases h with | cons hx hxs => exact ⟨hx, hxs⟩
  · rintro ⟨hx, hxs⟩; exact .cons hx hxs

theorem approxSpineArgs_replicate_bot {E : ResolvedEnv} {ρ : EnvI} :
    (xs : List (Expr Nat)) → ApproxSpineArgs E ρ xs (List.replicate xs.length .bot)
  | [] => .nil
  | x :: xs => .cons (.bot ρ x) (approxSpineArgs_replicate_bot xs)

theorem approxSpineArgs_append_iff {E : ResolvedEnv} {ρ : EnvI} :
    (xs ys : List (Expr Nat)) → (us vs : List CptI) →
    xs.length = us.length →
    (ApproxSpineArgs E ρ (xs ++ ys) (us ++ vs) ↔
      ApproxSpineArgs E ρ xs us ∧ ApproxSpineArgs E ρ ys vs)
  | [], ys, [], vs, _ => by
      simp only [List.nil_append]
      exact ⟨fun h => ⟨.nil, h⟩, fun h => h.2⟩
  | [], _, _ :: _, _, hlen => by cases hlen
  | _ :: _, _, [], _, hlen => by cases hlen
  | x :: xs, ys, u :: us, vs, hlen => by
      simp only [List.length_cons] at hlen
      simp only [List.cons_append, approxSpineArgs_cons_iff]
      rw [approxSpineArgs_append_iff xs ys us vs (Nat.succ.inj hlen)]
      exact ⟨fun ⟨hx, hxs, hys⟩ => ⟨⟨hx, hxs⟩, hys⟩,
        fun ⟨⟨hx, hxs⟩, hys⟩ => ⟨hx, hxs, hys⟩⟩

theorem foldAppCpt_spine_iff {E : ResolvedEnv} {ρ : EnvI} (r : Nat) :
    (xs : List (Expr Nat)) → (args : List CptI) → (c : CptI) →
    (FoldAppCpt E ρ (.spine r args) xs c ↔
      c = .bot ∨ ∃ us, ApproxSpineArgs E ρ xs us ∧ c = .spine r (args ++ us))
  | [], args, c => by
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | nil => exact Or.inr ⟨[], .nil, by simp⟩
      · rintro (rfl | ⟨us, hus, rfl⟩)
        · exact .bot _ _
        · cases hus
          simp only [List.append_nil]
          exact .nil _
  | x :: xs, args, c => by
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | cons hstep hrest =>
            cases hstep with
            | bot => exact Or.inl (foldAppCpt_bot_inv hrest)
            | @appSpine _ _ _ u hx =>
                rcases (foldAppCpt_spine_iff r xs (args ++ [u]) c).mp hrest with
                  rfl | ⟨us, hxs, rfl⟩
                · exact Or.inl rfl
                · rw [List.append_assoc]
                  exact Or.inr ⟨u :: us, .cons hx hxs, rfl⟩
      · rintro (rfl | ⟨us₀, hus, rfl⟩)
        · exact .bot _ _
        · cases hus with
          | @cons _ _ u us hx hxs =>
              refine .cons (.appSpine hx) ((foldAppCpt_spine_iff r xs (args ++ [u]) _).mpr ?_)
              refine Or.inr ⟨us, hxs, ?_⟩
              simp [List.append_assoc]

/-- Exact characterization of `ApproxDI` on a rigid constant application `foldApps (.const r ls) xs`. -/
theorem approxDI_foldApps_rigid_iff {E : ResolvedEnv} {ρ : EnvI} {r : Nat} (ls : List Level)
    (hrigid : RigidConst E r) (xs : List (Expr Nat)) (c : CptI) :
    ApproxDI E ρ (foldApps (.const r ls) xs) c ↔
      c = .bot ∨ ∃ us, ApproxSpineArgs E ρ xs us ∧ c = .spine r us := by
  rw [approxDI_foldApps_iff]
  constructor
  · rintro ⟨d, hd, hfold⟩
    rcases approxDI_rigid_const_inv hrigid hd with rfl | rfl
    · exact Or.inl (foldAppCpt_bot_inv hfold)
    · simpa using (foldAppCpt_spine_iff r xs [] c).mp hfold
  · rintro (rfl | ⟨us, hus, rfl⟩)
    · exact ⟨.bot, .bot ρ (.const r ls), .bot .bot xs⟩
    · refine ⟨.spine r [], .const ρ r ls hrigid, ?_⟩
      exact (foldAppCpt_spine_iff r xs [] (.spine r us)).mpr (Or.inr ⟨us, hus, rfl⟩)

theorem fieldDemandVectors_length :
    ∀ {us_fields : List (List CptI)} {vec : List CptI},
      vec ∈ fieldDemandVectors us_fields → vec.length = us_fields.length
  | [], _, h => (List.not_mem_nil _ h).elim
  | us :: uss, vec, h => by
      simp only [fieldDemandVectors, List.mem_append, List.mem_map] at h
      rcases h with ⟨u, _, rfl⟩ | ⟨vec', hvec', rfl⟩
      · simp
      · simp [fieldDemandVectors_length hvec']

/-- `fieldDemandVectors` tests `ApproxArgsDemand E ρ fields us_fields` via `ApproxSpineArgs`. -/
theorem forall_fieldDemandVectors_iff {E : ResolvedEnv} {ρ : EnvI} :
    (fields : List (Expr Nat)) → (us_fields : List (List CptI)) →
    fields.length = us_fields.length →
    ((∀ vec ∈ fieldDemandVectors us_fields, ApproxSpineArgs E ρ fields vec) ↔
      ApproxArgsDemand E ρ fields us_fields)
  | [], [], _ => by
      simp only [fieldDemandVectors]
      exact ⟨fun _ => .nil, fun _ _ h => (List.not_mem_nil _ h).elim⟩
  | [], _ :: _, hlen => by cases hlen
  | _ :: _, [], hlen => by cases hlen
  | f :: fs, us :: uss, hlen => by
      simp only [List.length_cons] at hlen
      have hlen' : fs.length = uss.length := Nat.succ.inj hlen
      simp only [fieldDemandVectors, List.mem_append, List.mem_map]
      constructor
      · intro hall
        refine .cons (fun u hu => ?_) ((forall_fieldDemandVectors_iff fs uss hlen').mp (fun vec hvec => ?_))
        · have h := hall (u :: List.replicate uss.length .bot) (Or.inl ⟨u, hu, rfl⟩)
          exact ((approxSpineArgs_cons_iff f fs u _).mp h).1
        · have h := hall (.bot :: vec) (Or.inr ⟨vec, hvec, rfl⟩)
          exact ((approxSpineArgs_cons_iff f fs .bot vec).mp h).2
      · intro hargs vec hmem
        cases hargs with
        | cons hf hfs =>
            rcases hmem with ⟨u, hu, rfl⟩ | ⟨vec', hvec', rfl⟩
            · rw [← hlen']
              exact .cons (hf u hu) (approxSpineArgs_replicate_bot fs)
            · exact .cons (.bot ρ f)
                ((forall_fieldDemandVectors_iff fs uss hlen').mpr hfs vec' hvec')

/-- Forward direction of `ctorDemand`: if `ctorRef = ctorRef'`, `ctorParams.length = nparams`,
    and `ApproxArgsDemand E ρ fields us_fields`, then the constructor spine satisfies every
    demand in `ctorDemand ctorRef nparams us_fields`. -/
theorem ctorDemand_intro {E : ResolvedEnv} {ρ : EnvI} {ctorRef : Nat} (lsC : List Level)
    (hrigid : RigidConst E ctorRef) {ctorParams fields : List (Expr Nat)} {nparams : Nat}
    (hparams : ctorParams.length = nparams) {us_fields : List (List CptI)}
    (hflds : ApproxArgsDemand E ρ fields us_fields) :
    ∀ v ∈ ctorDemand ctorRef nparams us_fields,
      ApproxDI E ρ (foldApps (.const ctorRef lsC) (ctorParams ++ fields)) v := by
  have hflen : fields.length = us_fields.length := hflds.length_eq.symm
  have hrepP : ApproxSpineArgs E ρ ctorParams (List.replicate nparams .bot) := by
    rw [← hparams]; exact approxSpineArgs_replicate_bot ctorParams
  intro v hv
  simp only [ctorDemand, List.mem_cons, List.mem_map] at hv
  rw [approxDI_foldApps_rigid_iff lsC hrigid]
  rcases hv with rfl | ⟨vec, hvec, rfl⟩
  · refine Or.inr ⟨_, ?_, rfl⟩
    rw [approxSpineArgs_append_iff ctorParams fields _ _ (by simp [hparams])]
    refine ⟨hrepP, ?_⟩
    rw [← hflen]
    exact approxSpineArgs_replicate_bot fields
  · refine Or.inr ⟨_, ?_, rfl⟩
    rw [approxSpineArgs_append_iff ctorParams fields _ _ (by simp [hparams])]
    exact ⟨hrepP, (forall_fieldDemandVectors_iff fields us_fields hflen).mpr hflds vec hvec⟩

/-- Inverse of `ctorDemand`: if a constructor spine with head `ctorRef'` satisfies
    `ctorDemand ctorRef nparams us_fields`, then `ctorRef = ctorRef'`, and whenever
    `ctorParams.length = nparams` and `fields.length = us_fields.length`,
    `ApproxArgsDemand E ρ fields us_fields` holds. -/
theorem ctorDemand_inv {E : ResolvedEnv} {ρ : EnvI} {ctorRef ctorRef' nparams : Nat}
    {lsC : List Level} (hrigid : RigidConst E ctorRef') {ctorParams fields : List (Expr Nat)}
    {us_fields : List (List CptI)}
    (h : ∀ v ∈ ctorDemand ctorRef nparams us_fields,
      ApproxDI E ρ (foldApps (.const ctorRef' lsC) (ctorParams ++ fields)) v) :
    ctorRef = ctorRef' ∧
      (ctorParams.length = nparams → fields.length = us_fields.length →
        ApproxArgsDemand E ρ fields us_fields) := by
  have htag := h (.spine ctorRef (List.replicate nparams .bot ++ List.replicate us_fields.length .bot))
    (List.mem_cons_self _ _)
  rw [approxDI_foldApps_rigid_iff lsC hrigid] at htag
  rcases htag with hbot | ⟨us₀, _, heq⟩
  · cases hbot
  · injection heq with hctor _
    refine ⟨hctor, fun hparams hflen => ?_⟩
    apply (forall_fieldDemandVectors_iff fields us_fields hflen).mp
    intro vec hvec
    have hv := h (.spine ctorRef (List.replicate nparams .bot ++ vec))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vec, hvec, rfl⟩))
    rw [approxDI_foldApps_rigid_iff lsC hrigid] at hv
    rcases hv with hbot | ⟨us, hus, heq'⟩
    · cases hbot
    · injection heq' with _ husEq
      subst husEq
      exact ((approxSpineArgs_append_iff ctorParams fields _ _ (by simp [hparams])).mp hus).2

/-- **Unconditional ι-soundness for `IotaWitnessS`**: for every environment `E : ResolvedEnv`,
    every shape witness `w : IotaWitnessS E`, and every variable valuation `ρ : EnvI`, the
    recursor redex `iotaLhsOfS w` and its contractum `iotaRhsOfS w` have the exact same
    approximations (`SemEqDI E ρ (iotaLhsOfS w) (iotaRhsOfS w)`). -/
theorem approxDI_iotaS {E : ResolvedEnv} (w : IotaWitnessS E) (ρ : EnvI) :
    SemEqDI E ρ (iotaLhsOfS w) (iotaRhsOfS w) := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  have hrigidCtor : RigidConst E w.ctorRef := rigidConst_of_ctor w.hctor w.hctorK
  intro c
  constructor
  · intro hlhs
    unfold iotaLhsOfS recCall at hlhs
    rw [approxDI_foldApps_iff] at hlhs
    obtain ⟨d, hd, hfold⟩ := hlhs
    rcases approxDI_recursor_const_inv w.hrec w.hrecK hd with
      rfl | ⟨w', us_pre, us_fields, c₀, hrecEq, hpreLen, hfldsLen, hschema', rfl⟩
    · rw [foldAppCpt_bot_inv hfold]
      exact .bot ρ (iotaRhsOfS w)
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length =
          (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCpt_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, hmajArgs⟩ :=
          (ApproxArgsDemand.append_iff w.preMajor _ _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, hmajEq⟩ := List.append_inj hsplitEq hlenPre
        cases hmajArgs with
        | cons hmaj _ =>
            cases hmajEq
            obtain ⟨hctorEq, hfldsFn⟩ := ctorDemand_inv hrigidCtor hmaj
            obtain ⟨hnparEq, _, _, _, _, hfldsLenEq, _, hschemaEq⟩ :=
              iotaWitnessS_same_branch w' w hrecEq hctorEq
            have hfldsArgs : ApproxArgsDemand E ρ w.fields us_fields :=
              hfldsFn (w.hctorParams.trans hnparEq.symm) (hfldsLenEq.symm.trans hfldsLen.symm)
            rw [hschemaEq] at hschema'
            unfold iotaRhsOfS
            rw [approxDI_instPrefix_closed_iff E ρ _ _ hclSchema]
            exact ⟨us_pre ++ us_fields,
              (ApproxArgsDemand.append_iff _ _ _).mpr ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩,
              hschema'⟩
  · intro hrhs
    unfold iotaRhsOfS at hrhs
    rw [approxDI_instPrefix_closed_iff E ρ _ _ hclSchema] at hrhs
    obtain ⟨uss, hargs, hschema⟩ := hrhs
    obtain ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩ :=
      (ApproxArgsDemand.append_iff w.preMajor w.fields uss).mp hargs
    have hrecHead : ApproxDI E ρ (.const w.recRef w.ls)
        (curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c) :=
      .recursor w.ls hpreArgs.length_eq hfldsArgs.length_eq hschema
    have hmaj : ∀ v ∈ ctorDemand w.ctorRef w.nparams us_fields,
        ApproxDI E ρ (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) v :=
      ctorDemand_intro w.lsC hrigidCtor w.hctorParams hfldsArgs
    have htotArgs : ApproxArgsDemand E ρ
        (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)])
        (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) :=
      (ApproxArgsDemand.append_iff _ _ _).mpr
        ⟨us_pre, [ctorDemand w.ctorRef w.nparams us_fields], rfl, hpreArgs, .cons hmaj .nil⟩
    unfold iotaLhsOfS recCall
    rw [approxDI_foldApps_iff]
    exact ⟨_, hrecHead, (foldAppCpt_curryStep_iff htotArgs.length_eq).mpr (Or.inr ⟨htotArgs, rfl⟩)⟩

/-- Soundness of `DerivedIotaT` in `ApproxDI` (unconditional on `E` and `ρ`). -/
theorem approxDI_iotaT {E : ResolvedEnv} {lhs rhs : Expr Nat} (h : DerivedIotaT E lhs rhs)
    (ρ : EnvI) : SemEqDI E ρ lhs rhs := by
  cases h with
  | of w => exact approxDI_iotaS w ρ

/-- Soundness of legacy `IotaWitness` in `ApproxDI` at every `EnvWfT E` (via
    `derivedIotaT_of_iotaWitness_envWfT`). -/
theorem approxDI_iota_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitness E)
    (ρ : EnvI) : SemEqDI E ρ (iotaLhsOf w) (iotaRhsOf w) := by
  obtain ⟨ht⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  exact approxDI_iotaT ht ρ

/-- Soundness of union `DerivedIotaU` (`WhStep.iota`) in `ApproxDI` at every `EnvWfT E`. -/
theorem approxDI_iotaU_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (ρ : EnvI) : SemEqDI E ρ lhs rhs := by
  obtain ⟨ht⟩ := derivedIotaT_of_derivedIotaU_envWfT hW h
  exact approxDI_iotaT ht ρ

/-- Soundness of `ConvT.iota` (`DerivedIota`) in `ApproxDI` at every `EnvWfT E`. -/
theorem semEqDI_of_convT_iota {E : ResolvedEnv} (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (h : DerivedIota E lhs rhs) (ρ : EnvI) : SemEqDI E ρ lhs rhs := by
  obtain ⟨ht⟩ := derivedIotaT_of_derivedIota_envWfT hW h
  exact approxDI_iotaT ht ρ

/-! ## §8. Congruences, `WhStep`/`WhRed` Soundness, Model Π-Injectivity, and Logical-Relation Bridge -/

theorem semEqDI_sorts (E : ResolvedEnv) (ρ : EnvI) (l₁ l₂ : Level) :
    SemEqDI E ρ (.sort l₁) (.sort l₂) := by
  intro c
  constructor <;> (intro h; rcases approxDI_sort_inv h with rfl | rfl; exact .bot _ _; exact .sort _ _)

theorem semEqDI_app {E : ResolvedEnv} {ρ : EnvI} {f f' a a' : Expr Nat}
    (hf : SemEqDI E ρ f f') (ha : SemEqDI E ρ a a') :
    SemEqDI E ρ (.app f a) (.app f' a') := by
  intro c
  constructor
  · intro h
    rcases approxDI_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, hax⟩ | ⟨r, args, u, rfl, hfs, hau⟩
    · exact .bot _ _
    · exact .app ((hf (.lam g)).mp hfg) hs (fun u hu => (ha u).mp (hax u hu))
    · exact .appSpine ((hf (.spine r args)).mp hfs) ((ha u).mp hau)
  · intro h
    rcases approxDI_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, hax⟩ | ⟨r, args, u, rfl, hfs, hau⟩
    · exact .bot _ _
    · exact .app ((hf (.lam g)).mpr hfg) hs (fun u hu => (ha u).mpr (hax u hu))
    · exact .appSpine ((hf (.spine r args)).mpr hfs) ((ha u).mpr hau)

theorem semEqDI_lam {E : ResolvedEnv} {ρ : EnvI} (A A' : Expr Nat) {b b' : Expr Nat}
    (hb : ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) b b') :
    SemEqDI E ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro h
    rcases approxDI_lam_inv h with rfl | ⟨f, rfl, hbf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mp (hbf s hs))
  · intro h
    rcases approxDI_lam_inv h with rfl | ⟨f, rfl, hbf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mpr (hbf s hs))

theorem semEqDI_pi {E : ResolvedEnv} {ρ : EnvI} {A A' B B' : Expr Nat}
    (hA : SemEqDI E ρ A A') (hB : ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) B B') :
    SemEqDI E ρ (.pi A B) (.pi A' B') := by
  intro c
  constructor
  · intro h
    rcases approxDI_pi_inv h with rfl | ⟨a, f, rfl, hAa, hBf⟩
    · exact .bot _ _
    · exact .pi ((hA a).mp hAa) (fun s hs => (hB s.1 s.2).mp (hBf s hs))
  · intro h
    rcases approxDI_pi_inv h with rfl | ⟨a, f, rfl, hAa, hBf⟩
    · exact .bot _ _
    · exact .pi ((hA a).mpr hAa) (fun s hs => (hB s.1 s.2).mpr (hBf s hs))

theorem semEqDI_letE {E : ResolvedEnv} {ρ : EnvI} (A A' : Expr Nat) {v v' b b' : Expr Nat}
    (hv : SemEqDI E ρ v v') (hb : ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) b b') :
    SemEqDI E ρ (.letE A v b) (.letE A' v' b') := by
  have happ : SemEqDI E ρ (.app (.lam A b) v) (.app (.lam A' b') v') :=
    semEqDI_app (semEqDI_lam A A' hb) hv
  intro c
  constructor
  · intro h
    rcases approxDI_letE_inv h with rfl | h'
    · exact .bot _ _
    · exact .letE ((happ c).mp h')
  · intro h
    rcases approxDI_letE_inv h with rfl | h'
    · exact .bot _ _
    · exact .letE ((happ c).mpr h')

/-- Soundness of every weak-head step (`WhStep E a b` from `RcicNativePiModelLR`) in `ApproxDI`
    at every `EnvWfT E` and every valuation `ρ : EnvI`. -/
theorem semEqDI_whStep {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStep E a b) (ρ : EnvI) : SemEqDI E ρ a b := by
  induction hs with
  | beta A body arg => exact approxDI_beta E ρ A body arg
  | zeta A v body => exact approxDI_zeta E ρ A v body
  | delta hres hbody => exact semEqDI_of_whStep_delta hW hres hbody ρ
  | iota h => exact approxDI_iotaU_of_envWfT hW h ρ
  | lit t => exact approxDI_lit E ρ t
  | @appHead f f' arg _ ih => exact semEqDI_app ih (semEqDI_refl E ρ arg)

/-- Soundness of multi-step weak-head reduction (`WhRed E a b` from `RcicNativePiModelLR`) in
    `ApproxDI` at every `EnvWfT E` and every valuation `ρ : EnvI`. -/
theorem semEqDI_whRed {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRed E a b) (ρ : EnvI) : SemEqDI E ρ a b := by
  induction hr with
  | refl e => exact semEqDI_refl E ρ e
  | step hs _ ih => exact semEqDI_trans (semEqDI_whStep hW hs ρ) ih

/-- Model Π-injectivity for `SemEqDI`: on domains, and on codomains at every finite demand. -/
theorem semEqDI_pi_inj {E : ResolvedEnv} {ρ : EnvI} {A B A' B' : Expr Nat}
    (h : SemEqDI E ρ (.pi A B) (.pi A' B')) :
    SemEqDI E ρ A A' ∧ ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) B B' := by
  refine ⟨fun a => ⟨fun hA => ?_, fun hA' => ?_⟩, fun us v => ⟨fun hB => ?_, fun hB' => ?_⟩⟩
  · have := (h (.pi a [])).mp (.pi hA (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxDI_pi_inv this with h0 | ⟨_, _, heq, hA', _⟩
    · cases h0
    · cases heq; exact hA'
  · have := (h (.pi a [])).mpr (.pi hA' (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxDI_pi_inv this with h0 | ⟨_, _, heq, hA, _⟩
    · cases h0
    · cases heq; exact hA
  · have := (h (.pi .bot [(us, v)])).mp (.pi (.bot ρ A) (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB))
    rcases approxDI_pi_inv this with h0 | ⟨_, _, heq, _, hB'⟩
    · cases h0
    · cases heq; exact hB' (us, v) (List.mem_singleton.mpr rfl)
  · have := (h (.pi .bot [(us, v)])).mpr (.pi (.bot ρ A') (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB'))
    rcases approxDI_pi_inv this with h0 | ⟨_, _, heq, _, hB⟩
    · cases h0
    · cases heq; exact hB (us, v) (List.mem_singleton.mpr rfl)

/-- Π-types and sorts are disjoint in `SemEqDI`. -/
theorem semEqDI_pi_sort_disjoint {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat} {l : Level}
    (h : SemEqDI E ρ (.pi A B) (.sort l)) : False := by
  have := (h (.pi .bot [])).mp (.pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim))
  rcases approxDI_sort_inv this with h0 | h0 <;> cases h0

/-- `.pi .bot []` approximates every Π-type in `ApproxDI`. -/
theorem approxDI_pi_bot_nil (E : ResolvedEnv) (ρ : EnvI) (A B : Expr Nat) :
    ApproxDI E ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-! ### Non-Vacuity Pins -/

/-- Positive δ pin: in `defSortEnv` (where raw `SemEqI` failed in `defSortEnv_delta_step_and_raw_refuted`),
    `SemEqDI defSortEnv ρ (.const 0 []) (.sort .zero)` holds for every `ρ : EnvI`. -/
theorem pin_defSortEnv_delta (ρ : EnvI) :
    SemEqDI defSortEnv ρ (.const 0 []) (.sort .zero) :=
  semEqDI_of_whStep_delta defSortEnvWfT (r := 0)
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl ρ

/-- Positive ι pin on `wZero` / `wZeroS` in `natEnv` (where raw `SemEqI` failed in
    `wZero_unsound_raw_approxI`): `SemEqDI natEnv ρ (iotaLhsOf wZero) (iotaRhsOf wZero)` and
    `ApproxDI natEnv ρ (iotaLhsOf wZero) (.spine 1 [])` hold for every `ρ : EnvI`. -/
theorem pin_wZero_iota (ρ : EnvI) :
    SemEqDI natEnv ρ (iotaLhsOfS wZeroS) (iotaRhsOfS wZeroS) ∧
      SemEqDI natEnv ρ (iotaLhsOf wZero) (iotaRhsOf wZero) ∧
      ApproxDI natEnv ρ (iotaLhsOf wZero) (.spine 1 []) := by
  have hS := approxDI_iotaS wZeroS ρ
  have hlhsEq : iotaLhsOfS wZeroS = iotaLhsOf wZero :=
    iotaLhsOfS_iotaWitnessSOf wZero 64 pin_iotaWitnessSB_wZero
  have hL : SemEqDI natEnv ρ (iotaLhsOf wZero) (iotaRhsOf wZero) := by
    simpa only [hlhsEq, pin_wZeroS_rhs] using hS
  have hrhs : ApproxDI natEnv ρ (iotaRhsOf wZero) (.spine 1 []) :=
    .const ρ 1 [] (rigidConst_of_ctor (m := natZeroMember) rfl rfl)
  exact ⟨hS, hL, (hL (.spine 1 [])).mpr hrhs⟩

/-- Positive ι pins on `wSuccS` (`natEnv`), `wNilS` (`listEnv`), `wConsS` (`listEnv`),
    `wVconsS` (`vecEnv`), and `wSuccU1` (`natEnvU`). -/
theorem pin_admitted_families_iota (ρ : EnvI) :
    SemEqDI natEnv ρ (iotaLhsOfS wSuccS) (iotaRhsOfS wSuccS) ∧
      SemEqDI listEnv ρ (iotaLhsOfS wNilS) (iotaRhsOfS wNilS) ∧
      SemEqDI listEnv ρ (iotaLhsOfS wConsS) (iotaRhsOfS wConsS) ∧
      SemEqDI vecEnv ρ (iotaLhsOfS wVconsS) (iotaRhsOfS wVconsS) ∧
      SemEqDI natEnvU ρ (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) :=
  ⟨approxDI_iotaS wSuccS ρ,
   approxDI_iotaS wNilS ρ,
   approxDI_iotaS wConsS ρ,
   approxDI_iotaS wVconsS ρ,
   approxDI_iota_of_envWfT natEnvUWfT wSuccU1 ρ⟩

/-- Non-vacuity pin: `IotaDetU natEnvU` holds via `iotaDetU_of_envWfT`. -/
theorem pin_iotaDetU_natEnvU : IotaDetU natEnvU :=
  iotaDetU_of_envWfT natEnvUWfT

/-! ## §9. Discharging `WhDet`, `WhApproxInvCore`/`WhApproxInv`, and Spine-Freedom `(O3)` -/

open Rcic.Declarative.NativeValleys.PiModelIrrAudit

/-! ### §9.1. Weak-Head Determinism `WhDet E` (`RcicNativePiModelLRCases`) from `EnvWfT E` -/

/-- Lambda abstractions are weak-head normal (`WhStep E (.lam A b) e` is impossible). -/
theorem whStep_lam_false {E : ResolvedEnv} {A b e : Expr Nat}
    (h : WhStep E (.lam A b) e) : False := by
  cases h with
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl

/-- In any well-formed environment `EnvWfT E`, a partial application `foldApps (.const w.recRef ls) xs`
    with `xs.length ≤ w.preMajor.length` is weak-head normal: the recursor head has no δ-body
    (`not_deltaConst_of_recursor`), is not a λ (`F8EtaK.foldApps_const_ne_lam_any`), and has
    strictly fewer arguments than any ι redex for `w.recRef` (`iotaWitnessS_preMajor_length_eq`). -/
theorem not_whStep_recursor_prefix {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) {e : Expr Nat}
    (hs : WhStep E (foldApps (.const w.recRef ls) xs) e) : False := by
  have key : ∀ {f e : Expr Nat} (ys : List (Expr Nat)),
      WhStep E f e → appsSpine f = (.const w.recRef ls, ys) →
      ys.length ≤ w.preMajor.length → False := by
    intro f e ys hstep
    induction hstep generalizing ys with
    | beta A b a =>
        intro hsp _
        simp [appsSpine] at hsp
    | zeta A v b =>
        intro hsp _
        simp [appsSpine] at hsp
    | delta hres hbody =>
        intro hsp _
        simp only [appsSpine, Prod.mk.injEq, Expr.const.injEq] at hsp
        obtain ⟨⟨rfl, _⟩, _⟩ := hsp
        obtain ⟨hd, _⟩ := envWfT_member_body_closed hW w.recRef _ _ hres hbody
        exact not_deltaConst_of_recursor w hd
    | iota hI =>
        intro hsp hlen'
        obtain ⟨hT⟩ := derivedIotaT_of_derivedIotaU_envWfT hW hI
        have unpack : ∀ {l r : Expr Nat}, DerivedIotaT E l r →
            ∃ w' : IotaWitnessS E, l = iotaLhsOfS w' ∧ r = iotaRhsOfS w' := by
          intro l r h; cases h with | of w' => exact ⟨w', rfl, rfl⟩
        obtain ⟨w', hl, _⟩ := unpack hT
        unfold iotaLhsOfS recCall at hl
        have s₂ := appsSpine_foldApps (.const w'.recRef w'.ls)
          (w'.preMajor ++ [foldApps (.const w'.ctorRef w'.lsC) (w'.ctorParams ++ w'.fields)])
        simp only [appsSpine_const, List.nil_append] at s₂
        rw [hl, s₂] at hsp
        injection hsp with hhead hargs
        injection hhead with hrec _
        have hpreLen := (iotaWitnessS_preMajor_length_eq w w' hrec.symm).2
        have hlenEq := congrArg List.length hargs
        simp only [List.length_append, List.length_singleton] at hlenEq
        omega
    | lit t =>
        intro hsp _
        simp [appsSpine] at hsp
    | @appHead f₀ f₀' a _ ih =>
        intro hsp hlen'
        simp only [appsSpine, Prod.mk.injEq] at hsp
        obtain ⟨hhead, hargs⟩ := hsp
        subst hargs
        simp only [List.length_append, List.length_singleton] at hlen'
        exact ih (appsSpine f₀).2 (Prod.ext hhead rfl) (by omega)
  have hsp₀ := appsSpine_foldApps (.const w.recRef ls) xs
  simp only [appsSpine_const, List.nil_append] at hsp₀
  exact key xs hs hsp₀ hlen

/-- Unconditional discharge of `WhDet E` (`RcicNativePiModelLRCases`) at every well-formed
    environment `EnvWfT E`. -/
theorem whDet_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : WhDet E := by
  intro a b c h₁ h₂
  induction h₁ generalizing c with
  | beta A body arg =>
      cases h₂ with
      | beta => rfl
      | iota hI =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
          simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
          exact (F8EtaK.foldApps_const_ne_lam_any hl.1.symm).elim
      | appHead hf => exact (whStep_lam_false hf).elim
  | zeta A v body =>
      cases h₂ with
      | zeta => rfl
      | iota hI =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
          simp [recCall, foldApps_snoc] at hl
  | delta hres₁ hbody₁ =>
      cases h₂ with
      | delta hres₂ hbody₂ =>
          have hm : _ = _ := Option.some.inj (hres₁.symm.trans hres₂)
          subst hm
          have hb : _ = _ := Option.some.inj (hbody₁.symm.trans hbody₂)
          subst hb
          rfl
      | iota hI =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
          simp [recCall, foldApps_snoc] at hl
  | iota hI₁ =>
      have unpack : ∀ {l r : Expr Nat}, DerivedIotaT E l r →
          ∃ w : IotaWitnessS E, l = iotaLhsOfS w ∧ r = iotaRhsOfS w := by
        intro l r h; cases h with | of w => exact ⟨w, rfl, rfl⟩
      obtain ⟨hT₁⟩ := derivedIotaT_of_derivedIotaU_envWfT hW hI₁
      obtain ⟨w₁, hl₁, _⟩ := unpack hT₁
      cases h₂ with
      | beta =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI₁
          simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
          exact (F8EtaK.foldApps_const_ne_lam_any hl.1.symm).elim
      | zeta =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI₁
          simp [recCall, foldApps_snoc] at hl
      | delta =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI₁
          simp [recCall, foldApps_snoc] at hl
      | iota hI₂ =>
          exact iotaDetU_of_envWfT hW hI₁ hI₂
      | lit =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI₁
          simp [recCall, foldApps_snoc] at hl
      | appHead hf =>
          unfold iotaLhsOfS recCall at hl₁
          rw [foldApps_snoc] at hl₁
          injection hl₁ with hfEq _
          subst hfEq
          exact (not_whStep_recursor_prefix hW w₁ w₁.ls w₁.preMajor (Nat.le_refl _) hf).elim
  | lit t =>
      cases h₂ with
      | lit => rfl
      | iota hI =>
          obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
          simp [recCall, foldApps_snoc] at hl
  | appHead hf₁ ih =>
      cases h₂ with
      | beta => exact (whStep_lam_false hf₁).elim
      | iota hI₂ =>
          have unpack : ∀ {l r : Expr Nat}, DerivedIotaT E l r →
              ∃ w : IotaWitnessS E, l = iotaLhsOfS w ∧ r = iotaRhsOfS w := by
            intro l r h; cases h with | of w => exact ⟨w, rfl, rfl⟩
          obtain ⟨hT₂⟩ := derivedIotaT_of_derivedIotaU_envWfT hW hI₂
          obtain ⟨w₂, hl₂, _⟩ := unpack hT₂
          unfold iotaLhsOfS recCall at hl₂
          rw [foldApps_snoc] at hl₂
          injection hl₂ with hfEq _
          subst hfEq
          exact (not_whStep_recursor_prefix hW w₂ w₂.ls w₂.preMajor (Nat.le_refl _) hf₁).elim
      | appHead hf₂ => rw [ih hf₂]

/-- Uniqueness of weak-head normal forms at every `EnvWfT E` (without assuming `WhDet E`). -/
theorem whRed_normal_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a X Y : Expr Nat} (h₁ : WhRed E a X) (hX : WhNormal E X)
    (h₂ : WhRed E a Y) (hY : WhNormal E Y) : X = Y :=
  whRed_normal_unique (whDet_of_envWfT hW) h₁ hX h₂ hY

/-- Transitivity of `LRTypeIN` at every `EnvWfT E` (without assuming `WhDet E`). -/
theorem lrTypeIN_trans_of_envWfT {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hW : EnvWfT E) {Γ : LCtx} {A B C : Expr Nat} {c : CptI}
    (h₁ : LRTypeIN E n Γ A B c) (h₂ : LRTypeIN E n Γ B C c) :
    LRTypeIN E n Γ A C c :=
  lrTypeIN_trans hcl hW (whDet_of_envWfT hW) h₁ h₂

/-- Non-vacuity pins for `WhDet`: holds on `defSortEnv` and `natEnvU`. -/
theorem pin_whDet_defSortEnv_and_natEnvU : WhDet defSortEnv ∧ WhDet natEnvU :=
  ⟨whDet_of_envWfT defSortEnvWfT, whDet_of_envWfT natEnvUWfT⟩

/-! ### §9.2. Refutation of Raw `WhApproxInvCore`/`WhApproxInv` and Discharge of `WhApproxInvCoreDI`/`WhApproxInvDI` -/

/-- Any definition with a sort body refutes `WhApproxInvCore E` on raw `ApproxI`. -/
theorem not_whApproxInvCore_of_delta_sort {E : ResolvedEnv} {r : Nat} (ls : List Level)
    {m : CheckedMember} {u : Level} (hres : E.members r = some m)
    (hbody : m.body = some (.sort u)) : ¬ WhApproxInvCore E := by
  intro hcore
  exact delta_unsound_raw_approxI EnvI.bot r ls (instLevel ls u)
    (fun c => hcore.1 (ls := ls) hres hbody EnvI.bot c)

/-- Any definition with a sort body refutes `WhApproxInv E` on raw `ApproxI`. -/
theorem not_whApproxInv_of_delta_sort {E : ResolvedEnv} {r : Nat} (ls : List Level)
    {m : CheckedMember} {u : Level} (hres : E.members r = some m)
    (hbody : m.body = some (.sort u)) : ¬ WhApproxInv E := by
  intro hinv
  exact delta_unsound_raw_approxI EnvI.bot r ls (instLevel ls u)
    (fun c => hinv (.delta (ls := ls) hres hbody) EnvI.bot c)

/-- `defSortEnv` refutes `WhApproxInvCore` on raw `ApproxI`. -/
theorem not_whApproxInvCore_defSortEnv : ¬ WhApproxInvCore defSortEnv :=
  not_whApproxInvCore_of_delta_sort (r := 0) []
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl

/-- `defSortEnv` refutes `WhApproxInv` on raw `ApproxI`. -/
theorem not_whApproxInv_defSortEnv : ¬ WhApproxInv defSortEnv :=
  not_whApproxInv_of_delta_sort (r := 0) []
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl

/-- `natEnv` refutes `WhApproxInvCore` on raw `ApproxI` (via `wZero`). -/
theorem not_whApproxInvCore_natEnv : ¬ WhApproxInvCore natEnv := by
  intro hcore
  exact (wZero_unsound_raw_approxI EnvI.bot).1 (fun c => hcore.2 (.ofU wZero) EnvI.bot c)

/-- `natEnv` refutes `WhApproxInv` on raw `ApproxI` (via `wZero`). -/
theorem not_whApproxInv_natEnv : ¬ WhApproxInv natEnv := by
  intro hinv
  exact (wZero_unsound_raw_approxI EnvI.bot).1 (fun c => hinv (.iota (.ofU wZero)) EnvI.bot c)

/-- The δ and ι core weak-head invariance statement over `ApproxDI`
    (counterpart to `RcicNativePiModelLRTerm.WhApproxInvCore`). -/
def WhApproxInvCoreDI (E : ResolvedEnv) : Prop :=
  (∀ {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat},
    E.members r = some m → m.body = some b →
    ∀ ρ c, ApproxDI E ρ (.const r ls) c ↔ ApproxDI E ρ (instantiateLevels ls b) c) ∧
  (∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs →
    ∀ ρ c, ApproxDI E ρ lhs c ↔ ApproxDI E ρ rhs c)

/-- Full weak-head step invariance over `ApproxDI`
    (counterpart to `RcicNativePiModelLRTerm.WhApproxInv`). -/
def WhApproxInvDI (E : ResolvedEnv) : Prop :=
  ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxDI E ρ a c ↔ ApproxDI E ρ b c

/-- `WhApproxInvCoreDI E` holds unconditionally at every `EnvWfT E`. -/
theorem whApproxInvCoreDI_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : WhApproxInvCoreDI E :=
  ⟨fun hres hbody ρ c => semEqDI_of_whStep_delta hW hres hbody ρ c,
   fun hι ρ c => approxDI_iotaU_of_envWfT hW hι ρ c⟩

/-- `WhApproxInvDI E` holds unconditionally at every `EnvWfT E`. -/
theorem whApproxInvDI_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : WhApproxInvDI E :=
  fun hs ρ c => semEqDI_whStep hW hs ρ c

/-- Backward transport of `ApproxDI` along `WhRed E A X` at every `EnvWfT E`. -/
theorem approxDI_whRed_back {E : ResolvedEnv} (hW : EnvWfT E) {A X : Expr Nat}
    (h : WhRed E A X) {ρ : EnvI} {c : CptI} (hX : ApproxDI E ρ X c) :
    ApproxDI E ρ A c :=
  (semEqDI_whRed hW h ρ c).mpr hX

/-- Whenever `WhRed E A (.sort l)` at `EnvWfT E`, `.sort ∈ ⟦A⟧_ρ` in `ApproxDI`. -/
theorem approxDI_sort_of_whRed {E : ResolvedEnv} (hW : EnvWfT E) {A : Expr Nat} {l : Level}
    (h : WhRed E A (.sort l)) (ρ : EnvI) : ApproxDI E ρ A .sort :=
  approxDI_whRed_back hW h (.sort ρ l)

/-- Non-vacuity pins: `WhApproxInvCoreDI` and `WhApproxInvDI` hold on `defSortEnv` and `natEnvU`. -/
theorem pin_whApproxInvDI_defSortEnv_and_natEnvU :
    WhApproxInvCoreDI defSortEnv ∧ WhApproxInvDI defSortEnv ∧
      WhApproxInvCoreDI natEnvU ∧ WhApproxInvDI natEnvU :=
  ⟨whApproxInvCoreDI_of_envWfT defSortEnvWfT,
   whApproxInvDI_of_envWfT defSortEnvWfT,
   whApproxInvCoreDI_of_envWfT natEnvUWfT,
   whApproxInvDI_of_envWfT natEnvUWfT⟩

/-! ### §9.3. Spine-Freedom (`NoSpine`, `(O3)`) and Projected Equality (`PEqDI`) over `ApproxDI` -/

/-- In raw `ApproxI`, applying any `.spine r args` head to `xs` extends the spine by `xs.length`
    copies of `.bot`. -/
theorem approxI_foldApps_spine_bot (ρ : EnvI) (r : Nat) :
    ∀ (xs : List (Expr Nat)) {f : Expr Nat} {args : List CptI},
      ApproxI ρ f (.spine r args) →
      ApproxI ρ (foldApps f xs) (.spine r (args ++ List.replicate xs.length .bot))
  | [], _, _, hf => by simpa using hf
  | x :: xs, f, args, hf => by
      have hstep : ApproxI ρ (.app f x) (.spine r (args ++ [.bot])) :=
        .appSpine hf (.bot ρ x)
      have ih := approxI_foldApps_spine_bot ρ r xs hstep
      simpa [foldApps, List.replicate, List.append_assoc] using ih

/-- Refutation tooth on raw `ApproxI`: NO constant-headed application `foldApps (.const r ls) xs`
    (in particular no recursor eliminator) ever satisfies `NoSpine` in raw `ApproxI`. -/
theorem not_noSpine_foldApps_const_approxI (ρ : EnvI) (r : Nat) (ls : List Level)
    (xs : List (Expr Nat)) : ¬ NoSpine (denI ρ (foldApps (.const r ls) xs)) := by
  intro hns
  have hsp : ApproxI ρ (foldApps (.const r ls) xs)
      (.spine r (List.replicate xs.length .bot)) := by
    simpa using approxI_foldApps_spine_bot ρ r xs (.const ρ r ls)
  exact hns r (List.replicate xs.length .bot) hsp

/-- Applying `curryStep uss c₀` to strictly fewer than `uss.length` arguments in `ApproxDI`
    yields only `.bot` or `.lam g` compacts (never a `.spine`). -/
theorem foldAppCpt_curryStep_lt {E : ResolvedEnv} {ρ : EnvI} :
    ∀ (xs : List (Expr Nat)) (uss : List (List CptI)) (c₀ c : CptI),
      xs.length < uss.length →
      FoldAppCpt E ρ (curryStep uss c₀) xs c →
      c = .bot ∨ ∃ g, c = .lam g
  | [], [], _, _, hlt, _ => by simp at hlt
  | [], us :: uss, c₀, c, _, h => by
      cases h with
      | bot => exact Or.inl rfl
      | nil => exact Or.inr ⟨[(us, curryStep uss c₀)], rfl⟩
  | _ :: _, [], _, _, hlt, _ => by simp at hlt
  | _ :: xs, _ :: uss, c₀, c, hlt, h => by
      cases h with
      | bot => exact Or.inl rfl
      | cons hstep htail =>
          cases hstep with
          | bot => exact Or.inl (foldAppCpt_bot_inv htail)
          | app hs _ =>
              have heq := List.mem_singleton.mp hs
              cases heq
              simp only [List.length_cons] at hlt
              exact foldAppCpt_curryStep_lt xs uss c₀ c (by omega) htail

/-- In `ApproxDI`, every partial application `foldApps (.const w.recRef ls) xs` of an admitted
    recursor with `xs.length ≤ w.preMajor.length` is unconditionally spine-free (`NoSpine`),
    discharging the `NoSpine` half of `(O3)` from `RcicNativePiModelIrr`. -/
theorem noSpine_recursor_prefix_approxDI {E : ResolvedEnv} (w : IotaWitnessS E)
    (ls : List Level) (ρ : EnvI) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) :
    NoSpine (denDI E ρ (foldApps (.const w.recRef ls) xs)) := by
  intro r' args' hsp
  have hsp' : ApproxDI E ρ (foldApps (.const w.recRef ls) xs) (.spine r' args') := hsp
  rw [approxDI_foldApps_iff] at hsp'
  obtain ⟨d, hd, hfold⟩ := hsp'
  rcases approxDI_recursor_const_inv w.hrec w.hrecK hd with rfl |
    ⟨w', us_pre, us_fields, c₀, hrec, hpre, _, _, rfl⟩
  · have hbot := foldAppCpt_bot_inv hfold
    cases hbot
  · have hpreEq := (iotaWitnessS_preMajor_length_eq w' w hrec).2
    have hlt : xs.length <
        (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rcases foldAppCpt_curryStep_lt xs
      (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]) c₀
      (.spine r' args') hlt hfold with h0 | ⟨_, h0⟩ <;> cases h0

/-- In particular, every recursor eliminator `foldApps (.const w.recRef w.ls) w.preMajor` (applied
    up to the major premise) satisfies `NoSpine` unconditionally in `ApproxDI`. -/
theorem noSpine_recursor_elim_approxDI {E : ResolvedEnv} (w : IotaWitnessS E) (ρ : EnvI) :
    NoSpine (denDI E ρ (foldApps (.const w.recRef w.ls) w.preMajor)) :=
  noSpine_recursor_prefix_approxDI w w.ls ρ w.preMajor (Nat.le_refl _)

/-- Projected equality `PEqDI E ρ A a b` at type `A` over `denDI E ρ` (using `tprojI` from
    `RcicNativePiModelIrr`). -/
def PEqDI (E : ResolvedEnv) (ρ : EnvI) (A a b : Expr Nat) : Prop :=
  ∀ u, tprojI E (denDI E ρ A) (denDI E ρ a) u ↔ tprojI E (denDI E ρ A) (denDI E ρ b) u

theorem PEqDI.refl {E : ResolvedEnv} (ρ : EnvI) (A a : Expr Nat) : PEqDI E ρ A a a :=
  fun _ => Iff.rfl

theorem PEqDI.symm {E : ResolvedEnv} {ρ : EnvI} {A a b : Expr Nat} (h : PEqDI E ρ A a b) :
    PEqDI E ρ A b a :=
  fun u => (h u).symm

theorem PEqDI.trans {E : ResolvedEnv} {ρ : EnvI} {A a b c : Expr Nat}
    (h₁ : PEqDI E ρ A a b) (h₂ : PEqDI E ρ A b c) : PEqDI E ρ A a c :=
  fun u => (h₁ u).trans (h₂ u)

/-- Untyped `SemEqDI` implies projected equality `PEqDI` at every type `A`. -/
theorem pEqDI_of_semEqDI {E : ResolvedEnv} {ρ : EnvI} {A a b : Expr Nat}
    (h : SemEqDI E ρ a b) : PEqDI E ρ A a b :=
  fun u => ⟨fun ⟨hu, ha⟩ => ⟨(h u).mp hu, ha⟩, fun ⟨hu, ha⟩ => ⟨(h u).mpr hu, ha⟩⟩

theorem tprojI_denDI_bot (E : ResolvedEnv) (ρ : EnvI) (A a : Expr Nat) :
    tprojI E (denDI E ρ A) (denDI E ρ a) .bot :=
  ⟨.bot ρ a, .bot, .bot ρ A, .bot .bot⟩

theorem tprojI_denDI_prop {E : ResolvedEnv} {ρ : EnvI} {P : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P)) (a : Expr Nat) (u : CptI) :
    tprojI E (denDI E ρ P) (denDI E ρ a) u ↔ u = .bot :=
  ⟨fun ⟨_, c, hc, hty⟩ => cty_prop_bot (hP c hc) hty,
   fun h => h ▸ tprojI_denDI_bot E ρ P a⟩

/-- Proof irrelevance (`ConvT.irr`) for `PEqDI` at any proposition ideal `IsPropIdealI E (denDI E ρ P)`. -/
theorem pEqDI_irr {E : ResolvedEnv} {ρ : EnvI} {P : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P)) (a b : Expr Nat) : PEqDI E ρ P a b :=
  fun u => (tprojI_denDI_prop hP a u).trans (tprojI_denDI_prop hP b u).symm

/-- Soundness of δ for projected equality `PEqDI` at every `EnvWfT E`. -/
theorem pEqDI_delta {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m)
    (hbody : m.body = some b) (ρ : EnvI) (T : Expr Nat) :
    PEqDI E ρ T (.const r ls) (instantiateLevels ls b) :=
  pEqDI_of_semEqDI (semEqDI_of_whStep_delta hW hres hbody ρ)

/-- Unconditional soundness of ι (`IotaWitnessS`) for projected equality `PEqDI`. -/
theorem pEqDI_iotaS {E : ResolvedEnv} (w : IotaWitnessS E) (ρ : EnvI) (T : Expr Nat) :
    PEqDI E ρ T (iotaLhsOfS w) (iotaRhsOfS w) :=
  pEqDI_of_semEqDI (approxDI_iotaS w ρ)

/-- Soundness of `DerivedIotaU` for projected equality `PEqDI` at every `EnvWfT E`. -/
theorem pEqDI_iotaU_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (ρ : EnvI) (T : Expr Nat) :
    PEqDI E ρ T lhs rhs :=
  pEqDI_of_semEqDI (approxDI_iotaU_of_envWfT hW h ρ)

/-- Application stability in `ApproxDI` at a proposition domain (`IsPropIdealI`). -/
theorem semEqDI_app_stable {E : ResolvedEnv} {ρ : EnvI} {A f : Expr Nat}
    (hA : IsPropIdealI E (denDI E ρ A)) (hdom : DomTyped E (denDI E ρ A) (denDI E ρ f))
    (hns : NoSpine (denDI E ρ f)) (a b : Expr Nat) : SemEqDI E ρ (.app f a) (.app f b) := by
  have dir : ∀ x y c, ApproxDI E ρ (.app f x) c → ApproxDI E ρ (.app f y) c := by
    intro x y c h
    cases h with
    | bot => exact .bot _ _
    | app hf hs _ =>
        refine .app hf hs (fun u hu => ?_)
        obtain ⟨a', ha', hc⟩ := hdom _ hf _ hs u hu
        have hu0 : u = .bot := cty_prop_bot (hA a' ha') hc
        subst hu0
        exact .bot _ _
    | appSpine hf _ => exact absurd hf (hns _ _)
  exact fun c => ⟨dir a b c, dir b a c⟩

theorem pEqDI_app_stable {E : ResolvedEnv} {ρ : EnvI} {A f : Expr Nat} (T : Expr Nat)
    (hA : IsPropIdealI E (denDI E ρ A)) (hdom : DomTyped E (denDI E ρ A) (denDI E ρ f))
    (hns : NoSpine (denDI E ρ f)) (a b : Expr Nat) : PEqDI E ρ T (.app f a) (.app f b) :=
  pEqDI_of_semEqDI (semEqDI_app_stable hA hdom hns a b)

/-- K over `ApproxDI` for any `w : IotaWitnessS E`: both `(O3)` hypotheses of
    `RcicNativePiModelIrr.pEqI_k_of_iota` (`NoSpine` of the recursor eliminator and `ι`
    soundness at the canonical constructor term) are discharged unconditionally by
    `noSpine_recursor_elim_approxDI` and `pEqDI_iotaS`. -/
theorem pEqDI_k_of_domTyped_iotaS {E : ResolvedEnv} (w : IotaWitnessS E) {ρ : EnvI}
    {P T : Expr Nat} (hP : IsPropIdealI E (denDI E ρ P))
    (hdom : DomTyped E (denDI E ρ P)
      (denDI E ρ (foldApps (.const w.recRef w.ls) w.preMajor)))
    (h : Expr Nat) :
    PEqDI E ρ T (.app (foldApps (.const w.recRef w.ls) w.preMajor) h) (iotaRhsOfS w) := by
  have hstab : PEqDI E ρ T
      (.app (foldApps (.const w.recRef w.ls) w.preMajor) h)
      (iotaLhsOfS w) := by
    unfold iotaLhsOfS recCall
    rw [foldApps_snoc]
    exact pEqDI_app_stable T hP hdom (noSpine_recursor_elim_approxDI w ρ) h
      (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
  exact hstab.trans (pEqDI_iotaS w ρ T)

/-! ## §10. Logical-Relation Consumers over `ApproxDI` without External `WhDet` or `WhApproxInv` -/

/-- Model soundness for type conversions in `ApproxDI` at `EnvI.bot`. -/
def TypeSoundnessDI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    ConvT E n Γ A B (.sort u) → SemEqDI E EnvI.bot A B

/-- Soundness for a `TyConvT` chain in `ApproxDI` from soundness for its links. -/
theorem semEqDI_of_tyConvT {E : ResolvedEnv} {n : Nat} (hS : TypeSoundnessDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B → SemEqDI E EnvI.bot A B
  | _, _, .refl _ _ => fun _ => Iff.rfl
  | _, _, .of _ _ _ _ hc => hS hΓ hc
  | _, _, .trans _ _ _ _ c₁ c₂ => fun c =>
      (semEqDI_of_tyConvT hS hΓ c₁ c).trans (semEqDI_of_tyConvT hS hΓ c₂ c)

/-- The typed type-level fundamental lemma over `ApproxDI`. -/
def FundamentalLRINT_DI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, ApproxDI E EnvI.bot A c → LRTypeIN E n Γ A A' c

/-- The fundamental lemma for terms (diagonal and conversions) over `ApproxDI` at `EnvI.bot`. -/
def FundamentalTermDI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermI E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermI E n Γ M M' A u)

/-- Adequacy at Π over `ApproxDI`. -/
def AdequacyPiDI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
    ∀ {a : CptI} {f : List (List CptI × CptI)}, ApproxDI E EnvI.bot A (.pi a f) →
    ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) ∧ ApproxDI E EnvI.bot A₁ a ∧
      ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2

/-- The typed type-level fundamental lemma over `ApproxDI` from `FundamentalTermDI` and
    `TypeSoundnessDI`: unlike `RcicNativePiModelLRTerm.fundamentalLRINT_of_fundamentalTermI`,
    no external `WhDet E` hypothesis is needed because `whDet_of_envWfT hW` discharges it. -/
theorem fundamentalLRINT_DI_of_fundamentalTermDI {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hW : EnvWfT E) (hS : TypeSoundnessDI E n)
    (F : FundamentalTermDI E n) : FundamentalLRINT_DI E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hcA; exact lrTypeIN_of_lrTermI_sort c (F.1 hΓ hA c hcA)
  | of A B v hc => intro u hA c hcA; exact lrTypeIN_of_lrTermI_sort c (F.2 hΓ hc c hcA)
  | trans A M B c₁ c₂ ih₁ ih₂ =>
      intro u hA c hcA
      obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA
      exact lrTypeIN_trans_of_envWfT hcl hW (ih₁ hA c hcA)
        (ih₂ hM c ((semEqDI_of_tyConvT hS hΓ c₁ c).mp hcA))

/-- Π-injectivity (`piRow` shape) from `FundamentalLRINT_DI` over `ApproxDI`. -/
theorem piRow_of_fundamentalLRINT_DI {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRINT_DI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrTypeIN_pi_components (F hΓ hPi hc _ (approxDI_pi_bot_nil E EnvI.bot A B))

/-- Shape half of adequacy at Π from `FundamentalTermDI`. -/
theorem adequacyPiShape_of_fundamentalTermDI {E : ResolvedEnv} {n : Nat}
    (F : FundamentalTermDI E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u))
    {a : CptI} {f : List (List CptI × CptI)} (hc : ApproxDI E EnvI.bot A (.pi a f)) :
    ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) := by
  have h := lrTypeIN_of_lrTermI_sort (.pi a f) (F.1 hΓ hA _ hc)
  cases h with
  | pi h _ _ _ _ _ _ => exact ⟨_, _, h⟩

/-- Full adequacy at Π from `FundamentalTermDI` and `EnvWfT E`: unlike
    `RcicNativePiModelLRTerm.adequacyPiI_of_fundamentalTermI`, no external `WhApproxInv`
    hypothesis is needed because `semEqDI_whRed hW` discharges weak-head invariance across
    all β, ζ, δ, ι, and literal steps. -/
theorem adequacyPiDI_of_fundamentalTermDI {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalTermDI E n) : AdequacyPiDI E n := by
  intro Γ hΓ A u hA a f hc
  obtain ⟨A₁, B₁, hred⟩ := adequacyPiShape_of_fundamentalTermDI F hΓ hA hc
  have hc' := (semEqDI_whRed hW hred EnvI.bot _).mp hc
  rcases approxDI_pi_inv hc' with h0 | ⟨a', f', heq, hA₁, hB₁⟩
  · exact nomatch h0
  · cases heq
    exact ⟨A₁, B₁, hred, hA₁, hB₁⟩

/-- The `sort` typing rule on the diagonal in `ApproxDI`. -/
theorem fundTermDI_sorts (E : ResolvedEnv) (n : Nat) {Γ : LCtx} (l : Level) :
    ∀ u, ApproxDI E EnvI.bot (.sort l) u →
      LRTermI E n Γ (.sort l) (.sort l) (.sort (.succ l)) u := by
  intro u hu
  rcases approxDI_sort_inv hu with h0 | h0 <;> subst h0
  · exact lrTermI_bot _ _ _ _
  · rw [lrTermI_sort_iff]
    exact ⟨⟨_, .refl _⟩, lrTypeIN_sort_congr Γ l l⟩

/-- Any single weak-head step conversion case in `ApproxDI` reduces to the diagonal on the
    contractum without any external `WhApproxInv` assumption. -/
theorem fundConvDI_of_whStep {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} (h : WhStep E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermI E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whStep hW h EnvI.bot u).mp hu
  exact lrTermI_expand (.step h (.refl _)) (.refl _) u (hdiag u hu')

/-- Multi-step weak-head conversion in `ApproxDI` from the diagonal on the contractum. -/
theorem fundConvDI_of_whRed {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} (h : WhRed E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermI E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whRed hW h EnvI.bot u).mp hu
  exact lrTermI_expand h (.refl _) u (hdiag u hu')

/-- The `ConvT.delta` conversion case of `FundamentalTermDI` from the diagonal on the
    unfolded body `instantiateLevels ls b`. -/
theorem fundConvDI_delta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b A : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : ∀ u, ApproxDI E EnvI.bot (instantiateLevels ls b) u →
      LRTermI E n Γ (instantiateLevels ls b) (instantiateLevels ls b) A u) :
    ∀ u, ApproxDI E EnvI.bot (.const r ls) u →
      LRTermI E n Γ (.const r ls) (instantiateLevels ls b) A u :=
  fundConvDI_of_whStep hW (.delta hres hbody) hdiag

/-- The `ConvT.iota` conversion case of `FundamentalTermDI` from the diagonal on the
    ι contractum `rhs`. -/
theorem fundConvDI_iota {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {lhs rhs A : Expr Nat} (hι : DerivedIotaU E lhs rhs)
    (hdiag : ∀ u, ApproxDI E EnvI.bot rhs u → LRTermI E n Γ rhs rhs A u) :
    ∀ u, ApproxDI E EnvI.bot lhs u → LRTermI E n Γ lhs rhs A u :=
  fundConvDI_of_whStep hW (.iota hι) hdiag

/-- Type-level `ConvT.delta` case in `ApproxDI` from the diagonal on `instantiateLevels ls b`. -/
theorem lrTypeIN_delta_DI {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : ∀ c, ApproxDI E EnvI.bot (instantiateLevels ls b) c →
      LRTypeIN E n Γ (instantiateLevels ls b) (instantiateLevels ls b) c) :
    ∀ c, ApproxDI E EnvI.bot (.const r ls) c →
      LRTypeIN E n Γ (.const r ls) (instantiateLevels ls b) c := by
  intro c hc
  have hc' := (semEqDI_of_whStep_delta hW hres hbody EnvI.bot c).mp hc
  exact lrTypeIN_expand (.step (.delta hres hbody) (.refl _)) (.refl _) (hdiag c hc')

/-- Type-level `ConvT.iota` case in `ApproxDI` from the diagonal on `rhs`. -/
theorem lrTypeIN_iota_DI {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {lhs rhs : Expr Nat} (hι : DerivedIotaU E lhs rhs)
    (hdiag : ∀ c, ApproxDI E EnvI.bot rhs c → LRTypeIN E n Γ rhs rhs c) :
    ∀ c, ApproxDI E EnvI.bot lhs c → LRTypeIN E n Γ lhs rhs c := by
  intro c hc
  have hc' := (approxDI_iotaU_of_envWfT hW hι EnvI.bot c).mp hc
  exact lrTypeIN_expand (.step (.iota hι) (.refl _)) (.refl _) (hdiag c hc')

/-! ## §11. Lift-0 Invariance and Discharging `RcicNativePiModelK`'s Open `(O3)` Remainders Under a Binder -/

/-- Exact two-way weakening invariance for `lift 0 1` in `ApproxDI`: extending `ρ` by any
    predicate `S` at index `0` (`EnvI.cons S ρ`) on `lift 0 1 e` has the exact same
    compact approximations as `e` in `ρ`. -/
theorem approxDI_lift0_one_iff (E : ResolvedEnv) (ρ : EnvI) (S : CptI → Prop)
    (e : Expr Nat) (c : CptI) :
    ApproxDI E (EnvI.cons S ρ) (lift 0 1 e) c ↔ ApproxDI E ρ e c := by
  constructor
  · intro h
    have h' : ApproxDI E (EnvI.insert ρ 0 S) (lift 0 1 e) c := by
      rwa [EnvI.insert_zero]
    exact approxDI_lift_elim e h'
  · intro h
    have h' := approxDI_lift_intro h 0 S
    rwa [EnvI.insert_zero] at h'

/-- `denDI` of `lift 0 1 e` under `EnvI.cons S ρ` equals `denDI E ρ e`. -/
theorem denDI_lift0_one_eq (E : ResolvedEnv) (ρ : EnvI) (S : CptI → Prop) (e : Expr Nat) :
    denDI E (EnvI.cons S ρ) (lift 0 1 e) = denDI E ρ e := by
  funext c
  exact propext (approxDI_lift0_one_iff E ρ S e c)

/-- `SemEqDI` of `lift 0 1`-shifted expressions under `EnvI.cons S ρ` is equivalent to
    `SemEqDI` in `ρ`. -/
theorem semEqDI_lift0_one_iff (E : ResolvedEnv) (ρ : EnvI) (S : CptI → Prop)
    (a b : Expr Nat) :
    SemEqDI E (EnvI.cons S ρ) (lift 0 1 a) (lift 0 1 b) ↔ SemEqDI E ρ a b := by
  constructor
  · intro h c
    exact (approxDI_lift0_one_iff E ρ S a c).symm.trans
      ((h c).trans (approxDI_lift0_one_iff E ρ S b c))
  · intro h c
    exact (approxDI_lift0_one_iff E ρ S a c).trans
      ((h c).trans (approxDI_lift0_one_iff E ρ S b c).symm)

/-- λ-congruence of `SemEqDI` across arbitrary domain annotations when the bodies are
    semantically equal at every finite demand (`RcicNativePiModelK.semEqI_lam_congrK` counterpart). -/
theorem semEqDI_lam_congrK {E : ResolvedEnv} {ρ : EnvI} {A A' b b' : Expr Nat}
    (hb : ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) b b') :
    SemEqDI E ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro h
    rcases approxDI_lam_inv h with rfl | ⟨f, rfl, hf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mp (hf s hs))
  · intro h
    rcases approxDI_lam_inv h with rfl | ⟨f, rfl, hf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mpr (hf s hs))

/-- η at `f` for `PEqDI` (`RcicNativePiModelK.EtaSoundAt` counterpart). -/
def EtaSoundAtDI (E : ResolvedEnv) (ρ : EnvI) (A B f : Expr Nat) : Prop :=
  PEqDI E ρ (.pi A B) (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- `irr` under the λ-binder for `PEqDI` (`RcicNativePiModelK.LamIrrAt` counterpart). -/
def LamIrrAtDI (E : ResolvedEnv) (ρ : EnvI) (A B f r : Expr Nat) : Prop :=
  PEqDI E ρ (.pi A B)
    (.lam A (.app (lift 0 1 f) (.bvar 0)))
    (.lam A (.app (lift 0 1 f) (lift 0 1 r)))

/-- `ι` under the λ-binder for `PEqDI` (`RcicNativePiModelK.LamIotaAt` counterpart). -/
def LamIotaAtDI (E : ResolvedEnv) (ρ : EnvI) (A B f r x : Expr Nat) : Prop :=
  PEqDI E ρ (.pi A B)
    (.lam A (.app (lift 0 1 f) (lift 0 1 r)))
    (.lam A (lift 0 1 x))

/-- The `ι` clause under the λ-binder in `ApproxDI` (`RcicNativePiModelK.IotaClauseUnder`
    counterpart, which was left as the open `(O3)` remainder in `RcicNativePiModelK`). -/
def IotaClauseUnderDI (E : ResolvedEnv) (ρ : EnvI) (f r x : Expr Nat) : Prop :=
  ∀ us, SemEqDI E (EnvI.cons (demand us) ρ) (.app (lift 0 1 f) (lift 0 1 r)) (lift 0 1 x)

/-- By `semEqDI_lift0_one_iff`, `IotaClauseUnderDI E ρ f r x` is equivalent to
    `SemEqDI E ρ (.app f r) x`. -/
theorem iotaClauseUnderDI_iff_semEqDI (E : ResolvedEnv) (ρ : EnvI) (f r x : Expr Nat) :
    IotaClauseUnderDI E ρ f r x ↔ SemEqDI E ρ (.app f r) x := by
  constructor
  · intro h
    exact (semEqDI_lift0_one_iff E ρ (demand []) (.app f r) x).mp (h [])
  · intro h us
    exact (semEqDI_lift0_one_iff E ρ (demand us) (.app f r) x).mpr h

/-- Unconditional discharge of `IotaClauseUnderDI` (`RcicNativePiModelK`'s open `(O3)` remainder)
    for every `w : IotaWitnessS E`. -/
theorem iotaClauseUnderDI_of_iotaWitnessS {E : ResolvedEnv} (w : IotaWitnessS E) (ρ : EnvI) :
    IotaClauseUnderDI E ρ
      (foldApps (.const w.recRef w.ls) w.preMajor)
      (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
      (iotaRhsOfS w) := by
  rw [iotaClauseUnderDI_iff_semEqDI]
  have h := approxDI_iotaS w ρ
  unfold iotaLhsOfS recCall at h
  rwa [foldApps_snoc] at h

/-- Unconditional discharge of `IotaClauseUnderDI` for every `DerivedIotaU E (.app f r) x`
    at `EnvWfT E`. -/
theorem iotaClauseUnderDI_of_derivedIotaU {E : ResolvedEnv} (hW : EnvWfT E)
    {f r x : Expr Nat} (hι : DerivedIotaU E (.app f r) x) (ρ : EnvI) :
    IotaClauseUnderDI E ρ f r x :=
  (iotaClauseUnderDI_iff_semEqDI E ρ f r x).mpr (approxDI_iotaU_of_envWfT hW hι ρ)

/-- `LamIotaAtDI` from `IotaClauseUnderDI` by `semEqDI_lam_congrK`. -/
theorem lamIotaAtDI_of_iotaClause {E : ResolvedEnv} {ρ : EnvI} {A B f r x : Expr Nat}
    (h : IotaClauseUnderDI E ρ f r x) : LamIotaAtDI E ρ A B f r x :=
  pEqDI_of_semEqDI (semEqDI_lam_congrK h)

/-- Unconditional discharge of `LamIotaAtDI` for every `w : IotaWitnessS E`. -/
theorem lamIotaAtDI_of_iotaWitnessS {E : ResolvedEnv} (w : IotaWitnessS E)
    (ρ : EnvI) (A B : Expr Nat) :
    LamIotaAtDI E ρ A B
      (foldApps (.const w.recRef w.ls) w.preMajor)
      (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
      (iotaRhsOfS w) :=
  lamIotaAtDI_of_iotaClause (iotaClauseUnderDI_of_iotaWitnessS w ρ)

/-- Unconditional discharge of `LamIotaAtDI` for every `DerivedIotaU E (.app f r) x` at `EnvWfT E`. -/
theorem lamIotaAtDI_of_derivedIotaU {E : ResolvedEnv} (hW : EnvWfT E)
    {f r x : Expr Nat} (hι : DerivedIotaU E (.app f r) x) (ρ : EnvI) (A B : Expr Nat) :
    LamIotaAtDI E ρ A B f r x :=
  lamIotaAtDI_of_iotaClause (iotaClauseUnderDI_of_derivedIotaU hW hι ρ)

/-- Unconditional discharge of `NoSpine` under a binder for every recursor eliminator
    `w : IotaWitnessS E`. -/
theorem noSpine_lift0_recursor_elim_approxDI {E : ResolvedEnv} (w : IotaWitnessS E)
    (ρ : EnvI) (us : List CptI) :
    NoSpine (denDI E (EnvI.cons (demand us) ρ)
      (lift 0 1 (foldApps (.const w.recRef w.ls) w.preMajor))) := by
  rw [denDI_lift0_one_eq]
  exact noSpine_recursor_elim_approxDI w ρ

/-- `LamIrrAtDI` from `IsPropIdealI`, `DomTyped`, and `NoSpine` in `ρ` (with `RcicNativePiModelK`'s
    `∀ us` quantifiers collapsed by `denDI_lift0_one_eq`). -/
theorem lamIrrAtDI_of_domTyped {E : ResolvedEnv} {ρ : EnvI} {A B f r : Expr Nat}
    (hA : IsPropIdealI E (denDI E ρ A))
    (hdom : DomTyped E (denDI E ρ A) (denDI E ρ f))
    (hns : NoSpine (denDI E ρ f)) :
    LamIrrAtDI E ρ A B f r := by
  refine pEqDI_of_semEqDI (semEqDI_lam_congrK (fun us => ?_))
  have hA' : IsPropIdealI E (denDI E (EnvI.cons (demand us) ρ) (lift 0 1 A)) := by
    rwa [denDI_lift0_one_eq]
  have hdom' : DomTyped E (denDI E (EnvI.cons (demand us) ρ) (lift 0 1 A))
      (denDI E (EnvI.cons (demand us) ρ) (lift 0 1 f)) := by
    rwa [denDI_lift0_one_eq, denDI_lift0_one_eq]
  have hns' : NoSpine (denDI E (EnvI.cons (demand us) ρ) (lift 0 1 f)) := by
    rwa [denDI_lift0_one_eq]
  exact semEqDI_app_stable hA' hdom' hns' (.bvar 0) (lift 0 1 r)

/-- `LamIrrAtDI` for any recursor eliminator `w : IotaWitnessS E`, with `NoSpine` discharged
    unconditionally by `noSpine_recursor_elim_approxDI`. -/
theorem lamIrrAtDI_of_domTyped_recursor {E : ResolvedEnv} (w : IotaWitnessS E)
    {ρ : EnvI} {A B r : Expr Nat}
    (hA : IsPropIdealI E (denDI E ρ A))
    (hdom : DomTyped E (denDI E ρ A)
      (denDI E ρ (foldApps (.const w.recRef w.ls) w.preMajor))) :
    LamIrrAtDI E ρ A B (foldApps (.const w.recRef w.ls) w.preMajor) r :=
  lamIrrAtDI_of_domTyped hA hdom (noSpine_recursor_elim_approxDI w ρ)

/-- `η-K` over `ApproxDI` for any admitted recursor `w : IotaWitnessS E`: both `(O3)` hypotheses
    of `RcicNativePiModelK.pEqI_etaK_of_eta_dom_iota` (`NoSpine` under the binder and
    `IotaClauseUnder`) are discharged unconditionally by `noSpine_recursor_elim_approxDI` and
    `lamIotaAtDI_of_iotaWitnessS`, and the `∀ us` quantifiers are collapsed by `denDI_lift0_one_eq`. -/
theorem pEqDI_etaK_of_eta_dom_iotaS {E : ResolvedEnv} (w : IotaWitnessS E)
    {ρ : EnvI} {A B : Expr Nat}
    (hη : EtaSoundAtDI E ρ A B (foldApps (.const w.recRef w.ls) w.preMajor))
    (hA : IsPropIdealI E (denDI E ρ A))
    (hdom : DomTyped E (denDI E ρ A)
      (denDI E ρ (foldApps (.const w.recRef w.ls) w.preMajor))) :
    PEqDI E ρ (.pi A B)
      (foldApps (.const w.recRef w.ls) w.preMajor)
      (.lam A (lift 0 1 (iotaRhsOfS w))) :=
  hη.symm.trans ((lamIrrAtDI_of_domTyped_recursor w (B := B)
    (r := foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) hA hdom).trans
    (lamIotaAtDI_of_iotaWitnessS w ρ A B))

/-! ## §12. Admitted Obstructions on Un-Restricted Π-Demands and Untyped `TypeSoundness`, and the Repaired `BotPiCpt` / `LRTypeINBiDI` Layer -/

/-! ### §12.1. Unconditional Refutation of `FundamentalLRI`, `FundamentalLRIN`, `FundamentalLRINT`, `FundamentalTermI`, `FundamentalLRINT_DI`, and `FundamentalTermDI` -/

/-- Bound variables are weak-head normal (`WhStep E (.bvar i) e` is impossible). -/
theorem whStep_bvar_false {E : ResolvedEnv} {i : Nat} {e : Expr Nat}
    (h : WhStep E (.bvar i) e) : False := by
  cases h with
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl

/-- Bound variables weak-head reduce only to themselves. -/
theorem whRed_bvar_eq {E : ResolvedEnv} {i : Nat} {e : Expr Nat}
    (h : WhRed E (.bvar i) e) : e = .bvar i := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStep_bvar_false hs).elim

/-- The closed impredicative Π-type `Π (P : Sort 0), P` (`idPiProp`). -/
def idPiProp : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- The Π compact `.pi .bot [([.sort], .sort)]` whose step demands `[.sort]` on `.bvar 0`. -/
def idPiPropSortStep : CptI := .pi .bot [([.sort], .sort)]

/-- `idPiProp` is well-typed at `.sort (.imax (.succ .zero) .zero)` in `[]` for every `E, n`. -/
def hasTyT_idPiProp (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] idPiProp (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort [] .zero)
    (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)

/-- `idPiPropSortStep` approximates `idPiProp` at `EnvI.bot` in raw `ApproxI`. -/
theorem approxI_idPiProp_sortStep : ApproxI EnvI.bot idPiProp idPiPropSortStep := by
  refine .pi (.bot _ _) (fun s hs => ?_)
  have heq := List.mem_singleton.mp hs
  subst heq
  exact .bvar (List.mem_singleton.mpr rfl)

/-- `idPiPropSortStep` approximates `idPiProp` at `EnvI.bot` in `ApproxDI E` for every `E`. -/
theorem approxDI_idPiProp_sortStep (E : ResolvedEnv) :
    ApproxDI E EnvI.bot idPiProp idPiPropSortStep := by
  refine .pi (.bot _ _) (fun s hs => ?_)
  have heq := List.mem_singleton.mp hs
  subst heq
  exact .bvar (List.mem_singleton.mpr rfl)

/-- `LRTypeI` (`RcicNativePiModelLR`) fails on `idPiProp` at `idPiPropSortStep` because its `.pi`
    clause checks `LRTypeI` on the un-instantiated codomain `.bvar 0` at `s.2 = .sort` even when
    `s.1 = [.sort]` is a non-`⊥` demand, forcing `WhRed E (.bvar 0) (.sort u)`. -/
theorem not_lrTypeI_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeI E n [] idPiProp idPiProp idPiPropSortStep := by
  intro h
  cases h with
  | pi h₁ _ _ _ _ rf =>
      have hEq := whRed_pi_eq h₁
      injection hEq with _ hB₁
      subst hB₁
      have hsort := rf ([.sort], .sort) (List.mem_singleton.mpr rfl)
      cases hsort with
      | sort hs _ =>
          have := whRed_bvar_eq hs
          cases this

/-- `LRTypeIN` (`RcicNativePiModelLRCases`) likewise fails on `idPiProp` at `idPiPropSortStep`. -/
theorem not_lrTypeIN_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeIN E n [] idPiProp idPiProp idPiPropSortStep := by
  intro h
  cases h with
  | pi h₁ _ _ _ _ _ rf =>
      have hEq := whRed_pi_eq h₁
      injection hEq with _ hB₁
      subst hB₁
      have hsort := rf ([.sort], .sort) (List.mem_singleton.mpr rfl)
      cases hsort with
      | sort hs _ =>
          have := whRed_bvar_eq hs
          cases this

/-- `LRTermI` (`RcicNativePiModelLRTerm`) fails on `idPiProp` at `idPiPropSortStep` at any sort. -/
theorem not_lrTermI_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) {u : Level} :
    ¬ LRTermI E n [] idPiProp idPiProp (.sort u) idPiPropSortStep := by
  intro h
  exact not_lrTypeIN_idPiProp_sortStep E n (lrTypeIN_of_lrTermI_sort idPiPropSortStep h)

/-- Unconditional refutation of `FundamentalLRI E n` (`RcicNativePiModelLR`) for every `E, n`. -/
theorem not_fundamentalLRI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRI E n :=
  fun F => not_lrTypeI_idPiProp_sortStep E n
    (F .nil (.refl [] idPiProp) idPiPropSortStep approxI_idPiProp_sortStep)

/-- Unconditional refutation of `FundamentalLRIN E n` (`RcicNativePiModelLRCases`) for every `E, n`. -/
theorem not_fundamentalLRIN (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRIN E n :=
  fun F => not_lrTypeIN_idPiProp_sortStep E n
    (F .nil (.refl [] idPiProp) idPiPropSortStep approxI_idPiProp_sortStep)

/-- Unconditional refutation of `FundamentalLRINT E n` (`RcicNativePiModelLRTerm`) for every `E, n`. -/
theorem not_fundamentalLRINT (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRINT E n :=
  fun F => not_lrTypeIN_idPiProp_sortStep E n
    (F .nil (hasTyT_idPiProp E n) (.refl [] idPiProp) idPiPropSortStep approxI_idPiProp_sortStep)

/-- Unconditional refutation of `FundamentalTermI E n` (`RcicNativePiModelLRTerm`) for every `E, n`
    (including `emptyEnv`, without any constant member). -/
theorem not_fundamentalTermI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermI E n :=
  fun F => not_lrTermI_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep approxI_idPiProp_sortStep)

/-- Unconditional refutation of un-restricted `FundamentalLRINT_DI E n` (§10) for every `E, n`. -/
theorem not_fundamentalLRINT_DI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRINT_DI E n :=
  fun F => not_lrTypeIN_idPiProp_sortStep E n
    (F .nil (hasTyT_idPiProp E n) (.refl [] idPiProp) idPiPropSortStep
      (approxDI_idPiProp_sortStep E))

/-- Unconditional refutation of un-restricted `FundamentalTermDI E n` (§10) for every `E, n`. -/
theorem not_fundamentalTermDI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermDI E n :=
  fun F => not_lrTermI_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep (approxDI_idPiProp_sortStep E))

/-! ### §12.2. Unconditional Refutations of `TypeSoundnessI` and `TypeSoundnessDI` -/

/-- The well-formed context `[.letBinding (Sort 1) (Sort 0)]` (`let X : Sort 1 := Sort 0`). -/
def zetaLocalSortCtx : LCtx := [.letBinding (.sort (.succ .zero)) (.sort .zero)]

/-- `zetaLocalSortCtx` is well-formed for every `E, n`. -/
def zetaLocalSortCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n zetaLocalSortCtx :=
  .letBinding [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
    .nil (.sort [] (.succ .zero)) (.sort [] .zero)

/-- `ConvT.zetaLocal` converts `.bvar 0` to `.sort .zero` at `.sort (.succ .zero)` in `zetaLocalSortCtx`. -/
def zetaLocalSortCtx_conv (E : ResolvedEnv) (n : Nat) :
    ConvT E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) :=
  .zetaLocal zetaLocalSortCtx 0 (.sort (.succ .zero)) (.sort .zero)
    rfl rfl (.sort zetaLocalSortCtx .zero)

/-- Unconditional refutation of `TypeSoundnessI E n` (`RcicNativePiModelLRTerm`) for every `E, n`:
    at `EnvI.bot`, `.bvar 0` denotes `{.bot}` while `.sort .zero` has `.sort`. -/
theorem not_typeSoundnessI (E : ResolvedEnv) (n : Nat) : ¬ TypeSoundnessI E n := by
  intro hS
  have h := (hS (zetaLocalSortCtx_wf E n) (zetaLocalSortCtx_conv E n) .sort).mpr
    (.sort EnvI.bot .zero)
  rcases approxI_bvar_inv h with h0 | h0 <;> cases h0

/-- Unconditional refutation of `TypeSoundnessDI E n` (§10) for every `E, n`. -/
theorem not_typeSoundnessDI (E : ResolvedEnv) (n : Nat) : ¬ TypeSoundnessDI E n := by
  intro hS
  have h := (hS (zetaLocalSortCtx_wf E n) (zetaLocalSortCtx_conv E n) .sort).mpr
    (.sort EnvI.bot .zero)
  rcases approxDI_bvar_inv h with h0 | h0 <;> cases h0

/-- Closed Π-type `Π (P : Sort 0) (F : P → Sort 0) (p : P) (q : P), F p` in `Γ = []`. -/
def closedIrrPiL : Expr Nat :=
  .pi (.sort .zero) (.pi (.pi (.bvar 0) (.sort .zero))
    (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))))

/-- Closed Π-type `Π (P : Sort 0) (F : P → Sort 0) (p : P) (q : P), F q` in `Γ = []`. -/
def closedIrrPiR : Expr Nat :=
  .pi (.sort .zero) (.pi (.pi (.bvar 0) (.sort .zero))
    (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0)))))

/-- The compact feeding `F ↦ [.lam [([.sort], .sort)]]`, `p ↦ [.sort]`, `q ↦ []`. -/
def closedIrrPiCpt : CptI :=
  .pi .bot [([], .pi .bot [([.lam [([.sort], .sort)]], .pi .bot [([.sort], .pi .bot [([], .sort)])])])]

/-- In the empty context `[]`, `closedIrrPiL` and `closedIrrPiR` are convertible at a sort
    by four `ConvT.pi` congruence steps over `ConvT.app (ConvT.refl F) (ConvT.irr P p q)`. -/
def closedIrrPi_conv (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] closedIrrPiL closedIrrPiR
      (.sort (.imax (.succ .zero) (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero))))) := by
  let Γ₁ : LCtx := [.assumption (.sort .zero)]
  let Γ₂ : LCtx := .assumption (.pi (.bvar 0) (.sort .zero)) :: Γ₁
  let Γ₃ : LCtx := .assumption (.bvar 1) :: Γ₂
  let Γ₄ : LCtx := .assumption (.bvar 2) :: Γ₃
  have hA₀ : HasTyT E n [] (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
  have hA₁ : HasTyT E n Γ₁ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₁ (.bvar 0) .zero (.sort .zero) (.succ .zero)
      (.bvar Γ₁ 0 (.sort .zero) rfl) (.sort _ .zero)
  have hA₂ : HasTyT E n Γ₂ (.bvar 1) (.sort .zero) := .bvar Γ₂ 1 (.sort .zero) rfl
  have hA₃ : HasTyT E n Γ₃ (.bvar 2) (.sort .zero) := .bvar Γ₃ 2 (.sort .zero) rfl
  have hP : HasTyT E n Γ₄ (.bvar 3) (.sort .zero) := .bvar Γ₄ 3 (.sort .zero) rfl
  have hF : HasTyT E n Γ₄ (.bvar 2) (.pi (.bvar 3) (.sort .zero)) :=
    .bvar Γ₄ 2 (.pi (.bvar 3) (.sort .zero)) rfl
  have hp : HasTyT E n Γ₄ (.bvar 1) (.bvar 3) := .bvar Γ₄ 1 (.bvar 3) rfl
  have hq : HasTyT E n Γ₄ (.bvar 0) (.bvar 3) := .bvar Γ₄ 0 (.bvar 3) rfl
  have hirr : ConvT E n Γ₄ (.bvar 1) (.bvar 0) (.bvar 3) :=
    .irr Γ₄ (.bvar 3) (.bvar 1) (.bvar 0) hP hp hq
  have hbody : ConvT E n Γ₄ (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 0)) (.sort .zero) :=
    .app Γ₄ (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0) (.bvar 3) (.sort .zero)
      (.refl Γ₄ (.bvar 2) _ hF) hirr
  exact .pi [] _ _ _ _ _ _ (.refl [] _ _ hA₀)
    (.pi Γ₁ _ _ _ _ _ _ (.refl Γ₁ _ _ hA₁)
      (.pi Γ₂ _ _ _ _ _ _ (.refl Γ₂ _ _ hA₂)
        (.pi Γ₃ _ _ _ _ _ _ (.refl Γ₃ _ _ hA₃) hbody)))

/-- `closedIrrPiCpt` approximates `closedIrrPiL` at `EnvI.bot` in both `ApproxDI` and `ApproxI`. -/
theorem approxDI_closedIrrPiL_cpt (E : ResolvedEnv) :
    ApproxDI E EnvI.bot closedIrrPiL closedIrrPiCpt := by
  refine .pi (.bot _ _) (fun s₁ hs₁ => ?_)
  rcases List.mem_singleton.mp hs₁ with rfl
  refine .pi (.bot _ _) (fun s₂ hs₂ => ?_)
  rcases List.mem_singleton.mp hs₂ with rfl
  refine .pi (.bot _ _) (fun s₃ hs₃ => ?_)
  rcases List.mem_singleton.mp hs₃ with rfl
  refine .pi (.bot _ _) (fun s₄ hs₄ => ?_)
  rcases List.mem_singleton.mp hs₄ with rfl
  refine .app (g := [([.sort], .sort)]) (s := ([.sort], .sort))
    (.bvar (List.mem_singleton.mpr rfl)) (List.mem_singleton.mpr rfl) (fun u hu => ?_)
  rcases List.mem_singleton.mp hu with rfl
  exact .bvar (List.mem_singleton.mpr rfl)

theorem approxI_closedIrrPiL_cpt : ApproxI EnvI.bot closedIrrPiL closedIrrPiCpt :=
  (approxDI_emptyEnv_iff EnvI.bot _ _).mp (approxDI_closedIrrPiL_cpt emptyEnv)

/-- `closedIrrPiCpt` does NOT approximate `closedIrrPiR` at `EnvI.bot` in `ApproxI` or `ApproxDI`. -/
theorem not_approxDI_closedIrrPiR_cpt (E : ResolvedEnv) :
    ¬ ApproxDI E EnvI.bot closedIrrPiR closedIrrPiCpt := by
  intro h
  rcases approxDI_pi_inv h with h0 | ⟨_, _, heq₁, _, hf₁⟩
  · cases h0
  · cases heq₁
    have h₂ := hf₁ _ (List.mem_singleton.mpr rfl)
    rcases approxDI_pi_inv h₂ with h0 | ⟨_, _, heq₂, _, hf₂⟩
    · cases h0
    · cases heq₂
      have h₃ := hf₂ _ (List.mem_singleton.mpr rfl)
      rcases approxDI_pi_inv h₃ with h0 | ⟨_, _, heq₃, _, hf₃⟩
      · cases h0
      · cases heq₃
        have h₄ := hf₃ _ (List.mem_singleton.mpr rfl)
        rcases approxDI_pi_inv h₄ with h0 | ⟨_, _, heq₄, _, hf₄⟩
        · cases h0
        · cases heq₄
          have happ := hf₄ _ (List.mem_singleton.mpr rfl)
          rcases approxDI_app_inv happ with h0 | ⟨g, s, heq₅, hF, hs, ha⟩ | ⟨_, _, _, heq₅, _, _⟩
          · cases h0
          · rcases approxDI_bvar_inv hF with h0 | hF'
            · cases h0
            · have heqg := List.mem_singleton.mp hF'
              injection heqg with hg
              subst hg
              rcases List.mem_singleton.mp hs with rfl
              have hq := ha .sort (List.mem_singleton.mpr rfl)
              rcases approxDI_bvar_inv hq with h0 | hq'
              · cases h0
              · exact List.not_mem_nil _ hq'
          · cases heq₅

theorem not_approxI_closedIrrPiR_cpt : ¬ ApproxI EnvI.bot closedIrrPiR closedIrrPiCpt := by
  intro h
  exact not_approxDI_closedIrrPiR_cpt emptyEnv ((approxDI_emptyEnv_iff EnvI.bot _ _).mpr h)

/-- Even in the empty context `[]` (closed types, no `letBinding`), `closedIrrPiL` and `closedIrrPiR`
    are convertible at a sort (`closedIrrPi_conv`) yet neither `SemEqI EnvI.bot` nor
    `SemEqDI E EnvI.bot` holds. -/
theorem not_semEqI_closedIrrPi : ¬ SemEqI EnvI.bot closedIrrPiL closedIrrPiR :=
  fun h => not_approxI_closedIrrPiR_cpt ((h closedIrrPiCpt).mp approxI_closedIrrPiL_cpt)

theorem not_semEqDI_closedIrrPi (E : ResolvedEnv) :
    ¬ SemEqDI E EnvI.bot closedIrrPiL closedIrrPiR :=
  fun h => not_approxDI_closedIrrPiR_cpt E ((h closedIrrPiCpt).mp (approxDI_closedIrrPiL_cpt E))

/-! ### §12.3. The Repaired `BotDemand` / `BotPiCpt` / `LRTypeINBiDI` Layer without `WhDet` or `TypeSoundness` -/

/-- A demand list `us : List CptI` is a `BotDemand` iff every element in `us` is `.bot`. -/
def BotDemand (us : List CptI) : Prop := ∀ u ∈ us, u = .bot

theorem botDemand_nil : BotDemand [] := fun _ h => (List.not_mem_nil _ h).elim

/-- Monotonicity of `ApproxDI` on non-`⊥` compacts (`c ≠ .bot`), since `.bot` approximates
    every expression in every environment via `ApproxDI.bot`. -/
theorem approxDI_mono_env_nonbot {E : ResolvedEnv} {ρ ρ' : EnvI}
    (hle : ∀ i c, c ≠ .bot → ρ i c → ρ' i c) {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) : ApproxDI E ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | @bvar ρ i c h =>
      cases c with
      | bot => exact .bot _ _
      | sort => exact .bvar (hle i .sort (fun h => nomatch h) h)
      | pi a f => exact .bvar (hle i (.pi a f) (fun h => nomatch h) h)
      | spine r args => exact .bvar (hle i (.spine r args) (fun h => nomatch h) h)
      | lam g => exact .bvar (hle i (.lam g) (fun h => nomatch h) h)
  | sort => exact .sort _ _
  | pi _ _ ihA ihB =>
      refine .pi (ihA hle) (fun s hs => ihB s hs ?_)
      intro i c hc
      cases i with
      | zero => exact id
      | succ i => exact hle i c hc
  | lam _ ihb =>
      refine .lam (fun s hs => ihb s hs ?_)
      intro i c hc
      cases i with
      | zero => exact id
      | succ i => exact hle i c hc
  | app _ hs _ ihf iha =>
      exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const _ _ _ hrig => exact .const _ _ _ hrig
  | delta hd h => exact .delta hd h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

theorem approxDI_cons_botDemand_iff {E : ResolvedEnv} {ρ : EnvI} {us : List CptI}
    (h : BotDemand us) (e : Expr Nat) (c : CptI) :
    ApproxDI E (EnvI.cons (demand us) ρ) e c ↔ ApproxDI E (EnvI.cons (EnvI.bot 0) ρ) e c := by
  constructor
  · refine approxDI_mono_env_nonbot (fun i u hne => ?_)
    cases i with
    | zero => intro hu; exact (hne (h u hu)).elim
    | succ i => exact id
  · refine approxDI_mono_env_nonbot (fun i u hne => ?_)
    cases i with
    | zero => intro hu; exact (hne hu).elim
    | succ i => exact id

/-- Extending `EnvI.bot` by a `BotDemand` leaves `ApproxDI` invariant (`EnvI.cons (demand us) EnvI.bot ≡ EnvI.bot`). -/
theorem approxDI_cons_botDemand_bot_iff {E : ResolvedEnv} {us : List CptI}
    (h : BotDemand us) (e : Expr Nat) (c : CptI) :
    ApproxDI E (EnvI.cons (demand us) EnvI.bot) e c ↔ ApproxDI E EnvI.bot e c := by
  refine (approxDI_cons_botDemand_iff h e c).trans ⟨approxDI_mono_env ?_, approxDI_mono_env ?_⟩
  · intro i u; cases i <;> exact id
  · intro i u; cases i <;> exact id

/-- The inductive sub-family of compacts built from `.bot`, `.sort`, and `.pi a f` where every
    step `s ∈ f` has a `BotDemand` (`∀ u ∈ s.1, u = .bot`) and a `BotPiCpt` output `s.2`. -/
inductive BotPiCpt : CptI → Prop
  | bot : BotPiCpt .bot
  | sort : BotPiCpt .sort
  | pi {a : CptI} {f : List (List CptI × CptI)}
      (ha : BotPiCpt a)
      (hbd : ∀ s ∈ f, BotDemand s.1)
      (hf : ∀ s ∈ f, BotPiCpt s.2) :
      BotPiCpt (.pi a f)

theorem botPiCpt_pi_bot_nil : BotPiCpt (.pi .bot []) :=
  .pi .bot (fun _ h => (List.not_mem_nil _ h).elim) (fun _ h => (List.not_mem_nil _ h).elim)

theorem botPiCpt_pi_nil_step {a b : CptI} (ha : BotPiCpt a) (hb : BotPiCpt b) :
    BotPiCpt (.pi a [([], b)]) :=
  .pi ha
    (fun s hs => by rcases List.mem_singleton.mp hs with rfl; exact botDemand_nil)
    (fun s hs => by rcases List.mem_singleton.mp hs with rfl; exact hb)

theorem not_botPiCpt_spine (r : Nat) (args : List CptI) : ¬ BotPiCpt (.spine r args) :=
  fun h => nomatch h

theorem not_botPiCpt_lam (g : List (List CptI × CptI)) : ¬ BotPiCpt (.lam g) :=
  fun h => nomatch h

/-- `idPiPropSortStep = .pi .bot [([.sort], .sort)]` is excluded by `BotPiCpt`. -/
theorem not_botPiCpt_idPiPropSortStep : ¬ BotPiCpt idPiPropSortStep := by
  intro h
  cases h with
  | pi _ hbd _ =>
      have := hbd ([.sort], .sort) (List.mem_singleton.mpr rfl) .sort (List.mem_singleton.mpr rfl)
      cases this

/-- Key theorem eliminating `TypeSoundness` on `BotPiCpt` compacts: at every `EnvWfT E`,
    `LRTypeIN E n Γ A B c` on a `BotPiCpt c` implies **both** `ApproxDI E EnvI.bot A c`
    and `ApproxDI E EnvI.bot B c` (by `approxDI_whRed_back` and `approxDI_cons_botDemand_bot_iff`). -/
theorem approxDI_of_lrTypeIN_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : LRTypeIN E n Γ A B c) :
    ApproxDI E EnvI.bot A c ∧ ApproxDI E EnvI.bot B c := by
  induction h with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort hA hB =>
      exact ⟨approxDI_sort_of_whRed hW hA EnvI.bot, approxDI_sort_of_whRed hW hB EnvI.bot⟩
  | @pi Γ A B A₁ B₁ A₂ B₂ a f hA hB _ _ _ _ _ iha ihf =>
      cases hc with
      | pi ha hbd hf =>
          obtain ⟨ha₁, ha₂⟩ := iha ha
          have hf₁ : ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2 :=
            fun s hs => (approxDI_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mpr (ihf s hs (hf s hs)).1
          have hf₂ : ∀ s ∈ f, ApproxDI E (EnvI.cons (demand s.1) EnvI.bot) B₂ s.2 :=
            fun s hs => (approxDI_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mpr (ihf s hs (hf s hs)).2
          exact ⟨approxDI_whRed_back hW hA (.pi ha₁ hf₁),
                 approxDI_whRed_back hW hB (.pi ha₂ hf₂)⟩
  | spine => cases hc

/-- Bidirectional `BotPiCpt`-restricted logical relation over `ApproxDI E EnvI.bot`:
    for every `BotPiCpt c` approximating either `A` or `B`, `LRTypeIN E n Γ A B c` holds. -/
def LRTypeINBiDI (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c → (ApproxDI E EnvI.bot A c ∨ ApproxDI E EnvI.bot B c) → LRTypeIN E n Γ A B c

/-- Diagonal case for `.bvar i`: at `EnvI.bot`, `.bvar i` has only `.bot`. -/
theorem lrTypeINBiDI_bvar_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) :
    LRTypeINBiDI E n Γ (.bvar i) (.bvar i) := by
  intro c _ h
  have hb : ApproxDI E EnvI.bot (.bvar i) c := h.elim id id
  rcases approxDI_bvar_inv hb with rfl | h0
  · exact .bot _ _ _
  · cases h0
    exact .bot _ _ _

/-- Conversion and diagonal case for `.sort l₁` and `.sort l₂`. -/
theorem lrTypeINBiDI_sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) :
    LRTypeINBiDI E n Γ (.sort l₁) (.sort l₂) := by
  intro c _ h
  rcases h with h | h
  · rcases approxDI_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact lrTypeIN_sort_congr Γ l₁ l₂
  · rcases approxDI_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact lrTypeIN_sort_congr Γ l₁ l₂

theorem lrTypeINBiDI_sort_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    LRTypeINBiDI E n Γ (.sort l) (.sort l) :=
  lrTypeINBiDI_sorts E n Γ l l

/-- Conversion and diagonal case for any `RigidConst E r`: its only `BotPiCpt` compact is `.bot`. -/
theorem lrTypeINBiDI_rigidConsts {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    {r : Nat} (ls ls' : List Level) (hrig : RigidConst E r) :
    LRTypeINBiDI E n Γ (.const r ls) (.const r ls') := by
  intro c hc h
  rcases h with h | h
  · rcases approxDI_rigid_const_inv hrig h with rfl | rfl
    · exact .bot _ _ _
    · cases hc
  · rcases approxDI_rigid_const_inv hrig h with rfl | rfl
    · exact .bot _ _ _
    · cases hc

theorem lrTypeINBiDI_rigidConst_diag {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    {r : Nat} (ls : List Level) (hrig : RigidConst E r) :
    LRTypeINBiDI E n Γ (.const r ls) (.const r ls) :=
  lrTypeINBiDI_rigidConsts n Γ ls ls hrig

/-- The `.pi` congruence case of `LRTypeINBiDI` at `EnvI.bot`: because `BotPiCpt` restricts
    every step `s ∈ f` to `BotDemand s.1`, `EnvI.cons (demand s.1) EnvI.bot` reduces directly
    to `EnvI.bot` (`approxDI_cons_botDemand_bot_iff`), closing `.pi` at `EnvI.bot` from `ihA`
    and `ihB` at `EnvI.bot` without related substitutions. -/
theorem lrTypeINBiDI_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (ihA : LRTypeINBiDI E n Γ A₁ A₂)
    (ihB : LRTypeINBiDI E n (.assumption A₁ :: Γ) B₁ B₂) :
    LRTypeINBiDI E n Γ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro c hc h
  rcases h with h₁ | h₂
  · rcases approxDI_pi_inv h₁ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine lrTypeIN_pi_congr hΓ₁ hdom hcod (ihA a hca (Or.inl ha)) (fun s hs => ?_)
          have hb := (approxDI_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inl hb)
  · rcases approxDI_pi_inv h₂ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine lrTypeIN_pi_congr hΓ₁ hdom hcod (ihA a hca (Or.inr ha)) (fun s hs => ?_)
          have hb := (approxDI_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inr hb)

theorem lrTypeINBiDI_pi_diag {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (ihA : LRTypeINBiDI E n Γ A A)
    (ihB : LRTypeINBiDI E n (.assumption A :: Γ) B B) :
    LRTypeINBiDI E n Γ (.pi A B) (.pi A B) :=
  lrTypeINBiDI_pi hΓ₁ (.refl Γ A) (.refl (.assumption A :: Γ) B) ihA ihB

/-- Positive repair of Obstruction §12.1: `idPiProp = .pi (.sort .zero) (.bvar 0)` satisfies
    `LRTypeINBiDI E n [] idPiProp idPiProp` unconditionally for every `E, n`. -/
theorem lrTypeINBiDI_idPiProp (E : ResolvedEnv) (n : Nat) :
    LRTypeINBiDI E n [] idPiProp idPiProp :=
  lrTypeINBiDI_pi_diag
    (.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero))
    (lrTypeINBiDI_sort_diag E n [] .zero)
    (lrTypeINBiDI_bvar_diag E n [.assumption (.sort .zero)] 0)

/-- Positive repair of Obstruction §12.2: the closed `ConvT.irr`-under-`ConvT.pi` pair
    `closedIrrPiL` and `closedIrrPiR` satisfies `LRTypeINBiDI E n [] closedIrrPiL closedIrrPiR`
    unconditionally for every `E, n`. -/
theorem lrTypeINBiDI_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    LRTypeINBiDI E n [] closedIrrPiL closedIrrPiR := by
  let Γ₁ : LCtx := [.assumption (.sort .zero)]
  let Γ₂ : LCtx := .assumption (.pi (.bvar 0) (.sort .zero)) :: Γ₁
  let Γ₃ : LCtx := .assumption (.bvar 1) :: Γ₂
  let Γ₄ : LCtx := .assumption (.bvar 2) :: Γ₃
  have hΓ₁ : CtxWfT E n Γ₁ := .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)
  have hA₁ : HasTyT E n Γ₁ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₁ (.bvar 0) .zero (.sort .zero) (.succ .zero)
      (.bvar Γ₁ 0 (.sort .zero) rfl) (.sort _ .zero)
  have hΓ₂ : CtxWfT E n Γ₂ := .assumption Γ₁ _ _ hΓ₁ hA₁
  have hΓ₃ : CtxWfT E n Γ₃ := .assumption Γ₂ (.bvar 1) .zero hΓ₂ (.bvar Γ₂ 1 (.sort .zero) rfl)
  have hΓ₄ : CtxWfT E n Γ₄ := .assumption Γ₃ (.bvar 2) .zero hΓ₃ (.bvar Γ₃ 2 (.sort .zero) rfl)
  have hP : HasTyT E n Γ₄ (.bvar 3) (.sort .zero) := .bvar Γ₄ 3 (.sort .zero) rfl
  have hF : HasTyT E n Γ₄ (.bvar 2) (.pi (.bvar 3) (.sort .zero)) :=
    .bvar Γ₄ 2 (.pi (.bvar 3) (.sort .zero)) rfl
  have hp : HasTyT E n Γ₄ (.bvar 1) (.bvar 3) := .bvar Γ₄ 1 (.bvar 3) rfl
  have hq : HasTyT E n Γ₄ (.bvar 0) (.bvar 3) := .bvar Γ₄ 0 (.bvar 3) rfl
  have hbodyConv : ConvT E n Γ₄ (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 0)) (.sort .zero) :=
    .app Γ₄ (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0) (.bvar 3) (.sort .zero)
      (.refl Γ₄ (.bvar 2) _ hF) (.irr Γ₄ (.bvar 3) (.bvar 1) (.bvar 0) hP hp hq)
  have hcod₃ : ConvT E n Γ₃ (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))
      (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0))) (.sort (.imax .zero .zero)) :=
    .pi Γ₃ _ _ _ _ .zero .zero (.refl Γ₃ _ _ (.bvar Γ₃ 2 (.sort .zero) rfl)) hbodyConv
  have hcod₂ : ConvT E n Γ₂ (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1))))
      (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0))))
      (.sort (.imax .zero (.imax .zero .zero))) :=
    .pi Γ₂ _ _ _ _ .zero _ (.refl Γ₂ _ _ (.bvar Γ₂ 1 (.sort .zero) rfl)) hcod₃
  have hcod₁ : ConvT E n Γ₁
      (.pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))))
      (.pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0)))))
      (.sort (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)))) :=
    .pi Γ₁ _ _ _ _ _ _ (.refl Γ₁ _ _ hA₁) hcod₂
  have hinner : LRTypeINBiDI E n Γ₄ (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 0)) := by
    intro c _ h
    rcases h with h | h
    · rcases approxDI_app_inv h with rfl | ⟨_, _, _, hf, _, _⟩ | ⟨_, _, _, _, hf, _⟩
      · exact .bot _ _ _
      · rcases approxDI_bvar_inv hf with h0 | h0 <;> cases h0
      · rcases approxDI_bvar_inv hf with h0 | h0 <;> cases h0
    · rcases approxDI_app_inv h with rfl | ⟨_, _, _, hf, _, _⟩ | ⟨_, _, _, _, hf, _⟩
      · exact .bot _ _ _
      · rcases approxDI_bvar_inv hf with h0 | h0 <;> cases h0
      · rcases approxDI_bvar_inv hf with h0 | h0 <;> cases h0
  exact lrTypeINBiDI_pi hΓ₁ (.refl [] _) (.of Γ₁ _ _ _ hcod₁)
    (lrTypeINBiDI_sort_diag E n [] .zero)
    (lrTypeINBiDI_pi hΓ₂ (.refl Γ₁ _) (.of Γ₂ _ _ _ hcod₂)
      (lrTypeINBiDI_pi_diag
        (.assumption Γ₁ (.bvar 0) .zero hΓ₁ (.bvar Γ₁ 0 (.sort .zero) rfl))
        (lrTypeINBiDI_bvar_diag E n Γ₁ 0)
        (lrTypeINBiDI_sort_diag E n (.assumption (.bvar 0) :: Γ₁) .zero))
      (lrTypeINBiDI_pi hΓ₃ (.refl Γ₂ _) (.of Γ₃ _ _ _ hcod₃)
        (lrTypeINBiDI_bvar_diag E n Γ₂ 1)
        (lrTypeINBiDI_pi hΓ₄ (.refl Γ₃ _) (.of Γ₄ _ _ _ hbodyConv)
          (lrTypeINBiDI_bvar_diag E n Γ₃ 2) hinner)))

/-- Symmetry of `LRTypeINBiDI` at `EnvWfT E` (without `TypeSoundness`). -/
theorem lrTypeINBiDI_symm {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} (h : LRTypeINBiDI E n Γ A B) :
    LRTypeINBiDI E n Γ B A :=
  fun c hc hBA => lrTypeIN_symm hcl hW (h c hc hBA.symm)

/-- Transitivity of `LRTypeINBiDI` at `EnvWfT E` (without `WhDet` and without `TypeSoundness`,
    using `approxDI_of_lrTypeIN_botPiCpt` and `lrTypeIN_trans_of_envWfT`). -/
theorem lrTypeINBiDI_trans {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) (hW : EnvWfT E)
    {Γ : LCtx} {A B C : Expr Nat}
    (h₁ : LRTypeINBiDI E n Γ A B) (h₂ : LRTypeINBiDI E n Γ B C) :
    LRTypeINBiDI E n Γ A C := by
  intro c hc hAC
  rcases hAC with hA | hC
  · have r₁ := h₁ c hc (Or.inl hA)
    have hB := (approxDI_of_lrTypeIN_botPiCpt hW hc r₁).2
    exact lrTypeIN_trans_of_envWfT hcl hW r₁ (h₂ c hc (Or.inl hB))
  · have r₂ := h₂ c hc (Or.inr hC)
    have hB := (approxDI_of_lrTypeIN_botPiCpt hW hc r₂).1
    exact lrTypeIN_trans_of_envWfT hcl hW (h₁ c hc (Or.inr hB)) r₂

/-- Weak-head step conversion in `LRTypeINBiDI` from the diagonal on the contractum. -/
theorem lrTypeINBiDI_of_whStep {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} (hs : WhStep E M M')
    (hdiag : LRTypeINBiDI E n Γ M' M') :
    LRTypeINBiDI E n Γ M M' := by
  intro c hc h
  have hM' : ApproxDI E EnvI.bot M' c :=
    h.elim (fun hM => (semEqDI_whStep hW hs EnvI.bot c).mp hM) id
  exact lrTypeIN_expand (.step hs (.refl _)) (.refl _) (hdiag c hc (Or.inl hM'))

/-- Diagonal weak-head step reduction in `LRTypeINBiDI` (for `HasTyT.letE`, `DeltaConst`, `HasTyT.lit`). -/
theorem lrTypeINBiDI_diag_of_whStep {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} (hs : WhStep E M M')
    (hdiag : LRTypeINBiDI E n Γ M' M') :
    LRTypeINBiDI E n Γ M M := by
  intro c hc h
  have hM : ApproxDI E EnvI.bot M c := h.elim id id
  have hM' : ApproxDI E EnvI.bot M' c := (semEqDI_whStep hW hs EnvI.bot c).mp hM
  exact lrTypeIN_expand (.step hs (.refl _)) (.step hs (.refl _)) (hdiag c hc (Or.inl hM'))

theorem lrTypeINBiDI_beta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (A b a : Expr Nat)
    (hdiag : LRTypeINBiDI E n Γ (instantiate0 a b) (instantiate0 a b)) :
    LRTypeINBiDI E n Γ (.app (.lam A b) a) (instantiate0 a b) :=
  lrTypeINBiDI_of_whStep hW (.beta A b a) hdiag

theorem lrTypeINBiDI_zeta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (A v b : Expr Nat)
    (hdiag : LRTypeINBiDI E n Γ (instantiate0 v b) (instantiate0 v b)) :
    LRTypeINBiDI E n Γ (.letE A v b) (instantiate0 v b) :=
  lrTypeINBiDI_of_whStep hW (.zeta A v b) hdiag

theorem lrTypeINBiDI_delta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : LRTypeINBiDI E n Γ (instantiateLevels ls b) (instantiateLevels ls b)) :
    LRTypeINBiDI E n Γ (.const r ls) (instantiateLevels ls b) :=
  lrTypeINBiDI_of_whStep hW (.delta hres hbody) hdiag

theorem lrTypeINBiDI_iota {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {lhs rhs : Expr Nat} (hι : DerivedIotaU E lhs rhs)
    (hdiag : LRTypeINBiDI E n Γ rhs rhs) :
    LRTypeINBiDI E n Γ lhs rhs :=
  lrTypeINBiDI_of_whStep hW (.iota hι) hdiag

theorem lrTypeINBiDI_lit {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (t : Nat)
    (hdiag : LRTypeINBiDI E n Γ (natExpand t) (natExpand t)) :
    LRTypeINBiDI E n Γ (.lit t) (natExpand t) :=
  lrTypeINBiDI_of_whStep hW (.lit t) hdiag

theorem lrTypeINBiDI_letE_diag {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (A v b : Expr Nat)
    (hdiag : LRTypeINBiDI E n Γ (instantiate0 v b) (instantiate0 v b)) :
    LRTypeINBiDI E n Γ (.letE A v b) (.letE A v b) :=
  lrTypeINBiDI_diag_of_whStep hW (.zeta A v b) hdiag

theorem lrTypeINBiDI_deltaConst_diag {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : LRTypeINBiDI E n Γ (instantiateLevels ls b) (instantiateLevels ls b)) :
    LRTypeINBiDI E n Γ (.const r ls) (.const r ls) :=
  lrTypeINBiDI_diag_of_whStep hW (.delta hres hbody) hdiag

theorem lrTypeINBiDI_lit_diag {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (t : Nat)
    (hdiag : LRTypeINBiDI E n Γ (natExpand t) (natExpand t)) :
    LRTypeINBiDI E n Γ (.lit t) (.lit t) :=
  lrTypeINBiDI_diag_of_whStep hW (.lit t) hdiag

/-- The `BotPiCpt`-restricted typed type-level fundamental lemma over `ApproxDI`
    (repairing `FundamentalLRINT_DI` from §10). -/
def FundamentalLRINBotDI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c → LRTypeIN E n Γ A A' c

/-- `FundamentalLRINBotDI E n` follows from its diagonal (`refl`) and single-link (`ConvT`)
    cases at `EnvWfT E` **without `WhDet E` and without `TypeSoundnessDI E n`**
    (because `approxDI_of_lrTypeIN_botPiCpt` transports `BotPiCpt` compacts across the
    middle type `M` directly from `ih₁`). -/
theorem fundamentalLRINBotDI_of_links {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level},
      HasTyT E n Γ A (.sort u) → ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c →
      LRTypeIN E n Γ A A c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
      ConvT E n Γ A B (.sort u) → ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c →
      LRTypeIN E n Γ A B c) :
    FundamentalLRINBotDI E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hc hcA; exact hdiag hΓ hA c hc hcA
  | of A B v hc => intro _ _ c hcpt hcA; exact hlink hΓ hc c hcpt hcA
  | trans A M B c₁ c₂ ih₁ ih₂ =>
      intro u hA c hcpt hcA
      obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA
      have r₁ := ih₁ hA c hcpt hcA
      have hcM := (approxDI_of_lrTypeIN_botPiCpt hW hcpt r₁).2
      exact lrTypeIN_trans_of_envWfT hcl hW r₁ (ih₂ hM c hcpt hcM)

/-- Π-injectivity (`piRow` shape) from `FundamentalLRINBotDI`: uses `c = .pi .bot []`,
    which satisfies `BotPiCpt` (`botPiCpt_pi_bot_nil`). -/
theorem piRow_of_fundamentalLRINBotDI {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRINBotDI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrTypeIN_pi_components
      (F hΓ hPi hc (.pi .bot []) botPiCpt_pi_bot_nil (approxDI_pi_bot_nil E EnvI.bot A B))

/-- Disjointness of Π and Sort under `TyConvT` from `FundamentalLRINBotDI`. -/
theorem not_tyConvT_pi_sort_of_fundamentalLRINBotDI {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRINBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (A B : Expr Nat) (l : Level)
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · cases heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have h := F hΓ hPi hc (.pi .bot []) botPiCpt_pi_bot_nil (approxDI_pi_bot_nil E EnvI.bot A B)
    cases h with
    | pi _ h' _ _ _ _ _ => exact nomatch whRed_sort_eq h'

/-! ## §13. Discharging `RcicNativePiModelK` Interfaces & Unconditional Refutations of `IrrCaseT` and `EtaCaseT` (`RcicNativePiModelTermIrr`, Batch 179) -/

open Rcic.Declarative.NativeValleys.PiModelKAudit
open Rcic.Declarative.NativeValleys.PiModelTermAudit

/-! ### §13.1. Connecting to `RcicNativePiModelK` (`PiModelKAudit`): Raw Refutations, `MajorStableDI` / `IotaSoundAtDI`, and Positive η-Calculus -/

/-- `.spine 0 []` (`Nat`) is not a proposition code in `natEnv`. -/
theorem not_isPropC_natEnv_spine0 : ¬ IsPropC natEnv (.spine 0 []) := by
  intro h
  cases h with
  | spine hres hsort =>
      have hm : _ = natFamMember := Option.some.inj hres.symm
      subst hm
      cases hsort

/-- Raw `PiModelKAudit.IotaClauseUnder` (`RcicNativePiModelK`) is refuted on `wZero` in `natEnv`
    for every `ρ : EnvI`. -/
theorem not_iotaClauseUnder_wZero (ρ : EnvI) :
    ¬ PiModelKAudit.IotaClauseUnder ρ
        (foldApps (.const wZero.recRef wZero.ls) wZero.preMajor)
        (ctorMajor wZero) (iotaRhsOf wZero) := by
  intro h
  have h0 : SemEqI (EnvI.cons (demand []) ρ) (iotaLhsOf wZero) (iotaRhsOf wZero) := by
    simpa [iotaLhsOf, recCall, foldApps_snoc] using h []
  exact (wZero_unsound_raw_approxI (EnvI.cons (demand []) ρ)).1 h0

/-- Raw `PiModelKAudit.IotaSoundAt` (`RcicNativePiModelK`) is refuted on `wZero` at type
    `.const 0 []` (`Nat`) in `natEnv` for every `ρ : EnvI`. -/
theorem not_iotaSoundAt_wZero (ρ : EnvI) :
    ¬ PiModelKAudit.IotaSoundAt natEnv ρ (.const 0 [])
        (foldApps (.const wZero.recRef wZero.ls) wZero.preMajor)
        (ctorMajor wZero) (iotaRhsOf wZero) := by
  intro h
  have hlhsEq :
      Expr.app (foldApps (.const wZero.recRef wZero.ls) wZero.preMajor) (ctorMajor wZero) =
        iotaLhsOf wZero := by
    simp [iotaLhsOf, recCall, foldApps_snoc]
  have hrhsProj : tprojI natEnv (denI ρ (.const 0 [])) (denI ρ (iotaRhsOf wZero)) (.spine 1 []) :=
    ⟨.const ρ 1 [], .spine 0 [], .const ρ 0 [], .spine not_isPropC_natEnv_spine0⟩
  have hlhsProj := (h (.spine 1 [])).mpr hrhsProj
  rw [hlhsEq] at hlhsProj
  rcases approxI_foldApps_const_head_inv hlhsProj.1 with h0 | ⟨_, h0⟩ <;> cases h0

/-- Eliminator stability in its major premise in `PEqDI` (counterpart to
    `PiModelKAudit.MajorStable`). -/
def MajorStableDI (E : ResolvedEnv) (ρ : EnvI) (P T R : Expr Nat) : Prop :=
  ∀ x y, PEqDI E ρ P x y → PEqDI E ρ T (.app R x) (.app R y)

/-- ι-soundness at the canonical proof `c` in `PEqDI` (counterpart to
    `PiModelKAudit.IotaSoundAt`). -/
def IotaSoundAtDI (E : ResolvedEnv) (ρ : EnvI) (T R c m : Expr Nat) : Prop :=
  PEqDI E ρ T (.app R c) m

/-- Unconditional discharge of `IotaSoundAtDI` for every `w : IotaWitnessS E` and `ρ : EnvI`
    (repairing `not_iotaSoundAt_wZero`). -/
theorem iotaSoundAtDI_of_iotaWitnessS {E : ResolvedEnv} (w : IotaWitnessS E)
    (ρ : EnvI) (T : Expr Nat) :
    IotaSoundAtDI E ρ T (foldApps (.const w.recRef w.ls) w.preMajor)
      (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
      (iotaRhsOfS w) := by
  have hlhs :
      Expr.app (foldApps (.const w.recRef w.ls) w.preMajor)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) =
        iotaLhsOfS w := by
    simp [iotaLhsOfS, recCall, foldApps_snoc]
  unfold IotaSoundAtDI
  rw [hlhs]
  exact pEqDI_iotaS w ρ T

/-- Discharge of `IotaSoundAtDI` for any `DerivedIotaU E (.app R c) m` under `EnvWfT E`. -/
theorem iotaSoundAtDI_of_derivedIotaU {E : ResolvedEnv} (hW : EnvWfT E)
    (ρ : EnvI) (T : Expr Nat) {R c m : Expr Nat}
    (hι : DerivedIotaU E (.app R c) m) :
    IotaSoundAtDI E ρ T R c m :=
  pEqDI_iotaU_of_envWfT hW hι ρ T

/-- `MajorStableDI` from `DomTyped` and `NoSpine` in `ApproxDI`. -/
theorem majorStableDI_of_domTyped {E : ResolvedEnv} {ρ : EnvI} {P T R : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P))
    (hdom : DomTyped E (denDI E ρ P) (denDI E ρ R))
    (hns : NoSpine (denDI E ρ R)) :
    MajorStableDI E ρ P T R :=
  fun x y _ => pEqDI_app_stable T hP hdom hns x y

/-- `MajorStableDI` for any recursor eliminator `foldApps (.const w.recRef ls) w.preMajor` from
    `DomTyped` alone (`NoSpine` is discharged unconditionally by `noSpine_recursor_prefix_approxDI`). -/
theorem majorStableDI_of_domTyped_recursor {E : ResolvedEnv} (w : IotaWitnessS E)
    (ls : List Level) {ρ : EnvI} {P T : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P))
    (hdom : DomTyped E (denDI E ρ P) (denDI E ρ (foldApps (.const w.recRef ls) w.preMajor))) :
    MajorStableDI E ρ P T (foldApps (.const w.recRef ls) w.preMajor) :=
  majorStableDI_of_domTyped hP hdom (noSpine_recursor_prefix_approxDI w ls ρ w.preMajor (Nat.le_refl _))

/-- K in `PEqDI` from `IsPropIdealI`, `MajorStableDI`, and `IotaSoundAtDI`
    (counterpart to `PiModelKAudit.pEqI_K`). -/
theorem pEqDI_K {E : ResolvedEnv} {ρ : EnvI} {P T R c m : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P))
    (hs : MajorStableDI E ρ P T R)
    (hι : IotaSoundAtDI E ρ T R c m)
    (h : Expr Nat) : PEqDI E ρ T (.app R h) m :=
  (hs h c (pEqDI_irr hP h c)).trans hι

/-- K in `PEqDI` from `IsPropIdealI`, `DomTyped`, `NoSpine`, and `IotaSoundAtDI`
    (counterpart to `PiModelKAudit.pEqI_K_of_domTyped`). -/
theorem pEqDI_K_of_domTyped {E : ResolvedEnv} {ρ : EnvI} {P T R c m : Expr Nat}
    (hP : IsPropIdealI E (denDI E ρ P))
    (hdom : DomTyped E (denDI E ρ P) (denDI E ρ R))
    (hns : NoSpine (denDI E ρ R))
    (hι : IotaSoundAtDI E ρ T R c m)
    (h : Expr Nat) : PEqDI E ρ T (.app R h) m :=
  pEqDI_K hP (majorStableDI_of_domTyped hP hdom hns) hι h

/-- `(O4)` in `ApproxDI`: `EtaSoundAtDI` for the free variable `.bvar 0` at `EnvI.bot` is false
    for every `E : ResolvedEnv` (matching `PiModelKAudit.eta_unsound_bot`). -/
theorem eta_unsound_bot_DI (E : ResolvedEnv) :
    ¬ EtaSoundAtDI E EnvI.bot (.sort .zero) (.sort .zero) (.bvar 0) := by
  intro h
  have hcode : denDI E EnvI.bot (.pi (.sort .zero) (.sort .zero)) (.pi .bot [([], .sort)]) :=
    .pi (.bot _ _) (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact .sort _ _)
  have hty : CTy E (.lam [([], .bot)]) (.pi .bot [([], .sort)]) :=
    .lam (not_isPropC_pi_sortCod E)
      (fun s hs u hu => by
        simp only [List.mem_singleton] at hs; subst hs; exact nomatch hu)
      (fun s hs _ _ _ => by
        simp only [List.mem_singleton] at hs; subst hs; exact .bot _)
  have hl : denDI E EnvI.bot (.lam (.sort .zero) (.app (lift 0 1 (.bvar 0)) (.bvar 0)))
      (.lam [([], .bot)]) :=
    .lam (fun s hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact .bot _ _)
  obtain ⟨hr, _⟩ := (h (.lam [([], .bot)])).mp ⟨hl, _, hcode, hty⟩
  rcases approxDI_bvar_inv hr with h0 | h0 <;> cases h0

/-- For every expression `f : Expr Nat`, every `.lam g` compact of `f` is preserved by
    η-expansion `.lam A (.app (lift 0 1 f) (.bvar 0))` in `ApproxDI`. -/
theorem approxDI_eta_lam_intro {E : ResolvedEnv} {ρ : EnvI} {f A : Expr Nat}
    {g : List (List CptI × CptI)} (hf : ApproxDI E ρ f (.lam g)) :
    ApproxDI E ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam g) :=
  .lam (fun s hs =>
    .app ((approxDI_lift0_one_iff E ρ (demand s.1) f (CptI.lam g)).mpr hf) hs
      (fun _ hu => .bvar hu))

/-- Unconditional `SemEqI` η-equivalence for every λ-abstraction `.lam A₀ b` in raw `ApproxI`
    (via `approxI_beta` and `instantiate_bvar_lift`). -/
theorem semEqI_eta_lam (ρ : EnvI) (A A₀ b : Expr Nat) :
    SemEqI ρ (.lam A (.app (lift 0 1 (.lam A₀ b)) (.bvar 0))) (.lam A₀ b) :=
  PiModelKAudit.semEqI_lam_congrK (fun us c => by
    change ApproxI (EnvI.cons (demand us) ρ)
      (.app (.lam (lift 0 1 A₀) (lift 1 1 b)) (.bvar 0)) c ↔ _
    rw [approxI_beta, instantiate0, instantiate_bvar_lift b 0])

/-- Unconditional `SemEqDI` η-equivalence for every λ-abstraction `.lam A₀ b` in `ApproxDI`
    (via `approxDI_beta` and `instantiate_bvar_lift`). -/
theorem semEqDI_eta_lam (E : ResolvedEnv) (ρ : EnvI) (A A₀ b : Expr Nat) :
    SemEqDI E ρ (.lam A (.app (lift 0 1 (.lam A₀ b)) (.bvar 0))) (.lam A₀ b) :=
  semEqDI_lam_congrK (fun us c => by
    change ApproxDI E (EnvI.cons (demand us) ρ)
      (.app (.lam (lift 0 1 A₀) (lift 1 1 b)) (.bvar 0)) c ↔ _
    rw [approxDI_beta, instantiate0, instantiate_bvar_lift b 0])

/-- Unconditional discharge of `PiModelKAudit.EtaSoundAt` (`RcicNativePiModelK`) for every
    λ-abstraction `.lam A₀ b`. -/
theorem etaSoundAt_lam (E : ResolvedEnv) (ρ : EnvI) (A B A₀ b : Expr Nat) :
    PiModelKAudit.EtaSoundAt E ρ A B (.lam A₀ b) :=
  pEqI_of_semEqI (semEqI_eta_lam ρ A A₀ b)

/-- Unconditional discharge of `EtaSoundAtDI` for every λ-abstraction `.lam A₀ b`. -/
theorem etaSoundAtDI_lam (E : ResolvedEnv) (ρ : EnvI) (A B A₀ b : Expr Nat) :
    EtaSoundAtDI E ρ A B (.lam A₀ b) :=
  pEqDI_of_semEqDI (semEqDI_eta_lam E ρ A A₀ b)

/-- Unconditional `SemEqDI` η-equivalence for any δ-constant `.const r ls` whose admitted body is
    a closed λ-abstraction `.lam A₀ b`. -/
theorem semEqDI_eta_delta_lam {E : ResolvedEnv} {r : Nat} (ls : List Level)
    {m : CheckedMember} {A₀ b : Expr Nat}
    (hd : DeltaConst E r m (.lam A₀ b))
    (hcl : exprClosedAt 0 (.lam A₀ b) = true)
    (ρ : EnvI) (A : Expr Nat) :
    SemEqDI E ρ (.lam A (.app (lift 0 1 (.const r ls)) (.bvar 0))) (.const r ls) := by
  have hδ : ∀ ρ', SemEqDI E ρ' (.const r ls)
      (.lam (instantiateLevels ls A₀) (instantiateLevels ls b)) :=
    fun _ => semEqDI_delta hd hcl
  have hl : SemEqDI E ρ
      (.lam A (.app (lift 0 1 (.const r ls)) (.bvar 0)))
      (.lam A (.app (lift 0 1 (.lam (instantiateLevels ls A₀) (instantiateLevels ls b))) (.bvar 0))) :=
    semEqDI_lam_congrK (fun us =>
      semEqDI_app ((semEqDI_lift0_one_iff E ρ (demand us) _ _).mpr (hδ ρ))
        (semEqDI_refl E _ _))
  exact semEqDI_trans hl
    (semEqDI_trans (semEqDI_eta_lam E ρ A (instantiateLevels ls A₀) (instantiateLevels ls b))
      (semEqDI_symm (hδ ρ)))

/-- Unconditional discharge of `EtaSoundAtDI` for any δ-constant `.const r ls` whose admitted body
    is a closed λ-abstraction `.lam A₀ b`. -/
theorem etaSoundAtDI_delta_lam {E : ResolvedEnv} {r : Nat} (ls : List Level)
    {m : CheckedMember} {A₀ b : Expr Nat}
    (hd : DeltaConst E r m (.lam A₀ b))
    (hcl : exprClosedAt 0 (.lam A₀ b) = true)
    (ρ : EnvI) (A B : Expr Nat) :
    EtaSoundAtDI E ρ A B (.const r ls) :=
  pEqDI_of_semEqDI (semEqDI_eta_delta_lam ls hd hcl ρ A)

/-! ### §13.2. Unconditional Refutations of `PiModelTermAudit.IrrCaseT` and `PiModelTermAudit.EtaCaseT` (`RcicNativePiModelTermIrr`, Batch 179) for Every `E` and `n` -/

/-- Any weak-head step from `.app (.lam A b) a` has reduct `instantiate0 a b` (valid in every
    `E : ResolvedEnv`, without `EnvWfT E`). -/
theorem whStep_app_lam_eq {E : ResolvedEnv} {A b a e : Expr Nat}
    (h : WhStep E (.app (.lam A b) a) e) : e = instantiate0 a b := by
  cases h with
  | beta => rfl
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
      exact (F8EtaK.foldApps_const_ne_lam_any hl.1.symm).elim
  | appHead hf => exact (whStep_lam_false hf).elim

/-- Any weak-head step from `.app (.app (.lam A b) a₁) a₂` steps the inner β-redex (valid in every
    `E : ResolvedEnv`, without `EnvWfT E`). -/
theorem whStep_app2_lam_eq {E : ResolvedEnv} {A b a₁ a₂ e : Expr Nat}
    (h : WhStep E (.app (.app (.lam A b) a₁) a₂) e) :
    e = .app (instantiate0 a₁ b) a₂ := by
  cases h with
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      have hsp := congrArg (Prod.fst ∘ appsSpine) hl
      simp only [appsSpine, recCall, appsSpine_foldApps, appsSpine_const,
        Function.comp_apply] at hsp
      cases hsp
  | appHead hf => exact congrArg (fun t => Expr.app t a₂) (whStep_app_lam_eq hf)

/-- Any weak-head step from `.app (.app (.app (.lam A b) a₁) a₂) a₃` steps the innermost β-redex
    (valid in every `E : ResolvedEnv`, without `EnvWfT E`). -/
theorem whStep_app3_lam_eq {E : ResolvedEnv} {A b a₁ a₂ a₃ e : Expr Nat}
    (h : WhStep E (.app (.app (.app (.lam A b) a₁) a₂) a₃) e) :
    e = .app (.app (instantiate0 a₁ b) a₂) a₃ := by
  cases h with
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      have hsp := congrArg (Prod.fst ∘ appsSpine) hl
      simp only [appsSpine, recCall, appsSpine_foldApps, appsSpine_const,
        Function.comp_apply] at hsp
      cases hsp
  | appHead hf => exact congrArg (fun t => Expr.app t a₃) (whStep_app2_lam_eq hf)

/-- Deterministic single-step inversion of `WhRed`: if `u ≠ v` and every one-step reduct of `u`
    equals `u'`, then `WhRed E u v` implies `WhRed E u' v`. -/
theorem whRed_step_inv_of_unique {E : ResolvedEnv} {u u' v : Expr Nat}
    (hred : WhRed E u v) (huniq : ∀ t, WhStep E u t → t = u')
    (hne : u ≠ v) : WhRed E u' v := by
  cases hred with
  | refl => exact (hne rfl).elim
  | step hs hr =>
      rw [← huniq _ hs]
      exact hr

/-- The closed impredicative proposition `∀ (X : Prop), X → X → X` (`Π (X : Sort 0), X → X → X`). -/
def irrProjType : Expr Nat :=
  .pi (.sort .zero) (.pi (.bvar 0) (.pi (.bvar 1) (.bvar 2)))

/-- First closed proof of `irrProjType`: `fun (X : Prop) (x y : X) => x`. -/
def irrProjL : Expr Nat :=
  .lam (.sort .zero) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 1)))

/-- Second closed proof of `irrProjType`: `fun (X : Prop) (x y : X) => y`. -/
def irrProjR : Expr Nat :=
  .lam (.sort .zero) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 0)))

/-- Step-function compact `λ ([] ↦ λ ([sort] ↦ λ ([] ↦ sort)))` approximating `irrProjL`. -/
def irrProjCpt : CptI :=
  .lam [([], .lam [([.sort], .lam [([], .sort)])])]

/-- `irrProjType` has type `Sort 0` (`Prop`) in `Γ = []` for every `E` and `n`. -/
def hasTyT_irrProjType (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] irrProjType (.sort .zero) :=
  let piZero {Γ : LCtx} {A B : Expr Nat} {u : Level}
      (hA : HasTyT E n Γ A (.sort u))
      (hB : HasTyT E n (.assumption A :: Γ) B (.sort .zero)) :
      HasTyT E n Γ (.pi A B) (.sort .zero) :=
    .conv Γ (.pi A B) (.sort (.imax u .zero)) (.sort .zero) (.succ (.imax u .zero))
      (.pi Γ A u B .zero hA hB)
      (.sorts Γ (.imax u .zero) .zero (fun _ => rfl))
  piZero (.sort [] .zero)
    (piZero (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)
      (piZero (.bvar [.assumption (.bvar 0), .assumption (.sort .zero)] 1 (.sort .zero) rfl)
        (.bvar [.assumption (.bvar 1), .assumption (.bvar 0), .assumption (.sort .zero)]
          2 (.sort .zero) rfl)))

/-- `irrProjL` has type `irrProjType` in `Γ = []` for every `E` and `n`. -/
def hasTyT_irrProjL (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] irrProjL irrProjType :=
  .lam [] (.sort .zero) (.succ .zero) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 1)))
    (.pi (.bvar 0) (.pi (.bvar 1) (.bvar 2)))
    (.sort [] .zero)
    (.lam [.assumption (.sort .zero)] (.bvar 0) .zero (.lam (.bvar 1) (.bvar 1))
      (.pi (.bvar 1) (.bvar 2))
      (.bvar _ 0 (.sort .zero) rfl)
      (.lam [.assumption (.bvar 0), .assumption (.sort .zero)] (.bvar 1) .zero (.bvar 1) (.bvar 2)
        (.bvar _ 1 (.sort .zero) rfl)
        (.bvar _ 1 (.bvar 2) rfl)))

/-- `irrProjR` has type `irrProjType` in `Γ = []` for every `E` and `n`. -/
def hasTyT_irrProjR (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] irrProjR irrProjType :=
  .lam [] (.sort .zero) (.succ .zero) (.lam (.bvar 0) (.lam (.bvar 1) (.bvar 0)))
    (.pi (.bvar 0) (.pi (.bvar 1) (.bvar 2)))
    (.sort [] .zero)
    (.lam [.assumption (.sort .zero)] (.bvar 0) .zero (.lam (.bvar 1) (.bvar 0))
      (.pi (.bvar 1) (.bvar 2))
      (.bvar _ 0 (.sort .zero) rfl)
      (.lam [.assumption (.bvar 0), .assumption (.sort .zero)] (.bvar 1) .zero (.bvar 0) (.bvar 2)
        (.bvar _ 1 (.sort .zero) rfl)
        (.bvar _ 0 (.bvar 2) rfl)))

/-- `ConvT.irr` relates `irrProjL` and `irrProjR` at `irrProjType` in `Γ = []` for every `E` and `n`. -/
def convT_irrProj (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] irrProjL irrProjR irrProjType :=
  .irr [] irrProjType irrProjL irrProjR
    (hasTyT_irrProjType E n) (hasTyT_irrProjL E n) (hasTyT_irrProjR E n)

/-- `irrProjCpt` approximates `irrProjL` in `ApproxI` at every `ρ : EnvI`. -/
theorem approxI_irrProjL (ρ : EnvI) : ApproxI ρ irrProjL irrProjCpt := by
  refine .lam (fun s₁ hs₁ => ?_)
  simp only [List.mem_singleton] at hs₁; subst hs₁
  refine .lam (fun s₂ hs₂ => ?_)
  simp only [List.mem_singleton] at hs₂; subst hs₂
  refine .lam (fun s₃ hs₃ => ?_)
  simp only [List.mem_singleton] at hs₃; subst hs₃
  exact .bvar (List.Mem.head _)

/-- `irrProjCpt` approximates `irrProjL` in `ApproxDI` at every `E` and `ρ : EnvI`. -/
theorem approxDI_irrProjL (E : ResolvedEnv) (ρ : EnvI) : ApproxDI E ρ irrProjL irrProjCpt := by
  refine .lam (fun s₁ hs₁ => ?_)
  simp only [List.mem_singleton] at hs₁; subst hs₁
  refine .lam (fun s₂ hs₂ => ?_)
  simp only [List.mem_singleton] at hs₂; subst hs₂
  refine .lam (fun s₃ hs₃ => ?_)
  simp only [List.mem_singleton] at hs₃; subst hs₃
  exact .bvar (List.Mem.head _)

/-- `irrProjCpt` does not approximate `irrProjR` in `ApproxI EnvI.bot`. -/
theorem not_approxI_irrProjR : ¬ ApproxI EnvI.bot irrProjR irrProjCpt := by
  intro h
  rcases approxI_lam_inv h with h0 | ⟨_, heq₁, hb₁⟩
  · cases h0
  · injection heq₁ with hf₁; subst hf₁
    have h₁ := hb₁ _ (List.Mem.head _)
    rcases approxI_lam_inv h₁ with h0 | ⟨_, heq₂, hb₂⟩
    · cases h0
    · injection heq₂ with hf₂; subst hf₂
      have h₂ := hb₂ _ (List.Mem.head _)
      rcases approxI_lam_inv h₂ with h0 | ⟨_, heq₃, hb₃⟩
      · cases h0
      · injection heq₃ with hf₃; subst hf₃
        have h₃ := hb₃ _ (List.Mem.head _)
        rcases approxI_bvar_inv h₃ with h0 | h0 <;> cases h0

/-- `irrProjCpt` does not approximate `irrProjR` in `ApproxDI E EnvI.bot`. -/
theorem not_approxDI_irrProjR (E : ResolvedEnv) : ¬ ApproxDI E EnvI.bot irrProjR irrProjCpt := by
  intro h
  rcases approxDI_lam_inv h with h0 | ⟨_, heq₁, hb₁⟩
  · cases h0
  · injection heq₁ with hf₁; subst hf₁
    have h₁ := hb₁ _ (List.Mem.head _)
    rcases approxDI_lam_inv h₁ with h0 | ⟨_, heq₂, hb₂⟩
    · cases h0
    · injection heq₂ with hf₂; subst hf₂
      have h₂ := hb₂ _ (List.Mem.head _)
      rcases approxDI_lam_inv h₂ with h0 | ⟨_, heq₃, hb₃⟩
      · cases h0
      · injection heq₃ with hf₃; subst hf₃
        have h₃ := hb₃ _ (List.Mem.head _)
        rcases approxDI_bvar_inv h₃ with h0 | h0 <;> cases h0

/-- `LRTermI E n [] irrProjL irrProjR irrProjType irrProjCpt` is false for every `E` and `n`. -/
theorem not_lrTermI_irrProj (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermI E n [] irrProjL irrProjR irrProjType irrProjCpt := by
  intro h
  rw [irrProjCpt, lrTermI_lam_iff] at h
  obtain ⟨A₁, B₁, hP₁, _, happ₁⟩ := h
  have e₁ := whRed_pi_eq hP₁
  injection e₁ with eA₁ eB₁; subst eA₁; subst eB₁
  have h₂ := happ₁ ([], .lam [([.sort], .lam [([], .sort)])]) (List.Mem.head _)
    (.sort .zero) (.sort .zero) (fun _ hu => nomatch hu)
  change LRTermI E n [] (.app irrProjL (.sort .zero)) (.app irrProjR (.sort .zero))
    (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)))
    (.lam [([.sort], .lam [([], .sort)])]) at h₂
  rw [lrTermI_lam_iff] at h₂
  obtain ⟨A₂, B₂, hP₂, _, happ₂⟩ := h₂
  have e₂ := whRed_pi_eq hP₂
  injection e₂ with eA₂ eB₂; subst eA₂; subst eB₂
  have h₃ := happ₂ ([.sort], .lam [([], .sort)]) (List.Mem.head _)
    (.sort .zero) (.sort .zero) (fun u hu => by
      simp only [List.mem_singleton] at hu; subst hu
      rw [lrTermI_sort_iff]
      exact ⟨⟨.zero, .refl _⟩, .sort (.refl _) (.refl _)⟩)
  change LRTermI E n [] (.app (.app irrProjL (.sort .zero)) (.sort .zero))
    (.app (.app irrProjR (.sort .zero)) (.sort .zero))
    (.pi (.sort .zero) (.sort .zero))
    (.lam [([], .sort)]) at h₃
  rw [lrTermI_lam_iff] at h₃
  obtain ⟨A₃, B₃, hP₃, _, happ₃⟩ := h₃
  have e₃ := whRed_pi_eq hP₃
  injection e₃ with eA₃ eB₃; subst eA₃; subst eB₃
  have h₄ := happ₃ ([], .sort) (List.Mem.head _)
    (.bvar 0) (.bvar 0) (fun _ hu => nomatch hu)
  change LRTermI E n []
    (.app (.app (.app irrProjL (.sort .zero)) (.sort .zero)) (.bvar 0))
    (.app (.app (.app irrProjR (.sort .zero)) (.sort .zero)) (.bvar 0))
    (.sort .zero) .sort at h₄
  rw [lrTermI_sort_iff] at h₄
  cases h₄.2 with
  | sort _ hR =>
      have hR₁ : WhRed E
          (.app (.app (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 0))) (.sort .zero)) (.bvar 0))
          (.sort _) :=
        whRed_step_inv_of_unique hR (fun _ => whStep_app3_lam_eq) (fun h => by cases h)
      have hR₂ : WhRed E
          (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
          (.sort _) :=
        whRed_step_inv_of_unique hR₁ (fun _ => whStep_app2_lam_eq) (fun h => by cases h)
      have hR₃ : WhRed E (.bvar 0) (.sort _) :=
        whRed_step_inv_of_unique hR₂ (fun _ => whStep_app_lam_eq) (fun h => by cases h)
      exact nomatch whRed_bvar_eq hR₃

/-- The `ApproxDI` counterpart to `PiModelTermAudit.IrrCaseT` (`RcicNativePiModelTermIrr`). -/
def IrrCaseT_DI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P p q : Expr Nat}, HasTyT E n Γ P (.sort .zero) →
    HasTyT E n Γ p P → HasTyT E n Γ q P →
    ∀ u, ApproxDI E EnvI.bot p u → LRTermI E n Γ p q P u

/-- **Unconditional refutation of `PiModelTermAudit.IrrCaseT` (`RcicNativePiModelTermIrr`)**:
    `IrrCaseT E n` is false for **every** `E : ResolvedEnv` and `n : Nat` (in `Γ = []`, without
    any `pi_member` hypothesis). -/
theorem not_irrCaseT (E : ResolvedEnv) (n : Nat) :
    ¬ PiModelTermAudit.IrrCaseT E n := fun F =>
  not_lrTermI_irrProj E n
    (F .nil (hasTyT_irrProjType E n) (hasTyT_irrProjL E n) (hasTyT_irrProjR E n)
      irrProjCpt (approxI_irrProjL EnvI.bot))

/-- **Unconditional refutation of `IrrCaseT_DI`**: false for **every** `E : ResolvedEnv` and
    `n : Nat` in `Γ = []`. -/
theorem not_irrCaseT_DI (E : ResolvedEnv) (n : Nat) :
    ¬ IrrCaseT_DI E n := fun F =>
  not_lrTermI_irrProj E n
    (F .nil (hasTyT_irrProjType E n) (hasTyT_irrProjL E n) (hasTyT_irrProjR E n)
      irrProjCpt (approxDI_irrProjL E EnvI.bot))

/-- Closed function `fun (_ : Prop) => ∀ (Y : Prop), Y` of type `Prop → Prop` in `Γ = []`. -/
def etaIdPiPropFn : Expr Nat :=
  .lam (.sort .zero) idPiProp

/-- Step-function compact `λ ([] ↦ idPiPropSortStep)` approximating the η-expansion of
    `etaIdPiPropFn`. -/
def etaIdPiPropCpt : CptI :=
  .lam [([], idPiPropSortStep)]

/-- `etaIdPiPropFn` has type `.pi (.sort .zero) (.sort .zero)` (`Prop → Prop`) in `Γ = []` for
    every `E` and `n`. -/
def hasTyT_etaIdPiPropFn (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) :=
  .lam [] (.sort .zero) (.succ .zero) idPiProp (.sort .zero) (.sort [] .zero)
    (.conv [.assumption (.sort .zero)] idPiProp (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
      (.succ (.imax (.succ .zero) .zero))
      (.pi [.assumption (.sort .zero)] (.sort .zero) (.succ .zero) (.bvar 0) .zero
        (.sort _ .zero) (.bvar _ 0 (.sort .zero) rfl))
      (.sorts [.assumption (.sort .zero)] (.imax (.succ .zero) .zero) .zero (fun _ => rfl)))

/-- `etaIdPiPropCpt` approximates `.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0))`
    in `ApproxI EnvI.bot`. -/
theorem approxI_eta_etaIdPiPropFn :
    ApproxI EnvI.bot (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
      etaIdPiPropCpt := by
  refine .lam (fun s hs => ?_)
  simp only [List.mem_singleton] at hs; subst hs
  have h0 : ApproxI (EnvI.cons (demand []) EnvI.bot) idPiProp idPiPropSortStep :=
    (approxDI_emptyEnv_iff _ _ _).mp
      ((approxDI_cons_botDemand_bot_iff botDemand_nil idPiProp idPiPropSortStep).mpr
        (approxDI_idPiProp_sortStep emptyEnv))
  exact (approxI_beta (EnvI.cons (demand []) EnvI.bot) (.sort .zero) idPiProp (.bvar 0)
    idPiPropSortStep).mpr h0

/-- `etaIdPiPropCpt` approximates `.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0))`
    in `ApproxDI E EnvI.bot`. -/
theorem approxDI_eta_etaIdPiPropFn (E : ResolvedEnv) :
    ApproxDI E EnvI.bot (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
      etaIdPiPropCpt := by
  refine .lam (fun s hs => ?_)
  simp only [List.mem_singleton] at hs; subst hs
  have h0 : ApproxDI E (EnvI.cons (demand []) EnvI.bot) idPiProp idPiPropSortStep :=
    (approxDI_cons_botDemand_bot_iff botDemand_nil idPiProp idPiPropSortStep).mpr
      (approxDI_idPiProp_sortStep E)
  exact (approxDI_beta E (EnvI.cons (demand []) EnvI.bot) (.sort .zero) idPiProp (.bvar 0)
    idPiPropSortStep).mpr h0

/-- `LRTermI` fails at `etaIdPiPropCpt` between the η-expansion of `etaIdPiPropFn` and
    `etaIdPiPropFn` for every `E` and `n`. -/
theorem not_lrTermI_eta_etaIdPiPropFn (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermI E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  intro h
  rw [etaIdPiPropCpt, lrTermI_lam_iff] at h
  obtain ⟨A₁, B₁, hP₁, _, happ⟩ := h
  have e₁ := whRed_pi_eq hP₁
  injection e₁ with eA₁ eB₁; subst eA₁; subst eB₁
  have h₂ := happ ([], idPiPropSortStep) (List.Mem.head _)
    (.sort .zero) (.sort .zero) (fun _ hu => nomatch hu)
  change LRTermI E n []
    (.app (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0))) (.sort .zero))
    (.app etaIdPiPropFn (.sort .zero)) (.sort .zero) idPiPropSortStep at h₂
  rw [idPiPropSortStep, lrTermI_pi_iff] at h₂
  cases h₂.2 with
  | pi _ h' _ _ _ _ rf =>
      have h'' : WhRed E idPiProp (.pi _ _) :=
        whRed_step_inv_of_unique h' (fun _ => whStep_app_lam_eq) (fun h => by cases h)
      have e₂ := whRed_pi_eq h''
      injection e₂ with _ eB₂; subst eB₂
      have hs := rf ([.sort], .sort) (List.Mem.head _)
      cases hs with
      | sort _ hb => exact nomatch whRed_bvar_eq hb

/-- The `ApproxDI` counterpart to `PiModelTermAudit.EtaCaseT` (`RcicNativePiModelTermIrr`). -/
def EtaCaseT_DI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat}, HasTyT E n Γ f (.pi A B) →
    ∀ u, ApproxDI E EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) u →
      LRTermI E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) u

/-- **Unconditional refutation of `PiModelTermAudit.EtaCaseT` (`RcicNativePiModelTermIrr`)**:
    `EtaCaseT E n` is false for **every** `E : ResolvedEnv` and `n : Nat` (in `Γ = []`). -/
theorem not_etaCaseT (E : ResolvedEnv) (n : Nat) :
    ¬ PiModelTermAudit.EtaCaseT E n := fun F =>
  not_lrTermI_eta_etaIdPiPropFn E n
    (F .nil (hasTyT_etaIdPiPropFn E n) etaIdPiPropCpt approxI_eta_etaIdPiPropFn)

/-- **Unconditional refutation of `EtaCaseT_DI`**: false for **every** `E : ResolvedEnv` and
    `n : Nat` in `Γ = []`. -/
theorem not_etaCaseT_DI (E : ResolvedEnv) (n : Nat) :
    ¬ EtaCaseT_DI E n := fun F =>
  not_lrTermI_eta_etaIdPiPropFn E n
    (F .nil (hasTyT_etaIdPiPropFn E n) etaIdPiPropCpt (approxDI_eta_etaIdPiPropFn E))

/-! ## §14. Weakening, Substitution, and `TyConvT`-Chain Context Conversion for `WhStep`/`WhRed`, `HasTyT`/`ConvT`/`TyConvT`, `LRTypeIN` on `BotPiCpt`, and `LRTypeINBiDI` -/

/-! ### §14.1. Unconditional `WhStep.iota` Lifting/Substitution and `WhStep`/`WhRed` Commutation -/

/-- `WhStep.iota` is closed under `lift c 1` unconditionally for every `E : ResolvedEnv`. -/
theorem whStep_iota_lift {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (c : Nat) :
    WhStep E (lift c 1 lhs) (lift c 1 rhs) :=
  .iota (derivedIotaU_lift c h)

/-- `WhStep.iota` is closed under `instantiate j s` unconditionally for every `E : ResolvedEnv`
    (discharging the open `hι` hypothesis of `RcicNativePiModelLRTermSubst`). -/
theorem whStep_iota_instantiate {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (j : Nat) (s : Expr Nat) :
    WhStep E (instantiate j s lhs) (instantiate j s rhs) :=
  .iota (derivedIotaU_subst j s h)

/-- `WhStep` commutes with `lift c 1` under `EnvClosed E`. -/
theorem whStep_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhStep E a b) :
    ∀ (c : Nat), WhStep E (lift c 1 a) (lift c 1 b) := by
  induction h with
  | beta A body arg =>
      intro c
      rw [show lift c 1 (.app (.lam A body) arg) =
          .app (.lam (lift c 1 A) (lift (c + 1) 1 body)) (lift c 1 arg) from rfl,
        instantiate0, lift_instantiate_low 1 c 0 arg (Nat.zero_le c) body]
      exact .beta _ _ _
  | zeta A value body =>
      intro c
      rw [show lift c 1 (.letE A value body) =
          .letE (lift c 1 A) (lift c 1 value) (lift (c + 1) 1 body) from rfl,
        instantiate0, lift_instantiate_low 1 c 0 value (Nat.zero_le c) body]
      exact .zeta _ _ _
  | @delta rmem ls m b hres hbody =>
      intro c
      have hbod : ∀ k, lift k 1 b = b := (hcl rmem m hres).2 b hbody
      have hfix : lift c 1 (instantiateLevels ls b) = instantiateLevels ls b := by
        rw [lift_instantiateLevels, hbod c]
      rw [show lift c 1 (.const rmem ls) = .const rmem ls from rfl, hfix]
      exact .delta hres hbody
  | iota hI =>
      intro c
      exact whStep_iota_lift hI c
  | lit t =>
      intro c
      rw [show lift c 1 (.lit t) = .lit t from rfl, natExpand_lift c 1 t]
      exact .lit t
  | appHead _ ih =>
      intro c
      exact .appHead (ih c)

/-- `WhRed` commutes with `lift c 1` under `EnvClosed E`. -/
theorem whRed_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhRed E a b) (c : Nat) :
    WhRed E (lift c 1 a) (lift c 1 b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStep_lift_of_envClosed hcl hs c) ih

/-- `WhStep` commutes with `instantiate j s` under `EnvClosed E` (with zero ι side hypotheses). -/
theorem whStep_instantiate_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhStep E a b) :
    ∀ (j : Nat) (s : Expr Nat), WhStep E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | beta A body arg =>
      intro j s
      rw [show instantiate j s (.app (.lam A body) arg) =
          .app (.lam (instantiate j s A) (instantiate (j + 1) (lift 0 1 s) body))
            (instantiate j s arg) from rfl,
        instantiate0, instantiate_instantiate 0 j arg s (Nat.zero_le j) body]
      exact .beta _ _ _
  | zeta A value body =>
      intro j s
      rw [show instantiate j s (.letE A value body) =
          .letE (instantiate j s A) (instantiate j s value)
            (instantiate (j + 1) (lift 0 1 s) body) from rfl,
        instantiate0, instantiate_instantiate 0 j value s (Nat.zero_le j) body]
      exact .zeta _ _ _
  | @delta rmem ls m b hres hbody =>
      intro j s
      have hbod : ∀ k, lift k 1 b = b := (hcl rmem m hres).2 b hbody
      have hfix : instantiate j s (instantiateLevels ls b) = instantiateLevels ls b := by
        rw [instantiate_eq_substT]
        exact substT_closed (lift_instantiateLevels_closedT hbod ls) _
      rw [show instantiate j s (.const rmem ls) = .const rmem ls from rfl, hfix]
      exact .delta hres hbody
  | iota hI =>
      intro j s
      exact whStep_iota_instantiate hI j s
  | lit t =>
      intro j s
      rw [show instantiate j s (.lit t) = .lit t from rfl, natExpand_instantiate j s t]
      exact .lit t
  | appHead _ ih =>
      intro j s
      exact .appHead (ih j s)

/-- `WhRed` commutes with `instantiate j s` under `EnvClosed E` (with zero ι side hypotheses). -/
theorem whRed_instantiate_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhRed E a b) (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStep_instantiate_of_envClosed hcl hs j s) ih

/-- `WhRed` to `.sort l` commutes with `instantiate j s` under `EnvClosed E`. -/
theorem whRed_instantiate_sort_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a : Expr Nat} {l : Level} (h : WhRed E a (.sort l)) (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (.sort l) :=
  whRed_instantiate_of_envClosed hcl h j s

/-- `WhRed` to `.pi A B` commutes with `instantiate j s` under `EnvClosed E`. -/
theorem whRed_instantiate_pi_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {e A B : Expr Nat} (h : WhRed E e (.pi A B)) (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s e)
      (.pi (instantiate j s A) (instantiate (j + 1) (lift 0 1 s) B)) :=
  whRed_instantiate_of_envClosed hcl h j s

/-! ### §14.2. Context Conversion Along a `TyConvT` Chain (`tyConvT_ctx`, `hasTyT_tyConvT_head`, `codomain_transport_of_tyConvT`) -/

/-- `TyConvT` transports across pointwise-convertible contexts `CtxConvT E n Γ Γ'`. -/
def tyConvT_ctx {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → {A B : Expr Nat} →
    TyConvT E n Γ A B → TyConvT E n Γ' A B
  | _, Γ', _, _, _, .refl _ A => .refl Γ' A
  | _, Γ', hcc, _, _, .of _ A B u h => .of Γ' A B u (convT_ctx hcl hcc h)
  | _, Γ', hcc, _, _, .trans _ A M B h1 h2 =>
      .trans Γ' A M B (tyConvT_ctx hcl hcc h1) (tyConvT_ctx hcl hcc h2)

/-- Extend a `CtxConvT E n Γ Γ'` by an identical prefix `Δ` (`CtxConvT.same` iterated). -/
def ctxConvT_append_same {E : ResolvedEnv} {n : Nat} :
    (Δ : LCtx) → {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → CtxConvT E n (Δ ++ Γ) (Δ ++ Γ')
  | [], _, _, hcc => hcc
  | d :: Δ, _, _, hcc => .same d (ctxConvT_append_same Δ hcc)

/-- `HasTyT` transports across `Δ ++ .assumption A :: Γ` to `Δ ++ .assumption A' :: Γ` along any
    `TyConvT E n Γ A A'` chain. -/
def hasTyT_tyConvT_assumption {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (Δ : LCtx) :
    {A A' : Expr Nat} → TyConvT E n Γ A A' → {e T : Expr Nat} →
    HasTyT E n (Δ ++ .assumption A :: Γ) e T →
    HasTyT E n (Δ ++ .assumption A' :: Γ) e T
  | _, _, .refl _ _, _, _, he => he
  | _, _, .of _ _ _ _ hc₀, _, _, he =>
      let hEnds := convEnds hW hΓ hc₀
      hasTyT_ctx (envClosed_of_envWfT hW)
        (ctxConvT_append_same Δ (.assumption (ctxConvT_refl Γ) hEnds.1 hEnds.2.1 hc₀)) he
  | _, _, .trans _ _ _ _ c₁ c₂, _, _, he =>
      hasTyT_tyConvT_assumption hW hΓ Δ c₂ (hasTyT_tyConvT_assumption hW hΓ Δ c₁ he)

/-- `ConvT` transports across `Δ ++ .assumption A :: Γ` to `Δ ++ .assumption A' :: Γ` along any
    `TyConvT E n Γ A A'` chain. -/
def convT_tyConvT_assumption {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (Δ : LCtx) :
    {A A' : Expr Nat} → TyConvT E n Γ A A' → {a b T : Expr Nat} →
    ConvT E n (Δ ++ .assumption A :: Γ) a b T →
    ConvT E n (Δ ++ .assumption A' :: Γ) a b T
  | _, _, .refl _ _, _, _, _, hc => hc
  | _, _, .of _ _ _ _ hc₀, _, _, _, hc =>
      let hEnds := convEnds hW hΓ hc₀
      convT_ctx (envClosed_of_envWfT hW)
        (ctxConvT_append_same Δ (.assumption (ctxConvT_refl Γ) hEnds.1 hEnds.2.1 hc₀)) hc
  | _, _, .trans _ _ _ _ c₁ c₂, _, _, _, hc =>
      convT_tyConvT_assumption hW hΓ Δ c₂ (convT_tyConvT_assumption hW hΓ Δ c₁ hc)

/-- `TyConvT` transports across `Δ ++ .assumption A :: Γ` to `Δ ++ .assumption A' :: Γ` along any
    `TyConvT E n Γ A A'` chain. -/
def tyConvT_tyConvT_assumption {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (Δ : LCtx) :
    {A A' : Expr Nat} → TyConvT E n Γ A A' → {B B' : Expr Nat} →
    TyConvT E n (Δ ++ .assumption A :: Γ) B B' →
    TyConvT E n (Δ ++ .assumption A' :: Γ) B B'
  | _, _, .refl _ _, _, _, hc => hc
  | _, _, .of _ _ _ _ hc₀, _, _, hc =>
      let hEnds := convEnds hW hΓ hc₀
      tyConvT_ctx (envClosed_of_envWfT hW)
        (ctxConvT_append_same Δ (.assumption (ctxConvT_refl Γ) hEnds.1 hEnds.2.1 hc₀)) hc
  | _, _, .trans _ _ _ _ c₁ c₂, _, _, hc =>
      tyConvT_tyConvT_assumption hW hΓ Δ c₂ (tyConvT_tyConvT_assumption hW hΓ Δ c₁ hc)

/-- Head specialization (`Δ = []`): `HasTyT` transports from `.assumption A :: Γ` to
    `.assumption A' :: Γ` along `TyConvT E n Γ A A'`. -/
def hasTyT_tyConvT_head {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' e T : Expr Nat}
    (hc : TyConvT E n Γ A A')
    (he : HasTyT E n (.assumption A :: Γ) e T) :
    HasTyT E n (.assumption A' :: Γ) e T :=
  hasTyT_tyConvT_assumption hW hΓ [] hc he

/-- Head specialization (`Δ = []`): `ConvT` transports from `.assumption A :: Γ` to
    `.assumption A' :: Γ` along `TyConvT E n Γ A A'`. -/
def convT_tyConvT_head {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' a b T : Expr Nat}
    (hc : TyConvT E n Γ A A')
    (h : ConvT E n (.assumption A :: Γ) a b T) :
    ConvT E n (.assumption A' :: Γ) a b T :=
  convT_tyConvT_assumption hW hΓ [] hc h

/-- Head specialization (`Δ = []`): `TyConvT` transports from `.assumption A :: Γ` to
    `.assumption A' :: Γ` along `TyConvT E n Γ A A'`. -/
def tyConvT_tyConvT_head {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' B B' : Expr Nat}
    (hc : TyConvT E n Γ A A')
    (hB : TyConvT E n (.assumption A :: Γ) B B') :
    TyConvT E n (.assumption A' :: Γ) B B' :=
  tyConvT_tyConvT_assumption hW hΓ [] hc hB

/-- Full Π-codomain transport along a `TyConvT E n Γ A₁ A₂` chain: transports `CtxWfT`, `HasTyT` of
    `B₁`, `TyConvT` of `B₁` and `B₂`, and derives sorting `HasTyT E n (.assumption A₂ :: Γ) B₂ (.sort w₂)`
    in the moved context `.assumption A₂ :: Γ`. -/
theorem codomain_transport_of_tyConvT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ B₁ B₂ : Expr Nat} {u₂ w₁ : Level}
    (hA₂ : HasTyT E n Γ A₂ (.sort u₂))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁))
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    Nonempty (CtxWfT E n (.assumption A₂ :: Γ)) ∧
      Nonempty (HasTyT E n (.assumption A₂ :: Γ) B₁ (.sort w₁)) ∧
      Nonempty (TyConvT E n (.assumption A₂ :: Γ) B₁ B₂) ∧
      ∃ w₂, Nonempty (HasTyT E n (.assumption A₂ :: Γ) B₂ (.sort w₂)) := by
  have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption _ _ _ hΓ hA₂
  have hB₁' : HasTyT E n (.assumption A₂ :: Γ) B₁ (.sort w₁) :=
    hasTyT_tyConvT_head hW hΓ hdom hB₁
  have hcod' : TyConvT E n (.assumption A₂ :: Γ) B₁ B₂ :=
    tyConvT_tyConvT_head hW hΓ hdom hcod
  obtain ⟨w₂, hB₂⟩ := tyConvT_endTyped hW hΓ₂ hcod' hB₁'
  exact ⟨⟨hΓ₂⟩, ⟨hB₁'⟩, ⟨hcod'⟩, w₂, ⟨hB₂⟩⟩

/-! ### §14.3. Weakening and Substitution Stability of `LRTypeIN` on `BotPiCpt` and `LRTypeINBiDI` -/

/-- `LRTypeIN` on any `BotPiCpt` compact is stable under one-declaration weakening `insertAt d k Γ` /
    `lift k 1`. -/
theorem lrTypeIN_weaken_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} (d : LocalDecl) (k : Nat),
      CtxWfT E n (insertAt d k Γ) →
      LRTypeIN E n Γ A A' c →
      LRTypeIN E n (insertAt d k Γ) (lift k 1 A) (lift k 1 A') c := by
  induction hc with
  | bot =>
      intro Γ A A' d k _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' d k _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRed_lift_of_envClosed hcl h₁ k) (whRed_lift_of_envClosed hcl h₂ k)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' d k hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have h₁' : WhRed E (lift k 1 A) (.pi (lift k 1 A₁) (lift (k + 1) 1 B₁)) :=
            whRed_lift_of_envClosed hcl h₁ k
          have h₂' : WhRed E (lift k 1 A') (.pi (lift k 1 A₂) (lift (k + 1) 1 B₂)) :=
            whRed_lift_of_envClosed hcl h₂ k
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (insertAt d k Γ) (lift k 1 A₁) (.sort u) :=
            hasTyTWeaken d hcl (c := k) hA₁
          have hΓ₁' : CtxWfT E n (.assumption (lift k 1 A₁) :: insertAt d k Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hdom' : TyConvT E n (insertAt d k Γ) (lift k 1 A₁) (lift k 1 A₂) :=
            tyConvTWeaken d hcl (c := k) hdom
          have hcod' : TyConvT E n (.assumption (lift k 1 A₁) :: insertAt d k Γ)
              (lift (k + 1) 1 B₁) (lift (k + 1) 1 B₂) :=
            tyConvTWeaken d hcl (c := k + 1) (Γ := .assumption A₁ :: Γ) hcod
          exact .pi h₁' h₂' hΓ₁' hdom' hcod'
            (iha d k hΓ' ra)
            (fun s hs => by
              have hΓ₁_ins : CtxWfT E n (insertAt d (k + 1) (.assumption A₁ :: Γ)) := hΓ₁'
              exact ihf s hs d (k + 1) hΓ₁_ins (rf s hs))

/-- Cutoff-`0` specialization: `LRTypeIN` on any `BotPiCpt` compact is stable under head weakening
    `d :: Γ` / `lift 0 1`. -/
theorem lrTypeIN_weaken0_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeIN E n Γ A A' c) :
    LRTypeIN E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') c :=
  lrTypeIN_weaken_botPiCpt hcl hc d 0 hΓ' h

/-- `LRTypeINBiDI` is stable under head weakening `d :: Γ` / `lift 0 1`. -/
theorem lrTypeINBiDI_weaken0 {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} (h : LRTypeINBiDI E n Γ A A') :
    LRTypeINBiDI E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') := by
  intro c hc happrox
  have happrox₀ : ApproxDI E EnvI.bot A c ∨ ApproxDI E EnvI.bot A' c := by
    rcases happrox with hL | hR
    · exact Or.inl ((approxDI_lift0_one_iff E EnvI.bot (demand []) A c).mp
        ((approxDI_cons_botDemand_bot_iff botDemand_nil (lift 0 1 A) c).mpr hL))
    · exact Or.inr ((approxDI_lift0_one_iff E EnvI.bot (demand []) A' c).mp
        ((approxDI_cons_botDemand_bot_iff botDemand_nil (lift 0 1 A') c).mpr hR))
  exact lrTypeIN_weaken0_botPiCpt hcl hΓ' hc (h c hc happrox₀)

/-- `LRTypeIN` on any `BotPiCpt` compact is stable under `substRemove v j Γ` /
    `instantiate j (lift 0 j v)` at an `.assumption t` hole. -/
theorem lrTypeIN_subst_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (v t : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.assumption t) →
      HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
      CtxWfT E n (substRemove v j Γ) →
      LRTypeIN E n Γ A A' c →
      LRTypeIN E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j _ _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRed_instantiate_of_envClosed hcl h₁ j (lift 0 j v))
            (whRed_instantiate_of_envClosed hcl h₂ j (lift 0 j v))
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) v
          have h₁' : WhRed E (instantiate j (lift 0 j v) A)
              (.pi (instantiate j (lift 0 j v) A₁) (instantiate (j + 1) (lift 0 (j + 1) v) B₁)) := by
            have h0 := whRed_instantiate_of_envClosed hcl h₁ j (lift 0 j v)
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRed E (instantiate j (lift 0 j v) A')
              (.pi (instantiate j (lift 0 j v) A₂) (instantiate (j + 1) (lift 0 (j + 1) v) B₂)) := by
            have h0 := whRed_instantiate_of_envClosed hcl h₂ j (lift 0 j v)
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hΓ₁' : CtxWfT E n (substRemove v (j + 1) (.assumption A₁ :: Γ)) :=
            subst_arg_wf_assump hcl hinst hget hvty hΓ' hA₁
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.assumption t) := by
            rw [List.getElem?_cons_succ]; exact hget
          have hvty' : HasTyT E n (substRemove v (j + 1) (.assumption A₁ :: Γ))
              (lift 0 (j + 1) v) (lift 0 (j + 1) t) := by
            have h0 := hasTyTWeaken (instDecl j v (.assumption A₁)) hcl (c := 0) hvty
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
                lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
            exact h0
          have hdom' : TyConvT E n (substRemove v j Γ)
              (instantiate j (lift 0 j v) A₁) (instantiate j (lift 0 j v) A₂) :=
            tyConvT_substS hcl hinst v t hdom hget hvty
          have hcod' : TyConvT E n (.assumption (instantiate j (lift 0 j v) A₁) :: substRemove v j Γ)
              (instantiate (j + 1) (lift 0 (j + 1) v) B₁)
              (instantiate (j + 1) (lift 0 (j + 1) v) B₂) := by
            simpa only [substRemove_succ_cons, instDecl] using
              tyConvT_substS hcl hinst v t (j := j + 1) hcod hget' hvty'
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j v) A₁) :: substRemove v j Γ) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hvty' hΓ₁' (rf s hs))

/-- Head (`j = 0`) specialization: `LRTypeIN` on any `BotPiCpt` compact is stable under
    `instantiate0 v` for any `HasTyT E n Γ v t`. -/
theorem lrTypeIN_subst0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t A A' : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeIN E n (.assumption t :: Γ) A A' c) :
    LRTypeIN E n Γ (instantiate0 v A) (instantiate0 v A') c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTypeIN_subst_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) v t hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hv)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTypeIN` on any `BotPiCpt` compact is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole. -/
theorem lrTypeIN_substLet_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (t w0 : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.letBinding t w0) →
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
      CtxWfT E n (substRemove w0 j Γ) →
      LRTypeIN E n Γ A A' c →
      LRTypeIN E n (substRemove w0 j Γ)
        (instantiate j (lift 0 j w0) A) (instantiate j (lift 0 j w0) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j _ _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRed_instantiate_of_envClosed hcl h₁ j (lift 0 j w0))
            (whRed_instantiate_of_envClosed hcl h₂ j (lift 0 j w0))
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j w0) = lift 0 (j + 1) w0 :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) w0
          have h₁' : WhRed E (instantiate j (lift 0 j w0) A)
              (.pi (instantiate j (lift 0 j w0) A₁) (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)) := by
            have h0 := whRed_instantiate_of_envClosed hcl h₁ j (lift 0 j w0)
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRed E (instantiate j (lift 0 j w0) A')
              (.pi (instantiate j (lift 0 j w0) A₂) (instantiate (j + 1) (lift 0 (j + 1) w0) B₂)) := by
            have h0 := whRed_instantiate_of_envClosed hcl h₂ j (lift 0 j w0)
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A₁) (.sort u) :=
            hasTyT_substLetS hcl hinst t w0 hA₁ hget hvty
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hΓ₁' : CtxWfT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ)) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁''
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.letBinding t w0) := by
            rw [List.getElem?_cons_succ]; exact hget
          have hvty' : HasTyT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ))
              (lift 0 (j + 1) w0) (lift 0 (j + 1) t) := by
            have h0 := hasTyTWeaken (instDecl j w0 (.assumption A₁)) hcl (c := 0) hvty
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
                lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
            exact h0
          have hdom' : TyConvT E n (substRemove w0 j Γ)
              (instantiate j (lift 0 j w0) A₁) (instantiate j (lift 0 j w0) A₂) :=
            tyConvT_substLetS hcl hinst t w0 hdom hget hvty
          have hcod' : TyConvT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₂) := by
            simpa only [substRemove_succ_cons, instDecl] using
              tyConvT_substLetS hcl hinst t w0 (j := j + 1) hcod hget' hvty'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hvty' hΓ₁' (rf s hs))

/-- Head (`j = 0`) specialization: `LRTypeIN` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ`. -/
theorem lrTypeIN_substLet0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 A A' : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeIN E n (.letBinding t w0 :: Γ) A A' c) :
    LRTypeIN E n Γ (instantiate0 w0 A) (instantiate0 w0 A') c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTypeIN_substLet_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) t w0 hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

#print axioms delta_unsound_raw_approxI
#print axioms defSortEnv_delta_step_and_raw_refuted
#print axioms wZero_unsound_raw_approxI
#print axioms ApproxDI
#print axioms SemEqDI
#print axioms approxDI_emptyEnv_iff
#print axioms approxDI_mono_env
#print axioms approxDI_closedAt_env
#print axioms approxDI_instantiateLevels_iff
#print axioms semEqDI_const_levels
#print axioms approxDI_factor
#print axioms approxDI_lift_intro
#print axioms approxDI_lift_elim
#print axioms approxDI_subst_intro
#print axioms approxDI_subst_elim
#print axioms approxDI_subst_demand_iff
#print axioms approxDI_instPrefix_demand_iff
#print axioms approxDI_instPrefix_closed_iff
#print axioms approxDI_beta
#print axioms approxDI_zeta
#print axioms approxDI_lit
#print axioms semEqDI_delta
#print axioms envWfT_member_body_closed
#print axioms semEqDI_of_whStep_delta
#print axioms semEqDI_of_convT_delta
#print axioms iotaWitnessS_same_branch
#print axioms iotaDetT
#print axioms iotaDetU_of_envWfT
#print axioms iotaRhsOf_eq_instPrefix_legacySchema
#print axioms approxDI_iotaS
#print axioms approxDI_iotaT
#print axioms approxDI_iota_of_envWfT
#print axioms approxDI_iotaU_of_envWfT
#print axioms semEqDI_of_convT_iota
#print axioms semEqDI_whStep
#print axioms semEqDI_whRed
#print axioms semEqDI_pi_inj
#print axioms semEqDI_pi_sort_disjoint
#print axioms pin_defSortEnv_delta
#print axioms pin_wZero_iota
#print axioms pin_admitted_families_iota
#print axioms pin_iotaDetU_natEnvU
#print axioms whStep_lam_false
#print axioms not_whStep_recursor_prefix
#print axioms whDet_of_envWfT
#print axioms whRed_normal_unique_of_envWfT
#print axioms lrTypeIN_trans_of_envWfT
#print axioms pin_whDet_defSortEnv_and_natEnvU
#print axioms not_whApproxInvCore_of_delta_sort
#print axioms not_whApproxInv_of_delta_sort
#print axioms not_whApproxInvCore_defSortEnv
#print axioms not_whApproxInv_defSortEnv
#print axioms not_whApproxInvCore_natEnv
#print axioms not_whApproxInv_natEnv
#print axioms WhApproxInvCoreDI
#print axioms WhApproxInvDI
#print axioms whApproxInvCoreDI_of_envWfT
#print axioms whApproxInvDI_of_envWfT
#print axioms approxDI_whRed_back
#print axioms approxDI_sort_of_whRed
#print axioms pin_whApproxInvDI_defSortEnv_and_natEnvU
#print axioms approxI_foldApps_spine_bot
#print axioms not_noSpine_foldApps_const_approxI
#print axioms foldAppCpt_curryStep_lt
#print axioms noSpine_recursor_prefix_approxDI
#print axioms noSpine_recursor_elim_approxDI
#print axioms PEqDI
#print axioms PEqDI.refl
#print axioms PEqDI.symm
#print axioms PEqDI.trans
#print axioms pEqDI_of_semEqDI
#print axioms tprojI_denDI_bot
#print axioms tprojI_denDI_prop
#print axioms pEqDI_irr
#print axioms pEqDI_delta
#print axioms pEqDI_iotaS
#print axioms pEqDI_iotaU_of_envWfT
#print axioms semEqDI_app_stable
#print axioms pEqDI_app_stable
#print axioms pEqDI_k_of_domTyped_iotaS
#print axioms TypeSoundnessDI
#print axioms semEqDI_of_tyConvT
#print axioms FundamentalLRINT_DI
#print axioms FundamentalTermDI
#print axioms AdequacyPiDI
#print axioms fundamentalLRINT_DI_of_fundamentalTermDI
#print axioms piRow_of_fundamentalLRINT_DI
#print axioms adequacyPiShape_of_fundamentalTermDI
#print axioms adequacyPiDI_of_fundamentalTermDI
#print axioms fundTermDI_sorts
#print axioms fundConvDI_of_whStep
#print axioms fundConvDI_of_whRed
#print axioms fundConvDI_delta
#print axioms fundConvDI_iota
#print axioms lrTypeIN_delta_DI
#print axioms lrTypeIN_iota_DI
#print axioms approxDI_lift0_one_iff
#print axioms denDI_lift0_one_eq
#print axioms semEqDI_lift0_one_iff
#print axioms semEqDI_lam_congrK
#print axioms EtaSoundAtDI
#print axioms LamIrrAtDI
#print axioms LamIotaAtDI
#print axioms IotaClauseUnderDI
#print axioms iotaClauseUnderDI_iff_semEqDI
#print axioms iotaClauseUnderDI_of_iotaWitnessS
#print axioms iotaClauseUnderDI_of_derivedIotaU
#print axioms lamIotaAtDI_of_iotaClause
#print axioms lamIotaAtDI_of_iotaWitnessS
#print axioms lamIotaAtDI_of_derivedIotaU
#print axioms noSpine_lift0_recursor_elim_approxDI
#print axioms lamIrrAtDI_of_domTyped
#print axioms lamIrrAtDI_of_domTyped_recursor
#print axioms pEqDI_etaK_of_eta_dom_iotaS
#print axioms whStep_bvar_false
#print axioms whRed_bvar_eq
#print axioms idPiProp
#print axioms idPiPropSortStep
#print axioms hasTyT_idPiProp
#print axioms approxI_idPiProp_sortStep
#print axioms approxDI_idPiProp_sortStep
#print axioms not_lrTypeI_idPiProp_sortStep
#print axioms not_lrTypeIN_idPiProp_sortStep
#print axioms not_lrTermI_idPiProp_sortStep
#print axioms not_fundamentalLRI
#print axioms not_fundamentalLRIN
#print axioms not_fundamentalLRINT
#print axioms not_fundamentalTermI
#print axioms not_fundamentalLRINT_DI
#print axioms not_fundamentalTermDI
#print axioms zetaLocalSortCtx
#print axioms zetaLocalSortCtx_wf
#print axioms zetaLocalSortCtx_conv
#print axioms not_typeSoundnessI
#print axioms not_typeSoundnessDI
#print axioms closedIrrPiL
#print axioms closedIrrPiR
#print axioms closedIrrPiCpt
#print axioms closedIrrPi_conv
#print axioms approxDI_closedIrrPiL_cpt
#print axioms approxI_closedIrrPiL_cpt
#print axioms not_approxDI_closedIrrPiR_cpt
#print axioms not_approxI_closedIrrPiR_cpt
#print axioms not_semEqI_closedIrrPi
#print axioms not_semEqDI_closedIrrPi
#print axioms BotDemand
#print axioms botDemand_nil
#print axioms approxDI_mono_env_nonbot
#print axioms approxDI_cons_botDemand_iff
#print axioms approxDI_cons_botDemand_bot_iff
#print axioms BotPiCpt
#print axioms botPiCpt_pi_bot_nil
#print axioms botPiCpt_pi_nil_step
#print axioms not_botPiCpt_spine
#print axioms not_botPiCpt_lam
#print axioms not_botPiCpt_idPiPropSortStep
#print axioms approxDI_of_lrTypeIN_botPiCpt
#print axioms LRTypeINBiDI
#print axioms lrTypeINBiDI_bvar_diag
#print axioms lrTypeINBiDI_sorts
#print axioms lrTypeINBiDI_sort_diag
#print axioms lrTypeINBiDI_rigidConsts
#print axioms lrTypeINBiDI_rigidConst_diag
#print axioms lrTypeINBiDI_pi
#print axioms lrTypeINBiDI_pi_diag
#print axioms lrTypeINBiDI_idPiProp
#print axioms lrTypeINBiDI_closedIrrPi
#print axioms lrTypeINBiDI_symm
#print axioms lrTypeINBiDI_trans
#print axioms lrTypeINBiDI_of_whStep
#print axioms lrTypeINBiDI_diag_of_whStep
#print axioms lrTypeINBiDI_beta
#print axioms lrTypeINBiDI_zeta
#print axioms lrTypeINBiDI_delta
#print axioms lrTypeINBiDI_iota
#print axioms lrTypeINBiDI_lit
#print axioms lrTypeINBiDI_letE_diag
#print axioms lrTypeINBiDI_deltaConst_diag
#print axioms lrTypeINBiDI_lit_diag
#print axioms FundamentalLRINBotDI
#print axioms fundamentalLRINBotDI_of_links
#print axioms piRow_of_fundamentalLRINBotDI
#print axioms not_tyConvT_pi_sort_of_fundamentalLRINBotDI
#print axioms not_isPropC_natEnv_spine0
#print axioms not_iotaClauseUnder_wZero
#print axioms not_iotaSoundAt_wZero
#print axioms MajorStableDI
#print axioms IotaSoundAtDI
#print axioms iotaSoundAtDI_of_iotaWitnessS
#print axioms iotaSoundAtDI_of_derivedIotaU
#print axioms majorStableDI_of_domTyped
#print axioms majorStableDI_of_domTyped_recursor
#print axioms pEqDI_K
#print axioms pEqDI_K_of_domTyped
#print axioms eta_unsound_bot_DI
#print axioms approxDI_eta_lam_intro
#print axioms semEqI_eta_lam
#print axioms semEqDI_eta_lam
#print axioms etaSoundAt_lam
#print axioms etaSoundAtDI_lam
#print axioms semEqDI_eta_delta_lam
#print axioms etaSoundAtDI_delta_lam
#print axioms whStep_app_lam_eq
#print axioms whStep_app2_lam_eq
#print axioms whStep_app3_lam_eq
#print axioms whRed_step_inv_of_unique
#print axioms irrProjType
#print axioms irrProjL
#print axioms irrProjR
#print axioms irrProjCpt
#print axioms hasTyT_irrProjType
#print axioms hasTyT_irrProjL
#print axioms hasTyT_irrProjR
#print axioms convT_irrProj
#print axioms approxI_irrProjL
#print axioms approxDI_irrProjL
#print axioms not_approxI_irrProjR
#print axioms not_approxDI_irrProjR
#print axioms not_lrTermI_irrProj
#print axioms IrrCaseT_DI
#print axioms not_irrCaseT
#print axioms not_irrCaseT_DI
#print axioms etaIdPiPropFn
#print axioms etaIdPiPropCpt
#print axioms hasTyT_etaIdPiPropFn
#print axioms approxI_eta_etaIdPiPropFn
#print axioms approxDI_eta_etaIdPiPropFn
#print axioms not_lrTermI_eta_etaIdPiPropFn
#print axioms EtaCaseT_DI
#print axioms not_etaCaseT
#print axioms not_etaCaseT_DI
#print axioms whStep_iota_lift
#print axioms whStep_iota_instantiate
#print axioms whStep_lift_of_envClosed
#print axioms whRed_lift_of_envClosed
#print axioms whStep_instantiate_of_envClosed
#print axioms whRed_instantiate_of_envClosed
#print axioms whRed_instantiate_sort_of_envClosed
#print axioms whRed_instantiate_pi_of_envClosed
#print axioms tyConvT_ctx
#print axioms ctxConvT_append_same
#print axioms hasTyT_tyConvT_assumption
#print axioms convT_tyConvT_assumption
#print axioms tyConvT_tyConvT_assumption
#print axioms hasTyT_tyConvT_head
#print axioms convT_tyConvT_head
#print axioms tyConvT_tyConvT_head
#print axioms codomain_transport_of_tyConvT
#print axioms lrTypeIN_weaken_botPiCpt
#print axioms lrTypeIN_weaken0_botPiCpt
#print axioms lrTypeINBiDI_weaken0
#print axioms lrTypeIN_subst_botPiCpt
#print axioms lrTypeIN_subst0_botPiCpt
#print axioms lrTypeIN_substLet_botPiCpt
#print axioms lrTypeIN_substLet0_botPiCpt

end Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
