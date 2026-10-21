import rcic.RcicNativeTypedModelProbe
import rcic.RcicIotaLegacyBridge
import rcic.RcicDerivedIotaU

/-!
# RcicNativeTypedModelTypingFin — the model typing lemma (finite-joint form): refutations,
covariant restatement, and simultaneous induction with conversion soundness

This module addresses the HANDOFF on PR #7673 (`issuecomment-6271576104`, §2.3/§2.4):
the finite-joint model typing lemma `TypingLemmaEnvFinT` and its simultaneous induction with
model conversion soundness.

## Summary of results

1. **§1 — Handoff §2.3 interface & single-code non-suppliability (`not_argTypedAt_polyId`).**
   We state the exact §2.3 definitions (`ArgTypedFinAt`, `ModelBetaExpandTypedFin`,
   `argTypedFinAt_of_argTypedAt`, `not_argTypedFinAt_cex`, `modelBetaExpandTyped_of_fin`,
   `EnvTypedFinAtT`, `TypingLemmaEnvFinT`, `ArgTypedFinAtM`, `ModelBetaExpandTypedM`,
   `modelBetaExpandTypedM_iff_fin`) and #7728's ι premises (`ModelIotaStepT`,
   `ReadbackIotaStepT`, with `readbackIotaStepT_whStepCtx` and `modelIotaStepT_of_iotaSoundT`),
   and kernel-check `not_argTypedAt_polyId : ¬ ArgTypedAt E ρ cexPolyId cexPolyIdTy`.

2. **§2 — Three independent kernel refutations of `TypingLemmaEnvFinT` (and `ArgTypedFinAt`,
   `TypingLemmaEnvT`, `TypingLemmaT`) on `ApproxT`.**
   * **Obstruction 1 (`not_elT_polyId_cpt01`, `not_argTypedFinAt_polyId`,
     `not_typingLemmaT`, `not_typingLemmaEnvT`, `not_typingLemmaEnvFinT`)**:
     At the handoff's polymorphic identity `cexPolyId = λ (X : Sort 1) (x : X). x` of type
     `cexPolyIdTy = Π (X : Sort 1), X → X` in `Γ = []`, `ρ = EnvT.bot` (at **every**
     `E : ResolvedEnv` and `n : Nat`), `CTyS`'s universal cross-step compatibility clause
     `∀ s ∈ f, ∀ t ∈ g, (∀ v ∈ t.1, v ∈ s.1) → CTyS E s.2 t.2` refutes even the finite-joint
     and single-compact statements.  Specifically, the step `s₀ = ([.sort], λ [([.prop], .prop)])`
     requires a covering codomain step `t ∈ g` with `t.1 ⊆ [.sort]`; since `[.sort] ⊆ [.sort, X₁]`
     (where `X₁ = .pi .sort [([.prop], .sort)]`), universal compatibility forces the step
     `s₁ = ([.sort, X₁], λ [([u₁], u₁)])` (with `u₁ = .lam [([.prop], .prop)]`) to have its output
     typed at `t.2`, which is a compact of `X → X` under `X ↦ t.1 ⊆ [.sort]` (where `X` can only
     denote `.bot` or `.sort`), contradiction.
   * **Obstruction 2 (`not_joint_ctyT_idOnVar`)**:
     Even if `CTyS` is weakened all the way to `CTyT` (dropping coverage and universal cross-step
     compatibility), the multi-compact jointness condition in `TypingLemmaEnvFinT` still fails in
     `Γ = [X : Sort 1]` at the valid `EnvTypedFinAtT` environment
     `ρ = EnvT.cons (demandT [.sort, X₁]) EnvT.bot` for `λ (x : X). x : X → X`: the two 1-step
     compacts `polyIdOut0` and `polyIdOut1` are each individually in `ElT`, yet no single compact
     `.pi a f` of `X → X` in `ρ` types both (since `a ∈ {.bot, .sort, X₁}`).
   * **Obstruction 3 (`not_elT_spine_pi`, `not_elTCov_spine_pi`, `not_semEqT_eta_rigidConst`)**:
     At any non-proof rigid constant `r` of Π-type `.pi A B` (such as `Nat.succ : Nat → Nat` in
     `natEnvU`), `ApproxT.const` produces `.spine r []`, which is untyped at every compact of
     `.pi A B` (under both `CTyT` and `CTyCov`) and separates `.const r ls` from its η-expansion
     (`ConvT.eta`).
   * **Obstruction 4 (`not_typingLemmaEnvFinT_letBinding`, `not_typingLemmaEnvFinT_via_letBinding`)**:
     `EnvTypedFinAtT` (and `EnvTypedAtT`) inspects only `lookupType` and omits `CtxEnvT`
     (`letBinding` value coherence), refuting `TypingLemmaEnvFinT` even on the non-polymorphic
     1-step term `idSort1 = λ (Y : Sort 1). Y : .bvar 0` in `letSort1Ctx` at `EnvT.bot`.

3. **§3 — Exact restatement (`CTyCov`, `ElTCov`, `TypingLemmaEnvCovT`), `letBinding`/`letE`
   resolutions, and pointwise `relSubstAtT_cons_pointwise`.**
   * `CTyCov` combines `CTyS`'s universal `hcod` and existential `hcov` into the existential
     step-covering clause `∀ s ∈ f, s.2 = .bot ∨ ∃ t ∈ g, (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov E s.2 t.2`
     (which is all `typedPERS`'s `irrel_stepS` / `symmTm_stepS` / `transTm_stepS` ever consume).
     It preserves proposition collapse (`ctyCov_prop_bot`), is implied by `CTyS`
     (`ctyCov_of_ctyS`), is monotone in the codomain step list (`ctyCov_pi_mono_steps`), and
     types `cexPolyId`'s refuting compacts (`elTCov_polyId_cpt01`, `joint_ctyCov_polyId_cpt0_cpt1`),
     `letSort1Ctx`'s `zetaLocal`-converted term (`envTypedCovAtT_letSort1Ctx`,
     `elTCov_idSort1_bvar0_ctxEnvT`), and concrete `letE`/`zeta` terms (`elTCov_letSort1`,
     `semEqT_zeta_letSort1`, `elTCov_letIdSort1`).
   * `relSubstAtT_cons_pointwise` unbundles the single domain code `{a : CptT}` in
     `relSubstAtT_cons` into pointwise `∀ v ∈ d, ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ CTyS E v a`,
     showing that `fundT_beta` only ever needed pointwise argument typing (`fundT_beta_pointwise`),
     not multi-compact jointness across `us`.

4. **§4 — The simultaneous inductions (`TypingLemmaEnvFinT` + `ConvSoundEnvFinT` over abstract
   model laws, and concrete `ApproxT` simultaneous induction for `TypingLemmaEnvCovT` +
   `ConvSoundEnvCovT`).**
   * §4A proves the simultaneous strong induction on `sizeOf` of `HasTyT` and `ConvT` for
     `TypingLemmaEnvFinCtxT` + `ConvSoundEnvFinT`, with non-vacuity witness `ctxModelT_botOnly`.
   * §4B proves finite-demand factorization on `ApproxT E` (`approxT_fin_at`,
     `approxT_cons_iff_exists_demandT`) and `letBinding` environment extension
     (`envTypedCovAtT_cons_letBinding`), and discharges **8 of 9 `HasTyT` constructors** (`sort`,
     `bvar`, `pi`, `lam`, `app`, `letE`, `lit`, `conv` — every constructor except `const`) and
     **14 of 18 `ConvT` constructors** (`refl`, `symm`, `trans`, `zetaLocal`, `delta`, `iota`,
     `lit`, `app`, `lam`, `pi`, `sorts`, `consts`, `irr`, `tyConv`) directly on `ApproxT E` in
     `covTyping_step`, plus the unconditional forward β/ζ reduction directions (`covConv_beta_fwd`,
     `covConv_zeta_fwd`) and the exact reduction of backward β/ζ/`letE` conversion to
     `ArgTypedFinAt` (`covConv_beta_of_argTypedFinAt`, `covConv_zeta_of_argTypedFinAt`,
     `covConv_letE_of_zeta`).

5. **§5 — Concrete `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` instances on `natEnvU`
   (`natEnvUWfT`) and the constant/recursor clause (`ConstCovClauseT`, `covTyping_const`).**
   * On `natEnvU` (`natEnvUWfT`), `Nat` (`.const 0 []`) and `Nat.zero` (`.const 1 []`) satisfy
     `ElT` and `ElTCov` at every compact (`elT_natEnvU_nat`, `elT_natEnvU_zero`), while
     `Nat.succ` (`.const 2 [] : Nat → Nat`) refutes `ElTCov` and `ConvT.eta` via `.spine 2 []`
     (`not_elTCov_natSucc_spine`, `not_semEqT_eta_natSucc`).
   * For `Nat.rec` (`.const 3 [.succ .zero]`), `ApproxT.recursor` without step-typing produces
     `covBadRecCpt` (at `us_pre = [[], [], [covBadHsCpt]]`, `us_fields = [[covBadSpine]]`) which is
     not in `ElTCov` (`not_elTCov_natRec_covBadRecCpt`, `not_elT_natRec_covBadRecCpt`), whereas at
     well-typed motive/minor demands `ApproxT.recursor` produces `covGoodRecCpt` which IS in both
     `ElT` and `ElTCov` at `instantiateLevels [.succ .zero] natRecMemberU.mtype`
     (`approxT_natRec_covGoodRecCpt`, `elT_natRec_covGoodRecCpt`, `elTCov_natRec_covGoodRecCpt`).
   * `ConstCovClauseT` (`covTyping_const`) isolates the exact 9th `HasTyT` constructor obligation.

`closure_claim = 0`.  No `sorry`, no `Classical.choice`, axioms `⊆ {propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — Handoff §2.3 & #7728 declarations, plus `not_argTypedAt_polyId` -/

namespace TypingFin

/-- **Finite-joint argument typing** (handoff §2.3): every finite list of compacts of `arg` is
    jointly typed at one code of `A`. -/
def ArgTypedFinAt (E : ResolvedEnv) (ρ : EnvT) (arg A : Expr Nat) : Prop :=
  ∀ us : List CptT, (∀ u ∈ us, ApproxT E ρ arg u) → ∃ a, ApproxT E ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- **Typed β expansion, finite-joint form** (handoff §2.3, swe-zeta #7704). -/
def ModelBetaExpandTypedFin (E : ResolvedEnv) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, ArgTypedFinAt E ρ arg A →
    ApproxT E ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), ApproxT E ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, ApproxT E ρ arg u) ∧ ApproxT E (EnvT.cons (demandT us) ρ) body c

theorem argTypedFinAt_of_argTypedAt {E : ResolvedEnv} {ρ : EnvT} {arg A : Expr Nat} :
    ArgTypedAt E ρ arg A → ArgTypedFinAt E ρ arg A :=
  fun ⟨a, hA, hty⟩ _ hus => ⟨a, hA, fun u hu => hty u (hus u hu)⟩

theorem not_argTypedFinAt_cex (E : ResolvedEnv) (ρ : EnvT) : ¬ ArgTypedFinAt E ρ cexP cexD := by
  intro hfin
  have hP : ApproxT E ρ cexP (.pi .bot []) := approxT_pi_bot_nil E ρ _ _
  obtain ⟨a, hDa, hty⟩ := hfin [.pi .bot []] (fun u hu => by
    rcases List.mem_singleton.mp hu with rfl; exact hP)
  rcases approxT_cexD_shape hDa with rfl | ⟨g, rfl⟩
  · exact CptT.noConfusion (ctyS_bot_inv (hty _ (List.mem_singleton.mpr rfl)))
  · exact CptT.noConfusion (ctyS_lam_inv (hty _ (List.mem_singleton.mpr rfl)))

theorem modelBetaExpandTyped_of_fin {E : ResolvedEnv} :
    ModelBetaExpandTypedFin E → ModelBetaExpandTyped E :=
  fun hfin _ _ _ _ _ hT hc => hfin (argTypedFinAt_of_argTypedAt hT) hc

/-- **Environment typing, finite-joint form** (handoff §2.3). -/
def EnvTypedFinAtT (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ∀ us : List CptT,
    (∀ u ∈ us, ρ i u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- **The model typing lemma, finite-joint form** (handoff §2.3). -/
def TypingLemmaEnvFinT (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A → ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ →
    ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ e u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- Model-parametric `ArgTypedFinAt` (handoff §2.3). -/
def ArgTypedFinAtM (M : CtxModelT E) (ρ : EnvT) (arg A : Expr Nat) : Prop :=
  ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ arg u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- Model-parametric `ModelBetaExpandTypedFin` (handoff §2.3). -/
def ModelBetaExpandTypedM (M : CtxModelT E) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, ArgTypedFinAtM M ρ arg A →
    M.Ap ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), M.Ap ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c

theorem modelBetaExpandTypedM_iff_fin {E : ResolvedEnv} :
    ModelBetaExpandTypedM (ctxModelT_approxT E) ↔ ModelBetaExpandTypedFin E :=
  ⟨fun h _ _ _ _ _ hT hc => h hT hc, fun h _ _ _ _ _ hT hc => h hT hc⟩

/-- **The model's ι law** (#7728): every derived-ι pair has the same compacts at every environment. -/
def ModelIotaStepT (E : ResolvedEnv) (M : CtxModelT E) : Prop :=
  ∀ {lhs rhs : Expr Nat}, DerivedIota E lhs rhs → ∀ (ρ : EnvT) (c : CptT),
    M.Ap ρ lhs c ↔ M.Ap ρ rhs c

/-- **The readback's ι clause** (#7728): a derived-ι pair steps in one readback step. -/
def ReadbackIotaStepT (E : ResolvedEnv) (R : Readback) : Prop :=
  ∀ (Γ : LCtx) {lhs rhs : Expr Nat}, DerivedIota E lhs rhs → R Γ lhs rhs

theorem readbackIotaStepT_whStepCtx (E : ResolvedEnv) : ReadbackIotaStepT E (WhStepCtx E) :=
  fun _ _ _ h => .iota (derivedIotaU_ofDerivedIota h)

theorem modelIotaStepT_of_iotaSoundT {E : ResolvedEnv} (hW : EnvWfT E) (hI : IotaSoundT E) :
    ModelIotaStepT E (ctxModelT_approxT E) := by
  intro lhs rhs h ρ c
  obtain ⟨ht⟩ := derivedIotaT_of_derivedIota_envWfT hW h
  obtain ⟨w', hl, hr⟩ := derivedIotaT_inv ht
  have hse := hI w' ρ c
  rw [hl, hr] at hse
  exact hse

theorem sortCode_succ (l : Level) : sortCode (.succ l) = .sort :=
  (sortCode_eq_sort_iff _).mpr (Rcic.Declarative.Ann.not_eqN_succ_zero l)

/-- The polymorphic identity `λ (X : Sort 1) (x : X). x` and its type `Π (X : Sort 1), X → X`. -/
def cexPolyId : Expr Nat := .lam (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0))
def cexPolyIdTy : Expr Nat := .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))

end TypingFin

open TypingFin

/-- Typing derivation of `cexPolyId : cexPolyIdTy` in `Γ = []` at any `(E, n)`. -/
def hasTyT_cexPolyId (E : ResolvedEnv) (n : Nat) : HasTyT E n [] cexPolyId cexPolyIdTy :=
  .lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.lam (.bvar 0) (.bvar 0))
    (.pi (.bvar 0) (.bvar 1))
    (.sort [] (.succ .zero))
    (.lam [.assumption (.sort (.succ .zero))] (.bvar 0) (.succ .zero) (.bvar 0) (.bvar 1)
      (.bvar _ 0 _ rfl)
      (.bvar _ 0 _ rfl))

/-! ### §2 — Kernel refutations of `TypingLemmaEnvFinT`, `ArgTypedFinAt`, `TypingLemmaEnvT`, `TypingLemmaT` -/

/-- The Π-type code `Π (_ : Sort), Sort` with step `[([.prop], .sort)]`. -/
def polyIdDom1 : CptT := .pi .sort [([.prop], .sort)]

/-- The witness compact `λ [([.prop], .prop)]` typed at `polyIdDom1`. -/
def polyIdWitness1 : CptT := .lam [([.prop], .prop)]

/-- Inner output compact at `X = .sort`: `λ [([.prop], .prop)]`. -/
def polyIdOut0 : CptT := .lam [([.prop], .prop)]

/-- Inner output compact at `X = polyIdDom1`: `λ [([polyIdWitness1], polyIdWitness1)]`. -/
def polyIdOut1 : CptT := .lam [([polyIdWitness1], polyIdWitness1)]

/-- 1-step compact of `cexPolyId` demanding `[.sort]` on `X`. -/
def polyIdCpt0 : CptT := .lam [([.sort], polyIdOut0)]

/-- 1-step compact of `cexPolyId` demanding `[.sort, polyIdDom1]` on `X`. -/
def polyIdCpt1 : CptT := .lam [([.sort, polyIdDom1], polyIdOut1)]

/-- Single 2-step compact of `cexPolyId` combining both steps. -/
def polyIdCpt01 : CptT := .lam [([.sort], polyIdOut0), ([.sort, polyIdDom1], polyIdOut1)]

theorem tyCodeCT_polyIdDom1 : TyCodeCT polyIdDom1 :=
  .pi .sort (fun t ht => by
    rcases List.mem_singleton.mp ht with rfl
    exact .sort)

theorem not_isPropCT_polyIdDom1 (E : ResolvedEnv) : ¬ IsPropCT E polyIdDom1 := by
  intro h
  cases h with
  | pi _ hg =>
      exact not_isPropCT_sort E (hg ([.prop], .sort) (List.mem_singleton.mpr rfl))

theorem ctyS_prop_sort (E : ResolvedEnv) : CTyS E .prop .sort := by
  rw [CTyS]; exact Or.inr .prop

theorem ctyS_sort_sort (E : ResolvedEnv) : CTyS E .sort .sort := by
  rw [CTyS]; exact Or.inr .sort

theorem ctyS_polyIdDom1_sort (E : ResolvedEnv) : CTyS E polyIdDom1 .sort := by
  rw [CTyS]; exact Or.inr tyCodeCT_polyIdDom1

theorem ctyS_polyIdWitness1_polyIdDom1 (E : ResolvedEnv) :
    CTyS E polyIdWitness1 polyIdDom1 := by
  rw [polyIdDom1, CTyS]
  refine Or.inr ⟨[([.prop], .prop)], rfl, not_isPropCT_polyIdDom1 E, ?_, ?_, ?_⟩
  · intro s hs v hv
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hv with rfl
    exact ctyS_prop_sort E
  · intro s hs t ht _
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp ht with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact Or.inr ⟨([.prop], .sort), List.mem_singleton.mpr rfl, fun v hv => hv⟩

theorem approxT_polyIdOut0 (E : ResolvedEnv) (ρ : EnvT) {d : List CptT} (hd : CptT.sort ∈ d) :
    ApproxT E (EnvT.cons (demandT d) ρ) (.lam (.bvar 0) (.bvar 0)) polyIdOut0 := by
  refine .lam (.bvar hd) ?_ ⟨([.prop], .prop), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .bvar (List.mem_singleton.mpr rfl)

theorem approxT_polyIdOut1 (E : ResolvedEnv) (ρ : EnvT) {d : List CptT} (hd : polyIdDom1 ∈ d) :
    ApproxT E (EnvT.cons (demandT d) ρ) (.lam (.bvar 0) (.bvar 0)) polyIdOut1 := by
  refine .lam (.bvar hd) ?_
    ⟨([polyIdWitness1], polyIdWitness1), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_polyIdWitness1_polyIdDom1 E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .bvar (List.mem_singleton.mpr rfl)

theorem approxT_cexPolyId_cpt0 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ cexPolyId polyIdCpt0 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  refine .lam hA ?_ ⟨([.sort], polyIdOut0), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_sort_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact approxT_polyIdOut0 E ρ (List.mem_singleton.mpr rfl)

theorem approxT_cexPolyId_cpt1 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ cexPolyId polyIdCpt1 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  refine .lam hA ?_ ⟨([.sort, polyIdDom1], polyIdOut1), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact ctyS_sort_sort E
    · rcases List.mem_singleton.mp hu' with rfl
      exact ctyS_polyIdDom1_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact approxT_polyIdOut1 E ρ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

theorem approxT_cexPolyId_cpt01 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ cexPolyId polyIdCpt01 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  refine .lam hA ?_ ⟨([.sort], polyIdOut0), List.mem_cons_self _ _, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs'
    · rcases List.mem_singleton.mp hu with rfl
      exact ctyS_sort_sort E
    · rcases List.mem_singleton.mp hs' with rfl
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact ctyS_sort_sort E
      · rcases List.mem_singleton.mp hu' with rfl
        exact ctyS_polyIdDom1_sort E
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact approxT_polyIdOut0 E ρ (List.mem_singleton.mpr rfl)
    · rcases List.mem_singleton.mp hs' with rfl
      exact approxT_polyIdOut1 E ρ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

/-- Any compact `t2` of `X → X` formed under a demand `ts ⊆ [.sort]` on `X` cannot type
    `polyIdOut1` (even under `CTyT`), because `X`'s domain code is `.bot` or `.sort`, neither of
    which types `polyIdWitness1 = .lam [([.prop], .prop)]`. -/
theorem not_ctyT_polyIdOut1_of_sub_sort {E : ResolvedEnv} {ρ : EnvT} {ts : List CptT} {t2 : CptT}
    (hsub : ∀ v ∈ ts, v ∈ ([CptT.sort] : List CptT))
    (hstep : ApproxT E (EnvT.cons (demandT ts) ρ) (.pi (.bvar 0) (.bvar 1)) t2) :
    ¬ CTyT E polyIdOut1 t2 := by
  intro hty
  rcases approxT_pi_inv hstep with rfl | ⟨a', f', rfl, hA', _⟩
  · exact CptT.noConfusion (ctyT_bot_inv hty)
  · rcases ctyT_pi_inv hty with h0 | ⟨f₁, hf₁, _, hdom, _⟩
    · exact CptT.noConfusion h0
    · injection hf₁ with hf₁'
      subst hf₁'
      have hw : CTyT E polyIdWitness1 a' :=
        hdom ([polyIdWitness1], polyIdWitness1) (List.mem_singleton.mpr rfl)
          polyIdWitness1 (List.mem_singleton.mpr rfl)
      rcases approxT_bvar_inv hA' with rfl | hmem
      · exact CptT.noConfusion (ctyT_bot_inv hw)
      · have hasort : a' = .sort := List.mem_singleton.mp (hsub a' hmem)
        subst hasort
        rcases ctyT_sort_inv hw with h0 | htc
        · exact CptT.noConfusion h0
        · cases htc

theorem not_ctyS_polyIdOut1_of_sub_sort {E : ResolvedEnv} {ρ : EnvT} {ts : List CptT} {t2 : CptT}
    (hsub : ∀ v ∈ ts, v ∈ ([CptT.sort] : List CptT))
    (hstep : ApproxT E (EnvT.cons (demandT ts) ρ) (.pi (.bvar 0) (.bvar 1)) t2) :
    ¬ CTyS E polyIdOut1 t2 :=
  fun h => not_ctyT_polyIdOut1_of_sub_sort hsub hstep (ctyT_of_ctyS t2 polyIdOut1 h)

/-- **Refutation 1a (`ElT`)**: the compact `polyIdCpt01` of `cexPolyId` is not in `ElT` of
    `cexPolyIdTy` at any environment. -/
theorem not_elT_polyId_cpt01 (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ElT E ρ cexPolyIdTy polyIdCpt01 := by
  rintro ⟨a, hAa, hty⟩
  rcases approxT_pi_inv hAa with rfl | ⟨a', f, rfl, _, hf⟩
  · exact CptT.noConfusion (ctyS_bot_inv hty)
  · rcases ctyS_pi_inv hty with h0 | ⟨g, hg, _, _, hcod, hcov⟩
    · exact CptT.noConfusion h0
    · injection hg with hg'
      subst hg'
      have hs0 : ([CptT.sort], polyIdOut0) ∈
          ([([CptT.sort], polyIdOut0), ([CptT.sort, polyIdDom1], polyIdOut1)] : List (List CptT × CptT)) :=
        List.mem_cons_self _ _
      have hs1 : ([CptT.sort, polyIdDom1], polyIdOut1) ∈
          ([([CptT.sort], polyIdOut0), ([CptT.sort, polyIdDom1], polyIdOut1)] : List (List CptT × CptT)) :=
        List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
      rcases hcov _ hs0 with hbot | ⟨t, htf, hsub0⟩
      · exact CptT.noConfusion hbot
      · have hsub1 : ∀ v ∈ t.1, v ∈ ([CptT.sort, polyIdDom1] : List CptT) := by
          intro v hv
          have := List.mem_singleton.mp (hsub0 v hv)
          subst this
          exact List.mem_cons_self _ _
        exact not_ctyS_polyIdOut1_of_sub_sort hsub0 (hf t htf).2 (hcod _ hs1 t htf hsub1)

/-- **Refutation 1b (2-element 1-step list)**: the two 1-step compacts `polyIdCpt0` and
    `polyIdCpt1` of `cexPolyId` have no joint code in `cexPolyIdTy` under `CTyS`. -/
theorem not_joint_ctyS_polyId_cpt0_cpt1 (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ∃ a, ApproxT E ρ cexPolyIdTy a ∧ CTyS E polyIdCpt0 a ∧ CTyS E polyIdCpt1 a := by
  rintro ⟨a, hAa, hty0, hty1⟩
  rcases approxT_pi_inv hAa with rfl | ⟨a', f, rfl, _, hf⟩
  · exact CptT.noConfusion (ctyS_bot_inv hty0)
  · rcases ctyS_pi_inv hty0 with h0 | ⟨g0, hg0, _, _, _, hcov0⟩
    · exact CptT.noConfusion h0
    · injection hg0 with hg0'; subst hg0'
      rcases ctyS_pi_inv hty1 with h1 | ⟨g1, hg1, _, _, hcod1, _⟩
      · exact CptT.noConfusion h1
      · injection hg1 with hg1'; subst hg1'
        rcases hcov0 ([.sort], polyIdOut0) (List.mem_singleton.mpr rfl) with hbot | ⟨t, htf, hsub0⟩
        · exact CptT.noConfusion hbot
        · have hsub1 : ∀ v ∈ t.1, v ∈ ([CptT.sort, polyIdDom1] : List CptT) := by
            intro v hv
            have := List.mem_singleton.mp (hsub0 v hv)
            subst this
            exact List.mem_cons_self _ _
          exact not_ctyS_polyIdOut1_of_sub_sort hsub0 (hf t htf).2
            (hcod1 ([.sort, polyIdDom1], polyIdOut1) (List.mem_singleton.mpr rfl) t htf hsub1)

/-- **Refutation 1c (`ArgTypedFinAt`)**: `ArgTypedFinAt` is refuted at the polymorphic identity
    `cexPolyId : cexPolyIdTy` (both by `[polyIdCpt0, polyIdCpt1]` and by `[polyIdCpt01]`). -/
theorem not_argTypedFinAt_polyId (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ArgTypedFinAt E ρ cexPolyId cexPolyIdTy := by
  intro hfin
  obtain ⟨a, hAa, hty⟩ := hfin [polyIdCpt0, polyIdCpt1] (by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact approxT_cexPolyId_cpt0 E ρ
    · rcases List.mem_singleton.mp hu' with rfl
      exact approxT_cexPolyId_cpt1 E ρ)
  exact not_joint_ctyS_polyId_cpt0_cpt1 E ρ
    ⟨a, hAa, hty polyIdCpt0 (List.mem_cons_self _ _),
      hty polyIdCpt1 (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))⟩

namespace TypingFin

/-- **Kernel check of handoff §2.3 risk (`not_argTypedAt_polyId`)**: single-code `ArgTypedAt`
    is not suppliable at `cexPolyId : cexPolyIdTy`. -/
theorem not_argTypedAt_polyId (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ArgTypedAt E ρ cexPolyId cexPolyIdTy :=
  fun h => not_argTypedFinAt_polyId E ρ (argTypedFinAt_of_argTypedAt h)

end TypingFin

/-- **Refutation 1d (`TypingLemmaT`)**: `TypingLemmaT E n` is false for every `(E, n)`. -/
theorem not_typingLemmaT (E : ResolvedEnv) (n : Nat) : ¬ TypingLemmaT E n := by
  intro hTL
  exact not_elT_polyId_cpt01 E (ctxEnvT E [])
    (hTL .nil (hasTyT_cexPolyId E n) polyIdCpt01 (approxT_cexPolyId_cpt01 E (ctxEnvT E [])))

/-- **Refutation 1e (`TypingLemmaEnvT`)**: `TypingLemmaEnvT (ctxModelT_approxT E) n` is false
    for every `(E, n)`. -/
theorem not_typingLemmaEnvT (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaEnvT (ctxModelT_approxT E) n := by
  intro hTL
  have hE : EnvTypedAtT (ctxModelT_approxT E) [] EnvT.bot := envTypedAtT_bot []
  exact not_elT_polyId_cpt01 E EnvT.bot
    (hTL (hasTyT_cexPolyId E n) hE polyIdCpt01 (approxT_cexPolyId_cpt01 E EnvT.bot))

/-- The empty-context `EnvT.bot` satisfies `EnvTypedFinAtT` vacuously. -/
theorem envTypedFinAtT_nil (M : CtxModelT E) (ρ : EnvT) : EnvTypedFinAtT M [] ρ :=
  fun _ _ h => Option.noConfusion h

/-- **Refutation 1f (`TypingLemmaEnvFinT`)**: `TypingLemmaEnvFinT (ctxModelT_approxT E) n` is
    false for every `(E, n)`. -/
theorem not_typingLemmaEnvFinT (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaEnvFinT (ctxModelT_approxT E) n := by
  intro hTL
  obtain ⟨a, hAa, hty⟩ := hTL (hasTyT_cexPolyId E n)
    (envTypedFinAtT_nil (ctxModelT_approxT E) EnvT.bot)
    [polyIdCpt0, polyIdCpt1] (by
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact approxT_cexPolyId_cpt0 E EnvT.bot
      · rcases List.mem_singleton.mp hu' with rfl
        exact approxT_cexPolyId_cpt1 E EnvT.bot)
  exact not_joint_ctyS_polyId_cpt0_cpt1 E EnvT.bot
    ⟨a, hAa, hty polyIdCpt0 (List.mem_cons_self _ _),
      hty polyIdCpt1 (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))⟩

/-! #### Refutation 2: multi-compact jointness fails at a type-variable binder even under `CTyT` -/

/-- Context `[X : Sort 1]`. -/
def polyIdVarCtx : LCtx := [.assumption (.sort (.succ .zero))]

/-- Environment assigning `{.sort, polyIdDom1}` to `X : Sort 1`. -/
def polyIdVarEnv (ρ : EnvT) : EnvT := EnvT.cons (demandT [.sort, polyIdDom1]) ρ

/-- Term `λ (x : X). x` and its type `X → X` in `polyIdVarCtx`. -/
def idOnVar : Expr Nat := .lam (.bvar 0) (.bvar 0)
def idOnVarTy : Expr Nat := .pi (.bvar 0) (.bvar 1)

def hasTyT_idOnVar (E : ResolvedEnv) (n : Nat) : HasTyT E n polyIdVarCtx idOnVar idOnVarTy :=
  .lam polyIdVarCtx (.bvar 0) (.succ .zero) (.bvar 0) (.bvar 1)
    (.bvar _ 0 _ rfl)
    (.bvar _ 0 _ rfl)

theorem envTypedFinAtT_polyIdVarEnv (E : ResolvedEnv) :
    EnvTypedFinAtT (ctxModelT_approxT E) polyIdVarCtx (polyIdVarEnv EnvT.bot) := by
  intro i A hA us hus
  cases i with
  | zero =>
      simp only [polyIdVarCtx, lookupType, List.get?_cons_zero] at hA
      injection hA with hA; subst hA
      have hsort : ApproxT E (polyIdVarEnv EnvT.bot) (lift 0 1 (.sort (.succ .zero))) .sort := by
        simpa only [lift, sortCode_succ] using
          approxT_sort_code E (polyIdVarEnv EnvT.bot) (.succ .zero)
      refine ⟨.sort, hsort, fun u hu => ?_⟩
      rcases List.mem_cons.mp (hus u hu) with rfl | hu'
      · exact ctyS_sort_sort E
      · rcases List.mem_singleton.mp hu' with rfl
        exact ctyS_polyIdDom1_sort E
  | succ j =>
      simp [polyIdVarCtx, lookupType] at hA

theorem approxT_idOnVar_polyIdOut0 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E (polyIdVarEnv ρ) idOnVar polyIdOut0 :=
  approxT_polyIdOut0 E ρ (List.mem_cons_self _ _)

theorem approxT_idOnVar_polyIdOut1 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E (polyIdVarEnv ρ) idOnVar polyIdOut1 :=
  approxT_polyIdOut1 E ρ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

/-- **Refutation 2 (`not_joint_ctyT_idOnVar`)**: in `polyIdVarCtx` under `polyIdVarEnv EnvT.bot`
    (which satisfies `EnvTypedFinAtT`), both `polyIdOut0` (`approxT_idOnVar_polyIdOut0`) and
    `polyIdOut1` (`approxT_idOnVar_polyIdOut1`) are compacts of `idOnVar : idOnVarTy`, yet no
    single compact `a` of `idOnVarTy` types both even under the weak `CTyT` (without coverage or
    universal `hcod`). -/
theorem not_joint_ctyT_idOnVar (E : ResolvedEnv) :
    ¬ ∃ a, ApproxT E (polyIdVarEnv EnvT.bot) idOnVarTy a ∧
      CTyT E polyIdOut0 a ∧ CTyT E polyIdOut1 a := by
  rintro ⟨a, hAa, hty0, hty1⟩
  rcases approxT_pi_inv hAa with rfl | ⟨a_X, f, rfl, hAX, _⟩
  · exact CptT.noConfusion (ctyT_bot_inv hty0)
  · rcases ctyT_pi_inv hty0 with h0 | ⟨f0, hf0, _, hdom0, _⟩
    · exact CptT.noConfusion h0
    · injection hf0 with hf0'; subst hf0'
      rcases ctyT_pi_inv hty1 with h1 | ⟨f1, hf1, _, hdom1, _⟩
      · exact CptT.noConfusion h1
      · injection hf1 with hf1'; subst hf1'
        have hprop : CTyT E .prop a_X :=
          hdom0 ([.prop], .prop) (List.mem_singleton.mpr rfl) .prop (List.mem_singleton.mpr rfl)
        have hwit : CTyT E polyIdWitness1 a_X :=
          hdom1 ([polyIdWitness1], polyIdWitness1) (List.mem_singleton.mpr rfl)
            polyIdWitness1 (List.mem_singleton.mpr rfl)
        rcases approxT_bvar_inv hAX with rfl | hmem
        · exact CptT.noConfusion (ctyT_bot_inv hprop)
        · rcases List.mem_cons.mp hmem with rfl | hmem'
          · rcases ctyT_sort_inv hwit with hbot | htc
            · exact CptT.noConfusion hbot
            · cases htc
          · rcases List.mem_singleton.mp hmem' with rfl
            rcases ctyT_pi_inv hprop with hbot | ⟨_, hlam, _⟩
            · exact CptT.noConfusion hbot
            · exact CptT.noConfusion hlam

/-! #### Refutation 3: rigid non-proof constants of Π-type have `.spine` compacts -/

/-- A `.spine` compact is never typed at any compact of `.pi A B` (even under `CTyT`). -/
theorem not_ctyT_spine_of_approxT_pi {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat}
    {r : Nat} {args : List CptT} {a : CptT} (h : ApproxT E ρ (.pi A B) a) :
    ¬ CTyT E (.spine r args) a := by
  intro hty
  rcases approxT_pi_inv h with rfl | ⟨a', f, rfl, _, _⟩
  · exact CptT.noConfusion (ctyT_bot_inv hty)
  · rcases ctyT_pi_inv hty with hbot | ⟨_, hlam, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion hlam

theorem not_elT_spine_pi (E : ResolvedEnv) (ρ : EnvT) (A B : Expr Nat) (r : Nat) (args : List CptT) :
    ¬ ElT E ρ (.pi A B) (.spine r args) :=
  fun ⟨a, hAa, hty⟩ => not_ctyT_spine_of_approxT_pi hAa (ctyT_of_ctyS a (.spine r args) hty)

/-- Any rigid non-proof constant `r` does not satisfy `SemEqT` with its η-expansion in `ApproxT`:
    `.const r ls` has compact `.spine r []`, whereas `.lam A ...` has only `.bot` and `.lam` compacts. -/
theorem not_semEqT_eta_rigidConst {E : ResolvedEnv} (ρ : EnvT) {r : Nat} (ls : List Level)
    (A : Expr Nat) (hrigid : RigidConst E r) (hnp : ¬ PropCtorT E r) :
    ¬ SemEqT E ρ (.lam A (.app (lift 0 1 (.const r ls)) (.bvar 0))) (.const r ls) := by
  intro hse
  have hsp : ApproxT E ρ (.const r ls) (.spine r []) := .const ρ r ls hrigid hnp
  have hlam : ApproxT E ρ (.lam A (.app (lift 0 1 (.const r ls)) (.bvar 0))) (.spine r []) :=
    (hse (.spine r [])).mpr hsp
  rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
  · exact CptT.noConfusion hbot
  · exact CptT.noConfusion heq

/-! #### Refutation 4: `EnvTypedAtT` / `EnvTypedFinAtT` omit `CtxEnvT` (`letBinding` + `ConvT.zetaLocal`) -/

/-- The non-polymorphic identity `λ (Y : Sort 1). Y` and its type `Sort 1 → Sort 1`. -/
def idSort1 : Expr Nat := .lam (.sort (.succ .zero)) (.bvar 0)
def idSort1Ty : Expr Nat := .pi (.sort (.succ .zero)) (.sort (.succ .zero))
def idSort1TySort : Level := .imax (.succ (.succ .zero)) (.succ (.succ .zero))

/-- A 1-element `letBinding` context `[X := Sort 1 → Sort 1 : Sort (imax 2 2)]`. -/
def letSort1Ctx : LCtx := [.letBinding (.sort idSort1TySort) idSort1Ty]

/-- In `letSort1Ctx`, `idSort1 : .bvar 0` via `HasTyT.conv` and `ConvT.zetaLocal`. -/
def hasTyT_idSort1_bvar0 (E : ResolvedEnv) (n : Nat) : HasTyT E n letSort1Ctx idSort1 (.bvar 0) :=
  have hPi : HasTyT E n letSort1Ctx idSort1Ty (.sort idSort1TySort) :=
    .pi letSort1Ctx (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort _ _) (.sort _ _)
  have hid : HasTyT E n letSort1Ctx idSort1 idSort1Ty :=
    .lam letSort1Ctx (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.sort (.succ .zero))
      (.sort _ _) (.bvar _ 0 _ rfl)
  have hzl : ConvT E n letSort1Ctx (.bvar 0) idSort1Ty (.sort idSort1TySort) :=
    .zetaLocal letSort1Ctx 0 (.sort idSort1TySort) idSort1Ty rfl rfl hPi
  .conv letSort1Ctx idSort1 idSort1Ty (.bvar 0) idSort1TySort hid (.symm _ _ _ _ hzl)

/-- `EnvT.bot` satisfies `EnvTypedFinAtT` in every context `Γ` (even with `letBinding`s),
    because `EnvTypedFinAtT` inspects only `lookupType` and `EnvT.bot i u → u = .bot`. -/
theorem envTypedFinAtT_bot (M : CtxModelT E) (hbot : ∀ ρ e, M.Ap ρ e .bot) (Γ : LCtx) :
    EnvTypedFinAtT M Γ EnvT.bot := by
  intro i A _ us hus
  refine ⟨.bot, hbot EnvT.bot A, fun u hu => ?_⟩
  have h0 : u = .bot := hus u hu
  subst h0
  exact ctyS_bot .bot

theorem approxT_idSort1_polyIdOut0 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ idSort1 polyIdOut0 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  refine .lam hA ?_ ⟨([.prop], .prop), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .bvar (List.mem_singleton.mpr rfl)

/-- **Refutation 4 (`not_typingLemmaEnvFinT_letBinding`)**: even on the non-polymorphic 1-step
    term `idSort1 = λ (Y : Sort 1). Y`, `EnvTypedFinAtT` (and `EnvTypedAtT`) is refuted at
    `ρ = EnvT.bot` in `letSort1Ctx`, because `EnvTypedFinAtT` omits `CtxEnvT` (`letBinding`
    coherence) while `HasTyT.conv` + `ConvT.zetaLocal` types `idSort1` at `.bvar 0`. -/
theorem not_typingLemmaEnvFinT_letBinding (E : ResolvedEnv) :
    ¬ (∃ a, ApproxT E EnvT.bot (.bvar 0) a ∧ CTyT E polyIdOut0 a) := by
  rintro ⟨a, hba, hty⟩
  rcases approxT_bvar_inv hba with rfl | hbot
  · exact CptT.noConfusion (ctyT_bot_inv hty)
  · subst hbot
    exact CptT.noConfusion (ctyT_bot_inv hty)

/-- Direct refutation of `TypingLemmaEnvFinT (ctxModelT_approxT E) n` from the `letBinding`
    counterexample `hasTyT_idSort1_bvar0` alone (without using `cexPolyId`). -/
theorem not_typingLemmaEnvFinT_via_letBinding (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaEnvFinT (ctxModelT_approxT E) n := by
  intro hTL
  obtain ⟨a, hba, hty⟩ := hTL (hasTyT_idSort1_bvar0 E n)
    (envTypedFinAtT_bot (ctxModelT_approxT E) (fun ρ e => .bot ρ e) letSort1Ctx)
    [polyIdOut0] (fun u hu => by
      rcases List.mem_singleton.mp hu with rfl
      exact approxT_idSort1_polyIdOut0 E EnvT.bot)
  exact not_typingLemmaEnvFinT_letBinding E
    ⟨a, hba, ctyT_of_ctyS a polyIdOut0 (hty polyIdOut0 (List.mem_singleton.mpr rfl))⟩

/-! ### §3 — Exact restatement (`CTyCov`, `ElTCov`) and pointwise `relSubstAtT_cons_pointwise` -/

/-- **Covariant semantic typing** (`CTyCov`): combines `CTyS`'s universal `hcod` and existential
    `hcov` into the existential step-covering clause
    `∀ s ∈ f, s.2 = .bot ∨ ∃ t, ∃ (_ : t ∈ g), (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov E s.2 t.2`.
    In `RcicNativeTypedModelRelS` (`irrel_stepS`, `symmTm_stepS`, `transTm_stepS`), `CTyS` is
    only ever invoked on the existential covering step `t ∈ g`; dropping cross-step universal
    `hcod` eliminates Obstruction 1 while preserving `ctyCov_prop_bot` and `ctyCov_of_ctyS`. -/
def CTyCov (E : ResolvedEnv) : CptT → CptT → Prop
  | u, .bot => u = .bot
  | u, .prop => u = .bot ∨ IsPropCT E u
  | u, .sort => u = .bot ∨ TyCodeCT u
  | u, .pi a g => u = .bot ∨ ∃ f, u = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyCov E v a) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ (t : List CptT × CptT) (_ : t ∈ g),
        (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov E s.2 t.2)
  | u, .lam _ => u = .bot
  | u, .spine r' args' => u = .bot ∨ ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args'))
termination_by _ a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show t ∈ g from ‹_›)
       have h₂ := sizeOfT_snd_lt t
       omega)

theorem ctyCov_bot_inv {u : CptT} (h : CTyCov E u .bot) : u = .bot := by rw [CTyCov] at h; exact h
theorem ctyCov_prop_inv {u : CptT} (h : CTyCov E u .prop) : u = .bot ∨ IsPropCT E u := by
  rw [CTyCov] at h; exact h
theorem ctyCov_sort_inv {u : CptT} (h : CTyCov E u .sort) : u = .bot ∨ TyCodeCT u := by
  rw [CTyCov] at h; exact h
theorem ctyCov_lam_inv {u : CptT} {g : List (List CptT × CptT)} (h : CTyCov E u (.lam g)) :
    u = .bot := by
  rw [CTyCov] at h; exact h
theorem ctyCov_pi_inv {u a : CptT} {g : List (List CptT × CptT)} (h : CTyCov E u (.pi a g)) :
    u = .bot ∨ ∃ f, u = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyCov E v a) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ (t : List CptT × CptT) (_ : t ∈ g),
        (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov E s.2 t.2) := by
  rw [CTyCov] at h; exact h
theorem ctyCov_spine_inv {u : CptT} {r' : Nat} {args' : List CptT}
    (h : CTyCov E u (.spine r' args')) :
    u = .bot ∨ ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args')) := by
  rw [CTyCov] at h; exact h

theorem ctyCov_bot (a : CptT) : CTyCov E .bot a := by
  cases a <;> rw [CTyCov] <;> first | rfl | exact Or.inl rfl

/-- `CTyS` implies `CTyCov`. -/
theorem ctyCov_of_ctyS : ∀ (a u : CptT), CTyS E u a → CTyCov E u a
  | .bot, u, h => by rw [ctyS_bot_inv h]; exact ctyCov_bot _
  | .prop, u, h => by rw [CTyCov]; exact ctyS_prop_inv h
  | .sort, u, h => by rw [CTyCov]; exact ctyS_sort_inv h
  | .pi a g, u, h => by
      rcases ctyS_pi_inv h with rfl | ⟨f, rfl, hnp, hdom, hcod, hcov⟩
      · exact ctyCov_bot _
      · rw [CTyCov]
        refine Or.inr ⟨f, rfl, hnp, fun s hs v hv => ctyCov_of_ctyS a v (hdom s hs v hv),
          fun s hs => ?_⟩
        rcases hcov s hs with hbot | ⟨t, htg, hsub⟩
        · exact Or.inl hbot
        · exact Or.inr ⟨t, htg, hsub, ctyCov_of_ctyS t.2 s.2 (hcod s hs t htg hsub)⟩
  | .lam g, u, h => by rw [ctyS_lam_inv h]; exact ctyCov_bot _
  | .spine r' args', u, h => by rw [CTyCov]; exact ctyS_spine_inv h
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show t ∈ g from ‹_›)
       have h₂ := sizeOfT_snd_lt t
       omega)

/-- **§3.6 proof collapse for `CTyCov`**: every compact typed at a proposition code is `.bot`. -/
theorem ctyCov_prop_bot {a u : CptT} (hP : IsPropCT E a) (h : CTyCov E u a) : u = .bot := by
  cases a with
  | bot => exact ctyCov_bot_inv h
  | prop => cases hP
  | sort => cases hP
  | pi a g =>
      rcases ctyCov_pi_inv h with rfl | ⟨_, _, hnp, _⟩
      · rfl
      · exact (hnp hP).elim
  | lam g => exact ctyCov_lam_inv h
  | spine r' args' =>
      rcases ctyCov_spine_inv h with rfl | ⟨_, hnp⟩
      · rfl
      · exact (hnp hP).elim

/-- Step-list monotonicity for `CTyCov` on Π-codes: enlarging the codomain step list `g ⊆ g'`
    preserves `CTyCov` (unlike `CTyS`, where adding codomain steps can break universal `hcod`). -/
theorem ctyCov_pi_mono_steps {a u : CptT} {g g' : List (List CptT × CptT)}
    (hsub : ∀ t ∈ g, t ∈ g') (h : CTyCov E u (.pi a g)) : CTyCov E u (.pi a g') := by
  rcases ctyCov_pi_inv h with rfl | ⟨f, rfl, hnp, hdom, hcov⟩
  · exact ctyCov_bot _
  · have hnp' : ¬ IsPropCT E (.pi a g') := by
      intro hp'
      cases hp' with
      | pi hta hg' => exact hnp (.pi hta (fun t ht => hg' t (hsub t ht)))
    rw [CTyCov]
    refine Or.inr ⟨f, rfl, hnp', hdom, fun s hs => ?_⟩
    rcases hcov s hs with hbot | ⟨t, htg, hts, hty⟩
    · exact Or.inl hbot
    · exact Or.inr ⟨t, hsub t htg, hts, hty⟩

/-- Covariant type interpretation (`ElTCov`). -/
def ElTCov (E : ResolvedEnv) (ρ : EnvT) (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, ApproxT E ρ A a ∧ CTyCov E u a

theorem elTCov_of_elT {E : ResolvedEnv} {ρ : EnvT} {A : Expr Nat} {u : CptT}
    (h : ElT E ρ A u) : ElTCov E ρ A u :=
  let ⟨a, hAa, hty⟩ := h
  ⟨a, hAa, ctyCov_of_ctyS a u hty⟩

theorem elTCov_bot (E : ResolvedEnv) (ρ : EnvT) (A : Expr Nat) : ElTCov E ρ A .bot :=
  ⟨.bot, .bot ρ A, ctyCov_bot .bot⟩

/-- A `.spine` compact is never `CTyCov`-typed at any compact of `.pi A B`. -/
theorem not_ctyCov_spine_of_approxT_pi {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat}
    {r : Nat} {args : List CptT} {a : CptT} (h : ApproxT E ρ (.pi A B) a) :
    ¬ CTyCov E (.spine r args) a := by
  intro hty
  rcases approxT_pi_inv h with rfl | ⟨a', f, rfl, _, _⟩
  · exact CptT.noConfusion (ctyCov_bot_inv hty)
  · rcases ctyCov_pi_inv hty with hbot | ⟨_, hlam, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion hlam

theorem not_elTCov_spine_pi (E : ResolvedEnv) (ρ : EnvT) (A B : Expr Nat) (r : Nat)
    (args : List CptT) : ¬ ElTCov E ρ (.pi A B) (.spine r args) :=
  fun ⟨_, hAa, hty⟩ => not_ctyCov_spine_of_approxT_pi hAa hty

/-- Codomain compact of `X → X` at `X = .sort`: `Π (_ : Sort), Sort` with step `([.prop], .sort)`. -/
def polyIdTyCod0 : CptT := .pi .sort [([.prop], .sort)]

/-- Codomain compact of `X → X` at `X = polyIdDom1`: `Π (_ : polyIdDom1), polyIdDom1` with step
    `([polyIdWitness1], polyIdDom1)`. -/
def polyIdTyCod1 : CptT := .pi polyIdDom1 [([polyIdWitness1], polyIdDom1)]

/-- Combined Π-compact of `cexPolyIdTy` covering both steps of `polyIdCpt01`. -/
def polyIdTyCpt01 : CptT :=
  .pi .sort [([.sort], polyIdTyCod0), ([.sort, polyIdDom1], polyIdTyCod1)]

theorem approxT_polyIdTyCod0 (E : ResolvedEnv) (ρ : EnvT) {d : List CptT} (hd : CptT.sort ∈ d) :
    ApproxT E (EnvT.cons (demandT d) ρ) (.pi (.bvar 0) (.bvar 1)) polyIdTyCod0 := by
  refine .pi (.bvar hd) ?_ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .bvar hd

theorem approxT_polyIdTyCod1 (E : ResolvedEnv) (ρ : EnvT) {d : List CptT} (hd : polyIdDom1 ∈ d) :
    ApproxT E (EnvT.cons (demandT d) ρ) (.pi (.bvar 0) (.bvar 1)) polyIdTyCod1 := by
  refine .pi (.bvar hd) ?_ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_polyIdWitness1_polyIdDom1 E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .bvar hd

theorem approxT_cexPolyIdTy_cpt01 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ cexPolyIdTy polyIdTyCpt01 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  refine .pi hA ?_ ?_
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs'
    · rcases List.mem_singleton.mp hu with rfl
      exact ctyS_sort_sort E
    · rcases List.mem_singleton.mp hs' with rfl
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact ctyS_sort_sort E
      · rcases List.mem_singleton.mp hu' with rfl
        exact ctyS_polyIdDom1_sort E
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact approxT_polyIdTyCod0 E ρ (List.mem_singleton.mpr rfl)
    · rcases List.mem_singleton.mp hs' with rfl
      exact approxT_polyIdTyCod1 E ρ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

theorem ctyS_polyIdOut1_polyIdTyCod1 (E : ResolvedEnv) :
    CTyS E polyIdOut1 polyIdTyCod1 := by
  have hnp : ¬ IsPropCT E polyIdTyCod1 := by
    intro h
    cases h with
    | pi _ hg =>
        exact not_isPropCT_polyIdDom1 E
          (hg ([polyIdWitness1], polyIdDom1) (List.mem_singleton.mpr rfl))
  rw [polyIdTyCod1, CTyS]
  refine Or.inr ⟨[([polyIdWitness1], polyIdWitness1)], rfl, hnp, ?_, ?_, ?_⟩
  · intro s hs v hv
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hv with rfl
    exact ctyS_polyIdWitness1_polyIdDom1 E
  · intro s hs t ht _
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp ht with rfl
    exact ctyS_polyIdWitness1_polyIdDom1 E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact Or.inr ⟨([polyIdWitness1], polyIdDom1), List.mem_singleton.mpr rfl, fun v hv => hv⟩

theorem not_isPropCT_polyIdTyCpt01 (E : ResolvedEnv) : ¬ IsPropCT E polyIdTyCpt01 := by
  intro h
  cases h with
  | pi _ hg =>
      exact not_isPropCT_polyIdDom1 E
        (hg ([.sort], polyIdTyCod0) (List.mem_cons_self _ _))

/-- **Positive resolution of Obstruction 1a (`elTCov_polyId_cpt01`)**: the exact 2-step compact
    `polyIdCpt01` of `cexPolyId` that refuted `ElT` (`not_elT_polyId_cpt01`) IS in `ElTCov` of
    `cexPolyIdTy` at every environment `ρ`. -/
theorem ctyCov_polyIdCpt01_polyIdTyCpt01 (E : ResolvedEnv) :
    CTyCov E polyIdCpt01 polyIdTyCpt01 := by
  rw [polyIdTyCpt01, CTyCov]
  refine Or.inr ⟨[([.sort], polyIdOut0), ([.sort, polyIdDom1], polyIdOut1)], rfl,
    not_isPropCT_polyIdTyCpt01 E, ?_, ?_⟩
  · intro s hs v hv
    rcases List.mem_cons.mp hs with rfl | hs'
    · rcases List.mem_singleton.mp hv with rfl
      exact ctyCov_of_ctyS .sort .sort (ctyS_sort_sort E)
    · rcases List.mem_singleton.mp hs' with rfl
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact ctyCov_of_ctyS .sort .sort (ctyS_sort_sort E)
      · rcases List.mem_singleton.mp hv' with rfl
        exact ctyCov_of_ctyS .sort polyIdDom1 (ctyS_polyIdDom1_sort E)
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact Or.inr ⟨([.sort], polyIdTyCod0), List.mem_cons_self _ _, fun v hv => hv,
        ctyCov_of_ctyS polyIdTyCod0 polyIdOut0 (ctyS_polyIdWitness1_polyIdDom1 E)⟩
    · rcases List.mem_singleton.mp hs' with rfl
      exact Or.inr ⟨([.sort, polyIdDom1], polyIdTyCod1),
        List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), fun v hv => hv,
        ctyCov_of_ctyS polyIdTyCod1 polyIdOut1 (ctyS_polyIdOut1_polyIdTyCod1 E)⟩

theorem elTCov_polyId_cpt01 (E : ResolvedEnv) (ρ : EnvT) :
    ElTCov E ρ cexPolyIdTy polyIdCpt01 :=
  ⟨polyIdTyCpt01, approxT_cexPolyIdTy_cpt01 E ρ, ctyCov_polyIdCpt01_polyIdTyCpt01 E⟩

/-- **Positive resolution of Obstruction 1b (`joint_ctyCov_polyId_cpt0_cpt1`)**: the two 1-step
    compacts `polyIdCpt0` and `polyIdCpt1` that had no joint `CTyS` code (`not_joint_ctyS_polyId_cpt0_cpt1`)
    are jointly typed at `polyIdTyCpt01` under `CTyCov`. -/
theorem joint_ctyCov_polyId_cpt0_cpt1 (E : ResolvedEnv) (ρ : EnvT) :
    ∃ a, ApproxT E ρ cexPolyIdTy a ∧ CTyCov E polyIdCpt0 a ∧ CTyCov E polyIdCpt1 a := by
  refine ⟨polyIdTyCpt01, approxT_cexPolyIdTy_cpt01 E ρ, ?_, ?_⟩
  · rw [polyIdTyCpt01, CTyCov]
    refine Or.inr ⟨[([.sort], polyIdOut0)], rfl, not_isPropCT_polyIdTyCpt01 E, ?_, ?_⟩
    · intro s hs v hv
      rcases List.mem_singleton.mp hs with rfl
      rcases List.mem_singleton.mp hv with rfl
      exact ctyCov_of_ctyS .sort .sort (ctyS_sort_sort E)
    · intro s hs
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inr ⟨([.sort], polyIdTyCod0), List.mem_cons_self _ _, fun v hv => hv,
        ctyCov_of_ctyS polyIdTyCod0 polyIdOut0 (ctyS_polyIdWitness1_polyIdDom1 E)⟩
  · rw [polyIdTyCpt01, CTyCov]
    refine Or.inr ⟨[([.sort, polyIdDom1], polyIdOut1)], rfl, not_isPropCT_polyIdTyCpt01 E, ?_, ?_⟩
    · intro s hs v hv
      rcases List.mem_singleton.mp hs with rfl
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact ctyCov_of_ctyS .sort .sort (ctyS_sort_sort E)
      · rcases List.mem_singleton.mp hv' with rfl
        exact ctyCov_of_ctyS .sort polyIdDom1 (ctyS_polyIdDom1_sort E)
    · intro s hs
      rcases List.mem_singleton.mp hs with rfl
      exact Or.inr ⟨([.sort, polyIdDom1], polyIdTyCod1),
        List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), fun v hv => hv,
        ctyCov_of_ctyS polyIdTyCod1 polyIdOut1 (ctyS_polyIdOut1_polyIdTyCod1 E)⟩

/-! #### Pointwise `relSubstAtT_cons_pointwise` and `fundT_beta_pointwise` (resolving Obstruction 2) -/

/-- **Pointwise extension of `RelSubstAtT`** (`relSubstAtT_cons_pointwise`): in
    `RcicNativeTypedModelFund.relSubstAtT_cons`, the domain code `{a : CptT}` is only ever used
    pointwise for each `v ∈ d`.  Unbundling `{a : CptT}` to a per-element witness
    `∀ v ∈ d, ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ CTyS E v a` produces the exact same
    `RelSubstAtT` conclusion without requiring a single code `a` to jointly type all of `d`. -/
theorem relSubstAtT_cons_pointwise (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {Δ : LCtx} (hΔ : CtxWfT E n Δ) {ρ ρ' : EnvT}
    {σ σ' : SubstT} (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) (A : Expr Nat) (u : Level)
    (ihA : FundTyAt M R n Γ A (.sort u))
    (d : List CptT) (hdT : ∀ v ∈ d, ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ CTyS E v a)
    (hAc : ConvT E n Δ (substT σ A) (substT σ' A) (.sort u))
    (N N' : Expr Nat) (hN : HasTyT E n Δ N (substT σ A)) (hN' : HasTyT E n Δ N' (substT σ A))
    (hcN : ConvT E n Δ N N' (substT σ A))
    (hrel : ∀ v ∈ d, LRSCoreS R E n Δ N N' (substT σ A) v) :
    RelSubstAtT M R n Δ (EnvT.cons (demandT d) ρ) (EnvT.cons (demandT d) ρ')
      (SubstT.cons N σ) (SubstT.cons N' σ') (.assumption A :: Γ) := by
  have hN'ty : HasTyT E n Δ N' (substT σ' A) := .conv _ _ _ _ u hN' hAc
  have hrel' : ∀ v ∈ d, LRSCoreS R E n Δ N' N (substT σ' A) v := fun v hv => by
    obtain ⟨a, ha, hvT⟩ := hdT v hv
    obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha
    exact lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hAA' hvT
      (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA hvT (hrel v hv))
  have hrelD : ∀ v ∈ d, LRSCoreS R E n Δ N N (substT σ A) v := fun v hv => by
    obtain ⟨a, ha, hvT⟩ := hdT v hv
    obtain ⟨_, hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha
    exact lrSCoreS_trans_tm hL hNU hW hCAs hCAt hΔ hAA hvT (hrel v hv)
      (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA hvT (hrel v hv))
  have hrelD' : ∀ v ∈ d, LRSCoreS R E n Δ N' N' (substT σ' A) v := fun v hv => by
    obtain ⟨a, ha, hvT⟩ := hdT v hv
    obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha
    exact lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hAA' hvT
      (lrSCoreS_trans_tm hL hNU hW hCAs hCAt hΔ hAA hvT
        (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA hvT (hrel v hv)) (hrel v hv))
  obtain ⟨hT, hT', hc, hrelS, hletS⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i A' h => ?_, fun i v hv => ?_⟩
    · cases i with
      | zero =>
          simp only [lookupType, List.get?_cons_zero] at h
          injection h with h; subst h
          exact ⟨by rw [substT_cons_lift]; exact hN⟩
      | succ i =>
          rw [lookupType_cons_succ] at h
          cases hA₀ : lookupType Γ i with
          | none => rw [hA₀] at h; exact Option.noConfusion h
          | some A₀ =>
              rw [hA₀] at h; injection h with h; subst h
              obtain ⟨ht⟩ := hT.1 i A₀ hA₀
              exact ⟨by rw [substT_cons_lift]; exact ht⟩
    · cases i with
      | zero => simp [lookupValue] at hv
      | succ i =>
          rw [lookupValue_cons_succ] at hv
          cases hv₀ : lookupValue Γ i with
          | none => rw [hv₀] at hv; exact Option.noConfusion hv
          | some v₀ =>
              rw [hv₀] at hv; injection hv with hv; subst hv
              obtain ⟨A₀, hA₀, ⟨hc₀⟩⟩ := hT.2 i v₀ hv₀
              refine ⟨lift 0 1 A₀, by rw [lookupType_cons_succ, hA₀]; rfl, ⟨?_⟩⟩
              rw [substT_cons_lift, substT_cons_lift]; exact hc₀
  · refine ⟨fun i A' h => ?_, fun i v hv => ?_⟩
    · cases i with
      | zero =>
          simp only [lookupType, List.get?_cons_zero] at h
          injection h with h; subst h
          exact ⟨by rw [substT_cons_lift]; exact hN'ty⟩
      | succ i =>
          rw [lookupType_cons_succ] at h
          cases hA₀ : lookupType Γ i with
          | none => rw [hA₀] at h; exact Option.noConfusion h
          | some A₀ =>
              rw [hA₀] at h; injection h with h; subst h
              obtain ⟨ht⟩ := hT'.1 i A₀ hA₀
              exact ⟨by rw [substT_cons_lift]; exact ht⟩
    · cases i with
      | zero => simp [lookupValue] at hv
      | succ i =>
          rw [lookupValue_cons_succ] at hv
          cases hv₀ : lookupValue Γ i with
          | none => rw [hv₀] at hv; exact Option.noConfusion hv
          | some v₀ =>
              rw [hv₀] at hv; injection hv with hv; subst hv
              obtain ⟨A₀, hA₀, ⟨hc₀⟩⟩ := hT'.2 i v₀ hv₀
              refine ⟨lift 0 1 A₀, by rw [lookupType_cons_succ, hA₀]; rfl, ⟨?_⟩⟩
              rw [substT_cons_lift, substT_cons_lift]; exact hc₀
  · intro i A' h
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at h
        injection h with h; subst h
        exact ⟨by rw [substT_cons_lift]; exact hcN⟩
    | succ i =>
        rw [lookupType_cons_succ] at h
        cases hA₀ : lookupType Γ i with
        | none => rw [hA₀] at h; exact Option.noConfusion h
        | some A₀ =>
            rw [hA₀] at h; injection h with h; subst h
            obtain ⟨hc₀⟩ := hc i A₀ hA₀
            exact ⟨by rw [substT_cons_lift]; exact hc₀⟩
  · intro i A' h c hc'
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at h
        injection h with h; subst h
        have hd : c ∈ d := by rcases hc' with hc' | hc' <;> exact hc'
        simp only [SubstT.cons_zero]
        rw [substT_cons_lift, substT_cons_lift]
        exact ⟨hrel c hd, hrel' c hd, hrelD c hd, hrelD' c hd⟩
    | succ i =>
        rw [lookupType_cons_succ] at h
        cases hA₀ : lookupType Γ i with
        | none => rw [hA₀] at h; exact Option.noConfusion h
        | some A₀ =>
            rw [hA₀] at h; injection h with h; subst h
            simp only [SubstT.cons_succ]
            rw [substT_cons_lift, substT_cons_lift]
            exact hrelS i A₀ hA₀ c hc'
  · intro i v A' hv h c hc'
    cases i with
    | zero => simp [lookupValue] at hv
    | succ i =>
        rw [lookupValue_cons_succ] at hv
        rw [lookupType_cons_succ] at h
        cases hv₀ : lookupValue Γ i with
        | none => rw [hv₀] at hv; exact Option.noConfusion hv
        | some v₀ =>
            cases hA₀ : lookupType Γ i with
            | none => rw [hA₀] at h; exact Option.noConfusion h
            | some A₀ =>
                rw [hv₀] at hv; rw [hA₀] at h
                injection hv with hv; injection h with h
                subst hv; subst h
                simp only [SubstT.cons_succ]
                rw [substT_cons_lift, substT_cons_lift, substT_cons_lift, substT_cons_lift]
                refine hletS i v₀ A₀ hv₀ hA₀ c ?_
                rcases hc' with hc' | hc' | hc' | hc'
                · exact Or.inl hc'
                · exact Or.inr (Or.inl hc')
                · exact Or.inr (Or.inr (Or.inl (hM.lift0_elim hc')))
                · exact Or.inr (Or.inr (Or.inr (hM.lift0_elim hc')))

namespace TypingFin

/-- Unconditional substitution-factorization laws of `ApproxT` (#7704: `approxT_subst0_iff` +
    `approxT_factor` + `approxT_mono_update`), stated without any typing side condition on `arg`. -/
structure ModelSubstFactorT (M : CtxModelT E) : Prop where
  subst0_intro : ∀ {ρ : EnvT} {arg body : Expr Nat} {us : List CptT} {c : CptT},
    (∀ u ∈ us, M.Ap ρ arg u) → M.Ap (EnvT.cons (demandT us) ρ) body c →
    M.Ap ρ (instantiate0 arg body) c
  subst0_factor : ∀ {ρ : EnvT} {arg body : Expr Nat} {c : CptT},
    M.Ap ρ (instantiate0 arg body) c →
    ∃ us : List CptT, (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c

end TypingFin

open TypingFin

theorem modelBetaExpandTypedM_of_substFactor {M : CtxModelT E} (hF : ModelSubstFactorT M) :
    ModelBetaExpandTypedM M := by
  intro ρ A arg body c hT hc
  obtain ⟨us, hus, hb⟩ := hF.subst0_factor hc
  obtain ⟨a, hA, hty⟩ := hT us hus
  exact ⟨a, us, hA, hty, hus, hb⟩

/-- **`fundT_beta_pointwise`**: the β conversion case of the fundamental lemma (`FundConvAt`)
    using `relSubstAtT_cons_pointwise` + `ModelSubstFactorT.subst0_factor` + single-compact
    pointwise argument typing `TypingAt M ρ ρ' arg arg A` instead of `ModelBetaExpandT` /
    `ArgTypedFinAt` (eliminating multi-compact jointness across `us`). -/
theorem fundT_beta_pointwise (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hF : ModelSubstFactorT M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (harg : HasTyT E n Γ arg A)
    (ihA : FundTyAt M R n Γ A (.sort u)) (ihb : FundTyAt M R n (.assumption A :: Γ) body B)
    (iharg : FundTyAt M R n Γ arg A)
    (hTyArg : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      TypingAt M ρ ρ' arg arg A) :
    FundConvAt M R n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hcS
  obtain ⟨hargσ⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT
  obtain ⟨hargσ'⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT'
  obtain ⟨hargc⟩ := convT_substT_pointwise hW hcl hst hι hΓ harg hΔ hT hT' hcS
  have hargσ'A : HasTyT E n Δ (substT σ' arg) (substT σ A) := .conv _ _ _ _ u hargσ' (.symm _ _ _ _ hAc)
  have finish : ∀ (us : List CptT),
      (∀ v ∈ us, ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ CTyS E v a) →
      (∀ v ∈ us, M.Ap ρ arg v ∨ M.Ap ρ' arg v) →
      (M.Ap (EnvT.cons (demandT us) ρ) body c ∨ M.Ap (EnvT.cons (demandT us) ρ') body c) →
      LRSCoreS R E n Δ (substT σ (.app (.lam A body) arg)) (substT σ' (instantiate0 arg body))
        (substT σ (instantiate0 arg B)) c := by
    intro us hdT hus hb
    have hrel : ∀ v ∈ us, LRSCoreS R E n Δ (substT σ arg) (substT σ' arg) (substT σ A) v :=
      fun v hv => iharg hΔ hS v (hus v hv)
    have hS' := relSubstAtT_cons_pointwise hL hNU hW hcl hst hι hCAs hCAt hM hΓ hΔ hS A u ihA us
      hdT hAc (substT σ arg) (substT σ' arg) hargσ hargσ'A hargc hrel
    have hih := ihb hΔ hS' c hb
    simp only [substT]
    rw [substT_instantiate0, substT_instantiate0]
    rw [← instantiate0_substT_up, ← instantiate0_substT_up, ← instantiate0_substT_up] at hih
    exact lrSCoreS_expand hL (hL.beta _ _ _ _) c hih
  rcases hc with hc | hc
  · rcases hM.app_inv hc with rfl | ⟨g, s, rfl, hfg, hs, hau⟩ | ⟨r, args, v, rfl, hfg, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · rcases hM.lam_inv hfg with h0 | ⟨a, g', e, ha, _, hg⟩
      · exact CptT.noConfusion h0
      · injection e with eg; subst eg
        obtain ⟨hdT, hb⟩ := hg s hs
        exact finish s.1 (fun v hv => ⟨a, Or.inl ha, hdT v hv⟩)
          (fun v hv => Or.inl (hau v hv)) (Or.inl hb)
    · rcases hM.lam_inv hfg with h0 | ⟨_, _, e, _⟩
      · exact CptT.noConfusion h0
      · exact CptT.noConfusion e
  · obtain ⟨us, hus, hb⟩ := hF.subst0_factor hc
    exact finish us (fun v hv => hTyArg hS v (Or.inr (hus v hv)))
      (fun v hv => Or.inr (hus v hv)) (Or.inr hb)

/-! ### §4 — Simultaneous inductions (`HasTyT` + `ConvT`) -/

/-- Constructive splitting of `.bot` elements out of a finite list `us : List CptT` in `Prop`
    (no `DecidableEq`, no `Classical.choice`). -/
theorem split_bot_list {P : CptT → Prop} :
    ∀ (us : List CptT), (∀ u ∈ us, u = .bot ∨ P u) →
    ∃ us' : List CptT, (∀ u ∈ us', P u) ∧ (∀ u ∈ us, u = .bot ∨ u ∈ us')
  | [], _ =>
      ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | u :: us, h => by
      obtain ⟨us', hP, hmem⟩ := split_bot_list us (fun v hv => h v (List.mem_cons_of_mem _ hv))
      rcases h u (List.mem_cons_self _ _) with rfl | huP
      · exact ⟨us', hP, fun v hv => by
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact Or.inl rfl
          · exact hmem v hv'⟩
      · exact ⟨u :: us', fun v hv => by
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact huP
          · exact hP v hv',
          fun v hv => by
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact Or.inr (List.mem_cons_self _ _)
          · rcases hmem v hv' with rfl | hmem'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ hmem')⟩

/-! #### §4A — Simultaneous strong induction for `TypingLemmaEnvFinT` + `ConvSoundEnvFinT` -/

/-- Model-parametric let-binding value coherence (`CtxEnvT` for `M`). -/
def CtxEnvM (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  ∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v → ∀ c, M.Ap ρ (.bvar i) c ↔ M.Ap ρ v c

/-- Model conversion soundness under `EnvTypedFinAtT` and `CtxEnvM`. -/
def ConvSoundEnvFinT (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b A : Expr Nat}, ConvT E n Γ a b A →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ a c ↔ M.Ap ρ b c

/-- Finite-joint model typing lemma under `EnvTypedFinAtT` and `CtxEnvM`. -/
def TypingLemmaEnvFinCtxT (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ e u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- Simultaneous inductive hypotheses for all `HasTyT` and `ConvT` derivations of `sizeOf < k`. -/
def IHBelowTypingFin (M : CtxModelT E) (n : Nat) (k : Nat) : Prop :=
  (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), sizeOf d < k →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ e u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a) ∧
  (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), sizeOf d < k →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ a c ↔ M.Ap ρ b c)

/-- In `ConvT.beta`, the inductive hypothesis on `harg : HasTyT E n Γ arg A` supplies
    `ArgTypedFinAtM M ρ arg A`, which feeds directly into `ModelBetaExpandTypedM M` (#7704) to
    produce the typed β-expansion witness. -/
theorem beta_expand_of_ih_and_modelBetaExpandTypedM {M : CtxModelT E}
    (hβ : ModelBetaExpandTypedM M) {Γ : LCtx} {A body arg : Expr Nat}
    (harg : HasTyT E n Γ arg A) {k : Nat} (ih : IHBelowTypingFin M n k)
    (hlt : sizeOf harg < k) {ρ : EnvT} (hρ : EnvTypedFinAtT M Γ ρ) (hctx : CtxEnvM M Γ ρ)
    {c : CptT} (hc : M.Ap ρ (instantiate0 arg body) c) :
    ∃ (a : CptT) (us : List CptT), M.Ap ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c :=
  hβ (fun us hus => ih.1 harg hlt hρ hctx us hus) hc

/-- Per-constructor obligations for `TypingLemmaEnvFinCtxT` + `ConvSoundEnvFinT` not already
    closed by `CtxModelTLaws'` + `ModelIotaStepT` (`bvar`, `conv`, `refl`, `symm`, `trans`,
    `zetaLocal`, `iota`, `irr`, `tyConv` are discharged directly in `typingFin_step`). -/
structure TypingFinCases (M : CtxModelT E) (n : Nat) : Prop where
  sort : ∀ {Γ : LCtx} (l : Level) {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ (.sort l) u) →
    ∃ a, M.Ap ρ (.sort (.succ l)) a ∧ ∀ u ∈ us, CTyS E u a
  const : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ (.const r ls) u) →
    ∃ a, M.Ap ρ (instantiateLevels ls m.mtype) a ∧ ∀ u ∈ us, CTyS E u a
  pi : ∀ {Γ : LCtx} {A : Expr Nat} {u : Level} {B : Expr Nat} {v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)),
    IHBelowTypingFin M n (sizeOf (HasTyT.pi Γ A u B v hA hB)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ w ∈ us, M.Ap ρ (.pi A B) w) →
    ∃ a, M.Ap ρ (.sort (.imax u v)) a ∧ ∀ w ∈ us, CTyS E w a
  lam : ∀ {Γ : LCtx} {A : Expr Nat} {u : Level} {body B : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B),
    IHBelowTypingFin M n (sizeOf (HasTyT.lam Γ A u body B hA hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ w ∈ us, M.Ap ρ (.lam A body) w) →
    ∃ a, M.Ap ρ (.pi A B) a ∧ ∀ w ∈ us, CTyS E w a
  app : ∀ {Γ : LCtx} {f a A B : Expr Nat} (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A),
    IHBelowTypingFin M n (sizeOf (HasTyT.app Γ f a A B hf ha)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ w ∈ us, M.Ap ρ (.app f a) w) →
    ∃ a₀, M.Ap ρ (instantiate0 a B) a₀ ∧ ∀ w ∈ us, CTyS E w a₀
  letE : ∀ {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    IHBelowTypingFin M n (sizeOf (HasTyT.letE Γ A u value B body hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ w ∈ us, M.Ap ρ (.letE A value body) w) →
    ∃ a₀, M.Ap ρ (instantiate0 value B) a₀ ∧ ∀ w ∈ us, CTyS E w a₀
  lit : ∀ {Γ : LCtx} {t : Nat} {T : Expr Nat} (hexp : HasTyT E n Γ (natExpand t) T),
    IHBelowTypingFin M n (sizeOf (HasTyT.lit Γ t T hexp)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ us : List CptT, (∀ w ∈ us, M.Ap ρ (.lit t) w) →
    ∃ a₀, M.Ap ρ T a₀ ∧ ∀ w ∈ us, CTyS E w a₀
  beta : ∀ {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A),
    IHBelowTypingFin M n (sizeOf (ConvT.beta Γ A body arg B u hA hb harg)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.app (.lam A body) arg) c ↔ M.Ap ρ (instantiate0 arg body) c
  zeta : ∀ {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    IHBelowTypingFin M n (sizeOf (ConvT.zeta Γ A value body B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.letE A value body) c ↔ M.Ap ρ (instantiate0 value body) c
  delta : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (htr : transparent m.mclass = true)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)),
    IHBelowTypingFin M n (sizeOf (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.const r ls) c ↔ M.Ap ρ (instantiateLevels ls b) c
  litConv : ∀ {Γ : LCtx} {t : Nat} {exp T : Expr Nat} (h : LiteralExpansion t exp)
    (hexp : HasTyT E n Γ exp T),
    IHBelowTypingFin M n (sizeOf (ConvT.lit Γ t exp T h hexp)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.lit t) c ↔ M.Ap ρ exp c
  appConv : ∀ {Γ : LCtx} {f g a b A B : Expr Nat} (h1 : ConvT E n Γ f g (.pi A B))
    (h2 : ConvT E n Γ a b A),
    IHBelowTypingFin M n (sizeOf (ConvT.app Γ f g a b A B h1 h2)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.app f a) c ↔ M.Ap ρ (.app g b) c
  lamConv : ∀ {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hb : ConvT E n (.assumption A :: Γ) b b' B),
    IHBelowTypingFin M n (sizeOf (ConvT.lam Γ A A' b b' B u hA hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.lam A b) c ↔ M.Ap ρ (.lam A' b') c
  piConv : ∀ {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)),
    IHBelowTypingFin M n (sizeOf (ConvT.pi Γ A A' B B' u v hA hB)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.pi A B) c ↔ M.Ap ρ (.pi A' B') c
  letEConv : ∀ {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    IHBelowTypingFin M n (sizeOf (ConvT.letE Γ A A' v v' b b' B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.letE A v b) c ↔ M.Ap ρ (.letE A' v' b') c
  sorts : ∀ {Γ : LCtx} {l₁ l₂ : Level}, eqN l₁ l₂ →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.sort l₁) c ↔ M.Ap ρ (.sort l₂) c
  consts : ∀ {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    levelsBounded n ls' = true → eqNList ls ls' →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.const r ls) c ↔ M.Ap ρ (.const r ls') c
  eta : ∀ {Γ : LCtx} {f A B : Expr Nat} (h : HasTyT E n Γ f (.pi A B)),
    IHBelowTypingFin M n (sizeOf (ConvT.eta Γ f A B h)) →
    ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
    ∀ c, M.Ap ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) c ↔ M.Ap ρ f c

/-- **One step of the simultaneous induction (`typingFin_step`)**: discharges `bvar`, `conv`,
    `refl`, `symm`, `trans`, `zetaLocal`, `iota` (from `ModelIotaStepT`), `irr` (from the typing
    IH on `P`, `p`, `q` and proof collapse), and `tyConv`, and dispatches the remaining cases to
    `TypingFinCases`. -/
theorem typingFin_step {M : CtxModelT E} (hM : CtxModelTLaws M) (hIota : ModelIotaStepT E M)
    (hC : TypingFinCases M n) :
    (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A),
      IHBelowTypingFin M n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
      ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ e u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a) ∧
    (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A),
      IHBelowTypingFin M n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ →
      ∀ c, M.Ap ρ a c ↔ M.Ap ρ b c) := by
  refine ⟨?_, ?_⟩
  · intro Γ e A d ih ρ hρ hctx us hus
    cases d with
    | sort _ l => exact hC.sort l hρ hctx us hus
    | bvar _ i _ hA =>
        obtain ⟨us', hP, hmem⟩ := split_bot_list us (fun u hu => hM.bvar_inv (hus u hu))
        obtain ⟨a, hAa, hty'⟩ := hρ i A hA us' hP
        refine ⟨a, hAa, fun u hu => ?_⟩
        rcases hmem u hu with rfl | hu'
        · exact ctyS_bot a
        · exact hty' u hu'
    | const _ _ _ _ hres hlen hwf => exact hC.const hres hlen hwf hρ hctx us hus
    | pi _ _ _ _ _ hA hB => exact hC.pi hA hB ih hρ hctx us hus
    | lam _ _ _ _ _ hA hb => exact hC.lam hA hb ih hρ hctx us hus
    | app _ _ _ _ _ hf ha => exact hC.app hf ha ih hρ hctx us hus
    | letE _ _ _ _ _ _ hA hv hb => exact hC.letE hA hv hb ih hρ hctx us hus
    | lit _ _ _ hexp => exact hC.lit hexp ih hρ hctx us hus
    | conv _ _ _ _ _ h hc =>
        have hlt_h : sizeOf h < sizeOf (HasTyT.conv _ _ _ _ _ h hc) := by simp; omega
        have hlt_c : sizeOf hc < sizeOf (HasTyT.conv _ _ _ _ _ h hc) := by simp; omega
        obtain ⟨a, hAa, hty⟩ := ih.1 h hlt_h hρ hctx us hus
        have hAB := ih.2 hc hlt_c hρ hctx a
        exact ⟨a, hAB.mp hAa, hty⟩
  · intro Γ a b A d ih ρ hρ hctx c
    cases d with
    | refl _ _ _ _ => exact Iff.rfl
    | symm _ _ _ _ h =>
        have hlt : sizeOf h < sizeOf (ConvT.symm _ _ _ _ h) := by simp; omega
        exact (ih.2 h hlt hρ hctx c).symm
    | trans _ _ _ _ _ h1 h2 =>
        have hlt1 : sizeOf h1 < sizeOf (ConvT.trans _ _ _ _ _ h1 h2) := by simp; omega
        have hlt2 : sizeOf h2 < sizeOf (ConvT.trans _ _ _ _ _ h1 h2) := by simp; omega
        exact (ih.2 h1 hlt1 hρ hctx c).trans (ih.2 h2 hlt2 hρ hctx c)
    | beta _ _ _ _ _ _ hA hb harg => exact hC.beta hA hb harg ih hρ hctx c
    | zeta _ _ _ _ _ _ hA hv hb => exact hC.zeta hA hv hb ih hρ hctx c
    | zetaLocal _ i _ _ hval _ _ => exact hctx i b hval c
    | delta _ _ _ _ _ hres hbody htr hlen hwf hb =>
        exact hC.delta hres hbody htr hlen hwf hb ih hρ hctx c
    | iota _ _ _ _ h _ _ => exact hIota h ρ c
    | lit _ _ _ _ h hexp => exact hC.litConv h hexp ih hρ hctx c
    | app _ _ _ _ _ _ _ h1 h2 => exact hC.appConv h1 h2 ih hρ hctx c
    | lam _ _ _ _ _ _ _ hA hb => exact hC.lamConv hA hb ih hρ hctx c
    | pi _ _ _ _ _ _ _ hA hB => exact hC.piConv hA hB ih hρ hctx c
    | letE _ _ _ _ _ _ _ _ _ hA hv hb => exact hC.letEConv hA hv hb ih hρ hctx c
    | sorts _ _ _ h => exact hC.sorts h hρ hctx c
    | consts _ _ _ _ _ hres hlen hwf hwf' h =>
        exact hC.consts hres hlen hwf hwf' h hρ hctx c
    | eta _ _ _ _ h => exact hC.eta h ih hρ hctx c
    | irr _ _ _ _ hP hp hq =>
        have hltP : sizeOf hP < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        have hltp : sizeOf hp < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        have hltq : sizeOf hq < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        have collapse : ∀ {x : Expr Nat} (hx : HasTyT E n Γ x A),
            sizeOf hx < sizeOf (ConvT.irr _ _ _ _ hP hp hq) → M.Ap ρ x c → c = .bot := by
          intro x hx hltx hxc
          obtain ⟨a₀, hPa, hca⟩ := ih.1 hx hltx hρ hctx [c] (fun u hu => by
            rcases List.mem_singleton.mp hu with rfl; exact hxc)
          obtain ⟨s, hSs, has⟩ := ih.1 hP hltP hρ hctx [a₀] (fun u hu => by
            rcases List.mem_singleton.mp hu with rfl; exact hPa)
          have hca' : CTyS E c a₀ := hca c (List.mem_singleton.mpr rfl)
          have has' : CTyS E a₀ s := has a₀ (List.mem_singleton.mpr rfl)
          have haProp : IsPropCT E a₀ := by
            rcases hM.sort_inv hSs with rfl | hs0
            · rw [ctyS_bot_inv has']; exact .bot
            · rw [sortCode_zero] at hs0; subst hs0
              rcases ctyS_prop_inv has' with rfl | hP'
              · exact .bot
              · exact hP'
          exact ctyS_prop_bot haProp hca'
        constructor
        · intro hpc
          rw [collapse hp hltp hpc]
          exact hM.bot ρ b
        · intro hqc
          rw [collapse hq hltq hqc]
          exact hM.bot ρ a
    | tyConv _ _ _ _ _ _ h hA =>
        have hlt : sizeOf h < sizeOf (ConvT.tyConv _ _ _ _ _ _ h hA) := by simp; omega
        exact ih.2 h hlt hρ hctx c

/-- **Simultaneous strong induction (`typingFin_strong`)** on `sizeOf` of `HasTyT` and `ConvT`. -/
theorem typingFin_strong {M : CtxModelT E} (hM : CtxModelTLaws M) (hIota : ModelIotaStepT E M)
    (hC : TypingFinCases M n) : ∀ k : Nat, IHBelowTypingFin M n k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro _ _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
      · intro _ _ _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
      obtain ⟨stepTy, stepConv⟩ := typingFin_step hM hIota hC
      refine ⟨?_, ?_⟩
      · intro Γ e A d hd ρ hρ hctx us hus
        by_cases hk : sizeOf d < k
        · exact ih.1 d hk hρ hctx us hus
        · have hk' : sizeOf d = k := by omega
          exact stepTy d (hk' ▸ ih) hρ hctx us hus
      · intro Γ a b A d hd ρ hρ hctx c
        by_cases hk : sizeOf d < k
        · exact ih.2 d hk hρ hctx c
        · have hk' : sizeOf d = k := by omega
          exact stepConv d (hk' ▸ ih) hρ hctx c

/-- **Simultaneous typing lemma and conversion soundness (`typingLemmaEnvFin_and_convSound_of_cases`)**. -/
theorem typingLemmaEnvFin_and_convSound_of_cases {M : CtxModelT E} (hM : CtxModelTLaws M)
    (hIota : ModelIotaStepT E M) (hC : TypingFinCases M n) :
    TypingLemmaEnvFinCtxT M n ∧ ConvSoundEnvFinT M n := by
  refine ⟨?_, ?_⟩
  · intro Γ e A d ρ hρ hctx us hus
    exact (typingFin_strong hM hIota hC (sizeOf d + 1)).1 d (Nat.lt_succ_self _) hρ hctx us hus
  · intro Γ a b A d ρ hρ hctx c
    exact (typingFin_strong hM hIota hC (sizeOf d + 1)).2 d (Nat.lt_succ_self _) hρ hctx c

/-- When every `EnvTypedFinAtT M Γ ρ` satisfies `CtxEnvM M Γ ρ`, `TypingLemmaEnvFinCtxT M n`
    specializes directly to the handoff §2.3 `TypingLemmaEnvFinT M n`. -/
theorem typingLemmaEnvFinT_of_cases {M : CtxModelT E} (hM : CtxModelTLaws M)
    (hIota : ModelIotaStepT E M) (hC : TypingFinCases M n)
    (hCtx : ∀ {Γ : LCtx} {ρ : EnvT}, EnvTypedFinAtT M Γ ρ → CtxEnvM M Γ ρ) :
    TypingLemmaEnvFinT M n ∧ ConvSoundEnvFinT M n := by
  obtain ⟨hTy, hConv⟩ := typingLemmaEnvFin_and_convSound_of_cases hM hIota hC
  refine ⟨?_, hConv⟩
  intro Γ e A d ρ hρ us hus
  exact hTy d hρ (hCtx hρ) us hus

/-- Non-vacuity witness for `TypingLemmaEnvFinT` + `ConvSoundEnvFinT`: the `.bot`-only model
    `ctxModelT_botOnly E` satisfies `CtxModelTLaws'`, `ModelSubstFactorT`, `ModelBetaExpandTypedM`,
    `ModelIotaStepT`, `TypingFinCases`, `TypingLemmaEnvFinT`, and `ConvSoundEnvFinT`. -/
def ctxModelT_botOnly (E : ResolvedEnv) : CtxModelT E := ⟨fun _ _ c => c = .bot⟩

theorem ctxModelTLaws'_botOnly (E : ResolvedEnv) : CtxModelTLaws' (ctxModelT_botOnly E) where
  bot := fun _ _ => rfl
  bvar_inv := fun h => Or.inl h
  sort_inv := fun h => Or.inl h
  pi_inv := fun h => Or.inl h
  lam_inv := fun h => Or.inl h
  app_inv := fun h => Or.inl h
  letE_inv := fun h => h
  lift0_elim := fun h => h
  lift0_intro := fun h => h

theorem modelSubstFactorT_botOnly (E : ResolvedEnv) : ModelSubstFactorT (ctxModelT_botOnly E) where
  subst0_intro := fun _ h => h
  subst0_factor := fun h => ⟨[], fun _ hm => (List.not_mem_nil _ hm).elim, h⟩

theorem modelBetaExpandTypedM_botOnly (E : ResolvedEnv) :
    ModelBetaExpandTypedM (ctxModelT_botOnly E) :=
  modelBetaExpandTypedM_of_substFactor (modelSubstFactorT_botOnly E)

theorem modelIotaStepT_botOnly (E : ResolvedEnv) : ModelIotaStepT E (ctxModelT_botOnly E) :=
  fun _ _ _ => Iff.rfl

theorem typingFinCases_botOnly (E : ResolvedEnv) (n : Nat) :
    TypingFinCases (ctxModelT_botOnly E) n where
  sort := by intro _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  const := by intro _ _ _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  pi := by intro _ _ _ _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  lam := by intro _ _ _ _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  app := by intro _ _ _ _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  letE := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  lit := by intro _ _ _ _ _ _ _ _ us hus; exact ⟨.bot, rfl, fun u hu => by rw [hus u hu]; exact ctyS_bot .bot⟩
  beta := by intros; exact Iff.rfl
  zeta := by intros; exact Iff.rfl
  delta := by intros; exact Iff.rfl
  litConv := by intros; exact Iff.rfl
  appConv := by intros; exact Iff.rfl
  lamConv := by intros; exact Iff.rfl
  piConv := by intros; exact Iff.rfl
  letEConv := by intros; exact Iff.rfl
  sorts := by intros; exact Iff.rfl
  consts := by intros; exact Iff.rfl
  eta := by intros; exact Iff.rfl

theorem typingLemmaEnvFinT_botOnly (E : ResolvedEnv) (n : Nat) :
    TypingLemmaEnvFinT (ctxModelT_botOnly E) n ∧ ConvSoundEnvFinT (ctxModelT_botOnly E) n :=
  typingLemmaEnvFinT_of_cases (ctxModelTLaws'_botOnly E).toCtxModelTLaws
    (modelIotaStepT_botOnly E) (typingFinCases_botOnly E n) (fun _ _ _ _ _ => Iff.rfl)

/-! #### §4B — Concrete `ApproxT` simultaneous induction for `TypingLemmaEnvCovT` + `ConvSoundEnvCovT` -/

/-- Covariant environment typing on `ApproxT E`: every variable's compacts are in `ElTCov` of its
    context type, and let-bound variables satisfy `CtxEnvT E Γ ρ`. -/
def EnvTypedCovAtT (E : ResolvedEnv) (Γ : LCtx) (ρ : EnvT) : Prop :=
  (∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ∀ u, ρ i u → ElTCov E ρ A u) ∧
  CtxEnvT E Γ ρ

/-- **Covariant model typing lemma on `ApproxT E`**: every compact of a well-typed term is in
    `ElTCov` of its type at any `EnvTypedCovAtT` environment. -/
def TypingLemmaEnvCovT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → ∀ u, ApproxT E ρ e u → ElTCov E ρ A u

/-- **Covariant model conversion soundness on `ApproxT E`**: every `ConvT` equates its endpoints
    under `SemEqT E ρ` at any `EnvTypedCovAtT` environment. -/
def ConvSoundEnvCovT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b A : Expr Nat}, ConvT E n Γ a b A →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ a b

theorem envTypedCovAtT_nil (E : ResolvedEnv) (ρ : EnvT) : EnvTypedCovAtT E [] ρ :=
  ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩

/-- Extending an `EnvTypedCovAtT` environment across `.assumption A :: Γ` by `demandT d` where
    `∀ v ∈ d, CTyCov E v a` for a compact `a` of `A`. -/
theorem envTypedCovAtT_cons_assumption {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} {A : Expr Nat}
    {a : CptT} {d : List CptT} (hρ : EnvTypedCovAtT E Γ ρ) (hAa : ApproxT E ρ A a)
    (hd : ∀ v ∈ d, CTyCov E v a) :
    EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT d) ρ) := by
  refine ⟨fun i A' hA' u hu => ?_, fun i v hv c => ?_⟩
  · cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at hA'
        injection hA' with hA'; subst hA'
        exact ⟨a, (approxT_cons_lift0_iff E ρ (demandT d) A a).mpr hAa, hd u hu⟩
    | succ j =>
        rw [lookupType_cons_succ] at hA'
        cases hA₀ : lookupType Γ j with
        | none => rw [hA₀] at hA'; exact Option.noConfusion hA'
        | some A₀ =>
            rw [hA₀] at hA'; injection hA' with hA'; subst hA'
            obtain ⟨a₀, hA₀a, hty₀⟩ := hρ.1 j A₀ hA₀ u hu
            exact ⟨a₀, (approxT_cons_lift0_iff E ρ (demandT d) A₀ a₀).mpr hA₀a, hty₀⟩
  · cases i with
    | zero => simp [lookupValue] at hv
    | succ j =>
        rw [lookupValue_cons_succ] at hv
        cases hv₀ : lookupValue Γ j with
        | none => rw [hv₀] at hv; exact Option.noConfusion hv
        | some v₀ =>
            rw [hv₀] at hv; injection hv with hv; subst hv
            rw [approxT_cons_lift0_iff]
            have ih := hρ.2 j v₀ hv₀ c
            rw [approxT_bvar_iff] at ih ⊢
            exact ih

theorem tyCodeCT_of_elTCov_sort {E : ResolvedEnv} {ρ : EnvT} {u : Level} {a : CptT}
    (h : ElTCov E ρ (.sort u) a) : TyCodeCT a := by
  obtain ⟨s, hUs, hty⟩ := h
  rcases approxT_sort_inv hUs with rfl | rfl
  · rw [ctyCov_bot_inv hty]; exact .bot
  · rcases sortCode_prop_or_sort u with hp | hs
    · rw [hp] at hty
      rcases ctyCov_prop_inv hty with rfl | hP
      · exact .bot
      · exact tyCodeCT_of_isPropCT hP
    · rw [hs] at hty
      rcases ctyCov_sort_inv hty with rfl | hT
      · exact .bot
      · exact hT

theorem isPropCT_of_elTCov_sort_prop {E : ResolvedEnv} {ρ : EnvT} {v : Level} {a : CptT}
    (hv : sortCode v = .prop) (h : ElTCov E ρ (.sort v) a) : IsPropCT E a := by
  obtain ⟨s, hVs, hty⟩ := h
  rcases approxT_sort_inv hVs with rfl | rfl
  · rw [ctyCov_bot_inv hty]; exact .bot
  · rw [hv] at hty
    rcases ctyCov_prop_inv hty with rfl | hP
    · exact .bot
    · exact hP

theorem eqN_zero_of_imax_eqN_zero {u v : Level} (h : eqN (.imax u v) .zero) : eqN v .zero := by
  intro val
  have himax := h val
  simp only [eval] at himax ⊢
  cases hv : eval val v with
  | none => rw [hv] at himax; exact Option.noConfusion himax
  | some y =>
      rw [hv] at himax
      simp only [Option.bind] at himax
      split at himax
      · next hy => subst hy; rfl
      · next hy =>
          cases hu : eval val u with
          | none => rw [hu] at himax; exact Option.noConfusion himax
          | some x =>
              rw [hu] at himax
              simp only [Option.map] at himax
              injection himax with hmax
              omega

theorem sortCode_v_prop_of_imax_prop {u v : Level} (h : sortCode (.imax u v) = .prop) :
    sortCode v = .prop :=
  (sortCode_eq_prop_iff v).mpr (eqN_zero_of_imax_eqN_zero ((sortCode_eq_prop_iff (.imax u v)).mp h))

/-- Constructive finite-list codomain step synthesis in `Prop` (for `HasTyT.lam` under `ElTCov`,
    without `Classical.choice`). -/
theorem exists_cod_steps_of_lam_steps {E : ResolvedEnv} {ρ : EnvT} {B : Expr Nat} :
    ∀ (g : List (List CptT × CptT)),
      (∀ s ∈ g, ElTCov E (EnvT.cons (demandT s.1) ρ) B s.2) →
      ∃ f : List (List CptT × CptT),
        (∀ t ∈ f, (∃ s ∈ g, t.1 = s.1) ∧ ApproxT E (EnvT.cons (demandT t.1) ρ) B t.2) ∧
        (∀ s ∈ g, ∃ t ∈ f, t.1 = s.1 ∧ CTyCov E s.2 t.2)
  | [], _ =>
      ⟨[], ⟨fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩⟩
  | s :: g, h => by
      obtain ⟨b_s, hBs, hty_s⟩ := h s (List.mem_cons_self _ _)
      obtain ⟨f', hf'1, hf'2⟩ :=
        exists_cod_steps_of_lam_steps g (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
      refine ⟨(s.1, b_s) :: f', ⟨?_, ?_⟩⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact ⟨⟨s, List.mem_cons_self _ _, rfl⟩, hBs⟩
        · obtain ⟨⟨s', hs', heq⟩, hBt⟩ := hf'1 t ht'
          exact ⟨⟨s', List.mem_cons_of_mem _ hs', heq⟩, hBt⟩
      · intro s' hs'
        rcases List.mem_cons.mp hs' with rfl | hs''
        · exact ⟨(s'.1, b_s), List.mem_cons_self _ _, rfl, hty_s⟩
        · obtain ⟨t, htf', heq, hty'⟩ := hf'2 s' hs''
          exact ⟨t, List.mem_cons_of_mem _ htf', heq, hty'⟩

/-- **`HasTyT.sort` on `ApproxT E` (`covTyping_sort`)**: unconditional. -/
theorem covTyping_sort (E : ResolvedEnv) (ρ : EnvT) (l : Level) {u : CptT}
    (hu : ApproxT E ρ (.sort l) u) : ElTCov E ρ (.sort (.succ l)) u := by
  have hsort : ApproxT E ρ (.sort (.succ l)) .sort := by
    have := approxT_sort_code E ρ (.succ l)
    rwa [sortCode_succ] at this
  refine ⟨.sort, hsort, ?_⟩
  rcases approxT_sort_inv hu with rfl | rfl
  · exact ctyCov_bot .sort
  · rw [CTyCov]
    rcases sortCode_prop_or_sort l with hp | hs
    · rw [hp]; exact Or.inr .prop
    · rw [hs]; exact Or.inr .sort

/-- **`HasTyT.bvar` on `ApproxT E` (`covTyping_bvar`)**: unconditional. -/
theorem covTyping_bvar {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    {i : Nat} {A : Expr Nat} (hA : lookupType Γ i = some A) {u : CptT}
    (hu : ApproxT E ρ (.bvar i) u) : ElTCov E ρ A u := by
  rcases approxT_bvar_inv hu with rfl | hmem
  · exact elTCov_bot E ρ A
  · exact hρ.1 i A hA u hmem

/-- **`HasTyT.pi` on `ApproxT E` (`covTyping_pi`)**: closes unconditionally from the inductive
    hypotheses on `A` and `B`. -/
theorem covTyping_pi {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    {A : Expr Nat} {u : Level} {B : Expr Nat} {v : Level}
    (ihA : ∀ {ρ' : EnvT}, EnvTypedCovAtT E Γ ρ' → ∀ c, ApproxT E ρ' A c → ElTCov E ρ' (.sort u) c)
    (ihB : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.assumption A :: Γ) ρ' →
      ∀ c, ApproxT E ρ' B c → ElTCov E ρ' (.sort v) c)
    {c : CptT} (hc : ApproxT E ρ (.pi A B) c) :
    ElTCov E ρ (.sort (.imax u v)) c := by
  rcases approxT_pi_inv hc with rfl | ⟨a, f, rfl, hAa, hf⟩
  · exact elTCov_bot E ρ _
  · refine ⟨sortCode (.imax u v), approxT_sort_code E ρ (.imax u v), ?_⟩
    have hta : TyCodeCT a := tyCodeCT_of_elTCov_sort (ihA hρ a hAa)
    have hEnvS : ∀ s ∈ f, EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
      fun s hs => envTypedCovAtT_cons_assumption hρ hAa
        (fun w hw => ctyCov_of_ctyS a w ((hf s hs).1 w hw))
    rcases sortCode_prop_or_sort (.imax u v) with hp | hs
    · rw [hp, CTyCov]
      have hvP : sortCode v = .prop := sortCode_v_prop_of_imax_prop hp
      exact Or.inr (.pi hta (fun s hs =>
        isPropCT_of_elTCov_sort_prop hvP (ihB (hEnvS s hs) s.2 (hf s hs).2)))
    · rw [hs, CTyCov]
      exact Or.inr (.pi hta (fun s hs =>
        tyCodeCT_of_elTCov_sort (ihB (hEnvS s hs) s.2 (hf s hs).2)))

/-- **`HasTyT.lam` on `ApproxT E` (`covTyping_lam`)**: closes unconditionally from the inductive
    hypothesis on `body` (by `exists_cod_steps_of_lam_steps`, because `CTyCov` is covariant). -/
theorem covTyping_lam {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    {A body B : Expr Nat}
    (ihb : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.assumption A :: Γ) ρ' →
      ∀ c, ApproxT E ρ' body c → ElTCov E ρ' B c)
    {c : CptT} (hc : ApproxT E ρ (.lam A body) c) :
    ElTCov E ρ (.pi A B) c := by
  rcases approxT_lam_inv hc with rfl | ⟨a, g, rfl, hAa, ⟨s₀, hs₀, hne₀⟩, hg⟩
  · exact elTCov_bot E ρ _
  · have hEnvS : ∀ s ∈ g, EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
      fun s hs => envTypedCovAtT_cons_assumption hρ hAa
        (fun w hw => ctyCov_of_ctyS a w ((hg s hs).1 w hw))
    obtain ⟨f, ⟨hf1, hf2⟩⟩ := exists_cod_steps_of_lam_steps g
      (fun s hs => ihb (hEnvS s hs) s.2 (hg s hs).2)
    have hPi : ApproxT E ρ (.pi A B) (.pi a f) := by
      refine .pi hAa (fun t ht w hw => ?_) (fun t ht => (hf1 t ht).2)
      obtain ⟨⟨s, hs, heq⟩, _⟩ := hf1 t ht
      rw [heq] at hw
      exact (hg s hs).1 w hw
    have hnp : ¬ IsPropCT E (.pi a f) := by
      intro hp
      cases hp with
      | pi _ htf =>
          obtain ⟨t₀, ht₀f, _, hty₀⟩ := hf2 s₀ hs₀
          exact hne₀ (ctyCov_prop_bot (htf t₀ ht₀f) hty₀)
    refine ⟨.pi a f, hPi, ?_⟩
    rw [CTyCov]
    refine Or.inr ⟨g, rfl, hnp, fun s hs w hw => ctyCov_of_ctyS a w ((hg s hs).1 w hw),
      fun s hs => ?_⟩
    obtain ⟨t, htf, heq, hty⟩ := hf2 s hs
    exact Or.inr ⟨t, htf, fun w hw => by rw [← heq]; exact hw, hty⟩

/-- **`HasTyT.lit` on `ApproxT E` (`covTyping_lit`)**: closes unconditionally from the inductive
    hypothesis on `natExpand t`. -/
theorem covTyping_lit {E : ResolvedEnv} {ρ : EnvT} {t : Nat} {T : Expr Nat}
    (ihexp : ∀ c, ApproxT E ρ (natExpand t) c → ElTCov E ρ T c)
    {c : CptT} (hc : ApproxT E ρ (.lit t) c) : ElTCov E ρ T c := by
  cases hc with
  | bot => exact elTCov_bot E ρ T
  | lit h => exact ihexp c h

/-- **`HasTyT.conv` on `ApproxT E` (`covTyping_conv`)**: closes unconditionally from the typing IH
    on `e : A` and conversion soundness IH on `A ≡ B`. -/
theorem covTyping_conv {E : ResolvedEnv} {ρ : EnvT} {e A B : Expr Nat}
    (ih : ∀ c, ApproxT E ρ e c → ElTCov E ρ A c)
    (ihc : SemEqT E ρ A B) {c : CptT} (hc : ApproxT E ρ e c) : ElTCov E ρ B c := by
  obtain ⟨a, hAa, hty⟩ := ih c hc
  exact ⟨a, (ihc a).mp hAa, hty⟩

/-- **`ConvT.sorts` on `ApproxT E` (`covConv_sorts`)**: unconditional. -/
theorem covConv_sorts (E : ResolvedEnv) (ρ : EnvT) {l₁ l₂ : Level} (h : eqN l₁ l₂) :
    SemEqT E ρ (.sort l₁) (.sort l₂) := by
  have hsc : sortCode l₁ = sortCode l₂ := by
    have heq0 : eqN l₁ .zero ↔ eqN l₂ .zero :=
      ⟨fun h1 val => (h val).symm.trans (h1 val), fun h2 val => (h val).trans (h2 val)⟩
    rcases sortCode_prop_or_sort l₁ with hp | hs
    · rw [hp]
      exact ((sortCode_eq_prop_iff l₂).mpr (heq0.mp ((sortCode_eq_prop_iff l₁).mp hp))).symm
    · rw [hs]
      exact ((sortCode_eq_sort_iff l₂).mpr (fun h2 =>
        (sortCode_eq_sort_iff l₁).mp hs (heq0.mpr h2))).symm
  intro c
  constructor <;> intro hc <;> (
    rcases approxT_sort_inv hc with rfl | rfl
    · exact .bot _ _
    · first
      | (rw [hsc]; exact .sort ρ l₂)
      | (rw [← hsc]; exact .sort ρ l₁))

/-- **`ConvT.lit` on `ApproxT E` (`covConv_lit`)**: unconditional. -/
theorem covConv_lit (E : ResolvedEnv) (ρ : EnvT) {t : Nat} {exp : Expr Nat}
    (h : LiteralExpansion t exp) : SemEqT E ρ (.lit t) exp := by
  cases h
  intro c
  constructor
  · intro hc
    cases hc with
    | bot => exact .bot _ _
    | lit h => exact h
  · intro hc
    exact .lit hc

/-- **`ConvT.irr` on `ApproxT E` (`covConv_irr`)**: closes unconditionally from the covariant
    typing IHs on `P`, `p`, and `q` via `ctyCov_prop_bot`. -/
theorem covConv_irr {E : ResolvedEnv} {ρ : EnvT} {P p q : Expr Nat}
    (ihP : ∀ c, ApproxT E ρ P c → ElTCov E ρ (.sort .zero) c)
    (ihp : ∀ c, ApproxT E ρ p c → ElTCov E ρ P c)
    (ihq : ∀ c, ApproxT E ρ q c → ElTCov E ρ P c) :
    SemEqT E ρ p q := by
  have collapse : ∀ {x : Expr Nat}, (∀ c, ApproxT E ρ x c → ElTCov E ρ P c) →
      ∀ {c : CptT}, ApproxT E ρ x c → c = .bot := by
    intro x ihx c hxc
    obtain ⟨a, hPa, hca⟩ := ihx c hxc
    have haP : IsPropCT E a := isPropCT_of_elTCov_sort_prop sortCode_zero (ihP a hPa)
    exact ctyCov_prop_bot haP hca
  intro c
  constructor
  · intro hpc
    rw [collapse ihp hpc]
    exact .bot ρ q
  · intro hqc
    rw [collapse ihq hqc]
    exact .bot ρ p

/-- Pointwise environment update at slot `k`. -/
def EnvT.updateAt (ρ : EnvT) (k : Nat) (S : CptT → Prop) : EnvT :=
  fun i u => if i = k then S u else ρ i u

theorem EnvT.le_updateAt_of_sub {ρ : EnvT} {k : Nat} {S₁ S₂ : CptT → Prop}
    (h : ∀ u, S₁ u → S₂ u) : EnvT.le (EnvT.updateAt ρ k S₁) (EnvT.updateAt ρ k S₂) := by
  intro i u hu
  simp only [EnvT.updateAt] at hu ⊢
  by_cases hik : i = k
  · rw [if_pos hik] at hu ⊢; exact h u hu
  · rw [if_neg hik] at hu ⊢; exact hu

theorem EnvT.le_updateAt_cons {ρ : EnvT} {k : Nat} {S₀ S : CptT → Prop} :
    EnvT.le (EnvT.updateAt (EnvT.cons S₀ ρ) (k + 1) S)
      (EnvT.cons S₀ (EnvT.updateAt ρ k S)) := by
  intro i u hu
  cases i with
  | zero =>
      simp only [EnvT.updateAt, Nat.zero_ne_add_one, ite_false] at hu
      exact hu
  | succ j =>
      simp only [EnvT.updateAt, Nat.succ.injEq] at hu
      exact hu

/-- Constructive finite-list demand aggregation in `Prop` (no `Classical.choice`). -/
theorem collect_fin_lists {α : Type} {P : CptT → Prop} {Q : α → List CptT → Prop} :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ us : List CptT, (∀ u ∈ us, P u) ∧ Q x us) →
    ∃ usAll : List CptT, (∀ u ∈ usAll, P u) ∧
      ∀ x ∈ xs, ∃ us : List CptT, (∀ u ∈ us, u ∈ usAll) ∧ Q x us
  | [], _ =>
      ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | x :: xs, h => by
      obtain ⟨us₁, hP₁, hQ₁⟩ := h x (List.mem_cons_self _ _)
      obtain ⟨us₂, hP₂, hQ₂⟩ := collect_fin_lists xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun y hy => ?_⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact hP₁ u h1
        · exact hP₂ u h2
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨us₁, fun u hu => List.mem_append_left us₂ hu, hQ₁⟩
        · obtain ⟨us, hus, hQy⟩ := hQ₂ y hy'
          exact ⟨us, fun u hu => List.mem_append_right us₁ (hus u hu), hQy⟩

/-- **Finite demand on `ApproxT E` (`approxT_fin_at`)**: every `ApproxT E ρ e c` derivation uses
    only finitely many compacts of any environment slot `k`. -/
theorem approxT_fin_at {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) :
    ∀ (k : Nat), ∃ us : List CptT, (∀ u ∈ us, ρ k u) ∧
      ApproxT E (EnvT.updateAt ρ k (demandT us)) e c := by
  induction h with
  | bot _ _ =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bot _ _⟩
  | @bvar ρ i c hmem =>
      intro k
      by_cases hik : i = k
      · subst hik
        refine ⟨[c], fun u hu => by rcases List.mem_singleton.mp hu with rfl; exact hmem, .bvar ?_⟩
        simp only [EnvT.updateAt, ite_true]
        exact List.mem_singleton.mpr rfl
      · refine ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bvar ?_⟩
        simp only [EnvT.updateAt, if_neg hik]
        exact hmem
  | sort _ l =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .sort _ l⟩
  | @pi ρ A B a f _ hT _ ihA ihf =>
      intro k
      obtain ⟨usA, hA1, hA2⟩ := ihA k
      obtain ⟨usB, hB1, hB2⟩ := collect_fin_lists f (fun s hs => by
        obtain ⟨us, h1, h2⟩ := ihf s hs (k + 1)
        exact ⟨us, h1, approxT_mono_env EnvT.le_updateAt_cons h2⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .pi ?_ hT ?_⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact hA1 u h1
        · exact hB1 u h2
      · exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun u hu => List.mem_append_left usB hu)) hA2
      · intro s hs
        obtain ⟨us, hus, hsB⟩ := hB2 s hs
        refine approxT_mono_env (fun i u hu => ?_) hsB
        cases i with
        | zero => exact hu
        | succ j =>
            exact EnvT.le_updateAt_of_sub (fun w hw => List.mem_append_right usA (hus w hw)) j u hu
  | @lam ρ A b a g _ hT hnt _ ihA ihb =>
      intro k
      obtain ⟨usA, hA1, hA2⟩ := ihA k
      obtain ⟨usB, hB1, hB2⟩ := collect_fin_lists g (fun s hs => by
        obtain ⟨us, h1, h2⟩ := ihb s hs (k + 1)
        exact ⟨us, h1, approxT_mono_env EnvT.le_updateAt_cons h2⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .lam ?_ hT hnt ?_⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact hA1 u h1
        · exact hB1 u h2
      · exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun u hu => List.mem_append_left usB hu)) hA2
      · intro s hs
        obtain ⟨us, hus, hsb⟩ := hB2 s hs
        refine approxT_mono_env (fun i u hu => ?_) hsb
        cases i with
        | zero => exact hu
        | succ j =>
            exact EnvT.le_updateAt_of_sub (fun w hw => List.mem_append_right usA (hus w hw)) j u hu
  | @app ρ f a g s _ hs _ ihf iha =>
      intro k
      obtain ⟨usf, hf1, hf2⟩ := ihf k
      obtain ⟨usa, ha1, ha2⟩ := collect_fin_lists s.1 (fun u hu => iha u hu k)
      refine ⟨usf ++ usa, fun u hu => ?_, .app ?_ hs ?_⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact hf1 u h1
        · exact ha1 u h2
      · exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun u hu => List.mem_append_left usa hu)) hf2
      · intro u hu
        obtain ⟨us, hus, hua⟩ := ha2 u hu
        exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun w hw => List.mem_append_right usf (hus w hw))) hua
  | const _ r ls hrigid hnp =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .const _ r ls hrigid hnp⟩
  | delta hd h _ =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .delta hd h⟩
  | recursor ls hnp hpre hflds h _ =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursor ls hnp hpre hflds h⟩
  | recursorProp ls hP hpre h _ =>
      intro k
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursorProp ls hP hpre h⟩
  | appSpine _ _ ihf iha =>
      intro k
      obtain ⟨usf, hf1, hf2⟩ := ihf k
      obtain ⟨usa, ha1, ha2⟩ := iha k
      refine ⟨usf ++ usa, fun u hu => ?_, .appSpine ?_ ?_⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact hf1 u h1
        · exact ha1 u h2
      · exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun u hu => List.mem_append_left usa hu)) hf2
      · exact approxT_mono_env
          (EnvT.le_updateAt_of_sub (fun u hu => List.mem_append_right usf hu)) ha2
  | letE _ ih =>
      intro k
      obtain ⟨us, h1, h2⟩ := ih k
      exact ⟨us, h1, .letE h2⟩
  | lit _ ih =>
      intro k
      obtain ⟨us, h1, h2⟩ := ih k
      exact ⟨us, h1, .lit h2⟩

/-- **Finite-demand factorization at slot `0` (`approxT_cons_iff_exists_demandT`)**:
    `ApproxT E (EnvT.cons S₀ ρ) e c` holds iff there is a finite list `us : List CptT` with
    `∀ u ∈ us, S₀ u` and `ApproxT E (EnvT.cons (demandT us) ρ) e c`. -/
theorem approxT_cons_iff_exists_demandT (E : ResolvedEnv) (S₀ : CptT → Prop) (ρ : EnvT)
    (e : Expr Nat) (c : CptT) :
    ApproxT E (EnvT.cons S₀ ρ) e c ↔
      ∃ us : List CptT, (∀ u ∈ us, S₀ u) ∧ ApproxT E (EnvT.cons (demandT us) ρ) e c := by
  constructor
  · intro h
    obtain ⟨us, hus, hup⟩ := approxT_fin_at h 0
    refine ⟨us, hus, approxT_mono_env (fun i u hu => ?_) hup⟩
    cases i with
    | zero =>
        simp only [EnvT.updateAt, ite_true] at hu
        exact hu
    | succ j =>
        simp only [EnvT.updateAt, Nat.succ_ne_zero, ite_false] at hu
        exact hu
  · rintro ⟨us, hus, hd⟩
    refine approxT_mono_env (fun i u hu => ?_) hd
    cases i with
    | zero => exact hus u hu
    | succ j => exact hu

private theorem covInsert_lt {ρ : EnvT} {k i : Nat} (S : CptT → Prop) (h : i < k) :
    EnvT.insert ρ k S i = ρ i := by
  simp [EnvT.insert, h]

private theorem covInsert_self (ρ : EnvT) (k : Nat) (S : CptT → Prop) :
    EnvT.insert ρ k S k = S := by
  simp [EnvT.insert]

private theorem covInsert_gt {ρ : EnvT} {k i : Nat} (S : CptT → Prop) (h : k < i) :
    EnvT.insert ρ k S i = ρ (i - 1) := by
  have h1 : ¬ i < k := Nat.not_lt.mpr (Nat.le_of_lt h)
  have h2 : i ≠ k := Nat.ne_of_gt h
  simp [EnvT.insert, h1, h2]

private def covDrop (ρ : EnvT) (k : Nat) : EnvT := fun i => ρ (i + k)

private theorem covDrop_zero (ρ : EnvT) : covDrop ρ 0 = ρ := rfl

private theorem covDrop_cons (S : CptT → Prop) (ρ : EnvT) (k : Nat) :
    covDrop (EnvT.cons S ρ) (k + 1) = covDrop ρ k := by
  funext i
  show EnvT.cons S ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 from rfl]
  rfl

private theorem covDrop_succ (ρ : EnvT) (k : Nat) :
    covDrop ρ (k + 1) = covDrop (covDrop ρ 1) k := rfl

private theorem covInsert_drop_one (ρ : EnvT) : EnvT.insert (covDrop ρ 1) 0 (ρ 0) = ρ := by
  funext i
  cases i with
  | zero => rw [covInsert_self]
  | succ i => rw [covInsert_gt _ (Nat.succ_pos i)]; rfl

private theorem covApproxT_const_env {E : ResolvedEnv} (ρ ρ' : EnvT) {r : Nat} {ls : List Level}
    {c : CptT} (h : ApproxT E ρ (.const r ls) c) :
    ApproxT E ρ' (.const r ls) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid hnp => exact .const _ _ _ hrigid hnp
  | delta hd hh => exact .delta hd hh
  | recursor ls hnp hpre hflds hh => exact .recursor ls hnp hpre hflds hh
  | recursorProp ls hP hpre hh => exact .recursorProp ls hP hpre hh

private theorem covApproxT_natExpand_env {E : ResolvedEnv} (ρ ρ' : EnvT) :
    ∀ (t : Nat) {c : CptT},
      ApproxT E ρ (natExpand t) c → ApproxT E ρ' (natExpand t) c := by
  intro t
  induction t with
  | zero =>
      intro c h
      exact covApproxT_const_env ρ ρ' h
  | succ t ih =>
      intro c h
      rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨r, args, u, rfl, hf, ha⟩
      · exact .bot _ _
      · exact .app (covApproxT_const_env ρ ρ' hf) hs (fun u hu => ih (ha u hu))
      · exact .appSpine (covApproxT_const_env ρ ρ' hf) (ih ha)

private theorem covApproxT_liftN_intro {E : ResolvedEnv} {e : Expr Nat} {c : CptT} :
    ∀ (ρ : EnvT) (j : Nat), ApproxT E (covDrop ρ j) e c →
      ApproxT E ρ (lift 0 j e) c
  | ρ, 0, h => by rw [covDrop_zero] at h; rw [lift_zero_idx]; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx]
      rw [covDrop_succ] at h
      have := approxT_lift_intro (covApproxT_liftN_intro (covDrop ρ 1) j h) 0 (ρ 0)
      rwa [covInsert_drop_one] at this

private theorem covApproxT_liftN_elim {E : ResolvedEnv} {e : Expr Nat} {c : CptT} :
    ∀ (ρ : EnvT) (j : Nat), ApproxT E ρ (lift 0 j e) c →
      ApproxT E (covDrop ρ j) e c
  | ρ, 0, h => by rw [covDrop_zero]; rw [lift_zero_idx] at h; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx] at h
      rw [covDrop_succ]
      have h' : ApproxT E (EnvT.insert (covDrop ρ 1) 0 (ρ 0))
          (lift 0 1 (lift 0 j e)) c := by
        rwa [covInsert_drop_one]
      exact covApproxT_liftN_elim (covDrop ρ 1) j (approxT_lift_elim (lift 0 j e) h')

private theorem covApproxT_subst_intro {E : ResolvedEnv} {ρ' : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ' e c) :
    ∀ (ρ : EnvT) (j : Nat) (r : Expr Nat),
      ρ' = EnvT.insert ρ j (denT E (covDrop ρ j) r) →
      ApproxT E ρ (instantiate j (lift 0 j r) e) c := by
  induction h with
  | bot => intro ρ j r _; exact .bot _ _
  | @bvar ρ' i c h =>
      intro ρ j r hρ
      subst hρ
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [covInsert_self] at h
        exact covApproxT_liftN_intro ρ i h
      · rw [if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]
          rw [covInsert_gt _ hlt] at h
          exact .bvar h
        · rw [if_neg hlt]
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rw [covInsert_lt _ hil] at h
          exact .bvar h
  | sort => intro ρ j r _; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .pi (ihA ρ j r hρ) hT (fun s hs => ihf s hs _ (j + 1) r
        (by rw [hρ, EnvT.cons_insert, covDrop_cons]))
  | lam _ hT hnt _ ihA ihb =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .lam (ihA ρ j r hρ) hT hnt (fun s hs => ihb s hs _ (j + 1) r
        (by rw [hρ, EnvT.cons_insert, covDrop_cons]))
  | app _ hs _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .app (ihf ρ j r hρ) hs (fun u hu => iha u hu ρ j r hρ)
  | const _ _ _ hrigid hnp => intro _ _ _ _; exact .const _ _ _ hrigid hnp
  | delta hdelta h _ => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hnp hpre hflds h _ => intro _ _ _ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h _ => intro _ _ _ _; exact .recursorProp ls hP hpre h
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

private theorem covApproxT_subst_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvT} {j : Nat} {r : Expr Nat} {c : CptT},
      ApproxT E ρ (instantiate j (lift 0 j r) e) c →
      ApproxT E (EnvT.insert ρ j (denT E (covDrop ρ j) r)) e c
  | .bvar i, ρ, j, r, c, h => by
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact .bvar (by rw [covInsert_self]; exact covApproxT_liftN_elim ρ i h)
      · rw [if_neg hij] at h
        by_cases hlt : j < i
        · rw [if_pos hlt] at h
          rcases approxT_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [covInsert_gt _ hlt]; exact h0)
        · rw [if_neg hlt] at h
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rcases approxT_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [covInsert_lt _ hil]; exact h0)
  | .sort l, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxT_sort_inv h with rfl | rfl
      · exact .bot _ _
      · exact .sort _ _
  | .const k ls, ρ, j, r, c, h => by
      simp only [instantiate] at h
      exact covApproxT_const_env ρ _ h
  | .app f a, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨k, args, u, rfl, hf, ha⟩
      · exact .bot _ _
      · exact .app (covApproxT_subst_elim f hf) hs (fun u hu => covApproxT_subst_elim a (ha u hu))
      · exact .appSpine (covApproxT_subst_elim f hf) (covApproxT_subst_elim a ha)
  | .lam A b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxT_lam_inv h with rfl | ⟨a, g, rfl, hA, hnt, hg⟩
      · exact .bot _ _
      · exact .lam (covApproxT_subst_elim A hA) (fun s hs => (hg s hs).1) hnt
          (fun s hs => by
            rw [EnvT.cons_insert, ← covDrop_cons (demandT s.1) ρ j]
            exact covApproxT_subst_elim b ((hg s hs).2))
  | .pi A B, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxT_pi_inv h with rfl | ⟨a, f, rfl, hA, hf⟩
      · exact .bot _ _
      · exact .pi (covApproxT_subst_elim A hA) (fun s hs => (hf s hs).1)
          (fun s hs => by
            rw [EnvT.cons_insert, ← covDrop_cons (demandT s.1) ρ j]
            exact covApproxT_subst_elim B ((hf s hs).2))
  | .letE A v b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      cases h with
      | bot => exact .bot _ _
      | letE h =>
          rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨k, args, u, rfl, hf, ha⟩
          · exact .letE (.bot _ _)
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, hA', hnt', hg'⟩
            · cases h1
            · injection e with eg
              subst eg
              rw [lift_shift_comp_idx] at hg'
              exact .letE (.app
                (.lam (covApproxT_subst_elim A hA')
                  (fun s' hs' => (hg' s' hs').1) hnt'
                  (fun s' hs' => by
                    rw [EnvT.cons_insert, ← covDrop_cons (demandT s'.1) ρ j]
                    exact covApproxT_subst_elim b ((hg' s' hs').2)))
                hs
                (fun u hu => covApproxT_subst_elim v (ha u hu)))
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, _, _, _⟩
            · cases h1
            · cases e
  | .lit t, ρ, j, r, c, h => by
      simp only [instantiate] at h
      cases h with
      | bot => exact .bot _ _
      | lit h' => exact .lit (covApproxT_natExpand_env ρ _ t h')

/-- **Semantic substitution at slot `0` on `ApproxT E` (`covApproxT_subst0_iff`)**. -/
theorem covApproxT_subst0_iff (E : ResolvedEnv) (ρ : EnvT) (arg body : Expr Nat) (c : CptT) :
    ApproxT E ρ (instantiate0 arg body) c ↔
      ApproxT E (EnvT.cons (denT E ρ arg) ρ) body c := by
  constructor
  · intro h
    show ApproxT E (EnvT.cons (denT E ρ arg) ρ) body c
    rw [← EnvT.insert_zero, ← covDrop_zero ρ]
    exact covApproxT_subst_elim body (by
      show ApproxT E ρ (instantiate 0 (lift 0 0 arg) body) c
      rw [lift_zero_idx]
      exact h)
  · intro h
    have h' : ApproxT E (EnvT.insert ρ 0 (denT E (covDrop ρ 0) arg)) body c := by
      rwa [covDrop_zero, EnvT.insert_zero]
    have := covApproxT_subst_intro h' ρ 0 arg rfl
    rwa [lift_zero_idx] at this

/-- **Unconditional `ModelSubstFactorT` instance for `ctxModelT_approxT E` (`covModelSubstFactorT_approxT`)**:
    combines `covApproxT_subst0_iff` with `approxT_cons_iff_exists_demandT`. -/
theorem covModelSubstFactorT_approxT (E : ResolvedEnv) :
    ModelSubstFactorT (ctxModelT_approxT E) where
  subst0_intro {ρ arg body us c} hus hb :=
    (covApproxT_subst0_iff E ρ arg body c).mpr
      ((approxT_cons_iff_exists_demandT E (denT E ρ arg) ρ body c).mpr ⟨us, hus, hb⟩)
  subst0_factor {ρ arg body c} h :=
    (approxT_cons_iff_exists_demandT E (denT E ρ arg) ρ body c).mp
      ((covApproxT_subst0_iff E ρ arg body c).mp h)

/-- **Unconditional `ModelBetaExpandTypedM` and `ModelBetaExpandTypedFin` on `ApproxT E`**. -/
theorem modelBetaExpandTypedM_approxT (E : ResolvedEnv) :
    ModelBetaExpandTypedM (ctxModelT_approxT E) :=
  modelBetaExpandTypedM_of_substFactor (covModelSubstFactorT_approxT E)

theorem modelBetaExpandTypedFin_approxT (E : ResolvedEnv) :
    ModelBetaExpandTypedFin E :=
  modelBetaExpandTypedM_iff_fin.mp (modelBetaExpandTypedM_approxT E)

/-- Exact characterization of `ApproxT` at `.letE A v b`. -/
theorem approxT_letE_iff (E : ResolvedEnv) (ρ : EnvT) (A v b : Expr Nat) (c : CptT) :
    ApproxT E ρ (.letE A v b) c ↔ ApproxT E ρ (.app (.lam A b) v) c := by
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | letE h => exact h
  · exact .letE

theorem semEqT_letE_app_lam (E : ResolvedEnv) (ρ : EnvT) (A v b : Expr Nat) :
    SemEqT E ρ (.letE A v b) (.app (.lam A b) v) :=
  approxT_letE_iff E ρ A v b

/-- Extending an `EnvTypedCovAtT` environment across `.letBinding A value :: Γ` by
    `EnvT.cons (denT E ρ value) ρ` (using the single-compact typing IH on `value : A`). -/
theorem envTypedCovAtT_cons_letBinding {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} {A value : Expr Nat}
    (hρ : EnvTypedCovAtT E Γ ρ) (ihv : ∀ u, ApproxT E ρ value u → ElTCov E ρ A u) :
    EnvTypedCovAtT E (.letBinding A value :: Γ) (EnvT.cons (denT E ρ value) ρ) := by
  refine ⟨fun i A' hA' u hu => ?_, fun i v hv c => ?_⟩
  · cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at hA'
        injection hA' with hA'; subst hA'
        obtain ⟨a, hAa, hty⟩ := ihv u hu
        exact ⟨a, (approxT_cons_lift0_iff E ρ (denT E ρ value) A a).mpr hAa, hty⟩
    | succ j =>
        rw [lookupType_cons_succ] at hA'
        cases hA₀ : lookupType Γ j with
        | none => rw [hA₀] at hA'; exact Option.noConfusion hA'
        | some A₀ =>
            rw [hA₀] at hA'; injection hA' with hA'; subst hA'
            obtain ⟨a₀, hA₀a, hty₀⟩ := hρ.1 j A₀ hA₀ u hu
            exact ⟨a₀, (approxT_cons_lift0_iff E ρ (denT E ρ value) A₀ a₀).mpr hA₀a, hty₀⟩
  · cases i with
    | zero =>
        simp only [lookupValue, List.get?_cons_zero] at hv
        injection hv with hv; subst hv
        rw [approxT_cons_lift0_iff, approxT_bvar_iff]
        exact ⟨fun h => h.elim (fun e => e ▸ .bot _ _) id, fun h => Or.inr h⟩
    | succ j =>
        rw [lookupValue_cons_succ] at hv
        cases hv₀ : lookupValue Γ j with
        | none => rw [hv₀] at hv; exact Option.noConfusion hv
        | some v₀ =>
            rw [hv₀] at hv; injection hv with hv; subst hv
            rw [approxT_cons_lift0_iff]
            have ih := hρ.2 j v₀ hv₀ c
            rw [approxT_bvar_iff] at ih ⊢
            exact ih

/-- **`HasTyT.app` on `ApproxT E` (`covTyping_app`)**: closes from the typing IH on `f : .pi A B`
    and `ModelSubstFactorT.subst0_intro` (using `not_ctyCov_spine_of_approxT_pi` to rule out
    `.appSpine`). -/
theorem covTyping_app {E : ResolvedEnv} {ρ : EnvT} {f a A B : Expr Nat}
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (ihf : ∀ c, ApproxT E ρ f c → ElTCov E ρ (.pi A B) c)
    {u : CptT} (hu : ApproxT E ρ (.app f a) u) :
    ElTCov E ρ (instantiate0 a B) u := by
  rcases approxT_app_inv hu with rfl | ⟨g, s, rfl, hfg, hs, hau⟩ | ⟨r, args, v, rfl, hfg, _⟩
  · exact elTCov_bot E ρ (instantiate0 a B)
  · obtain ⟨p, hPip, htyp⟩ := ihf (.lam g) hfg
    rcases approxT_pi_inv hPip with rfl | ⟨a₀, f₀, rfl, _, hf₀⟩
    · exact CptT.noConfusion (ctyCov_bot_inv htyp)
    · rcases ctyCov_pi_inv htyp with hbot | ⟨g', heq, _, _, hcov⟩
      · exact CptT.noConfusion hbot
      · injection heq with eg'; subst eg'
        rcases hcov s hs with hbot | ⟨t, htf₀, hsub, hty_st⟩
        · rw [hbot]; exact elTCov_bot E ρ (instantiate0 a B)
        · have htB : ApproxT E (EnvT.cons (demandT t.1) ρ) B t.2 := (hf₀ t htf₀).2
          have hta : ∀ w ∈ t.1, ApproxT E ρ a w := fun w hw => hau w (hsub w hw)
          exact ⟨t.2, hF.subst0_intro hta htB, hty_st⟩
  · obtain ⟨p, hPip, htyp⟩ := ihf (.spine r args) hfg
    exact (not_ctyCov_spine_of_approxT_pi hPip htyp).elim

/-- **`HasTyT.letE` on `ApproxT E` (`covTyping_letE`)**: closes from the typing IHs on `value : A`
    and `body : B` (in `.letBinding A value :: Γ`), `envTypedCovAtT_cons_letBinding`,
    `approxT_cons_iff_exists_demandT`, and `ModelSubstFactorT.subst0_intro`. -/
theorem covTyping_letE {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    {A value B body : Expr Nat}
    (ihv : ∀ u, ApproxT E ρ value u → ElTCov E ρ A u)
    (ihb : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.letBinding A value :: Γ) ρ' →
      ∀ w, ApproxT E ρ' body w → ElTCov E ρ' B w)
    {w : CptT} (hw : ApproxT E ρ (.letE A value body) w) :
    ElTCov E ρ (instantiate0 value B) w := by
  have happ : ApproxT E ρ (.app (.lam A body) value) w := (approxT_letE_iff E ρ A value body w).mp hw
  rcases approxT_app_inv happ with rfl | ⟨g, s, rfl, hlam, hs, hval⟩ | ⟨r, args, u, rfl, hlam, _⟩
  · exact elTCov_bot E ρ (instantiate0 value B)
  · rcases approxT_lam_inv hlam with hbot | ⟨a, g', heq, _, _, hg⟩
    · exact CptT.noConfusion hbot
    · injection heq with eg'; subst eg'
      have hbody_s : ApproxT E (EnvT.cons (demandT s.1) ρ) body s.2 := (hg s hs).2
      have hle : EnvT.le (EnvT.cons (demandT s.1) ρ) (EnvT.cons (denT E ρ value) ρ) := by
        intro i c hc
        cases i with
        | zero => exact hval c hc
        | succ j => exact hc
      have hbody_den : ApproxT E (EnvT.cons (denT E ρ value) ρ) body s.2 :=
        approxT_mono_env hle hbody_s
      have hρ' := envTypedCovAtT_cons_letBinding hρ ihv
      obtain ⟨b₀, hBb₀, hty₀⟩ := ihb hρ' s.2 hbody_den
      obtain ⟨us, hus, hBus⟩ := (approxT_cons_iff_exists_demandT E (denT E ρ value) ρ B b₀).mp hBb₀
      exact ⟨b₀, hF.subst0_intro hus hBus, hty₀⟩
  · rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-- **`ConvT.app` on `ApproxT E` (`covConv_app`)**: closes unconditionally from the conversion
    IHs on `f ≡ g` and `a ≡ b`. -/
theorem covConv_app {E : ResolvedEnv} {ρ : EnvT} {f g a b : Expr Nat}
    (ih1 : SemEqT E ρ f g) (ih2 : SemEqT E ρ a b) :
    SemEqT E ρ (.app f a) (.app g b) := by
  have dir : ∀ {f₁ f₂ a₁ a₂ : Expr Nat}, SemEqT E ρ f₁ f₂ → SemEqT E ρ a₁ a₂ →
      ∀ {c : CptT}, ApproxT E ρ (.app f₁ a₁) c → ApproxT E ρ (.app f₂ a₂) c := by
    intro f₁ f₂ a₁ a₂ hf ha c hc
    rcases approxT_app_inv hc with rfl | ⟨g₀, s, rfl, hfg, hs, hau⟩ | ⟨r, args, u, rfl, hfg, hau⟩
    · exact .bot _ _
    · exact .app ((hf (.lam g₀)).mp hfg) hs (fun u hu => (ha u).mp (hau u hu))
    · exact .appSpine ((hf (.spine r args)).mp hfg) ((ha u).mp hau)
  intro c
  exact ⟨dir ih1 ih2, dir (fun x => (ih1 x).symm) (fun x => (ih2 x).symm)⟩

/-- **`ConvT.lam` on `ApproxT E` (`covConv_lam`)**: closes unconditionally from the conversion
    IHs on `A ≡ A'` and `b ≡ b'`. -/
theorem covConv_lam {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    {A A' b b' : Expr Nat}
    (ihA : SemEqT E ρ A A')
    (ihb : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.assumption A :: Γ) ρ' → SemEqT E ρ' b b') :
    SemEqT E ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro hc
    rcases approxT_lam_inv hc with rfl | ⟨a, g, rfl, hAa, hnt, hg⟩
    · exact .bot _ _
    · refine .lam ((ihA a).mp hAa) (fun s hs => (hg s hs).1) hnt (fun s hs => ?_)
      have hEnv : EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
        envTypedCovAtT_cons_assumption hρ hAa
          (fun u hu => ctyCov_of_ctyS a u ((hg s hs).1 u hu))
      exact (ihb hEnv s.2).mp (hg s hs).2
  · intro hc
    rcases approxT_lam_inv hc with rfl | ⟨a, g, rfl, hA'a, hnt, hg⟩
    · exact .bot _ _
    · have hAa : ApproxT E ρ A a := (ihA a).mpr hA'a
      refine .lam hAa (fun s hs => (hg s hs).1) hnt (fun s hs => ?_)
      have hEnv : EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
        envTypedCovAtT_cons_assumption hρ hAa
          (fun u hu => ctyCov_of_ctyS a u ((hg s hs).1 u hu))
      exact (ihb hEnv s.2).mpr (hg s hs).2

/-- **`ConvT.pi` on `ApproxT E` (`covConv_pi`)**: closes unconditionally from the conversion
    IHs on `A ≡ A'` and `B ≡ B'`. -/
theorem covConv_pi {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    {A A' B B' : Expr Nat}
    (ihA : SemEqT E ρ A A')
    (ihB : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.assumption A :: Γ) ρ' → SemEqT E ρ' B B') :
    SemEqT E ρ (.pi A B) (.pi A' B') := by
  intro c
  constructor
  · intro hc
    rcases approxT_pi_inv hc with rfl | ⟨a, f, rfl, hAa, hf⟩
    · exact .bot _ _
    · refine .pi ((ihA a).mp hAa) (fun s hs => (hf s hs).1) (fun s hs => ?_)
      have hEnv : EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
        envTypedCovAtT_cons_assumption hρ hAa
          (fun u hu => ctyCov_of_ctyS a u ((hf s hs).1 u hu))
      exact (ihB hEnv s.2).mp (hf s hs).2
  · intro hc
    rcases approxT_pi_inv hc with rfl | ⟨a, f, rfl, hA'a, hf⟩
    · exact .bot _ _
    · have hAa : ApproxT E ρ A a := (ihA a).mpr hA'a
      refine .pi hAa (fun s hs => (hf s hs).1) (fun s hs => ?_)
      have hEnv : EnvTypedCovAtT E (.assumption A :: Γ) (EnvT.cons (demandT s.1) ρ) :=
        envTypedCovAtT_cons_assumption hρ hAa
          (fun u hu => ctyCov_of_ctyS a u ((hf s hs).1 u hu))
      exact (ihB hEnv s.2).mpr (hf s hs).2

/-- Structural expression equivalence up to level equivalence (`eqN` on sorts, `eqNList` on
    constants). -/
inductive ExprEqN : Expr Nat → Expr Nat → Prop
  | bvar (i : Nat) : ExprEqN (.bvar i) (.bvar i)
  | sort {l₁ l₂ : Level} (h : eqN l₁ l₂) : ExprEqN (.sort l₁) (.sort l₂)
  | const (r : Nat) {ls₁ ls₂ : List Level} (h : eqNList ls₁ ls₂) :
      ExprEqN (.const r ls₁) (.const r ls₂)
  | app {f₁ f₂ a₁ a₂ : Expr Nat} (hf : ExprEqN f₁ f₂) (ha : ExprEqN a₁ a₂) :
      ExprEqN (.app f₁ a₁) (.app f₂ a₂)
  | lam {A₁ A₂ b₁ b₂ : Expr Nat} (hA : ExprEqN A₁ A₂) (hb : ExprEqN b₁ b₂) :
      ExprEqN (.lam A₁ b₁) (.lam A₂ b₂)
  | pi {A₁ A₂ B₁ B₂ : Expr Nat} (hA : ExprEqN A₁ A₂) (hB : ExprEqN B₁ B₂) :
      ExprEqN (.pi A₁ B₁) (.pi A₂ B₂)
  | letE {A₁ A₂ v₁ v₂ b₁ b₂ : Expr Nat} (hA : ExprEqN A₁ A₂) (hv : ExprEqN v₁ v₂)
      (hb : ExprEqN b₁ b₂) : ExprEqN (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂)
  | lit (t : Nat) : ExprEqN (.lit t) (.lit t)

theorem exprEqN_refl : (e : Expr Nat) → ExprEqN e e
  | .bvar i => .bvar i
  | .sort l => .sort (eqN_refl l)
  | .const r ls => .const r (eqNList_refl ls)
  | .app f a => .app (exprEqN_refl f) (exprEqN_refl a)
  | .lam A b => .lam (exprEqN_refl A) (exprEqN_refl b)
  | .pi A B => .pi (exprEqN_refl A) (exprEqN_refl B)
  | .letE A v b => .letE (exprEqN_refl A) (exprEqN_refl v) (exprEqN_refl b)
  | .lit t => .lit t

theorem exprEqN_instantiateLevels {ls₁ ls₂ : List Level} (h : eqNList ls₁ ls₂) :
    (e : Expr Nat) → ExprEqN (instantiateLevels ls₁ e) (instantiateLevels ls₂ e)
  | .bvar i => .bvar i
  | .sort l => .sort (instLevel_eqNList h l)
  | .const r us => .const r (instLevel_eqNList_map h us)
  | .app f a => .app (exprEqN_instantiateLevels h f) (exprEqN_instantiateLevels h a)
  | .lam A b => .lam (exprEqN_instantiateLevels h A) (exprEqN_instantiateLevels h b)
  | .pi A B => .pi (exprEqN_instantiateLevels h A) (exprEqN_instantiateLevels h B)
  | .letE A v b =>
      .letE (exprEqN_instantiateLevels h A) (exprEqN_instantiateLevels h v)
        (exprEqN_instantiateLevels h b)
  | .lit t => .lit t

/-- `ApproxT E` is invariant under `ExprEqN`. -/
theorem approxT_of_exprEqN {E : ResolvedEnv} {ρ : EnvT} {e₁ : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e₁ c) : ∀ {e₂ : Expr Nat}, ExprEqN e₁ e₂ → ApproxT E ρ e₂ c := by
  induction h with
  | bot _ _ => intro e₂ _; exact .bot _ e₂
  | bvar hmem => intro _ heq; cases heq; exact .bvar hmem
  | sort ρ l =>
      intro _ heq
      cases heq with
      | sort hl => exact (covConv_sorts E ρ hl (sortCode l)).mp (.sort ρ l)
  | pi _ hT _ ihA ihf =>
      intro _ heq
      cases heq with
      | pi hA hB => exact .pi (ihA hA) hT (fun s hs => ihf s hs hB)
  | lam _ hT hnt _ ihA ihb =>
      intro _ heq
      cases heq with
      | lam hA hb => exact .lam (ihA hA) hT hnt (fun s hs => ihb s hs hb)
  | app _ hs _ ihf iha =>
      intro _ heq
      cases heq with
      | app hf ha => exact .app (ihf hf) hs (fun u hu => iha u hu ha)
  | const _ r _ hrigid hnp =>
      intro _ heq
      cases heq with
      | const _ _ => exact .const _ r _ hrigid hnp
  | delta hd _ ih =>
      intro _ heq
      cases heq with
      | const _ hls => exact .delta hd (ih (exprEqN_instantiateLevels hls _))
  | recursor _ hnp hpre hflds _ ih =>
      intro _ heq
      cases heq with
      | const _ hls => exact .recursor _ hnp hpre hflds (ih (exprEqN_instantiateLevels hls _))
  | recursorProp _ hP hpre _ ih =>
      intro _ heq
      cases heq with
      | const _ hls => exact .recursorProp _ hP hpre (ih (exprEqN_instantiateLevels hls _))
  | appSpine _ _ ihf iha =>
      intro _ heq
      cases heq with
      | app hf ha => exact .appSpine (ihf hf) (iha ha)
  | letE _ ih =>
      intro _ heq
      cases heq with
      | letE hA hv hb => exact .letE (ih (.app (.lam hA hb) hv))
  | lit _ ih =>
      intro _ heq
      cases heq
      exact .lit (ih (exprEqN_refl _))

/-- **`ConvT.consts` on `ApproxT E` (`covConv_consts`)**: unconditional. -/
theorem covConv_consts (E : ResolvedEnv) (ρ : EnvT) (r : Nat) {ls ls' : List Level}
    (h : eqNList ls ls') : SemEqT E ρ (.const r ls) (.const r ls') :=
  fun _ => ⟨fun hc => approxT_of_exprEqN hc (.const r h),
    fun hc => approxT_of_exprEqN hc (.const r (eqNList_symm h))⟩

/-- Inversion of `ApproxT` at a `DeltaConst`. -/
theorem approxT_delta_const_inv_cov {E : ResolvedEnv} {ρ : EnvT} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) {c : CptT}
    (h : ApproxT E ρ (.const r ls) c) :
    ApproxT E EnvT.bot (instantiateLevels ls b) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid _ => exact (not_rigidConst_of_deltaConst hdelta hrigid).elim
  | delta hdelta' h' =>
      have hm : m = _ := Option.some.inj (hdelta.1.symm.trans hdelta'.1)
      subst hm
      have hb : b = _ := Option.some.inj (hdelta.2.1.symm.trans hdelta'.2.1)
      subst hb
      exact h'
  | @recursor _ w => exact (not_deltaConst_of_recursor w hdelta).elim
  | @recursorProp _ w => exact (not_deltaConst_of_recursor w hdelta).elim

/-- If `exprClosedAt k e = true` and `ρ` agrees with `ρ'` below `k`, then
    `ApproxT E ρ e c → ApproxT E ρ' e c`. -/
theorem approxT_closedAt_env_cov {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) :
    ∀ {k : Nat} {ρ' : EnvT}, exprClosedAt k e = true → (∀ i < k, ρ i = ρ' i) →
      ApproxT E ρ' e c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, decide_eq_true_eq] at hcl
      exact .bvar (heq i hcl ▸ h)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ hT _ ihA ihB =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .pi (ihA hcl.1 heq) hT (fun s hs => ihB s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | lam _ hT hnt _ ihA ihb =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .lam (ihA hcl.1 heq) hT hnt (fun s hs => ihb s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | app _ hs _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .app (ihf hcl.1 heq) hs (fun u hu => iha u hu hcl.2 heq)
  | const _ _ _ hrigid hnp => intro _ _ _ _; exact .const _ _ _ hrigid hnp
  | delta hdelta h => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hnp hpre hflds h => intro _ _ _ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h => intro _ _ _ _; exact .recursorProp ls hP hpre h
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

theorem approxT_closed0_env_cov {E : ResolvedEnv} (ρ ρ' : EnvT) {e : Expr Nat}
    (hcl : exprClosedAt 0 e = true) {c : CptT}
    (h : ApproxT E ρ e c) : ApproxT E ρ' e c :=
  approxT_closedAt_env_cov h hcl (fun _ hi => (Nat.not_lt_zero _ hi).elim)

/-- **`ConvT.delta` on `ApproxT E` (`covConv_delta`)**: closes unconditionally under `EnvWfT E`. -/
theorem covConv_delta {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m) (hbody : m.body = some b)
    (ρ : EnvT) : SemEqT E ρ (.const r ls) (instantiateLevels ls b) := by
  obtain ⟨hdelta, hcl⟩ := envWfT_member_body_closed hW r m b hres hbody
  have hcl_inst : exprClosedAt 0 (instantiateLevels ls b) = true := by
    rw [exprClosedAt_instantiateLevels]
    exact hcl
  intro c
  exact ⟨fun h => approxT_closed0_env_cov EnvT.bot ρ hcl_inst (approxT_delta_const_inv_cov hdelta h),
    fun h => .delta hdelta (approxT_closed0_env_cov ρ EnvT.bot hcl_inst h)⟩

/-- **Forward β-reduction on `ApproxT E` (`covConv_beta_fwd`)**: holds unconditionally from
    `ModelSubstFactorT.subst0_intro` without any typing hypothesis on `arg`. -/
theorem covConv_beta_fwd {E : ResolvedEnv} (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (ρ : EnvT) (A body arg : Expr Nat) {c : CptT}
    (h : ApproxT E ρ (.app (.lam A body) arg) c) :
    ApproxT E ρ (instantiate0 arg body) c := by
  rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hlam, hs, harg⟩ | ⟨r, args, u, rfl, hlam, _⟩
  · exact .bot _ _
  · rcases approxT_lam_inv hlam with hbot | ⟨a, g', heq, _, _, hg⟩
    · exact CptT.noConfusion hbot
    · injection heq with eg'; subst eg'
      exact hF.subst0_intro harg (hg s hs).2
  · rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-- **Forward ζ-reduction on `ApproxT E` (`covConv_zeta_fwd`)**: holds unconditionally from
    `ModelSubstFactorT.subst0_intro` without any typing hypothesis on `value`. -/
theorem covConv_zeta_fwd {E : ResolvedEnv} (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (ρ : EnvT) (A value body : Expr Nat) {c : CptT}
    (h : ApproxT E ρ (.letE A value body) c) :
    ApproxT E ρ (instantiate0 value body) c :=
  covConv_beta_fwd hF ρ A body value ((approxT_letE_iff E ρ A value body c).mp h)

theorem cptT_eq_bot_or_ne_bot (c : CptT) : c = .bot ∨ c ≠ .bot := by
  cases c <;> first | exact Or.inl rfl | exact Or.inr CptT.noConfusion

/-- **Full `ConvT.beta` on `ApproxT E` from `ArgTypedFinAt` (`covConv_beta_of_argTypedFinAt`)**:
    combines `covConv_beta_fwd` with `modelBetaExpandTypedM_of_substFactor`. -/
theorem covConv_beta_of_argTypedFinAt {E : ResolvedEnv}
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    {ρ : EnvT} {A body arg : Expr Nat} (hT : TypingFin.ArgTypedFinAt E ρ arg A) :
    SemEqT E ρ (.app (.lam A body) arg) (instantiate0 arg body) := by
  intro c
  refine ⟨covConv_beta_fwd hF ρ A body arg, fun hc => ?_⟩
  rcases cptT_eq_bot_or_ne_bot c with rfl | hc0
  · exact .bot _ _
  · obtain ⟨a, us, hAa, hty, hus, hb⟩ :=
      modelBetaExpandTypedM_of_substFactor hF hT hc
    have hlam : ApproxT E ρ (.lam A body) (.lam [(us, c)]) := by
      refine .lam hAa ?_ ⟨(us, c), List.mem_singleton.mpr rfl, hc0⟩ ?_
      · intro s hs u hu
        rcases List.mem_singleton.mp hs with rfl
        exact hty u hu
      · intro s hs
        rcases List.mem_singleton.mp hs with rfl
        exact hb
    exact .app hlam (List.mem_singleton.mpr rfl) hus

/-- **Full `ConvT.zeta` on `ApproxT E` from `ArgTypedFinAt` (`covConv_zeta_of_argTypedFinAt`)**:
    since `ApproxT E ρ (.letE A value body) c ↔ ApproxT E ρ (.app (.lam A body) value) c`,
    `SemEqT` for `zeta` is equivalent to `SemEqT` for `beta`. -/
theorem covConv_zeta_of_argTypedFinAt {E : ResolvedEnv}
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    {ρ : EnvT} {A value body : Expr Nat} (hT : TypingFin.ArgTypedFinAt E ρ value A) :
    SemEqT E ρ (.letE A value body) (instantiate0 value body) :=
  fun c => (approxT_letE_iff E ρ A value body c).trans
    (covConv_beta_of_argTypedFinAt hF hT c)

/-- **`ConvT.letE` on `ApproxT E` from `zeta` on both sides (`covConv_letE_of_zeta`)**:
    given the conversion IHs on `v ≡ v'` and `b ≡ b'` (at `EnvT.cons (denT E ρ v) ρ`) together
    with `SemEqT` for `zeta` on `(A, v, b)` and `(A', v', b')`, `.letE A v b` and `.letE A' v' b'`
    are `SemEqT`. -/
theorem covConv_letE_of_zeta {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hρ : EnvTypedCovAtT E Γ ρ)
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    {A A' v v' b b' : Expr Nat}
    (ihvTy : ∀ u, ApproxT E ρ v u → ElTCov E ρ A u)
    (ihv : SemEqT E ρ v v')
    (ihb : ∀ {ρ' : EnvT}, EnvTypedCovAtT E (.letBinding A v :: Γ) ρ' → SemEqT E ρ' b b')
    (hzeta1 : SemEqT E ρ (.letE A v b) (instantiate0 v b))
    (hzeta2 : SemEqT E ρ (.letE A' v' b') (instantiate0 v' b')) :
    SemEqT E ρ (.letE A v b) (.letE A' v' b') := by
  have hρ' := envTypedCovAtT_cons_letBinding hρ ihvTy
  have hden_eq : ∀ u, denT E ρ v u ↔ denT E ρ v' u := ihv
  intro c
  refine (hzeta1 c).trans (Iff.trans ?_ (hzeta2 c).symm)
  constructor
  · intro hc
    obtain ⟨us, hus, hb_us⟩ := hF.subst0_factor hc
    have hle : EnvT.le (EnvT.cons (demandT us) ρ) (EnvT.cons (denT E ρ v) ρ) := by
      intro i u hu; cases i with | zero => exact hus u hu | succ j => exact hu
    have hb'_den : ApproxT E (EnvT.cons (denT E ρ v) ρ) b' c :=
      (ihb hρ' c).mp (approxT_mono_env hle hb_us)
    obtain ⟨us', hus', hb'_us'⟩ :=
      (approxT_cons_iff_exists_demandT E (denT E ρ v) ρ b' c).mp hb'_den
    exact hF.subst0_intro (fun u hu => (hden_eq u).mp (hus' u hu)) hb'_us'
  · intro hc
    obtain ⟨us, hus, hb'_us⟩ := hF.subst0_factor hc
    have hle : EnvT.le (EnvT.cons (demandT us) ρ) (EnvT.cons (denT E ρ v) ρ) := by
      intro i u hu; cases i with | zero => exact (hden_eq u).mpr (hus u hu) | succ j => exact hu
    have hb_den : ApproxT E (EnvT.cons (denT E ρ v) ρ) b c :=
      (ihb hρ' c).mpr (approxT_mono_env hle hb'_us)
    obtain ⟨us', hus', hb_us'⟩ :=
      (approxT_cons_iff_exists_demandT E (denT E ρ v) ρ b c).mp hb_den
    exact hF.subst0_intro hus' hb_us'

/-! #### Positive resolutions of Obstruction 4 (`letSort1Ctx`, `letSort1`, `letIdSort1`) -/

/-- In `letSort1Ctx = [.letBinding (.sort idSort1TySort) idSort1Ty]`, `idSort1Ty` has compact
    `polyIdDom1 = .pi .sort [([.prop], .sort)]`. -/
theorem approxT_idSort1Ty_polyIdDom1 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ idSort1Ty polyIdDom1 := by
  have hA : ApproxT E ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E ρ (.succ .zero)
    rwa [sortCode_succ] at this
  have hB : ApproxT E (EnvT.cons (demandT [.prop]) ρ) (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code E (EnvT.cons (demandT [.prop]) ρ) (.succ .zero)
    rwa [sortCode_succ] at this
  refine .pi hA ?_ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact hB

/-- Every compact of `idSort1Ty` in any environment `ρ` is a `TyCodeCT`, hence in `ElTCov` of
    `.sort idSort1TySort`. -/
theorem elTCov_idSort1Ty_sort (E : ResolvedEnv) (ρ : EnvT) {u : CptT}
    (hu : ApproxT E ρ idSort1Ty u) : ElTCov E ρ (.sort idSort1TySort) u :=
  covTyping_pi (envTypedCovAtT_nil E ρ)
    (fun _ _ hc => covTyping_sort E _ (.succ .zero) hc)
    (fun _ _ hc => covTyping_sort E _ (.succ .zero) hc) hu

/-- **Positive resolution of Obstruction 4a (`envTypedCovAtT_letSort1Ctx`)**: the canonical
    context environment `ctxEnvT E letSort1Ctx = EnvT.cons (denT E EnvT.bot idSort1Ty) EnvT.bot`
    satisfies `EnvTypedCovAtT E letSort1Ctx`. -/
theorem envTypedCovAtT_letSort1Ctx (E : ResolvedEnv) :
    EnvTypedCovAtT E letSort1Ctx (ctxEnvT E letSort1Ctx) :=
  envTypedCovAtT_cons_letBinding (envTypedCovAtT_nil E EnvT.bot)
    (fun _ hu => elTCov_idSort1Ty_sort E EnvT.bot hu)

/-- **Positive resolution of Obstruction 4b (`elTCov_polyIdOut0_bvar0_ctxEnvT`,
    `elTCov_idSort1_bvar0_ctxEnvT`)**: in `ctxEnvT E letSort1Ctx` (where `CtxEnvT` holds, unlike
    `EnvT.bot` in `not_typingLemmaEnvFinT_letBinding`), `polyIdOut0` and every compact of `idSort1`
    are in `ElTCov E (ctxEnvT E letSort1Ctx) (.bvar 0)`. -/
theorem elTCov_polyIdOut0_bvar0_ctxEnvT (E : ResolvedEnv) :
    ElTCov E (ctxEnvT E letSort1Ctx) (.bvar 0) polyIdOut0 :=
  ⟨polyIdDom1, .bvar (approxT_idSort1Ty_polyIdDom1 E EnvT.bot),
    ctyCov_of_ctyS polyIdDom1 polyIdOut0 (ctyS_polyIdWitness1_polyIdDom1 E)⟩

theorem elTCov_idSort1_bvar0_ctxEnvT (E : ResolvedEnv) {c : CptT}
    (hc : ApproxT E (ctxEnvT E letSort1Ctx) idSort1 c) :
    ElTCov E (ctxEnvT E letSort1Ctx) (.bvar 0) c := by
  have hρ := envTypedCovAtT_letSort1Ctx E
  have hid : ElTCov E (ctxEnvT E letSort1Ctx) idSort1Ty c :=
    covTyping_lam (A := .sort (.succ .zero)) (B := .sort (.succ .zero)) hρ
      (fun hρ' w hw => covTyping_bvar (i := 0) (A := .sort (.succ .zero)) hρ' rfl hw) hc
  have hzl : SemEqT E (ctxEnvT E letSort1Ctx) idSort1Ty (.bvar 0) :=
    fun w => (hρ.2 0 idSort1Ty rfl w).symm
  obtain ⟨a, hAa, hty⟩ := hid
  exact ⟨a, (hzl a).mp hAa, hty⟩

/-- Concrete `letE` term `let X : Sort 2 := Sort 1 in X`. -/
def letSort1 : Expr Nat :=
  .letE (.sort (.succ (.succ .zero))) (.sort (.succ .zero)) (.bvar 0)

def hasTyT_letSort1 (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] letSort1 (.sort (.succ (.succ .zero))) :=
  .letE [] (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) (.bvar 0)
    (.sort _ _) (.sort _ _) (.bvar _ 0 _ rfl)

def convT_zeta_letSort1 (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] letSort1 (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .zeta [] (.sort (.succ (.succ .zero))) (.sort (.succ .zero)) (.bvar 0)
    (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
    (.sort _ _) (.sort _ _) (.bvar _ 0 _ rfl)

/-- Concrete `ConvT.zeta` soundness on `letSort1` (`semEqT_zeta_letSort1`): holds unconditionally
    at every environment `ρ`. -/
theorem semEqT_zeta_letSort1 (E : ResolvedEnv) (ρ : EnvT) :
    SemEqT E ρ letSort1 (.sort (.succ .zero)) := by
  intro c
  constructor
  · intro hc
    have happ := (approxT_letE_iff E ρ _ _ _ c).mp hc
    rcases approxT_app_inv happ with rfl | ⟨g, s, rfl, hlam, hs, hval⟩ | ⟨r, args, u, rfl, hlam, _⟩
    · exact .bot _ _
    · rcases approxT_lam_inv hlam with hbot | ⟨a, g', heq, _, _, hg⟩
      · exact CptT.noConfusion hbot
      · injection heq with eg'; subst eg'
        rcases approxT_bvar_inv (hg s hs).2 with h0 | hmem
        · rw [h0]; exact .bot _ _
        · exact hval s.2 hmem
    · rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
      · exact CptT.noConfusion hbot
      · exact CptT.noConfusion heq
  · intro hc
    rcases approxT_sort_inv hc with rfl | rfl
    · exact .bot _ _
    · rw [sortCode_succ]
      have hA : ApproxT E ρ (.sort (.succ (.succ .zero))) .sort := by
        have := approxT_sort_code E ρ (.succ (.succ .zero))
        rwa [sortCode_succ] at this
      have hS1 : ApproxT E ρ (.sort (.succ .zero)) .sort := by
        have := approxT_sort_code E ρ (.succ .zero)
        rwa [sortCode_succ] at this
      have hlam : ApproxT E ρ (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
          (.lam [([.sort], .sort)]) := by
        refine .lam hA ?_ ⟨([.sort], .sort), List.mem_singleton.mpr rfl, CptT.noConfusion⟩ ?_
        · intro s hs u hu
          rcases List.mem_singleton.mp hs with rfl
          rcases List.mem_singleton.mp hu with rfl
          exact ctyS_sort_sort E
        · intro s hs
          rcases List.mem_singleton.mp hs with rfl
          exact .bvar (List.mem_singleton.mpr rfl)
      exact .letE (.app hlam (List.mem_singleton.mpr rfl) (fun u hu => by
        rcases List.mem_singleton.mp hu with rfl
        exact hS1))

/-- Concrete `HasTyT.letE` typing on `letSort1` (`elTCov_letSort1`). -/
theorem elTCov_letSort1 (E : ResolvedEnv) (ρ : EnvT) {c : CptT}
    (hc : ApproxT E ρ letSort1 c) :
    ElTCov E ρ (.sort (.succ (.succ .zero))) c :=
  covTyping_sort E ρ (.succ .zero) ((semEqT_zeta_letSort1 E ρ c).mp hc)

/-- Concrete `letE` term `let f : Sort 1 → Sort 1 := idSort1 in f`. -/
def letIdSort1 : Expr Nat :=
  .letE idSort1Ty idSort1 (.bvar 0)

theorem approxT_letIdSort1_polyIdOut0 (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ letIdSort1 polyIdOut0 := by
  have hlam : ApproxT E ρ (.lam idSort1Ty (.bvar 0)) (.lam [([polyIdOut0], polyIdOut0)]) := by
    refine .lam (approxT_idSort1Ty_polyIdDom1 E ρ) ?_
      ⟨([polyIdOut0], polyIdOut0), List.mem_singleton.mpr rfl, CptT.noConfusion⟩ ?_
    · intro s hs u hu
      rcases List.mem_singleton.mp hs with rfl
      rcases List.mem_singleton.mp hu with rfl
      exact ctyS_polyIdWitness1_polyIdDom1 E
    · intro s hs
      rcases List.mem_singleton.mp hs with rfl
      exact .bvar (List.mem_singleton.mpr rfl)
  exact .letE (.app hlam (List.mem_singleton.mpr rfl) (fun u hu => by
    rcases List.mem_singleton.mp hu with rfl
    exact approxT_idSort1_polyIdOut0 E ρ))

theorem elTCov_letIdSort1 (E : ResolvedEnv) (ρ : EnvT) {c : CptT}
    (hc : ApproxT E ρ letIdSort1 c) :
    ElTCov E ρ idSort1Ty c := by
  have happ := (approxT_letE_iff E ρ _ _ _ c).mp hc
  rcases approxT_app_inv happ with rfl | ⟨g, s, rfl, hlam, hs, hval⟩ | ⟨r, args, u, rfl, hlam, _⟩
  · exact elTCov_bot E ρ idSort1Ty
  · rcases approxT_lam_inv hlam with hbot | ⟨a, g', heq, _, _, hg⟩
    · exact CptT.noConfusion hbot
    · injection heq with eg'; subst eg'
      rcases approxT_bvar_inv (hg s hs).2 with h0 | hmem
      · rw [h0]; exact elTCov_bot E ρ idSort1Ty
      · exact covTyping_lam (A := .sort (.succ .zero)) (B := .sort (.succ .zero))
          (envTypedCovAtT_nil E ρ)
          (fun hρ' w hw => covTyping_bvar (i := 0) (A := .sort (.succ .zero)) hρ' rfl hw)
          (hval s.2 hmem)
  · rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-! #### Simultaneous strong induction on `ApproxT E` (`covTyping_step`, `covTyping_strong`) -/

/-- Simultaneous inductive hypotheses below `sizeOf < k` for `TypingLemmaEnvCovT` and
    `ConvSoundEnvCovT` on `ApproxT E`. -/
def IHBelowCov (E : ResolvedEnv) (n : Nat) (k : Nat) : Prop :=
  (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), sizeOf d < k →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → ∀ u, ApproxT E ρ e u → ElTCov E ρ A u) ∧
  (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), sizeOf d < k →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ a b)

/-- Remaining per-constructor obligations on `ApproxT E` after **8 of 9 `HasTyT` constructors**
    (`sort`, `bvar`, `pi`, `lam`, `app`, `letE`, `lit`, `conv`) and **14 of 18 `ConvT`
    constructors** (`refl`, `symm`, `trans`, `zetaLocal`, `delta`, `iota`, `lit`, `app`, `lam`,
    `pi`, `sorts`, `consts`, `irr`, `tyConv`) are discharged directly in `covTyping_step`.
    Only `HasTyT.const` (1 of 9) and `ConvT.beta`, `ConvT.zeta`, `ConvT.letE`, `ConvT.eta` (4 of
    18) remain in `CovModelCases`. -/
structure CovModelCases (E : ResolvedEnv) (n : Nat) : Prop where
  const : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → ∀ u, ApproxT E ρ (.const r ls) u →
    ElTCov E ρ (instantiateLevels ls m.mtype) u
  beta : ∀ {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A),
    IHBelowCov E n (sizeOf (ConvT.beta Γ A body arg B u hA hb harg)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.app (.lam A body) arg) (instantiate0 arg body)
  zeta : ∀ {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    IHBelowCov E n (sizeOf (ConvT.zeta Γ A value body B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.letE A value body) (instantiate0 value body)
  letEConv : ∀ {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    IHBelowCov E n (sizeOf (ConvT.letE Γ A A' v v' b b' B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.letE A v b) (.letE A' v' b')
  eta : ∀ {Γ : LCtx} {f A B : Expr Nat} (h : HasTyT E n Γ f (.pi A B)),
    IHBelowCov E n (sizeOf (ConvT.eta Γ f A B h)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- **One step of the concrete `ApproxT` simultaneous induction (`covTyping_step`)**:
    discharges **8 of 9 `HasTyT` constructors** (`sort`, `bvar`, `pi`, `lam`, `app`, `letE`,
    `lit`, `conv`) and **14 of 18 `ConvT` constructors** (`refl`, `symm`, `trans`, `zetaLocal`,
    `delta`, `iota`, `lit`, `app`, `lam`, `pi`, `sorts`, `consts`, `irr`, `tyConv`) directly on
    `ApproxT E`. -/
theorem covTyping_step (hW : EnvWfT E) (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A),
      IHBelowCov E n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → ∀ u, ApproxT E ρ e u → ElTCov E ρ A u) ∧
    (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A),
      IHBelowCov E n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ a b) := by
  refine ⟨?_, ?_⟩
  · intro Γ e A d ih ρ hρ u hu
    cases d with
    | sort _ l => exact covTyping_sort E ρ l hu
    | bvar _ _ _ hA => exact covTyping_bvar hρ hA hu
    | const _ _ _ _ hres hlen hwf => exact hC.const hres hlen hwf hρ u hu
    | pi _ _ _ _ _ hA hB =>
        have hltA : sizeOf hA < sizeOf (HasTyT.pi _ _ _ _ _ hA hB) := by simp; omega
        have hltB : sizeOf hB < sizeOf (HasTyT.pi _ _ _ _ _ hA hB) := by simp; omega
        exact covTyping_pi hρ (fun hρ' c hc => ih.1 hA hltA hρ' c hc)
          (fun hρ' c hc => ih.1 hB hltB hρ' c hc) hu
    | lam _ _ _ _ _ hA hb =>
        have hltb : sizeOf hb < sizeOf (HasTyT.lam _ _ _ _ _ hA hb) := by simp; omega
        exact covTyping_lam hρ (fun hρ' c hc => ih.1 hb hltb hρ' c hc) hu
    | app _ _ _ _ _ hf ha =>
        have hltf : sizeOf hf < sizeOf (HasTyT.app _ _ _ _ _ hf ha) := by simp; omega
        exact covTyping_app hF (fun c hc => ih.1 hf hltf hρ c hc) hu
    | letE _ _ _ _ _ _ hA hv hb =>
        have hltv : sizeOf hv < sizeOf (HasTyT.letE _ _ _ _ _ _ hA hv hb) := by simp; omega
        have hltb : sizeOf hb < sizeOf (HasTyT.letE _ _ _ _ _ _ hA hv hb) := by simp; omega
        exact covTyping_letE hρ hF (fun c hc => ih.1 hv hltv hρ c hc)
          (fun hρ' c hc => ih.1 hb hltb hρ' c hc) hu
    | lit _ _ _ hexp =>
        have hlt : sizeOf hexp < sizeOf (HasTyT.lit _ _ _ hexp) := by simp; omega
        exact covTyping_lit (fun c hc => ih.1 hexp hlt hρ c hc) hu
    | conv _ _ _ _ _ h hc =>
        have hlt_h : sizeOf h < sizeOf (HasTyT.conv _ _ _ _ _ h hc) := by simp; omega
        have hlt_c : sizeOf hc < sizeOf (HasTyT.conv _ _ _ _ _ h hc) := by simp; omega
        exact covTyping_conv (fun c hc' => ih.1 h hlt_h hρ c hc') (ih.2 hc hlt_c hρ) hu
  · intro Γ a b A d ih ρ hρ c
    cases d with
    | refl _ _ _ _ => exact Iff.rfl
    | symm _ _ _ _ h =>
        have hlt : sizeOf h < sizeOf (ConvT.symm _ _ _ _ h) := by simp; omega
        exact (ih.2 h hlt hρ c).symm
    | trans _ _ _ _ _ h1 h2 =>
        have hlt1 : sizeOf h1 < sizeOf (ConvT.trans _ _ _ _ _ h1 h2) := by simp; omega
        have hlt2 : sizeOf h2 < sizeOf (ConvT.trans _ _ _ _ _ h1 h2) := by simp; omega
        exact (ih.2 h1 hlt1 hρ c).trans (ih.2 h2 hlt2 hρ c)
    | beta _ _ _ _ _ _ hA hb harg => exact hC.beta hA hb harg ih hρ c
    | zeta _ _ _ _ _ _ hA hv hb => exact hC.zeta hA hv hb ih hρ c
    | zetaLocal _ i _ _ hval _ _ => exact hρ.2 i b hval c
    | delta _ _ _ _ _ hres hbody _ _ _ _ =>
        exact covConv_delta hW hres hbody ρ c
    | iota _ _ _ _ h _ _ => exact hIota h ρ c
    | lit _ _ _ _ h _ => exact covConv_lit E ρ h c
    | app _ _ _ _ _ _ _ h1 h2 =>
        have hlt1 : sizeOf h1 < sizeOf (ConvT.app _ _ _ _ _ _ _ h1 h2) := by simp; omega
        have hlt2 : sizeOf h2 < sizeOf (ConvT.app _ _ _ _ _ _ _ h1 h2) := by simp; omega
        exact covConv_app (ih.2 h1 hlt1 hρ) (ih.2 h2 hlt2 hρ) c
    | lam _ _ _ _ _ _ _ hA hb =>
        have hltA : sizeOf hA < sizeOf (ConvT.lam _ _ _ _ _ _ _ hA hb) := by simp; omega
        have hltb : sizeOf hb < sizeOf (ConvT.lam _ _ _ _ _ _ _ hA hb) := by simp; omega
        exact covConv_lam hρ (ih.2 hA hltA hρ) (fun hρ' => ih.2 hb hltb hρ') c
    | pi _ _ _ _ _ _ _ hA hB =>
        have hltA : sizeOf hA < sizeOf (ConvT.pi _ _ _ _ _ _ _ hA hB) := by simp; omega
        have hltB : sizeOf hB < sizeOf (ConvT.pi _ _ _ _ _ _ _ hA hB) := by simp; omega
        exact covConv_pi hρ (ih.2 hA hltA hρ) (fun hρ' => ih.2 hB hltB hρ') c
    | letE _ _ _ _ _ _ _ _ _ hA hv hb => exact hC.letEConv hA hv hb ih hρ c
    | sorts _ _ _ h => exact covConv_sorts E ρ h c
    | consts _ r _ _ _ _ _ _ _ h =>
        exact covConv_consts E ρ r h c
    | eta _ _ _ _ h => exact hC.eta h ih hρ c
    | irr _ _ _ _ hP hp hq =>
        have hltP : sizeOf hP < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        have hltp : sizeOf hp < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        have hltq : sizeOf hq < sizeOf (ConvT.irr _ _ _ _ hP hp hq) := by simp; omega
        exact covConv_irr (fun c' hc' => ih.1 hP hltP hρ c' hc')
          (fun c' hc' => ih.1 hp hltp hρ c' hc')
          (fun c' hc' => ih.1 hq hltq hρ c' hc') c
    | tyConv _ _ _ _ _ _ h hA =>
        have hlt : sizeOf h < sizeOf (ConvT.tyConv _ _ _ _ _ _ h hA) := by simp; omega
        exact ih.2 h hlt hρ c

/-- **Simultaneous strong induction on `ApproxT E` (`covTyping_strong`)**. -/
theorem covTyping_strong (hW : EnvWfT E) (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    ∀ k : Nat, IHBelowCov E n k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro _ _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
      · intro _ _ _ _ _ hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
      obtain ⟨stepTy, stepConv⟩ := covTyping_step hW hF hIota hC
      refine ⟨?_, ?_⟩
      · intro Γ e A d hd ρ hρ u hu
        by_cases hk : sizeOf d < k
        · exact ih.1 d hk hρ u hu
        · have hk' : sizeOf d = k := by omega
          exact stepTy d (hk' ▸ ih) hρ u hu
      · intro Γ a b A d hd ρ hρ c
        by_cases hk : sizeOf d < k
        · exact ih.2 d hk hρ c
        · have hk' : sizeOf d = k := by omega
          exact stepConv d (hk' ▸ ih) hρ c

/-- **Simultaneous `TypingLemmaEnvCovT` and `ConvSoundEnvCovT` on `ApproxT E`**. -/
theorem typingLemmaEnvCovT_and_convSound_of_cases (hW : EnvWfT E)
    (hF : ModelSubstFactorT (ctxModelT_approxT E))
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    TypingLemmaEnvCovT E n ∧ ConvSoundEnvCovT E n := by
  refine ⟨?_, ?_⟩
  · intro Γ e A d ρ hρ u hu
    exact (covTyping_strong hW hF hIota hC (sizeOf d + 1)).1 d (Nat.lt_succ_self _) hρ u hu
  · intro Γ a b A d ρ hρ c
    exact (covTyping_strong hW hF hIota hC (sizeOf d + 1)).2 d (Nat.lt_succ_self _) hρ c

/-- **`hF`-free specialization of `covTyping_step` on `ApproxT E`**:
    discharges `ModelSubstFactorT (ctxModelT_approxT E)` unconditionally via `covModelSubstFactorT_approxT E`. -/
theorem covTyping_step_approxT (hW : EnvWfT E)
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A),
      IHBelowCov E n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → ∀ u, ApproxT E ρ e u → ElTCov E ρ A u) ∧
    (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A),
      IHBelowCov E n (sizeOf d) →
      ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ a b) :=
  covTyping_step hW (covModelSubstFactorT_approxT E) hIota hC

/-- **`hF`-free specialization of `covTyping_strong` on `ApproxT E`**. -/
theorem covTyping_strong_approxT (hW : EnvWfT E)
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    ∀ k : Nat, IHBelowCov E n k :=
  covTyping_strong hW (covModelSubstFactorT_approxT E) hIota hC

/-- **`hF`-free specialization of `typingLemmaEnvCovT_and_convSound_of_cases` on `ApproxT E`**:
    takes only `hW : EnvWfT E`, `hIota : ModelIotaStepT E (ctxModelT_approxT E)`, and `hC : CovModelCases E n`. -/
theorem typingLemmaEnvCovT_and_convSound_of_cases_approxT (hW : EnvWfT E)
    (hIota : ModelIotaStepT E (ctxModelT_approxT E)) (hC : CovModelCases E n) :
    TypingLemmaEnvCovT E n ∧ ConvSoundEnvCovT E n :=
  typingLemmaEnvCovT_and_convSound_of_cases hW (covModelSubstFactorT_approxT E) hIota hC

/-! ### §5 — Concrete `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` on `natEnvU` (`natEnvUWfT`)
    and the constant/recursor clause (`ConstCovClauseT`, `covTyping_const`) -/

/-- In `natEnvU` (`natEnvUWfT`), `Nat = .const 0 []` is a non-proof `RigidConst`. -/
theorem rigidConst_natEnvU_nat : RigidConst natEnvU 0 := by
  intro m hm
  injection hm with hm; subst hm
  exact ⟨Or.inl rfl, MemberClass.noConfusion⟩

theorem not_propCtorT_natEnvU_nat : ¬ PropCtorT natEnvU 0 := by
  rintro ⟨m, _, _, hm, hctor, _⟩
  injection hm with hm; subst hm
  exact MemberClass.noConfusion hctor

/-- In `natEnvU`, `Nat.zero = .const 1 []` is a non-proof `RigidConst`. -/
theorem rigidConst_natEnvU_zero : RigidConst natEnvU 1 := by
  intro m hm
  injection hm with hm; subst hm
  exact ⟨Or.inl rfl, MemberClass.noConfusion⟩

theorem not_propCtorT_natEnvU_zero : ¬ PropCtorT natEnvU 1 := by
  rintro ⟨m, fam, fm, hm, _, hhead, hfm, hsort⟩
  injection hm with hm; subst hm
  injection hhead with hfam; subst hfam
  injection hfm with hfm; subst hfm
  injection hsort with hsort
  exact Level.noConfusion hsort

/-- In `natEnvU`, `Nat.succ = .const 2 []` is a non-proof `RigidConst`. -/
theorem rigidConst_natEnvU_succ : RigidConst natEnvU 2 := by
  intro m hm
  injection hm with hm; subst hm
  exact ⟨Or.inl rfl, MemberClass.noConfusion⟩

theorem not_propCtorT_natEnvU_succ : ¬ PropCtorT natEnvU 2 := by
  rintro ⟨m, fam, fm, hm, _, hhead, hfm, hsort⟩
  injection hm with hm; subst hm
  injection hhead with hfam; subst hfam
  injection hfm with hfm; subst hfm
  injection hsort with hsort
  exact Level.noConfusion hsort

theorem not_isPropCT_natEnvU_nat_spine (args : List CptT) :
    ¬ IsPropCT natEnvU (.spine 0 args) := by
  intro h
  cases h with
  | spine hres hsort =>
      injection hres with hm; subst hm
      injection hsort with hsort
      exact Level.noConfusion hsort

/-- Every compact of `Nat = .const 0 []` in `natEnvU` is in `ElT` (and `ElTCov`) of
    `natFamMember.mtype = .sort (.succ .zero)`. -/
theorem elT_natEnvU_nat (ρ : EnvT) {u : CptT} (hu : ApproxT natEnvU ρ (.const 0 []) u) :
    ElT natEnvU ρ (.sort (.succ .zero)) u := by
  have hsort : ApproxT natEnvU ρ (.sort (.succ .zero)) .sort := by
    have := approxT_sort_code natEnvU ρ (.succ .zero)
    rwa [sortCode_succ] at this
  rcases approxT_rigid_const_inv rigidConst_natEnvU_nat hu with rfl | rfl
  · exact elT_bot natEnvU ρ _
  · refine ⟨.sort, hsort, ?_⟩
    rw [CTyS]
    exact Or.inr (.spine 0 [])

theorem elTCov_natEnvU_nat (ρ : EnvT) {u : CptT} (hu : ApproxT natEnvU ρ (.const 0 []) u) :
    ElTCov natEnvU ρ (.sort (.succ .zero)) u :=
  elTCov_of_elT (elT_natEnvU_nat ρ hu)

/-- Every compact of `Nat.zero = .const 1 []` in `natEnvU` is in `ElT` (and `ElTCov`) of
    `natZeroMember.mtype = .const 0 []`. -/
theorem elT_natEnvU_zero (ρ : EnvT) {u : CptT} (hu : ApproxT natEnvU ρ (.const 1 []) u) :
    ElT natEnvU ρ (.const 0 []) u := by
  have hNat : ApproxT natEnvU ρ (.const 0 []) (.spine 0 []) :=
    .const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat
  rcases approxT_rigid_const_inv rigidConst_natEnvU_zero hu with rfl | rfl
  · exact elT_bot natEnvU ρ _
  · refine ⟨.spine 0 [], hNat, ?_⟩
    rw [CTyS]
    exact Or.inr ⟨⟨1, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

theorem elTCov_natEnvU_zero (ρ : EnvT) {u : CptT} (hu : ApproxT natEnvU ρ (.const 1 []) u) :
    ElTCov natEnvU ρ (.const 0 []) u :=
  elTCov_of_elT (elT_natEnvU_zero ρ hu)

/-- Concrete instance of Obstruction 3 on `natEnvU`: `Nat.succ = .const 2 []` has compact
    `.spine 2 []`, which is not in `ElTCov natEnvU ρ (.pi (.const 0 []) (.const 0 []))` and
    refutes `SemEqT` for `ConvT.eta`. -/
theorem approxT_natSucc_spine (ρ : EnvT) :
    ApproxT natEnvU ρ (.const 2 []) (.spine 2 []) :=
  .const ρ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ

theorem not_elTCov_natSucc_spine (ρ : EnvT) :
    ¬ ElTCov natEnvU ρ (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) :=
  not_elTCov_spine_pi natEnvU ρ (.const 0 []) (.const 0 []) 2 []

theorem not_semEqT_eta_natSucc (ρ : EnvT) :
    ¬ SemEqT natEnvU ρ (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
        (.const 2 []) :=
  not_semEqT_eta_rigidConst ρ [] (.const 0 []) rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ

/-! #### `Nat.rec` on `natEnvU`: both the negative (`covBadRecCpt`) and positive (`covGoodRecCpt`)
    arms of `ApproxT.recursor` -/

/-- The `Nat.succ` computation schema in `natEnvU`:
    `bvar 1 (bvar 0) (const 3 [param 0] (bvar 3) (bvar 2) (bvar 1) (bvar 0))`. -/
def covNatSuccSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0))
    (.app (.app (.app (.app (.const 3 [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))

/-- Structured `IotaWitnessS` for `Nat.rec` on `Nat.succ` in `natEnvU` at `ls = [.succ .zero]`. -/
def covWNatSucc : IotaWitnessS natEnvU where
  recRef := 3
  ctorRef := 2
  ls := [.succ .zero]
  lsC := []
  recMember := natRecMemberU
  ctorMember := natSuccMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [natMotive, natMinorZ, natMinorS]
  fields := [natField]
  ctorParams := []
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.const 0 []]
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := natRecDomsU
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.recursive 0]
  hshapes := rfl
  schema := covNatSuccSchema
  hschema := rfl
  hstable := by
    intro E' hE'
    have h0 : E'.members 0 = some natFamMember := hE' 0 natFamMember rfl
    simp [fieldShapesFuel, fieldAnalyze, domainsContainFuel, properFamilyFuel,
      indicesCleanFuel, familyIdx, List.range, List.range.loop, piTelescopeFuel, whnfFuel,
      transparentBody, h0, natFamMember, natRecMemberU, transparent, isFamilyApp,
      exactParamLocals, appsSpine, occursConst, iotaOpenRhs, iotaArgs, recCallField, foldApps,
      canonRecLevels, preMajorBvars, fieldBvars, ctorFieldTelRaw, lift, covNatSuccSchema]
  hschemaScope := rfl

theorem not_propFamilyS_covWNatSucc : ¬ PropFamilyS covWNatSucc := by
  intro h
  injection h with h
  exact Level.noConfusion h

theorem instantiateLevels_natRecMemberU_mtype :
    instantiateLevels [.succ .zero] natRecMemberU.mtype = natRecType := rfl

/-- Inversion of `ElTCov` on `.lam [(us, body)]` at `.pi A B`: extracts a covering step `t` of
    `B` with `t.1 ⊆ us`, `ApproxT E (EnvT.cons (demandT t.1) ρ) B t.2`, and `CTyCov E body t.2`. -/
theorem elTCov_lam_singleton_pi_inv {E : ResolvedEnv} {ρ : EnvT} {A B : Expr Nat}
    {us : List CptT} {body : CptT} (hnb : body ≠ .bot)
    (h : ElTCov E ρ (.pi A B) (.lam [(us, body)])) :
    ∃ (a : CptT) (t : List CptT × CptT),
      ApproxT E ρ A a ∧ (∀ v ∈ us, CTyCov E v a) ∧ (∀ v ∈ t.1, v ∈ us) ∧
      ApproxT E (EnvT.cons (demandT t.1) ρ) B t.2 ∧ CTyCov E body t.2 := by
  obtain ⟨p, hPip, htyp⟩ := h
  rcases approxT_pi_inv hPip with rfl | ⟨a, f, rfl, hAa, hf⟩
  · exact CptT.noConfusion (ctyCov_bot_inv htyp)
  · rcases ctyCov_pi_inv htyp with hbot | ⟨g, heq, _, hdom, hcov⟩
    · exact CptT.noConfusion hbot
    · injection heq with eg; subst eg
      have hmem : (us, body) ∈ [(us, body)] := List.mem_singleton.mpr rfl
      rcases hcov (us, body) hmem with hbot | ⟨t, htf, hsub, hty⟩
      · exact (hnb hbot).elim
      · exact ⟨a, t, hAa, hdom (us, body) hmem, hsub, (hf t htf).2, hty⟩

/-- Untyped compact `covBadRecCpt` of `Nat.rec` produced by `ApproxT.recursor` when `us_pre` puts
    `[]` on the motive `C` (`bvar 3`) and `[covBadHsCpt]` on `ms` (`bvar 1`) (#7737 audit). -/
def covBadSpine : CptT := .spine 99 []
def covBadHsCpt : CptT := .lam [([covBadSpine], .lam [([], covBadSpine)])]
def covBadRecCpt : CptT :=
  curryStepT [[], [], [covBadHsCpt], ctorDemandT 2 0 [[covBadSpine]]] covBadSpine

theorem approxT_natRec_covBadRecCpt (ρ : EnvT) :
    ApproxT natEnvU ρ (.const 3 [.succ .zero]) covBadRecCpt := by
  let ρpush := EnvT.pushArgs (([[], [], [covBadHsCpt]] ++ [[covBadSpine]]).map demandT) EnvT.bot
  have h1 : ApproxT natEnvU ρpush (.bvar 1) covBadHsCpt :=
    .bvar (List.mem_singleton.mpr rfl)
  have h0 : ApproxT natEnvU ρpush (.bvar 0) covBadSpine :=
    .bvar (List.mem_singleton.mpr rfl)
  have happ1 : ApproxT natEnvU ρpush (.app (.bvar 1) (.bvar 0)) (.lam [([], covBadSpine)]) :=
    .app h1 (List.mem_singleton.mpr rfl) (fun u hu => by
      rcases List.mem_singleton.mp hu with rfl; exact h0)
  have hschema : ApproxT natEnvU ρpush
      (instantiateLevels [.succ .zero] covWNatSucc.schema) covBadSpine :=
    .app happ1 (List.mem_singleton.mpr rfl) (fun _ hu => (List.not_mem_nil _ hu).elim)
  exact ApproxT.recursor (w := covWNatSucc) [.succ .zero] not_propFamilyS_covWNatSucc rfl rfl hschema

/-- **Negative arm on `Nat.rec` (`not_elTCov_natRec_covBadRecCpt`, `not_elT_natRec_covBadRecCpt`)**:
    because `ApproxT.recursor` does not constrain `us_pre` by the recursor telescope's types,
    `covBadRecCpt` demands `[]` on the motive `C` (`bvar 3`) and outputs `covBadSpine = .spine 99 []`,
    whereas in `.app (.bvar 3) (.bvar 0)` with `t₁.1 ⊆ []`, `.bvar 3` has only `.bot` as compact,
    forcing the codomain compact `t₄.2` to be `.bot`. -/
theorem not_elTCov_natRec_covBadRecCpt (ρ : EnvT) :
    ¬ ElTCov natEnvU ρ (instantiateLevels [.succ .zero] natRecMemberU.mtype) covBadRecCpt := by
  rw [instantiateLevels_natRecMemberU_mtype]
  intro h
  have hne3 : curryStepT [[], [covBadHsCpt], ctorDemandT 2 0 [[covBadSpine]]] covBadSpine ≠ .bot :=
    CptT.noConfusion
  have hne2 : curryStepT [[covBadHsCpt], ctorDemandT 2 0 [[covBadSpine]]] covBadSpine ≠ .bot :=
    CptT.noConfusion
  have hne1 : curryStepT [ctorDemandT 2 0 [[covBadSpine]]] covBadSpine ≠ .bot :=
    CptT.noConfusion
  have hne0 : covBadSpine ≠ .bot := CptT.noConfusion
  obtain ⟨_, t₁, _, _, hsub₁, hB₁, hty₁⟩ := elTCov_lam_singleton_pi_inv hne3 h
  obtain ⟨_, t₂, _, _, _, hB₂, hty₂⟩ := elTCov_lam_singleton_pi_inv hne2 ⟨t₁.2, hB₁, hty₁⟩
  obtain ⟨_, t₃, _, _, _, hB₃, hty₃⟩ := elTCov_lam_singleton_pi_inv hne1 ⟨t₂.2, hB₂, hty₂⟩
  obtain ⟨_, t₄, _, _, _, hB₄, hty₄⟩ := elTCov_lam_singleton_pi_inv hne0 ⟨t₃.2, hB₃, hty₃⟩
  rcases approxT_app_inv hB₄ with hbot | ⟨g, s, _, hfg, _, _⟩ | ⟨r, args, u, _, hfg, _⟩
  · rw [hbot] at hty₄
    exact hne0 (ctyCov_bot_inv hty₄)
  · rcases approxT_bvar_inv hfg with hbot | hmem
    · exact CptT.noConfusion hbot
    · exact List.not_mem_nil _ (hsub₁ (.lam g) hmem)
  · rcases approxT_bvar_inv hfg with hbot | hmem
    · exact CptT.noConfusion hbot
    · exact List.not_mem_nil _ (hsub₁ (.spine r args) hmem)

theorem not_elT_natRec_covBadRecCpt (ρ : EnvT) :
    ¬ ElT natEnvU ρ (instantiateLevels [.succ .zero] natRecMemberU.mtype) covBadRecCpt :=
  fun h => not_elTCov_natRec_covBadRecCpt ρ (elTCov_of_elT h)

/-- Well-typed compacts for the positive arm on `Nat.rec`:
    - `covGoodMotiveCpt = .lam [([], .spine 0 [])]` (constant motive `λ _ : Nat. Nat`),
    - `covGoodHsCpt = .lam [([], .lam [([], .spine 1 [])])]` (step minor returning `Nat.zero`),
    - `covGoodRecCpt = curryStepT [[covGoodMotiveCpt], [], [covGoodHsCpt], ctorDemandT 2 0 [[]]] (.spine 1 [])`. -/
def covGoodMotiveCpt : CptT := .lam [([], .spine 0 [])]
def covGoodHsCpt : CptT := .lam [([], .lam [([], .spine 1 [])])]
def covGoodRecCpt : CptT :=
  curryStepT [[covGoodMotiveCpt], [], [covGoodHsCpt], ctorDemandT 2 0 [[]]] (.spine 1 [])

/-- **Positive arm on `Nat.rec` (`approxT_natRec_covGoodRecCpt`)**: `ApproxT.recursor` on
    `covWNatSucc` produces `covGoodRecCpt` for `.const 3 [.succ .zero]`. -/
theorem approxT_natRec_covGoodRecCpt (ρ : EnvT) :
    ApproxT natEnvU ρ (.const 3 [.succ .zero]) covGoodRecCpt := by
  let ρpush :=
    EnvT.pushArgs (([[covGoodMotiveCpt], [], [covGoodHsCpt]] ++ [[]]).map demandT) EnvT.bot
  have h1 : ApproxT natEnvU ρpush (.bvar 1) covGoodHsCpt :=
    .bvar (List.mem_singleton.mpr rfl)
  have happ1 : ApproxT natEnvU ρpush (.app (.bvar 1) (.bvar 0)) (.lam [([], .spine 1 [])]) :=
    .app h1 (List.mem_singleton.mpr rfl) (fun _ hu => (List.not_mem_nil _ hu).elim)
  have hschema : ApproxT natEnvU ρpush
      (instantiateLevels [.succ .zero] covWNatSucc.schema) (.spine 1 []) :=
    .app happ1 (List.mem_singleton.mpr rfl) (fun _ hu => (List.not_mem_nil _ hu).elim)
  exact ApproxT.recursor (w := covWNatSucc) [.succ .zero] not_propFamilyS_covWNatSucc rfl rfl hschema

/-- 1-step `CTyS` introduction at `.pi a [(us, b)]` for `.lam [(us, body)]`. -/
theorem ctyS_lam_singleton {E : ResolvedEnv} {a b body : CptT} {us : List CptT}
    (hnp : ¬ IsPropCT E b) (hdom : ∀ v ∈ us, CTyS E v a) (hcod : CTyS E body b) :
    CTyS E (.lam [(us, body)]) (.pi a [(us, b)]) := by
  have hnpPi : ¬ IsPropCT E (.pi a [(us, b)]) := by
    intro h
    cases h with
    | pi _ hg => exact hnp (hg (us, b) (List.mem_singleton.mpr rfl))
  rw [CTyS]
  refine Or.inr ⟨[(us, body)], rfl, hnpPi, ?_, ?_, ?_⟩
  · intro s hs v hv
    rcases List.mem_singleton.mp hs with rfl
    exact hdom v hv
  · intro s hs t ht _
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp ht with rfl
    exact hcod
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact Or.inr ⟨(us, b), List.mem_singleton.mpr rfl, fun v hv => hv⟩

theorem not_isPropCT_pi_singleton {E : ResolvedEnv} {a b : CptT} (us : List CptT)
    (hnp : ¬ IsPropCT E b) : ¬ IsPropCT E (.pi a [(us, b)]) := by
  intro h
  cases h with
  | pi _ hg => exact hnp (hg (us, b) (List.mem_singleton.mpr rfl))

/-- **Positive arm on `Nat.rec` (`elT_natRec_covGoodRecCpt`, `elTCov_natRec_covGoodRecCpt`)**:
    `covGoodRecCpt` IS in `ElT` and `ElTCov` of `instantiateLevels [.succ .zero] natRecMemberU.mtype`
    at every environment `ρ`. -/
theorem elT_natRec_covGoodRecCpt (ρ : EnvT) :
    ElT natEnvU ρ (instantiateLevels [.succ .zero] natRecMemberU.mtype) covGoodRecCpt := by
  rw [instantiateLevels_natRecMemberU_mtype]
  have hNat : ∀ ρ' : EnvT, ApproxT natEnvU ρ' (.const 0 []) (.spine 0 []) :=
    fun ρ' => .const ρ' 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat
  have hSort1 : ∀ ρ' : EnvT, ApproxT natEnvU ρ' (.sort (.succ .zero)) .sort := by
    intro ρ'
    have := approxT_sort_code natEnvU ρ' (.succ .zero)
    rwa [sortCode_succ] at this
  have hnpNat : ¬ IsPropCT natEnvU (.spine 0 []) := not_isPropCT_natEnvU_nat_spine []
  have hctySpine : ∀ r args, CTyS natEnvU (.spine r args) (.spine 0 []) := by
    intro r args
    rw [CTyS]
    exact Or.inr ⟨⟨r, args, rfl⟩, hnpNat⟩
  -- Domain 0: `P : Nat → Sort 1` has compact `domP = .pi (.spine 0 []) [([], .sort)]`
  let domP : CptT := .pi (.spine 0 []) [([], .sort)]
  have hdomP : ApproxT natEnvU ρ (.pi (.const 0 []) (.sort (.succ .zero))) domP :=
    .pi (hNat ρ) (fun _ hs _ hv => by
      rcases List.mem_singleton.mp hs with rfl; exact (List.not_mem_nil _ hv).elim)
      (fun s hs => by rcases List.mem_singleton.mp hs with rfl; exact hSort1 _)
  have hMotiveTy : CTyS natEnvU covGoodMotiveCpt domP := by
    refine ctyS_lam_singleton (not_isPropCT_sort natEnvU)
      (fun _ hv => (List.not_mem_nil _ hv).elim) ?_
    rw [CTyS]; exact Or.inr (.spine 0 [])
  let ρ₁ := EnvT.cons (demandT [covGoodMotiveCpt]) ρ
  -- Domain 2: `ms : Π n : Nat, Π ih : P n, P (succ n)` has compact `domMs`
  let domMsInner : CptT := .pi (.spine 0 []) [([], .spine 0 [])]
  let domMs : CptT := .pi (.spine 0 []) [([], domMsInner)]
  let ρ₂ := EnvT.cons (demandT []) ρ₁
  have hdomMs : ApproxT natEnvU ρ₂
      (.pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))) domMs := by
    refine .pi (hNat ρ₂)
      (fun _ hs _ hv => by rcases List.mem_singleton.mp hs with rfl; exact (List.not_mem_nil _ hv).elim)
      (fun s hs => ?_)
    rcases List.mem_singleton.mp hs with rfl
    let ρ₂n := EnvT.cons (demandT []) ρ₂
    have hb2 : ApproxT natEnvU ρ₂n (.bvar 2) covGoodMotiveCpt :=
      .bvar (List.mem_singleton.mpr rfl)
    have hPn : ApproxT natEnvU ρ₂n (.app (.bvar 2) (.bvar 0)) (.spine 0 []) :=
      .app hb2 (List.mem_singleton.mpr rfl) (fun _ hv => (List.not_mem_nil _ hv).elim)
    refine .pi hPn
      (fun _ hs' _ hv => by rcases List.mem_singleton.mp hs' with rfl; exact (List.not_mem_nil _ hv).elim)
      (fun s' hs' => ?_)
    rcases List.mem_singleton.mp hs' with rfl
    let ρ₂nih := EnvT.cons (demandT []) ρ₂n
    have hb3 : ApproxT natEnvU ρ₂nih (.bvar 3) covGoodMotiveCpt :=
      .bvar (List.mem_singleton.mpr rfl)
    exact .app hb3 (List.mem_singleton.mpr rfl) (fun _ hv => (List.not_mem_nil _ hv).elim)
  have hHsTy : CTyS natEnvU covGoodHsCpt domMs :=
    ctyS_lam_singleton (not_isPropCT_pi_singleton [] hnpNat)
      (fun _ hv => (List.not_mem_nil _ hv).elim)
      (ctyS_lam_singleton hnpNat (fun _ hv => (List.not_mem_nil _ hv).elim) (hctySpine 1 []))
  -- Major demand `ctorDemandT 2 0 [[]] = [.spine 2 [.bot]]`
  let majDem := ctorDemandT 2 0 [[]]
  have hmajDem : ∀ v ∈ majDem, CTyS natEnvU v (.spine 0 []) := by
    intro v hv
    change v ∈ [CptT.spine 2 [.bot]] at hv
    rcases List.mem_singleton.mp hv with rfl
    exact hctySpine 2 [.bot]
  -- Assemble the 4-binder Π-compact `recTyCpt` of `natRecType`
  let c₃ : CptT := .pi (.spine 0 []) [(majDem, .spine 0 [])]
  let c₂ : CptT := .pi domMs [([covGoodHsCpt], c₃)]
  let c₁ : CptT := .pi (.spine 0 []) [([], c₂)]
  let recTyCpt : CptT := .pi domP [([covGoodMotiveCpt], c₁)]
  refine ⟨recTyCpt, ?_, ?_⟩
  · refine .pi hdomP
      (fun s hs v hv => by
        rcases List.mem_singleton.mp hs with rfl
        rcases List.mem_singleton.mp hv with rfl
        exact hMotiveTy)
      (fun s hs => ?_)
    rcases List.mem_singleton.mp hs with rfl
    have hP0 : ApproxT natEnvU ρ₁ (.app (.bvar 0) (.const 1 [])) (.spine 0 []) :=
      .app (.bvar (List.mem_singleton.mpr rfl)) (List.mem_singleton.mpr rfl)
        (fun _ hv => (List.not_mem_nil _ hv).elim)
    refine .pi hP0
      (fun s₁ hs₁ _ hv => by
        rcases List.mem_singleton.mp hs₁ with rfl; exact (List.not_mem_nil _ hv).elim)
      (fun s₁ hs₁ => ?_)
    rcases List.mem_singleton.mp hs₁ with rfl
    refine .pi hdomMs
      (fun s₂ hs₂ v hv => by
        rcases List.mem_singleton.mp hs₂ with rfl
        rcases List.mem_singleton.mp hv with rfl
        exact hHsTy)
      (fun s₂ hs₂ => ?_)
    rcases List.mem_singleton.mp hs₂ with rfl
    let ρ₃ := EnvT.cons (demandT [covGoodHsCpt]) ρ₂
    refine .pi (hNat ρ₃)
      (fun s₃ hs₃ v hv => by
        rcases List.mem_singleton.mp hs₃ with rfl
        exact hmajDem v hv)
      (fun s₃ hs₃ => ?_)
    rcases List.mem_singleton.mp hs₃ with rfl
    let ρ₄ := EnvT.cons (demandT majDem) ρ₃
    have hb3_4 : ApproxT natEnvU ρ₄ (.bvar 3) covGoodMotiveCpt :=
      .bvar (List.mem_singleton.mpr rfl)
    exact ApproxT.app (s := ([], .spine 0 [])) hb3_4 (List.mem_singleton.mpr rfl)
      (fun _ hv => (List.not_mem_nil _ hv).elim)
  · exact ctyS_lam_singleton
      (not_isPropCT_pi_singleton [] (not_isPropCT_pi_singleton [covGoodHsCpt]
        (not_isPropCT_pi_singleton majDem hnpNat)))
      (fun v hv => by rcases List.mem_singleton.mp hv with rfl; exact hMotiveTy)
      (ctyS_lam_singleton
        (not_isPropCT_pi_singleton [covGoodHsCpt] (not_isPropCT_pi_singleton majDem hnpNat))
        (fun _ hv => (List.not_mem_nil _ hv).elim)
        (ctyS_lam_singleton
          (not_isPropCT_pi_singleton majDem hnpNat)
          (fun v hv => by rcases List.mem_singleton.mp hv with rfl; exact hHsTy)
          (ctyS_lam_singleton hnpNat hmajDem (hctySpine 1 []))))

theorem elTCov_natRec_covGoodRecCpt (ρ : EnvT) :
    ElTCov natEnvU ρ (instantiateLevels [.succ .zero] natRecMemberU.mtype) covGoodRecCpt :=
  elTCov_of_elT (elT_natRec_covGoodRecCpt ρ)

/-- The exact 9th `HasTyT` constructor obligation on `ApproxT E` (`ConstCovClauseT`): every
    compact of a well-formed constant `.const r ls` is in `ElTCov E ρ (instantiateLevels ls m.mtype)`. -/
def ConstCovClauseT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {r : Nat} {ls : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ (ρ : EnvT) (u : CptT), ApproxT E ρ (.const r ls) u →
    ElTCov E ρ (instantiateLevels ls m.mtype) u

theorem covTyping_const (hConst : ConstCovClauseT E n) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) {ρ : EnvT} (_hρ : EnvTypedCovAtT E Γ ρ) {u : CptT}
    (hu : ApproxT E ρ (.const r ls) u) :
    ElTCov E ρ (instantiateLevels ls m.mtype) u :=
  hConst hres hlen hwf ρ u hu

/-- Closed-type environment invariance for `ElTCov` and `ElT`: because `CTyCov` and `CTyS` do not
    depend on `ρ` and `ApproxT` on a closed type (`exprClosedAt 0 A = true`) is environment-independent
    (`approxT_closed0_env_cov`), semantic membership at `A` transfers between any two environments
    `ρ₁, ρ₂ : EnvT`. -/
theorem elTCov_closed0_env {E : ResolvedEnv} (ρ₁ ρ₂ : EnvT) {A : Expr Nat}
    (hcl : exprClosedAt 0 A = true) {u : CptT} :
    ElTCov E ρ₁ A u ↔ ElTCov E ρ₂ A u :=
  ⟨fun ⟨a, hA, hty⟩ => ⟨a, approxT_closed0_env_cov ρ₁ ρ₂ hcl hA, hty⟩,
   fun ⟨a, hA, hty⟩ => ⟨a, approxT_closed0_env_cov ρ₂ ρ₁ hcl hA, hty⟩⟩

theorem elT_closed0_env {E : ResolvedEnv} (ρ₁ ρ₂ : EnvT) {A : Expr Nat}
    (hcl : exprClosedAt 0 A = true) {u : CptT} :
    ElT E ρ₁ A u ↔ ElT E ρ₂ A u :=
  ⟨fun ⟨a, hA, hty⟩ => ⟨a, approxT_closed0_env_cov ρ₁ ρ₂ hcl hA, hty⟩,
   fun ⟨a, hA, hty⟩ => ⟨a, approxT_closed0_env_cov ρ₂ ρ₁ hcl hA, hty⟩⟩

/-- Every member added in a `GroupMembersT` chain has a closed stored type (`exprClosedAt 0 m.mtype = true`). -/
theorem groupMembersT_mtype_closed {S E E' : ResolvedEnv} {l : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E l E')
    (hE : ∀ r m, E.members r = some m → exprClosedAt 0 m.mtype = true) :
    ∀ r m, E'.members r = some m → exprClosedAt 0 m.mtype = true := by
  induction hmem with
  | nil _ => exact hE
  | @cons E₀ r₀ m₀ _ _ _ _ _ _ _ _ _ _ _ _ hT _ _ _ ih =>
      refine ih (fun r m hm => ?_)
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        injection hm with hm; subst hm
        exact hasTyT_exprClosedAt hT
      · rw [members_extend_ne E₀ r₀ m₀ r hrr] at hm
        exact hE r m hm

/-- In any well-formed environment `EnvWfT E`, every member `m` has `exprClosedAt 0 m.mtype = true`. -/
theorem envWfT_member_mtype_closed {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ r m, E.members r = some m → exprClosedAt 0 m.mtype = true := by
  induction hW with
  | empty => intro _ _ hm; exact Option.noConfusion hm
  | @«axiom» E₀ r₀ A _ _ _ hA _ _ ih =>
      intro r m hm
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; injection hm with hm; subst hm
        exact hasTyT_exprClosedAt hA
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m hm
  | @definition E₀ r₀ A _ _ _ _ hA _ _ _ _ _ ih =>
      intro r m hm
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; injection hm with hm; subst hm
        exact hasTyT_exprClosedAt hA
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m hm
  | @thm E₀ r₀ A _ _ _ hA _ _ _ _ _ ih =>
      intro r m hm
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; injection hm with hm; subst hm
        exact hasTyT_exprClosedAt hA
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m hm
  | @«opaque» E₀ r₀ A _ _ _ _ hA _ _ _ _ _ ih =>
      intro r m hm
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; injection hm with hm; subst hm
        exact hasTyT_exprClosedAt hA
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m hm
  | group _ _ _ _ _ _ _ _ _ _ _ hmem ih =>
      exact groupMembersT_mtype_closed hmem ih

/-- Closed `EnvT.bot` restriction of `ConstCovClauseT`: because both `.const r ls` and
    `instantiateLevels ls m.mtype` are closed under `EnvWfT E`, `ConstCovClauseT E n` at arbitrary
    `ρ` is equivalent to its `EnvT.bot` specialization (`constCovClauseT_iff_bot`). -/
def ConstCovBotClauseT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {r : Nat} {ls : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ (u : CptT), ApproxT E EnvT.bot (.const r ls) u →
    ElTCov E EnvT.bot (instantiateLevels ls m.mtype) u

theorem constCovClauseT_iff_bot {E : ResolvedEnv} (hW : EnvWfT E) (n : Nat) :
    ConstCovClauseT E n ↔ ConstCovBotClauseT E n := by
  constructor
  · intro h r ls m hres hlen hwf u hu
    exact h hres hlen hwf EnvT.bot u hu
  · intro h r ls m hres hlen hwf ρ u hu
    have hcl_inst : exprClosedAt 0 (instantiateLevels ls m.mtype) = true := by
      rw [exprClosedAt_instantiateLevels]
      exact envWfT_member_mtype_closed hW r m hres
    have hu_bot : ApproxT E EnvT.bot (.const r ls) u :=
      approxT_closed0_env_cov ρ EnvT.bot (e := .const r ls) rfl hu
    exact (elTCov_closed0_env EnvT.bot ρ hcl_inst).mp (h hres hlen hwf u hu_bot)

/-- Three-arm decomposition of `ConstCovBotClauseT E n` matching the non-`⊥` constructors of
    `ApproxT E EnvT.bot (.const r ls) u`:
    - `MemberDeltaCovT`: transparent definitions (`ApproxT.delta`),
    - `MemberRigidCovT`: non-proof rigid constants (`ApproxT.const`),
    - `MemberRecCovT`: recursor constants (`ApproxT.recursor` and `ApproxT.recursorProp`). -/
def MemberDeltaCovT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    DeltaConst E r m b → ∀ (u : CptT), ApproxT E EnvT.bot (instantiateLevels ls b) u →
    ElTCov E EnvT.bot (instantiateLevels ls m.mtype) u

def MemberRigidCovT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {r : Nat} {ls : List Level} {m : CheckedMember},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    RigidConst E r → ¬ PropCtorT E r →
    ElTCov E EnvT.bot (instantiateLevels ls m.mtype) (.spine r [])

def MemberRecCovT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {w : IotaWitnessS E} {ls : List Level} {m : CheckedMember},
    E.members w.recRef = some m → ls.length = m.arity → levelsBounded n ls = true →
    (∀ {us_pre us_fields : List (List CptT)} {c : CptT},
      ¬ PropFamilyS w →
      us_pre.length = w.preMajor.length → us_fields.length = w.fields.length →
      ApproxT E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c →
      ElTCov E EnvT.bot (instantiateLevels ls m.mtype)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)) ∧
    (∀ {us_pre : List (List CptT)} {c : CptT},
      PropFamilyS w →
      us_pre.length = w.preMajor.length →
      ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c →
      ElTCov E EnvT.bot (instantiateLevels ls m.mtype)
        (curryStepT (us_pre ++ [[]]) c))

theorem constCovBotClauseT_of_arms {E : ResolvedEnv} {n : Nat}
    (hDelta : MemberDeltaCovT E n) (hRigid : MemberRigidCovT E n) (hRec : MemberRecCovT E n) :
    ConstCovBotClauseT E n := by
  intro r ls m hres hlen hwf u hu
  generalize he : Expr.const r ls = e at hu
  cases hu with
  | bot => exact elTCov_bot E EnvT.bot _
  | bvar _ => exact Expr.noConfusion he
  | sort _ _ => exact Expr.noConfusion he
  | pi _ _ _ => exact Expr.noConfusion he
  | lam _ _ _ _ => exact Expr.noConfusion he
  | app _ _ _ => exact Expr.noConfusion he
  | const _ r' ls' hrigid hnp =>
      injection he with er els; subst er; subst els
      exact hRigid hres hlen hwf hrigid hnp
  | delta hdelta hb =>
      injection he with er els; subst er; subst els
      have hm : _ = m := Option.some.inj (hdelta.1.symm.trans hres)
      subst hm
      exact hDelta hres hlen hwf hdelta _ hb
  | recursor ls' hnp hpre hflds hschema =>
      injection he with er els; subst er; subst els
      exact (hRec hres hlen hwf).1 hnp hpre hflds hschema
  | recursorProp ls' hP hpre hschema =>
      injection he with er els; subst er; subst els
      exact (hRec hres hlen hwf).2 hP hpre hschema
  | appSpine _ _ => exact Expr.noConfusion he
  | letE _ => exact Expr.noConfusion he
  | lit _ => exact Expr.noConfusion he

theorem constCovClauseT_of_arms {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hDelta : MemberDeltaCovT E n) (hRigid : MemberRigidCovT E n) (hRec : MemberRecCovT E n) :
    ConstCovClauseT E n :=
  (constCovClauseT_iff_bot hW n).mpr (constCovBotClauseT_of_arms hDelta hRigid hRec)

/-- Concrete `HasTyT` and `ConvT.eta` witnesses on `natEnvU` (`natEnvUWfT`). -/
def hasTyT_natEnvU_nat (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ (.const 0 []) (.sort (.succ .zero)) :=
  .const Γ 0 [] natFamMember rfl rfl rfl

def hasTyT_natEnvU_zero (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ (.const 1 []) (.const 0 []) :=
  .const Γ 1 [] natZeroMember rfl rfl rfl

def hasTyT_natEnvU_succ (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  .const Γ 2 [] natSuccMember rfl rfl rfl

def convT_eta_natSucc (n : Nat) (Γ : LCtx) :
    ConvT natEnvU n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 [])
      (.pi (.const 0 []) (.const 0 [])) :=
  .eta Γ (.const 2 []) (.const 0 []) (.const 0 []) (hasTyT_natEnvU_succ n Γ)

def hasTyT_natEnvU_rec (Γ : LCtx) :
    HasTyT natEnvU 1 Γ (.const 3 [.succ .zero])
      (instantiateLevels [.succ .zero] natRecMemberU.mtype) :=
  .const Γ 3 [.succ .zero] natRecMemberU rfl rfl rfl

/-- **Refutation of `MemberRigidCovT` on `natEnvU` (`not_memberRigidCovT_natEnvU`)**:
    completes the concrete rigid-const counterexample (`Nat.succ = .const 2 [] : Nat → Nat`). -/
theorem not_memberRigidCovT_natEnvU (n : Nat) : ¬ MemberRigidCovT natEnvU n := by
  intro hRigid
  have h := hRigid (r := 2) (ls := []) (m := natSuccMember) rfl rfl rfl
    rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ
  exact not_elTCov_natSucc_spine EnvT.bot h

/-- **Refutation of `MemberRecCovT` on `natEnvU` (`not_memberRecCovT_natEnvU`)**:
    `ApproxT.recursor` on `covWNatSucc` produces `covBadRecCpt`, which is not in `ElTCov`
    (`not_elTCov_natRec_covBadRecCpt`), mirroring `#7737`'s `not_memberRecDiagT_natEnvU` on `CTyCov`. -/
theorem not_memberRecCovT_natEnvU : ¬ MemberRecCovT natEnvU 1 := by
  intro hRec
  have hschema :
      ApproxT natEnvU
        (EnvT.pushArgs (([[], [], [covBadHsCpt]] ++ [[covBadSpine]]).map demandT) EnvT.bot)
        (instantiateLevels [.succ .zero] covWNatSucc.schema) covBadSpine := by
    let ρpush := EnvT.pushArgs (([[], [], [covBadHsCpt]] ++ [[covBadSpine]]).map demandT) EnvT.bot
    have h1 : ApproxT natEnvU ρpush (.bvar 1) covBadHsCpt :=
      .bvar (List.mem_singleton.mpr rfl)
    have h0 : ApproxT natEnvU ρpush (.bvar 0) covBadSpine :=
      .bvar (List.mem_singleton.mpr rfl)
    have happ1 : ApproxT natEnvU ρpush (.app (.bvar 1) (.bvar 0)) (.lam [([], covBadSpine)]) :=
      .app h1 (List.mem_singleton.mpr rfl) (fun u hu => by
        rcases List.mem_singleton.mp hu with rfl; exact h0)
    exact .app happ1 (List.mem_singleton.mpr rfl) (fun _ hu => (List.not_mem_nil _ hu).elim)
  have h := (hRec (w := covWNatSucc) (ls := [.succ .zero]) (m := natRecMemberU) rfl rfl rfl).1
    not_propFamilyS_covWNatSucc rfl rfl hschema
  exact not_elTCov_natRec_covBadRecCpt EnvT.bot h

theorem not_constCovClauseT_natEnvU (n : Nat) : ¬ ConstCovClauseT natEnvU n := by
  intro hConst
  have h := hConst (r := 2) (ls := []) (m := natSuccMember) rfl rfl rfl
    EnvT.bot (.spine 2 []) (approxT_natSucc_spine EnvT.bot)
  exact not_elTCov_natSucc_spine EnvT.bot h

theorem not_constCovClauseT_natEnvU_via_rec : ¬ ConstCovClauseT natEnvU 1 := by
  intro hConst
  have h := hConst (r := 3) (ls := [.succ .zero]) (m := natRecMemberU) rfl rfl rfl
    EnvT.bot covBadRecCpt (approxT_natRec_covBadRecCpt EnvT.bot)
  exact not_elTCov_natRec_covBadRecCpt EnvT.bot h

theorem not_typingLemmaEnvCovT_natEnvU (n : Nat) : ¬ TypingLemmaEnvCovT natEnvU n := by
  intro hTy
  have h := hTy (hasTyT_natEnvU_succ n []) (envTypedCovAtT_nil natEnvU EnvT.bot)
    (.spine 2 []) (approxT_natSucc_spine EnvT.bot)
  exact not_elTCov_natSucc_spine EnvT.bot h

theorem not_typingLemmaEnvCovT_natEnvU_via_rec : ¬ TypingLemmaEnvCovT natEnvU 1 := by
  intro hTy
  have h := hTy (hasTyT_natEnvU_rec []) (envTypedCovAtT_nil natEnvU EnvT.bot)
    covBadRecCpt (approxT_natRec_covBadRecCpt EnvT.bot)
  exact not_elTCov_natRec_covBadRecCpt EnvT.bot h

theorem not_convSoundEnvCovT_natEnvU (n : Nat) : ¬ ConvSoundEnvCovT natEnvU n := by
  intro hConv
  exact not_semEqT_eta_natSucc EnvT.bot
    (hConv (convT_eta_natSucc n []) (envTypedCovAtT_nil natEnvU EnvT.bot))

#print axioms TypingFin.ArgTypedFinAt
#print axioms TypingFin.ModelBetaExpandTypedFin
#print axioms TypingFin.argTypedFinAt_of_argTypedAt
#print axioms TypingFin.not_argTypedFinAt_cex
#print axioms TypingFin.modelBetaExpandTyped_of_fin
#print axioms TypingFin.EnvTypedFinAtT
#print axioms TypingFin.TypingLemmaEnvFinT
#print axioms TypingFin.ArgTypedFinAtM
#print axioms TypingFin.ModelBetaExpandTypedM
#print axioms TypingFin.modelBetaExpandTypedM_iff_fin
#print axioms TypingFin.ModelIotaStepT
#print axioms TypingFin.ReadbackIotaStepT
#print axioms TypingFin.readbackIotaStepT_whStepCtx
#print axioms TypingFin.modelIotaStepT_of_iotaSoundT
#print axioms TypingFin.sortCode_succ
#print axioms TypingFin.cexPolyId
#print axioms TypingFin.cexPolyIdTy
#print axioms hasTyT_cexPolyId
#print axioms polyIdDom1
#print axioms polyIdWitness1
#print axioms polyIdOut0
#print axioms polyIdOut1
#print axioms polyIdCpt0
#print axioms polyIdCpt1
#print axioms polyIdCpt01
#print axioms tyCodeCT_polyIdDom1
#print axioms not_isPropCT_polyIdDom1
#print axioms ctyS_prop_sort
#print axioms ctyS_sort_sort
#print axioms ctyS_polyIdDom1_sort
#print axioms ctyS_polyIdWitness1_polyIdDom1
#print axioms approxT_polyIdOut0
#print axioms approxT_polyIdOut1
#print axioms approxT_cexPolyId_cpt0
#print axioms approxT_cexPolyId_cpt1
#print axioms approxT_cexPolyId_cpt01
#print axioms not_ctyT_polyIdOut1_of_sub_sort
#print axioms not_ctyS_polyIdOut1_of_sub_sort
#print axioms not_elT_polyId_cpt01
#print axioms not_joint_ctyS_polyId_cpt0_cpt1
#print axioms not_argTypedFinAt_polyId
#print axioms TypingFin.not_argTypedAt_polyId
#print axioms not_typingLemmaT
#print axioms not_typingLemmaEnvT
#print axioms envTypedFinAtT_nil
#print axioms not_typingLemmaEnvFinT
#print axioms polyIdVarCtx
#print axioms polyIdVarEnv
#print axioms idOnVar
#print axioms idOnVarTy
#print axioms hasTyT_idOnVar
#print axioms envTypedFinAtT_polyIdVarEnv
#print axioms approxT_idOnVar_polyIdOut0
#print axioms approxT_idOnVar_polyIdOut1
#print axioms not_joint_ctyT_idOnVar
#print axioms not_ctyT_spine_of_approxT_pi
#print axioms not_elT_spine_pi
#print axioms not_semEqT_eta_rigidConst
#print axioms idSort1
#print axioms idSort1Ty
#print axioms idSort1TySort
#print axioms letSort1Ctx
#print axioms hasTyT_idSort1_bvar0
#print axioms envTypedFinAtT_bot
#print axioms approxT_idSort1_polyIdOut0
#print axioms not_typingLemmaEnvFinT_letBinding
#print axioms not_typingLemmaEnvFinT_via_letBinding
#print axioms CTyCov
#print axioms ctyCov_bot_inv
#print axioms ctyCov_prop_inv
#print axioms ctyCov_sort_inv
#print axioms ctyCov_lam_inv
#print axioms ctyCov_pi_inv
#print axioms ctyCov_spine_inv
#print axioms ctyCov_bot
#print axioms ctyCov_of_ctyS
#print axioms ctyCov_prop_bot
#print axioms ctyCov_pi_mono_steps
#print axioms ElTCov
#print axioms elTCov_of_elT
#print axioms elTCov_bot
#print axioms not_ctyCov_spine_of_approxT_pi
#print axioms not_elTCov_spine_pi
#print axioms polyIdTyCod0
#print axioms polyIdTyCod1
#print axioms polyIdTyCpt01
#print axioms approxT_polyIdTyCod0
#print axioms approxT_polyIdTyCod1
#print axioms approxT_cexPolyIdTy_cpt01
#print axioms ctyS_polyIdOut1_polyIdTyCod1
#print axioms not_isPropCT_polyIdTyCpt01
#print axioms ctyCov_polyIdCpt01_polyIdTyCpt01
#print axioms elTCov_polyId_cpt01
#print axioms joint_ctyCov_polyId_cpt0_cpt1
#print axioms relSubstAtT_cons_pointwise
#print axioms TypingFin.ModelSubstFactorT
#print axioms modelBetaExpandTypedM_of_substFactor
#print axioms fundT_beta_pointwise
#print axioms split_bot_list
#print axioms CtxEnvM
#print axioms ConvSoundEnvFinT
#print axioms TypingLemmaEnvFinCtxT
#print axioms IHBelowTypingFin
#print axioms beta_expand_of_ih_and_modelBetaExpandTypedM
#print axioms TypingFinCases
#print axioms typingFin_step
#print axioms typingFin_strong
#print axioms typingLemmaEnvFin_and_convSound_of_cases
#print axioms typingLemmaEnvFinT_of_cases
#print axioms ctxModelT_botOnly
#print axioms ctxModelTLaws'_botOnly
#print axioms modelSubstFactorT_botOnly
#print axioms modelBetaExpandTypedM_botOnly
#print axioms modelIotaStepT_botOnly
#print axioms typingFinCases_botOnly
#print axioms typingLemmaEnvFinT_botOnly
#print axioms EnvTypedCovAtT
#print axioms TypingLemmaEnvCovT
#print axioms ConvSoundEnvCovT
#print axioms envTypedCovAtT_nil
#print axioms envTypedCovAtT_cons_assumption
#print axioms tyCodeCT_of_elTCov_sort
#print axioms isPropCT_of_elTCov_sort_prop
#print axioms eqN_zero_of_imax_eqN_zero
#print axioms sortCode_v_prop_of_imax_prop
#print axioms exists_cod_steps_of_lam_steps
#print axioms covTyping_sort
#print axioms covTyping_bvar
#print axioms covTyping_pi
#print axioms covTyping_lam
#print axioms covTyping_lit
#print axioms covTyping_conv
#print axioms covConv_sorts
#print axioms covConv_lit
#print axioms covConv_irr
#print axioms EnvT.updateAt
#print axioms EnvT.le_updateAt_of_sub
#print axioms EnvT.le_updateAt_cons
#print axioms collect_fin_lists
#print axioms approxT_fin_at
#print axioms approxT_cons_iff_exists_demandT
#print axioms covApproxT_subst0_iff
#print axioms covModelSubstFactorT_approxT
#print axioms modelBetaExpandTypedM_approxT
#print axioms modelBetaExpandTypedFin_approxT
#print axioms approxT_letE_iff
#print axioms semEqT_letE_app_lam
#print axioms envTypedCovAtT_cons_letBinding
#print axioms covTyping_app
#print axioms covTyping_letE
#print axioms covConv_app
#print axioms covConv_lam
#print axioms covConv_pi
#print axioms ExprEqN
#print axioms exprEqN_refl
#print axioms exprEqN_instantiateLevels
#print axioms approxT_of_exprEqN
#print axioms covConv_consts
#print axioms approxT_delta_const_inv_cov
#print axioms approxT_closedAt_env_cov
#print axioms approxT_closed0_env_cov
#print axioms covConv_delta
#print axioms covConv_beta_fwd
#print axioms covConv_zeta_fwd
#print axioms cptT_eq_bot_or_ne_bot
#print axioms covConv_beta_of_argTypedFinAt
#print axioms covConv_zeta_of_argTypedFinAt
#print axioms covConv_letE_of_zeta
#print axioms approxT_idSort1Ty_polyIdDom1
#print axioms elTCov_idSort1Ty_sort
#print axioms envTypedCovAtT_letSort1Ctx
#print axioms elTCov_polyIdOut0_bvar0_ctxEnvT
#print axioms elTCov_idSort1_bvar0_ctxEnvT
#print axioms letSort1
#print axioms hasTyT_letSort1
#print axioms convT_zeta_letSort1
#print axioms semEqT_zeta_letSort1
#print axioms elTCov_letSort1
#print axioms letIdSort1
#print axioms approxT_letIdSort1_polyIdOut0
#print axioms elTCov_letIdSort1
#print axioms IHBelowCov
#print axioms CovModelCases
#print axioms covTyping_step
#print axioms covTyping_strong
#print axioms typingLemmaEnvCovT_and_convSound_of_cases
#print axioms covTyping_step_approxT
#print axioms covTyping_strong_approxT
#print axioms typingLemmaEnvCovT_and_convSound_of_cases_approxT
#print axioms rigidConst_natEnvU_nat
#print axioms not_propCtorT_natEnvU_nat
#print axioms rigidConst_natEnvU_zero
#print axioms not_propCtorT_natEnvU_zero
#print axioms rigidConst_natEnvU_succ
#print axioms not_propCtorT_natEnvU_succ
#print axioms not_isPropCT_natEnvU_nat_spine
#print axioms elT_natEnvU_nat
#print axioms elTCov_natEnvU_nat
#print axioms elT_natEnvU_zero
#print axioms elTCov_natEnvU_zero
#print axioms approxT_natSucc_spine
#print axioms not_elTCov_natSucc_spine
#print axioms not_semEqT_eta_natSucc
#print axioms covNatSuccSchema
#print axioms covWNatSucc
#print axioms not_propFamilyS_covWNatSucc
#print axioms instantiateLevels_natRecMemberU_mtype
#print axioms elTCov_lam_singleton_pi_inv
#print axioms covBadSpine
#print axioms covBadHsCpt
#print axioms covBadRecCpt
#print axioms approxT_natRec_covBadRecCpt
#print axioms not_elTCov_natRec_covBadRecCpt
#print axioms not_elT_natRec_covBadRecCpt
#print axioms covGoodMotiveCpt
#print axioms covGoodHsCpt
#print axioms covGoodRecCpt
#print axioms approxT_natRec_covGoodRecCpt
#print axioms ctyS_lam_singleton
#print axioms not_isPropCT_pi_singleton
#print axioms elT_natRec_covGoodRecCpt
#print axioms elTCov_natRec_covGoodRecCpt
#print axioms ConstCovClauseT
#print axioms covTyping_const
#print axioms elTCov_closed0_env
#print axioms elT_closed0_env
#print axioms groupMembersT_mtype_closed
#print axioms envWfT_member_mtype_closed
#print axioms ConstCovBotClauseT
#print axioms constCovClauseT_iff_bot
#print axioms MemberDeltaCovT
#print axioms MemberRigidCovT
#print axioms MemberRecCovT
#print axioms constCovBotClauseT_of_arms
#print axioms constCovClauseT_of_arms
#print axioms hasTyT_natEnvU_nat
#print axioms hasTyT_natEnvU_zero
#print axioms hasTyT_natEnvU_succ
#print axioms convT_eta_natSucc
#print axioms hasTyT_natEnvU_rec
#print axioms not_memberRigidCovT_natEnvU
#print axioms not_memberRecCovT_natEnvU
#print axioms not_constCovClauseT_natEnvU
#print axioms not_constCovClauseT_natEnvU_via_rec
#print axioms not_typingLemmaEnvCovT_natEnvU
#print axioms not_typingLemmaEnvCovT_natEnvU_via_rec
#print axioms not_convSoundEnvCovT_natEnvU

end Rcic.Declarative.NativeValleys.TypedModelAudit

