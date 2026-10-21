import rcic.RcicNativeTypedModelProbe
import rcic.RcicNativeTypedModelTypingFin

/-!
# RcicNativeTypedModelBeta — the β link re-closed from the typed, finite-joint model law

Item 2.3.  The raw `ModelBetaExpandT` premise of segment 9's `beta` case is unsatisfiable at
`ctxModelT_approxT` (#7721); segment 10's `ModelBetaExpandTyped` restricts it to arguments whose
compacts are jointly typed at ONE code — a restriction the `ArgTypedAt` hypothesis cannot meet
for polymorphic arguments (`TypingFin.not_argTypedAt_polyId`).  The finite-joint restatement
(`TypingFin.ArgTypedFinAt`/`TypingFin.ModelBetaExpandTypedFin`) is the form a typing lemma supplies, and
is tested at #7721's counterexample first (`TypingFin.not_argTypedFinAt_cex`: still excluded; the raw
conclusion stays refuted there).

**Where the typing lemma enters — a design finding.**  The plan's `FundTyAtTyped` motive bundles
the environment typing into the IH package; but the β case's left branch applies the body's IH at
the `cons`-extended environments, and the extended package's right-environment field has **no
supplier**: it needs a `ρ'`-code of the binder's type typing the λ-step's demand list, and the
left branch's data (all from the `ρ`-side: the λ's own step code) determines none.  So the motive
here keeps the landed `FundTyAt`/`FundConvAt` (T-packages) for the IHs, and the environment
typing enters **at the case's own environments, per application** (`FundConvAtTyped` below):
the β case's `hβ`-premise is fed by `hTL harg hE'` at the redex's right environment — which the
`cons`-extension never touches.  The same per-application shape is what `symm`/`tyConv`/`trans`
consume (`typingAt_of_typedPackageFin`, the `TypingAt` supplier).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the model-side finite-joint law -/

/-- Finite-joint argument typing at a model (`M.Ap` for `ApproxT`). -/
def ArgTypedFinAtM (M : CtxModelT E) (ρ : EnvT) (arg A : Expr Nat) : Prop :=
  ∀ us : List CptT, (∀ u ∈ us, M.Ap ρ arg u) → ∃ a, M.Ap ρ A a ∧ ∀ u ∈ us, CTyS E u a

/-- **Typed β expansion for a model**, finite-joint form — the premise swe-zeta is asked to
    supply (retargeted; tell it this shape). -/
def ModelBetaExpandTypedM (M : CtxModelT E) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, ArgTypedFinAtM M ρ arg A →
    M.Ap ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), M.Ap ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c

/-- At the canonical model the two finite-joint laws are the same statement. -/
theorem modelBetaExpandTypedM_iff_fin :
    ModelBetaExpandTypedM (ctxModelT_approxT E) ↔ TypingFin.ModelBetaExpandTypedFin E := by
  constructor
  · intro h ρ A arg body c hT hc; exact h hT hc
  · intro h ρ A arg body c hT hc; exact h hT hc

/-! ### §2 — the typed-package motive: environment typing per application -/

/-- `FundTyAt` with the environments typed along `Γ` (finite-joint) — the environment typing is
    a per-application premise, never extended under binders (see the module header). -/
def FundTyAtTyped (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    TypingFin.EnvTypedFinAtT M Γ ρ → TypingFin.EnvTypedFinAtT M Γ ρ' →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c → LRSCoreS R E n Δ (substT σ e) (substT σ' e) (substT σ A) c

/-- `FundConvAt` with the environments typed along `Γ` (finite-joint). -/
def FundConvAtTyped (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    TypingFin.EnvTypedFinAtT M Γ ρ → TypingFin.EnvTypedFinAtT M Γ ρ' →
    ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c → LRSCoreS R E n Δ (substT σ a) (substT σ' b) (substT σ A) c

/-! ### §3 — the β re-close -/

/-- **`beta` (conversion side), from the typed, finite-joint law.**  `fundT_beta`'s proof
    verbatim — the left (structural) branch untouched, the IHs at the landed T-package motive —
    except the right-compact branch: the model's β law is applied with its finite-joint premise
    fed by the generalised typing lemma at the redex's right environment. -/
theorem fundT_beta_typed (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hβ : ModelBetaExpandTypedM M)
    (hTL : TypingFin.TypingLemmaEnvFinT M n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (harg : HasTyT E n Γ arg A)
    (ihA : FundTyAt M R n Γ A (.sort u)) (ihb : FundTyAt M R n (.assumption A :: Γ) body B)
    (iharg : FundTyAt M R n Γ arg A) :
    FundConvAtTyped M R n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) := by
  intro Δ ρ ρ' σ σ' hΔ hS hE hE' c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAσ⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hcS
  obtain ⟨hargσ⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT
  obtain ⟨hargσ'⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT'
  obtain ⟨hargc⟩ := convT_substT_pointwise hW hcl hst hι hΓ harg hΔ hT hT' hcS
  have hargσ'A : HasTyT E n Δ (substT σ' arg) (substT σ A) := .conv _ _ _ _ u hargσ' (.symm _ _ _ _ hAc)
  -- from a domain code and a realised, typed demand, the conclusion
  have finish : ∀ (a : CptT) (us : List CptT), (M.Ap ρ A a ∨ M.Ap ρ' A a) → (∀ v ∈ us, CTyS E v a) →
      (∀ v ∈ us, M.Ap ρ arg v ∨ M.Ap ρ' arg v) →
      (M.Ap (EnvT.cons (demandT us) ρ) body c ∨ M.Ap (EnvT.cons (demandT us) ρ') body c) →
      LRSCoreS R E n Δ (substT σ (.app (.lam A body) arg)) (substT σ' (instantiate0 arg body))
        (substT σ (instantiate0 arg B)) c := by
    intro a us ha hdT hus hb
    obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha
    have hrel : ∀ v ∈ us, LRSCoreS R E n Δ (substT σ arg) (substT σ' arg) (substT σ A) v :=
      fun v hv => iharg hΔ hS v (hus v hv)
    have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM hΔ hS A u us hdT hAA' hAA hAc
      (substT σ arg) (substT σ' arg) hargσ hargσ'A hargc hrel
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
        exact finish a s.1 (Or.inl ha) hdT (fun v hv => Or.inl (hau v hv)) (Or.inl hb)
    · rcases hM.lam_inv hfg with h0 | ⟨_, _, e, _⟩
      · exact CptT.noConfusion h0
      · exact CptT.noConfusion e
  · obtain ⟨a, us, ha, hdT, hus, hb⟩ :=
      hβ (A := A) (fun us' hus' => hTL harg hE' us' hus') hc
    exact finish a us (Or.inr ha) hdT (fun v hv => Or.inr (hus v hv)) (Or.inr hb)

/-! ### §4 — the typing-lemma suppliers at the case level -/

/-- With the finite-joint package, segment 9's `TypingAt` input (`symm`/`tyConv`/`trans`) is the
    generalised typing lemma's conclusion at the two environments — the finite-joint form of
    Probe's `typingAt_of_typedPackage`. -/
theorem typingAt_of_typedPackageFin {M : CtxModelT E} (hTL : TypingFin.TypingLemmaEnvFinT M n)
    {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hE : TypingFin.EnvTypedFinAtT M Γ ρ) (hE' : TypingFin.EnvTypedFinAtT M Γ ρ')
    {a b A : Expr Nat} (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A) :
    TypingAt M ρ ρ' a b A := by
  intro c hc
  rcases hc with hc | hc
  · obtain ⟨a₀, hA, hty⟩ := hTL ha hE [c] (fun u hu => by
      rcases List.mem_singleton.mp hu with rfl; exact hc)
    exact ⟨a₀, Or.inl hA, hty c (List.mem_singleton.mpr rfl)⟩
  · obtain ⟨a₀, hA, hty⟩ := hTL hb hE' [c] (fun u hu => by
      rcases List.mem_singleton.mp hu with rfl; exact hc)
    exact ⟨a₀, Or.inr hA, hty c (List.mem_singleton.mpr rfl)⟩

-- BEGIN GLM FUND BETA ROOTS
#print axioms ArgTypedFinAtM
#print axioms ModelBetaExpandTypedM
#print axioms modelBetaExpandTypedM_iff_fin
#print axioms FundTyAtTyped
#print axioms FundConvAtTyped
#print axioms fundT_beta_typed
#print axioms typingAt_of_typedPackageFin
-- END GLM FUND BETA ROOTS

end Rcic.Declarative.NativeValleys.TypedModelAudit
