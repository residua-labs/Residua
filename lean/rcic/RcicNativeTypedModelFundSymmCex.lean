import rcic.RcicNativeTypedModelProbe

/-!
# `RcicNativeTypedModelFundSymmCex` — sealed record: the #7731 conversion-field inputs are
false at `ctxModelT_approxT`

The #7731 lane (`RcicNativeTypedModelFundTrans`, deleted) proved `FundCases.trans`,
`FundCases.tyConv`, `FundCases.symmTyping` at the exact field types under named premises.
Audit lane 6 kernel-refuted every named input at `ctxModelT_approxT`; this module is the
sealed record of those refutations (the auditor's reproducer verbatim, checked at `f0fff0dd16`).

The refuted statements are kept as named `Prop`s — they are the exact shapes the re-founded
typed relation (with escape) must make satisfiable:

- `TypingInputT` — the typing lemma in related-substitution form (`not_typingInputT_approxT`).
  It is `FundCases.symmTyping` up to `ConvT.symm`, so `FundCases` itself is uninhabitable at
  `ApproxT` (`not_fundCases_approxT`). Cause: `RelSubstAtT` only constrains *relatedness* — an
  environment may assign `badPiCpt = .pi .bot [([.prop], .prop)]`, which `LRSCoreS` relates at a
  sort index because its `.pi` clause's per-step demands are vacuously unmet, while `CTyS`
  gives it no code.
- `EnvTypingOfRelSubstT` — "a `RelSubstAtT` package's environments are `EnvTypedAtT`"
  (`not_envTypingOfRelSubstT_approxT`, and even at the degenerate model
  `not_envTypingOfRelSubstT_bot`) — the same cause.
- `ModelConvSoundT` — conversion denotation-invariance at a fixed environment
  (`not_modelConvSoundT_approxT` at a let-bound variable; `not_modelConvSoundAt_closed_beta`
  at a closed β-redex even under `CtxEnvT` + `EnvTypedAtT` guards): `ApproxT`'s lam-step
  semantics does not preserve denotation across `ConvT.beta`. This removes the `trans` route
  the handoff prescribed, which is why `fundT_trans`/`fundT_tyConv` are deleted rather than
  kept — both consumed `TypingInputT` (the `CTyS` obligations of `irrel`/`symm_tm`/`trans_tm`)
  and `ModelConvSoundT`.
- `TypingLemmaEnvT` at `ctxModelT_approxT` is likewise refuted
  (`not_typingLemmaEnvT_approxT`): `cexTerm`'s compact `cexCpt` is not `CTyS`-typed at any
  `ApproxT` code of `cexType`.

`closure_claim = 0`. Nothing here is consumed downstream; each `not_*` names exactly what the
re-founded relation must turn satisfiable.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### the refuted statements (formerly `RcicNativeTypedModelFundTrans`, #7731) -/

/-- **Refuted** (`not_typingInputT_approxT`): the typing lemma in related-substitution form. -/
def TypingInputT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b A : Expr Nat}, ConvT E n Γ a b A → CtxWfT E n Γ →
    ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      RelSubstAtT M R n Δ ρ ρ' σ σ' Γ → TypingAt M ρ ρ' a b A

/-- **Refuted** (`not_modelConvSoundT_approxT`, `not_modelConvSoundAt_closed_beta`): a typed
conversion `a ≡ b` is denotation-invariant at a fixed environment. -/
def ModelConvSoundT (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b A : Expr Nat}, ConvT E n Γ a b A → CtxWfT E n Γ →
    ∀ (ρ : EnvT), ModelConvSoundAt M ρ a b

/-- **Refuted** (`not_envTypingOfRelSubstT_approxT`, `_bot`): a `RelSubstAtT` package's two
environments are typed along `Γ`. -/
def EnvTypingOfRelSubstT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ → EnvTypedAtT M Γ ρ ∧ EnvTypedAtT M Γ ρ'

/-- The `⊥`-only model; `not_envTypingOfRelSubstT_bot` refutes the bridge there too. -/
def botModelT (E : ResolvedEnv) : CtxModelT E := ⟨fun _ _ c => c = .bot⟩

/-! ### the kernel-checked reproducer (audit lane 6, verbatim) -/

def badPiCpt : CptT := .pi .bot [([.prop], .prop)]
def idPiPropExpr : Expr Nat := .pi (.sort .zero) (.bvar 0)
def propImax : Level := .imax (.succ .zero) .zero

theorem sortCode_propImax : sortCode propImax = .prop :=
  (sortCode_eq_prop_iff propImax).mpr (fun _ => rfl)

theorem not_isPropCT_badPiCpt (E : ResolvedEnv) : ¬ IsPropCT E badPiCpt := by
  intro h
  cases h with
  | pi _ hg => exact not_isPropCT_prop E (hg ([.prop], .prop) (List.mem_singleton.mpr rfl))

theorem not_ctyS_badPiCpt_sort_propImax (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ∃ a₀, ApproxT E ρ (.sort propImax) a₀ ∧ CTyS E badPiCpt a₀ := by
  rintro ⟨a₀, ha₀, hty⟩
  rcases approxT_sort_inv ha₀ with rfl | rfl
  · exact CptT.noConfusion (ctyS_bot_inv hty)
  · rw [sortCode_propImax] at hty
    rcases ctyS_prop_inv hty with h0 | hp
    · exact CptT.noConfusion h0
    · exact not_isPropCT_badPiCpt E hp

theorem lrSCoreS_idPiProp_badPiCpt (R : Readback) (E : ResolvedEnv) (n : Nat) :
    LRSCoreS R E n [] idPiPropExpr idPiPropExpr (.sort propImax) badPiCpt := by
  rw [LRSCoreS.eq_def]
  refine ⟨⟨propImax, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0, .refl _, .refl _,
    ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, lrSCoreS_bot _ _ _ _⟩, ?_⟩
  intro s hs hdom
  have hs' : s = ([.prop], .prop) := List.mem_singleton.mp hs
  subst hs'
  have hbad : CTyS E .prop .bot := hdom .prop (List.mem_singleton.mpr rfl)
  exact CptT.noConfusion (ctyS_bot_inv hbad)

def badCtx : LCtx := [.assumption (.sort propImax)]
def badEnv : EnvT := fun _ c => c = badPiCpt
def badSubst : SubstT := fun _ => idPiPropExpr

def hasTyT_idPiProp (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] idPiPropExpr (.sort propImax) :=
  .pi [] (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort [] .zero)
    (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)

theorem relSubstAtT_bad {E : ResolvedEnv} (M : CtxModelT E) (R : Readback) (n : Nat) :
    RelSubstAtT M R n [] badEnv badEnv badSubst badSubst badCtx := by
  have hty : TypedSubstT E n [] badSubst badCtx := by
    refine ⟨fun i A hA => ?_, fun i v hv => ?_⟩
    · cases i with
      | zero =>
          simp [badCtx, lookupType, lift] at hA
          subst hA
          exact ⟨by simpa [badSubst, substT] using hasTyT_idPiProp E n⟩
      | succ i => simp [badCtx, lookupType] at hA
    · cases i <;> simp [badCtx, lookupValue] at hv
  refine ⟨hty, hty, ?_, ?_, ?_⟩
  · intro i A hA
    cases i with
    | zero =>
        simp [badCtx, lookupType, lift] at hA
        subst hA
        exact ⟨.refl _ _ _ (by simpa [badSubst, substT] using hasTyT_idPiProp E n)⟩
    | succ i => simp [badCtx, lookupType] at hA
  · intro i A hA c hc
    cases i with
    | zero =>
        simp [badCtx, lookupType, lift] at hA
        subst hA
        have hc' : c = badPiCpt := hc.elim id id
        subst hc'
        have hrel := lrSCoreS_idPiProp_badPiCpt R E n
        simpa [badSubst, substT] using And.intro hrel (And.intro hrel (And.intro hrel hrel))
    | succ i => simp [badCtx, lookupType] at hA
  · intro i v A hv
    cases i <;> simp [badCtx, lookupValue] at hv

theorem not_envTypingOfRelSubstT_approxT (E : ResolvedEnv) (R : Readback) (n : Nat) :
    ¬ EnvTypingOfRelSubstT (ctxModelT_approxT E) R n := by
  intro hET
  have h := (hET (relSubstAtT_bad (ctxModelT_approxT E) R n)).1
  obtain ⟨a₀, ha₀, hty⟩ := h 0 (.sort propImax) rfl badPiCpt rfl
  exact not_ctyS_badPiCpt_sort_propImax E badEnv ⟨a₀, ha₀, hty⟩

theorem not_envTypingOfRelSubstT_bot (E : ResolvedEnv) (R : Readback) (n : Nat) :
    ¬ EnvTypingOfRelSubstT (botModelT E) R n := by
  intro hET
  have h := (hET (relSubstAtT_bad (botModelT E) R n)).1
  obtain ⟨a₀, ha₀, hty⟩ := h 0 (.sort propImax) rfl badPiCpt rfl
  have ha₀' : a₀ = .bot := ha₀
  subst ha₀'
  exact CptT.noConfusion (ctyS_bot_inv hty)

theorem not_typingInputT_approxT (E : ResolvedEnv) (R : Readback) (n : Nat) :
    ¬ TypingInputT (ctxModelT_approxT E) R n := by
  intro hTI
  have hΓ : CtxWfT E n badCtx := .assumption [] (.sort propImax) (.succ propImax) .nil (.sort [] propImax)
  have hbvar : HasTyT E n badCtx (.bvar 0) (.sort propImax) := .bvar badCtx 0 (.sort propImax) rfl
  have hconv : ConvT E n badCtx (.bvar 0) (.bvar 0) (.sort propImax) := .refl badCtx (.bvar 0) (.sort propImax) hbvar
  have hTy := hTI hconv hΓ (relSubstAtT_bad (ctxModelT_approxT E) R n)
    badPiCpt (Or.inl (.bvar (ρ := badEnv) (i := 0) (c := badPiCpt) rfl))
  rcases hTy with ⟨a₀, ha₀ | ha₀, hcty⟩
  · exact not_ctyS_badPiCpt_sort_propImax E badEnv ⟨a₀, ha₀, hcty⟩
  · exact not_ctyS_badPiCpt_sort_propImax E badEnv ⟨a₀, ha₀, hcty⟩

theorem not_fundCases_approxT (E : ResolvedEnv) (R : Readback) (n : Nat) :
    ¬ FundCases (ctxModelT_approxT E) R n := by
  intro hFC
  have hΓ : CtxWfT E n badCtx := .assumption [] (.sort propImax) (.succ propImax) .nil (.sort [] propImax)
  have hbvar : HasTyT E n badCtx (.bvar 0) (.sort propImax) := .bvar badCtx 0 (.sort propImax) rfl
  have hconv : ConvT E n badCtx (.bvar 0) (.bvar 0) (.sort propImax) := .refl badCtx (.bvar 0) (.sort propImax) hbvar
  have hTy := hFC.symmTyping hconv hΓ (relSubstAtT_bad (ctxModelT_approxT E) R n)
    badPiCpt (Or.inl (.bvar (ρ := badEnv) (i := 0) (c := badPiCpt) rfl))
  rcases hTy with ⟨a₀, ha₀ | ha₀, hcty⟩
  · exact not_ctyS_badPiCpt_sort_propImax E badEnv ⟨a₀, ha₀, hcty⟩
  · exact not_ctyS_badPiCpt_sort_propImax E badEnv ⟨a₀, ha₀, hcty⟩

theorem not_modelConvSoundT_approxT (E : ResolvedEnv) (n : Nat) :
    ¬ ModelConvSoundT (ctxModelT_approxT E) n := by
  intro hMS
  let Γ : LCtx := [.letBinding (.sort (.succ .zero)) (.sort .zero)]
  have hA : HasTyT E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort [] (.succ .zero)
  have hv : HasTyT E n [] (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
  have hΓ : CtxWfT E n Γ := .letBinding [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero) .nil hA hv
  have hv' : HasTyT E n Γ (.sort .zero) (.sort (.succ .zero)) := .sort Γ .zero
  have hconv : ConvT E n Γ (.bvar 0) (.sort .zero) (.sort (.succ .zero)) :=
    .zetaLocal Γ 0 (.sort (.succ .zero)) (.sort .zero) rfl rfl hv'
  have hsound := (hMS hconv hΓ EnvT.bot .prop).mpr (by rw [← sortCode_zero]; exact .sort EnvT.bot .zero)
  rcases approxT_bvar_inv hsound with h0 | h0
  · exact CptT.noConfusion h0
  · exact CptT.noConfusion h0

def U1 : Level := .succ .zero
def U2 : Level := .succ U1
theorem sortCode_U1 : sortCode U1 = .sort := rfl

def cexTerm : Expr Nat := .lam (.sort U1) (.lam (.bvar 0) (.sort .zero))
def cexType : Expr Nat := .pi (.sort U1) (.pi (.bvar 0) (.sort U1))

def hasTyT_cexTerm (E : ResolvedEnv) (n : Nat) : HasTyT E n [] cexTerm cexType := by
  have hX : HasTyT E n [] (.sort U1) (.sort U2) := .sort [] U1
  have hb0 : HasTyT E n [.assumption (.sort U1)] (.bvar 0) (.sort U1) :=
    .bvar [.assumption (.sort U1)] 0 (.sort U1) rfl
  have hbody : HasTyT E n [.assumption (.bvar 0), .assumption (.sort U1)] (.sort .zero) (.sort U1) :=
    .sort _ .zero
  have hinner : HasTyT E n [.assumption (.sort U1)] (.lam (.bvar 0) (.sort .zero)) (.pi (.bvar 0) (.sort U1)) :=
    .lam _ (.bvar 0) U1 (.sort .zero) (.sort U1) hb0 hbody
  exact .lam [] (.sort U1) U2 _ _ hX hinner

def inner1 : CptT := .lam [([], .prop)]
def inner2 : CptT := .lam [([.sort], .prop)]
def cexStep1 : List CptT × CptT := ([.prop], inner1)
def cexStep2 : List CptT × CptT := ([.prop, .sort], inner2)
def cexCpt : CptT := .lam [cexStep1, cexStep2]

theorem approxT_cexTerm (E : ResolvedEnv) : ApproxT E EnvT.bot cexTerm cexCpt := by
  refine .lam (a := .sort) (by rw [← sortCode_U1]; exact .sort EnvT.bot U1) ?_ ?_ ?_
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs
    · have hu' : u = .prop := List.mem_singleton.mp hu
      subst hu'
      rw [CTyS]; exact Or.inr .prop
    · have hs' : s = cexStep2 := List.mem_singleton.mp hs
      subst hs'
      rcases List.mem_cons.mp hu with rfl | hu
      · rw [CTyS]; exact Or.inr .prop
      · have hu' : u = .sort := List.mem_singleton.mp hu
        subst hu'
        rw [CTyS]; exact Or.inr .sort
  · exact ⟨cexStep1, List.mem_cons_self _ _, fun h => CptT.noConfusion h⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · refine .lam (a := .bot) (.bot _ _) ?_ ⟨([], .prop), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
      · intro s' hs' v hv
        have hs'' := List.mem_singleton.mp hs'
        subst hs''
        exact (List.not_mem_nil _ hv).elim
      · intro s' hs'
        have hs'' := List.mem_singleton.mp hs'
        subst hs''
        rw [← sortCode_zero]
        exact .sort _ .zero
    · have hs' : s = cexStep2 := List.mem_singleton.mp hs
      subst hs'
      have hXsort : ApproxT E (EnvT.cons (demandT [.prop, .sort]) EnvT.bot) (.bvar 0) .sort :=
        .bvar (List.mem_cons_of_mem CptT.prop (List.mem_singleton.mpr rfl))
      refine .lam (a := .sort) hXsort ?_ ⟨([.sort], .prop), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩ ?_
      · intro s' hs' v hv
        have hs'' := List.mem_singleton.mp hs'
        subst hs''
        have hv' := List.mem_singleton.mp hv
        subst hv'
        rw [CTyS]; exact Or.inr .sort
      · intro s' hs'
        have hs'' := List.mem_singleton.mp hs'
        subst hs''
        rw [← sortCode_zero]
        exact .sort _ .zero

theorem not_ctyS_cexCpt_cexType (E : ResolvedEnv) :
    ¬ ∃ a, ApproxT E EnvT.bot cexType a ∧ CTyS E cexCpt a := by
  rintro ⟨a, hAa, hcty⟩
  rcases approxT_pi_inv hAa with rfl | ⟨a_dom, g, rfl, _, hg⟩
  · exact CptT.noConfusion (ctyS_bot_inv hcty)
  · rcases ctyS_pi_inv hcty with h0 | ⟨f, hf, _, _, hcod, hcov⟩
    · exact CptT.noConfusion h0
    · injection hf with hf; subst hf
      rcases hcov cexStep1 (List.mem_cons_self _ _) with h0 | ⟨t₁, ht₁, hsub₁⟩
      · exact CptT.noConfusion h0
      · have hsub₂ : ∀ v ∈ t₁.1, v ∈ cexStep2.1 := fun v hv => by
          have hv' : v = .prop := List.mem_singleton.mp (hsub₁ v hv)
          subst hv'
          exact List.mem_cons_self _ _
        have hcty2 : CTyS E inner2 t₁.2 :=
          hcod cexStep2 (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) t₁ ht₁ hsub₂
        have ht₁B := (hg t₁ ht₁).2
        rcases approxT_pi_inv ht₁B with hbot | ⟨a_X, g', heq, ha_X, _⟩
        · rw [hbot] at hcty2
          exact CptT.noConfusion (ctyS_bot_inv hcty2)
        · rw [heq] at hcty2
          rcases ctyS_pi_inv hcty2 with h0 | ⟨f', hf', _, hdom', _, _⟩
          · exact CptT.noConfusion h0
          · injection hf' with hf'; subst hf'
            have hsort_aX : CTyS E .sort a_X :=
              hdom' ([.sort], .prop) (List.mem_singleton.mpr rfl) .sort (List.mem_singleton.mpr rfl)
            rcases approxT_bvar_inv ha_X with rfl | hmem
            · exact CptT.noConfusion (ctyS_bot_inv hsort_aX)
            · have haX_prop : a_X = .prop := List.mem_singleton.mp (hsub₁ a_X hmem)
              subst haX_prop
              rcases ctyS_prop_inv hsort_aX with h0 | hp
              · exact CptT.noConfusion h0
              · exact not_isPropCT_sort E hp

theorem not_typingLemmaEnvT_approxT (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaEnvT (ctxModelT_approxT E) n := by
  intro hTL
  exact not_ctyS_cexCpt_cexType E
    (hTL (hasTyT_cexTerm E n) (envTypedAtT_bot (E := E) []) cexCpt (approxT_cexTerm E))

def hasTyT_cexType (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] cexType (.sort (.imax U2 (.imax U1 U2))) := by
  have hX : HasTyT E n [] (.sort U1) (.sort U2) := .sort [] U1
  have hb0 : HasTyT E n [.assumption (.sort U1)] (.bvar 0) (.sort U1) :=
    .bvar [.assumption (.sort U1)] 0 (.sort U1) rfl
  have hcod : HasTyT E n [.assumption (.bvar 0), .assumption (.sort U1)] (.sort U1) (.sort U2) :=
    .sort _ U1
  have hpi : HasTyT E n [.assumption (.sort U1)] (.pi (.bvar 0) (.sort U1)) (.sort (.imax U1 U2)) :=
    .pi _ (.bvar 0) U1 (.sort U1) U2 hb0 hcod
  exact .pi [] (.sort U1) U2 (.pi (.bvar 0) (.sort U1)) (.imax U1 U2) hX hpi

def convT_beta_cex (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] (.app (.lam cexType (.bvar 0)) cexTerm) cexTerm cexType := by
  have hbody : HasTyT E n [.assumption cexType] (.bvar 0) (lift 0 1 cexType) :=
    .bvar [.assumption cexType] 0 (lift 0 1 cexType) rfl
  exact ConvT.beta [] cexType (.bvar 0) cexTerm (lift 0 1 cexType) (.imax U2 (.imax U1 U2))
    (hasTyT_cexType E n) hbody (hasTyT_cexTerm E n)

theorem not_approxT_beta_redex_cex (E : ResolvedEnv) :
    ¬ ApproxT E EnvT.bot (.app (.lam cexType (.bvar 0)) cexTerm) cexCpt := by
  intro happ
  rcases approxT_app_inv happ with h0 | ⟨g, s, hs2, hlam, hs, _⟩ | ⟨r, args, u, hsp, _, _⟩
  · exact CptT.noConfusion h0
  · rcases approxT_lam_inv hlam with h0 | ⟨a, g', hg', hAa, _, hg⟩
    · exact CptT.noConfusion h0
    · injection hg' with hg'; subst hg'
      obtain ⟨hdom, hb0⟩ := hg s hs
      rw [← hs2] at hb0
      rcases approxT_bvar_inv hb0 with h0 | hmem
      · exact CptT.noConfusion h0
      · exact not_ctyS_cexCpt_cexType E ⟨a, hAa, hdom cexCpt hmem⟩
  · exact CptT.noConfusion hsp

theorem not_modelConvSoundAt_closed_beta (E : ResolvedEnv) (n : Nat) :
    ∃ (a b A : Expr Nat), Nonempty (ConvT E n [] a b A) ∧
      CtxEnvT E [] EnvT.bot ∧ EnvTypedAtT (ctxModelT_approxT E) [] EnvT.bot ∧
      ¬ ModelConvSoundAt (ctxModelT_approxT E) EnvT.bot a b := by
  refine ⟨.app (.lam cexType (.bvar 0)) cexTerm, cexTerm, cexType, ⟨convT_beta_cex E n⟩,
    fun i v h => by simp [lookupValue] at h, envTypedAtT_bot [], ?_⟩
  intro hMS
  exact not_approxT_beta_redex_cex E ((hMS cexCpt).mpr (approxT_cexTerm E))
