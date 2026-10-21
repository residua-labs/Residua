import rcic.RcicNativeFamModelLRS

/-!
# RcicNativeFamModelLRSPER — PER of the relation, the model layer over `ApproxDI`, and the
`piRow ⇐ single links at the probe compacts` reduction

Continues `RcicNativeFamModelLRS` (#7673) under the ruling's three items.

* **§1 The law transitivity needs — unique readback normal forms.**  `NormalUniqueR R` (two
  normal readbacks of one term coincide).  Discharged from exact determinism
  (`normalUniqueR_of_det`) or from the single-step diamond (`normalUniqueR_of_diamond`, via the
  strip lemma and confluence).  `WhStepCtx E` satisfies it under `EnvWfT E`
  (`normalUniqueR_whStepCtx`, from §11's `whDetCtx_of_envWfT`); for `WhStepK`/`WhStepCK` either
  `DetR` or `DiamondR` discharges it (`normalUniqueR_whStepK_of_det`, `_of_diamond`) — the
  interface `devin-desktop/readback-ck`'s determinism/joinability lemma targets.
* **§2 PER on the `BotPiCpt` compacts** (`⊥`, `sort`, Π compacts whose steps all have `⊥`
  demands): `lrSCore_symm_botPiCpt`, `lrSCore_trans_botPiCpt` (and the `LRS` wrappers), from
  `ReadbackLaws`, `NormalUniqueR`, `EnvWfT`, `CtxWfT`; `lrSCore_sort_index_irrel` (the sort
  index is irrelevant).  **Beyond `BotPiCpt` the PER is not structural**: `sort_shape_of_symm_pi`
  proves that symmetry at the one-demand compact `pi ⊥ [([sort], sort)]` already entails
  sort-shape invariance of the readback under conversion (if `A₁ ≡ A₂`, `A₂` reads back to a
  sort with a sort-valued inhabitant, then `A₁` is not stuck) — valley strength, i.e. the
  fundamental lemma's own content.  The mechanism: the substitution-style clause relates
  arguments at the LEFT domain's syntactic index, and transporting that relation across
  `A₁ ≡ A₂` is index transport, which is shape invariance.
* **§3 The model layer.**  `CtxModel` (an approximation relation with a context environment),
  `CtxModelLaws`, instances `ctxModelI` (`ApproxI`, `ctxEnvI`) and `ctxModelDI E` (`ApproxDI E`,
  `ctxEnvDI E` — §11 of `RcicNativeFamModel`, reused, not redefined).  `ReadbackModelInv R M`:
  compacts transfer along steps; `WhStepCtx E` over `ctxModelDI E` has it unconditionally under
  `EnvWfT E` (`readbackModelInv_whStepCtx_DI`, §11), over `ctxModelI` only under the refuted
  `WhApproxInvCore E` — which is why the fundamental lemma lives over `ApproxDI`.  The
  statements of #7673 re-stated over an arbitrary model: `FundamentalLRSTM`, the pointwise
  related-substitution form `RelSubstAt`/`FundamentalSAt` (the inductive strengthening: the
  model environment `ρ` is a parameter, the substituents are realisable at `ρ` and related at
  every compact `ρ` assigns), `FundamentalSM` (full approximation sets) as its instance,
  `FundamentalSCtxM` under `RelSubstIdM`; consumers for both rows.
* **§4 The reduction.**  Compacts transfer across the relation at the probe compacts
  (`modelAt_right_of_lrSCore_probe`: `⊥`, `sort`, `pi ⊥ []` — exactly what `piRow` probes), so
  the chain form at the probes follows from the diagonal and the single links
  (`fundamentalLRSTMProbe_of_links`), and **`piRow` follows from the single-link fundamental
  lemma at `sort` and `pi ⊥ []`** (`piRowField_of_links`).  `trans` of chains is closed here,
  structurally, with no model soundness (point 5 showed it is false) — the transport is the
  relation's own readback plus `ReadbackModelInv`.
* **§5 Structural cases of the single-link lemma**, parametric in model and readback: every
  readback step (`link_of_step`/`link_of_redR`: β, ζ, `zetaLocal`, δ, ι, `lit`, and `WhStepK`'s
  `pmajor`), `refl`, `sorts`, `irr` at a non-universe proposition, `symm` at `BotPiCpt`,
  `ConvT.pi` and the Π diagonal at the probe compact, the `bvar` diagonal (assumption and let),
  and `ConvT.eta` at every λ compact (`link_eta_lam`: the η-expansion's extra compacts are
  ⊥-output steps, where the clause is trivial; the others are compacts of `f` by demand
  monotonicity).

**Not claimed.**  The single-link lemma at the probe compacts for `app`/`letE`/`lam`/`tyConv`/
`consts`/`trans`-beyond-probes, and `FundamentalSAt`'s induction, remain open; their common
obstacle is index transport at the argument position (§2's measurement) — the exact statements
are in the PR body.  `closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.FamModelLRSAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — unique readback normal forms -/

/-- Two normal readbacks of one term coincide. -/
def NormalUniqueR (R : Readback) : Prop :=
  ∀ (Γ : LCtx) {a X Y : Expr Nat}, RedR R Γ a X → NormalR R Γ X → RedR R Γ a Y → NormalR R Γ Y →
    X = Y

/-- Exact determinism of single steps. -/
def DetR (R : Readback) : Prop :=
  ∀ (Γ : LCtx) {a b c : Expr Nat}, R Γ a b → R Γ a c → b = c

/-- The single-step diamond (joinability shape). -/
def DiamondR (R : Readback) : Prop :=
  ∀ (Γ : LCtx) {a b c : Expr Nat}, R Γ a b → R Γ a c → b = c ∨ ∃ d, R Γ b d ∧ R Γ c d

theorem redR_of_normal {Γ : LCtx} {X Y : Expr Nat} (hX : NormalR R Γ X) (h : RedR R Γ X Y) :
    Y = X := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hX _ hs).elim

theorem normalUniqueR_of_det (hdet : DetR R) : NormalUniqueR R := by
  intro Γ a X Y h hX
  induction h with
  | refl =>
      intro h' _
      exact (redR_of_normal hX h').symm
  | step hs _ ih =>
      intro h' hY
      cases h' with
      | refl => exact (hY _ hs).elim
      | step hs' hr' =>
          have e := hdet Γ hs hs'
          subst e
          exact ih hX hr' hY

/-- The strip lemma for a diamond readback. -/
theorem redR_strip (hd : DiamondR R) {Γ : LCtx} {a b c : Expr Nat}
    (hab : R Γ a b) (hac : RedR R Γ a c) : ∃ d, RedR R Γ b d ∧ RedR R Γ c d := by
  induction hac generalizing b with
  | refl => exact ⟨b, .refl _, redR_single hab⟩
  | step hs hr ih =>
      rcases hd _ hab hs with e | ⟨d₁, hbd, hcd⟩
      · subst e; exact ⟨_, hr, .refl _⟩
      · obtain ⟨d₂, h₁, h₂⟩ := ih hcd
        exact ⟨d₂, .step hbd h₁, h₂⟩

theorem redR_confluent (hd : DiamondR R) {Γ : LCtx} {a b c : Expr Nat}
    (hab : RedR R Γ a b) (hac : RedR R Γ a c) : ∃ d, RedR R Γ b d ∧ RedR R Γ c d := by
  induction hab generalizing c with
  | refl => exact ⟨c, hac, .refl _⟩
  | step hs _ ih =>
      obtain ⟨d₁, h₁, h₂⟩ := redR_strip hd hs hac
      obtain ⟨d₂, h₃, h₄⟩ := ih h₁
      exact ⟨d₂, h₃, redR_trans h₂ h₄⟩

theorem normalUniqueR_of_diamond (hd : DiamondR R) : NormalUniqueR R := by
  intro Γ a X Y hX hXn hY hYn
  obtain ⟨d, h₁, h₂⟩ := redR_confluent hd hX hY
  exact (redR_of_normal hXn h₁).symm.trans (redR_of_normal hYn h₂)

theorem detR_whStepCtx (hW : EnvWfT E) : DetR (WhStepCtx E) :=
  fun Γ _ _ _ h₁ h₂ => whDetCtx_of_envWfT hW Γ h₁ h₂

theorem normalUniqueR_whStepCtx (hW : EnvWfT E) : NormalUniqueR (WhStepCtx E) :=
  normalUniqueR_of_det (detR_whStepCtx hW)

/-- The interface for the K-aware readback: exact determinism discharges the law. -/
theorem normalUniqueR_whStepK_of_det (hdet : DetR (WhStepK E n)) : NormalUniqueR (WhStepK E n) :=
  normalUniqueR_of_det hdet

/-- ... and so does the single-step diamond. -/
theorem normalUniqueR_whStepK_of_diamond (hd : DiamondR (WhStepK E n)) :
    NormalUniqueR (WhStepK E n) :=
  normalUniqueR_of_diamond hd

/-! ### §2 — PER on `BotPiCpt` -/

/-- The sort index is irrelevant: at a sort index only `A ↝ Sort` is read, and every sort reads
    back to itself. -/
theorem lrSCore_sort_index_irrel (hL : ReadbackLaws E R) {Γ : LCtx} {M M' : Expr Nat}
    {v v' : Level} : (c : CptI) → LRSCore R E n Γ M M' (.sort v) c → LRSCore R E n Γ M M' (.sort v') c
  | .bot, _ => lrSCore_bot _ _ _ _
  | .sort, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      exact ⟨⟨_, .refl _⟩, h.2⟩
  | .pi a f, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      exact ⟨⟨_, .refl _⟩, h.2⟩
  | .lam g, h => (lrSCore_lam_at_sort_false hL h).elim
  | .spine r args, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      rcases h with ⟨_, hT⟩ | ⟨hns, _⟩
      · exact Or.inl ⟨⟨_, .refl _⟩, hT⟩
      · exact (hns v (.refl _)).elim

/-- Symmetry at `BotPiCpt` compacts: the Π clause's arguments are related at `⊥` demands only,
    so moving them from the right domain to the left needs typing and conversion transport
    (`hasTyT_of_tyConvT`, `convT_of_tyConv`) but no index transport of the relation. -/
theorem lrSCore_symm_botPiCpt (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotPiCpt c) :
    ∀ {M M' A : Expr Nat}, LRSCore R E n Γ M M' A c → LRSCore R E n Γ M' M A c := by
  induction hc with
  | bot => intro M M' A _; exact lrSCore_bot _ _ _ _
  | sort =>
      intro M M' A h
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | @pi a f _ hbd _ iha ihf =>
      intro M M' A h
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂, B₂, A₁, B₁, h2, h1, ⟨.assumption Γ A₂ v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, iha hra⟩, ?_⟩
          intro s hs N N' hN hN' hcN _
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁ := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          obtain ⟨v', hv'⟩ := hrf s hs N' N hN'₁ hN₁ ⟨hc₁⟩
            (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
          exact ⟨v', ihf s hs hv'⟩

/-- Transitivity at `BotPiCpt` compacts: the middle term's two readbacks coincide by
    `NormalUniqueR`; codomains compose through the shared left argument. -/
theorem lrSCore_trans_botPiCpt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotPiCpt c) :
    ∀ {M N P A : Expr Nat}, LRSCore R E n Γ M N A c → LRSCore R E n Γ N P A c →
      LRSCore R E n Γ M P A c := by
  induction hc with
  | bot => intro M N P A _ _; exact lrSCore_bot _ _ _ _
  | sort =>
      intro M N P A h₁ h₂
      rw [LRSCore.eq_def] at h₁ h₂
      rw [LRSCore.eq_def]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h2⟩ := h₂
      exact ⟨hA, u, u'', h1, h2⟩
  | @pi a f _ hbd _ iha ihf =>
      intro M N P A h₁ h₂
      rw [LRSCore.eq_def] at h₁ h₂
      rw [LRSCore.eq_def]
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h₁
      obtain ⟨_, A₂', B₂', A₃, B₃, h2', h3, _, ⟨hdom'⟩, ⟨hcod'⟩, ⟨u₂, hra'⟩, hrf'⟩ := h₂
      have e := hNU Γ h2 (fun _ hs => hL.pi_normal _ _ _ _ hs) h2'
        (fun _ hs => hL.pi_normal _ _ _ _ hs)
      injection e with eA eB
      subst eA; subst eB
      refine ⟨hA, A₁, B₁, A₃, B₃, h1, h3, ⟨hΓ₁⟩, ⟨.trans _ _ _ _ hdom hdom'⟩,
        ⟨.trans _ _ _ _ hcod (tyConvT_assump_dom hW hΓ hdom hcod')⟩,
        ⟨u₁, iha hra (lrSCore_sort_index_irrel hL a hra')⟩, ?_⟩
      intro s hs N N' hN hN' hcN _
      obtain ⟨hcN⟩ := hcN
      obtain ⟨v, hv⟩ := hrf s hs N N hN hN ⟨.refl _ _ _ hN⟩
        (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
      have hN₂ : HasTyT E n Γ N A₂ := hasTyT_of_tyConvT hN hdom
      have hN'₂ : HasTyT E n Γ N' A₂ := hasTyT_of_tyConvT hN' hdom
      obtain ⟨v', hv'⟩ := hrf' s hs N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom⟩
        (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
      exact ⟨v, ihf s hs hv (lrSCore_sort_index_irrel hL s.2 hv')⟩

theorem lrS_symm_botPiCpt (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotPiCpt c) {M M' A : Expr Nat}
    (h : LRS R E n Γ M M' A c) : LRS R E n Γ M' M A c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCore_symm_botPiCpt hW hΓ hc h)

theorem lrS_trans_botPiCpt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotPiCpt c) {M N P A : Expr Nat}
    (h₁ : LRS R E n Γ M N A c) (h₂ : LRS R E n Γ N P A c) : LRS R E n Γ M P A c := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCore_trans_botPiCpt hL hNU hW hΓ hc h₁ h₂)

/-- **The measurement**: symmetry at the one-demand compact `pi ⊥ [([sort], sort)]` entails
    sort-shape invariance of the readback under conversion.  If `A₁ ≡ A₂`, `A₂` reads back to a
    sort and has an inhabitant reading back to a sort, then `A₁` cannot be stuck.  The forward
    instance `Π A₁ C ~ Π A₂ C` (with `C = Π (Sort 0) (Sort 0)`) holds vacuously when `A₁` is
    stuck; its mirror image is refuted by `N ~ N : A₂` at `sort`.  So the PER of the
    substitution-style clause beyond `BotPiCpt` is the fundamental lemma's own strength. -/
theorem sort_shape_of_symm_pi (hL : ReadbackLaws E R)
    (hsymm : ∀ {Γ : LCtx} {M M' A : Expr Nat},
      LRSCore R E n Γ M M' A (.pi .bot [([.sort], .sort)]) →
      LRSCore R E n Γ M' M A (.pi .bot [([.sort], .sort)]))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {u : Level}
    (hA₁ : HasTyT E n Γ A₁ (.sort u)) (hdom : TyConvT E n Γ A₁ A₂)
    (hA₂s : ∃ l, RedR R Γ A₂ (.sort l))
    {N : Expr Nat} (hN : HasTyT E n Γ N A₂) (hNs : ∃ l, RedR R Γ N (.sort l))
    (hA₁n : ∀ l, ¬ RedR R Γ A₁ (.sort l)) : False := by
  have hfwd : LRSCore R E n Γ (.pi A₁ (.pi (.sort .zero) (.sort .zero)))
      (.pi A₂ (.pi (.sort .zero) (.sort .zero))) (.sort u) (.pi .bot [([.sort], .sort)]) := by
    rw [LRSCore.eq_def]
    refine ⟨⟨_, .refl _⟩, A₁, .pi (.sort .zero) (.sort .zero), A₂, .pi (.sort .zero) (.sort .zero),
      .refl _, .refl _, ⟨.assumption Γ A₁ u hΓ hA₁⟩, ⟨hdom⟩, ⟨.refl _ _⟩,
      ⟨u, lrSCore_bot _ _ _ _⟩, ?_⟩
    intro s hs _ _ _ _ _ hrel
    have hs' := List.mem_singleton.mp hs
    subst hs'
    have h := hrel .sort (List.mem_singleton.mpr rfl)
    rw [LRSCore.eq_def] at h
    obtain ⟨⟨l, hl⟩, _⟩ := h
    exact (hA₁n l hl).elim
  have hbwd := hsymm hfwd
  rw [LRSCore.eq_def] at hbwd
  obtain ⟨_, A₂', B₂', _, _, h2, _, _, _, _, _, hrf⟩ := hbwd
  have e₂ := redR_pi_eq hL h2
  injection e₂ with eA₂ eB₂
  subst eA₂; subst eB₂
  obtain ⟨l, hNl⟩ := hNs
  obtain ⟨v, hv⟩ := hrf ([.sort], .sort) (List.mem_singleton.mpr rfl) N N hN hN
    ⟨.refl _ _ _ hN⟩ (fun w hw => by
      have hw' := List.mem_singleton.mp hw
      subst hw'
      rw [LRSCore.eq_def]
      exact ⟨hA₂s, l, l, hNl, hNl⟩)
  rw [LRSCore.eq_def] at hv
  obtain ⟨_, w, _, hw, _⟩ := hv
  exact Expr.noConfusion (redR_pi_eq hL hw)

/-! ### §3 — the model layer -/

/-- An approximation model with a context environment. -/
structure CtxModel where
  Ap : EnvI → Expr Nat → CptI → Prop
  env : LCtx → EnvI

/-- The model at a context. -/
def CtxModel.at (M : CtxModel) (Γ : LCtx) : Expr Nat → CptI → Prop := M.Ap (M.env Γ)

/-- `ApproxI` with `ctxEnvI` (`RcicNativeFamModel` §6). -/
def ctxModelI : CtxModel := ⟨ApproxI, ctxEnvI⟩

/-- `ApproxDI E` with `ctxEnvDI E` (`RcicNativePiModelDeltaIota`, `RcicNativeFamModel` §11). -/
def ctxModelDI (E : ResolvedEnv) : CtxModel := ⟨ApproxDI E, ctxEnvDI E⟩

/-- What the statements and the reduction use of a model. -/
structure CtxModelLaws (E : ResolvedEnv) (M : CtxModel) : Prop where
  mono : ∀ {ρ ρ' : EnvI}, EnvI.le ρ ρ' → ∀ {e : Expr Nat} {c : CptI}, M.Ap ρ e c → M.Ap ρ' e c
  bot_mem : ∀ (ρ : EnvI) (e : Expr Nat), M.Ap ρ e .bot
  bvar_inv : ∀ {ρ : EnvI} {i : Nat} {c : CptI}, M.Ap ρ (.bvar i) c → c = .bot ∨ ρ i c
  bvar_mem : ∀ {ρ : EnvI} {i : Nat} {c : CptI}, ρ i c → M.Ap ρ (.bvar i) c
  sort_inv : ∀ {ρ : EnvI} {l : Level} {c : CptI}, M.Ap ρ (.sort l) c → c = .bot ∨ c = .sort
  sort_mem : ∀ (ρ : EnvI) (l : Level), M.Ap ρ (.sort l) .sort
  pi_bot_nil : ∀ (ρ : EnvI) (A B : Expr Nat), M.Ap ρ (.pi A B) (.pi .bot [])
  lam_inv : ∀ {ρ : EnvI} {A b : Expr Nat} {c : CptI}, M.Ap ρ (.lam A b) c →
    c = .bot ∨ ∃ f, c = .lam f ∧ ∀ s ∈ f, M.Ap (EnvI.cons (demand s.1) ρ) b s.2
  app_inv : ∀ {ρ : EnvI} {f a : Expr Nat} {c : CptI}, M.Ap ρ (.app f a) c →
    c = .bot ∨
      (∃ g s, c = s.2 ∧ M.Ap ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, M.Ap ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ M.Ap ρ f (.spine r args) ∧ M.Ap ρ a u)
  lift0_elim : ∀ {ρ : EnvI} {S : CptI → Prop} {e : Expr Nat} {c : CptI},
    M.Ap (EnvI.cons S ρ) (lift 0 1 e) c → M.Ap ρ e c
  famApp_botVecI : EnvWfT E → ∀ (ρ : EnvI) {r : Nat} {m : CheckedMember},
    E.members r = some m → m.mclass = .inductiveM →
    ∀ (ls : List Level) (xs : List (Expr Nat)), M.Ap ρ (foldApps (.const r ls) xs) (.spine r (botVecI xs))
  env_none_bot : ∀ (Γ : LCtx) (i : Nat), lookupValue Γ i = none → ∀ c, M.env Γ i c → c = .bot

/-- `ctxEnvI` at an assumption (or out of range) is `{⊥}`. -/
theorem ctxEnvI_none_bot : ∀ (Γ : LCtx) (i : Nat), lookupValue Γ i = none →
    ∀ c, ctxEnvI Γ i c → c = .bot
  | [], _, _, _, h => h
  | .assumption _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact h
      | succ i =>
          apply ctxEnvI_none_bot Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this
  | .letBinding _ _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact Option.noConfusion h0
      | succ i =>
          apply ctxEnvI_none_bot Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this

theorem ctxEnvDI_none_bot (E : ResolvedEnv) : ∀ (Γ : LCtx) (i : Nat), lookupValue Γ i = none →
    ∀ c, ctxEnvDI E Γ i c → c = .bot
  | [], _, _, _, h => h
  | .assumption _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact h
      | succ i =>
          apply ctxEnvDI_none_bot E Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this
  | .letBinding _ _ :: Γ, i, h0, c, h => by
      cases i with
      | zero => exact Option.noConfusion h0
      | succ i =>
          apply ctxEnvDI_none_bot E Γ i _ c h
          have := h0
          rw [Rcic.Declarative.lookupValue_cons_succ] at this
          cases hv : lookupValue Γ i with
          | none => rfl
          | some v => rw [hv] at this; exact Option.noConfusion this

theorem ctxModelLaws_I (E : ResolvedEnv) : CtxModelLaws E ctxModelI where
  mono := fun {_ _} hle {_ _} h => approxI_mono_env hle h
  bot_mem := fun ρ e => .bot ρ e
  bvar_inv := fun h => approxI_bvar_inv h
  bvar_mem := fun h => .bvar h
  sort_inv := fun h => approxI_sort_inv h
  sort_mem := fun ρ l => .sort ρ l
  pi_bot_nil := fun ρ A B => approxI_pi_bot_nil ρ A B
  lam_inv := fun h => approxI_lam_inv h
  app_inv := fun h => approxI_app_inv h
  lift0_elim := fun h => (approxI_cons_lift0_iff _ _ _ _).mp h
  famApp_botVecI := fun _ ρ r _ _ _ ls xs => approxI_famApp_botVecI ρ r ls xs
  env_none_bot := ctxEnvI_none_bot

theorem ctxModelLaws_DI (E : ResolvedEnv) : CtxModelLaws E (ctxModelDI E) where
  mono := fun {_ _} hle {_ _} h => approxDI_mono_env hle h
  bot_mem := fun ρ e => .bot ρ e
  bvar_inv := fun h => approxDI_bvar_inv h
  bvar_mem := fun h => .bvar h
  sort_inv := fun h => approxDI_sort_inv h
  sort_mem := fun ρ l => .sort ρ l
  pi_bot_nil := fun ρ A B => .pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim)
  lam_inv := fun h => approxDI_lam_inv h
  app_inv := fun h => approxDI_app_inv h
  lift0_elim := fun h => approxDI_lift_elim _ (by rw [EnvI.insert_zero]; exact h)
  famApp_botVecI := fun hW ρ _ _ hm hind ls xs => approxDI_famApp_botVecI_of_inductiveM hW ρ hm hind ls xs
  env_none_bot := ctxEnvDI_none_bot E

/-- Compacts transfer along readback steps. -/
def ReadbackModelInv (R : Readback) (M : CtxModel) : Prop :=
  ∀ (Γ : LCtx) {a b : Expr Nat}, R Γ a b → ∀ c, M.at Γ a c ↔ M.at Γ b c

theorem redR_modelInv {M : CtxModel} (hinv : ReadbackModelInv R M) {Γ : LCtx} {a b : Expr Nat}
    (h : RedR R Γ a b) (c : CptI) : M.at Γ a c ↔ M.at Γ b c := by
  induction h with
  | refl => exact Iff.rfl
  | step hs _ ih => exact (hinv _ hs c).trans ih

/-- Over `ApproxDI`/`ctxEnvDI`, the context-aware readback is model-invariant at every admitted
    environment (§11) — δ and ι included. -/
theorem readbackModelInv_whStepCtx_DI (hW : EnvWfT E) :
    ReadbackModelInv (WhStepCtx E) (ctxModelDI E) :=
  fun _ _ _ h c => approxDI_ctxEnvDI_whStepCtx_of_envWfT hW h c

/-- Over raw `ApproxI` the same needs `WhApproxInvCore E`, refuted at every environment with a
    transparent definition (`not_whApproxInvCore_defSortEnv`). -/
theorem readbackModelInv_whStepCtx_I (hcore : WhApproxInvCore E) :
    ReadbackModelInv (WhStepCtx E) ctxModelI :=
  fun _ _ _ h c => approxI_ctxEnvI_whStepCtx hcore h c

/-- The typed type-level chain form over a model. -/
def FundamentalLRSTM (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, M.at Γ A c → LRSCore R E n Γ A A' (.sort u) c

theorem fundamentalLRSTM_ctxModelI_iff : FundamentalLRSTM ctxModelI R E n ↔ FundamentalLRST R E n :=
  Iff.rfl

theorem piRowField_of_fundamentalLRSTM {M : CtxModel} (hL : ReadbackLaws E R) (hM : CtxModelLaws E M)
    (hW : EnvWfT E) (F : FundamentalLRSTM M R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCore_pi_components hL (F hΓ hPi hc (.pi .bot []) (hM.pi_bot_nil _ A B))

theorem famAppRow_of_fundamentalLRSTM {M : CtxModel} (hL : ReadbackLaws E R) (hM : CtxModelLaws E M)
    (hW : EnvWfT E) (F : FundamentalLRSTM M R E n) : Rcic.Syn.FamAppRowLink E n :=
  fun {_} hΓ {r _ ls _ xs _ _} hm hind hty hc =>
    lrSCore_famApp_components hL hW hm hind
      (F hΓ hty hc (.spine r (botVecI xs)) (hM.famApp_botVecI hW _ hm hind ls xs))

/-- The model environment of a substitution: the full approximation set of each substituent. -/
def envOfSubstM (M : CtxModel) (Δ : LCtx) (σ : SubstT) : EnvI := fun i c => M.at Δ (σ i) c

/-- **Pointwise related substitutions** `Δ ⊢ σ ≡ σ' : Γ` at a pair of model environments
    `(ρ, ρ')` (left / right): typed, convertible, and at every compact `ρ` assigns to `i` the left
    substituent has it in `Δ` and the two are related — symmetrically for `ρ'` and the right
    substituent; let-bound variables of `Γ` go to terms convertible to their substituted values.
    This is the inductive form: the λ case extends `(ρ, ρ')` by the step's demand on both sides. -/
def RelSubstAt (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) (Δ : LCtx) (ρ ρ' : EnvI)
    (σ σ' : SubstT) (Γ : LCtx) : Prop :=
  (∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A →
    Nonempty (HasTyT E n Δ (σ i) (substT σ A)) ∧ Nonempty (HasTyT E n Δ (σ' i) (substT σ A)) ∧
    Nonempty (ConvT E n Δ (σ i) (σ' i) (substT σ A)) ∧
    (∀ c, ρ i c → M.at Δ (σ i) c ∧ LRS R E n Δ (σ i) (σ' i) (substT σ A) c) ∧
    (∀ c, ρ' i c → M.at Δ (σ' i) c ∧ LRS R E n Δ (σ i) (σ' i) (substT σ A) c)) ∧
  (∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v →
    ∃ A, lookupType Γ i = some A ∧ Nonempty (ConvT E n Δ (σ i) (substT σ v) (substT σ A)))

/-- The fundamental lemma in pointwise related-substitution form: the left term's compacts are
    read at `ρ`, the right term's at `ρ'`. -/
def FundamentalSAt (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ Δ : LCtx} {ρ ρ' : EnvI} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ →
    RelSubstAt M R E n Δ ρ ρ' σ σ' Γ →
    ∀ {M₀ A : Expr Nat}, HasTyT E n Γ M₀ A →
    ∀ c, (M.Ap ρ M₀ c ∨ M.Ap ρ' M₀ c) →
      LRS R E n Δ (substT σ M₀) (substT σ' M₀) (substT σ A) c) ∧
  (∀ {Γ Δ : LCtx} {ρ ρ' : EnvI} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ →
    RelSubstAt M R E n Δ ρ ρ' σ σ' Γ →
    ∀ {M₀ M₀' A : Expr Nat}, ConvT E n Γ M₀ M₀' A →
    ∀ c, (M.Ap ρ M₀ c ∨ M.Ap ρ' M₀' c) →
      LRS R E n Δ (substT σ M₀) (substT σ' M₀') (substT σ A) c)

/-- Full-approximation-set related substitutions (the #7673 shape, over a model): the
    environments are the full approximation sets of the two substituents. -/
def RelSubstM (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) (Δ : LCtx)
    (σ σ' : SubstT) (Γ : LCtx) : Prop :=
  RelSubstAt M R E n Δ (envOfSubstM M Δ σ) (envOfSubstM M Δ σ') σ σ' Γ

/-- The fundamental lemma over full approximation sets. -/
def FundamentalSM (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ Δ : LCtx} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ → RelSubstM M R E n Δ σ σ' Γ →
    ∀ {M₀ A : Expr Nat}, HasTyT E n Γ M₀ A →
    ∀ c, (M.Ap (envOfSubstM M Δ σ) M₀ c ∨ M.Ap (envOfSubstM M Δ σ') M₀ c) →
      LRS R E n Δ (substT σ M₀) (substT σ' M₀) (substT σ A) c) ∧
  (∀ {Γ Δ : LCtx} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ → RelSubstM M R E n Δ σ σ' Γ →
    ∀ {M₀ M₀' A : Expr Nat}, ConvT E n Γ M₀ M₀' A →
    ∀ c, (M.Ap (envOfSubstM M Δ σ) M₀ c ∨ M.Ap (envOfSubstM M Δ σ') M₀' c) →
      LRS R E n Δ (substT σ M₀) (substT σ' M₀') (substT σ A) c)

theorem fundamentalSM_of_fundamentalSAt {M : CtxModel} (F : FundamentalSAt M R E n) :
    FundamentalSM M R E n :=
  ⟨fun {_ _ _ _} hΓ hΔ hrel {_ _} hM₀ c hc => F.1 hΓ hΔ hrel hM₀ c hc,
   fun {_ _ _ _} hΓ hΔ hrel {_ _ _} hc c hcc => F.2 hΓ hΔ hrel hc c hcc⟩

/-- `RelSubstM` over `ctxModelI` is at least #7673's `RelSubst` (which relates at the left
    substituent's compacts only). -/
theorem relSubst_of_relSubstM_I {Δ : LCtx} {σ σ' : SubstT} {Γ : LCtx}
    (h : RelSubstM ctxModelI R E n Δ σ σ' Γ) : RelSubst R E n Δ σ σ' Γ :=
  ⟨fun i A hA => ⟨(h.1 i A hA).1, (h.1 i A hA).2.1, (h.1 i A hA).2.2.1,
      fun c hc => ((h.1 i A hA).2.2.2.1 c hc).2⟩,
   h.2⟩

/-- #7673's `FundamentalS` (left-biased related substitutions, a stronger claim) implies the
    model form at `ctxModelI`. -/
theorem fundamentalSM_I_of_fundamentalS (F : FundamentalS R E n) : FundamentalSM ctxModelI R E n :=
  ⟨fun {_ _ _ _} hΓ hΔ hrel {_ _} hM₀ c hc =>
      hc.elim (fun h => F.1 hΓ hΔ (relSubst_of_relSubstM_I hrel) hM₀ c h)
        (fun h => F.2 hΓ hΔ (relSubst_of_relSubstM_I hrel) (.refl _ _ _ hM₀) c (Or.inr h)),
   fun {_ _ _ _} hΓ hΔ hrel {_ _ _} hc c hcc => F.2 hΓ hΔ (relSubst_of_relSubstM_I hrel) hc c hcc⟩

/-- The identity-substitution corollary form over a model. -/
def FundamentalSCtxM (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M₀ A : Expr Nat}, HasTyT E n Γ M₀ A →
    ∀ c, M.at Γ M₀ c → LRS R E n Γ M₀ M₀ A c) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M₀ M₀' A : Expr Nat}, ConvT E n Γ M₀ M₀' A →
    ∀ c, (M.at Γ M₀ c ∨ M.at Γ M₀' c) → LRS R E n Γ M₀ M₀' A c)

def RelSubstIdM (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → RelSubstM M R E n Γ SubstT.id SubstT.id Γ

theorem envOfSubstM_id_le {M : CtxModel} (hM : CtxModelLaws E M) (Γ : LCtx) :
    EnvI.le (M.env Γ) (envOfSubstM M Γ SubstT.id) :=
  fun _ _ h => hM.bvar_mem h

theorem fundamentalSCtxM_of_fundamentalSM {M : CtxModel} (hM : CtxModelLaws E M)
    (hid : RelSubstIdM M R E n) (F : FundamentalSM M R E n) : FundamentalSCtxM M R E n := by
  refine ⟨fun {Γ} hΓ {M₀ A} hM₀ c hc => ?_, fun {Γ} hΓ {M₀ M₀' A} hc c hcc => ?_⟩
  · have h := F.1 hΓ hΓ (hid hΓ) hM₀ c (Or.inl (hM.mono (envOfSubstM_id_le hM Γ) hc))
    rwa [substT_id, substT_id] at h
  · have h := F.2 hΓ hΓ (hid hΓ) hc c
      (hcc.elim (fun h => Or.inl (hM.mono (envOfSubstM_id_le hM Γ) h))
        (fun h => Or.inr (hM.mono (envOfSubstM_id_le hM Γ) h)))
    rwa [substT_id, substT_id, substT_id] at h

/-- Witness for `RelSubstIdM`: on a let-free context (every variable denotes `⊥` only). -/
theorem relSubstM_id_of_noLet {M : CtxModel} (hM : CtxModelLaws E M) {Γ : LCtx} (hnl : NoLetCtx Γ) :
    RelSubstM M R E n Γ SubstT.id SubstT.id Γ := by
  refine ⟨fun i A hA => ?_, fun i v hv => ?_⟩
  · rw [substT_id]
    have hrel : ∀ c, M.at Γ (SubstT.id i) c → LRS R E n Γ (SubstT.id i) (SubstT.id i) A c := by
      intro c hc
      rcases hM.bvar_inv hc with h0 | h0
      · subst h0; exact lrS_bot _ _ _ _
      · have := hM.env_none_bot Γ i (hnl i) c h0
        subst this; exact lrS_bot _ _ _ _
    exact ⟨⟨.bvar Γ i A hA⟩, ⟨.bvar Γ i A hA⟩, ⟨.refl _ _ _ (.bvar Γ i A hA)⟩,
      fun c hc => ⟨hc, hrel c hc⟩, fun c hc => ⟨hc, hrel c hc⟩⟩
  · have := hnl i
    rw [this] at hv
    exact Option.noConfusion hv

/-! ### §4 — the reduction: `piRow` from single links at the probe compacts -/

/-- The compacts the row consumers probe. -/
inductive ProbeCpt : CptI → Prop
  | bot : ProbeCpt .bot
  | sort : ProbeCpt .sort
  | piBotNil : ProbeCpt (.pi .bot [])

theorem botPiCpt_of_probe {c : CptI} (h : ProbeCpt c) : BotPiCpt c := by
  cases h with
  | bot => exact .bot
  | sort => exact .sort
  | piBotNil => exact botPiCpt_pi_bot_nil

/-- Compact transport across the relation at a probe compact: the right side reads back to a
    sort or a Π, which has the compact, and the readback is model-invariant. -/
theorem modelAt_right_of_lrSCore_probe {M : CtxModel} (hM : CtxModelLaws E M)
    (hinv : ReadbackModelInv R M) {Γ : LCtx} {A B : Expr Nat} {u : Level} {c : CptI}
    (hc : ProbeCpt c) (h : LRSCore R E n Γ A B (.sort u) c) : M.at Γ B c := by
  cases hc with
  | bot => exact hM.bot_mem _ _
  | sort =>
      rw [LRSCore.eq_def] at h
      obtain ⟨_, _, u', _, h2⟩ := h
      exact (redR_modelInv hinv h2 .sort).mpr (hM.sort_mem _ u')
  | piBotNil =>
      rw [LRSCore.eq_def] at h
      obtain ⟨_, A₁, B₁, A₂, B₂, _, h2, _⟩ := h
      exact (redR_modelInv hinv h2 _).mpr (hM.pi_bot_nil _ A₂ B₂)

/-- The chain form restricted to the probe compacts. -/
def FundamentalLRSTMProbe (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, ProbeCpt c → M.at Γ A c → LRSCore R E n Γ A A' (.sort u) c

theorem fundamentalLRSTMProbe_of_fundamentalLRSTM {M : CtxModel} (F : FundamentalLRSTM M R E n) :
    FundamentalLRSTMProbe M R E n :=
  fun {_} hΓ {_ _ _} hA hc c _ hcA => F hΓ hA hc c hcA

/-- **The chain form at the probes from the diagonal and the single links**: `trans` composes by
    `lrSCore_trans_botPiCpt` after transporting the compact across the middle type by
    `modelAt_right_of_lrSCore_probe` — no model soundness. -/
theorem fundamentalLRSTMProbe_of_links {M : CtxModel} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, ProbeCpt c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, ProbeCpt c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    FundamentalLRSTMProbe M R E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hpc hcA; exact hdiag hΓ hA c hpc hcA
  | of A B v hc => intro u _ c hpc hcA; exact lrSCore_sort_index_irrel hL c (hlink hΓ hc c hpc hcA)
  | trans A B C c₁ c₂ ih₁ ih₂ =>
      intro u hA c hpc hcA
      obtain ⟨v, hB⟩ := tyConvT_endTyped hW hΓ c₁ hA
      have r₁ := ih₁ hA c hpc hcA
      have hcB := modelAt_right_of_lrSCore_probe hM hinv hpc r₁
      exact lrSCore_trans_botPiCpt hL hNU hW hΓ (botPiCpt_of_probe hpc) r₁
        (lrSCore_sort_index_irrel hL c (ih₂ hB c hpc hcB))

theorem piRowField_of_fundamentalLRSTMProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMProbe M R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCore_pi_components hL (F hΓ hPi hc (.pi .bot []) .piBotNil (hM.pi_bot_nil _ A B))

/-- **`piRow` from the single-link fundamental lemma at `sort` and `pi ⊥ []`.** -/
theorem piRowField_of_links {M : CtxModel} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, ProbeCpt c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, ProbeCpt c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    PiRowField E n :=
  piRowField_of_fundamentalLRSTMProbe hL hM hW
    (fundamentalLRSTMProbe_of_links hL hNU hM hinv hW hdiag hlink)

/-! ### §5 — structural cases of the single-link lemma -/

/-- Every readback step is a conversion case: expand on the left, transfer the compact. -/
theorem link_of_step {M : CtxModel} (hL : ReadbackLaws E R) (hinv : ReadbackModelInv R M)
    {Γ : LCtx} {M₀ M₀' A : Expr Nat} (hs : R Γ M₀ M₀')
    (hdiag : ∀ c, M.at Γ M₀' c → LRS R E n Γ M₀' M₀' A c) :
    ∀ c, (M.at Γ M₀ c ∨ M.at Γ M₀' c) → LRS R E n Γ M₀ M₀' A c := by
  intro c hc
  have hc' : M.at Γ M₀' c := hc.elim (fun h => (hinv Γ hs c).mp h) id
  exact lrS_expand hL (redR_single hs) (.refl _) c (hdiag c hc')

theorem link_of_redR {M : CtxModel} (hL : ReadbackLaws E R) (hinv : ReadbackModelInv R M)
    {Γ : LCtx} {M₀ M₀' A : Expr Nat} (hs : RedR R Γ M₀ M₀')
    (hdiag : ∀ c, M.at Γ M₀' c → LRS R E n Γ M₀' M₀' A c) :
    ∀ c, (M.at Γ M₀ c ∨ M.at Γ M₀' c) → LRS R E n Γ M₀ M₀' A c := by
  intro c hc
  have hc' : M.at Γ M₀' c := hc.elim (fun h => (redR_modelInv hinv hs c).mp h) id
  exact lrS_expand hL hs (.refl _) c (hdiag c hc')

/-- The six `WhStepCtx` conversion cases over `ApproxDI` at any admitted environment, and the
    `pmajor` case of `WhStepK` given its model invariance. -/
theorem link_beta_DI (hW : EnvWfT E) {Γ : LCtx} (A b a T : Expr Nat)
    (hdiag : ∀ c, (ctxModelDI E).at Γ (instantiate0 a b) c →
      LRS (WhStepCtx E) E n Γ (instantiate0 a b) (instantiate0 a b) T c) :
    ∀ c, ((ctxModelDI E).at Γ (.app (.lam A b) a) c ∨ (ctxModelDI E).at Γ (instantiate0 a b) c) →
      LRS (WhStepCtx E) E n Γ (.app (.lam A b) a) (instantiate0 a b) T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.beta A b a) hdiag

theorem link_zeta_DI (hW : EnvWfT E) {Γ : LCtx} (A v b T : Expr Nat)
    (hdiag : ∀ c, (ctxModelDI E).at Γ (instantiate0 v b) c →
      LRS (WhStepCtx E) E n Γ (instantiate0 v b) (instantiate0 v b) T c) :
    ∀ c, ((ctxModelDI E).at Γ (.letE A v b) c ∨ (ctxModelDI E).at Γ (instantiate0 v b) c) →
      LRS (WhStepCtx E) E n Γ (.letE A v b) (instantiate0 v b) T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.zeta A v b) hdiag

theorem link_zetaLocal_DI (hW : EnvWfT E) {Γ : LCtx} {i : Nat} {v : Expr Nat}
    (hv : lookupValue Γ i = some v) (T : Expr Nat)
    (hdiag : ∀ c, (ctxModelDI E).at Γ v c → LRS (WhStepCtx E) E n Γ v v T c) :
    ∀ c, ((ctxModelDI E).at Γ (.bvar i) c ∨ (ctxModelDI E).at Γ v c) →
      LRS (WhStepCtx E) E n Γ (.bvar i) v T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.zetaLocal hv) hdiag

theorem link_delta_DI (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat} (hres : E.members r = some m) (hbody : m.body = some b) (T : Expr Nat)
    (hdiag : ∀ c, (ctxModelDI E).at Γ (instantiateLevels ls b) c →
      LRS (WhStepCtx E) E n Γ (instantiateLevels ls b) (instantiateLevels ls b) T c) :
    ∀ c, ((ctxModelDI E).at Γ (.const r ls) c ∨ (ctxModelDI E).at Γ (instantiateLevels ls b) c) →
      LRS (WhStepCtx E) E n Γ (.const r ls) (instantiateLevels ls b) T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.delta hres hbody) hdiag

theorem link_iota_DI (hW : EnvWfT E) {Γ : LCtx} {lhs rhs : Expr Nat} (hI : DerivedIotaU E lhs rhs)
    (T : Expr Nat) (hdiag : ∀ c, (ctxModelDI E).at Γ rhs c → LRS (WhStepCtx E) E n Γ rhs rhs T c) :
    ∀ c, ((ctxModelDI E).at Γ lhs c ∨ (ctxModelDI E).at Γ rhs c) →
      LRS (WhStepCtx E) E n Γ lhs rhs T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.iota hI) hdiag

theorem link_lit_DI (hW : EnvWfT E) {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (hdiag : ∀ c, (ctxModelDI E).at Γ (natExpand t) c →
      LRS (WhStepCtx E) E n Γ (natExpand t) (natExpand t) T c) :
    ∀ c, ((ctxModelDI E).at Γ (.lit t) c ∨ (ctxModelDI E).at Γ (natExpand t) c) →
      LRS (WhStepCtx E) E n Γ (.lit t) (natExpand t) T c :=
  link_of_step (readbackLaws_whStepCtx E) (readbackModelInv_whStepCtx_DI hW) (.lit t) hdiag

/-- K at a non-canonical proof major, as a conversion case of the K-aware readback: given the
    model invariance of `WhStepK` (the Opus seat's typed soundness), it is one `link_of_step`. -/
theorem link_pmajor_K {M : CtxModel} (hinv : ReadbackModelInv (WhStepK E n) M) {Γ : LCtx}
    {r : Nat} {ls : List Level} {pre : List (Expr Nat)} {canon x rhs P T : Expr Nat}
    (hI : DerivedIotaU E (recCall (.const r ls) pre canon) rhs)
    (hP : HasTyT E n Γ P (.sort .zero)) (hcanon : HasTyT E n Γ canon P) (hx : HasTyT E n Γ x P)
    (hdiag : ∀ c, M.at Γ rhs c → LRS (WhStepK E n) E n Γ rhs rhs T c) :
    ∀ c, (M.at Γ (recCall (.const r ls) pre x) c ∨ M.at Γ rhs c) →
      LRS (WhStepK E n) E n Γ (recCall (.const r ls) pre x) rhs T c :=
  link_of_step (readbackLaws_whStepK E n) hinv (.pmajor hI ⟨hP⟩ ⟨hcanon⟩ ⟨hx⟩) hdiag

/-- The `sort` diagonal and the `sorts` conversion. -/
theorem diag_sort {M : CtxModel} (hM : CtxModelLaws E M) {Γ : LCtx} (l : Level) :
    ∀ c, M.at Γ (.sort l) c → LRSCore R E n Γ (.sort l) (.sort l) (.sort (.succ l)) c := by
  intro c hc
  rcases hM.sort_inv hc with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

theorem link_sorts {M : CtxModel} (hM : CtxModelLaws E M) {Γ : LCtx} (l₁ l₂ : Level) :
    ∀ c, (M.at Γ (.sort l₁) c ∨ M.at Γ (.sort l₂) c) →
      LRSCore R E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) c := by
  intro c hc
  have h : c = .bot ∨ c = .sort := hc.elim (fun h => hM.sort_inv h) (fun h => hM.sort_inv h)
  rcases h with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]; exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

/-- `irr` at a proposition that does not read back to a universe: the collapse. -/
theorem link_irr {Γ : LCtx} {P : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hns : ∀ l, ¬ RedR R Γ P (.sort l)) (p q : Expr Nat) : ∀ c, LRS R E n Γ p q P c :=
  fun c => lrS_prop_total ⟨hP⟩ hns c

/-- The Π diagonal at the probe compact. -/
theorem diag_pi_probe {Γ : LCtx} {A B : Expr Nat} (hΓ₁ : CtxWfT E n (.assumption A :: Γ)) (u : Level) :
    LRSCore R E n Γ (.pi A B) (.pi A B) (.sort u) (.pi .bot []) := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, A, B, A, B, .refl _, .refl _, ⟨hΓ₁⟩, ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨u, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- `ConvT.pi` at the probe compact: the clause's data are the derivation's premises. -/
theorem link_pi_congr_probe {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (hA : ConvT E n Γ A A' (.sort u)) (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) (w : Level) :
    LRSCore R E n Γ (.pi A B) (.pi A' B') (.sort w) (.pi .bot []) := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, A, B, A', B', .refl _, .refl _, ⟨hΓ₁⟩, ⟨.of _ _ _ _ hA⟩, ⟨.of _ _ _ _ hB⟩,
    ⟨u, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- The variable diagonal at an assumption: only `⊥`. -/
theorem diag_bvar_assumption {M : CtxModel} (hM : CtxModelLaws E M) {Γ : LCtx} {i : Nat}
    (h0 : lookupValue Γ i = none) (A : Expr Nat) :
    ∀ c, M.at Γ (.bvar i) c → LRSCore R E n Γ (.bvar i) (.bvar i) A c := by
  intro c hc
  rcases hM.bvar_inv hc with rfl | h
  · exact lrSCore_bot _ _ _ _
  · have := hM.env_none_bot Γ i h0 c h
    subst this; exact lrSCore_bot _ _ _ _

/-- The variable diagonal at a let: the value's diagonal, expanded on both sides. -/
theorem diag_bvar_let {M : CtxModel} (hL : ReadbackLaws E R) (hinv : ReadbackModelInv R M)
    {Γ : LCtx} {i : Nat} {v : Expr Nat} (hstep : R Γ (.bvar i) v) (A : Expr Nat)
    (hdiag : ∀ c, M.at Γ v c → LRS R E n Γ v v A c) :
    ∀ c, M.at Γ (.bvar i) c → LRS R E n Γ (.bvar i) (.bvar i) A c := by
  intro c hc
  exact lrS_expand hL (redR_single hstep) (redR_single hstep) c (hdiag c ((hinv Γ hstep c).mp hc))

/-- The η-expansion's body instantiates to the application. -/
theorem instantiate0_etaApp (f N : Expr Nat) :
    instantiate0 N (.app (lift 0 1 f) (.bvar 0)) = .app f N :=
  instantiate0_eta f N

/-- `ConvT.eta` at every λ compact of the η-expansion: a step of `λx. f x` with output `c` comes
    from a step of `f` with a smaller demand and the same output (demand monotonicity through
    `app_inv`/`lift0_elim`), so the clause is the clause of `f`'s diagonal after one β step;
    steps with output `⊥` are trivial.  This is the sense in which η-unsoundness of the model
    (`eta_unsound_bot`) is harmless for the relation.  Restricted to `f` without spine compacts
    (a constant-headed `f` enters through the data-spine clause — named remainder). -/
theorem link_eta_lam {M : CtxModel} (hL : ReadbackLaws E R) (hM : CtxModelLaws E M)
    {Γ : LCtx} {f A B : Expr Nat} {w : Level}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort w))
    (hnospine : ∀ (r : Nat) (args : List CptI), ¬ M.at Γ f (.spine r args))
    (hdiag : ∀ g', M.at Γ f (.lam g') → LRSCore R E n Γ f f (.pi A B) (.lam g')) :
    ∀ g, M.at Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam g) →
      LRS R E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) (.lam g) := by
  intro g hg
  rcases hM.lam_inv hg with hbot | ⟨g', hgg, hbody⟩
  · exact CptI.noConfusion hbot
  · injection hgg with hgg'
    subst hgg'
    refine Or.inr ?_
    rw [LRSCore.eq_def]
    refine ⟨A, B, w, .refl _, ⟨hΓ₁⟩, ⟨hB⟩, fun s hs N N' hN hN' hcN hrel => ?_⟩
    have hb := hbody s hs
    rcases hM.app_inv hb with h0 | ⟨g₀, s₀, hs2, hf, hs₀, hargs⟩ | ⟨r, args, u, hs2, hf, _⟩
    · rw [h0]; exact Or.inr (lrSCore_bot _ _ _ _)
    · have hf' : M.at Γ f (.lam g₀) := hM.lift0_elim hf
      have hdf := hdiag g₀ hf'
      rw [LRSCore.eq_def] at hdf
      obtain ⟨A₁, B₁, _, hred, _, _, happ⟩ := hdf
      have e := redR_pi_eq hL hred
      injection e with eA eB
      subst eA; subst eB
      have hrel₀ : ∀ u ∈ s₀.1, LRSCore R E n Γ N N' A₁ u := by
        intro u hu
        rcases hM.bvar_inv (hargs u hu) with rfl | hmem
        · exact lrSCore_bot _ _ _ _
        · exact hrel u hmem
      rcases happ s₀ hs₀ N N' hN hN' hcN hrel₀ with hP | hcore
      · rw [hs2]; exact Or.inl hP
      · rw [hs2]
        refine Or.inr (lrSCore_expand hL ?_ (.refl _) s₀.2 hcore)
        have hβ := hL.beta Γ A₁ (.app (lift 0 1 f) (.bvar 0)) N
        rw [instantiate0_etaApp] at hβ
        exact redR_single hβ
    · exact absurd (hM.lift0_elim hf) (hnospine r args)

#print axioms NormalUniqueR
#print axioms DetR
#print axioms DiamondR
#print axioms redR_of_normal
#print axioms normalUniqueR_of_det
#print axioms redR_strip
#print axioms redR_confluent
#print axioms normalUniqueR_of_diamond
#print axioms detR_whStepCtx
#print axioms normalUniqueR_whStepCtx
#print axioms normalUniqueR_whStepK_of_det
#print axioms normalUniqueR_whStepK_of_diamond
#print axioms lrSCore_sort_index_irrel
#print axioms lrSCore_symm_botPiCpt
#print axioms lrSCore_trans_botPiCpt
#print axioms lrS_symm_botPiCpt
#print axioms lrS_trans_botPiCpt
#print axioms sort_shape_of_symm_pi
#print axioms CtxModel
#print axioms CtxModel.at
#print axioms ctxModelI
#print axioms ctxModelDI
#print axioms CtxModelLaws
#print axioms ctxEnvI_none_bot
#print axioms ctxEnvDI_none_bot
#print axioms ctxModelLaws_I
#print axioms ctxModelLaws_DI
#print axioms ReadbackModelInv
#print axioms redR_modelInv
#print axioms readbackModelInv_whStepCtx_DI
#print axioms readbackModelInv_whStepCtx_I
#print axioms FundamentalLRSTM
#print axioms fundamentalLRSTM_ctxModelI_iff
#print axioms piRowField_of_fundamentalLRSTM
#print axioms famAppRow_of_fundamentalLRSTM
#print axioms envOfSubstM
#print axioms RelSubstAt
#print axioms FundamentalSAt
#print axioms RelSubstM
#print axioms FundamentalSM
#print axioms fundamentalSM_of_fundamentalSAt
#print axioms relSubst_of_relSubstM_I
#print axioms fundamentalSM_I_of_fundamentalS
#print axioms FundamentalSCtxM
#print axioms RelSubstIdM
#print axioms envOfSubstM_id_le
#print axioms fundamentalSCtxM_of_fundamentalSM
#print axioms relSubstM_id_of_noLet
#print axioms ProbeCpt
#print axioms botPiCpt_of_probe
#print axioms modelAt_right_of_lrSCore_probe
#print axioms FundamentalLRSTMProbe
#print axioms fundamentalLRSTMProbe_of_fundamentalLRSTM
#print axioms fundamentalLRSTMProbe_of_links
#print axioms piRowField_of_fundamentalLRSTMProbe
#print axioms piRowField_of_links
#print axioms link_of_step
#print axioms link_of_redR
#print axioms link_beta_DI
#print axioms link_zeta_DI
#print axioms link_zetaLocal_DI
#print axioms link_delta_DI
#print axioms link_iota_DI
#print axioms link_lit_DI
#print axioms link_pmajor_K
#print axioms diag_sort
#print axioms link_sorts
#print axioms link_irr
#print axioms diag_pi_probe
#print axioms link_pi_congr_probe
#print axioms diag_bvar_assumption
#print axioms diag_bvar_let
#print axioms instantiate0_etaApp
#print axioms link_eta_lam

end Rcic.Declarative.NativeValleys.FamModelLRSAudit
