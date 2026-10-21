import rcic.RcicNativeTypedModelRelS
import rcic.RcicTypedInvert

/-!
# RcicNativeTypedModelFund — the fundamental lemma over `LRSCoreS` in related-substitution form:
readback expansion, the model interface, `RelSubstAtT`, the statement, and the single links

Items 1–3 of the ruling after segment 6, relation side (the syntactic half is `RcicSubstTTyped`).

* **§1 Readback expansion** `lrSCoreS_expand` / `lrSCoreS_expand_right`: a readback step on
  either side is absorbed, at every compact (the λ clause by `appHead`, structurally on the
  compact).  This is what the β/ζ/ζ-local/δ links use; it needs the data-spine clause to carry
  no conversion at the index (segment 4 amended accordingly).
* **§2 The model interface** `CtxModelT`/`CtxModelTLaws` — an `ApproxT`-shaped model over
  `CptT` (inversions for `bvar`/`sort`/`pi`/`lam`/`app`/`letE`, with the typed demands and the
  non-`⊥` λ output), `ctxModelT_approxT` the instance.
* **§3 `RelSubstAtT`** — the pointwise related substitution: `σ, σ'` typed (`TypedSubstT`),
  pointwise convertible (`ConvSubstT`), related in both orders and on both diagonals at the
  compacts the two environments assign (a symmetric package, so no PER of the relation is needed
  to flip it), and the let clause relating `σ i` to the substituted value.  No realisability:
  the induction never substitutes in the model.  **`FundTyAt`/`FundConvAt`/`FundamentalSAtT`**.
* **§4 The single links.**  Each case of the induction as a lemma whose hypotheses are exactly
  the inductive hypotheses it uses, plus the model-side facts it needs, named:
  - closed by the relation alone: `bvar`, `sort`, `pi`, `lam`, `app`, `letE` (typing side);
    `refl`, `beta`, `zeta`, `zetaLocal`, `sorts`, `app`/`lam`/`pi` congruences (conversion side);
  - `tyConv`, `symm`, `trans`: need the compact typed at the derivation's type (`ElT`, the model
    typing lemma) for `typedPERS`/`lrSCoreS_irrel`; `trans` additionally needs the model soundness
    of the first conversion at one environment (compact transport through the middle term);
  - `irr`: needs the collapse (the compact of a proof is `⊥`, the typing lemma at propositions);
  - `delta`/`consts`: need the unfolded body's diagonal (the fundamental lemma at the member's
    body — admission induction);
  - `iota`: needs the contractum's diagonal; `eta`: the η-expansion's relation from `f`'s.
* **§5 Item 3** — the typing data at a redex, from the derivation's own `app` nodes:
  `RecSpineTypedAt` and `recSpineTypedAt_of_hasTyT` (via the landed `hasTyTInv_app`): every
  argument of a `recCall` is typed at the Π-domain the derivation reaches, with the domains
  chained by `instantiate0`; the major is typed at the last domain.  No Π-injectivity.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — readback expansion -/

/-- A readback step on the left is absorbed, at every compact. -/
theorem lrSCoreS_expand (hL : ReadbackLaws E R) {Γ : LCtx} {M N M' A : Expr Nat}
    (hs : R Γ M N) : (c : CptT) → LRSCoreS R E n Γ N M' A c → LRSCoreS R E n Γ M M' A c
  | .bot, _ => lrSCoreS_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreS_prop_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u, u', .step hs h1, h2⟩
  | .sort, h => by
      rw [lrSCoreS_sort_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u, u', .step hs h1, h2⟩
  | .pi a f, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, rest⟩ := h
      exact ⟨hA, A₁, B₁, A₂, B₂, .step hs h1, h2, rest⟩
  | .lam g, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨A₁, B₁, hr, hΓ₁, hcl⟩ := h
      refine ⟨A₁, B₁, hr, hΓ₁, fun s hs' X X' hX hX' hc hrel => ?_⟩
      exact lrSCoreS_expand hL (hL.appHead _ X hs) s.2 (hcl s hs' X X' hX hX' hc hrel)
  | .spine r args, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, rest⟩ := h
      exact ⟨m, ls₁, ls₂, xs₁, xs₂, hm, .step hs h1, h2, rest⟩
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
     have h₂ := sizeOfT_snd_lt s
     omega)

/-- A readback step on the right is absorbed, at every compact. -/
theorem lrSCoreS_expand_right (hL : ReadbackLaws E R) {Γ : LCtx} {M N' M' A : Expr Nat}
    (hs : R Γ M' N') : (c : CptT) → LRSCoreS R E n Γ M N' A c → LRSCoreS R E n Γ M M' A c
  | .bot, _ => lrSCoreS_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreS_prop_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u, u', h1, .step hs h2⟩
  | .sort, h => by
      rw [lrSCoreS_sort_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u, u', h1, .step hs h2⟩
  | .pi a f, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, rest⟩ := h
      exact ⟨hA, A₁, B₁, A₂, B₂, h1, .step hs h2, rest⟩
  | .lam g, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨A₁, B₁, hr, hΓ₁, hcl⟩ := h
      refine ⟨A₁, B₁, hr, hΓ₁, fun s hs' X X' hX hX' hc hrel => ?_⟩
      exact lrSCoreS_expand_right hL (hL.appHead _ X' hs) s.2 (hcl s hs' X X' hX hX' hc hrel)
  | .spine r args, h => by
      rw [LRSCoreS.eq_def] at h ⊢
      obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, rest⟩ := h
      exact ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, .step hs h2, rest⟩
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
     have h₂ := sizeOfT_snd_lt s
     omega)

theorem lrSCoreS_expand_red (hL : ReadbackLaws E R) {Γ : LCtx} {M N M' A : Expr Nat}
    (hr : RedR R Γ M N) (c : CptT) (h : LRSCoreS R E n Γ N M' A c) : LRSCoreS R E n Γ M M' A c := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact lrSCoreS_expand hL hs c (ih h)

theorem lrSCoreS_expand_red_right (hL : ReadbackLaws E R) {Γ : LCtx} {M N' M' A : Expr Nat}
    (hr : RedR R Γ M' N') (c : CptT) (h : LRSCoreS R E n Γ M N' A c) : LRSCoreS R E n Γ M M' A c := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact lrSCoreS_expand_right hL hs c (ih h)

/-! ### §2 — the model interface -/

/-- A model over `CptT`: an environment-indexed approximation relation. -/
structure CtxModelT (E : ResolvedEnv) where
  Ap : EnvT → Expr Nat → CptT → Prop

/-- The laws the induction reads: the `ApproxT`-shaped inversions. -/
structure CtxModelTLaws (M : CtxModelT E) : Prop where
  bot : ∀ ρ e, M.Ap ρ e .bot
  bvar_inv : ∀ {ρ : EnvT} {i : Nat} {c : CptT}, M.Ap ρ (.bvar i) c → c = .bot ∨ ρ i c
  sort_inv : ∀ {ρ : EnvT} {l : Level} {c : CptT}, M.Ap ρ (.sort l) c → c = .bot ∨ c = sortCode l
  pi_inv : ∀ {ρ : EnvT} {A B : Expr Nat} {c : CptT}, M.Ap ρ (.pi A B) c →
    c = .bot ∨ ∃ a f, c = .pi a f ∧ M.Ap ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧ M.Ap (EnvT.cons (demandT s.1) ρ) B s.2
  lam_inv : ∀ {ρ : EnvT} {A b : Expr Nat} {c : CptT}, M.Ap ρ (.lam A b) c →
    c = .bot ∨ ∃ a g, c = .lam g ∧ M.Ap ρ A a ∧ (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧ M.Ap (EnvT.cons (demandT s.1) ρ) b s.2
  app_inv : ∀ {ρ : EnvT} {f a : Expr Nat} {c : CptT}, M.Ap ρ (.app f a) c →
    c = .bot ∨
    (∃ g s, c = s.2 ∧ M.Ap ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, M.Ap ρ a u) ∨
    (∃ r args u, c = .spine r (args ++ [u]) ∧ M.Ap ρ f (.spine r args) ∧ M.Ap ρ a u)
  letE_inv : ∀ {ρ : EnvT} {A v b : Expr Nat} {c : CptT}, M.Ap ρ (.letE A v b) c →
    M.Ap ρ (.app (.lam A b) v) c
  lift0_elim : ∀ {ρ : EnvT} {S : CptT → Prop} {e : Expr Nat} {c : CptT},
    M.Ap (EnvT.cons S ρ) (lift 0 1 e) c → M.Ap ρ e c

/-- The typed model as a `CtxModelT`. -/
def ctxModelT_approxT (E : ResolvedEnv) : CtxModelT E := ⟨ApproxT E⟩

theorem ctxModelTLaws_approxT (E : ResolvedEnv) : CtxModelTLaws (ctxModelT_approxT E) where
  bot := fun ρ e => .bot ρ e
  bvar_inv := fun h => approxT_bvar_inv h
  sort_inv := fun h => approxT_sort_inv h
  pi_inv := fun h => approxT_pi_inv h
  lam_inv := fun h => approxT_lam_inv h
  app_inv := fun h => approxT_app_inv h
  letE_inv := fun h => by
    cases h with
    | bot => exact .bot _ _
    | letE h => exact h
  lift0_elim := fun h => (approxT_cons_lift0_iff _ _ _ _ _).mp h

/-! ### §3 — related substitutions and the statement -/

/-- **The pointwise related substitution** `Δ ⊢ (ρ, σ) ≡ (ρ', σ') : Γ`: both substitutions typed
    and pointwise convertible; at the compacts either environment assigns to a variable, the
    substituents are related in both orders and on both diagonals, at the two index instances;
    for a let-bound variable, the four substituent/value pairs likewise (a symmetric package: no
    PER of the relation is needed to flip or to take a diagonal). -/
def RelSubstAtT (M : CtxModelT E) (R : Readback) (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT)
    (Γ : LCtx) : Prop :=
  TypedSubstT E n Δ σ Γ ∧ TypedSubstT E n Δ σ' Γ ∧ ConvSubstT E n Δ σ σ' Γ ∧
  (∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ∀ c, ρ i c ∨ ρ' i c →
    LRSCoreS R E n Δ (σ i) (σ' i) (substT σ A) c ∧ LRSCoreS R E n Δ (σ' i) (σ i) (substT σ' A) c ∧
    LRSCoreS R E n Δ (σ i) (σ i) (substT σ A) c ∧ LRSCoreS R E n Δ (σ' i) (σ' i) (substT σ' A) c) ∧
  (∀ (i : Nat) (v A : Expr Nat), lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ c, ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c →
    LRSCoreS R E n Δ (σ i) (substT σ' v) (substT σ A) c ∧
    LRSCoreS R E n Δ (σ' i) (substT σ v) (substT σ' A) c ∧
    LRSCoreS R E n Δ (σ i) (substT σ v) (substT σ A) c ∧
    LRSCoreS R E n Δ (σ' i) (substT σ' v) (substT σ' A) c)

/-- Flipping needs only the pointwise conversion's flip (along `A[σ] ≡ A[σ']`). -/
theorem RelSubstAtT.symm {M : CtxModelT E} {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} {Γ : LCtx}
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ) (h : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtT M R n Δ ρ' ρ σ' σ Γ := by
  obtain ⟨hT, hT', hc, hrel, hlet⟩ := h
  refine ⟨hT', hT, fun i A hA => ?_, fun i A hA c hc' => ?_, fun i v A hv hA c hc' => ?_⟩
  · obtain ⟨hci⟩ := hc i A hA
    obtain ⟨w₀, ⟨hA₀⟩⟩ := ctxWfT_lookupType_sort hcl hΓ hA
    obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA₀ hΔ hT hT' hc
    exact ⟨.tyConv _ _ _ _ _ w₀ (.symm _ _ _ _ hci) hAc⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hrel i A hA c hc'.symm
    exact ⟨h2, h1, h4, h3⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hlet i v A hv hA c (by
      rcases hc' with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h)))
    exact ⟨h2, h1, h4, h3⟩

/-- The left diagonal. -/
theorem RelSubstAtT.diagL {M : CtxModelT E} {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} {Γ : LCtx}
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ) (h : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtT M R n Δ ρ ρ σ σ Γ := by
  obtain ⟨hT, hT', hc, hrel, hlet⟩ := h
  refine ⟨hT, hT, fun i A hA => ?_, fun i A hA c hc' => ?_, fun i v A hv hA c hc' => ?_⟩
  · obtain ⟨ht⟩ := hT.1 i A hA
    exact ⟨.refl _ _ _ ht⟩
  · have hc'' : ρ i c ∨ ρ' i c := Or.inl (hc'.elim id id)
    obtain ⟨_, _, h3, _⟩ := hrel i A hA c hc''
    exact ⟨h3, h3, h3, h3⟩
  · have hc'' : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
      rcases hc' with h | h | h | h
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨_, _, h3, _⟩ := hlet i v A hv hA c hc''
    exact ⟨h3, h3, h3, h3⟩

/-- The right diagonal. -/
theorem RelSubstAtT.diagR {M : CtxModelT E} {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} {Γ : LCtx}
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ) (h : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtT M R n Δ ρ' ρ' σ' σ' Γ :=
  RelSubstAtT.diagL hW hcl hst hι hΓ hΔ (RelSubstAtT.symm hW hcl hst hι hΓ hΔ h)

/-- The typing conjunct's motive. -/
def FundTyAt (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ → RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c → LRSCoreS R E n Δ (substT σ e) (substT σ' e) (substT σ A) c

/-- The conversion conjunct's motive. -/
def FundConvAt (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ → RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c → LRSCoreS R E n Δ (substT σ a) (substT σ' b) (substT σ A) c

/-- **The fundamental lemma in related-substitution form over the typed relation.** -/
def FundamentalSAtT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat}, HasTyT E n Γ e A → FundTyAt M R n Γ e A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b A : Expr Nat}, ConvT E n Γ a b A → FundConvAt M R n Γ a b A)

/-! ### §4 — the single links -/

/-- `bvar`. -/
theorem fundT_bvar {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (i : Nat) (A : Expr Nat)
    (hA : lookupType Γ i = some A) : FundTyAt M R n Γ (.bvar i) A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  rcases hc with hc | hc
  · rcases hM.bvar_inv hc with rfl | hc
    · exact lrSCoreS_bot _ _ _ _
    · exact (hS.2.2.2.1 i A hA c (Or.inl hc)).1
  · rcases hM.bvar_inv hc with rfl | hc
    · exact lrSCoreS_bot _ _ _ _
    · exact (hS.2.2.2.1 i A hA c (Or.inr hc)).1

/-- `sort`: both universe codes read back the sorts. -/
theorem fundT_sort {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (l : Level) :
    FundTyAt M R n Γ (.sort l) (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  have hc' : c = .bot ∨ c = sortCode l := by
    rcases hc with hc | hc <;> exact hM.sort_inv hc
  rcases hc' with rfl | rfl
  · exact lrSCoreS_bot _ _ _ _
  · simp only [substT]
    rcases sortCode_prop_or_sort l with h | h <;> rw [h]
    · rw [lrSCoreS_prop_iff]; exact ⟨⟨_, .refl _⟩, l, l, .refl _, .refl _⟩
    · rw [lrSCoreS_sort_iff]; exact ⟨⟨_, .refl _⟩, l, l, .refl _, .refl _⟩

/-- `refl`. -/
theorem fundT_refl {M : CtxModelT E} {Γ : LCtx} {a A : Expr Nat} (ih : FundTyAt M R n Γ a A) :
    FundConvAt M R n Γ a a A := ih

/-- The extension of a related substitution under an assumption binder by related, typed,
    convertible arguments (the λ/Π/β cases' instrument).  The four relatedness combinations are
    produced from one (`hrel`) by the typed PER at the domain code `a` typing the demands, given
    the domain's relations `A[σ] ~ A[σ']` and `A[σ] ~ A[σ]` at `a`. -/
theorem relSubstAtT_cons (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) {Δ : LCtx} (hΔ : CtxWfT E n Δ) {ρ ρ' : EnvT}
    {σ σ' : SubstT} {Γ : LCtx} (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) (A : Expr Nat) (u : Level)
    (d : List CptT) {a : CptT} (hdT : ∀ v ∈ d, CTyS E v a) {wA : Level}
    (hAA' : LRSCoreS R E n Δ (substT σ A) (substT σ' A) (.sort wA) a)
    (hAA : LRSCoreS R E n Δ (substT σ A) (substT σ A) (.sort wA) a)
    (hAc : ConvT E n Δ (substT σ A) (substT σ' A) (.sort u))
    (N N' : Expr Nat) (hN : HasTyT E n Δ N (substT σ A)) (hN' : HasTyT E n Δ N' (substT σ A))
    (hcN : ConvT E n Δ N N' (substT σ A))
    (hrel : ∀ v ∈ d, LRSCoreS R E n Δ N N' (substT σ A) v) :
    RelSubstAtT M R n Δ (EnvT.cons (demandT d) ρ) (EnvT.cons (demandT d) ρ')
      (SubstT.cons N σ) (SubstT.cons N' σ') (.assumption A :: Γ) := by
  obtain ⟨hT, hT', hc, hrelS, hletS⟩ := hS
  have hN'ty : HasTyT E n Δ N' (substT σ' A) := .conv _ _ _ _ u hN' hAc
  have hNty' : HasTyT E n Δ N (substT σ' A) := .conv _ _ _ _ u hN hAc
  -- the three other combinations, by the typed PER
  have hrel' : ∀ v ∈ d, LRSCoreS R E n Δ N' N (substT σ' A) v := fun v hv =>
    lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hAA' (hdT v hv)
      (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA (hdT v hv) (hrel v hv))
  have hrelD : ∀ v ∈ d, LRSCoreS R E n Δ N N (substT σ A) v := fun v hv =>
    lrSCoreS_trans_tm hL hNU hW hCAs hCAt hΔ hAA (hdT v hv) (hrel v hv)
      (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA (hdT v hv) (hrel v hv))
  have hrelD' : ∀ v ∈ d, LRSCoreS R E n Δ N' N' (substT σ' A) v := fun v hv =>
    lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hAA' (hdT v hv)
      (lrSCoreS_trans_tm hL hNU hW hCAs hCAt hΔ hAA (hdT v hv)
        (lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hAA (hdT v hv) (hrel v hv)) (hrel v hv))
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

/-- The domain's two relations the λ/Π/β cases feed to `relSubstAtT_cons`, from the domain's
    inductive hypothesis. -/
theorem domRelations_of_ih (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {u : Level}
    (ihA : FundTyAt M R n Γ A (.sort u)) {Δ : LCtx} (hΔ : CtxWfT E n Δ) {ρ ρ' : EnvT}
    {σ σ' : SubstT} (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) {a : CptT}
    (ha : M.Ap ρ A a ∨ M.Ap ρ' A a) :
    LRSCoreS R E n Δ (substT σ A) (substT σ' A) (.sort u) a ∧
    LRSCoreS R E n Δ (substT σ A) (substT σ A) (.sort u) a ∧
    LRSCoreS R E n Δ (substT σ' A) (substT σ' A) (.sort u) a := by
  -- re-paired instances: the membership-providing environment with each substitution
  -- pair (the diagonal's own components are already in `hS`; no PER is needed)
  have hT := hS.1; have hT' := hS.2.1; have hrel := hS.2.2.2.1; have hlet := hS.2.2.2.2
  have hσσρ' : RelSubstAtT M R n Δ ρ' ρ' σ σ Γ := by
    refine ⟨hT, hT, fun i A hA => ?_, fun i A hA c hc' => ?_, fun i v A hv hA c hc' => ?_⟩
    · obtain ⟨ht⟩ := hT.1 i A hA
      exact ⟨.refl _ _ _ ht⟩
    · obtain ⟨_, _, h3, _⟩ := hrel i A hA c (Or.inr (hc'.elim id id))
      exact ⟨h3, h3, h3, h3⟩
    · have hc'' : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
        rcases hc' with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr h))
      obtain ⟨_, _, h3, _⟩ := hlet i v A hv hA c hc''
      exact ⟨h3, h3, h3, h3⟩
  have hσ'σ'ρ : RelSubstAtT M R n Δ ρ ρ σ' σ' Γ := by
    refine ⟨hT', hT', fun i A hA => ?_, fun i A hA c hc' => ?_, fun i v A hv hA c hc' => ?_⟩
    · obtain ⟨ht⟩ := hT'.1 i A hA
      exact ⟨.refl _ _ _ ht⟩
    · obtain ⟨_, _, _, h4⟩ := hrel i A hA c (Or.inl (hc'.elim id id))
      exact ⟨h4, h4, h4, h4⟩
    · have hc'' : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
        rcases hc' with h | h | h | h
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))
      obtain ⟨_, _, _, h4⟩ := hlet i v A hv hA c hc''
      exact ⟨h4, h4, h4, h4⟩
  rcases ha with h | h
  · exact ⟨ihA hΔ hS a (Or.inl h),
      ihA hΔ (RelSubstAtT.diagL hW hcl hst hι hΓ hΔ hS) a (Or.inl h),
      ihA hΔ hσ'σ'ρ a (Or.inl h)⟩
  · exact ⟨ihA hΔ hS a (Or.inr h),
      ihA hΔ hσσρ' a (Or.inl h),
      ihA hΔ (RelSubstAtT.diagR hW hcl hst hι hΓ hΔ hS) a (Or.inl h)⟩

/-- **`lam` (typing side).**  The λ clause of the relation at `λ A. body`'s compacts: β-expand both
    applications and use the body's inductive hypothesis at the extended substitution. -/
theorem fundT_lam (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u : Level} {body B : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u))
    (ihA : FundTyAt M R n Γ A (.sort u)) (ihb : FundTyAt M R n (.assumption A :: Γ) body B) :
    FundTyAt M R n Γ (.lam A body) (.pi A B) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAσ⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hcS
  -- the compact: `⊥` or a λ compact with a domain code `a` at one of the two environments
  have key : ∀ (ρ₀ : EnvT), (ρ₀ = ρ ∨ ρ₀ = ρ') → M.Ap ρ₀ (.lam A body) c →
      LRSCoreS R E n Δ (substT σ (.lam A body)) (substT σ' (.lam A body)) (substT σ (.pi A B)) c := by
    intro ρ₀ hρ₀ hc
    rcases hM.lam_inv hc with rfl | ⟨a, g, rfl, ha, _, hg⟩
    · exact lrSCoreS_bot _ _ _ _
    · have ha' : M.Ap ρ A a ∨ M.Ap ρ' A a := by
        rcases hρ₀ with rfl | rfl
        · exact Or.inl ha
        · exact Or.inr ha
      obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha'
      simp only [substT]
      rw [LRSCoreS.eq_def]
      refine ⟨substT σ A, substT σ.up B, .refl _, ⟨.assumption Δ _ u hΔ hAσ⟩, ?_⟩
      intro s hs N N' hN hN' hcN hrel
      obtain ⟨hdT, hb⟩ := hg s hs
      obtain ⟨hcN⟩ := hcN
      have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM hΔ hS A u s.1 hdT hAA' hAA hAc N N'
        hN hN' hcN hrel
      have hb' : M.Ap (EnvT.cons (demandT s.1) ρ) body s.2 ∨ M.Ap (EnvT.cons (demandT s.1) ρ') body s.2 := by
        rcases hρ₀ with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
      have hih := ihb hΔ hS' s.2 hb'
      -- β-expand both sides; `body[cons N σ] = instantiate0 N (body[σ.up])`
      rw [← instantiate0_substT_up, ← instantiate0_substT_up, ← instantiate0_substT_up] at hih
      exact lrSCoreS_expand hL (hL.beta _ _ _ _) s.2
        (lrSCoreS_expand_right hL (hL.beta _ _ _ _) s.2 hih)
  rcases hc with hc | hc
  · exact key ρ (Or.inl rfl) hc
  · exact key ρ' (Or.inr rfl) hc

/-- **`pi` (typing side).**  The Π clause of the relation at `Π A. B`'s compacts. -/
theorem fundT_pi (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u : Level} {B : Expr Nat} {v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ihA : FundTyAt M R n Γ A (.sort u)) (ihB : FundTyAt M R n (.assumption A :: Γ) B (.sort v)) :
    FundTyAt M R n Γ (.pi A B) (.sort (.imax u v)) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAσ⟩ := hasTyT_substT hW hcl hst hι hΓ hA hΔ hT
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hcS
  obtain ⟨hBc⟩ := convT_substT_pointwise hW hcl hst hι (.assumption Γ A u hΓ hA) hB
    (.assumption Δ _ u hΔ hAσ) (typedSubstT_up hcl hT A) (typedSubstT_up_conv hcl hT' A u hAc)
    (convSubstT_up_decl hcl hcS _ _ A rfl (.bvar _ 0 _ rfl))
  have key : ∀ (ρ₀ : EnvT), (ρ₀ = ρ ∨ ρ₀ = ρ') → M.Ap ρ₀ (.pi A B) c →
      LRSCoreS R E n Δ (substT σ (.pi A B)) (substT σ' (.pi A B)) (substT σ (.sort (.imax u v))) c := by
    intro ρ₀ hρ₀ hc
    rcases hM.pi_inv hc with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact lrSCoreS_bot _ _ _ _
    · have ha' : M.Ap ρ A a ∨ M.Ap ρ' A a := by
        rcases hρ₀ with rfl | rfl
        · exact Or.inl ha
        · exact Or.inr ha
      obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha'
      simp only [substT]
      rw [LRSCoreS.eq_def]
      refine ⟨⟨_, .refl _⟩, substT σ A, substT σ.up B, substT σ' A, substT σ'.up B, .refl _, .refl _,
        ⟨.assumption Δ _ u hΔ hAσ⟩, ⟨.of _ _ _ u hAc⟩, ⟨.of _ _ _ v hBc⟩, ⟨u, hAA'⟩, ?_⟩
      intro s hs hdT N N' hN hN' hcN hrel
      obtain ⟨_, hBs⟩ := hf s hs
      obtain ⟨hcN⟩ := hcN
      have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM hΔ hS A u s.1 hdT hAA' hAA hAc N N'
        hN hN' hcN hrel
      have hB' : M.Ap (EnvT.cons (demandT s.1) ρ) B s.2 ∨ M.Ap (EnvT.cons (demandT s.1) ρ') B s.2 := by
        rcases hρ₀ with rfl | rfl
        · exact Or.inl hBs
        · exact Or.inr hBs
      have hih := ihB hΔ hS' s.2 hB'
      rw [← instantiate0_substT_up, ← instantiate0_substT_up] at hih
      exact ⟨v, hih⟩
  rcases hc with hc | hc
  · exact key ρ (Or.inl rfl) hc
  · exact key ρ' (Or.inr rfl) hc

/-- **`app` (typing side), at non-spine compacts.**  The function's λ clause at the argument.
    At a spine compact the relation reads a type-level family spine, whose `ConvArgsT` along the
    declared telescope is not available from the derivation's own domains without Π-injectivity
    (W-FAMSPINE, named in the PR); that case is excluded here. -/
theorem fundT_app (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    {M : CtxModelT E} (hM : CtxModelTLaws M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A)
    (ihf : FundTyAt M R n Γ f (.pi A B)) (iha : FundTyAt M R n Γ a A)
    {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} (hΔ : CtxWfT E n Δ)
    (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) (c : CptT)
    (hns : ∀ r args, c ≠ .spine r args)
    (hc : M.Ap ρ (.app f a) c ∨ M.Ap ρ' (.app f a) c) :
    LRSCoreS R E n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ (instantiate0 a B)) c := by
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨w, hAty⟩ := tySort hW hΓ ha
  obtain ⟨haσ⟩ := hasTyT_substT hW hcl hst hι hΓ ha hΔ hT
  obtain ⟨haσ'⟩ := hasTyT_substT hW hcl hst hι hΓ ha hΔ hT'
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hAty hΔ hT hT' hcS
  obtain ⟨hac⟩ := convT_substT_pointwise hW hcl hst hι hΓ ha hΔ hT hT' hcS
  have haσ'A : HasTyT E n Δ (substT σ' a) (substT σ A) := .conv _ _ _ _ w haσ' (.symm _ _ _ _ hAc)
  have key : ∀ (ρ₀ : EnvT), (ρ₀ = ρ ∨ ρ₀ = ρ') → M.Ap ρ₀ (.app f a) c →
      LRSCoreS R E n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ (instantiate0 a B)) c := by
    intro ρ₀ hρ₀ hc
    rcases hM.app_inv hc with rfl | ⟨g, s, rfl, hfg, hs, hau⟩ | ⟨r, args, u, rfl, _, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · have hfg' : M.Ap ρ f (.lam g) ∨ M.Ap ρ' f (.lam g) := by
        rcases hρ₀ with rfl | rfl
        · exact Or.inl hfg
        · exact Or.inr hfg
      have hih := ihf hΔ hS (.lam g) hfg'
      rw [LRSCoreS.eq_def] at hih
      obtain ⟨A₁, B₁, hr, _, hcl'⟩ := hih
      -- the Π readback of `(Π A B)[σ]` is itself
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr (.refl _)
      subst eA; subst eB
      have hrel : ∀ u ∈ s.1, LRSCoreS R E n Δ (substT σ a) (substT σ' a) (substT σ A) u := fun u hu => by
        refine iha hΔ hS u ?_
        rcases hρ₀ with rfl | rfl
        · exact Or.inl (hau u hu)
        · exact Or.inr (hau u hu)
      have := hcl' s hs (substT σ a) (substT σ' a) haσ haσ'A ⟨hac⟩ hrel
      simp only [substT]
      rw [substT_instantiate0]
      exact this
    · exact (hns r (args ++ [u]) rfl).elim
  rcases hc with hc | hc
  · exact key ρ (Or.inl rfl) hc
  · exact key ρ' (Or.inr rfl) hc

/-- The model's β law (the `ApproxT` substitution lemma's half the β link needs, swe-zeta): a
    compact of the instance `body[arg]` comes from a compact of the body under a demand realised
    by the argument, typed at a code of the binder's type. -/
def ModelBetaExpandT (M : CtxModelT E) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, M.Ap ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), M.Ap ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c

/-- **`beta` (conversion side).**  The left compact comes from the λ's step (structural); the
    right compact from the model's β law. -/
theorem fundT_beta (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hβ : ModelBetaExpandT M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (harg : HasTyT E n Γ arg A)
    (ihA : FundTyAt M R n Γ A (.sort u)) (ihb : FundTyAt M R n (.assumption A :: Γ) body B)
    (iharg : FundTyAt M R n Γ arg A) :
    FundConvAt M R n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
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
  · obtain ⟨a, us, ha, hdT, hus, hb⟩ := hβ (A := A) hc
    exact finish a us (Or.inr ha) hdT (fun v hv => Or.inr (hus v hv)) (Or.inr hb)

/-! ### §5 — item 3: the typing data at a redex, from the derivation's own `app` nodes -/

/-- Arguments typed along the domains the derivation reaches: `doms` lists, for each argument,
    the Π-domain of the function's type AT THAT NODE (already instantiated by the earlier
    arguments), and the argument is typed at it. -/
def RecSpineTypedAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : List (Expr Nat) → List (Expr Nat) → Prop
  | [], [] => True
  | x :: xs, A :: As => Nonempty (HasTyT E n Γ x A) ∧ RecSpineTypedAt E n Γ xs As
  | _, _ => False

theorem recSpineTypedAt_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {xs doms : List (Expr Nat)}, RecSpineTypedAt E n Γ xs doms →
      ∀ {y A : Expr Nat}, Nonempty (HasTyT E n Γ y A) →
      RecSpineTypedAt E n Γ (xs ++ [y]) (doms ++ [A])
  | [], [], _, y, A, hy => ⟨hy, trivial⟩
  | x :: xs, A₀ :: doms, ⟨hx, hrest⟩, y, A, hy => ⟨hx, recSpineTypedAt_append hrest hy⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- **Every argument of a typed application spine is typed at the Π-domain its node reaches** —
    read off the derivation by `hasTyTInv_app`, no Π-injectivity.  The domains are returned
    together with the head's type at the spine's root. -/
theorem recSpineTypedAt_of_hasTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ (k : Nat) (xs : List (Expr Nat)), xs.length = k → ∀ {f T : Expr Nat},
      HasTyT E n Γ (foldApps f xs) T →
      ∃ (doms : List (Expr Nat)) (F : Expr Nat), Nonempty (HasTyT E n Γ f F) ∧
        doms.length = xs.length ∧ RecSpineTypedAt E n Γ xs doms := by
  intro k
  induction k with
  | zero =>
      intro xs hk f T h
      cases xs with
      | nil => exact ⟨[], T, ⟨h⟩, rfl, trivial⟩
      | cons _ _ => cases hk
  | succ k ih =>
      intro xs hk f T h
      rcases FamModelAudit.list_eq_nil_or_snoc xs with rfl | ⟨ys, y, rfl⟩
      · cases hk
      · rw [foldApps_snoc] at h
        obtain ⟨A, B, hf, hy, _⟩ := hasTyTInv_app h rfl
        have hk' : ys.length = k := by simp at hk; omega
        obtain ⟨doms, F, hF, hlen, hsp⟩ := ih ys hk' hf
        refine ⟨doms ++ [A], F, hF, by simp [hlen], ?_⟩
        exact recSpineTypedAt_append hsp ⟨hy⟩

/-- The major of a typed `recCall` is typed at the last domain the derivation reaches, and the
    pre-major arguments along theirs. -/
theorem recCall_typed_data {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {pre : List (Expr Nat)} {x T : Expr Nat} (h : HasTyT E n Γ (recCall (.const r ls) pre x) T) :
    ∃ (doms : List (Expr Nat)) (Dx : Expr Nat), doms.length = pre.length ∧
      RecSpineTypedAt E n Γ pre doms ∧ Nonempty (HasTyT E n Γ x Dx) := by
  unfold recCall at h
  rw [foldApps_snoc] at h
  obtain ⟨A, B, hf, hx, _⟩ := hasTyTInv_app h rfl
  obtain ⟨doms, F, _, hlen, hsp⟩ := recSpineTypedAt_of_hasTyT pre.length pre rfl hf
  exact ⟨doms, A, hlen, hsp, ⟨hx⟩⟩

#print axioms lrSCoreS_expand
#print axioms lrSCoreS_expand_right
#print axioms lrSCoreS_expand_red
#print axioms lrSCoreS_expand_red_right
#print axioms CtxModelT
#print axioms CtxModelTLaws
#print axioms ctxModelT_approxT
#print axioms ctxModelTLaws_approxT
#print axioms RelSubstAtT
#print axioms RelSubstAtT.symm
#print axioms RelSubstAtT.diagL
#print axioms RelSubstAtT.diagR
#print axioms FundTyAt
#print axioms FundConvAt
#print axioms FundamentalSAtT
#print axioms fundT_bvar
#print axioms fundT_sort
#print axioms fundT_refl
#print axioms relSubstAtT_cons
#print axioms domRelations_of_ih
#print axioms fundT_lam
#print axioms fundT_pi
#print axioms fundT_app
#print axioms ModelBetaExpandT
#print axioms fundT_beta
#print axioms RecSpineTypedAt
#print axioms recSpineTypedAt_append
#print axioms recSpineTypedAt_of_hasTyT
#print axioms recCall_typed_data

end Rcic.Declarative.NativeValleys.TypedModelAudit
