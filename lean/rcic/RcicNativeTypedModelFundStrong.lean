import rcic.RcicNativeTypedModelFamSpine

/-!
# RcicNativeTypedModelFundStrong — the fundamental lemma by strong induction on the derivation

Item 1 of the ruling after segment 8.  The induction is on `sizeOf` of the `HasTyT`/`ConvT`
derivation (the measure RcicTypedLevels already uses for the mutual family), and its motive
carries **type validity**:

* `TyValidAt Γ A := ∃ w, FundTyAt Γ A (.sort w)` — the type is self-related under every related
  substitution at every compact it has;
* `CtxValidAt Γ` — every variable's type is valid.  It is a hypothesis of the motive and is
  extended under a binder by **reindexing** (`tyValidAt_lift`, `ctxValidAt_cons`): validity
  quantifies over all substitutions, so weakening is `substT σ (lift 0 1 A) = substT (shiftAt 0 σ) A`
  and the tail of the environment — no Kripke closure is needed.

**Where the measure could fail, and why it does not.**  `symm`, `trans` and `tyConv` need the
relation of the TYPE (`A[σ] ~ A[σ']`, `A[σ] ~ A[σ]`), and `A`'s typing derivation is not a
sub-derivation of these rules (`convEnds` produces one of unbounded size).  Here it is never
recursed on: the type's relation is the **validity conjunct of the inductive hypothesis** on the
sub-derivation (`fundT_symm_strong` shows the shape: one call to the IH on `h : b ≡ a`, at
swapped environments, and the typed PER).  `tyConv` and `trans` additionally need two model-side
facts, stated exactly (`TypingAt`, `ModelConvSoundAt`) — the typing lemma and the conversion
soundness of the model — which are not recursive calls.

**The principle** `fund_strong`: from the per-constructor obligations (`FundCases`, each given
the inductive hypotheses for ALL derivations of smaller `sizeOf`, in any context — `IHBelow`),
the motive for every derivation.  The structural cases are discharged here (`sort`, `bvar`,
`pi`, `lam`, `refl`, `beta` given the model's β law, `symm` given the typing lemma); the others
are fields of `FundCases` with their exact IH shapes.  `fundamentalSAtT_of_cases` closes the
loop: `CtxValidAt` is itself produced from `CtxWfT` by the lemma at the binders' derivations
(`ctxValidAt_of_ctxWfT`).

**Item 3** — `BackTransportT R E ρ Γ`: backward compact transport along one readback step, the
hypothesis `hinv` of `domAlign_of_chain`.  It is a **model fact** (about `ApproxT`, not the
relation): the `b ⊆ a` half of `ReadbackModelInv`.  Non-vacuity: `backTransportT_zetaLocal` (the
ζ-local rule, at every context environment, unconditionally) and `backTransportT_appHead_closure`
(the congruence rule is inherited).  For `WhStepCK` the remaining rules are β/ζ (from
`ModelBetaExpandT`, swe-zeta), δ (`approxT_closed_env` + the δ clause), ι and K (`IotaSoundT`,
swe-iotaret, with `semEqT_kStar_of_iotaSoundT`).

**Superseded for the raw β rule** (#7721, `no_readback_with_raw_approxT_back`): at a readback
with the raw β law, `BackTransportT` is unsatisfiable — `z = (λ (x : D). x) P` reads back to `P`,
which has the probe `pi ⊥ []`, while every compact of `z` is `⊥`.  The witnesses above stand
(ζ-local, congruence); the chain consumer no longer uses it: `RcicNativeTypedModelProbe`
re-proves the alignment from relation-seeded links (`domAlign_of_chain_probe`,
`nodeDeclAlign_const_of_probeLinks`) and states the typed, realised β laws.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — type validity and context validity -/

/-- The type is self-related under every related substitution at every compact it has. -/
def TyValidAt (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  ∃ w : Level, FundTyAt M R n Γ A (.sort w)

/-- Every variable's type is valid. -/
def CtxValidAt (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → TyValidAt M R n Γ A

/-- The model laws plus the lift introduction (the other half of `lift0_elim`). -/
structure CtxModelTLaws' (M : CtxModelT E) extends CtxModelTLaws M : Prop where
  lift0_intro : ∀ {ρ : EnvT} {S : CptT → Prop} {e : Expr Nat} {c : CptT},
    M.Ap ρ e c → M.Ap (EnvT.cons S ρ) (lift 0 1 e) c

theorem ctxModelTLaws'_approxT (E : ResolvedEnv) : CtxModelTLaws' (ctxModelT_approxT E) :=
  { ctxModelTLaws_approxT E with
    lift0_intro := fun h => (approxT_cons_lift0_iff _ _ _ _ _).mpr h }

/-- The tail of an environment. -/
def EnvT.tail (ρ : EnvT) : EnvT := fun i => ρ (i + 1)

theorem EnvT.cons_tail (ρ : EnvT) : EnvT.cons (ρ 0) (EnvT.tail ρ) = ρ := by
  funext i c
  cases i with
  | zero => rfl
  | succ i => rfl

/-- A related substitution into `d :: Γ` restricts to one into `Γ` by shifting. -/
theorem relSubstAtT_tail {M : CtxModelT E} (hM : CtxModelTLaws' M) {Δ : LCtx} {ρ ρ' : EnvT}
    {σ σ' : SubstT} {d : LocalDecl} {Γ : LCtx} (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' (d :: Γ)) :
    RelSubstAtT M R n Δ (EnvT.tail ρ) (EnvT.tail ρ') (SubstT.shiftAt 0 σ) (SubstT.shiftAt 0 σ') Γ := by
  obtain ⟨hT, hT', hc, hrel, hlet⟩ := hS
  have e : ∀ (τ : SubstT) (A : Expr Nat), substT (SubstT.shiftAt 0 τ) A = substT τ (lift 0 1 A) :=
    fun τ A => (substT_lift 0 τ A).symm
  have sh : ∀ (τ : SubstT) (i : Nat), SubstT.shiftAt 0 τ i = τ (i + 1) := fun τ i => by
    simp [SubstT.shiftAt]
  refine ⟨⟨fun i A h => ?_, fun i v hv => ?_⟩, ⟨fun i A h => ?_, fun i v hv => ?_⟩,
    fun i A h => ?_, fun i A h c hc' => ?_, fun i v A hv hA c hc' => ?_⟩
  · have h' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by rw [lookupType_cons_succ, h]; rfl
    obtain ⟨ht⟩ := hT.1 (i + 1) _ h'
    rw [sh, e]; exact ⟨ht⟩
  · have hv' : lookupValue (d :: Γ) (i + 1) = some (lift 0 1 v) := by rw [lookupValue_cons_succ, hv]; rfl
    obtain ⟨A', hA', ⟨hc₀⟩⟩ := hT.2 (i + 1) _ hv'
    rw [lookupType_cons_succ] at hA'
    cases hA₀ : lookupType Γ i with
    | none => rw [hA₀] at hA'; exact Option.noConfusion hA'
    | some A₀ =>
        rw [hA₀] at hA'; injection hA' with hA'; subst hA'
        exact ⟨A₀, rfl, ⟨by rw [sh, e, e]; exact hc₀⟩⟩
  · have h' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by rw [lookupType_cons_succ, h]; rfl
    obtain ⟨ht⟩ := hT'.1 (i + 1) _ h'
    rw [sh, e]; exact ⟨ht⟩
  · have hv' : lookupValue (d :: Γ) (i + 1) = some (lift 0 1 v) := by rw [lookupValue_cons_succ, hv]; rfl
    obtain ⟨A', hA', ⟨hc₀⟩⟩ := hT'.2 (i + 1) _ hv'
    rw [lookupType_cons_succ] at hA'
    cases hA₀ : lookupType Γ i with
    | none => rw [hA₀] at hA'; exact Option.noConfusion hA'
    | some A₀ =>
        rw [hA₀] at hA'; injection hA' with hA'; subst hA'
        exact ⟨A₀, rfl, ⟨by rw [sh, e, e]; exact hc₀⟩⟩
  · have h' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by rw [lookupType_cons_succ, h]; rfl
    obtain ⟨hc₀⟩ := hc (i + 1) _ h'
    rw [sh, sh, e]; exact ⟨hc₀⟩
  · have h' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by rw [lookupType_cons_succ, h]; rfl
    have := hrel (i + 1) _ h' c hc'
    rw [sh, sh, e, e]; exact this
  · have hv' : lookupValue (d :: Γ) (i + 1) = some (lift 0 1 v) := by rw [lookupValue_cons_succ, hv]; rfl
    have hA' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by rw [lookupType_cons_succ, hA]; rfl
    have hc'' : ρ (i + 1) c ∨ ρ' (i + 1) c ∨ M.Ap ρ (lift 0 1 v) c ∨ M.Ap ρ' (lift 0 1 v) c := by
      rcases hc' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (by rw [← EnvT.cons_tail ρ]; exact hM.lift0_intro h)))
      · exact Or.inr (Or.inr (Or.inr (by rw [← EnvT.cons_tail ρ']; exact hM.lift0_intro h)))
    have := hlet (i + 1) _ _ hv' hA' c hc''
    rw [sh, sh, e, e, e, e]; exact this

/-- Environment re-pairing: every component of `RelSubstAtT` quantifies over `ρ i c ∨ ρ' i c`, so
    any pair of environments drawn from `{ρ, ρ'}` works with the same substitutions. -/
theorem RelSubstAtT.envs {M : CtxModelT E} {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} {Γ : LCtx}
    (h : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) (ρ₁ ρ₂ : EnvT) (h₁ : ρ₁ = ρ ∨ ρ₁ = ρ')
    (h₂ : ρ₂ = ρ ∨ ρ₂ = ρ') : RelSubstAtT M R n Δ ρ₁ ρ₂ σ σ' Γ := by
  obtain ⟨hT, hT', hc, hrel, hlet⟩ := h
  have mem : ∀ {i : Nat} {c : CptT}, ρ₁ i c ∨ ρ₂ i c → ρ i c ∨ ρ' i c := by
    intro i c hm
    rcases hm with hm | hm
    · rcases h₁ with rfl | rfl
      · exact Or.inl hm
      · exact Or.inr hm
    · rcases h₂ with rfl | rfl
      · exact Or.inl hm
      · exact Or.inr hm
  have memv : ∀ {v : Expr Nat} {i : Nat} {c : CptT},
      ρ₁ i c ∨ ρ₂ i c ∨ M.Ap ρ₁ v c ∨ M.Ap ρ₂ v c →
      ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
    intro v i c hm
    rcases hm with hm | hm | hm | hm
    · exact (mem (Or.inl hm)).elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact (mem (Or.inr hm)).elim Or.inl (fun h => Or.inr (Or.inl h))
    · rcases h₁ with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hm))
      · exact Or.inr (Or.inr (Or.inr hm))
    · rcases h₂ with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hm))
      · exact Or.inr (Or.inr (Or.inr hm))
  exact ⟨hT, hT', hc, fun i A hA c hc' => hrel i A hA c (mem hc'),
    fun i v A hv hA c hc' => hlet i v A hv hA c (memv hc')⟩

/-- **Validity weakens by reindexing**: no Kripke closure. -/
theorem tyValidAt_lift {M : CtxModelT E} (hM : CtxModelTLaws' M) {Γ : LCtx} {A : Expr Nat}
    (d : LocalDecl) (h : TyValidAt M R n Γ A) : TyValidAt M R n (d :: Γ) (lift 0 1 A) := by
  obtain ⟨w, hF⟩ := h
  refine ⟨w, fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_⟩
  have hS' := relSubstAtT_tail hM hS
  have hc' : M.Ap (EnvT.tail ρ) A c ∨ M.Ap (EnvT.tail ρ') A c := by
    rcases hc with hc | hc
    · exact Or.inl (hM.lift0_elim (S := ρ 0) (ρ := EnvT.tail ρ) (by rw [EnvT.cons_tail]; exact hc))
    · exact Or.inr (hM.lift0_elim (S := ρ' 0) (ρ := EnvT.tail ρ') (by rw [EnvT.cons_tail]; exact hc))
  have := hF hΔ hS' c hc'
  rw [substT_lift, substT_lift]
  exact this

theorem ctxValidAt_cons {M : CtxModelT E} (hM : CtxModelTLaws' M) {Γ : LCtx} (d : LocalDecl)
    (A : Expr Nat) (hd : lookupType (d :: Γ) 0 = some (lift 0 1 A))
    (hA : TyValidAt M R n Γ A) (hΓ : CtxValidAt M R n Γ) : CtxValidAt M R n (d :: Γ) := by
  intro i A' h
  cases i with
  | zero =>
      rw [hd] at h; injection h with h; subst h
      exact tyValidAt_lift hM d hA
  | succ i =>
      rw [lookupType_cons_succ] at h
      cases hA₀ : lookupType Γ i with
      | none => rw [hA₀] at h; exact Option.noConfusion h
      | some A₀ =>
          rw [hA₀] at h; injection h with h; subst h
          exact tyValidAt_lift hM d (hΓ i A₀ hA₀)

/-- The sort index of a type's relation is irrelevant. -/
theorem fundTyAt_sortIdx (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {M : CtxModelT E}
    {Γ : LCtx} {A : Expr Nat} {w w' : Level} (h : FundTyAt M R n Γ A (.sort w)) :
    FundTyAt M R n Γ A (.sort w') := fun hΔ hS c hc =>
  lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨w', .refl _⟩ c (h hΔ hS c hc)

/-! ### §2 — the inductive hypotheses below a size, and the structural cases -/

/-- The inductive hypotheses for every derivation of `sizeOf` below `k`, in any context. -/
def IHBelow (M : CtxModelT E) (R : Readback) (n : Nat) (k : Nat) : Prop :=
  (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), sizeOf d < k →
    CtxWfT E n Γ → CtxValidAt M R n Γ → FundTyAt M R n Γ e A ∧ TyValidAt M R n Γ A) ∧
  (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), sizeOf d < k →
    CtxWfT E n Γ → CtxValidAt M R n Γ → FundConvAt M R n Γ a b A ∧ TyValidAt M R n Γ A)

/-- Exact model-side input of `symm`/`tyConv`/`trans`: the compact is typed at a code of the
    derivation's type (the typing lemma, pointwise). -/
def TypingAt (M : CtxModelT E) (ρ ρ' : EnvT) (a b A : Expr Nat) : Prop :=
  ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c → ∃ a₀, (M.Ap ρ A a₀ ∨ M.Ap ρ' A a₀) ∧ CTyS E c a₀

/-- Exact model-side input of `trans`: the model's soundness of a conversion at one environment. -/
def ModelConvSoundAt (M : CtxModelT E) (ρ : EnvT) (a b : Expr Nat) : Prop :=
  ∀ c, M.Ap ρ a c ↔ M.Ap ρ b c

/-- **`symm` by the IH on the sub-derivation only**: at swapped environments, plus the typed PER
    at the type's own relation (the IH's validity conjunct) and the typing lemma. -/
theorem fundT_symm_strong (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (ih : FundConvAt M R n Γ b a A) (ihV : TyValidAt M R n Γ A)
    (hTy : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      TypingAt M ρ ρ' a b A) :
    FundConvAt M R n Γ a b A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  obtain ⟨w, hV⟩ := ihV
  obtain ⟨a₀, ha₀, hty⟩ := hTy hS c hc
  have hS' := RelSubstAtT.symm hW hcl hst hι hΓ hΔ hS
  have hrel : LRSCoreS R E n Δ (substT σ' b) (substT σ a) (substT σ' A) c :=
    ih hΔ hS' c (hc.symm)
  -- the type's relations from validity: `A[σ'] ~ A[σ]` and `A[σ'] ~ A[σ']` at `a₀`
  have hA'A : LRSCoreS R E n Δ (substT σ' A) (substT σ A) (.sort w) a₀ := hV hΔ hS' a₀ ha₀.symm
  have hA'A' : LRSCoreS R E n Δ (substT σ' A) (substT σ' A) (.sort w) a₀ := by
    rcases ha₀ with ha | ha
    · exact hV hΔ (RelSubstAtT.diagR hW hcl hst hι hΓ hΔ (hS.envs ρ ρ (Or.inl rfl) (Or.inl rfl)))
        a₀ (Or.inl ha)
    · exact hV hΔ (RelSubstAtT.diagR hW hcl hst hι hΓ hΔ (hS.envs ρ' ρ' (Or.inr rfl) (Or.inr rfl)))
        a₀ (Or.inl ha)
  have hsym := lrSCoreS_symm_tm hL hNU hW hCAs hCAt hΔ hA'A' hty hrel
  exact lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hA'A hty hsym

/-- The validity of an instance `B[arg]` from the validity of `B` under the binder (the β/app/let
    cases' validity output), given the model's β law. -/
theorem tyValidAt_inst (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hβ : ModelBetaExpandT M) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {u : Level} {arg B : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u)) (harg : HasTyT E n Γ arg A)
    (ihA : FundTyAt M R n Γ A (.sort u)) (iharg : FundTyAt M R n Γ arg A)
    (ihB : TyValidAt M R n (.assumption A :: Γ) B) :
    TyValidAt M R n Γ (instantiate0 arg B) := by
  obtain ⟨w, hB⟩ := ihB
  refine ⟨w, fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_⟩
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ hT hT' hcS
  obtain ⟨hargσ⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT
  obtain ⟨hargσ'⟩ := hasTyT_substT hW hcl hst hι hΓ harg hΔ hT'
  obtain ⟨hargc⟩ := convT_substT_pointwise hW hcl hst hι hΓ harg hΔ hT hT' hcS
  have hargσ'A : HasTyT E n Δ (substT σ' arg) (substT σ A) := .conv _ _ _ _ u hargσ' (.symm _ _ _ _ hAc)
  have finish : ∀ (a : CptT) (us : List CptT), (M.Ap ρ A a ∨ M.Ap ρ' A a) → (∀ v ∈ us, CTyS E v a) →
      (∀ v ∈ us, M.Ap ρ arg v ∨ M.Ap ρ' arg v) →
      (M.Ap (EnvT.cons (demandT us) ρ) B c ∨ M.Ap (EnvT.cons (demandT us) ρ') B c) →
      LRSCoreS R E n Δ (substT σ (instantiate0 arg B)) (substT σ' (instantiate0 arg B)) (.sort w) c := by
    intro a us ha hdT hus hb
    obtain ⟨hAA', hAA, _⟩ := domRelations_of_ih hW hcl hst hι hΓ ihA hΔ hS ha
    have hrel : ∀ v ∈ us, LRSCoreS R E n Δ (substT σ arg) (substT σ' arg) (substT σ A) v :=
      fun v hv => iharg hΔ hS v (hus v hv)
    have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM hΔ hS A u us hdT hAA' hAA hAc
      (substT σ arg) (substT σ' arg) hargσ hargσ'A hargc hrel
    have hih := hB hΔ hS' c hb
    rw [substT_instantiate0, substT_instantiate0]
    rw [← instantiate0_substT_up, ← instantiate0_substT_up] at hih
    exact hih
  rcases hc with hc | hc
  · obtain ⟨a, us, ha, hdT, hus, hb⟩ := hβ (A := A) hc
    exact finish a us (Or.inl ha) hdT (fun v hv => Or.inl (hus v hv)) (Or.inl hb)
  · obtain ⟨a, us, ha, hdT, hus, hb⟩ := hβ (A := A) hc
    exact finish a us (Or.inr ha) hdT (fun v hv => Or.inr (hus v hv)) (Or.inr hb)

/-! ### §3 — the case obligations and the principle -/

/-- **The per-constructor obligations**, each with the inductive hypotheses for every derivation
    of smaller `sizeOf` (in any context).  The structural cases `sort`, `bvar`, `pi`, `lam`,
    `refl`, `beta`, `symm` are discharged in `fund_step`; these are the remaining ones, stated
    with the exact IH shape so that every recursive call's decrease is explicit. -/
structure FundCases (M : CtxModelT E) (R : Readback) (n : Nat) : Prop where
  app : ∀ {Γ : LCtx} {f a A B : Expr Nat} (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (HasTyT.app Γ f a A B hf ha)) →
    FundTyAt M R n Γ (.app f a) (instantiate0 a B) ∧ TyValidAt M R n Γ (instantiate0 a B)
  const : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    FundTyAt M R n Γ (.const r ls) (instantiateLevels ls m.mtype) ∧
      TyValidAt M R n Γ (instantiateLevels ls m.mtype)
  letE : ∀ {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (HasTyT.letE Γ A u value B body hA hv hb)) →
    FundTyAt M R n Γ (.letE A value body) (instantiate0 value B) ∧
      TyValidAt M R n Γ (instantiate0 value B)
  lit : ∀ {Γ : LCtx} {t : Nat} {T : Expr Nat} (hexp : HasTyT E n Γ (natExpand t) T),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (HasTyT.lit Γ t T hexp)) →
    FundTyAt M R n Γ (.lit t) T ∧ TyValidAt M R n Γ T
  conv : ∀ {Γ : LCtx} {e A B : Expr Nat} {u : Level} (h : HasTyT E n Γ e A)
    (hc : ConvT E n Γ A B (.sort u)),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (HasTyT.conv Γ e A B u h hc)) →
    FundTyAt M R n Γ e B ∧ TyValidAt M R n Γ B
  trans : ∀ {Γ : LCtx} {a b c A : Expr Nat} (h1 : ConvT E n Γ a b A) (h2 : ConvT E n Γ b c A),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.trans Γ a b c A h1 h2)) →
    FundConvAt M R n Γ a c A ∧ TyValidAt M R n Γ A
  zeta : ∀ {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.zeta Γ A value body B u hA hv hb)) →
    FundConvAt M R n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B) ∧
      TyValidAt M R n Γ (instantiate0 value B)
  zetaLocal : ∀ {Γ : LCtx} {i : Nat} {A v : Expr Nat} (hval : lookupValue Γ i = some v)
    (hty : lookupType Γ i = some A) (hv : HasTyT E n Γ v A),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.zetaLocal Γ i A v hval hty hv)) →
    FundConvAt M R n Γ (.bvar i) v A ∧ TyValidAt M R n Γ A
  delta : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (htr : transparent m.mclass = true)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb)) →
    FundConvAt M R n Γ (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype) ∧
      TyValidAt M R n Γ (instantiateLevels ls m.mtype)
  iota : ∀ {Γ : LCtx} {lhs rhs T : Expr Nat} (h : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.iota Γ lhs rhs T h hlhs hrhs)) →
    FundConvAt M R n Γ lhs rhs T ∧ TyValidAt M R n Γ T
  litConv : ∀ {Γ : LCtx} {t : Nat} {exp T : Expr Nat} (h : LiteralExpansion t exp)
    (hexp : HasTyT E n Γ exp T),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.lit Γ t exp T h hexp)) →
    FundConvAt M R n Γ (.lit t) exp T ∧ TyValidAt M R n Γ T
  appConv : ∀ {Γ : LCtx} {f g a b A B : Expr Nat} (h1 : ConvT E n Γ f g (.pi A B))
    (h2 : ConvT E n Γ a b A),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.app Γ f g a b A B h1 h2)) →
    FundConvAt M R n Γ (.app f a) (.app g b) (instantiate0 a B) ∧ TyValidAt M R n Γ (instantiate0 a B)
  lamConv : ∀ {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hb : ConvT E n (.assumption A :: Γ) b b' B),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.lam Γ A A' b b' B u hA hb)) →
    FundConvAt M R n Γ (.lam A b) (.lam A' b') (.pi A B) ∧ TyValidAt M R n Γ (.pi A B)
  piConv : ∀ {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.pi Γ A A' B B' u v hA hB)) →
    FundConvAt M R n Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) ∧
      TyValidAt M R n Γ (.sort (.imax u v))
  letEConv : ∀ {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.letE Γ A A' v v' b b' B u hA hv hb)) →
    FundConvAt M R n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B) ∧
      TyValidAt M R n Γ (instantiate0 v B)
  sorts : ∀ {Γ : LCtx} {l₁ l₂ : Level} (h : eqN l₁ l₂), CtxWfT E n Γ → CtxValidAt M R n Γ →
    FundConvAt M R n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) ∧ TyValidAt M R n Γ (.sort (.succ l₁))
  consts : ∀ {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls'),
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    FundConvAt M R n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) ∧
      TyValidAt M R n Γ (instantiateLevels ls m.mtype)
  eta : ∀ {Γ : LCtx} {f A B : Expr Nat} (h : HasTyT E n Γ f (.pi A B)),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.eta Γ f A B h)) →
    FundConvAt M R n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) ∧ TyValidAt M R n Γ (.pi A B)
  irr : ∀ {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.irr Γ P p q hP hp hq)) →
    FundConvAt M R n Γ p q P ∧ TyValidAt M R n Γ P
  tyConv : ∀ {Γ : LCtx} {a b A A' : Expr Nat} {u : Level} (h : ConvT E n Γ a b A)
    (hA : ConvT E n Γ A A' (.sort u)),
    CtxWfT E n Γ → CtxValidAt M R n Γ → IHBelow M R n (sizeOf (ConvT.tyConv Γ a b A A' u h hA)) →
    FundConvAt M R n Γ a b A' ∧ TyValidAt M R n Γ A'
  symmTyping : ∀ {Γ : LCtx} {a b A : Expr Nat} (h : ConvT E n Γ b a A), CtxWfT E n Γ →
    ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      TypingAt M ρ ρ' a b A

/-- **One step of the induction**: the motive at a derivation from the motive below it. -/
theorem fund_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) (hβ : ModelBetaExpandT M) (hC : FundCases M R n) :
    (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), CtxWfT E n Γ → CtxValidAt M R n Γ →
      IHBelow M R n (sizeOf d) → FundTyAt M R n Γ e A ∧ TyValidAt M R n Γ A) ∧
    (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), CtxWfT E n Γ → CtxValidAt M R n Γ →
      IHBelow M R n (sizeOf d) → FundConvAt M R n Γ a b A ∧ TyValidAt M R n Γ A) := by
  refine ⟨fun {Γ e A} d hΓ hV ih => ?_, fun {Γ a b A} d hΓ hV ih => ?_⟩
  · cases d with
    | sort Γ l =>
        exact ⟨fundT_sort hM.toCtxModelTLaws l, .succ (.succ l), fundT_sort hM.toCtxModelTLaws (.succ l)⟩
    | bvar Γ i A h => exact ⟨fundT_bvar hM.toCtxModelTLaws i A h, hV i A h⟩
    | const Γ r ls m hres hlen hwf => exact hC.const hres hlen hwf hΓ hV
    | pi Γ A u B v hA hB =>
        have hltA : sizeOf hA < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
        have hltB : sizeOf hB < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
        obtain ⟨ihA, _⟩ := ih.1 hA hltA hΓ hV
        have hVA : TyValidAt M R n Γ A := ⟨u, ihA⟩
        obtain ⟨ihB, _⟩ := ih.1 hB hltB (.assumption Γ A u hΓ hA)
          (ctxValidAt_cons hM (.assumption A) A rfl hVA hV)
        exact ⟨fundT_pi hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hΓ hA hB ihA ihB,
          .succ (.imax u v), fundT_sort hM.toCtxModelTLaws (.imax u v)⟩
    | lam Γ A u body B hA hbody =>
        have hltA : sizeOf hA < sizeOf (HasTyT.lam Γ A u body B hA hbody) := by simp; omega
        have hltb : sizeOf hbody < sizeOf (HasTyT.lam Γ A u body B hA hbody) := by simp; omega
        obtain ⟨ihA, _⟩ := ih.1 hA hltA hΓ hV
        have hVA : TyValidAt M R n Γ A := ⟨u, ihA⟩
        have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
        obtain ⟨ihb, ⟨v, ihB⟩⟩ := ih.1 hbody hltb hΓ' (ctxValidAt_cons hM (.assumption A) A rfl hVA hV)
        obtain ⟨v', hB⟩ := tySort hW hΓ' hbody
        refine ⟨fundT_lam hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hΓ hA ihA ihb,
          .imax u v', ?_⟩
        exact fundT_pi hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hΓ hA hB ihA
          (fundTyAt_sortIdx hL hNU ihB)
    | app Γ f a A B hf ha => exact hC.app hf ha hΓ hV ih
    | letE Γ A u value B body hA hv hb => exact hC.letE hA hv hb hΓ hV ih
    | lit Γ t T hexp => exact hC.lit hexp hΓ hV ih
    | conv Γ e A B u h hc => exact hC.conv h hc hΓ hV ih
  · cases d with
    | refl Γ a A h =>
        have hlt : sizeOf h < sizeOf (ConvT.refl Γ a A h) := by simp; omega
        obtain ⟨ihT, hVA⟩ := ih.1 h hlt hΓ hV
        exact ⟨fundT_refl ihT, hVA⟩
    | symm Γ a b A h =>
        have hlt : sizeOf h < sizeOf (ConvT.symm Γ b a A h) := by simp; omega
        obtain ⟨ihc, hVA⟩ := ih.2 h hlt hΓ hV
        exact ⟨fundT_symm_strong hL hNU hW hcl hst hι hCAs hCAt hΓ ihc hVA
          (fun hS => hC.symmTyping h hΓ hS), hVA⟩
    | trans Γ a b c A h1 h2 => exact hC.trans h1 h2 hΓ hV ih
    | beta Γ A body arg B u hA hbody harg =>
        have hltA : sizeOf hA < sizeOf (ConvT.beta Γ A body arg B u hA hbody harg) := by simp; omega
        have hltb : sizeOf hbody < sizeOf (ConvT.beta Γ A body arg B u hA hbody harg) := by simp; omega
        have hlta : sizeOf harg < sizeOf (ConvT.beta Γ A body arg B u hA hbody harg) := by simp; omega
        obtain ⟨ihA, _⟩ := ih.1 hA hltA hΓ hV
        have hVA : TyValidAt M R n Γ A := ⟨u, ihA⟩
        have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
        obtain ⟨ihb, hVB⟩ := ih.1 hbody hltb hΓ' (ctxValidAt_cons hM (.assumption A) A rfl hVA hV)
        obtain ⟨iharg, _⟩ := ih.1 harg hlta hΓ hV
        exact ⟨fundT_beta hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hβ hΓ hA harg ihA ihb iharg,
          tyValidAt_inst hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hβ hΓ hA harg ihA iharg hVB⟩
    | zeta Γ A value body B u hA hv hb => exact hC.zeta hA hv hb hΓ hV ih
    | zetaLocal Γ i A v hval hty hv => exact hC.zetaLocal hval hty hv hΓ hV ih
    | delta Γ r ls m b hres hbody htr hlen hwf hb => exact hC.delta hres hbody htr hlen hwf hb hΓ hV ih
    | iota Γ lhs rhs T h hlhs hrhs => exact hC.iota h hlhs hrhs hΓ hV ih
    | lit Γ t exp T h hexp => exact hC.litConv h hexp hΓ hV ih
    | app Γ f g a b A B h1 h2 => exact hC.appConv h1 h2 hΓ hV ih
    | lam Γ A A' b b' B u hA hb => exact hC.lamConv hA hb hΓ hV ih
    | pi Γ A A' B B' u v hA hB => exact hC.piConv hA hB hΓ hV ih
    | letE Γ A A' v v' b b' B u hA hv hb => exact hC.letEConv hA hv hb hΓ hV ih
    | sorts Γ l₁ l₂ h => exact hC.sorts h hΓ hV
    | consts Γ r ls ls' m hres hlen hwf hwf' h => exact hC.consts hres hlen hwf hwf' h hΓ hV
    | eta Γ f A B h => exact hC.eta h hΓ hV ih
    | irr Γ P p q hP hp hq => exact hC.irr hP hp hq hΓ hV ih
    | tyConv Γ a b A A' u h hA => exact hC.tyConv h hA hΓ hV ih

/-- **The principle**: strong induction on `sizeOf` of the derivation. -/
theorem fund_strong (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) (hβ : ModelBetaExpandT M) (hC : FundCases M R n) :
    ∀ k : Nat, IHBelow M R n k := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun d hd => ?_, fun d hd => ?_⟩
      · exact absurd hd (Nat.not_lt_zero _)
      · exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
      obtain ⟨stepTy, stepConv⟩ := fund_step hL hNU hW hcl hst hι hCAs hCAt hM hβ hC
      refine ⟨fun d hd hΓ hV => ?_, fun d hd hΓ hV => ?_⟩
      · by_cases hk : sizeOf d < k
        · exact ih.1 d hk hΓ hV
        · have hk' : sizeOf d = k := by omega
          exact stepTy d hΓ hV (hk' ▸ ih)
      · by_cases hk : sizeOf d < k
        · exact ih.2 d hk hΓ hV
        · have hk' : sizeOf d = k := by omega
          exact stepConv d hΓ hV (hk' ▸ ih)

/-- Context validity from context well-formedness, by the lemma at the binders' derivations. -/
theorem ctxValidAt_of_ctxWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) (hβ : ModelBetaExpandT M) (hC : FundCases M R n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → CtxValidAt M R n Γ
  | [], _ => fun i A h => by simp [lookupType] at h
  | _ :: _, .assumption Γ A u hΓ hA => by
      have hV := ctxValidAt_of_ctxWfT hL hNU hW hcl hst hι hCAs hCAt hM hβ hC hΓ
      obtain ⟨ihA, _⟩ := (fund_strong hL hNU hW hcl hst hι hCAs hCAt hM hβ hC (sizeOf hA + 1)).1 hA
        (Nat.lt_succ_self _) hΓ hV
      exact ctxValidAt_cons hM (.assumption A) A rfl ⟨u, ihA⟩ hV
  | _ :: _, .letBinding Γ A u v hΓ hA hv => by
      have hV := ctxValidAt_of_ctxWfT hL hNU hW hcl hst hι hCAs hCAt hM hβ hC hΓ
      obtain ⟨ihA, _⟩ := (fund_strong hL hNU hW hcl hst hι hCAs hCAt hM hβ hC (sizeOf hA + 1)).1 hA
        (Nat.lt_succ_self _) hΓ hV
      exact ctxValidAt_cons hM (.letBinding A v) A rfl ⟨u, ihA⟩ hV

/-- **The fundamental lemma from the case obligations.** -/
theorem fundamentalSAtT_of_cases (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) (hβ : ModelBetaExpandT M) (hC : FundCases M R n) :
    FundamentalSAtT M R n := by
  refine ⟨fun {Γ} hΓ {e A} d => ?_, fun {Γ} hΓ {a b A} d => ?_⟩
  · exact ((fund_strong hL hNU hW hcl hst hι hCAs hCAt hM hβ hC (sizeOf d + 1)).1 d
      (Nat.lt_succ_self _) hΓ (ctxValidAt_of_ctxWfT hL hNU hW hcl hst hι hCAs hCAt hM hβ hC hΓ)).1
  · exact ((fund_strong hL hNU hW hcl hst hι hCAs hCAt hM hβ hC (sizeOf d + 1)).2 d
      (Nat.lt_succ_self _) hΓ (ctxValidAt_of_ctxWfT hL hNU hW hcl hst hι hCAs hCAt hM hβ hC hΓ)).1

/-! ### §4 — item 3: backward compact transport along a readback step -/

/-- **Backward compact transport** along one readback step: the compacts of the reduct are
    compacts of the redex.  A model fact (about `ApproxT`), the `b ⊆ a` half of
    `ReadbackModelInv`; it is `domAlign_of_chain`'s `hinv`. -/
def BackTransportT (R : Readback) (E : ResolvedEnv) (ρ : EnvT) (Γ : LCtx) : Prop :=
  ∀ {a b : Expr Nat} {c : CptT}, R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c

/-- Non-vacuity: the ζ-local rule, at every context environment, unconditionally. -/
theorem backTransportT_zetaLocal {E : ResolvedEnv} {Γ : LCtx} {ρ : EnvT} (hctx : CtxEnvT E Γ ρ) :
    BackTransportT (fun Γ' a b => ∃ i, a = .bvar i ∧ lookupValue Γ' i = some b) E ρ Γ := by
  intro a b c hs h
  obtain ⟨i, rfl, hv⟩ := hs
  exact (semEqT_zetaLocal hctx hv c).mpr h

/-- The congruence rule is inherited: if `f ↦ f'` transports backward, so does `app f a ↦ app f' a`. -/
theorem backTransportT_appHead_closure {E : ResolvedEnv} {ρ : EnvT} {f f' a : Expr Nat}
    (hf : ∀ {c : CptT}, ApproxT E ρ f' c → ApproxT E ρ f c) {c : CptT}
    (h : ApproxT E ρ (.app f' a) c) : ApproxT E ρ (.app f a) c := by
  rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, ha⟩ | ⟨r, args, u, rfl, hfr, ha⟩
  · exact .bot _ _
  · exact .app (hf hfg) hs ha
  · exact .appSpine (hf hfr) ha

/-- `domAlign_of_chain`'s hypothesis is exactly `BackTransportT`. -/
theorem domAlign_of_chain_backTransport {R : Readback} {E : ResolvedEnv} {n : Nat}
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx} {ρ : EnvT} {h : Nat}
    (hF : ∀ {X Y : Expr Nat} {u : Level} (hc : ConvT E n Γ X Y (.sort u)), sizeOf hc < h →
      ∀ c, ApproxT E ρ X c ∨ ApproxT E ρ Y c → LRSCoreS R E n Γ X Y (.sort u) c)
    (hinv : BackTransportT R E ρ Γ) {X Y : Expr Nat} (hch : ConvChainBelow E n Γ h X Y)
    {X₁ X₂ : Expr Nat} (hX : RedR R Γ X (.pi X₁ X₂)) (hm : ApproxT E ρ X (.pi .bot []))
    {Y₁ Y₂ : Expr Nat} (hY : RedR R Γ Y (.pi Y₁ Y₂)) : Nonempty (TyConvT E n Γ X₁ Y₁) :=
  domAlign_of_chain hL hNU hF (fun hs hb => hinv hs hb) hch hX hm hY

#print axioms TyValidAt
#print axioms CtxValidAt
#print axioms CtxModelTLaws'
#print axioms ctxModelTLaws'_approxT
#print axioms EnvT.tail
#print axioms EnvT.cons_tail
#print axioms relSubstAtT_tail
#print axioms RelSubstAtT.envs
#print axioms tyValidAt_lift
#print axioms ctxValidAt_cons
#print axioms fundTyAt_sortIdx
#print axioms IHBelow
#print axioms TypingAt
#print axioms ModelConvSoundAt
#print axioms fundT_symm_strong
#print axioms tyValidAt_inst
#print axioms FundCases
#print axioms fund_step
#print axioms fund_strong
#print axioms ctxValidAt_of_ctxWfT
#print axioms fundamentalSAtT_of_cases
#print axioms BackTransportT
#print axioms backTransportT_zetaLocal
#print axioms backTransportT_appHead_closure
#print axioms domAlign_of_chain_backTransport

end Rcic.Declarative.NativeValleys.TypedModelAudit
