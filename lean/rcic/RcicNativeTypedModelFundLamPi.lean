import rcic.RcicNativeTypedModelFundStrong

/-!
# RcicNativeTypedModelFundLamPi — FundCases fields `lamConv`, `piConv` (swe-cleut lane)

The two binder-congruence cases of the fundamental lemma
(`RcicNativeTypedModelFundStrong:355`, `:359`), each as a theorem whose conclusion is exactly
the field's type.

* `lamConv` — `λ A. b ≡ λ A'. b'` at `Π A. B`.  The λ clause carries no domain code of its own
  beyond the `lam_inv` domain code `a`; the demand-relatedness of `relSubstAtT_cons` is paid by
  the conversion IH repackaged (`convDomRelations_of_ih`), and the β-expansion closes the
  applied sides (`lrSCoreS_expand`/`_right`).  Validity of `Π A. B` is the typing-side `pi`
  case fed by the domain's diagonal `FundTyAt` (`fundTyAt_of_fundConvAt`) and the body
  conversion IH's validity conjunct.
* `piConv` — `Π A. B ≡ Π A'. B'` at `sort (imax u v)`.  The Π clause needs the domain
  relation `A[σ] ~ A'[σ']` (the conversion IH outright), the left-to-left `A[σ] ~ A[σ]` and
  diagonal `A[σ] ~ A[σ]` for `relSubstAtT_cons` (`convDomRelations_of_ih`), and the two
  syntactic conversions `A[σ] ≡ A'[σ']`, `B[σ.up] ≡ B'[σ'.up]` — built by trans through the
  pointwise diagonal `A[σ] ≡ A[σ']` / `B'[σ.up] ≡ B'[σ'.up]` (`convT_substT_pointwise` on the
  regularity endpoints; the σ'.up landing context `assumption A[σ] :: Δ` is
  `typedSubstT_up_conv`).  Validity of `sort (imax u v)` is `fundT_sort`.

The only conversion-IH repackagings are `RelSubstAtT.symm` / `.diagL` / `.diagR` / `.envs`
(the symmetric related-substitution package, no PER needed to flip or to take a diagonal),
combined by the type-level PER `lrSCoreS_symm` / `lrSCoreS_trans`.  The manufactured
regularity derivations (`convEnds`, `tySort` outputs) feed only substitution lemmas —
`hasTyT_substT`, `convT_substT`, `convT_substT_pointwise`, `convSubstT_up_decl` — never the
inductive hypothesis.  No new model fact is consumed beyond `CtxModelTLaws` (`lam_inv`,
`pi_inv`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- The domain's three relations the binder cases feed to the Π clause and
    `relSubstAtT_cons`, from the domain's CONVERSION inductive hypothesis: `A[σ] ~ A'[σ']`
    outright, `A[σ] ~ A[σ']` by trans through `A'[σ'] ~ A[σ']` (the diagonal re-pairing plus
    the flip), and `A[σ] ~ A[σ]` by trans through the flip.  The compact approximates `A` on
    the left environment or `A'` on the right. -/
theorem convDomRelations_of_ih (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (ihA : FundConvAt M R n Γ A A' (.sort u)) {Δ : LCtx} (hΔ : CtxWfT E n Δ) {ρ ρ' : EnvT}
    {σ σ' : SubstT} (hS : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ) {a : CptT}
    (ha : M.Ap ρ A a ∨ M.Ap ρ' A' a) :
    LRSCoreS R E n Δ (substT σ A) (substT σ' A') (.sort u) a ∧
    LRSCoreS R E n Δ (substT σ A) (substT σ' A) (.sort u) a ∧
    LRSCoreS R E n Δ (substT σ A) (substT σ A) (.sort u) a := by
  have hσ'σ'ρ : RelSubstAtT M R n Δ ρ ρ σ' σ' Γ :=
    RelSubstAtT.diagR hW hcl hst hι hΓ hΔ (hS.envs ρ ρ (Or.inl rfl) (Or.inl rfl))
  have hσ'σ'ρ' : RelSubstAtT M R n Δ ρ' ρ' σ' σ' Γ :=
    RelSubstAtT.diagR hW hcl hst hι hΓ hΔ hS
  have hAA' : LRSCoreS R E n Δ (substT σ A) (substT σ' A') (.sort u) a := ihA hΔ hS a ha
  have hA'A : LRSCoreS R E n Δ (substT σ' A') (substT σ' A) (.sort u) a := by
    rcases ha with h | h
    · exact lrSCoreS_symm hL hNU hW hCAs hCAt hΔ (ihA hΔ hσ'σ'ρ a (Or.inl h))
    · exact lrSCoreS_symm hL hNU hW hCAs hCAt hΔ (ihA hΔ hσ'σ'ρ' a (Or.inr h))
  exact ⟨hAA',
    lrSCoreS_trans hL hNU hW hCAs hCAt hΔ hAA' hA'A,
    lrSCoreS_trans hL hNU hW hCAs hCAt hΔ hAA'
      (lrSCoreS_symm hL hNU hW hCAs hCAt hΔ hAA')⟩

/-- The domain's self-relation `A[σ] ~ A[σ']` at a compact approximating `A` on either
    environment: the conversion IH re-paired at the diagonal and flipped substitution
    packages, chained by the type-level PER.  This is the `TyValidAt A` input of
    `ctxValidAt_cons` for the binder cases — the conversion IH's own validity conjunct is
    `TyValidAt (.sort u)`, not `TyValidAt A`. -/
theorem fundTyAt_of_fundConvAt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (ihA : FundConvAt M R n Γ A A' (.sort u)) : FundTyAt M R n Γ A (.sort u) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hSymm : RelSubstAtT M R n Δ ρ' ρ σ' σ Γ :=
    RelSubstAtT.symm hW hcl hst hι hΓ hΔ hS
  have hσσρ' : RelSubstAtT M R n Δ ρ' ρ' σ σ Γ :=
    RelSubstAtT.diagL hW hcl hst hι hΓ hΔ (hS.envs ρ' ρ' (Or.inr rfl) (Or.inr rfl))
  have hσ'σ'ρ : RelSubstAtT M R n Δ ρ ρ σ' σ' Γ :=
    RelSubstAtT.diagR hW hcl hst hι hΓ hΔ (hS.envs ρ ρ (Or.inl rfl) (Or.inl rfl))
  rcases hc with hc | hc
  · -- `c` approximates `A` on the left environment: `A[σ] ~ A'[σ']` then `A'[σ'] ~ A[σ']`
    exact lrSCoreS_trans hL hNU hW hCAs hCAt hΔ (ihA hΔ hS c (Or.inl hc))
      (lrSCoreS_symm hL hNU hW hCAs hCAt hΔ (ihA hΔ hσ'σ'ρ c (Or.inl hc)))
  · -- `c` approximates `A` on the right environment: `A[σ] ~ A'[σ]` then `A'[σ] ~ A[σ']`
    exact lrSCoreS_trans hL hNU hW hCAs hCAt hΔ (ihA hΔ hσσρ' c (Or.inl hc))
      (lrSCoreS_symm hL hNU hW hCAs hCAt hΔ (ihA hΔ hSymm c (Or.inl hc)))

/-- **`lamConv`.**  `λ A. b ≡ λ A'. b'` at `Π A. B`, from the domain conversion IH and the
    body conversion IH under the extended substitution. -/
theorem fundT_lamConv (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hb : ConvT E n (.assumption A :: Γ) b b' B) :
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.lam Γ A A' b b' B u hA hb)) →
    FundConvAt M R n Γ (.lam A b) (.lam A' b') (.pi A B) ∧ TyValidAt M R n Γ (.pi A B) := by
  intro hΓ hV ih
  have hAtyL := (convEnds hW hΓ hA).1
  have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hAtyL
  have hltA : sizeOf hA < sizeOf (ConvT.lam Γ A A' b b' B u hA hb) := by simp; omega
  have hltb : sizeOf hb < sizeOf (ConvT.lam Γ A A' b b' B u hA hb) := by simp; omega
  obtain ⟨ihcA, _⟩ := ih.2 hA hltA hΓ hV
  have hVA : TyValidAt M R n Γ A :=
    ⟨u, fundTyAt_of_fundConvAt hL hNU hW hcl hst hι hCAs hCAt hΓ ihcA⟩
  obtain ⟨ihcb, hVB⟩ := ih.2 hb hltb hΓ' (ctxValidAt_cons hM (.assumption A) A rfl hVA hV)
  obtain ⟨v', hBty⟩ := tySort hW hΓ' (convEnds hW hΓ' hb).1
  obtain ⟨w₀, ihB₀⟩ := hVB
  refine ⟨?_, .imax u v', ?_⟩
  · intro Δ ρ ρ' σ σ' hΔ hS c hc
    have hT := hS.1
    have hT' := hS.2.1
    have hcS := hS.2.2.1
    obtain ⟨hAσ⟩ := hasTyT_substT hW hcl hst hι hΓ hAtyL hΔ hT
    obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hAtyL hΔ hT hT' hcS
    -- the compact: `.bot` or a λ compact whose domain code approximates `A`/`A'` on one side
    have key : ∀ (ρ₀ : EnvT) (A₀ b₀ : Expr Nat),
        (ρ₀ = ρ ∨ ρ₀ = ρ') → M.Ap ρ₀ (.lam A₀ b₀) c →
        (∀ {a' : CptT}, M.Ap ρ₀ A₀ a' → M.Ap ρ A a' ∨ M.Ap ρ' A' a') →
        (∀ {s₂ : CptT} (d : List CptT), M.Ap (EnvT.cons (demandT d) ρ₀) b₀ s₂ →
          M.Ap (EnvT.cons (demandT d) ρ) b s₂ ∨ M.Ap (EnvT.cons (demandT d) ρ') b' s₂) →
        LRSCoreS R E n Δ (substT σ (.lam A b)) (substT σ' (.lam A' b'))
          (substT σ (.pi A B)) c := by
      intro ρ₀ A₀ b₀ _ hc' hdom hbody
      rcases hM.toCtxModelTLaws.lam_inv hc' with rfl | ⟨a, g, rfl, ha, _, hg⟩
      · exact lrSCoreS_bot _ _ _ _
      · obtain ⟨_, hAA2, hAA⟩ := convDomRelations_of_ih hL hNU hW hcl hst hι hCAs hCAt hΓ ihcA
          hΔ hS (hdom ha)
        simp only [substT]
        rw [LRSCoreS.eq_def]
        refine ⟨substT σ A, substT σ.up B, .refl _, ⟨.assumption Δ _ u hΔ hAσ⟩, ?_⟩
        intro s hs N N' hN hN' hcN hrel
        obtain ⟨hdT, hb₀⟩ := hg s hs
        obtain ⟨hcN⟩ := hcN
        have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM.toCtxModelTLaws hΔ hS A u s.1 hdT
          hAA2 hAA hAc N N' hN hN' hcN hrel
        have hih := ihcb hΔ hS' s.2 (hbody s.1 hb₀)
        rw [← instantiate0_substT_up, ← instantiate0_substT_up, ← instantiate0_substT_up] at hih
        exact lrSCoreS_expand hL (hL.beta _ _ _ _) s.2
          (lrSCoreS_expand_right hL (hL.beta _ _ _ _) s.2 hih)
    rcases hc with hc | hc
    · exact key ρ A b (Or.inl rfl) hc (fun h => Or.inl h) (fun _ h => Or.inl h)
    · exact key ρ' A' b' (Or.inr rfl) hc (fun h => Or.inr h) (fun _ h => Or.inr h)
  · exact fundT_pi hL hNU hW hcl hst hι hCAs hCAt hM.toCtxModelTLaws hΓ hAtyL hBty
      (fundTyAt_of_fundConvAt hL hNU hW hcl hst hι hCAs hCAt hΓ ihcA)
      (fundTyAt_sortIdx hL hNU ihB₀)

/-- **`piConv`.**  `Π A. B ≡ Π A'. B'` at `sort (imax u v)`: the Π clause of the relation at
    each Π compact, from the domain conversion IH and the codomain conversion IH under the
    extended substitution. -/
theorem fundT_piConv (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws' M) {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    IHBelow M R n (sizeOf (ConvT.pi Γ A A' B B' u v hA hB)) →
    FundConvAt M R n Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) ∧
      TyValidAt M R n Γ (.sort (.imax u v)) := by
  intro hΓ hV ih
  have hAtyL := (convEnds hW hΓ hA).1
  have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hAtyL
  have hBtyR := (convEnds hW hΓ' hB).2.1
  have hltA : sizeOf hA < sizeOf (ConvT.pi Γ A A' B B' u v hA hB) := by simp; omega
  have hltB : sizeOf hB < sizeOf (ConvT.pi Γ A A' B B' u v hA hB) := by simp; omega
  obtain ⟨ihcA, _⟩ := ih.2 hA hltA hΓ hV
  have hVA : TyValidAt M R n Γ A :=
    ⟨u, fundTyAt_of_fundConvAt hL hNU hW hcl hst hι hCAs hCAt hΓ ihcA⟩
  obtain ⟨ihcB, _⟩ := ih.2 hB hltB hΓ' (ctxValidAt_cons hM (.assumption A) A rfl hVA hV)
  refine ⟨?_, .succ (.imax u v), fundT_sort hM.toCtxModelTLaws (.imax u v)⟩
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  obtain ⟨hAσ⟩ := hasTyT_substT hW hcl hst hι hΓ hAtyL hΔ hT
  obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hAtyL hΔ hT hT' hcS
  obtain ⟨hAcA'⟩ := convT_substT hW hcl hst hι hΓ hA hΔ hT'
  -- the domain conversion `A[σ] ≡ A'[σ']` through the diagonal `A[σ] ≡ A[σ']`
  have hAc' : ConvT E n Δ (substT σ A) (substT σ' A') (.sort u) :=
    .trans _ _ _ _ _ hAc hAcA'
  -- the codomain conversion `B[σ.up] ≡ B'[σ'.up]` at `assumption A[σ] :: Δ`
  have hΔ' : CtxWfT E n (.assumption (substT σ A) :: Δ) := .assumption Δ _ u hΔ hAσ
  obtain ⟨hBc1⟩ := convT_substT hW hcl hst hι hΓ' hB hΔ' (typedSubstT_up hcl hT A)
  obtain ⟨hBc2⟩ := convT_substT_pointwise hW hcl hst hι hΓ' hBtyR hΔ'
    (typedSubstT_up hcl hT A) (typedSubstT_up_conv hcl hT' A u hAc)
    (convSubstT_up_decl hcl hcS _ _ A rfl (.bvar _ 0 _ rfl))
  have hBc' : ConvT E n (.assumption (substT σ A) :: Δ) (substT σ.up B) (substT σ'.up B')
      (.sort v) := .trans _ _ _ _ _ hBc1 hBc2
  -- the compact: `.bot` or a Π compact whose domain code approximates `A`/`A'` on one side
  have key : ∀ (ρ₀ : EnvT) (A₀ B₀ : Expr Nat),
      (ρ₀ = ρ ∨ ρ₀ = ρ') → M.Ap ρ₀ (.pi A₀ B₀) c →
      (∀ {a' : CptT}, M.Ap ρ₀ A₀ a' → M.Ap ρ A a' ∨ M.Ap ρ' A' a') →
      (∀ {s₂ : CptT} (d : List CptT), M.Ap (EnvT.cons (demandT d) ρ₀) B₀ s₂ →
        M.Ap (EnvT.cons (demandT d) ρ) B s₂ ∨ M.Ap (EnvT.cons (demandT d) ρ') B' s₂) →
      LRSCoreS R E n Δ (substT σ (.pi A B)) (substT σ' (.pi A' B'))
        (substT σ (.sort (.imax u v))) c := by
    intro ρ₀ A₀ B₀ _ hc' hdom hcod
    rcases hM.toCtxModelTLaws.pi_inv hc' with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact lrSCoreS_bot _ _ _ _
    · obtain ⟨hAA', hAA2, hAA⟩ := convDomRelations_of_ih hL hNU hW hcl hst hι hCAs hCAt hΓ ihcA
        hΔ hS (hdom ha)
      simp only [substT]
      rw [LRSCoreS.eq_def]
      refine ⟨⟨_, .refl _⟩, substT σ A, substT σ.up B, substT σ' A', substT σ'.up B',
        .refl _, .refl _, ⟨hΔ'⟩, ⟨.of _ _ _ u hAc'⟩, ⟨.of _ _ _ v hBc'⟩, ⟨u, hAA'⟩, ?_⟩
      intro s hs hdT N N' hN hN' hcN hrel
      obtain ⟨hcN⟩ := hcN
      have hS' := relSubstAtT_cons hL hNU hW hCAs hCAt hM.toCtxModelTLaws hΔ hS A u s.1 hdT
        hAA2 hAA hAc N N' hN hN' hcN hrel
      obtain ⟨_, hBs⟩ := hf s hs
      have hih := ihcB hΔ hS' s.2 (hcod s.1 hBs)
      rw [← instantiate0_substT_up, ← instantiate0_substT_up] at hih
      exact ⟨v, hih⟩
  rcases hc with hc | hc
  · exact key ρ A B (Or.inl rfl) hc (fun h => Or.inl h) (fun _ h => Or.inl h)
  · exact key ρ' A' B' (Or.inr rfl) hc (fun h => Or.inr h) (fun _ h => Or.inr h)

#print axioms convDomRelations_of_ih
#print axioms fundTyAt_of_fundConvAt
#print axioms fundT_lamConv
#print axioms fundT_piConv
