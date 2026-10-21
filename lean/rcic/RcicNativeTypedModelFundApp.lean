import rcic.RcicNativeTypedModelFundStrong
import rcic.RcicNativeTypedModelTypingFin
import rcic.RcicNativeTypedModelRelSL

/-!
# RcicNativeTypedModelFundApp — the `app`/`appConv`/`conv` FundCases fields against
CTyCov-typed pointwise supplies and the pointwise β route (cc 20:00Z)

Per the #7738 audit (`TypingLemmaEnvFinT`/`ArgTypedFinAt` are FALSE at `ApproxT`;
`FundCases` as stated is not instantiable there — #7731), the three fields are delivered as
per-constructor facts over the LANDED relation (`FundTyAt`/`FundConvAt`/`TyValidAt`,
T-motive) with every unpaid input NAMED as a premise, in the shape the CTyCov typing lemma
(`covTyping_strong`) and the pointwise β supply (`ModelSubstFactorT` →
`modelBetaExpandTypedM_of_substFactor`) are to pay:

* `conv` — `fundT_conv` closes FULLY from the IHs plus one pointwise supply
  (`TypingAtConv`: the substituted conversion's endpoints relate at a sort code that types
  the demand compact).  The supplier `typingAtConv_of_diag` builds that supply from the
  conversion's own IH, the right endpoint's diagonal validity, and a right-endpoint compact.
* `app`/`appConv` — `fundT_app_of_spineExt` / `fundT_appConv_of_spineExt` close every
  non-spine compact from the LANDED `fundT_app`/`fundT_beta_pointwise` reasoning, and route
  the spine compacts to `AppSpineAtT`/`AppConvSpineAtT` (the extended `SpineClauseSL`, the
  exact named residue measured in #7721/#7723 as `AppArgActionT`'s relation-side content).
  The `TyValidAt (instantiate0 _ B)` conjunct takes `hVB` (the codomain's validity under the
  binder): the `HasTyT.app` derivation does not record it and no size-below inversion
  supplies it — a recorded boundary of the field as stated.

`closure_claim = 0`.  No `sorry`, no `Classical.choice`, axioms ⊆ {propext, Quot.sound}.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the declared-telescope walk and the one-argument extension of `ConvArgsT` -/

/-- The domain the LEFT argument list's walk reaches in a Π-telescope: the domain at the
    position one past the list (through instantiated codomains), or `none` when the list is
    empty.  Matches `ConvArgsT`'s recursion exactly (including the beyond-telescope walk
    measured in `convArgsT_beyondTelescope`). -/
def argDomAt : Expr Nat → List (Expr Nat) → Option (Expr Nat)
  | .pi A _, [] => some A
  | .pi _ B, f :: fs => argDomAt (instantiate0 f B) fs
  | _, _ => none

/-- Extending a `ConvArgsT` walk by one converted argument pair at the domain the left list
    reaches.  The extension of the relation's spine clause (§3) consumes this. -/
theorem convArgsT_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {D : Expr Nat} {y y' : Expr Nat}
    (hconv : ConvT E n Γ y y' D) :
    ∀ {T : Expr Nat} {xs xs' : List (Expr Nat)}, ConvArgsT E n Γ T xs xs' →
      argDomAt T xs = some D →
      ConvArgsT E n Γ T (xs ++ [y]) (xs' ++ [y']) := by
  intro T xs xs' hwalk
  induction hwalk with
  | nil T₀ =>
      intro hdom
      cases T₀ with
      | pi A B =>
        simp only [argDomAt] at hdom
        injection hdom with hdom
        subst hdom
        simp only [List.cons_append, List.nil_append]
        exact .cons _ _ _ _ _ _ ⟨hconv⟩ (.nil _)
      | bvar _ => exact Option.noConfusion hdom
      | sort _ => exact Option.noConfusion hdom
      | const _ _ => exact Option.noConfusion hdom
      | app _ _ => exact Option.noConfusion hdom
      | lam _ _ => exact Option.noConfusion hdom
      | letE _ _ _ => exact Option.noConfusion hdom
      | lit _ => exact Option.noConfusion hdom
  | cons A B f f' fs fs' hc hs ih =>
      intro hdom
      simp only [argDomAt] at hdom
      simp only [List.cons_append]
      exact .cons _ _ _ _ _ _ hc (ih hdom)

/-! ### §2 — the spine-extension supply and the `app` field -/

/-- The named spine residue of the `app` field: at every related substitution instance, the
    extended spine clause for the substituted application pair at the instantiated codomain
    index.  This is the relation-side content #7721/#7723 measured as `AppArgActionT`; the
    prefix clause comes from the head's IH and the extension algebra is §1's `convArgsT_snoc`
    + `spineClauseSL_app`. -/
def AppSpineAtT (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (f a B : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ r : Nat, ∀ args : List CptT,
    SpineClauseSL R E n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ B) r args

/-- **`app` (typing side)**: every non-spine compact closes from the landed `fundT_app`
    (composition; the `hns` exclusion is discharged by the compact's shape), the spine
    compacts are the named supply `hSpine`, and the codomain-validity conjunct takes `hVB`
    (the `HasTyT.app` derivation does not record the codomain's validity under the binder). -/
theorem fundT_app_of_spineExt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hβ : ModelBetaExpandT M) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A)
    (ihA : TyValidAt M R n Γ A)
    (ihf : FundTyAt M R n Γ f (.pi A B)) (iha : FundTyAt M R n Γ a A)
    (hSpine : AppSpineAtT M R n Γ f a (instantiate0 a B))
    (hVB : TyValidAt M R n (.assumption A :: Γ) B) :
    FundTyAt M R n Γ (.app f a) (instantiate0 a B) ∧
      TyValidAt M R n Γ (instantiate0 a B) := by
  obtain ⟨w, hAty⟩ := tySort hW hΓ ha
  obtain ⟨w', hAA⟩ := ihA
  have hAA' : FundTyAt M R n Γ A (.sort w) := fundTyAt_sortIdx hL hNU hAA
  refine ⟨fun hΔ hS c hc => ?_,
    tyValidAt_inst hL hNU hW hcl hst hι hCAs hCAt hM hβ hΓ hAty ha
      hAA' (fun hΔ' hS' c' hc' => iha hΔ' hS' c' hc') hVB⟩
  rcases c with _ | _ | _ | ⟨pa, pf⟩ | ⟨lg⟩ | ⟨r, args⟩
  · exact lrSCoreS_bot _ _ _ _
  · exact fundT_app hL hNU hW hcl hst hι hM hΓ hf ha ihf iha hΔ hS .prop
      (fun r' args' hne => (CptT.noConfusion hne : False).elim) hc
  · exact fundT_app hL hNU hW hcl hst hι hM hΓ hf ha ihf iha hΔ hS .sort
      (fun r' args' hne => (CptT.noConfusion hne : False).elim) hc
  · exact fundT_app hL hNU hW hcl hst hι hM hΓ hf ha ihf iha hΔ hS (.pi pa pf)
      (fun r' args' hne => (CptT.noConfusion hne : False).elim) hc
  · exact fundT_app hL hNU hW hcl hst hι hM hΓ hf ha ihf iha hΔ hS (.lam lg)
      (fun r' args' hne => (CptT.noConfusion hne : False).elim) hc
  · rw [lrSCoreS_spine_iff]
    exact spineClauseS_of_spineClauseSL (hSpine hΔ hS r args)


/-- The named spine residue of the `appConv` field: the extended spine clause for the
    substituted cross-application pair at the instantiated codomain index. -/
def AppConvSpineAtT (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (f a g b B : Expr Nat) :
    Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ r : Nat, ∀ args : List CptT,
    SpineClauseSL R E n Δ (substT σ (.app f a)) (substT σ' (.app g b)) (substT σ B) r args

/-- **`appConv`**: the λ-headed compacts close from `ih1`'s Π-clause at the argument pair
    (the `fundT_beta_pointwise` reasoning at `ConvT.app`'s premises; the endpoint typings come
    from `convEnds` regularity), the spine compacts are the named supply, and the codomain
    validity conjunct takes `ihA`/`iharg`/`hVB` (the `ConvT.app` constructor records none of
    them — a recorded boundary of the field as stated). -/
theorem fundT_appConv_of_spineExt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hβ : ModelBetaExpandT M) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f g a b A B : Expr Nat}
    (h1 : ConvT E n Γ f g (.pi A B)) (h2 : ConvT E n Γ a b A)
    (ih1 : FundConvAt M R n Γ f g (.pi A B)) (ih2 : FundConvAt M R n Γ a b A)
    (ihA : TyValidAt M R n Γ A) (iharg : FundTyAt M R n Γ a A)
    (hSpine : AppConvSpineAtT M R n Γ f a g b (instantiate0 a B))
    (hVB : TyValidAt M R n (.assumption A :: Γ) B) :
    FundConvAt M R n Γ (.app f a) (.app g b) (instantiate0 a B) ∧
      TyValidAt M R n Γ (instantiate0 a B) := by
  have hends := convEnds hW hΓ h2
  have haA := hends.1
  have hbA := hends.2.1
  have ⟨wA, hAty⟩ := hends.2.2
  obtain ⟨w', hAA⟩ := ihA
  have hAA' : FundTyAt M R n Γ A (.sort wA) := fundTyAt_sortIdx hL hNU hAA
  refine ⟨?_, tyValidAt_inst hL hNU hW hcl hst hι hCAs hCAt hM hβ hΓ hAty haA hAA'
    (fun hΔ' hS' c' hc' => iharg hΔ' hS' c' hc') hVB⟩
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hT := hS.1
  have hT' := hS.2.1
  have hcS := hS.2.2.1
  -- the cross-substituted argument conversion `a[σ] ≡ b[σ']` at `A[σ]`
  obtain ⟨haa⟩ := convT_substT_pointwise hW hcl hst hι hΓ haA hΔ hT hT' hcS
  obtain ⟨hbb'⟩ := convT_substT hW hcl hst hι hΓ h2 hΔ hT'
  obtain ⟨hAAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ hAty hΔ hT hT' hcS
  have hbb : ConvT E n Δ (substT σ' a) (substT σ' b) (substT σ A) :=
    .tyConv _ _ _ _ _ wA hbb' (.symm _ _ _ _ hAAc)
  have hconv_ab : ConvT E n Δ (substT σ a) (substT σ' b) (substT σ A) :=
    .trans _ _ _ _ _ haa hbb
  obtain ⟨haσ⟩ := hasTyT_substT hW hcl hst hι hΓ haA hΔ hT
  obtain ⟨hbσ'⟩ := hasTyT_substT hW hcl hst hι hΓ hbA hΔ hT'
  have hbσA : HasTyT E n Δ (substT σ' b) (substT σ A) :=
    .conv _ _ _ _ wA hbσ' (.symm _ _ _ _ hAAc)
  rcases hc with hc | hc
  · rcases hM.app_inv hc with rfl | ⟨g₀, s, rfl, hfg, hs, hau⟩ | ⟨r, args, u, rfl, hfg, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · have hih := ih1 hΔ hS (.lam g₀) (Or.inl hfg)
      rw [LRSCoreS.eq_def] at hih
      obtain ⟨A₁, B₁, hr, _, hcl⟩ := hih
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr (.refl _)
      subst eA; subst eB
      have hrel : ∀ u ∈ s.1, LRSCoreS R E n Δ (substT σ a) (substT σ' b) (substT σ A) u :=
        fun u hu => ih2 hΔ hS u (Or.inl (hau u hu))
      have hfin := hcl s hs (substT σ a) (substT σ' b) haσ hbσA ⟨hconv_ab⟩ hrel
      simp only [substT] at hfin ⊢
      rw [substT_instantiate0]
      exact hfin
    · rw [lrSCoreS_spine_iff]
      exact spineClauseS_of_spineClauseSL (hSpine hΔ hS r (args ++ [u]))
  · rcases hM.app_inv hc with rfl | ⟨g₀, s, rfl, hfg, hs, hau⟩ | ⟨r, args, u, rfl, hfg, _⟩
    · exact lrSCoreS_bot _ _ _ _
    · have hih := ih1 hΔ hS (.lam g₀) (Or.inr hfg)
      rw [LRSCoreS.eq_def] at hih
      obtain ⟨A₁, B₁, hr, _, hcl⟩ := hih
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr (.refl _)
      subst eA; subst eB
      have hrel : ∀ u ∈ s.1, LRSCoreS R E n Δ (substT σ a) (substT σ' b) (substT σ A) u :=
        fun u hu => ih2 hΔ hS u (Or.inr (hau u hu))
      have hfin := hcl s hs (substT σ a) (substT σ' b) haσ hbσA ⟨hconv_ab⟩ hrel
      simp only [substT] at hfin ⊢
      rw [substT_instantiate0]
      exact hfin
    · rw [lrSCoreS_spine_iff]
      exact spineClauseS_of_spineClauseSL (hSpine hΔ hS r (args ++ [u]))

/-- `foldApps` of a spine extended by one argument is the application of the prefix spine. -/
theorem foldApps_append_singleton (f : Expr Nat) (x : Expr Nat) :
    ∀ xs : List (Expr Nat), foldApps f (xs ++ [x]) = .app (foldApps f xs) x := by
  intro xs
  cases xs with
  | nil => rfl
  | cons y ys =>
      show foldApps (.app f y) (ys ++ [x]) = .app (foldApps (.app f y) ys) x
      exact foldApps_append_singleton (.app f y) x ys

/-- Assembling the extended spine clause of an application from the prefix data: the
    readbacks extend by `appHead` congruence (the raw substituted argument IS the new spine
    element — no argument readback is needed), the `ConvArgsT` walk extends by
    `convArgsT_snoc` at the walked domain, and the residues — the extended spines'
    normality and the saturation typings — are named. -/
theorem spineClauseSL_app (hL : ReadbackLaws E R) {Γ : LCtx} {F F' a a' T' D : Expr Nat}
    {r : Nat} {m : CheckedMember} {ls₁ ls₂ : List Level} {xs₁ xs₂ : List (Expr Nat)}
    {args : List CptT} {u : CptT}
    (hm : E.members r = some m) (hlen : ls₁.length = m.arity)
    (hwf₁ : levelsBounded n ls₁ = true) (hwf₂ : levelsBounded n ls₂ = true)
    (heq : eqNList ls₁ ls₂)
    (h1 : RedR R Γ F (foldApps (.const r ls₁) xs₁))
    (h2 : RedR R Γ F' (foldApps (.const r ls₂) xs₂))
    (hca : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂)
    (hl₁ : args.length ≤ xs₁.length) (hl₂ : args.length ≤ xs₂.length)
    (hn₁' : NormalR R Γ (foldApps (.const r ls₁) (xs₁ ++ [a])))
    (hn₂' : NormalR R Γ (foldApps (.const r ls₂) (xs₂ ++ [a'])))
    (hD : argDomAt (instantiateLevels ls₁ m.mtype) xs₁ = some D)
    (hconv : ConvT E n Γ a a' D)
    (hsat : (∃ l, RedR R Γ T' (.sort l)) → m.mclass = .inductiveM →
      (xs₁ ++ [a]).length = (piDomsOf m.mtype).length ∧
        (xs₂ ++ [a']).length = (piDomsOf m.mtype).length ∧
        (∃ w, Nonempty (HasTyT E n Γ (foldApps (.const r ls₁) (xs₁ ++ [a])) (.sort w))) ∧
        (∃ w', Nonempty (HasTyT E n Γ (foldApps (.const r ls₂) (xs₂ ++ [a'])) (.sort w')))) :
    SpineClauseSL R E n Γ (.app F a) (.app F' a') T' r (args ++ [u]) := by
  refine ⟨m, ls₁, ls₂, xs₁ ++ [a], xs₂ ++ [a'], hm, ?_, ?_, hn₁', hn₂', heq, hlen, hwf₁, hwf₂,
    ?_, ?_, convArgsT_snoc hconv hca hD, fun hs hind => hsat hs hind⟩
  · rw [foldApps_append_singleton]
    exact redR_appHead hL h1
  · rw [foldApps_append_singleton]
    exact redR_appHead hL h2
  · simp only [List.length_append, List.length_singleton]
    omega
  · simp only [List.length_append, List.length_singleton]
    omega

/-! ### §3 — `conv`: the type-conversion case for terms -/

/-- The pointwise supply the `conv` field consumes: at every related substitution instance,
    every demand compact of the term is typed (`CTyS`) at a sort code at which the
    substituted conversion's endpoints relate (`LRSCoreS A[σ] B[σ]`).  This is what the
    CTyCov typing lemma pays for a conversion at a sort: the two endpoint types share codes. -/
def TypingAtConv (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (e A B : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c →
      ∃ a₀ w, (M.Ap ρ A a₀ ∨ M.Ap ρ' A a₀ ∨ M.Ap ρ B a₀ ∨ M.Ap ρ' B a₀) ∧ CTyS E c a₀ ∧
        LRSCoreS R E n Δ (substT σ A) (substT σ B) (.sort w) a₀

/-- **`conv` (typing side)**: the type-conversion case closes from the term's own IH plus the
    pointwise shared-code supply — one `lrSCoreS_irrel` step reindexes the conclusion from
    `A[σ]` to `B[σ]`. -/
theorem fundT_conv (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {M : CtxModelT E} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e A B : Expr Nat} {u : Level} (h : HasTyT E n Γ e A)
    (hc : ConvT E n Γ A B (.sort u)) (ih_e : FundTyAt M R n Γ e A)
    (hTy : TypingAtConv M R n Γ e A B) :
    FundTyAt M R n Γ e B := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  obtain ⟨a₀, w, _, hcty, hAB⟩ := hTy hΔ hS c hc
  exact lrSCoreS_irrel hL hNU hW hCAs hCAt hΔ hAB hcty (ih_e hΔ hS c hc)

/-- The shared-code supply from the conversion's own IH and the right endpoint's diagonal
    validity: a right-endpoint compact typing the demand closes `TypingAtConv`. -/
theorem typingAtConv_of_diag (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hCAs : ConvArgsSymmS E n) (hCAt : ConvArgsTransS E n) {M : CtxModelT E} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e A B : Expr Nat} {u : Level} (hc : ConvT E n Γ A B (.sort u))
    (ihc : FundConvAt M R n Γ A B (.sort u)) (ihV_B : TyValidAt M R n Γ B)
    (hBc : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
      RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c →
        ∃ a₀, M.Ap ρ' B a₀ ∧ CTyS E c a₀) :
    TypingAtConv M R n Γ e A B := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  obtain ⟨a₀, ha₀B, hcty⟩ := hBc hΔ hS c hc
  obtain ⟨w, hV⟩ := ihV_B
  have hS' := RelSubstAtT.symm hW hcl hst hι hΓ hΔ hS
  have hAB' : LRSCoreS R E n Δ (substT σ A) (substT σ' B) (.sort u) a₀ :=
    ihc hΔ hS a₀ (Or.inr ha₀B)
  have hBB : LRSCoreS R E n Δ (substT σ' B) (substT σ B) (.sort w) a₀ :=
    hV hΔ hS' a₀ (Or.inl ha₀B)
  have hBB' : LRSCoreS R E n Δ (substT σ' B) (substT σ B) (.sort u) a₀ :=
    lrSCoreS_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨u, .refl _⟩ a₀ hBB
  exact ⟨a₀, u, Or.inr (Or.inr (Or.inr ha₀B)), hcty,
    lrSCoreS_trans hL hNU hW hCAs hCAt hΔ hAB' hBB'⟩


-- BEGIN GLM FUND APP SEAL (axiom queries; every public declaration)
#print axioms argDomAt
#print axioms convArgsT_snoc
#print axioms foldApps_append_singleton
#print axioms spineClauseSL_app
#print axioms AppSpineAtT
#print axioms fundT_app_of_spineExt
#print axioms AppConvSpineAtT
#print axioms fundT_appConv_of_spineExt
#print axioms TypingAtConv
#print axioms fundT_conv
#print axioms typingAtConv_of_diag
-- END GLM FUND APP SEAL

end Rcic.Declarative.NativeValleys.TypedModelAudit
