import rcic.RcicNativeTypedModelFundStrong

/-!
# RcicNativeTypedModelProbe — the Π probe without model transport; the typed, realised model laws

Response to the independent audit of segment 8 (#7721).  Two of its findings are accepted and
acted on here:

1. **Raw backward transport is unsatisfiable** with `ReadbackLaws` (`no_readback_with_raw_approxT_back`):
   `z = (λ (x : D). x) P`, `D = λ (x : Sort 0). x`, `P = Π (X : Sort 0). Sort 0` — the raw β
   law gives `R Γ z P`, `P` has the probe `pi ⊥ []`, every `ApproxT` compact of `z` is `⊥`.
   The same instance refutes the raw `ModelBetaExpandT` for `ApproxT`.
2. **The chain consumer does not need it.**  At the probe `pi ⊥ []` the typed relation agrees
   with the landed untyped one (`piProbeS_iff`), so the landed `BotPiCpt` PER applies with no
   `ConvArgs` premise, and **a link supplies its own next diagonal** (`piProbeS_right_diag`) —
   the route #7721's `RcicNativePiCycleProbe` takes.  `domAlign_of_chain_probe` re-proves the
   alignment with the single links **seeded by the relation** (`LinkSeededBelow`: `X ~ X` at the
   probe, instead of `pi ⊥ [] ∈ ⟦X⟧ρ`), and `nodeDeclAlign_const_of_probeLinks` the constant-head
   alignment; `BackTransportT` is not used.  The seed exists for every Π-type whose domain is
   typed (`lrSCoreS_pi_self`).

**The typed, realised replacements** of the two raw laws (item of the ruling): `ArgTypedAt`
(the argument's compacts are jointly typed at one code of the binder's type, in the model),
`ModelBetaExpandTyped` and `BackTransportBetaTyped` (β expansion / backward β transport only for
redexes whose argument is so typed).  Tested at the counterexample first, as required:
`not_argTypedAt_cex` — `P`'s compact `pi ⊥ []` is typed at no code of `D` (every code of `D` is
`⊥` or a λ code, which type only `⊥`), so neither typed law says anything about `z`
(`modelBetaExpandTyped_excludes_cex`).  Named risk for the port (swe-zeta): joint typing of a
term's compacts at ONE code is a directedness property of `⟦A⟧` under `CTyS`, and `CTyS`'s
universal codomain clause is anti-monotone in the codomain's steps.

**Seeding the fundamental lemma.**  The relation-seeded link is `PiProbeLinkT`'s shape and
closes `symm`/`trans` by the probe PER with no model transport — but a relation seed alone fails
`irr` (a proof `p ~ p` at the probe would force any `q` of the same proposition to read back to a
Π), which the model seed handles by the collapse.  The hybrid — a compact **typed at a code of
the derivation's type**, realised in the model OR self-related — makes `irr` trivial (`CTyS` at a
proposition code is `⊥`) and keeps `trans` transport-free (`fundConvAt_hybrid_trans_shape`).
That typing hypothesis is exactly where the typing lemma enters the simultaneous induction, as
segment 9's `TypingAt` already names.

**Adapters** (#7721's missing connections): `fundConvAt_ctx_of_id` (related-substitution →
identity-substitution form, given the identity package `RelSubstIdT`); the codomain
continuation along the chain (`domCodAlign_of_chain_probe`: the clause stores the codomain
conversion under the left binder, and later links' codomain conversions are moved to the first
binder by context transport along the accumulated domain alignment, `convT_ctx_tyConvT` — each
`TyConvT.of` step is a single-sort `CtxConvT.assumption`, no sort uniqueness); and the
environment-typing field `EnvTypedAtT` with the typed package `RelSubstTypedAtT`, under which
segment 9's `TypingAt` is the generalised typing lemma `TypingLemmaEnvT`'s conclusion
(`typingAt_of_typedPackage`).  `TypingLemmaEnvT` is the named model-side input; `TypingLemmaT`
(at `ctxEnvT`) is its instance, not a substitute.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — at the probe the typed relation is the landed one; its PER needs no premise -/

/-- The Π probe is the same observation in `LRSCoreS` and the landed `LRSCore`. -/
theorem piProbeS_iff {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreS R E n Γ M N A (.pi .bot []) ↔ LRSCore R E n Γ M N A (.pi .bot []) := by
  rw [LRSCoreS.eq_def, LRSCore.eq_def]
  constructor
  · rintro ⟨hidx, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, _⟩, _⟩
    exact ⟨hidx, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, lrSCore_bot _ _ _ _⟩,
      fun _ hs => (List.not_mem_nil _ hs).elim⟩
  · rintro ⟨hidx, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, _⟩, _⟩
    exact ⟨hidx, A₁, B₁, A₂, B₂, hM, hN, hΓ, hA, hB, ⟨u, lrSCoreS_bot _ _ _ _⟩,
      fun _ hs _ => (List.not_mem_nil _ hs).elim⟩

theorem piProbeS_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N A : Expr Nat}
    (h : LRSCoreS R E n Γ M N A (.pi .bot [])) : LRSCoreS R E n Γ N M A (.pi .bot []) :=
  piProbeS_iff.mpr (lrSCore_symm_botPiCpt hW hΓ
    PiModelDeltaIotaAudit.botPiCpt_pi_bot_nil (piProbeS_iff.mp h))

theorem piProbeS_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N P A : Expr Nat} (h₁ : LRSCoreS R E n Γ M N A (.pi .bot []))
    (h₂ : LRSCoreS R E n Γ N P A (.pi .bot [])) : LRSCoreS R E n Γ M P A (.pi .bot []) :=
  piProbeS_iff.mpr (lrSCore_trans_botPiCpt hL hNU hW hΓ
    PiModelDeltaIotaAudit.botPiCpt_pi_bot_nil
    (piProbeS_iff.mp h₁) (piProbeS_iff.mp h₂))

/-- **A link supplies its own next diagonal.** -/
theorem piProbeS_right_diag (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N A : Expr Nat} (h : LRSCoreS R E n Γ M N A (.pi .bot [])) :
    LRSCoreS R E n Γ N N A (.pi .bot []) :=
  piProbeS_trans hL hNU hW hΓ (piProbeS_symm hW hΓ h) h

/-- A Π-type with a typed domain is self-related at the probe. -/
theorem lrSCoreS_pi_self {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) :
    LRSCoreS R E n Γ (.pi A B) (.pi A B) (.sort w) (.pi .bot []) := by
  rw [LRSCoreS.eq_def]
  exact ⟨⟨w, .refl _⟩, A, B, A, B, .refl _, .refl _, ⟨.assumption Γ A u hΓ hA⟩, ⟨.refl _ _⟩,
    ⟨.refl _ _⟩, ⟨u, lrSCoreS_bot _ _ _ _⟩, fun _ hs _ => (List.not_mem_nil _ hs).elim⟩

/-! ### §2 — the chain consumer without model transport -/

/-- The relation-seeded single links below a size: a conversion at a sort preserves a
    self-related Π probe (the `PiProbeLinkT` shape, bounded). -/
def LinkSeededBelow (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (h : Nat) : Prop :=
  ∀ {X Y : Expr Nat} {u : Level} (hc : ConvT E n Γ X Y (.sort u)), sizeOf hc < h →
    LRSCoreS R E n Γ X X (.sort u) (.pi .bot []) → LRSCoreS R E n Γ X Y (.sort u) (.pi .bot [])

/-- **The alignment from relation-seeded links**: no model, no backward transport.  The seed
    is carried along the chain by the probe PER. -/
theorem domAlign_of_chain_probe (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {h : Nat} (hF : LinkSeededBelow R E n Γ h) :
    ∀ {X Y : Expr Nat}, ConvChainBelow E n Γ h X Y →
      ∀ {u : Level}, LRSCoreS R E n Γ X X (.sort u) (.pi .bot []) →
      ∀ {X₁ X₂ : Expr Nat}, RedR R Γ X (.pi X₁ X₂) →
      ∀ {Y₁ Y₂ : Expr Nat}, RedR R Γ Y (.pi Y₁ Y₂) → Nonempty (TyConvT E n Γ X₁ Y₁) := by
  intro X Y hch
  induction hch with
  | refl X =>
      intro u _ X₁ X₂ hX Y₁ Y₂ hY
      obtain ⟨eA, _⟩ := redR_pi_unique hL hNU hX hY
      subst eA
      exact ⟨.refl _ _⟩
  | step hc hlt rest ih =>
      intro u hself X₁ X₂ hX Y₁ Y₂ hY
      -- the link at `u'` (the conversion's sort): move the seed's index
      rename_i X₀ M Z u'
      have hself' : LRSCoreS R E n Γ X₀ X₀ (.sort u') (.pi .bot []) :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨u', .refl _⟩ _ hself
      have hlink := hF hc hlt hself'
      obtain ⟨A₁, A₂, B₁, B₂, hXr, hMr, ⟨hd⟩⟩ := lrSCoreS_pi_probe hlink
      obtain ⟨eA, _⟩ := redR_pi_unique hL hNU hX hXr
      subst eA
      have hnext := piProbeS_right_diag hL hNU hW hΓ hlink
      obtain ⟨hrest⟩ := ih hnext hMr hY
      exact ⟨.trans _ _ _ _ hd hrest⟩

/-- **The constant-head alignment from relation-seeded links** — the Π-injectivity instance
    W-FAMSPINE and NodeDeclAlign need, at a strictly smaller measure, with no model input. -/
theorem nodeDeclAlign_const_of_probeLinks (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls : List Level} {A B : Expr Nat}
    (d : HasTyT E n Γ (.const r ls) (.pi A B)) (hF : LinkSeededBelow R E n Γ (sizeOf d))
    {m : CheckedMember} {dA dB : Expr Nat} (hm : E.members r = some m)
    (hdecl : instantiateLevels ls m.mtype = .pi dA dB) {u : Level}
    (hdA : HasTyT E n Γ dA (.sort u)) : Nonempty (TyConvT E n Γ dA A) := by
  obtain ⟨m', hm', chain⟩ := convChainBelow_const d
  rw [hm] at hm'
  injection hm' with hm'
  subst hm'
  rw [hdecl] at chain
  exact domAlign_of_chain_probe hL hNU hW hΓ hF chain (lrSCoreS_pi_self hΓ hdA (w := u))
    (.refl _) (.refl _)

/-! ### §3 — the typed, realised model laws, tested at the counterexample -/

/-- The argument's compacts are jointly typed at one code of the binder's type. -/
def ArgTypedAt (E : ResolvedEnv) (ρ : EnvT) (arg A : Expr Nat) : Prop :=
  ∃ a : CptT, ApproxT E ρ A a ∧ ∀ u, ApproxT E ρ arg u → CTyS E u a

/-- **Typed β expansion**: for a redex whose argument is jointly typed at a code of the binder's
    type, a compact of the instance comes from a compact of the body under a demand realised by
    the argument and typed at that code. -/
def ModelBetaExpandTyped (E : ResolvedEnv) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, ArgTypedAt E ρ arg A →
    ApproxT E ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), ApproxT E ρ A a ∧ (∀ u ∈ us, CTyS E u a) ∧
      (∀ u ∈ us, ApproxT E ρ arg u) ∧ ApproxT E (EnvT.cons (demandT us) ρ) body c

/-- **Typed backward β transport**: the same restriction, in transport form. -/
def BackTransportBetaTyped (E : ResolvedEnv) : Prop :=
  ∀ {ρ : EnvT} {A arg body : Expr Nat} {c : CptT}, ArgTypedAt E ρ arg A →
    ApproxT E ρ (instantiate0 arg body) c → ApproxT E ρ (.app (.lam A body) arg) c

/-- Typed β expansion gives typed backward transport (the λ clause needs a non-`⊥` output; at
    `⊥` the `bot` clause applies). -/
theorem backTransportBetaTyped_of_expand (h : ModelBetaExpandTyped E) : BackTransportBetaTyped E := by
  intro ρ A arg body c hT hc
  obtain ⟨a, us, hA, hus, hreal, hb⟩ := h hT hc
  cases c <;> first
    | exact .bot _ _
    | exact .app (.lam hA (fun s hs u hu => by
          have := List.mem_singleton.mp hs
          subst this
          exact hus u hu)
        ⟨(us, _), List.mem_singleton.mpr rfl, fun e => (CptT.noConfusion e : False)⟩
        (fun s hs => by
          have := List.mem_singleton.mp hs
          subst this
          exact hb))
        (List.mem_singleton.mpr rfl) hreal

/-- #7721's counterexample: the binder "type" `D = λ (x : Sort 0). x` and the argument
    `P = Π (X : Sort 0). Sort 0`. -/
def cexD : Expr Nat := .lam (.sort .zero) (.bvar 0)
def cexP : Expr Nat := .pi (.sort .zero) (.sort .zero)

/-- Every code of `D` is `⊥` or a λ code. -/
theorem approxT_cexD_shape {ρ : EnvT} {a : CptT} (h : ApproxT E ρ cexD a) :
    a = .bot ∨ ∃ g, a = .lam g := by
  rcases approxT_lam_inv h with h0 | ⟨_, g, rfl, _⟩
  · exact Or.inl h0
  · exact Or.inr ⟨g, rfl⟩

/-- **The typed laws exclude the counterexample**: `P` is not jointly typed at any code of `D`
    (its compact `pi ⊥ []` is typed only at type codes, and `D` has none). -/
theorem not_argTypedAt_cex (E : ResolvedEnv) (ρ : EnvT) : ¬ ArgTypedAt E ρ cexP cexD := by
  rintro ⟨a, hDa, hty⟩
  have hP : ApproxT E ρ cexP (.pi .bot []) := approxT_pi_bot_nil E ρ _ _
  have := hty _ hP
  rcases approxT_cexD_shape hDa with rfl | ⟨g, rfl⟩
  · exact CptT.noConfusion (ctyS_bot_inv this)
  · exact CptT.noConfusion (ctyS_lam_inv this)

/-- So `ModelBetaExpandTyped` says nothing about `z = (λ (x : D). x) P`: its hypothesis is
    false there, while the raw law's conclusion is refuted by #7721. -/
theorem modelBetaExpandTyped_excludes_cex (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ∃ (hT : ArgTypedAt E ρ cexP cexD), True :=
  fun ⟨hT, _⟩ => not_argTypedAt_cex E ρ hT

/-! ### §4 — adapters -/

/-- The identity related substitution at a context and environment. -/
def RelSubstIdT (M : CtxModelT E) (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) : Prop :=
  RelSubstAtT M R n Γ ρ ρ SubstT.id SubstT.id Γ

/-- **Related-substitution form → identity-substitution form** (the `hF` adapter #7721 asks for),
    given the identity package. -/
theorem fundConvAt_ctx_of_id {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : EnvT}
    (hId : RelSubstIdT M R n Γ ρ) {a b A : Expr Nat} (h : FundConvAt M R n Γ a b A) (c : CptT)
    (hc : M.Ap ρ a c ∨ M.Ap ρ b c) : LRSCoreS R E n Γ a b A c := by
  have := h hΓ hId c hc
  rwa [substT_id, substT_id, substT_id] at this

theorem fundTyAt_ctx_of_id {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : EnvT}
    (hId : RelSubstIdT M R n Γ ρ) {e A : Expr Nat} (h : FundTyAt M R n Γ e A) (c : CptT)
    (hc : M.Ap ρ e c) : LRSCoreS R E n Γ e e A c := by
  have := h hΓ hId c (Or.inl hc)
  simpa only [substT_id] using this

/-- The environment-typing field `RelSubstAtT` lacks (#7721): every compact a variable is
    assigned is typed at a code of its type, in the model.  With it, `TypingAt` becomes the
    generalised typing lemma's conclusion rather than a separate model-side input. -/
def EnvTypedAtT (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ∀ c, ρ i c → ∃ a, M.Ap ρ A a ∧ CTyS E c a

/-- The hybrid seed: a compact typed at a code of the type, realised in the model or self-related
    in the relation. -/
def HybridSeed (M : CtxModelT E) (R : Readback) (n : Nat) (Δ : LCtx) (ρ : EnvT) (σ : SubstT)
    (a A : Expr Nat) (c : CptT) : Prop :=
  (∃ a₀, M.Ap ρ A a₀ ∧ CTyS E c a₀) ∧
  (M.Ap ρ a c ∨ LRSCoreS R E n Δ (substT σ a) (substT σ a) (substT σ A) c)

/-- **Why the hybrid seed makes `trans` transport-free**: from the left link's output, the
    middle term's diagonal is a relation fact (PER at the typed compact), which seeds the right
    link; no compact is transported through the model.  Stated as the shape of the `trans` step
    at the probe, where the PER needs no premise. -/
theorem fundConvAt_hybrid_trans_shape (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c₀ A : Expr Nat}
    (ih₁ : LRSCoreS R E n Γ a a A (.pi .bot []) → LRSCoreS R E n Γ a b A (.pi .bot []))
    (ih₂ : LRSCoreS R E n Γ b b A (.pi .bot []) → LRSCoreS R E n Γ b c₀ A (.pi .bot []))
    (hseed : LRSCoreS R E n Γ a a A (.pi .bot [])) : LRSCoreS R E n Γ a c₀ A (.pi .bot []) :=
  piProbeS_trans hL hNU hW hΓ (ih₁ hseed) (ih₂ (piProbeS_right_diag hL hNU hW hΓ (ih₁ hseed)))

/-! ### §5 — the codomain continuation along the chain -/

/-- A probe link carries the codomain conversion too, under the LEFT domain (the clause stores
    `TyConvT (A₁ :: Γ) B₁ B₂`); `lrSCoreS_pi_probe` exposes only the domains. -/
theorem lrSCoreS_pi_probe_codom {Γ : LCtx} {X Y : Expr Nat} {u : Level}
    (h : LRSCoreS R E n Γ X Y (.sort u) (.pi .bot [])) :
    ∃ X₁ X₂ Y₁ Y₂, RedR R Γ X (.pi X₁ X₂) ∧ RedR R Γ Y (.pi Y₁ Y₂) ∧
      Nonempty (TyConvT E n Γ X₁ Y₁) ∧ Nonempty (TyConvT E n (.assumption X₁ :: Γ) X₂ Y₂) := by
  rw [LRSCoreS.eq_def] at h
  obtain ⟨_, X₁, X₂, Y₁, Y₂, h1, h2, _, hdom, hcod, _⟩ := h
  exact ⟨X₁, X₂, Y₁, Y₂, h1, h2, hdom, hcod⟩

/-- Context transport along a `TyConvT`-convertible binder: each `.of` step is a single-sort
    `CtxConvT.assumption` (both ends typed at that sort by `convEnds`), `.trans` composes.  No
    sort uniqueness: the sort is the step's own. -/
def convT_ctx_tyConvT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A A' : Expr Nat} → TyConvT E n Γ A A' → {a b T : Expr Nat} →
    ConvT E n (.assumption A :: Γ) a b T → ConvT E n (.assumption A' :: Γ) a b T
  | _, _, .refl _ _, _, _, _, h => h
  | _, _, .of _ _ _ _ hc, _, _, _, h =>
      let e := convEnds hW hΓ hc
      convT_ctx (envClosed_of_envWfT hW) (.assumption (ctxConvT_refl Γ) e.1 e.2.1 hc) h
  | _, _, .trans _ _ _ _ h1 h2, _, _, _, h =>
      convT_ctx_tyConvT hW hΓ h2 (convT_ctx_tyConvT hW hΓ h1 h)

def tyConvT_ctx_tyConvT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat}
    (hd : TyConvT E n Γ A A') : {B C : Expr Nat} →
    TyConvT E n (.assumption A :: Γ) B C → TyConvT E n (.assumption A' :: Γ) B C
  | _, _, .refl _ B => .refl _ B
  | _, _, .of _ B C u hc => .of _ B C u (convT_ctx_tyConvT hW hΓ hd hc)
  | _, _, .trans _ B C D h1 h2 =>
      .trans _ B C D (tyConvT_ctx_tyConvT hW hΓ hd h1) (tyConvT_ctx_tyConvT hW hΓ hd h2)

/-- **The alignment with its codomain continuation**: along a chain of relation-seeded links
    the domains are aligned AND the codomains, under the chain's first left domain — each
    later link's codomain conversion is moved to that binder along the (symmetric) domain
    alignment accumulated so far.  This is the "original conversion's codomain continuation"
    #7721 lists as missing; the next telescope slot is read from this conjunct. -/
theorem domCodAlign_of_chain_probe (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {h : Nat} (hF : LinkSeededBelow R E n Γ h) :
    ∀ {X Y : Expr Nat}, ConvChainBelow E n Γ h X Y →
      ∀ {u : Level}, LRSCoreS R E n Γ X X (.sort u) (.pi .bot []) →
      ∀ {X₁ X₂ : Expr Nat}, RedR R Γ X (.pi X₁ X₂) →
      ∀ {Y₁ Y₂ : Expr Nat}, RedR R Γ Y (.pi Y₁ Y₂) →
        Nonempty (TyConvT E n Γ X₁ Y₁) ∧ Nonempty (TyConvT E n (.assumption X₁ :: Γ) X₂ Y₂) := by
  intro X Y hch
  induction hch with
  | refl X =>
      intro u _ X₁ X₂ hX Y₁ Y₂ hY
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hX hY
      subst eA; subst eB
      exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  | step hc hlt rest ih =>
      intro u hself X₁ X₂ hX Y₁ Y₂ hY
      rename_i X₀ M Z u'
      have hself' : LRSCoreS R E n Γ X₀ X₀ (.sort u') (.pi .bot []) :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨u', .refl _⟩ _ hself
      have hlink := hF hc hlt hself'
      obtain ⟨A₁, A₂, B₁, B₂, hXr, hMr, ⟨hd⟩, ⟨hcod⟩⟩ := lrSCoreS_pi_probe_codom hlink
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hX hXr
      subst eA; subst eB
      have hnext := piProbeS_right_diag hL hNU hW hΓ hlink
      obtain ⟨⟨hrest⟩, ⟨hrestCod⟩⟩ := ih hnext hMr hY
      exact ⟨⟨.trans _ _ _ _ hd hrest⟩,
        ⟨.trans _ _ _ _ hcod (tyConvT_ctx_tyConvT hW hΓ hd.symmT hrestCod)⟩⟩

/-! ### §6 — environment typing in the motive -/

/-- `RelSubstAtT` with the environment-typing field on both environments (#7721: the package
    the generalised typing lemma needs, so that `FundamentalSAtT`'s arbitrary `ρ, ρ'` meet
    `TypingLemmaT`'s canonical `ctxEnvT`). -/
def RelSubstTypedAtT (M : CtxModelT E) (R : Readback) (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT)
    (σ σ' : SubstT) (Γ : LCtx) : Prop :=
  RelSubstAtT M R n Δ ρ ρ' σ σ' Γ ∧ EnvTypedAtT M Γ ρ ∧ EnvTypedAtT M Γ ρ'

/-- **The generalised typing lemma**: at an environment typed along `Γ`, every compact of a
    well-typed term is typed at a code of its type.  `TypingLemmaT` is the instance at
    `ctxEnvT E Γ`; this is the statement the simultaneous induction proves and the strong
    induction consumes. -/
def TypingLemmaEnvT (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A → ∀ {ρ : EnvT}, EnvTypedAtT M Γ ρ →
    ∀ c, M.Ap ρ e c → ∃ a, M.Ap ρ A a ∧ CTyS E c a

/-- With the typed package, segment 9's `TypingAt` input (`symm`/`tyConv`/`trans`) is the
    generalised typing lemma's conclusion at the two environments — the connection #7721 asked
    for. -/
theorem typingAt_of_typedPackage {M : CtxModelT E} (hTL : TypingLemmaEnvT M n) {Γ Δ : LCtx}
    {ρ ρ' : EnvT} {σ σ' : SubstT} (hS : RelSubstTypedAtT M R n Δ ρ ρ' σ σ' Γ)
    {a b A : Expr Nat} (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A) :
    TypingAt M ρ ρ' a b A := by
  intro c hc
  rcases hc with hc | hc
  · obtain ⟨a₀, hA, hty⟩ := hTL ha hS.2.1 c hc
    exact ⟨a₀, Or.inl hA, hty⟩
  · obtain ⟨a₀, hA, hty⟩ := hTL hb hS.2.2 c hc
    exact ⟨a₀, Or.inr hA, hty⟩

/-- Non-vacuity: an environment assigning only `⊥` is typed along every context (`⊥` is typed
    at every code, and `⊥` is a compact of every type). -/
theorem envTypedAtT_bot (Γ : LCtx) : EnvTypedAtT (ctxModelT_approxT E) Γ EnvT.bot := by
  intro i A _ c hc
  have hc' : c = .bot := hc
  subst hc'
  exact ⟨.bot, .bot _ _, ctyS_bot _⟩

#print axioms piProbeS_iff
#print axioms piProbeS_symm
#print axioms piProbeS_trans
#print axioms piProbeS_right_diag
#print axioms lrSCoreS_pi_self
#print axioms LinkSeededBelow
#print axioms domAlign_of_chain_probe
#print axioms nodeDeclAlign_const_of_probeLinks
#print axioms ArgTypedAt
#print axioms ModelBetaExpandTyped
#print axioms BackTransportBetaTyped
#print axioms backTransportBetaTyped_of_expand
#print axioms cexD
#print axioms cexP
#print axioms approxT_cexD_shape
#print axioms not_argTypedAt_cex
#print axioms modelBetaExpandTyped_excludes_cex
#print axioms RelSubstIdT
#print axioms fundConvAt_ctx_of_id
#print axioms fundTyAt_ctx_of_id
#print axioms EnvTypedAtT
#print axioms HybridSeed
#print axioms fundConvAt_hybrid_trans_shape
#print axioms lrSCoreS_pi_probe_codom
#print axioms convT_ctx_tyConvT
#print axioms tyConvT_ctx_tyConvT
#print axioms domCodAlign_of_chain_probe
#print axioms RelSubstTypedAtT
#print axioms TypingLemmaEnvT
#print axioms typingAt_of_typedPackage
#print axioms envTypedAtT_bot

end Rcic.Declarative.NativeValleys.TypedModelAudit
