import rcic.RcicAnnLR3Chain

/-!
# Typed application-prefix reconstruction for LR3

An application step either already has a positive normal function, or
contains a typed function step at an actual Pi carrier. The latter is
supplied by the constructor of `HeadA3`, not reconstructed by executing a
step function. Finite application chains therefore expose a finite prefix
of Pi-typed head steps ending at a positive normal function.

The Pi carrier may vary between prefix edges. Turning this witness into a
term chain at one previously chosen Pi type additionally needs type-carrier
compatibility. No uniqueness-of-types premise is silently supplied here.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- The precise one-step prefix law, independent of any evaluator. -/
def HeadAppPrefixA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA) (f a b T : ExprA), H.step Γ (.app f a) b T →
    H.normal Γ f ∨ ∃ (f' D C : ExprA) (u v : Level),
      H.step Γ f f' (.pi D u C v) ∧ b = .app f' a

/-- Positive application normality reflects to its function prefix. -/
def NormalAppPrefixA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA) (f a : ExprA), H.normal Γ (.app f a) → H.normal Γ f

/-- Every contextual LR3 application route supplies the typed prefix law. -/
theorem contextualHeadLayerA3_appPrefix {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hR : IotaRecHeadA E I) :
    HeadAppPrefixA3 E I n (contextualHeadLayerA3 E I n) := by
  intro Γ f a b T h
  change HeadA3 E I n Γ (.app f a) b T at h
  generalize he : ExprA.app f a = e at h
  induction h generalizing f a with
  | primitive e b T hl ha ht =>
      cases he
      exact Or.inl hl.app_normal
  | app f₀ f' a₀ D C T₀ u v hs hc hat ha ih =>
      cases he
      exact Or.inr ⟨f', D, C, u, v, .convert _ _ _ _ hs hc, rfl⟩
  | major f₀ a₀ a' D C T₀ u v hs hc hft ha hf hst hi hr hu ih =>
      cases he
      exact Or.inl (.neutral hf)
  | convert e b T U hs hc ih =>
      exact ih f a he
  | k s hw =>
      obtain ⟨w⟩ := hw
      have hsrc : ExprA.app f a = ExprA.app s.prefix s.major := he
      have hf := (ExprA.app.inj hsrc).1
      rw [hf]
      exact Or.inl (.neutral (target_prefix_neutral hR Γ w.target))

theorem contextualHeadLayerA3_normalAppPrefix
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    NormalAppPrefixA3 E I n (contextualHeadLayerA3 E I n) :=
  fun _ _ _ hn => normalA3_app_function hn

/-- A prefix edge retains the actual Pi typing of its head step. -/
def PiHeadEdgeA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) (Γ : LCtxA) (f f' : ExprA) : Prop :=
  ∃ (D C : ExprA) (u v : Level), H.step Γ f f' (.pi D u C v)

/-- Typed prefix extraction by induction on a supplied finite application
chain. There is no branch on whether an arbitrary expression steps. -/
theorem tmChainA3_piHeadPrefix {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} (hP : HeadAppPrefixA3 E I n H)
    (hN : NormalAppPrefixA3 E I n H) {Γ : LCtxA} {T e N : ExprA}
    (t : TmChainA3 E I n H Γ T e N) (hn : H.normal Γ N) :
    ∀ (f a : ExprA), e = .app f a →
      ∃ Nf, LR3Measurement.Trace (PiHeadEdgeA3 E I n H Γ) f Nf ∧ H.normal Γ Nf := by
  induction t with
  | refl e ht =>
      intro f a he
      subst e
      exact ⟨f, .refl f, hN Γ f a hn⟩
  | cons e e' N ht hs t ih =>
      intro f a he
      subst e
      rcases hP Γ f a e' T hs with hf | ⟨f', D, C, u, v, hff', he'⟩
      · exact ⟨f, .refl f, hf⟩
      · obtain ⟨Nf, htr, hnf⟩ := ih hn f' a he'
        exact ⟨Nf, .cons ⟨D, C, u, v, hff'⟩ htr, hnf⟩

/-- The actual contextual layer supplies the finite typed prefix. -/
theorem contextualHeadLayerA3_piHeadPrefix
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (hR : IotaRecHeadA E I)
    {Γ : LCtxA} {T f a N : ExprA}
    (h : TyHRedStarA3 E I n (contextualHeadLayerA3 E I n) Γ (.app f a) N T)
    (hn : NormalA3 E I n Γ N) :
    ∃ Nf, LR3Measurement.Trace
      (PiHeadEdgeA3 E I n (contextualHeadLayerA3 E I n) Γ) f Nf ∧
      NormalA3 E I n Γ Nf := by
  obtain ⟨t⟩ := h
  exact tmChainA3_piHeadPrefix (contextualHeadLayerA3_appPrefix hR)
    contextualHeadLayerA3_normalAppPrefix t hn f a rfl

#print axioms HeadAppPrefixA3
#print axioms NormalAppPrefixA3
#print axioms contextualHeadLayerA3_appPrefix
#print axioms contextualHeadLayerA3_normalAppPrefix
#print axioms PiHeadEdgeA3
#print axioms tmChainA3_piHeadPrefix
#print axioms contextualHeadLayerA3_piHeadPrefix

end Rcic.Declarative.Ann.LR3
