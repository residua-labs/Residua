import rcic.RcicAnnLR3EnvironmentEval

/-!
# Exact compositional laws of finite environment-aware interpretation

Finite translation trees are directed by native approximation inclusion.
Finite observations, even in different local environments, therefore have
one common translation witness. The joins supply the complete lambda graph
and exact application, without selecting a global native term or a normal
form. The relations used by the final function lemmas are arbitrary PER
indices: the laws are value equalities, not only one-sided approximation.
Paired substitution and the admitted member telescope remain separate.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentEval

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

theorem NativeBelow.trans {s t u : Expr Nat} (h : NativeBelow s t)
    (g : NativeBelow t u) : NativeBelow s u := fun ρ c hc => g ρ c (h ρ c hc)

/-- Two finite unfoldings of the same expression have a common finite
refinement. The witnesses stay inside Prop; no representative is chosen. -/
theorem Translation.directed {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {e : ExprA} {s t : Expr Nat} (hs : Translation E F ν e s)
    (ht : Translation E F ν e t) :
    ∃ u, Translation E F ν e u ∧ NativeBelow s u ∧ NativeBelow t u := by
  induction hs generalizing t with
  | cut e => exact ⟨t, ht, NativeBelow.cut t, NativeBelow.refl t⟩
  | bvar i =>
      cases ht with
      | cut => exact ⟨_, .bvar i, .refl _, .cut _⟩
      | bvar => exact ⟨_, .bvar i, .refl _, .refl _⟩
  | sort l =>
      cases ht with
      | cut => exact ⟨_, .sort l, .refl _, .cut _⟩
      | sort => exact ⟨_, .sort l, .refl _, .refl _⟩
  | constBody hb hs ih =>
      cases ht with
      | cut => exact ⟨_, .constBody hb hs, .refl _, .cut _⟩
      | constBody hb' ht =>
          rw [hb] at hb'
          cases hb'
          obtain ⟨u, hu, hsu, htu⟩ := ih ht
          exact ⟨u, .constBody hb hu, hsu, htu⟩
      | constRigid hn => rw [hb] at hn; cases hn
  | constRigid hn =>
      cases ht with
      | cut => exact ⟨_, .constRigid hn, .refl _, .cut _⟩
      | constBody hb _ => rw [hn] at hb; cases hb
      | constRigid => exact ⟨_, .constRigid hn, .refl _, .refl _⟩
  | app hsf hsa ihf iha =>
      cases ht with
      | cut => exact ⟨_, .app hsf hsa, .refl _, .cut _⟩
      | app htf hta =>
          obtain ⟨f, huf, hsf', htf'⟩ := ihf htf
          obtain ⟨a, hua, hsa', hta'⟩ := iha hta
          exact ⟨.app f a, .app huf hua,
            NativeBelow.app hsf' hsa', NativeBelow.app htf' hta'⟩
  | lam hsA hsb _ ihb =>
      cases ht with
      | cut => exact ⟨_, .lam hsA hsb, .refl _, .cut _⟩
      | lam _ htb =>
          obtain ⟨b, hub, hsb', htb'⟩ := ihb htb
          exact ⟨_, .lam hsA hub, NativeBelow.lam hsb', NativeBelow.lam htb'⟩
  | pi hsA hsB ihA ihB =>
      cases ht with
      | cut => exact ⟨_, .pi hsA hsB, .refl _, .cut _⟩
      | pi htA htB =>
          obtain ⟨A, huA, hsA', htA'⟩ := ihA htA
          obtain ⟨B, huB, hsB', htB'⟩ := ihB htB
          exact ⟨_, .pi huA huB, NativeBelow.tagged _ (NativeBelow.pi hsA' hsB'),
            NativeBelow.tagged _ (NativeBelow.pi htA' htB')⟩
  | letE hsA hsv hsb _ ihv ihb =>
      cases ht with
      | cut => exact ⟨_, .letE hsA hsv hsb, .refl _, .cut _⟩
      | letE _ htv htb =>
          obtain ⟨v, huv, hsv', htv'⟩ := ihv htv
          obtain ⟨b, hub, hsb', htb'⟩ := ihb htb
          exact ⟨_, .letE hsA huv hub, NativeBelow.letE hsv' hsb',
            NativeBelow.letE htv' htb'⟩
  | lit hs ih =>
      cases ht with
      | cut => exact ⟨_, .lit hs, .refl _, .cut _⟩
      | lit ht =>
          obtain ⟨u, hu, hsu, htu⟩ := ih ht
          exact ⟨u, .lit hu, hsu, htu⟩

/-- Finite observations in different environments share one finite
translation. Existence is obtained by finite induction, not by choice. -/
theorem finite_observations {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {e : ExprA} (observations : List (EnvI × CptI))
    (h : ∀ p ∈ observations, denote E F ν p.1 e p.2) :
    ∃ t, Translation E F ν e t ∧ ∀ p ∈ observations, denI p.1 t p.2 := by
  induction observations with
  | nil => exact ⟨cutTerm, .cut e, by simp⟩
  | cons p ps ih =>
      obtain ⟨s, hs, hsp⟩ := h p (by simp)
      obtain ⟨t, ht, htp⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
      obtain ⟨u, hu, hsu, htu⟩ := Translation.directed hs ht
      refine ⟨u, hu, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q
        exact hsu _ _ hsp
      · exact htu _ _ (htp q hq)

theorem finite_compacts {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {e : ExprA} (cs : List CptI)
    (h : ∀ c ∈ cs, denote E F ν ρ e c) :
    ∃ t, Translation E F ν e t ∧ ∀ c ∈ cs, denI ρ t c := by
  obtain ⟨t, ht, hc⟩ := finite_observations (cs.map (fun c => (ρ, c))) (by
    intro p hp
    obtain ⟨c, hcs, rfl⟩ := List.mem_map.mp hp
    exact h c hcs)
  exact ⟨t, ht, fun c hcs => hc (ρ, c) (List.mem_map.mpr ⟨c, hcs, rfl⟩)⟩

/-- Exact application at all raw values produced by the evaluator. -/
theorem denote_application (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (f a : ExprA) :
    ValueEq (denote E F ν ρ (.app f a))
      (NeutralPi.applyValue (denote E F ν ρ f) (denote E F ν ρ a)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut => exact Or.inl (cutTerm_only_bottom hc)
    | app hf ha =>
        rcases approxI_app_inv hc with hc | ⟨g, s, hc, hfg, hs, harg⟩ |
            ⟨r, args, u, hc, hfg, harg⟩
        · exact Or.inl hc
        · exact Or.inr (Or.inl ⟨g, s, hc, ⟨_, hf, hfg⟩, hs,
            fun u hu => ⟨_, ha, harg u hu⟩⟩)
        · exact Or.inr (Or.inr ⟨r, args, u, hc, ⟨_, hf, hfg⟩, ⟨_, ha, harg⟩⟩)
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨r, args, u, hc, hf, ha⟩
    · cases hc
      exact denote_bot E F ν ρ _
    · obtain ⟨f', htf, hf'⟩ := hf
      obtain ⟨a', hta, ha'⟩ := finite_compacts s.1 ha
      cases hc
      exact ⟨.app f' a', .app htf hta, .app hf' hs ha'⟩
    · obtain ⟨f', htf, hf'⟩ := hf
      obtain ⟨a', hta, ha'⟩ := ha
      cases hc
      exact ⟨.app f' a', .app htf hta, .appSpine hf' ha'⟩

/-- The complete graph quantifies over all raw arguments. Finite joins
combine the different body translations needed by a finite graph. -/
theorem denote_lambda_graph (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A body : ExprA) (u : Level) :
    ValueEq (denote E F ν ρ (.lam A u body))
      (UnifiedPi.legalGraph (fun _ _ => True)
        (fun x => denote E F ν (EnvI.cons x ρ) body)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut => exact Or.inl (cutTerm_only_bottom hc)
    | lam hA hb =>
        have hg := (FunctionEval.native_lambda_graph _ _ _ c).mp hc
        rcases hg with hc | ⟨g, hc, hg⟩
        · exact Or.inl hc
        · exact Or.inr ⟨g, hc, fun s hs x hx hargs => ⟨_, hb, hg s hs x hx hargs⟩⟩
  · intro hc
    rcases hc with hc | ⟨g, hc, hg⟩
    · cases hc
      exact denote_bot E F ν ρ _
    · let observations : List (EnvI × CptI) :=
        g.map (fun s => (EnvI.cons (demand s.1) ρ, s.2))
      have hobs : ∀ p ∈ observations, denote E F ν p.1 body p.2 := by
        intro p hp
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
        exact hg s hs (demand s.1) True.intro (fun _ hu => hu)
      obtain ⟨b', htb, hb⟩ := finite_observations observations hobs
      cases hc
      refine ⟨.lam cutTerm b', .lam (.cut A) htb, .lam ?_⟩
      intro s hs
      exact hb _ (List.mem_map.mpr ⟨s, hs, rfl⟩)

/-- Finite demand is inherited separately for each finite translation
witness. It does not require a global native representative. -/
theorem body_legalFiniteDemand (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (body : ExprA) (D : Relation) :
    UnifiedPi.LegalFiniteDemand D (fun x => denote E F ν (EnvI.cons x ρ) body) := by
  intro x hx c hc
  obtain ⟨t, ht, hc⟩ := hc
  obtain ⟨us, hus, hrow⟩ := UnifiedPi.native_body_legalFiniteDemand D ρ t x hx c hc
  exact ⟨us, hus, fun y hy hargs => ⟨t, ht, hrow y hy hargs⟩⟩

/-- Exact lambda application for every raw argument, without normalization. -/
theorem denote_lambda_application (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A body : ExprA) (u : Level) (x : Value) :
    ValueEq (NeutralPi.applyValue (denote E F ν ρ (.lam A u body)) x)
      (denote E F ν (EnvI.cons x ρ) body) :=
  (NeutralPi.applyValue_congr (denote_lambda_graph E F ν ρ A body u)
    (ValueEq.refl x)).trans
    (UnifiedPi.applyValue_legalGraph (fun y _ => denote_bot E F ν (EnvI.cons y ρ) body)
      (body_legalFiniteDemand E F ν ρ body (fun _ _ => True)) True.intro)

theorem denote_lambdas_related {E : ResolvedEnvA} {F : FamilySyntax}
    {D : Relation} {C : Value → Relation} {ν μ : Valuation} {ρ σ : EnvI}
    {A A' body body' : ExprA} {u u' : Level}
    (hbody : ∀ x y, D x y →
      C x (denote E F ν (EnvI.cons x ρ) body) (denote E F μ (EnvI.cons y σ) body')) :
    FunctionPER NeutralPi.applyValue D C
      (denote E F ν ρ (.lam A u body)) (denote E F μ σ (.lam A' u' body')) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (denote_lambda_application E F ν ρ A body u x),
    NeutralCodes.valueEq_eq (denote_lambda_application E F μ σ A' body' u' y)]
  exact hbody x y hxy

theorem denote_applications_related {E : ResolvedEnvA} {F : FamilySyntax}
    {D : Relation} {C : Value → Relation} {ν μ : Valuation} {ρ σ : EnvI}
    {f g a b : ExprA}
    (hfg : FunctionPER NeutralPi.applyValue D C (denote E F ν ρ f) (denote E F μ σ g))
    (hab : D (denote E F ν ρ a) (denote E F μ σ b)) :
    C (denote E F ν ρ a) (denote E F ν ρ (.app f a)) (denote E F μ σ (.app g b)) := by
  rw [NeutralCodes.valueEq_eq (denote_application E F ν ρ f a),
    NeutralCodes.valueEq_eq (denote_application E F μ σ g b)]
  exact hfg _ _ hab


end Rcic.Declarative.Ann.LR3.EnvironmentEval
