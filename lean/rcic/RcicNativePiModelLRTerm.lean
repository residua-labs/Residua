import rcic.RcicNativePiModelLRCases

/-!
# RcicNativePiModelLRTerm — the term-level relation and adequacy at Π

The step from the type-level relation (`LRTypeIN`, #7631) to the diagonal: the `refl` case
of the fundamental lemma at a Π compact is adequacy — a well-typed type approximated by a
Π compact weak-head reduces to a Π-type — and adequacy is a consequence of the fundamental
lemma for TERMS, whose function clause is where the model's step functions meet the syntax.

**Why not an inductive.**  The function clause of a logical relation quantifies over
related ARGUMENTS in a hypothesis: a negative occurrence.  So `LRTermI` is defined by
well-founded recursion on the ELEMENT compact (the paper's recursion on compacts, §2.6):
* `bot` — degenerate (the (Bot) property);
* `sort`, `pi a f`, `spine r args` — the element is a type code: `A ↝* Sort u` and the two
  terms are related AS TYPES at that code (the (ToType) property);
* `lam g` — the element is a step function: `A ↝* Π A₁ B₁`, the extended context is
  well formed, and for every bounded step `(us, v) ∈ g`, arguments related at every
  `u ∈ us` give applications related at `v` in `B₁[N]` — Kripke-free, since neutrals are `⊥`.

**Compiled.**  `LRTermI` and its unfolding lemmas; `lrTermI_expand` (closure under
weak-head expansion on both sides, by recursion on the compact; the function clause uses
head congruence); `lrTermI_lam_at_sort_false` (a type is never a step function);
`semEqI_of_tyConvT` (model soundness for a chain from soundness for links);
`fundamentalLRINT_of_fundamentalTermI` (the typed type-level fundamental lemma from the
term-level one, model soundness and determinism); `piRow_of_fundamentalLRINT`
(Π-injectivity: the first link types the Π, `tyConvT_firstOf_data`);
`adequacyPiShape_of_fundamentalTermI` (a well-typed type approximated by a Π compact
weak-head reduces to a Π-type); `WhApproxInv` from its δ/ι core (`whApproxInv_of_core`:
β is `approxI_beta`, ζ is `approxI_zeta`, `lit` is the clause, head congruence is the `app`
congruence of the model); `adequacyPiI_of_fundamentalTermI` (adequacy with the components).

**Named** (the exact remaining theorems).  `FundamentalTermI` — the fundamental lemma for
terms (diagonal and conversions) in the final environment-`⊥` form; its proof is the
induction over related substitutions (paper §2.7 (Subst)); its `irr` case is
`devin/below-irr`'s (#7633) totality of `LRTermI` at proposition codes; δ/ι are
`agy-pimodel`'s.  `TypeSoundnessI` — model soundness for type conversions (Theorem 2.31
at `⊥`; `irr` inside types is the same strict-Prop layer).  `WhApproxInvCore` — the δ/ι
clauses of weak-head invariance of the model.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### the term-level relation -/

theorem sizeOf_fst_lt (s : List CptI × CptI) : sizeOf s.1 < sizeOf s := by
  cases s; simp; omega

theorem sizeOf_snd_lt (s : List CptI × CptI) : sizeOf s.2 < sizeOf s := by
  cases s; simp; omega

/-- `LRTermI E n Γ M M' A u`: `M`, `M'` of type `A` are related at the element compact `u`. -/
def LRTermI (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' .sort
  | .pi a f => (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' (.pi a f)
  | .spine r args => (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' (.spine r args)
  | .lam g =>
      ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, (∀ u ∈ s.1, LRTermI E n Γ N N' A₁ u) →
          LRTermI E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOf_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOf_snd_lt s
    omega

theorem lrTermI_bot (Γ : LCtx) (M M' A : Expr Nat) : LRTermI E n Γ M M' A .bot := by
  rw [LRTermI]; trivial

theorem lrTermI_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermI E n Γ M M' A .sort ↔ (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' .sort := by
  rw [LRTermI]

theorem lrTermI_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI) (f : List (List CptI × CptI)) :
    LRTermI E n Γ M M' A (.pi a f) ↔
      (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' (.pi a f) := by
  rw [LRTermI]

theorem lrTermI_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermI E n Γ M M' A (.spine r args) ↔
      (∃ u, WhRed E A (.sort u)) ∧ LRTypeIN E n Γ M M' (.spine r args) := by
  rw [LRTermI]

theorem lrTermI_lam_iff (Γ : LCtx) (M M' A : Expr Nat) (g : List (List CptI × CptI)) :
    LRTermI E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, (∀ u ∈ s.1, LRTermI E n Γ N N' A₁ u) →
          LRTermI E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 := by
  rw [LRTermI]

/-- Head congruence lifts to weak-head reduction. -/
theorem whRed_appHead {f f' a : Expr Nat} (h : WhRed E f f') : WhRed E (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.appHead h) ih

/-- Closure under weak-head expansion on both sides, by recursion on the element compact. -/
theorem lrTermI_expand {Γ : LCtx} {M M' X X' A : Expr Nat} (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermI E n Γ X X' A u → LRTermI E n Γ M M' A u
  | .bot, _ => lrTermI_bot _ _ _ _
  | .sort, h => by
      rw [lrTermI_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermI_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .spine r args, h => by
      rw [lrTermI_spine_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .lam g, h => by
      rw [lrTermI_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, hA, hΓ₁, happ⟩ := h
      refine ⟨A₁, B₁, hA, hΓ₁, fun s hs N N' hN => ?_⟩
      exact lrTermI_expand (whRed_appHead hX) (whRed_appHead hX') s.2 (happ s hs N N' hN)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOf_snd_lt s
  omega

/-- A type is never accepted as a step function: at a universe the function clause is
    contradictory. -/
theorem lrTermI_lam_at_sort_false {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    {g : List (List CptI × CptI)} (h : LRTermI E n Γ M M' (.sort u) (.lam g)) : False := by
  rw [lrTermI_lam_iff] at h
  obtain ⟨A₁, B₁, hA, _, _⟩ := h
  exact nomatch whRed_sort_eq hA

/-- The type-level relation from the term-level one at a universe, by the element compact. -/
theorem lrTypeIN_of_lrTermI_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} :
    (c : CptI) → LRTermI E n Γ M M' (.sort u) c → LRTypeIN E n Γ M M' c
  | .bot, _ => .bot _ _ _
  | .sort, h => ((lrTermI_sort_iff _ _ _ _).mp h).2
  | .pi _ _, h => ((lrTermI_pi_iff _ _ _ _ _ _).mp h).2
  | .spine _ _, h => ((lrTermI_spine_iff _ _ _ _ _ _).mp h).2
  | .lam _, h => (lrTermI_lam_at_sort_false h).elim

/-! ### the named inputs -/

/-- The fundamental lemma for terms (diagonal and conversions), environment-`⊥` form. -/
def FundamentalTermI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxI EnvI.bot M u → LRTermI E n Γ M M' A u)

/-- Model soundness for type conversions at the degenerate environment (Theorem 2.31 at
    `⊥`, for types). -/
def TypeSoundnessI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
    SemEqI EnvI.bot A B

/-- Soundness for a chain from soundness for its links. -/
theorem semEqI_of_tyConvT (hS : TypeSoundnessI E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B → SemEqI EnvI.bot A B
  | _, _, .refl _ _ => fun _ => Iff.rfl
  | _, _, .of _ _ _ _ hc => hS hΓ hc
  | _, _, .trans _ _ _ _ c₁ c₂ => fun c =>
      (semEqI_of_tyConvT hS hΓ c₁ c).trans (semEqI_of_tyConvT hS hΓ c₂ c)

/-- The typed type-level fundamental lemma: the left type is sorted. -/
def FundamentalLRINT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
    TyConvT E n Γ A A' → ∀ c, ApproxI EnvI.bot A c → LRTypeIN E n Γ A A' c

/-- The typed type-level fundamental lemma from the term-level one, model soundness and
    determinism: `refl` is the diagonal, `.of` the conversion clause at the link's sort,
    `trans` composes by `lrTypeIN_trans` after transporting the compact across the middle
    type by soundness. -/
theorem fundamentalLRINT_of_fundamentalTermI (hcl : EnvClosed E) (hW : EnvWfT E) (hdet : WhDet E)
    (hS : TypeSoundnessI E n) (F : FundamentalTermI E n) : FundamentalLRINT E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hcA; exact lrTypeIN_of_lrTermI_sort c (F.1 hΓ hA c hcA)
  | of A B v hc => intro u hA c hcA; exact lrTypeIN_of_lrTermI_sort c (F.2 hΓ hc c hcA)
  | trans A M B c₁ c₂ ih₁ ih₂ =>
      intro u hA c hcA
      obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA
      exact lrTypeIN_trans hcl hW hdet (ih₁ hA c hcA)
        (ih₂ hM c ((semEqI_of_tyConvT hS hΓ c₁ c).mp hcA))

/-- Π-injectivity (`piRow` shape) from the typed type-level fundamental lemma: a pure
    reflexivity chain is split by `Expr.pi.inj`; otherwise the first link sorts the Π. -/
theorem piRow_of_fundamentalLRINT (hW : EnvWfT E) (F : FundamentalLRINT E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrTypeIN_pi_components (F hΓ hPi hc _ (approxI_pi_bot_nil EnvI.bot A B))

/-! ### adequacy -/

/-- The shape half of adequacy from the diagonal: a well-typed type approximated by a Π
    compact weak-head reduces to a Π-type. -/
theorem adequacyPiShape_of_fundamentalTermI (F : FundamentalTermI E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u))
    {a : CptI} {f : List (List CptI × CptI)} (hc : ApproxI EnvI.bot A (.pi a f)) :
    ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) := by
  have h := lrTypeIN_of_lrTermI_sort (.pi a f) (F.1 hΓ hA _ hc)
  cases h with
  | pi h _ _ _ _ _ _ => exact ⟨_, _, h⟩

/-- Weak-head invariance of the model at every environment. -/
def WhApproxInv (E : ResolvedEnv) : Prop :=
  ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c

/-- Its δ and ι clauses (`agy-pimodel`'s semantics of constants and recursors). -/
def WhApproxInvCore (E : ResolvedEnv) : Prop :=
  (∀ {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat},
    E.members r = some m → m.body = some b →
    ∀ ρ c, ApproxI ρ (.const r ls) c ↔ ApproxI ρ (instantiateLevels ls b) c) ∧
  (∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ ρ c, ApproxI ρ lhs c ↔ ApproxI ρ rhs c)

/-- The `app` congruence of the model in the function position. -/
theorem semEqI_app_left {ρ : EnvI} {f g a : Expr Nat} (hf : SemEqI ρ f g) :
    SemEqI ρ (.app f a) (.app g a) := by
  intro c
  constructor
  · intro h
    rcases approxI_app_inv h with h0 | ⟨s, p, heq, hs, hp, hap⟩ | ⟨r, args, u, heq, hs, hau⟩
    · subst h0; exact .bot _ _
    · subst heq; exact .app ((hf _).mp hs) hp hap
    · subst heq; exact .appSpine ((hf _).mp hs) hau
  · intro h
    rcases approxI_app_inv h with h0 | ⟨s, p, heq, hs, hp, hap⟩ | ⟨r, args, u, heq, hs, hau⟩
    · subst h0; exact .bot _ _
    · subst heq; exact .app ((hf _).mpr hs) hp hap
    · subst heq; exact .appSpine ((hf _).mpr hs) hau

/-- The `lit` clause as an invariance. -/
theorem approxI_lit_iff (ρ : EnvI) (t : Nat) (c : CptI) :
    ApproxI ρ (.lit t) c ↔ ApproxI ρ (natExpand t) c := by
  constructor
  · intro h
    rcases approxI_lit_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact h'
  · intro h; exact .lit h

/-- Weak-head invariance from its δ/ι core: β and ζ are the model's soundness lemmas, `lit`
    is the clause, head congruence is the `app` congruence. -/
theorem whApproxInv_of_core (hcore : WhApproxInvCore E) : WhApproxInv E := by
  intro a b h
  induction h with
  | beta A b a => exact fun ρ c => approxI_beta ρ A b a c
  | zeta A v b => exact fun ρ c => approxI_zeta ρ A v b c
  | delta hres hbody => exact hcore.1 hres hbody
  | iota hι => exact hcore.2 hι
  | lit t => exact fun ρ c => approxI_lit_iff ρ t c
  | appHead _ ih => exact fun ρ => semEqI_app_left (ih ρ)

/-- Invariance along weak-head reduction. -/
theorem approxI_whRed (hinv : WhApproxInv E) {a b : Expr Nat} (h : WhRed E a b) (ρ : EnvI)
    (c : CptI) : ApproxI ρ a c ↔ ApproxI ρ b c := by
  induction h with
  | refl => exact Iff.rfl
  | step h _ ih => exact (hinv h ρ c).trans ih

/-- Adequacy at Π with the components, from the diagonal and weak-head invariance. -/
theorem adequacyPiI_of_fundamentalTermI (F : FundamentalTermI E n) (hinv : WhApproxInv E) :
    AdequacyPiI E n := by
  intro Γ hΓ A u hA a f hc
  obtain ⟨A₁, B₁, hred⟩ := adequacyPiShape_of_fundamentalTermI F hΓ hA hc
  have hc' := (approxI_whRed hinv hred EnvI.bot _).mp hc
  rcases approxI_pi_inv hc' with h0 | ⟨a', f', heq, hA₁, hB₁⟩
  · exact nomatch h0
  · cases heq
    exact ⟨A₁, B₁, hred, hA₁, hB₁⟩

#print axioms sizeOf_fst_lt
#print axioms sizeOf_snd_lt
#print axioms LRTermI
#print axioms lrTermI_bot
#print axioms lrTermI_sort_iff
#print axioms lrTermI_pi_iff
#print axioms lrTermI_spine_iff
#print axioms lrTermI_lam_iff
#print axioms whRed_appHead
#print axioms lrTermI_expand
#print axioms lrTermI_lam_at_sort_false
#print axioms lrTypeIN_of_lrTermI_sort
#print axioms FundamentalTermI
#print axioms TypeSoundnessI
#print axioms semEqI_of_tyConvT
#print axioms FundamentalLRINT
#print axioms fundamentalLRINT_of_fundamentalTermI
#print axioms piRow_of_fundamentalLRINT
#print axioms adequacyPiShape_of_fundamentalTermI
#print axioms WhApproxInv
#print axioms WhApproxInvCore
#print axioms semEqI_app_left
#print axioms approxI_lit_iff
#print axioms whApproxInv_of_core
#print axioms approxI_whRed
#print axioms adequacyPiI_of_fundamentalTermI

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
