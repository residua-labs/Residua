import rcic.RcicNativePiModelLRCases

/-!
# RcicNativePiModelLRTermS — the term-level relation with the split spine clause

Findings 2 and 3 of #7641 made exact and partly discharged, on `main` only (#7632/#7637).

* **Split spine clause.**  A spine compact as an ELEMENT of type `A` is read as a type code
  when `A ↝* Sort l` (the terms are related as types), and as a CONSTRUCTOR spine when `A`
  itself is approximated by a family spine (the terms weak-head reduce to normal
  convertible spines).  No reading at a Π: opaque function constants are not elements of
  the model once δ unfolds (`agy-pimodel`).
* **Presuppositions.**  The function clause carries `CtxWfT (A₁ :: Γ)`, the sorting of the
  codomain, and the typings of the arguments, so that index transport can substitute
  (`tyConvT_subst0_of_envWfT`, `hasTyT_subst0_of_envWfT`).
* **Compiled.**  `LRTermS` (well-founded recursion on the element compact), unfolding
  lemmas, `lrTermS_expand` (weak-head expansion on both sides), `lrTermS_spine_split` (the
  two readings), `lrTermS_lam_at_sort_false`, `lrTypeIN_of_lrTermS_sort`, and the
  type-code half of index transport `lrTermS_transport_typeCode` (sort, Π and
  type-reading spine compacts move along `TyConvT` on the index using the typed type-level
  fundamental lemma and weak-head invariance).
* **Named.**  `LRTermSTransportLam` — the function-clause half of index transport: its exact
  obstruction is the typing of the transported codomain `B₂` in the moved context
  `A₂ :: Γ`, i.e. context conversion of a typing along a `TyConvT` CHAIN (composition of
  `CtxConvT` links), after which the clause follows by the recursive transports at the
  argument demands and at the output compact with `tyConvT_subst0_of_envWfT`.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

theorem sizeOfS_fst_lt (s : List CptI × CptI) : sizeOf s.1 < sizeOf s := by
  cases s; simp; omega

theorem sizeOfS_snd_lt (s : List CptI × CptI) : sizeOf s.2 < sizeOf s := by
  cases s; simp; omega

/-- The term-level relation with the split spine clause and typing presuppositions. -/
def LRTermS (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort
  | .pi a f => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f)
  | .spine r args =>
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      ((∃ r' args', ApproxI EnvI.bot A (.spine r' args')) ∧
        ∃ Y Y', WhRed E M Y ∧ WhRed E M' Y' ∧ WhNormal E Y ∧ WhNormal E Y' ∧
          Nonempty (ConvT E n Γ Y Y' A))
  | .lam g =>
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermS E n Γ N N' A₁ u) →
          LRTermS E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfS_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfS_snd_lt s
    omega

theorem lrTermS_bot (Γ : LCtx) (M M' A : Expr Nat) : LRTermS E n Γ M M' A .bot := by
  rw [LRTermS]; trivial

theorem lrTermS_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermS E n Γ M M' A .sort ↔ (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort := by
  rw [LRTermS]

theorem lrTermS_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI) (f : List (List CptI × CptI)) :
    LRTermS E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f) := by
  rw [LRTermS]

theorem lrTermS_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermS E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      ((∃ r' args', ApproxI EnvI.bot A (.spine r' args')) ∧
        ∃ Y Y', WhRed E M Y ∧ WhRed E M' Y' ∧ WhNormal E Y ∧ WhNormal E Y' ∧
          Nonempty (ConvT E n Γ Y Y' A)) := by
  rw [LRTermS]

theorem lrTermS_lam_iff (Γ : LCtx) (M M' A : Expr Nat) (g : List (List CptI × CptI)) :
    LRTermS E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermS E n Γ N N' A₁ u) →
          LRTermS E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 := by
  rw [LRTermS]

/-- The two readings of a spine compact. -/
theorem lrTermS_spine_split {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptI}
    (h : LRTermS E n Γ M M' A (.spine r args)) :
    (∃ l, WhRed E A (.sort l)) ∨ (∃ r' args', ApproxI EnvI.bot A (.spine r' args')) := by
  rw [lrTermS_spine_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h2, _⟩
  · exact Or.inl h1
  · exact Or.inr h2

theorem whRedS_appHead {f f' a : Expr Nat} (h : WhRed E f f') : WhRed E (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.appHead h) ih

/-- Closure under weak-head expansion on both sides. -/
theorem lrTermS_expand {Γ : LCtx} {M M' X X' A : Expr Nat} (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermS E n Γ X X' A u → LRTermS E n Γ M M' A u
  | .bot, _ => lrTermS_bot _ _ _ _
  | .sort, h => by
      rw [lrTermS_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermS_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .spine r args, h => by
      rw [lrTermS_spine_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, Y, Y', hY, hY', hn, hn', hc⟩
      · exact Or.inl ⟨h1, lrTypeIN_expand hX hX' h2⟩
      · exact Or.inr ⟨h1, Y, Y', whRed_trans hX hY, whRed_trans hX' hY', hn, hn', hc⟩
  | .lam g, h => by
      rw [lrTermS_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩ := h
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      exact lrTermS_expand (whRedS_appHead hX) (whRedS_appHead hX') s.2 (happ s hs N N' hN hN' hrel)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfS_snd_lt s
  omega

/-- A type is never accepted as a step function. -/
theorem lrTermS_lam_at_sort_false {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    {g : List (List CptI × CptI)} (h : LRTermS E n Γ M M' (.sort u) (.lam g)) : False := by
  rw [lrTermS_lam_iff] at h
  obtain ⟨A₁, B₁, _, hA, _, _, _⟩ := h
  exact nomatch whRed_sort_eq hA

/-- At a universe, a spine compact is read as a type code: the constructor reading would
    need the universe itself to be approximated by a family spine, which it is not. -/
theorem lrTermS_spine_at_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} {r : Nat} {args : List CptI}
    (h : LRTermS E n Γ M M' (.sort u) (.spine r args)) : LRTypeIN E n Γ M M' (.spine r args) := by
  rw [lrTermS_spine_iff] at h
  rcases h with ⟨_, h2⟩ | ⟨⟨r', args', hsp⟩, _⟩
  · exact h2
  · rcases approxI_sort_inv hsp with h0 | h0 <;> cases h0

/-- The type-level relation from the term-level one at a universe. -/
theorem lrTypeIN_of_lrTermS_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} :
    (c : CptI) → LRTermS E n Γ M M' (.sort u) c → LRTypeIN E n Γ M M' c
  | .bot, _ => .bot _ _ _
  | .sort, h => ((lrTermS_sort_iff _ _ _ _).mp h).2
  | .pi _ _, h => ((lrTermS_pi_iff _ _ _ _ _ _).mp h).2
  | .spine _ _, h => lrTermS_spine_at_sort h
  | .lam _, h => (lrTermS_lam_at_sort_false h).elim

/-! ### index transport, type-code half -/

/-- `sort ∈ ⟦A⟧_⊥` whenever `A ↝* Sort l`, by weak-head invariance. -/
theorem approxI_whRed_back (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    {A X : Expr Nat} (h : WhRed E A X) {c : CptI} (hX : ApproxI EnvI.bot X c) :
    ApproxI EnvI.bot A c := by
  induction h with
  | refl => exact hX
  | step h _ ih => exact (hinv h _ _).mpr (ih hX)

theorem approxI_sort_of_whRed (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    {A : Expr Nat} {l : Level} (h : WhRed E A (.sort l)) : ApproxI EnvI.bot A .sort :=
  approxI_whRed_back hinv h (.sort _ _)

/-- Index transport for type-code compacts (sort, Π, type-reading spine): the type-level
    fundamental lemma at `sort` moves the universe shape to the converted index. -/
theorem lrTermS_transport_typeCode
    (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    (hT : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
      HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' → ∀ c, ApproxI EnvI.bot A c →
      LRTypeIN E n Γ A A' c)
    (hS : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ c, ApproxI EnvI.bot A c → ApproxI EnvI.bot A' c)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → (∀ g, c ≠ .lam g) → LRTermS E n Γ M M' A c → LRTermS E n Γ M M' A' c
  | .bot, _, _ => lrTermS_bot _ _ _ _
  | .sort, _, h => by
      rw [lrTermS_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hT hΓ hA hAA' .sort (approxI_sort_of_whRed hinv hl)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .pi a f, _, h => by
      rw [lrTermS_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hT hΓ hA hAA' .sort (approxI_sort_of_whRed hinv hl)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .spine r args, _, h => by
      rw [lrTermS_spine_iff] at h ⊢
      rcases h with ⟨⟨l, hl⟩, h2⟩ | ⟨⟨r', args', hsp⟩, Y, Y', hY, hY', hn, hn', ⟨hc⟩⟩
      · have hs := hT hΓ hA hAA' .sort (approxI_sort_of_whRed hinv hl)
        cases hs with
        | sort _ hl' => exact Or.inl ⟨⟨_, hl'⟩, h2⟩
      · exact Or.inr ⟨⟨r', args', hS hΓ hAA' _ hsp⟩, Y, Y', hY, hY', hn, hn',
          ⟨convT_of_tyConv hc hAA'⟩⟩
  | .lam g, hne, _ => (hne g rfl).elim

/-- The function-clause half of index transport (named): the exact obstruction is the
    typing of the transported codomain in the moved context, a context conversion of a
    typing along a `TyConvT` chain. -/
def LRTermSTransportLam (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
    TyConvT E n Γ A A' → ∀ {M M' : Expr Nat} (g : List (List CptI × CptI)),
      LRTermS E n Γ M M' A (.lam g) → LRTermS E n Γ M M' A' (.lam g)

#print axioms sizeOfS_fst_lt
#print axioms sizeOfS_snd_lt
#print axioms LRTermS
#print axioms lrTermS_bot
#print axioms lrTermS_sort_iff
#print axioms lrTermS_pi_iff
#print axioms lrTermS_spine_iff
#print axioms lrTermS_lam_iff
#print axioms lrTermS_spine_split
#print axioms whRedS_appHead
#print axioms lrTermS_expand
#print axioms lrTermS_lam_at_sort_false
#print axioms lrTermS_spine_at_sort
#print axioms lrTypeIN_of_lrTermS_sort
#print axioms approxI_whRed_back
#print axioms approxI_sort_of_whRed
#print axioms lrTermS_transport_typeCode
#print axioms LRTermSTransportLam

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
