import rcic.RcicNativePiModelLRTerm

/-!
# RcicNativePiModelLRTermD — the repaired term-level relation

Answer to the #7646 audit and #7640's `not_fundamentalTermI_of_pi_member`: the earlier
relations read every `spine r args` element as a TYPE code, so constants at non-sort types
(constructors, proof and function constants — all denoted `spine r []`) were never
related, making the fundamental lemma false as stated.  `LRTermD` repairs both defects:

* **Data spines** (paper §3.4): `spine r args` as an ELEMENT of any type reads the terms as
  constant-headed weak-head normal spines with the same head `r`, convertible, and related
  PAIRWISE on the first `args.length` arguments at the corresponding compacts and an
  explicitly existential list of argument types.  At a Π type this is the application
  reading the audit asks for: `const r ls : Π A B` alone (`args = []`) is related to
  itself, and applying both sides to related arguments is related at the extended spine
  compact.  `whNormal_const_of_opaque` gives the normal form for constants with no δ-body.
* **Proposition collapse** (paper §3.6, `#7633`'s `tprojI_prop` layer): `LRTermD` is total
  whenever the type `A` is a proposition and not literally a universe:
  `IsPropTyI := Nonempty (HasTyT Γ A (sort 0)) ∧ ∀ l, A ≠ .sort l`.
  `lrTermD_prop_total` is the `ConvT.irr` interface `devin/below-irr` consumes.

**Compiled.**  `LRTermDCore`/`LRTermD` (well-founded recursion on the element compact —
the pairwise-argument clause recurses into `args`' elements through `zip`), unfolding
lemmas, `lrTermD_expand` (weak-head expansion on both sides), `lrTermD_prop_total`
(totality at propositions), **`lrTermD_const_pi_diag`** — the positive analogue of
#7640's refutation: an opaque constant at a Π type is related to ITSELF at `spine r []`,
so the refuted statement does not hold for `LRTermD`; `lrTermD_lam_at_sort_false`,
`lrTypeIN_of_lrTermD_sort`, `FundamentalTermD`,
`fundamentalLRINT_of_fundamentalTermD` (the typed type-level fundamental lemma from the
repaired term-level one, exactly as #7636's chain), `piRow_of_fundamentalTermD`
(Π-injectivity from it via `piRow_of_fundamentalLRINT`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

theorem sizeOfD_fst_lt (s : List CptI × CptI) : sizeOf s.1 < sizeOf s := by
  cases s; simp; omega

theorem sizeOfD_snd_lt (s : List CptI × CptI) : sizeOf s.2 < sizeOf s := by
  cases s; simp; omega

/-- `foldApps` over a snoc never reaches a bare constant. -/
theorem foldApps_snoc_ne_const {r : Nat} {ls : List Level} (f x : Expr Nat)
    (ys : List (Expr Nat)) : foldApps f (ys ++ [x]) ≠ .const r ls := by
  induction ys generalizing f with
  | nil => intro h; injection h
  | cons y ys ih => intro h; simp only [List.cons_append, foldApps] at h; exact ih _ h

/-- A constant with no δ-body is weak-head normal. -/
theorem whNormal_const_of_opaque {r : Nat} {ls : List Level} {m : CheckedMember}
    (hmem : E.members r = some m) (hbody : m.body = none) : WhNormal E (.const r ls) := by
  intro e h
  cases h with
  | delta hres hbody' =>
      rw [hmem] at hres
      cases hres
      rw [hbody] at hbody'
      exact nomatch hbody'
  | iota hι =>
      obtain ⟨r', ls', pre, major, hl⟩ := derivedIotaU_source hι
      exact foldApps_snoc_ne_const (.const r' ls') major pre (by simpa [recCall] using hl.symm)

/-- The type is a proposition (and not literally a universe, so the disjunct never fires
    at a sort — needed to read `LRTypeIN` back). -/
def IsPropTyI (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ A (.sort .zero)) ∧ ∀ l, A ≠ .sort l

/-- The core relation (without the proposition disjunct; the disjunction is inlined where
    the relation is invoked on computed types). -/
def LRTermDCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort
  | .pi a f => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f)
  | .spine r args =>
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormal E (foldApps (.const r ls₁) args₁) ∧
        WhNormal E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        ∃ (Ts : List (Expr Nat)) (hb1 : args.length ≤ args₁.length)
          (hb2 : args.length ≤ args₂.length) (hl : args.length = Ts.length),
          ∀ i : Fin args.length,
            IsPropTyI E n Γ (Ts.get (i.cast hl)) ∨
            LRTermDCore E n Γ (args₁.get (i.castLE hb1)) (args₂.get (i.castLE hb2))
              (Ts.get (i.cast hl)) (args.get i))
  | .lam g =>
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermDCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem i.isLt)
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega

/-- The term-level relation: total at propositions, else the core reading. -/
def LRTermD (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (u : CptI) : Prop :=
  IsPropTyI E n Γ A ∨ LRTermDCore E n Γ M M' A u

/-- Totality at propositions — the `irr` interface (the §3.6 collapse, stated on the
    relation itself). -/
theorem lrTermD_prop_total {Γ : LCtx} {A M M' : Expr Nat}
    (hA : Nonempty (HasTyT E n Γ A (.sort .zero))) (hns : ∀ l, A ≠ .sort l)
    (u : CptI) : LRTermD E n Γ M M' A u :=
  Or.inl ⟨hA, hns⟩

theorem lrTermD_bot (Γ : LCtx) (M M' A : Expr Nat) : LRTermD E n Γ M M' A .bot :=
  Or.inr (by rw [LRTermDCore.eq_def]; trivial)

/-! ### expansion closure -/

theorem whRedD_appHead {f f' a : Expr Nat} (h : WhRed E f f') : WhRed E (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.appHead h) ih

/-- Weak-head expansion on both sides, by recursion on the element compact. -/
theorem lrTermD_expand {Γ : LCtx} {M M' X X' A : Expr Nat} (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermD E n Γ X X' A u → LRTermD E n Γ M M' A u
  | .bot, _ => lrTermD_bot _ _ _ _
  | .sort, h => by
      rcases h with hP | h
      · exact Or.inl hP
      · rw [LRTermDCore.eq_def] at h
        refine Or.inr ?_
        rw [LRTermDCore.eq_def]
        exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rcases h with hP | h
      · exact Or.inl hP
      · rw [LRTermDCore.eq_def] at h
        refine Or.inr ?_
        rw [LRTermDCore.eq_def]
        exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .spine r args, h => by
      rcases h with hP | h
      · exact Or.inl hP
      · rw [LRTermDCore.eq_def] at h
        refine Or.inr ?_
        rw [LRTermDCore.eq_def]
        rcases h with ⟨h1, h2⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, hc, Ts, hb1, hb2, hl, harg⟩
        · exact Or.inl ⟨h1, lrTypeIN_expand hX hX' h2⟩
        · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, whRed_trans hX h1, whRed_trans hX' h2,
            n1, n2, hc, Ts, hb1, hb2, hl, harg⟩
  | .lam g, h => by
      rcases h with hP | h
      · exact Or.inl hP
      · rw [LRTermDCore.eq_def] at h
        obtain ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩ := h
        refine Or.inr ?_
        rw [LRTermDCore.eq_def]
        refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
        exact lrTermD_expand (whRedD_appHead hX) (whRedD_appHead hX') s.2
          (happ s hs N N' hN hN' hrel)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfD_snd_lt s
  omega

/-- The unfolding of the spine reading. -/
theorem lrTermD_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermD E n Γ M M' A (.spine r args) ↔
      IsPropTyI E n Γ A ∨
      (((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
        (∃ ls₁ ls₂ args₁ args₂,
          WhRed E M (foldApps (.const r ls₁) args₁) ∧
          WhRed E M' (foldApps (.const r ls₂) args₂) ∧
          WhNormal E (foldApps (.const r ls₁) args₁) ∧
          WhNormal E (foldApps (.const r ls₂) args₂) ∧
          Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
            (foldApps (.const r ls₂) args₂) A) ∧
          ∃ (Ts : List (Expr Nat)) (hb1 : args.length ≤ args₁.length)
            (hb2 : args.length ≤ args₂.length) (hl : args.length = Ts.length),
            ∀ i : Fin args.length,
              IsPropTyI E n Γ (Ts.get (i.cast hl)) ∨
              LRTermDCore E n Γ (args₁.get (i.castLE hb1)) (args₂.get (i.castLE hb2))
                (Ts.get (i.cast hl)) (args.get i))) := by
  unfold LRTermD
  rw [LRTermDCore.eq_def]

/-- A type is never accepted as a step function. -/
theorem lrTermD_lam_at_sort_false {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    {g : List (List CptI × CptI)} (h : LRTermDCore E n Γ M M' (.sort u) (.lam g)) : False := by
  rw [LRTermDCore.eq_def] at h
  obtain ⟨A₁, B₁, _, hA, _, _, _⟩ := h
  exact Expr.noConfusion (whRed_sort_eq hA)

/-- The type-level relation from the term-level one at a universe. -/
theorem lrTypeIN_of_lrTermD_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} :
    (c : CptI) → LRTermD E n Γ M M' (.sort u) c → LRTypeIN E n Γ M M' c
  | .bot, h => by
      rcases h with ⟨hP, hns⟩ | _
      · exact (hns u rfl).elim
      · exact .bot _ _ _
  | .sort, h => by
      rcases h with ⟨hP, hns⟩ | h
      · exact (hns u rfl).elim
      · rw [LRTermDCore.eq_def] at h; exact h.2
  | .pi _ _, h => by
      rcases h with ⟨hP, hns⟩ | h
      · exact (hns u rfl).elim
      · rw [LRTermDCore.eq_def] at h; exact h.2
  | .spine r args, h => by
      rcases h with ⟨hP, hns⟩ | h
      · exact (hns u rfl).elim
      · rw [LRTermDCore.eq_def] at h
        rcases h with ⟨_, h2⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨hc⟩, _⟩
        · exact h2
        · exact .spine h1 h2 n1 n2 (.of _ _ _ _ hc)
  | .lam _, h => by
      rcases h with ⟨hP, hns⟩ | h
      · exact (hns u rfl).elim
      · exact (lrTermD_lam_at_sort_false h).elim

/-! ### the fundamental lemma and the consumers -/

/-- The fundamental lemma for the repaired relation (diagonal and conversions),
    environment-`⊥` form. -/
def FundamentalTermD (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxI EnvI.bot M u → LRTermD E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxI EnvI.bot M u → LRTermD E n Γ M M' A u)

/-- The typed type-level fundamental lemma from the repaired term-level one — the same
    derivation as #7636's `fundamentalLRINT_of_fundamentalTermI`. -/
theorem fundamentalLRINT_of_fundamentalTermD (hcl : EnvClosed E) (hW : EnvWfT E) (hdet : WhDet E)
    (hS : TypeSoundnessI E n) (F : FundamentalTermD E n) : FundamentalLRINT E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hcA; exact lrTypeIN_of_lrTermD_sort c (F.1 hΓ hA c hcA)
  | of A B v hc => intro u hA c hcA; exact lrTypeIN_of_lrTermD_sort c (F.2 hΓ hc c hcA)
  | trans A M B c₁ c₂ ih₁ ih₂ =>
      intro u hA c hcA
      obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA
      exact lrTypeIN_trans hcl hW hdet (ih₁ hA c hcA)
        (ih₂ hM c ((semEqI_of_tyConvT hS hΓ c₁ c).mp hcA))

/-- Π-injectivity from the repaired fundamental lemma. -/
theorem piRow_of_fundamentalTermD (hcl : EnvClosed E) (hW : EnvWfT E) (hdet : WhDet E)
    (hS : TypeSoundnessI E n) (F : FundamentalTermD E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalLRINT hW (fundamentalLRINT_of_fundamentalTermD hcl hW hdet hS F)

/-! ### the positive diagonal: #7640's refutation fails for this relation -/

/-- An opaque constant at a Π type is related to itself at its own spine compact — the
    analogue of `not_fundamentalTermI_of_pi_member` is FALSE for `LRTermD`: the data-spine
    reading gives the application reading of a spine at a Π type (applying both sides to
    related arguments is related at the extended spine). -/
theorem lrTermD_const_pi_diag {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {A B : Expr Nat} (hmem : E.members r = some m) (hbody : m.body = none)
    (hM : HasTyT E n Γ (.const r ls) (.pi A B)) :
    LRTermD E n Γ (.const r ls) (.const r ls) (.pi A B) (.spine r []) := by
  refine Or.inr ?_
  rw [LRTermDCore.eq_def]
  refine Or.inr ⟨ls, ls, [], [], .refl _, .refl _, whNormal_const_of_opaque hmem hbody,
    whNormal_const_of_opaque hmem hbody, ⟨.refl _ _ _ hM⟩, [], Nat.le_refl 0,
    Nat.le_refl 0, rfl, fun i => absurd i.isLt (Nat.not_lt_zero _)⟩

#print axioms sizeOfD_fst_lt
#print axioms sizeOfD_snd_lt
#print axioms foldApps_snoc_ne_const
#print axioms whNormal_const_of_opaque
#print axioms IsPropTyI
#print axioms LRTermDCore
#print axioms LRTermD
#print axioms lrTermD_prop_total
#print axioms lrTermD_bot
#print axioms whRedD_appHead
#print axioms lrTermD_expand
#print axioms lrTermD_spine_iff
#print axioms lrTermD_lam_at_sort_false
#print axioms lrTypeIN_of_lrTermD_sort
#print axioms FundamentalTermD
#print axioms fundamentalLRINT_of_fundamentalTermD
#print axioms piRow_of_fundamentalTermD
#print axioms lrTermD_const_pi_diag

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
