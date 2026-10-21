import rcic.RcicAnnLRFund
import rcic.RcicAnnLRCumG
import rcic.RcicAnnLRExpG
import rcic.RcicAnnLRConvG
import rcic.RcicAnnLRNeutG
import rcic.RcicAnnLRPerG
/-!
# M2-e (1) — the fundamental theorem over valid substitutions in worlds:
# statement, arm bundle, assembly, and the arms without binder content

THE STATEMENT (`M2_PLAN.md` §2, re-indexed without the universe). For a judgment
`Γ ⊢ e ≈ e' : A` (a typing is the diagonal `e = e'`):

    FundArmAg Γ e e' A :=
      ∃ k₀, ∀ k ≥ k₀, ∀ Δ σ σ', CtxWfA Δ → ValidSubstAg k Δ σ σ' Γ →
        LREqAg k Δ (σA) (σ'A) ∧ LRRelAg k Δ (σA) (σe) (σ'e')

A VALID PAIR OF SUBSTITUTIONS `ValidSubstAg k Δ σ σ' Γ` sends every variable of `Γ`
to related images at its substituted type, carries the type's own equality under
the pair (so the pair is symmetric and reflexive on the left, `ValidSubstA_symmg`,
`ValidSubstA_refl_leftg`, through transport), and sends a let-bound variable to
something related to the substituted value (so `zetaLocal` is an arm, not a
rule about contexts). Heights: the threshold `k₀` is the derivation's; every
sort clause's CONTENT lives at the sort's own height `ht` (R-PropOutOfTower) and
is lifted to `k` by cumulativity (`LRRelA_sort_elimg`). THE TYPE-EQUALITY HALF
is what makes `symm` an arm: the IH under the swapped pair relates the images
at `σ'A`, and the equality `σ'A ≡ σA` transports them.

THE TYPED RULES CARRY THE TYPINGS: no syntactic substitution lemma is consumed.
Each arm re-applies its own rule to the typings the relation carries
(`LRRelA_hasTyg`), so the fundamental theorem IS the substitution lemma, semantic
and syntactic at once (`M2_PLAN.md` §3: M2-s (3) is not on the path).

WHAT THIS FILE PROVES. The assembly `fundOfArmsAg` (mutual structural recursion on
the derivations, the face's device) from an arm bundle, and SIXTEEN of the
twenty-seven arms: `sort`, `bvar`, `const`, `lit`, `conv` (typing) and `refl`,
`symm`, `trans`, `zetaLocal`, `delta`, `iota`, `lit`, `sorts`, `consts`, `irr`,
`tyConv` (conversion). Hypotheses, named once (`M2_PLAN.md` §2): `EnvClosedA`,
`IotaLiftA`, `IotaSubstA` (the oracle commutes with substitution — defined here),
`IotaConstHeadA` (ι fires on constant-headed spines only, so a quoted ι step
survives substitution: `hStepFnA_substA_constHead`), `EnvSemAg` (every member is
related to its `=ₙ`-level instantiations at its type, in every well-formed
context — defined here; for transparent members it is the theorem on the body
after the level-irrelevance lemma, for recursors it is M2-f/M3's content).

THE ELEVEN RESIDUAL ARMS, at their shapes, are the binder arms: `pi`, `lam`,
`app`, `letE` (typing) and `beta`, `zeta`, `app`, `lam`, `pi`, `letE`, `eta`
(conversion) — M2-e (2): the extension of a valid pair under a binder
(`SubstA.cons`), its weakening into worlds, and the `EqKAg.pi`/`TyKAg.pi`
construction from the IHs at the pi's sort height (the M2-e (0) witness,
generalised). `fundHasTyArmsA_ofg` / `fundConvArmsA_ofg` take them as hypotheses.

No `sorry`; axioms ⊆ {`propext`, `Quot.sound`}; no `Classical.choice`
(`Nonempty.elim` throughout, never `.some`; no `by_contra`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) heights under a total valuation -/

/-! ## (1) the hypotheses named here -/

/-- semantic environment well-formedness: every member is related to its
    `=ₙ`-level instantiations at its type, above some height, in every well-formed
    context. For transparent members this is the fundamental theorem on the body
    (after the level-irrelevance lemma); for recursors it is M2-f/M3's content; for
    axioms it is reflection (they are neutral). -/
def EnvSemAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelAg E I n ρ₀ k Δ (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls')

theorem emptyEnvA_semg (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : EnvSemAg emptyEnvA I n ρ₀ :=
  fun _ _ h => Option.noConfusion h

/-- the semantic clause for ONE member: `EnvSemAg`'s body at `r`. -/
def EnvSemClauseAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (r : Nat)
    (m : CheckedMemberA) : Prop :=
  ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelAg E I n ρ₀ k Δ (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls')

/-- `EnvSemAg` on the members in `D` only (M2-e (4)): what the environment
    induction has below the member it discharges, and all the `const` and
    `consts` arms consume on a derivation whose constants lie in `D`. -/
def EnvSemAtg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (D : Nat → Prop) : Prop :=
  ∀ r m, D r → E.members r = some m → EnvSemClauseAg E I n ρ₀ r m

theorem envSemAt_univg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hS : EnvSemAg E I n ρ₀) : EnvSemAtg E I n ρ₀ (fun _ => True) :=
  fun r m _ hres => hS r m hres

theorem envSemA_of_envSemAtg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hS : EnvSemAtg E I n ρ₀ (fun _ => True)) : EnvSemAg E I n ρ₀ :=
  fun r m hres => hS r m trivial hres

section Knot
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (2) small knotted helpers -/

/-- the typings the relation carries. -/
theorem LRRelA_hasTyg {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelAg E I n ρ₀ k Γ A a b) :
    Nonempty (HasTyA E I n Γ a A) ∧ Nonempty (HasTyA E I n Γ b A) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  exact escapeA_hasTyg hR hab

theorem LRRelA_convg {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelAg E I n ρ₀ k Γ A a b) :
    Nonempty (ConvA E I n Γ a b A) := by
  obtain ⟨R, hR, hab⟩ := h
  exact escape_LRTyAg hR hab

theorem LRRelA_validg {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelAg E I n ρ₀ k Γ A a b) :
    ∃ R, LRTyAg E I n ρ₀ k Γ A R :=
  h.elim fun R hR => ⟨R, hR.1⟩

/-- a valid type has a sort. -/
theorem LRTyA_hasTyg {k : Nat} {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ k Γ A R) : ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  rw [LRTyA_eqg] at h
  exact tyKA_hasTyg h

/-- the relation of a sort is the `sortT` one (Type-level) or the `sortP` one. -/
theorem tyKA_sort_invg {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {u : Level}
    {R : ExprA → ExprA → Prop} (h : TyKAg E I n ρ₀ k LE LT Γ (.sort u) R) :
    (isZero u = false ∧ ∃ hk : ht ρ₀ u < k, R = fun a b =>
        LE (ht ρ₀ u) hk Γ a b ∧ (∃ R, LT (ht ρ₀ u) hk Γ a R) ∧ (∃ R, LT (ht ρ₀ u) hk Γ b R) ∧
        Nonempty (HasTyA E I n Γ a (.sort u)) ∧ Nonempty (HasTyA E I n Γ b (.sort u)) ∧
        Nonempty (ConvA E I n Γ a b (.sort u))) ∨
    (isZero u = true ∧ R = fun a b =>
        PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
        Nonempty (HasTyA E I n Γ a (.sort u)) ∧ Nonempty (HasTyA E I n Γ b (.sort u)) ∧
        Nonempty (ConvA E I n Γ a b (.sort u)) ∧ PropEqA E I n Γ a b) := by
  have hS : WhTyA E I n Γ (.sort u) (.sort u) := whTyA_of_hasTy (.sort Γ u)
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA hS hn (hStepFnA_sort E I.fn Γ u)
      subst e
      exact absurd hP (not_isPropTy_sort E I Γ u)
  | sortT hA hz hk =>
      have e := whTyA_det hA hS (hStepFnA_sort E I.fn Γ _) (hStepFnA_sort E I.fn Γ u)
      cases e
      exact Or.inl ⟨hz, hk, rfl⟩
  | sortP hA hz =>
      have e := whTyA_det hA hS (hStepFnA_sort E I.fn Γ _) (hStepFnA_sort E I.fn Γ u)
      cases e
      exact Or.inr ⟨hz, rfl⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hS (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_sort E I.fn Γ u)
      cases e
  | fam hA hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hS hn (hStepFnA_sort E I.fn Γ u)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA hN _ =>
      have e := whTyA_det hA hS hN.1 (hStepFnA_sort E I.fn Γ u)
      subst e
      exact (stuckA_not_sort hN).elim

/-- what relatedness at a sort gives: the equality at the same height (cumulativity
    lifts the sort's own height), the validity of both sides, their typings and
    conversion at the sort. -/
theorem LRRelA_sort_elimg {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ (.sort u) A B) :
    LREqAg E I n ρ₀ k Γ A B ∧ (∃ R, LRTyAg E I n ρ₀ k Γ A R) ∧ (∃ R, LRTyAg E I n ρ₀ k Γ B R) ∧
    Nonempty (HasTyA E I n Γ A (.sort u)) ∧ Nonempty (HasTyA E I n Γ B (.sort u)) ∧
    Nonempty (ConvA E I n Γ A B (.sort u)) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  rcases tyKA_sort_invg hR with ⟨_, hk, e⟩ | ⟨_, e⟩
  · subst e
    obtain ⟨hle, hva, hvb, hta, htb, hc⟩ := hab
    exact ⟨LREqA_monog (Nat.le_of_lt hk) hle,
      hva.elim fun R h => ⟨R, LRTyA_monog (Nat.le_of_lt hk) h⟩,
      hvb.elim fun R h => ⟨R, LRTyA_monog (Nat.le_of_lt hk) h⟩, hta, htb, hc⟩
  · subst e
    -- S1-g.2: the guarded `sortP` hands over key-propositions — the prop clause, no K here
    obtain ⟨⟨N, hN, hnN, hPN⟩, ⟨M, hM, hnM, hPM⟩, hta, htb, hc, _⟩ := hab
    refine ⟨?_, ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hN hnN hPN⟩,
      ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hM hnM hPM⟩, hta, htb, hc⟩
    rw [LREqA_eqg]
    exact .stuck hN hM ⟨hnN, Or.inl hPN⟩ ⟨hnM, Or.inl hPM⟩
      (hta.elim fun ta => htb.elim fun tb => hc.elim fun c =>
        ⟨.of Γ A B u u u ta (eqNA_refl u) tb (eqNA_refl u) c⟩)
      ⟨fun _ => hPM, fun _ => hPN⟩

theorem LREqA_of_sortRelg {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ (.sort u) A B) : LREqAg E I n ρ₀ k Γ A B :=
  (LRRelA_sort_elimg h).1

/-- at `sort 0` the content is the `sortP` one: valid propositions, typed, convertible. -/
theorem LRRelA_sort0_elimg {k : Nat} {Γ : LCtxA} {A B : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ (.sort .zero) A B) :
    PropValidKA E I n Γ A ∧ PropValidKA E I n Γ B ∧
    Nonempty (HasTyA E I n Γ A (.sort .zero)) ∧ Nonempty (HasTyA E I n Γ B (.sort .zero)) ∧
    Nonempty (ConvA E I n Γ A B (.sort .zero)) ∧ PropEqA E I n Γ A B := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  rcases tyKA_sort_invg hR with ⟨hz, _, _⟩ | ⟨_, e⟩
  · cases hz
  · subst e; exact hab

/-- `sort l ≡ sort l'` above the height of `l`. -/
theorem LREqA_sortsg {k : Nat} (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ l < k) (hl : eqN l l') :
    LREqAg E I n ρ₀ k Γ (.sort l) (.sort l') := by
  rw [LREqA_eqg]
  exact .sort (whTyA_of_hasTy (.sort Γ l)) (whTyA_of_hasTy (.sort Γ l')) hk hl ⟨tyConvA_sorts Γ hl⟩

theorem LREqA_sort_reflg {k : Nat} (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    LREqAg E I n ρ₀ k Γ (.sort l) (.sort l) :=
  LREqA_sortsg Γ hk (eqNA_refl l)

/-- a sort is valid above its height (`sortT`), or at any height (`sortP`). -/
theorem LRTyA_sort_validg {k : Nat} (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    ∃ R, LRTyAg E I n ρ₀ k Γ (.sort l) R := by
  rw [LRTyA_eqg]
  cases hz : isZero l with
  | false => exact ⟨_, .sortT (whTyA_of_hasTy (.sort Γ l)) hz hk⟩
  | true => exact ⟨_, .sortP (whTyA_of_hasTy (.sort Γ l)) hz⟩

/-- `sort l ≈ sort l'` as elements of `sort (succ l)`, above that sort's height. -/
theorem LRRelA_sortsg {k : Nat} (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ (.succ l) < k)
    (hl : eqN l l') : LRRelAg E I n ρ₀ k Γ (.sort (.succ l)) (.sort l) (.sort l') := by
  have hk' : ht ρ₀ l < ht ρ₀ (.succ l) := by rw [ht_succ]; exact Nat.lt_succ_self _
  have hk'' : ht ρ₀ l' < ht ρ₀ (.succ l) := by rw [← ht_of_eqN hl]; exact hk'
  refine ⟨_, by rw [LRTyA_eqg]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ l))) (isZero_succ l) hk, ?_⟩
  exact ⟨LREqA_sortsg Γ hk' hl, LRTyA_sort_validg Γ hk', LRTyA_sort_validg Γ hk'', ⟨.sort Γ l⟩,
    ⟨hasTyA_retype_sort (.sort Γ l') (eqNA_succ (eqNA_symm hl))⟩, ⟨.sorts Γ l l' hl⟩⟩

end Knot

/-! ## (3) valid pairs of substitutions -/

/-- a related pair of substitutions from `Γ` into `Δ` at height `k`: every variable's
    images are related at its substituted type, whose equality under the pair the
    validity carries; a let-bound variable's image is related to the substituted
    value, and the value's images are related. -/
def ValidSubstAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (Δ : LCtxA) (σ σ' : SubstA) (Γ : LCtxA) : Prop :=
  (∀ i A, lookupTypeA Γ i = some A →
    LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) ∧
    LRRelAg E I n ρ₀ k Δ (substA σ A) (σ i) (σ' i)) ∧
  (∀ i A v, lookupTypeA Γ i = some A → lookupValueA Γ i = some v →
    LRRelAg E I n ρ₀ k Δ (substA σ A) (σ i) (substA σ v) ∧
    LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v))

section Valid
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem ValidSubstA_monog {j j' : Nat} (hjj : j ≤ j') {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAg E I n ρ₀ j Δ σ σ' Γ) : ValidSubstAg E I n ρ₀ j' Δ σ σ' Γ :=
  ⟨fun i A hA => ⟨LREqA_monog hjj (h.1 i A hA).1, LRRelA_monog hjj (h.1 i A hA).2⟩,
   fun i A v hA hv => ⟨LRRelA_monog hjj (h.2 i A v hA hv).1, LRRelA_monog hjj (h.2 i A v hA hv).2⟩⟩

theorem ValidSubstA_symmg (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ) : ValidSubstAg E I n ρ₀ k Δ σ' σ Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqA_symmg hEN he, LRRelA_transport'g hEN he (LRRelA_symmg hEN hr)⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    have h1 : LRRelAg E I n ρ₀ k Δ (substA σ A) (σ' i) (substA σ' v) :=
      LRRelA_transg hEN (LRRelA_symmg hEN hr) (LRRelA_transg hEN hv1 hv2)
    exact ⟨LRRelA_transport'g hEN he h1, LRRelA_transport'g hEN he (LRRelA_symmg hEN hv2)⟩

theorem ValidSubstA_refl_leftg (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ) : ValidSubstAg E I n ρ₀ k Δ σ σ Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqA_transg hEN he (LREqA_symmg hEN he), LRRelA_refl_leftg hEN hr⟩
  · obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    exact ⟨hv1, LRRelA_refl_leftg hEN hv2⟩

theorem ValidSubstA_refl_rightg (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ) : ValidSubstAg E I n ρ₀ k Δ σ' σ' Γ :=
  ValidSubstA_refl_leftg hEN (ValidSubstA_symmg hEN h)

/-- the empty context: every pair is valid. -/
theorem ValidSubstA_nilg {k : Nat} (Δ : LCtxA) (σ σ' : SubstA) : ValidSubstAg E I n ρ₀ k Δ σ σ' [] :=
  ⟨fun i _ h => by cases i <;> simp [lookupTypeA] at h,
   fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h⟩

end Valid

/-! ## (4) the statement -/

/-- the fundamental theorem's conclusion for `Γ ⊢ e ≈ e' : A`. -/
def FundArmAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) (e e' A : ExprA) : Prop :=
  ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
    ValidSubstAg E I n ρ₀ k Δ σ σ' Γ →
    LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) ∧
    LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ e) (substA σ' e')

/-- typing half: every typed term is related to itself under every valid pair. -/
def FundHasTyAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E I n Γ e A → FundArmAg E I n ρ₀ Γ e e A

/-- conversion half. -/
def FundConvAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {a b A : ExprA}, ConvA E I n Γ a b A → FundArmAg E I n ρ₀ Γ a b A

/-! ## (5) the twenty-seven arms, at their shapes -/

section Arms
variable (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)

def HasTyArmSortAg : Prop := ∀ (Γ : LCtxA) (l : Level),
  FundArmAg E I n ρ₀ Γ (.sort l) (.sort l) (.sort (.succ l))

def HasTyArmBvarAg : Prop := ∀ (Γ : LCtxA) (i : Nat) (A : ExprA) (u : Level),
  lookupTypeA Γ i = some A → HasTyA E I n Γ A (.sort u) → FundArmAg E I n ρ₀ Γ A A (.sort u) →
  FundArmAg E I n ρ₀ Γ (.bvar i) (.bvar i) A

def HasTyArmConstAg (D : Nat → Prop) : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls : List Level)
  (m : CheckedMemberA) (u : Level), D r → E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
  HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u) →
  FundArmAg E I n ρ₀ Γ (instantiateLevelsA ls m.mtypeA) (instantiateLevelsA ls m.mtypeA) (.sort u) →
  FundArmAg E I n ρ₀ Γ (.const r ls) (.const r ls) (instantiateLevelsA ls m.mtypeA)

def HasTyArmPiAg : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  FundArmAg E I n ρ₀ Γ A A (.sort u) → FundArmAg E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmAg E I n ρ₀ Γ (.pi A u B v) (.pi A u B v) (.sort (.imax u v))

def HasTyArmLamAg : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (body B : ExprA) (v : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  HasTyA E I n (.assumption A :: Γ) body B →
  FundArmAg E I n ρ₀ Γ A A (.sort u) → FundArmAg E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmAg E I n ρ₀ (.assumption A :: Γ) body body B →
  FundArmAg E I n ρ₀ Γ (.lam A u body) (.lam A u body) (.pi A u B v)

def HasTyArmAppAg : Prop := ∀ (Γ : LCtxA) (f a A B : ExprA) (u v w : Level),
  HasTyA E I n (.assumption A :: Γ) B (.sort v) → HasTyA E I n Γ (instantiate0A a B) (.sort w) →
  HasTyA E I n Γ f (.pi A u B v) → HasTyA E I n Γ a A →
  FundArmAg E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmAg E I n ρ₀ Γ (instantiate0A a B) (instantiate0A a B) (.sort w) →
  FundArmAg E I n ρ₀ Γ f f (.pi A u B v) → FundArmAg E I n ρ₀ Γ a a A →
  FundArmAg E I n ρ₀ Γ (.app f a) (.app f a) (instantiate0A a B)

def HasTyArmLetEAg : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u w : Level) (value B body : ExprA),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n Γ value A →
  HasTyA E I n Γ (instantiate0A value B) (.sort w) →
  HasTyA E I n (.letBinding A value :: Γ) body B →
  FundArmAg E I n ρ₀ Γ A A (.sort u) → FundArmAg E I n ρ₀ Γ value value A →
  FundArmAg E I n ρ₀ Γ (instantiate0A value B) (instantiate0A value B) (.sort w) →
  FundArmAg E I n ρ₀ (.letBinding A value :: Γ) body body B →
  FundArmAg E I n ρ₀ Γ (.letE A value body) (.letE A value body) (instantiate0A value B)

def HasTyArmLitAg : Prop := ∀ (Γ : LCtxA) (t : Nat) (T : ExprA),
  HasTyA E I n Γ (natExpandA t) T → FundArmAg E I n ρ₀ Γ (natExpandA t) (natExpandA t) T →
  FundArmAg E I n ρ₀ Γ (.lit t) (.lit t) T

def HasTyArmConvAg : Prop := ∀ (Γ : LCtxA) (e A B : ExprA) (l u : Level),
  HasTyA E I n Γ e A → HasTyA E I n Γ A (.sort l) → eqN l u → HasTyA E I n Γ B (.sort u) →
  ConvA E I n Γ A B (.sort u) →
  FundArmAg E I n ρ₀ Γ e e A → FundArmAg E I n ρ₀ Γ A A (.sort l) →
  FundArmAg E I n ρ₀ Γ B B (.sort u) → FundArmAg E I n ρ₀ Γ A B (.sort u) →
  FundArmAg E I n ρ₀ Γ e e B

def ConvArmReflAg : Prop := ∀ (Γ : LCtxA) (a A : ExprA),
  HasTyA E I n Γ a A → FundArmAg E I n ρ₀ Γ a a A → FundArmAg E I n ρ₀ Γ a a A

def ConvArmSymmAg : Prop := ∀ (Γ : LCtxA) (a b A : ExprA),
  ConvA E I n Γ a b A → FundArmAg E I n ρ₀ Γ a b A → FundArmAg E I n ρ₀ Γ b a A

def ConvArmTransAg : Prop := ∀ (Γ : LCtxA) (a b c A : ExprA),
  ConvA E I n Γ a b A → ConvA E I n Γ b c A →
  FundArmAg E I n ρ₀ Γ a b A → FundArmAg E I n ρ₀ Γ b c A → FundArmAg E I n ρ₀ Γ a c A

def ConvArmBetaAg : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (body arg B : ExprA),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) body B →
  HasTyA E I n Γ arg A → HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B) →
  FundArmAg E I n ρ₀ Γ A A (.sort u) → FundArmAg E I n ρ₀ (.assumption A :: Γ) body body B →
  FundArmAg E I n ρ₀ Γ arg arg A →
  FundArmAg E I n ρ₀ Γ (instantiate0A arg body) (instantiate0A arg body) (instantiate0A arg B) →
  FundArmAg E I n ρ₀ Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B)

def ConvArmZetaAg : Prop := ∀ (Γ : LCtxA) (A value body B : ExprA) (u : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n Γ value A →
  HasTyA E I n (.letBinding A value :: Γ) body B →
  HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B) →
  FundArmAg E I n ρ₀ Γ A A (.sort u) → FundArmAg E I n ρ₀ Γ value value A →
  FundArmAg E I n ρ₀ (.letBinding A value :: Γ) body body B →
  FundArmAg E I n ρ₀ Γ (instantiate0A value body) (instantiate0A value body) (instantiate0A value B) →
  FundArmAg E I n ρ₀ Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B)

def ConvArmZetaLocalAg : Prop := ∀ (Γ : LCtxA) (i : Nat) (A v : ExprA),
  lookupValueA Γ i = some v → lookupTypeA Γ i = some A → HasTyA E I n Γ v A →
  FundArmAg E I n ρ₀ Γ v v A → FundArmAg E I n ρ₀ Γ (.bvar i) v A

def ConvArmDeltaAg : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls : List Level) (m : CheckedMemberA)
  (b : ExprA), E.members r = some m → m.bodyA = some b → transparent m.mclass = true →
  ls.length = m.arity → levelsBounded n ls = true →
  HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) →
  FundArmAg E I n ρ₀ Γ (instantiateLevelsA ls b) (instantiateLevelsA ls b)
    (instantiateLevelsA ls m.mtypeA) →
  FundArmAg E I n ρ₀ Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)

def ConvArmIotaAg : Prop := ∀ (Γ : LCtxA) (lhs rhs T : ExprA),
  I.rel E Γ lhs rhs → HasTyA E I n Γ lhs T → HasTyA E I n Γ rhs T →
  FundArmAg E I n ρ₀ Γ lhs lhs T → FundArmAg E I n ρ₀ Γ rhs rhs T → FundArmAg E I n ρ₀ Γ lhs rhs T

/-- W-1 (e): ι at a struct group (`ConvA.structIota`): its premises and the three hypotheses on its
    derivations. -/
def ConvArmStructIotaAg : Prop := ∀ (Γ : LCtxA) (f a rhs e T : ExprA),
  recAtMajorA E f = true → structArmA E f a = some e → I.fn (.app f a) = some rhs →
  HasTyA E I n Γ (.app f a) T → HasTyA E I n Γ rhs T → ConvA E I n Γ rhs e T →
  FundArmAg E I n ρ₀ Γ (.app f a) (.app f a) T → FundArmAg E I n ρ₀ Γ rhs rhs T →
  FundArmAg E I n ρ₀ Γ rhs e T → FundArmAg E I n ρ₀ Γ (.app f a) rhs T

def ConvArmLitAg : Prop := ∀ (Γ : LCtxA) (t : Nat) (T : ExprA),
  HasTyA E I n Γ (natExpandA t) T → FundArmAg E I n ρ₀ Γ (natExpandA t) (natExpandA t) T →
  FundArmAg E I n ρ₀ Γ (.lit t) (natExpandA t) T

def ConvArmAppAg : Prop := ∀ (Γ : LCtxA) (f g a b A B : ExprA) (u v : Level),
  ConvA E I n Γ f g (.pi A u B v) → ConvA E I n Γ a b A →
  HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  HasTyA E I n Γ (.app g b) (instantiate0A a B) →
  FundArmAg E I n ρ₀ Γ f g (.pi A u B v) → FundArmAg E I n ρ₀ Γ a b A →
  FundArmAg E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmAg E I n ρ₀ Γ (.app g b) (.app g b) (instantiate0A a B) →
  FundArmAg E I n ρ₀ Γ (.app f a) (.app g b) (instantiate0A a B)

def ConvArmLamAg : Prop := ∀ (Γ : LCtxA) (A A' b b' B : ExprA) (u u' v : Level), eqN u u' →
  ConvA E I n Γ A A' (.sort u) → ConvA E I n (.assumption A :: Γ) b b' B →
  HasTyA E I n Γ (.lam A' u' b') (.pi A u B v) →
  FundArmAg E I n ρ₀ Γ A A' (.sort u) → FundArmAg E I n ρ₀ (.assumption A :: Γ) b b' B →
  FundArmAg E I n ρ₀ Γ (.lam A' u' b') (.lam A' u' b') (.pi A u B v) →
  FundArmAg E I n ρ₀ Γ (.lam A u b) (.lam A' u' b') (.pi A u B v)

def ConvArmPiAg : Prop := ∀ (Γ : LCtxA) (A A' B B' : ExprA) (u u' v v' : Level),
  eqN u u' → eqN v v' →
  ConvA E I n Γ A A' (.sort u) → ConvA E I n (.assumption A :: Γ) B B' (.sort v) →
  HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v)) →
  FundArmAg E I n ρ₀ Γ A A' (.sort u) → FundArmAg E I n ρ₀ (.assumption A :: Γ) B B' (.sort v) →
  FundArmAg E I n ρ₀ Γ (.pi A' u' B' v') (.pi A' u' B' v') (.sort (.imax u v)) →
  FundArmAg E I n ρ₀ Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))

def ConvArmLetEAg : Prop := ∀ (Γ : LCtxA) (A A' v v' b b' B : ExprA) (u : Level),
  ConvA E I n Γ A A' (.sort u) → ConvA E I n Γ v v' A →
  ConvA E I n (.letBinding A v :: Γ) b b' B →
  HasTyA E I n Γ (.letE A' v' b') (instantiate0A v B) →
  FundArmAg E I n ρ₀ Γ A A' (.sort u) → FundArmAg E I n ρ₀ Γ v v' A →
  FundArmAg E I n ρ₀ (.letBinding A v :: Γ) b b' B →
  FundArmAg E I n ρ₀ Γ (.letE A' v' b') (.letE A' v' b') (instantiate0A v B) →
  FundArmAg E I n ρ₀ Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B)

def ConvArmSortsAg : Prop := ∀ (Γ : LCtxA) (l₁ l₂ : Level), eqN l₁ l₂ →
  FundArmAg E I n ρ₀ Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))

def ConvArmConstsAg (D : Nat → Prop) : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls ls' : List Level)
  (m : CheckedMemberA), D r → E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
  levelsBounded n ls' = true → eqNList ls ls' →
  HasTyA E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA) →
  FundArmAg E I n ρ₀ Γ (.const r ls') (.const r ls') (instantiateLevelsA ls m.mtypeA) →
  FundArmAg E I n ρ₀ Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)

def ConvArmEtaAg : Prop := ∀ (Γ : LCtxA) (f A B : ExprA) (u v : Level),
  HasTyA E I n Γ f (.pi A u B v) →
  HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v) →
  FundArmAg E I n ρ₀ Γ f f (.pi A u B v) →
  FundArmAg E I n ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.lam A u (.app (liftA 0 1 f) (.bvar 0)))
    (.pi A u B v) →
  FundArmAg E I n ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v)

def ConvArmIrrAg : Prop := ∀ (Γ : LCtxA) (P p q : ExprA),
  HasTyA E I n Γ P (.sort .zero) → HasTyA E I n Γ p P → HasTyA E I n Γ q P →
  FundArmAg E I n ρ₀ Γ P P (.sort .zero) → FundArmAg E I n ρ₀ Γ p p P → FundArmAg E I n ρ₀ Γ q q P →
  FundArmAg E I n ρ₀ Γ p q P

def ConvArmTyConvAg : Prop := ∀ (Γ : LCtxA) (a b A A' : ExprA) (l l' u : Level),
  ConvA E I n Γ a b A → HasTyA E I n Γ A (.sort l) → eqN l u → HasTyA E I n Γ A' (.sort l') →
  eqN l' u → ConvA E I n Γ A A' (.sort u) →
  FundArmAg E I n ρ₀ Γ a b A → FundArmAg E I n ρ₀ Γ A A (.sort l) →
  FundArmAg E I n ρ₀ Γ A' A' (.sort l') → FundArmAg E I n ρ₀ Γ A A' (.sort u) →
  FundArmAg E I n ρ₀ Γ a b A'

structure FundHasTyArmsAg (D : Nat → Prop) : Prop where
  sortA : HasTyArmSortAg E I n ρ₀
  bvarA : HasTyArmBvarAg E I n ρ₀
  constA : HasTyArmConstAg E I n ρ₀ D
  piA : HasTyArmPiAg E I n ρ₀
  lamA : HasTyArmLamAg E I n ρ₀
  appA : HasTyArmAppAg E I n ρ₀
  letEA : HasTyArmLetEAg E I n ρ₀
  litA : HasTyArmLitAg E I n ρ₀
  convA : HasTyArmConvAg E I n ρ₀

structure FundConvArmsAg (D : Nat → Prop) : Prop where
  reflA : ConvArmReflAg E I n ρ₀
  symmA : ConvArmSymmAg E I n ρ₀
  transA : ConvArmTransAg E I n ρ₀
  betaA : ConvArmBetaAg E I n ρ₀
  zetaA : ConvArmZetaAg E I n ρ₀
  zetaLocalA : ConvArmZetaLocalAg E I n ρ₀
  deltaA : ConvArmDeltaAg E I n ρ₀
  iotaA : ConvArmIotaAg E I n ρ₀
  structIotaA : ConvArmStructIotaAg E I n ρ₀
  litA : ConvArmLitAg E I n ρ₀
  appA : ConvArmAppAg E I n ρ₀
  lamA : ConvArmLamAg E I n ρ₀
  piA : ConvArmPiAg E I n ρ₀
  letEA : ConvArmLetEAg E I n ρ₀
  sortsA : ConvArmSortsAg E I n ρ₀
  constsA : ConvArmConstsAg E I n ρ₀ D
  etaA : ConvArmEtaAg E I n ρ₀
  irrA : ConvArmIrrAg E I n ρ₀
  tyConvA : ConvArmTyConvAg E I n ρ₀

end Arms

/-! ## (6) the assembly: structural recursion on the derivations -/

section Assembly
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

mutual

theorem fundHasTyOfArmsAg (ht : FundHasTyArmsAg E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsAg E I n ρ₀ (fun _ => True)) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → FundArmAg E I n ρ₀ Γ e e A
  | _, _, _, .sort Γ l => ht.sortA Γ l
  | _, _, _, .bvar Γ i A u h hA => ht.bvarA Γ i A u h hA (fundHasTyOfArmsAg ht hc hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      ht.constA Γ r ls m u trivial hres hlen hwf hT (fundHasTyOfArmsAg ht hc hT)
  | _, _, _, .pi Γ A u B v hA hB =>
      ht.piA Γ A u B v hA hB (fundHasTyOfArmsAg ht hc hA) (fundHasTyOfArmsAg ht hc hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      ht.lamA Γ A u body B v hA hB hbody (fundHasTyOfArmsAg ht hc hA)
        (fundHasTyOfArmsAg ht hc hB) (fundHasTyOfArmsAg ht hc hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      ht.appA Γ f a A B u v w hB hTy hf ha (fundHasTyOfArmsAg ht hc hB)
        (fundHasTyOfArmsAg ht hc hTy) (fundHasTyOfArmsAg ht hc hf) (fundHasTyOfArmsAg ht hc ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      ht.letEA Γ A u w value B body hA hv hTy hb (fundHasTyOfArmsAg ht hc hA)
        (fundHasTyOfArmsAg ht hc hv) (fundHasTyOfArmsAg ht hc hTy) (fundHasTyOfArmsAg ht hc hb)
  | _, _, _, .lit Γ t T hexp => ht.litA Γ t T hexp (fundHasTyOfArmsAg ht hc hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hcv =>
      ht.convA Γ e A B l u h hAl hlu hB hcv (fundHasTyOfArmsAg ht hc h)
        (fundHasTyOfArmsAg ht hc hAl) (fundHasTyOfArmsAg ht hc hB) (fundConvOfArmsAg ht hc hcv)

theorem fundConvOfArmsAg (ht : FundHasTyArmsAg E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsAg E I n ρ₀ (fun _ => True)) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A → FundArmAg E I n ρ₀ Γ a b A
  | _, _, _, _, .refl Γ a A h => hc.reflA Γ a A h (fundHasTyOfArmsAg ht hc h)
  | _, _, _, _, .symm Γ a b A h => hc.symmA Γ a b A h (fundConvOfArmsAg ht hc h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      hc.transA Γ a b c A h1 h2 (fundConvOfArmsAg ht hc h1) (fundConvOfArmsAg ht hc h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      hc.betaA Γ A u body arg B hA hbody harg hred (fundHasTyOfArmsAg ht hc hA)
        (fundHasTyOfArmsAg ht hc hbody) (fundHasTyOfArmsAg ht hc harg) (fundHasTyOfArmsAg ht hc hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      hc.zetaA Γ A value body B u hA hv hb hred (fundHasTyOfArmsAg ht hc hA)
        (fundHasTyOfArmsAg ht hc hv) (fundHasTyOfArmsAg ht hc hb) (fundHasTyOfArmsAg ht hc hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      hc.zetaLocalA Γ i A v hval hty hv (fundHasTyOfArmsAg ht hc hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      hc.deltaA Γ r ls m b hres hbody htr hlen hwf hb (fundHasTyOfArmsAg ht hc hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      hc.iotaA Γ lhs rhs T h hlhs hrhs (fundHasTyOfArmsAg ht hc hlhs) (fundHasTyOfArmsAg ht hc hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      hc.structIotaA Γ f a rhs e T hrec hs h hlhs hrhs hcv (fundHasTyOfArmsAg ht hc hlhs)
        (fundHasTyOfArmsAg ht hc hrhs) (fundConvOfArmsAg ht hc hcv)
  | _, _, _, _, .lit Γ t T hexp => hc.litA Γ t T hexp (fundHasTyOfArmsAg ht hc hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      hc.appA Γ f g a b A B u v h1 h2 hB hrt (fundConvOfArmsAg ht hc h1) (fundConvOfArmsAg ht hc h2)
        (fundHasTyOfArmsAg ht hc hB) (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      hc.lamA Γ A A' b b' B u u' v hu hA hb hrt (fundConvOfArmsAg ht hc hA)
        (fundConvOfArmsAg ht hc hb) (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      hc.piA Γ A A' B B' u u' v v' hu hv hA hB hrt (fundConvOfArmsAg ht hc hA)
        (fundConvOfArmsAg ht hc hB) (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      hc.letEA Γ A A' v v' b b' B u hA hv hb hrt (fundConvOfArmsAg ht hc hA)
        (fundConvOfArmsAg ht hc hv) (fundConvOfArmsAg ht hc hb) (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => hc.sortsA Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      hc.constsA Γ r ls ls' m trivial hres hlen hwf hwf' h hrt (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt =>
      hc.etaA Γ f A B u v h hrt (fundHasTyOfArmsAg ht hc h) (fundHasTyOfArmsAg ht hc hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      hc.irrA Γ P p q hP hp hq (fundHasTyOfArmsAg ht hc hP) (fundHasTyOfArmsAg ht hc hp)
        (fundHasTyOfArmsAg ht hc hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      hc.tyConvA Γ a b A A' l l' u h hAl hlu hA'l hl'u hA (fundConvOfArmsAg ht hc h)
        (fundHasTyOfArmsAg ht hc hAl) (fundHasTyOfArmsAg ht hc hA'l) (fundConvOfArmsAg ht hc hA)

end

/-- the fundamental theorem from an arm bundle. -/
theorem fundOfArmsAg (ht : FundHasTyArmsAg E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsAg E I n ρ₀ (fun _ => True)) :
    FundHasTyAg E I n ρ₀ ∧ FundConvAg E I n ρ₀ :=
  ⟨fun h => fundHasTyOfArmsAg ht hc h, fun h => fundConvOfArmsAg ht hc h⟩

end Assembly

/-! ## (7) the arms without binder content -/

section ArmsProved
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem hasTyArmSortA_holdsg : HasTyArmSortAg E I n ρ₀ := fun Γ l =>
  ⟨ht ρ₀ (.succ l) + 1, fun k hk Δ _ _ _ _ =>
    ⟨LREqA_sort_reflg Δ hk, LRRelA_sortsg Δ hk (eqNA_refl l)⟩⟩

theorem convArmSortsA_holdsg : ConvArmSortsAg E I n ρ₀ := fun Γ l₁ l₂ h =>
  ⟨ht ρ₀ (.succ l₁) + 1, fun k hk Δ _ _ _ _ => ⟨LREqA_sort_reflg Δ hk, LRRelA_sortsg Δ hk h⟩⟩

theorem hasTyArmBvarA_holdsg : HasTyArmBvarAg E I n ρ₀ := fun _ i A _ h _ _ =>
  ⟨0, fun _ _ _ _ _ _ hσ => hσ.1 i A h⟩

theorem convArmReflA_holdsg : ConvArmReflAg E I n ρ₀ := fun _ _ _ _ ih => ih

theorem convArmSymmA_holdsg (hEN : EnvNormCtorTypeA E) : ConvArmSymmAg E I n ρ₀ := fun _ _ _ _ _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ' σ hΔ (ValidSubstA_symmg hEN hσ)
  exact ⟨LREqA_symmg hEN he, LRRelA_transport'g hEN he (LRRelA_symmg hEN hr)⟩

theorem convArmTransA_holdsg (hEN : EnvNormCtorTypeA E) : ConvArmTransAg E I n ρ₀ := fun _ _ _ _ _ _ _ ih₁ ih₂ => by
  obtain ⟨k₁, h₁⟩ := ih₁
  obtain ⟨k₂, h₂⟩ := ih₂
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr₁⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ hΔ (ValidSubstA_refl_leftg hEN hσ)
  obtain ⟨he, hr₂⟩ := h₂ k (le_max_of_le₂ hk) Δ σ σ' hΔ hσ
  exact ⟨he, LRRelA_transg hEN hr₁ hr₂⟩

theorem hasTyArmConvA_holdsg (hEN : EnvNormCtorTypeA E) : HasTyArmConvAg E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ ih _ ihB ihc => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihB
  obtain ⟨k₃, h₃⟩ := ihc
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hB⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hc⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_leftg hEN hσ)
  exact ⟨LREqA_of_sortRelg hB, LRRelA_transport'g hEN (LREqA_of_sortRelg hc) hr⟩

theorem convArmTyConvA_holdsg (hEN : EnvNormCtorTypeA E) : ConvArmTyConvAg E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ ihA' ihA => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihA'
  obtain ⟨k₃, h₃⟩ := ihA
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hA'⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hAA'⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_leftg hEN hσ)
  exact ⟨LREqA_of_sortRelg hA', LRRelA_transport'g hEN (LREqA_of_sortRelg hAA') hr⟩

theorem convArmZetaLocalA_holdsg (hEN : EnvNormCtorTypeA E) : ConvArmZetaLocalAg E I n ρ₀ := fun _ i A v hval hty _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  obtain ⟨hv1, _⟩ := hσ.2 i A v hty hval
  exact ⟨he, LRRelA_transg hEN hv1 hr⟩

theorem hasTyArmLitA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) : HasTyArmLitAg E I n ρ₀ :=
  fun _ t T _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelA_hasTyg hr
  have hs : StepAtA E I n Δ (.lit t) (natExpandA t) (substA σ T) :=
    ⟨hl.elim fun x => ⟨.lit Δ t _ x⟩, hl.elim fun x => ⟨.lit Δ t _ x⟩⟩
  exact ⟨he, LRRelA_expand_leftg hE hI hs (LRRelA_expand_rightg hE hI hs hr)⟩

theorem convArmLitA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) : ConvArmLitAg E I n ρ₀ :=
  fun _ t T _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelA_hasTyg hr
  have hs : StepAtA E I n Δ (.lit t) (natExpandA t) (substA σ T) :=
    ⟨hl.elim fun x => ⟨.lit Δ t _ x⟩, hl.elim fun x => ⟨.lit Δ t _ x⟩⟩
  simp only [substA_natExpandA]
  exact ⟨he, LRRelA_expand_leftg hE hI hs hr⟩

theorem convArmDeltaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) : ConvArmDeltaAg E I n ρ₀ :=
  fun _ r ls m b hres hbody htr hlen hwf _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mbody hE hres hbody, substA_mbody hE hres hbody] at hr
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_mbody hE hres hbody, substA_const]
  obtain ⟨hl, _⟩ := LRRelA_hasTyg hr
  obtain ⟨R, hR⟩ := LRRelA_validg hr
  obtain ⟨u, hTu⟩ := LRTyA_hasTyg hR
  have hs : StepAtA E I n Δ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) :=
    ⟨hTu.elim fun tu => ⟨.const Δ r ls m u hres hlen hwf tu⟩,
     hl.elim fun x => ⟨.delta Δ r ls m b hres hbody htr hlen hwf x⟩⟩
  exact ⟨he, LRRelA_expand_leftg hE hI hs hr⟩

theorem hasTyArmConstA_holdsg (hE : EnvClosedA E) {D : Nat → Prop} (hS : EnvSemAtg E I n ρ₀ D) :
    HasTyArmConstAg E I n ρ₀ D :=
  fun _ r ls m _ hD hres hlen hwf _ ih => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hD hres ls ls hlen hwf hwf (eqNList_refl ls)
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hTT⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at hTT
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨LREqA_of_sortRelg hTT, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmConstsA_holdsg (hE : EnvClosedA E) {D : Nat → Prop} (hS : EnvSemAtg E I n ρ₀ D) :
    ConvArmConstsAg E I n ρ₀ D :=
  fun _ r ls ls' m hD hres hlen hwf hwf' h _ ih => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hD hres ls ls' hlen hwf hwf' h
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, _⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨he, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmIrrA_holdsg (hEN : EnvNormCtorTypeA E) : ConvArmIrrAg E I n ρ₀ := fun _ P p q _ _ _ ihP ihp ihq => by
  obtain ⟨k₁, h₁⟩ := ihP
  obtain ⟨k₂, h₂⟩ := ihp
  obtain ⟨k₃, h₃⟩ := ihq
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hPP⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨heP, hp⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hq⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ' σ' hΔ (ValidSubstA_refl_rightg hEN hσ)
  obtain ⟨⟨N, hN, hnN, hPN⟩, _, hPt, hP't, hPc, _⟩ := LRRelA_sort0_elimg hPP
  have hpt : Nonempty (HasTyA E I n Δ (substA σ p) (substA σ P)) := (LRRelA_hasTyg hp).1
  have hqt' : Nonempty (HasTyA E I n Δ (substA σ' q) (substA σ' P)) := (LRRelA_hasTyg hq).1
  have hqt : Nonempty (HasTyA E I n Δ (substA σ' q) (substA σ P)) :=
    hqt'.elim fun tq => hP't.elim fun tP' => hPt.elim fun tP => hPc.elim fun c =>
      ⟨.conv Δ _ _ _ .zero .zero tq tP' (eqNA_refl _) tP (.symm Δ _ _ _ c)⟩
  refine ⟨heP, ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hN hnN hPN, ?_⟩⟩
  obtain ⟨tc⟩ := whTyA_tyConv hN
  exact ⟨hpt.elim fun tp => ⟨hasTyA_of_tyConvA tp tc⟩, hqt.elim fun tq => ⟨hasTyA_of_tyConvA tq tc⟩,
    hPt.elim fun tP => hpt.elim fun tp => hqt.elim fun tq =>
      ⟨convA_of_tyConvA (.irr Δ _ _ _ tP tp tq) tc⟩⟩

/-! ### ι survives substitution: the redex's head chain stays normal (exact arity),
    the step is preserved (`IotaSubstA`) -/

theorem convArmIotaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) : ConvArmIotaAg E I n ρ₀ := fun Γ lhs rhs T h hlhsT _ ihl ihr => by
  obtain ⟨k₁, h₁⟩ := ihl
  obtain ⟨k₂, h₂⟩ := ihr
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hl⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hr⟩ := h₂ k (le_max_of_le₂ hk) Δ σ σ' hΔ hσ
  obtain ⟨hlt, _⟩ := LRRelA_hasTyg hl
  obtain ⟨hrt, _⟩ := LRRelA_hasTyg hr
  have hs : StepAtA E I n Δ (substA σ lhs) (substA σ rhs) (substA σ T) :=
    ⟨hlt, hlt.elim fun tl => hrt.elim fun tr =>
      ⟨.iota Δ _ _ _ (iotaRel_substA hE (iotaRecHeadTypedA_of hR) hIS σ h ⟨hlhsT⟩ ⟨tl⟩) tl tr⟩⟩
  exact ⟨he, LRRelA_expand_leftg hE hI hs hr⟩

/-- W-1 (e): THE ARM OF ι AT A STRUCT GROUP. Under a valid pair the substituted spine steps by the
    struct arm (`TyHRedA.kstruct`): its conversion is the rule rebuilt at the substituted spine followed
    by the carried conversion, escaped from its own hypothesis. The relation expands on the left
    along that step, and the carried conversion relates the two contracta. -/
theorem convArmStructIotaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) : ConvArmStructIotaAg E I n ρ₀ :=
  fun Γ f a rhs e T hrec hs h _ _ _ ihl ihr ihc => by
  obtain ⟨k₁, h₁⟩ := ihl
  obtain ⟨k₂, h₂⟩ := ihr
  obtain ⟨k₃, h₃⟩ := ihc
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hl⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hr⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hc⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_leftg hEN hσ)
  obtain ⟨⟨tl⟩, _⟩ := LRRelA_hasTyg hl
  obtain ⟨⟨tr⟩, _⟩ := LRRelA_hasTyg hr
  obtain ⟨_, ⟨te⟩⟩ := LRRelA_hasTyg hc
  obtain ⟨cc⟩ := LRRelA_convg hc
  obtain ⟨r, ls, m, hsp, hres, hcl, _⟩ := recAtMajorA_true hrec
  have hrec' : recAtMajorA E (substA σ f) = true := by rw [recAtMajorA_substA E σ hsp]; exact hrec
  have hs' : structArmA E (substA σ f) (substA σ a) = some (substA σ e) := structArmA_substA hE σ hs
  have hfn' : I.fn (.app (substA σ f) (substA σ a)) = some (substA σ rhs) := hIS σ (.app f a) rhs h
  have hf' : hStepFnA E I.fn Δ (substA σ f) = none :=
    hStepFnA_below_none hR Δ (substA σ f) (by rw [appsSpineA_substA_const σ f hsp]) hres hcl
      (belowMajorA_substA E σ hsp (belowMajorA_of_rec hrec))
  have node : ConvA E I n Δ (.app (substA σ f) (substA σ a)) (substA σ rhs) (substA σ T) :=
    .structIota Δ _ _ _ _ _ hrec' hs' hfn' tl tr cc
  have hst : StepAtA E I n Δ (substA σ (.app f a)) (substA σ e) (substA σ T) :=
    ⟨⟨tl⟩, ⟨.kstruct Δ _ _ _ _ hrec' hs' hf' (.trans _ _ _ _ _ node cc) te⟩⟩
  exact ⟨he, LRRelA_expand_leftg hE hI hst (LRRelA_transg hEN (LRRelA_symmg hEN hc) hr)⟩

/-! ### the bundles, with the binder arms as hypotheses -/

theorem fundHasTyArmsA_ofg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E)
    {D : Nat → Prop}
    (hS : EnvSemAtg E I n ρ₀ D)
    (hpi : HasTyArmPiAg E I n ρ₀) (hlam : HasTyArmLamAg E I n ρ₀) (happ : HasTyArmAppAg E I n ρ₀)
    (hletE : HasTyArmLetEAg E I n ρ₀) : FundHasTyArmsAg E I n ρ₀ D :=
  ⟨hasTyArmSortA_holdsg, hasTyArmBvarA_holdsg, hasTyArmConstA_holdsg hE hS, hpi, hlam, happ, hletE,
   hasTyArmLitA_holdsg hE hI, hasTyArmConvA_holdsg hEN⟩

theorem fundConvArmsA_ofg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) {D : Nat → Prop} (hS : EnvSemAtg E I n ρ₀ D)
    (hbeta : ConvArmBetaAg E I n ρ₀) (hzeta : ConvArmZetaAg E I n ρ₀) (happ : ConvArmAppAg E I n ρ₀)
    (hlam : ConvArmLamAg E I n ρ₀) (hpi : ConvArmPiAg E I n ρ₀) (hletE : ConvArmLetEAg E I n ρ₀)
    (heta : ConvArmEtaAg E I n ρ₀) : FundConvArmsAg E I n ρ₀ D :=
  ⟨convArmReflA_holdsg, convArmSymmA_holdsg hEN, convArmTransA_holdsg hEN, hbeta, hzeta,
   convArmZetaLocalA_holdsg hEN, convArmDeltaA_holdsg hE hI, convArmIotaA_holdsg hE hI hIS hEN hR,
   convArmStructIotaA_holdsg hE hI hIS hEN hR,
   convArmLitA_holdsg hE hI, happ, hlam, hpi, hletE, convArmSortsA_holdsg,
   convArmConstsA_holdsg hE hS, heta, convArmIrrA_holdsg hEN, convArmTyConvA_holdsg hEN⟩

/-- the fundamental theorem, given the eleven binder arms (M2-e (2)). -/
theorem fund_of_binderArmsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) (hS : EnvSemAg E I n ρ₀)
    (hpi : HasTyArmPiAg E I n ρ₀) (hlam : HasTyArmLamAg E I n ρ₀) (happ : HasTyArmAppAg E I n ρ₀)
    (hletE : HasTyArmLetEAg E I n ρ₀)
    (cbeta : ConvArmBetaAg E I n ρ₀) (czeta : ConvArmZetaAg E I n ρ₀) (capp : ConvArmAppAg E I n ρ₀)
    (clam : ConvArmLamAg E I n ρ₀) (cpi : ConvArmPiAg E I n ρ₀) (cletE : ConvArmLetEAg E I n ρ₀)
    (ceta : ConvArmEtaAg E I n ρ₀) : FundHasTyAg E I n ρ₀ ∧ FundConvAg E I n ρ₀ :=
  fundOfArmsAg (fundHasTyArmsA_ofg hE hI hEN (envSemAt_univg hS) hpi hlam happ hletE)
    (fundConvArmsA_ofg hE hI hIS hEN hR (envSemAt_univg hS) cbeta czeta capp clam cpi cletE ceta)

end ArmsProved

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.fundOfArmsAg
#print axioms Rcic.Declarative.Ann.LRRelA_sort_elimg
#print axioms Rcic.Declarative.Ann.ValidSubstA_symmg
#print axioms Rcic.Declarative.Ann.convArmIrrA_holdsg
#print axioms Rcic.Declarative.Ann.convArmIotaA_holdsg
#print axioms Rcic.Declarative.Ann.convArmStructIotaA_holdsg
#print axioms Rcic.Declarative.Ann.fund_of_binderArmsg
