import rcic.RcicAnnSynMap
import rcic.RcicAnnSubst
import rcic.RcicAnnLRCum
import rcic.RcicAnnLRPer
import rcic.RcicAnnLRNeut
import rcic.RcicAnnLRExp
import rcic.RcicAnnLRConv

/-!
# M2-e (1) — the fundamental theorem over valid substitutions in worlds:
# statement, arm bundle, assembly, and the arms without binder content

THE STATEMENT (`M2_PLAN.md` §2, re-indexed without the universe). For a judgment
`Γ ⊢ e ≈ e' : A` (a typing is the diagonal `e = e'`):

    FundArmA Γ e e' A :=
      ∃ k₀, ∀ k ≥ k₀, ∀ Δ σ σ', CtxWfA Δ → ValidSubstA k Δ σ σ' Γ →
        LREqA k Δ (σA) (σ'A) ∧ LRRelA k Δ (σA) (σe) (σ'e')

A VALID PAIR OF SUBSTITUTIONS `ValidSubstA k Δ σ σ' Γ` sends every variable of `Γ`
to related images at its substituted type, carries the type's own equality under
the pair (so the pair is symmetric and reflexive on the left, `ValidSubstA_symm`,
`ValidSubstA_refl_left`, through transport), and sends a let-bound variable to
something related to the substituted value (so `zetaLocal` is an arm, not a
rule about contexts). Heights: the threshold `k₀` is the derivation's; every
sort clause's CONTENT lives at the sort's own height `ht` (R-PropOutOfTower) and
is lifted to `k` by cumulativity (`LRRelA_sort_elim`). THE TYPE-EQUALITY HALF
is what makes `symm` an arm: the IH under the swapped pair relates the images
at `σ'A`, and the equality `σ'A ≡ σA` transports them.

THE TYPED RULES CARRY THE TYPINGS: no syntactic substitution lemma is consumed.
Each arm re-applies its own rule to the typings the relation carries
(`LRRelA_hasTy`), so the fundamental theorem IS the substitution lemma, semantic
and syntactic at once (`M2_PLAN.md` §3: M2-s (3) is not on the path).

WHAT THIS FILE PROVES. The assembly `fundOfArmsA` (mutual structural recursion on
the derivations, the face's device) from an arm bundle, and SIXTEEN of the
twenty-seven arms: `sort`, `bvar`, `const`, `lit`, `conv` (typing) and `refl`,
`symm`, `trans`, `zetaLocal`, `delta`, `iota`, `lit`, `sorts`, `consts`, `irr`,
`tyConv` (conversion). Hypotheses, named once (`M2_PLAN.md` §2): `EnvClosedA`,
`IotaLiftA`, `IotaSubstA` (the oracle commutes with substitution — defined here),
`IotaConstHeadA` (ι fires on constant-headed spines only, so a quoted ι step
survives substitution: `hStepFnA_substA_constHead`), `EnvSemA` (every member is
related to its `=ₙ`-level instantiations at its type, in every well-formed
context — defined here; for transparent members it is the theorem on the body
after the level-irrelevance lemma, for recursors it is M2-f/M3's content).

THE ELEVEN RESIDUAL ARMS, at their shapes, are the binder arms: `pi`, `lam`,
`app`, `letE` (typing) and `beta`, `zeta`, `app`, `lam`, `pi`, `letE`, `eta`
(conversion) — M2-e (2): the extension of a valid pair under a binder
(`SubstA.cons`), its weakening into worlds, and the `EqKA.pi`/`TyKA.pi`
construction from the IHs at the pi's sort height (the M2-e (0) witness,
generalised). `fundHasTyArmsA_of` / `fundConvArmsA_of` take them as hypotheses.

No `sorry`; axioms ⊆ {`propext`, `Quot.sound`}; no `Classical.choice`
(`Nonempty.elim` throughout, never `.some`; no `by_contra`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) heights under a total valuation -/

theorem eval_total (ρ₀ : Nat → Nat) : (l : Level) → eval (fun i => some (ρ₀ i)) l = some (ht ρ₀ l)
  | .zero => rfl
  | .succ l => by
      have ih := eval_total ρ₀ l
      show (eval _ l).map (· + 1) = some (((eval _ l).map (· + 1)).getD 0)
      rw [ih]; rfl
  | .max a b => by
      have iha := eval_total ρ₀ a
      have ihb := eval_total ρ₀ b
      show (eval _ a).bind (fun x => (eval _ b).map (max x ·))
        = some (((eval _ a).bind (fun x => (eval _ b).map (max x ·))).getD 0)
      rw [iha, ihb]; rfl
  | .imax a b => by
      have iha := eval_total ρ₀ a
      have ihb := eval_total ρ₀ b
      show (eval _ b).bind (fun y => if y = 0 then some 0 else (eval _ a).map fun x => max x y)
        = some (((eval _ b).bind
            (fun y => if y = 0 then some 0 else (eval _ a).map fun x => max x y)).getD 0)
      rw [iha, ihb]
      show (if ht ρ₀ b = 0 then some 0 else some (max (ht ρ₀ a) (ht ρ₀ b)))
        = some ((if ht ρ₀ b = 0 then some 0 else some (max (ht ρ₀ a) (ht ρ₀ b))).getD 0)
      by_cases h : ht ρ₀ b = 0 <;> simp [h]
  | .param _ => rfl

theorem ht_succ (ρ₀ : Nat → Nat) (l : Level) : ht ρ₀ (.succ l) = ht ρ₀ l + 1 := by
  show ((eval _ l).map (· + 1)).getD 0 = ht ρ₀ l + 1
  rw [eval_total ρ₀ l]; rfl

theorem isZero_succ (l : Level) : isZero (.succ l) = false := rfl

theorem eqNList_refl : (ls : List Level) → eqNList ls ls
  | [] => trivial
  | l :: t => ⟨eqNA_refl l, eqNList_refl t⟩

/-! ## (1) the hypotheses named here -/

/-- the ι oracle PRESERVES ITS SUCCESSFUL STEPS under parallel substitution: a
    redex stays a redex, with the substituted reduct (05's ι fires on constructor
    shapes, which substitution preserves). Only this direction is consumed
    (`iotaRel_substA`, the ι arm). NOT an `Option` equality: as one, restricted to
    constant-headed spines (M2-e (4), after Codex P1 on #6115: unrestricted, with
    `IotaConstHeadA` it forced `I.fn ≡ none`), it still forced `I.fn e = none →
    I.fn (substA σ e) = none`, which standard ι violates — `Nat.rec motive mz ms x`
    under `[zero/x]` has `I.fn e = none` and `I.fn (σ e) = some mz`: substitution
    CREATES ι-redexes (independent review, 2026-10-04; M2-f (1)). The `none` side
    below the major that the equality paid is paid by exact telescope arity
    (`IotaRecHeadA`, `iotaFn_none_of_below`). -/
def IotaSubstA (I : IotaIfaceA) : Prop :=
  ∀ (σ : SubstA) (e e' : ExprA), I.fn e = some e' → I.fn (substA σ e) = some (substA σ e')

theorem noIotaA_subst : IotaSubstA noIotaA := fun _ _ _ h => Option.noConfusion h

/-- semantic environment well-formedness: every member is related to its
    `=ₙ`-level instantiations at its type, above some height, in every well-formed
    context. For transparent members this is the fundamental theorem on the body
    (after the level-irrelevance lemma); for recursors it is M2-f/M3's content; for
    axioms it is reflection (they are neutral). -/
def EnvSemA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelA E I n ρ₀ k Δ (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls')

theorem emptyEnvA_sem (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : EnvSemA emptyEnvA I n ρ₀ :=
  fun _ _ h => Option.noConfusion h

/-- the semantic clause for ONE member: `EnvSemA`'s body at `r`. -/
def EnvSemClauseA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (r : Nat)
    (m : CheckedMemberA) : Prop :=
  ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      LRRelA E I n ρ₀ k Δ (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls')

/-- `EnvSemA` on the members in `D` only (M2-e (4)): what the environment
    induction has below the member it discharges, and all the `const` and
    `consts` arms consume on a derivation whose constants lie in `D`. -/
def EnvSemAt (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (D : Nat → Prop) : Prop :=
  ∀ r m, D r → E.members r = some m → EnvSemClauseA E I n ρ₀ r m

theorem envSemAt_univ {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hS : EnvSemA E I n ρ₀) : EnvSemAt E I n ρ₀ (fun _ => True) :=
  fun r m _ hres => hS r m hres

theorem envSemA_of_envSemAt {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hS : EnvSemAt E I n ρ₀ (fun _ => True)) : EnvSemA E I n ρ₀ :=
  fun r m hres => hS r m trivial hres

section Knot
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (2) small knotted helpers -/

/-- the typings the relation carries. -/
theorem LRRelA_hasTy {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelA E I n ρ₀ k Γ A a b) :
    Nonempty (HasTyA E I n Γ a A) ∧ Nonempty (HasTyA E I n Γ b A) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eq] at hR
  exact escapeA_hasTy hR hab

theorem LRRelA_conv {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelA E I n ρ₀ k Γ A a b) :
    Nonempty (ConvA E I n Γ a b A) := by
  obtain ⟨R, hR, hab⟩ := h
  exact escape_LRTyA hR hab

theorem LRRelA_valid {k : Nat} {Γ : LCtxA} {A a b : ExprA} (h : LRRelA E I n ρ₀ k Γ A a b) :
    ∃ R, LRTyA E I n ρ₀ k Γ A R :=
  h.elim fun R hR => ⟨R, hR.1⟩

/-- a valid type has a sort. -/
theorem LRTyA_hasTy {k : Nat} {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyA E I n ρ₀ k Γ A R) : ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  rw [LRTyA_eq] at h
  exact tyKA_hasTy h

/-- the relation of a sort is the `sortT` one (Type-level) or the `sortP` one. -/
theorem tyKA_sort_inv {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {u : Level}
    {R : ExprA → ExprA → Prop} (h : TyKA E I n ρ₀ k LE LT Γ (.sort u) R) :
    (isZero u = false ∧ ∃ hk : ht ρ₀ u < k, R = fun a b =>
        LE (ht ρ₀ u) hk Γ a b ∧ (∃ R, LT (ht ρ₀ u) hk Γ a R) ∧ (∃ R, LT (ht ρ₀ u) hk Γ b R) ∧
        Nonempty (HasTyA E I n Γ a (.sort u)) ∧ Nonempty (HasTyA E I n Γ b (.sort u)) ∧
        Nonempty (ConvA E I n Γ a b (.sort u))) ∨
    (isZero u = true ∧ R = fun a b =>
        PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
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
  | stuck hA hN =>
      have e := whTyA_det hA hS hN.1 (hStepFnA_sort E I.fn Γ u)
      subst e
      exact (stuckA_not_sort hN).elim

/-- what relatedness at a sort gives: the equality at the same height (cumulativity
    lifts the sort's own height), the validity of both sides, their typings and
    conversion at the sort. -/
theorem LRRelA_sort_elim {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelA E I n ρ₀ k Γ (.sort u) A B) :
    LREqA E I n ρ₀ k Γ A B ∧ (∃ R, LRTyA E I n ρ₀ k Γ A R) ∧ (∃ R, LRTyA E I n ρ₀ k Γ B R) ∧
    Nonempty (HasTyA E I n Γ A (.sort u)) ∧ Nonempty (HasTyA E I n Γ B (.sort u)) ∧
    Nonempty (ConvA E I n Γ A B (.sort u)) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eq] at hR
  rcases tyKA_sort_inv hR with ⟨_, hk, e⟩ | ⟨_, e⟩
  · subst e
    obtain ⟨hle, hva, hvb, hta, htb, hc⟩ := hab
    exact ⟨LREqA_mono (Nat.le_of_lt hk) hle,
      hva.elim fun R h => ⟨R, LRTyA_mono (Nat.le_of_lt hk) h⟩,
      hvb.elim fun R h => ⟨R, LRTyA_mono (Nat.le_of_lt hk) h⟩, hta, htb, hc⟩
  · subst e
    obtain ⟨⟨N, hN, hN'⟩, ⟨M, hM, hM'⟩, hta, htb, hc, _⟩ := hab
    refine ⟨?_, ⟨_, by rw [LRTyA_eq]; exact tyKA_of_tripleLike hN hN'⟩,
      ⟨_, by rw [LRTyA_eq]; exact tyKA_of_tripleLike hM hM'⟩, hta, htb, hc⟩
    rw [LREqA_eq]
    exact .stuck hN hM hN' hM' (hta.elim fun ta => htb.elim fun tb => hc.elim fun c =>
      ⟨.of Γ A B u u u ta (eqNA_refl u) tb (eqNA_refl u) c⟩)

theorem LREqA_of_sortRel {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelA E I n ρ₀ k Γ (.sort u) A B) : LREqA E I n ρ₀ k Γ A B :=
  (LRRelA_sort_elim h).1

/-- at `sort 0` the content is the `sortP` one: valid propositions, typed, convertible. -/
theorem LRRelA_sort0_elim {k : Nat} {Γ : LCtxA} {A B : ExprA}
    (h : LRRelA E I n ρ₀ k Γ (.sort .zero) A B) :
    PropValidA E I n Γ A ∧ PropValidA E I n Γ B ∧
    Nonempty (HasTyA E I n Γ A (.sort .zero)) ∧ Nonempty (HasTyA E I n Γ B (.sort .zero)) ∧
    Nonempty (ConvA E I n Γ A B (.sort .zero)) ∧ PropEqA E I n Γ A B := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eq] at hR
  rcases tyKA_sort_inv hR with ⟨hz, _, _⟩ | ⟨_, e⟩
  · cases hz
  · subst e; exact hab

/-- `sort l ≡ sort l'` above the height of `l`. -/
theorem LREqA_sorts {k : Nat} (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ l < k) (hl : eqN l l') :
    LREqA E I n ρ₀ k Γ (.sort l) (.sort l') := by
  rw [LREqA_eq]
  exact .sort (whTyA_of_hasTy (.sort Γ l)) (whTyA_of_hasTy (.sort Γ l')) hk hl ⟨tyConvA_sorts Γ hl⟩

theorem LREqA_sort_refl {k : Nat} (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    LREqA E I n ρ₀ k Γ (.sort l) (.sort l) :=
  LREqA_sorts Γ hk (eqNA_refl l)

/-- a sort is valid above its height (`sortT`), or at any height (`sortP`). -/
theorem LRTyA_sort_valid {k : Nat} (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    ∃ R, LRTyA E I n ρ₀ k Γ (.sort l) R := by
  rw [LRTyA_eq]
  cases hz : isZero l with
  | false => exact ⟨_, .sortT (whTyA_of_hasTy (.sort Γ l)) hz hk⟩
  | true => exact ⟨_, .sortP (whTyA_of_hasTy (.sort Γ l)) hz⟩

/-- `sort l ≈ sort l'` as elements of `sort (succ l)`, above that sort's height. -/
theorem LRRelA_sorts {k : Nat} (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ (.succ l) < k)
    (hl : eqN l l') : LRRelA E I n ρ₀ k Γ (.sort (.succ l)) (.sort l) (.sort l') := by
  have hk' : ht ρ₀ l < ht ρ₀ (.succ l) := by rw [ht_succ]; exact Nat.lt_succ_self _
  have hk'' : ht ρ₀ l' < ht ρ₀ (.succ l) := by rw [← ht_of_eqN hl]; exact hk'
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ l))) (isZero_succ l) hk, ?_⟩
  exact ⟨LREqA_sorts Γ hk' hl, LRTyA_sort_valid Γ hk', LRTyA_sort_valid Γ hk'', ⟨.sort Γ l⟩,
    ⟨hasTyA_retype_sort (.sort Γ l') (eqNA_succ (eqNA_symm hl))⟩, ⟨.sorts Γ l l' hl⟩⟩

end Knot

/-! ## (3) valid pairs of substitutions -/

/-- a related pair of substitutions from `Γ` into `Δ` at height `k`: every variable's
    images are related at its substituted type, whose equality under the pair the
    validity carries; a let-bound variable's image is related to the substituted
    value, and the value's images are related. -/
def ValidSubstA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (Δ : LCtxA) (σ σ' : SubstA) (Γ : LCtxA) : Prop :=
  (∀ i A, lookupTypeA Γ i = some A →
    LREqA E I n ρ₀ k Δ (substA σ A) (substA σ' A) ∧
    LRRelA E I n ρ₀ k Δ (substA σ A) (σ i) (σ' i)) ∧
  (∀ i A v, lookupTypeA Γ i = some A → lookupValueA Γ i = some v →
    LRRelA E I n ρ₀ k Δ (substA σ A) (σ i) (substA σ v) ∧
    LRRelA E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v))

section Valid
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem ValidSubstA_mono {j j' : Nat} (hjj : j ≤ j') {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstA E I n ρ₀ j Δ σ σ' Γ) : ValidSubstA E I n ρ₀ j' Δ σ σ' Γ :=
  ⟨fun i A hA => ⟨LREqA_mono hjj (h.1 i A hA).1, LRRelA_mono hjj (h.1 i A hA).2⟩,
   fun i A v hA hv => ⟨LRRelA_mono hjj (h.2 i A v hA hv).1, LRRelA_mono hjj (h.2 i A v hA hv).2⟩⟩

theorem ValidSubstA_symm (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstA E I n ρ₀ k Δ σ σ' Γ) : ValidSubstA E I n ρ₀ k Δ σ' σ Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqA_symm hEN he, LRRelA_transport' hEN he (LRRelA_symm hEN hr)⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    have h1 : LRRelA E I n ρ₀ k Δ (substA σ A) (σ' i) (substA σ' v) :=
      LRRelA_trans hEN (LRRelA_symm hEN hr) (LRRelA_trans hEN hv1 hv2)
    exact ⟨LRRelA_transport' hEN he h1, LRRelA_transport' hEN he (LRRelA_symm hEN hv2)⟩

theorem ValidSubstA_refl_left (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstA E I n ρ₀ k Δ σ σ' Γ) : ValidSubstA E I n ρ₀ k Δ σ σ Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqA_trans hEN he (LREqA_symm hEN he), LRRelA_refl_left hEN hr⟩
  · obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    exact ⟨hv1, LRRelA_refl_left hEN hv2⟩

theorem ValidSubstA_refl_right (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    (h : ValidSubstA E I n ρ₀ k Δ σ σ' Γ) : ValidSubstA E I n ρ₀ k Δ σ' σ' Γ :=
  ValidSubstA_refl_left hEN (ValidSubstA_symm hEN h)

/-- the empty context: every pair is valid. -/
theorem ValidSubstA_nil {k : Nat} (Δ : LCtxA) (σ σ' : SubstA) : ValidSubstA E I n ρ₀ k Δ σ σ' [] :=
  ⟨fun i _ h => by cases i <;> simp [lookupTypeA] at h,
   fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h⟩

end Valid

/-! ## (4) the statement -/

/-- the fundamental theorem's conclusion for `Γ ⊢ e ≈ e' : A`. -/
def FundArmA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) (e e' A : ExprA) : Prop :=
  ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
    ValidSubstA E I n ρ₀ k Δ σ σ' Γ →
    LREqA E I n ρ₀ k Δ (substA σ A) (substA σ' A) ∧
    LRRelA E I n ρ₀ k Δ (substA σ A) (substA σ e) (substA σ' e')

/-- typing half: every typed term is related to itself under every valid pair. -/
def FundHasTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E I n Γ e A → FundArmA E I n ρ₀ Γ e e A

/-- conversion half. -/
def FundConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {a b A : ExprA}, ConvA E I n Γ a b A → FundArmA E I n ρ₀ Γ a b A

/-! ## (5) the twenty-seven arms, at their shapes -/

section Arms
variable (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)

def HasTyArmSortA : Prop := ∀ (Γ : LCtxA) (l : Level),
  FundArmA E I n ρ₀ Γ (.sort l) (.sort l) (.sort (.succ l))

def HasTyArmBvarA : Prop := ∀ (Γ : LCtxA) (i : Nat) (A : ExprA) (u : Level),
  lookupTypeA Γ i = some A → HasTyA E I n Γ A (.sort u) → FundArmA E I n ρ₀ Γ A A (.sort u) →
  FundArmA E I n ρ₀ Γ (.bvar i) (.bvar i) A

def HasTyArmConstA (D : Nat → Prop) : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls : List Level)
  (m : CheckedMemberA) (u : Level), D r → E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
  HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u) →
  FundArmA E I n ρ₀ Γ (instantiateLevelsA ls m.mtypeA) (instantiateLevelsA ls m.mtypeA) (.sort u) →
  FundArmA E I n ρ₀ Γ (.const r ls) (.const r ls) (instantiateLevelsA ls m.mtypeA)

def HasTyArmPiA : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (B : ExprA) (v : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  FundArmA E I n ρ₀ Γ A A (.sort u) → FundArmA E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmA E I n ρ₀ Γ (.pi A u B v) (.pi A u B v) (.sort (.imax u v))

def HasTyArmLamA : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (body B : ExprA) (v : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  HasTyA E I n (.assumption A :: Γ) body B →
  FundArmA E I n ρ₀ Γ A A (.sort u) → FundArmA E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmA E I n ρ₀ (.assumption A :: Γ) body body B →
  FundArmA E I n ρ₀ Γ (.lam A u body) (.lam A u body) (.pi A u B v)

def HasTyArmAppA : Prop := ∀ (Γ : LCtxA) (f a A B : ExprA) (u v w : Level),
  HasTyA E I n (.assumption A :: Γ) B (.sort v) → HasTyA E I n Γ (instantiate0A a B) (.sort w) →
  HasTyA E I n Γ f (.pi A u B v) → HasTyA E I n Γ a A →
  FundArmA E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmA E I n ρ₀ Γ (instantiate0A a B) (instantiate0A a B) (.sort w) →
  FundArmA E I n ρ₀ Γ f f (.pi A u B v) → FundArmA E I n ρ₀ Γ a a A →
  FundArmA E I n ρ₀ Γ (.app f a) (.app f a) (instantiate0A a B)

def HasTyArmLetEA : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u w : Level) (value B body : ExprA),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n Γ value A →
  HasTyA E I n Γ (instantiate0A value B) (.sort w) →
  HasTyA E I n (.letBinding A value :: Γ) body B →
  FundArmA E I n ρ₀ Γ A A (.sort u) → FundArmA E I n ρ₀ Γ value value A →
  FundArmA E I n ρ₀ Γ (instantiate0A value B) (instantiate0A value B) (.sort w) →
  FundArmA E I n ρ₀ (.letBinding A value :: Γ) body body B →
  FundArmA E I n ρ₀ Γ (.letE A value body) (.letE A value body) (instantiate0A value B)

def HasTyArmLitA : Prop := ∀ (Γ : LCtxA) (t : Nat) (T : ExprA),
  HasTyA E I n Γ (natExpandA t) T → FundArmA E I n ρ₀ Γ (natExpandA t) (natExpandA t) T →
  FundArmA E I n ρ₀ Γ (.lit t) (.lit t) T

def HasTyArmConvA : Prop := ∀ (Γ : LCtxA) (e A B : ExprA) (l u : Level),
  HasTyA E I n Γ e A → HasTyA E I n Γ A (.sort l) → eqN l u → HasTyA E I n Γ B (.sort u) →
  ConvA E I n Γ A B (.sort u) →
  FundArmA E I n ρ₀ Γ e e A → FundArmA E I n ρ₀ Γ A A (.sort l) →
  FundArmA E I n ρ₀ Γ B B (.sort u) → FundArmA E I n ρ₀ Γ A B (.sort u) →
  FundArmA E I n ρ₀ Γ e e B

def ConvArmReflA : Prop := ∀ (Γ : LCtxA) (a A : ExprA),
  HasTyA E I n Γ a A → FundArmA E I n ρ₀ Γ a a A → FundArmA E I n ρ₀ Γ a a A

def ConvArmSymmA : Prop := ∀ (Γ : LCtxA) (a b A : ExprA),
  ConvA E I n Γ a b A → FundArmA E I n ρ₀ Γ a b A → FundArmA E I n ρ₀ Γ b a A

def ConvArmTransA : Prop := ∀ (Γ : LCtxA) (a b c A : ExprA),
  ConvA E I n Γ a b A → ConvA E I n Γ b c A →
  FundArmA E I n ρ₀ Γ a b A → FundArmA E I n ρ₀ Γ b c A → FundArmA E I n ρ₀ Γ a c A

def ConvArmBetaA : Prop := ∀ (Γ : LCtxA) (A : ExprA) (u : Level) (body arg B : ExprA),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n (.assumption A :: Γ) body B →
  HasTyA E I n Γ arg A → HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B) →
  FundArmA E I n ρ₀ Γ A A (.sort u) → FundArmA E I n ρ₀ (.assumption A :: Γ) body body B →
  FundArmA E I n ρ₀ Γ arg arg A →
  FundArmA E I n ρ₀ Γ (instantiate0A arg body) (instantiate0A arg body) (instantiate0A arg B) →
  FundArmA E I n ρ₀ Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B)

def ConvArmZetaA : Prop := ∀ (Γ : LCtxA) (A value body B : ExprA) (u : Level),
  HasTyA E I n Γ A (.sort u) → HasTyA E I n Γ value A →
  HasTyA E I n (.letBinding A value :: Γ) body B →
  HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B) →
  FundArmA E I n ρ₀ Γ A A (.sort u) → FundArmA E I n ρ₀ Γ value value A →
  FundArmA E I n ρ₀ (.letBinding A value :: Γ) body body B →
  FundArmA E I n ρ₀ Γ (instantiate0A value body) (instantiate0A value body) (instantiate0A value B) →
  FundArmA E I n ρ₀ Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B)

def ConvArmZetaLocalA : Prop := ∀ (Γ : LCtxA) (i : Nat) (A v : ExprA),
  lookupValueA Γ i = some v → lookupTypeA Γ i = some A → HasTyA E I n Γ v A →
  FundArmA E I n ρ₀ Γ v v A → FundArmA E I n ρ₀ Γ (.bvar i) v A

def ConvArmDeltaA : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls : List Level) (m : CheckedMemberA)
  (b : ExprA), E.members r = some m → m.bodyA = some b → transparent m.mclass = true →
  ls.length = m.arity → levelsBounded n ls = true →
  HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) →
  FundArmA E I n ρ₀ Γ (instantiateLevelsA ls b) (instantiateLevelsA ls b)
    (instantiateLevelsA ls m.mtypeA) →
  FundArmA E I n ρ₀ Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)

def ConvArmIotaA : Prop := ∀ (Γ : LCtxA) (lhs rhs T : ExprA),
  I.rel E Γ lhs rhs → HasTyA E I n Γ lhs T → HasTyA E I n Γ rhs T →
  FundArmA E I n ρ₀ Γ lhs lhs T → FundArmA E I n ρ₀ Γ rhs rhs T → FundArmA E I n ρ₀ Γ lhs rhs T

/-- W-1 (e): ι at a struct group (`ConvA.structIota`): its premises and the three hypotheses on its
    derivations. -/
def ConvArmStructIotaA : Prop := ∀ (Γ : LCtxA) (f a rhs e T : ExprA),
  recAtMajorA E f = true → structArmA E f a = some e → I.fn (.app f a) = some rhs →
  HasTyA E I n Γ (.app f a) T → HasTyA E I n Γ rhs T → ConvA E I n Γ rhs e T →
  FundArmA E I n ρ₀ Γ (.app f a) (.app f a) T → FundArmA E I n ρ₀ Γ rhs rhs T →
  FundArmA E I n ρ₀ Γ rhs e T → FundArmA E I n ρ₀ Γ (.app f a) rhs T

def ConvArmLitA : Prop := ∀ (Γ : LCtxA) (t : Nat) (T : ExprA),
  HasTyA E I n Γ (natExpandA t) T → FundArmA E I n ρ₀ Γ (natExpandA t) (natExpandA t) T →
  FundArmA E I n ρ₀ Γ (.lit t) (natExpandA t) T

def ConvArmAppA : Prop := ∀ (Γ : LCtxA) (f g a b A B : ExprA) (u v : Level),
  ConvA E I n Γ f g (.pi A u B v) → ConvA E I n Γ a b A →
  HasTyA E I n (.assumption A :: Γ) B (.sort v) →
  HasTyA E I n Γ (.app g b) (instantiate0A a B) →
  FundArmA E I n ρ₀ Γ f g (.pi A u B v) → FundArmA E I n ρ₀ Γ a b A →
  FundArmA E I n ρ₀ (.assumption A :: Γ) B B (.sort v) →
  FundArmA E I n ρ₀ Γ (.app g b) (.app g b) (instantiate0A a B) →
  FundArmA E I n ρ₀ Γ (.app f a) (.app g b) (instantiate0A a B)

def ConvArmLamA : Prop := ∀ (Γ : LCtxA) (A A' b b' B : ExprA) (u u' v : Level), eqN u u' →
  ConvA E I n Γ A A' (.sort u) → ConvA E I n (.assumption A :: Γ) b b' B →
  HasTyA E I n Γ (.lam A' u' b') (.pi A u B v) →
  FundArmA E I n ρ₀ Γ A A' (.sort u) → FundArmA E I n ρ₀ (.assumption A :: Γ) b b' B →
  FundArmA E I n ρ₀ Γ (.lam A' u' b') (.lam A' u' b') (.pi A u B v) →
  FundArmA E I n ρ₀ Γ (.lam A u b) (.lam A' u' b') (.pi A u B v)

def ConvArmPiA : Prop := ∀ (Γ : LCtxA) (A A' B B' : ExprA) (u u' v v' : Level),
  eqN u u' → eqN v v' →
  ConvA E I n Γ A A' (.sort u) → ConvA E I n (.assumption A :: Γ) B B' (.sort v) →
  HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v)) →
  FundArmA E I n ρ₀ Γ A A' (.sort u) → FundArmA E I n ρ₀ (.assumption A :: Γ) B B' (.sort v) →
  FundArmA E I n ρ₀ Γ (.pi A' u' B' v') (.pi A' u' B' v') (.sort (.imax u v)) →
  FundArmA E I n ρ₀ Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))

def ConvArmLetEA : Prop := ∀ (Γ : LCtxA) (A A' v v' b b' B : ExprA) (u : Level),
  ConvA E I n Γ A A' (.sort u) → ConvA E I n Γ v v' A →
  ConvA E I n (.letBinding A v :: Γ) b b' B →
  HasTyA E I n Γ (.letE A' v' b') (instantiate0A v B) →
  FundArmA E I n ρ₀ Γ A A' (.sort u) → FundArmA E I n ρ₀ Γ v v' A →
  FundArmA E I n ρ₀ (.letBinding A v :: Γ) b b' B →
  FundArmA E I n ρ₀ Γ (.letE A' v' b') (.letE A' v' b') (instantiate0A v B) →
  FundArmA E I n ρ₀ Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B)

def ConvArmSortsA : Prop := ∀ (Γ : LCtxA) (l₁ l₂ : Level), eqN l₁ l₂ →
  FundArmA E I n ρ₀ Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))

def ConvArmConstsA (D : Nat → Prop) : Prop := ∀ (Γ : LCtxA) (r : Nat) (ls ls' : List Level)
  (m : CheckedMemberA), D r → E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
  levelsBounded n ls' = true → eqNList ls ls' →
  HasTyA E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA) →
  FundArmA E I n ρ₀ Γ (.const r ls') (.const r ls') (instantiateLevelsA ls m.mtypeA) →
  FundArmA E I n ρ₀ Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)

def ConvArmEtaA : Prop := ∀ (Γ : LCtxA) (f A B : ExprA) (u v : Level),
  HasTyA E I n Γ f (.pi A u B v) →
  HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v) →
  FundArmA E I n ρ₀ Γ f f (.pi A u B v) →
  FundArmA E I n ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.lam A u (.app (liftA 0 1 f) (.bvar 0)))
    (.pi A u B v) →
  FundArmA E I n ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v)

def ConvArmIrrA : Prop := ∀ (Γ : LCtxA) (P p q : ExprA),
  HasTyA E I n Γ P (.sort .zero) → HasTyA E I n Γ p P → HasTyA E I n Γ q P →
  FundArmA E I n ρ₀ Γ P P (.sort .zero) → FundArmA E I n ρ₀ Γ p p P → FundArmA E I n ρ₀ Γ q q P →
  FundArmA E I n ρ₀ Γ p q P

def ConvArmTyConvA : Prop := ∀ (Γ : LCtxA) (a b A A' : ExprA) (l l' u : Level),
  ConvA E I n Γ a b A → HasTyA E I n Γ A (.sort l) → eqN l u → HasTyA E I n Γ A' (.sort l') →
  eqN l' u → ConvA E I n Γ A A' (.sort u) →
  FundArmA E I n ρ₀ Γ a b A → FundArmA E I n ρ₀ Γ A A (.sort l) →
  FundArmA E I n ρ₀ Γ A' A' (.sort l') → FundArmA E I n ρ₀ Γ A A' (.sort u) →
  FundArmA E I n ρ₀ Γ a b A'

structure FundHasTyArmsA (D : Nat → Prop) : Prop where
  sortA : HasTyArmSortA E I n ρ₀
  bvarA : HasTyArmBvarA E I n ρ₀
  constA : HasTyArmConstA E I n ρ₀ D
  piA : HasTyArmPiA E I n ρ₀
  lamA : HasTyArmLamA E I n ρ₀
  appA : HasTyArmAppA E I n ρ₀
  letEA : HasTyArmLetEA E I n ρ₀
  litA : HasTyArmLitA E I n ρ₀
  convA : HasTyArmConvA E I n ρ₀

structure FundConvArmsA (D : Nat → Prop) : Prop where
  reflA : ConvArmReflA E I n ρ₀
  symmA : ConvArmSymmA E I n ρ₀
  transA : ConvArmTransA E I n ρ₀
  betaA : ConvArmBetaA E I n ρ₀
  zetaA : ConvArmZetaA E I n ρ₀
  zetaLocalA : ConvArmZetaLocalA E I n ρ₀
  deltaA : ConvArmDeltaA E I n ρ₀
  iotaA : ConvArmIotaA E I n ρ₀
  structIotaA : ConvArmStructIotaA E I n ρ₀
  litA : ConvArmLitA E I n ρ₀
  appA : ConvArmAppA E I n ρ₀
  lamA : ConvArmLamA E I n ρ₀
  piA : ConvArmPiA E I n ρ₀
  letEA : ConvArmLetEA E I n ρ₀
  sortsA : ConvArmSortsA E I n ρ₀
  constsA : ConvArmConstsA E I n ρ₀ D
  etaA : ConvArmEtaA E I n ρ₀
  irrA : ConvArmIrrA E I n ρ₀
  tyConvA : ConvArmTyConvA E I n ρ₀

end Arms

/-! ## (6) the assembly: structural recursion on the derivations -/

section Assembly
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

mutual

theorem fundHasTyOfArmsA (ht : FundHasTyArmsA E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsA E I n ρ₀ (fun _ => True)) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → FundArmA E I n ρ₀ Γ e e A
  | _, _, _, .sort Γ l => ht.sortA Γ l
  | _, _, _, .bvar Γ i A u h hA => ht.bvarA Γ i A u h hA (fundHasTyOfArmsA ht hc hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      ht.constA Γ r ls m u trivial hres hlen hwf hT (fundHasTyOfArmsA ht hc hT)
  | _, _, _, .pi Γ A u B v hA hB =>
      ht.piA Γ A u B v hA hB (fundHasTyOfArmsA ht hc hA) (fundHasTyOfArmsA ht hc hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      ht.lamA Γ A u body B v hA hB hbody (fundHasTyOfArmsA ht hc hA)
        (fundHasTyOfArmsA ht hc hB) (fundHasTyOfArmsA ht hc hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha =>
      ht.appA Γ f a A B u v w hB hTy hf ha (fundHasTyOfArmsA ht hc hB)
        (fundHasTyOfArmsA ht hc hTy) (fundHasTyOfArmsA ht hc hf) (fundHasTyOfArmsA ht hc ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      ht.letEA Γ A u w value B body hA hv hTy hb (fundHasTyOfArmsA ht hc hA)
        (fundHasTyOfArmsA ht hc hv) (fundHasTyOfArmsA ht hc hTy) (fundHasTyOfArmsA ht hc hb)
  | _, _, _, .lit Γ t T hexp => ht.litA Γ t T hexp (fundHasTyOfArmsA ht hc hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hcv =>
      ht.convA Γ e A B l u h hAl hlu hB hcv (fundHasTyOfArmsA ht hc h)
        (fundHasTyOfArmsA ht hc hAl) (fundHasTyOfArmsA ht hc hB) (fundConvOfArmsA ht hc hcv)

theorem fundConvOfArmsA (ht : FundHasTyArmsA E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsA E I n ρ₀ (fun _ => True)) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A → FundArmA E I n ρ₀ Γ a b A
  | _, _, _, _, .refl Γ a A h => hc.reflA Γ a A h (fundHasTyOfArmsA ht hc h)
  | _, _, _, _, .symm Γ a b A h => hc.symmA Γ a b A h (fundConvOfArmsA ht hc h)
  | _, _, _, _, .trans Γ a b c A h1 h2 =>
      hc.transA Γ a b c A h1 h2 (fundConvOfArmsA ht hc h1) (fundConvOfArmsA ht hc h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      hc.betaA Γ A u body arg B hA hbody harg hred (fundHasTyOfArmsA ht hc hA)
        (fundHasTyOfArmsA ht hc hbody) (fundHasTyOfArmsA ht hc harg) (fundHasTyOfArmsA ht hc hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      hc.zetaA Γ A value body B u hA hv hb hred (fundHasTyOfArmsA ht hc hA)
        (fundHasTyOfArmsA ht hc hv) (fundHasTyOfArmsA ht hc hb) (fundHasTyOfArmsA ht hc hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      hc.zetaLocalA Γ i A v hval hty hv (fundHasTyOfArmsA ht hc hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      hc.deltaA Γ r ls m b hres hbody htr hlen hwf hb (fundHasTyOfArmsA ht hc hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      hc.iotaA Γ lhs rhs T h hlhs hrhs (fundHasTyOfArmsA ht hc hlhs) (fundHasTyOfArmsA ht hc hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      hc.structIotaA Γ f a rhs e T hrec hs h hlhs hrhs hcv (fundHasTyOfArmsA ht hc hlhs)
        (fundHasTyOfArmsA ht hc hrhs) (fundConvOfArmsA ht hc hcv)
  | _, _, _, _, .lit Γ t T hexp => hc.litA Γ t T hexp (fundHasTyOfArmsA ht hc hexp)
  | _, _, _, _, .app Γ f g a b A B u v h1 h2 hB hrt =>
      hc.appA Γ f g a b A B u v h1 h2 hB hrt (fundConvOfArmsA ht hc h1) (fundConvOfArmsA ht hc h2)
        (fundHasTyOfArmsA ht hc hB) (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      hc.lamA Γ A A' b b' B u u' v hu hA hb hrt (fundConvOfArmsA ht hc hA)
        (fundConvOfArmsA ht hc hb) (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      hc.piA Γ A A' B B' u u' v v' hu hv hA hB hrt (fundConvOfArmsA ht hc hA)
        (fundConvOfArmsA ht hc hB) (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt =>
      hc.letEA Γ A A' v v' b b' B u hA hv hb hrt (fundConvOfArmsA ht hc hA)
        (fundConvOfArmsA ht hc hv) (fundConvOfArmsA ht hc hb) (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => hc.sortsA Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      hc.constsA Γ r ls ls' m trivial hres hlen hwf hwf' h hrt (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt =>
      hc.etaA Γ f A B u v h hrt (fundHasTyOfArmsA ht hc h) (fundHasTyOfArmsA ht hc hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      hc.irrA Γ P p q hP hp hq (fundHasTyOfArmsA ht hc hP) (fundHasTyOfArmsA ht hc hp)
        (fundHasTyOfArmsA ht hc hq)
  | _, _, _, _, .tyConv Γ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      hc.tyConvA Γ a b A A' l l' u h hAl hlu hA'l hl'u hA (fundConvOfArmsA ht hc h)
        (fundHasTyOfArmsA ht hc hAl) (fundHasTyOfArmsA ht hc hA'l) (fundConvOfArmsA ht hc hA)

end

/-- the fundamental theorem from an arm bundle. -/
theorem fundOfArmsA (ht : FundHasTyArmsA E I n ρ₀ (fun _ => True))
    (hc : FundConvArmsA E I n ρ₀ (fun _ => True)) :
    FundHasTyA E I n ρ₀ ∧ FundConvA E I n ρ₀ :=
  ⟨fun h => fundHasTyOfArmsA ht hc h, fun h => fundConvOfArmsA ht hc h⟩

end Assembly

/-! ## (7) the arms without binder content -/

section ArmsProved
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the threshold of two IHs. -/
theorem le_max_of_le₁ {k₁ k₂ k : Nat} (hk : max k₁ k₂ ≤ k) : k₁ ≤ k :=
  Nat.le_trans (Nat.le_max_left _ _) hk
theorem le_max_of_le₂ {k₁ k₂ k : Nat} (hk : max k₁ k₂ ≤ k) : k₂ ≤ k :=
  Nat.le_trans (Nat.le_max_right _ _) hk

theorem hasTyArmSortA_holds : HasTyArmSortA E I n ρ₀ := fun Γ l =>
  ⟨ht ρ₀ (.succ l) + 1, fun k hk Δ _ _ _ _ =>
    ⟨LREqA_sort_refl Δ hk, LRRelA_sorts Δ hk (eqNA_refl l)⟩⟩

theorem convArmSortsA_holds : ConvArmSortsA E I n ρ₀ := fun Γ l₁ l₂ h =>
  ⟨ht ρ₀ (.succ l₁) + 1, fun k hk Δ _ _ _ _ => ⟨LREqA_sort_refl Δ hk, LRRelA_sorts Δ hk h⟩⟩

theorem hasTyArmBvarA_holds : HasTyArmBvarA E I n ρ₀ := fun _ i A _ h _ _ =>
  ⟨0, fun _ _ _ _ _ _ hσ => hσ.1 i A h⟩

theorem convArmReflA_holds : ConvArmReflA E I n ρ₀ := fun _ _ _ _ ih => ih

theorem convArmSymmA_holds (hEN : EnvNormCtorTypeA E) : ConvArmSymmA E I n ρ₀ := fun _ _ _ _ _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ' σ hΔ (ValidSubstA_symm hEN hσ)
  exact ⟨LREqA_symm hEN he, LRRelA_transport' hEN he (LRRelA_symm hEN hr)⟩

theorem convArmTransA_holds (hEN : EnvNormCtorTypeA E) : ConvArmTransA E I n ρ₀ := fun _ _ _ _ _ _ _ ih₁ ih₂ => by
  obtain ⟨k₁, h₁⟩ := ih₁
  obtain ⟨k₂, h₂⟩ := ih₂
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr₁⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ hΔ (ValidSubstA_refl_left hEN hσ)
  obtain ⟨he, hr₂⟩ := h₂ k (le_max_of_le₂ hk) Δ σ σ' hΔ hσ
  exact ⟨he, LRRelA_trans hEN hr₁ hr₂⟩

theorem hasTyArmConvA_holds (hEN : EnvNormCtorTypeA E) : HasTyArmConvA E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ ih _ ihB ihc => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihB
  obtain ⟨k₃, h₃⟩ := ihc
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hB⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hc⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_left hEN hσ)
  exact ⟨LREqA_of_sortRel hB, LRRelA_transport' hEN (LREqA_of_sortRel hc) hr⟩

theorem convArmTyConvA_holds (hEN : EnvNormCtorTypeA E) : ConvArmTyConvA E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ ihA' ihA => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihA'
  obtain ⟨k₃, h₃⟩ := ihA
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hA'⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hAA'⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_left hEN hσ)
  exact ⟨LREqA_of_sortRel hA', LRRelA_transport' hEN (LREqA_of_sortRel hAA') hr⟩

theorem convArmZetaLocalA_holds (hEN : EnvNormCtorTypeA E) : ConvArmZetaLocalA E I n ρ₀ := fun _ i A v hval hty _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  obtain ⟨hv1, _⟩ := hσ.2 i A v hty hval
  exact ⟨he, LRRelA_trans hEN hv1 hr⟩

theorem hasTyArmLitA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) : HasTyArmLitA E I n ρ₀ :=
  fun _ t T _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelA_hasTy hr
  have hs : StepAtA E I n Δ (.lit t) (natExpandA t) (substA σ T) :=
    ⟨hl.elim fun x => ⟨.lit Δ t _ x⟩, hl.elim fun x => ⟨.lit Δ t _ x⟩⟩
  exact ⟨he, LRRelA_expand_left hE hI hs (LRRelA_expand_right hE hI hs hr)⟩

theorem convArmLitA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) : ConvArmLitA E I n ρ₀ :=
  fun _ t T _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelA_hasTy hr
  have hs : StepAtA E I n Δ (.lit t) (natExpandA t) (substA σ T) :=
    ⟨hl.elim fun x => ⟨.lit Δ t _ x⟩, hl.elim fun x => ⟨.lit Δ t _ x⟩⟩
  simp only [substA_natExpandA]
  exact ⟨he, LRRelA_expand_left hE hI hs hr⟩

/-- member bodies are fixed by every substitution (`EnvClosedA`; types: `substA_mtype`). -/
theorem substA_mbody (hE : EnvClosedA E) {r : Nat} {m : CheckedMemberA} {b : ExprA}
    (hres : E.members r = some m) (hb : m.bodyA = some b) (ls : List Level) (τ : SubstA) :
    substA τ (instantiateLevelsA ls b) = instantiateLevelsA ls b :=
  substA_closed (liftA_instantiateLevelsA_closed ((hE r m hres).2 b hb) ls) τ

theorem convArmDeltaA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) : ConvArmDeltaA E I n ρ₀ :=
  fun _ r ls m b hres hbody htr hlen hwf _ ih => by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mbody hE hres hbody, substA_mbody hE hres hbody] at hr
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_mbody hE hres hbody, substA_const]
  obtain ⟨hl, _⟩ := LRRelA_hasTy hr
  obtain ⟨R, hR⟩ := LRRelA_valid hr
  obtain ⟨u, hTu⟩ := LRTyA_hasTy hR
  have hs : StepAtA E I n Δ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) :=
    ⟨hTu.elim fun tu => ⟨.const Δ r ls m u hres hlen hwf tu⟩,
     hl.elim fun x => ⟨.delta Δ r ls m b hres hbody htr hlen hwf x⟩⟩
  exact ⟨he, LRRelA_expand_left hE hI hs hr⟩

theorem hasTyArmConstA_holds (hE : EnvClosedA E) {D : Nat → Prop} (hS : EnvSemAt E I n ρ₀ D) :
    HasTyArmConstA E I n ρ₀ D :=
  fun _ r ls m _ hD hres hlen hwf _ ih => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hD hres ls ls hlen hwf hwf (eqNList_refl ls)
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hTT⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at hTT
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨LREqA_of_sortRel hTT, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmConstsA_holds (hE : EnvClosedA E) {D : Nat → Prop} (hS : EnvSemAt E I n ρ₀ D) :
    ConvArmConstsA E I n ρ₀ D :=
  fun _ r ls ls' m hD hres hlen hwf hwf' h _ ih => by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hD hres ls ls' hlen hwf hwf' h
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, _⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨he, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmIrrA_holds (hEN : EnvNormCtorTypeA E) : ConvArmIrrA E I n ρ₀ := fun _ P p q _ _ _ ihP ihp ihq => by
  obtain ⟨k₁, h₁⟩ := ihP
  obtain ⟨k₂, h₂⟩ := ihp
  obtain ⟨k₃, h₃⟩ := ihq
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨_, hPP⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨heP, hp⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hq⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ' σ' hΔ (ValidSubstA_refl_right hEN hσ)
  obtain ⟨⟨N, hN, hNt⟩, _, hPt, hP't, hPc, _⟩ := LRRelA_sort0_elim hPP
  have hpt : Nonempty (HasTyA E I n Δ (substA σ p) (substA σ P)) := (LRRelA_hasTy hp).1
  have hqt' : Nonempty (HasTyA E I n Δ (substA σ' q) (substA σ' P)) := (LRRelA_hasTy hq).1
  have hqt : Nonempty (HasTyA E I n Δ (substA σ' q) (substA σ P)) :=
    hqt'.elim fun tq => hP't.elim fun tP' => hPt.elim fun tP => hPc.elim fun c =>
      ⟨.conv Δ _ _ _ .zero .zero tq tP' (eqNA_refl _) tP (.symm Δ _ _ _ c)⟩
  refine ⟨heP, ⟨_, by rw [LRTyA_eq]; exact tyKA_of_tripleLike hN hNt, ?_⟩⟩
  obtain ⟨tc⟩ := whTyA_tyConv hN
  exact ⟨hpt.elim fun tp => ⟨hasTyA_of_tyConvA tp tc⟩, hqt.elim fun tq => ⟨hasTyA_of_tyConvA tq tc⟩,
    hPt.elim fun tP => hpt.elim fun tp => hqt.elim fun tq =>
      ⟨convA_of_tyConvA (.irr Δ _ _ _ tP tp tq) tc⟩⟩

/-! ### ι survives substitution: the redex's head chain stays normal (exact arity),
    the step is preserved (`IotaSubstA`) -/

/-- the spine of a constant-headed term under substitution: the same head, the
    arguments substituted. -/
theorem appsSpineA_substA_const (σ : SubstA) :
    (e : ExprA) → {r : Nat} → {ls : List Level} → (appsSpineA e).1 = .const r ls →
    appsSpineA (substA σ e) = (.const r ls, (appsSpineA e).2.map (substA σ))
  | .const r' ls', _, _, h => by
      have h' : ExprA.const r' ls' = .const _ _ := h
      injection h' with h1 h2
      subst h1; subst h2
      rfl
  | .app f x, r, ls, h => by
      have hf : (appsSpineA f).1 = .const r ls := h
      show appsSpineA (.app (substA σ f) (substA σ x)) = _
      simp only [appsSpineA, appsSpineA_substA_const σ f hf, List.map_append, List.map_cons,
        List.map_nil]
  | .bvar _, _, _, h => by simp [appsSpineA] at h
  | .sort _, _, _, h => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, h => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, h => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, h => by simp [appsSpineA] at h
  | .lit _, _, _, h => by simp [appsSpineA] at h

theorem recAtMajorA_substA (E : ResolvedEnvA) (σ : SubstA) {f : ExprA} {r : Nat} {ls : List Level}
    (hf : (appsSpineA f).1 = .const r ls) : recAtMajorA E (substA σ f) = recAtMajorA E f := by
  unfold recAtMajorA
  rw [appsSpineA_substA_const σ f hf, hf, List.length_map]

/-- a spine at its major stays at its major under a substitution. -/
theorem recAtMajorA_substA_true (E : ResolvedEnvA) (σ : SubstA) {f : ExprA} (h : recAtMajorA E f = true) :
    recAtMajorA E (substA σ f) = true := by
  obtain ⟨r, ls, m, hsp, _, _, _⟩ := recAtMajorA_true h
  rw [recAtMajorA_substA E σ hsp]; exact h

/-- W-1 (e): the struct head and the struct position read the spine's head, which a substitution keeps
    at a constant head. -/
theorem structHeadA_substA (E : ResolvedEnvA) (σ : SubstA) {f : ExprA} {r : Nat} {ls : List Level}
    (hf : (appsSpineA f).1 = .const r ls) : structHeadA E (substA σ f) = structHeadA E f := by
  unfold structHeadA
  rw [appsSpineA_substA_const σ f hf, hf]

theorem structPosA_substA (E : ResolvedEnvA) (σ : SubstA) {f : ExprA} {r : Nat} {ls : List Level}
    (hf : (appsSpineA f).1 = .const r ls) : structPosA E (substA σ f) = structPosA E f := by
  unfold structPosA
  rw [recAtMajorA_substA E σ hf, structHeadA_substA E σ hf]

theorem belowMajorA_substA (E : ResolvedEnvA) (σ : SubstA) {e : ExprA} {r : Nat} {ls : List Level}
    (he : (appsSpineA e).1 = .const r ls) (hb : BelowMajorA E e) : BelowMajorA E (substA σ e) := by
  intro r' ls' m hsp hres hc
  rw [appsSpineA_substA_const σ e he] at hsp ⊢
  rw [List.length_map]
  exact hb r' ls' m (he.trans hsp) hres hc

/-- EXACT ARITY: ι refuses on a member-headed spine strictly below the major, given the head-recursor
    fact of every step of it. -/
theorem iotaFn_none_of_head {e : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (he : (appsSpineA e).1 = .const r ls) (hres : E.members r = some m)
    (hb : BelowMajorA E e)
    (hh : ∀ e', I.fn e = some e' → ∃ r ls m, (appsSpineA e).1 = .const r ls ∧ E.members r = some m ∧
      m.mclass = .recursorM ∧ (appsSpineA e).2.length = piCountA m.mtypeA) : I.fn e = none := by
  cases hfn : I.fn e with
  | none => rfl
  | some e' =>
      exfalso
      obtain ⟨r', ls', m', hsp', hres', hc, hlen⟩ := hh e' hfn
      have h1 : ExprA.const r ls = .const r' ls' := he.symm.trans hsp'
      injection h1 with h1 _
      subst h1
      rw [hres] at hres'
      cases hres'
      have := hb r ls m he hres hc
      omega

/-- EXACT ARITY: ι refuses on a member-headed spine strictly below the major. -/
theorem iotaFn_none_of_below (hR : IotaRecHeadA E I) {e : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (he : (appsSpineA e).1 = .const r ls) (hres : E.members r = some m)
    (hb : BelowMajorA E e) : I.fn e = none :=
  iotaFn_none_of_head he hres hb (fun e' hfn => hR e e' hfn)

/-- the same at a typed spine, from the typed head fact (R-NoFunRec-1 step 1 (1c-ε2d-0)). -/
theorem iotaFn_none_of_below_typed (hR : IotaRecHeadTypedA E I) {n : Nat} {Γ : LCtxA} {e T : ExprA}
    {r : Nat} {ls : List Level} {m : CheckedMemberA} (ht : Nonempty (HasTyA E I n Γ e T))
    (he : (appsSpineA e).1 = .const r ls) (hres : E.members r = some m) (hb : BelowMajorA E e) :
    I.fn e = none :=
  iotaFn_none_of_head he hres hb (fun e' hfn => hR n Γ e e' T hfn ht)

/-- the function part of a typed application is typed (R-NoFunRec-1 step 1 (1c-ε2d-0)). -/
theorem hasTyA_app_fun {n : Nat} : {Γ : LCtxA} → {f a T : ExprA} → HasTyA E I n Γ (.app f a) T →
    ∃ T', Nonempty (HasTyA E I n Γ f T')
  | _, _, _, _, .app _ _ _ A B u v _ _ _ hf _ => ⟨.pi A u B v, ⟨hf⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_app_fun h

/-- on a member-headed spine strictly below the major the head step commutes with
    substitution: the head is fixed, δ unfolds a closed body (`EnvClosedA`), ι
    refuses on both sides (exact arity) and the major arm is dead on both sides. -/
theorem hStepFnA_substA_below (hE : EnvClosedA E) (hR : IotaRecHeadTypedA E I) {n : Nat} (Γ Δ : LCtxA)
    (σ : SubstA) :
    (e : ExprA) → {T T' : ExprA} → {r : Nat} → {ls : List Level} → {m : CheckedMemberA} →
    (appsSpineA e).1 = .const r ls → E.members r = some m → BelowMajorA E e →
    Nonempty (HasTyA E I n Γ e T) → Nonempty (HasTyA E I n Δ (substA σ e) T') →
    hStepFnA E I.fn Δ (substA σ e) = (hStepFnA E I.fn Γ e).map (substA σ)
  | .const r' ls', _, _, _, _, _, _, _, _, _, _ => by
      rw [substA_const]
      show (match E.members r' with
          | some m => if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls') else none
          | none => none) =
        (match E.members r' with
          | some m => if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls') else none
          | none => none).map (substA σ)
      cases hm : E.members r' with
      | none => rfl
      | some m =>
          show (if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none) =
            (if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none).map
              (substA σ)
          cases htr : transparent m.mclass with
          | false => rfl
          | true =>
              cases hb : m.bodyA with
              | none => rfl
              | some b =>
                  show some (instantiateLevelsA ls' b) = some (substA σ (instantiateLevelsA ls' b))
                  rw [substA_mbody hE hm hb]
  | .app f x, _, _, r, ls, m, he, hres, hb, ⟨t⟩, ⟨t'⟩ => by
      have hf : (appsSpineA f).1 = .const r ls := he
      obtain ⟨_, ⟨tf⟩⟩ := hasTyA_app_fun t
      obtain ⟨_, ⟨tf'⟩⟩ := hasTyA_app_fun (show HasTyA E I n Δ (.app (substA σ f) (substA σ x)) _ from t')
      have ih := hStepFnA_substA_below hE hR Γ Δ σ f hf hres (belowMajorA_app hb) ⟨tf⟩ ⟨tf'⟩
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by
        subst e; simp [appsSpineA] at hf
      have hnl' : ∀ A u b, substA σ f ≠ .lam A u b := fun A u b e => by
        cases f <;> simp [appsSpineA, substA] at hf e
      have hi : I.fn (.app f x) = none := iotaFn_none_of_below_typed hR ⟨t⟩ he hres hb
      have hi' : I.fn (.app (substA σ f) (substA σ x)) = none :=
        iotaFn_none_of_below_typed hR (e := substA σ (.app f x)) ⟨t'⟩
          (by rw [appsSpineA_substA_const σ _ he]) hres (belowMajorA_substA E σ he hb)
      rw [substA_app, hStepFnA_app_nonlam E I.fn Δ (substA σ x) hnl',
        hStepFnA_app_nonlam E I.fn Γ x hnl, ih]
      cases hStepFnA E I.fn Γ f with
      | some f' => rfl
      | none =>
          dsimp only
          rw [structPosA_substA E σ hf, structPosA_of_not_rec (recAtMajorA_of_below hb),
            if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hi', hi,
            recAtMajorA_substA E σ hf, recAtMajorA_of_below hb]
          rfl
  | .bvar _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h
  | .sort _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h
  | .lit _, _, _, _, _, _, h, _, _, _, _ => by simp [appsSpineA] at h

/-- a recursor spine strictly below its major does not step: its head is a recursor (no δ), ι refuses
    (exact arity), and neither the struct arm nor the major arm is live. -/
theorem hStepFnA_below_none (hR : IotaRecHeadA E I) (Γ : LCtxA) :
    (e : ExprA) → {r : Nat} → {ls : List Level} → {m : CheckedMemberA} →
    (appsSpineA e).1 = .const r ls → E.members r = some m → m.mclass = .recursorM →
    BelowMajorA E e → hStepFnA E I.fn Γ e = none
  | .const r' ls', r, ls, m, he, hres, hc, _ => by
      have h1 : ExprA.const r' ls' = .const r ls := he
      injection h1 with h1 _
      subst h1
      show (match E.members r' with
          | some m => if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls') else none
          | none => none) = none
      rw [hres]
      simp [hc, transparent]
  | .app f x, r, ls, m, he, hres, hc, hb => by
      have hf : (appsSpineA f).1 = .const r ls := he
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by
        subst e; simp [appsSpineA] at hf
      exact hStepFnA_app_none E I.fn Γ hnl (hStepFnA_below_none hR Γ f hf hres hc (belowMajorA_app hb))
        (iotaFn_none_of_below hR he hres hb) (recAtMajorA_of_below hb)
  | .bvar _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .sort _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h
  | .lit _, _, _, _, h, _, _, _ => by simp [appsSpineA] at h

/-- a declarative ι step survives substitution, as a declarative ι step: the graph
    by `IotaSubstA`, its execution because the redex's function part is strictly
    below the major (exact arity) and so steps the same way under substitution. -/
theorem iotaRel_substA (hE : EnvClosedA E) (hR : IotaRecHeadTypedA E I) (hIS : IotaSubstA I) {n : Nat}
    {Γ Δ : LCtxA} (σ : SubstA) {lhs rhs T T' : ExprA} (h : I.rel E Γ lhs rhs)
    (ht : Nonempty (HasTyA E I n Γ lhs T)) (ht' : Nonempty (HasTyA E I n Δ (substA σ lhs) T')) :
    I.rel E Δ (substA σ lhs) (substA σ rhs) := by
  obtain ⟨r, ls, m, hsp, hres, hc, hlen⟩ := hR n Γ lhs rhs T h.1 ht
  refine ⟨hIS σ lhs rhs h.1, ?_⟩
  have h2 := h.2
  cases lhs with
  | app f x =>
      have hf : (appsSpineA f).1 = .const r ls := hsp
      have hb : BelowMajorA E f := belowMajorA_of_at hsp hres hlen
      have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by
        subst e; simp [appsSpineA] at hf
      have hnl' : ∀ A u b, substA σ f ≠ .lam A u b := fun A u b e => by
        cases f <;> simp [appsSpineA, substA] at hf e
      obtain ⟨t⟩ := ht
      obtain ⟨t'⟩ := ht'
      obtain ⟨_, ⟨tf⟩⟩ := hasTyA_app_fun t
      obtain ⟨_, ⟨tf'⟩⟩ := hasTyA_app_fun (show HasTyA E I n Δ (.app (substA σ f) (substA σ x)) _ from t')
      have hsub := hStepFnA_substA_below hE hR Γ Δ σ f hf hres hb ⟨tf⟩ ⟨tf'⟩
      rw [hStepFnA_app_nonlam E I.fn Γ x hnl] at h2
      cases hff : hStepFnA E I.fn Γ f with
      | some f' =>
          rw [hff] at h2 hsub
          have h2' : some (ExprA.app f' x) = some rhs := h2
          injection h2' with h2'
          have hsub' : hStepFnA E I.fn Δ (substA σ f) = some (substA σ f') := hsub
          rw [← h2', substA_app, substA_app]
          exact hStepFnA_app_head E I.fn Δ (substA σ x) hsub'
      | none =>
          rw [hff] at hsub
          have hsub' : hStepFnA E I.fn Δ (substA σ f) = none := hsub
          rw [substA_app]
          cases hp : structPosA E f with
          | true =>
              -- W-1 (e): at the struct position the step is the struct arm's, so ι's contractum is it
              have harm : structArmA E f x = some rhs := by
                rw [← hStepFnA_app_structPos E I.fn Γ hnl hff hp]; exact h.2
              rw [hStepFnA_app_structPos E I.fn Δ hnl' hsub' (by rw [structPosA_substA E σ hf]; exact hp)]
              exact structArmA_substA hE σ harm
          | false =>
              exact hStepFnA_app_iota E I.fn Δ hnl' hsub' (by rw [structPosA_substA E σ hf]; exact hp)
                (hIS σ (.app f x) rhs h.1)
  | const r' ls' =>
      exfalso
      have h1 : ExprA.const r' ls' = .const r ls := hsp
      injection h1 with h1 _
      subst h1
      have h2' : (match E.members r' with
          | some m => if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ls') else none
          | none => none) = some rhs := h2
      rw [hres] at h2'
      simp [hc, transparent] at h2'
  | bvar _ => simp [appsSpineA] at hsp
  | sort _ => simp [appsSpineA] at hsp
  | lam _ _ _ => simp [appsSpineA] at hsp
  | pi _ _ _ _ => simp [appsSpineA] at hsp
  | letE _ _ _ => simp [appsSpineA] at hsp
  | lit _ => simp [appsSpineA] at hsp

theorem convArmIotaA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) : ConvArmIotaA E I n ρ₀ := fun Γ lhs rhs T h hlhsT _ ihl ihr => by
  obtain ⟨k₁, h₁⟩ := ihl
  obtain ⟨k₂, h₂⟩ := ihr
  refine ⟨max k₁ k₂, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hl⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hr⟩ := h₂ k (le_max_of_le₂ hk) Δ σ σ' hΔ hσ
  obtain ⟨hlt, _⟩ := LRRelA_hasTy hl
  obtain ⟨hrt, _⟩ := LRRelA_hasTy hr
  have hs : StepAtA E I n Δ (substA σ lhs) (substA σ rhs) (substA σ T) :=
    ⟨hlt, hlt.elim fun tl => hrt.elim fun tr =>
      ⟨.iota Δ _ _ _ (iotaRel_substA hE (iotaRecHeadTypedA_of hR) hIS σ h ⟨hlhsT⟩ ⟨tl⟩) tl tr⟩⟩
  exact ⟨he, LRRelA_expand_left hE hI hs hr⟩

/-- W-1 (e): THE ARM OF ι AT A STRUCT GROUP. Under a valid pair the substituted spine steps by the
    struct arm (`TyHRedA.kstruct`): its conversion is the rule rebuilt at the substituted spine followed
    by the carried conversion, escaped from its own hypothesis. The relation expands on the left
    along that step, and the carried conversion relates the two contracta. -/
theorem convArmStructIotaA_holds (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) : ConvArmStructIotaA E I n ρ₀ :=
  fun Γ f a rhs e T hrec hs h _ _ _ ihl ihr ihc => by
  obtain ⟨k₁, h₁⟩ := ihl
  obtain ⟨k₂, h₂⟩ := ihr
  obtain ⟨k₃, h₃⟩ := ihc
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨he, hl⟩ := h₁ k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hr⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ σ σ' hΔ hσ
  obtain ⟨_, hc⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ σ σ hΔ (ValidSubstA_refl_left hEN hσ)
  obtain ⟨⟨tl⟩, _⟩ := LRRelA_hasTy hl
  obtain ⟨⟨tr⟩, _⟩ := LRRelA_hasTy hr
  obtain ⟨_, ⟨te⟩⟩ := LRRelA_hasTy hc
  obtain ⟨cc⟩ := LRRelA_conv hc
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
  exact ⟨he, LRRelA_expand_left hE hI hst (LRRelA_trans hEN (LRRelA_symm hEN hc) hr)⟩

/-! ### the bundles, with the binder arms as hypotheses -/

theorem fundHasTyArmsA_of (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E)
    {D : Nat → Prop}
    (hS : EnvSemAt E I n ρ₀ D)
    (hpi : HasTyArmPiA E I n ρ₀) (hlam : HasTyArmLamA E I n ρ₀) (happ : HasTyArmAppA E I n ρ₀)
    (hletE : HasTyArmLetEA E I n ρ₀) : FundHasTyArmsA E I n ρ₀ D :=
  ⟨hasTyArmSortA_holds, hasTyArmBvarA_holds, hasTyArmConstA_holds hE hS, hpi, hlam, happ, hletE,
   hasTyArmLitA_holds hE hI, hasTyArmConvA_holds hEN⟩

theorem fundConvArmsA_of (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) {D : Nat → Prop} (hS : EnvSemAt E I n ρ₀ D)
    (hbeta : ConvArmBetaA E I n ρ₀) (hzeta : ConvArmZetaA E I n ρ₀) (happ : ConvArmAppA E I n ρ₀)
    (hlam : ConvArmLamA E I n ρ₀) (hpi : ConvArmPiA E I n ρ₀) (hletE : ConvArmLetEA E I n ρ₀)
    (heta : ConvArmEtaA E I n ρ₀) : FundConvArmsA E I n ρ₀ D :=
  ⟨convArmReflA_holds, convArmSymmA_holds hEN, convArmTransA_holds hEN, hbeta, hzeta,
   convArmZetaLocalA_holds hEN, convArmDeltaA_holds hE hI, convArmIotaA_holds hE hI hIS hEN hR,
   convArmStructIotaA_holds hE hI hIS hEN hR,
   convArmLitA_holds hE hI, happ, hlam, hpi, hletE, convArmSortsA_holds,
   convArmConstsA_holds hE hS, heta, convArmIrrA_holds hEN, convArmTyConvA_holds hEN⟩

/-- the fundamental theorem, given the eleven binder arms (M2-e (2)). -/
theorem fund_of_binderArms (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hpi : HasTyArmPiA E I n ρ₀) (hlam : HasTyArmLamA E I n ρ₀) (happ : HasTyArmAppA E I n ρ₀)
    (hletE : HasTyArmLetEA E I n ρ₀)
    (cbeta : ConvArmBetaA E I n ρ₀) (czeta : ConvArmZetaA E I n ρ₀) (capp : ConvArmAppA E I n ρ₀)
    (clam : ConvArmLamA E I n ρ₀) (cpi : ConvArmPiA E I n ρ₀) (cletE : ConvArmLetEA E I n ρ₀)
    (ceta : ConvArmEtaA E I n ρ₀) : FundHasTyA E I n ρ₀ ∧ FundConvA E I n ρ₀ :=
  fundOfArmsA (fundHasTyArmsA_of hE hI hEN (envSemAt_univ hS) hpi hlam happ hletE)
    (fundConvArmsA_of hE hI hIS hEN hR (envSemAt_univ hS) cbeta czeta capp clam cpi cletE ceta)

end ArmsProved

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.fundOfArmsA
#print axioms Rcic.Declarative.Ann.LRRelA_sort_elim
#print axioms Rcic.Declarative.Ann.ValidSubstA_symm
#print axioms Rcic.Declarative.Ann.convArmIrrA_holds
#print axioms Rcic.Declarative.Ann.convArmIotaA_holds
#print axioms Rcic.Declarative.Ann.convArmStructIotaA_holds
#print axioms Rcic.Declarative.Ann.iotaFn_none_of_head
#print axioms Rcic.Declarative.Ann.iotaFn_none_of_below_typed
#print axioms Rcic.Declarative.Ann.hasTyA_app_fun
#print axioms Rcic.Declarative.Ann.hStepFnA_substA_below
#print axioms Rcic.Declarative.Ann.iotaRel_substA
#print axioms Rcic.Declarative.Ann.fund_of_binderArms
