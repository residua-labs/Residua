import rcic.RcicAnnSemTel
import rcic.RcicAnnLREnvG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnLRRowsG
/-!
# M2-f (4b) — semantic telescopes: related argument lists are valid substitutions

The families' clause runs the fundamental theorem on parts typed in the base, in the contexts of
the family's parameters and the constructors' plain fields, under the substitutions that the
telescope walks build. This file turns a related argument list along a built telescope
(`ArgsRelKAg` along `piTelA ms B w`, the telescope's domains typed in the base) into a VALID pair
of substitutions for the telescope's context at every height above a threshold
(`validSubstA_of_telg`): by induction from the innermost binder, each domain's equality under the
pair from the fundamental theorem on its typing (the `Sort` element relation, `LRRelA_sort_elimg`),
each argument's relatedness from the walk at the domain the prefix reaches
(`applyTelA_piTelA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) list and telescope algebra -/

section Walk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem argsRelKA_lengthg {k : Nat} {Δ : LCtxA} :
    {T : ExprA} → {xs xs' : List ExprA} → ArgsRelKAg E I n ρ₀ k Δ T xs xs' → xs.length = xs'.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ hs => congrArg Nat.succ (argsRelKA_lengthg hs)

/-- a related list splits at a prefix: the prefix is related, and the rest along the telescope
    the prefix reaches. -/
theorem argsRelKA_append_invg {k : Nat} {Δ : LCtxA} :
    {T : ExprA} → {xs xs' ys ys' : List ExprA} → xs.length = xs'.length →
    ArgsRelKAg E I n ρ₀ k Δ T (xs ++ ys) (xs' ++ ys') →
    ∃ T', applyTelA xs T = some T' ∧ ArgsRelKAg E I n ρ₀ k Δ T xs xs' ∧
      ArgsRelKAg E I n ρ₀ k Δ T' ys ys'
  | T, [], [], _, _, _, h => ⟨T, rfl, .nil _, h⟩
  | _, x :: xs, x' :: xs', ys, ys', hl, .cons A u B v _ _ _ _ hr hs => by
      obtain ⟨T', hT', h1, h2⟩ := argsRelKA_append_invg (Nat.succ.inj hl) hs
      exact ⟨T', hT', .cons A u B v x x' xs xs' hr h1, h2⟩
  | _, [], _ :: _, _, _, hl, _ => nomatch hl
  | _, _ :: _, [], _, _, hl, _ => nomatch hl

end Walk

/-! ## (1b) contexts and heights -/

section Ctx
variable {E : ResolvedEnvA} {I : IotaIfaceA}

end Ctx

section Height
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the relation at a type does not depend on the height, once the type is valid at the target
    height (cumulativity, `LR_mono_allg`, and `LRTyA_uniqueg`). -/
theorem LRRelA_heightg {j k : Nat} {Γ : LCtxA} {A a b : ExprA}
    (hj : ∃ R, LRTyAg E I n ρ₀ j Γ A R) (h : LRRelAg E I n ρ₀ k Γ A a b) : LRRelAg E I n ρ₀ j Γ A a b := by
  obtain ⟨Rj, hRj⟩ := hj
  obtain ⟨R, hR, hab⟩ := h
  rcases Nat.le_total j k with hjk | hkj
  · have hRj' := LRTyA_monog hjk hRj
    rw [LRTyA_uniqueg hR hRj'] at hab
    exact ⟨Rj, hRj, hab⟩
  · exact LRRelA_monog hkj ⟨R, hR, hab⟩

end Height

/-! ## (2) the telescope's valid substitution -/

/-- the fundamental theorem on every derivation of the base `E₀`, read in `E`. -/
def BaseFundAg (E₀ E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E₀ I n Γ e A → FundArmAg E I n ρ₀ Γ e e A

section Valid
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fundamental theorem on every CONVERSION derivation of the base `E₀`, read in `E`. -/
def BaseFundConvAg (E₀ E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e e' A : ExprA}, ConvA E₀ I n Γ e e' A → FundArmAg E I n ρ₀ Γ e e' A

/-- both, from the base's clauses (the environment induction's hypothesis at a step). -/
theorem baseFundA_ofg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    (hpre : PrefixA E₀ E)
    (ih : EnvSemAtg E I n ρ₀ (domA E₀)) : BaseFundAg E₀ E I n ρ₀ ∧ BaseFundConvAg E₀ E I n ρ₀ :=
  have harms := fundArmsA_atg hE hI hIS hEN hNC hR hρ hK ih
  ⟨fun h => fundHasTyPrefixAg hpre harms.1 harms.2 h, fun h => fundConvPrefixAg hpre harms.1 harms.2 h⟩

/-- THE FUNDAMENTAL THEOREM ACROSS TWO `=ₙ` LEVEL LISTS on a base derivation: the
    level-irrelevance conversion of its two instantiations is a base derivation
    (`convA_levelIrr_wf` at the base, with the ι head at typed redexes), and its arm relates the
    left instantiation under `σ` to the right one under `σ'`. At one list it is the derivation's
    own arm. -/
theorem fundLevelsAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = a) (hl' : ls'.length = a) (heq : eqNList ls ls') {Γ : LCtxA}
    (hΓ : CtxWfA E₀ I a Γ) {e A : ExprA} (h : HasTyA E₀ I a Γ e A) :
    FundArmAg E I n ρ₀ (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls' e)
      (instantiateLevelsA ls A) :=
  (convA_levelIrr_wf hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓ h).elim fun c => hfc c

/-- RELATED ARGUMENTS ALONG A BASE-TYPED TELESCOPE ARE A VALID SUBSTITUTION, at every height
    above a threshold (the domains' fundamental-theorem thresholds). -/
theorem validSubstA_of_telg (hEN : EnvNormCtorTypeA E) (hfund : BaseFundAg E₀ E I n ρ₀) :
    (ms : List (ExprA × Level)) → CtxWfA E₀ I n (telCtxA ms) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKAg E I n ρ₀ k Δ (piTelA ms B w).1 as as' →
      ValidSubstAg E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) := by
  refine snocInduction (P := fun ms => CtxWfA E₀ I n (telCtxA ms) → ∃ k₀, ∀ k, k₀ ≤ k →
      ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKAg E I n ρ₀ k Δ (piTelA ms B w).1 as as' →
      ValidSubstAg E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms))
    ?_ ?_
  · intro _
    refine ⟨0, fun k _ Δ _ B w as as' hlen hrel => ?_⟩
    have hl' := argsRelKA_lengthg hrel
    cases as with
    | cons _ _ => cases hlen
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact ValidSubstA_nilg Δ _ _
  · intro ms M ih hwf
    rw [telCtxA_snoc] at hwf
    cases hwf with
    | assumption hΓ hA =>
        obtain ⟨k₀', hk₀'⟩ := ih hΓ
        obtain ⟨k₁, hk₁⟩ := hfund hA
        refine ⟨max k₀' k₁, fun k hk Δ hΔ B w as as' hlen hrel => ?_⟩
        have hl' := argsRelKA_lengthg hrel
        rw [List.length_append, List.length_singleton] at hlen
        have hne : as ≠ [] := fun h => by
          subst h
          exact absurd hlen (Nat.succ_ne_zero _).symm
        have hne' : as' ≠ [] := fun h => by
          subst h
          rw [hl'] at hlen
          exact absurd hlen (Nat.succ_ne_zero _).symm
        obtain ⟨as₀, a, rfl⟩ := list_eq_dropLast_snoc as hne
        obtain ⟨as₀', a', rfl⟩ := list_eq_dropLast_snoc as' hne'
        rw [List.length_append, List.length_singleton] at hlen
        have hlen₀ : as₀.length = ms.length := Nat.succ.inj hlen
        rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton] at hl'
        have hl₀ : as₀.length = as₀'.length := Nat.succ.inj hl'
        rw [piTelA_append] at hrel
        obtain ⟨T', hT', h₀, h₁⟩ := argsRelKA_append_invg hl₀ hrel
        have happ := applyTelA_piTelA (piTelA [M] B w).1 (piTelA [M] B w).2 ms as₀ hlen₀ SubstA.id
        rw [substA_id] at happ
        rw [happ] at hT'
        cases hT'
        have hV := hk₀' k (Nat.le_trans (Nat.le_max_left _ _) hk) Δ hΔ _ _ as₀ as₀' hlen₀ h₀
        obtain ⟨_, hD⟩ := hk₁ k (Nat.le_trans (Nat.le_max_right _ _) hk) Δ _ _ hΔ hV
        have heq := (LRRelA_sort_elimg hD).1
        obtain ⟨M₁, u⟩ := M
        cases h₁ with
        | cons _ _ _ _ _ _ _ _ ha _ =>
            rw [consListA_snoc, consListA_snoc, telCtxA_snoc]
            exact ValidSubstA_consg hEN hV heq ha

/-- THE TELESCOPE'S VALID SUBSTITUTION AT ANOTHER `=ₙ` LEVEL LIST: arguments related along the
    telescope at `ls₀` are a valid pair for the telescope's context at `ls`, each argument
    carried from its `ls₀` domain to its `ls` domain along their equality (`fundLevelsAg` at the
    left substitution, `LRRelA_transport'g`). -/
theorem validSubstA_of_tel_lvg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀)
    (hIL : IotaLevelsA I) {a : Nat} {ls₀ ls : List Level} (hb₀ : levelsBounded n ls₀ = true)
    (hb : levelsBounded n ls = true) (hl₀ : ls₀.length = a) (hl : ls.length = a)
    (heq : eqNList ls₀ ls) :
    (ms : List (ExprA × Level)) → CtxWfA E₀ I a (telCtxA ms) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKAg E I n ρ₀ k Δ (piTelA (instDomsA ls₀ ms) B w).1 as as' →
      ValidSubstAg E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id)
        (instCtxA ls (telCtxA ms)) := by
  have hrefl : eqNList ls ls := eqNList_refl ls
  refine snocInduction (P := fun ms => CtxWfA E₀ I a (telCtxA ms) → ∃ k₀, ∀ k, k₀ ≤ k →
      ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKAg E I n ρ₀ k Δ (piTelA (instDomsA ls₀ ms) B w).1 as as' →
      ValidSubstAg E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id)
        (instCtxA ls (telCtxA ms)))
    ?_ ?_
  · intro _
    refine ⟨0, fun k _ Δ _ B w as as' hlen hrel => ?_⟩
    have hl' := argsRelKA_lengthg hrel
    cases as with
    | cons _ _ => cases hlen
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact ValidSubstA_nilg Δ _ _
  · intro ms M ih hwf
    have hwf₀ := hwf
    rw [telCtxA_snoc] at hwf
    cases hwf with
    | assumption hΓ hA =>
        obtain ⟨k₁, hk₁⟩ := ih hΓ
        have hΓ₀ : CtxWfA E₀ I n (telCtxA (instDomsA ls₀ ms)) := by
          rw [telCtxA_instDomsA]; exact ctxWfA_instLevels hEL₀ hIL hb₀ hl₀ hΓ
        obtain ⟨k₂, hk₂⟩ := validSubstA_of_telg hEN hfund (instDomsA ls₀ ms) hΓ₀
        obtain ⟨k₃, hk₃⟩ := fundLevelsAg hfc hE₀ hI hR₀ hEL₀ hIL hb₀ hb hl₀ hl heq hΓ hA
        obtain ⟨k₄, hk₄⟩ := fundLevelsAg hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl hrefl hΓ hA
        refine ⟨max (max k₁ k₂) (max k₃ k₄), fun k hk Δ hΔ B w as as' hlen hrel => ?_⟩
        have hk1 : k₁ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
        have hk2 : k₂ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
        have hk3 : k₃ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk
        have hk4 : k₄ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk
        have hl' := argsRelKA_lengthg hrel
        rw [List.length_append, List.length_singleton] at hlen
        have hne : as ≠ [] := fun h => by
          subst h
          exact absurd hlen (Nat.succ_ne_zero _).symm
        have hne' : as' ≠ [] := fun h => by
          subst h
          rw [hl'] at hlen
          exact absurd hlen (Nat.succ_ne_zero _).symm
        obtain ⟨as₀, x, rfl⟩ := list_eq_dropLast_snoc as hne
        obtain ⟨as₀', x', rfl⟩ := list_eq_dropLast_snoc as' hne'
        rw [List.length_append, List.length_singleton] at hlen
        have hlen₀ : as₀.length = ms.length := Nat.succ.inj hlen
        rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton] at hl'
        have hll₀ : as₀.length = as₀'.length := Nat.succ.inj hl'
        rw [instDomsA_snoc, piTelA_append] at hrel
        obtain ⟨T', hT', h₀, h₁⟩ := argsRelKA_append_invg hll₀ hrel
        have hlenI : as₀.length = (instDomsA ls₀ ms).length := by
          rw [hlen₀]; simp [instDomsA]
        have happ := applyTelA_piTelA
          (piTelA [(instantiateLevelsA ls₀ M.1, instLevel ls₀ M.2)] B w).1
          (piTelA [(instantiateLevelsA ls₀ M.1, instLevel ls₀ M.2)] B w).2
          (instDomsA ls₀ ms) as₀ hlenI SubstA.id
        rw [substA_id] at happ
        rw [happ] at hT'
        cases hT'
        have hV₀ := hk₂ k hk2 Δ hΔ _ _ as₀ as₀' hlenI h₀
        rw [telCtxA_instDomsA] at hV₀
        have hV := hk₁ k hk1 Δ hΔ _ _ as₀ as₀' hlen₀ h₀
        obtain ⟨_, hD₀⟩ := hk₃ k hk3 Δ _ _ hΔ (ValidSubstA_refl_leftg hEN hV₀)
        have hDeq₀ := (LRRelA_sort_elimg hD₀).1
        obtain ⟨_, hD⟩ := hk₄ k hk4 Δ _ _ hΔ hV
        have hDeq := (LRRelA_sort_elimg hD).1
        obtain ⟨M₁, u⟩ := M
        cases h₁ with
        | cons _ _ _ _ _ _ _ _ ha _ =>
            have ha' := LRRelA_transport'g hEN hDeq₀ ha
            rw [consListA_snoc, consListA_snoc, telCtxA_snoc, instCtxA_cons]
            exact ValidSubstA_consg hEN hV hDeq ha'
end Valid

/-! ## (3) the clause's canonical relations -/

/-- the canonical FIELD relation at a carrier's clause: at constructor `c`'s instantiated type,
    after the prefix `prev` (the parameters, then fields), the relation of the domain reached, at
    height `j`, at the world `ρ`. -/
def famRsAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA) :
    WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ c lsC _ prev a b => ∃ (cm : CheckedMemberA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
    E.members c = some cm ∧ applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC) ∧
    LRRelAg E I n ρ₀ j (wkCtxA ρ Γ) D a b

/-- the canonical INDEX relation at a carrier's clause: at the family's instantiated type, after the
    prefix `prev` (the parameters, then indices), the relation of the domain reached. -/
def famRsFAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA)
    (fm : CheckedMemberA) : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ lsF _ prev a b => ∃ (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
    applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some (.pi D uD C vC) ∧
    LRRelAg E I n ρ₀ j (wkCtxA ρ Γ) D a b

/-- the canonical INNER relation at a carrier's clause (R-NoFunRec-1 step 1 (1b)): at constructor `c`'s
    instantiated type, after the prefix `prev`, the domain reached is a telescope; after the inner
    prefix `iprev` along it, the relation of the inner domain reached, at height `j`, at the world `σ`. -/
def famRsIAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA) :
    InnerRelsA :=
  fun σ c lsC _ prev _ iprev a b => ∃ (cm : CheckedMemberA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
    (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
    E.members c = some cm ∧ applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC) ∧
    applyTelA iprev D = some (.pi D₁ u₁ C₁ v₁) ∧ LRRelAg E I n ρ₀ j (wkCtxA σ Γ) D₁ a b

section Canon
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- at a reached domain, the canonical field relation IS the relation there. -/
theorem famRsA_eqg {j : Nat} {Γ : LCtxA} {ρ : WkSpecA} {c : Nat} {cm : CheckedMemberA}
    {lsC : List Level} {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level}
    (hm : E.members c = some cm)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC)) :
    famRsAg E I n ρ₀ j Γ ρ c lsC i prev = fun a b => LRRelAg E I n ρ₀ j (wkCtxA ρ Γ) D a b := by
  funext a b
  apply propext
  constructor
  · rintro ⟨cm', D', uD', C', vC', hm', hT', hr⟩
    rw [hm] at hm'
    cases hm'
    rw [hT] at hT'
    cases hT'
    exact hr
  · intro hr
    exact ⟨cm, D, uD, C, vC, hm, hT, hr⟩

theorem famRsFA_eqg {j : Nat} {Γ : LCtxA} {fm : CheckedMemberA} {ρ : WkSpecA} {lsF : List Level}
    {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level}
    (hT : applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some (.pi D uD C vC)) :
    famRsFAg E I n ρ₀ j Γ fm ρ lsF i prev = fun a b => LRRelAg E I n ρ₀ j (wkCtxA ρ Γ) D a b := by
  funext a b
  apply propext
  constructor
  · rintro ⟨D', uD', C', vC', hT', hr⟩
    rw [hT] at hT'
    cases hT'
    exact hr
  · intro hr
    exact ⟨D, uD, C, vC, hT, hr⟩

/-- at a reached inner domain, the canonical inner relation IS the relation there. -/
theorem famRsIA_eqg {j : Nat} {Γ : LCtxA} {σ : WkSpecA} {c : Nat} {cm : CheckedMemberA}
    {lsC : List Level} {i : Nat} {prev : List ExprA} {ii : Nat} {iprev : List ExprA} {D : ExprA} {uD : Level}
    {C : ExprA} {vC : Level} {D₁ : ExprA} {u₁ : Level} {C₁ : ExprA} {v₁ : Level}
    (hm : E.members c = some cm)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC))
    (hD : applyTelA iprev D = some (.pi D₁ u₁ C₁ v₁)) :
    famRsIAg E I n ρ₀ j Γ σ c lsC i prev ii iprev = fun a b => LRRelAg E I n ρ₀ j (wkCtxA σ Γ) D₁ a b := by
  funext a b
  apply propext
  constructor
  · rintro ⟨cm', D', uD', C', vC', D₁', u₁', C₁', v₁', hm', hT', hD', hr⟩
    rw [hm] at hm'
    cases hm'
    rw [hT] at hT'
    cases hT'
    rw [hD] at hD'
    cases hD'
    exact hr
  · intro hr
    exact ⟨cm, D, uD, C, vC, D₁, u₁, C₁, v₁, hm, hT, hD, hr⟩

/-- the canonical inner relations as a walk at world `ρ` reads them at an extension `ρ'` (the field
    prefix weakened there, `innerRelsA`): the constructor's type is closed, so the field domain reached
    is the weakened one, and the relation is the inner domain's at the extended world. -/
theorem innerRelsA_famRsIAg (hE : EnvClosedA E) {j : Nat} {Γ : LCtxA} {ρ ρ' : WkSpecA} {c : Nat}
    {cm : CheckedMemberA} {lsC : List Level} {i : Nat} {prev : List ExprA} {ii : Nat} {zs : List ExprA}
    {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D₁ : ExprA} {u₁ : Level} {C₁ : ExprA} {v₁ : Level}
    (hm : E.members c = some cm)
    (hncl : ∀ k, liftA k 1 (cm.normA.getD cm.mtypeA) = (cm.normA.getD cm.mtypeA))
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC))
    (hD : applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁)) :
    innerRelsA (famRsIAg E I n ρ₀ j Γ) ρ c lsC i prev ρ' ii zs =
      fun a b => LRRelAg E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ a b := by
  have hcl := liftA_instantiateLevelsA_closed hncl lsC
  have hT' : applyTelA (prev.map (wkExprA ρ')) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk_closed ρ' prev hcl, hT, Option.map_some', wkExprA_pi_ub]
  show famRsIAg E I n ρ₀ j Γ (WkSpecA.comp ρ ρ') c lsC i (prev.map (wkExprA ρ')) ii zs = _
  rw [famRsIA_eqg hm hT' hD, wkCtxA_comp]

/-- the canonical field relation at a weakened context is the canonical one at the composed world
    (R-NoFunRec-1 step 1 (1c-δ)). -/
theorem famRsA_wkCtxg (j : Nat) (σ : WkSpecA) (Γ : LCtxA) :
    famRsAg E I n ρ₀ j (wkCtxA σ Γ) = fun ρ => famRsAg E I n ρ₀ j Γ (WkSpecA.comp σ ρ) := by
  funext ρ c lsC i prev a b
  simp only [famRsAg, wkCtxA_comp]

theorem famRsFA_wkCtxg (j : Nat) (σ : WkSpecA) (Γ : LCtxA) (fm : CheckedMemberA) :
    famRsFAg E I n ρ₀ j (wkCtxA σ Γ) fm = fun ρ => famRsFAg E I n ρ₀ j Γ fm (WkSpecA.comp σ ρ) := by
  funext ρ lsF i prev a b
  simp only [famRsFAg, wkCtxA_comp]

theorem famRsIA_wkCtxg (j : Nat) (σ : WkSpecA) (Γ : LCtxA) :
    famRsIAg E I n ρ₀ j (wkCtxA σ Γ) = fun ρ => famRsIAg E I n ρ₀ j Γ (WkSpecA.comp σ ρ) := by
  funext ρ c lsC i prev ii iprev a b
  simp only [famRsIAg, wkCtxA_comp]

/-- a valid type's validity WITH the relation-at-the-type as its relation (`TyKA_uniqueg`). -/
theorem LRTyA_rel_selfg {j : Nat} {Γ : LCtxA} {D : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ j Γ D R) : LRTyAg E I n ρ₀ j Γ D (fun a b => LRRelAg E I n ρ₀ j Γ D a b) := by
  have e : (fun a b => LRRelAg E I n ρ₀ j Γ D a b) = R := by
    funext a b
    apply propext
    constructor
    · rintro ⟨R', hR', hab⟩
      rw [LRTyA_uniqueg hR' h] at hab
      exact hab
    · intro hab
      exact ⟨R, h, hab⟩
  rw [e]
  exact h

end Canon

/-! ## (4) the field walk -/

section FieldWalk
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE FIELD WALK ADVANCES THE PLAIN SUBSTITUTION VALIDLY, at any position relation (R-NoFunRec-1 step 1
    (1c-δ): `fieldWalkAg` at the canonical field relation, the function-recursive field's inner walk at
    the relation of the inner domains). Along a built field telescope at `lsC`, a walk with a position
    relation `R` that gives the relation at the domain reached in the type `T0` the walk started from,
    in the context `Δ`, keeps the plain pair `(κ, κ')` valid for the instantiated plain context: at a
    plain field the argument pair is related at the reached domain (carried up to `K`), and the domain's
    equality under the pair is the base derivation's arm (`fundLevelsAg`); a recursive field leaves the
    pair and the plain context unchanged. The context reached is `plainCtxA fsPre Γp`. -/
theorem fieldWalkRelAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hEN : EnvNormCtorTypeA E)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsC : List Level} (hb : levelsBounded n lsC = true) (hl : lsC.length = a)
    {f : Nat} {s : Level} {pl : List ExprA} {idxTel : Nat → ExprA} {res : List ExprA}
    {j : Nat} {Δ : LCtxA} {T0 : ExprA} {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hR : ∀ (i : Nat) (prev : List ExprA) (x x' D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      applyTelA prev T0 = some (.pi D uD C vC) → R i prev x x' → LRRelAg E I n ρ₀ j Δ D x x')
    (hΔ : Nonempty (CtxWfA E I n Δ)) {fsRest : List FieldA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res → CtxWfA E₀ I a Γp →
    ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K → ∀ (κ κ' : SubstA) (i : Nat) (prev pre pre' : List ExprA),
      ValidSubstAg E I n ρ₀ K Δ κ κ' (instCtxA lsC Γp) →
      applyTelA prev T0 =
        some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 →
      ArgsRelA R X F i prev
        (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 (fsPre.map FieldA.shape) pre pre' →
      ValidSubstAg E I n ρ₀ K Δ (consListA (plainArgsA fsPre pre) κ)
        (consListA (plainArgsA fsPre pre') κ') (instCtxA lsC (plainCtxA fsPre Γp))
  | [], _, _, _, _ => ⟨0, fun K _ _ κ κ' i prev pre pre' hV _ hw => by
      obtain ⟨rfl, rfl⟩ := argsRelA_nil_kinds hw
      exact hV⟩
  | .plain D u :: fsPre, Γp, jc, hF, hΓp => by
      cases hF with
      | plain _ _ _ _ _ _ hD tl =>
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelAg (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
            hEL₀ hIL hb hl hR hΔ fsPre tl (.assumption hΓp hD)
          obtain ⟨K₂, hK₂⟩ := fundLevelsAg hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl (eqNList_refl lsC) hΓp hD
          refine ⟨max K₁ K₂, fun K hK hjK κ κ' i prev pre pre' hV hT hw => ?_⟩
          simp only [List.cons_append, List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, FieldA.norm] at hT hw
          cases hw with
          | plain _ _ _ _ _ _ x x' _ xs xs' hr htl =>
              have hr' := LRRelA_monog (Nat.le_trans hjK (Nat.le_refl K)) (hR _ _ _ _ _ _ _ _ hT hr)
              obtain ⟨_, hDK⟩ := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ κ κ'
                hΔ hV
              have hDeq := (LRRelA_sort_elimg hDK).1
              have hV' : ValidSubstAg E I n ρ₀ K Δ (SubstA.cons x κ) (SubstA.cons x' κ')
                  (instCtxA lsC (.assumption D :: Γp)) := ValidSubstA_consg hEN hV hDeq hr'
              have hT' : applyTelA (prev ++ [x]) T0 =
                  some (ctorFieldsA f lsC s pl (SubstA.cons x κ) (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
                    (res.map (instantiateLevelsA lsC))).1 := by
                rw [applyTelA_append, hT]
                simp only [applyTelA, Option.bind]
                rw [instantiate0A_ctorFieldsA_plain]
                rfl
              rw [instantiate0A_ctorFieldsA_plain] at htl
              exact hK₁ K (Nat.le_trans (Nat.le_max_left _ _) hK) hjK
                (SubstA.cons x κ) (SubstA.cons x' κ') (i + 1) (prev ++ [x]) xs xs' hV' hT' htl
  | .drec idx :: fsPre, Γp, jc, hF, hΓp => by
      cases hF with
      | drec _ _ _ _ _ _ tl =>
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelAg (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
            hEL₀ hIL hb hl hR hΔ fsPre tl hΓp
          refine ⟨K₁, fun K hK hjK κ κ' i prev pre pre' hV hT hw => ?_⟩
          simp only [List.cons_append, List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, FieldA.norm] at hT hw
          cases hw with
          | directRec _ _ _ _ _ _ x x' _ xs xs' _ htl =>
              have hT' : applyTelA (prev ++ [x]) T0 =
                  some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
                    (res.map (instantiateLevelsA lsC))).1 := by
                rw [applyTelA_append, hT]
                simp only [applyTelA, Option.bind]
                rw [instantiate0A_ctorFieldsA_drec]
                rfl
              rw [instantiate0A_ctorFieldsA_drec] at htl
              exact hK₁ K hK hjK κ κ' (i + 1) (prev ++ [x]) xs xs' hV hT' htl
  | .drecD D idx :: fsPre, Γp, jc, hF, hΓp => by
      cases hF with
      | drecD _ _ _ _ _ _ _ tl =>
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelAg (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
            hEL₀ hIL hb hl hR hΔ fsPre tl hΓp
          refine ⟨K₁, fun K hK hjK κ κ' i prev pre pre' hV hT hw => ?_⟩
          simp only [List.cons_append, List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, FieldA.norm] at hT hw
          cases hw with
          | directRec _ _ _ _ _ _ x x' _ xs xs' _ htl =>
              have hT' : applyTelA (prev ++ [x]) T0 =
                  some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
                    (res.map (instantiateLevelsA lsC))).1 := by
                rw [applyTelA_append, hT]
                simp only [applyTelA, Option.bind]
                rw [instantiate0A_ctorFieldsA_drec]
                rfl
              rw [instantiate0A_ctorFieldsA_drec] at htl
              exact hK₁ K hK hjK κ κ' (i + 1) (prev ++ [x]) xs xs' hV hT' htl
  | .frec B uB Bs idx :: fsPre, Γp, jc, hF, hΓp => by
      cases hF with
      | frec _ _ _ _ _ _ _ _ _ tl =>
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelAg (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
            hEL₀ hIL hb hl hR hΔ fsPre tl hΓp
          refine ⟨K₁, fun K hK hjK κ κ' i prev pre pre' hV hT hw => ?_⟩
          simp only [List.cons_append, List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, FieldA.norm] at hT hw
          cases hw with
          | funRec _ _ _ _ _ _ x x' _ _ xs xs' _ htl =>
              have hT' : applyTelA (prev ++ [x]) T0 =
                  some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
                    (res.map (instantiateLevelsA lsC))).1 := by
                rw [applyTelA_append, hT]
                simp only [applyTelA, Option.bind]
                rw [instantiate0A_ctorFieldsA_drec]
                rfl
              rw [instantiate0A_ctorFieldsA_drec] at htl
              exact hK₁ K hK hjK κ κ' (i + 1) (prev ++ [x]) xs xs' hV hT' htl

/-- the field walk at the canonical field relation. -/
theorem fieldWalkAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hEN : EnvNormCtorTypeA E)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsC : List Level} (hb : levelsBounded n lsC = true) (hl : lsC.length = a)
    {f : Nat} {s : Level} {pl : List ExprA} {idxTel : Nat → ExprA} {res : List ExprA}
    {j : Nat} {Γ : LCtxA} {ρ : WkSpecA} {c : Nat} {cm : CheckedMemberA} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} (hm : E.members c = some cm) (hΔ : Nonempty (CtxWfA E I n (wkCtxA ρ Γ))) {fsRest : List FieldA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res → CtxWfA E₀ I a Γp →
    ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K → ∀ (κ κ' : SubstA) (i : Nat) (prev pre pre' : List ExprA),
      ValidSubstAg E I n ρ₀ K (wkCtxA ρ Γ) κ κ' (instCtxA lsC Γp) →
      applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
        some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 →
      ArgsRelA (famRsAg E I n ρ₀ j Γ ρ c lsC) X F i prev
        (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 (fsPre.map FieldA.shape) pre pre' →
      ValidSubstAg E I n ρ₀ K (wkCtxA ρ Γ) (consListA (plainArgsA fsPre pre) κ)
        (consListA (plainArgsA fsPre pre') κ') (instCtxA lsC (plainCtxA fsPre Γp)) :=
  fun fsPre _ _ hF hΓp =>
    fieldWalkRelAg hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hl
      (R := famRsAg E I n ρ₀ j Γ ρ c lsC) (T0 := instantiateLevelsA lsC (cm.normA.getD cm.mtypeA))
      (fun _ _ _ _ _ _ _ _ hT hr => by rw [famRsA_eqg hm hT] at hr; exact hr) hΔ fsPre hF hΓp

end FieldWalk

#print axioms LRRelA_heightg
#print axioms validSubstA_of_telg
#print axioms baseFundA_ofg
#print axioms fundLevelsAg
#print axioms validSubstA_of_tel_lvg
#print axioms famRsA_eqg
#print axioms famRsFA_eqg
#print axioms famRsIA_eqg
#print axioms innerRelsA_famRsIAg
#print axioms famRsA_wkCtxg
#print axioms famRsFA_wkCtxg
#print axioms famRsIA_wkCtxg
#print axioms LRTyA_rel_selfg
#print axioms fieldWalkRelAg
#print axioms fieldWalkAg

end Rcic.Declarative.Ann
