import rcic.RcicAnnFamClause

/-!
# M2-f (4b) — semantic telescopes: related argument lists are valid substitutions

The families' clause runs the fundamental theorem on parts typed in the base, in the contexts of
the family's parameters and the constructors' plain fields, under the substitutions that the
telescope walks build. This file turns a related argument list along a built telescope
(`ArgsRelKA` along `piTelA ms B w`, the telescope's domains typed in the base) into a VALID pair
of substitutions for the telescope's context at every height above a threshold
(`validSubstA_of_tel`): by induction from the innermost binder, each domain's equality under the
pair from the fundamental theorem on its typing (the `Sort` element relation, `LRRelA_sort_elim`),
each argument's relatedness from the walk at the domain the prefix reaches
(`applyTelA_piTelA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) list and telescope algebra -/

/-- induction from the end of a list. -/
theorem snocInduction {α : Type} {P : List α → Prop} (h0 : P []) (hs : ∀ xs x, P xs → P (xs ++ [x])) :
    ∀ l, P l := by
  have hr : ∀ r : List α, P r.reverse := by
    intro r
    induction r with
    | nil => exact h0
    | cons x r ih => rw [List.reverse_cons]; exact hs _ _ ih
  intro l
  have h := hr l.reverse
  rwa [List.reverse_reverse] at h

theorem consListA_append (xs ys : List ExprA) (τ : SubstA) :
    consListA (xs ++ ys) τ = consListA ys (consListA xs τ) := by
  induction xs generalizing τ with
  | nil => rfl
  | cons x xs ih => exact ih (SubstA.cons x τ)

theorem consListA_snoc (xs : List ExprA) (y : ExprA) (τ : SubstA) :
    consListA (xs ++ [y]) τ = SubstA.cons y (consListA xs τ) := by
  rw [consListA_append]; rfl

theorem telCtxA_snoc (ms : List (ExprA × Level)) (M : ExprA × Level) :
    telCtxA (ms ++ [M]) = LocalDeclA.assumption M.1 :: telCtxA ms := by
  simp only [telCtxA, List.map_append, List.map, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]

section Walk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem argsRelKA_length {k : Nat} {Δ : LCtxA} :
    {T : ExprA} → {xs xs' : List ExprA} → ArgsRelKA E I n ρ₀ k Δ T xs xs' → xs.length = xs'.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ hs => congrArg Nat.succ (argsRelKA_length hs)

/-- a related list splits at a prefix: the prefix is related, and the rest along the telescope
    the prefix reaches. -/
theorem argsRelKA_append_inv {k : Nat} {Δ : LCtxA} :
    {T : ExprA} → {xs xs' ys ys' : List ExprA} → xs.length = xs'.length →
    ArgsRelKA E I n ρ₀ k Δ T (xs ++ ys) (xs' ++ ys') →
    ∃ T', applyTelA xs T = some T' ∧ ArgsRelKA E I n ρ₀ k Δ T xs xs' ∧
      ArgsRelKA E I n ρ₀ k Δ T' ys ys'
  | T, [], [], _, _, _, h => ⟨T, rfl, .nil _, h⟩
  | _, x :: xs, x' :: xs', ys, ys', hl, .cons A u B v _ _ _ _ hr hs => by
      obtain ⟨T', hT', h1, h2⟩ := argsRelKA_append_inv (Nat.succ.inj hl) hs
      exact ⟨T', hT', .cons A u B v x x' xs xs' hr h1, h2⟩
  | _, [], _ :: _, _, _, hl, _ => nomatch hl
  | _, _ :: _, [], _, _, hl, _ => nomatch hl

end Walk

/-! ## (1b) contexts and heights -/

section Ctx
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- a well-formed context, instantiated at a bounded level list of its arity. -/
def ctxWfA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → CtxWfA E I a Γ → CtxWfA E I n (instCtxA ls Γ)
  | _, .nil => .nil
  | _, .assumption hΓ hA =>
      .assumption (ctxWfA_instLevels hEL hIL hls hlen hΓ) (hasTyA_instLevels hEL hIL hls hlen hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (ctxWfA_instLevels hEL hIL hls hlen hΓ) (hasTyA_instLevels hEL hIL hls hlen hA)
        (hasTyA_instLevels hEL hIL hls hlen hv)

/-- a typed telescope's domains form a well-formed context over the outer one, and its body is
    typed there. -/
theorem ctxWfA_telA {a : Nat} (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → {Γ : LCtxA} → CtxWfA E I a Γ → {T : ExprA} →
    HasTyA E I a Γ (piTelA ds B w).1 T →
    Nonempty (CtxWfA E I a (telCtxA ds ++ Γ)) ∧ ∃ T', Nonempty (HasTyA E I a (telCtxA ds ++ Γ) B T')
  | [], Γ, hΓ, T, h => ⟨⟨hΓ⟩, T, ⟨h⟩⟩
  | (D, u) :: ds, Γ, hΓ, T, h => by
      have hpi : HasTyA E I a Γ (.pi D u (piTelA ds B w).1 (piTelA ds B w).2) T := h
      obtain ⟨⟨hD⟩, ⟨hC⟩⟩ := hasTyA_pi_inv hpi
      have ih := ctxWfA_telA B w ds (Γ := .assumption D :: Γ) (.assumption hΓ hD) hC
      have e : telCtxA ((D, u) :: ds) ++ Γ = telCtxA ds ++ (.assumption D :: Γ) := by
        simp only [telCtxA, List.map, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [e]
      exact ih

end Ctx

section Height
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the relation at a type does not depend on the height, once the type is valid at the target
    height (cumulativity, `LR_mono_all`, and `LRTyA_unique`). -/
theorem LRRelA_height {j k : Nat} {Γ : LCtxA} {A a b : ExprA}
    (hj : ∃ R, LRTyA E I n ρ₀ j Γ A R) (h : LRRelA E I n ρ₀ k Γ A a b) : LRRelA E I n ρ₀ j Γ A a b := by
  obtain ⟨Rj, hRj⟩ := hj
  obtain ⟨R, hR, hab⟩ := h
  rcases Nat.le_total j k with hjk | hkj
  · have hRj' := LRTyA_mono hjk hRj
    rw [LRTyA_unique hR hRj'] at hab
    exact ⟨Rj, hRj, hab⟩
  · exact LRRelA_mono hkj ⟨R, hR, hab⟩

end Height

/-! ## (2) the telescope's valid substitution -/

/-- the fundamental theorem on every derivation of the base `E₀`, read in `E`. -/
def BaseFundA (E₀ E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E₀ I n Γ e A → FundArmA E I n ρ₀ Γ e e A

section Valid
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fundamental theorem on every CONVERSION derivation of the base `E₀`, read in `E`. -/
def BaseFundConvA (E₀ E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ {Γ : LCtxA} {e e' A : ExprA}, ConvA E₀ I n Γ e e' A → FundArmA E I n ρ₀ Γ e e' A

/-- both, from the base's clauses (the environment induction's hypothesis at a step). -/
theorem baseFundA_of (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀)
    (hpre : PrefixA E₀ E)
    (ih : EnvSemAt E I n ρ₀ (domA E₀)) : BaseFundA E₀ E I n ρ₀ ∧ BaseFundConvA E₀ E I n ρ₀ :=
  have harms := fundArmsA_at hE hI hIS hEN hNC hR hρ ih
  ⟨fun h => fundHasTyPrefixA hpre harms.1 harms.2 h, fun h => fundConvPrefixA hpre harms.1 harms.2 h⟩

/-- THE FUNDAMENTAL THEOREM ACROSS TWO `=ₙ` LEVEL LISTS on a base derivation: the
    level-irrelevance conversion of its two instantiations is a base derivation
    (`convA_levelIrr_wf` at the base, with the ι head at typed redexes), and its arm relates the
    left instantiation under `σ` to the right one under `σ'`. At one list it is the derivation's
    own arm. -/
theorem fundLevelsA (hfc : BaseFundConvA E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = a) (hl' : ls'.length = a) (heq : eqNList ls ls') {Γ : LCtxA}
    (hΓ : CtxWfA E₀ I a Γ) {e A : ExprA} (h : HasTyA E₀ I a Γ e A) :
    FundArmA E I n ρ₀ (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls' e)
      (instantiateLevelsA ls A) :=
  (convA_levelIrr_wf hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓ h).elim fun c => hfc c

/-- a list splits off its last element. -/
theorem list_eq_dropLast_snoc {α : Type} : (l : List α) → l ≠ [] → ∃ xs x, l = xs ++ [x]
  | [], h => absurd rfl h
  | [x], _ => ⟨[], x, rfl⟩
  | x :: y :: l, _ => by
      obtain ⟨xs, z, e⟩ := list_eq_dropLast_snoc (y :: l) (fun h => List.noConfusion h)
      exact ⟨x :: xs, z, by rw [e]; rfl⟩

/-- RELATED ARGUMENTS ALONG A BASE-TYPED TELESCOPE ARE A VALID SUBSTITUTION, at every height
    above a threshold (the domains' fundamental-theorem thresholds). -/
theorem validSubstA_of_tel (hEN : EnvNormCtorTypeA E) (hfund : BaseFundA E₀ E I n ρ₀) :
    (ms : List (ExprA × Level)) → CtxWfA E₀ I n (telCtxA ms) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKA E I n ρ₀ k Δ (piTelA ms B w).1 as as' →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) := by
  refine snocInduction (P := fun ms => CtxWfA E₀ I n (telCtxA ms) → ∃ k₀, ∀ k, k₀ ≤ k →
      ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKA E I n ρ₀ k Δ (piTelA ms B w).1 as as' →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms))
    ?_ ?_
  · intro _
    refine ⟨0, fun k _ Δ _ B w as as' hlen hrel => ?_⟩
    have hl' := argsRelKA_length hrel
    cases as with
    | cons _ _ => cases hlen
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact ValidSubstA_nil Δ _ _
  · intro ms M ih hwf
    rw [telCtxA_snoc] at hwf
    cases hwf with
    | assumption hΓ hA =>
        obtain ⟨k₀', hk₀'⟩ := ih hΓ
        obtain ⟨k₁, hk₁⟩ := hfund hA
        refine ⟨max k₀' k₁, fun k hk Δ hΔ B w as as' hlen hrel => ?_⟩
        have hl' := argsRelKA_length hrel
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
        obtain ⟨T', hT', h₀, h₁⟩ := argsRelKA_append_inv hl₀ hrel
        have happ := applyTelA_piTelA (piTelA [M] B w).1 (piTelA [M] B w).2 ms as₀ hlen₀ SubstA.id
        rw [substA_id] at happ
        rw [happ] at hT'
        cases hT'
        have hV := hk₀' k (Nat.le_trans (Nat.le_max_left _ _) hk) Δ hΔ _ _ as₀ as₀' hlen₀ h₀
        obtain ⟨_, hD⟩ := hk₁ k (Nat.le_trans (Nat.le_max_right _ _) hk) Δ _ _ hΔ hV
        have heq := (LRRelA_sort_elim hD).1
        obtain ⟨M₁, u⟩ := M
        cases h₁ with
        | cons _ _ _ _ _ _ _ _ ha _ =>
            rw [consListA_snoc, consListA_snoc, telCtxA_snoc]
            exact ValidSubstA_cons hEN hV heq ha


theorem telCtxA_instDomsA (ls : List Level) (ms : List (ExprA × Level)) :
    telCtxA (instDomsA ls ms) = instCtxA ls (telCtxA ms) := by
  simp only [telCtxA, instDomsA, instCtxA, List.map_reverse, List.map_map]
  rfl

theorem instDomsA_snoc (ls : List Level) (ms : List (ExprA × Level)) (M : ExprA × Level) :
    instDomsA ls (ms ++ [M]) = instDomsA ls ms ++ [(instantiateLevelsA ls M.1, instLevel ls M.2)] := by
  simp only [instDomsA, List.map_append, List.map]

/-- THE TELESCOPE'S VALID SUBSTITUTION AT ANOTHER `=ₙ` LEVEL LIST: arguments related along the
    telescope at `ls₀` are a valid pair for the telescope's context at `ls`, each argument
    carried from its `ls₀` domain to its `ls` domain along their equality (`fundLevelsA` at the
    left substitution, `LRRelA_transport'`). -/
theorem validSubstA_of_tel_lv (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀)
    (hIL : IotaLevelsA I) {a : Nat} {ls₀ ls : List Level} (hb₀ : levelsBounded n ls₀ = true)
    (hb : levelsBounded n ls = true) (hl₀ : ls₀.length = a) (hl : ls.length = a)
    (heq : eqNList ls₀ ls) :
    (ms : List (ExprA × Level)) → CtxWfA E₀ I a (telCtxA ms) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKA E I n ρ₀ k Δ (piTelA (instDomsA ls₀ ms) B w).1 as as' →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id)
        (instCtxA ls (telCtxA ms)) := by
  have hrefl : eqNList ls ls := eqNList_refl ls
  refine snocInduction (P := fun ms => CtxWfA E₀ I a (telCtxA ms) → ∃ k₀, ∀ k, k₀ ≤ k →
      ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA), as.length = ms.length →
      ArgsRelKA E I n ρ₀ k Δ (piTelA (instDomsA ls₀ ms) B w).1 as as' →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id)
        (instCtxA ls (telCtxA ms)))
    ?_ ?_
  · intro _
    refine ⟨0, fun k _ Δ _ B w as as' hlen hrel => ?_⟩
    have hl' := argsRelKA_length hrel
    cases as with
    | cons _ _ => cases hlen
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact ValidSubstA_nil Δ _ _
  · intro ms M ih hwf
    have hwf₀ := hwf
    rw [telCtxA_snoc] at hwf
    cases hwf with
    | assumption hΓ hA =>
        obtain ⟨k₁, hk₁⟩ := ih hΓ
        have hΓ₀ : CtxWfA E₀ I n (telCtxA (instDomsA ls₀ ms)) := by
          rw [telCtxA_instDomsA]; exact ctxWfA_instLevels hEL₀ hIL hb₀ hl₀ hΓ
        obtain ⟨k₂, hk₂⟩ := validSubstA_of_tel hEN hfund (instDomsA ls₀ ms) hΓ₀
        obtain ⟨k₃, hk₃⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb₀ hb hl₀ hl heq hΓ hA
        obtain ⟨k₄, hk₄⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl hrefl hΓ hA
        refine ⟨max (max k₁ k₂) (max k₃ k₄), fun k hk Δ hΔ B w as as' hlen hrel => ?_⟩
        have hk1 : k₁ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
        have hk2 : k₂ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
        have hk3 : k₃ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk
        have hk4 : k₄ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk
        have hl' := argsRelKA_length hrel
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
        obtain ⟨T', hT', h₀, h₁⟩ := argsRelKA_append_inv hll₀ hrel
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
        obtain ⟨_, hD₀⟩ := hk₃ k hk3 Δ _ _ hΔ (ValidSubstA_refl_left hEN hV₀)
        have hDeq₀ := (LRRelA_sort_elim hD₀).1
        obtain ⟨_, hD⟩ := hk₄ k hk4 Δ _ _ hΔ hV
        have hDeq := (LRRelA_sort_elim hD).1
        obtain ⟨M₁, u⟩ := M
        cases h₁ with
        | cons _ _ _ _ _ _ _ _ ha _ =>
            have ha' := LRRelA_transport' hEN hDeq₀ ha
            rw [consListA_snoc, consListA_snoc, telCtxA_snoc, instCtxA_cons]
            exact ValidSubstA_cons hEN hV hDeq ha'
end Valid

/-! ## (3) the clause's canonical relations -/

/-- the canonical FIELD relation at a carrier's clause: at constructor `c`'s instantiated type,
    after the prefix `prev` (the parameters, then fields), the relation of the domain reached, at
    height `j`, at the world `ρ`. -/
def famRsA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA) :
    WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ c lsC _ prev a b => ∃ (cm : CheckedMemberA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
    E.members c = some cm ∧ applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC) ∧
    LRRelA E I n ρ₀ j (wkCtxA ρ Γ) D a b

/-- the canonical INDEX relation at a carrier's clause: at the family's instantiated type, after the
    prefix `prev` (the parameters, then indices), the relation of the domain reached. -/
def famRsFA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA)
    (fm : CheckedMemberA) : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun ρ lsF _ prev a b => ∃ (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
    applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some (.pi D uD C vC) ∧
    LRRelA E I n ρ₀ j (wkCtxA ρ Γ) D a b

/-- the canonical INNER relation at a carrier's clause (R-NoFunRec-1 step 1 (1b)): at constructor `c`'s
    instantiated type, after the prefix `prev`, the domain reached is a telescope; after the inner
    prefix `iprev` along it, the relation of the inner domain reached, at height `j`, at the world `σ`. -/
def famRsIA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Γ : LCtxA) :
    InnerRelsA :=
  fun σ c lsC _ prev _ iprev a b => ∃ (cm : CheckedMemberA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
    (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
    E.members c = some cm ∧ applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC) ∧
    applyTelA iprev D = some (.pi D₁ u₁ C₁ v₁) ∧ LRRelA E I n ρ₀ j (wkCtxA σ Γ) D₁ a b

section Canon
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- at a reached domain, the canonical field relation IS the relation there. -/
theorem famRsA_eq {j : Nat} {Γ : LCtxA} {ρ : WkSpecA} {c : Nat} {cm : CheckedMemberA}
    {lsC : List Level} {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level}
    (hm : E.members c = some cm)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC)) :
    famRsA E I n ρ₀ j Γ ρ c lsC i prev = fun a b => LRRelA E I n ρ₀ j (wkCtxA ρ Γ) D a b := by
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

theorem famRsFA_eq {j : Nat} {Γ : LCtxA} {fm : CheckedMemberA} {ρ : WkSpecA} {lsF : List Level}
    {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level}
    (hT : applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some (.pi D uD C vC)) :
    famRsFA E I n ρ₀ j Γ fm ρ lsF i prev = fun a b => LRRelA E I n ρ₀ j (wkCtxA ρ Γ) D a b := by
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
theorem famRsIA_eq {j : Nat} {Γ : LCtxA} {σ : WkSpecA} {c : Nat} {cm : CheckedMemberA}
    {lsC : List Level} {i : Nat} {prev : List ExprA} {ii : Nat} {iprev : List ExprA} {D : ExprA} {uD : Level}
    {C : ExprA} {vC : Level} {D₁ : ExprA} {u₁ : Level} {C₁ : ExprA} {v₁ : Level}
    (hm : E.members c = some cm)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC))
    (hD : applyTelA iprev D = some (.pi D₁ u₁ C₁ v₁)) :
    famRsIA E I n ρ₀ j Γ σ c lsC i prev ii iprev = fun a b => LRRelA E I n ρ₀ j (wkCtxA σ Γ) D₁ a b := by
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
theorem innerRelsA_famRsIA (hE : EnvClosedA E) {j : Nat} {Γ : LCtxA} {ρ ρ' : WkSpecA} {c : Nat}
    {cm : CheckedMemberA} {lsC : List Level} {i : Nat} {prev : List ExprA} {ii : Nat} {zs : List ExprA}
    {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D₁ : ExprA} {u₁ : Level} {C₁ : ExprA} {v₁ : Level}
    (hm : E.members c = some cm)
    (hncl : ∀ k, liftA k 1 (cm.normA.getD cm.mtypeA) = (cm.normA.getD cm.mtypeA))
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC))
    (hD : applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁)) :
    innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC i prev ρ' ii zs =
      fun a b => LRRelA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ a b := by
  have hcl := liftA_instantiateLevelsA_closed hncl lsC
  have hT' : applyTelA (prev.map (wkExprA ρ')) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk_closed ρ' prev hcl, hT, Option.map_some', wkExprA_pi_ub]
  show famRsIA E I n ρ₀ j Γ (WkSpecA.comp ρ ρ') c lsC i (prev.map (wkExprA ρ')) ii zs = _
  rw [famRsIA_eq hm hT' hD, wkCtxA_comp]

/-- the canonical field relation at a weakened context is the canonical one at the composed world
    (R-NoFunRec-1 step 1 (1c-δ)). -/
theorem famRsA_wkCtx (j : Nat) (σ : WkSpecA) (Γ : LCtxA) :
    famRsA E I n ρ₀ j (wkCtxA σ Γ) = fun ρ => famRsA E I n ρ₀ j Γ (WkSpecA.comp σ ρ) := by
  funext ρ c lsC i prev a b
  simp only [famRsA, wkCtxA_comp]

theorem famRsFA_wkCtx (j : Nat) (σ : WkSpecA) (Γ : LCtxA) (fm : CheckedMemberA) :
    famRsFA E I n ρ₀ j (wkCtxA σ Γ) fm = fun ρ => famRsFA E I n ρ₀ j Γ fm (WkSpecA.comp σ ρ) := by
  funext ρ lsF i prev a b
  simp only [famRsFA, wkCtxA_comp]

theorem famRsIA_wkCtx (j : Nat) (σ : WkSpecA) (Γ : LCtxA) :
    famRsIA E I n ρ₀ j (wkCtxA σ Γ) = fun ρ => famRsIA E I n ρ₀ j Γ (WkSpecA.comp σ ρ) := by
  funext ρ c lsC i prev ii iprev a b
  simp only [famRsIA, wkCtxA_comp]

/-- a valid type's validity WITH the relation-at-the-type as its relation (`TyKA_unique`). -/
theorem LRTyA_rel_self {j : Nat} {Γ : LCtxA} {D : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyA E I n ρ₀ j Γ D R) : LRTyA E I n ρ₀ j Γ D (fun a b => LRRelA E I n ρ₀ j Γ D a b) := by
  have e : (fun a b => LRRelA E I n ρ₀ j Γ D a b) = R := by
    funext a b
    apply propext
    constructor
    · rintro ⟨R', hR', hab⟩
      rw [LRTyA_unique hR' h] at hab
      exact hab
    · intro hab
      exact ⟨R, h, hab⟩
  rw [e]
  exact h

end Canon

/-! ## (4) the field walk -/

theorem plainArgsA_instLevels (ls : List Level) :
    (fs : List FieldA) → (as : List ExprA) → plainArgsA (fs.map (FieldA.instLevels ls)) as = plainArgsA fs as
  | [], _ => rfl
  | .plain _ _ :: _, [] => rfl
  | .drec _ :: _, [] => rfl
  | .frec _ _ _ _ :: _, [] => rfl
  | .drecD _ _ :: _, [] => rfl
  | .plain _ _ :: fs, _ :: as => by
      simp only [List.map, FieldA.instLevels, plainArgsA, plainArgsA_instLevels ls fs as]
  | .drec _ :: fs, _ :: as => by
      simp only [List.map, FieldA.instLevels, plainArgsA, plainArgsA_instLevels ls fs as]
  | .frec _ _ _ _ :: fs, _ :: as => by
      simp only [List.map, FieldA.instLevels, plainArgsA, plainArgsA_instLevels ls fs as]
  | .drecD _ _ :: fs, _ :: as => by
      simp only [List.map, FieldA.instLevels, plainArgsA, plainArgsA_instLevels ls fs as]

/-- THE BUILDER AT A PREFIX: applying the first fields' arguments reaches the builder's state after
    them. -/
theorem applyTelA_ctorFieldsA_prefix (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (fsRest : List FieldA) :
    (fsPre : List FieldA) → (as : List ExprA) → as.length = fsPre.length → (pl : List ExprA) →
    (σ : SubstA) →
    applyTelA as (ctorFieldsA f ls w pl σ (fsPre ++ fsRest) res).1 =
      some (ctorFieldsA f ls w pl (consListA (plainArgsA fsPre as) σ) fsRest res).1
  | [], [], _, _, _ => rfl
  | .plain D u :: fs, x :: as, h, pl, σ => by
      simp only [List.cons_append, ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_plain]
      exact applyTelA_ctorFieldsA_prefix f ls w res fsRest fs as (Nat.succ.inj h) pl (SubstA.cons x σ)
  | .drec idx :: fs, x :: as, h, pl, σ => by
      simp only [List.cons_append, ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA_prefix f ls w res fsRest fs as (Nat.succ.inj h) pl σ
  | .frec _ _ _ _ :: fs, x :: as, h, pl, σ => by
      simp only [List.cons_append, ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA_prefix f ls w res fsRest fs as (Nat.succ.inj h) pl σ
  | .drecD _ _ :: fs, x :: as, h, pl, σ => by
      simp only [List.cons_append, ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA_prefix f ls w res fsRest fs as (Nat.succ.inj h) pl σ
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h

section FieldWalk
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the fields' typing after a prefix. -/
def FieldsTyA.drop {a : Nat} {idxTel : Nat → ExprA} {fsRest : List FieldA} {res : List ExprA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res →
    FieldsTyA E₀ I a idxTel (plainCtxA fsPre Γp) (plainIdxA fsPre jc) fsRest res
  | [], _, _, h => h
  | .plain _ _ :: fsPre, _, _, .plain _ _ _ _ _ _ _ tl => FieldsTyA.drop fsPre tl
  | .drec _ :: fsPre, _, _, .drec _ _ _ _ _ _ tl => FieldsTyA.drop fsPre tl
  | .frec _ _ _ _ :: fsPre, _, _, .frec _ _ _ _ _ _ _ _ _ tl => FieldsTyA.drop fsPre tl
  | .drecD _ _ :: fsPre, _, _, .drecD _ _ _ _ _ _ _ tl => FieldsTyA.drop fsPre tl

/-- the plain context after a prefix of typed fields is well formed. -/
def ctxWfA_plainCtx {a : Nat} {idxTel : Nat → ExprA} {fsRest : List FieldA} {res : List ExprA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res → CtxWfA E₀ I a Γp →
    CtxWfA E₀ I a (plainCtxA fsPre Γp)
  | [], _, _, _, hΓ => hΓ
  | .plain _ _ :: fsPre, _, _, .plain _ _ _ _ _ _ hD tl, hΓ => ctxWfA_plainCtx fsPre tl (.assumption hΓ hD)
  | .drec _ :: fsPre, _, _, .drec _ _ _ _ _ _ tl, hΓ => ctxWfA_plainCtx fsPre tl hΓ
  | .frec _ _ _ _ :: fsPre, _, _, .frec _ _ _ _ _ _ _ _ _ tl, hΓ => ctxWfA_plainCtx fsPre tl hΓ
  | .drecD _ _ :: fsPre, _, _, .drecD _ _ _ _ _ _ _ tl, hΓ => ctxWfA_plainCtx fsPre tl hΓ

/-- a walk over no kinds consumes nothing. -/
theorem argsRelA_nil_kinds {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {i : Nat}
    {prev : List ExprA} {T : ExprA} {fs fs' : List ExprA} (h : ArgsRelA R X F i prev T [] fs fs') :
    fs = [] ∧ fs' = [] := by
  cases h
  exact ⟨rfl, rfl⟩

/-- THE FIELD WALK ADVANCES THE PLAIN SUBSTITUTION VALIDLY, at any position relation (R-NoFunRec-1 step 1
    (1c-δ): `fieldWalkA` at the canonical field relation, the function-recursive field's inner walk at
    the relation of the inner domains). Along a built field telescope at `lsC`, a walk with a position
    relation `R` that gives the relation at the domain reached in the type `T0` the walk started from,
    in the context `Δ`, keeps the plain pair `(κ, κ')` valid for the instantiated plain context: at a
    plain field the argument pair is related at the reached domain (carried up to `K`), and the domain's
    equality under the pair is the base derivation's arm (`fundLevelsA`); a recursive field leaves the
    pair and the plain context unchanged. The context reached is `plainCtxA fsPre Γp`. -/
theorem fieldWalkRelA (hfc : BaseFundConvA E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hEN : EnvNormCtorTypeA E)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsC : List Level} (hb : levelsBounded n lsC = true) (hl : lsC.length = a)
    {f : Nat} {s : Level} {pl : List ExprA} {idxTel : Nat → ExprA} {res : List ExprA}
    {j : Nat} {Δ : LCtxA} {T0 : ExprA} {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hR : ∀ (i : Nat) (prev : List ExprA) (x x' D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      applyTelA prev T0 = some (.pi D uD C vC) → R i prev x x' → LRRelA E I n ρ₀ j Δ D x x')
    (hΔ : Nonempty (CtxWfA E I n Δ)) {fsRest : List FieldA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res → CtxWfA E₀ I a Γp →
    ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K → ∀ (κ κ' : SubstA) (i : Nat) (prev pre pre' : List ExprA),
      ValidSubstA E I n ρ₀ K Δ κ κ' (instCtxA lsC Γp) →
      applyTelA prev T0 =
        some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 →
      ArgsRelA R X F i prev
        (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 (fsPre.map FieldA.shape) pre pre' →
      ValidSubstA E I n ρ₀ K Δ (consListA (plainArgsA fsPre pre) κ)
        (consListA (plainArgsA fsPre pre') κ') (instCtxA lsC (plainCtxA fsPre Γp))
  | [], _, _, _, _ => ⟨0, fun K _ _ κ κ' i prev pre pre' hV _ hw => by
      obtain ⟨rfl, rfl⟩ := argsRelA_nil_kinds hw
      exact hV⟩
  | .plain D u :: fsPre, Γp, jc, hF, hΓp => by
      cases hF with
      | plain _ _ _ _ _ _ hD tl =>
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelA (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
            hEL₀ hIL hb hl hR hΔ fsPre tl (.assumption hΓp hD)
          obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl (eqNList_refl lsC) hΓp hD
          refine ⟨max K₁ K₂, fun K hK hjK κ κ' i prev pre pre' hV hT hw => ?_⟩
          simp only [List.cons_append, List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, FieldA.norm] at hT hw
          cases hw with
          | plain _ _ _ _ _ _ x x' _ xs xs' hr htl =>
              have hr' := LRRelA_mono (Nat.le_trans hjK (Nat.le_refl K)) (hR _ _ _ _ _ _ _ _ hT hr)
              obtain ⟨_, hDK⟩ := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ κ κ'
                hΔ hV
              have hDeq := (LRRelA_sort_elim hDK).1
              have hV' : ValidSubstA E I n ρ₀ K Δ (SubstA.cons x κ) (SubstA.cons x' κ')
                  (instCtxA lsC (.assumption D :: Γp)) := ValidSubstA_cons hEN hV hDeq hr'
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
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelA (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
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
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelA (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
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
          obtain ⟨K₁, hK₁⟩ := fieldWalkRelA (f := f) (s := s) (pl := pl) (j := j) (X := X) (F := F) hfc hE₀ hI hEN hR₀
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
theorem fieldWalkA (hfc : BaseFundConvA E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hEN : EnvNormCtorTypeA E)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsC : List Level} (hb : levelsBounded n lsC = true) (hl : lsC.length = a)
    {f : Nat} {s : Level} {pl : List ExprA} {idxTel : Nat → ExprA} {res : List ExprA}
    {j : Nat} {Γ : LCtxA} {ρ : WkSpecA} {c : Nat} {cm : CheckedMemberA} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} (hm : E.members c = some cm) (hΔ : Nonempty (CtxWfA E I n (wkCtxA ρ Γ))) {fsRest : List FieldA} :
    (fsPre : List FieldA) → {Γp : LCtxA} → {jc : Nat} →
    FieldsTyA E₀ I a idxTel Γp jc (fsPre ++ fsRest) res → CtxWfA E₀ I a Γp →
    ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K → ∀ (κ κ' : SubstA) (i : Nat) (prev pre pre' : List ExprA),
      ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) κ κ' (instCtxA lsC Γp) →
      applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
        some (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F i prev
        (ctorFieldsA f lsC s pl κ (((fsPre ++ fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
          (res.map (instantiateLevelsA lsC))).1 (fsPre.map FieldA.shape) pre pre' →
      ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) (consListA (plainArgsA fsPre pre) κ)
        (consListA (plainArgsA fsPre pre') κ') (instCtxA lsC (plainCtxA fsPre Γp)) :=
  fun fsPre _ _ hF hΓp =>
    fieldWalkRelA hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hl
      (R := famRsA E I n ρ₀ j Γ ρ c lsC) (T0 := instantiateLevelsA lsC (cm.normA.getD cm.mtypeA))
      (fun _ _ _ _ _ _ _ _ hT hr => by rw [famRsA_eq hm hT] at hr; exact hr) hΔ fsPre hF hΓp

end FieldWalk

#print axioms ctxWfA_telA
#print axioms LRRelA_height
#print axioms validSubstA_of_tel
#print axioms baseFundA_of
#print axioms fundLevelsA
#print axioms validSubstA_of_tel_lv
#print axioms famRsA_eq
#print axioms famRsFA_eq
#print axioms famRsIA_eq
#print axioms innerRelsA_famRsIA
#print axioms famRsA_wkCtx
#print axioms famRsFA_wkCtx
#print axioms famRsIA_wkCtx
#print axioms LRTyA_rel_self
#print axioms applyTelA_ctorFieldsA_prefix
#print axioms fieldWalkRelA
#print axioms fieldWalkA

end Rcic.Declarative.Ann
