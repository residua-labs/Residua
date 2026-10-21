/- W-0/S-0: the guarded LR cone keeps the same large-index boundary as the
   unguarded one (`RcicAnnFamHeight` (1)). `tyKAg_famApp_firstIndexSort_lt` and
   `LRRelAg_famApp_firstIndexSort_refuted` ported to `TyKAg`/`LRRelAg`, then the
   `pinFamF0` fixture refutation of `EnvSemAg`/`EnvSemIndAg` — the guarded cone's
   own semantic environment FAILS at the same fixture, by a direct proof (member
   clause + `LRRelA_pi_elimg`), with no `fundAg` and no `PropKeyA`: the boundary
   is a relation-shape fact, not a fundamental-theorem gap, and
   `SmallIndexProfileA` is a necessary premise of `EnvSemAg` itself. -/
import rcic.RcicAnnFamHeight
import rcic.RcicAnnEnvWfG

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FamHeightG

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a type whose normal form is a non-`Prop` sort is valid only above that sort's
    height — guarded cone. -/
theorem tyKAg_sort_ht_lt {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {l : Level}
    {R : ExprA → ExprA → Prop} (h : TyKAg E I n ρ₀ k LE LT Γ (.sort l) R)
    (hz : isZero l = false) : ht ρ₀ l < k := by
  rcases tyKA_sort_invg h with ⟨_, hk, _⟩ | ⟨hz', _⟩
  · exact hk
  · rw [hz] at hz'
    cases hz'

/-- the guarded `fam` clause still validates each index domain at the clause's own
    height: a family application whose first index domain is `Sort l` (isZero l =
    false) needs `ht l < k`. -/
theorem tyKAg_famApp_firstIndexSort_lt {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {A : ExprA} {r : Nat} {ls : List Level} {ps is : List ExprA} {m : CheckedMemberA}
    {l uD vC : Level} {C : ExprA} {R : ExprA → ExprA → Prop}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hps : ps.length = m.nparamsA)
    (hT : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some (.pi (.sort l) uD C vC))
    (hz : isZero l = false) (h : TyKAg E I n ρ₀ k LE LT Γ A R) : ht ρ₀ l < k := by
  cases h with
  | prop hA' hn' hP =>
      have e := whTyA_det hA hA' hn hn'
      subst e
      exact absurd hP hnp
  | sortT hA' _ _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | sortP hA' _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA' _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | fam hA' hn' _ hm' _ _ hps' _ _ _ RsF _ _ hFldF _ _ _ _ =>
      have e := whTyA_det hA hA' hn hn'
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er; subst els
      rw [hm] at hm'; cases hm'
      obtain ⟨eps, _⟩ := List.append_inj exs (by rw [hps, hps'])
      subst eps
      have hD := hFldF [] (wkOk₀A_nil E I n Γ) ls (.pi (.sort l) uD C vC) [] [] (.sort l) uD C vC
        (eqNListB_refl (whTyA_famApp_bounded hA)) (by rw [map_wkExprA_nil]; exact hT) (.nil _ _ _) rfl
      exact tyKAg_sort_ht_lt hD hz
  | stuck hA' hN =>
      have e := whTyA_det hA hA' hn hN.1
      subst e
      exact (hN.2 (by rw [foldAppsA_const_head]; exact ⟨m, hm, hind⟩)).elim

/-- THE LARGE-INDEX BOUNDARY, guarded cone: a Type-level sort `Sort u` relates its
    elements by validity at `ht u`, so a family application whose first INDEX lives
    in `Sort l`, `ht u ≤ ht l`, is related at `Sort u` to nothing, at any height. -/
theorem LRRelAg_famApp_firstIndexSort_refuted {k : Nat} {Γ : LCtxA} {A B : ExprA} {r : Nat}
    {ls : List Level} {ps is : List ExprA} {m : CheckedMemberA} {u l uD vC : Level} {C : ExprA}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hps : ps.length = m.nparamsA)
    (hT : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some (.pi (.sort l) uD C vC))
    (hz : isZero l = false) (hzu : isZero u = false) (hle : ht ρ₀ u ≤ ht ρ₀ l) :
    ¬ LRRelAg E I n ρ₀ k Γ (.sort u) A B := by
  intro h
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  rcases tyKA_sort_invg hR with ⟨_, hk, e⟩ | ⟨hz', _⟩
  · subst e
    obtain ⟨_, ⟨R', hR'⟩, _⟩ := hab
    rw [LRTyA_eqg] at hR'
    exact absurd (tyKAg_famApp_firstIndexSort_lt hA hn hm hind hnp hps hT hz hR') (Nat.not_lt.mpr hle)
  · rw [hzu] at hz'
    cases hz'

end FamHeightG

/-! ## the `pinFamF0` fixture at the guarded cone -/

section PinLargeIndexG

variable {n : Nat} {ρ₀ : Nat → Nat}

/-- `Sort 0` related to itself at `Sort 1`, at a height above `ht 1` — the domain
    argument the `pi` eliminator needs. -/
theorem pinFamF0Arg_relatedg (k : Nat) (hk : ht ρ₀ (.succ .zero) < k) :
    LRRelAg (pinFamFEnvA 0) noIotaA n ρ₀ k [] (.sort (.succ .zero)) (.sort .zero) (.sort .zero) := by
  have h1 : LRTyAg (pinFamFEnvA 0) noIotaA n ρ₀ k [] (.sort (.succ .zero))
      (fun a b => LREqAg (pinFamFEnvA 0) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) [] a b ∧
        (∃ R, LRTyAg (pinFamFEnvA 0) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) [] a R) ∧
        (∃ R, LRTyAg (pinFamFEnvA 0) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) [] b R) ∧
        Nonempty (HasTyA (pinFamFEnvA 0) noIotaA n [] a (.sort (.succ .zero))) ∧
        Nonempty (HasTyA (pinFamFEnvA 0) noIotaA n [] b (.sort (.succ .zero))) ∧
        Nonempty (ConvA (pinFamFEnvA 0) noIotaA n [] a b (.sort (.succ .zero)))) := by
    rw [LRTyA_eqg]
    exact .sortT (whTyA_of_hasTy (.sort [] (.succ .zero))) rfl hk
  refine LRRelAg.of h1 ⟨?_, ?_, ?_, ⟨.sort [] .zero⟩, ⟨.sort [] .zero⟩, ⟨.refl [] _ _ (.sort [] .zero)⟩⟩
  · exact LREqA_sortsg [] Nat.zero_lt_one (eqNA_refl .zero)
  · exact ⟨_, by rw [LRTyA_eqg]; exact .sortP (whTyA_of_hasTy (.sort [] .zero)) rfl⟩
  · exact ⟨_, by rw [LRTyA_eqg]; exact .sortP (whTyA_of_hasTy (.sort [] .zero)) rfl⟩

/-- declared with no parameter, `F (Sort 0)` is related to nothing at `Sort 1`,
    at any height — guarded cone. -/
theorem pinFamF0App_refutedg (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (B : ExprA) :
    ¬ LRRelAg (pinFamFEnvA 0) noIotaA n ρ₀ k Γ (.sort (.succ .zero)) pinFamFAppA B :=
  LRRelAg_famApp_firstIndexSort_refuted (r := 0) (ls := []) (ps := []) (is := [.sort .zero])
    (m := pinFamFA 0) (l := .succ .zero) (uD := .succ (.succ .zero)) (vC := .succ (.succ .zero))
    (C := .sort (.succ .zero))
    (whTyA_of_hasTy (pinFamFAppTy (pinFamF_members 0) n Γ)) (pinFamFApp_nf (pinFamF_members 0) Γ)
    (pinFamF_members 0) rfl (pinFamFApp_notProp (pinFamF_members 0) Γ) rfl rfl rfl rfl (Nat.le_refl _)

/-- core: no `EnvSemClauseAg` can hold at member `0` of `pinFamFEnvA 0` — relating
    `F` at its pi type puts `F (Sort 0)` at `Sort 1`, which the boundary refutes. -/
theorem pinFamF0_clause_false {k₀ : Nat}
    (h : ∀ k, k₀ ≤ k → ∀ Δ, Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n Δ) →
      LRRelAg (pinFamFEnvA 0) noIotaA n ρ₀ k Δ (pinFamFA 0).mtypeA (.const 0 []) (.const 0 [])) :
    False := by
  have hΓ : Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n []) := ⟨.nil⟩
  have hrr := h (k₀ + (ht ρ₀ (.succ .zero) + 1)) (Nat.le_add_right _ _) [] hΓ
  have hk1 : ht ρ₀ (.succ .zero) < k₀ + (ht ρ₀ (.succ .zero) + 1) := by omega
  have hnp : ¬ IsPropTy (pinFamFEnvA 0) noIotaA [] (pinFamFA 0).mtypeA := fun hP => by
    have e := (isPropTy_pi_iff _ _ _ _ _ _ _).1 hP
    exact absurd e (by decide)
  have happ := LRRelA_pi_elimg hrr hnp [] ⟨trivial, hΓ⟩ (.sort .zero) (.sort .zero)
    (pinFamF0Arg_relatedg _ hk1)
  have happ' : LRRelAg (pinFamFEnvA 0) noIotaA n ρ₀ _ [] (.sort (.succ .zero))
      pinFamFAppA pinFamFAppA := happ
  exact pinFamF0App_refutedg n ρ₀ _ [] _ happ'

/-- the guarded semantic environment fails outside the profile — no fundamental
    theorem needed: the member clause plus the `pi` eliminator suffice. -/
theorem pinFamF0_not_envSemAg {n : Nat} {ρ₀ : Nat → Nat} :
    ¬ EnvSemAg (pinFamFEnvA 0) noIotaA n ρ₀ := by
  intro hSg
  obtain ⟨k₀, h⟩ := hSg 0 (pinFamFA 0) (pinFamF_members 0) [] [] rfl rfl rfl (eqNListA_refl [])
  exact pinFamF0_clause_false h

/-- the families' clause `EnvSemIndAg` is likewise unsatisfiable at the fixture. -/
theorem pinFamF0_not_envSemIndAg {n : Nat} {ρ₀ : Nat → Nat} :
    ¬ EnvSemIndAg (pinFamFEnvA 0) noIotaA n ρ₀ := by
  intro hInd
  have hcl := hInd 0 (pinFamFA 0) (pinFamF_members 0) (Or.inl rfl)
  obtain ⟨k₀, h⟩ := hcl [] [] rfl rfl rfl (eqNListA_refl [])
  exact pinFamF0_clause_false h

end PinLargeIndexG

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.pinFamF0_not_envSemAg
#print axioms Rcic.Declarative.Ann.pinFamF0_not_envSemIndAg
