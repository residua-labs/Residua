import rcic.RcicF3GroupSound

/-!
# F3: group walks and stage monotonicity

`groupMembersT_cases` / `groupMembersT_fresh_base` (a group's members are
the base's or the listed ones, the listed ones fresh in the base), `W4_mono`
(the stages grow), `ed_mem_W4_of_mem_U` (the element set of a member of a
sort lies in the stage of any level at least the sort's).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs hasTyT_denRefs groupMembersT_preserve)

namespace PSet

theorem groupMembersT_cases {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → ∀ r m, E'.members r = some m → E.members r = some m ∨ (r, m) ∈ ms
  | _, _, _, .nil _, _, _, h => Or.inl h
  | E, _, _, .cons _ r₀ m₀ _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, r, m, h => by
      rcases groupMembersT_cases hrest r m h with h1 | h1
      · by_cases hr : r = r₀
        · subst hr; rw [members_extend_eq] at h1; cases h1; exact Or.inr (List.mem_cons_self _ _)
        · rw [members_extend_ne E r₀ m₀ r hr] at h1; exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem groupMembersT_fresh_base {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → ∀ r m, (r, m) ∈ ms → E.members r = none
  | _, _, _, .nil _, _, _, h => absurd h (List.not_mem_nil _)
  | E, _, _, .cons _ r₀ m₀ _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, r, m, h => by
      rcases List.mem_cons.mp h with h1 | h1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1; exact hfresh
      · have := groupMembersT_fresh_base hrest r m h1
        by_cases hr : r = r₀
        · subst hr; exact hfresh
        · rwa [members_extend_ne E r₀ m₀ r hr] at this

theorem W4_mono (P : Premises4) {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) {x : PSet.{4}} (hx : x ∈ W4 a) :
    x ∈ W4 b := by
  have hC := chain4 P.c0 P.c1 P.c2 P.c3
  by_cases hb : b ≤ 4
  · have := hC.lift_le ha (b - a) (by omega) hx
    rwa [show a + (b - a) = b by omega] at this
  · have h4 : x ∈ W4 4 := by
      by_cases ha4 : a ≤ 4
      · have := hC.lift_le ha (4 - a) (by omega) hx
        rwa [show a + (4 - a) = 4 by omega] at this
      · have hw : W4 a = W4 4 := by
          match a, ha4 with
          | a + 5, _ => rfl
        rwa [hw] at hx
    have hw : W4 b = W4 4 := by
      match b, hb with
      | b + 5, _ => rfl
    rwa [hw]

/-- The element set of an element of a sort at level `k ≤ ℓ` lies in the stage `W ℓ`. -/
theorem ed_mem_W4_of_mem_U (P : Premises4) (M : Interp.{4}) {k ℓ : Nat} (hkℓ : k ≤ ℓ) (hℓ : 1 ≤ ℓ)
    {x : PSet.{4}} (hx : x ∈ U W4 k) : Ed M x ∈ W4 ℓ := by
  cases k with
  | zero =>
      obtain ⟨S, hS, he⟩ := mem_sImage_tyv.mp hx
      have hSp := mem_propSets.mp hS
      have e := (ed_congr M he).trans (ed_tyv M (Or.inl hSp))
      obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
      exact mem_congr_left e.symm ((stage4 P ℓ').prop_mem hSp)
  | succ k =>
      obtain ⟨S, hS, he⟩ := mem_sImage_tyv.mp hx
      obtain ⟨i, hd, hi⟩ := mem_sep.mp hS
      have hSW : S ∈ W4 (k + 1) := ⟨i, hi⟩
      have hSd : Dich S := (dich_congr hi).mp hd
      have e := (ed_congr M he).trans (ed_tyv M hSd)
      exact mem_congr_left e.symm (W4_mono P (Nat.succ_pos k) hkℓ hSW)


end PSet

end Rcic.F3
