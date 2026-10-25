import rcic.RcicF3Fund
import rcic.RcicF3Table
import rcic.RcicTypedGroupPins

/-!
# F3: consistency at the admitted `False` environment, end to end

`falseEnvU` is the admitted environment with the standard empty family
`False : Prop` at reference 0 and its recursor
`False.rec.{u} : Π (motive : False → Sort u) (t : False), motive t` at
reference 1 (`falseEnvUWfT`).

- `falseμ`: `False` denotes the empty type value; the recursor denotes the
  abstraction that, given a motive, returns the abstraction over the empty
  domain;
- `falseEnvSound`: this table satisfies `EnvSound` (membership; δ is vacuous,
  no member has a body; ι is vacuous, no member is a constructor);
- `falseEnvU_consistent4`: no closed term has type `False` in `falseEnvU` by
  a derivation whose sort levels stay below 4.

Residual assumptions, as one hypothesis `P : Premises4` (no axiom):
decidability of every proposition and the choice premises
`Choice.{0} … Choice.{3}`. The model lives in
`PSet.{4}`: the statement is relative consistency in Lean with universes
`0 … 4`, as Gödel's second theorem requires. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

theorem Premises4.good (P : Premises4) (M : Interp.{4}) (hU : M.U = U W4) : Good M 4 (Lvl W4) :=
  good4 P.c0 P.c1 P.c2 P.c3 M hU

/-- The table without constants (only `dec` and `U` are read by `piVal`). -/
def falseM0 (dec : ∀ p : Prop, Decidable p) : Interp.{4} := ⟨dec, U W4, fun _ _ => pempty⟩

/-- The interpretation of `falseEnvU`'s members. -/
def falseμ (dec : ∀ p : Prop, Decidable p) : Nat → List Nat → PSet.{4}
  | 0, _ => tyv pempty
  | 1, vs => lamVal (falseM0 dec)
      (piVal (falseM0 dec) (tyv pempty) (fun _ => tyv (U W4 (vs.headD 0))))
      (fun _ => lamVal (falseM0 dec) (tyv pempty) (fun _ => pempty))
  | _, _ => pempty

def falseM (dec : ∀ p : Prop, Decidable p) : Interp.{4} := ⟨dec, U W4, falseμ dec⟩

theorem falseEnvU_m0 : falseEnvU.members 0 = some falseFamMember := rfl

theorem falseEnvU_m1 : falseEnvU.members 1 = some falseRecMemberU := rfl

theorem falseEnvU_m2 (r : Nat) : falseEnvU.members (r + 2) = none := by
  simp only [falseEnvU, falsePrefix, extendEnv, emptyEnv]
  rw [if_neg (by omega), if_neg (by omega)]

/-- No member of `falseEnvU` is a constructor or has a body. -/
theorem falseEnvU_member_shape {r : Nat} {m : CheckedMember} (h : falseEnvU.members r = some m) :
    m.mclass ≠ .constructorM ∧ m.body = none := by
  match r, h with
  | 0, h => rw [falseEnvU_m0] at h; cases h; exact ⟨fun h => MemberClass.noConfusion h, rfl⟩
  | 1, h => rw [falseEnvU_m1] at h; cases h; exact ⟨fun h => MemberClass.noConfusion h, rfl⟩
  | r + 2, h => rw [falseEnvU_m2] at h; exact Option.noConfusion h

theorem ed_tyv_pempty (M : Interp.{4}) {x : PSet.{4}} (hx : x ∈ Ed M (tyv pempty)) : False := by
  have e : Equiv (Ed M (tyv pempty)) pempty :=
    ed_tyv M (Or.inl fun _ h => (not_mem_pempty h).elim)
  exact not_mem_pempty (mem_congr_right e hx)

theorem falseEnvSound (P : Premises4) (σ : Nat → Nat) (K : Nat → Nat) (n : Nat) :
    EnvSound (falseM P.dec) σ K falseEnvU n where
  const := by
    intro Γ r ls m ρ hres hlen _ _
    match r, hres with
    | 1, hres =>
      rw [falseEnvU_m1] at hres
      cases hres
      match ls, hlen with
      | [l], _ =>
        show lamVal (falseM0 P.dec) _ _ ∈ Ed (falseM P.dec) (piVal (falseM P.dec) _ _)
        refine lam_mem (falseM P.dec) (fun _ _ _ => Equiv.rfl) ?_ ?_
        · intro x x' hx
          exact den_resp (falseM P.dec) σ ρ _ x x' hx
        · intro x _
          refine lam_mem (falseM P.dec) (fun _ _ _ => Equiv.rfl) ?_ ?_
          · intro t t' ht
            exact den_resp (falseM P.dec) σ (vcons x ρ) (.app (.bvar 1) (.bvar 0)) t t' ht
          · intro t ht
            exact (ed_tyv_pempty (falseM P.dec) ht).elim
    | 0, hres =>
      rw [falseEnvU_m0] at hres
      cases hres
      match ls, hlen with
      | [], _ =>
        show tyv pempty ∈ Ed (falseM P.dec) (tyv (U W4 0))
        have hG := P.good (falseM P.dec) rfl
        refine mem_congr_right (ed_sortU hG (Nat.zero_le 4)).symm ?_
        exact ((hG.U_iff (Nat.zero_le 4) _).mpr
          ⟨pempty, fun _ h => (not_mem_pempty h).elim, Equiv.rfl⟩)
    | r + 2, hres => rw [falseEnvU_m2] at hres; exact Option.noConfusion hres
  delta := by
    intro Γ r ls m b ρ hres hbody _ _ _ _
    rw [(falseEnvU_member_shape hres).2] at hbody
    exact Option.noConfusion hbody
  iota := by
    intro Γ lhs rhs T ρ hι _ _ _ _ _ _ _ _
    cases hι with
    | of w => exact ((falseEnvU_member_shape w.hctor).1 w.hctorK).elim

/-- No closed proof of `False` in `falseEnvU` below level 4. -/
theorem falseEnvU_consistent4 (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (h : HasTyT falseEnvU n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False := by
  have hG := P.good (falseM P.dec) rfl
  have hm := sound_ty hG (falseEnvSound P (fun _ => 0) K n) h hl (fun _ => pempty) trivial
  exact ed_tyv_pempty (falseM P.dec) hm

end PSet

end Rcic.F3
