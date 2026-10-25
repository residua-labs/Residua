import rcic.RcicF3Syn

/-!
# F3 S5a-7: the group's values read only the levels below the arity

`FamBounded fd k`: every expression of the group's data has its levels
bounded by `k`. Then the family's, the constructors' and the recursor's
values at two level valuations that agree below `k` are `≈`-equal
(`famVal_levels`, `piLam_levels`), and fitting is the same
(`TelFits_levels`, `CtorFits_levels`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- Every expression of the list has its levels bounded by `k`. -/
def ExprsBounded (k : Nat) (es : List (Expr Nat)) : Prop := ∀ e, e ∈ es → exprLevelsBounded k e = true

/-- Every expression of the group's data has its levels bounded by `k`. -/
structure FamBounded (fd : FamData) (k : Nat) : Prop where
  params : ExprsBounded k fd.params
  indices : ExprsBounded k fd.indices
  res : levelBounded k fd.resLevel = true
  ctors : ∀ c, c ∈ fd.ctors → ExprsBounded k c.1 ∧ ExprsBounded k c.2

section Agree

variable (M : Interp.{T}) {σ σ' : Nat → Nat} {k : Nat} (h : ∀ i, i < k → σ i = σ' i)
include h

theorem TelFits_levels : (Ds : List (Expr Nat)) → ExprsBounded k Ds → (ρ : Nat → PSet.{T}) →
    (xs : List PSet.{T}) → (TelFits M σ Ds ρ xs ↔ TelFits M σ' Ds ρ xs)
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | A :: Ds, hb, ρ, x :: xs => by
      show (x ∈ Ed M (den M σ ρ A) ∧ _) ↔ (x ∈ Ed M (den M σ' ρ A) ∧ _)
      rw [den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ,
        TelFits_levels Ds (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x ρ) xs]

theorem map_den_levels (es : List (Expr Nat)) (hb : ExprsBounded k es) (ρ : Nat → PSet.{T}) :
    es.map (den M σ ρ) = es.map (den M σ' ρ) :=
  List.map_congr_left fun e he => den_levels_agree M h e (hb e he) ρ

theorem CtorFits_levels (fd : FamData) (hB : FamBounded fd k) (ρp : Nat → PSet.{T})
    (is : List PSet.{T}) (j : Nat) (xs : List PSet.{T}) :
    CtorFits M σ fd.ctors ρp is j xs ↔ CtorFits M σ' fd.ctors ρp is j xs := by
  constructor
  · rintro ⟨c, hc, hf, hi⟩
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    refine ⟨c, hc, (TelFits_levels M h c.1 (hB.ctors c hcm).1 ρp xs).mp hf, ?_⟩
    rw [← map_den_levels M h c.2 (hB.ctors c hcm).2]; exact hi
  · rintro ⟨c, hc, hf, hi⟩
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    refine ⟨c, hc, (TelFits_levels M h c.1 (hB.ctors c hcm).1 ρp xs).mpr hf, ?_⟩
    rw [map_den_levels M h c.2 (hB.ctors c hcm).2]; exact hi

theorem FitSetT_levels (W : Nat → PSet.{T}) (k' : Nat) : (Ds : List (Expr Nat)) → ExprsBounded k Ds →
    (ρ : Nat → PSet.{T}) → FitSetT M W k' σ Ds ρ = FitSetT M W k' σ' Ds ρ
  | [], _, _ => rfl
  | A :: Ds, hb, ρ => by
      show sUnion (sImage _ (truncW M W k' (Ed M (den M σ ρ A)))) =
        sUnion (sImage _ (truncW M W k' (Ed M (den M σ' ρ A))))
      rw [den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ]
      have : (fun x => sImage (fun t => ordPair x t) (FitSetT M W k' σ Ds (vcons x ρ))) =
          (fun x => sImage (fun t => ordPair x t) (FitSetT M W k' σ' Ds (vcons x ρ))) :=
        funext fun x => by rw [FitSetT_levels W k' Ds (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x ρ)]
      rw [this]

theorem BoundT_levels (W : Nat → PSet.{T}) (k' : Nat) (ρp : Nat → PSet.{T}) :
    (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) →
    (∀ c, c ∈ cs → ExprsBounded k c.1) → BoundT M W k' σ ρp j cs = BoundT M W k' σ' ρp j cs
  | _, [], _ => rfl
  | j, c :: cs, hb => by
      show sUnion (pair (sImage _ (FitSetT M W k' σ c.1 ρp)) _) = sUnion (pair (sImage _ (FitSetT M W k' σ' c.1 ρp)) _)
      rw [FitSetT_levels M h W k' c.1 (hb c (List.mem_cons_self _ _)) ρp,
        BoundT_levels W k' ρp (j + 1) cs (fun c' hc' => hb c' (List.mem_cons_of_mem _ hc'))]

theorem famEnd_levels (W : Nat → PSet.{T}) (fd : FamData) (hB : FamBounded fd k) (ρ : Nat → PSet.{T}) :
    Equiv (famEnd M W σ fd ρ) (famEnd M W σ' fd ρ) := by
  unfold famEnd
  rw [evalTotal_agree h fd.resLevel hB.res]
  refine cond_congr Iff.rfl (tyv_congr (tv_congr ?_)) (tyv_congr ?_)
  · exact ⟨fun ⟨j, xs, hc⟩ => ⟨j, xs, (CtorFits_levels M h fd hB _ _ j xs).mp hc⟩,
      fun ⟨j, xs, hc⟩ => ⟨j, xs, (CtorFits_levels M h fd hB _ _ j xs).mpr hc⟩⟩
  · unfold TypeFib
    rw [BoundT_levels M h W _ _ 0 fd.ctors (fun c hc => (hB.ctors c hc).1)]
    exact sep_congr
      (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, (CtorFits_levels M h fd hB _ _ j xs).mp hc, hab.symm.trans he⟩)
      (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, (CtorFits_levels M h fd hB _ _ j xs).mpr hc, hab.symm.trans he⟩)
      Equiv.rfl

theorem piLam_levels {g g' : (Nat → PSet.{T}) → PSet.{T}} (hg : EnvResp g)
    (hgg : ∀ ρ, Equiv (g ρ) (g' ρ)) (b : Expr Nat) (hbb : ∀ ρ, Equiv (piLam M σ g ρ b) (piLam M σ' g' ρ b)) :
    (Ds : List (Expr Nat)) → ExprsBounded k Ds → (ρ : Nat → PSet.{T}) →
      Equiv (piLam M σ g ρ (policyPi Ds b)) (piLam M σ' g' ρ (policyPi Ds b))
  | [], _, ρ => hbb ρ
  | A :: Ds, hb, ρ => by
      show Equiv (lamVal M (den M σ ρ A) _) (lamVal M (den M σ' ρ A) _)
      rw [den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ]
      refine lamVal_congr M Equiv.rfl fun x x' hx => ?_
      exact (piLam_congr M σ hg _ (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))).trans
        (piLam_levels hg hgg b hbb Ds (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x' ρ))

theorem famVal_levels (W : Nat → PSet.{T}) (fd : FamData) (hB : FamBounded fd k) :
    Equiv (famVal M W σ fd) (famVal M W σ' fd) :=
  piLam_levels M h (famEnd_resp M W σ fd) (famEnd_levels M h W fd hB) (.sort fd.resLevel)
    (famEnd_levels M h W fd hB) (fd.params ++ fd.indices)
    (fun e he => by
      rcases List.mem_append.mp he with h1 | h1
      · exact hB.params e h1
      · exact hB.indices e h1) _

end Agree

end PSet

end Rcic.F3
