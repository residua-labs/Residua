import rcic.RcicF3Agree
import rcic.RcicF3FamFix

/-!
# F3 S5b-2: the limit of a recursive family's iterates (definitions)

The definitions of `RcicF3FamLim` (iterates `famIter`, the limit `famLim`),
placed before the group roles (`RcicF3EnvG`) that install a family at its
limit, with the syntactic facts they share.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs denRefsLit)

namespace PSet

theorem denRefsLit_mem : (t : Nat) → ∀ r, r ∈ denRefsLit t → r = 1 ∨ (r = 2 ∧ t ≠ 0)
  | 0, r, h => Or.inl (List.mem_singleton.mp h)
  | t + 1, r, h => by
      rcases List.mem_cons.mp h with h | h
      · exact Or.inr ⟨h, by omega⟩
      · rcases denRefsLit_mem t r h with h1 | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by omega⟩

/-- A reference of an expression in which `f` does not occur is not `f`. -/
theorem denRefs_ne_of_occurs {f : Nat} : (T : Expr Nat) → occursConst f T = false → ∀ r, r ∈ denRefs T → r ≠ f
  | .bvar _, _, _, h => absurd h (List.not_mem_nil _)
  | .sort _, _, _, h => absurd h (List.not_mem_nil _)
  | .const r' _, ho, r, h => by
      have hr : r = r' := List.mem_singleton.mp h
      subst hr
      intro he; subst he
      simp [occursConst] at ho
  | .app a b, ho, r, h => by
      have ho' : (occursConst f a || occursConst f b) = false := ho
      rw [Bool.or_eq_false_iff] at ho'
      rcases List.mem_append.mp h with h | h
      · exact denRefs_ne_of_occurs a ho'.1 r h
      · exact denRefs_ne_of_occurs b ho'.2 r h
  | .lam a b, ho, r, h => by
      have ho' : (occursConst f a || occursConst f b) = false := ho
      rw [Bool.or_eq_false_iff] at ho'
      rcases List.mem_append.mp h with h | h
      · exact denRefs_ne_of_occurs a ho'.1 r h
      · exact denRefs_ne_of_occurs b ho'.2 r h
  | .pi a b, ho, r, h => by
      have ho' : (occursConst f a || occursConst f b) = false := ho
      rw [Bool.or_eq_false_iff] at ho'
      rcases List.mem_append.mp h with h | h
      · exact denRefs_ne_of_occurs a ho'.1 r h
      · exact denRefs_ne_of_occurs b ho'.2 r h
  | .letE a v b, ho, r, h => by
      have ho' : ((occursConst f a || occursConst f v) || occursConst f b) = false := ho
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at ho'
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact denRefs_ne_of_occurs a ho'.1.1 r h
        · exact denRefs_ne_of_occurs v ho'.1.2 r h
      · exact denRefs_ne_of_occurs b ho'.2 r h
  | .lit t, ho, r, h => by
      have ho' : litOccurs f t = false := ho
      intro he; subst he
      rcases denRefsLit_mem t r h with h1 | ⟨h1, ht⟩
      · subst h1
        cases t with
        | zero => simp [litOccurs] at ho'
        | succ t => simp [litOccurs] at ho'
      · subst h1
        cases t with
        | zero => exact ht rfl
        | succ t => simp [litOccurs] at ho'

theorem mem_ofFin {α : Type} {x : α} : (n : Nat) → (g : Fin n → α) → x ∈ ofFin n g → ∃ i, x = g i
  | 0, _, h => absurd h (List.not_mem_nil _)
  | n + 1, g, h => by
      rcases List.mem_cons.mp h with h | h
      · exact ⟨_, h⟩
      · obtain ⟨i, hi⟩ := mem_ofFin n _ h
        exact ⟨_, hi⟩

theorem foldApps_ne_pi (f : Expr Nat) (hf : ∀ A B, f ≠ .pi A B) : (as : List (Expr Nat)) →
    ∀ A B, foldApps f as ≠ .pi A B := by
  intro as
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih => exact ih (.app f a) (fun _ _ h => Expr.noConfusion h)

/-- The canonical universe vector of arity `ar`. -/
def canonL (ar : Nat) : List Level := (List.range ar).map Level.param

/-- The family with every fibre empty. -/
def famZero (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat) : PSet.{4} :=
  piLam (mkM P μ) σ (fun _ => tyv pempty) ρ0 (famType fd)

/-- The iterates of the family's entry. -/
def famIter (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) : Nat → List Nat → PSet.{4}
  | 0 => fun vs => famZero P μ fd (σOf vs)
  | n + 1 => fun vs => famVal (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 (σOf vs) fd

/-- The table at stage `n`. -/
def tabIter (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (n : Nat) :
    Nat → List Nat → PSet.{4} :=
  upd μ fd.fref (famIter P μ fd n)

/-- The end of the limit: the union of the iterates' fibres. -/
def limEnd (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) : PSet.{4} :=
  tyv (iUnionN fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd ρ))

/-- The limit of the iterates. -/
def famLim (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) : List Nat → PSet.{4} :=
  fun vs => piLam (mkM P μ) (σOf vs) (limEnd P μ fd (σOf vs)) ρ0 (famType fd)

/-- The table at the limit. -/
def tabLim (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) : Nat → List Nat → PSet.{4} :=
  upd μ fd.fref (famLim P μ fd)

theorem limEnd_resp (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat) :
    EnvResp (limEnd P μ fd σ) := fun _ _ h =>
  tyv_congr (iUnionN_congr fun _ => el_congr (famEnd_resp _ W4 σ fd _ _ h))

/-- The family instance of a recursor or constructor instance agrees with it below the family arity. -/
theorem σOf_famLevels_agree (vs : List Nat) (ar : Nat) :
    ∀ i, i < ar → σOf (((List.range ar).map Level.param).map (evalTotal (σOf vs))) i = σOf vs i := by
  intro i hi
  have hl : i < (((List.range ar).map Level.param).map (evalTotal (σOf vs))).length := by simp; exact hi
  simp only [σOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_map,
    List.getElem_range, evalTotal]

theorem σOf_policyFamilyLevels_agree {E : ResolvedEnv} (fam : PolicyFamilyView E) (vs : List Nat) :
    ∀ i, i < fam.member.arity → σOf ((policyFamilyLevels fam).map (evalTotal (σOf vs))) i = σOf vs i :=
  σOf_famLevels_agree vs _

end PSet

end Rcic.F3
