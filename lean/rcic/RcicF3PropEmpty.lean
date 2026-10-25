import rcic.RcicF3RecValRec

/-!
# F3 C: a `Prop` family each of whose constructors has a recursive field is empty

- `PropEmpty` (defined in `RcicF3Fam`): no constructor fits;
- `telFits_free_of_empty`: fields that fit are family-free when every
  recursive field's set is empty;
- `famIter_prop_empty`: at a `Prop` level, if every constructor has a field
  that is not family-free, every iterate of the family has empty fibres (by
  induction on the iterate: a recursive field's set at iterate `n + 1` is a
  fibre of iterate `n`, and at iterate `0` it is empty);
- `propEmpty_of_lim`: the same holds at the limit of the iterates, and at any
  table whose family entry is that limit.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

universe T

/-- Fields that fit are family-free when every recursive field's set is empty. -/
theorem telFits_free_of_empty {M : Interp.{T}} {σ : Nat → Nat} {f : Nat} {R : Expr Nat → Prop}
    (hR : ∀ A, R A → ∀ ρ x, ¬ x ∈ Ed M (den M σ ρ A)) :
    (Ds : List (Expr Nat)) → (∀ A, A ∈ Ds → occursConst f A = false ∨ R A) →
    ∀ ρ xs, TelFits M σ Ds ρ xs → ∀ A, A ∈ Ds → occursConst f A = false
  | [], _, _, _, _, A, hA => absurd hA (List.not_mem_nil A)
  | B :: Ds, hcls, ρ, x :: xs, ⟨hx, ht⟩, A, hA => by
      rcases List.mem_cons.mp hA with rfl | hA
      · rcases hcls A (List.mem_cons_self _ _) with h | h
        · exact h
        · exact absurd hx (hR A h ρ x)
      · exact telFits_free_of_empty hR Ds (fun A' h' => hcls A' (List.mem_cons_of_mem _ h')) _ xs ht A hA
  | _ :: _, _, _, [], h, _, _ => h.elim

/-- A family's fibre at a `Prop` level is empty when its fields that fit are
family-free and every constructor has a field that is not. -/
theorem el_famEnd_empty (P : Premises4) (μ' : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (fd : FamData)
    (h0 : evalTotal σ fd.resLevel = 0)
    (hnf : ∀ c, c ∈ fd.ctors → ¬ ∀ A, A ∈ c.1 → occursConst fd.fref A = false)
    (hfree : ∀ c, c ∈ fd.ctors → ∀ ρ xs, TelFits (mkM P μ') σ c.1 ρ xs → ∀ A, A ∈ c.1 → occursConst fd.fref A = false)
    (ρ : Nat → PSet.{4}) (z : PSet.{4}) : ¬ z ∈ El (famEnd (mkM P μ') W4 σ fd ρ) := by
  intro hz
  unfold famEnd cond at hz
  dsimp only [mkM] at hz
  cases hd : P.dec (evalTotal σ fd.resLevel = 0) with
  | isFalse h => exact h h0
  | isTrue _ =>
      rw [hd] at hz
      obtain ⟨⟨j, xs, c, hcj, hf, _⟩, _⟩ := mem_tv.mp (mem_congr_right el_tyv hz)
      have hc : c ∈ fd.ctors := mem_of_getElem?' hcj
      exact hnf c hc (hfree c hc _ xs hf)

section Iter

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hcls : ∀ c, c ∈ fd.ctors → ∀ A, A ∈ c.1 → occursConst fd.fref A = false ∨ RecApp fd ar A)
  (σ : Nat → Nat) (h0 : evalTotal σ fd.resLevel = 0)
  (hnf : ∀ c, c ∈ fd.ctors → ¬ ∀ A, A ∈ c.1 → occursConst fd.fref A = false)
include hB hpf hcls h0 hnf

/-- **Every iterate of the family has empty fibres.** -/
theorem famIter_prop_empty : ∀ n ρ z, ¬ z ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd ρ) := by
  intro n
  induction n with
  | zero =>
      refine el_famEnd_empty P _ σ fd h0 hnf (fun c hc => telFits_free_of_empty ?_ c.1 (hcls c hc))
      rintro A ⟨args, rfl, hl, hargs⟩ ρ x hx
      exact not_mem_pempty (mem_congr_right (ed_rec_zero P μ fd ar hB hpf σ ρ args hargs hl) hx)
  | succ n ih =>
      refine el_famEnd_empty P _ σ fd h0 hnf (fun c hc => telFits_free_of_empty ?_ c.1 (hcls c hc))
      rintro A ⟨args, rfl, hl, hargs⟩ ρ x hx
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
      · exact ih _ x (mem_congr_right (ed_rec_succ_fit P μ fd ar hB hpf n σ ρ args hargs hfit) hx)
      · exact not_mem_pempty (mem_congr_right (ed_rec_succ_nofit P μ fd ar hB hpf n σ ρ args hargs hl hfit) hx)

/-- **The family is empty at the limit of its iterates**, and at any table
whose entries agree with the limit's. -/
theorem propEmpty_of_lim {μ' : Nat → List Nat → PSet.{4}} (htab : ∀ r ls, Equiv (μ' r ls) (tabLim P μ fd r ls)) :
    PropEmpty (mkM P μ') σ fd := by
  rintro ρp is j xs hcf
  obtain ⟨c, hcj, hf, _⟩ := CtorFits_mono (famLE_tables P htab pempty σ fd.ctors) hcf
  have hc : c ∈ fd.ctors := mem_of_getElem?' hcj
  refine hnf c hc (telFits_free_of_empty ?_ c.1 (hcls c hc) ρp xs hf)
  rintro A ⟨args, rfl, hl, hargs⟩ ρ x hx
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (ed_rec_lim_fit P μ fd ar hB hpf σ ρ args hargs hfit) hx)
    exact famIter_prop_empty P μ fd ar hB hpf hcls σ h0 hnf n _ x hn
  · exact not_mem_pempty (mem_congr_right (ed_rec_lim_nofit P μ fd ar hB hpf σ ρ args hargs hl hfit) hx)

end Iter

end PSet

end Rcic.F3
