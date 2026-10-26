import rcic.RcicF3KTWPack

/-!
# F3 S7 KT-2c: the concrete family least fixed point.

`famLfp := famOfD (DStar …)` — `DStar`'s dispatched lfp makes `famLfp` the
least fixed point of `PhiF` — and `famLfp_fix` is its fixed-point equation.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

namespace PSet

open Rcic.Declarative

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)

/-- `DStar` respects pointwise equivalence of its environment. -/
theorem DStar_env (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) {ρ ρ' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρ i) (ρ' i)) :
    Equiv (DStar P μ fd σ ρ) (DStar P μ fd σ ρ') := by
  cases hkk : evalTotal σ fd.resLevel with
  | zero => rw [DStar_zero P μ fd σ ρ hkk, DStar_zero P μ fd σ ρ' hkk]; exact Equiv.rfl
  | succ n =>
      have hk : evalTotal σ fd.resLevel ≠ 0 := fun h0 => Nat.succ_ne_zero _ (hkk ▸ h0)
      exact IsLfp.unique_of_congr
        (fun X => PsiF_env P μ fd σ h (Equiv.refl X))
        (DStar_lfp P μ fd σ ρ hk (hN σ ρ)).1
        (DStar_lfp P μ fd σ ρ' hk (hN σ ρ')).1

/-- `DStar` respects level valuations agreeing below `ar`. -/
theorem DStar_levels (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρ : Nat → PSet.{4}) :
    Equiv (DStar P μ fd σ ρ) (DStar P μ fd σ' ρ) := by
  have hkk := evalTotal_agree hσ fd.resLevel hB.res
  cases hn : evalTotal σ fd.resLevel with
  | zero =>
      rw [DStar_zero P μ fd σ ρ hn,
        DStar_zero P μ fd σ' ρ (by rw [← hkk]; exact hn)]; exact Equiv.rfl
  | succ n =>
      have hk0 : evalTotal σ fd.resLevel ≠ 0 := fun h0 => Nat.succ_ne_zero _ (hn ▸ h0)
      exact IsLfp.unique_of_congr
        (fun X => PsiF_levels P μ fd hB hσ ρ X)
        (DStar_lfp P μ fd σ ρ hk0 (hN σ ρ)).1
        (DStar_lfp P μ fd σ' ρ (fun h0 => hk0 (hkk.trans h0)) (hN σ' ρ)).1

/-- Members of `DStar` are nonempty. -/
theorem DStar_ne (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (z : PSet.{4})
    (hz : z ∈ DStar P μ fd σ ρ) : ¬ Equiv z pempty := by
  cases hkk : evalTotal σ fd.resLevel with
  | zero => rw [DStar_zero P μ fd σ ρ hkk] at hz; exact hz.elim fun i _ => i.elim
  | succ n =>
      have hk : evalTotal σ fd.resLevel ≠ 0 := fun h0 => Nat.succ_ne_zero _ (hkk ▸ h0)
      have hlfp := (DStar_lfp P μ fd σ ρ hk (hN σ ρ)).1
      have hz' := hlfp.2.1 z hz
      obtain ⟨i, hpi, hzi⟩ := mem_sep.mp hz'
      obtain ⟨j, c, xs, hcj, hdv, hIn⟩ := hpi
      exact fun hp => dataVal_ne_pempty j xs ((hzi.symm.trans hdv).symm.trans hp)

/-- `DStar` is a member of its `W4` bound. -/
theorem DStar_mem (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    DStar P μ fd σ ρ ∈ W4 (evalTotal σ fd.resLevel) := by
  cases hkk : evalTotal σ fd.resLevel with
  | zero => rw [DStar_zero P μ fd σ ρ hkk]; exact (stageW4 P _).empty
  | succ n =>
      exact hkk ▸ (DStar_lfp P μ fd σ ρ
        (fun h0 => Nat.succ_ne_zero _ (hkk ▸ h0)) (hN σ ρ)).2

/-- `DStar` is below every `PsiF`-prefixed point. -/
theorem DStar_least (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0)
    {Z : PSet.{4}} (hZ : Sub (PsiF P μ fd σ ρp Z) Z) :
    Sub (DStar P μ fd σ ρp) Z :=
  (DStar_lfp P μ fd σ ρp hk (hN σ ρp)).1.2.2 Z hZ

/-- `DStar` is a fixed point of `PhiF`. -/
theorem DStar_fixed (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0) :
    Equiv (PhiF P μ fd (DStar P μ fd) σ ρp) (DStar P μ fd σ ρp) :=
  have hlfp := (DStar_lfp P μ fd σ ρp hk (hN σ ρp)).1
  Subset.equiv hlfp.1 hlfp.2.1

/-- `famEndD` respects `D`-congruence at a fixed `σ ρ` — `D` only appears as
the `fibAt` bound set. -/
theorem famEndD_D (D D' : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (h : Equiv (D σ (shiftρ fd.indices.length ρ))
      (D' σ (shiftρ fd.indices.length ρ))) :
    Equiv (famEndD P μ fd D σ ρ) (famEndD P μ fd D' σ ρ) :=
  tyv_congr (sep_congr
    (fun a b hab h => (resTupF_congr P μ fd σ (shiftρ fd.indices.length ρ) hab).symm.trans h)
    (fun a b hab h => (resTupF_congr P μ fd σ (shiftρ fd.indices.length ρ) hab.symm).trans h)
    h)

/-- `famOfD` respects `D`-congruence at a fixed valuation. -/
theorem famOfD_congr_at (vs : List Nat)
    {D D' : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}}
    (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
    (hDD : ∀ ρ, Equiv (D (σOf vs) ρ) (D' (σOf vs) ρ)) :
    Equiv (famOfD P μ fd D vs) (famOfD P μ fd D' vs) := by
  show Equiv (piLam (mkM P μ) (σOf vs) (famEndD P μ fd D (σOf vs)) ρ0 (famType fd))
    (piLam (mkM P μ) (σOf vs) (famEndD P μ fd D' (σOf vs)) ρ0 (famType fd))
  refine piLam_congr_fits (mkM P μ) (σOf vs)
    _ ?_ _ ρ0 (fun xs _ => ?_)
  · intro A B hcontra
    exact Expr.noConfusion hcontra
  · exact famEndD_D P μ fd D D' (σOf vs) _ (hDD _)

/-- The concrete least fixed point of the family operator. -/
noncomputable def famLfp (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : List Nat → PSet.{4} := famOfD P μ fd (DStar P μ fd)

/-- `famLfp` is the fixed point of `famVal` at the `famOfD D` table. -/
theorem famLfp_fix (hN : ∀ σ ρp (j : Fin fd.ctors.length),
    NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (vs : List Nat) (hk : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    Equiv (famVal (mkM P (upd μ fd.fref (famLfp P μ fd))) W4 (σOf vs) fd)
      (famLfp P μ fd vs) :=
  (famVal_famOfD P μ fd ar (DStar P μ fd) hB hpf
    (fun σ ρ ρ' h => DStar_env P μ fd hN σ h)
    (fun σ σ' hσ ρ => DStar_levels P μ fd ar hN hB hσ ρ)
    (fun σ ρ z hz => DStar_ne P μ fd hN σ ρ z hz)
    (fun σ ρ => DStar_mem P μ fd hN σ ρ)
    hclsA hri hres vs hk).trans
    (famOfD_congr_at P μ fd vs
      (fun σ ρ ρ' h => PsiF_env P μ fd σ h (DStar_env P μ fd hN σ h))
      (fun ρ => DStar_fixed P μ fd hN (σOf vs) ρ hk))

end PSet

end Rcic.F3
