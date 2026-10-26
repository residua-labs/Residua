import rcic.RcicF3KTWRecA

/-!
# The W fixture, class A: `RecGroupA` for the function-recursive W group
and `recVal_mem_rec_KTA` — the W recursor is in its type at the `famKT` table.
-/

namespace Rcic.F3.PSet

open Rcic.Declarative

noncomputable section

/-- W's shapes read off its field kinds: `wFieldA` is family-free
(`.nonrecursive`), `wFieldF` is a Π field (`.recursive 1`). -/
theorem w_shapesOf : shapesOf 4 [wFieldA, wFieldF] = [.nonrecursive, .recursive 1] :=
  rfl

/-- `W` is a class-A recursive group: its only constructor's fields are
`wFieldA` (family-free) and `wFieldF` (`FnRec`), and its derived minor at
fuel 8 matches the stored minor `wMinorTy`. -/
theorem w_recGroupA : RecGroupA wGroupAdmitted where
  bounded := w_bounded
  famFree := w_famFree
  fields := fun i => w_fieldsClassA _
    (List.getElem?_mem (famDataOf_ctor wGroupAdmitted i))
  riFree := fun i e he => w_ri _
    (List.getElem?_mem (famDataOf_ctor wGroupAdmitted i)) e he
  opq := fun ls => rfl
  shapes := fun i => by
    obtain ⟨i', hlt⟩ := i
    have h : i' = 0 := by
      have hcl : wGroupAdmitted.constructors.length = 1 := rfl
      omega
    subst h
    refine ⟨8, ?_⟩
    exact wMinor_derived

/-- The W recursor is an element of its type at the `famKT` table. -/
theorem w_recVal_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hKT : ∀ vs, Equiv (μ wGroupAdmitted.family.ref vs)
      (famKT P μ (famDataOf wGroupAdmitted) vs)) (vs : List Nat)
    (hctorμ : ∀ i : Fin wGroupAdmitted.constructors.length,
      Equiv (μ (wGroupAdmitted.family.ref + 1 + i.val)
        ((policyFamilyLevels wGroupAdmitted.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs)
          (famDataOf wGroupAdmitted) i.val
          (wGroupAdmitted.constructorViews i).fields.length) ρ0
          (wGroupAdmitted.constructors[i.val]).mtype)) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs)
      (famDataOf wGroupAdmitted)) ρ0 wRecMember.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 wRecMember.mtype) :=
  recVal_mem_rec_KTA P μ wGroupAdmitted w_recGroupA vs (w_nonIR P μ) w_hf hKT
    hctorμ (w_type _)

end

end PSet
