/- KT-2d-3: the combined family entry `famKT` (Prop-instance lfp at result
level 0, the Type-instance lfp elsewhere), its fixed point at every instance
via the canonical-instance table transfer, and the admission bridges that
discharge the class-A premises for real groups. -/

import rcic.RcicF3KTWPropFix

universe T

namespace Rcic.F3.PSet

open Rcic.Declarative

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
  (ar : Nat)

/-- The family's entry: the Prop-instance lfp where the result level is 0,
the Type-instance lfp elsewhere. -/
noncomputable def famKT (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) : PSet.{4} :=
  if evalTotal (σOf vs) fd.resLevel = 0 then famLfpP P μ fd vs else famLfp P μ fd vs

/-- `famKT` is a semantic fixed point of the family's `famVal` operator at
every instance. -/
theorem famKT_fix
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (vs : List Nat) :
    Equiv (famVal (mkM P (upd μ fd.fref (famKT P μ fd))) W4 (σOf vs) fd)
      (famKT P μ fd vs) := by
  let σ := σOf vs
  have hvl : evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel =
      evalTotal σ fd.resLevel :=
    evalTotal_agree (σOf_canon σ ar) fd.resLevel hB.res
  cases hkk : evalTotal σ fd.resLevel with
  | zero =>
      have hvs : famKT P μ fd vs = famLfpP P μ fd vs := by
        unfold famKT; rw [if_pos hkk]
      have hvs' : famKT P μ fd ((canonL ar).map (evalTotal σ)) =
          famLfpP P μ fd ((canonL ar).map (evalTotal σ)) := by
        unfold famKT; rw [if_pos (hvl.trans hkk)]
      have hret : Equiv (famLfpP P μ fd vs) (famKT P μ fd vs) := by
        rw [hvs]
        exact Equiv.rfl
      exact (famVal_transfer P μ fd ar hpf hclsA hri σ hf hvs').trans
        ((famVal_famLfpP P μ fd ar hB hpf hclsA hri hres vs hkk).trans hret)
  | succ n =>
      have hkk0 : evalTotal σ fd.resLevel ≠ 0 := by
        rw [hkk]; exact Nat.succ_ne_zero n
      have hvs : famKT P μ fd vs = famLfp P μ fd vs := by
        unfold famKT; rw [if_neg hkk0]
      have hvs' : famKT P μ fd ((canonL ar).map (evalTotal σ)) =
          famLfp P μ fd ((canonL ar).map (evalTotal σ)) := by
        unfold famKT
        rw [if_neg (by rw [hvl, hkk]; exact Nat.succ_ne_zero n)]
      have hret : Equiv (famLfp P μ fd vs) (famKT P μ fd vs) := by
        rw [hvs]
        exact Equiv.rfl
      exact (famVal_transfer P μ fd ar hpf hclsA hri σ hf hvs').trans
        ((famLfp_fix P μ fd ar hN hB hpf hclsA hri hres vs hkk0).trans hret)

/-- The combined family entry as a table update. -/
noncomputable def tabKT (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Nat → List Nat → PSet.{4} :=
  upd μ fd.fref (famKT P μ fd)

/-- `famKT_fix` restated through `tabKT`. -/
theorem tabKT_fix
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (vs : List Nat) :
    Equiv (famVal (mkM P (tabKT P μ fd)) W4 (σOf vs) fd)
      (famKT P μ fd vs) :=
  famKT_fix P μ fd ar hN hB hpf hclsA hri hres hf vs

end

/-- `FieldsClass` (family-free or directly recursive) embeds into the
class-A field disjunction. -/
theorem fieldsClassA_of_fieldsClass {f ar np nq : Nat} :
    ∀ {Fs : List (Expr Nat)} {d : Nat}, FieldsClass f ar np nq Fs d →
      FieldsClassA f ar np nq Fs d
  | [], _, _ => trivial
  | _ :: _, _, ⟨hA, hFs⟩ =>
      ⟨hA.elim Or.inl (Or.inr ∘ Or.inl),
        fieldsClassA_of_fieldsClass hFs⟩

/-- The result-index length premise from an admitted recursor elimination:
each constructor view's `indexCount`. -/
theorem hres_of_admitted {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) :
    ∀ c, c ∈ (famDataOf a).ctors → c.2.length = (famDataOf a).indices.length := by
  intro c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  show ((a.constructorViews i).resultIndices).length =
    (famDataOf a).indices.length
  exact (a.constructorViews i).indexCount

/-- The class-A field-condition premise from a `RecGroup`'s `fields`:
each constructor's fields are `FieldsClass`, hence `FieldsClassA`. -/
theorem hclsA_of_recGroup {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} (G : RecGroup a) :
    ∀ c, c ∈ (famDataOf a).ctors →
      FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length c.1 0 := by
  intro c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  show FieldsClassA _ _ _ _ (a.constructorViews i).fields 0
  exact fieldsClassA_of_fieldsClass (G.fields i)

end Rcic.F3.PSet
