import rcic.RcicF3KTWAgree
import rcic.RcicF3RecValRec

open Rcic.Declarative

/-!
# KT-3a: the real table carrying `famKT`

A table `μ` that already contains the family's `famKT` entry
(`μ (famDataOf a).fref vs ≈ famKT P μ fd vs`) behaves at that entry exactly
like `tabKT P μ fd`: the family's entry is the semantic `famVal`, and a
recursive field occurrence denotes the `DStar`/`DStarP` fibre at its index
tuple — the Type-instance reading at nonzero result levels and the
Prop-instance reading at level 0.
-/

namespace Rcic.F3.PSet

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})
  {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m)
  (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))

include hKT in
/-- `tabKT` agrees with the real table pointwise. -/
theorem tabKT_equiv : ∀ r' ls, Equiv (tabKT P μ (famDataOf a) r' ls) (μ r' ls) := by
  intro r' ls
  by_cases hr : r' = a.family.ref
  · subst hr
    show Equiv (upd μ a.family.ref (famKT P μ (famDataOf a)) a.family.ref ls) _
    rw [upd_eq]
    exact (hKT ls).symm
  · show Equiv (upd μ a.family.ref (famKT P μ (famDataOf a)) r' ls) _
    rw [upd_ne μ _ _ hr]
    exact Equiv.rfl

/-- Constructor result-index expressions are family-free (from `RecGroup`). -/
theorem hri_of_recGroup (G : RecGroup a) :
    ∀ c, c ∈ (famDataOf a).ctors → ∀ e, e ∈ c.2 →
      occursConst (famDataOf a).fref e = false := by
  intro c hc e he
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  exact G.riFree i e he

include hKT in
/-- The family's entry is the family's value, at every recursor instance. -/
theorem famμ_of_KT (G : RecGroup a)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2) (vs : List Nat) :
    Equiv (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf a)) :=
  (hKT _).trans ((famKT_fix P μ (famDataOf a) a.family.member.arity hN G.bounded G.famFree
      (hclsA_of_recGroup G) (hri_of_recGroup a G) (hres_of_admitted a) hf _).symm.trans
    ((famVal_levels (mkM P (tabKT P μ (famDataOf a)))
      (σOf_policyFamilyLevels_agree a.family vs) W4 _ G.bounded).trans
      (famVal_tables P (tabKT_equiv P μ a hKT) _ _)))

include hKT in
/-- A recursive occurrence at a nonzero result level reads the `DStar` fibre,
at the real table. -/
theorem ed_recOcc_KT (G : RecGroup a)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (σ : Nat → Nat) (hk : evalTotal σ (famDataOf a).resLevel ≠ 0)
    (ps ys : List PSet.{4}) (hps : ps.length = (famDataOf a).params.length)
    (idx : List (Expr Nat)) (hidx : idx.length = (famDataOf a).indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst (famDataOf a).fref e = false)
    (x : PSet.{4}) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) σ (push ys (push ps ρ0))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) ↔
      x ∈ DStar P μ (famDataOf a) σ (push ps ρ0) ∧
        Equiv (resTupF P μ (famDataOf a) σ (push ps ρ0) x)
          (recTupAt P μ (famDataOf a) σ (push ys (push ps ρ0))
            (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
              (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  have hpf : ∀ e, e ∈ (famDataOf a).params ++ (famDataOf a).indices →
      occursConst (famDataOf a).fref e = false := G.famFree
  let A := foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
    (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)
  let ρ := push ys (push ps ρ0)
  let vs' := (canonL a.family.member.arity).map (evalTotal σ)
  have hagg := evalTotal_agree (σOf_canon σ a.family.member.arity)
    (famDataOf a).resLevel hB.res
  have hkk : evalTotal (σOf vs') (famDataOf a).resLevel ≠ 0 :=
    fun h0 => hk (hagg.symm.trans h0)
  have hX : famKT P μ (famDataOf a) vs' = famLfp P μ (famDataOf a) vs' := by
    unfold famKT
    rw [if_neg hkk]
  have hco : CanonOcc (famDataOf a).fref a.family.member.arity A :=
    canonOcc_foldApps _ (fun e he => by
      rcases List.mem_append.mp he with h | h
      · exact canonOcc_of_free
          (paramLocals_free (famDataOf a).fref (famDataOf a).params.length ys.length e h)
      · exact canonOcc_of_free (hfree e h))
  have deneq := den_transfer P μ (famDataOf a).fref a.family.member.arity σ hX hf A hco ρ
  have e1 := ed_recOcc P μ (famDataOf a) a.family.member.arity
    (DStar P μ (famDataOf a)) hB hpf
    (fun σ' ρ1 ρ' hρ => DStar_env P μ (famDataOf a) hN σ' hρ)
    (fun σ' σ'' hσ ρ1 => DStar_levels P μ (famDataOf a) a.family.member.arity hN hB hσ ρ1)
    (fun σ' ρ1 z hz => DStar_ne P μ (famDataOf a) hN σ' ρ1 z hz)
    (fun σ' ρ1 => DStar_mem P μ (famDataOf a) hN σ' ρ1)
    σ ps ys hps idx hidx hfree
  have e2 : Equiv (Ed (mkM P (tabKT P μ (famDataOf a)))
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A)) :=
    Ed_dec_eq P (tabKT P μ (famDataOf a)) μ
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) ▸
      ed_congr (mkM P μ)
        (den_tables P (tabKT_equiv P μ a hKT) σ A (fun _ => Equiv.rfl))
  constructor
  · intro hx
    have hx1 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) :=
      mem_congr_right e2.symm hx
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a)))))
        (den (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a))))) σ ρ A) :=
      (Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))) σ ρ A)).symm ▸
        (deneq.symm ▸ hx1)
    obtain ⟨i, h1, h2⟩ := mem_sep.mp (mem_congr_right e1 hx2)
    exact ⟨⟨i, h2⟩, (resTupF_congr P μ (famDataOf a) σ (push ps ρ0) h2).symm.trans h1⟩
  · intro ⟨hd, he⟩
    obtain ⟨i, hxi⟩ := hd
    have hx : x ∈ sep (fun z => Equiv (resTupF P μ (famDataOf a) σ (push ps ρ0) z)
        (recTupAt P μ (famDataOf a) σ (push ys (push ps ρ0)) A))
        (DStar P μ (famDataOf a) σ (push ps ρ0)) :=
      mem_sep.mpr ⟨i, (resTupF_congr P μ (famDataOf a) σ (push ps ρ0) hxi).trans he, hxi⟩
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a)))))
        (den (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a))))) σ ρ A) :=
      mem_congr_right e1.symm hx
    have hx1 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a))))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) :=
      Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) ▸
        (deneq ▸ hx2)
    have hx3 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) := hx1
    exact mem_congr_right e2 hx3

include hKT in
/-- A recursive occurrence at a zero result level reads the `DStarP` fibre,
at the real table. -/
theorem ed_recOcc_KTP (G : RecGroup a)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (σ : Nat → Nat) (hk : evalTotal σ (famDataOf a).resLevel = 0)
    (ps ys : List PSet.{4}) (hps : ps.length = (famDataOf a).params.length)
    (idx : List (Expr Nat)) (hidx : idx.length = (famDataOf a).indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst (famDataOf a).fref e = false)
    (x : PSet.{4}) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) σ (push ys (push ps ρ0))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) ↔
      Equiv x pempty ∧
        argsFitF P μ (famDataOf a) σ (push ys (push ps ρ0))
          (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
            (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)) ∧
        tup (idx.map (den (mkM P μ) σ (push ys (push ps ρ0)))) ∈
          DStarP P μ (famDataOf a) σ (push ps ρ0) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  have hpf : ∀ e, e ∈ (famDataOf a).params ++ (famDataOf a).indices →
      occursConst (famDataOf a).fref e = false := G.famFree
  let A := foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
    (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)
  let ρ := push ys (push ps ρ0)
  let vs' := (canonL a.family.member.arity).map (evalTotal σ)
  have hagg := evalTotal_agree (σOf_canon σ a.family.member.arity)
    (famDataOf a).resLevel hB.res
  have hkk : evalTotal (σOf vs') (famDataOf a).resLevel = 0 := hagg.trans hk
  have hX : famKT P μ (famDataOf a) vs' = famLfpP P μ (famDataOf a) vs' := by
    unfold famKT
    rw [if_pos hkk]
  have hco : CanonOcc (famDataOf a).fref a.family.member.arity A :=
    canonOcc_foldApps _ (fun e he => by
      rcases List.mem_append.mp he with h | h
      · exact canonOcc_of_free
          (paramLocals_free (famDataOf a).fref (famDataOf a).params.length ys.length e h)
      · exact canonOcc_of_free (hfree e h))
  have deneq := den_transfer P μ (famDataOf a).fref a.family.member.arity σ hX hf A hco ρ
  have e1 := ed_recOccP P μ (famDataOf a) a.family.member.arity hB hpf σ ps ys hps idx hidx hfree
  have e2 : Equiv (Ed (mkM P (tabKT P μ (famDataOf a)))
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A)) :=
    (Ed_dec_eq P (tabKT P μ (famDataOf a)) μ
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) ▸
      (ed_congr (mkM P μ)
        (den_tables P (tabKT_equiv P μ a hKT) σ A (fun _ => Equiv.rfl))).symm).symm
  constructor
  · intro hx
    have hx1 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) :=
      mem_congr_right e2.symm hx
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a))))
        (den (mkM P (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a)))) σ ρ A) :=
      (Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a)))) σ ρ A)).symm ▸
        (deneq.symm ▸ hx1)
    obtain ⟨h1, h2⟩ := mem_tv.mp (mem_congr_right e1 hx2)
    exact ⟨h2, h1⟩
  · intro ⟨hx0, hf2, hm⟩
    have hx : x ∈ tv (argsFitF P μ (famDataOf a) σ (push ys (push ps ρ0)) A ∧
        tup (idx.map (den (mkM P μ) σ (push ys (push ps ρ0)))) ∈
          DStarP P μ (famDataOf a) σ (push ps ρ0)) :=
      mem_tv.mpr ⟨⟨hf2, hm⟩, hx0⟩
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a))))
        (den (mkM P (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a)))) σ ρ A) :=
      mem_congr_right e1.symm hx
    have hx1 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a))))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) :=
      Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfpP P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) ▸
        (deneq ▸ hx2)
    have hx3 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) := hx1
    exact mem_congr_right e2 hx3

end Rcic.F3.PSet
