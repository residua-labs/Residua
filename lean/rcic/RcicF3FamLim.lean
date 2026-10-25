import rcic.RcicF3LimDef

/-!
# F3 S5b-2: the family of a recursive group as a fixed point

A recursive field reads the family's own table entry. The entry is built as
the limit of iterates: `famIter 0` has every fibre empty, `famIter (n+1)` is
the family's value read at the table with `famIter n` at the family, and
`famLim`'s fibre at each environment is the union of the iterates' fibres.

- `RecApp`: a recursive field, the family at its canonical instance applied
  to family-free arguments; its set at a table `upd μ f X` is `X`'s end at the
  arguments when they fit the family's telescope, `∅` otherwise
  (`ed_recApp_fit` / `ed_recApp_nofit`);
- `famChain_iter`: the iterates' field sets grow, and their union is the
  limit's (`FamChain` of `RcicF3FamFix`), given that every field is
  family-free or recursive and the parameters, indices and result indices
  are family-free;
- `famLim_fix`: **the limit is a fixed point**, the family's value read at the
  table with the limit at the family is `≈` the limit.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs denRefsLit)

namespace PSet

/-! ### applications of family-shaped values -/

theorem ed_mkM (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (t : PSet.{4}) :
    Ed (mkM P μ₁) t = Ed (mkM P μ₂) t := rfl

/-- At fitting values, a family-shaped value applies to its end. -/
theorem fapps_fam_fit (P : Premises4) (μ' : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat)
    {g : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g) (as : List PSet.{4})
    (hfit : TelFits (mkM P μ') σ (fd.params ++ fd.indices) ρ0 as) :
    Equiv (fapps (piLam (mkM P μ') σ g ρ0 (famType fd)) as) (g (push as ρ0)) :=
  fapps_piLam (mkM P μ') σ hg (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 as hfit

/-- At values that do not fit, a family-shaped value applies to `∅`. -/
theorem fapps_fam_nofit (P : Premises4) (μ' : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat)
    {g : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g) (as : List PSet.{4})
    (hl : as.length = (fd.params ++ fd.indices).length)
    (hfit : ¬ TelFits (mkM P μ') σ (fd.params ++ fd.indices) ρ0 as) :
    Equiv (fapps (piLam (mkM P μ') σ g ρ0 (famType fd)) as) pempty := by
  cases hd : P.dec (Equiv (fapps (piLam (mkM P μ') σ g ρ0 (famType fd)) as) pempty) with
  | isTrue h => exact h
  | isFalse h => exact absurd (fits_of_fapps_ne (mkM P μ') σ hg (.sort fd.resLevel) _ ρ0 as hl h) hfit

/-! ### recursive fields -/

/-- A recursive field: the family at its canonical instance applied to
family-free arguments, as many as its parameters and indices. -/
def RecApp (fd : FamData) (ar : Nat) (A : Expr Nat) : Prop :=
  ∃ args : List (Expr Nat), A = foldApps (.const fd.fref (canonL ar)) args ∧
    args.length = (fd.params ++ fd.indices).length ∧ ∀ e, e ∈ args → occursConst fd.fref e = false

theorem σOf_canon (σ : Nat → Nat) (ar : Nat) : ∀ i, i < ar → σOf ((canonL ar).map (evalTotal σ)) i = σ i := by
  intro i hi
  simp only [σOf, canonL, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem agreeOn_upd_off (μ : Nat → List Nat → PSet.{4}) (f : Nat) (X : List Nat → PSet.{4}) :
    AgreeOn (upd μ f X) μ (fun r => r ≠ f) := fun _ hr ls => upd_ne μ f X hr ls

theorem den_off (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat) (X : List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {e : Expr Nat} (he : occursConst f e = false) :
    den (mkM P (upd μ f X)) σ ρ e = den (mkM P μ) σ ρ e :=
  den_agreeOn P (agreeOn_upd_off μ f X) σ e (denRefs_ne_of_occurs e he) ρ

/-- A recursive field denotes the family entry applied to its arguments. -/
theorem den_recApp (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {fd : FamData} {ar : Nat}
    (X : List Nat → PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {args : List (Expr Nat)}
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) :
    den (mkM P (upd μ fd.fref X)) σ ρ (foldApps (.const fd.fref (canonL ar)) args) =
      fapps (X ((canonL ar).map (evalTotal σ))) (args.map (den (mkM P μ) σ ρ)) := by
  rw [den_foldApps]
  show fapps (upd μ fd.fref X fd.fref _) _ = _
  rw [upd_eq]
  congr 1
  exact List.map_congr_left fun e he => den_off P μ fd.fref X σ ρ (hargs e he)

section Shaped

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hpi : ExprsBounded ar (fd.params ++ fd.indices))
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (X : List Nat → PSet.{4}) (μX : Nat → List Nat → PSet.{4}) (gX : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
  (hX : ∀ vs, X vs = piLam (mkM P μX) (σOf vs) (gX (σOf vs)) ρ0 (famType fd))
  (hμX : AgreeOn μX μ (fun r => r ≠ fd.fref)) (hg : ∀ σ, EnvResp (gX σ))
  (hlv : ∀ σ σ', (∀ i, i < ar → σ i = σ' i) → ∀ ρ, Equiv (gX σ ρ) (gX σ' ρ))
include hpi hpf hμX

theorem telFits_shaped (σ : Nat → Nat) (as : List PSet.{4}) :
    TelFits (mkM P μX) (σOf ((canonL ar).map (evalTotal σ))) (fd.params ++ fd.indices) ρ0 as ↔
      TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 as :=
  (TelFits_levels (mkM P μX) (σOf_canon σ ar) _ hpi ρ0 as).trans
    (TelFits_agreeOn P hμX σ _ (fun e he => denRefs_ne_of_occurs e (hpf e he)) ρ0 as)

include hX hg hlv

/-- A recursive field's set at fitting arguments: the entry's end there. -/
theorem ed_recApp_fit (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false)
    (hfit : TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ))) :
    Equiv (Ed (mkM P (upd μ fd.fref X)) (den (mkM P (upd μ fd.fref X)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)))
      (Ed (mkM P μ) (gX σ (push (args.map (den (mkM P μ) σ ρ)) ρ0))) := by
  rw [den_recApp P μ X σ ρ hargs, hX]
  refine ed_congr _ ((fapps_fam_fit P μX fd _ (hg _) _ ((telFits_shaped P μ fd ar hpi hpf μX hμX σ _).mpr hfit)).trans ?_)
  exact hlv _ σ (σOf_canon σ ar) _

omit hlv in
/-- A recursive field's set at arguments that do not fit: empty. -/
theorem ed_recApp_nofit (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length)
    (hfit : ¬ TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ))) :
    Equiv (Ed (mkM P (upd μ fd.fref X)) (den (mkM P (upd μ fd.fref X)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)))
      pempty := by
  rw [den_recApp P μ X σ ρ hargs, hX]
  refine (ed_congr _ (fapps_fam_nofit P μX fd _ (hg _) _ (by rw [List.length_map, hl])
    fun h => hfit ((telFits_shaped P μ fd ar hpi hpf μX hμX σ _).mp h))).trans (ed_pempty _)

end Shaped

/-! ### fibres along the iterates -/

theorem stageW4 (P : Premises4) : ∀ k, Stage (W4 k)
  | 0 => stage_univIn.{3, 4} P.c3
  | k + 1 => stage4 P k

theorem dich_el_famEnd (M : Interp.{4}) (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{4}) :
    Dich (El (famEnd M W4 σ fd ρ)) := by
  unfold famEnd cond
  cases M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ => exact (dich_congr el_tyv.symm).mp (dich_tv _)
  | isFalse _ => exact (dich_congr el_tyv.symm).mp (TypeFib_dich M W4 _ σ _ _ _)

theorem ed_famEnd (M M' : Interp.{4}) (hd : M'.dec = M.dec) (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{4}) :
    Equiv (Ed M' (famEnd M W4 σ fd ρ)) (El (famEnd M W4 σ fd ρ)) := by
  have e := ed_of_dich M (dich_el_famEnd M σ fd ρ)
  unfold Ed at e ⊢
  rw [hd, e]
  exact Equiv.rfl

/-- A family fibre lies in the stage of the family's level. -/
theorem el_famEnd_mem (P : Premises4) (μ' : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (fd : FamData)
    (ρ : Nat → PSet.{4}) : El (famEnd (mkM P μ') W4 σ fd ρ) ∈ W4 (evalTotal σ fd.resLevel) := by
  have hW := stageW4 P (evalTotal σ fd.resLevel)
  unfold famEnd cond
  cases (mkM P μ').dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      refine mem_congr_left el_tyv.symm (hW.subset (hW.singleton_mem hW.empty) fun y hy => ?_)
      exact mem_singleton.mpr (mem_tv.mp hy).2
  | isFalse _ => exact mem_congr_left el_tyv.symm (TypeFib_mem _ σ hW _ _ _)

/-- Fibres grow with the field sets. -/
theorem el_famEnd_mono (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {σ : Nat → Nat} {fd : FamData}
    (h : FamLE (mkM P μ₁) (mkM P μ₂) (W4 (evalTotal σ fd.resLevel)) σ fd.ctors) (ρ : Nat → PSet.{4})
    {z : PSet.{4}} (hz : z ∈ El (famEnd (mkM P μ₁) W4 σ fd ρ)) : z ∈ El (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  revert hz
  unfold famEnd cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ => exact fun hz => mem_congr_right el_tyv.symm (PropFib_mono h (mem_congr_right el_tyv hz))
  | isFalse _ => exact fun hz => mem_congr_right el_tyv.symm (TypeFib_mono h (mem_congr_right el_tyv hz))

/-! ### the chain of iterates -/

section Chain

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hcls : ∀ c, c ∈ fd.ctors → ∀ A, A ∈ c.1 → occursConst fd.fref A = false ∨ RecApp fd ar A)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)

theorem hpi_of (hB : FamBounded fd ar) : ExprsBounded ar (fd.params ++ fd.indices) := fun e he => by
  rcases List.mem_append.mp he with h | h
  · exact hB.params e h
  · exact hB.indices e h

/-- The fitting test of a recursive field's arguments. -/
def RecFits (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat)) : Prop :=
  TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 (args.map (den (mkM P μ) σ ρ))

include hB hpf

theorem ed_rec_zero (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length) :
    Equiv (Ed (mkM P (tabIter P μ fd 0)) (den (mkM P (tabIter P μ fd 0)) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))) pempty := by
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
  · exact (ed_recApp_fit P μ fd ar (hpi_of fd ar hB) hpf (famIter P μ fd 0) μ (fun _ _ => tyv pempty) (fun _ => rfl)
      (fun _ _ _ => rfl) (fun _ => envResp_const _) (fun _ _ _ _ => Equiv.rfl) σ ρ args hargs hfit).trans
      (ed_tyv_empty _)
  · exact ed_recApp_nofit P μ fd ar (hpi_of fd ar hB) hpf (famIter P μ fd 0) μ (fun _ _ => tyv pempty) (fun _ => rfl)
      (fun _ _ _ => rfl) (fun _ => envResp_const _) σ ρ args hargs hl hfit

theorem ed_rec_succ_fit (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hfit : RecFits P μ fd σ ρ args) :
    Equiv (Ed (mkM P (tabIter P μ fd (n + 1))) (den (mkM P (tabIter P μ fd (n + 1))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args)))
      (El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd (push (args.map (den (mkM P μ) σ ρ)) ρ0))) :=
  (ed_recApp_fit P μ fd ar (hpi_of fd ar hB) hpf (famIter P μ fd (n + 1)) (tabIter P μ fd n)
    (fun σ => famEnd (mkM P (tabIter P μ fd n)) W4 σ fd) (fun _ => rfl) (agreeOn_upd_off μ fd.fref _)
    (fun σ => famEnd_resp _ W4 σ fd) (fun _ _ h ρ => famEnd_levels _ h W4 fd hB ρ) σ ρ args hargs hfit).trans
    (ed_famEnd _ _ rfl σ fd _)

theorem ed_rec_succ_nofit (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length)
    (hfit : ¬ RecFits P μ fd σ ρ args) :
    Equiv (Ed (mkM P (tabIter P μ fd (n + 1))) (den (mkM P (tabIter P μ fd (n + 1))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))) pempty :=
  ed_recApp_nofit P μ fd ar (hpi_of fd ar hB) hpf (famIter P μ fd (n + 1)) (tabIter P μ fd n)
    (fun σ => famEnd (mkM P (tabIter P μ fd n)) W4 σ fd) (fun _ => rfl) (agreeOn_upd_off μ fd.fref _)
    (fun σ => famEnd_resp _ W4 σ fd) σ ρ args hargs hl hfit

omit hB hpf in
theorem dich_iUnion_famEnd (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Dich (iUnionN fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd ρ)) := by
  unfold famEnd cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      refine Or.inl fun y hy => ?_
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hy
      exact (mem_tv.mp (mem_congr_right el_tyv hn)).2
  | isFalse _ =>
      refine Or.inr fun hy => ?_
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hy
      obtain ⟨j, xs, _, _, _, hz, _⟩ := mem_TypeFib.mp (mem_congr_right el_tyv hn)
      exact dataVal_ne_pempty j xs hz.symm

theorem ed_rec_lim_fit (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hfit : RecFits P μ fd σ ρ args) :
    Equiv (Ed (mkM P (tabLim P μ fd)) (den (mkM P (tabLim P μ fd)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)))
      (iUnionN fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd (push (args.map (den (mkM P μ) σ ρ)) ρ0))) := by
  refine (ed_recApp_fit P μ fd ar (hpi_of fd ar hB) hpf (famLim P μ fd) μ (limEnd P μ fd) (fun _ => rfl)
    (fun _ _ _ => rfl) (limEnd_resp P μ fd) (fun _ _ h ρ => tyv_congr (iUnionN_congr fun n =>
      el_congr (famEnd_levels _ h W4 fd hB ρ))) σ ρ args hargs hfit).trans ?_
  exact ed_tyv _ (dich_iUnion_famEnd P μ fd σ _)

theorem ed_rec_lim_nofit (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length)
    (hfit : ¬ RecFits P μ fd σ ρ args) :
    Equiv (Ed (mkM P (tabLim P μ fd)) (den (mkM P (tabLim P μ fd)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)))
      pempty :=
  ed_recApp_nofit P μ fd ar (hpi_of fd ar hB) hpf (famLim P μ fd) μ (limEnd P μ fd) (fun _ => rfl)
    (fun _ _ _ => rfl) (limEnd_resp P μ fd) σ ρ args hargs hl hfit

end Chain

theorem denRefs_policyPi_mem {r : Nat} (b : Expr Nat) : (D : List (Expr Nat)) → r ∈ denRefs (policyPi D b) →
    (∃ e, e ∈ D ∧ r ∈ denRefs e) ∨ r ∈ denRefs b
  | [], h => Or.inr h
  | A :: D, h => by
      rcases List.mem_append.mp h with h | h
      · exact Or.inl ⟨A, List.mem_cons_self _ _, h⟩
      · rcases denRefs_policyPi_mem b D h with ⟨e, he, hr⟩ | hr
        · exact Or.inl ⟨e, List.mem_cons_of_mem _ he, hr⟩
        · exact Or.inr hr

section Fix

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hcls : ∀ c, c ∈ fd.ctors → ∀ A, A ∈ c.1 → occursConst fd.fref A = false ∨ RecApp fd ar A)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)

include hcls hri in
/-- Fibres grow from `upd μ f X₁` to `upd μ f X₂` when the recursive fields' sets do. -/
theorem famLE_upd (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat)
    (hrec : ∀ ρ args, (∀ e, e ∈ args → occursConst fd.fref e = false) →
      args.length = (fd.params ++ fd.indices).length → ∀ z,
      z ∈ Ed (mkM P (upd μ fd.fref X₁)) (den (mkM P (upd μ fd.fref X₁)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) →
      z ∈ Ed (mkM P (upd μ fd.fref X₂)) (den (mkM P (upd μ fd.fref X₂)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)))
    (hsm : ∀ ρ args, (∀ e, e ∈ args → occursConst fd.fref e = false) →
      args.length = (fd.params ++ fd.indices).length →
      Ed (mkM P (upd μ fd.fref X₂)) (den (mkM P (upd μ fd.fref X₂)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈
        W4 (evalTotal σ fd.resLevel)) :
    FamLE (mkM P (upd μ fd.fref X₁)) (mkM P (upd μ fd.fref X₂)) (W4 (evalTotal σ fd.resLevel)) σ fd.ctors where
  fields := fun c hc A hA ρ z hz => by
    rcases hcls c hc A hA with h0 | ⟨args, rfl, hl, hargs⟩
    · rw [den_off P μ fd.fref X₁ σ ρ h0] at hz
      rw [den_off P μ fd.fref X₂ σ ρ h0]
      exact hz
    · exact hrec ρ args hargs hl z hz
  small := fun c hc A hA ρ hW => by
    rcases hcls c hc A hA with h0 | ⟨args, rfl, hl, hargs⟩
    · rw [den_off P μ fd.fref X₁ σ ρ h0] at hW
      rw [den_off P μ fd.fref X₂ σ ρ h0]
      exact hW
    · exact hsm ρ args hargs hl
  ri := fun c hc e he ρ => by
    rw [den_off P μ fd.fref X₁ σ ρ (hri c hc e he), den_off P μ fd.fref X₂ σ ρ (hri c hc e he)]
    exact Equiv.rfl

include hB hpf

theorem small_rec_iter (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length) :
    Ed (mkM P (tabIter P μ fd n)) (den (mkM P (tabIter P μ fd n)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈
      W4 (evalTotal σ fd.resLevel) := by
  have hW := stageW4 P (evalTotal σ fd.resLevel)
  cases n with
  | zero => exact mem_congr_left (ed_rec_zero P μ fd ar hB hpf σ ρ args hargs hl).symm hW.empty
  | succ n =>
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
      · exact mem_congr_left (ed_rec_succ_fit P μ fd ar hB hpf n σ ρ args hargs hfit).symm
          (el_famEnd_mem P _ σ fd _)
      · exact mem_congr_left (ed_rec_succ_nofit P μ fd ar hB hpf n σ ρ args hargs hl hfit).symm hW.empty

theorem small_rec_lim (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false) (hl : args.length = (fd.params ++ fd.indices).length) :
    Ed (mkM P (tabLim P μ fd)) (den (mkM P (tabLim P μ fd)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈
      W4 (evalTotal σ fd.resLevel) := by
  have hW := stageW4 P (evalTotal σ fd.resLevel)
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
  · exact mem_congr_left (ed_rec_lim_fit P μ fd ar hB hpf σ ρ args hargs hfit).symm
      (stageN_W4 P.c0 P.c1 P.c2 P.c3 _ _ fun n => el_famEnd_mem P _ σ fd _)
  · exact mem_congr_left (ed_rec_lim_nofit P μ fd ar hB hpf σ ρ args hargs hl hfit).symm hW.empty

include hcls hri

/-- The recursive fields' sets grow along the iterates. -/
theorem rec_iter_mono : (n : Nat) → ∀ (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat)),
    (∀ e, e ∈ args → occursConst fd.fref e = false) → args.length = (fd.params ++ fd.indices).length → ∀ z,
    z ∈ Ed (mkM P (tabIter P μ fd n)) (den (mkM P (tabIter P μ fd n)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) →
    z ∈ Ed (mkM P (tabIter P μ fd (n + 1))) (den (mkM P (tabIter P μ fd (n + 1))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args))
  | 0, σ, ρ, args, hargs, hl, z, hz =>
      absurd (mem_congr_right (ed_rec_zero P μ fd ar hB hpf σ ρ args hargs hl) hz) not_mem_pempty
  | n + 1, σ, ρ, args, hargs, hl, z, hz => by
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
      · have h1 := mem_congr_right (ed_rec_succ_fit P μ fd ar hB hpf n σ ρ args hargs hfit) hz
        refine mem_congr_right (ed_rec_succ_fit P μ fd ar hB hpf (n + 1) σ ρ args hargs hfit).symm ?_
        exact el_famEnd_mono P (famLE_upd P μ fd ar hcls hri (famIter P μ fd n) (famIter P μ fd (n + 1)) σ
          (rec_iter_mono n σ) (fun ρ args hargs hl => small_rec_iter P μ fd ar hB hpf (n + 1) σ ρ args hargs hl)) _ h1
      · exact absurd (mem_congr_right (ed_rec_succ_nofit P μ fd ar hB hpf n σ ρ args hargs hl hfit) hz) not_mem_pempty

/-- The iterates form a growing chain with the limit's field sets as their union. -/
theorem famChain_iter (σ : Nat → Nat) :
    FamChain (fun n => mkM P (tabIter P μ fd n)) (mkM P (tabLim P μ fd)) (W4 (evalTotal σ fd.resLevel)) σ fd.ctors where
  step := fun n => famLE_upd P μ fd ar hcls hri (famIter P μ fd n) (famIter P μ fd (n + 1)) σ
    (rec_iter_mono P μ fd ar hB hpf hcls hri n σ)
    (fun ρ args hargs hl => small_rec_iter P μ fd ar hB hpf (n + 1) σ ρ args hargs hl)
  toLim := fun n => famLE_upd P μ fd ar hcls hri (famIter P μ fd n) (famLim P μ fd) σ
    (fun ρ args hargs hl z hz => by
      cases n with
      | zero => exact absurd (mem_congr_right (ed_rec_zero P μ fd ar hB hpf σ ρ args hargs hl) hz) not_mem_pempty
      | succ n =>
          refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
          · refine mem_congr_right (ed_rec_lim_fit P μ fd ar hB hpf σ ρ args hargs hfit).symm ?_
            exact mem_iUnionN.mpr ⟨n, mem_congr_right (ed_rec_succ_fit P μ fd ar hB hpf n σ ρ args hargs hfit) hz⟩
          · exact absurd (mem_congr_right (ed_rec_succ_nofit P μ fd ar hB hpf n σ ρ args hargs hl hfit) hz)
              not_mem_pempty)
    (fun ρ args hargs hl => small_rec_lim P μ fd ar hB hpf σ ρ args hargs hl)
  lim := fun c hc A hA ρ z hz => by
    rcases hcls c hc A hA with h0 | ⟨args, rfl, hl, hargs⟩
    · refine ⟨0, ?_⟩
      have e1 : den (mkM P (tabIter P μ fd 0)) σ ρ A = den (mkM P μ) σ ρ A := den_off P μ fd.fref _ σ ρ h0
      have e2 : den (mkM P (tabLim P μ fd)) σ ρ A = den (mkM P μ) σ ρ A := den_off P μ fd.fref _ σ ρ h0
      rw [e2] at hz
      show z ∈ Ed (mkM P (tabIter P μ fd 0)) _
      rw [e1]
      exact hz
    · refine @Decidable.byCases _ _ (P.dec (RecFits P μ fd σ ρ args)) (fun hfit => ?_) (fun hfit => ?_)
      · obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (ed_rec_lim_fit P μ fd ar hB hpf σ ρ args hargs hfit) hz)
        exact ⟨n + 1, mem_congr_right (ed_rec_succ_fit P μ fd ar hB hpf n σ ρ args hargs hfit).symm hn⟩
      · exact absurd (mem_congr_right (ed_rec_lim_nofit P μ fd ar hB hpf σ ρ args hargs hl hfit) hz) not_mem_pempty
  limSmall := fun c hc A hA ρ hW n => by
    rcases hcls c hc A hA with h0 | ⟨args, rfl, hl, hargs⟩
    · have e1 : den (mkM P (tabIter P μ fd n)) σ ρ A = den (mkM P μ) σ ρ A := den_off P μ fd.fref _ σ ρ h0
      have e2 : den (mkM P (tabLim P μ fd)) σ ρ A = den (mkM P μ) σ ρ A := den_off P μ fd.fref _ σ ρ h0
      rw [e2] at hW
      show Ed (mkM P (tabIter P μ fd n)) _ ∈ _
      rw [e1]
      exact hW
    · exact small_rec_iter P μ fd ar hB hpf n σ ρ args hargs hl

/-- The limit's end is the family's end read at the limit table. -/
theorem famEnd_lim_fix (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (famEnd (mkM P (tabLim P μ fd)) W4 σ fd ρ) (limEnd P μ fd σ ρ) := by
  have hC := famChain_iter P μ fd ar hB hpf hcls hri σ
  unfold limEnd famEnd cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      refine tyv_congr (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
      · obtain ⟨n, hn⟩ := (PropFib_lim hC).mp hz
        exact mem_iUnionN.mpr ⟨n, mem_congr_right el_tyv.symm hn⟩
      · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
        exact (PropFib_lim hC).mpr ⟨n, mem_congr_right el_tyv hn⟩
  | isFalse _ =>
      refine tyv_congr (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
      · obtain ⟨n, hn⟩ := (TypeFib_lim hC rfl).mp hz
        exact mem_iUnionN.mpr ⟨n, mem_congr_right el_tyv.symm hn⟩
      · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
        exact (TypeFib_lim hC rfl).mpr ⟨n, mem_congr_right el_tyv hn⟩

/-- **The limit is a fixed point**: the family's value read at the table with
the limit at the family is the limit. -/
theorem famLim_fix (vs : List Nat) :
    Equiv (famVal (mkM P (tabLim P μ fd)) W4 (σOf vs) fd) (famLim P μ fd vs) :=
  piLam_agreeOn P (agreeOn_upd_off μ fd.fref (famLim P μ fd)) (σOf vs) (famEnd_resp _ W4 _ fd)
    (famEnd_lim_fix P μ fd ar hB hpf hcls hri (σOf vs)) (famType fd)
    (fun r hr => by
      rcases denRefs_policyPi_mem _ _ hr with ⟨e, he, hre⟩ | hr'
      · exact denRefs_ne_of_occurs e (hpf e he) r hre
      · exact absurd hr' (List.not_mem_nil _)) ρ0

end Fix

/-! ### tables pointwise-`≈` on the references read -/

section TablesOn

variable (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
  (h : ∀ r, S r → ∀ ls, Equiv (μ₁ r ls) (μ₂ r ls))
include h

theorem denLit_tablesOn : (t : Nat) → (∀ r, r ∈ denRefsLit t → S r) →
    Equiv (denLit (mkM P μ₁) t) (denLit (mkM P μ₂) t)
  | 0, hr => h 1 (hr 1 (List.mem_singleton_self 1)) []
  | t + 1, hr => fapp_congr (h 2 (hr 2 (List.mem_cons_self 2 _)) [])
      (denLit_tablesOn t fun r h' => hr r (List.mem_cons_of_mem _ h'))

theorem den_tablesOn (σ : Nat → Nat) : (e : Expr Nat) → (∀ r, r ∈ denRefs e → S r) →
    ∀ {ρ ρ' : Nat → PSet.{4}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ' e)
  | .bvar i, _, _, _, hρ => hρ i
  | .sort _, _, _, _, _ => Equiv.rfl
  | .const r _, hr, _, _, _ => h r (hr r (List.mem_singleton_self r)) _
  | .app f a, hr, _, _, hρ =>
      fapp_congr (den_tablesOn σ f (fun r h' => hr r (List.mem_append_left _ h')) hρ)
        (den_tablesOn σ a (fun r h' => hr r (List.mem_append_right _ h')) hρ)
  | .lam A b, hr, _, _, hρ =>
      lamVal_congr (mkM P μ₂) (den_tablesOn σ A (fun r h' => hr r (List.mem_append_left _ h')) hρ)
        (fun _ _ hx => den_tablesOn σ b (fun r h' => hr r (List.mem_append_right _ h')) (vcons_congr hx hρ))
  | .pi A B, hr, _, _, hρ =>
      piVal_congr (mkM P μ₂) (den_tablesOn σ A (fun r h' => hr r (List.mem_append_left _ h')) hρ)
        (fun _ _ hx => den_tablesOn σ B (fun r h' => hr r (List.mem_append_right _ h')) (vcons_congr hx hρ))
  | .letE a v b, hr, _, _, hρ =>
      den_tablesOn σ b (fun r h' => hr r (List.mem_append_right _ h'))
        (vcons_congr (den_tablesOn σ v (fun r h' => hr r (List.mem_append_left _ (List.mem_append_right _ h'))) hρ) hρ)
  | .lit t, hr, _, _, _ => denLit_tablesOn P h t hr

theorem piLam_tablesOn (σ : Nat → Nat) {g₁ g₂ : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g₁)
    (hgg : ∀ ρ, Equiv (g₁ ρ) (g₂ ρ)) : (e : Expr Nat) → (∀ r, r ∈ denRefs e → S r) → (ρ : Nat → PSet.{4}) →
    Equiv (piLam (mkM P μ₁) σ g₁ ρ e) (piLam (mkM P μ₂) σ g₂ ρ e)
  | .pi A B, hr, ρ => lamVal_congr (mkM P μ₂)
      (den_tablesOn P h σ A (fun r h' => hr r (List.mem_append_left _ h')) (fun _ => Equiv.rfl)) fun _ x' hx =>
      (piLam_congr (mkM P μ₁) σ hg B (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))).trans
        (piLam_tablesOn σ hg hgg B (fun r h' => hr r (List.mem_append_right _ h')) (vcons x' ρ))
  | .bvar _, _, ρ => hgg ρ
  | .sort _, _, ρ => hgg ρ
  | .const _ _, _, ρ => hgg ρ
  | .app _ _, _, ρ => hgg ρ
  | .lam _ _, _, ρ => hgg ρ
  | .letE _ _ _, _, ρ => hgg ρ
  | .lit _, _, ρ => hgg ρ

theorem famLE_tablesOn (W : PSet.{4}) (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (hcs : ∀ c, c ∈ cs → RefsIn S c.1 ∧ RefsIn S c.2) : FamLE (mkM P μ₁) (mkM P μ₂) W σ cs where
  fields := fun c hc A hA _ _ hz =>
    mem_congr_right (ed_congr (mkM P μ₂) (den_tablesOn P h σ A ((hcs c hc).1 A hA) (fun _ => Equiv.rfl))) hz
  small := fun c hc A hA _ hW =>
    mem_congr_left (ed_congr (mkM P μ₂) (den_tablesOn P h σ A ((hcs c hc).1 A hA) (fun _ => Equiv.rfl))) hW
  ri := fun c hc e he _ => den_tablesOn P h σ e ((hcs c hc).2 e he) (fun _ => Equiv.rfl)

theorem famEnd_tablesOn (σ : Nat → Nat) (fd : FamData) (hcs : ∀ c, c ∈ fd.ctors → RefsIn S c.1 ∧ RefsIn S c.2)
    (ρ : Nat → PSet.{4}) : Equiv (famEnd (mkM P μ₁) W4 σ fd ρ) (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  have h' : ∀ r, S r → ∀ ls, Equiv (μ₂ r ls) (μ₁ r ls) := fun r hr ls => (h r hr ls).symm
  unfold famEnd cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => PropFib_mono (famLE_tablesOn P h (W4 0) σ fd.ctors hcs) hz,
        fun hz => PropFib_mono (famLE_tablesOn P h' (W4 0) σ fd.ctors hcs) hz⟩)
  | isFalse _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => TypeFib_mono (famLE_tablesOn P h _ σ fd.ctors hcs) hz,
        fun hz => TypeFib_mono (famLE_tablesOn P h' _ σ fd.ctors hcs) hz⟩)

omit h in
theorem famType_refs (fd : FamData) (hpi : RefsIn S (fd.params ++ fd.indices)) :
    ∀ r, r ∈ denRefs (famType fd) → S r := fun r hr => by
  rcases denRefs_policyPi_mem _ _ hr with ⟨e, he, hre⟩ | hr'
  · exact hpi e he r hre
  · exact absurd hr' (List.not_mem_nil _)

end TablesOn

/-- The limit reads the table only at the family's references other than the family. -/
theorem famLim_agreeOn (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
    (h : ∀ r, S r → ∀ ls, Equiv (μ₁ r ls) (μ₂ r ls)) (fd : FamData) (hpi : RefsIn S (fd.params ++ fd.indices))
    (hfam : FamRefsIn (fun r => S r ∨ r = fd.fref) fd) (vs : List Nat) :
    Equiv (famLim P μ₁ fd vs) (famLim P μ₂ fd vs) := by
  have hpi' : RefsIn (fun r => S r ∨ r = fd.fref) (fd.params ++ fd.indices) := fun e he r hr => Or.inl (hpi e he r hr)
  have hIter : ∀ n vs, Equiv (famIter P μ₁ fd n vs) (famIter P μ₂ fd n vs) := by
    intro n
    induction n with
    | zero => exact fun vs => piLam_tablesOn P h _ (envResp_const _) (fun _ => Equiv.rfl) _ (famType_refs fd hpi) ρ0
    | succ n ih =>
        intro vs
        have hT : ∀ r, (S r ∨ r = fd.fref) → ∀ ls, Equiv (upd μ₁ fd.fref (famIter P μ₁ fd n) r ls)
            (upd μ₂ fd.fref (famIter P μ₂ fd n) r ls) := by
          intro r hr ls
          by_cases hrf : r = fd.fref
          · subst hrf; rw [upd_eq, upd_eq]; exact ih ls
          · rw [upd_ne _ _ _ hrf, upd_ne _ _ _ hrf]
            rcases hr with hr | hr
            · exact h r hr ls
            · exact absurd hr hrf
        exact piLam_tablesOn P hT _ (famEnd_resp _ W4 _ fd) (famEnd_tablesOn P hT _ fd hfam) _
          (famType_refs fd hpi') ρ0
  have hTab : ∀ n, ∀ r, (S r ∨ r = fd.fref) → ∀ ls, Equiv (tabIter P μ₁ fd n r ls) (tabIter P μ₂ fd n r ls) := by
    intro n r hr ls
    show Equiv (upd μ₁ fd.fref (famIter P μ₁ fd n) r ls) (upd μ₂ fd.fref (famIter P μ₂ fd n) r ls)
    by_cases hrf : r = fd.fref
    · subst hrf; rw [upd_eq, upd_eq]; exact hIter n ls
    · rw [upd_ne _ _ _ hrf, upd_ne _ _ _ hrf]
      rcases hr with hr | hr
      · exact h r hr ls
      · exact absurd hr hrf
  exact piLam_tablesOn P h _ (limEnd_resp P μ₁ fd _)
    (fun ρ => tyv_congr (iUnionN_congr fun n => el_congr (famEnd_tablesOn P (hTab n) _ fd hfam ρ)))
    _ (famType_refs fd hpi) ρ0

end PSet

end Rcic.F3
