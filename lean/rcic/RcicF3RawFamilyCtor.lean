import rcic.RcicF3RawFamilyLaws
import rcic.RcicF3KTWRecMem
/-! Literal data-constructor bridge for the raw family role. The theorem
keeps hereditarily typed results, stage bounds and candidate closure visible
as component inputs. It introduces no raw shape, reference-label, or product
depth restriction. Producing those inputs from admission remains open.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex

theorem table_equiv (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame)
    (hf : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd C vs)) :
    ∀ r vs, Equiv (μ r vs) (table P μ fd C r vs) := by
  intro r vs
  unfold table
  by_cases hr : r = fd.fref
  · subst r
    rw [upd_eq]
    exact hf vs
  · rw [upd_ne _ _ _ hr]
    exact Equiv.rfl
theorem smallAlong_tables (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}}
    (h : ∀ r vs, Equiv (μ₁ r vs) (μ₂ r vs)) (σ : Nat → Nat) (W : PSet.{4}) :
    ∀ Ds ρ xs, SmallAlong (mkM P μ₁) σ W Ds ρ xs ↔
      SmallAlong (mkM P μ₂) σ W Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil => intro ρ xs; exact Iff.rfl
  | cons A Ds ih =>
      intro ρ xs
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs =>
          have he := ed_congr (mkM P μ₂)
            (den_tables P h σ A (ρ := ρ) (ρ' := ρ) (fun _ => Equiv.rfl))
          exact and_congr ⟨fun hx => mem_congr_left he hx,
            fun hx => mem_congr_left he.symm hx⟩ (ih _ _)
theorem telFits_prefix (M : Interp.{4}) (σ : Nat → Nat) :
    ∀ Ds Es ρ xs ys, xs.length = Ds.length →
      TelFits M σ (Ds ++ Es) ρ (xs ++ ys) → TelFits M σ Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil =>
      intro Es ρ xs ys hl _
      cases xs with
      | nil => exact True.intro
      | cons _ _ => cases hl
  | cons A Ds ih =>
      intro Es ρ xs ys hl h
      cases xs with
      | nil => cases hl
      | cons x xs =>
          exact ⟨h.1, ih Es (vcons x ρ) xs ys (Nat.succ.inj hl) h.2⟩
theorem ctor_end_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hc : Closed P μ fd C)
    (hf : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd C vs))
    (vs : List Nat) (j : Fin fd.ctors.length) (ps xs : List PSet.{4})
    (hp : TelFits (mkM P μ) (σOf vs) fd.params ρ0 ps)
    (hx : TelFits (mkM P μ) (σOf vs) (fd.ctors.get j).1 (push ps ρ0) xs)
    (hs : evalTotal (σOf vs) fd.resLevel ≠ 0 →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel))
        (fd.ctors.get j).1 (push ps ρ0) xs) :
    ctorEnd (mkM P μ) (σOf vs) fd j.val xs.length (push (ps ++ xs) ρ0) ∈
      C vs (key (ps ++ (fd.ctors.get j).2.map
        (den (mkM P μ) (σOf vs) (push xs (push ps ρ0))))) := by
  have he := table_equiv P μ fd C hf
  apply hc
  refine ⟨j, ps, xs, (TelFits_tables_equiv P he _ _ _ _).mp hp,
    (TelFits_tables_equiv P he _ _ _ _).mp hx, ?_, ?_, ?_⟩
  · split
    · trivial
    · exact (smallAlong_tables P he _ _ _ _ _).mp (hs ‹_›)
  · exact (key_eq_iff _ _).mpr (LEq_append (LEq.refl ps)
      (LEq_map_den_tables _ (fun e _ => den_tables P he _ e (fun _ => Equiv.rfl))))
  · unfold ctorEnd cond
    rw [push_append, lastVals_push]
    cases h : P.dec (evalTotal (σOf vs) fd.resLevel = 0) with
    | isTrue h0 => simp only [if_pos h0]; exact Equiv.rfl
    | isFalse h0 => simp only [if_neg h0]; exact Equiv.rfl
/-- Literal stored data constructor, with no raw-shape or label walls.
Closure and stage bounds are component obligations to be produced from typing. -/
theorem ctor_value_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C)
    (vs : List Nat) (j : Nat) (cps fs ri : List (Expr Nat))
    (hj : fd.ctors[j]? = some (fs, ri)) (hnp : cps.length = fd.params.length)
    (hq : ri.length = fd.indices.length)
    (hf : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd C vs))
    (htyp : ∀ zs, TelFits (mkM P μ) (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0) (foldApps
        (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs,
      TelFits (mkM P μ) (σOf vs) cps ρ0 ps →
      TelFits (mkM P μ) (σOf vs) fs (push ps ρ0) xs →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel))
        fs (push ps ρ0) xs) :
    piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j fs.length) ρ0
      (policyPi (cps ++ fs) (foldApps
        (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri))) ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (policyPi (cps ++ fs)
        (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
          (policyParameterLocals cps.length fs.length ++ ri)))) := by
  let M := mkM P μ
  refine piLam_mem M _ (ctorEnd_resp M _ fd j fs.length) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, xs, rfl, hps, hxs⟩ := TelFits_split cps fs ρ0 zs hz
  have hpl : ps.length = cps.length := hps.length
  have hxl : xs.length = fs.length := hxs.length
  have hR : Equiv (den M (σOf vs) (push (ps ++ xs) ρ0) (foldApps
      (.const fd.fref ((List.range vs.length).map Level.param))
      (policyParameterLocals cps.length fs.length ++ ri)))
      (fapps (ofFrame P μ fd C vs)
        (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0))))) := by
    rw [den_foldApps, List.map_append, ← hpl, ← hxl, den_paramLocals]
    change Equiv (fapps (μ fd.fref (((List.range vs.length).map Level.param).map
      (evalTotal (σOf vs)))) _) _
    rw [map_param_σOf, push_append]
    exact fapps_congr (hf vs) _
  obtain ⟨v, hv0⟩ := htyp (ps ++ xs) hz
  have hv := mem_congr_left hR hv0
  have hne := ne_of_mem_sort (M := M) rfl hv
  have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0
      (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0)))) :=
    fits_of_fapps_ne M (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 _
      (by rw [List.length_append, List.length_append, List.length_map, hpl, hnp, hq]) hne
  have he := hR.trans (apply_ofFrame P μ fd C vs _ hfit)
  refine mem_congr_right ((ed_congr M he).trans
    (ed_tyv M (admissible_dich hC vs _))).symm ?_
  obtain ⟨hjl, hjg⟩ := List.getElem?_eq_some_iff.mp hj
  have hget : fd.ctors.get ⟨j, hjl⟩ = (fs, ri) := hjg
  have hp : TelFits M (σOf vs) fd.params ρ0 ps :=
    telFits_prefix M (σOf vs) fd.params fd.indices ρ0 ps _ (hpl.trans hnp) hfit
  have hh := ctor_end_mem P μ fd C hc hf vs ⟨j, hjl⟩ ps xs hp
    (by rw [hget]; exact hxs)
    (by rw [hget]; exact fun h0 => hsmall h0 ps xs hps hxs)
  rw [hget] at hh
  rw [← hxl]
  exact hh
end Rcic.F3.PSet.RawFamily
