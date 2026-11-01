import rcic.RcicF3RawFamilyCtor
import rcic.RcicF3DTransfer

/-!
# A small closed frame for normalized finite recursive fields

The existing finite-stage family construction is lifted to the complete
quotient-valued parameter/index key. The candidate is allowed to contain
values at unused keys; its constructor closure retains the exact result
key and does not add a result-index fitting premise.

Its size and proof/data face hold at every universe vector. Closure uses
the existing finite-stage fixed-point theorem for family-free or direct
recursive fields. These syntactic premises will be supplied by the actual
normalized no-PendA cache. No equality of raw and normalized invariants,
semantic normalization callback, or new checked condition occurs here.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.RawFiniteFrame
open Rcic.Declarative PiIndex RawFamily

def fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) : PSet.{4} :=
  iUnionN fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd ρ)

theorem fibre_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    fibre P μ fd σ ρ ∈ W4 (evalTotal σ fd.resLevel) :=
  stageN_W4 P.c0 P.c1 P.c2 P.c3 _ _
    (fun n => el_famEnd_mem P (tabIter P μ fd n) σ fd ρ)

theorem fibre_resp (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) : EnvResp (fibre P μ fd σ) := by
  intro ρ ρ' hρ
  exact iUnionN_congr fun n =>
    el_congr (famEnd_resp (mkM P (tabIter P μ fd n)) W4 σ fd ρ ρ' hρ)

theorem fibre_prop (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (h0 : evalTotal σ fd.resLevel = 0)
    (ρ : Nat → PSet.{4}) (z : PSet.{4})
    (hz : z ∈ fibre P μ fd σ ρ) : Equiv z pempty := by
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  unfold famEnd at hn
  rw [cond_pos h0] at hn
  exact (mem_tv.mp (mem_congr_right el_tyv hn)).2

theorem fibre_data (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (h0 : evalTotal σ fd.resLevel ≠ 0)
    (ρ : Nat → PSet.{4}) (z : PSet.{4})
    (hz : z ∈ fibre P μ fd σ ρ) : ¬ Equiv z pempty := by
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  unfold famEnd at hn
  rw [cond_neg h0] at hn
  obtain ⟨j, xs, _c, _hc, _hf, he, _hs⟩ :=
    mem_TypeFib.mp (mem_congr_right el_tyv hn)
  exact fun hz0 => dataVal_ne_pempty j xs (he.symm.trans hz0)

/-- Separation descends to an extensional key without choosing a list
representative. No fitting test is imposed on output indices. -/
def candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Frame := fun vs i =>
  sep (fun z => ∃ xs : List PSet.{4}, key xs = i ∧
    z ∈ fibre P μ fd (σOf vs) (push xs ρ0))
    (W4 (evalTotal (σOf vs) fd.resLevel))

theorem candidate_key (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) (xs : List PSet.{4}) :
    Equiv (candidate P μ fd vs (key xs))
      (fibre P μ fd (σOf vs) (push xs ρ0)) := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨j, ⟨ys, hys, hy⟩, hj⟩ := mem_sep.mp hz
    have he := fibre_resp P μ fd (σOf vs) _ _
      (push_congr ((key_eq_iff ys xs).mp hys)
        (ρ := ρ0) (ρ' := ρ0) (fun _ => Equiv.rfl))
    exact mem_congr_right he (mem_congr_left hj hy)
  · intro hz
    obtain ⟨j, hj⟩ := (stageW4 P _).trans
      (fibre_mem P μ fd (σOf vs) (push xs ρ0)) hz
    exact mem_sep.mpr ⟨j, ⟨xs, rfl, mem_congr_left hj.symm hz⟩, hj⟩

theorem candidate_admissible (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) :
    Admissible fd (candidate P μ fd) := by
  intro vs i
  refine Quotient.inductionOn i ?_
  intro xs
  have he := candidate_key P μ fd vs xs
  refine ⟨mem_congr_left he.symm
    (fibre_mem P μ fd (σOf vs) (push xs ρ0)), ?_⟩
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [if_pos h0]
    exact fun z hz => fibre_prop P μ fd (σOf vs) h0 _ z
      (mem_congr_right he hz)
  · rw [if_neg h0]
    exact fun z hz => fibre_data P μ fd (σOf vs) h0 _ z
      (mem_congr_right he hz)

/-- At complete fitting applications the candidate abstracts to the
existing finite limit. This equality retains the entire universe vector. -/
theorem of_candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) :
    Equiv (ofFrame P μ fd (candidate P μ fd) vs) (famLim P μ fd vs) := by
  unfold ofFrame famLim famType
  apply piLam_congr_fits (mkM P μ) (σOf vs) (.sort fd.resLevel)
    (fun _ _ h => Expr.noConfusion h) (fd.params ++ fd.indices) ρ0
  intro xs hxs
  change Equiv (tyv (candidate P μ fd vs
    (key (lastVals (fd.params.length + fd.indices.length) (push xs ρ0)))))
    (tyv (fibre P μ fd (σOf vs) (push xs ρ0)))
  have hl : fd.params.length + fd.indices.length = xs.length := by
    rw [hxs.length, List.length_append]
  rw [hl, lastVals_push]
  exact tyv_congr (candidate_key P μ fd vs xs)

theorem candidate_table (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : ∀ r vs,
    Equiv (table P μ fd (candidate P μ fd) r vs) (tabLim P μ fd r vs) := by
  intro r vs
  unfold table tabLim
  by_cases hr : r = fd.fref
  · subst r
    rw [upd_eq, upd_eq]
    exact of_candidate P μ fd vs
  · rw [upd_ne _ _ _ hr, upd_ne _ _ _ hr]
    exact Equiv.rfl

/-- The exact finite candidate is constructor closed. Result-index counts
are a syntactic admission fact, not a semantic fitting requirement. -/
theorem candidate_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (hcount : ∀ c ∈ fd.ctors, c.2.length = fd.indices.length) :
    Closed P μ fd (candidate P μ fd) := by
  intro vs i z hctor
  obtain ⟨j, ps, xs, _hp, hx, hs, hi, hz⟩ := hctor
  let M := mkM P (table P μ fd (candidate P μ fd))
  let is := (fd.ctors.get j).2.map (den M (σOf vs) (push xs (push ps ρ0)))
  have hc : fd.ctors.get j ∈ fd.ctors := List.getElem_mem j.isLt
  have his : is.length = fd.indices.length :=
    (List.length_map _ _).trans (hcount _ hc)
  change i = key (ps ++ is) at hi
  rw [hi]
  apply mem_congr_right (candidate_key P μ fd vs (ps ++ is)).symm
  have hcf : CtorFits M (σOf vs) fd.ctors (push ps ρ0) is j.val xs :=
    ⟨fd.ctors.get j, List.getElem?_eq_getElem j.isLt, hx, LEq.refl _⟩
  have hm : z ∈ El (famEnd M W4 (σOf vs) fd (push (ps ++ is) ρ0)) := by
    unfold famEnd
    rw [push_append, ← his, shiftρ_push, lastVals_push]
    by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · rw [cond_pos h0]
      rw [if_pos h0] at hz
      exact mem_congr_right el_tyv.symm
        (mem_tv.mpr ⟨⟨j.val, xs, hcf⟩, hz⟩)
    · rw [cond_neg h0]
      rw [if_neg h0] at hs hz
      exact mem_congr_right el_tyv.symm
        (mem_TypeFib.mpr ⟨j.val, xs, fd.ctors.get j,
          List.getElem?_eq_getElem j.isLt, hcf, hz, hs⟩)
  have he := (famEnd_tables P (candidate_table P μ fd) (σOf vs) fd
    (push (ps ++ is) ρ0)).trans
    (famEnd_lim_fix P μ fd ar hB hpf hcls hri (σOf vs) (push (ps ++ is) ρ0))
  have hzlim := mem_congr_right (el_congr he) hm
  change z ∈ El (tyv (fibre P μ fd (σOf vs) (push (ps ++ is) ρ0))) at hzlim
  exact mem_congr_right el_tyv hzlim

theorem raw_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (hcount : ∀ c ∈ fd.ctors, c.2.length = fd.indices.length) :
    Admissible fd (frame P μ fd) :=
  frame_admissible P μ fd
    ⟨candidate P μ fd, candidate_admissible P μ fd,
      candidate_closed P μ fd ar hB hpf hcls hri hcount⟩

end Rcic.F3.PSet.RawFiniteFrame
