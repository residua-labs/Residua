import rcic.RcicF3PendAWGroup
import rcic.RcicF3KTWFamKT

/-!
# A W-closed replacement for the finite-stage family entry

The concrete entry tested here is `famKT`: the Prop fixed point at result
level zero and the guarded-W least fixed point at Type levels. The tests
use the literal admitted `PendAW.recA`, its valid infinite small parameter,
and the same `fxZW` that refutes the old `StepAG` interpretation.

This is a family-entry result. It does not assert `GInv` or a group step.
The new target and its remaining consumers are tracked separately.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.PendAFamily
open Rcic.Declarative
open PendAWBridge (fd rp)

/-- The actual Type-stage W fixed point contains every finite iterate. -/
theorem finite_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Sub (iterPhiUnion P μ fd fxσ rp) (DStar P μ fd fxσ rp) := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  exact iterPhi_le (PendAWLim.Typed.nonIR P μ) fxσ rp
    (PendAWLim.Typed.typeRead fxσ) (n + 1) z hn

/-- Every W value at this no-index family has the empty index tuple. -/
theorem resultTuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {z : PSet.{4}} (hz : z ∈ DStar P μ fd fxσ rp) :
    Equiv (resTupF P μ fd fxσ rp z) (ordPair pempty (tup [])) := by
  have hp := (DStar_lfp P μ fd fxσ rp (PendAWLim.Typed.typeRead fxσ)
    (PendAWLim.Typed.nonIR P μ fxσ rp)).1.2.1 z hz
  obtain ⟨i, ⟨j, c, xs, hcj, hid, hIn⟩, hiz⟩ := mem_sep.mp hp
  have hl : xs.length = c.1.length :=
    (Sem.InPhi.length _ (kindsOf fd.fref c.1) xs 0 [] hIn).trans (List.length_map _ _)
  have he := resTupF_dataVal P μ fd fxσ rp hcj hl (hiz.symm.trans hid)
  have hc0 : c.2 = [] := List.length_eq_zero.mp
    (PendAWLim.Typed.indicesLen c (List.getElem?_mem hcj))
  simpa only [hc0, List.map_nil] using he

/-- At this no-index family, the index guard retains the entire W set. -/
theorem fibreFull (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (fibAt P μ fd (DStar P μ fd) fxσ rp []) (DStar P μ fd fxσ rp) := by
  apply ext; intro z
  constructor
  · exact mem_sep_subset
  · intro hz
    obtain ⟨i, hi⟩ := hz
    exact mem_sep.mpr ⟨i, resultTuple P μ ⟨i, Equiv.rfl⟩, hi⟩

/-- Applying the replacement entry to the exact valid W parameter reads
the guarded-W fixed point, rather than the union of finite stages. -/
theorem fibre_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (El (fapps (famKT P μ fd []) [tyv fxS])) (DStar P μ fd fxσ rp) := by
  have hk : evalTotal (σOf []) fd.resLevel ≠ 0 := PendAWLim.Typed.typeRead _
  unfold famKT
  rw [if_neg hk]
  have hx : TelFits (mkM P μ) fxσ (fd.params ++ fd.indices) ρ0 [tyv fxS] :=
    PendAWBridge.argsFit P μ pempty
  have hb := fapps_piLam (mkM P μ) fxσ
    (famEndD_envResp P μ fd (DStar P μ fd)
      (fun σ _ _ h => DStar_env P μ fd (PendAWLim.Typed.nonIR P μ) σ h) fxσ)
    (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 [tyv fxS] hx
  exact (el_congr hb).trans (el_tyv.trans (fibreFull P μ))

/-- The height-omega value missing from `famLim` belongs to the new entry. -/
theorem heightOmega (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ El (fapps (famKT P μ fd []) [tyv fxS]) := by
  apply mem_congr_right (fibre_eq P μ).symm
  exact (DStar_lfp P μ fd fxσ rp (PendAWLim.Typed.typeRead fxσ)
    (PendAWLim.Typed.nonIR P μ fxσ rp)).1.1 _
      (PsiF_mono P μ fd fxσ rp (finite_sub P μ) _ (PendAWBridge.heightOmega P μ).1)

/-- The literal replacement fibre is constructor-closed at the exact
parameter where the landed finite-stage fibre fails closure. -/
theorem closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Sub (PsiF P μ fd fxσ rp (El (fapps (famKT P μ fd []) [tyv fxS])))
      (El (fapps (famKT P μ fd []) [tyv fxS])) := by
  intro z hz
  apply mem_congr_right (fibre_eq P μ).symm
  exact (DStar_lfp P μ fd fxσ rp (PendAWLim.Typed.typeRead fxσ)
    (PendAWLim.Typed.nonIR P μ fxσ rp)).1.1 z
      (PsiF_mono P μ fd fxσ rp (fun x hx => mem_congr_right (fibre_eq P μ) hx) z hz)

/-- The full family fixed-point equation at the admitted W descriptor.
All of the landed class-A prerequisites are paid by this fixture. -/
theorem fixed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat) :
    Equiv (famVal (mkM P (tabKT P μ fd)) W4 (σOf vs) fd) (famKT P μ fd vs) := by
  exact tabKT_fix P μ fd 0 (PendAWLim.Typed.nonIR P μ) PendAWLim.Typed.bounded
    PendAWLim.Typed.paramsFree PendAWLim.Typed.classes PendAWLim.Typed.indicesFree
    PendAWLim.Typed.indicesLen PendAWLim.Typed.fresh vs

/-- Local non-refutability of the repaired closure wall, conditional on
the supplied model data. This statement does not quantify `StepAG`. -/
theorem closure_nonrefutable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ¬ (Sub (PsiF P μ fd fxσ rp (El (fapps (famKT P μ fd []) [tyv fxS])))
      (El (fapps (famKT P μ fd []) [tyv fxS])) → (Premises4 → False)) := by
  intro h
  exact h (closed P μ) P

end Rcic.F3.PSet.PendAFamily
