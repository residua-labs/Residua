import rcic.RcicF3PendAWFixture
import rcic.RcicF3FamKTFnReal
/-!
# The finite-stage obstruction at the typed parameterized W descriptor

`closure_claim = 0`.

`fd` is extracted from the admitted `PendAW.recA`; `rp` instantiates its
parameter with the landed infinite small set `fxS`. `argsFit` checks this
universe argument, for every table `μ`. No axiom-domain table entry is used.
`psiEq`, `iterEq` and `unionEq` transport the landed height-omega witness
through the one-step operator and every finite stage. `heightOmega` and
`fnContUnion_false` therefore pin failure of finite-stage closure at this
actual typed family descriptor, independently of the interpretation table.

This does not refute `StepAG_PendA`. The follow-up `RcicF3PendAWLim`
identifies this union with the literal `famLim` fibre. Paying the full
`FaithfulR`, `GInv`, walk and bound premises remains open. This module does
rule out assuming `FnContUnion` for all typed PendA groups.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
namespace Rcic.F3.PSet.PendAWBridge
open Rcic.Declarative
abbrev fd : FamData := famDataOf PendAW.recA
abbrev rp : Nat → PSet.{4} := vcons (tyv fxS) ρ0
kernel_rfl_theorem fdExact :
  fd = ⟨4, [.sort (.succ .zero)], [], .succ .zero,
    [([], []), ([PendAW.field], [])], .anySort⟩
theorem domEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
  domBigF P μ fd fxσ rp [PendAW.field] 0 [] = fxDomBig P := rfl
theorem argsFit (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (y : PSet.{4}) :
  argsFitF P μ fd fxσ (vcons y rp) (.app (.const 4 []) (.bvar 1)) := by
  change tyv fxS ∈ Ed (mkM P μ) (tyv (U W4 1)) ∧ True
  refine ⟨?_, trivial⟩
  apply mem_congr_right (ed_tyv (mkM P μ) (U4_dich 1)).symm
  exact ((P.good (mkM P μ) rfl).U_iff (k := 1) (by decide) (tyv fxS)).mpr
    ⟨fxS, ⟨fx_fxS_mem P, fx_dich⟩, Equiv.rfl⟩
theorem resEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (z : PSet.{4}) :
    resTupF P μ fd fxσ rp z = resTupF P fxμ fxFd fxσ fxρp z := by
  unfold resTupF
  have hl : fd.ctors.length = 2 := rfl
  rw [hl, fxFd_ctors_len]
  rw [findIdx_of_dec (M := mkM P fxμ) (M' := mkM P μ) rfl]
  cases findIdx (mkM P μ) (fun j => Equiv (tagOf z) (ord j)) 2 with
  | none => rfl
  | some j => cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
theorem recEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (y : PSet.{4}) :
    recTupF P μ fd fxσ rp [PendAW.field] 0 [] y =
      ordPair pempty (tup []) := by
  change cond P.dec (fxDomEF P ∈ W4 1)
    (recTupAt P μ fd fxσ (vcons y rp) (.app (.const 4 []) (.bvar 1)))
    (singleton pempty) = _
  have hsmall : fxDomEF P ∈ W4 1 := fx_domEF_mem P
  rw [cond_pos hsmall]
  unfold recTupAt
  rw [cond_pos (argsFit P μ y)]
  rfl
theorem fibEq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X y : PSet.{4}) :
    Equiv ((semF P μ fd fxσ rp [PendAW.field]).fib X 0 [] y)
      ((semF P fxμ fxFd fxσ fxρp fxNode.1).fib X 0 [] y) := by
  have ht : Equiv (recTupF P μ fd fxσ rp [PendAW.field] 0 [] y)
      (recTupF P fxμ fxFd fxσ fxρp fxNode.1 0 [] y) := by
    rw [recEq P μ y]
    exact (fx_recTup P y).symm
  apply sep_congr _ _ Equiv.rfl
  · intro a b hab h
    change Equiv (resTupF P fxμ fxFd fxσ fxρp b) _
    change Equiv (resTupF P μ fd fxσ rp a) _ at h
    rw [resEq P μ a] at h
    exact ((resTupF_congr P fxμ fxFd fxσ fxρp hab).symm.trans h).trans ht
  · intro a b hab h
    change Equiv (resTupF P μ fd fxσ rp b) _
    rw [resEq P μ b]
    exact ((resTupF_congr P fxμ fxFd fxσ fxρp hab).symm.trans h).trans ht.symm
theorem nodeFit (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : PSet.{4}) (xs : List PSet.{4}) :
    (semF P μ fd fxσ rp [PendAW.field]).InPhi X [.fn] xs 0 [] ↔
      (semF P fxμ fxFd fxσ fxρp fxNode.1).InPhi X [.fn] xs 0 [] := by
  cases xs with
  | nil => exact Iff.rfl
  | cons x xs =>
    cases xs with
    | cons a tail => exact ⟨fun h => h.2.elim, fun h => h.2.elim⟩
    | nil =>
      have hd : Equiv ((semF P μ fd fxσ rp [PendAW.field]).domBig 0 [])
          ((semF P fxμ fxFd fxσ fxρp fxNode.1).domBig 0 []) := by
        rw [show (semF P μ fd fxσ rp [PendAW.field]).domBig 0 [] = fxDomBig P
          from domEq P μ]
        exact Equiv.rfl
      have hp := piSet_congr hd (fun a b hab =>
        (fibEq P μ X a).trans ((semF P fxμ fxFd fxσ fxρp fxNode.1).fib_resp X 0 [] hab))
      exact ⟨fun h => ⟨mem_congr_right hp h.1, trivial⟩,
        fun h => ⟨mem_congr_right hp.symm h.1, trivial⟩⟩
theorem psiEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (X : PSet.{4}) :
    Equiv (PsiF P μ fd fxσ rp X) (PsiF P fxμ fxFd fxσ fxρp X) := by
  refine (PsiF_fin P μ fd fxσ rp X).trans
    ((sep_congr ?_ ?_ Equiv.rfl).trans (PsiF_fin P fxμ fxFd fxσ fxρp X).symm)
  · intro a b hab ⟨⟨j, hj⟩, xs, ha, hin⟩
    refine ⟨⟨j, hj⟩, xs, hab.symm.trans ha, ?_⟩
    cases j with
    | zero => cases xs <;> exact hin
    | succ j => cases j with
      | zero => exact (nodeFit P μ X xs).mp hin
      | succ j =>
        have h : j + 1 + 1 < 2 := hj
        exact (by omega : False).elim
  · intro a b hab ⟨⟨j, hj⟩, xs, ha, hin⟩
    refine ⟨⟨j, hj⟩, xs, hab.symm.trans ha, ?_⟩
    cases j with
    | zero => cases xs <;> exact hin
    | succ j => cases j with
      | zero => exact (nodeFit P μ X xs).mpr hin
      | succ j =>
        have h : j + 1 + 1 < 2 := hj
        exact (by omega : False).elim
theorem iterEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (n : Nat) :
    Equiv (iterPhi P μ fd n fxσ rp) (iterPhi P fxμ fxFd n fxσ fxρp) := by
  induction n with
  | zero => exact Equiv.rfl
  | succ n ih =>
    refine (psiEq P μ (iterPhi P μ fd n fxσ rp)).trans ?_
    apply ext; intro z
    exact ⟨PsiF_mono P fxμ fxFd fxσ fxρp
        (fun a ha => mem_congr_right ih ha) z,
      PsiF_mono P fxμ fxFd fxσ fxρp
        (fun a ha => mem_congr_right ih.symm ha) z⟩
theorem unionEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (iterPhiUnion P μ fd fxσ rp) (iterPhiUnion P fxμ fxFd fxσ fxρp) := by
  exact iUnionN_congr (fun n => iterEq P μ (n + 1))
theorem heightOmega (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ PsiF P μ fd fxσ rp (iterPhiUnion P μ fd fxσ rp) ∧
      fxZW P ∉ iterPhiUnion P μ fd fxσ rp := by
  constructor
  · apply mem_congr_right (psiEq P μ (iterPhiUnion P μ fd fxσ rp)).symm
    exact PsiF_mono P fxμ fxFd fxσ fxρp
      (fun a ha => mem_congr_right (unionEq P μ).symm ha) _ (fx_zW_mem_PsiF P)
  · intro h
    exact fx_zW_not_mem P (mem_congr_right (unionEq P μ) h)
theorem fnContUnion_false (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ¬ FnContUnion (P := P) (μ := μ) (fd := fd) fxσ rp := by
  intro h
  exact (heightOmega P μ).2 (h _ (heightOmega P μ).1)
end Rcic.F3.PSet.PendAWBridge
