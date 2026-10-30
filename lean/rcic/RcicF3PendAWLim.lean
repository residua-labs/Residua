import rcic.RcicF3PendAWBridge
import rcic.RcicF3KTWNonIR

/-!
# The literal finite-stage limit at an admitted inhabited W family

`closure_claim = 0`.

`entry` and `endFiber` align the existing family iterates with the semantic
operator on families whose result stays in Type at every level valuation.
Their explicit class-A and non-IR premises are only for this alignment;
there is no restriction added to `StepAG_PendA`. Function-recursive fields
are retained. `Typed` discharges every premise at `PendAW.recA`.

`Typed.famFiberEq` identifies the actual `famLim` application at the valid
infinite small parameter with the union of finite data stages.
`Typed.famHeightOmega` places the named height-omega tree in its constructor
operator and outside that exact family fibre. `Typed.famClosure_false`
therefore refutes constructor closure at the literal interpretation.

These are interpretation-bridge and obstruction artifacts, not a producer
or a refutation of the full group step. A full StepAG refutation would also
have to pay its faithful-table, base invariant, walk and bound premises.
The Type-only alignment is not offered as a decomposition of that target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Rcic.F3.PSet.PendAWLim
open Rcic.Declarative
variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hcls : ∀ c, c ∈ fd.ctors → FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
  (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
  (hN : ∀ σ ρp (j : Fin fd.ctors.length), NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
  (hType : ∀ σ, evalTotal σ fd.resLevel ≠ 0)
include hf hB hpf hcls hri hres hN hType
/-- Finite entry alignment, retaining the function-recursive class-A arm. -/
theorem entry : ∀ (n : Nat) (vs : List Nat),
    Equiv (famIter P μ fd n vs) (famOfD P μ fd (iterPhi P μ fd n) vs) := by
  intro n
  induction n with
  | zero => exact fun vs => famZero_famOfD_zero P μ fd vs
  | succ n ih =>
    intro vs
    have hc : ∀ c, c ∈ fd.ctors →
        (∀ e, e ∈ c.1 → ∀ ρ, Equiv
          (den (mkM P (tabIter P μ fd n)) (σOf vs) ρ e)
          (den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) (σOf vs) ρ e)) ∧
        (∀ e, e ∈ c.2 → ∀ ρ, Equiv
          (den (mkM P (tabIter P μ fd n)) (σOf vs) ρ e)
          (den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) (σOf vs) ρ e)) :=
      fun _ _ => ⟨fun e _ ρ => den_upd_congr P μ fd.fref hf (σOf vs)
        (fun ls => ih (ls.map (evalTotal (σOf vs)))) e ρ,
        fun e _ ρ => den_upd_congr P μ fd.fref hf (σOf vs)
        (fun ls => ih (ls.map (evalTotal (σOf vs)))) e ρ⟩
    have ht : ∀ e, e ∈ fd.params ++ fd.indices → ∀ ρ,
        den (mkM P (tabIter P μ fd n)) (σOf vs) ρ e =
        den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) (σOf vs) ρ e :=
      fun e he ρ => den_upd_eq_famFree P μ fd (σOf vs) hf e (hpf e he) ρ
    refine (famVal_den_congr P (tabIter P μ fd n)
      (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n))) (σOf vs) fd hc ht).trans ?_
    exact famVal_famOfD P μ fd ar (iterPhi P μ fd n) hB hpf
      (fun σ _ _ hρ => iterPhi_env n σ hρ)
      (fun _ _ hσ ρ => iterPhi_levels ar hB n hσ ρ)
      (iterPhi_ne n) (fun σ ρ => iterPhi_mem hN σ ρ (hType σ) n) hcls hri hres vs (hType (σOf vs))
/-- Alignment at every parameter/index tuple of the specified lengths. -/
theorem endFiber (n : Nat) (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length) (his : is.length = fd.indices.length) :
    Equiv (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd (push (ps ++ is) ρ0))
      (famEndD P μ fd (iterPhi P μ fd (n + 1)) σ (push (ps ++ is) ρ0)) := by
  have hd := fun (e : Expr Nat) (ρ : Nat → PSet.{4}) =>
    den_upd_congr P μ fd.fref hf σ
      (fun ls => entry P μ fd ar hf hB hpf hcls hri hres hN hType n (ls.map (evalTotal σ))) e ρ
  refine (famEnd_den_congr P (tabIter P μ fd n)
    (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n))) σ fd
    (fun _ _ => ⟨fun e _ ρ => hd e ρ, fun e _ ρ => hd e ρ⟩) _).trans ?_
  unfold famEnd famEndD
  rw [cond_neg (hType σ), push_append, ← his, shiftρ_push, lastVals_push]
  exact tyv_congr (TypeFib_famOfD P μ fd ar (iterPhi P μ fd n) hB hpf
    (fun σ _ _ hρ => iterPhi_env n σ hρ)
    (fun _ _ hσ ρ => iterPhi_levels ar hB n hσ ρ)
    (iterPhi_ne n) (fun σ ρ => iterPhi_mem hN σ ρ (hType σ) n) hcls hri hres σ ps hps is his)
end Rcic.F3.PSet.PendAWLim
namespace Rcic.F3.PSet.PendAWLim.Typed
open Rcic.Declarative
open PendAWBridge (fd rp)
theorem fresh : fd.fref ≠ 1 ∧ fd.fref ≠ 2 := by rw [PendAWBridge.fdExact]; decide
theorem typeRead (σ : Nat → Nat) : evalTotal σ fd.resLevel ≠ 0 := by
  rw [PendAWBridge.fdExact]; exact Nat.one_ne_zero
theorem bounded : FamBounded fd 0 := by
  rw [PendAWBridge.fdExact]
  constructor
  · intro e he; have : e = .sort (.succ .zero) := List.mem_singleton.mp he
    subst this; rfl
  · intro e he; exact (List.not_mem_nil e he).elim
  · rfl
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨fun e he => (List.not_mem_nil e he).elim, fun e he => (List.not_mem_nil e he).elim⟩
    · have : c = ([PendAW.field], []) := List.mem_singleton.mp hc
      subst this
      exact ⟨fun e he => by rw [List.mem_singleton.mp he]; rfl,
        fun e he => (List.not_mem_nil e he).elim⟩
theorem paramsFree : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false := by
  rw [PendAWBridge.fdExact]
  intro e he; have : e = .sort (.succ .zero) := List.mem_singleton.mp he
  subst this; rfl
theorem indicesFree : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false := by
  rw [PendAWBridge.fdExact]
  intro c hc e he
  rcases List.mem_cons.mp hc with rfl | hc
  · exact (List.not_mem_nil e he).elim
  · rw [List.mem_singleton.mp hc] at he
    exact (List.not_mem_nil e he).elim
theorem indicesLen : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length := by
  rw [PendAWBridge.fdExact]
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rfl
  · rw [List.mem_singleton.mp hc]
theorem classes : ∀ c, c ∈ fd.ctors →
    FieldsClassA fd.fref 0 fd.params.length fd.indices.length c.1 0 := by
  rw [PendAWBridge.fdExact]
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact True.intro
  · rw [List.mem_singleton.mp hc]
    refine ⟨Or.inr (Or.inr ⟨.bvar 0, [], rfl, rfl, rfl, ?_⟩), trivial⟩
    intro e he; exact (List.not_mem_nil e he).elim
/-- The leaf has no fields and the node has one: no later field can read it. -/
theorem nonIR (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∀ σ ρp (j : Fin fd.ctors.length), NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1 := by
  intro σ ρp j
  apply nonIRSem_of_kinds
  rcases j with ⟨j, hj⟩
  change j < 2 at hj
  cases j with
  | zero => intro a b _ hb; exact (Nat.not_lt_zero b hb).elim
  | succ j =>
    have hz : j = 0 := by omega
    subst hz
    intro a b hab hb
    change b < 1 at hb
    exact (by omega : False).elim
theorem resultTuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (n : Nat) {z : PSet.{4}} (hz : z ∈ iterPhi P μ fd n fxσ rp) :
    Equiv (resTupF P μ fd fxσ rp z) (ordPair pempty (tup [])) := by
  cases n with
  | zero => exact (not_mem_pempty hz).elim
  | succ n =>
    change z ∈ PsiF P μ fd fxσ rp (iterPhi P μ fd n fxσ rp) at hz
    obtain ⟨i, ⟨j, c, xs, hcj, hid, hIn⟩, hiz⟩ := mem_sep.mp hz
    have hl : xs.length = c.1.length :=
      (Sem.InPhi.length _ (kindsOf fd.fref c.1) xs 0 [] hIn).trans (List.length_map _ _)
    have he := resTupF_dataVal P μ fd fxσ rp hcj hl (hiz.symm.trans hid)
    have hc0 : c.2 = [] := List.length_eq_zero.mp (indicesLen c (List.getElem?_mem hcj))
    simpa only [hc0, List.map_nil] using he
theorem fibFull (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (n : Nat) :
    Equiv (fibAt P μ fd (iterPhi P μ fd n) fxσ rp [])
      (iterPhi P μ fd n fxσ rp) := by
  apply ext; intro z
  constructor
  · exact mem_sep_subset
  · intro hz
    obtain ⟨i, hi⟩ := hz
    exact mem_sep.mpr ⟨i, resultTuple P μ n ⟨i, Equiv.rfl⟩, hi⟩
theorem endEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (n : Nat) :
    Equiv (famEnd (mkM P (tabIter P μ fd n)) W4 fxσ fd rp)
      (tyv (iterPhi P μ fd (n + 1) fxσ rp)) := by
  have he := PendAWLim.endFiber P μ fd 0 fresh bounded paramsFree classes indicesFree
    indicesLen (nonIR P μ) typeRead n fxσ [tyv fxS] [] rfl rfl
  change Equiv (famEnd (mkM P (tabIter P μ fd n)) W4 fxσ fd rp)
    (tyv (fibAt P μ fd (iterPhi P μ fd (n + 1)) fxσ rp [])) at he
  exact he.trans (tyv_congr (fibFull P μ (n + 1)))
theorem limEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (El (limEnd P μ fd fxσ rp)) (iterPhiUnion P μ fd fxσ rp) := by
  exact (el_tyv (S := iUnionN (fun n =>
    El (famEnd (mkM P (tabIter P μ fd n)) W4 fxσ fd rp)))).trans
    (iUnionN_congr (fun n => (el_congr (endEq P μ n)).trans el_tyv))
/-- The exact consumer family fibre at the valid infinite small parameter. -/
theorem famFiberEq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (El (fapps (famLim P μ fd []) [tyv fxS]))
      (iterPhiUnion P μ fd fxσ rp) := by
  have hx : TelFits (mkM P μ) fxσ (fd.params ++ fd.indices) ρ0 [tyv fxS] := by
    exact PendAWBridge.argsFit P μ pempty
  have hb := fapps_piLam (mkM P μ) fxσ (limEnd_resp P μ fd fxσ)
    (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 [tyv fxS] hx
  exact (el_congr hb).trans (limEq P μ)
/-- A named constructor output is missing from that exact family fibre. -/
theorem famHeightOmega (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ PsiF P μ fd fxσ rp (El (fapps (famLim P μ fd []) [tyv fxS])) ∧
      fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) := by
  have h := PendAWBridge.heightOmega P μ
  constructor
  · exact PsiF_mono P μ fd fxσ rp
      (fun a ha => mem_congr_right (famFiberEq P μ).symm ha) _ h.1
  · intro hz
    exact h.2 (mem_congr_right (famFiberEq P μ) hz)
theorem famClosure_false (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ¬ Sub (PsiF P μ fd fxσ rp (El (fapps (famLim P μ fd []) [tyv fxS])))
      (El (fapps (famLim P μ fd []) [tyv fxS])) := by
  intro h
  exact (famHeightOmega P μ).2 (h _ (famHeightOmega P μ).1)
end Rcic.F3.PSet.PendAWLim.Typed
