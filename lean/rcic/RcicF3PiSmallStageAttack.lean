import rcic.RcicF3PiSmallStage
import rcic.RcicF3PiSmallAttack
/-!
# Stage-bound witnesses and a decoder counterexample

The existing W family has a small height-omega element. Acc on Nat.lt is
inhabited at every index and small already at stage 1. A small nullary tree
whose decoder returns the whole universe is refused: small shapes and
branches alone do not supply local code closure. These are semantic-model
fixtures; no universal raw-group compilation is asserted.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallStageAttack
open PiSmallProducer PiSmallAttack

theorem w_small (P : Premises4) (M : Interp.{4}) :
    Small.{3,4} (family M wSig .unit) := by
  apply PiSmallStage.family_small P.c3 M wSig wInvariants.2
  intro ⟨s⟩ f hf
  cases s with
  | leaf =>
      exact mem_univIn.{3,4}.mp (dataVal_mem_stage (stage_univIn.{3,4} P.c3) 0 []
        (fun _ h => False.elim (List.not_mem_nil _ h)))
  | node =>
      apply mem_univIn.{3,4}.mp
      apply dataVal_mem_stage (stage_univIn.{3,4} P.c3) 1 [f .unit]
      intro x hx
      cases List.mem_singleton.mp hx
      exact mem_univIn.{3,4}.mpr (hf .unit)

theorem w_omega_small (P : Premises4) (M : Interp.{4}) :
    Small.{3,4} (decode M wSig wOmega) ∧ ∀ n, ¬ wBound n wOmega := by
  refine ⟨small_of_mem_small (w_small P M) ?_, wOmega_bound_refuted⟩
  exact ⟨⟨⟨wOmega, wOmega_valid⟩⟩, Equiv.rfl⟩

theorem acc_stage1 (P : Premises4) (M : Interp.{4}) (x : Nat) :
    Small.{0,4} (family M (accSig Nat.lt) x) ∧
      pempty ∈ family M (accSig Nat.lt) x := by
  constructor
  · have hs : Small.{0,4} (singleton (pempty : PSet.{4})) :=
      mem_univIn.{0,4}.mp ((stage_univIn.{0,4} P.c0).singleton_mem
        (mem_univIn.{0,4}.mpr small_pempty))
    apply small_subset hs
    intro z ⟨⟨⟨t, ht⟩⟩, he⟩
    cases ht with
    | sup s g hg => exact mem_singleton.mpr he.symm
  · exact (acc_exact M Nat.lt x).mpr (Nat.lt_wfRel.wf.apply x)

def oversizedSig : Sig PUnit.{1} where
  Sh := PUnit.{4}
  Field := fun _ => PEmpty.{4}
  depth := fun _ _ => 0
  tel := fun _ k => PEmpty.elim k
  out := fun _ => .unit
  code := fun _ _ => univIn.{3,4}
  code_congr := fun _ _ _ _ => Equiv.rfl

def oversizedTree : Tree oversizedSig := .sup .unit (fun p => PEmpty.elim p.1)

theorem oversized_refused (M : Interp.{4}) :
    ¬ Small.{3,4} (family M oversizedSig .unit) := by
  intro hs
  have hv : Valid oversizedSig .unit oversizedTree :=
    Valid.sup (S := oversizedSig) PUnit.unit (fun p => PEmpty.elim p.1)
      (fun k => PEmpty.elim k)
  have hm : univIn.{3,4} ∈ family M oversizedSig .unit :=
    ⟨⟨⟨oversizedTree, hv⟩⟩, Equiv.rfl⟩
  exact mem_irrefl (univIn.{3,4})
    (mem_univIn.{3,4}.mpr (small_of_mem_small hs hm))

end Rcic.F3.PSet.PiSmallStageAttack
