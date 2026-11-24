import NfCompose.Sum
import NfCompose.Seq
import NfCompose.Prod

/-!
`AtMostOneAdmit` under the three compositions.

Sum: equivalent to every component. The `#guard`s on `two` show a Tier-1 sum
(`two_sum_profile`) whose admissible class still has two raws.

Sequential: stage 1's axiom is enough (`seq_atMost_of_stage1`). Stage 2's
axiom is not (`seq_stage2_collision_stays` with `witnessModel`). The converse
fails when stage 2 refuses the collided class (`seq_stage1_collision_blocked`).

Product: both axioms suffice (`prod_atMost`). One does not, when the other
model admits nothing (`prod_atMost_while_left_fails`).
-/

namespace NfCompose

open MSTNecessityExecModelMWE

theorem sum_atMost_iff {ι : Type} (F : ι → ExecModel) :
    AtMostOneAdmit (sumModel F) ↔ ∀ i, AtMostOneAdmit (F i) := by
  constructor
  · intro h i c r1 r2 hq1 hq2 hadm
    have hraw := h ⟨i, c⟩ ⟨i, r1⟩ ⟨i, r2⟩
      (Sigma.ext rfl (heq_of_eq hq1)) (Sigma.ext rfl (heq_of_eq hq2)) hadm
    exact sigma_eq_snd hraw
  · intro h c raw1 raw2 hq1 hq2 hadm
    rcases c with ⟨i, cls⟩
    rcases raw1 with ⟨j, r1⟩
    rcases raw2 with ⟨k, r2⟩
    have hj : j = i := congrArg Sigma.fst hq1
    have hk : k = i := congrArg Sigma.fst hq2
    cases hj
    cases hk
    have hr := h i cls r1 r2 (sigma_eq_snd hq1) (sigma_eq_snd hq2) hadm
    exact Sigma.ext rfl (heq_of_eq hr)

theorem seq_atMost_of_stage1 (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)
    (h : AtMostOneAdmit M1) : AtMostOneAdmit (seqModel M1 M2 feed) := by
  intro c r1 r2 hq1 hq2 hadm
  have ha1 : M1.admissible c = true := by
    cases ha : M1.admissible c with
    | true => rfl
    | false =>
        cases hs : M1.sigma c <;> simp [seqModel, seqAdmOf, ha, hs] at hadm
  exact h c r1 r2 hq1 hq2 ha1

theorem prod_atMost (M1 M2 : ExecModel) (h1 : AtMostOneAdmit M1) (h2 : AtMostOneAdmit M2) :
    AtMostOneAdmit (prodModel M1 M2) := by
  intro c r s hqr hqs hadm
  rcases c with ⟨c1, c2⟩
  rcases r with ⟨r1, r2⟩
  rcases s with ⟨s1, s2⟩
  have hq1 : M1.q r1 = c1 := congrArg Prod.fst hqr
  have hq2 : M2.q r2 = c2 := congrArg Prod.snd hqr
  have hs1 : M1.q s1 = c1 := congrArg Prod.fst hqs
  have hs2 : M2.q s2 = c2 := congrArg Prod.snd hqs
  have hadmAnd : (M1.admissible c1 && M2.admissible c2) = true := by
    simpa [prodModel] using hadm
  have ⟨ha1, ha2⟩ := bool_and_true hadmAnd
  have e1 := h1 c1 r1 s1 hq1 hs1 ha1
  have e2 := h2 c2 r2 s2 hq2 hs2 ha2
  cases e1
  cases e2
  rfl

inductive PointRaw | u
  deriving DecidableEq

inductive PointClass | c
  deriving DecidableEq

inductive PointRep | r
  deriving DecidableEq

inductive PointRes | e
  deriving DecidableEq

inductive PointOut | o
  deriving DecidableEq

def admitPoint : ExecModel where
  Raw := PointRaw
  Class := PointClass
  Rep := PointRep
  Residue := PointRes
  Outcome := PointOut
  q := fun _ => .c
  evalRaw := fun _ => .o
  evalClass := fun _ => .o
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some .r

def refusePoint : ExecModel where
  Raw := PointRaw
  Class := PointClass
  Rep := PointRep
  Residue := PointRes
  Outcome := PointOut
  q := fun _ => .c
  evalRaw := fun _ => .o
  evalClass := fun _ => .o
  admissible := fun _ => false
  rho := fun _ => some .e
  sigma := fun _ => none

theorem admitPoint_profile : hasMSTNFProfile admitPoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; cases r; rfl
  · intro cls rp _; cases cls; cases rp; rfl
  · intro _ _ hadm
    simp [admitPoint] at hadm
  · intro _ _ _
    intro h
    simp [admitPoint] at h

theorem admitPoint_atMost : AtMostOneAdmit admitPoint := by
  intro _ r1 r2 _ _ _
  cases r1; cases r2; rfl

theorem refusePoint_profile : hasMSTNFProfile refusePoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; cases r; rfl
  · intro _ _ h
    simp [refusePoint] at h
  · intro cls _ _
    cases cls
    intro h
    simp [refusePoint] at h
  · intro _ _ hadm
    simp [refusePoint] at hadm

def feedPrimary : admitPoint.Rep → witnessModel.Raw := fun _ => .primary

def feedRefuse : witnessModel.Rep → refusePoint.Raw := fun _ => .u

theorem seq_stage2_collision_stays :
    AtMostOneAdmit (seqModel admitPoint witnessModel feedPrimary) :=
  seq_atMost_of_stage1 admitPoint witnessModel feedPrimary admitPoint_atMost

theorem seq_stage2_source_fails : ¬ AtMostOneAdmit witnessModel :=
  witnessModel_not_atMostOneAdmit

theorem seq_stage1_collision_blocked :
    AtMostOneAdmit (seqModel witnessModel refusePoint feedRefuse) := by
  intro c _ _ _ _ hadm
  cases c with
  | canonical => simp [seqModel, seqAdmOf, witnessModel, refusePoint, feedRefuse] at hadm
  | rejected => simp [seqModel, seqAdmOf, witnessModel] at hadm

theorem seq_stage1_source_fails : ¬ AtMostOneAdmit witnessModel :=
  witnessModel_not_atMostOneAdmit

theorem prod_atMost_while_left_fails :
    AtMostOneAdmit (prodModel witnessModel refusePoint) := by
  intro c _ _ _ _ hadm
  rcases c with ⟨_, c2⟩
  cases c2
  simp [prodModel, refusePoint] at hadm

def two : Bool → ExecModel
  | false => admitPoint
  | true => witnessModel

theorem two_profile : ∀ b, hasMSTNFProfile (two b)
  | false => admitPoint_profile
  | true => witnessModel_has_mstnf_profile

theorem two_sum_profile : hasMSTNFProfile (sumModel two) :=
  sum_profile two two_profile

theorem two_sum_not_atMost : ¬ AtMostOneAdmit (sumModel two) := by
  intro h
  exact witnessModel_not_atMostOneAdmit ((sum_atMost_iff two).mp h true)

def witnessClass (r : RawEvent) : EventClass := witnessModel.q r

def twoSumClass (r : RawEvent) : EventClass :=
  ((sumModel two).q ⟨true, r⟩).2

#guard decide (witnessClass .primary = witnessClass .duplicate)
#guard decide (witnessModel.admissible .canonical = true)
#guard decide (RawEvent.primary ≠ RawEvent.duplicate)
#guard decide ((seqModel witnessModel refusePoint feedRefuse).admissible .canonical = false)
#guard decide ((seqModel witnessModel refusePoint feedRefuse).admissible .rejected = false)
#guard decide ((seqModel admitPoint witnessModel feedPrimary).admissible .c = true)
#guard decide ((prodModel witnessModel refusePoint).admissible (.canonical, .c) = false)
#guard decide (twoSumClass .primary = .canonical)
#guard decide (twoSumClass .duplicate = .canonical)
#guard decide (twoSumClass .primary = twoSumClass .duplicate)
#guard decide ((sumModel two).admissible ⟨true, .canonical⟩ = true)

end NfCompose
