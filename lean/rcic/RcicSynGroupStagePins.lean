import rcic.RcicSynGroupStage
import rcic.RcicTypedGroupPins

/-!
# Step 4c-S2a: Nat group-stage consumers and the skipped-zero tooth

Family-only and family-plus-zero are real cursors into `natMembersT`.
`natEskip` keeps family and successor and drops zero: `CvWalkHyp` plus
`EnvExt` accept it, and `GroupStageAt natMembersT` refuses it.
`closure_claim = 0`.
-/

namespace Rcic.Syn.GroupStagePins

open Rcic.Declarative

def natFamOnlyEnv : ResolvedEnv := extendEnv emptyEnv 0 natFamMember

def natFamZeroEnv : ResolvedEnv := extendEnv natFamOnlyEnv 1 natZeroMember

/-- Family 0 and successor 2, with zero 1 omitted. -/
def natEskip : ResolvedEnv := extendEnv natFamOnlyEnv 2 natSuccMember

def natCursorFam : GroupStageAt natMembersT natFamOnlyEnv := by
  unfold natMembersT
  exact .next (.here _)

def natCursorFamZero : GroupStageAt natMembersT natFamZeroEnv := by
  unfold natMembersT
  exact .next (.next (.here _))

noncomputable def natFamOrigin : GroupOrigin natEnvU where
  base := emptyEnv
  baseWf := .empty
  f := 0
  fm := natFamMember
  ctors := [(1, natZeroMember), (2, natSuccMember)]
  rr := 3
  rm := natRecMemberU
  Eend := natEnvU
  famClass := rfl
  ctorClass := fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl
  recClass := rfl
  chain := natMembersT
  stage := natFamOnlyEnv
  atStage := natCursorFam
  endExt := envExt_refl _

noncomputable def natFamZeroOrigin : GroupOrigin natEnvU where
  base := emptyEnv
  baseWf := .empty
  f := 0
  fm := natFamMember
  ctors := [(1, natZeroMember), (2, natSuccMember)]
  rr := 3
  rm := natRecMemberU
  Eend := natEnvU
  famClass := rfl
  ctorClass := fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl
  recClass := rfl
  chain := natMembersT
  stage := natFamZeroEnv
  atStage := natCursorFamZero
  endExt := envExt_refl _

def natFamCtx : CtxWfT natFamOnlyEnv 0 [.assumption (.const 0 [])] :=
  .assumption [] (.const 0 []) (.succ .zero) .nil (natConstTyT rfl)

def natFamZeroCtx : CtxWfT natFamZeroEnv 0 [.assumption (.const 0 [])] :=
  .assumption [] (.const 0 []) (.succ .zero) .nil (natConstTyT rfl)

theorem natFam_walk : Nonempty (CvWalkHyp natFamOnlyEnv) :=
  ⟨natFamOrigin.walk⟩

theorem natFam_memberSort : Nonempty (MemberSortP natFamOnlyEnv) :=
  ⟨natFamOrigin.memberSort⟩

theorem natFam_ctx : Nonempty (CtxP natFamOnlyEnv 0 [.assumption (.const 0 [])]) :=
  ⟨natFamOrigin.ctx natFamCtx⟩

theorem natFamZero_walk : Nonempty (CvWalkHyp natFamZeroEnv) :=
  ⟨natFamZeroOrigin.walk⟩

theorem natFamZero_memberSort : Nonempty (MemberSortP natFamZeroEnv) :=
  ⟨natFamZeroOrigin.memberSort⟩

theorem natFamZero_ctx : Nonempty (CtxP natFamZeroEnv 0 [.assumption (.const 0 [])]) :=
  ⟨natFamZeroOrigin.ctx natFamZeroCtx⟩

noncomputable def eskipWalk : CvWalkHyp natEskip :=
  cvWalkHyp_cons
    (cvWalkHyp_cons (cvWalkHyp_of_envWfT .empty)
      (rfl : emptyEnv.members 0 = none) rfl (fun _ => rfl) rfl rfl)
    (rfl : natFamOnlyEnv.members 2 = none) rfl (fun _ => rfl) rfl rfl

theorem eskip_ext : EnvExt natEskip natEnvU := by
  intro r m h
  simp only [natEskip, natFamOnlyEnv, extendEnv, emptyEnv] at h
  by_cases hr2 : r = 2
  · subst hr2
    simp only [if_pos rfl] at h
    cases h
    simp [natEnvU, natEnvPrefix, extendEnv]
  · by_cases hr0 : r = 0
    · subst hr0
      simp only [if_neg hr2, if_pos rfl] at h
      cases h
      simp [natEnvU, natEnvPrefix, extendEnv]
    · simp only [if_neg hr2, if_neg hr0] at h
      cases h

theorem natChainEnvs : chainEnvs natMembersT =
    [emptyEnv, natFamOnlyEnv, natFamZeroEnv, natEnvPrefix, natEnvU] := rfl

theorem natStage_shape {E : ResolvedEnv} (p : GroupStageAt natMembersT E) :
    E = emptyEnv ∨ E = natFamOnlyEnv ∨ E = natFamZeroEnv ∨ E = natEnvPrefix ∨ E = natEnvU := by
  have hmem := stage_mem p
  rw [natChainEnvs] at hmem
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem natEskip_not_stage : ¬ Nonempty (GroupStageAt natMembersT natEskip) := by
  intro ⟨p⟩
  have hshape := natStage_shape p
  have h2 : natEskip.members 2 = some natSuccMember := by
    simp [natEskip, natFamOnlyEnv, extendEnv]
  have h1 : natEskip.members 1 = none := by
    simp [natEskip, natFamOnlyEnv, emptyEnv, extendEnv]
  rcases hshape with h | h | h | h | h
  · rw [h] at h2; simp [emptyEnv] at h2
  · rw [h] at h2; simp [natFamOnlyEnv, emptyEnv, extendEnv] at h2
  · rw [h] at h2; simp [natFamZeroEnv, natFamOnlyEnv, emptyEnv, extendEnv] at h2
  · rw [h] at h1; simp [natEnvPrefix, extendEnv] at h1
  · rw [h] at h1; simp [natEnvU, natEnvPrefix, extendEnv] at h1

/-- Paired tooth: the weakened stage bundle accepts the skip, the exact cursor refuses it. -/
theorem eskip_tooth :
    (Nonempty (CvWalkHyp natEskip) ∧ EnvExt natEskip natEnvU) ∧
      ¬ Nonempty (GroupStageAt natMembersT natEskip) :=
  ⟨⟨⟨eskipWalk⟩, eskip_ext⟩, natEskip_not_stage⟩

end Rcic.Syn.GroupStagePins
