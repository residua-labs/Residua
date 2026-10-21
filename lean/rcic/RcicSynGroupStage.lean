import rcic.RcicSynEnrich
import rcic.RcicSynBelowScoped

/-!
# Step 4c-S2a: native group-stage cursor

`CvWalkHyp` and `MemberSortP` are derived along an actual `GroupMembersT`
chain. The cursor has no constructor for a skipped or reordered member.
Public `ScopedCtx` / `BelowScoped` keep their `EnvWfT` guards.
`closure_claim = 0`. Blocker 2 and native `hcoh` are not addressed.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A position in one concrete `GroupMembersT` chain.
`here` is that chain's current environment. `next` moves into the
suffix after one original `cons`, keeping every admission field in the index. -/
inductive GroupStageAt :
    {S E₀ : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {Eend : ResolvedEnv} →
    GroupMembersT S E₀ ms Eend → ResolvedEnv → Type
  | here {S E₀ : ResolvedEnv} {ms : List (Nat × CheckedMember)} {Eend : ResolvedEnv}
      (g : GroupMembersT S E₀ ms Eend) : GroupStageAt g E₀
  | next {S E : ResolvedEnv} {r : Nat} {m : CheckedMember}
      {rest : List (Nat × CheckedMember)} {E' : ResolvedEnv}
      {hfresh : E.members r = none} {hnobody : m.body = none}
      {hclT : ∀ k, lift k 1 m.mtype = m.mtype}
      {harity : m.mclass = .inductiveM → isArity m.mtype = true}
      {hlvlB : exprLevelsBounded m.arity m.mtype = true}
      {hcanon : exprFamCanonical E m.mtype = true}
      {harities : groupArityCoherent E m = true}
      {hadm : IndGroupAdmitted E r m} {hidx : IdxAdmittedT hadm} {u : Level}
      {hT : HasTyT E m.arity [] m.mtype (.sort u)}
      {hTc : m.mclass = .constructorM → Nonempty (HasTyT S m.arity [] m.mtype (.sort u))}
      {htyped : IndGroupTypedT hadm}
      {hrest : GroupMembersT S (extendEnv E r m) rest E'}
      {Eᵢ : ResolvedEnv} (p : GroupStageAt hrest Eᵢ) :
      GroupStageAt
        (GroupMembersT.cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
          hadm hidx u hT hTc htyped hrest) Eᵢ

/-- Environments that occur as the current base of `g` or of a suffix. -/
def chainEnvs {S E₀ Eend : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (g : GroupMembersT S E₀ ms Eend) : List ResolvedEnv :=
  match g with
  | .nil E => [E]
  | .cons E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest => E :: chainEnvs hrest

theorem stage_mem {S E₀ Eend Eᵢ : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {g : GroupMembersT S E₀ ms Eend} (p : GroupStageAt g Eᵢ) : Eᵢ ∈ chainEnvs g :=
  match g, p with
  | .nil _, .here _ => List.Mem.head _
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, .here _ => List.Mem.head _
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, .next p' =>
      List.Mem.tail _ (stage_mem p')

/-- The suffix of `g` that still remains at this stage. -/
def stageSuffix {S E₀ Eend Eᵢ : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {g : GroupMembersT S E₀ ms Eend} (p : GroupStageAt g Eᵢ) :
    Σ ms' : List (Nat × CheckedMember), GroupMembersT S Eᵢ ms' Eend :=
  match g, p with
  | g', .here _ => ⟨ms, g'⟩
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, .next p' => stageSuffix p'

/-- Walk cache at the stage, by the same `cvWalkHyp_cons` step as `enrichGroupMembersT`. -/
def stageWalk {S E₀ : ResolvedEnv} {ms : List (Nat × CheckedMember)} {Eend : ResolvedEnv}
    {g : GroupMembersT S E₀ ms Eend} {Eᵢ : ResolvedEnv} (hw : CvWalkHyp E₀) :
    GroupStageAt g Eᵢ → CvWalkHyp Eᵢ
  | .here _ => hw
  | .next (hfresh := hfresh) (hnobody := hnobody) (hclT := hclT)
      (hlvlB := hlvlB) (harities := harities) p' =>
    stageWalk (cvWalkHyp_cons hw hfresh hnobody hclT hlvlB harities) p'
termination_by structural p => p

/-- Member-sort cache at the stage, by the same `enrichHasTyT` / `memberSortP_extendEnv`
step as `enrichGroupMembersT`. -/
def stageMember {S E₀ : ResolvedEnv} {ms : List (Nat × CheckedMember)} {Eend : ResolvedEnv}
    {g : GroupMembersT S E₀ ms Eend} {Eᵢ : ResolvedEnv} (hw : CvWalkHyp E₀) (hm : MemberSortP E₀) :
    GroupStageAt g Eᵢ → MemberSortP Eᵢ
  | .here _ => hm
  | .next (m := m) (hfresh := hfresh) (hnobody := hnobody) (hclT := hclT)
      (hlvlB := hlvlB) (harities := harities) (hT := hT) p' =>
    stageMember (cvWalkHyp_cons hw hfresh hnobody hclT hlvlB harities)
      (memberSortP_extendEnv hm hfresh
        (enrichHasTyT hw.closed (envExt_refl _) hm (letCtxConvP_of_cvWalkHyp hw)
          (CtxP.nil _ m.arity) hT))
      p'
termination_by structural p => p

/-- Cursor at the first suffix of one concrete `cons`. -/
def stageAtNextHere
    {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {rest : List (Nat × CheckedMember)}
    (hfresh : E.members r = none) (hnobody : m.body = none)
    (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
    (harity : m.mclass = .inductiveM → isArity m.mtype = true)
    (hlvlB : exprLevelsBounded m.arity m.mtype = true)
    (hcanon : exprFamCanonical E m.mtype = true)
    (harities : groupArityCoherent E m = true)
    (hadm : IndGroupAdmitted E r m) (hidx : IdxAdmittedT hadm) (u : Level)
    (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (hTc : m.mclass = .constructorM → Nonempty (HasTyT S m.arity [] m.mtype (.sort u)))
    (htyped : IndGroupTypedT hadm)
    (hrest : GroupMembersT S (extendEnv E r m) rest E') :
    GroupStageAt
      (GroupMembersT.cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon
        harities hadm hidx u hT hTc htyped hrest)
      (extendEnv E r m) :=
  GroupStageAt.next (hfresh := hfresh) (hnobody := hnobody) (hclT := hclT) (harity := harity)
    (hlvlB := hlvlB) (hcanon := hcanon) (harities := harities) (hadm := hadm) (hidx := hidx)
    (u := u) (hT := hT) (hTc := hTc) (htyped := htyped) (hrest := hrest)
    (GroupStageAt.here hrest)

theorem stageWalk_here {S E₀ Eend : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {g : GroupMembersT S E₀ ms Eend} (hw : CvWalkHyp E₀) :
    stageWalk hw (GroupStageAt.here g) = hw := by
  simp [stageWalk]

theorem stageMember_here {S E₀ Eend : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {g : GroupMembersT S E₀ ms Eend} (hw : CvWalkHyp E₀) (hm : MemberSortP E₀) :
    stageMember hw hm (GroupStageAt.here g) = hm := by
  simp [stageMember]

theorem enrichGroupMembersT_eq_stage_here
    {S E₀ Eend : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (g : GroupMembersT S E₀ ms Eend) (hw : CvWalkHyp E₀) (hm : MemberSortP E₀) :
    enrichGroupMembersT hw hm g =
      enrichGroupMembersT (stageWalk hw (GroupStageAt.here g))
        (stageMember hw hm (GroupStageAt.here g)) g := by
  simp [stageWalk_here, stageMember_here]

/-- One `cons` of enrichment is the stage cache of `next (here suffix)`. -/
theorem enrichGroupMembersT_eq_stage_step
    {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {rest : List (Nat × CheckedMember)}
    (hfresh : E.members r = none) (hnobody : m.body = none)
    (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
    (harity : m.mclass = .inductiveM → isArity m.mtype = true)
    (hlvlB : exprLevelsBounded m.arity m.mtype = true)
    (hcanon : exprFamCanonical E m.mtype = true)
    (harities : groupArityCoherent E m = true)
    (hadm : IndGroupAdmitted E r m) (hidx : IdxAdmittedT hadm) (u : Level)
    (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (hTc : m.mclass = .constructorM → Nonempty (HasTyT S m.arity [] m.mtype (.sort u)))
    (htyped : IndGroupTypedT hadm)
    (hrest : GroupMembersT S (extendEnv E r m) rest E')
    (hw : CvWalkHyp E) (hm : MemberSortP E) :
    enrichGroupMembersT hw hm
        (GroupMembersT.cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon
          harities hadm hidx u hT hTc htyped hrest) =
      GroupMembersP.cons E r m rest E' hfresh hnobody u
        (enrichHasTyT hw.closed (envExt_refl E) hm (letCtxConvP_of_cvWalkHyp hw)
          (CtxP.nil E m.arity) hT)
        (enrichGroupMembersT
          (stageWalk hw (stageAtNextHere hfresh hnobody hclT harity hlvlB hcanon harities
            hadm hidx u hT hTc htyped hrest))
          (stageMember hw hm (stageAtNextHere hfresh hnobody hclT harity hlvlB hcanon harities
            hadm hidx u hT hTc htyped hrest))
          hrest) := by
  simp [enrichGroupMembersT, stageWalk, stageMember, stageAtNextHere]

/-- A member chain only adds members, so its base is included in its end. -/
theorem groupMembersT_ext {S E₀ Eend : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (g : GroupMembersT S E₀ ms Eend) : EnvExt E₀ Eend :=
  match g with
  | .nil _ => envExt_refl _
  | .cons _ _ m _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest =>
      envExt_trans (envExt_extendEnv m hfresh) (groupMembersT_ext hrest)

/-- Admitted native group plus one cursor into its actual member chain. -/
structure GroupOrigin (Eₐ : ResolvedEnv) where
  base : ResolvedEnv
  baseWf : EnvWfT base
  f : Nat
  fm : CheckedMember
  ctors : List (Nat × CheckedMember)
  rr : Nat
  rm : CheckedMember
  Eend : ResolvedEnv
  famClass : fm.mclass = .inductiveM
  ctorClass : ∀ c ∈ ctors, c.2.mclass = .constructorM
  recClass : rm.mclass = .recursorM
  chain : GroupMembersT (extendEnv base f fm) base ((f, fm) :: ctors ++ [(rr, rm)]) Eend
  stage : ResolvedEnv
  atStage : GroupStageAt chain stage
  endExt : EnvExt Eend Eₐ

noncomputable def GroupOrigin.walk {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ) :
    CvWalkHyp o.stage :=
  stageWalk (cvWalkHyp_of_envWfT o.baseWf) o.atStage

noncomputable def GroupOrigin.memberSort {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ) :
    MemberSortP o.stage :=
  stageMember (cvWalkHyp_of_envWfT o.baseWf)
    (memberSortP_of_envWfP (enrichEnvWfT o.baseWf)) o.atStage

/-- Stage context spine from the derived walk and member caches. Not an `EnvWfT` guard. -/
noncomputable def GroupOrigin.ctx {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT o.stage n Γ) : CtxP o.stage n Γ :=
  enrichCtxWfT o.walk.closed (envExt_refl _) o.memberSort
    (letCtxConvP_of_cvWalkHyp o.walk) hΓ

/-- Members at the stage survive the remaining suffix and the recorded ambient inclusion. -/
def GroupOrigin.ambientExt {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ) : EnvExt o.stage Eₐ :=
  envExt_trans (groupMembersT_ext (stageSuffix o.atStage).2) o.endExt

/-- Canonical disposition of the stage spine. -/
noncomputable def GroupOrigin.can {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT o.stage n Γ) (σ : Level → Level) : List Disp :=
  (o.ctx hΓ).disp σ

theorem GroupOrigin.canDispForHom {Eₐ : ResolvedEnv} (o : GroupOrigin Eₐ)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT o.stage n Γ) {σ : Level → Level} (hσ : LevelHom σ) :
    DispForHom σ o.stage n Γ (o.can hΓ σ) :=
  dispForHom_of_ctxP hσ (o.ctx hΓ)

/-- Admitted-root canonical disposition is the signed-off `ScopedCtx.can`. -/
theorem admittedCan_eq_scopedCtx {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :
    (enrichCtxWfT_of_envWfT S.env S.ctx).disp σ = S.can σ := rfl

/-- Ordinary admitted environment. Its context spine is `enrichCtxWfT_of_envWfT`,
so the disposition is exactly `ScopedCtx.can`. -/
structure AdmittedRoot (Eₐ : ResolvedEnv) where
  env : ResolvedEnv
  wf : EnvWfT env
  ext : EnvExt env Eₐ

noncomputable def AdmittedRoot.ctx {Eₐ : ResolvedEnv} (o : AdmittedRoot Eₐ)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT o.env n Γ) : CtxP o.env n Γ :=
  enrichCtxWfT_of_envWfT o.wf hΓ

theorem AdmittedRoot.can_eq_scopedCtx {Eₐ : ResolvedEnv} (o : AdmittedRoot Eₐ)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT o.env n Γ) (σ : Level → Level) :
    (o.ctx hΓ).disp σ = ({ env := o.wf, ext := o.ext, ctx := hΓ } : ScopedCtx Eₐ o.env n Γ).can σ := rfl

end Rcic.Syn
