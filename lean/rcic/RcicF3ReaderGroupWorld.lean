import rcic.RcicF3ReaderPacketWorld
import rcic.RcicF3NormRoleDelta
import rcic.RcicF3PointwisePrefix
import rcic.RcicF3PointwiseRoleEquations

/-!
# The actual predecessor produces the reader's environment facts

The reader adds only bodyless group members. Every transparent lookup is
therefore an exact predecessor lookup, with its original BoundG source.
Reapplying the chosen predecessor invariant after each fresh family update
supplies both original tables' member soundness and stable old iota. The
faithful predecessor supplies all-list transparent equations, preserved
by the same fresh update.

Both existing normalized and separate pointwise predecessors are covered.
No current recursor package, constructor closure, small frame, reader
provenance or domain-mask premise is introduced. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderPacket
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- This construction uses literal preexisting environment facts. Its
semantic inputs are discharged by the two predecessor producers below. -/
noncomputable def World.of_group_facts (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundG K hE)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hfd : fd.fref = f)
    (hAC : AllSound P (table P μ fd C) K E)
    (hAD : AllSound P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) K E)
    (hIC : ∀ r m, E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ fd C) K E' r)
    (hID : ∀ r m, E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ fd (RawFamilyEnlarge.enlarge fd C)) K E' r)
    (hδ : DeltaNormalize.BodyEquations (mkM P μ) E σ) :
    World P μ fd C σ K node.E0 := by
  have hfresh : E.members fd.fref = none := by
    rw [hfd]
    exact groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hnew : ∀ r m, node.E0.members r = some m → E.members r = none → m.body = none := by
    intro r m hm hn
    have hm' := node.sub r m (members_extend_preserved node.fresh r m hm)
    rcases groupMembersT_cases hmem r m hm' with hold | hnew
    · rw [hn] at hold
      cases hold
    · exact groupMembersT_body_none hmem r m hnew
  have hread : ∀ r ls, transparentBody node.E0 r ls = transparentBody E r ls :=
    CandidateScope.transparentBody_eq_of_bodyless_extension node.base hnew
  have hδC : DeltaNormalize.BodyEquations (mkM P (table P μ fd C)) E σ :=
    EvalRoleDelta.bodyEquations_transfer P hE
      (agreeOn_upd hfresh μ (ofFrame P μ fd C)) σ hδ
  have hδD : DeltaNormalize.BodyEquations
      (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) E σ :=
    EvalRoleDelta.bodyEquations_transfer P hE
      (agreeOn_upd hfresh μ (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C))) σ hδ
  exact
    { previous := E, finalEnv := E', wellformed := hE, bounded := hB,
      sub := groupMembersT_preserve hmem, allC := hAC, allD := hAD,
      iotaC := hIC, iotaD := hID, reads := hread,
      deltaC := fun r ls b hr ρ => hδC r ls b ((hread r ls).symm.trans hr) ρ,
      deltaD := fun r ls b hr ρ => hδD r ls b ((hread r ls).symm.trans hr) ρ }

/-- The unchanged normalized predecessor supplies the entire reader
environment package for arbitrary fresh-family replacements. -/
noncomputable def World.of_normalized_predecessor (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundG K hE)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hfd : fd.fref = f)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E) :
    World P μ fd C σ K node.E0 := by
  have hfresh : E.members fd.fref = none := by
    rw [hfd]
    exact groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hC := NormCandidatePrefix.prior_at_frame P K hE hPred μ ctx plans
    hctx hplans hFaith fd C hfresh
  have hD := NormCandidatePrefix.prior_at_frame P K hE hPred μ ctx plans
    hctx hplans hFaith fd (RawFamilyEnlarge.enlarge fd C) hfresh
  exact World.of_group_facts P μ fd C σ K hE hB hmem node hfd hC.1 hD.1
    (hC.2 E' (groupMembersT_preserve hmem))
    (hD.2 E' (groupMembersT_preserve hmem))
    (NormRoleDelta.bodyEquations_of_faithful P μ ctx plans hE hctx hFaith σ)

/-- The separate pointwise predecessor pays the same literal reader
facts. This neither converts it to the normalized invariant nor assumes
any local constructor-closed candidate. -/
noncomputable def World.of_pointwise_predecessor (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundG K hE)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hfd : fd.fref = f)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E) :
    World P μ fd C σ K node.E0 := by
  have hfresh : E.members fd.fref = none := by
    rw [hfd]
    exact groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hC := PointwiseRole.prior_at_frame P K hE hPred α hα μ ctx plans
    hctx hplans hFaith fd C hfresh
  have hD := PointwiseRole.prior_at_frame P K hE hPred α hα μ ctx plans
    hctx hplans hFaith fd (RawFamilyEnlarge.enlarge fd C) hfresh
  exact World.of_group_facts P μ fd C σ K hE hB hmem node hfd hC.1 hD.1
    (hC.2 E' (groupMembersT_preserve hmem))
    (hD.2 E' (groupMembersT_preserve hmem))
    (PointwiseRoleEquations.bodyEquations_of_faithful P α μ ctx plans hE hctx hFaith σ)

end Rcic.F3.PSet.ReaderPacket
