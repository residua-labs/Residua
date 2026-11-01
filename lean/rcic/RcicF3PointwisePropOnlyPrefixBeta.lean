import rcic.RcicF3ReaderPrefixBeta

/-!
# Original-bound PropOnly from the available recursive-reader prefix

The source certificate follows the literal original/cached fields. A local
beta argument is obtained from the fitting FAMILY parameters, earlier raw
fields, or a domain entered by Pi descent. No fit for the constructor's own
parameter telescope is used. The certificate also composes the existing
fresh-family beta, delta, zeta and application-head constructions.

This module proves the internal transport boundary and composes the one
shared PropOnly invariant pipeline. It adds no semantic callback to the
public producer. Completeness for arbitrary actual reader paths remains
open; closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyPrefixBeta
open Rcic.Declarative RawFamily

theorem field_transport (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hsource : ReaderPrefixBeta.SourcePrefixBeta node) :
    PointwisePropOnlyPipeline.FieldTransport P node := by
  intro μ σ fm ctors hE hmem α ctx plans hctx hFaith X D hX hD hsub j ps xs hps hxs
  exact ReaderPrefixBeta.fields_to_raw_of_pointwise P μ σ
    (EvalPlan.ofNode node) fm ctors hE hmem α ctx plans hctx hFaith
    hsource X D hX hD hsub j ps xs hps hxs

/-- A complete original invariant producer on the actual source face.
The unchanged pipeline owns constructor/evaluation/recursor/iota assembly. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hsource : ReaderPrefixBeta.SourcePrefixBeta
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  PointwisePropOnlyPipeline.Group.invariant_step P K hE hfam hctors hrec hmem
    hProp hpolicy (field_transport P _ hsource) hB hD hPred

end Rcic.F3.PSet.PointwisePropOnlyPrefixBeta

#print axioms Rcic.F3.PSet.PointwisePropOnlyPrefixBeta.field_transport
#print axioms Rcic.F3.PSet.PointwisePropOnlyPrefixBeta.invariant_step
