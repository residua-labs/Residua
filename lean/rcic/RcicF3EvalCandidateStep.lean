import rcic.RcicF3EvalCandidatePrefix
import rcic.RcicF3PropEvalCandidateStep
import rcic.RcicF3RawFamilyProp

/-!
# Candidate constructor production under the new evaluation-role invariant

The predecessor is the repaired EvalRole.GInv. Its canonical normalized-plan
read support is produced from typed admission, including at every candidate
family update. The bounded Prop/anySort constructor proof then consumes
ordinary semantic prefix facts. No old PlanRole.GInv conversion is used.
On the selected Prop/anySort face, admission produces a uniform Prop
result, so raw-frame admissibility is also produced. Global constructor
monotonicity, raw-frame closure and the complete recursor package remain
separate obligations. No data-face admissibility is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalCandidateStep
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate

/-- The actual large-elimination selection forces a uniformly Prop result.
The existing proof-family candidate then sizes the raw frame at every
family valuation, without a closure or monotonicity premise. -/
theorem raw_admissible (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort) :
    Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)) :=
  RawFamilyProp.admissible P μ (famDataOf C.node.a)
    (fun vs => (selection_prop C.node.a C.σ h0 hpolicy).1 (σOf vs))

/-- The public step producer consumes the actual predecessor invariant and
typed recursor inputs. All candidate-prefix, normalization, child-existence,
typed-IH, stored-minor composition and this Prop-face raw admissibility
obligations are discharged internally. -/
theorem constructor_step (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (C : Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hPred : EvalRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (role P μ (famDataOf C.node.a) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (v : Level)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, CtorAt P μ (famDataOf C.node.a) (candidate P μ C) vs i z →
      EvalPredicate C vs i z := by
  have hRaw := raw_admissible P μ C h0 hpolicy
  exact PropEvalCandidate.constructor_step_of_prefixes P μ K C hM fm ctors hE hfam hctors hrec hmem hBound
    (EvalCandidatePrefix.group_facts P K μ hE hfam hmem C.node hPred ctx plans hctx hplans hFaith
      hFamily hRaw)
    hFamily hRaw fullvs hσfull hvs h0 hpolicy v hmo hminors


end Rcic.F3.PSet.EvalCandidateStep
