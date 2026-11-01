import rcic.RcicF3PointwisePropOnlyNormalized
import rcic.RcicF3FamilyBetaMirror

/-!
# Original-bound PropOnly groups with family-argument beta wrappers

Each original field is required to be literally the actual cached field,
wrapped finitely many times as `(fun _ : familyType => field) family`.
Different fields may use different depths, including zero. This is an
inductive syntax certificate, with no fitting or denotation callback.

The fresh family constant inhabits its original stored type in every
admissible candidate. FamilyBetaMirror.den_of_group therefore erases the
wrappers at every local environment. Global normalized tuple monotonicity
then produces both original tuples used by the existing evaluation proof.
The complete group endpoint below retains the original GInv and bounds.
Source-only draft; root owns native validation. closure_claim = 0.
-/
/- Evaluation, recursor membership and invariant assembly are shared
through PointwisePropOnlyPipeline; this file constructs its field boundary
from the same syntax hypothesis carried by every public endpoint. -/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaFields
open Rcic.Declarative RawFamily

/-- Literal source/cache syntax, allowing an independent finite wrapper
depth at each field position. -/
inductive Sources (fd : FamData) (arity : Nat) :
    List (Expr Nat) → List (Expr Nat) → Prop where
  | nil : Sources fd arity [] []
  | cons (depth : Nat) (A : Expr Nat) {As Bs : List (Expr Nat)}
      (tail : Sources fd arity As Bs) :
      Sources fd arity
        (FamilyBetaMirror.mirrors fd arity depth A :: As) (A :: Bs)

theorem sources_refl (fd : FamData) (arity : Nat) (As : List (Expr Nat)) :
    Sources fd arity As As := by
  induction As with
  | nil => exact .nil
  | cons A As ih => exact .cons 0 A ih

/-- The actual stored fields are syntax-certified wrappers of their
actual EvalPlan cached fields. -/
def Cached (p : EvalPlan.Plan) : Prop :=
  ∀ j : Fin p.node.a.constructors.length,
    Sources (EvalPlanNormal.fd p) p.node.a.family.member.arity
      (p.node.a.constructorViews j).fields (EvalPlanNormal.fields p j)

def SourceFamilyBeta {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop := Cached (EvalPlan.ofNode node)

/-- The earlier literal-equality face is the depth-zero instance. -/
theorem cached_of_source_eq (p : EvalPlan.Plan)
    (he : ∀ j : Fin p.node.a.constructors.length,
      EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields) :
    Cached p := by
  intro j
  rw [he j]
  exact sources_refl _ _ _

theorem sourceFamilyBeta_of_sourceNormalized
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (he : PointwisePropOnlyNormalizedFields.SourceNormalized node) :
    SourceFamilyBeta node :=
  cached_of_source_eq (EvalPlan.ofNode node) he

/-- Family admissibility pays each actual beta argument at every local
environment; the original tuple is produced without an own-parameter fit. -/
theorem fits_source (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (D : Frame) (hD : Admissible (EvalPlanNormal.fd p) D)
    (σ : Nat → Nat) {As Bs : List (Expr Nat)}
    (hsource : Sources (EvalPlanNormal.fd p) p.node.a.family.member.arity As Bs) :
    ∀ (ρ : Nat → PSet.{4}) (xs : List PSet.{4}),
      TelFits (mkM P (table P μ (EvalPlanNormal.fd p) D)) σ Bs ρ xs →
      TelFits (mkM P (table P μ (EvalPlanNormal.fd p) D)) σ As ρ xs := by
  induction hsource with
  | nil => intro ρ xs hxs; exact hxs
  | @cons depth A As Bs htail ih =>
      intro ρ xs hxs
      cases xs with
      | nil => exact hxs
      | cons x xs =>
          have he := ed_congr (mkM P (table P μ (EvalPlanNormal.fd p) D))
            (FamilyBetaMirror.den_of_group P μ p fm ctors hE hmem D hD
              σ ρ depth A)
          exact ⟨mem_congr_right he.symm hxs.1, ih (vcons x ρ) xs hxs.2⟩

/-- A globally included candidate's actual normalized tuple becomes an
original tuple in the selected target candidate, at the same values. -/
theorem fields_to_raw (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hsource : Cached p) (X D : Frame)
    (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hsub : FrameSub X D) (j : Fin p.node.a.constructors.length)
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X)) σ
      (EvalPlanNormal.fields p j) ρ xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields ρ xs := by
  have hnorm := PointwisePropOnlyNormalizedFields.fields_mono P μ σ p
    X D hX hD hsub j ρ xs hxs
  exact fits_source P μ p fm ctors hE hmem D hD σ (hsource j) ρ xs hnorm


/-- The actual family-beta syntax pays the shared internal boundary. -/
theorem field_transport (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hsource : SourceFamilyBeta node) :
    PointwisePropOnlyPipeline.FieldTransport P node := by
  intro μ σ fm ctors hE hmem α ctx plans hctx hFaith X D hX hD hsub j ps xs hps hxs
  exact fields_to_raw P μ σ (EvalPlan.ofNode node) fm ctors hE hmem
    hsource X D hX hD hsub j (push ps ρ0) xs hxs

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaFields

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, CtorAt P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (NormPropEval.candidate P μ C) vs i z → EvalPredicate C vs i z := by
  exact PointwisePropOnlyPipeline.Eval.constructor_step P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Source-field composition produces candidate admissibility and global
constructor closure for the actual normalized operator. -/
theorem candidate_closed (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (NormPropEval.candidate P μ C) ∧
    Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (NormPropEval.candidate P μ C) := by
  exact PointwisePropOnlyPipeline.Eval.candidate_closed P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

/-- Every normalized member produces evaluation at the complete key
once the actual valuation and parameter guard are supplied. -/
theorem normalized_evaluates (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, z ∈ base P μ C vs i → EvalPredicate C vs i z := by
  exact PointwisePropOnlyPipeline.Eval.normalized_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Produced totality and typed guarding justify the literal erased value
in the exact requested dependent Prop motive. -/
theorem empty_mem (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) :
    pempty ∈ Ed C.M (fapps C.motive (is ++ [major])) := by
  exact PointwisePropOnlyPipeline.Eval.empty_mem P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors is major hps his hmajor

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaRecMem
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

/-- At every bounded full recursor vector, the actual new abstraction is a
member of the actual stored type. Its end obligation is produced inside
this proof from the typed group and the repaired predecessor invariant. -/
theorem memberValue_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta p.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (fullvs : List Nat) (hvl : fullvs.length = p.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K p.rr)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hpolicy : p.node.a.policy = .propOnly) :
    EvalPlanValue.memberValue (mkM P μ) (σOf fullvs) p p.rm ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) ρ0 p.rm.mtype) := by
  exact PointwisePropOnlyPipeline.RecMem.memberValue_mem P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hvl hvs hProp hpolicy

/-- The canonical new recursor is sound on the uniformly Prop/propOnly
family-beta syntax face. Both equations are read from the actual admitted group
and faithful table; the original bound packages retain their literal types. -/
theorem member_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    MemberSound P μ K rr rm := by
  exact PointwisePropOnlyPipeline.RecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaRecMem

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaIota
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The produced source-field membership composes with the already-general
PropOnly stable IotaAt theorem at the same actual pointwise table. -/
theorem rec_pkg (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    RecPkg P μ K E' rr rm := by
  exact PointwisePropOnlyPipeline.Iota.rec_pkg P μ K hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource) hPred α hα ctx plans hctx hplans hFaith
    ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaIota

namespace Rcic.F3.PSet.PointwisePropOnlyFamilyBetaGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Complete group composition on the admitted family-beta syntax face, with
arbitrary constructor parameter mirrors and the original bound packages. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
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
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  exact PointwisePropOnlyPipeline.Group.group_step P K hE hfam hctors hrec hmem hProp hpolicy (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource)

/-- Uniform Prop admission pays the walk premise at every RecNode, so
this invariant step has neither a W check nor a D check. -/
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
    (hsource : PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  exact PointwisePropOnlyPipeline.Group.invariant_step P K hE hfam hctors hrec hmem hProp hpolicy (PointwisePropOnlyFamilyBetaFields.field_transport P _ hsource)
    hB hD hPred

end Rcic.F3.PSet.PointwisePropOnlyFamilyBetaGroup

#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaFields.fields_to_raw
#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval.constructor_step
#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaEval.normalized_evaluates
#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaRecMem.member_sound
#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaIota.rec_pkg
#print axioms Rcic.F3.PSet.PointwisePropOnlyFamilyBetaGroup.invariant_step
