import rcic.RcicF3PointwisePropParamGroup
import rcic.RcicF3PropShapeCoverage

/-!
# Shared internal assembly for original-bound PropOnly syntax producers

FieldTransport is an internal interface for the only step that differs
between the plain, source-normalized, no-beta-reader and family-beta
producers. Each public producer constructs this interface from its own
syntax certificate before invoking this module. It is not a new premise
on any public syntax theorem or on the original root.

The fitting parameters below are the family parameters already extracted
from the actual constructor membership. No constructor-own-parameter fit
is requested. The source tuple and output tuple use the same actual values,
valuation, original node and local environment.

The existing plain-field assembly is moved here once. Original BoundG,
BoundDG, PointwiseRole.GInv and supplied Premises4 are retained throughout.
The unrestricted StepPropOnly remains open. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline
open Rcic.Declarative RawFamily

/-- Internal field boundary. Every exported syntax producer pays this
boundary in its own source module; no public syntax theorem accepts it.
The target family fit is already available at both constructor uses. -/
def FieldTransport (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT E)
    (_hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (α : PointwiseRole.Arities) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (_hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (_hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (X D : Frame)
    (_hX : Admissible (famDataOf node.a) X)
    (_hD : Admissible (famDataOf node.a) D)
    (_hsub : FrameSub X D)
    (j : Fin node.a.constructors.length) (ps xs : List PSet.{4}),
    TelFits (mkM P (table P μ (famDataOf node.a) D)) σ
      node.a.family.parameters ρ0 ps →
    TelFits (mkM P (table P μ (famDataOf node.a) X)) σ
      (EvalPlanNormal.fields (EvalPlan.ofNode node) j) (push ps ρ0) xs →
    TelFits (mkM P (table P μ (famDataOf node.a) D)) σ
      (node.a.constructorViews j).fields (push ps ρ0) xs

end Rcic.F3.PSet.PointwisePropOnlyPipeline

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P C.node)
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
  have h0 := hProp C.σ
  let p := EvalPlan.ofNode C.node
  let N := base P μ C
  let X := NormPropEval.candidate P μ C
  let R := N
  obtain ⟨hN, _⟩ := NormPropCtorUniform.normalized_closed P μ p fm ctors hE hmem hProp
  have hNraw : Admissible (famDataOf C.node.a) N := hN
  have hX : Admissible (famDataOf C.node.a) X :=
    PropEvalFrame.admissible P C N hNraw
  have hRaw : Admissible (famDataOf C.node.a) R := hNraw
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith N hNraw hFamily
  obtain ⟨hAX, hIX, hEX⟩ := PointwiseRole.target_facts P μ K p fm ctors
    hE hfam hmem hPred α hα ctx plans hctx hplans hFaith X hX
  obtain ⟨hAR, hIR, hER⟩ := PointwiseRole.target_facts P μ K p fm ctors
    hE hfam hmem hPred α hα ctx plans hctx hplans hFaith R hRaw
  intro vs i z hc hσ hkey
  obtain ⟨jn, xs, hpX, hxX, hi, _⟩ := ctorAt_parameters_at P μ (EvalPlanNormal.fd p) X
    C.node.a.family.member.arity (EvalPlanNormal.bounded_of_group p fm ctors hE hmem)
    vs C.σ hσ i z hc C.parameters hkey h0
  let j := EvalPlanNormal.index p jn
  have hget := EvalPlanNormal.ctor_get p jn
  rw [hget] at hxX hi
  have hpR : TelFits (mkM P (table P μ (famDataOf C.node.a) R)) C.σ
      C.node.a.family.parameters ρ0 C.parameters :=
    (PiIndependent.telFits_free P μ (famDataOf C.node.a).fref
      (ofFrame P μ (famDataOf C.node.a) X) (ofFrame P μ (famDataOf C.node.a) R)
      C.σ C.node.a.family.parameters
      (fun e he => F.free e (List.mem_append_left _ he)) ρ0 C.parameters).mp hpX
  have hxOriginalX := hfields μ C.σ fm ctors hE hmem
    α ctx plans hctx hFaith X X hX hX (fun _ _ _ hz => hz)
    j C.parameters xs hpX hxX
  have hxOriginalR := hfields μ C.σ fm ctors hE hmem
    α ctx plans hctx hFaith X R hX hRaw (fun _ _ _ hz => mem_sep_subset hz)
    j C.parameters xs hpR hxX
  have he := table_equiv P μ (famDataOf C.node.a) R hFamily
  have hpRaw : TelFits (mkM P μ) C.σ C.node.a.family.parameters ρ0 C.parameters :=
    (TelFits_tables_equiv P he _ _ _ _).mpr hpR
  have hxRaw : TelFits (mkM P μ) C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs :=
    (TelFits_tables_equiv P he _ _ _ _).mpr hxOriginalR
  have hERaw := F.rawEnv C.σ C.node.a.family.member.arity
  obtain ⟨endVal, hEnd, hF, hProof⟩ :=
    NormPropEval.frame_inputs P μ C hM F.bounded N hFamily hNraw h0
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact PropEvalProof.functional C (by rw [hM]; rfl) hmo hProof hz hz'
  have hb := CandidateBoundFields.family_prefix_bodiesOK C.σ K hE hBound.1 hmem
  have hInst := NormPropParamFields.original_fields_instOK C.σ K
    hE hfam hctors hrec hmem hBoundD C.node fullvs hσfull hvl hvs j
  have hRawC : EnvSound C.M C.σ K (extendEnv C.E C.f fm) C.node.a.family.member.arity := by
    rw [hM]
    exact hERaw
  have hpC : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters := by
    rw [hM]
    exact hpRaw
  have hxC : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs := by
    rw [hM]
    exact hxRaw
  have heval := eval_of_frame_fields P μ C hM N hNraw F.free fm ctors hmem K
    hRawC (hEX C.σ C.node.a.family.member.arity) hb F.closedReader .zero (by rw [hM]; rfl)
    endVal hEnd hF hmo hProof hfunctional hpC hminors j xs hInst hxC hxOriginalX
  have hread := PiIndependent.leafArgs_free P μ (famDataOf C.node.a).fref
    (ofFrame P μ (famDataOf C.node.a) X) (μ (famDataOf C.node.a).fref)
    C.σ (C.node.a.constructorViews j).resultIndices
    (C.node.a.constructorViews j).noFamilyInIndices (push xs (push C.parameters ρ0))
  rw [PiIndependent.upd_self] at hread
  change (C.node.a.constructorViews j).resultIndices.map
      (den (mkM P (table P μ (famDataOf C.node.a) X)) C.σ (push xs (push C.parameters ρ0))) =
    (C.node.a.constructorViews j).resultIndices.map
      (den (mkM P μ) C.σ (push xs (push C.parameters ρ0))) at hread
  change i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
    (den (mkM P (table P μ (famDataOf C.node.a) X)) C.σ (push xs (push C.parameters ρ0)))) at hi
  rw [hread] at hi
  have hiC : i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
    rw [hM]
    exact hi
  rw [hiC]
  exact heval


end Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Plain-field composition produces candidate admissibility and global
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P C.node)
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
  let p := EvalPlan.ofNode C.node
  obtain ⟨hN, hClosed⟩ := NormPropCtorUniform.normalized_closed P μ p fm ctors hE hmem
    hProp
  have hX : Admissible (EvalPlanNormal.fd p) (NormPropEval.candidate P μ C) :=
    PropEvalFrame.admissible P C (base P μ C) hN
  have hStep := constructor_step P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvl hvs hProp hmo hminors
  have hMono := EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem
  refine ⟨hX, ?_⟩
  intro vs i z hz
  have hR := hClosed vs i z (hMono _ _ hX hN
    (fun _ _ _ hm => mem_sep_subset hm) vs i z hz)
  obtain ⟨j, hj⟩ := hR
  exact mem_sep.mpr ⟨j, hStep vs i z hz, hj⟩

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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P C.node)
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
  obtain ⟨hX, hClosed⟩ := candidate_closed P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvl hvs hProp hmo hminors
  intro vs i z hz hσ hp
  exact PropEvalFrame.exists_of_mem C (base P μ C) vs i z
    (frame_least P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (NormPropEval.candidate P μ C) hX hClosed vs i z hz) hσ hp

end Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P C.node)
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
  have h0 := hProp C.σ
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (NormPropCtorUniform.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem hProp).1
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hmajorR := NormPropEval.major_at_frame P μ C hM F.bounded hFamily hRaw is major hps his hmajor
  have hkey : RawFamilyRec.paramKey C.node.a.family.parameters.length (key (C.parameters ++ is)) =
      key C.parameters := by
    rw [← hps.length]
    exact RawFamilyRec.paramKey_append C.parameters is
  have hex := normalized_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvl hvs hProp hmo hminors vs
    (key (C.parameters ++ is)) major hmajorR (canonical_agreement C) hkey
  obtain ⟨_, _, _, hProof⟩ := NormPropEval.frame_inputs P μ C hM F.bounded (base P μ C) hFamily hRaw h0
  have hU : C.M.U = U W4 := by rw [hM]; rfl
  have hguard : ∀ i z, Eval C i z → z ∈ childCarrier C .zero i := by
    intro i z hz
    exact hz.mem_guarded_of_typed_motive .zero hU hmo hProof
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact PropEvalProof.functional C hU hmo hProof hz hz'
  have hs := PropEvalValue.result_spec C .zero (key (C.parameters ++ is)) hex
    (hguard _) (hfunctional _)
  have hproof : Equiv major pempty := hProof (C.parameters ++ is)
    (by rw [List.length_append, hps.length, his.length]) major hmajor
  exact mem_congr_left (PropEvalProof.output_prop C hU hmo hProof hs.2)
    (PropEvalValue.result_mem_motive C .zero is major hU hps.length
      hmo his hmajor hproof hs.1)

end Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.RecMem
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P p.node)
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
  let M := mkM P μ
  let a := p.node.a
  let σ := σOf fullvs
  let g := EvalPlanValue.endValue M σ p
  change piLam M σ g ρ0 p.rm.mtype ∈ Ed M (den M σ ρ0 p.rm.mtype)
  rw [a.recursorType, policyRecursorType_eq]
  refine piLam_mem M σ (EvalPlanValue.endValue_resp M σ p) _ ρ0 ?_
  refine piGood_policyPi_fits M σ g _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M σ g _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, rest, rfl, hps, hrest⟩ := TelFits_split _ _ ρ0 zs hz
  obtain ⟨mo, rest', rfl, hmo, hrest'⟩ : ∃ mo rest', rest = mo :: rest' ∧
      mo ∈ Ed M (den M σ (push ps ρ0) (policyMotiveType a.family a.policy)) ∧
      TelFits M σ (a.minorTypes ++
        (liftFields (a.minorTypes.length + 1) a.family.indices 0 ++ _))
        (vcons mo (push ps ρ0)) rest' := by
    cases rest with
    | nil => exact hrest.elim
    | cons mo rest' => exact ⟨mo, rest', rfl, hrest.1, hrest.2⟩
  obtain ⟨ms, rest'', rfl, hms, hrest''⟩ := TelFits_split _ _ _ rest' hrest'
  obtain ⟨is, zl, rfl, his, hzl⟩ := TelFits_split _ _ _ rest'' hrest''
  have hmsl : ms.length = a.minorTypes.length := hms.length
  have hmsk : ms.length = a.constructors.length := hmsl.trans a.minorCount
  have hisl : is.length = a.family.indices.length := by
    rw [his.length, liftFields_length']
  have hpsl : ps.length = a.family.parameters.length := hps.length
  have hisfit : TelFits M σ a.family.indices (push ps ρ0) is := by
    apply (TelFits_liftFields M σ (mo :: ms) (push ps ρ0)
      a.family.indices [] is).mp
    show TelFits M σ (liftFields (ms.length + 1) a.family.indices 0)
      (push ms (vcons mo (push ps ρ0))) is
    rw [hmsl]
    exact his
  obtain ⟨z, rfl, hmajor⟩ : ∃ z, zl = [z] ∧ z ∈ Ed M
      (den M σ (push is (push ms (vcons mo (push ps ρ0))))
        (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals a.family.parameters.length
            (a.minorTypes.length + 1 + a.family.indices.length) ++
              policyLocals a.family.indices.length))) := by
    match zl, hzl with
    | [z], ⟨hz, _⟩ => exact ⟨z, rfl, hz⟩
  have hres := den_recResult M σ mo z ms is (push ps ρ0)
  rw [hmsl, hisl, ← push_cons_eq] at hres
  rw [hres]
  have hmajorType : den M σ (push is (push ms (vcons mo (push ps ρ0))))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals a.family.parameters.length
          (a.minorTypes.length + 1 + a.family.indices.length) ++
            policyLocals a.family.indices.length)) =
      fapps (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal σ)))
        (ps ++ is) := by
    have hpush : push is (push ms (vcons mo (push ps ρ0))) =
        push (ps ++ (mo :: (ms ++ is))) ρ0 := by
      rw [push_append]
      show push is (push ms (vcons mo (push ps ρ0))) =
        push (ms ++ is) (vcons mo (push ps ρ0))
      rw [push_append]
    have hlength : a.minorTypes.length + 1 + a.family.indices.length =
        (mo :: (ms ++ is)).length := by
      rw [List.length_cons, List.length_append, hmsl, hisl]
      exact Nat.add_right_comm _ _ _
    have hparams : (policyParameterLocals a.family.parameters.length
        (a.minorTypes.length + 1 + a.family.indices.length)).map
        (den M σ (push is (push ms (vcons mo (push ps ρ0))))) = ps := by
      rw [hpush, hlength, ← hpsl]
      exact den_paramLocals M σ ps _ ρ0
    have hindices : (policyLocals a.family.indices.length).map
        (den M σ (push is (push ms (vcons mo (push ps ρ0))))) = is := by
      rw [← hisl]
      exact den_policyLocals M σ is _
    rw [den_foldApps, List.map_append, hparams, hindices]
    rfl
  rw [hmajorType] at hmajor
  change EvalPlanValue.endValue M σ p
    (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ0) ∈
      Ed M (fapps mo (is ++ [z]))
  rw [NormDPlanBridge.endpoint_propOnly M σ p hProp hpolicy,
    recEnd_propOnly M σ (famDataOf p.node.a) _ (hProp σ) hpolicy]
  let C := (EvalPlanValue.context p M σ ρ0).withValues ps mo ms hmsk
  have hmo0 : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi a.family.indices
        (.pi (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyLocals (a.family.parameters.length + a.family.indices.length)))
          (.sort .zero)))) := by
    simpa only [policyMotiveType, show a.policy = .propOnly from hpolicy,
      policyMotiveLevel] using hmo
  exact PointwisePropOnlyPipeline.Eval.empty_mem P μ K C rfl fm ctors
    hE hfam hctors hrec hmem hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs rfl hvl hvs hProp hmo0 hms is z hps hisfit hmajor

/-- The canonical new recursor is sound on the uniformly Prop/propOnly
plain-field face. Both equations are read from the actual admitted group
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
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
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam hctors hrec hmem
    ctxFull plansFull hctxFull hFaithFull hProp
  have hrm : E'.members rr = some rm :=
    groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hbody : rm.body = none :=
    groupMembersT_body_none hmem rr rm
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hTF := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hrecValue := PointwiseRoleEquations.recursor_value_of_group P α μ
    hE hfam hctors hrec hmem ctxFull plansFull hctxFull hplansFull hFaithFull
  intro σ ls ρ hlen hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvs : ∀ u, u ∈ ls.map (evalTotal σ) → u ≤ K rr := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact hlevels l hl
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype
    (hTF rr rm hrm).1 (hlen ▸ (hTF rr rm hrm).2.1)]
  refine mem_congr_left (hrecValue _).symm ?_
  have hvl : (ls.map (evalTotal σ)).length = p.node.a.family.member.arity := by
    rw [List.length_map, hlen]
    change p.rm.arity = p.node.a.family.member.arity
    have hp : p.node.a.policy = .propOnly := hpolicy
    simpa only [policyRecursorArity, hp] using p.node.a.recursorArity
  exact memberValue_mem P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith hFamily
    (ls.map (evalTotal σ)) hvl hvs hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyPipeline.RecMem

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.Iota
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The produced plain-field membership composes with the already-general
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
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
    RecPkg P μ K E' rr rm :=
  ⟨PointwisePropOnlyPipeline.RecMem.member_sound P μ K hE hfam hctors hrec hmem
      hBound hBoundD hfields hPred α hα ctx plans hctx hplans hFaith
      ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy,
    fun Efin _ => PointwisePropOnlyIota.iota_at P μ K hE hfam hctors hrec hmem
      α ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy Efin⟩

end Rcic.F3.PSet.PointwisePropOnlyPipeline.Iota

namespace Rcic.F3.PSet.PointwisePropOnlyPipeline.Group
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Complete group composition on the admitted plain-field face, with
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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P (EvalPlan.ofGroup hE hfam hctors hrec hmem).node) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro _hwalk hBound hBoundD hPred
  intro α hα ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (hsubE r m hm)
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono hsubE
  have hPrior := hPred α hαE ctx hctxE plans hplansE μ hFaithE
  have hFamily := PointwisePropPrefix.family_equation_of_group P α μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith hProp
  have hN := (NormPropCtorUniform.normalized_closed P μ p fm ctors
    hE hmem hProp).1
  obtain ⟨_hfm, hty, _hfree, hTF, _hclosed, _hbounded⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  change fm.mtype = famType (EvalPlanNormal.fd p) at hty
  have hfm : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hfmSound : MemberSound P μ K f fm := by
    intro σ ls ρ hlen _hlevels
    refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
      (hTF f fm hfm).1 (hlen ▸ (hTF f fm hfm).2.1), hty]
    have hf : Equiv (μ f (ls.map (evalTotal σ)))
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) := by
      have hF := hFamily (ls.map (evalTotal σ))
      change Equiv (μ p.node.a.family.ref (ls.map (evalTotal σ)))
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) at hF
      simpa only [p.node.fam] using hF
    exact mem_congr_left hf.symm
      (ofFrame_mem P μ (EvalPlanNormal.fd p) (frame P μ (EvalPlanNormal.fd p)) hN _)
  have hctorSound : ∀ j : Fin p.node.a.constructors.length,
      MemberSound P μ K (f + 1 + j.val) (p.node.a.constructors[j.val]) :=
    fun j => PointwisePropCtor.member_sound P μ K hE hfam hctors hrec hmem hBound
      hPred α hα ctx plans hctx hplans hFaith hProp j
  have hPkg := PointwisePropOnlyPipeline.Iota.rec_pkg P μ K hE hfam hctors hrec hmem
    hBound hBoundD hfields hPred α hαE ctx plans hctxE hplansE hFaithE
    ctx plans hctx hplans hFaith hProp hpolicy
  constructor
  · intro r m hm
    rcases group_member_cases hmem hL hrr p.node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.1 r m hold
    · exact hfmSound
    · exact hPkg.1
    · exact hctorSound j
  · intro Efin hsub r m hm hk
    rcases group_member_cases hmem hL hrr p.node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hPrior.2 Efin (fun s n hn => hsub s n (hsubE s n hn)) r m hold hk
    · rw [hfam] at hk
      cases hk
    · exact hPkg.2 Efin hsub
    · rw [(p.node.a.constructorViews j).hasClass] at hk
      cases hk


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
    (hfields : PointwisePropOnlyPipeline.FieldTransport P (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  apply group_step P K hE hfam hctors hrec hmem hProp hpolicy hfields ?_ hB hD hPred
  intro node
  have hp : UniformProp node.a.family.resultLevel := by
    rw [Rcic.F3.StepWGroup.nodeResult_unique node p.node]
    exact hProp
  exact Rcic.Syn.FamApp.StepW.stepW_of_uniformProp hE hfam hctors hrec hmem node
    (walkRec_of_group hmem) hp

end Rcic.F3.PSet.PointwisePropOnlyPipeline.Group

#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval.constructor_step
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval.candidate_closed
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval.normalized_evaluates
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Eval.empty_mem
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.RecMem.memberValue_mem
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.RecMem.member_sound
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Iota.rec_pkg
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Group.group_step
#print axioms Rcic.F3.PSet.PointwisePropOnlyPipeline.Group.invariant_step
