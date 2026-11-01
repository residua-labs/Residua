import rcic.RcicF3NormPropEvalStep

/-!
# Produced candidate closure and totality for the normalized family role

The actual admitted normalized frame is small and closed on this Prop face.
The constructor producer proves its guarded evaluation candidate closed.
Leastness supplies evaluation at every reached full valuation/parameter key.
The predecessor invariant is NormRole.GInv throughout.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate

/-- Checked composition: both candidate admissibility and its global
constructor closure are produced for the normalized operator. -/
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
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
    Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (candidate P μ C) ∧
    Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (candidate P μ C) := by
  let p := EvalPlan.ofNode C.node
  obtain ⟨hN, hClosed⟩ := EvalPlanNormalProp.normalized_closed P μ p fm ctors hE hmem
    C.σ h0 hpolicy
  have hX : Admissible (EvalPlanNormal.fd p) (candidate P μ C) :=
    PropEvalFrame.admissible P C (base P μ C) hN
  have hStep := constructor_step P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hPred ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs h0 hpolicy v hmo hminors
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
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
    ∀ vs i z, z ∈ base P μ C vs i → EvalPredicate C vs i z := by
  obtain ⟨hX, hClosed⟩ := candidate_closed P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hPred ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs h0 hpolicy v hmo hminors
  intro vs i z hz hσ hp
  exact PropEvalFrame.exists_of_mem C (base P μ C) vs i z
    (frame_least P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (candidate P μ C) hX hClosed vs i z hz) hσ hp

end Rcic.F3.PSet.NormPropEval
