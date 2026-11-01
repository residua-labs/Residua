import rcic.RcicF3PropEvalNormalTotal
import rcic.RcicF3PropEvalValue
import rcic.RcicF3PropEvalMotiveGuard

/-!
# Typed indexed result from the produced normalized candidate

Actual typed parameters, indices and the raw-family major yield evaluation
existence at their full key. The actual BoundG Prop clause supplies
functionality, and the typed motive supplies bounded membership. The
bounded extractor therefore evaluates and belongs to the motive at that
major. No existence, functionality, motive-guard, raw-closure, or raw-
monotonicity callback remains in the public composition theorem.

This is the Prop/anySort scalar endpoint. The complete stored recursor
abstraction, iota package and data-face producer remain separate work.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalNormalized
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval PropEvalCandidate

/-- A complete fitting application decodes into the unchanged raw frame.
The canonical family vector agrees with the full recursor valuation only
on family slots; the extra motive universe is not truncated in the context. -/
theorem major_at_frame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Context) (hM : C.M = mkM P μ)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (role P μ (famDataOf C.node.a) vs))
    (hRaw : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (is : List PSet.{4}) (z : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hz : z ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) :
    z ∈ frame P μ (famDataOf C.node.a)
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))
      (key (C.parameters ++ is)) := by
  let fd := famDataOf C.node.a
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hσ : ∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u :=
    canonical_agreement C
  have hfit : TelFits (mkM P μ) C.σ (fd.params ++ fd.indices) ρ0
      (C.parameters ++ is) := by
    rw [← hM]
    exact hps.append his
  have hfitVs : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0
      (C.parameters ++ is) :=
    (TelFits_levels (mkM P μ) hσ (fd.params ++ fd.indices)
      (fun e he => by
        rcases List.mem_append.mp he with hp | hi
        · exact hB.params e hp
        · exact hB.indices e hi) ρ0 (C.parameters ++ is)).mp hfit
  rw [hM] at hz
  have hrole := mem_congr_right
    (ed_congr (mkM P μ) (fapps_congr (hFamily vs) (C.parameters ++ is))) hz
  exact mem_congr_right
    (apply_ofFrame_ed P μ fd (frame P μ fd) hRaw vs (C.parameters ++ is) hfitVs) hrole

/-- Existence, guarded typing and functionality are all produced from the
actual admitted group and typed recursor arguments. The output contains
the evaluation and its exact requested dependent motive membership. -/
theorem result_spec (P : Premises4)
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
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom C.E' r →
      ctxFull r = envCtx (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful role P μ ctxFull plansFull C.E')
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) :
    PropEvalValue.result C v (key (C.parameters ++ is)) ∈
        childCarrier C v (key (C.parameters ++ is)) ∧
    Eval C (key (C.parameters ++ is)) (PropEvalValue.result C v (key (C.parameters ++ is))) ∧
    PropEvalValue.result C v (key (C.parameters ++ is)) ∈
        Ed C.M (fapps C.motive (is ++ [major])) := by
  have hRaw := EvalCandidateStep.raw_admissible P μ C h0 hpolicy
  have F := EvalCandidatePrefix.group_facts P K μ hE hfam hmem C.node
    hPred ctx plans hctx hplans hFaith hFamily hRaw
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hmajorR := major_at_frame P μ C hM F.bounded hFamily hRaw is major hps his hmajor
  have hkey : paramKey C.node.a.family.parameters.length (key (C.parameters ++ is)) =
      key C.parameters := by
    rw [← hps.length]
    exact paramKey_append C.parameters is
  have hex := raw_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hPred ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs h0 hpolicy v hmo hminors ctxFull plansFull hctxFull hFaithFull vs
    (key (C.parameters ++ is)) major hmajorR (canonical_agreement C) hkey
  obtain ⟨_, _, _, hProp⟩ := raw_family_inputs P μ C hM F.bounded hFamily hRaw h0
  have hU : C.M.U = U W4 := by rw [hM]; rfl
  have hguard : ∀ i z, Eval C i z → z ∈ childCarrier C v i := by
    intro i z hz
    exact hz.mem_guarded_of_typed_motive v hU hmo hProp
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact Eval.functional_of_boundG C P μ K hE hfam hctors hrec hmem hBound
      hM h0 hpolicy (F.rawEnv C.σ C.node.a.family.member.arity)
      fullvs hσfull hvs hz hz'
  have hs := PropEvalValue.result_spec C v (key (C.parameters ++ is)) hex
    (hguard _) (hfunctional _)
  have hproof : Equiv major pempty := hProp (C.parameters ++ is)
    (by rw [List.length_append, hps.length, his.length]) major hmajor
  exact ⟨hs.1, hs.2, PropEvalValue.result_mem_motive C v is major hU hps.length
    hmo his hmajor hproof hs.1⟩

end Rcic.F3.PSet.PropEvalNormalized
