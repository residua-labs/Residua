import rcic.RcicF3CandidatePrefixFromGroup
import rcic.RcicF3CandidateBoundTuple
import rcic.RcicF3PropEvalCandidateLevels
import rcic.RcicF3PropEvalRawFamily
import rcic.RcicF3PropEvalAdmittedInputs

/-!
# The candidate constructor step

Original candidate constructor fields produce a literal indexed evaluation.
The complete parameter/index key is transported across the family update;
the actual bounded field typings pay reverse normalization, and the actual
stored typed minors consume the produced typed IH spine. No child-evaluation,
normalization, functionality, or recursive-input callback is assumed.

The public producer obtains ordinary prefix facts from the predecessor GInv.
Universal raw-frame admissibility, raw closure/monotonicity and the production
recursor endpoint remain later obligations. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidate
open Rcic.Declarative PiIndex RawFamily PropEval CandidatePrefixFromGroup

/-- The constructor step from the produced ordinary prefix facts. -/
theorem constructor_step_of_prefixes (P : Premises4)
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
    (F : GroupPrefixFacts P μ K C.E C.E' C.f C.rr C.rm fm C.node)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (role P μ (famDataOf C.node.a) vs))
    (hRaw : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
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
  intro vs i z hc hσ hkey
  let fd := famDataOf C.node.a
  let X := candidate P μ C
  let R := frame P μ fd
  have hX : Admissible fd X := admissible P μ C hRaw
  have hsub : FrameSub X R := fun _ _ _ hm => mem_sep_subset hm
  have hERaw := F.rawEnv C.σ C.node.a.family.member.arity
  have hECandidate := F.candidateEnv X hX C.σ C.node.a.family.member.arity
  obtain ⟨j, xs, hpX, hxX, hi, _⟩ := ctorAt_parameters_at P μ fd X
    C.node.a.family.member.arity F.bounded vs C.σ hσ i z hc C.parameters hkey h0
  let j' : Fin C.node.a.constructors.length :=
    ⟨j.val, by simpa only [fd, famDataOf_ctors_length] using j.isLt⟩
  have hget : fd.ctors.get j =
      ((C.node.a.constructorViews j').fields, (C.node.a.constructorViews j').resultIndices) := by
    have hj := famDataOf_ctor C.node.a j'
    rw [List.getElem?_eq_getElem j.isLt] at hj
    exact Option.some.inj hj
  rw [hget] at hxX hi
  have hparam := PiIndependent.telFits_free P μ fd.fref (ofFrame P μ fd X)
    (μ fd.fref) C.σ fd.params
    (fun e he => F.free e (List.mem_append_left _ he)) ρ0 C.parameters
  rw [PiIndependent.upd_self] at hparam
  have hpRaw : TelFits (mkM P μ) C.σ C.node.a.family.parameters ρ0 C.parameters :=
    hparam.mp hpX
  have hxRaw := CandidateBoundFields.field_tuple_raw P μ C.σ K
    hE hfam hctors hrec hmem hBound C.node F.prior.1 F.prior.2 h0 hpolicy
    X R hX hRaw hsub hFamily hERaw hECandidate fullvs hσfull hvs
    j' (C.node.h14.fuelAt j') (C.node.h14.shapesAt j') (C.node.h14.analyzed j')
    C.parameters xs hpRaw hxX
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact Eval.functional_of_boundG C P μ K hE hfam hctors hrec hmem hBound
      hM h0 hpolicy hERaw fullvs hσfull hvs hz hz'
  obtain ⟨endVal, hEnd, hF, hProp⟩ := raw_family_inputs P μ C hM F.bounded hFamily hRaw h0
  have hb := CandidateBoundFields.family_prefix_bodiesOK C.σ K hE hBound.1 hmem
  have hInst := CandidateBoundFields.original_fields_instOK C.σ K
    hE hfam hctors hrec hmem hBound C.node h0 hpolicy fullvs hσfull hvs j'
  have hRawC : EnvSound C.M C.σ K (extendEnv C.E C.f fm) C.node.a.family.member.arity := by
    rw [hM]
    exact hERaw
  have hpC : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters := by
    rw [hM]
    exact hpRaw
  have hxC : TelFits C.M C.σ (C.node.a.constructorViews j').fields
      (push C.parameters ρ0) xs := by
    rw [hM]
    exact hxRaw
  have heval := eval_of_candidate_fields P μ C hM hRaw F.free fm ctors hmem K
    hRawC hECandidate hb F.closedReader v (by rw [hM]; rfl)
    endVal hEnd hF hmo hProp hfunctional hpC hminors j' xs hInst hxC hxX
  have hread := PiIndependent.leafArgs_free P μ fd.fref (ofFrame P μ fd X)
    (μ fd.fref) C.σ (C.node.a.constructorViews j').resultIndices
    (C.node.a.constructorViews j').noFamilyInIndices (push xs (push C.parameters ρ0))
  rw [PiIndependent.upd_self] at hread
  change (C.node.a.constructorViews j').resultIndices.map
      (den (mkM P (table P μ fd X)) C.σ (push xs (push C.parameters ρ0))) =
    (C.node.a.constructorViews j').resultIndices.map
      (den (mkM P μ) C.σ (push xs (push C.parameters ρ0))) at hread
  change i = key (C.parameters ++ (C.node.a.constructorViews j').resultIndices.map
    (den (mkM P (table P μ fd X)) C.σ (push xs (push C.parameters ρ0)))) at hi
  rw [hread] at hi
  have hiC : i = key (C.parameters ++ (C.node.a.constructorViews j').resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
    rw [hM]
    exact hi
  rw [hiC]
  exact heval

/-- The public step producer consumes the actual predecessor invariant and
typed recursor inputs. All candidate-prefix, normalization, child-existence,
typed-IH, and stored-minor composition obligations are discharged internally. -/
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
    (hPred : PlanRole.GInv role P K hE)
    (ctx : Nat → Role) (plans : PlanRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = PlanRole.envPlan hE r)
    (hFaith : PlanRole.Faithful role P μ ctx plans C.E)
    (hReads : ReadsClosed ctx C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (role P μ (famDataOf C.node.a) vs))
    (hRaw : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
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
      EvalPredicate C vs i z :=
  constructor_step_of_prefixes P μ K C hM fm ctors hE hfam hctors hrec hmem hBound
    (group_facts P K μ hE hfam hmem C.node hPred ctx plans hctx hplans hFaith hReads
      hFamily hRaw)
    hFamily hRaw fullvs hσfull hvs h0 hpolicy v hmo hminors

/-- Checked closure composition. The all-instance raw closure and constructor
monotonicity inputs remain explicit; the bounded step alone does not imply them. -/
theorem closed_of_constructor_step (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context)
    (hRaw : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (hClosed : Closed P μ (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (hMono : ConstructorMono P μ (famDataOf C.node.a))
    (hStep : ∀ vs i z, CtorAt P μ (famDataOf C.node.a) (candidate P μ C) vs i z →
      EvalPredicate C vs i z) :
    Closed P μ (famDataOf C.node.a) (candidate P μ C) := by
  intro vs i z hz
  have hR := hClosed vs i z (hMono _ _ (admissible P μ C hRaw) hRaw
    (fun _ _ _ hm => mem_sep_subset hm) vs i z hz)
  obtain ⟨j, hj⟩ := hR
  exact mem_sep.mpr ⟨j, hStep vs i z hz, hj⟩

end Rcic.F3.PSet.PropEvalCandidate
