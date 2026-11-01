import rcic.RcicF3PropEvalFrameInputs
import rcic.RcicF3CandidateFieldAdmission

/-!
# Admitted evaluation inputs over a produced admissible base frame

The actual original fields fit both the faithful raw interpretation and the
restriction of N by the same guarded evaluation predicate. The existing
normalized views, input-spine induction and stored-minor derivation are
reused with that restriction. Recursive child existence comes from actual
candidate membership; no evaluation or IH callback is supplied here.

The base's admissibility is an explicit intermediate premise. A subsequent
public producer must instantiate it with the produced normalized frame and
pay constructor closure. No universal StepAG is asserted. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- The actual admission scan and ordinary raw/candidate fields produce the
stored minor's input spine, including its initial motive/minor prefix. -/
theorem inputs_of_admitted_on_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (K : Nat → Nat) {nRaw nCandidate : Nat}
    (hERaw : EnvSound C.M C.σ K (extendEnv C.E C.f fm) nRaw)
    (hECandidate : EnvSound
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C)))
      C.σ K (extendEnv C.E C.f fm) nCandidate)
    (hb : BodiesOK (extendEnv C.E C.f fm) C.σ K)
    (hcl : EnvClosed C.node.E0)
    (v : Level) (hU : C.M.U = U W4)
    (endVal : (Nat → PSet.{4}) → PSet.{4}) (hEnd : EnvResp endVal)
    (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hF : Equiv
      (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (piLam C.M C.σ endVal ρ0
        (policyPi (C.node.a.family.parameters ++ C.node.a.family.indices)
          (.sort C.node.a.family.resultLevel))))
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ z, z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) →
        Equiv z pempty)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z')
    (fuel : Nat) (j : Fin C.node.a.constructors.length)
    (hshapes : fieldShapesFuel C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length C.node.a.family.parameters.length
      (C.node.a.constructorViews j).fields = some (C.node.h14.shapesAt j))
    (xs : List PSet.{4})
    (hI : ∀ A ∈ (C.node.a.constructorViews j).fields,
      InstOK (extendEnv C.E C.f fm) C.σ K A)
    (hxRaw : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    (hxCandidate : TelFits
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C))) C.σ (C.node.a.constructorViews j).fields
        (push C.parameters ρ0) xs) :
    ∃ ys out, Inputs C fuel (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j)
      (C.rootT j) (C.rootCtx j C.parameters) xs ys out := by
  let c := C.node.a.constructorViews j
  let Mc := mkM P (RawFamily.table P μ (famDataOf C.node.a)
    (PropEvalFrame.candidate N C))
  let T : Expr Nat :=
    foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
      (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices)
  let Cert : Nat → Expr Nat → FieldShape → Prop :=
    fun _ A s => PiCleanViews.Clean C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length A s
  obtain ⟨hviews, hcerts⟩ := CandidateFieldAdmission.of_fields c.fields 0
    (C.node.h14.shapesAt j) (by simpa only [Nat.add_zero] using hshapes)
  have hviews' : PiRawFieldViews.Views C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length (1 + j.val) (C.node.h14.shapesAt j)
      (liftFields (1 + j.val) c.fields 0) := by
    simpa only [Nat.zero_add] using hviews.lift hcl 0 (1 + j.val) (Nat.zero_le 0)
  have hcerts' : FieldCertificates Cert (1 + j.val) (C.node.h14.shapesAt j)
      (liftFields (1 + j.val) c.fields 0) := by
    simpa only [Nat.zero_add] using FieldCertificates.lift Cert
      (fun _ A s c a _ h => h.lift hcl c a)
      (C.node.h14.shapesAt j) c.fields 0 hcerts 0 (1 + j.val) (Nat.zero_le 0)
  have hxRaw' : TelFits C.M C.σ (liftFields (1 + j.val) c.fields 0)
      (C.rootCtx j C.parameters) xs := by
    simpa only [C.prefix_length j] using
      (TelFits_liftFields C.M C.σ (C.prefix j) (push C.parameters ρ0) c.fields [] xs).mpr hxRaw
  have hxCandidate' : TelFits Mc C.σ (liftFields (1 + j.val) c.fields 0)
      (C.rootCtx j C.parameters) xs := by
    simpa only [C.prefix_length j] using
      (TelFits_liftFields Mc C.σ (C.prefix j) (push C.parameters ρ0) c.fields [] xs).mpr hxCandidate
  obtain ⟨ys, out, hi⟩ := inputs_of_clean_views_on_frame P μ C hM N hN hf fm ctors hmem K
    hERaw hECandidate hb hcl v hU endVal hEnd hps hF hmo hProp hfunctional fuel
    (C.node.h14.shapesAt j) (liftFields (1 + j.val) c.fields 0) (1 + j.val)
    hviews' hcerts' (C.prefix j) (C.prefix_length j)
    (Rcic.Declarative.lift c.fields.length (1 + j.val) T)
    (C.rootMx j) (C.rootAcc j) xs
    (RawFamilyMinor.instOK_liftFields c.fields hI (1 + j.val) 0)
    (C.rootMx_den j C.parameters) hxRaw' hxCandidate'
  have hT : C.rootT j = policyPi (liftFields (1 + j.val) c.fields 0)
      (Rcic.Declarative.lift c.fields.length (1 + j.val) T) := by
    change Rcic.Declarative.lift 0 (1 + j.val) (policyPi c.fields T) = _
    rw [lift_policyPi, Nat.zero_add]
  refine ⟨ys, out, ?_⟩
  rw [hT]
  exact hi

/-- Actual admission chooses the stored minor and its successful executable
derivation. Candidate ordinary fields then produce an evaluation at their
complete parameter/index key. The minor input is the ordinary typed list. -/
theorem eval_of_frame_fields (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (K : Nat → Nat) {nRaw nCandidate : Nat}
    (hERaw : EnvSound C.M C.σ K (extendEnv C.E C.f fm) nRaw)
    (hECandidate : EnvSound
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C)))
      C.σ K (extendEnv C.E C.f fm) nCandidate)
    (hb : BodiesOK (extendEnv C.E C.f fm) C.σ K)
    (hcl : EnvClosed C.node.E0)
    (v : Level) (hU : C.M.U = U W4)
    (endVal : (Nat → PSet.{4}) → PSet.{4}) (hEnd : EnvResp endVal)
    (hF : Equiv
      (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (piLam C.M C.σ endVal ρ0
        (policyPi (C.node.a.family.parameters ++ C.node.a.family.indices)
          (.sort C.node.a.family.resultLevel))))
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ z, z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) →
        Equiv z pempty)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z')
    (hparameters : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4})
    (hI : ∀ A ∈ (C.node.a.constructorViews j).fields,
      InstOK (extendEnv C.E C.f fm) C.σ K A)
    (hxRaw : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    (hxCandidate : TelFits
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C))) C.σ (C.node.a.constructorViews j).fields
        (push C.parameters ρ0) xs) :
    ∃ z, Eval C (key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0))))) z := by
  obtain ⟨shapes, fuel, hshapes, hderived⟩ := C.node.h12 j
  have hsame : shapes = C.node.h14.shapesAt j :=
    fieldShapesFuel_unique hshapes (C.node.h14.analyzed j)
  subst shapes
  have hj : j.val < C.node.a.minorTypes.length := by
    rw [C.node.a.minorCount]
    exact j.isLt
  let R := C.node.a.minorTypes[j.val]'hj
  have hstored : C.node.a.minorTypes[j.val]? = some R :=
    List.getElem?_eq_getElem hj
  have hderived' : derivedMinor C.node.a j fuel (C.node.h14.shapesAt j) = some R :=
    hderived.trans hstored
  have hminor : C.minors.getD j.val pempty ∈
      Ed C.M (den C.M C.σ (C.rootCtx j C.parameters) R) := by
    have hm := TelFits_get C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors hminors j.val hj
    simpa only [Context.rootCtx, Context.prefix, push, R] using hm
  obtain ⟨ys, out, hinputs⟩ := inputs_of_admitted_on_frame P μ C hM N hN hf fm ctors hmem K
    hERaw hECandidate hb hcl v hU endVal hEnd hparameters.length hF hmo hProp hfunctional
    fuel j hshapes xs hI hxRaw hxCandidate
  refine ⟨fapps (C.minors.getD j.val pempty) ys, ?_⟩
  exact Eval.root j C.parameters xs ys fuel R out _ hparameters
    (LEq.refl C.parameters) hxRaw hshapes hstored hderived' hminor hinputs Equiv.rfl

end Rcic.F3.PSet.PropEval
