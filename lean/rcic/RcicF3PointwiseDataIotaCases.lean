import rcic.RcicF3PointwiseDataValue

/-!
# Actual-table original cases for the pointwise DATA interpretation

Membership decodes at the complete parameter/index key. The pointwise
frame's produced density gives normalized cases without local candidate
existence; bounded original-field transport then recovers the actual stored
constructor tuple. Only pointwise equivalence to this same frame update is
used. No global closure or old/raw-frame comparison is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataIotaCases
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval

/-- The same complete key and original tuple are recovered in the actual
installed model. Only pointwise equivalence to its own normalized-family
update is used; no raw-frame comparison is asserted. -/
theorem original_cases_at (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (C : Context)
    (hM : C.M = mkM P μ)
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
    (hpar : ∀ j : Fin C.node.a.constructors.length,
      (C.node.a.constructorViews j).parameters = C.node.a.family.parameters)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a)
        (PointwiseDataCases.frame P μ C.node) vs))
    (hvs : ∀ u, u ∈ (canonL C.node.a.family.member.arity).map (evalTotal C.σ) → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    (i : Index.{4}) (z : PSet.{4})
    (hkey : paramKey C.node.a.family.parameters.length i = key C.parameters)
    (hz : z ∈ PointwiseDataCases.frame P μ C.node
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i) :
    ∃ (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}),
      TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters ∧
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs ∧
      i = key (C.parameters ++ C.indicesAt j C.parameters xs) ∧
      Equiv z (dataVal j.val xs) := by
  let p := EvalPlan.ofNode C.node
  let N := PointwiseDataCases.frame P μ C.node
  let ν := table P μ (famDataOf C.node.a) N
  let D := C.withModel (mkM P ν)
  have hEq : ∀ r vs, Equiv (μ r vs) (ν r vs) :=
    table_equiv P μ (famDataOf C.node.a) N hFamily
  obtain ⟨j, xs, hp, hx, hi, he⟩ :=
    PointwiseDataCases.original_cases P μ K D rfl fm ctors hE hfam hctors hrec hmem
      hBound hBoundD hpar hPred α hα ctx plans hctx hplans hFaith hvs h0
      i z hkey hz
  have hpAt : TelFits (mkM P μ) C.σ C.node.a.family.parameters ρ0 C.parameters :=
    (TelFits_tables_equiv P hEq C.σ _ _ _).mpr hp
  have hxAt : TelFits (mkM P μ) C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs :=
    (TelFits_tables_equiv P hEq C.σ _ _ _).mpr hx
  have hindices : LEq (C.indicesAt j C.parameters xs) (D.indicesAt j D.parameters xs) := by
    change LEq ((C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0))))
      ((C.node.a.constructorViews j).resultIndices.map
        (den (mkM P ν) C.σ (push xs (push C.parameters ρ0))))
    rw [hM]
    exact LEq_map_den_tables _
      (fun e _ => den_tables P hEq C.σ e (fun _ => Equiv.rfl))
  have hkeyAt : i = key (C.parameters ++ C.indicesAt j C.parameters xs) :=
    hi.trans ((key_eq_iff _ _).mpr (LEq_append (LEq.refl C.parameters) hindices.symm))
  exact ⟨j, xs, by simpa only [hM] using hpAt,
    by simpa only [hM] using hxAt, hkeyAt, he⟩

end Rcic.F3.PSet.PointwiseDataIotaCases
