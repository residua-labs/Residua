import rcic.RcicF3NormDataValue

/-!
# Actual-table DATA family decoding and original constructor cases

A member of a complete installed family application supplies its fitting
parameter/index telescope and its exact normalized-frame key. The decoder
retains the full valuation while comparing only the family's universe slots.
The original-case wrapper transports the already produced normalized cases
back from the equivalent frame update to the actual installed table.

The small normalized candidate remains explicit. No equality with a raw
fixed point, recursor-soundness or iota premise is used. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataIotaCases
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval

/-- Membership itself supplies the complete fitting family telescope. -/
theorem application_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (A : Frame) (ar : Nat)
    (hA : Admissible fd A) (hB : FamBounded fd ar)
    (hFamily : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd A vs))
    (σ : Nat → Nat) (xs : List PSet.{4}) (z : PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length)
    (hz : z ∈ Ed (mkM P μ)
      (fapps (μ fd.fref ((canonL ar).map (evalTotal σ))) xs)) :
    TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 xs ∧
      z ∈ A ((canonL ar).map (evalTotal σ)) (key xs) := by
  let vs := (canonL ar).map (evalTotal σ)
  have hrole : z ∈ Ed (mkM P μ) (fapps (ofFrame P μ fd A vs) xs) :=
    mem_congr_right (ed_congr (mkM P μ) (fapps_congr (hFamily vs) xs)) hz
  have hn : ¬ Equiv (fapps (ofFrame P μ fd A vs) xs) pempty := by
    intro he
    exact not_mem_pempty (mem_congr_right
      ((ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))) hrole)
  have hfit : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs :=
    fits_of_fapps_ne (mkM P μ) (σOf vs)
      (endValue_resp A vs (fd.params.length + fd.indices.length))
      (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 xs hl hn
  have hσ : ∀ k, k < ar → σ k = σOf vs k :=
    fun k hk => (σOf_canon σ ar k hk).symm
  have hdomains : ExprsBounded ar (fd.params ++ fd.indices) := by
    intro e he
    rcases List.mem_append.mp he with hp | hi
    · exact hB.params e hp
    · exact hB.indices e hi
  exact ⟨(TelFits_levels (mkM P μ) hσ _ hdomains ρ0 xs).mpr hfit,
    mem_congr_right (apply_ofFrame_ed P μ fd A hA vs xs hfit) hrole⟩

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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))) vs))
    (hsmall : ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) A)
    (hvs : ∀ u, u ∈ (canonL C.node.a.family.member.arity).map (evalTotal C.σ) → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    (i : Index.{4}) (z : PSet.{4})
    (hkey : paramKey C.node.a.family.parameters.length i = key C.parameters)
    (hz : z ∈ frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i) :
    ∃ (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}),
      TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters ∧
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs ∧
      i = key (C.parameters ++ C.indicesAt j C.parameters xs) ∧
      Equiv z (dataVal j.val xs) := by
  let p := EvalPlan.ofNode C.node
  let N := frame P μ (EvalPlanNormal.fd p)
  let ν := table P μ (famDataOf C.node.a) N
  let D := C.withModel (mkM P ν)
  have hN := frame_admissible P μ (EvalPlanNormal.fd p) hsmall
  have hClosed := frame_closed_of_mono P μ (EvalPlanNormal.fd p) hsmall
    (EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem)
  have hEq : ∀ r vs, Equiv (μ r vs) (ν r vs) :=
    table_equiv P μ (famDataOf C.node.a) N hFamily
  obtain ⟨j, xs, hp, hx, hi, he⟩ :=
    NormDataCases.original_cases P μ K D rfl fm ctors hE hfam hctors hrec hmem
      hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hN hClosed hvs h0
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

end Rcic.F3.PSet.NormDataIotaCases
