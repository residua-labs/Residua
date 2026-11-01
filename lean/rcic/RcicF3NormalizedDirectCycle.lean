import rcic.RcicF3PointwisePropOnlyPlain

/-!
# The actual normalized frame is empty on mandatory direct cycles

Every constructor row contains a depth-zero recursive field. A normalized
constructor tuple in the empty candidate would therefore contain a member
of the empty family fibre. The empty candidate is closed, and leastness
forces the actual normalized intersection frame to be empty at every full
key and every universe vector. Parameter mirrors and reverse reader
normalization do not enter this argument. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormalizedDirectCycle
open Rcic.Declarative RawFamily PiIndex PiValueRule PropEval

def emptyFrame : Frame := fun _ _ => pempty

theorem empty_admissible (P : Premises4) (fd : FamData) :
    Admissible fd emptyFrame := by
  intro vs i
  refine ⟨(stageW4 P _).empty, ?_⟩
  split <;> intro z hz <;> exact (not_mem_pempty hz).elim

/-- Even an ill-fitting complete application of the empty candidate has
no member. The existing application theorem retains the full key. -/
theorem direct_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hf : ∀ A ∈ fd.params ++ fd.indices, occursConst fd.fref A = false)
    (σ : Nat → Nat) (ls : List Level) (args : List (Expr Nat))
    (ha : args.length = fd.params.length + fd.indices.length)
    (ρ : Nat → PSet.{4}) (x : PSet.{4}) :
    ¬ x ∈ Ed (mkM P (table P μ fd emptyFrame))
      (den (mkM P (table P μ fd emptyFrame)) σ ρ
        (foldApps (.const fd.fref ls) args)) := by
  intro hx
  rw [den_foldApps] at hx
  have hh := (apply_updated_mem_iff P μ fd emptyFrame
    (empty_admissible P fd) hf (ls.map (evalTotal σ))
    (args.map (den (mkM P (table P μ fd emptyFrame)) σ ρ))
    (by rw [List.length_map, List.length_append]; exact ha) x).mp hx
  exact not_mem_pempty hh.2

/-- A mandatory direct recursive shape prevents a fitting normalized
field tuple. Other fields, including higher-depth fields, are retained. -/
theorem no_tuple (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hf : ∀ A ∈ fd.params ++ fd.indices, occursConst fd.fref A = false)
    (σ : Nat → Nat) {E : ResolvedEnv} {fuel nu prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (q : EvalPlan.Fields E fuel fd.fref nu fd.params.length
      fd.indices.length prior ss Fs) :
    FieldShape.recursive 0 ∈ ss →
    ∀ (ρ : Nat → PSet.{4}) (xs : List PSet.{4}),
      TelFits (mkM P (table P μ fd emptyFrame)) σ
        ((EvalPlanNormal.specs q).map (fieldExpr fd.fref (canonL nu))) ρ xs →
      False := by
  induction q with
  | nil =>
      intro hs
      exact (List.not_mem_nil _ hs).elim
  | @cons prior s A ss Fs head tail ih =>
      intro hs ρ xs hx
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
          rcases List.mem_cons.mp hs with hs | hs
          · cases hs
            cases head with
            | recursive r =>
                have hds : r.domains = [] := List.length_eq_zero.mp r.depth
                have hx0 : x ∈ Ed (mkM P (table P μ fd emptyFrame))
                    (den (mkM P (table P μ fd emptyFrame)) σ ρ
                      (policyPi r.domains
                        (foldApps (.const fd.fref (canonL nu)) r.arguments))) := hx.1
                rw [hds] at hx0
                exact direct_empty P μ fd hf σ (canonL nu) r.arguments
                  r.argument_count ρ x hx0
          · exact ih hs (vcons x ρ) xs hx.2

/-- Actual admission supplies the family-free telescope and the cached
constructor rows; the empty candidate is closed without a checker. -/
theorem empty_closed (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hcycles : PropShapeCoverage.DirectCycle p.node) :
    Closed P μ (EvalPlanNormal.fd p) emptyFrame := by
  obtain ⟨_, _, hfree, _, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  intro vs i z hc
  obtain ⟨jn, ps, xs, _hp, hx, _⟩ := hc
  let j := EvalPlanNormal.index p jn
  rw [EvalPlanNormal.ctor_get p jn] at hx
  have hs : FieldShape.recursive 0 ∈ (p.constructors j).shapes := by
    rw [(p.constructors j).shapes_admitted]
    exact hcycles j
  exact False.elim (no_tuple P μ (EvalPlanNormal.fd p) hfree (σOf vs)
    (p.constructors j).fields hs (push ps ρ0) xs hx)

/-- Leastness now produces emptiness of the actual normalized frame. -/
theorem frame_no_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hcycles : PropShapeCoverage.DirectCycle p.node)
    (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    ¬ z ∈ frame P μ (EvalPlanNormal.fd p) vs i := by
  intro hz
  exact not_mem_pempty (frame_least P μ (EvalPlanNormal.fd p) emptyFrame
    (empty_admissible P _) (empty_closed P μ p fm ctors hE hmem hcycles)
    vs i z hz)

/-- An actual fitting major at the faithful normalized family cannot
exist. The complete family key and recursor valuation are retained. -/
theorem major_false (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hcycles : PropShapeCoverage.DirectCycle C.node)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (NormPropEval.base P μ C) vs))
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) : False := by
  let p := EvalPlan.ofNode C.node
  obtain ⟨_, _, _, _, _, hBound⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem C.node
  have hRaw : Admissible (famDataOf C.node.a) (NormPropEval.base P μ C) :=
    frame_admissible P μ (EvalPlanNormal.fd p)
      ⟨emptyFrame, empty_admissible P _, empty_closed P μ p fm ctors hE hmem hcycles⟩
  have hz := NormPropEval.major_at_frame P μ C hM hBound hFamily hRaw
    is major hps his hmajor
  exact frame_no_mem P μ p fm ctors hE hmem hcycles _ _ major hz

end Rcic.F3.PSet.NormalizedDirectCycle

#print axioms Rcic.F3.PSet.NormalizedDirectCycle.empty_closed
#print axioms Rcic.F3.PSet.NormalizedDirectCycle.major_false
