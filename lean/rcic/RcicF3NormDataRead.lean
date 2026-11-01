import rcic.RcicF3NormPropCtor
import rcic.RcicF3EvalPlanValue

/-!
# Literal normalized DATA value equations

The canonical faithful constructor equation keeps the original stored
type and original field count at every universe vector. Its endpoint is
independent of the descriptor's normalized field syntax. Family-level
scope moves that equation to the full recursor valuation. The data endpoint
then reads exactly the supplied minors and major from the original tuple.

No constructor membership, frame closure or recursor typing is assumed or
claimed by these read equations. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRead
open Rcic.Declarative Rcic.Model.PS RawFamily

theorem constructor_value_of_group (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E') :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ (j : Fin p.node.a.constructors.length) vs,
      Equiv (μ (p.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
            (p.node.a.constructorViews j).fields.length) ρ0
          (p.node.a.constructors[j.val]).mtype) := by
  dsimp only
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  intro j vs
  have hm : E'.members (f + 1 + j.val) = some (p.node.a.constructors[j.val]) :=
    node_ctor_member p.node j
  have hr : rr = f + 1 + p.node.a.constructors.length := by
    have h := p.node.a.recursorRef
    rw [p.node.fam] at h
    exact h
  have hjr : f + 1 + j.val < rr := by
    exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left j.isLt (f + 1)) hr.symm
  have h := hFaith _ _ hm vs
  rw [hctx _ (dom_of_members hm), NormRole.envCtx_group,
    groupRoles_at_ctor _ _ hjr] at h
  change Equiv (μ (f + 1 + j.val) vs)
    (piLam (mkM P μ) (σOf vs)
      (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
        (nfOf (EvalPlanNormal.fd p) j.val)) ρ0
      (p.node.a.constructors[j.val]).mtype) at h
  rw [NormPropCtor.field_count] at h
  change Equiv (μ (p.node.a.family.ref + 1 + j.val) vs) _
  rw [p.node.fam]
  exact h

theorem constructor_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan)
    (hB : FamBounded (famDataOf p.node.a) p.node.a.family.member.arity)
    (hCB : ∀ j : Fin p.node.a.constructors.length,
      exprLevelsBounded p.node.a.family.member.arity
        (p.node.a.constructors[j.val]).mtype = true)
    (hCtor : ∀ (j : Fin p.node.a.constructors.length) vs,
      Equiv (μ (p.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
            (p.node.a.constructorViews j).fields.length) ρ0
          (p.node.a.constructors[j.val]).mtype))
    (σ : Nat → Nat) (j : Fin p.node.a.constructors.length) :
    Equiv (μ (p.node.a.family.ref + 1 + j.val)
      ((policyFamilyLevels p.node.a.family).map (evalTotal σ)))
      (piLam (mkM P μ) σ (ctorEnd (mkM P μ) σ (famDataOf p.node.a) j.val
        (p.node.a.constructorViews j).fields.length) ρ0
        (p.node.a.constructors[j.val]).mtype) := by
  refine (hCtor j _).trans ?_
  have hst := (p.node.a.constructorViews j).storedType
  rw [hst]
  have hb := hCB j
  rw [hst] at hb
  obtain ⟨hD, _⟩ := levelsBounded_policyPi _ _ _ hb
  have hσ : ∀ i, i < p.node.a.family.member.arity →
      σOf ((policyFamilyLevels p.node.a.family).map (evalTotal σ)) i = σ i :=
    σOf_canon σ p.node.a.family.member.arity
  refine piLam_levels (mkM P μ) hσ (ctorEnd_resp _ _ _ _ _) (fun ρ => ?_)
    _ (fun ρ => ?_) _ hD ρ0
  · unfold ctorEnd
    rw [evalTotal_agree hσ _ hB.res]
    exact Equiv.rfl
  · rw [piLam_foldApps_const, piLam_foldApps_const]
    unfold ctorEnd
    rw [evalTotal_agree hσ _ hB.res]
    exact Equiv.rfl

theorem data_policy {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hType : UniformType a.family.resultLevel) :
    a.policy = .anySort :=
  EliminationSelection.deterministic a.selected (.uniformType hType)

theorem family_vector_bound (vs : List Nat) (ar b : Nat) (hlen : ar ≤ vs.length)
    (hb : ∀ u, u ∈ vs → u ≤ b) :
    ∀ u, u ∈ (canonL ar).map (evalTotal (σOf vs)) → u ≤ b := by
  intro u hu
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  have hi' : i < vs.length := Nat.lt_of_lt_of_le (List.mem_range.mp hi) hlen
  change vs.getD i 0 ≤ b
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  exact hb _ (List.getElem_mem hi')

theorem endpoint_data (M : Interp.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (z : PSet.{4}) (ρ : Nat → PSet.{4})
    (h0 : evalTotal σ p.node.a.family.resultLevel ≠ 0)
    (hms : ms.length = p.node.a.constructors.length)
    (his : is.length = p.node.a.family.indices.length) :
    EvalPlanValue.endValue M σ p (push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ) =
      RecPlan.nodeCore M p.node ms z := by
  rw [EvalPlanValue.endValue_fallback M σ p _ (fun h => h0 h.1)]
  unfold RecPlanValue.endValue
  have h0' : evalTotal σ (famDataOf p.node.a).resLevel ≠ 0 := h0
  rw [cond_neg h0']
  have his' : is.length = (famDataOf p.node.a).indices.length := his
  rw [minorsOf_env ps mo ms is z ρ
    (hms.trans (famDataOf_ctors_length p.node.a).symm) his']
  have hz : push (ps ++ mo :: (ms ++ (is ++ [z]))) ρ 0 = z := by
    rw [push_cons_eq]
    rfl
  rw [hz]
  change RecPlan.core M p.node.a.family.ref (RecPlan.nodePlan p.node) ms z =
    RecPlan.core M p.f (RecPlan.nodePlan p.node) ms z
  rw [p.node.fam]

end Rcic.F3.PSet.NormDataRead
