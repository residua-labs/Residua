import rcic.RcicF3NormFiniteFamily
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3NormDRec

/-!
# Actual normalized family and stored-value equations on the D fallback face

The admitted cache produces the finite-family package. Faithfulness of the
new canonical interpretation then gives the normalized limit at every
universe vector and soundness of the original stored family member. The
bounded D stage connects that limit to the original constructor operator.

Constructor values retain their original stored type and field count. The
recursor equation is proved only on the literal data/propOnly fallback;
the indexed Prop/anySort endpoint remains a separate typed producer. No
legacy invariant, raw all-instance family equality, or semantic callback
is assumed. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDFaith
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder RawFamily

section
variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})
  {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
  {ctors : List (Nat × CheckedMember)}
  (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
  (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
  (hrec : rm.mclass = .recursorM)
  (hmem : GroupMembersT (extendEnv E f fm) E
    ((f, fm) :: ctors ++ [(rr, rm)]) E')
  (ctx : Nat → Role) (plans : EvalRole.Plans)
  (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
    (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
  (hFaith : EvalRole.Faithful role P μ ctx plans E')
  (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)

include hctx hFaith hN

/-- The actual installed family is the normalized finite limit at every
complete universe vector. The stored type is not normalized or replaced. -/
theorem family_limit :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (famLim P μ (nodeFam p.node) vs) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  change ∀ vs : List Nat, Equiv (μ p.node.a.family.ref vs)
    (famLim P μ (nodeFam p.node) vs)
  have hF := NormCandidatePrefix.family_equation_of_group P μ hE hfam hctors
    hrec hmem ctx plans hctx hFaith
  have hPkg := NormFiniteFamily.package_of_group P μ p fm ctors hE hmem hN
  have he := NormDPlanBridge.normalized_descriptor p
    (NormDPlanBridge.bodies_of_group hE hmem p.node) hN
  intro vs
  have h := (hF vs).trans (hPkg.value vs)
  rw [he] at h
  exact h

/-- Admissibility produced from this same admitted node pays the family
member at every bound K; there is no bound on the frame construction. -/
theorem family_member_sound (K : Nat → Nat) : MemberSound P μ K f fm := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hF := NormCandidatePrefix.family_equation_of_group P μ hE hfam hctors
    hrec hmem ctx plans hctx hFaith
  have hA := (NormFiniteFamily.package_of_group P μ p fm ctors hE hmem hN).admissible
  obtain ⟨_, hty, _, hTF, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  change fm.mtype = famType (EvalPlanNormal.fd p) at hty
  have hfm : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  intro σ ls ρ hlen _hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
    (hTF f fm hfm).1 (hlen ▸ (hTF f fm hfm).2.1), hty]
  have hf : Equiv (μ f (ls.map (evalTotal σ)))
      (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) := by
    have h := hF (ls.map (evalTotal σ))
    change Equiv (μ p.node.a.family.ref (ls.map (evalTotal σ)))
      (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) at h
    simpa only [p.node.fam] using h
  exact mem_congr_left hf.symm
    (ofFrame_mem P μ (EvalPlanNormal.fd p)
      (frame P μ (EvalPlanNormal.fd p)) hA _)

/-- Constructor installation agrees with the original endpoint at all
universe vectors. Read uniqueness pays the exact descriptor and count. -/
theorem constructor_value
    (j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length)
    (vs : List Nat) :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    Equiv (μ (f + 1 + j.val) vs)
      (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
          (nfOf (famDataOf p.node.a) j.val)) ρ0
        (p.node.a.constructors[j.val]).mtype) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  change Equiv (μ (f + 1 + j.val) vs)
    (piLam (mkM P μ) (σOf vs)
      (ctorEnd (mkM P μ) (σOf vs) (famDataOf p.node.a) j.val
        (nfOf (famDataOf p.node.a) j.val)) ρ0
      (p.node.a.constructors[j.val]).mtype)
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hlen := node_ctors_length p.node hrr
  have hjr : f + 1 + j.val < rr := by
    have hj : j.val < ctors.length := Nat.lt_of_lt_of_eq j.isLt hlen
    omega
  have hm : E'.members (f + 1 + j.val) = some (p.node.a.constructors[j.val]) :=
    node_ctor_member p.node j
  have h := hFaith _ _ hm vs
  rw [hctx _ (dom_of_members hm), NormRole.envCtx_group,
    groupRoles_at_ctor _ _ hjr] at h
  change Equiv (μ (f + 1 + j.val) vs)
    (piLam (mkM P μ) (σOf vs)
      (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
        (nfOf (EvalPlanNormal.fd p) j.val)) ρ0
      (p.node.a.constructors[j.val]).mtype) at h
  have hFF := NormDPlanBridge.bodies_of_group hE hmem p.node
  have he := NormDPlanBridge.normalized_descriptor p hFF hN
  have hData := nodeFam_recDataAgree p.node hFF hN
  rw [he, hData.nfOf_agree, hData.ctorEnd_eq] at h
  exact h

end

/-- Actual admission turns the logical fallback case into the pointwise
condition used by the installed endpoint, including its extra universe. -/
theorem fallback_at {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hFallback : ¬ (UniformProp node.a.family.resultLevel ∧ node.a.policy = .anySort))
    (σ : Nat → Nat) :
    ¬ (evalTotal σ node.a.family.resultLevel = 0 ∧ node.a.policy = .anySort) := by
  intro h
  rcases selection_uniform node.a with hp | ht
  · exact hFallback ⟨hp, h.2⟩
  · exact Nat.ne_of_gt (ht σ) h.1

/-- The bounded family and all-instance stored constructor/recursor
equations are supplied by the same normalized faithful table. This
record is only for the actual data/propOnly fallback face. -/
theorem group_faith (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hFallback : ¬ (UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel ∧
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort))
    (D : DStage P K (EvalPlan.ofGroup hE hfam hctors hrec hmem).node μ) :
    GroupFaithB P μ K fm (EvalPlan.ofGroup hE hfam hctors hrec hmem).node := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨_, hty, _, hTF, _, hBound⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hlim := family_limit P μ hE hfam hctors hrec hmem ctx plans hctx hFaith hN
  refine ⟨?_, ?_, ?_, hty, hBound, ?_⟩
  · intro vs hvs hlen
    rw [hty]
    change Equiv (μ f vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf p.node.a))
    have h := NormDRec.famB_normal D hlim vs hvs hlen
    change Equiv (μ p.node.a.family.ref vs)
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf p.node.a)) at h
    rw [p.node.fam] at h
    exact h
  · intro j vs
    exact constructor_value P μ hE hfam hctors hrec hmem ctx plans hctx hFaith hN j vs
  · intro vs
    have hrm : E'.members rr = some rm :=
      groupMembersT_installed hmem
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
    have hlt : f < rr := by
      have hr := p.node.a.recursorRef
      rw [p.node.fam] at hr
      change rr = f + 1 + p.node.a.constructors.length at hr
      rw [hr]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self f)
        (Nat.le_add_right (f + 1) p.node.a.constructors.length)
    have h := hFaith rr rm hrm vs
    rw [hctx rr (dom_of_members hrm), NormRole.envCtx_group hE hfam hctors hrec hmem,
      groupRoles_at_rr _ hlt] at h
    have hp : plans rr = some p := by
      rw [hplans rr (dom_of_members hrm)]
      change (if rr = rr then some p else EvalRole.envPlan hE rr) = some p
      exact if_pos rfl
    rw [hp] at h
    change Equiv (μ rr vs) (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p rm) at h
    rw [NormDPlanBridge.member_fallback (mkM P μ) (σOf vs) p
      (NormDPlanBridge.bodies_of_group hE hmem p.node) hN
      (fallback_at p.node hFallback (σOf vs)) rm] at h
    exact h
  · intro j
    have hb := (hTF _ _ (node_ctor_member p.node j)).2.1
    rw [(p.node.a.constructorViews j).arity] at hb
    exact hb

end Rcic.F3.PSet.NormDFaith
