import rcic.RcicF3PointwiseDataFinite

/-!
# Finite DATA without a constructor-to-recursor bound comparison

The actual NoFunRec candidate is small and closed at every universe world.
Its projection therefore closes the pointwise frame at every constructor
invocation directly. The original bound K is never replaced or reordered.
This removes the D check from the finite DATA producer; no local-candidate
or reader-soundness callback is assumed.

The general finite group theorem still displays syntactic constructor
parameter equality and the original GroupStepAt walk premise. The empty
constructor subcase below produces both vacuously and yields the literal
PointwiseRole.GInv under the same original BoundG/BoundDG and predecessor.
It does not close arbitrary DATA. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteOriginal
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The already-produced global finite candidate pays pointwise closure
at every vector, with no numeric comparison between member bounds. -/
theorem frame_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hFinite : NoFunRec p.node) :
    Closed P μ (EvalPlanNormal.fd p) (PointwiseDataLocal.frame P μ p) := by
  have h := NormFiniteFamily.package_of_group P μ p fm ctors hE hmem hFinite
  intro vs
  exact PointwiseData.frame_closed_at P μ p fm ctors hE hmem vs
    (PointwiseData.exists_of_candidate P μ p fm ctors hE hmem
      (RawFiniteFrame.candidate P μ (EvalPlanNormal.fd p)) h.candidateAdmissible
      (PiSmallFrame.canonical p.node.a.family.member.arity vs)
      (PiSmallFrame.canonical_idem _ vs) (h.candidateClosed _))

/-- The actual constructor walk uses all-world finite closure. -/
theorem prefix_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    (∀ r m, E'.members r = some m → r ≠ rr → MemberSound P μ K r m) ∧
      (∀ σ n, EnvSound (mkM P μ) σ K p.node.E0 n) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  let N := PointwiseDataLocal.frame P μ p
  have hN : Admissible (EvalPlanNormal.fd p) N :=
    PointwiseDataLocal.admissible P μ p fm ctors hE hmem
  have hFacts := PointwiseGroupFacts.canonical_group_facts P K μ hE hfam hctors
    hrec hmem hPred α hα ctx plans hctx hplans hFaith hType
  have hFamily := PointwiseRoleEquations.family_equation_of_group P α μ hE hfam
    hctors hrec hmem hα ctx plans hctx hFaith hType
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hlen := node_ctors_length p.node hrr
  have hfm : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hbf : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hty : fm.mtype = famType (EvalPlanNormal.fd p) := hFacts.familyType
  have hfS : MemberSound P μ K f fm := by
    intro σ ls ρ hls _
    refine ⟨?_, fun b hb => by rw [hbf] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
      (hFacts.facts f fm hfm).1 (hls ▸ (hFacts.facts f fm hfm).2.1), hty]
    have hf : Equiv (μ f (ls.map (evalTotal σ)))
        (ofFrame P μ (EvalPlanNormal.fd p) N (ls.map (evalTotal σ))) := by
      have h := hFamily (ls.map (evalTotal σ))
      change Equiv (μ p.node.a.family.ref (ls.map (evalTotal σ)))
        (ofFrame P μ (EvalPlanNormal.fd p) N (ls.map (evalTotal σ))) at h
      rw [p.node.fam] at h
      exact h
    exact mem_congr_left hf.symm (ofFrame_mem P μ (EvalPlanNormal.fd p) N hN _)
  have hI : ∀ r m, E'.members r = some m → r ≠ rr →
      m.mclass = .recursorM → IotaAt P μ K E' r := by
    intro r m hm hne hk
    rcases group_member_cases hmem hL hrr p.node hm with
      hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    · exact hFacts.prior.2 r m hold hk
    · rw [hfam] at hk
      cases hk
    · exact (hne rfl).elim
    · rw [(p.node.a.constructorViews j).hasClass] at hk
      cases hk
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (famO : PolicyFamilyView Ew) (cv : PolicyConstructorView Ew famO m),
      (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → Ew.members r = none →
      Ew.members rr = none → FieldUniverseAdmitted cv →
      AgreeAt p.node.a.family.parameters.length Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity →
        (∀ v, v ∈ vs → v ≤ K r) → ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity
            (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
              LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh hnrr h07 hag hB2 hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' :=
      fun r' m' hm => hsubw r' m' (members_extend_preserved hfresh r' m' hm)
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin p.node.a.constructors.length,
        r = f + 1 + i.val ∧ m = p.node.a.constructors[i.val] := by
      rcases List.mem_cons.mp hin with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [hfam] at hkC
        cases hkC
      · rcases List.mem_append.mp h with hc | hr
        · have href : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, hc, rfl⟩
          rw [hL] at href
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp href
          have hi' : i < p.node.a.constructors.length := by
            rw [hlen]
            exact List.mem_range.mp hi
          exact ⟨⟨i, hi'⟩, rfl, Option.some.inj
            ((groupMembersT_installed hmem hin).symm.trans (node_ctor_member p.node ⟨i, hi'⟩))⟩
        · rw [List.mem_singleton] at hr
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
          rw [hrec] at hkC
          cases hkC
    obtain ⟨i, rfl, rfl⟩ := hctor
    have hESw : ∀ σ n, EnvSound (mkM P μ) σ K Ew n := by
      intro σ n
      refine envSound_of P (Efin := E') hEw hAw ?_ σ n
      intro r m hm hk
      exact hI r m (hEw r m hm) (fun he => by rw [he, hnrr] at hm; cases hm) hk
    have hvalue : ∀ vs, Equiv (μ (f + 1 + i.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) i.val
            (nfOf (EvalPlanNormal.fd p) i.val)) ρ0
          (p.node.a.constructors[i.val]).mtype) := by
      intro vs
      have hc : E'.members (f + 1 + i.val) =
          some (p.node.a.constructors[i.val]) := node_ctor_member p.node i
      have h := hFaith _ _ hc vs
      have hir : f + 1 + i.val < rr := by
        have hi : i.val < ctors.length := Nat.lt_of_lt_of_eq i.isLt hlen
        omega
      rw [hctx _ (dom_of_members hc), NormRole.envCtx_group,
        groupRoles_at_ctor _ _ hir] at h
      exact h
    have hClosed : ∀ (σ : Nat → Nat) (ls : List Level),
        ls.length = (p.node.a.constructors[i.val]).arity →
        (∀ l, l ∈ ls → evalTotal σ l ≤ K (p.f + 1 + i.val)) →
        ∀ q z, CtorAt P μ (EvalPlanNormal.fd p) N (ls.map (evalTotal σ)) q z →
          z ∈ N (ls.map (evalTotal σ)) q := by
      intro σ ls _ _
      exact frame_closed P μ p fm ctors hE hmem hFinite (ls.map (evalTotal σ))
    exact PointwiseDataCtor.constructor_at_walk P μ K p i famO cv hEw N hN hClosed
      hFamily hvalue
      (fun vs => PointwiseRoleEquations.bodyEquations_at_node P α μ ctx plans hE hfam hctors
        hrec hmem hctx hFaith p.node (σOf vs))
      hFacts.facts (groupMembersT_body_none hmem _ _ (node_ctor_mem hmem hL hrr p.node i))
      h07 hag hFacts.rawEnv hESw (hBound.2.1 p.node i) hB2
  have hAll : ∀ r m, E'.members r = some m → r ≠ rr → MemberSound P μ K r m := by
    refine NormDataPrefix.walk_before_rec P μ K ((f, fm) :: ctors ++ [(rr, rm)])
      (AgreeAt p.node.a.family.parameters.length) ?_ hfS hcS
      ((f, fm) :: ctors) hmem ?_ ?_ (fun _ _ h => h)
      (walkRec_of_group hmem) (hAg p.node) hBound.2.2.1 hFacts.prior.1
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · rcases List.mem_append.mp h with hc | hr
        · rw [hctors c hc] at hk
          cases hk
        · rw [List.mem_singleton] at hr
          subst c
          rw [hrec] at hk
          cases hk
    · intro c hc
      rcases List.mem_cons.mp hc with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ h))
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · subst c
        rw [hfam] at hk
        cases hk
      · rw [hctors c h] at hk
        cases hk
  refine ⟨hAll, ?_⟩
  intro σ n
  have hsub := node_sub' p.node
  have hfresh : p.node.E0.members rr = none := p.node.fresh
  have hne : ∀ r m, p.node.E0.members r = some m → r ≠ rr :=
    fun r m hm he => by rw [he, hfresh] at hm; cases hm
  exact envSound_of P (Efin := E') hsub
    (fun r m hm => hAll r m (hsub r m hm) (hne r m hm))
    (fun r m hm hk => hI r m (hsub r m hm) (hne r m hm) hk) σ n

/-- Stored members use the same original bounds and produced prefix reader. -/
theorem all_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    AllSound P μ K E' := by
  have hPrefix := prefix_sound P μ K hE hfam hctors hrec hmem
    hAg hBound hPred α hα ctx plans hctx hplans hFaith hFinite hType
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hR := PointwiseDataRecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred α hα ctx plans hctxE hplansE hFaithE
    ctx plans hctx hplans hFaith hType
    (fun fullvs _ _ => hPrefix.2 (σOf fullvs) _)
  have hrm : E'.members rr = some rm := groupMembersT_installed hmem
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  intro r m hm
  by_cases hr : r = rr
  · subst r
    have hm' : m = rm := Option.some.inj (hm.symm.trans hrm)
    subst m
    exact hR
  · exact hPrefix.1 r m hm hr

/-- The actual finite DATA group producer has no W/D checker argument.
Its GroupStepAt result retains the original walk and bounds. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hpar : ∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro hAg hBound hBoundD hPred α hα ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hAll := all_sound P μ K hE hfam hctors hrec hmem
    hAg hBound hBoundD hPred α hα ctx plans hctx hplans hFaith hFinite hpar hType
  have hIota := PointwiseDataRecPkg.iota_at P μ K hE hfam hctors hrec hmem
    hBound hBoundD hpar hPred α hα ctx plans hctx hplans hFaith hType
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono hsubE
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (hsubE r m hm)
  have hPrior := hPred α hαE ctx hctxE plans hplansE μ hFaithE
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  refine ⟨hAll, ?_⟩
  intro Efin hsub r m hm hk
  rcases group_member_cases hmem hL hrr p.node hm with
    hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · exact hPrior.2 Efin (fun s n hn => hsub s n (hsubE s n hn)) r m hold hk
  · rw [hfam] at hk
    cases hk
  · exact hIota Efin hsub
  · rw [(p.node.a.constructorViews j).hasClass] at hk
    cases hk

/-- A walk containing no constructor-class member needs no level agreement. -/
theorem walkAgree_of_no_constructors
    (agree : ∀ (Ew : ResolvedEnv) (fam : PolicyFamilyView Ew) (m : CheckedMember),
      PolicyConstructorView Ew fam m → Prop)
    {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S E ms E') →
    (∀ c ∈ ms, c.2.mclass ≠ .constructorM) → WalkAgree agree hw
  | _, _, _, .nil _, _ => True.intro
  | _, _, _, .cons _ r m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest, hnone => by
      refine ⟨?_, walkAgree_of_no_constructors agree hrest
        (fun c hc => hnone c (List.mem_cons_of_mem _ hc))⟩
      cases hadm with
      | family _ _ _ _ _ => trivial
      | recursor _ _ _ _ _ _ _ => trivial
      | constructor fam cv _ _ _ _ _ =>
          exact False.elim (hnone (r, m) (List.mem_cons_self _ _) cv.hasClass)

/-- Empty DATA groups are a fully produced original-domain case. Neither
walk agreement nor parameter equality nor either check is a premise. -/
theorem invariant_step_empty (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ([] : List (Nat × CheckedMember)), c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: [] ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hBound : BoundG K (EnvWfT.group E f fm [] rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm [] rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm [] rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨_, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hzero : p.node.a.constructors.length = 0 :=
    node_ctors_length (ctors := []) p.node hrr
  have hnone : ∀ i : Fin p.node.a.constructors.length, False :=
    fun i => Nat.not_lt_zero i.val (Nat.lt_of_lt_of_eq i.isLt hzero)
  have hFinite : NoFunRec p.node := fun i => (hnone i).elim
  have hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters :=
    fun j => (hnone j).elim
  apply group_step P K hE hfam hctors hrec hmem hType hFinite hpar
    ?_ hBound hBoundD hPred
  intro node
  apply walkAgree_of_no_constructors (AgreeAt node.a.family.parameters.length) hmem
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · subst c
    rw [hfam]
    exact fun h => MemberClass.noConfusion h
  · have hc' : c = (rr, rm) := List.mem_singleton.mp h
    subst c
    rw [hrec]
    exact fun h => MemberClass.noConfusion h

end Rcic.F3.PSet.PointwiseDataFiniteOriginal

#print axioms Rcic.F3.PSet.PointwiseDataFiniteOriginal.frame_closed
#print axioms Rcic.F3.PSet.PointwiseDataFiniteOriginal.group_step
#print axioms Rcic.F3.PSet.PointwiseDataFiniteOriginal.invariant_step_empty
