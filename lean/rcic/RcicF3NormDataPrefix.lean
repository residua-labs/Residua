import rcic.RcicF3NormDataCtor
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3EvalPlanNormalMono

/-!
# Constructor-walk soundness before the new DATA recursor

The actual walk installs the family and constructors before its final
recursor. Their soundness uses the normalized closed frame and the original
bounded field derivations. Only predecessor recursors occur in these walk
environments, so their iota facts come from the predecessor invariant.

This produces ordinary soundness of the actual recursor reader environment
without assuming the new recursor's membership or iota package. A small
closed normalized candidate remains the explicit size-production input.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.NormDataPrefix
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Walk only the prefix preceding the final recursor. The new recursor's
soundness is absent from both inputs and conclusion. -/
theorem walk_before_rec (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {S E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} (full : List (Nat × CheckedMember))
    (agree : ∀ (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew) (m : CheckedMember),
      PolicyConstructorView Ew famO m → Prop)
    (hcl : ∀ c, c ∈ full → c.2.mclass = .inductiveM → c = (f, fm))
    (hfS : MemberSound P μ K f fm)
    (hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (famO : PolicyFamilyView Ew) (cv : PolicyConstructorView Ew famO m),
      (r, m) ∈ full → Ew.members r = none → Ew.members rr = none →
      FieldUniverseAdmitted cv → agree Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity →
        (∀ v, v ∈ vs → v ≤ K r) → ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity
            (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
              LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m) :
    {Ew E'' : ResolvedEnv} → (pre : List (Nat × CheckedMember)) →
    (hw : GroupMembersT S Ew (pre ++ [(rr, rm)]) E'') →
    (∀ c, c ∈ pre → c ∈ full) →
    (∀ c, c ∈ pre → c.2.mclass ≠ .recursorM) →
    (∀ r m, E''.members r = some m → E'.members r = some m) →
    WalkRec hw → WalkAgree agree hw → WalkB2 K hw → AllSound P μ K Ew →
      ∀ r m, E''.members r = some m → r ≠ rr → MemberSound P μ K r m
  | _, _, [], hw, _, _, _, _, _, _, hA => by
      intro r m hm hne
      rcases groupMembersT_cases hw r m hm with hold | hnew
      · exact hA r m hold
      · simp only [List.nil_append, List.mem_singleton] at hnew
        exact (hne (congrArg Prod.fst hnew)).elim
  | Ew, _, (r, m) :: pre,
      .cons _ _ _ _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest,
      hms, hclasses, hsub, hW, hAgr, hWB, hA => by
      obtain ⟨hwc, hwcs⟩ := hW
      obtain ⟨hagc, hagcs⟩ := hAgr
      obtain ⟨hwb, hwbs⟩ := hWB
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv Ew r m).members r' = some m' →
          E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hrr : Ew.members rr = none := by
        have hnone := groupMembersT_fresh_base hrest rr rm
          (List.mem_append_right _ (List.mem_singleton_self _))
        exact (extendEnv_ne_none hnone).2
      have hnew : MemberSound P μ K r m := by
        cases hadm with
        | family _ view _ hm _ =>
            have hk : m.mclass = .inductiveM := hm ▸ view.hasClass
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hcl _ hin hk)
            exact hfS
        | recursor _ _ _ _ _ _ _ =>
            exact (hclasses _ (List.mem_cons_self _ _) hwc).elim
        | constructor famO view _ _ _ h07 _ =>
            exact hcS Ew r m famO view hin hfresh hrr h07 hagc hwb hsubR hA
      have hA' : AllSound P μ K (extendEnv Ew r m) := by
        intro r' m' h
        by_cases hr : r' = r
        · subst r'
          rw [members_extend_eq] at h
          cases h
          exact hnew
        · rw [members_extend_ne Ew r m r' hr] at h
          exact hA r' m' h
      exact walk_before_rec P μ K full agree hcl hfS hcS pre hrest
        (fun c hc => hms c (List.mem_cons_of_mem _ hc))
        (fun c hc => hclasses c (List.mem_cons_of_mem _ hc)) hsub
        hwcs hagcs hwbs hA'

/-- The actual bounded admission walk supplies every constructor and the
ordinary reader environment. The new recursor is not assumed sound. -/
theorem sound_of_small_frame (P : Premises4)
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful role P μ ctx plans E')
    (hsmall : ∃ A,
      Admissible (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofGroup hE hfam hctors hrec hmem)) A) :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    (∀ r m, E'.members r = some m → r ≠ rr → MemberSound P μ K r m) ∧
      (∀ σ n, EnvSound (mkM P μ) σ K p.node.E0 n) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  let N := frame P μ (EvalPlanNormal.fd p)
  have hN : Admissible (EvalPlanNormal.fd p) N :=
    frame_admissible P μ (EvalPlanNormal.fd p) hsmall
  have hClosed : Closed P μ (EvalPlanNormal.fd p) N :=
    frame_closed_of_mono P μ (EvalPlanNormal.fd p) hsmall
      (EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem)
  have hFacts := NormCandidatePrefix.canonical_group_facts P K μ hE hfam hctors
    hrec hmem hPred ctx plans hctx hplans hFaith hN
  have hFamily := NormCandidatePrefix.family_equation_of_group P μ hE hfam
    hctors hrec hmem ctx plans hctx hFaith
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
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) := by
      have h := hFamily (ls.map (evalTotal σ))
      change Equiv (μ p.node.a.family.ref (ls.map (evalTotal σ)))
        (role P μ (EvalPlanNormal.fd p) (ls.map (evalTotal σ))) at h
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
    exact NormDataCtor.constructor_at_walk P μ K p i famO cv hEw N hN hClosed
      hFamily hvalue
      (fun vs => NormRoleDelta.bodyEquations_at_node P μ ctx plans hE hfam hctors
        hrec hmem hctx hFaith p.node (σOf vs))
      hFacts.facts (groupMembersT_body_none hmem _ _ (node_ctor_mem hmem hL hrr p.node i))
      h07 hag hFacts.rawEnv hESw (hBound.2.1 p.node i) hB2
  have hAll : ∀ r m, E'.members r = some m → r ≠ rr → MemberSound P μ K r m := by
    refine walk_before_rec P μ K ((f, fm) :: ctors ++ [(rr, rm)])
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

end Rcic.F3.PSet.NormDataPrefix
