import rcic.RcicF3PlanWalk
import rcic.RcicF3RawFamilyGroup
/-! Raw-frame group composition. Constructor membership and full family type
membership use the repaired frame directly. The legacy family fixed-point
equation is absent. Universal production of an admissible closed frame and
of the recursor package remain separate obligations. `closure_claim = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.PlanRole
open Rcic.Declarative

def GInvAt (F : RoleModel.FamilyValue) (P : Premises4) (K : Nat → Nat)
    (Efin : ResolvedEnv) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  (∀ r m, E.members r = some m → Efin.members r = some m) →
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) →
  ∀ plans : Plans, (∀ r, Dom E r → plans r = envPlan hW r) →
  ∀ μ, Faithful F P μ ctx plans E →
    AllSound P μ K E ∧ ∀ r m, E.members r = some m →
      m.mclass = .recursorM → IotaAt P μ K Efin r

/-- Elementary rearrangement of the existing invariant's quantifiers. -/
theorem gInvAt_of_gInv {F : RoleModel.FamilyValue} {P : Premises4} {K : Nat → Nat}
    {Efin E : ResolvedEnv} {hW : EnvWfT E} (h : GInv F P K hW) : GInvAt F P K Efin hW :=
  fun hsub ctx hctx plans hplans μ hF =>
    ⟨(h ctx hctx plans hplans μ hF).1, (h ctx hctx plans hplans μ hF).2 Efin hsub⟩

/-- Elementary rearrangement of the existing invariant's quantifiers. -/
theorem gInv_of_gInvAt {F : RoleModel.FamilyValue} {P : Premises4} {K : Nat → Nat}
    {E : ResolvedEnv} {hW : EnvWfT E} (h : ∀ Efin, GInvAt F P K Efin hW) : GInv F P K hW :=
  fun ctx hctx plans hplans μ hF =>
    ⟨(h E (fun _ _ h => h) ctx hctx plans hplans μ hF).1,
      fun Efin hsub => (h Efin hsub ctx hctx plans hplans μ hF).2⟩
end Rcic.F3.PSet.PlanRole

namespace Rcic.F3.PSet.PlanFamilyGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

structure GroupValues (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (fm : CheckedMember) (node : RecNode E E' f rr rm) : Prop where
  fam : ∀ vs, Equiv (μ f vs) (role P μ (famDataOf node.a) vs)
  ctor : ∀ (i : Fin node.a.constructors.length) vs, Equiv (μ (f + 1 + i.val) vs)
    (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val
      (nfOf (famDataOf node.a) i.val)) ρ0 (node.a.constructors[i.val]).mtype)
  recur : ∀ vs, Equiv (μ rr vs) (piLam (mkM P μ) (σOf vs)
    (RecPlanValue.endValue (mkM P μ) (σOf vs) (famDataOf node.a)
      (PlanRole.admittedPlan node.a node.h14)) ρ0 rm.mtype)
  famTy : fm.mtype = famType (famDataOf node.a)
  bounded : FamBounded (famDataOf node.a) node.a.family.member.arity
  ctorBounded : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

theorem values_of_faithful (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {ctx ctx0 : Nat → Role} {plans : PlanRole.Plans} {E E' : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) (hF : PlanRole.Faithful role P μ ctx plans E')
    (hctx : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr ctx0 r) (hplan : plans rr = PlanRole.admittedPlan node.a node.h14) (hTF : TypeFacts E') :
    GroupValues P μ fm node := by
  obtain ⟨_, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hfm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfm, node.a.family.storedType]; rfl
  refine ⟨fun vs => ?_, fun i vs => ?_, fun vs => ?_, hty, famBounded_node node hTF, fun i => ?_⟩
  · have h := hF f fm hf' vs
    rw [hctx f (dom_of_members hf'), groupRoles_at_f] at h
    exact h
  · have hc := node_ctor_member node i
    have h := hF _ _ hc vs
    rw [hctx _ (dom_of_members hc), groupRoles_at_ctor _ _ (by have := i.isLt; omega)] at h
    exact h
  · have h := hF rr rm hr' vs
    rw [hctx rr (dom_of_members hr'), groupRoles_at_rr _ (by omega)] at h
    rw [hplan] at h
    exact h
  · have hb' := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at hb'
    exact hb'

structure RecStepCtx (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (fm : CheckedMember) (node : RecNode E E' f rr rm)
    (μ : Nat → List Nat → PSet.{4}) : Prop where
  faith : GroupValues P μ fm node
  lim : ∀ vs, Equiv (μ node.a.family.ref vs) (role P μ (famDataOf node.a) vs)
  admissible : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a))
  closed : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a))
  scope : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n
  facts : TypeFacts E'
  pfree : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
    occursConst (famDataOf node.a).fref e = false
  rmem : E'.members rr = some rm
  rbody : rm.body = none
  lvC : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

theorem gInv_group_ofAt_node (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hs : scanRec hmem = some (famDataOf node.a))
    (hsp : PlanRole.scanPlan hmem = some (PlanRole.admittedPlan node.a node.h14))
    (hFrameA : ∀ (μ : Nat → List Nat → PSet.{4}),
      AllSound P μ K E →
      (∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r) →
      (∀ vs, Equiv (μ node.a.family.ref vs) (role P μ (famDataOf node.a) vs)) →
      Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)) ∧
      Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hWR : WalkRec hmem)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB1 : (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
      vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d))
    (hWB : WalkB2 K hmem)
    (hpkgA : ∀ (μ : Nat → List Nat → PSet.{4}),
      RecStepCtx P K fm node μ → RecPkgAt P μ K Efin E' rr rm)
    (IH : PlanRole.GInvAt role P K Efin hE) :
    PlanRole.GInvAt role P K Efin (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  intro hsubFin ctx hctx plans hplans μ hF
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtx hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr (envCtx hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtx_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : PlanRole.Faithful role P μ ctx plans E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH (fun r m h => hsubFin r m (hsubE r m h)) ctx hctxE plans (fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (PlanRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)) μ hFE
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := PSet.groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  -- The family entry is the explicitly chosen interpretation.
  have hLimμ : ∀ vs, Equiv (μ node.a.family.ref vs) (role P μ (famDataOf node.a) vs) := fun vs => by
    have h := hF f fm hf' vs
    rw [hctxG f (dom_of_members hf'), groupRoles_at_f] at h
    rw [node.fam]
    exact h
  have hpfF : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have := groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at this
    unfold Dom at this
    rw [hf0] at this
    exact absurd this (by decide)
  have hplan : plans rr = PlanRole.admittedPlan node.a node.h14 := by
    rw [hplans rr (dom_of_members hr')]
    change (match PlanRole.scanPlan hmem with
      | some plan => fun r => if r = rr then plan else PlanRole.envPlan hE r
      | none => PlanRole.envPlan hE) rr = _
    rw [hsp]
    exact if_pos rfl
  have hG := values_of_faithful P hmem hL hrr node hF hctxG hplan hTF
  obtain ⟨hC, hc⟩ := hFrameA μ IHμ.1 IHμ.2 hLimμ
  have hfmS : MemberSound P μ K f fm := by
    intro σ ls ρ hlen _
    refine ⟨?_, fun b hb => by rw [hbf] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype
      (hTF f fm hf').1 (hlen ▸ (hTF f fm hf').2.1), hG.famTy]
    exact mem_congr_left (hG.fam _).symm
      (ofFrame_mem P μ (famDataOf node.a) (frame P μ (famDataOf node.a)) hC _)
  have hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true := fun i => by
    have h := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at h
    exact h
  -- the constructor scope at the table
  have hES_S : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
    intro σ n
    refine envSound_of P (Efin := Efin) (fun r m h => hsubFin r m (hSsub r m h)) ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.2 r m h hk
  -- the recursor's package (its soundness and ι), from the class's step
  have hrb : rm.body = none :=
    hbody _ _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hP := hpkgA μ ⟨hG, hLimμ, hC, hc, hES_S, hTF, hpfF, hr', hrb, hlvC⟩ hsubFin
  have hIrr := hP.2
  have hrmS := hP.1
  -- every recursor of the extended environment
  have hIall : ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
    intro r m h hk
    rcases group_member_cases hmem hL hrr node h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact IHμ.2 r m h1 hk
    · rw [hfam] at hk; cases hk
    · exact hIrr
    · rw [(node.a.constructorViews i).hasClass] at hk; cases hk
  -- the constructors, along the walk
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → Ew.members r = none →
      FieldUniverseAdmitted cv →
      AgreeAt node.a.family.parameters.length Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh h07 hagc hB2w hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' := fun r' m' h =>
      hsubw r' m' (members_extend_preserved hfresh r' m' h)
    -- the member is one of the group's constructors
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
      rcases group_member_cases hmem hL hrr node (groupMembersT_installed hmem hin) with
        h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h1
      · rcases List.mem_cons.mp hin with h2 | h2
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; rw [hfam] at hkC; cases hkC
        · rcases List.mem_append.mp h2 with h3 | h3
          · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
            rw [hL] at hr
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
            have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
            exact ⟨⟨i, hi'⟩, rfl, Option.some.inj ((groupMembersT_installed hmem hin).symm.trans
              (node_ctor_member node ⟨i, hi'⟩))⟩
          · rw [List.mem_singleton] at h3
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3; rw [hrec] at hkC; cases hkC
      · rw [hfam] at hkC; cases hkC
      · rw [hrec] at hkC; cases hkC
      · exact h1
    obtain ⟨i, rfl, rfl⟩ := hctor
    have hES_w : ∀ σ n, EnvSound (mkM P μ) σ K Ew n := by
      intro σ n
      exact envSound_of P (Efin := Efin)
        (fun r m h => hsubFin r m (hEw r m h)) hAw
        (fun r m h hk => hIall r m (hEw r m h) hk) σ n
    exact RawFamilyWalk.constructor_at_walk P μ K node i famO cv hEw
      (frame P μ (famDataOf node.a)) hC hc hLimμ (hG.ctor i) hTF
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) h07 hagc hES_S hES_w
      (hB1 node i) hB2w
  have hAll : AllSound P μ K E' := by
    refine walk_sound P μ K ((f, fm) :: ctors ++ [(rr, rm)]) (AgreeAt node.a.family.parameters.length) ?_ ?_ hfmS hrmS
      hcS hmem (fun _ h => h) (fun _ _ h => h) hWR (hAg node) hWB IHμ.1
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; subst h; rw [hrec] at hk; cases hk
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · subst h; rw [hfam] at hk; cases hk
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; exact h
  exact ⟨hAll, hIall⟩



/-- Literal complete group-step composition. The two remaining component
inputs are explicit; this theorem does not produce either input universally. -/
theorem stepAt_node (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hs : scanRec hmem = some (famDataOf node.a))
    (hsp : PlanRole.scanPlan hmem = some (PlanRole.admittedPlan node.a node.h14))
    (hFrame : ∀ Efin, ∀ μ, AllSound P μ K E →
      (∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r) →
      (∀ vs, Equiv (μ node.a.family.ref vs) (role P μ (famDataOf node.a) vs)) →
      Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)) ∧
      Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hpkg : ∀ Efin μ, RecStepCtx P K fm node μ → RecPkgAt P μ K Efin E' rr rm) :
    PlanRole.GroupStepAt role P K hE hfam hctors hrec hmem := by
  intro hAg hB _ IH
  exact PlanRole.gInv_of_gInvAt (fun Efin =>
    gInv_group_ofAt_node P K Efin hE hfam hctors hrec hmem node hs hsp (hFrame Efin)
      (walkRec_of_group hmem) hAg hB.2.1 hB.2.2.1 (hpkg Efin) (PlanRole.gInvAt_of_gInv IH))


/-- Compatibility at an actual node whose admitted and raw plans coincide.
This is not a requirement on hidden-field groups. -/
theorem GroupValues.toRaw (P : Premises4) {μ : Nat → List Nat → PSet.{4}}
    {E E' : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    {node : RecNode E E' f rr rm} (h : GroupValues P μ fm node)
    (hraw : PlanRole.admittedPlan node.a node.h14 = RecPlan.rawPlan (famDataOf node.a)) :
    RawFamilyGroup.GroupValues P μ fm node := by
  refine ⟨h.fam, h.ctor, ?_, h.famTy, h.bounded, h.ctorBounded⟩
  intro vs
  have hr := h.recur vs
  rw [hraw] at hr
  have he : RecPlanValue.endValue (mkM P μ) (σOf vs) (famDataOf node.a)
      (RecPlan.rawPlan (famDataOf node.a)) = recEnd (mkM P μ) (σOf vs) (famDataOf node.a) :=
    funext (RecPlanValue.laws (mkM P μ) (σOf vs) (famDataOf node.a)
      (RecPlan.rawPlan (famDataOf node.a))).2
  rw [he] at hr
  exact hr
/-- Elementary compatibility of the package context at a raw-plan node. -/
theorem RecStepCtx.toRaw (P : Premises4) {K : Nat → Nat}
    {E E' : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (h : RecStepCtx P K fm node μ)
    (hraw : PlanRole.admittedPlan node.a node.h14 = RecPlan.rawPlan (famDataOf node.a)) :
    RawFamilyGroup.RecStepCtx P K fm node μ :=
  ⟨h.faith.toRaw P hraw, h.lim, h.admissible, h.closed, h.scope,
    h.facts, h.pfree, h.rmem, h.rbody, h.lvC⟩
end Rcic.F3.PSet.PlanFamilyGroup
