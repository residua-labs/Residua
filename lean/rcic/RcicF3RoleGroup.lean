import rcic.RcicF3RoleModel
import rcic.RcicF3StepAObstr

/-!
# The full group consumer with an explicit family interpretation

This transports the landed constructor walk and final-environment iota
obligations to `RoleModel.GInv`. The family fixed-point equation is owed
only at tables faithful to the chosen interpretation. No shape wall or
recursor obligation is removed. This is composition, not a global producer.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RoleModel
open Rcic.Declarative Rcic.Model.PS

theorem groupFaith_of (F : FamilyValue) (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {ctx ctx0 : Nat → Role} {E E' : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) (hF : Faithful F P μ ctx E')
    (hctx : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr ctx0 r) (hTF : TypeFacts E')
    (hfix : ∀ vs, Equiv (F P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    GroupFaith P μ fm node := by
  obtain ⟨_, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hfm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfm, node.a.family.storedType]; rfl
  refine ⟨fun vs => ?_, fun i vs => ?_, fun vs => ?_, hty, famBounded_node node hTF, fun i => ?_⟩
  · have h := hF f fm hf' vs
    rw [hctx f (dom_of_members hf'), groupRoles_at_f] at h
    rw [hty]
    exact h.trans (hfix vs)
  · have hc := node_ctor_member node i
    have h := hF _ _ hc vs
    rw [hctx _ (dom_of_members hc), groupRoles_at_ctor _ _ (by have := i.isLt; omega)] at h
    exact h
  · have h := hF rr rm hr' vs
    rw [hctx rr (dom_of_members hr'), groupRoles_at_rr _ (by omega)] at h
    exact h
  · have hb' := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at hb'
    exact hb'

theorem gInvAt_of_gInv {F : FamilyValue} {P : Premises4} {K : Nat → Nat} {Efin E : ResolvedEnv} {hW : EnvWfT E}
    (h : GInv F P K hW) : GInvAt F P K Efin hW := fun hsub ctx hctx μ hF =>
  ⟨(h ctx hctx μ hF).1, (h ctx hctx μ hF).2 Efin hsub⟩

theorem gInv_of_gInvAt {F : FamilyValue} {P : Premises4} {K : Nat → Nat} {E : ResolvedEnv} {hW : EnvWfT E}
    (h : ∀ Efin, GInvAt F P K Efin hW) : GInv F P K hW := fun ctx hctx μ hF =>
  ⟨(h E (fun _ _ h => h) ctx hctx μ hF).1, fun Efin hsub => (h Efin hsub ctx hctx μ hF).2⟩

structure RecStepCtx (F : FamilyValue) (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (fm : CheckedMember) (node : RecNode E E' f rr rm)
    (μ : Nat → List Nat → PSet.{4}) : Prop where
  faith : GroupFaith P μ fm node
  lim : ∀ vs, Equiv (μ node.a.family.ref vs) (F P μ (famDataOf node.a) vs)
  scope : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n
  facts : TypeFacts E'
  pfree : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
    occursConst (famDataOf node.a).fref e = false
  rmem : E'.members rr = some rm
  rbody : rm.body = none
  lvC : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

theorem gInv_group_ofAt_node (F : FamilyValue) (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hs : scanRec hmem = some (famDataOf node.a))
    (hfixA : ∀ (μ : Nat → List Nat → PSet.{4}),
      (∀ vs, Equiv (μ node.a.family.ref vs) (F P μ (famDataOf node.a) vs)) → ∀ vs,
      Equiv (F P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)))
    (hWR : WalkRec hmem)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB1 : (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
      vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d))
    (hWB : WalkB2 K hmem)
    (hpkgA : ∀ (μ : Nat → List Nat → PSet.{4}),
      RecStepCtx F P K fm node μ → RecPkgAt P μ K Efin E' rr rm)
    (IH : GInvAt F P K Efin hE) :
    GInvAt F P K Efin (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  intro hsubFin ctx hctx μ hF
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtx hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr (envCtx hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtx_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : Faithful F P μ ctx E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH (fun r m h => hsubFin r m (hsubE r m h)) ctx hctxE μ hFE
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
  have hLimμ : ∀ vs, Equiv (μ node.a.family.ref vs) (F P μ (famDataOf node.a) vs) := fun vs => by
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
  -- The fixed-point equation is required only at this faithful table.
  have hfix : ∀ vs, Equiv (F P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) :=
    hfixA μ hLimμ
  have hG := groupFaith_of F P hmem hL hrr node hF hctxG hTF hfix
  have hfmS : MemberSound P μ K f fm :=
    fam_member_sound P (famDataOf node.a) hG.fam hG.famTy (hTF f fm hf').1 (hTF f fm hf').2.1 hbf
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
  have hP := hpkgA μ ⟨hG, hLimμ, hES_S, hTF, hpfF, hr', hrb, hlvC⟩ hsubFin
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
    -- the constructor's own view agrees with the recursor's
    have hstO := cv.storedType
    have hstR := (node.a.constructorViews i).storedType
    have hspl := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
      (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (hstO.symm.trans hstR)
    have hcat := hspl.1
    have href : famO.ref = node.a.family.ref := foldApps_const_head hspl.2
    have hfamO : famO.member = fm := by
      have h1 := famO.present
      rw [href, node.fam] at h1
      exact Option.some.inj ((hEw f _ h1).symm.trans hf')
    have hlvO : famO.resultLevel = node.a.family.resultLevel := by
      have e1 := famO.storedType
      have e2 := node.a.family.storedType
      rw [hfamO] at e1
      rw [hfmm] at e2
      have := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) (e1.symm.trans e2)).2
      injection this
    have harO : famO.member.arity = node.a.family.member.arity := by rw [hfamO, hfmm]
    refine ctor_member_sound P (famDataOf node.a) i.val (node.a.constructorViews i).parameters
      (node.a.constructorViews i).fields (node.a.constructorViews i).resultIndices (famDataOf_ctor node.a i)
      (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
      (hTF _ _ (node_ctor_member node i)).1 (hTF _ _ (node_ctor_member node i)).2.1
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) (fun vs => hG.ctor i vs) ?_ ?_ ?_
    · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
      rfl
    · intro vs _
      have h := hG.fam vs
      rw [hG.famTy] at h
      show Equiv (μ node.a.family.ref vs) _
      rw [node.fam]
      exact h
    · intro vs hvl hbd zs hz
      obtain ⟨u, d, hd⟩ := hB1 node i vs (hvl.trans (node.a.constructorViews i).arity) hbd
      have hsd := hsound_ty (P.good _ rfl) (hES_S (σOf vs) _) d hd
      have := tel_end_type' _ _ d (node.a.constructorViews i).storedType hsd ρ0 zs trivial hz
      have e : (List.range vs.length).map Level.param = policyFamilyLevels node.a.family := by
        rw [hvl, (node.a.constructorViews i).arity]; rfl
      rw [e]
      exact this
    · intro vs hvl hbd h0 ps xs hps hxs
      have hvlO : vs.length = famO.member.arity := by rw [harO, ← (node.a.constructorViews i).arity]; exact hvl
      have hB2v := hB2w vs hvlO hbd
      have hD : RefsIn (Dom Ew) (cv.parameters ++ cv.fields) := fun e he r hr => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
        obtain ⟨d, _⟩ := hB2v ⟨k, hk⟩
        exact hasTyT_denRefs d r hr
      have hES_w : EnvSound (mkM P μ) (σOf vs) K Ew famO.member.arity :=
        envSound_of P (Efin := Efin) (fun r m h => hsubFin r m (hEw r m h)) hAw
          (fun r m h hk => hIall r m (hEw r m h) hk) _ _
      have h0O : evalTotal (σOf vs) famO.resultLevel ≠ 0 := by rw [hlvO]; exact h0
      -- the level bound on the recursor view's fields: own fields by the own admission, positions the own
      -- view reads as parameters by the level agreement and the recursor's admission
      have hlevF : ∀ (j : Fin (node.a.constructorViews i).fields.length)
          (hk : (node.a.constructorViews i).parameters.length + j.val < (cv.parameters ++ cv.fields).length),
          evalTotal (σOf vs) (cv.domainsTyped.levels ⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩) ≤
            evalTotal (σOf vs) node.a.family.resultLevel := by
        intro j hk
        have hlenN : (node.a.constructorViews i).parameters.length = node.a.family.parameters.length :=
          (node.a.constructorViews i).parameterCount
        rcases Nat.lt_or_ge ((node.a.constructorViews i).parameters.length + j.val) cv.parameters.length with
          hpar | hfld
        · rcases hagc _ hk (by omega) hpar with hp | hle
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
        · have hj : (kk : Nat) → kk = (node.a.constructorViews i).parameters.length + j.val →
              kk - cv.parameters.length < cv.fields.length := fun kk hkk => by
            simp only [List.length_append] at hk; omega
          let j' : Fin cv.fields.length :=
            ⟨(node.a.constructorViews i).parameters.length + j.val - cv.parameters.length, hj _ rfl⟩
          have hfi : (⟨(node.a.constructorViews i).parameters.length + j.val, hk⟩ :
              Fin (cv.parameters ++ cv.fields).length) = cv.fieldIndex j' :=
            Fin.ext (by
              show (node.a.constructorViews i).parameters.length + j.val =
                cv.parameters.length + ((node.a.constructorViews i).parameters.length + j.val - cv.parameters.length)
              omega)
          rw [hfi]
          rcases h07 j' with hp | ⟨_, hle⟩
          · exact absurd (hp _) h0O
          · have := leN_evalTotal hle (σOf vs)
            rw [hlvO] at this
            exact this
      exact field_small_gen P μ μ K (Epre := Ew) famO.member.arity (cv.parameters ++ cv.fields)
        (node.a.constructorViews i).parameters (node.a.constructorViews i).fields hcat.symm
        cv.domainsTyped.levels node.a.family.resultLevel vs hES_w hB2v (fun _ _ _ => rfl) hD h0 hlevF ps xs hps hxs
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


/-- Full group-step composition at the actual node read by the walk.
The explicit scan equation permits concrete fixtures without assuming
that every alternative admission structure is definitionally identical. -/
theorem stepAt_node (F : FamilyValue) (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hs : scanRec hmem = some (famDataOf node.a))
    (hfix : ∀ μ, (∀ vs, Equiv (μ node.a.family.ref vs) (F P μ (famDataOf node.a) vs)) →
      ∀ vs, Equiv (F P μ (famDataOf node.a) vs)
        (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)))
    (hpkg : ∀ Efin μ, RecStepCtx F P K fm node μ → RecPkgAt P μ K Efin E' rr rm) :
    GroupStepAt F P K hE hfam hctors hrec hmem := by
  intro hAg hB _ IH
  exact gInv_of_gInvAt (fun Efin =>
    gInv_group_ofAt_node F P K Efin hE hfam hctors hrec hmem node hs hfix
      (walkRec_of_group hmem) hAg hB.2.1 hB.2.2.1 (hpkg Efin) (gInvAt_of_gInv IH))

end Rcic.F3.PSet.RoleModel
