import rcic.RcicF3NormDRec

/-!
# The checked D semantic kernel with the produced normalized family

This reuses the factored group kernel of #8459 (head 74e586d9), with the
actual family MemberSound supplied directly and the bounded recursor chain
fed by the normalized finite-limit equation. The family-only scope and the
constructor walk retain their original typed derivations and own bounds.

GroupFaithB still contains the literal old recEnd equation. The normalized
adapter supplies it only for data/PropOnly; Prop/anySort is composed through
the separate typed indexed-evaluation package. No legacy invariant equality
or global raw-limit equation is required. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDGroup
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder NormDStage

/-- Concrete sound-table obligations, with bounded normalized family reads. -/
theorem at_table (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    (hsh : NoFunRec node)
    (hpar : ∀ i : Fin node.a.constructors.length,
      (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hprop : UniformProp node.a.family.resultLevel →
      node.a.policy = .anySort → ∀ i : Fin node.a.constructors.length,
      (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
      (∀ k, k < (node.a.constructorViews i).fields.length →
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
          (node.a.constructorViews i).resultIndices = none))
    (hCB : CtorsBelowRec K node)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (μ : Nat → List Nat → PSet.{4}) (IHμ : TableSound P K E μ)
    (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs))
    (hfmS : MemberSound P μ K f fm)
    (D : DStage P K node μ) (hG : GroupFaithB P μ K fm node) : TableSound P K E' μ := by
  obtain ⟨hBG, hB1, hWB, hB3⟩ := hB
  have hWR : WalkRec hmem := walkRec_of_group hmem
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
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
  have hopq : ∀ ls, transparentBody node.E0 f ls = none := by
    intro ls
    have hp := node.a.family.present
    rw [node.fam] at hp
    unfold transparentBody
    rw [hp]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have hopq' : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by rw [node.fam]; exact hopq
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]; exact famFreeBodies_node hE hf0 hmem node
  have hBfd : FamBounded (famDataOf node.a) node.a.family.member.arity := famBounded_node node hTF
  -- the constructor scope at the table
  have hES_S : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
    intro σ n
    refine envSound_of P hSsub ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.2 E' hsubE r m h hk
  have hbodies_S : ∀ σ, BodiesOK (extendEnv E f fm) σ K := fun σ =>
    bodiesOK_of_envWfT K hE hBG (fun r m h => members_extend_preserved hf0 r m h) (fun r m hm h0 => by
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at hm; cases hm; exact hbf
      · rw [members_extend_ne E f fm r hr] at hm; rw [hm] at h0; cases h0) σ
  have hwhnf_S : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel (extendEnv E f fm) fuel e :=
    whnfFuel_eq_along hmem node.base (node_sub' node) (fun r m h => members_extend_preserved hf0 r m h) hSsub
  -- the transfer at instances within the recursor's bound
  have hagR0 : ∀ vs, vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
      AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs := fun vs hlen hvs => D.agree vs hvs hlen
  -- a recursor instance carries one more level under `anySort`: transport from the family's instance
  have hagR : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs :=
    fun vs hvs =>
    agreeAt_levels P μ node.a _ vs (σOf_policyFamilyLevels_agree node.a.family vs) hBfd
      (nodeFam_bounded node hTF (node_bodies_levelsBounded0 hE hmem node K hBG))
      (hagR0 _ (famLevels_length node.a.family vs) (famLevels_le node.a.family hvs))
  -- under large elimination of a `Prop` family: nonrecursive shapes, proof fields
  have hsh' : ∀ (i : Fin node.a.constructors.length) fuel shapes, UniformProp node.a.family.resultLevel →
      node.a.policy = .anySort →
      fieldShapesFuel node.E0 fuel f node.a.family.member.arity node.a.family.parameters.length
        node.a.family.indices.length node.a.family.parameters.length (node.a.constructorViews i).fields =
        some shapes →
      ShapesMatch f shapes (node.a.constructorViews i).fields := fun i fuel shapes hU hpol hfs =>
    shapesMatch_of_direct (famFreeBodies_node hE hf0 hmem node) hopq _ 0 _
      (recFieldsDirect_of_free (lsF := []) (np := 0) (nq := 0) _ 0
        (fun T hT => by rw [← node.fam]; exact (hprop hU hpol i).1 T hT)) shapes hfs
  have hnrec : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref
        node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
        node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
        ∀ s, s ∈ shapes → s = .nonrecursive := by
    intro hU hpol i fuel shapes hfs s hs
    have hnf := (hprop hU hpol i).1
    rw [node.fam] at hnf hfs
    obtain ⟨_, hm⟩ := hsh' i fuel shapes hU hpol hfs
    obtain ⟨k, hk1, hk2⟩ := List.mem_iff_getElem.mp hs
    have hkF : k < (node.a.constructorViews i).fields.length := by
      rw [← (hsh' i fuel shapes hU hpol hfs).1]; exact hk1
    rcases hm k s _ (by rw [List.getElem?_eq_getElem hk1, hk2]) (List.getElem?_eq_getElem hkF) with
      ⟨h, _⟩ | ⟨_, _, ho⟩
    · exact h
    · rw [hnf _ (List.getElem_mem hkF)] at ho; cases ho
  have hPT : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps,
        TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
        PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0) := by
    intro hU hpol i vs hvs ps hps
    refine propTel_of_typings P μ K vs _ _ (hES_S (σOf vs) node.a.family.member.arity) (fun k => ?_) ps hps
    obtain ⟨l, hl, hd⟩ := hB3 node hU hpol i vs hvs k
    exact ⟨l, hl _, hd⟩
  have hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true := fun i => by
    have h := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at h
    exact h
  -- ι at the group's recursor
  have hIrr : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr :=
    fun Efin hsubF => iota_at_D P hG hsubF hr' hFF hopq' (hsh) hlvC (fun hU hpol i => by
      obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
      have hmt := derivedMinor_nonrec node.a i fuel shapes (hnrec hU hpol i fuel shapes hfs)
        (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
      rw [hdm] at hmt
      exact ⟨fun T hT => (hprop hU hpol i).1 T hT, (hprop hU hpol i).2,
        ⟨_, hmt⟩, hPT hU hpol i⟩)
  -- every recursor of the extended environment
  have hIall : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) →
      ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
    intro Efin hsubF r m h hk
    rcases group_member_cases hmem hL hrr node h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact IHμ.2 Efin (fun r m h => hsubF r m (hsubE r m h)) r m h1 hk
    · rw [hfam] at hk; cases hk
    · exact hIrr Efin hsubF
    · rw [(node.a.constructorViews i).hasClass] at hk; cases hk
  -- the recursor
  have hrmS : MemberSound P μ K rr rm := by
    have hcl := (hTF _ _ hr').1
    have hlvl := (hTF _ _ hr').2.1
    have hrb : rm.body = none :=
      hbody _ _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
    rcases selection_uniform node.a with hU | hT
    · cases hpol : node.a.policy with
      | propOnly =>
          intro σ ls ρ hlen hls
          refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
          rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
          refine mem_congr_left (hG.recur _).symm ?_
          have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
            intro v hv
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
            exact hls l hl
          exact NormDRec.recVal_mem_recPDB D hlim hBfd _ hbnd (hagR _ hbnd) (groupFaithB_ctorAt P hG _) (hU _) hpol
      | anySort =>
          exact rec_member_soundB P hG hcl hlvl hrb (hnrec hU hpol)
            (fun hU' hpol' i => ⟨(hprop hU' hpol' i).2, hPT hU' hpol' i⟩)
            (fun i T hT => (hprop hU hpol i).1 T hT)
    · intro σ ls ρ hlen hls
      refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
      rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
      refine mem_congr_left (hG.recur _).symm ?_
      have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact hls l hl
      exact NormDRec.recVal_mem_recDB D hlim hBfd _ hbnd (hagR _ hbnd) (groupFaithB_ctorAt P hG _)
        (Nat.pos_iff_ne_zero.mp (hT _))
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
    have hES_w : ∀ vs, EnvSound (mkM P μ) (σOf vs) K Ew famO.member.arity := fun vs =>
      envSound_of P hEw hAw (fun r m h hk => hIall E' (fun _ _ h => h) r m (hEw r m h) hk) _ _
    refine ctor_member_soundB P (famDataOf node.a) i.val (node.a.constructorViews i).parameters
      (node.a.constructorViews i).fields (node.a.constructorViews i).resultIndices (famDataOf_ctor node.a i)
      (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
      (hTF _ _ (node_ctor_member node i)).1 (hTF _ _ (node_ctor_member node i)).2.1
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) (fun vs => hG.ctor i vs) ?_ ?_ ?_
    · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
      rfl
    · intro vs hvl hbd
      exact NormDRec.famB_normal D hlim vs (fun v hv => Nat.le_trans (hbd v hv) (hCB i))
        (hvl.trans (node.a.constructorViews i).arity)
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
        cv.domainsTyped.levels node.a.family.resultLevel vs (hES_w vs) hB2v (fun _ _ _ => rfl) hD h0 hlevF
        ps xs hps hxs
  have hAll : AllSound P μ K E' := by
    refine walk_sound P μ K ((f, fm) :: ctors ++ [(rr, rm)]) (AgreeAt node.a.family.parameters.length) ?_ ?_
      hfmS hrmS hcS hmem (fun _ h => h) (fun _ _ h => h) hWR (hAg node) hWB IHμ.1
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
  exact ⟨hAll, fun Efin hsubF r m h hk => hIall Efin hsubF r m h hk⟩


end Rcic.F3.PSet.NormDGroup
