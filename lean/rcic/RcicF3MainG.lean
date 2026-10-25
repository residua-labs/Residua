import rcic.RcicF3FieldSmall
import rcic.RcicF3PropEmpty

/-!
# F3 S5a-17 / S5b-5: consistency over environments of inductive groups

`consistent4_G`: in an admitted environment in the class `ClassG` whose
derivations used by the proof respect an instance bound `K` (`BoundG`) and
whose member 1 is the recursor of the empty type at 0, no closed term has the
type at 0, by any derivation with sort levels at most 4 and constant
instances within `K`. Relative to `Premises4`.

`ClassG`: no axioms; in every inductive group, each field family-free or
directly recursive (the family applied to the parameter locals and
family-free indices); under `Prop` large elimination, no field revealed in
the result indices; each constructor's own admission view splitting off the
recursor view's parameters. (Parameters, result indices, field shapes and the
group's layout are derived from admission.)

The proof installs every member at its role (`envCtx`, `envμR`; a family at
the limit of its iterates, `famLim`), checks that each member reads only the
environment before it (`readsOKAlong_envCtx`), and proves by induction on the
admission (`gInv`) that at every table faithful to the roles each member is
sound and ι holds at each recursor. In a group step (`gInv_group`) the
family's entry is a fixed point of its value (`famLim_fix`); the
constructors are sound in walk order (`walk_sound`), each from its own
admission at the real table; the recursor by `recVal_mem_rec` (`Type`),
`recVal_mem_recP` (`Prop` into `Prop`), `rec_member_sound` (`Prop` with
large elimination and family-free fields: proof fields are `∅`,
`propTel_of_typings`) or `rec_member_sound_empty` (`Prop` with large
elimination and a recursive field: the family is empty, `propEmpty_of_lim`);
ι by `iota_at` (with proof fields, read off the right-hand side's typing,
`spine_proofs`; for an empty family, vacuously). The empty type
is empty in the model because its recursor is sound (`empty_of_falseRec`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs denRefsLit hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

namespace PSet

/-- In a laid-out group, every reference strictly between the family and its
recursor is a constructor of the list. -/
theorem layout_between {f rr : Nat} {ctors : List (Nat × CheckedMember)}
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) {r : Nat} (h1 : f < r) (h2 : r < rr) :
    ∃ i, ∃ (hi : i < ctors.length), r = f + 1 + i ∧ (ctors[i]).1 = r := by
  refine ⟨r - f - 1, by omega, by omega, ?_⟩
  have hi : r - f - 1 < ctors.length := by omega
  have := congrArg (fun l => l[r - f - 1]?) hL
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_range hi, Option.map_some'] at this
  have := Option.some.inj this
  simp only at this
  omega

/-- A class environment's group layout, from its admission (`group_layout`). -/
theorem group_layout_of_class {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWC : ∀ node : RecNode E E' f rr rm, WalkClass node.a.family.parameters.length hmem) :
    ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i) ∧ rr = f + 1 + ctors.length := by
  obtain ⟨node, _⟩ := group_node hE hfam hctors hrec hmem
  exact group_layout hE hfam hctors hrec hmem (walkRec_of_walkClass _ hmem (hWC node))

/-- The group's references other than the family are fresh in the base and installed. -/
theorem group_refs {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) :
    E.members f = none ∧ E.members rr = none ∧ E'.members f = some fm ∧ E'.members rr = some rm ∧
    ∀ r, f < r → r < rr → E.members r = none ∧ ∃ i, ∃ (hi : i < ctors.length), r = f + 1 + i ∧
      E'.members r = some (ctors[i]).2 := by
  have hin : ∀ c, c ∈ (f, fm) :: ctors ++ [(rr, rm)] → E.members c.1 = none ∧ E'.members c.1 = some c.2 :=
    fun c hc => ⟨groupMembersT_fresh_base hmem c.1 c.2 hc, groupMembersT_installed hmem hc⟩
  have hf := hin (f, fm) (List.mem_cons_self _ _)
  have hr := hin (rr, rm) (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  refine ⟨hf.1, hr.1, hf.2, hr.2, fun r h1 h2 => ?_⟩
  obtain ⟨i, hi, hri, hci⟩ := layout_between hL hrr h1 h2
  have hc := hin (ctors[i]) (List.mem_cons_of_mem _ (List.mem_append_left _ (List.getElem_mem _)))
  rw [hci] at hc
  exact ⟨hc.1, i, hi, hri, hc.2⟩

theorem envCtx_group_some {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') (fd : FamData)
    (hs : scanRec hmem = some fd) :
    envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) = groupRoles fd f rr (envCtx hE) := by
  show (match scanRec hmem with
    | some fd => groupRoles fd f rr (envCtx hE)
    | none => envCtx hE) = _
  rw [hs]

/-- Fresh references have the plain role (over `WalkG`). -/
theorem envCtx_freshW : {E : ResolvedEnv} → (hW : EnvWfT E) → WalkG hW → ∀ r, E.members r = none →
    envCtx hW r = .plain
  | _, .empty, _, _, _ => rfl
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _ => hC.elim
  | _, .definition E r0 _ _ _ hE hfresh _ _ _ _ _ _, hC, r, h =>
      envCtx_freshW hE hC r (extendEnv_ne_none' h)
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hC, r, h => envCtx_freshW hE hC r (extendEnv_ne_none' h)
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hC, r, h => envCtx_freshW hE hC r (extendEnv_ne_none' h)
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, r, h => by
      obtain ⟨hCE, hWR, _⟩ := hC
      obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
      have hrE : E.members r = none := Rcic.Model.PS.groupMembersT_none hmem h
      show (match scanRec hmem with
        | some fd => groupRoles fd f rr (envCtx hE)
        | none => envCtx hE) r = _
      cases scanRec hmem with
      | none => exact envCtx_freshW hE hCE r hrE
      | some fd =>
          obtain ⟨_, _, hf', hr', hbet⟩ := group_refs hmem hL hrr
          show groupRoles fd f rr (envCtx hE) r = _
          unfold groupRoles
          have h1 : r ≠ f := by intro he; subst he; rw [hf'] at h; cases h
          have h2 : r ≠ rr := by intro he; subst he; rw [hr'] at h; cases h
          have h3 : ¬ (f < r ∧ r < rr) := by
            intro ⟨a, b⟩
            obtain ⟨_, _, _, _, hm⟩ := hbet r a b
            rw [hm] at h; cases h
          rw [if_neg h1, if_neg h2, if_neg h3]
          exact envCtx_freshW hE hCE r hrE
where
  extendEnv_ne_none' {E : ResolvedEnv} {r0 : Nat} {m : CheckedMember} {r : Nat}
      (h : (extendEnv E r0 m).members r = none) : E.members r = none :=
    (Rcic.Model.PS.extendEnv_ne_none h).2

/-- A group step does not change the roles of earlier members. -/
theorem envCtx_group_stable {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (r : Nat) (hr : Dom E r) :
    envCtx (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r = envCtx hE r := by
  obtain ⟨hf0, hr0, _, _, hbet⟩ := group_refs hmem hL hrr
  show (match scanRec hmem with
    | some fd => groupRoles fd f rr (envCtx hE)
    | none => envCtx hE) r = _
  cases scanRec hmem with
  | none => rfl
  | some fd =>
      show groupRoles fd f rr (envCtx hE) r = _
      unfold Dom at hr
      unfold groupRoles
      have h1 : r ≠ f := by intro he; subst he; rw [hf0] at hr; exact absurd hr (by decide)
      have h2 : r ≠ rr := by intro he; subst he; rw [hr0] at hr; exact absurd hr (by decide)
      have h3 : ¬ (f < r ∧ r < rr) := by
        intro ⟨a, b⟩
        rw [(hbet r a b).1] at hr; exact absurd hr (by decide)
      rw [if_neg h1, if_neg h2, if_neg h3]

/-! ### references -/

theorem refs_policyPi_dom {r : Nat} (b : Expr Nat) : (D : List (Expr Nat)) → ∀ T, T ∈ D → r ∈ denRefs T →
    r ∈ denRefs (policyPi D b)
  | [], _, h, _ => absurd h (List.not_mem_nil _)
  | A :: D, T, hT, hr => by
      show r ∈ denRefs A ++ denRefs (policyPi D b)
      rcases List.mem_cons.mp hT with rfl | hT
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (refs_policyPi_dom b D T hT hr)

theorem refs_policyPi_body {r : Nat} (b : Expr Nat) (hr : r ∈ denRefs b) : (D : List (Expr Nat)) →
    r ∈ denRefs (policyPi D b)
  | [] => hr
  | _ :: D => List.mem_append_right _ (refs_policyPi_body b hr D)

theorem refs_foldApps {r : Nat} : (g : Expr Nat) → (as : List (Expr Nat)) →
    (r ∈ denRefs g ∨ ∃ a, a ∈ as ∧ r ∈ denRefs a) → r ∈ denRefs (foldApps g as)
  | _, [], h => by
      rcases h with h | ⟨a, ha, _⟩
      · exact h
      · exact absurd ha (List.not_mem_nil _)
  | g, a :: as, h => by
      refine refs_foldApps (.app g a) as ?_
      rcases h with h | ⟨a', ha', hr⟩
      · exact Or.inl (List.mem_append_left _ h)
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · exact Or.inl (List.mem_append_right _ hr)
        · exact Or.inr ⟨a', ha', hr⟩

/-- A constructor of a group is typed in its constructor scope. -/
theorem groupMembersT_ctor_refs {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → ∀ r m, (r, m) ∈ ms → m.mclass = .constructorM →
      ∀ r', r' ∈ denRefs m.mtype → Dom S r'
  | _, _, _, .nil _, _, _, h, _ => absurd h (List.not_mem_nil _)
  | _, _, _, .cons _ r₀ m₀ _ _ _ _ _ _ _ _ _ _ _ u _ hTc _ hrest, r, m, h, hk => by
      rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨d⟩ := hTc hk
        exact fun r' hr' => hasTyT_denRefs d r' hr'
      · exact groupMembersT_ctor_refs hrest r m h hk

/-! ### reads -/

theorem dom_self {E : ResolvedEnv} {r : Nat} {m : CheckedMember} : Dom (extendEnv E r m) r := by
  unfold Dom; rw [members_extend_eq]; rfl

theorem dom_of_extend_ne {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {r' : Nat}
    (h : Dom (extendEnv E r m) r') (hne : r' ≠ r) : Dom E r' := by
  unfold Dom at *; rwa [members_extend_ne E r m r' hne] at h

theorem dom_of_members {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (h : E.members r = some m) : Dom E r := by
  unfold Dom; rw [h]; rfl

/-- A group's members read inside the environment built before them, given the
family's data reads inside the base. -/
theorem groupReadsOK_of (ctx : Nat → Role) {S Eb : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') → (∀ r, Dom Eb r → Dom E r) →
    (∀ c, c ∈ ms → ∀ fd, ctx c.1 = .fam fd → RefsIn (Dom Eb) (fd.params ++ fd.indices) ∧
      FamRefsIn (fun r => Dom Eb r ∨ r = fd.fref) fd) → GroupReadsOK ctx hmem
  | _, _, _, .nil _, _, _ => trivial
  | _, _, _, .cons _ r m _ _ hfresh hnobody _ _ _ _ _ _ _ _ hT _ _ hrest, hEb, hfam => by
      refine ⟨?_, groupReadsOK_of ctx hrest (fun r' h => dom_extend hfresh r' (hEb r' h))
        (fun c hc => hfam c (List.mem_cons_of_mem _ hc))⟩
      have href : ∀ r', r' ∈ denRefs m.mtype → Dom _ r' := fun r' hr' => hasTyT_denRefs hT r' hr'
      cases hc : ctx r with
      | plain => exact ⟨href, fun b hb => by rw [hnobody] at hb; cases hb⟩
      | fam fd =>
          have H := hfam (r, m) (List.mem_cons_self _ _) fd hc
          exact ⟨href, fun e he r' hr' => hEb r' (H.1 e he r' hr'),
            fun c hc' => ⟨fun e he r' hr' => ((H.2 c hc').1 e he r' hr').imp (hEb r') id,
              fun e he r' hr' => ((H.2 c hc').2 e he r' hr').imp (hEb r') id⟩⟩
      | ctor _ _ => exact href
      | recursor _ => exact href

theorem node_ctors_length {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (node : RecNode E E' f rr rm) (hrr : rr = f + 1 + ctors.length) : node.a.constructors.length = ctors.length := by
  have := node.a.recursorRef
  rw [node.fam] at this
  omega

theorem node_ctor_member {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (i : Fin node.a.constructors.length) : E'.members (f + 1 + i.val) = some (node.a.constructors[i.val]) := by
  have h := node.a.constructorsPresent i
  rw [node.fam] at h
  exact node.sub _ _ (members_extend_preserved node.fresh _ _ h)

theorem node_fam_member {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm) :
    E'.members f = some node.a.family.member := by
  have h := node.a.family.present
  rw [node.fam] at h
  exact node.sub _ _ (members_extend_preserved node.fresh _ _ h)

theorem groupMembersT_head_refs {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E ((r, m) :: ms) E') :
    ∀ r', r' ∈ denRefs m.mtype → Dom E r' := by
  cases hmem with
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT _ _ _ => exact fun r' h => hasTyT_denRefs hT r' h

/-- A member of a group is its family, one of its constructors, or its recursor. -/
theorem group_member_cases {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) {r : Nat} {m : CheckedMember}
    (h : E'.members r = some m) :
    E.members r = some m ∨ (r = f ∧ m = fm) ∨ (r = rr ∧ m = rm) ∨
      ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
  obtain ⟨_, _, hf', hr', hbet⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  rcases groupMembersT_cases hmem r m h with h1 | h1
  · exact Or.inl h1
  rcases List.mem_cons.mp h1 with h2 | h2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  rcases List.mem_append.mp h2 with h3 | h3
  · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
    rw [hL] at hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
    refine Or.inr (Or.inr (Or.inr ⟨⟨i, hi'⟩, rfl, ?_⟩))
    exact Option.some.inj (h.symm.trans (node_ctor_member node ⟨i, hi'⟩))
  · rw [List.mem_singleton] at h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem node_ctor_mem {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    (f + 1 + i.val, node.a.constructors[i.val]) ∈ (f, fm) :: ctors ++ [(rr, rm)] := by
  have hlen := node_ctors_length node hrr
  obtain ⟨_, _, _, _, hbet⟩ := group_refs hmem hL hrr
  have hfreshc := (hbet (f + 1 + i.val) (by omega) (by have := i.isLt; omega)).1
  rcases groupMembersT_cases hmem _ _ (node_ctor_member node i) with h | h
  · rw [hfreshc] at h; cases h
  · exact h

/-- The family's data reads inside the base, and its fields also at the family. -/
theorem famReads_node {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) :
    RefsIn (Dom E) ((famDataOf node.a).params ++ (famDataOf node.a).indices) ∧
      FamRefsIn (fun r => Dom E r ∨ r = (famDataOf node.a).fref) (famDataOf node.a) := by
  obtain ⟨_, _, hf', _, _⟩ := group_refs hmem hL hrr
  have hfm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfm, node.a.family.storedType]; rfl
  refine ⟨fun e he r hr => groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr),
    fun c hc => ?_⟩
  have hc' : c ∈ ofFin node.a.constructors.length
      (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
  have hrefs := groupMembersT_ctor_refs hmem _ _ (node_ctor_mem hmem hL hrr node i)
    (node.a.constructorViews i).hasClass
  rw [(node.a.constructorViews i).storedType] at hrefs
  have key : ∀ r, r ∈ denRefs (policyPi ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
      (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
        (policyParameterLocals (node.a.constructorViews i).parameters.length (node.a.constructorViews i).fields.length ++
          (node.a.constructorViews i).resultIndices))) → Dom E r ∨ r = (famDataOf node.a).fref := by
    intro r hr
    by_cases hrf : r = f
    · exact Or.inr (hrf.trans node.fam.symm)
    · exact Or.inl (dom_of_extend_ne (hrefs r hr) hrf)
  exact ⟨fun e he r hr => key r (refs_policyPi_dom _ _ e (List.mem_append_right _ he) hr),
    fun e he r hr => key r (refs_policyPi_body _ (refs_foldApps _ _ (Or.inr ⟨e, List.mem_append_right _ he, hr⟩)) _)⟩

theorem groupRoles_fam {fd fd' : FamData} {f rr : Nat} {ctx0 : Nat → Role} {r : Nat}
    (h : groupRoles fd f rr ctx0 r = .fam fd') (h0 : ctx0 r = .plain) : r = f ∧ fd' = fd := by
  unfold groupRoles at h
  by_cases h1 : r = f
  · rw [if_pos h1] at h; cases h; exact ⟨h1, rfl⟩
  · rw [if_neg h1] at h
    by_cases h2 : r = rr
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : f < r ∧ r < rr
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3, h0] at h; cases h

theorem dom_groupMembersT {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E ms E')
    {r : Nat} (h : Dom E r) : Dom E' r := by
  unfold Dom at *
  cases hm : E.members r with
  | none => rw [hm] at h; exact absurd h (by decide)
  | some m => rw [groupMembersT_preserve hmem r m hm]; rfl

/-- Fresh references have the plain role. -/
theorem envCtx_fresh {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassG hW) (r : Nat) (h : E.members r = none) :
    envCtx hW r = .plain :=
  envCtx_freshW hW (walkG_of_classG hW hC) r h

/-- **Every member reads inside the environment before it**, at the roles of the
environment (over `WalkG`). -/
theorem readsOKAlong_envCtxW : {E : ResolvedEnv} → (hW : EnvWfT E) → WalkG hW → ∀ ctx : Nat → Role,
    (∀ r, Dom E r → ctx r = envCtx hW r) → ReadsOKAlong ctx hW
  | _, .empty, _, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _ => hC.elim
  | _, .definition E r A v u hE hfresh hA hv _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxW hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshW hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .thm E r A p hE hfresh hA hp _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxW hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshW hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hp r' h⟩
  | _, .opaque E r A v u hE hfresh hA hv _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxW hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshW hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, ctx, hctx => by
      obtain ⟨hCE, hWR, _⟩ := hC
      obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
      refine ⟨readsOKAlong_envCtxW hE hCE ctx fun r' h => (hctx r' (dom_groupMembersT hmem h)).trans
        (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r' h), ?_⟩
      obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
      refine groupReadsOK_of ctx hmem (fun _ h => h) fun c hc fd hcf => ?_
      have hd : Dom E' c.1 := dom_of_members (groupMembersT_installed hmem hc)
      rw [hctx c.1 hd, envCtx_group_some hE hfam hctors hrec hmem _ hs] at hcf
      obtain ⟨hcf1, rfl⟩ := groupRoles_fam hcf (envCtx_freshW hE hCE c.1 (groupMembersT_fresh_base hmem c.1 c.2 hc))
      exact famReads_node hmem hL hrr node

/-- **Every member reads inside the environment before it**, at the roles of the
environment. -/
theorem readsOKAlong_envCtx {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassG hW) (ctx : Nat → Role)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r) : ReadsOKAlong ctx hW :=
  readsOKAlong_envCtxW hW (walkG_of_classG hW hC) ctx hctx

/-! ### the group's table entries -/

theorem groupRoles_at_f (fd : FamData) (f rr : Nat) (ctx0 : Nat → Role) : groupRoles fd f rr ctx0 f = .fam fd := by
  unfold groupRoles; rw [if_pos rfl]

theorem groupRoles_at_rr (fd : FamData) {f rr : Nat} (h : f < rr) (ctx0 : Nat → Role) :
    groupRoles fd f rr ctx0 rr = .recursor fd := by
  unfold groupRoles; rw [if_neg (by omega), if_pos rfl]

theorem groupRoles_at_ctor (fd : FamData) {f rr : Nat} (ctx0 : Nat → Role) {i : Nat} (h : f + 1 + i < rr) :
    groupRoles fd f rr ctx0 (f + 1 + i) = .ctor fd i := by
  unfold groupRoles
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, h⟩]
  congr 1
  omega

theorem famBounded_node {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hTF : TypeFacts E') : FamBounded (famDataOf node.a) node.a.family.member.arity := by
  have hb := (hTF f _ (node_fam_member node)).2.1
  rw [node.a.family.storedType] at hb
  obtain ⟨hD, _⟩ := levelsBounded_policyPi _ _ _ hb
  refine ⟨(ExprsBounded_append hD).1, (ExprsBounded_append hD).2, node.a.family.resultBounded, fun c hc => ?_⟩
  have hc' : c ∈ ofFin node.a.constructors.length
      (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
  have hb' := (hTF _ _ (node_ctor_member node i)).2.1
  rw [(node.a.constructorViews i).arity, (node.a.constructorViews i).storedType] at hb'
  obtain ⟨hD', hbody⟩ := levelsBounded_policyPi _ _ _ hb'
  exact ⟨(ExprsBounded_append hD').2, (ExprsBounded_append (levelsBounded_foldApps _ _ _ hbody).2).2⟩

theorem groupFaith_of (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {ctx ctx0 : Nat → Role} {E E' : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) (hF : FaithfulR P μ ctx E')
    (hctx : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr ctx0 r) (hTF : TypeFacts E')
    (hfix : ∀ vs, Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
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

/-! ### the empty type -/

/-- A sound recursor of the empty type's shape at reference 1 empties the type at
reference 0: apply it to the constant motive `fun _ => ∅`. -/
theorem empty_of_falseRec (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    (h1 : MemberSound P μ K 1 falseRecMemberU) {x : PSet.{4}} (hx : x ∈ Ed (mkM P μ) (μ 0 [])) : False := by
  have hR : μ 1 [0] ∈ Ed (mkM P μ) (piVal (mkM P μ) (piVal (mkM P μ) (μ 0 []) (fun _ => tyv (U W4 0)))
      (fun mot => piVal (mkM P μ) (μ 0 []) (fun t => fapp mot t))) :=
    (h1 (fun _ => 0) [.zero] ρ0 rfl (fun l hl => by
      rw [List.mem_singleton] at hl; subst hl; exact Nat.zero_le _)).1
  have hm : lamVal (mkM P μ) (μ 0 []) (fun _ => tyv pempty) ∈
      Ed (mkM P μ) (piVal (mkM P μ) (μ 0 []) (fun _ => tyv (U W4 0))) :=
    lam_mem _ (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) fun _ _ =>
      mem_congr_right (ed_tyv _ (U4_dich 0)).symm (tyv_pempty_mem_U4 P 0)
  have h2 := app_mem _ (fun mot mot' hm => piVal_congr _ Equiv.rfl fun t t' ht => fapp_congr hm ht) hR hm
  have h3 := app_mem _ (fun t t' ht => fapp_congr Equiv.rfl ht) h2 hx
  have hb := beta_val (mkM P μ) (b := fun _ => tyv pempty) (fun _ _ _ => Equiv.rfl) hx
  exact ed_tyv_pempty _ (mem_congr_right (ed_congr _ hb) h3)

/-! ### transfer and walk facts -/

theorem agreeOn_symm {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop} (h : AgreeOn μ₁ μ₂ S) :
    AgreeOn μ₂ μ₁ S := fun r hr ls => (h r hr ls).symm

/-- Faithfulness transfers to a table agreeing on the environment. -/
theorem faithfulR_transfer (P : Premises4) {μ μ' : Nat → List Nat → PSet.{4}} {ctx : Nat → Role}
    {E : ResolvedEnv} (hF : FaithfulR P μ ctx E) (hR : ReadsClosed ctx E) (hag : AgreeOn μ' μ (Dom E)) :
    FaithfulR P μ' ctx E := fun r m h vs => by
  rw [hag r (dom_of_members h) vs]
  exact (hF r m h vs).trans (memberValR_agree P (agreeOn_symm hag) (ctx r) m (hR r m h) vs)

/-- A singleton member with a closed, level-free body, sound in the prefix. -/
theorem memberSound_singleton' {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E : ResolvedEnv} {r : Nat} {k : MemberClass} {A v : Expr Nat}
    (hval : Equiv (μ r []) (den (mkM P μ) (fun _ => 0) ρ0 v))
    (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A) (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true)
    (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (hES : EnvSound (mkM P μ) (fun _ => 0) K E 0) : MemberSound P μ K r ⟨k, 0, A, some v⟩ := by
  intro σ ls ρ hlen _
  have hls : ls = [] := List.eq_nil_of_length_eq_zero hlen
  subst hls
  have hσ : σOf (([] : List Level).map (evalTotal σ)) = fun _ => 0 := rfl
  have hS := sound_ty (P.good (mkM P μ) rfl) hES hv hl ρ0 trivial
  show μ r [] ∈ _ ∧ _
  refine ⟨?_, fun b hb => ?_⟩
  · rw [den_inst_canon (mkM P μ) σ [] ρ A hclA hlvlA, hσ]
    exact mem_congr_left hval.symm hS
  · cases hb
    show Equiv (μ r []) _
    rw [den_inst_canon (mkM P μ) σ [] ρ v hclv hlvlv, hσ]
    exact hval

/-- The parameters, fields and result indices of a constructor read inside the base. -/
theorem node_ctor_refsIn {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm)
    (hocc : ∀ i, ∀ T, T ∈ (node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields ++
        (node.a.constructorViews i).resultIndices → occursConst f T = false) (i : Fin node.a.constructors.length) :
    RefsIn (Dom E) ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields ++
      (node.a.constructorViews i).resultIndices) := by
  have hrefs := groupMembersT_ctor_refs hmem _ _ (node_ctor_mem hmem hL hrr node i)
    (node.a.constructorViews i).hasClass
  rw [(node.a.constructorViews i).storedType] at hrefs
  intro e he r hr
  refine dom_of_extend_ne (hrefs r ?_) (denRefs_ne_of_occurs e (hocc i e he) r hr)
  rcases List.mem_append.mp he with he | he
  · exact refs_policyPi_dom _ _ e he hr
  · exact refs_policyPi_body _ (refs_foldApps _ _ (Or.inr ⟨e, List.mem_append_right _ he, hr⟩)) _

/-! ### occurrences and views -/

theorem one_mem_denRefsLit : (t : Nat) → 1 ∈ denRefsLit t
  | 0 => List.mem_singleton_self 1
  | t + 1 => List.mem_cons_of_mem _ (one_mem_denRefsLit t)

/-- An expression none of whose references is `f` does not mention `f`. -/
theorem occurs_false_of_refs {f : Nat} : (e : Expr Nat) → (∀ r, r ∈ denRefs e → r ≠ f) → occursConst f e = false
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r _, h => by
      have := h r (List.mem_singleton_self r)
      show decide (r = f) = false
      exact decide_eq_false this
  | .app a b, h => by
      show (occursConst f a || occursConst f b) = false
      rw [occurs_false_of_refs a (fun r hr => h r (List.mem_append_left _ hr)),
        occurs_false_of_refs b (fun r hr => h r (List.mem_append_right _ hr))]; rfl
  | .lam a b, h => by
      show (occursConst f a || occursConst f b) = false
      rw [occurs_false_of_refs a (fun r hr => h r (List.mem_append_left _ hr)),
        occurs_false_of_refs b (fun r hr => h r (List.mem_append_right _ hr))]; rfl
  | .pi a b, h => by
      show (occursConst f a || occursConst f b) = false
      rw [occurs_false_of_refs a (fun r hr => h r (List.mem_append_left _ hr)),
        occurs_false_of_refs b (fun r hr => h r (List.mem_append_right _ hr))]; rfl
  | .letE a v b, h => by
      show ((occursConst f a || occursConst f v) || occursConst f b) = false
      rw [occurs_false_of_refs a (fun r hr => h r (List.mem_append_left _ (List.mem_append_left _ hr))),
        occurs_false_of_refs v (fun r hr => h r (List.mem_append_left _ (List.mem_append_right _ hr))),
        occurs_false_of_refs b (fun r hr => h r (List.mem_append_right _ hr))]; rfl
  | .lit t, h => by
      show litOccurs f t = false
      have h1 : f ≠ 1 := fun e => h 1 (one_mem_denRefsLit t) e.symm
      unfold litOccurs
      cases t with
      | zero => exact decide_eq_false h1
      | succ t =>
          have h2 : f ≠ 2 := fun e => h 2 (List.mem_cons_self _ _) e.symm
          simp only [decide_eq_false h1, decide_eq_false h2, Bool.or_self]

theorem foldApps_const_head {r r' : Nat} {ls ls' : List Level} {as as' : List (Expr Nat)}
    (h : foldApps (.const r ls) as = foldApps (.const r' ls') as') : r = r' := by
  have := congrArg (fun e => (appsSpine e).1) h
  simp only [appsSpine_foldApps, appsSpine] at this
  cases this
  rfl

/-- A field list in the class is classified for the recursor's stage induction. -/
theorem fieldsClass_of_direct {f ar np nq : Nat} : (Fs : List (Expr Nat)) → (d : Nat) →
    RecFieldsDirect f (canonL ar) np nq Fs d → FieldsClass f ar np nq Fs d
  | [], _, _ => trivial
  | _ :: Fs, d, ⟨hA, hFs⟩ => ⟨hA, fieldsClass_of_direct Fs (d + 1) hFs⟩

theorem RecFieldsDirect.mem {f : Nat} {lsF : List Level} {np nq : Nat} : {Fs : List (Expr Nat)} → {d : Nat} →
    RecFieldsDirect f lsF np nq Fs d → ∀ A, A ∈ Fs →
      occursConst f A = false ∨ ∃ (d' : Nat) (idx : List (Expr Nat)),
        A = foldApps (.const f lsF) (policyParameterLocals np d' ++ idx) ∧ idx.length = nq ∧
          ∀ e, e ∈ idx → occursConst f e = false
  | B :: Fs, d, ⟨hB, hFs⟩, A, hA => by
      rcases List.mem_cons.mp hA with rfl | hA
      · rcases hB with h | ⟨idx, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨d, idx, h1, h2, h3⟩
      · exact RecFieldsDirect.mem hFs A hA

/-! ### soundness along a group's walk -/

/-- The members of a group are sound in walk order: the family and the recursor
by the given facts, each constructor from its own admission at the
environment it is admitted in. -/
theorem walk_sound (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S E' : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember} (full : List (Nat × CheckedMember))
    (agree : ∀ (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew) (m : CheckedMember),
      PolicyConstructorView Ew famO m → Prop)
    (hcl : ∀ c, c ∈ full → c.2.mclass = .inductiveM → c = (f, fm))
    (hrcl : ∀ c, c ∈ full → c.2.mclass = .recursorM → c = (rr, rm))
    (hfS : MemberSound P μ K f fm) (hrS : MemberSound P μ K rr rm)
    (hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ full → Ew.members r = none → FieldUniverseAdmitted cv →
      agree Ew famO m cv →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m) :
    {Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hw : GroupMembersT S Ew ms E'') →
    (∀ c, c ∈ ms → c ∈ full) → (∀ r m, E''.members r = some m → E'.members r = some m) →
    WalkRec hw → WalkAgree agree hw → WalkB2 K hw → AllSound P μ K Ew → AllSound P μ K E''
  | _, _, _, .nil _, _, _, _, _, _, hA => hA
  | Ew, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest, hms, hsub, hW, hAgr, hWB, hA => by
      obtain ⟨hwc, hwcs⟩ := hW
      obtain ⟨hagc, hagcs⟩ := hAgr
      obtain ⟨hwb, hwbs⟩ := hWB
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hnew : MemberSound P μ K r m := by
        cases hadm with
        | family _ view _ hm _ =>
            have hk : m.mclass = .inductiveM := hm ▸ view.hasClass
            have := hcl _ hin hk
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
            exact hfS
        | recursor _ _ _ _ _ _ _ =>
            have := hrcl _ hin hwc
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
            exact hrS
        | constructor famO view _ _ _ h07 _ =>
            exact hcS Ew r m famO view hin hfresh h07 hagc hwb hsubR hA
      have hA' : AllSound P μ K (extendEnv Ew r m) := by
        intro r' m' h
        by_cases hr : r' = r
        · subst hr; rw [members_extend_eq] at h; cases h; exact hnew
        · rw [members_extend_ne Ew r m r' hr] at h; exact hA r' m' h
      exact walk_sound P μ K full agree hcl hrcl hfS hrS hcS hrest (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub
        hwcs hagcs hwbs hA'

/-- What the induction carries: at any table faithful to the roles of the
environment, every member is sound and ι holds at every recursor. -/
def GInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) → ∀ μ, FaithfulR P μ ctx E →
    AllSound P μ K E ∧ ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

/-- The invariant relative to one final environment `Efin ⊇ E`: ι only at `Efin`. -/
def GInvAt (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  (∀ r m, E.members r = some m → Efin.members r = some m) →
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtx hW r) → ∀ μ, FaithfulR P μ ctx E →
    AllSound P μ K E ∧ ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

theorem gInvAt_of_gInv {P : Premises4} {K : Nat → Nat} {Efin E : ResolvedEnv} {hW : EnvWfT E}
    (h : GInv P K hW) : GInvAt P K Efin hW := fun hsub ctx hctx μ hF =>
  ⟨(h ctx hctx μ hF).1, (h ctx hctx μ hF).2 Efin hsub⟩

theorem gInv_of_gInvAt {P : Premises4} {K : Nat → Nat} {E : ResolvedEnv} {hW : EnvWfT E}
    (h : ∀ Efin, GInvAt P K Efin hW) : GInv P K hW := fun ctx hctx μ hF =>
  ⟨(h E (fun _ _ h => h) ctx hctx μ hF).1, fun Efin hsub => (h Efin hsub ctx hctx μ hF).2⟩

/-- The step of a definition, theorem or opaque constant, relative to `Efin`. -/
theorem gInv_singleWAt (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E : ResolvedEnv} {hE : EnvWfT E}
    {r : Nat} {k : MemberClass} {A v : Expr Nat} (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none) (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v) (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true) (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (hC : WalkG hE) (IH : GInvAt P K Efin hE)
    (hsubF : ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → Efin.members r' = some m')
    (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' → ctx r' = envCtx hE r') (μ : Nat → List Nat → PSet.{4})
    (hF : FaithfulR P μ ctx (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → m'.mclass = .recursorM →
        IotaAt P μ K Efin r' := by
  have hsub := members_extend_preserved (m := ⟨k, 0, A, some v⟩) hfresh
  have IHμ := IH (fun r' m' h => hsubF r' m' (hsub r' m' h)) ctx (fun r' h => hctx r' (dom_extend hfresh r' h)) μ
    (fun r' m' h => hF r' m' (hsub r' m' h))
  have hES : EnvSound (mkM P μ) (fun _ => 0) K E 0 := envSound_of P (Efin := Efin)
    (fun r' m' h => hsubF r' m' (hsub r' m' h)) IHμ.1 (fun r' m' h hk' => IHμ.2 r' m' h hk') _ 0
  have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshW hE hC r hfresh)
  have hval : Equiv (μ r []) (den (mkM P μ) (fun _ => 0) ρ0 v) := by
    have h := hF r _ (members_extend_eq E r _) []
    have e : memberValR P μ .plain ⟨k, 0, A, some v⟩ [] = den (mkM P μ) (fun _ => 0) ρ0 v :=
      mem_memberVal_def hk A v []
    rw [hr, e] at h
    exact h
  refine ⟨fun r' m' h => ?_, fun r' m' h hk' => ?_⟩
  · by_cases hr' : r' = r
    · subst hr'; rw [members_extend_eq] at h; cases h
      exact memberSound_singleton' hval hclA hclv hlvlA hlvlv hv hl hES
    · rw [members_extend_ne E r _ r' hr'] at h; exact IHμ.1 r' m' h
  · by_cases hr' : r' = r
    · subst hr'; rw [members_extend_eq] at h; cases h; rcases hk with rfl | rfl | rfl <;> cases hk'
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.2 r' m' h hk'

/-- The step of a definition, theorem or opaque constant. -/
theorem gInv_singleW (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} {hE : EnvWfT E} {r : Nat}
    {k : MemberClass} {A v : Expr Nat} (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none) (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v) (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true) (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (hC : WalkG hE) (IH : GInv P K hE) (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' → ctx r' = envCtx hE r') (μ : Nat → List Nat → PSet.{4})
    (hF : FaithfulR P μ ctx (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ Efin, (∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → Efin.members r' = some m') →
        ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → m'.mclass = .recursorM →
          IotaAt P μ K Efin r' := by
  refine ⟨(gInv_singleWAt P K _ hk hfresh hclA hclv hlvlA hlvlv hv hl hC (gInvAt_of_gInv IH) (fun _ _ h => h)
    ctx hctx μ hF).1, fun Efin hsubF => ?_⟩
  exact (gInv_singleWAt P K Efin hk hfresh hclA hclv hlvlA hlvlv hv hl hC (gInvAt_of_gInv IH) hsubF ctx hctx μ hF).2


/-- The step of a definition, theorem or opaque constant in `ClassG`. -/
theorem gInv_single (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} {hE : EnvWfT E} {r : Nat}
    {k : MemberClass} {A v : Expr Nat} (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none) (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v) (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true) (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (hC : ClassG hE) (IH : GInv P K hE) (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' → ctx r' = envCtx hE r') (μ : Nat → List Nat → PSet.{4})
    (hF : FaithfulR P μ ctx (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ Efin, (∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → Efin.members r' = some m') →
        ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → m'.mclass = .recursorM →
          IotaAt P μ K Efin r' :=
  gInv_singleW P K hk hfresh hclA hclv hlvlA hlvlv hv hl (walkG_of_classG hE hC) IH ctx hctx μ hF
/-- Under family-free fields, every matching shape is nonrecursive. -/
theorem nonrec_of_shapesMatch {f : Nat} {shapes : List FieldShape} {Fs : List (Expr Nat)}
    (hsm : ShapesMatch f shapes Fs) (hnf : ∀ T, T ∈ Fs → occursConst f T = false) :
    ∀ s, s ∈ shapes → s = .nonrecursive := by
  intro s hs
  obtain ⟨hl, hm⟩ := hsm
  obtain ⟨k, hk1, hk2⟩ := List.mem_iff_getElem.mp hs
  have hkF : k < Fs.length := by rw [← hl]; exact hk1
  rcases hm k s _ (by rw [List.getElem?_eq_getElem hk1, hk2]) (List.getElem?_eq_getElem hkF) with
    ⟨h, _⟩ | ⟨_, _, ho⟩
  · exact h
  · rw [hnf _ (List.getElem_mem hkF)] at ho; cases ho

/-- What the group step has established when it reaches the recursor. -/
structure RecStepCtx (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (fm : CheckedMember) (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}) : Prop where
  faith : GroupFaith P μ fm node
  lim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs)
  scope : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n
  facts : TypeFacts E'
  pfree : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
    occursConst (famDataOf node.a).fref e = false
  cls : ∀ c, c ∈ (famDataOf node.a).ctors → ∀ A, A ∈ c.1 →
    occursConst (famDataOf node.a).fref A = false ∨ RecApp (famDataOf node.a) node.a.family.member.arity A
  rmem : E'.members rr = some rm
  rbody : rm.body = none
  rfd : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
    node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0
  lvC : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true
  shapes : ∀ (i : Fin node.a.constructors.length) fuel shapes, fieldShapesFuel node.E0 fuel f
    node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
    node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
    ShapesMatch f shapes (node.a.constructorViews i).fields

/-- The recursor's package: it is sound, and ι holds at it in every extension. -/
def RecPkg (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (E' : ResolvedEnv) (rr : Nat)
    (rm : CheckedMember) : Prop :=
  MemberSound P μ K rr rm ∧ ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr

/-- The recursor's package relative to one final environment `Efin ⊇ E'`. -/
def RecPkgAt (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (Efin E' : ResolvedEnv) (rr : Nat)
    (rm : CheckedMember) : Prop :=
  (∀ r m, E'.members r = some m → Efin.members r = some m) → MemberSound P μ K rr rm ∧ IotaAt P μ K Efin rr

theorem recPkgAt_of {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {Efin E' : ResolvedEnv}
    {rr : Nat} {rm : CheckedMember} (h : RecPkg P μ K E' rr rm) : RecPkgAt P μ K Efin E' rr rm :=
  fun hsub => ⟨h.1, h.2 Efin hsub⟩

/-- **The recursor's package for `ClassG`**: `Type` groups (`recVal_mem_rec`),
`Prop` groups into `Prop` (`recVal_mem_recP`), `Prop` large elimination with
family-free fields (`rec_member_sound`) or with a recursive field (an empty
family, `rec_member_sound_empty`); ι by `iota_at`. -/
theorem recPkg_classG (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    (node : RecNode E E' f rr rm) {μ : Nat → List Nat → PSet.{4}}
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i k, k < (node.a.constructorViews i).fields.length →
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
          none)
    (hB3 : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) (vs : List Nat), (∀ v, v ∈ vs → v ≤ K rr) →
      ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level, UniformProp l ∧
        ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
          (policyPrefixContext (node.a.family.parameters ++ (node.a.constructorViews i).fields)
            (node.a.family.parameters.length + k.val))
          ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d) (X : RecStepCtx P K fm node μ) : RecPkg P μ K E' rr rm := by
  obtain ⟨hG, hLimμ, hES_S, hTF, hpfF, hclsF, hr', hrb, hrfR, hlvC, hsh⟩ := X
  -- under large elimination of a `Prop` family: nonrecursive shapes, proof fields
  have hnrec : ∀ (i : Fin node.a.constructors.length),
      (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) →
      ∀ fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref
        node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
        node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
        ∀ s, s ∈ shapes → s = .nonrecursive := by
    intro i hnf fuel shapes hfs
    rw [node.fam] at hfs
    exact nonrec_of_shapesMatch (hsh i fuel shapes hfs) hnf
  have hPT : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps,
        TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
        PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0) := by
    intro hU hpol i vs hvs ps hps
    refine propTel_of_typings P μ K vs _ _ (hES_S (σOf vs) node.a.family.member.arity) (fun k => ?_) ps hps
    obtain ⟨l, hl, hd⟩ := hB3 hU hpol i vs hvs k
    exact ⟨l, hl _, hd⟩
  -- under large elimination of a `Prop` family whose constructor has a recursive field: the family is empty
  have hone : UniformProp node.a.family.resultLevel → node.a.policy = .anySort → node.a.constructors.length ≤ 1 :=
    fun hU hpol => (selection_prop node.a (fun _ => 0) (hU _) hpol).2
  have hnfOf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length, ¬ (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) →
      ∀ c, c ∈ (famDataOf node.a).ctors → ¬ ∀ A, A ∈ c.1 → occursConst (famDataOf node.a).fref A = false := by
    intro hU hpol i hni c hc hall
    have hc' : c ∈ ofFin node.a.constructors.length
        (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
    obtain ⟨i', rfl⟩ := mem_ofFin _ _ hc'
    have e : i' = i := Fin.ext (by have := hone hU hpol; have := i.isLt; have := i'.isLt; omega)
    subst e
    have hfr : (famDataOf node.a).fref = f := node.fam
    rw [hfr] at hall
    exact hni hall
  have hEmpty : UniformProp node.a.family.resultLevel →
      (∀ c, c ∈ (famDataOf node.a).ctors → ¬ ∀ A, A ∈ c.1 → occursConst (famDataOf node.a).fref A = false) →
      ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a) := fun hU hnf vs =>
    propEmpty_of_lim P μ (famDataOf node.a) node.a.family.member.arity (famBounded_node node hTF) hpfF hclsF
      (σOf vs) (hU _) hnf (fun r ls => (tabLim_equiv P μ node.a hLimμ r ls).symm)
  -- ι at the group's recursor
  have hIrr : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr :=
    fun Efin hsubF => iota_at P hG hsubF hr' hrfR hlvC (fun hU hpol i => by
      refine @Decidable.byCases (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) _ inferInstance
        (fun hfree => ?_) (fun hni => Or.inr (hEmpty hU (hnfOf hU hpol i hni)))
      obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
      have hmt := derivedMinor_nonrec node.a i fuel shapes (hnrec i hfree fuel shapes hfs)
        (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
      rw [hdm] at hmt
      exact Or.inl ⟨fun T hT => by rw [node.fam]; exact hfree T hT, hpf hU hpol i, ⟨_, hmt⟩, hPT hU hpol i⟩)
  -- the recursor
  have hrmS : MemberSound P μ K rr rm := by
    have hcl := (hTF _ _ hr').1
    have hlvl := (hTF _ _ hr').2.1
    have RG : RecGroup node.a := by
      refine ⟨famBounded_node node hTF, hpfF, fun i => ?_, fun i e he => ?_, fun ls => ?_, fun i => ?_⟩
      · exact fieldsClass_of_direct _ 0 (hrfR i)
      · exact (node.a.constructorViews i).noFamilyInIndices e he
      · unfold transparentBody
        rw [node.a.family.present]
        show (if transparent node.a.family.member.mclass then _ else none) = none
        rw [node.a.family.hasClass]
        rfl
      · obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
        have hfs' := hfs
        rw [node.fam] at hfs'
        exact ⟨fuel, shapes, by rw [node.fam]; exact hsh i fuel shapes hfs', hdm⟩
    rcases selection_uniform node.a with hU | hT
    · cases hpol : node.a.policy with
      | propOnly =>
          intro σ ls ρ hlen _
          refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
          rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
          refine mem_congr_left (hG.recur _).symm ?_
          exact recVal_mem_recP P μ node.a RG hLimμ _ (groupFaith_ctorAt P hG _) (hU _) hpol
      | anySort =>
          refine @Decidable.byCases (∀ (i : Fin node.a.constructors.length) T, T ∈ (node.a.constructorViews i).fields →
            occursConst f T = false) _ inferInstance (fun hfree => ?_) (fun hni => ?_)
          · exact rec_member_sound P hG hcl hlvl hrb (fun i => hnrec i (hfree i))
              (fun hU' hpol' i => ⟨hpf hU' hpol' i, hPT hU' hpol' i⟩)
              (fun i T hT => by rw [node.fam]; exact hfree i T hT)
          · refine rec_member_sound_empty P hG hcl hlvl hrb hU (hEmpty hU fun c hc hall => ?_)
            have hc' : c ∈ ofFin node.a.constructors.length
                (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
            obtain ⟨i', rfl⟩ := mem_ofFin _ _ hc'
            have hfr : (famDataOf node.a).fref = f := node.fam
            rw [hfr] at hall
            refine hni fun i => ?_
            have e : i = i' := Fin.ext (by have := hone hU hpol; have := i.isLt; have := i'.isLt; omega)
            subst e
            exact hall
    · intro σ ls ρ hlen _
      refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
      rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
      refine mem_congr_left (hG.recur _).symm ?_
      exact recVal_mem_rec P μ node.a RG hLimμ _ (groupFaith_ctorAt P hG _) (Nat.pos_iff_ne_zero.mp (hT _))
  exact ⟨hrmS, hIrr⟩

/-- The step of a group relative to a final environment `Efin`, from the recursor's package: given the facts the
step establishes at the recursor (`RecStepCtx`), the class supplies the
recursor's soundness and ι there (`RecPkg`). Everything else (the family at
its limit, the constructors along the walk) is shared by every class. -/
theorem gInv_group_ofAt (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hrfN : ∀ node : RecNode E E' f rr rm, ∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hWR : WalkRec hmem)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB1 : (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
      vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d))
    (hWB : WalkB2 K hmem)
    (hpkg : ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ →
      RecPkgAt P μ K Efin E' rr rm)
    (IH : GInvAt P K Efin hE) : GInvAt P K Efin (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem hWR
  intro hsubFin ctx hctx μ hF
  obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
  have hrf := hrfN node
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtx hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr (envCtx hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtx_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : FaithfulR P μ ctx E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH (fun r m h => hsubFin r m (hsubE r m h)) ctx hctxE μ hFE
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  -- the family's entry is its limit, a fixed point of its value
  have hLimμ : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
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
  have hclsF : ∀ c, c ∈ (famDataOf node.a).ctors → ∀ A, A ∈ c.1 →
      occursConst (famDataOf node.a).fref A = false ∨ RecApp (famDataOf node.a) node.a.family.member.arity A := by
    intro c hc A hA
    have hc' : c ∈ ofFin node.a.constructors.length
        (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
    have hfr : (famDataOf node.a).fref = f := node.fam
    rw [hfr]
    rcases (hrf i).mem A hA with h | ⟨d, idx, hd, hidxl, hidxF⟩
    · exact Or.inl h
    · refine Or.inr ⟨policyParameterLocals node.a.family.parameters.length d ++ idx, by rw [hfr, hd]; rfl, ?_,
        fun e he => by rw [hfr]; exact recArgs_free _ _ _ hidxF e he⟩
      show _ = (node.a.family.parameters ++ node.a.family.indices).length
      rw [List.length_append, List.length_append, length_paramLocals, hidxl]
  have hriF : ∀ c, c ∈ (famDataOf node.a).ctors → ∀ e, e ∈ c.2 → occursConst (famDataOf node.a).fref e = false := by
    intro c hc e he
    have hc' : c ∈ ofFin node.a.constructors.length
        (fun i => ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices)) := hc
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
    exact (node.a.constructorViews i).noFamilyInIndices e he
  have hfix : ∀ vs, Equiv (famLim P μ (famDataOf node.a) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) :=
    fun vs => (famLim_fix P μ (famDataOf node.a) node.a.family.member.arity (famBounded_node node hTF) hpfF hclsF
      hriF vs).symm.trans (famVal_tables P (tabLim_equiv P μ node.a hLimμ) _ _)
  have hG := groupFaith_of P hmem hL hrr node hF hctxG hTF hfix
  have hfmS : MemberSound P μ K f fm :=
    fam_member_sound P (famDataOf node.a) hG.fam hG.famTy (hTF f fm hf').1 (hTF f fm hf').2.1 hbf
  -- ι at the group's recursor
  have hrfR : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0 :=
    fun i => by rw [node.fam]; exact hrf i
  have hopq : ∀ ls, transparentBody node.E0 f ls = none := by
    intro ls
    have hp := node.a.family.present
    rw [node.fam] at hp
    unfold transparentBody
    rw [hp]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have hsh : ∀ (i : Fin node.a.constructors.length) fuel shapes, fieldShapesFuel node.E0 fuel f
      node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
      node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
      ShapesMatch f shapes (node.a.constructorViews i).fields := fun i fuel shapes hfs =>
    shapesMatch_of_direct (famFreeBodies_node hE hf0 hmem node) hopq _ 0 _ (hrf i) shapes hfs
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
  have hP := hpkg node μ ⟨hG, hLimμ, hES_S, hTF, hpfF, hclsF, hr', hrb, hrfR, hlvC, hsh⟩ hsubFin
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
/-- The step of a group, from the recursor's package (in every extension). -/
theorem gInv_group_of (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hrfN : ∀ node : RecNode E E' f rr rm, ∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hWR : WalkRec hmem)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB1 : (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
      vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d))
    (hWB : WalkB2 K hmem)
    (hpkg : ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ →
      RecPkg P μ K E' rr rm)
    (IH : GInv P K hE) : GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  gInv_of_gInvAt fun Efin => gInv_group_ofAt P K Efin hE hfam hctors hrec hmem hrfN hWR hAg hB1 hWB
    (fun node μ X => recPkgAt_of (hpkg node μ X)) (gInvAt_of_gInv IH)


/-- The step of a group in `ClassG`. -/
theorem gInv_group (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hC : ClassG (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (IH : GInv P K hE) : GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  gInv_group_of P K hE hfam hctors hrec hmem (fun node => (hC.2.1 node).1)
    (walkG_of_classG (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) hC).2.1
    (walkG_of_classG (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) hC).2.2 hB.2.1 hB.2.2.1
    (fun node _ X => recPkg_classG P K node (hC.2.1 node).2 (hB.2.2.2 node) X) IH

/-- The bounds the whole-derivation induction reads: `BoundG` without its
`Prop` large-elimination field clause, which only a class's recursor package
uses (`recPkg_classG`). -/
def BoundW (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => BoundW K hE
  | _, .definition _ _ _ _ _ hE _ _ hv _ _ _ _ => BoundW K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .thm _ _ _ _ hE _ _ hp _ _ _ _ => BoundW K hE ∧ LOKt (fun _ => 0) 4 K hp
  | _, .opaque _ _ _ _ _ hE _ _ hv _ _ _ _ => BoundW K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .group E f fm _ rr rm E' hE _ _ _ hmem =>
      BoundW K hE ∧ (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
        ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
            (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d) ∧ WalkB2 K hmem

theorem boundW_of_boundG (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → BoundG K hW → BoundW K hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ hE _ _ _ _, hB => boundW_of_boundG K hE hB
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hB => ⟨boundW_of_boundG K hE hB.1, hB.2⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hB => ⟨boundW_of_boundG K hE hB.1, hB.2⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hB => ⟨boundW_of_boundG K hE hB.1, hB.2⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, hB => ⟨boundW_of_boundG K hE hB.1, hB.2.1, hB.2.2.1⟩

/-- At every group: the fields are family-free or direct family applications,
and the recursor's package holds (the class's ι and recursor soundness). -/
def PkgG (P : Premises4) (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => PkgG P K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => PkgG P K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => PkgG P K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => PkgG P K hE
  | _, .group E f fm _ rr rm E' hE _ _ _ _ =>
      PkgG P K hE ∧ (∀ node : RecNode E E' f rr rm, ∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family)
        node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ →
        RecPkg P μ K E' rr rm

/-- **The model invariant along a derivation**, for any class that supplies the
walk condition (`WalkG`), the bounds (`BoundG`) and each group's recursor
package (`PkgG`). -/
theorem gInv_of (P : Premises4) (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → WalkG hW →
    BoundW K hW → PkgG P K hW → GInv P K hW
  | _, .empty, _, _, _ => fun _ _ _ _ => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ _ _ h => (Option.noConfusion h)⟩
  | _, .axiom _ _ _ _ _ _ _ _ _, hW, _, _ => hW.elim
  | _, .definition _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hW, hB, hp =>
      gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2 hW (gInv_of P K hE hW hB.1 hp)
  | _, .thm _ _ _ _ hE hfresh _ hpr hclA hclp hlvlA hlvlp, hW, hB, hp =>
      gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hpr hB.2 hW (gInv_of P K hE hW hB.1 hp)
  | _, .opaque _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hW, hB, hp =>
      gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2 hW (gInv_of P K hE hW hB.1 hp)
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hW, hB, hp =>
      gInv_group_of P K hE hfam hctors hrec hmem hp.2.1 hW.2.1 hW.2.2 hB.2.1 hB.2.2 hp.2.2 (gInv_of P K hE hW.1 hB.1 hp.1)

/-- `ClassG` supplies every group's package. -/
theorem pkgG_of_classG (P : Premises4) (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassG hW →
    BoundG K hW → PkgG P K hW
  | _, .empty, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _ => hC.elim
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hB => pkgG_of_classG P K hE hC hB.1
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC, hB => pkgG_of_classG P K hE hC hB.1
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hB => pkgG_of_classG P K hE hC hB.1
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, hC, hB =>
      ⟨pkgG_of_classG P K hE hC.1 hB.1, fun node => (hC.2.1 node).1,
        fun node _ X => recPkg_classG P K node (hC.2.1 node).2 (hB.2.2.2 node) X⟩

/-- At every group: `RecFieldsDirect` and the recursor's package relative to `Efin`. -/
def PkgGAt (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => PkgGAt P K Efin hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => PkgGAt P K Efin hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => PkgGAt P K Efin hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => PkgGAt P K Efin hE
  | _, .group E f fm _ rr rm E' hE _ _ _ _ =>
      PkgGAt P K Efin hE ∧ (∀ node : RecNode E E' f rr rm, ∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family)
        node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
      ∀ (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ →
        RecPkgAt P μ K Efin E' rr rm

/-- **The model invariant relative to one final environment.** -/
theorem gInv_ofAt (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    WalkG hW → BoundW K hW → PkgGAt P K Efin hW → GInvAt P K Efin hW
  | _, .empty, _, _, _ => fun _ _ _ _ _ =>
      ⟨fun _ _ h => (Option.noConfusion h), fun _ _ h => (Option.noConfusion h)⟩
  | _, .axiom _ _ _ _ _ _ _ _ _, hW, _, _ => hW.elim
  | _, .definition _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hW, hB, hp => fun hsub =>
      gInv_singleWAt P K Efin (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2 hW
        (gInv_ofAt P K Efin hE hW hB.1 hp) hsub
  | _, .thm _ _ _ _ hE hfresh _ hpr hclA hclp hlvlA hlvlp, hW, hB, hp => fun hsub =>
      gInv_singleWAt P K Efin (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hpr hB.2 hW
        (gInv_ofAt P K Efin hE hW hB.1 hp) hsub
  | _, .opaque _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hW, hB, hp => fun hsub =>
      gInv_singleWAt P K Efin (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2 hW
        (gInv_ofAt P K Efin hE hW hB.1 hp) hsub
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hW, hB, hp =>
      gInv_group_ofAt P K Efin hE hfam hctors hrec hmem hp.2.1 hW.2.1 hW.2.2 hB.2.1 hB.2.2 hp.2.2
        (gInv_ofAt P K Efin hE hW.1 hB.1 hp.1)

/-- **The environment's own table is a sound model of it**, for any class
supplying the walk condition, the bounds and the recursor packages at the
environment itself: every member is sound, and `EnvSound` holds. -/
theorem envμR_sound_ofAt (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hWk : WalkG hW)
    (hB : BoundW K hW) (hp : PkgGAt P K E hW) :
    AllSound P (envμR P (envCtx hW) hW) K E ∧
      ∀ σ n, EnvSound (mkM P (envμR P (envCtx hW) hW)) σ K E n := by
  have hRA := readsOKAlong_envCtxW hW hWk (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hI := gInv_ofAt P K E hW hWk hB hp (fun _ _ h => h) (envCtx hW) (fun _ _ => rfl) _ hF
  exact ⟨hI.1, fun σ n => envSound_of P (Efin := E) (fun _ _ h => h) hI.1 (fun r m hm hk => hI.2 r m hm hk) σ n⟩

/-- `EnvSound` at the environment's own table, for any class (see `envμR_sound_ofAt`). -/
theorem envSound_envμR_ofAt (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hWk : WalkG hW)
    (hB : BoundW K hW) (hp : PkgGAt P K E hW) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx hW) hW)) σ K E n :=
  (envμR_sound_ofAt P K hW hWk hB hp).2 σ n

/-- **Consistency below level 4 for any class**, with the recursor packages owed
only at the environment itself. -/
theorem consistent4_ofAt (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hWk : WalkG hW)
    (hB : BoundW K hW) (hp : PkgGAt P K E hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (h : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  have hS := envμR_sound_ofAt P K hW hWk hB hp
  empty_of_falseRec P (hS.1 1 _ h1) (sound_ty (P.good _ rfl) (hS.2 (fun _ => 0) n) h hl ρ0 trivial)

/-- Every package gives the package relative to any final environment. -/
theorem pkgGAt_of_pkgG (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv) : {E : ResolvedEnv} →
    (hW : EnvWfT E) → PkgG P K hW → PkgGAt P K Efin hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ hE _ _ _ _, hp => pkgGAt_of_pkgG P K Efin hE hp
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hp => pkgGAt_of_pkgG P K Efin hE hp
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hp => pkgGAt_of_pkgG P K Efin hE hp
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hp => pkgGAt_of_pkgG P K Efin hE hp
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, hp =>
      ⟨pkgGAt_of_pkgG P K Efin hE hp.1, hp.2.1, fun node μ X => recPkgAt_of (hp.2.2 node μ X)⟩

/-- `EnvSound` at the environment's own table, for `ClassG`. -/
theorem envSound_envμR_classG (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassG hW)
    (hB : BoundG K hW) (σ : Nat → Nat) (n : Nat) : EnvSound (mkM P (envμR P (envCtx hW) hW)) σ K E n :=
  envSound_envμR_ofAt P K hW (walkG_of_classG hW hC) (boundW_of_boundG K hW hB)
    (pkgGAt_of_pkgG P K E hW (pkgG_of_classG P K hW hC hB)) σ n

theorem gInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassG hW)
    (hB : BoundG K hW) : GInv P K hW :=
  gInv_of P K hW (walkG_of_classG hW hC) (boundW_of_boundG K hW hB) (pkgG_of_classG P K hW hC hB)

/-- **Consistency below level 4 for any class** supplying the walk condition,
the bounds and the groups' recursor packages. -/
theorem consistent4_of (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hWk : WalkG hW)
    (hB : BoundW K hW) (hp : PkgG P K hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (h : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False := by
  have hRA := readsOKAlong_envCtxW hW hWk (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hI := gInv_of P K hW hWk hB hp (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hI.1
    (fun r m hm hk => hI.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hI.1 1 _ h1) (sound_ty (P.good _ rfl) hES h hl ρ0 trivial)

/-- **Consistency below level 4 over environments of inductive groups.**
In an admitted environment in `ClassG` (no axioms; inductive groups whose
recursive fields are the family at its parameters and family-free indices,
indexed or not; under `Prop` large elimination no field revealed in the
result indices), whose constructor and field typings respect the
instance bound `K` (`BoundG`), and whose member 1 is the recursor of the
empty type at 0, no closed term has the type at 0, by any derivation whose sort levels are
at most 4 and whose constant instances respect `K`.
Relative to `Premises4` (choice in Lean's universes 0..3, decidability). -/
theorem consistent4_G (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassG hW)
    (hB : BoundG K hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (h : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  consistent4_of P K hW (walkG_of_classG hW hC) (boundW_of_boundG K hW hB) (pkgG_of_classG P K hW hC hB) h1 n e h hl

/-- The admitted empty-type environment is in the class, at every bound. -/
theorem falseEnvU_classG : ClassG falseEnvUWfT ∧ ∀ K, BoundG K falseEnvUWfT := by
  refine ⟨⟨trivial, fun node => ?_, fun _ => ⟨trivial, rfl, trivial⟩⟩,
    fun K => ⟨trivial, fun node i => ?_, ⟨trivial, trivial, trivial⟩, fun node _ _ i => ?_⟩⟩
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact ⟨fun i => absurd i.isLt (by omega), fun _ _ i => absurd i.isLt (by omega)⟩
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact absurd i.isLt (by omega)
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact absurd i.isLt (by omega)

/-- `consistent4_G` at the admitted empty-type environment. -/
theorem falseEnvU_consistent4G (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (h : HasTyT falseEnvU n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  consistent4_G P K falseEnvUWfT falseEnvU_classG.1 (falseEnvU_classG.2 K) rfl n e h hl

end PSet

end Rcic.F3
