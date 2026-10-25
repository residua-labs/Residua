import rcic.RcicF3DCtor
import rcic.RcicF3DBoundDefs

/-!
# F3 D-10: roles and reads with the normalized family

The table of an environment installs each member at its role (`envCtx`,
`envμR`). Here the family of every group is installed at the limit of its
**normalized** data's iterates (`.fam (nodeFam node)`), read off the recursor's
admission through the descriptor's bounds (`scanRecD`); constructors and
recursor keep their roles with the original data.

- `envCtxD`, `envCtxD_group_some`, `envCtxD_fresh`, `envCtxD_group_stable`:
  the roles (as `envCtx` and its facts);
- `famReads_nodeD`, `readsOKAlong_envCtxD`: every member reads inside the
  environment before it; the normalized fields read only the base's
  references and the family (`denRefs_whnf`, with closed bodies);
- `ClassGD`: the class of environments (no axioms; every group without
  function-recursive shapes, under `Prop` large elimination only family-free
  unrevealed fields, each constructor's parameters the family's; each
  constructor's own view splitting off the recursor view's parameters). The
  extra bound `BoundDG` (each constructor's fields typed in the constructor
  scope at instances within the recursor's bound) is `RcicF3DBoundDefs`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

namespace PSet

/-! ### the roles -/

/-- The group's normalized data, read off the admission of its recursor (the
member of class `recursorM`) at the descriptor's bounds. -/
def scanRecD {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Option FamData
  | _, _, _, .nil _ => none
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      match hadm with
      | .recursor a _ _ _ _ _ h14 =>
          if m.mclass = .recursorM then some (normFamData a h14.fuelAt) else scanRecD hrest
      | _ => scanRecD hrest

/-- The roles of an admitted environment, the families at their normalized data. -/
def envCtxD : {E : ResolvedEnv} → EnvWfT E → Nat → Role
  | _, .empty => fun _ => .plain
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCtxD hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtxD hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCtxD hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCtxD hE
  | _, .group _ f _ _ rr _ _ hE _ _ _ hmem =>
      match scanRecD hmem with
      | some fd => groupRoles fd f rr (envCtxD hE)
      | none => envCtxD hE

/-- The recursor node of a group, with the scanned normalized data (as `group_rec_node`). -/
theorem group_rec_nodeD {Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hlay : FamilyLayout Ebase) (hrmK : rm.mclass = .recursorM) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    (∀ c, c ∈ ms → c.1 = f ∨ c.2.mclass ≠ .inductiveM) → GroupWalkInv Ebase E f →
    (∀ r m, Ebase.members r = some m → E.members r = some m) →
    (∀ c, c ∈ ms → c.2.mclass = .recursorM → c.1 = rr ∧ c.2 = rm) → (rr, rm) ∈ ms →
    ∃ node : RecNode E E' f rr rm, scanRecD hmem = some (nodeFam node)
  | _, _, _, .nil _, _, _, _, _, h => absurd h (List.not_mem_nil _)
  | E, _, _, .cons _ r₀ m₀ _ _ hfresh hnobody _ _ _ _ _ hadm _ u hT _ htyped hrest, hl, hinv, hsub, huniq, hin => by
      by_cases hk : m₀.mclass = .recursorM
      · obtain ⟨h1, h2⟩ := huniq (r₀, m₀) (List.mem_cons_self _ _) hk
        simp only at h1 h2
        subst h1; subst h2
        cases hadm with
        | family _ view _ hm _ =>
            exact absurd (show m₀.mclass = .inductiveM from hm ▸ view.hasClass) (by rw [hk]; decide)
        | constructor _ view _ _ _ _ _ =>
            exact absurd view.hasClass (by rw [hk]; decide)
        | recursor a hfresh' h04 h07 h08 h12 h14 =>
            refine ⟨⟨E, a, h14, recursor_family_eq_group a hfresh' h04 hinv hlay hsub, hfresh',
              groupMembersT_mono hrest, fun _ _ h => h, h04, h07, h12, htyped.1, htyped.2.1, u, hT⟩, ?_⟩
            show (if m₀.mclass = .recursorM then some (normFamData a h14.fuelAt) else scanRecD hrest) = _
            rw [if_pos hk]; rfl
      · have hin' : (rr, rm) ∈ ‹List (Nat × CheckedMember)› := by
          rcases List.mem_cons.mp hin with h | h
          · obtain ⟨_, h2⟩ := Prod.mk.inj h
            exact absurd (h2 ▸ hrmK) hk
          · exact h
        obtain ⟨node, hn⟩ := group_rec_nodeD hlay hrmK hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _)))
          (fun r m h => members_extend_preserved hfresh r m (hsub r m h))
          (fun c hc hcK => huniq c (List.mem_cons_of_mem _ hc) hcK) hin'
        refine ⟨⟨node.E0, node.a, node.h14, node.fam, node.fresh, node.sub,
          fun r m h => node.base r m (members_extend_preserved hfresh r m h), node.h04, node.h07, node.h12,
          node.famTyped, node.ctorsTyped, node.u, node.hT⟩, ?_⟩
        cases hadm with
        | recursor a _ _ _ _ _ h14 =>
            show (if m₀.mclass = .recursorM then some (normFamData a h14.fuelAt) else scanRecD hrest) = _
            rw [if_neg hk]; exact hn
        | family _ _ _ _ _ => exact hn
        | constructor _ _ _ _ _ _ _ => exact hn

/-- The recursor node of a group step, with the scanned normalized data (as `group_node`). -/
theorem group_nodeD {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∃ node : RecNode E E' f rr rm, scanRecD hmem = some (nodeFam node) := by
  refine group_rec_nodeD (familyLayout_of_envWfT hE) hrec hmem ?_ (fun _ _ h => Or.inl h) (fun _ _ h => h) ?_
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · rcases List.mem_append.mp hc with hc | hc
      · exact Or.inr (by rw [hctors c hc]; decide)
      · rw [List.mem_singleton] at hc; subst hc; exact Or.inr (by rw [hrec]; decide)
  · intro c hc hk
    rcases List.mem_cons.mp hc with rfl | hc
    · exact absurd (hfam.symm.trans hk) (by decide)
    · rcases List.mem_append.mp hc with hc | hc
      · exact absurd ((hctors c hc).symm.trans hk) (by decide)
      · rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩

theorem envCtxD_group_some {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') (fd : FamData)
    (hs : scanRecD hmem = some fd) :
    envCtxD (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) = groupRoles fd f rr (envCtxD hE) := by
  show (match scanRecD hmem with
    | some fd => groupRoles fd f rr (envCtxD hE)
    | none => envCtxD hE) = _
  rw [hs]

/-! ### the class -/

/-- The conditions on one group with δ-hidden fields, read at its recursor node:
no function-recursive shape; under `Prop` large elimination, fields family-free
and none revealed in the result indices; each constructor's own parameters are
the family's (the fields' typings in `BoundDG` are in the constructor's own
telescope context, read at the family's parameter values). -/
def GroupClassD (E E' : ResolvedEnv) (f rr : Nat) (rm : CheckedMember) : Prop :=
  ∀ node : RecNode E E' f rr rm,
    NoFunRec node ∧
    (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i, (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst f T = false) ∧
        ∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
    ∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters = node.a.family.parameters

/-- The class of environments: no axioms; every group in `GroupClassD`, each
constructor's own view splitting off the recursor view's parameters. -/
def ClassGD : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ _ _ _ _ _ => False
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => ClassGD hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => ClassGD hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => ClassGD hE
  | _, .group E f _ _ rr rm E' hE _ _ _ hmem =>
      ClassGD hE ∧ GroupClassD E E' f rr rm ∧
        ∀ node : RecNode E E' f rr rm, WalkClass node.a.family.parameters.length hmem

/-- Fresh references have the plain role. -/
theorem envCtxD_fresh : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassGD hW → ∀ r, E.members r = none →
    envCtxD hW r = .plain
  | _, .empty, _, _, _ => rfl
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _ => hC.elim
  | _, .definition E r0 _ _ _ hE hfresh _ _ _ _ _ _, hC, r, h =>
      envCtxD_fresh hE hC r (Rcic.Model.PS.extendEnv_ne_none h).2
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hC, r, h => envCtxD_fresh hE hC r (Rcic.Model.PS.extendEnv_ne_none h).2
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hC, r, h =>
      envCtxD_fresh hE hC r (Rcic.Model.PS.extendEnv_ne_none h).2
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, r, h => by
      obtain ⟨hCE, _, hWC⟩ := hC
      obtain ⟨hL, hrr⟩ := group_layout_of_class hE hfam hctors hrec hmem hWC
      have hrE : E.members r = none := Rcic.Model.PS.groupMembersT_none hmem h
      show (match scanRecD hmem with
        | some fd => groupRoles fd f rr (envCtxD hE)
        | none => envCtxD hE) r = _
      cases scanRecD hmem with
      | none => exact envCtxD_fresh hE hCE r hrE
      | some fd =>
          obtain ⟨_, _, hf', hr', hbet⟩ := group_refs hmem hL hrr
          show groupRoles fd f rr (envCtxD hE) r = _
          unfold groupRoles
          have h1 : r ≠ f := by intro he; subst he; rw [hf'] at h; cases h
          have h2 : r ≠ rr := by intro he; subst he; rw [hr'] at h; cases h
          have h3 : ¬ (f < r ∧ r < rr) := by
            intro ⟨a, b⟩
            obtain ⟨_, _, _, _, hm⟩ := hbet r a b
            rw [hm] at h; cases h
          rw [if_neg h1, if_neg h2, if_neg h3]
          exact envCtxD_fresh hE hCE r hrE

/-- A group step does not change the roles of earlier members. -/
theorem envCtxD_group_stable {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (r : Nat) (hr : Dom E r) :
    envCtxD (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r = envCtxD hE r := by
  obtain ⟨hf0, hr0, _, _, hbet⟩ := group_refs hmem hL hrr
  show (match scanRecD hmem with
    | some fd => groupRoles fd f rr (envCtxD hE)
    | none => envCtxD hE) r = _
  cases scanRecD hmem with
  | none => rfl
  | some fd =>
      show groupRoles fd f rr (envCtxD hE) r = _
      unfold Dom at hr
      unfold groupRoles
      have h1 : r ≠ f := by intro he; subst he; rw [hf0] at hr; exact absurd hr (by decide)
      have h2 : r ≠ rr := by intro he; subst he; rw [hr0] at hr; exact absurd hr (by decide)
      have h3 : ¬ (f < r ∧ r < rr) := by
        intro ⟨a, b⟩
        rw [(hbet r a b).1] at hr; exact absurd hr (by decide)
      rw [if_neg h1, if_neg h2, if_neg h3]

/-! ### every member's references are members -/

theorem refsClosed_groupμ {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → RefsClosed E → RefsClosed E'
  | _, _, _, .nil _, hR => hR
  | E, _, _, .cons _ r m _ _ hfresh hnobody _ _ _ _ _ _ _ _ hT _ _ hrest, hR => by
      have hm : RefsOK E m :=
        ⟨fun r' hr' => hasTyT_denRefs hT r' hr', fun b hb => by rw [hnobody] at hb; cases hb⟩
      exact refsClosed_groupμ hrest (refsClosed_step hR hfresh hm)

/-- Every member's references are members (the second component of `faithful_envμ`,
without a table). -/
theorem refsClosed_of_envWfT : {E : ResolvedEnv} → EnvWfT E → RefsClosed E
  | _, .empty => fun _ _ h => (Option.noConfusion h)
  | _, .axiom E r A u hE hfresh hA _ _ =>
      refsClosed_step (refsClosed_of_envWfT hE) hfresh
        ⟨fun r' hr' => hasTyT_denRefs hA r' hr', fun b hb => by cases hb⟩
  | _, .definition E r A v u hE hfresh hA hv _ _ _ _ =>
      refsClosed_step (refsClosed_of_envWfT hE) hfresh (refsOK_singleton (k := .definitionM) (ar := 0) hA hv)
  | _, .thm E r A p hE hfresh hA hp _ _ _ _ =>
      refsClosed_step (refsClosed_of_envWfT hE) hfresh (refsOK_singleton (k := .theoremM) (ar := 0) hA hp)
  | _, .opaque E r A v u hE hfresh hA hv _ _ _ _ =>
      refsClosed_step (refsClosed_of_envWfT hE) hfresh (refsOK_singleton (k := .opaqueM) (ar := 0) hA hv)
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem => refsClosed_groupμ hmem (refsClosed_of_envWfT hE)

/-! ### reads -/

/-- The normalized family's data reads inside the base, and its fields also at
the family: the fields' references and the unfolded bodies' are the base's. -/
theorem famReads_nodeD {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hRC : RefsClosed E)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) :
    RefsIn (Dom E) ((nodeFam node).params ++ (nodeFam node).indices) ∧
      FamRefsIn (fun r => Dom E r ∨ r = (nodeFam node).fref) (nodeFam node) := by
  obtain ⟨h1, h2⟩ := famReads_node hmem hL hrr node
  refine ⟨h1, fun c hc => ?_⟩
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  have hc0 : ((node.a.constructorViews i).fields, (node.a.constructorViews i).resultIndices) ∈
      (famDataOf node.a).ctors := List.getElem?_mem (famDataOf_ctor node.a i)
  obtain ⟨hF, hR⟩ := h2 _ hc0
  refine ⟨fun A' hA' r hr => ?_, hR⟩
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA'
  -- the unfolded bodies are the base's: their references are members of the base
  have hbodies : ∀ r0 m b ls, node.E0.members r0 = some m → m.body = some b → transparent m.mclass = true →
      ∀ r', r' ∈ denRefs (instantiateLevels ls b) → Dom E r' := by
    intro r0 m b ls hm hb _ r' hr'
    rw [denRefs_instantiateLevels] at hr'
    rcases groupMembersT_cases hmem r0 m (node_sub' node r0 m hm) with hE0 | hE0
    · exact (hRC r0 m hE0).2 b hb r' hr'
    · rw [groupMembersT_body_none hmem r0 m hE0] at hb; cases hb
  rcases normField_cases node.E0 (node.h14.fuelAt i) node.a.family.ref A with he | ⟨fu, hw⟩
  · rw [he] at hr
    exact hF A hA r hr
  · rcases denRefs_whnf hbodies fu A _ hw r hr with hr' | hD
    · exact hF A hA r hr'
    · exact Or.inl hD

/-- **Every member reads inside the environment before it**, at the roles with
the normalized families. -/
theorem readsOKAlong_envCtxD : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassGD hW → ∀ ctx : Nat → Role,
    (∀ r, Dom E r → ctx r = envCtxD hW r) → ReadsOKAlong ctx hW
  | _, .empty, _, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _ => hC.elim
  | _, .definition E r A v u hE hfresh hA hv _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxD hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtxD_fresh hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .thm E r A p hE hfresh hA hp _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxD hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtxD_fresh hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hp r' h⟩
  | _, .opaque E r A v u hE hfresh hA hv _ _ _ _, hC, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxD hE hC ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtxD_fresh hE hC r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, ctx, hctx => by
      obtain ⟨hCE, _, hWC⟩ := hC
      obtain ⟨hL, hrr⟩ := group_layout_of_class hE hfam hctors hrec hmem hWC
      refine ⟨readsOKAlong_envCtxD hE hCE ctx fun r' h => (hctx r' (dom_groupMembersT hmem h)).trans
        (envCtxD_group_stable hE hfam hctors hrec hmem hL hrr r' h), ?_⟩
      obtain ⟨node, hs⟩ := group_nodeD hE hfam hctors hrec hmem
      refine groupReadsOK_of ctx hmem (fun _ h => h) fun c hc fd hcf => ?_
      have hd : Dom E' c.1 := dom_of_members (groupMembersT_installed hmem hc)
      rw [hctx c.1 hd, envCtxD_group_some hE hfam hctors hrec hmem _ hs] at hcf
      obtain ⟨hcf1, rfl⟩ := groupRoles_fam hcf (envCtxD_fresh hE hCE c.1 (groupMembersT_fresh_base hmem c.1 c.2 hc))
      exact famReads_nodeD (refsClosed_of_envWfT hE) hmem hL hrr node

end PSet

end Rcic.F3
