import rcic.RcicF3StageFacts
import rcic.RcicIotaLegacyShapes
import rcic.RcicConstsClosedEnvWfT

/-!
# F3: a group's layout, from its admission

`group_layout`: in an admitted environment, a group step lists its
constructors at `f+1, f+2, …` and its recursor right after them, provided
every member admitted as a recursor has recursor class (`WalkRec`, part of
`WalkClass`). So the layout is not an assumption of the class.

The two environment invariants it uses, by induction on `EnvWfT`:
- `ctorFamPresent_of_envWfT`: a constructor's declared family is present;
- `recForFam_of_envWfT`: every family has a recursor declaring it.

A constructor of the group therefore belongs to its family: an earlier
family already has its recursor, and constructor admission refuses a family
with a recursor (`CtorBeforeRecursors`). Contiguity places it at the next
reference, and the recursor's census closes the group.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve groupMembersT_installed)

namespace PSet

theorem piResult_of_not_pi {b : Expr Nat} (hb : ∀ A B, b ≠ .pi A B) : piResult b = b := by
  cases b with
  | pi A B => exact absurd rfl (hb A B)
  | _ => rfl

theorem piResult_policyPi (b : Expr Nat) : (D : List (Expr Nat)) → piResult (policyPi D b) = piResult b
  | [] => rfl
  | _ :: D => piResult_policyPi b D

theorem piLastDom_of_not_pi {b : Expr Nat} (hb : ∀ A B, b ≠ .pi A B) : piLastDom b = none := by
  cases b with
  | pi A B => exact absurd rfl (hb A B)
  | _ => rfl

theorem piLastDom_policyPi_snoc {b : Expr Nat} (hb : ∀ A B, b ≠ .pi A B) (D : Expr Nat) :
    (L : List (Expr Nat)) → piLastDom (policyPi (L ++ [D]) b) = some D
  | [] => by
      show (match piLastDom b with | some D' => some D' | none => some D) = some D
      rw [piLastDom_of_not_pi hb]
  | A :: L => by
      show (match piLastDom (policyPi (L ++ [D]) b) with | some D' => some D' | none => some A) = some D
      rw [piLastDom_policyPi_snoc hb D L]

theorem spineHeadRef_foldApps_const (r : Nat) (ls : List Level) (as : List (Expr Nat)) :
    spineHeadRef (foldApps (.const r ls) as) = some r := by
  unfold spineHeadRef
  rw [appsSpine_foldApps]
  rfl

theorem spineHeadRef_foldApps_bvar (k : Nat) (as : List (Expr Nat)) :
    spineHeadRef (foldApps (.bvar k) as) = none := by
  unfold spineHeadRef
  rw [appsSpine_foldApps]
  rfl

/-- A constructor view's member declares the view's family. -/
theorem memberFamRef_ctorView {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (cv : PolicyConstructorView E fam m) : memberFamRef m = some fam.ref := by
  unfold memberFamRef
  rw [cv.hasClass]
  show spineHeadRef (piResult m.mtype) = _
  rw [cv.storedType, piResult_policyPi, piResult_of_not_pi (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _),
    spineHeadRef_foldApps_const]

/-- A member admitted as a recursor declares the recursor's family, if it has
recursor class, and no family if it has constructor class. -/
theorem memberFamRef_recAdm {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (hk : m.mclass = .recursorM) : memberFamRef m = some a.family.ref := by
  unfold memberFamRef
  rw [hk]
  show (match piLastDom m.mtype with | some D => spineHeadRef D | none => none) = _
  rw [recType_eq a]
  unfold recResultOf
  rw [piLastDom_policyPi_snoc (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)]
  exact spineHeadRef_foldApps_const _ _ _

theorem memberFamRef_recAdm_ctor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (hk : m.mclass = .constructorM) : memberFamRef m = none := by
  unfold memberFamRef
  rw [hk]
  show spineHeadRef (piResult m.mtype) = _
  rw [recType_eq a, piResult_policyPi]
  unfold recResultOf
  rw [piResult_of_not_pi (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)]
  exact spineHeadRef_foldApps_bvar _ _

/-- A constructor's declared family is present. -/
def CtorFamPresent (E : ResolvedEnv) : Prop :=
  ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → ∀ g, memberFamRef cm = some g →
    ∃ gm, E.members g = some gm

/-- Every family has a recursor declaring it. -/
def RecForFam (E : ResolvedEnv) : Prop :=
  ∀ g gm, E.members g = some gm → gm.mclass = .inductiveM →
    ∃ r rm, E.members r = some rm ∧ rm.mclass = .recursorM ∧ memberFamRef rm = some g

/-- The recursor node of a group step, with the scanned data. -/
def groupNode {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    {node : RecNode E E' f rr rm // scanRec hmem = some (famDataOf node.a)} := by
  refine groupRecNode (familyLayout_of_envWfT hE) hrec hmem ?_ (fun _ _ h => Or.inl h) (fun _ _ h => h) ?_
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · rcases List.mem_append.mp hc with hc | hc
      · exact Or.inr (by rw [hctors c hc]; decide)
      · rw [List.mem_singleton] at hc; subst hc; exact Or.inr (by rw [hrec]; decide)
  · intro c hc hk
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [hfam] at hk; cases hk
    · rcases List.mem_append.mp hc with hc | hc
      · rw [hctors c hc] at hk; cases hk
      · rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩

/-- Existing propositional interface for the constructive group node. -/
theorem group_node {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∃ node : RecNode E E' f rr rm, scanRec hmem = some (famDataOf node.a) := by
  let result := groupNode hE hfam hctors hrec hmem
  exact ⟨result.val, result.property⟩

theorem walk_ctorFam {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → ∀ r m, (r, m) ∈ ms → m.mclass = .constructorM → ∀ g, memberFamRef m = some g →
      ∃ gm, E'.members g = some gm
  | _, _, _, .nil _, _, _, h, _, _, _ => absurd h (List.not_mem_nil _)
  | E, _, _, .cons _ r₀ m₀ _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest, r, m, h, hk, g, hg => by
      rcases List.mem_cons.mp h with h1 | h1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
        cases hadm with
        | family _ view _ hm _ =>
            exact absurd (show m.mclass = .inductiveM from hm ▸ view.hasClass) (by rw [hk]; decide)
        | constructor famO view _ _ _ _ _ =>
            rw [memberFamRef_ctorView view] at hg
            cases hg
            exact ⟨_, groupMembersT_mono hrest _ _ (members_extend_preserved hfresh _ _ famO.present)⟩
        | recursor a _ _ _ _ _ _ =>
            rw [memberFamRef_recAdm_ctor a hk] at hg
            cases hg
      · exact walk_ctorFam hrest r m h1 hk g hg

theorem ctorFamPresent_of_envWfT : {E : ResolvedEnv} → EnvWfT E → CtorFamPresent E
  | _, .empty, _, _, h, _, _, _ => by cases h
  | _, .axiom E r' _ _ hE hfresh _ _ _, c, cm, h, hk, g, hg => by
      by_cases hr : c = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ c hr] at h
        obtain ⟨gm, hgm⟩ := ctorFamPresent_of_envWfT hE c cm h hk g hg
        exact ⟨gm, members_extend_preserved hfresh _ _ hgm⟩
  | _, .definition E r' _ _ _ hE hfresh _ _ _ _ _ _, c, cm, h, hk, g, hg => by
      by_cases hr : c = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ c hr] at h
        obtain ⟨gm, hgm⟩ := ctorFamPresent_of_envWfT hE c cm h hk g hg
        exact ⟨gm, members_extend_preserved hfresh _ _ hgm⟩
  | _, .thm E r' _ _ hE hfresh _ _ _ _ _ _, c, cm, h, hk, g, hg => by
      by_cases hr : c = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ c hr] at h
        obtain ⟨gm, hgm⟩ := ctorFamPresent_of_envWfT hE c cm h hk g hg
        exact ⟨gm, members_extend_preserved hfresh _ _ hgm⟩
  | _, .opaque E r' _ _ _ hE hfresh _ _ _ _ _ _, c, cm, h, hk, g, hg => by
      by_cases hr : c = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ c hr] at h
        obtain ⟨gm, hgm⟩ := ctorFamPresent_of_envWfT hE c cm h hk g hg
        exact ⟨gm, members_extend_preserved hfresh _ _ hgm⟩
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem, c, cm, h, hk, g, hg => by
      rcases groupMembersT_cases hmem c cm h with h1 | h1
      · obtain ⟨gm, hgm⟩ := ctorFamPresent_of_envWfT hE c cm h1 hk g hg
        exact ⟨gm, groupMembersT_preserve hmem _ _ hgm⟩
      · exact walk_ctorFam hmem c cm h1 hk g hg

theorem recForFam_of_envWfT : {E : ResolvedEnv} → EnvWfT E → RecForFam E
  | _, .empty, _, _, h, _ => by cases h
  | _, .axiom E r' _ _ hE hfresh _ _ _, g, gm, h, hk => by
      by_cases hr : g = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ g hr] at h
        obtain ⟨r, rm, h1, h2, h3⟩ := recForFam_of_envWfT hE g gm h hk
        exact ⟨r, rm, members_extend_preserved hfresh _ _ h1, h2, h3⟩
  | _, .definition E r' _ _ _ hE hfresh _ _ _ _ _ _, g, gm, h, hk => by
      by_cases hr : g = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ g hr] at h
        obtain ⟨r, rm, h1, h2, h3⟩ := recForFam_of_envWfT hE g gm h hk
        exact ⟨r, rm, members_extend_preserved hfresh _ _ h1, h2, h3⟩
  | _, .thm E r' _ _ hE hfresh _ _ _ _ _ _, g, gm, h, hk => by
      by_cases hr : g = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ g hr] at h
        obtain ⟨r, rm, h1, h2, h3⟩ := recForFam_of_envWfT hE g gm h hk
        exact ⟨r, rm, members_extend_preserved hfresh _ _ h1, h2, h3⟩
  | _, .opaque E r' _ _ _ hE hfresh _ _ _ _ _ _, g, gm, h, hk => by
      by_cases hr : g = r'
      · subst hr; rw [members_extend_eq] at h; cases h; cases hk
      · rw [members_extend_ne E r' _ g hr] at h
        obtain ⟨r, rm, h1, h2, h3⟩ := recForFam_of_envWfT hE g gm h hk
        exact ⟨r, rm, members_extend_preserved hfresh _ _ h1, h2, h3⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, g, gm, h, hk => by
      rcases groupMembersT_cases hmem g gm h with h1 | h1
      · obtain ⟨r, rm', h2, h3, h4⟩ := recForFam_of_envWfT hE g gm h1 hk
        exact ⟨r, rm', groupMembersT_preserve hmem _ _ h2, h3, h4⟩
      · have hgf : g = f := by
          rcases List.mem_cons.mp h1 with h2 | h2
          · exact (Prod.mk.inj h2).1
          · rcases List.mem_append.mp h2 with h3 | h3
            · rw [hctors _ h3] at hk; cases hk
            · rw [List.mem_singleton] at h3
              obtain ⟨_, rfl⟩ := Prod.mk.inj h3
              rw [hrec] at hk; cases hk
        subst hgf
        obtain ⟨node, _⟩ := group_node hE hfam hctors hrec hmem
        refine ⟨rr, rm, groupMembersT_installed hmem
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))), hrec, ?_⟩
        rw [memberFamRef_recAdm node.a hrec, node.fam]


/-- Every member admitted as a recursor has recursor class. -/
def WalkRec {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      (match hadm with
        | .recursor _ _ _ _ _ _ _ => m.mclass = .recursorM
        | _ => True) ∧ WalkRec hrest

theorem walkRec_of_walkClass {S : ResolvedEnv} (np : Nat) : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → (hw : GroupMembersT S E ms E') → WalkClass np hw → WalkRec hw
  | _, _, _, .nil _, _ => trivial
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest, hW => by
      obtain ⟨h1, h2⟩ := hW
      refine ⟨?_, walkRec_of_walkClass np hrest h2⟩
      cases hadm with
      | recursor _ _ _ _ _ _ _ => exact h1
      | family _ _ _ _ _ => trivial
      | constructor _ _ _ _ _ _ _ => trivial

/-- With the admission-integrity pin (`RecursorEliminationAdmitted.recursorMclass`),
`WalkRec` is derivable from the membership derivation alone: every
`.recursor`-tagged admission was constructed for a `.recursorM`-classed
member, so the per-cons check reduces to the record field. -/
theorem walkRec_of_group {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → (hw : GroupMembersT S E ms E') → WalkRec hw
  | _, _, _, .nil _ => trivial
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest => by
      refine ⟨?_, walkRec_of_group hrest⟩
      cases hadm with
      | recursor a _ _ _ _ _ _ => exact a.recursorMclass
      | family _ _ _ _ _ => trivial
      | constructor _ _ _ _ _ _ _ => trivial

/-- The constructor phase of a group's walk: the `i`-th constructor sits at
`f + 1 + i`, and the recursor right after the last. -/
theorem walk_layout {S Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (hlay : FamilyLayout Ebase)
    (hRF : RecForFam Ebase) (hrmK : rm.mclass = .recursorM) :
    (cs : List (Nat × CheckedMember)) → (i : Nat) → {Ew E' : ResolvedEnv} →
    (hw : GroupMembersT S Ew (cs ++ [(rr, rm)]) E') → WalkRec hw → (∀ c, c ∈ cs → c.2.mclass = .constructorM) →
    GroupWalkInv Ebase Ew f → (∀ r m, Ebase.members r = some m → Ew.members r = some m) →
    (∀ c, IsFamilyCtor Ew f c ↔ f < c ∧ c ≤ f + i) →
    cs.map Prod.fst = (List.range cs.length).map (fun j => f + 1 + i + j) ∧ rr = f + 1 + i + cs.length
  | [], i, Ew, _, .cons _ _ _ _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ _, _, _, hinv, hsub, hI => by
      refine ⟨rfl, ?_⟩
      cases hadm with
      | family _ view _ hm _ =>
          exact absurd (show rm.mclass = .inductiveM from hm ▸ view.hasClass) (by rw [hrmK]; decide)
      | constructor _ view _ _ _ _ _ => exact absurd view.hasClass (by rw [hrmK]; decide)
      | recursor a hfresh' h04 _ _ _ _ =>
          have hf := recursor_family_eq_group a hfresh' h04 hinv hlay hsub
          obtain ⟨h1, hcen⟩ := h04
          rw [hf] at h1 hcen
          have hlo : f + i < rr ∨ i = 0 := by
            rcases Nat.eq_zero_or_pos i with h0 | hpos
            · exact Or.inr h0
            · exact Or.inl ((hcen (f + i)).mp ((hI (f + i)).mpr ⟨by omega, Nat.le_refl _⟩)).2
          have hhi : rr ≤ f + 1 + i := by
            refine Nat.le_of_not_lt fun hlt => ?_
            have := (hI (f + 1 + i)).mp ((hcen (f + 1 + i)).mpr ⟨by omega, hlt⟩)
            omega
          simp only [List.length_nil, Nat.add_zero]
          omega
  | (r, m) :: cs, i, Ew, _, .cons _ _ _ _ _ hfresh hnobody _ _ _ _ _ hadm _ _ _ _ _ hrest, hWRc, hcs,
      hinv, hsub, hI => by
      obtain ⟨hR, hWR⟩ := hWRc
      have hk : m.mclass = .constructorM := hcs (r, m) (List.mem_cons_self _ _)
      cases hadm with
      | family _ view _ hm _ =>
          exact absurd (show m.mclass = .inductiveM from hm ▸ view.hasClass) (by rw [hk]; decide)
      | recursor _ _ _ _ _ _ _ =>
          have hR' : m.mclass = .recursorM := hR
          rw [hk] at hR'
          cases hR'
      | constructor famO view _ h04 hContig _ _ =>
          have hmf := memberFamRef_ctorView view
          -- the constructor's family is the group's
          have hgf : famO.ref = f := by
            rcases hinv _ _ famO.present with hb | ⟨_, hgf | hcls⟩
            · exfalso
              obtain ⟨rr', rm', h1, h2, h3⟩ := hRF _ _ hb famO.hasClass
              obtain ⟨g', hg', hno⟩ := h04
              rw [hmf] at hg'
              cases hg'
              exact hno rr' rm' (hsub _ _ h1) h2 h3
            · exact hgf
            · exact absurd famO.hasClass hcls
          -- contiguity places it at the next reference
          obtain ⟨g'', hg'', hlt, hbetween, hctors⟩ := hContig
          rw [hmf] at hg''
          cases hg''
          rw [hgf] at hlt hbetween hctors
          have hr : r = f + 1 + i := by
            have hle : r ≤ f + 1 + i := by
              refine Nat.le_of_not_lt fun hgt => ?_
              have := (hI (f + 1 + i)).mp (hbetween (f + 1 + i) (by omega) hgt)
              omega
            rcases Nat.eq_zero_or_pos i with h0 | hpos
            · omega
            · have := (hctors (f + i) ((hI (f + i)).mpr ⟨by omega, Nat.le_refl _⟩)).2
              omega
          subst hr
          have hI' : ∀ c, IsFamilyCtor (extendEnv Ew (f + 1 + i) m) f c ↔ f < c ∧ c ≤ f + (i + 1) := by
            intro c
            by_cases hc : c = f + 1 + i
            · subst hc
              refine ⟨fun _ => ⟨by omega, by omega⟩, fun _ => Exists.intro m ⟨members_extend_eq _ _ _, hk, ?_⟩⟩
              rw [hmf, hgf]
            · constructor
              · rintro ⟨cm, hcm, hcmK, hcmf⟩
                rw [members_extend_ne _ _ _ _ hc] at hcm
                have := (hI c).mp ⟨cm, hcm, hcmK, hcmf⟩
                exact ⟨by omega, by omega⟩
              · intro h
                have : f < c ∧ c ≤ f + i := ⟨h.1, by omega⟩
                obtain ⟨cm, hcm, hcmK, hcmf⟩ := (hI c).mpr this
                exact Exists.intro cm ⟨by rw [members_extend_ne _ _ _ _ hc]; exact hcm, hcmK, hcmf⟩
          obtain ⟨ih1, ih2⟩ := walk_layout hlay hRF hrmK cs (i + 1) hrest hWR
            (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
            (groupWalkInv_extend hinv hnobody (Or.inr (by rw [hk]; decide)))
            (fun r' m' h => members_extend_preserved hfresh r' m' (hsub r' m' h)) hI'
          refine ⟨?_, by rw [ih2, List.length_cons]; omega⟩
          rw [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, ih1]
          congr 1
          apply List.map_congr_left
          intro j _
          show f + 1 + (i + 1) + j = f + 1 + i + (j + 1)
          omega

/-- **A group's layout, from its admission.** -/
theorem group_layout {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') (hWR : WalkRec hmem) :
    ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i) ∧ rr = f + 1 + ctors.length := by
  cases hmem with
  | cons _ _ _ _ _ hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest =>
      have hCF := ctorFamPresent_of_envWfT hE
      have hI : ∀ c, IsFamilyCtor (extendEnv E f fm) f c ↔ f < c ∧ c ≤ f + 0 := by
        intro c
        refine ⟨fun hc0 => ?_, fun h => (by omega : False).elim⟩
        obtain ⟨cm, hcm, hcmK, hcmf⟩ := hc0
        exfalso
        by_cases hc : c = f
        · subst hc
          rw [members_extend_eq] at hcm
          cases hcm
          exact absurd hcmK (by rw [hfam]; decide)
        · rw [members_extend_ne _ _ _ _ hc] at hcm
          obtain ⟨gm, hgm⟩ := hCF c cm hcm hcmK f hcmf
          rw [hfresh] at hgm
          cases hgm
      obtain ⟨h1, h2⟩ := walk_layout (familyLayout_of_envWfT hE) (recForFam_of_envWfT hE) hrec ctors 0 hrest hWR.2
        hctors (groupWalkInv_extend (fun _ _ h => Or.inl h) hnobody (Or.inl rfl))
        (fun r m h => members_extend_preserved hfresh r m h) hI
      exact ⟨by rw [h1], by rw [h2]⟩


/-! ### field shapes, from the syntactic class of the fields -/

theorem occurs_foldApps_head (f : Nat) (ls : List Level) : (as : List (Expr Nat)) →
    occursConst f (foldApps (.const f ls) as) = true := by
  intro as
  suffices ∀ (g : Expr Nat), occursConst f g = true → occursConst f (foldApps g as) = true from
    this _ (by show decide (f = f) = true; exact decide_eq_true rfl)
  induction as with
  | nil => exact fun _ h => h
  | cons a as ih =>
      intro g hg
      exact ih (.app g a) (by show (occursConst f g || occursConst f a) = true; rw [hg]; rfl)


theorem isFamilyApp_direct {f : Nat} {lsF : List Level} {np d : Nat} {idx : List (Expr Nat)}
    (hidx : ∀ e, e ∈ idx → occursConst f e = false) :
    isFamilyApp f (foldApps (.const f lsF) (policyParameterLocals np d ++ idx)) = true := by
  unfold isFamilyApp
  rw [appsSpine_foldApps]
  simp only [appsSpine, List.nil_append]
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨trivial, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · unfold policyParameterLocals at he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    rfl
  · rw [hidx e he]; rfl

/-- **Field shapes match the fields** when every field is family-free or a
literal family application, and no transparent body mentions the family. -/
theorem shapesMatch_of_direct {E : ResolvedEnv} {f : Nat} (hFF : FamFreeBodies E f)
    (hop : ∀ ls, transparentBody E f ls = none) {lsF : List Level} {np nq fuel nu np' nq' : Nat} :
    (Fs : List (Expr Nat)) → (d depth : Nat) → RecFieldsDirect f lsF np nq Fs d → (shapes : List FieldShape) →
    fieldShapesFuel E fuel f nu np' nq' depth Fs = some shapes → ShapesMatch f shapes Fs
  | [], _, _, _, shapes, hs => by
      have e : shapes = [] := (Option.some.inj hs).symm
      subst e
      exact ⟨rfl, fun k s A h1 _ => by cases k <;> cases h1⟩
  | A :: Fs, d, depth, ⟨hA, hFs⟩, shapes, hs => by
      unfold fieldShapesFuel at hs
      cases ha : fieldAnalyze E fuel f nu np' nq' depth A with
      | permitted s idx =>
          rw [ha] at hs
          cases hr : fieldShapesFuel E fuel f nu np' nq' (depth + 1) Fs with
          | none => rw [hr] at hs; cases hs
          | some rest =>
              rw [hr] at hs
              have e : shapes = s :: rest := (Option.some.inj hs).symm
              subst e
              obtain ⟨hl, hm⟩ := shapesMatch_of_direct hFF hop Fs (d + 1) (depth + 1) hFs rest hr
              have hhead : (s = .nonrecursive ∧ occursConst f A = false) ∨
                  (s = .recursive 0 ∧ RecHead f A ∧ occursConst f A = true) := by
                rcases hA with h0 | ⟨idx', rfl, _, hidx'⟩
                · exact Or.inl ⟨fieldAnalyze_plain hFF h0 ha, h0⟩
                · exact Or.inr ⟨fieldAnalyze_directRec hop (isFamilyApp_direct hidx') ha, ⟨lsF, _, rfl⟩,
                    occurs_foldApps_head _ _ _⟩
              refine ⟨by rw [List.length_cons, List.length_cons, hl], fun k s' A' h1 h2 => ?_⟩
              cases k with
              | zero =>
                  rw [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
                  subst h1; subst h2
                  exact hhead
              | succ k =>
                  rw [List.getElem?_cons_succ] at h1 h2
                  exact hm k s' A' h1 h2
      | unresolved => rw [ha] at hs; cases hs
      | refused _ => rw [ha] at hs; cases hs

theorem groupMembersT_body_none {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → ∀ r m, (r, m) ∈ ms → m.body = none
  | _, _, _, .nil _, _, _, h => absurd h (List.not_mem_nil _)
  | _, _, _, .cons _ _ _ _ _ _ hnobody _ _ _ _ _ _ _ _ _ _ _ hrest, r, m, h => by
      rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hnobody
      · exact groupMembersT_body_none hrest r m h

/-- No transparent body in a group's recursor admission environment mentions
the group's family: they are the base environment's bodies. -/
theorem famFreeBodies_node {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hf0 : E.members f = none)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) : FamFreeBodies node.E0 f := by
  intro r ls b h
  unfold transparentBody at h
  cases hm : node.E0.members r with
  | none => rw [hm] at h; cases h
  | some m =>
      rw [hm] at h
      simp only at h
      by_cases htr : transparent m.mclass = true
      · rw [if_pos htr] at h
        cases hb : m.body with
        | none => rw [hb] at h; cases h
        | some b0 =>
            rw [hb] at h
            injection h with h
            subst h
            have hE' := node.sub r m (members_extend_preserved node.fresh r m hm)
            rcases groupMembersT_cases hmem r m hE' with h1 | h1
            · exact occursConst_false_of_constsMemberClosed hf0 (bodiesClosed_of_envWfT hE r m h1 b0 htr hb ls)
            · rw [groupMembersT_body_none hmem r m h1] at hb; cases hb
      · rw [if_neg htr] at h; cases h

/-- The level bound class W adds: at a position that a constructor's own admission view reads as a
parameter and the recursor's family view (`np` parameters) reads as a field, the own derivation types
the entry at a level below the family's result level (or the family is a `Prop`). The recursor's own
admission bounds the recursor-derivation's level at that entry (`FieldUniverseAdmitted`); this is the same
bound for the own derivation, and equals it under sort uniqueness. It is the only hypothesis class W adds. -/
def AgreeAt (np : Nat) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew) (m : CheckedMember)
    (cv : PolicyConstructorView Ew famO m) : Prop :=
  ∀ (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length), np ≤ k → k < cv.parameters.length →
    UniformProp famO.resultLevel ∨ leN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel

/-- A predicate on constructor admission views holds at every constructor of the walk. -/
def WalkAgree {S : ResolvedEnv}
    (agree : ∀ (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew) (m : CheckedMember),
      PolicyConstructorView Ew famO m → Prop) :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      (match hadm with
        | .constructor famO view _ _ _ _ _ => agree _ famO m view
        | _ => True) ∧ WalkAgree agree hrest

theorem group_layout_of_walkRec {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) :
    ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i) ∧ rr = f + 1 + ctors.length := by
  obtain ⟨node, _⟩ := group_node hE hfam hctors hrec hmem
  exact group_layout hE hfam hctors hrec hmem hWR

/-- Where the constructor views split off the recursor's parameter count, the level agreement is
vacuous: no position lies between the two cuts. -/
theorem walkAgree_of_walkClass {E0 E1 : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E0 E1 f rr rm) {S : ResolvedEnv} : {E E' : ResolvedEnv} →
    {ms : List (Nat × CheckedMember)} → (hw : GroupMembersT S E ms E') →
    WalkClass node.a.family.parameters.length hw → WalkAgree (AgreeAt node.a.family.parameters.length) hw
  | _, _, _, .nil _, _ => trivial
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest, hW => by
      obtain ⟨h1, h2⟩ := hW
      refine ⟨?_, walkAgree_of_walkClass node hrest h2⟩
      cases hadm with
      | recursor _ _ _ _ _ _ _ => trivial
      | family _ _ _ _ _ => trivial
      | constructor _ _ _ _ _ _ _ =>
          intro k hk hle hlt
          exact (by omega : False).elim

/-- The part of the class the whole-derivation induction reads: no axioms;
at every group, members admitted as recursors are of recursor class
(`WalkRec`), and where a constructor's own view reads as a parameter what
the recursor's view reads as a field, the own typing's level is below the
family's (`AgreeAt`). -/
def WalkG : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ _ _ _ _ _ => False
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => WalkG hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => WalkG hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => WalkG hE
  | _, .group E f _ _ rr rm E' hE _ _ _ hmem =>
      WalkG hE ∧ WalkRec hmem ∧ ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem

theorem walkG_of_classG : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassG hW → WalkG hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_classG hE hC
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_classG hE hC
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_classG hE hC
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hC => by
      obtain ⟨node0, _⟩ := group_node hE hfam hctors hrec hmem
      exact ⟨walkG_of_classG hE hC.1, walkRec_of_walkClass _ hmem (hC.2.2 node0),
        fun node => walkAgree_of_walkClass node hmem (hC.2.2 node)⟩

end PSet

end Rcic.F3
