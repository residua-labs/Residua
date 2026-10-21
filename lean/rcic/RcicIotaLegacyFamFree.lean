import rcic.RcicRecursorCellHT

/-!
# DT-019 S2 (b) — the recursor's admission prefix mentions its family in no body

The typed field analysis (`fieldAnalyze`) unfolds transparent definitions; the
legacy analysis (`analyzeField`) is syntactic. They agree on an admitted
constructor because, in the environment the recursor was admitted in, no
transparent body can mention the group's family: every body predates the
family (the group's members carry none), and the family was fresh when those
bodies were typed.

That needs the recursor's admission to read the group's OWN family
(`a.family.ref = f`). `EnvWfT` does not state it; it follows from admission's
`CtorCensus` and a layout every admitted family has — constructors at
`g+1 … g+k`, recursor at `g+1+k` (`FamilyLayout`, by induction on `EnvWfT`):
an older family's recursor would have to sit strictly inside the new census
window, where only constructors live, or the new recursor's reference would
collide with an older constructor's.

`RecursorCellHF` is `RecursorCellHT` plus that fam-freeness of `E0`'s bodies;
`envWfT_cellHF` is `envWfT_cellHT`'s walk carrying the group's base.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) fresh constants do not occur in closed terms -/

theorem constsMemberClosed_natExpand_one {E : ResolvedEnv} :
    (t : Nat) → ConstsMemberClosed E (natExpand t) → ∃ m, E.members 1 = some m
  | 0, h => by
      cases h with
      | const _ _ m hmem _ => exact ⟨m, hmem⟩
  | t + 1, h => by
      simp only [natExpand, litSucc] at h
      cases h with
      | app _ ha => exact constsMemberClosed_natExpand_one t ha

theorem constsMemberClosed_natExpand_two {E : ResolvedEnv} (t : Nat)
    (h : ConstsMemberClosed E (natExpand (t + 1))) : ∃ m, E.members 2 = some m := by
  simp only [natExpand, litSucc] at h
  cases h with
  | app hf _ =>
      cases hf with
      | const _ _ m hmem _ => exact ⟨m, hmem⟩

/-- a constant absent from `E` occurs in no term closed in `E`. -/
theorem occursConst_false_of_constsMemberClosed {E : ResolvedEnv} {f : Nat}
    (hf : E.members f = none) :
    {e : Expr Nat} → ConstsMemberClosed E e → occursConst f e = false
  | _, .bvar _ => rfl
  | _, .sort _ => rfl
  | _, .lit t h => by
      cases t with
      | zero =>
          show decide (f = 1) = false
          rw [decide_eq_false_iff_not]
          intro h1
          subst h1
          obtain ⟨m, hm⟩ := constsMemberClosed_natExpand_one 0 h
          rw [hf] at hm
          cases hm
      | succ t =>
          show (decide (f = 1) || decide (f = 2)) = false
          rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
          constructor
          · intro h1
            subst h1
            obtain ⟨m, hm⟩ := constsMemberClosed_natExpand_one _ h
            rw [hf] at hm
            cases hm
          · intro h2
            subst h2
            obtain ⟨m, hm⟩ := constsMemberClosed_natExpand_two t h
            rw [hf] at hm
            cases hm
  | _, .const r _ _ hmem _ => by
      show decide (r = f) = false
      rw [decide_eq_false_iff_not]
      intro h
      subst h
      rw [hf] at hmem
      cases hmem
  | _, .app hf' ha => by
      show (occursConst f _ || occursConst f _) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨occursConst_false_of_constsMemberClosed hf hf',
        occursConst_false_of_constsMemberClosed hf ha⟩
  | _, .lam hA hb => by
      show (occursConst f _ || occursConst f _) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨occursConst_false_of_constsMemberClosed hf hA,
        occursConst_false_of_constsMemberClosed hf hb⟩
  | _, .pi hA hb => by
      show (occursConst f _ || occursConst f _) = false
      rw [Bool.or_eq_false_iff]
      exact ⟨occursConst_false_of_constsMemberClosed hf hA,
        occursConst_false_of_constsMemberClosed hf hb⟩
  | _, .letE hA hv hb => by
      show (occursConst f _ || occursConst f _ || occursConst f _) = false
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
      exact ⟨⟨occursConst_false_of_constsMemberClosed hf hA,
        occursConst_false_of_constsMemberClosed hf hv⟩,
        occursConst_false_of_constsMemberClosed hf hb⟩

/-! ## (2) the layout of an admitted family -/

/-- every admitted family's constructors sit at `g+1 … g+k` and its recursor at
    `g+1+k`. -/
def FamilyLayout (E : ResolvedEnv) : Prop :=
  ∀ g gm, E.members g = some gm → gm.mclass = .inductiveM →
    ∃ k, (∀ i, i < k → ∃ cm, E.members (g + 1 + i) = some cm ∧ cm.mclass = .constructorM) ∧
      ∃ rm, E.members (g + 1 + k) = some rm ∧ rm.mclass = .recursorM

theorem familyLayout_extend_nonInd {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) (hcls : m.mclass ≠ .inductiveM) (h : FamilyLayout E) :
    FamilyLayout (extendEnv E r m) := by
  intro g gm hg hind
  simp only [extendEnv] at hg
  by_cases hr : g = r
  · rw [if_pos hr] at hg
    cases hg
    exact absurd hind hcls
  · rw [if_neg hr] at hg
    obtain ⟨k, hc, rm, hrm, hrmK⟩ := h g gm hg hind
    refine ⟨k, fun i hi => ?_, rm, members_extend_preserved hfresh _ _ hrm, hrmK⟩
    obtain ⟨cm, hcm, hcmK⟩ := hc i hi
    exact ⟨cm, members_extend_preserved hfresh _ _ hcm, hcmK⟩

/-- the members of the group built so far: the base's, or body-free members that
    are the family or not inductive. -/
def GroupWalkInv (Ebase E : ResolvedEnv) (f : Nat) : Prop :=
  ∀ r m, E.members r = some m →
    Ebase.members r = some m ∨ (m.body = none ∧ (r = f ∨ m.mclass ≠ .inductiveM))

theorem groupWalkInv_extend {Ebase E : ResolvedEnv} {f r : Nat} {m : CheckedMember}
    (hinv : GroupWalkInv Ebase E f) (hnobody : m.body = none)
    (hc : r = f ∨ m.mclass ≠ .inductiveM) : GroupWalkInv Ebase (extendEnv E r m) f := by
  intro r' m' h
  simp only [extendEnv] at h
  by_cases hr' : r' = r
  · rw [if_pos hr'] at h
    cases h
    subst hr'
    exact Or.inr ⟨hnobody, hc⟩
  · rw [if_neg hr'] at h
    exact hinv r' m' h

/-- a recursor admitted on the group built over a laid-out base reads the group's own
    family: an older family's recursor cannot sit inside the census window, and the new
    recursor cannot collide with an older constructor. -/
theorem recursor_family_eq_group {Ebase E : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (a : RecursorEliminationAdmitted E rr rm) (hfresh : E.members rr = none)
    (h04 : CtorCensus E a.family.ref rr)
    (hinv : GroupWalkInv Ebase E f) (hlay : FamilyLayout Ebase)
    (hsub : ∀ r m, Ebase.members r = some m → E.members r = some m) :
    a.family.ref = f := by
  rcases hinv _ _ a.family.present with hb | ⟨_, hf | hcls⟩
  · exfalso
    obtain ⟨k, hctors, rmg, hrec, hrecK⟩ := hlay _ _ hb a.family.hasClass
    obtain ⟨h1, hcen⟩ := h04
    by_cases hlt : a.family.ref + 1 + k < rr
    · obtain ⟨cm, hcm, hcmK, _⟩ := (hcen (a.family.ref + 1 + k)).2 ⟨by omega, hlt⟩
      have hrec' := hsub _ _ hrec
      rw [hcm] at hrec'
      have heq := Option.some.inj hrec'
      rw [heq, hrecK] at hcmK
      cases hcmK
    · have hne : rr ≠ a.family.ref + 1 + k := by
        intro h
        rw [h, hsub _ _ hrec] at hfresh
        cases hfresh
      obtain ⟨cm, hcm, _⟩ := hctors (rr - a.family.ref - 1) (by omega)
      have hcm' := hsub _ _ hcm
      rw [show a.family.ref + 1 + (rr - a.family.ref - 1) = rr by omega, hfresh] at hcm'
      cases hcm'
  · exact hf
  · exact absurd a.family.hasClass hcls

theorem groupMembersT_head_fresh {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {rest : List (Nat × CheckedMember)} :
    GroupMembersT S E ((r, m) :: rest) E' → E.members r = none
  | .cons _ _ _ _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ _ => hfresh

theorem groupMembersT_mem_of_list {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → {r : Nat} → {m : CheckedMember} → (r, m) ∈ l →
    E'.members r = some m
  | _, _, _, .nil _, _, _, h => absurd h (List.not_mem_nil _)
  | _, _, _, .cons E r₀ m₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, _, _, h => by
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1
        subst h2
        exact groupMembersT_mono hrest _ _ (by simp [extendEnv])
      · exact groupMembersT_mem_of_list hrest h

theorem groupMembersT_walkInv {S Ebase : ResolvedEnv} {f : Nat} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → (∀ c ∈ l, c.1 = f ∨ c.2.mclass ≠ .inductiveM) →
    GroupWalkInv Ebase E f → GroupWalkInv Ebase E' f
  | _, _, _, .nil _, _, hinv => hinv
  | _, _, _, .cons _ r₀ m₀ _ _ _ hnobody _ _ _ _ _ _ _ _ _ _ _ hrest, hl, hinv =>
      groupMembersT_walkInv hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
        (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _)))

/-- the new family's layout, read at its recursor's admission node. -/
theorem groupMembersT_recNode {S Ebase : ResolvedEnv} {f : Nat} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → (∀ c ∈ l, c.1 = f ∨ c.2.mclass ≠ .inductiveM) →
    GroupWalkInv Ebase E f → FamilyLayout Ebase →
    (∀ r m, Ebase.members r = some m → E.members r = some m) →
    {rr : Nat} → {rm : CheckedMember} → (rr, rm) ∈ l → rm.mclass = .recursorM →
    ∃ k, (∀ i, i < k → ∃ cm, E'.members (f + 1 + i) = some cm ∧ cm.mclass = .constructorM) ∧
      E'.members (f + 1 + k) = some rm
  | _, _, _, .nil _, _, _, _, _, _, _, h, _ => absurd h (List.not_mem_nil _)
  | _, _, _, .cons E r₀ m₀ _ _ hfresh hnobody _ _ _ _ _ hadm _ _ _ _ _ hrest, hl, hinv, hlay,
      hsub, rr, rm, h, hcls => by
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1
        subst h2
        cases hadm with
        | family _ view _ hm _ =>
            exact absurd (show rm.mclass = .inductiveM from hm ▸ view.hasClass)
              (fun h => by rw [hcls] at h; cases h)
        | constructor _ view _ _ _ _ _ =>
            exact absurd view.hasClass (fun h => by rw [hcls] at h; cases h)
        | recursor a hfresh' h04 _ _ _ _ =>
            have hf := recursor_family_eq_group a hfresh' h04 hinv hlay hsub
            refine ⟨a.constructors.length, fun i hi => ?_, ?_⟩
            · have hp := a.constructorsPresent ⟨i, hi⟩
              rw [hf] at hp
              exact ⟨_, groupMembersT_mono hrest _ _ (members_extend_preserved hfresh _ _ hp),
                (a.constructorViews ⟨i, hi⟩).hasClass⟩
            · have hr := a.recursorRef
              rw [hf] at hr
              rw [← hr]
              exact groupMembersT_mono hrest _ _ (by simp [extendEnv])
      · exact groupMembersT_recNode hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _))) hlay
          (fun r m hm => members_extend_preserved hfresh r m (hsub r m hm)) h hcls

theorem familyLayout_of_envWfT : {E : ResolvedEnv} → EnvWfT E → FamilyLayout E
  | _, .empty => fun _ _ h => by simp [emptyEnv] at h
  | _, .axiom _ _ _ _ hE hfresh _ _ _ =>
      familyLayout_extend_nonInd hfresh (by simp) (familyLayout_of_envWfT hE)
  | _, .definition _ _ _ _ _ hE hfresh _ _ _ _ _ _ =>
      familyLayout_extend_nonInd hfresh (by simp) (familyLayout_of_envWfT hE)
  | _, .thm _ _ _ _ hE hfresh _ _ _ _ _ _ =>
      familyLayout_extend_nonInd hfresh (by simp) (familyLayout_of_envWfT hE)
  | _, .opaque _ _ _ _ _ hE hfresh _ _ _ _ _ _ =>
      familyLayout_extend_nonInd hfresh (by simp) (familyLayout_of_envWfT hE)
  | _, .group E f fm ctors rr rm E' hE _ hctors hrec hmem => by
      have hlay := familyLayout_of_envWfT hE
      have hl : ∀ c ∈ (f, fm) :: ctors ++ [(rr, rm)], c.1 = f ∨ c.2.mclass ≠ .inductiveM := by
        intro c hc
        rcases List.mem_cons.1 hc with hc | hc
        · subst hc; exact Or.inl rfl
        · rcases List.mem_append.1 hc with hc | hc
          · exact Or.inr (by rw [hctors c hc]; simp)
          · rcases List.mem_singleton.1 hc with rfl
            exact Or.inr (by rw [hrec]; simp)
      have hinv0 : GroupWalkInv E E f := fun r m h => Or.inl h
      have hinv := groupMembersT_walkInv hmem hl hinv0
      intro g gm hg hind
      rcases hinv g gm hg with hb | ⟨_, hgf | hcls⟩
      · obtain ⟨k, hc, rmg, hrmg, hK⟩ := hlay g gm hb hind
        refine ⟨k, fun i hi => ?_, rmg, groupMembersT_mono hmem _ _ hrmg, hK⟩
        obtain ⟨cm, hcm, hcmK⟩ := hc i hi
        exact ⟨cm, groupMembersT_mono hmem _ _ hcm, hcmK⟩
      · subst hgf
        obtain ⟨k, hc, hr⟩ := groupMembersT_recNode hmem hl hinv0 hlay (fun _ _ h => h)
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))) hrec
        exact ⟨k, hc, rm, hr, hrec⟩
      · exact absurd hind hcls

/-! ## (3) the cell with fam-free bodies -/

/-- `RecursorCellHT` plus: no transparent body of the derivation prefix `E0` mentions the
    recursor's family. -/
structure RecursorCellHF (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type where
  cell : RecursorCellHT E r m
  famFree : ∀ r' ls b, transparentBody cell.cell.E0 r' ls = some b →
    occursConst cell.cell.adm.family.ref b = false

def RecursorCellHF.lift {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hsub : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    (c : RecursorCellHF E r m) : RecursorCellHF E' r m :=
  ⟨c.cell.lift hsub, c.famFree⟩

/-- the admission node's cell with fam-freeness: the family is the group's own
    (`recursor_family_eq_group`), fresh in the base, and every transparent body of the
    prefix is a base body, closed in the base. -/
def recursorCellHF_of_admitted {Ebase E E'' : ResolvedEnv} {f r : Nat} {m : CheckedMember}
    (hcls : m.mclass = .recursorM)
    (hsub : ∀ r' m', (extendEnv E r m).members r' = some m' → E''.members r' = some m')
    (u : Level) (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (hM : MembersClosed E) (hB : BodiesClosed E)
    (hinv : GroupWalkInv Ebase E f) (hlay : FamilyLayout Ebase)
    (hbase : ∀ r' m', Ebase.members r' = some m' → E.members r' = some m')
    (hff : Ebase.members f = none) (hBb : BodiesClosed Ebase) :
    (hadm : IndGroupAdmitted E r m) → IndGroupTypedT hadm → RecursorCellHF E'' r m
  | .family _ view _ hm _, _ =>
      absurd (show m.mclass = .inductiveM from hm ▸ view.hasClass)
        (fun h => by rw [hcls] at h; cases h)
  | .constructor _ view _ _ _ _ _, _ =>
      absurd view.hasClass (fun h => by rw [hcls] at h; cases h)
  | .recursor a hfresh h04 _ _ _ h14, ht =>
      ⟨⟨⟨E, a, h14, ht.2.2, hsub, hfresh⟩, u, hT, ht.1, ht.2.1, hM, hB⟩, by
        intro r' ls b h
        show occursConst a.family.ref b = false
        rw [recursor_family_eq_group a hfresh h04 hinv hlay hbase]
        unfold transparentBody at h
        cases hm' : E.members r' with
        | none => rw [hm'] at h; cases h
        | some m' =>
            rw [hm'] at h
            simp only at h
            by_cases htr : transparent m'.mclass = true
            · rw [if_pos htr] at h
              cases hb : m'.body with
              | none => rw [hb] at h; cases h
              | some b0 =>
                  rw [hb] at h
                  injection h with h
                  subst h
                  rcases hinv r' m' hm' with hbm | ⟨hnb, _⟩
                  · exact occursConst_false_of_constsMemberClosed hff (hBb r' m' hbm b0 htr hb ls)
                  · rw [hnb] at hb; cases hb
            · rw [if_neg htr] at h; cases h⟩

def groupMembersT_cellHF {S Ebase : ResolvedEnv} {f : Nat} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → (∀ c ∈ l, c.1 = f ∨ c.2.mclass ≠ .inductiveM) →
    GroupWalkInv Ebase E f → FamilyLayout Ebase →
    (∀ r m, Ebase.members r = some m → E.members r = some m) →
    Ebase.members f = none → BodiesClosed Ebase →
    BodiesClosed E → MembersClosed E → {r : Nat} → {m : CheckedMember} →
    E'.members r = some m → E.members r = none → m.mclass = .recursorM →
    RecursorCellHF E' r m
  | _, _, _, .nil _, _, _, _, _, _, _, _, _, _, _, hm, hnone, _ => absurd (hnone ▸ hm) (by simp)
  | _, _, _, .cons E r₀ m₀ _ E' hfresh hnobody _ _ _ _ _ hadm _ u hT _ htyped hrest, hl, hinv,
      hlay, hbase, hff, hBb, hB, hM, r, m, hm, hnone, hcls => by
      by_cases hr : r = r₀
      · subst hr
        have hm0 : E'.members r = some m₀ :=
          groupMembersT_mono hrest r m₀ (by simp [extendEnv])
        have heq : m₀ = m := Option.some.inj (hm0.symm.trans hm)
        subst heq
        exact recursorCellHF_of_admitted hcls (groupMembersT_mono hrest) u hT hM hB hinv hlay
          hbase hff hBb hadm htyped
      · exact groupMembersT_cellHF hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _))) hlay
          (fun r' m' h => members_extend_preserved hfresh r' m' (hbase r' m' h)) hff hBb
          (bodiesClosed_extend_nobody hfresh hnobody hB)
          (membersClosed_extend hfresh hB hM (hasTyT_constsIn hT)) hm
          (by simp only [extendEnv, if_neg hr]; exact hnone) hcls

/-- every recursor of an `EnvWfT` environment has a fam-free cell. -/
def envWfT_cellHF : {E : ResolvedEnv} → EnvWfT E → {r : Nat} → {m : CheckedMember} →
    E.members r = some m → m.mclass = .recursorM → RecursorCellHF E r m
  | _, .empty, _, _, hm, _ => absurd hm (by simp [emptyEnv])
  | _, .axiom E r₀ _ _ hE hfresh _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHF hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .definition E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHF hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .thm E r₀ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHF hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .opaque E r₀ _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hcls => by
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hcls
      · simp only [extendEnv, if_neg hr] at hm
        exact (envWfT_cellHF hE hm hcls).lift (members_extend_preserved hfresh)
  | _, .group E f fm ctors rr rm _ hE _ hctors hrec hmem, r, m, hm, hcls => by
      cases hb : E.members r with
      | some m' =>
          have h' := groupMembersT_mono hmem r m' hb
          have heq : m' = m := Option.some.inj (h'.symm.trans hm)
          subst heq
          exact (envWfT_cellHF hE hb hcls).lift (groupMembersT_mono hmem)
      | none =>
          have hl : ∀ c ∈ (f, fm) :: ctors ++ [(rr, rm)], c.1 = f ∨ c.2.mclass ≠ .inductiveM := by
            intro c hc
            rcases List.mem_cons.1 hc with hc | hc
            · subst hc; exact Or.inl rfl
            · rcases List.mem_append.1 hc with hc | hc
              · exact Or.inr (by rw [hctors c hc]; simp)
              · rcases List.mem_singleton.1 hc with rfl
                exact Or.inr (by rw [hrec]; simp)
          exact groupMembersT_cellHF hmem hl (fun r m h => Or.inl h) (familyLayout_of_envWfT hE)
            (fun _ _ h => h) (groupMembersT_head_fresh hmem) (bodiesClosed_of_envWfT hE)
            (bodiesClosed_of_envWfT hE) (membersClosed_of_envWfT hE) hm hb hcls

end Rcic.Declarative

#print axioms Rcic.Declarative.familyLayout_of_envWfT
#print axioms Rcic.Declarative.recursor_family_eq_group
#print axioms Rcic.Declarative.envWfT_cellHF
