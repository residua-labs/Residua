import rcic.RcicF3PlanRole
import rcic.RcicF3GroupWalk
/-! The same typed group walk selects both its descriptor and its admission
plan. Earlier members keep their plans. No raw-plan equality is assumed.
These are structural installation facts; universal A production is open. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PlanRole
open Rcic.Declarative

theorem envPlan_group_stable {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (r : Nat) (hr : Dom E r) :
    envPlan (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r =
      envPlan hE r := by
  have hrr0 := groupMembersT_fresh_base hmem rr rm
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hne : r ≠ rr := by
    intro he
    subst he
    unfold Dom at hr
    rw [hrr0] at hr
    exact absurd hr (by decide)
  show (match scanPlan hmem with
    | some plan => fun q => if q = rr then plan else envPlan hE q
    | none => envPlan hE) r = _
  cases scanPlan hmem with
  | none => rfl
  | some plan => exact if_neg hne
theorem group_rec_plan_node {Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hlay : FamilyLayout Ebase) (hrmK : rm.mclass = .recursorM) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    (∀ c, c ∈ ms → c.1 = f ∨ c.2.mclass ≠ .inductiveM) → GroupWalkInv Ebase E f →
    (∀ r m, Ebase.members r = some m → E.members r = some m) →
    (∀ c, c ∈ ms → c.2.mclass = .recursorM → c.1 = rr ∧ c.2 = rm) → (rr, rm) ∈ ms →
    ∃ node : RecNode E E' f rr rm, scanRec hmem = some (famDataOf node.a) ∧ scanPlan hmem = some (admittedPlan node.a node.h14)
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
              groupMembersT_mono hrest, fun _ _ h => h, h04, h07, h12, htyped.1, htyped.2.1, u, hT⟩, ?_, ?_⟩
            · show (if m₀.mclass = .recursorM then some (famDataOf a) else scanRec hrest) = _
              rw [if_pos hk]
            · show (if m₀.mclass = .recursorM then some (admittedPlan a h14) else scanPlan hrest) = _
              rw [if_pos hk]
      · have hin' : (rr, rm) ∈ ‹List (Nat × CheckedMember)› := by
          rcases List.mem_cons.mp hin with h | h
          · obtain ⟨_, h2⟩ := Prod.mk.inj h
            exact absurd (h2 ▸ hrmK) hk
          · exact h
        obtain ⟨node, hn, hp⟩ := group_rec_plan_node hlay hrmK hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _)))
          (fun r m h => members_extend_preserved hfresh r m (hsub r m h))
          (fun c hc hcK => huniq c (List.mem_cons_of_mem _ hc) hcK) hin'
        refine ⟨⟨node.E0, node.a, node.h14, node.fam, node.fresh, node.sub,
          fun r m h => node.base r m (members_extend_preserved hfresh r m h), node.h04, node.h07, node.h12,
          node.famTyped,
          node.ctorsTyped, node.u, node.hT⟩, ?_, ?_⟩
        · cases hadm with
          | recursor a _ _ _ _ _ _ =>
              show (if m₀.mclass = .recursorM then some (famDataOf a) else scanRec hrest) = _
              rw [if_neg hk]; exact hn
          | family _ _ _ _ _ => exact hn
          | constructor _ _ _ _ _ _ _ => exact hn
        · cases hadm with
          | recursor a _ _ _ _ _ h14 =>
              show (if m₀.mclass = .recursorM then some (admittedPlan a h14) else scanPlan hrest) = _
              rw [if_neg hk]; exact hp
          | family _ _ _ _ _ => exact hp
          | constructor _ _ _ _ _ _ _ => exact hp

theorem group_node {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∃ node : RecNode E E' f rr rm, scanRec hmem = some (famDataOf node.a) ∧ scanPlan hmem = some (admittedPlan node.a node.h14) := by
  refine group_rec_plan_node (familyLayout_of_envWfT hE) hrec hmem ?_ (fun _ _ h => Or.inl h) (fun _ _ h => h) ?_
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

end Rcic.F3.PSet.PlanRole
