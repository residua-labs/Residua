import rcic.RcicF3EnvG
import rcic.RcicIotaLegacyFamFree

/-!
# F3 S5a-12: a group's recursor node

`group_rec_node`: walking an admitted group, the member of class
`recursorM` is admitted by a `RecursorEliminationAdmitted` whose family is
the group's own (`recursor_family_eq_group`), with its admission
environment, its typed views and its minor-premise clause, and `scanRec`
reads exactly that admission.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

-- `RecNode` (what the walk finds at the group's recursor) is defined in `RcicF3BoundDefs`.

theorem group_rec_node {Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hlay : FamilyLayout Ebase) (hrmK : rm.mclass = .recursorM) {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    (∀ c, c ∈ ms → c.1 = f ∨ c.2.mclass ≠ .inductiveM) → GroupWalkInv Ebase E f →
    (∀ r m, Ebase.members r = some m → E.members r = some m) →
    (∀ c, c ∈ ms → c.2.mclass = .recursorM → c.1 = rr ∧ c.2 = rm) → (rr, rm) ∈ ms →
    ∃ node : RecNode E E' f rr rm, scanRec hmem = some (famDataOf node.a)
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
            show (if m₀.mclass = .recursorM then some (famDataOf a) else scanRec hrest) = _
            rw [if_pos hk]
      · have hin' : (rr, rm) ∈ ‹List (Nat × CheckedMember)› := by
          rcases List.mem_cons.mp hin with h | h
          · obtain ⟨_, h2⟩ := Prod.mk.inj h
            exact absurd (h2 ▸ hrmK) hk
          · exact h
        obtain ⟨node, hn⟩ := group_rec_node hlay hrmK hrest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          (groupWalkInv_extend hinv hnobody (hl (r₀, m₀) (List.mem_cons_self _ _)))
          (fun r m h => members_extend_preserved hfresh r m (hsub r m h))
          (fun c hc hcK => huniq c (List.mem_cons_of_mem _ hc) hcK) hin'
        refine ⟨⟨node.E0, node.a, node.h14, node.fam, node.fresh, node.sub,
          fun r m h => node.base r m (members_extend_preserved hfresh r m h), node.h04, node.h07, node.h12,
          node.famTyped,
          node.ctorsTyped, node.u, node.hT⟩, ?_⟩
        cases hadm with
        | recursor a _ _ _ _ _ _ =>
            show (if m₀.mclass = .recursorM then some (famDataOf a) else scanRec hrest) = _
            rw [if_neg hk]; exact hn
        | family _ _ _ _ _ => exact hn
        | constructor _ _ _ _ _ _ _ => exact hn

end PSet

end Rcic.F3
