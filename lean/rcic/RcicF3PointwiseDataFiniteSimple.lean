import rcic.RcicF3PointwiseDataFiniteOriginal

/-!
# Finite DATA with no family telescope is produced on the original domain

A family whose stored type is literally a sort has neither term parameters
nor indices. The stored constructor result head identifies each own
admission family with the selected family. Its telescope is therefore
empty too, so every W parameter-cut gap is vacuous. Parameter equality
for the selected constructor views follows from their parameterCount.

Together with the actual global finite candidate, this produces the full
original pointwise group invariant under BoundG, BoundDG, and the same
predecessor invariant. There is no W/D check, order condition, or semantic
callback. Other DATA shapes remain open. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteSimple
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- A syntactic constructor-view proof can be folded over the actual
member walk, preserving every own admission scope in the final group. -/
theorem walkAgree_of_views (allMembers : List (Nat × CheckedMember))
    (agree : ∀ (Ew : ResolvedEnv) (fam : PolicyFamilyView Ew) (m : CheckedMember),
      PolicyConstructorView Ew fam m → Prop)
    (Efin : ResolvedEnv)
    (hrow : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember)
      (fam : PolicyFamilyView Ew) (cv : PolicyConstructorView Ew fam m),
      (r, m) ∈ allMembers →
      (∀ s n, Ew.members s = some n → Efin.members s = some n) →
      agree Ew fam m cv)
    {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S E ms E') →
    (∀ c ∈ ms, c ∈ allMembers) →
    (∀ s n, E'.members s = some n → Efin.members s = some n) →
    WalkAgree agree hw
  | _, _, _, .nil _, _, _ => True.intro
  | _, _, _, .cons Ew r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest,
      hmem, hsub => by
      refine ⟨?_, walkAgree_of_views allMembers agree Efin hrow hrest
        (fun c hc => hmem c (List.mem_cons_of_mem _ hc)) hsub⟩
      cases hadm with
      | family _ _ _ _ _ => trivial
      | recursor _ _ _ _ _ _ _ => trivial
      | constructor fam cv _ _ _ _ _ =>
          exact hrow Ew r m fam cv (hmem (r, m) (List.mem_cons_self _ _))
            (fun s n hn => hsub s n (groupMembersT_preserve hrest s n
              (members_extend_preserved hfresh s n hn)))

theorem node_parameters_nil
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (u : Level) (hsort : fm.mtype = .sort u)
    (node : RecNode E E' f rr rm) : node.a.family.parameters = [] := by
  have hfm : node.a.family.member = fm :=
    Option.some.inj ((node_fam_member node).symm.trans
      (groupMembersT_installed hmem (List.mem_cons_self _ _)))
  have hst := node.a.family.storedType
  rw [hfm, hsort] at hst
  obtain ⟨h1, _⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  exact (List.append_eq_nil.mp h1.symm).1

/-- Even an arbitrary requested cut has no gap: each own constructor
view has an empty parameter telescope forced by the same stored sort. -/
theorem walk_agree_sort_header
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (u : Level) (hsort : fm.mtype = .sort u) (np : Nat) :
    WalkAgree (AgreeAt np) hmem := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  obtain ⟨hL, hrr⟩ :=
    group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  have hlen := node_ctors_length p.node hrr
  have hfm : p.node.a.family.member = fm :=
    Option.some.inj ((node_fam_member p.node).symm.trans
      (groupMembersT_installed hmem (List.mem_cons_self _ _)))
  refine walkAgree_of_views ((f, fm) :: ctors ++ [(rr, rm)])
    (AgreeAt np) E' ?_ hmem (fun _ hc => hc) (fun _ _ hm => hm)
  intro Ew r m fam cv hin hsub
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
          ((groupMembersT_installed hmem hin).symm.trans
            (node_ctor_member p.node ⟨i, hi'⟩))⟩
      · rw [List.mem_singleton] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        rw [hrec] at hkC
        cases hkC
  obtain ⟨i, rfl, rfl⟩ := hctor
  have hstO := cv.storedType
  have hstR := (p.node.a.constructorViews i).storedType
  have hspl := policyPi_split_eq _ _ _ _
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (hstO.symm.trans hstR)
  have href : fam.ref = p.node.a.family.ref := foldApps_const_head hspl.2
  have hfamO : fam.member = p.node.a.family.member := by
    have h := hsub fam.ref fam.member fam.present
    rw [href, p.node.fam] at h
    exact Option.some.inj (h.symm.trans (node_fam_member p.node))
  have hst := fam.storedType
  rw [hfamO, hfm, hsort] at hst
  obtain ⟨h1, _⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have hp : fam.parameters = [] := (List.append_eq_nil.mp h1.symm).1
  have hc : cv.parameters.length = 0 := by rw [cv.parameterCount, hp]; rfl
  intro k _ _ hlt
  rw [hc] at hlt
  exact False.elim (Nat.not_lt_zero k hlt)

/-- A literal original-domain DATA invariant step for every finite
sort-header family, including nonempty recursive constructor lists. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hFinite : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (u : Level) (hsort : fm.mtype = .sort u)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hp : p.node.a.family.parameters = [] := node_parameters_nil hmem u hsort p.node
  have hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters := by
    intro j
    have hc : (p.node.a.constructorViews j).parameters.length = 0 := by
      rw [(p.node.a.constructorViews j).parameterCount, hp]
      rfl
    exact (List.eq_nil_of_length_eq_zero hc).trans hp.symm
  exact PointwiseDataFiniteOriginal.group_step P K hE hfam hctors hrec hmem
    hType hFinite hpar
    (fun node => walk_agree_sort_header hE hfam hctors hrec hmem u hsort
      node.a.family.parameters.length) hBound hBoundD hPred

end Rcic.F3.PSet.PointwiseDataFiniteSimple

#print axioms Rcic.F3.PSet.PointwiseDataFiniteSimple.walk_agree_sort_header
#print axioms Rcic.F3.PSet.PointwiseDataFiniteSimple.invariant_step
