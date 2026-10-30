import rcic.RcicF3StepWRefusal

/-!
# Exact decidable W side condition at an admitted group

The stored recursor result head fixes the parameter/index cut: its de Bruijn
index is minorCount + indexCount + 1, while recursorRef fixes minorCount.
Together with the stored family type this fixes the parameter count at every
RecNode of the group. The family type also fixes its result level.

Consequently scanRec selects sufficient finite data to decide the ORIGINAL
GroupWChecked quantification. The Prop arm is vacuous; the Type arm is exactly
the landed finite walk test. A failed test itself supplies PendW and the
out-of-scope fact, using the existing closed-arm soundness and completeness.
No admission judgment or policy is changed. No universal pass theorem or
resolution of M0 is claimed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWGroup

open Rcic.Declarative Rcic.F3.PSet Rcic.F3.StepWMin Rcic.F3.StepWCheck
open Rcic.F3.StepWOpen Rcic.F3.StepWRefusal

/-- The stored signature exposes the recursor result motive index. -/
theorem recursorResult_head {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) :
    (appsSpine (piResult m.mtype)).1 =
      .bvar (a.minorTypes.length + a.family.indices.length + 1) := by
  rw [recType_eq a, Rcic.F3.PSet.piResult_policyPi]
  unfold recResultOf
  rw [piResult_of_not_pi (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)]
  exact appsSpine_fold_head _ _

/-- Equal recursor/family members fix the parameter cut, even across environments. -/
theorem recursorCut_unique {E₁ E₂ : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E₁ r m)
    (b : RecursorEliminationAdmitted E₂ r m)
    (hf : a.family.ref = b.family.ref)
    (hm : a.family.member = b.family.member) :
    a.family.parameters.length = b.family.parameters.length := by
  have hc : a.minorTypes.length = b.minorTypes.length := by
    have ha := a.recursorRef
    have hb := b.recursorRef
    have hma := a.minorCount
    have hmb := b.minorCount
    omega
  have hh := (recursorResult_head a).symm.trans (recursorResult_head b)
  have hq : a.family.indices.length = b.family.indices.length := by
    injection hh with he
    omega
  have hs := a.family.storedType.symm.trans
    ((congrArg CheckedMember.mtype hm).trans b.family.storedType)
  have ht := congrArg piCount hs
  simp only [Rcic.F3.PSet.piCount_policyPi, piCount, List.length_append, Nat.add_zero] at ht
  omega

/-- All RecNodes of one group use the same parameter count. -/
theorem nodeCut_unique {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (a b : RecNode E E' f rr rm) :
    a.a.family.parameters.length = b.a.family.parameters.length :=
  recursorCut_unique a.a b.a (a.fam.trans b.fam.symm)
    (Option.some.inj ((node_fam_member a).symm.trans (node_fam_member b)))

/-- All RecNodes of one group use the same family result level. -/
theorem nodeResult_unique {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (a b : RecNode E E' f rr rm) :
    a.a.family.resultLevel = b.a.family.resultLevel := by
  have hm := Option.some.inj ((node_fam_member a).symm.trans (node_fam_member b))
  have hs := a.a.family.storedType.symm.trans
    ((congrArg CheckedMember.mtype hm).trans b.a.family.storedType)
  have ht := congrArg piResult hs
  simp only [Rcic.F3.PSet.piResult_policyPi, piResult] at ht
  exact Expr.sort.inj ht

/-- Total named diagnostic; exactness below applies to the original admitted group. -/
def groupRefusal {S Ew E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hw : GroupMembersT S Ew ms E') : Option Refusal :=
  match scanRec hw with
  | none => none
  | some fd =>
    if evalTotal (fun _ => 0) fd.resLevel = 0 then none
    else refusalOf fd.params.length hw

/-- Unconditional exactness for the full per-group W condition, without extra guards. -/
theorem groupRefusal_none_iff {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    groupRefusal hmem = none ↔ GroupWChecked hE hfam hctors hrec hmem := by
  obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
  unfold groupRefusal
  rw [hs]
  change (if evalTotal (fun _ => 0) node.a.family.resultLevel = 0 then none
    else refusalOf node.a.family.parameters.length hmem) = none ↔ _
  rcases uniformProp_or_uniformType node with hp | ht
  · rw [if_pos (hp (fun _ => 0))]
    constructor
    · intro _ other _ htype _
      have hz := hp (fun _ => 0)
      have hpos := htype (fun _ => 0)
      rw [← nodeResult_unique node other] at hpos
      exact (by omega : False).elim
    · intro _; rfl
  · rw [if_neg (Nat.ne_of_gt (ht (fun _ => 0))), refusalOf_none_iff]
    constructor
    · intro hc other _ _ _
      rw [← nodeCut_unique node other]
      exact hc
    · intro hg
      by_cases hc : WalkAgree (AgreeAtDec node.a.family.parameters.length) hmem
      · exact hc
      · have complete : WalkAgree (AgreeAt node.a.family.parameters.length) hmem →
            WalkAgree (AgreeAtDec node.a.family.parameters.length) hmem :=
          walkAgreeDec_of_walkAgree_gen hE hfam hctors hrec hmem
            (walkRec_of_group hmem) node ht hmem (fun _ hh => hh) (fun _ _ hh => hh)
        have hpend : PendW hmem node := fun hclass =>
          hc (complete (walkAgree_of_walkClass node hmem hclass))
        have hout : ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope :=
          fun his => hc (complete (Rcic.Syn.FamApp.StepW.stepW_of_inScope
            hE hfam hctors hrec hmem node (walkRec_of_group hmem) his))
        exact hg node hpend ht hout

/-- Executable decision of the original GroupWChecked proposition. -/
def decideGroup {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    Decidable (GroupWChecked hE hfam hctors hrec hmem) :=
  if h : groupRefusal hmem = none then
    isTrue ((groupRefusal_none_iff hE hfam hctors hrec hmem).mp h)
  else isFalse (fun hc => h ((groupRefusal_none_iff hE hfam hctors hrec hmem).mpr hc))

/-- The diagnostic has exactly success and the existing named refusal as outcomes. -/
theorem groupRefusal_cases {S Ew E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hw : GroupMembersT S Ew ms E') :
    groupRefusal hw = none ∨ groupRefusal hw = some .gapSortBound := by
  unfold groupRefusal
  cases scanRec hw with
  | none => exact Or.inl rfl
  | some fd =>
    by_cases hz : evalTotal (fun _ => 0) fd.resLevel = 0
    · simp only [if_pos hz]
      exact Or.inl trivial
    · simp only [if_neg hz]
      by_cases hc : WalkAgree (AgreeAtDec fd.params.length) hw
      · exact Or.inl ((refusalOf_none_iff _ hw).mpr hc)
      · exact Or.inr ((refusalOf_gapSortBound_iff _ hw).mpr hc)

/-- Refusal is equivalent to failure of the full original group condition. -/
theorem groupRefusal_refusal_iff {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    groupRefusal hmem = some .gapSortBound ↔ ¬ GroupWChecked hE hfam hctors hrec hmem := by
  constructor
  · intro hr hc
    have hn := (groupRefusal_none_iff hE hfam hctors hrec hmem).mpr hc
    rw [hr] at hn
    cases hn
  · intro hn
    rcases groupRefusal_cases hmem with hp | hr
    · exact (hn ((groupRefusal_none_iff hE hfam hctors hrec hmem).mp hp)).elim
    · exact hr

/-- The unresolved global no-refusal claim; distinct from deciding any given group. -/
def AllGroupChecks : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (_hE : EnvWfT E) (_hfam : fm.mclass = .inductiveM)
    (_hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (_hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    groupRefusal hmem = none

/-- Universal group acceptance is exactly the existing global checked premise. -/
theorem all_groupChecks_iff_checked : AllGroupChecks ↔ StepWChecked := by
  constructor
  · intro h _ _ _ _ _ _ _ hE hfam hctors hrec hmem
    exact (groupRefusal_none_iff hE hfam hctors hrec hmem).mp (h hE hfam hctors hrec hmem)
  · intro h _ _ _ _ _ _ _ hE hfam hctors hrec hmem
    exact (groupRefusal_none_iff hE hfam hctors hrec hmem).mpr (h hE hfam hctors hrec hmem)

/-- Global completeness is conditional on precisely the original W conjecture. -/
theorem all_groupChecks_iff_hyp : AllGroupChecks ↔ StepWHyp :=
  all_groupChecks_iff_checked.trans stepWChecked_iff_hyp

/-- Composition adapter for the apex; its global premise remains unresolved. -/
theorem stepWChecked_of_all_groupChecks (h : AllGroupChecks) : StepWChecked :=
  all_groupChecks_iff_checked.mp h

/-- An actual admitted refusal would refute global W. -/
theorem groupRefusal_refutes_hyp {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hr : groupRefusal hmem = some .gapSortBound) : ¬ StepWHyp := by
  intro h
  exact (groupRefusal_refusal_iff hE hfam hctors hrec hmem).mp hr
    (stepWChecked_of_hyp h hE hfam hctors hrec hmem)

/-- Closed evaluation on the landed admitted Eq-prefix open-arm fixture. -/
theorem eqW_group_no_refusal : groupRefusal eqWMembersT = none := by decide

open Rcic.Syn.FamApp.StepW

/-- A concrete same-term sort disagreement forced by a refused admitted group.
One level is within a uniformly Type family bound; the other is not. -/
def BadSortPair (E : ResolvedEnv) : Prop :=
  ∃ (n : Nat) (Γ : LCtx) (T : Expr Nat) (u v L : Level),
    Nonempty (CtxWfT E n Γ) ∧
    Nonempty (HasTyT E n Γ T (.sort u)) ∧
    Nonempty (HasTyT E n Γ T (.sort v)) ∧
    UniformType L ∧ leN v L ∧ ¬ leN u L ∧ ¬ eqN u v

private theorem badLt (n : Nat) :
    ∀ (P : (k : Nat) → k < n → Prop) [∀ k hk, Decidable (P k hk)],
      (¬ ∀ k hk, P k hk) → ∃ k, ∃ hk, ¬ P k hk := by
  induction n with
  | zero =>
      intro P _ hn
      exact (hn (fun k hk => (Nat.not_lt_zero k hk).elim)).elim
  | succ n ih =>
      intro P _ hn
      by_cases hm : P n (Nat.lt_succ_self n)
      · have hprev : ¬ ∀ k hk, P k (Nat.lt_succ_of_lt hk) := by
          intro hp
          apply hn
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · exact hp k hlt
          · exact hm
        obtain ⟨k, hk, hb⟩ := ih (fun k hk => P k (Nat.lt_succ_of_lt hk)) hprev
        exact ⟨k, Nat.lt_succ_of_lt hk, hb⟩
      · exact ⟨n, Nat.lt_succ_self n, hm⟩

/-- A named refusal supplies an actual unequal-sort pair in the final group
environment. This extracts a necessary obstruction; it does not construct a refusal. -/
theorem refusal_has_badSortPair {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hr : groupRefusal hmem = some .gapSortBound) : BadSortPair E' := by
  obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
  have hcheck : ¬ WalkAgree (AgreeAtDec node.a.family.parameters.length) hmem := by
    intro hc
    unfold groupRefusal at hr
    rw [hs] at hr
    change (if evalTotal (fun _ => 0) node.a.family.resultLevel = 0 then none
      else refusalOf node.a.family.parameters.length hmem) = _ at hr
    split at hr
    · cases hr
    · have hh := (refusalOf_none_iff _ hmem).mpr hc
      rw [hh] at hr
      cases hr
  have htype : UniformType node.a.family.resultLevel := by
    rcases uniformProp_or_uniformType node with hp | ht
    · unfold groupRefusal at hr
      rw [hs] at hr
      change (if evalTotal (fun _ => 0) node.a.family.resultLevel = 0 then none
        else refusalOf node.a.family.parameters.length hmem) = _ at hr
      rw [if_pos (hp (fun _ => 0))] at hr
      cases hr
    · exact ht
  have go : ∀ {S Ew E'' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
      (hw : GroupMembersT S Ew ms E''),
      (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
      (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
      (¬ WalkAgree (AgreeAtDec node.a.family.parameters.length) hw) → BadSortPair E' := by
    intro S Ew E'' ms hw
    induction hw with
    | nil _ => intro _ _ hn; exact (hn trivial).elim
    | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
        intro hms hsub hn
        have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsub r' m' (Rcic.Model.PS.groupMembersT_preserve hrest r' m' h)
        have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
        have tail := ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub
        cases hadm with
        | family _ _ _ _ _ => exact tail (fun ht => hn ⟨trivial, ht⟩)
        | recursor _ _ _ _ _ _ _ => exact tail (fun ht => hn ⟨trivial, ht⟩)
        | constructor famO cv _ _ _ _ _ =>
            by_cases ha : AgreeAtDec node.a.family.parameters.length E₀ famO m cv
            · exact tail (fun ht => hn ⟨ha, ht⟩)
            · obtain ⟨k, hk, hb⟩ := badLt (cv.parameters ++ cv.fields).length
                (fun k hk => node.a.family.parameters.length ≤ k → k < cv.parameters.length →
                  decLeN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel = true) ha
              have hge : node.a.family.parameters.length ≤ k := by
                by_cases h : node.a.family.parameters.length ≤ k
                · exact h
                · exact (hb (fun hg => (h hg).elim)).elim
              have hnot : ¬ leN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel :=
                fun h => hb (fun _ _ => decLeN_complete h)
              obtain ⟨hΓ, hdO, uR, hdR, hbd⟩ := walk_entry_double_typed hE hfam hctors hrec hmem
                (walkRec_of_group hmem) node famO cv htyped.2
                (hms (r, m) (List.mem_cons_self _ _)) hEw k hk hge
              obtain ⟨_, _, _, _, hlv, _⟩ := walk_ctor_views_syn_eq hE hfam hctors hrec hmem
                (walkRec_of_group hmem) node famO cv (hms (r, m) (List.mem_cons_self _ _)) hEw
              have htO : UniformType famO.resultLevel := hlv.symm ▸ htype
              have hbR : leN uR famO.resultLevel := by
                rcases hbd with hp | hb
                · have hz := hp (fun _ => 0)
                  have hpos := htO (fun _ => 0)
                  exact (by omega : False).elim
                · exact hb
              have hneq : ¬ eqN (cv.domainsTyped.levels ⟨k, hk⟩) uR :=
                fun heq => hnot (leN_of_eqN_leN heq hbR)
              exact ⟨famO.member.arity, policyPrefixContext (cv.parameters ++ cv.fields) k,
                (cv.parameters ++ cv.fields)[k]'hk, cv.domainsTyped.levels ⟨k, hk⟩,
                uR, famO.resultLevel, hΓ, hdO, hdR, htO, hbR, hnot, hneq⟩
  exact go hmem (fun _ h => h) (fun _ _ h => h) hcheck

end Rcic.F3.StepWGroup
