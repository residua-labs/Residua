import rcic.RcicPiRowRefuteAttempt
import rcic.RcicIndGroupExclusions
import rcic.RcicIATypedIota

/-!
# ds-refute — the large-motive recursor of `bEnv` is REJECTED by the elimination policy

`RcicPiRowRefuteAttempt` refutes `TypedRowsWf bEnv n` via the two-constructor Prop `bP`
and the large-motive recursor `bRecType` (`M : bP → Sort 3`), glued by `irr` on the major.
The refutation is only meaningful if the recursor could ever be admitted: `TypedRowsWf` is
supplied at an environment from an `EnvWfT` root (`RcicTypedScopeCheck.typedRowsWf_of_scopeCheck`),
and `bEnv` is built by raw `extendEnv`.

This module closes that gap in the honest direction (case (a) of the follow-up on #6503):
`bEnv` has NO `EnvWfT` inhabitant.  `bP` is a Prop with two constructors, so
`EliminationSelection.multipleProp` forces `.propOnly`; `policyMotiveLevel` is then `.zero`,
and `bRecType`'s motive `bP → Sort 3` cannot equal the canonical recursor type.  The
complementary facts:

* `bEnv_only_inductive` — the only `.inductiveM` member of `bEnv` is `bFamMember` at 0;
* `not_admitted_bRecMember_sub` / `not_admitted_bRecMember` — no `RecursorEliminationAdmitted`
  at ref 3 ever matches `bRecType` (the elimination refusal);
* `not_envWfT_bEnv` — `EnvWfT bEnv` is uninhabited, extracted through
  `envWfT_recursorCell`.

Together with `bEnv_typedRowsWf_false` this is the tooth: the *elimination restriction*
is load-bearing for the typed rows — drop it (admit the large motive) and the rows are
inconsistent (the refutation); keep it and no `EnvWfT` supplier reaches that premise.
`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## (1) member bytes of `bPrefix` / `bEnv` -/

theorem bPrefix_members (n : Nat) :
    bPrefix.members n =
      if n = 2 then some bFalseMember
      else if n = 1 then some bTrueMember
      else if n = 0 then some bFamMember
      else none := rfl

theorem bEnv_members (n : Nat) :
    bEnv.members n =
      if n = 3 then some bRecMember
      else if n = 2 then some bFalseMember
      else if n = 1 then some bTrueMember
      else if n = 0 then some bFamMember
      else none := rfl

/-- `bEnv`'s only inductive family member is `bFamMember` at ref 0 (`bRecMember` is a
    recursor; the two constructors are constructors). -/
theorem bEnv_only_inductive {n : Nat} {m : CheckedMember}
    (hm : bEnv.members n = some m) (hc : m.mclass = .inductiveM) :
    n = 0 ∧ m = bFamMember := by
  rw [bEnv_members] at hm
  by_cases h3 : n = 3
  · rw [if_pos h3] at hm
    cases hm
    simp only [bRecMember] at hc
    cases hc
  · rw [if_neg h3] at hm
    by_cases h2 : n = 2
    · rw [if_pos h2] at hm
      cases hm
      simp only [bFalseMember] at hc
      cases hc
    · rw [if_neg h2] at hm
      by_cases h1 : n = 1
      · rw [if_pos h1] at hm
        cases hm
        simp only [bTrueMember] at hc
        cases hc
      · rw [if_neg h1] at hm
        by_cases h0 : n = 0
        · rw [if_pos h0] at hm
          cases hm
          exact ⟨h0, rfl⟩
        · rw [if_neg h0] at hm
          cases hm

/-! ## (2) the elimination refusal for the recursor member -/

/-- No `RecursorEliminationAdmitted` presents `bRecMember`'s large-motive type at ref 3, on
    any prefix whose members are among `bEnv`'s.  The proof pattern is `not_exBool_sub`
    (`RcicIndGroupExclusions`) at the large motive `Sort 3`: two Prop constructors force
    `.propOnly`, whose motive is `bP → Sort 0`, not `bP → Sort 3`. -/
theorem not_admitted_bRecMember_sub {E : ResolvedEnv}
    (hsub : ∀ {k : Nat} {cm : CheckedMember},
      E.members k = some cm → bEnv.members k = some cm)
    (a : RecursorEliminationAdmitted E 3 bRecMember) : False := by
  have ⟨href, hmem⟩ := bEnv_only_inductive (hsub a.family.present) a.family.hasClass
  have hs := a.family.storedType
  rw [hmem, bFamMember] at hs
  have ⟨hcat, hbody⟩ := policyPi_eq_sort hs.symm
  have hpar : a.family.parameters = [] := (List.append_eq_nil.mp hcat).1
  have hind : a.family.indices = [] := (List.append_eq_nil.mp hcat).2
  have hres : a.family.resultLevel = .zero := by injection hbody
  have hk : a.constructors.length = 2 := by
    have hr := a.recursorRef
    rw [href] at hr
    omega
  have hprop : UniformProp a.family.resultLevel := by
    rw [hres]
    exact uniformProp_zero
  have hmany : 1 < a.constructors.length := by omega
  have hpol : a.policy = .propOnly :=
    EliminationSelection.deterministic a.selected (.multipleProp hprop hmany)
  have ht := a.recursorType
  rw [hpol] at ht
  obtain ⟨_, hshape⟩ := propOnly_opens_motive a.family a.minorTypes hpar hind
  rw [hshape] at ht
  simp only [hmem, href, bFamMember, bRecMember, bP, L3,
    policyFamilyLevels, List.range_zero, List.map_nil, foldApps] at ht
  injection ht with hdom _
  injection hdom with _ hsort
  injection hsort with hlev
  cases hlev

/-- The exact member: `bRecMember` is not elimination-admitted at the raw prefix `bPrefix`. -/
theorem not_admitted_bRecMember :
    RecursorEliminationAdmitted bPrefix 3 bRecMember → False :=
  fun a => not_admitted_bRecMember_sub
    (fun hk => members_extend_preserved (E := bPrefix) (r := 3) (m := bRecMember)
      (by rfl) _ _ hk) a

/-! ## (3) `bEnv` has no typed environment inhabitant -/

/-- **Case (a) on #6503.**  `EnvWfT bEnv` is uninhabited.  The only way a recursor member
    enters an `EnvWfT` is the atomic group step; `envWfT_recursorCell` extracts the
    admission at ref 3, and `not_admitted_bRecMember_sub` refuses it. -/
theorem not_envWfT_bEnv (hW : EnvWfT bEnv) : False := by
  have hcell := envWfT_recursorCell hW (r := 3) (m := bRecMember) rfl rfl
  exact not_admitted_bRecMember_sub
    (fun {_ _} hk => hcell.sub _ _ (members_extend_preserved hcell.fresh _ _ hk))
    hcell.adm

/-! ## (4) the tooth -/

/-- The two halves of the #6503 follow-up, sealed together: the elimination restriction is
    load-bearing.  `not_envWfT_bEnv` says the legitimate supplier
    (`RcicTypedScopeCheck.typedRowsWf_of_scopeCheck`) can never reach `TypedRowsWf bEnv n`;
    `bEnv_typedRowsWf_false` says that if the restriction were dropped and the large motive
    admitted, the typed rows would be inconsistent. -/
theorem bEnv_elimination_loadBearing {n : Nat} :
    (EnvWfT bEnv → False) ∧ (TypedRowsWf bEnv n → False) :=
  ⟨not_envWfT_bEnv, fun R => bEnv_typedRowsWf_false R⟩

#print axioms Rcic.Declarative.bEnv_only_inductive
#print axioms Rcic.Declarative.not_admitted_bRecMember
#print axioms Rcic.Declarative.not_envWfT_bEnv
#print axioms Rcic.Declarative.bEnv_elimination_loadBearing

end Rcic.Declarative
