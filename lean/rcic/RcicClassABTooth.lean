import rcic.RcicClassABCex
import rcic.RcicIndGroupExclusions

/-!
# cc-classab — the typed positivity tooth for class (b)

`ExAlias` (`RcicIndGroupExclusions`) is the NEGATIVE twin of the δ-hidden fixture `drEnv`: a family
`U` at `0`, a transparent alias `Alias := U → Sort 1` at `10`, and a constructor `mk : Alias → U` at
`1`. After δ the field is `U → Sort 1`: `U` occurs in a domain. The legacy judgment refuses it
(`not_envWf_exAlias`). Here the TYPED judgment `EnvWfT` refuses it too, so `EnvWfT`'s admission scans
through transparent definitions (05 §§8–9) and `drEnvWfT` is not the only shape that the δ-scan
decides: the same group with a body that puts the family in a domain is refused.

`closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- a member chain whose list holds a refused member cannot be built on a sub-environment of the
    target. -/
theorem groupMembersT_bad_false {T : ResolvedEnv} {r : Nat} {bad : CheckedMember}
    (refuse : ∀ {E0 : ResolvedEnv}, E0.members r = none → IndGroupAdmitted E0 r bad →
      (∀ {k : Nat} {cm : CheckedMember}, E0.members k = some cm → T.members k = some cm) → False)
    {S E : ResolvedEnv} {l : List (Nat × CheckedMember)} {E' : ResolvedEnv}
    (h : GroupMembersT S E l E') :
    (r, bad) ∈ l →
    (∀ {k : Nat} {cm : CheckedMember}, E'.members k = some cm → T.members k = some cm) → False := by
  induction h with
  | nil E => intro hmem; cases hmem
  | cons E r0 m rest E' hfresh _ _ _ _ _ _ hadm _ u hT hTc htyped hrest ih =>
      intro hmem hsub
      rcases List.mem_cons.mp hmem with h | h
      · injection h with h1 h2
        subst h1; subst h2
        exact refuse hfresh hadm (fun {k cm} hk =>
          hsub (groupMembersT_mono hrest k cm (extendEnv_envSub hfresh k cm hk)))
      · exact ih h hsub

/-- a refused group-class member cannot sit in any `EnvWfT` environment whose members are among the
    target's. The typed twin of `envWf_bad_slot_false`. -/
theorem envWfT_bad_slot_false {T : ResolvedEnv} {r : Nat} {bad : CheckedMember}
    (hg : bad.mclass = .inductiveM ∨ bad.mclass = .constructorM ∨ bad.mclass = .recursorM)
    (refuse : ∀ {E0 : ResolvedEnv}, E0.members r = none → IndGroupAdmitted E0 r bad →
      (∀ {k : Nat} {cm : CheckedMember}, E0.members k = some cm → T.members k = some cm) → False)
    {E : ResolvedEnv} (hW : EnvWfT E) :
    E.members r = some bad →
    (∀ {k : Nat} {cm : CheckedMember}, E.members k = some cm → T.members k = some cm) → False := by
  induction hW with
  | empty => intro hm _; simp only [emptyEnv] at hm; cases hm
  | «axiom» E r0 A u hE hfresh hA hcl hlvl ih =>
      intro hm hsub
      by_cases hr : r = r0
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm; rcases hg with h | h | h <;> cases h
      · rw [members_extendEnv_ne E r0 _ hr] at hm
        exact ih hm (fun {k cm} hk => hsub (extendEnv_envSub hfresh k cm hk))
  | definition E r0 A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      intro hm hsub
      by_cases hr : r = r0
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm; rcases hg with h | h | h <;> cases h
      · rw [members_extendEnv_ne E r0 _ hr] at hm
        exact ih hm (fun {k cm} hk => hsub (extendEnv_envSub hfresh k cm hk))
  | thm E r0 A p hE hfresh hA hp hclA hclp hlvlA hlvlp ih =>
      intro hm hsub
      by_cases hr : r = r0
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm; rcases hg with h | h | h <;> cases h
      · rw [members_extendEnv_ne E r0 _ hr] at hm
        exact ih hm (fun {k cm} hk => hsub (extendEnv_envSub hfresh k cm hk))
  | «opaque» E r0 A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      intro hm hsub
      by_cases hr : r = r0
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm; rcases hg with h | h | h <;> cases h
      · rw [members_extendEnv_ne E r0 _ hr] at hm
        exact ih hm (fun {k cm} hk => hsub (extendEnv_envSub hfresh k cm hk))
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro hm hsub
      rcases groupMembersT_mem_cases hmem hm with hchain | hE0
      · exact groupMembersT_bad_false refuse hmem hchain hsub
      · exact ih hE0 (fun {k cm} hk => hsub (groupMembersT_mono hmem k cm hk))

/-- **the typed positivity tooth.** `ExAlias`'s group — the δ-hidden shape of `drEnv` with a body that
    puts the family in a domain — is refused by `EnvWfT`. -/
theorem not_envWfT_exAlias (hW : EnvWfT ExAlias.ctorPrefix) : False :=
  envWfT_bad_slot_false (T := ExAlias.ctorPrefix) (r := 1) (bad := ExAlias.ctor)
    (by unfold ExAlias.ctor; exact Or.inr (Or.inl rfl))
    (fun {_} _ h hsub => Empty.elim (not_exAlias_sub hsub h)) hW
    (by
      have hs := ExAlias.prefix_bytes
      exact congrArg (fun p : _ × _ × _ => p.2.2) hs)
    (fun hk => hk)

end Rcic.Declarative
