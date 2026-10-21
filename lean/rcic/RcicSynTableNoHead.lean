import rcic.RcicSynTableBuild
import rcic.RcicSynFamRigid

/-!
# piRow wall piece F — the derived table has `NoHeadRule` at admitted family heads

`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §7.3, discharging the builder half
that `RcicSynFamRigid`'s header leaves open (`built_no_family_rule`, spec
`research/rcic/sortrow/S4_IOTA_SPINE_CIRCULARITY.md` §57: each emitted rule's head is an
admitted definition; member uniqueness at the same ref plus the class difference refutes
an `.inductiveM` head).

`buildTableSyntax` emits `deltaRule r _` only at `.definition` nodes — every other
`EnvWfT` constructor forwards the accumulated table — so each rule head resolves, in the
environment the node actually built, to the `.definitionM` member that node installed
(`head_defM_build`, the class-strengthened sibling of `head_mem_build`; the same six-case
induction, with `envExt_extendEnv`/`members_extend_self`/`groupMembersT_ext` transporting
the *same* member and therefore its class). A real admitted-family lookup
`E.members f = some fm` with `fm.mclass = .inductiveM` then refutes `ρ.head = f` by
`Option.some` injectivity and `MemberClass` disjointness — `built_no_family_rule`.

Composition (`convE_appN_const_inv_build`): instantiating `convE_appN_const_inv_wf` at
`tbl := tableOf hEnv` with the landed `tableWF_build` and `built_no_family_rule` gives
the erased family rigidity row — `eqNList` on the level lists, equal arities, pointwise
`ConvMod` on the arguments — for a real admitted family, with no free `TableWF` table
hypothesis. As §7.3 notes this stops before the native `ConvT` argument comparisons;
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Every emitted rule's head resolves to the **`.definitionM`** member its node
installed — the class-refined sibling of `head_mem_build`. -/
theorem head_defM_build : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    ∀ ρ ∈ tableOf hEnv, ∃ m, E.members ρ.head = some m ∧ m.mclass = .definitionM
  | _, .empty, _, h => (List.not_mem_nil _ h).elim
  | _, .axiom E r' _ _ hE hfresh _ _ _, ρ, hρ => by
      rw [tableOf_axiom] at hρ
      rcases head_defM_build hE ρ hρ with ⟨m, hm, hmc⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc⟩
  | _, .definition E r' _ _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · exact ⟨⟨.definitionM, 0, _, some _⟩, members_extend_self _ _ _, rfl⟩
      · rcases head_defM_build hE ρ hρ' with ⟨m, hm, hmc⟩
        exact ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc⟩
  | _, .thm E r' _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_thm] at hρ
      rcases head_defM_build hE ρ hρ with ⟨m, hm, hmc⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc⟩
  | _, .opaque E r' _ _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_opaque] at hρ
      rcases head_defM_build hE ρ hρ with ⟨m, hm, hmc⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, ρ, hρ => by
      rw [tableOf_group] at hρ
      rcases head_defM_build hE ρ hρ with ⟨m, hm, hmc⟩
      exact ⟨m, groupMembersT_ext hmem _ _ hm, hmc⟩

/-- Any member whose class is not `.definitionM` has no rule at its head in the derived
table: every emitted head is a `.definitionM` member of the same environment, and a
member ref is unique. -/
theorem noHeadRule_tableOf_of_ne_defM {E : ResolvedEnv} (hEnv : EnvWfT E) {f : Nat}
    {fm : CheckedMember} (hf : E.members f = some fm) (hne : fm.mclass ≠ .definitionM) :
    NoHeadRule (tableOf hEnv) f := by
  intro ρ hρ hhead
  rcases head_defM_build hEnv ρ hρ with ⟨m, hm, hmc⟩
  rw [hhead] at hm
  exact hne ((Option.some.inj (hm.symm.trans hf)) ▸ hmc)

/-- PIECE F HEADLINE (S4 §5 `built_no_family_rule`): a real admitted family lookup —
`E.members f = some fm`, `fm.mclass = .inductiveM` — has `NoHeadRule` at `f` in the
table derived from `hEnv`. Only `.definition` nodes emit rules, and they install
`.definitionM` members; an inductive member ref can never be a rule head. -/
theorem built_no_family_rule {E : ResolvedEnv} (hEnv : EnvWfT E) {f : Nat}
    {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) : NoHeadRule (tableOf hEnv) f :=
  noHeadRule_tableOf_of_ne_defM hEnv hf fun h =>
    MemberClass.noConfusion (hclass.symm.trans h)

/-- ERASED FAMILY RIGIDITY FOR ADMITTED FAMILIES (spec §7.3): `convE_appN_const_inv_wf`
instantiated at the derived table — `TableWF` from `tableWF_build`, `NoHeadRule` from
`built_no_family_rule`. No free table hypothesis: the table is `tableOf hEnv` itself. -/
theorem convE_appN_const_inv_build {E : ResolvedEnv} (hEnv : EnvWfT E) {f : Nat}
    {fm : CheckedMember} (hf : E.members f = some fm)
    (hclass : fm.mclass = .inductiveM) {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep (tableOf hEnv)) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep (tableOf hEnv)) LvlEq) xs ys :=
  convE_appN_const_inv_wf (tableWF_build hEnv) (built_no_family_rule hEnv hf hclass) h

#print axioms head_defM_build
#print axioms noHeadRule_tableOf_of_ne_defM
#print axioms built_no_family_rule
#print axioms convE_appN_const_inv_build

end Rcic.Syn
