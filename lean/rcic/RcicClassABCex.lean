import rcic.RcicClassCCex
import rcic.RcicAccPiTable
import rcic.RcicTypedDeltaRecPins

/-!
# cc-classab — adversarial search for class (a)/(b) counterexamples to the rows: the positive half

Lane cc-classab (Klaus 2026-10-23). The report is `research/rcic/classab/CLASSAB_CEX.md`.
No counterexample to `TypedRowsWf` was found in class (a) (function-recursive fields) or class (b)
(`.drecD`, δ-reached recursive fields). `closure_claim = 0`.

* §1 (a) at the Prop Acc fixture `accPEnvWfT`: G1 (`RcicClassCCex`) instantiates with the
  Abel–Coquand ★-unfold rule `accStarRule`, and with every other bare override at the recursor.
* §2 (b) at the δ-hidden fixture `drEnvWfT`: `ConvT` has no ι at `mk` (`dr_no_derivedIota`, the
  twin of `accP_no_derivedIota`), `tableOfK` emits only the δ rule of `Id`, and G1 applies at the
  recursor.
-/

namespace Rcic.Syn.ClassAB

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Syn
open Rcic.Syn.ClassC

/-! ## §1 class (a): Acc -/

theorem accP_headsAtRecursors_star : HeadsAtRecursors accPEnvT [accStarRule] := by
  intro κ hκ
  simp only [List.mem_singleton] at hκ
  subst hκ
  exact ⟨paRecT, rfl, rfl⟩

theorem accStarRule_bareOverride : BareOverride [accStarRule] where
  bare := by
    intro ρ hρ
    simp only [List.mem_singleton] at hρ; subst hρ; rfl
  nullary := by
    intro ρ hρ ls
    simp only [List.mem_singleton] at hρ; subst hρ; rfl
  closed := by
    intro ρ hρ ls ms
    simp only [List.mem_singleton] at hρ; subst hρ
    simp [accStarRule, accStarCall, ETm.appN, ETm.ClosedAt]
  congr := by
    have h := accStarTable_wf.congr
    rw [accStarTable_eq] at h
    exact h
  nodup := by simp [accStarRule]

/-- the override table at the Acc fixture with the ★-unfold rule is #7884's `accStarTable`
    (`tableOfK accPEnvWfT = []`, so nothing is dropped). -/
theorem overrideTableK_accP_star :
    overrideTableK accPEnvWfT [accStarRule] = accStarTable := by
  simp [overrideTableK, tableOfK_accP, dropHeads, accStarTable_eq]

/-- G1 at the Acc fixture with the Abel–Coquand unfold: the erased system is confluent. -/
theorem accP_star_confluent : Confluent (EStep (overrideTableK accPEnvWfT [accStarRule])) :=
  confluent_override_tableOfK accPEnvWfT accStarRule_bareOverride accP_headsAtRecursors_star

/-- erased sort separation at Acc under the ★-unfold. -/
theorem accP_star_sortSep {l l' : Level}
    (h : ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq (.sort l) (.sort l')) :
    eqN l l' :=
  eqN_of_convE_sort_override accPEnvWfT accStarRule_bareOverride accP_headsAtRecursors_star h

/-- erased Π-injectivity at Acc under the ★-unfold. -/
theorem accP_star_piInj {A B A' B' : ETm}
    (h : ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq A A' ∧
      ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq B B' :=
  convE_pi_inv_override accPEnvWfT accStarRule_bareOverride accP_headsAtRecursors_star h

/-- erased rigidity of the `AccP` family applications under the ★-unfold. -/
theorem accP_star_famRigid {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq
      (ETm.appN (.const 10 ls) xs) (ETm.appN (.const 10 ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep (overrideTableK accPEnvWfT [accStarRule])) LvlEq) xs ys :=
  convE_appN_const_inv_override accPEnvWfT accStarRule_bareOverride accP_headsAtRecursors_star
    (f := 10) (fm := accPFamT) rfl rfl h

/-- G1 at Acc for EVERY bare override at the recursor: the Acc class is never a confluence gap. -/
theorem accP_anyOverride_confluent {ks : List CRule} (hk : BareOverride ks)
    (hrec : HeadsAtRecursors accPEnvT ks) :
    Confluent (EStep (overrideTableK accPEnvWfT ks)) :=
  confluent_override_tableOfK accPEnvWfT hk hrec

/-! ## §2 class (b): the δ-hidden recursive field -/

/-- every member of the δ-hidden env: `Id`, `F`, `mk`, `F.rec`. -/
theorem dr_mem {r : Nat} {m : CheckedMember} (h : drEnv.members r = some m) :
    (r = 0 ∧ m = drIdMember) ∨ (r = 1 ∧ m = drFamMember) ∨ (r = 2 ∧ m = drMkMember) ∨
      (r = 3 ∧ m = drRecMember) := by
  by_cases h3 : r = 3
  · subst h3; cases h; exact .inr (.inr (.inr ⟨rfl, rfl⟩))
  rw [show drEnv = extendEnv drMkEnv 3 drRecMember from rfl, members_extendEnv_ne _ _ _ h3] at h
  by_cases h2 : r = 2
  · subst h2; cases h; exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  rw [show drMkEnv = extendEnv drFamEnv 2 drMkMember from rfl, members_extendEnv_ne _ _ _ h2] at h
  by_cases h1 : r = 1
  · subst h1; cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  rw [show drFamEnv = extendEnv drBase 1 drFamMember from rfl, members_extendEnv_ne _ _ _ h1] at h
  by_cases h0 : r = 0
  · subst h0; cases h; exact .inl ⟨rfl, rfl⟩
  rw [show drBase = extendEnv emptyEnv 0 drIdMember from rfl, members_extendEnv_ne _ _ _ h0] at h
  exact Option.noConfusion h

/-- **`IotaWitness drEnv` is empty.** The family is `F` at `1`, the constructor `mk` at `2`, the field
    is `Id F`, and `analyzeFields` refuses it (`drMk_noKind`): the δ-hidden recursive occurrence has no
    kind in `main`'s ι. -/
theorem dr_no_iotaWitness (w : IotaWitness drEnv) : False := by
  have hctor := w.hctor
  have hctorK := w.hctorK
  have hfam := w.hfam
  have hfamK := w.hfamK
  rcases dr_mem hfam with ⟨-, hm⟩ | ⟨hr, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ <;>
    rw [hm] at hfamK <;> try exact absurd hfamK (by decide)
  rcases dr_mem hctor with ⟨-, hm'⟩ | ⟨-, hm'⟩ | ⟨-, hm'⟩ | ⟨-, hm'⟩ <;>
    rw [hm'] at hctorK <;> try exact absurd hctorK (by decide)
  have hnidx := w.hnidx
  have hnpar := w.hnpar
  have hpeel := w.hpeel
  have hkinds := w.hkinds
  rw [hm] at hnidx
  rw [hm'] at hnpar hpeel
  have hpi : piCount drMkMember.mtype = 1 := rfl
  have hpf : piCount drFamMember.mtype = 0 := rfl
  rw [hpi] at hnpar
  rw [hpf] at hnidx
  have hnp : w.nparams = 0 := by omega
  rw [hnp] at hpeel hnpar
  have hfl : w.fields.length = 1 := by omega
  rw [hfl] at hpeel
  have hpeel1 : peelPis (0 + 1) drMkMember.mtype = some ([drField], .const 1 []) := rfl
  rw [hpeel1] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms _
  rw [← hdoms, hnp, hr] at hkinds
  exact Option.noConfusion (drMk_noKind.symm.trans hkinds)

/-- hence `DerivedIota drEnv` is empty: no `ConvT.iota` node exists at the δ-hidden env. -/
theorem dr_no_derivedIota {lhs rhs : Expr Nat} (d : DerivedIota drEnv lhs rhs) : False := by
  cases d with
  | of w => exact dr_no_iotaWitness w

end Rcic.Syn.ClassAB
