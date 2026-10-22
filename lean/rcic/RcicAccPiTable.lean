import rcic.RcicAccPiEnv
import rcic.RcicSynTableKMeasure

/-!
# accpi (H) — the ★-major unfold rule for the Prop-valued Acc row, its table, its confluence

Hypothesis (H) of the accpi lane: for a recursive, large-eliminating, one-constructor Prop family
whose constructor fields are all proofs or bare result indices (the Acc class), add the
unconditional ★-major unfold rule to the erased table:

    rec M F x ★  ↦  F x (λ y. rec M F y)

(`★` majors are DROPPED by `TyP.eps`'s `app` clause, so the erased redex is `rec M F x`; the
constructor's proof field `g` and the guard `r : R y x` drop too, so the erased recursive
hypothesis is `λ y. rec M F y`.) In `CRule` form it is a BARE NULLARY rule at the recursor head:
`rec ↦ λ M F x. F x (λ y. rec M F y)` — the shape `tableOfK` already emits for `Loop`
(`loopKRule_rhs`) and `Eq`.

Measured here (all at `accPEnvWfT`, `RcicAccPiEnv`):

* `accP_no_iotaWitness` — the typed judgment of the rows (`ConvT`) has NO ι at the Acc group:
  `IotaWitness accPEnvT` is empty because `analyzeField` refuses the function-recursive field
  `Π y, R y x → AccP y` (`analyzeFields_accP_none`). So `ConvT.iota` never fires there and the
  Abel–Coquand unfold is not derivable in `ConvT`; the Lean kernel's Acc ι lives only in the
  frec extension (`DerivedIotaU`, `ConvA`). The question (H) answers is the extension's.
* `accP_iotaKGate_false`, `tableOfK_accP` — `tableOfK accPEnvWfT = []`: the K gate refuses the
  Acc group and `iotaRulesOf` emits nothing, so the erased `rec M F x` is stuck.
* `accStarTable_wf` — the extended table `[accStarRule]` (the Acc group's emission replaced by the
  ★-unfold rule, everything else `tableOfK`'s) is `TableWF` with NO new clause: the rule is bare
  and nullary, closed, congruent.
* `confluent_eStep_accStar` — so `EStep [accStarRule]` is confluent by the landed
  `confluent_eStep_wf` (Hindley–Rosen over Takahashi-style CR(β)/CR(const), no termination:
  `accStar_step_twice` pins that the rule refires on its own right-hand side).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## §1 `ConvT` has no ι at the Acc group -/

/-- every member of the Prop Acc env: the axiom `R`, the family, `intro`, the recursor. -/
theorem accP_mem {r : Nat} {m : CheckedMember} (h : accPEnvT.members r = some m) :
    (r = 9 ∧ m = paRelT) ∨ (r = 10 ∧ m = accPFamT) ∨ (r = 11 ∧ m = paIntroT) ∨
      (r = 12 ∧ m = paRecT) := by
  by_cases h12 : r = 12
  · subst h12; cases h; exact .inr (.inr (.inr ⟨rfl, rfl⟩))
  rw [members_extendEnv_ne _ _ _ h12] at h
  by_cases h11 : r = 11
  · subst h11; cases h; exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  rw [members_extendEnv_ne _ _ _ h11] at h
  by_cases h10 : r = 10
  · subst h10; cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  rw [members_extendEnv_ne _ _ _ h10] at h
  by_cases h9 : r = 9
  · subst h9; cases h; exact .inl ⟨rfl, rfl⟩
  rw [members_extendEnv_ne _ _ _ h9] at h
  exact Option.noConfusion h

/-- `analyzeFields` refuses `intro`'s fields at every parameter count the family allows:
    the function-recursive field `Π (y:S0), R y x → AccP y` mentions the family but is not a
    family application. -/
theorem analyzeFields_accP_none :
    analyzeFields 10 [.sort .zero, paFieldDom] = none ∧ analyzeFields 10 [paFieldDom] = none :=
  ⟨rfl, rfl⟩

/-- **`IotaWitness accPEnvT` is empty.** The witness's recursor must be `12`, its constructor
    `11`; `hpeel` reads `intro`'s domains `[S0, paFieldDom]`; `hnidx` bounds `nparams ≤ 1`;
    `hkinds` then asks `analyzeFields` to accept `paFieldDom`, which it refuses. -/
theorem accP_no_iotaWitness (w : IotaWitness accPEnvT) : False := by
  have hrec := w.hrec
  have hrecK := w.hrecK
  have hctor := w.hctor
  have hctorK := w.hctorK
  have hfam := w.hfam
  have hfamK := w.hfamK
  rcases accP_mem hfam with ⟨-, hm⟩ | ⟨hr, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ <;>
    rw [hm] at hfamK <;> try exact absurd hfamK (by decide)
  rcases accP_mem hctor with ⟨-, hm'⟩ | ⟨-, hm'⟩ | ⟨-, hm'⟩ | ⟨-, hm'⟩ <;>
    rw [hm'] at hctorK <;> try exact absurd hctorK (by decide)
  have hnidx := w.hnidx
  have hnpar := w.hnpar
  have hpeel := w.hpeel
  have hkinds := w.hkinds
  rw [hm] at hnidx
  rw [hm'] at hnpar hpeel
  have hpi : piCount paIntroT.mtype = 2 := rfl
  have hpf : piCount accPFamT.mtype = 1 := rfl
  rw [hpi] at hnpar
  rw [hpf] at hnidx
  rw [hnpar] at hpeel
  have hpeel2 : peelPis 2 paIntroT.mtype =
      some ([.sort .zero, paFieldDom], .app (.const 10 []) (.bvar 1)) := rfl
  rw [hpeel2] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms _
  rw [← hdoms, hr] at hkinds
  have hnp : w.nparams = 0 ∨ w.nparams = 1 := by omega
  rcases hnp with h0 | h1
  · rw [h0] at hkinds
    exact Option.noConfusion (analyzeFields_accP_none.1.symm.trans hkinds)
  · rw [h1] at hkinds
    exact Option.noConfusion (analyzeFields_accP_none.2.symm.trans hkinds)

/-- hence `DerivedIota accPEnvT` is empty: no `ConvT.iota` node exists at the Prop Acc env. -/
theorem accP_no_derivedIota {lhs rhs : Expr Nat} (d : DerivedIota accPEnvT lhs rhs) : False := by
  cases d with
  | of w => exact accP_no_iotaWitness w

/-! ## §2 `tableOfK` at the Prop Acc env is empty -/

/-- the K gate refuses the Acc group: its field is a Π, not a direct family application, and
    the family is indexed. -/
theorem accP_iotaKGate_false : iotaKGate 10 accPFamT paIntroT paRecT = false := by decide

/-- `iotaRuleOfCtor` refuses `intro` (the same `analyzeFields` refusal). -/
theorem accP_iotaRulesOf_nil : iotaRulesOf 10 accPFamT [(11, paIntroT)] 12 paRecT = [] :=
  rfl

theorem accP_iotaRulesKOf_nil : iotaRulesKOf 10 accPFamT [(11, paIntroT)] 12 paRecT = [] := by
  unfold iotaRulesKOf iotaKRuleOf
  simp only [accP_iotaKGate_false, Bool.false_eq_true, if_false]
  exact accP_iotaRulesOf_nil

/-- **`tableOfK accPEnvWfT = []`**: the axiom emits nothing, the group emits nothing. -/
theorem tableOfK_accP : tableOfK accPEnvWfT = [] := by
  show iotaRulesKOf 10 accPFamT [(11, paIntroT)] 12 paRecT ++ tableOfK paRelWfT = []
  rw [accP_iotaRulesKOf_nil]
  rfl

/-! ## §3 the ★-unfold rule and its table -/

/-- the erased recursive call `rec M F y` under the `λ y` (M, F, y at `3`, `2`, `0`). -/
def accStarCall (ls : List Level) : ETm :=
  ETm.appN (.const 12 ls) [.bvar 3, .bvar 2, .bvar 0]

/-- the ★-unfold rule at the Acc recursor `12`: `rec ↦ λ M F x. F x (λ y. rec M F y)`. -/
def accStarRule : CRule where
  head := 12
  nargs := fun _ => 0
  major := none
  rhs := fun ls _ =>
    .lam (.lam (.lam (.app (.app (.bvar 1) (.bvar 0)) (.lam (accStarCall ls)))))

/-- the extended table: `tableOfK accPEnvWfT` with the Acc group's (empty) emission replaced by
    the ★-unfold rule. -/
noncomputable def accStarTable : List CRule := accStarRule :: tableOfK accPEnvWfT

theorem accStarTable_eq : accStarTable = [accStarRule] := by
  rw [accStarTable, tableOfK_accP]

theorem accStarCall_congr {ls ls₂ : List Level} (h : eqNList ls ls₂) :
    LvlEq (accStarCall ls) (accStarCall ls₂) :=
  .app (.app (.app (.const 12 h) (.bvar 3)) (.bvar 2)) (.bvar 0)

/-- **(H)'s table is `TableWF`, with no new clause.** -/
theorem accStarTable_wf : TableWF accStarTable := by
  rw [accStarTable_eq]
  exact {
    congr :=
      { rhs := by
          intro ρ hρ ls ls₂ ms ms₂ hls _
          simp only [List.mem_singleton] at hρ; subst hρ
          exact .lam (.lam (.lam (.app (.app (.bvar 1) (.bvar 0))
            (.lam (accStarCall_congr hls)))))
        nargs := by
          intro ρ hρ _ _ _
          simp only [List.mem_singleton] at hρ; subst hρ; rfl
        marity := by
          intro ρ hρ _ _ hm
          simp only [List.mem_singleton] at hρ; subst hρ; cases hm }
    closed := by
      intro ρ hρ ls ms
      simp only [List.mem_singleton] at hρ; subst hρ
      simp [accStarRule, accStarCall, ETm.appN, ETm.ClosedAt]
    rigid := by
      intro ρ hρ _ _ hm
      simp only [List.mem_singleton] at hρ; subst hρ; cases hm
    bare_unique := by
      intro ρ hρ _ σ hσ _
      simp only [List.mem_singleton] at hρ hσ; subst hρ; subst hσ; rfl
    ctor_disjoint := by
      intro ρ hρ _ _ _ _ _ _ _ hm
      simp only [List.mem_singleton] at hρ; subst hρ; cases hm
    bare_nullary := by
      intro ρ hρ _ ls
      simp only [List.mem_singleton] at hρ; subst hρ; rfl }

/-- **CR of the extended erased system**, by the landed termination-free confluence. -/
theorem confluent_eStep_accStar : Confluent (EStep accStarTable) :=
  confluent_eStep_wf accStarTable_wf

/-- sort separation survives the extension. -/
theorem eqN_of_convE_sort_accStar {l l' : Level}
    (h : ConvMod (EStep accStarTable) LvlEq (.sort l) (.sort l')) : eqN l l' :=
  eqN_of_convE_sort_wf accStarTable_wf h

theorem accStarRule_mem : accStarRule ∈ accStarTable := List.Mem.head _

/-- the rule fires at the bare head, at every level list. -/
theorem accStar_step (ls : List Level) :
    EStep accStarTable (.const 12 ls) (accStarRule.rhs ls []) :=
  .inl (.cr (.bare accStarRule_mem rfl ls [] rfl))

/-- PIN (non-termination is real): the rule refires inside its own right-hand side. -/
theorem accStar_step_twice (ls : List Level) :
    RStar (EStep accStarTable) (.const 12 ls)
      (.lam (.lam (.lam (.app (.app (.bvar 1) (.bvar 0)) (.lam (ETm.appN (accStarRule.rhs ls [])
        [.bvar 3, .bvar 2, .bvar 0])))))) :=
  .step (accStar_step ls)
    (.single (.inl (.lam (.lam (.lam (.appR _ (.lam (rStep_appN_head
      (.cr (.bare accStarRule_mem rfl ls [] rfl)) _))))))))

end Rcic.Syn

#print axioms Rcic.Syn.accP_mem
#print axioms Rcic.Syn.analyzeFields_accP_none
#print axioms Rcic.Syn.accP_no_iotaWitness
#print axioms Rcic.Syn.accP_no_derivedIota
#print axioms Rcic.Syn.accP_iotaKGate_false
#print axioms Rcic.Syn.accP_iotaRulesOf_nil
#print axioms Rcic.Syn.accP_iotaRulesKOf_nil
#print axioms Rcic.Syn.tableOfK_accP
#print axioms Rcic.Syn.accStarTable_eq
#print axioms Rcic.Syn.accStarCall_congr
#print axioms Rcic.Syn.accStarTable_wf
#print axioms Rcic.Syn.confluent_eStep_accStar
#print axioms Rcic.Syn.eqN_of_convE_sort_accStar
#print axioms Rcic.Syn.accStar_step
#print axioms Rcic.Syn.accStar_step_twice
