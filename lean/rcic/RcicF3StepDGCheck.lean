import rcic.RcicF3StepDGRec
import rcic.RcicF3DFixture
import rcic.RcicAccPiEnv

/-!
# F3 StepDG — the checked side condition (#8235 face, stage 3)

`closure_claim = 0`.

cc's item after swe-audit-m3's stage-2 REFUSE (`/tmp/refuse-8273-s2.md`):
the three premises of `stepDG_under` — `hpar`, the `Prop`/`anySort`
corner, `CtorsBelowRec` — as **checked** side conditions in the shape of
`RcicF3StepWCheck`: each decided on the finite data of the node,
refusing by name, soundness unconditional, completeness stated honestly.

## What is decided, and how exactly

* `ctorParamsEqB` decides `hpar`: the constructor views' parameter
  prefix equals the family's — syntactic `Expr`-list equality.
* `propCornerB` decides the `Prop`/`anySort` corner. `UniformProp` is
  decided **exactly** by `levelUniformZero` (an iff, not a surrogate);
  `policy = .anySort` by `DecidableEq`; the consequent by the finite
  `occursConst`/`posOf` reads. The check is the B/C detector itself:
  `propCornerB node = false ↔ PendB node ∨ PendC node`.
* `ctorsBelowRecB` decides `CtorsBelowRec` (landed in stage 2).

## The measured refusal record

* At the admitted `accP` group the node's field `paFieldDom` mentions
  the family while `UniformProp`/`anySort` hold — a real `PendC`, so
  `propCornerB` refuses pointwise on real data
  (`accP_propCorner_refuses`, refusal name `.propCorner`). The same node
  is `PendA` (`recursive 2`), so the group is out of `StepDG`'s domain
  and the guarded face asks nothing there (`accP_domain_guard_fails`) —
  exactly the node whose demand made stage 2's unguarded premise
  vacuous; the guarded premise instantiated at `accP`'s group is
  *provable* (`accP_sideG_vacuous`), the inhabitation m3 showed the
  old premise lacked.
* At the δ fixture `drEnv` — a real in-domain group — the whole check
  reduces to `K 2 ≤ K 3` (`drSide_iff`); under it the producer runs
  end-to-end (`gInv_drEnv_of_stepDG`). `drKBad` shows the check is
  independent of every landed premise (`BoundG`, `BoundDG`, and the
  landed `RecBelowCtors` all hold there while `ctorsBelowRecB`
  refuses): cc's item 1, measured — the converse is not dischargeable
  from what is landed.
* `ctorParamsEqB`'s refusal arm is exercised by no admitted fixture —
  measured: it passes at `accPNode` and at every `DrNode`. The arm is
  named in `StepDGRefusal`, not hidden.

## Honest boundary

`StepDGChecked` — the premise `stepDG_under` now takes — asks
`StepDGSide` at every node of every in-domain group. Per node the
check is exact (`stepDGSideB_iff`); the `∀ node` quantifier over
`RecNode` is not a finite check, so the group-level face is a premise,
not a decided proposition — the same shape `StepWChecked` has. A
refusal fires at an in-domain group whose node is also `PendB`/`PendC`
(the `mk : P → P` `Prop`/`anySort` shape m3 named: `recursive 0`,
`PendD`, in-domain, occurs-refuted), at an `hpar` mismatch, or at a
bound inversion. No such group is on the admitted tree; the refusal is
the named residue, not a hidden premise. `StepDG` itself remains a
premise of the tier — `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepDGCheck

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet Rcic.F3.StepDGOrder Rcic.F3.TierGroup

/-! ## §1 the finite checkers

Each checker mirrors `ctorsBelowRecB`: a `Bool` over `List.range`, an
iff pair, and a `Decidable` for the `Prop`. `allFin` factors the
`∀ i : Fin n` quantifier (this toolchain has no `List.finRange`). -/

/-- `∀ i : Fin n, P i` as a finite `Bool`. -/
def allFin (n : Nat) (P : Fin n → Bool) : Bool :=
  (List.range n).all fun i => if h : i < n then P ⟨i, h⟩ else true

theorem allFin_iff (n : Nat) (P : Fin n → Bool) :
    allFin n P = true ↔ ∀ i : Fin n, P i = true := by
  constructor
  · intro h i
    have := (List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt)
    rwa [dif_pos i.isLt] at this
  · intro h
    exact List.all_eq_true.mpr fun i hi => by
      rw [dif_pos (List.mem_range.mp hi)]; exact h ⟨i, List.mem_range.mp hi⟩

/-- The constructive search under `¬∀`: `Fin n` is finite, so a failed
row is found by peeling index `0` and recursing on the tail — no
classical choice (the seal whitelists `propext`/`Quot.sound` only). -/
theorem finSearch (n : Nat) (P : Fin n → Bool) (h : ¬ ∀ i, P i = true) :
    ∃ i : Fin n, P i = false := by
  induction n with
  | zero => exact absurd (fun i => Fin.elim0 i) h
  | succ m ih =>
    by_cases h0 : P ⟨0, by omega⟩
    · have ht : ¬ ∀ j : Fin m, P j.succ = true := fun hall =>
        h fun i => by
          rcases i with ⟨i, hi⟩
          cases i with
          | zero => exact h0
          | succ k => exact hall ⟨k, Nat.lt_of_succ_lt_succ hi⟩
      obtain ⟨j, hj⟩ := ih (fun j => P j.succ) ht
      exact ⟨j.succ, hj⟩
    · exact ⟨⟨0, by omega⟩, Bool.of_not_eq_true h0⟩

theorem allFin_false_iff (n : Nat) (P : Fin n → Bool) :
    allFin n P = false ↔ ∃ i : Fin n, P i = false := by
  constructor
  · intro h
    exact finSearch n P fun hall =>
      Bool.noConfusion (h.symm.trans ((allFin_iff n P).mpr hall))
  · rintro ⟨i, hi⟩
    rw [← Bool.not_eq_true, allFin_iff]
    intro h'
    exact Bool.noConfusion (hi ▸ h' i)

/-- `l.all p = false` exactly: a witness element. Proved by induction —
the library's `List.all_eq_false` pulls `Classical.choice`, outside the
seal's whitelist. -/
theorem listAll_false_iff {α : Type} (l : List α) (p : α → Bool) :
    l.all p = false ↔ ∃ x ∈ l, p x = false := by
  induction l with
  | nil =>
    exact ⟨fun h => Bool.noConfusion h,
      fun ⟨_, hx, _⟩ => absurd hx (List.not_mem_nil _)⟩
  | cons a t ih =>
    rw [List.all_cons]
    cases ha : p a with
    | false =>
      exact ⟨fun _ => ⟨a, List.Mem.head _, ha⟩, fun _ => rfl⟩
    | true =>
      constructor
      · intro h
        obtain ⟨x, hx, hd⟩ := ih.mp h
        exact ⟨x, List.Mem.tail _ hx, hd⟩
      · rintro ⟨x, hx, hd⟩
        cases hx
        · exact absurd hd fun hh => Bool.noConfusion (ha ▸ hh)
        · exact ih.mpr ⟨x, ‹x ∈ t›, hd⟩

theorem bnot_true (b : Bool) : (!b) = true ↔ b = false := Iff.of_eq (Bool.not_eq_true' b)

theorem bnot_false (b : Bool) : (!b) = false ↔ b = true := Iff.of_eq (Bool.not_eq_false' b)

theorem bool_not_true (b : Bool) : ¬ (b = true) ↔ b = false := Iff.of_eq (Bool.not_eq_true b)

theorem bool_not_false (b : Bool) : ¬ (b = false) ↔ b = true := Iff.of_eq (Bool.not_eq_false b)

/-- `hpar` as a finite `Bool`: every constructor view's parameter
prefix equals the family's — `Expr`-list equality, exact. -/
def ctorParamsEqB {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Bool :=
  allFin node.a.constructors.length fun i =>
    decide ((node.a.constructorViews i).parameters = node.a.family.parameters)

theorem ctorParamsEqB_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    ctorParamsEqB node = true ↔
      ∀ i : Fin node.a.constructors.length,
        (node.a.constructorViews i).parameters = node.a.family.parameters := by
  rw [ctorParamsEqB, allFin_iff]
  exact forall_congr' fun i => decide_eq_true_iff

/-- `hpar` is decidable at every node. -/
def ctorParamsEq_dec {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    Decidable (∀ i : Fin node.a.constructors.length,
      (node.a.constructorViews i).parameters = node.a.family.parameters) :=
  if h : ctorParamsEqB node then .isTrue ((ctorParamsEqB_iff node).mp h)
  else .isFalse fun hp => h ((ctorParamsEqB_iff node).mpr hp)

/-- The corner's first conjunct: every field is family-free. -/
def fieldsFreeB {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) : Bool :=
  (node.a.constructorViews i).fields.all fun T => !occursConst node.a.family.ref T

theorem fieldsFreeB_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    fieldsFreeB node i = true ↔
      ∀ T, T ∈ (node.a.constructorViews i).fields →
        occursConst node.a.family.ref T = false := by
  rw [fieldsFreeB, List.all_eq_true]
  exact forall₂_congr fun T hT => bnot_true _

theorem fieldsFreeB_false_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    fieldsFreeB node i = false ↔
      ∃ T, T ∈ (node.a.constructorViews i).fields ∧
        occursConst node.a.family.ref T = true := by
  rw [fieldsFreeB, listAll_false_iff]
  exact exists_congr fun T => and_congr_right fun _ => bnot_false _

/-- The corner's second conjunct: no result index is a field binder —
`posOf (.bvar (len-1-k))` is `none` at every field position `k`. -/
def unrevealedB {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) : Bool :=
  (List.range (node.a.constructorViews i).fields.length).all fun k =>
    decide (posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
      (node.a.constructorViews i).resultIndices = none)

theorem unrevealedB_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    unrevealedB node i = true ↔
      ∀ k, k < (node.a.constructorViews i).fields.length →
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
          (node.a.constructorViews i).resultIndices = none := by
  rw [unrevealedB, List.all_eq_true]
  simp only [List.mem_range]
  exact forall₂_congr fun k hk => decide_eq_true_iff

theorem unrevealedB_false_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    unrevealedB node i = false ↔
      ∃ k, k < (node.a.constructorViews i).fields.length ∧
        posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
          (node.a.constructorViews i).resultIndices ≠ none := by
  rw [unrevealedB, listAll_false_iff]
  simp only [List.mem_range]
  exact exists_congr fun k => and_congr_right fun _ => Iff.intro
    (fun hd hp => Bool.noConfusion (hd ▸ decide_eq_true_iff.mpr hp))
    (fun h => Bool.of_not_eq_true fun ht => h (of_decide_eq_true ht))

/-- The corner consequent at constructor `i`. -/
def cornerConsequentB {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) : Bool :=
  fieldsFreeB node i && unrevealedB node i

theorem cornerConsequentB_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    cornerConsequentB node i = true ↔
      (∀ T, T ∈ (node.a.constructorViews i).fields →
          occursConst node.a.family.ref T = false) ∧
        (∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
            (node.a.constructorViews i).resultIndices = none) := by
  rw [cornerConsequentB, Bool.and_eq_true, fieldsFreeB_iff, unrevealedB_iff]

/-- **The `Prop`/`anySort` corner, decided exactly**: vacuously true
unless the family is `UniformProp` (`levelUniformZero` — an iff, not a
surrogate) AND the policy is `.anySort`; then every constructor's fields
must be family-free and unrevealed. -/
def propCornerB {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Bool :=
  !(levelUniformZero node.a.family.resultLevel && decide (node.a.policy = .anySort)) ||
    allFin node.a.constructors.length fun i => cornerConsequentB node i

theorem propCornerB_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    propCornerB node = true ↔
      (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
        ∀ i : Fin node.a.constructors.length,
          (∀ T, T ∈ (node.a.constructorViews i).fields →
              occursConst node.a.family.ref T = false) ∧
            (∀ k, k < (node.a.constructorViews i).fields.length →
              posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
                (node.a.constructorViews i).resultIndices = none)) := by
  unfold propCornerB
  rw [Bool.or_eq_true_iff, Bool.not_eq_true', allFin_iff]
  constructor
  · rintro (hA | hall) hU hpol
    · exact absurd (Bool.and_eq_true_iff.mpr
        ⟨(levelUniformZero_iff _).mpr hU, decide_eq_true_iff.mpr hpol⟩)
        fun h => Bool.noConfusion (hA ▸ h)
    · exact fun i => (cornerConsequentB_iff node i).mp (hall i)
  · intro h
    by_cases hA : (levelUniformZero node.a.family.resultLevel &&
      decide (node.a.policy = .anySort)) = true
    · right
      intro i
      obtain ⟨hz, hpol⟩ := Bool.and_eq_true_iff.mp hA
      exact (cornerConsequentB_iff node i).mpr
        (h ((levelUniformZero_iff _).mp hz) (of_decide_eq_true hpol) i)
    · left
      exact Bool.of_not_eq_true hA

/-- **The corner check is the B/C detector itself**: it refuses exactly
the `PendB`/`PendC` shapes — a `Prop` family eliminating into any sort
whose fields reveal or mention the family. Inside `StepDG`'s domain the
refusal is therefore a `PendD`-node that is also `PendB`/`PendC`: the
`mk : P → P` shape, measured-open (no admitted fixture). -/
theorem propCornerB_false_iff {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    propCornerB node = false ↔ PendB node ∨ PendC node := by
  unfold propCornerB
  rw [Bool.or_eq_false_iff, Bool.not_eq_false', allFin_false_iff]
  constructor
  · rintro ⟨hA, i, hcc⟩
    obtain ⟨hz, hpol⟩ := Bool.and_eq_true_iff.mp hA
    have hU := (levelUniformZero_iff _).mp hz
    have hP := of_decide_eq_true hpol
    rw [cornerConsequentB, Bool.and_eq_false_iff] at hcc
    rcases hcc with hf | hu
    · obtain ⟨T, hT, hocc⟩ := (fieldsFreeB_false_iff node i).mp hf
      exact Or.inr ⟨hU, hP, i, T, hT, by rw [node.fam] at hocc; exact hocc⟩
    · exact Or.inl ⟨hU, hP, i, (unrevealedB_false_iff node i).mp hu⟩
  · rintro (⟨hU, hP, i, k, hkl, hne⟩ | ⟨hU, hP, i, T, hT, hocc⟩)
    · refine ⟨Bool.and_eq_true_iff.mpr
        ⟨(levelUniformZero_iff _).mpr hU, decide_eq_true_iff.mpr hP⟩, i, ?_⟩
      rw [cornerConsequentB, Bool.and_eq_false_iff]
      exact Or.inr ((unrevealedB_false_iff node i).mpr ⟨k, hkl, hne⟩)
    · refine ⟨Bool.and_eq_true_iff.mpr
        ⟨(levelUniformZero_iff _).mpr hU, decide_eq_true_iff.mpr hP⟩, i, ?_⟩
      rw [cornerConsequentB, Bool.and_eq_false_iff]
      exact Or.inl ((fieldsFreeB_false_iff node i).mpr
        ⟨T, hT, by rw [node.fam]; exact hocc⟩)

/-- The corner is decidable at every node. -/
def propCorner_dec {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    Decidable (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        (∀ T, T ∈ (node.a.constructorViews i).fields →
            occursConst node.a.family.ref T = false) ∧
          (∀ k, k < (node.a.constructorViews i).fields.length →
            posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
              (node.a.constructorViews i).resultIndices = none)) :=
  if h : propCornerB node then .isTrue ((propCornerB_iff node).mp h)
  else .isFalse fun hp => h ((propCornerB_iff node).mpr hp)

/-- **The whole side condition as one `Bool`.** -/
def stepDGSideB (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Bool :=
  ctorParamsEqB node && propCornerB node &&
    ctorsBelowRecB K f rr node.a.constructors.length

/-- The check is exact: `stepDGSideB` returns `true` iff `StepDGSide`
holds — soundness and completeness together, unconditional per node. -/
theorem stepDGSideB_iff (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    stepDGSideB K node = true ↔ StepDGSide K node := by
  unfold stepDGSideB
  rw [Bool.and_eq_true, Bool.and_eq_true, ctorParamsEqB_iff, propCornerB_iff]
  constructor
  · rintro ⟨⟨hpar, hcorner⟩, hcb⟩
    exact ⟨hpar, hcorner, fun i => ctorsBelowRecB_true hcb i.val i.isLt⟩
  · intro h
    obtain ⟨hpar, hcorner, hcb⟩ := h
    exact ⟨⟨hpar, hcorner⟩, ctorsBelowRecB_eq_true fun i hi => hcb ⟨i, hi⟩⟩

/-- `StepDGSide` is decidable at every node. -/
def stepDGSide_dec (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Decidable (StepDGSide K node) :=
  if h : stepDGSideB K node then .isTrue ((stepDGSideB_iff K node).mp h)
  else .isFalse fun hs => h ((stepDGSideB_iff K node).mpr hs)

/-! ## §2 the named refusal

The checker reports which of the three conditions refused — the first
failing check in order (`hpar`, corner, bounds). -/

/-- The named residues of a `false`. -/
inductive StepDGRefusal : Type
  | /-- the constructor views' parameter prefix is not the family's -/
    ctorParams
  | /-- the `Prop`/`anySort` corner — the node is `PendB`/`PendC`-shaped -/
    propCorner
  | /-- a constructor's bound above the recursor's -/
    ctorsBelow
  deriving DecidableEq, Repr

/-- The first failing check, or `none` when the side condition holds. -/
def stepDGRefusalOf (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Option StepDGRefusal :=
  if ctorParamsEqB node = false then some .ctorParams
  else if propCornerB node = false then some .propCorner
  else if ctorsBelowRecB K f rr node.a.constructors.length = false then some .ctorsBelow
  else none

theorem stepDGRefusalOf_none_iff (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm) :
    stepDGRefusalOf K node = none ↔ StepDGSide K node := by
  rw [← stepDGSideB_iff]
  unfold stepDGRefusalOf stepDGSideB
  split <;> rename_i h1
  · refine ⟨fun h => Option.noConfusion h, fun hb => ?_⟩
    rw [h1] at hb; exact Bool.noConfusion hb
  · split <;> rename_i h2
    · refine ⟨fun h => Option.noConfusion h, fun hb => ?_⟩
      rw [Bool.of_not_eq_false h1, h2] at hb; exact Bool.noConfusion hb
    · split <;> rename_i h3
      · refine ⟨fun h => Option.noConfusion h, fun hb => ?_⟩
        rw [Bool.of_not_eq_false h1, Bool.of_not_eq_false h2, h3] at hb
        exact Bool.noConfusion hb
      · refine ⟨fun _ => ?_, fun _ => rfl⟩
        rw [Bool.of_not_eq_false h1, Bool.of_not_eq_false h2, Bool.of_not_eq_false h3]
        rfl

theorem stepDGRefusalOf_some_iff (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm) :
    stepDGRefusalOf K node ≠ none ↔ ¬ StepDGSide K node :=
  not_congr (stepDGRefusalOf_none_iff K node)

/-! ## §3 the checked face and the bridge -/

/-- **The checked side condition** — `stepDG_under`'s premise named:
`StepDGSide` at every node of every group inside `StepDG`'s own domain
(no `PendA`, a `PendD`). Per node the check is exact; the group's
`∀ node` is a premise, not a finite proposition. -/
def StepDGChecked (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    StepDGSideG K (E := E) (E' := E') (f := f) (rr := rr) (rm := rm) hmem

/-- **Soundness, unconditional**: wherever the checked side condition is
inhabited, `StepDG` follows — this is `stepDG_under` verbatim. -/
theorem stepDG_of_checked (P : Premises4) (K : Nat → Nat) (h : StepDGChecked K) :
    StepDG P K :=
  stepDG_under P K h

/-- **Completeness, conditional**: if `StepDGSide` holds at every node of
a group in the domain, the checker cannot refuse it there — the
per-node iff is exact, so a refusal is a real `¬ StepDGSide`, not a
surrogate's incompleteness. -/
theorem stepDGChecked_complete (K : Nat → Nat)
    (hsem : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (_hrec : rm.mclass = .recursorM)
      (_hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
      (∀ node : RecNode E E' f rr rm, ¬ PendA node) →
        (∃ node : RecNode E E' f rr rm, PendD node) →
        ∀ node : RecNode E E' f rr rm, StepDGSide K node) :
    StepDGChecked K :=
  hsem

/-- `RecBelowCtors` interplay: with the landed direction in hand
`CtorsBelowRec` collapses to bound equality — the two checks are
complementary directions, neither deriving the other. -/
theorem ctorsBelowRec_eq_of_recBelow (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hR : ∀ i : Fin node.a.constructors.length, K rr ≤ K (f + 1 + i.val)) :
    CtorsBelowRec K node ↔ ∀ i : Fin node.a.constructors.length, K (f + 1 + i.val) = K rr :=
  forall_congr' fun i =>
    ⟨fun h => Nat.le_antisymm h (hR i), fun h => Nat.le_of_eq h⟩

/-! ## §4 the `accP` tooth — the corner refuses on real admitted data -/

section AccPTooth

open Rcic.Declarative.Ann

/-- swe-audit-m3's pinned `accP` node (the stage-2 refusal probe's
construction), landed as the tooth: `PendC` (family-mentioning field at
a `UniformProp`/`anySort` group) AND `PendA` (`recursive 2`) — the
corner refuses pointwise while the domain guard asks nothing. -/
def accPNode : RecNode paRelEnvT accPEnvT 10 12 paRecT where
  E0 := accPSupEnvT
  a := accPGroupAdm
  h14 := accPIotaClause
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := fun r m h => by
    have h10 : r ≠ 10 := fun he => by
      subst he; rw [show paRelEnvT.members 10 = none from rfl] at h; cases h
    have h11 : r ≠ 11 := fun he => by
      subst he; rw [show paRelEnvT.members 11 = none from rfl] at h; cases h
    exact ((members_extend_ne accPFamEnvT 11 paIntroT r h11).trans
            (members_extend_ne paRelEnvT 10 accPFamT r h10)).trans h
  h04 := accPCensus
  h07 := fun i => match i with | ⟨0, _⟩ => accPIntroUniv
  h12 := accPMinorMatch
  famTyped := accPRecTyped.1
  ctorsTyped := accPRecTyped.2.1
  u := accPRecSortU
  hT := accPRecTyT

/-- `paFieldDom` is `Π y, R y x → AccP y`: `PendA`, `.recursive 2`. -/
theorem accP_pendA : PendA accPNode :=
  ⟨⟨0, by decide⟩, 1, 1, rfl⟩

/-- The corner's `PendC` arm: `UniformProp`/`anySort` hold and
`paFieldDom` mentions the family. -/
theorem accP_pendC : PendC accPNode :=
  ⟨fun _ => rfl, rfl, ⟨0, by decide⟩, paFieldDom, by decide, by decide⟩

/-- The corner check refuses at the admitted node — on real data, with
no dependence on `K`. -/
theorem accP_propCorner_refuses : propCornerB accPNode = false := by decide

theorem accP_propCorner_refuses_of_pendC :
    propCornerB accPNode = false :=
  (propCornerB_false_iff accPNode).mpr (Or.inr accP_pendC)

/-- `hpar` passes at `accP`: the refusal is the corner alone. -/
theorem accP_ctorParamsEq : ctorParamsEqB accPNode = true := by decide

/-- The whole check refuses, refusal name `.propCorner`. -/
theorem accP_stepDGSide_refuses (K : Nat → Nat) : stepDGSideB K accPNode = false := by
  unfold stepDGSideB
  rw [accP_ctorParamsEq, accP_propCorner_refuses]
  rfl

theorem accP_refusal_named (K : Nat → Nat) :
    stepDGRefusalOf K accPNode = some .propCorner := by
  unfold stepDGRefusalOf
  rw [accP_ctorParamsEq, accP_propCorner_refuses]
  rfl

/-- **The guard, measured**: `accP`'s group has a `PendA` node, so
`StepDG`'s domain antecedent fails there — the domain-guarded face
(`StepDGSideG`) asks nothing, which is exactly why the repaired
premise is inhabitable where stage 2's unguarded `∀` was not. -/
theorem accP_domain_guard_fails :
    ¬ (∀ node : RecNode paRelEnvT accPEnvT 10 12 paRecT, ¬ PendA node) :=
  fun h => h accPNode accP_pendA

/-- **The repair, measured at the counterexample**: the domain-guarded
premise instantiated at `accP`'s own group is *provable* — vacuously,
because its antecedent fails — where stage 2's unguarded `∀` demanded
the false triple pointwise. This is the exact inhabitation the m3
refusal showed the old premise lacked. -/
theorem accP_sideG_vacuous (K : Nat → Nat) :
    StepDGSideG K (E := paRelEnvT) (E' := accPEnvT) (f := 10) (rr := 12)
      (rm := paRecT) accPMembersT :=
  fun hA _ _ => absurd accP_pendA (hA accPNode)

end AccPTooth

/-! ## §5 the δ fixture — a real in-domain group, measured -/

/-- At `drEnv` the side condition reduces to the bound order alone:
`hpar` holds (both parameter lists are `[]`), the corner is vacuous
(`resultLevel = .succ .zero` is not `UniformProp`), and
`CtorsBelowRec` at the one constructor is `K 2 ≤ K 3`. -/
theorem drSide_iff (K : Nat → Nat) (node : DrNode) :
    StepDGSide K node ↔ K 2 ≤ K 3 := by
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  constructor
  · intro h
    exact h.2.2 ⟨0, by omega⟩
  · intro hk
    refine ⟨fun i => (dr_view node i).1.trans (dr_family node).1.symm,
      fun hU _ => ?_, fun i => ?_⟩
    · rw [(dr_family node).2.2] at hU
      exact absurd ((levelUniformZero_iff _).mpr hU) (by decide)
    · have hi : i.val = 0 := by rcases i with ⟨i, hi⟩; rw [hlen] at hi; omega
      have h2 : (1 : Nat) + 1 + i.val = 2 := by omega
      rw [h2]
      exact hk

/-- **cc item 1 measured** — `CtorsBelowRec` is independent of every
landed premise. `drKBad` puts the constructor's bound above the
recursor's; `BoundG`/`BoundDG` hold at every `K` (`drEnvWfT_classGD`)
and the landed `RecBelowCtors` holds too (`K 3 = 0 ≤ 1 = K 2`) — while
`ctorsBelowRecB` refuses. Nothing the premises supply derives
`K 2 ≤ K 3`: the check stays a checked condition, named `.ctorsBelow`. -/
def drKBad : Nat → Nat := fun r => if r = 2 then 1 else 0

theorem drKBad_boundG : BoundG drKBad drEnvWfT := (drEnvWfT_classGD.2 drKBad).1

theorem drKBad_boundDG : BoundDG drKBad drEnvWfT := (drEnvWfT_classGD.2 drKBad).2

theorem drKBad_recBelowCtors : RecBelowCtors drKBad drEnvWfT :=
  drEnvWfT_recBelowCtors drKBad (by decide)

theorem drKBad_refuses : ctorsBelowRecB drKBad 1 3 1 = false := by decide

theorem drKBad_side_fails (node : DrNode) : ¬ StepDGSide drKBad node :=
  fun h => absurd ((drSide_iff drKBad node).mp h) (by decide)

/-- **Non-vacuity, positive arm**: at the δ fixture — a real group in
`StepDG`'s domain (`drGroup_dArm` measures the guard) — the repaired
producer runs end-to-end: under `K 2 ≤ K 3` `stepDG_at` delivers the
raw-roles model invariant `GInv P K drEnvWfT`, the debt `DrRoleBridge`
records, here discharged by the order check alone. -/
theorem gInv_drEnv_of_stepDG (P : Premises4) (K : Nat → Nat) (hk : K 2 ≤ K 3) :
    GInv P K drEnvWfT :=
  stepDG_at P K (fm := drFamMember) (rm := drRecMember) (ctors := [(2, drMkMember)])
    drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl
    drMembersT (fun node => (drSide_iff K node).mpr hk)
    TierGroup.drGroup_dArm.1 TierGroup.drGroup_dArm.2
    TierGroup.drAgree (drEnvWfT_classGD.2 K).1 (drEnvWfT_classGD.2 K).2
    (TierGroup.gInv_drBase P K)

/-- The flat bound: every `K` with `K 2 ≤ K 3` runs the producer at the
fixture — the measured subdomain is inhabited, not vacuous. -/
theorem gInv_drEnv_of_stepDG_flat (P : Premises4) (K : Nat → Nat) (h : ∀ r, K r = 0) :
    GInv P K drEnvWfT :=
  gInv_drEnv_of_stepDG P K (Nat.le_of_eq (by rw [h 2, h 3]))

/-- `ctorsBelowRecB` fires on the in-domain fixture's shape — at `drEnv`
the check reduces to the single comparison `K 2 ≤ K 3`, the only arm
that bites there. -/
theorem drEnv_check_fires (K : Nat → Nat) :
    ctorsBelowRecB K 1 3 1 = decide (K 2 ≤ K 3) := by
  show (decide (K (1 + 1 + 0) ≤ K 3) && true) = decide (K 2 ≤ K 3)
  rw [Bool.and_true]

end Rcic.F3.StepDGCheck
