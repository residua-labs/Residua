import rcic.RcicSynPack

/-!
# Wall B §8.3 — the source-work multiset order `WorkStep`, well-founded

`research/rcic/sortrow/BELOWC_MIXED_STEP_AND_LEDGER.md` Part II §8 ("Work
coordinate"). The pending source-work record of a query is a multiset of
**source keys** `(atoms, wt) : List Nat × Nat`, ordered by the landed `LexDM`
(`SourceR`). A `WorkStep` removes a non-empty part `X` of the record and
inserts finitely many jobs `Y`, each `SourceR`-below some removed job — each
inserted job has a concrete operation and a removed job paying it. Two uses of
one shared packet are two jobs below one removed job; no second primary
occurrence is needed (`pin_workStep_two_uses`).

The order is the Dershowitz–Manna step of `RcicSynOrder` with the base order
`Nat.lt` replaced by an arbitrary well-founded relation. The proof is the
landed one, generalised (`closure_claim` stays 0):

* `CutExpR r`: one element removed, finitely many `r`-smaller ones added.
* `accR_cons_of_acc`: Nipkow's lemma — `a :: M` is accessible whenever `M` is,
  by well-founded induction on the removed key `a` (`Acc r a`) and then by
  accessibility of the retained list `M`.
* `cutExpR_wf`: list induction.
* `split_owners`: the finite ownership assignment of a multi-element cut —
  every inserted job is owned by the head of `X` or by a member of its tail.
  It is an existence statement proved by induction on `Y`, so no decidability
  of `r` is needed (the landed `Nat` proof decided `y < x` with `splitBelow`).
* `dmStepR_wf`: the multi-element step lies in the transitive closure of
  `CutExpR r` (`dmR_of_dmStepR`, via `split_owners`), which is well-founded
  (`transG_wf`, landed).

`dmStep_iff_dmStepR` records that the landed `DMStep` is literally the
instance at `Nat.lt`. Nothing here mentions a query, a `Before`, or an answer.
-/

namespace Rcic.Syn

/-! ## §1 the generic one-element cut and Nipkow's lemma -/

section Generic

variable {α : Type} (r : α → α → Prop)

/-- One generic Dershowitz–Manna step: `M'` arises from `M` by removing one `a`
    and adding finitely many elements, each `r`-below `a`. Multisets are lists
    up to permutation. -/
def CutExpR (M' M : List α) : Prop :=
  ∃ (a : α) (rest new : List α), M.Perm (a :: rest) ∧ M'.Perm (new ++ rest) ∧ ∀ y ∈ new, r y a

/-- The generic multi-element step: `M ~ X ++ Z`, `M' ~ Y ++ Z`, `X` non-empty,
    every element of `Y` `r`-below some element of `X`. -/
def DMStepR (M' M : List α) : Prop :=
  ∃ X Y Z : List α, X ≠ [] ∧ M.Perm (X ++ Z) ∧ M'.Perm (Y ++ Z) ∧ ∀ y ∈ Y, ∃ x ∈ X, r y x

variable {r}

theorem cutExpR_perm_right {K M M₁ : List α} (hp : M.Perm M₁) (h : CutExpR r K M) :
    CutExpR r K M₁ := by
  obtain ⟨a, rest, new, h1, h2, h3⟩ := h
  exact ⟨a, rest, new, hp.symm.trans h1, h2, h3⟩

theorem cutExpR_perm_left {K K₁ M : List α} (hp : K.Perm K₁) (h : CutExpR r K M) :
    CutExpR r K₁ M := by
  obtain ⟨a, rest, new, h1, h2, h3⟩ := h
  exact ⟨a, rest, new, h1, hp.symm.trans h2, h3⟩

theorem accR_cutExp_perm {M M₁ : List α} (hp : M.Perm M₁) (h : Acc (CutExpR r) M) :
    Acc (CutExpR r) M₁ :=
  Acc.intro _ fun _ hK => h.inv (cutExpR_perm_right hp.symm hK)

/-- A member can be brought to the front (by induction on membership; no choice). -/
theorem permR_cons_of_mem {c : α} : ∀ {M : List α}, c ∈ M → ∃ rest, M.Perm (c :: rest)
  | _, .head as => ⟨as, List.Perm.refl _⟩
  | _, .tail b h =>
      let ⟨rest, hp⟩ := permR_cons_of_mem h
      ⟨b :: rest, (hp.cons b).trans (List.Perm.swap c b rest)⟩

/-- Where the removed element of `a :: M` sits: it is `a` itself, or it lies in `M`. -/
theorem permR_cons_split {a c : α} {M rest : List α} (h : (a :: M).Perm (c :: rest)) :
    (c = a ∧ M.Perm rest) ∨ ∃ rest', M.Perm (c :: rest') ∧ rest.Perm (a :: rest') := by
  have hc : c ∈ a :: M := h.symm.mem_iff.mp (List.mem_cons_self c rest)
  rcases List.mem_cons.mp hc with hca | hcM
  · subst hca
    exact Or.inl ⟨rfl, h.cons_inv⟩
  · obtain ⟨rest', hp⟩ := permR_cons_of_mem hcM
    refine Or.inr ⟨rest', hp, ?_⟩
    have h1 : (a :: M).Perm (c :: a :: rest') := (hp.cons a).trans (List.Perm.swap c a _)
    exact (h.symm.trans h1).cons_inv

/-- Prepending elements `r`-below `a` keeps accessibility, given the claim for every `b` below `a`. -/
theorem accR_append_of_rel {a : α}
    (P : ∀ b, r b a → ∀ N, Acc (CutExpR r) N → Acc (CutExpR r) (b :: N)) :
    ∀ (new : List α), (∀ y ∈ new, r y a) → ∀ M, Acc (CutExpR r) M → Acc (CutExpR r) (new ++ M)
  | [], _, _, hM => hM
  | b :: new, hlt, M, hM =>
      P b (hlt b (List.mem_cons_self b new)) _
        (accR_append_of_rel P new (fun y hy => hlt y (List.mem_cons_of_mem b hy)) M hM)

/-- **Nipkow's lemma, generic.** `a :: M` is accessible whenever `M` is: well-founded
    induction on the removed key `a`, then induction on the accessibility of the
    retained list `M`. -/
theorem accR_cons_of_acc {a : α} (ha : Acc r a) :
    ∀ (M : List α), Acc (CutExpR r) M → Acc (CutExpR r) (a :: M) := by
  induction ha with
  | intro a _ iha =>
    intro M hM
    induction hM with
    | intro M hacc ihM =>
      refine Acc.intro _ ?_
      intro K hK
      obtain ⟨c, rest, new, hp, hK', hlt⟩ := hK
      rcases permR_cons_split hp with ⟨hca, hMr⟩ | ⟨rest', hMc, hra⟩
      · subst hca
        have hA : Acc (CutExpR r) (new ++ M) :=
          accR_append_of_rel (fun b hb N hN => iha b hb N hN) new hlt M (Acc.intro M hacc)
        exact accR_cutExp_perm ((List.Perm.append_left new hMr.symm).symm.trans hK'.symm) hA
      · have hstep : CutExpR r (new ++ rest') M := ⟨c, rest', new, hMc, List.Perm.refl _, hlt⟩
        have hA : Acc (CutExpR r) (a :: (new ++ rest')) := ihM _ hstep
        have hpK : K.Perm (a :: (new ++ rest')) :=
          hK'.trans ((List.Perm.append_left new hra).trans List.perm_middle)
        exact accR_cutExp_perm hpK.symm hA

/-- The generic one-element cut is well-founded (list induction on the multiset). -/
theorem cutExpR_wf (hr : WellFounded r) : WellFounded (CutExpR r) :=
  ⟨fun M => by
    induction M with
    | nil =>
        refine Acc.intro _ fun K hK => ?_
        obtain ⟨a, rest, new, hp, _, _⟩ := hK
        have h : 0 = rest.length + 1 := hp.length_eq
        exact Nat.noConfusion h
    | cons a M ih => exact accR_cons_of_acc (hr.apply a) M ih⟩

/-! ## §2 the multi-element cut, through the transitive closure -/

theorem transGR_cutExp_perm_right {K M M₁ : List α} (hp : M.Perm M₁)
    (h : TransG (CutExpR r) K M) : TransG (CutExpR r) K M₁ := by
  cases h with
  | single h => exact .single (cutExpR_perm_right hp h)
  | tail h1 h2 => exact .tail h1 (cutExpR_perm_right hp h2)

theorem transGR_cutExp_perm_left {K K₁ M : List α} (hp : K.Perm K₁)
    (h : TransG (CutExpR r) K M) : TransG (CutExpR r) K₁ M := by
  induction h with
  | single h => exact .single (cutExpR_perm_left hp h)
  | tail _ h2 ih => exact .tail ih h2

/-- The elements of `Y` dominated by one `x` are added in one step. -/
theorem cutExpR_replace (x : α) (Y Z : List α) (h : ∀ y ∈ Y, r y x) :
    CutExpR r (Y ++ Z) (x :: Z) :=
  ⟨x, Z, Y, List.Perm.refl _, List.Perm.refl _, h⟩

/-- **The finite ownership assignment.** Every inserted job of `Y` is owned by the
    head `a` of the removed part or by a member of its tail `X'`; the owners split
    `Y` (up to permutation) into the two parts. An existence statement by induction
    on `Y` — no decidability of `r`. -/
theorem split_owners (a : α) (X' : List α) : ∀ (Y : List α),
    (∀ y ∈ Y, ∃ x ∈ a :: X', r y x) →
    ∃ Y₁ Y₂ : List α, Y.Perm (Y₁ ++ Y₂) ∧ (∀ y ∈ Y₁, r y a) ∧ (∀ y ∈ Y₂, ∃ x ∈ X', r y x)
  | [], _ => ⟨[], [], List.Perm.refl _, fun _ h => absurd h (List.not_mem_nil _),
      fun _ h => absurd h (List.not_mem_nil _)⟩
  | y :: Y, hY => by
      obtain ⟨Y₁, Y₂, hp, h₁, h₂⟩ :=
        split_owners a X' Y (fun z hz => hY z (List.mem_cons_of_mem y hz))
      obtain ⟨x, hx, hr⟩ := hY y (List.mem_cons_self y Y)
      rcases List.mem_cons.mp hx with hxa | hxX
      · subst hxa
        refine ⟨y :: Y₁, Y₂, hp.cons y, ?_, h₂⟩
        intro z hz
        rcases List.mem_cons.mp hz with hzy | hzY
        · subst hzy; exact hr
        · exact h₁ z hzY
      · refine ⟨Y₁, y :: Y₂, (hp.cons y).trans List.perm_middle.symm, h₁, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with hzy | hzY
        · subst hzy; exact ⟨x, hxX, hr⟩
        · exact h₂ z hzY

/-- `X ++ Z` steps to `Y ++ Z` in the transitive closure of `CutExpR r` when every
    element of `Y` is `r`-below some element of the non-empty `X`. Induction on `X`:
    its head takes the part of `Y` it owns (`split_owners`), the tail the rest. -/
theorem transGR_of_dominated : ∀ (X : List α), X ≠ [] → ∀ (Y Z : List α),
    (∀ y ∈ Y, ∃ x ∈ X, r y x) → TransG (CutExpR r) (Y ++ Z) (X ++ Z)
  | [], hX, _, _, _ => absurd rfl hX
  | [x], _, Y, Z, hY => by
      refine .single (cutExpR_replace x Y Z fun y hy => ?_)
      obtain ⟨x', hx', hlt⟩ := hY y hy
      rcases List.mem_cons.mp hx' with h | h
      · subst h; exact hlt
      · exact absurd h (List.not_mem_nil _)
  | x :: x₂ :: X, _, Y, Z, hY => by
      obtain ⟨Y₁, Y₂, hYp, hY₁, hY₂⟩ := split_owners x (x₂ :: X) Y hY
      have ih := transGR_of_dominated (x₂ :: X) (List.cons_ne_nil _ _) Y₂ (Y₁ ++ Z) hY₂
      have hstep : CutExpR r (Y₁ ++ ((x₂ :: X) ++ Z)) (x :: ((x₂ :: X) ++ Z)) :=
        cutExpR_replace x _ _ hY₁
      have ih' : TransG (CutExpR r) (Y ++ Z) (Y₁ ++ ((x₂ :: X) ++ Z)) := by
        refine transGR_cutExp_perm_left ?_
          (transGR_cutExp_perm_right (List.perm_append_comm_assoc _ _ _) ih)
        refine (List.perm_append_comm_assoc _ _ _).trans ?_
        rw [← List.append_assoc]
        exact (List.Perm.append_right Z hYp).symm
      exact .tail ih' hstep

/-- Every multi-element step is in the transitive closure of the one-element cut. -/
theorem dmR_of_dmStepR {M' M : List α} (h : DMStepR r M' M) : TransG (CutExpR r) M' M := by
  obtain ⟨X, Y, Z, hX, hM, hM', hY⟩ := h
  exact transGR_cutExp_perm_left hM'.symm
    (transGR_cutExp_perm_right hM.symm (transGR_of_dominated X hX Y Z hY))

/-- **The generic multi-element Dershowitz–Manna step is well-founded.** -/
theorem dmStepR_wf (hr : WellFounded r) : WellFounded (DMStepR r) :=
  ⟨fun M => subrel_acc dmR_of_dmStepR ((transG_wf (cutExpR_wf hr)).apply M)⟩

/-! ## §3 generic combinators -/

theorem dmStepR_perm_left {M₁ M₂ M : List α} (hp : M₁.Perm M₂) (h : DMStepR r M₁ M) :
    DMStepR r M₂ M := by
  obtain ⟨X, Y, Z, hX, hM, hM₁, hlt⟩ := h
  exact ⟨X, Y, Z, hX, hM, hp.symm.trans hM₁, hlt⟩

theorem dmStepR_perm_right {M' M₁ M₂ : List α} (hp : M₁.Perm M₂) (h : DMStepR r M' M₁) :
    DMStepR r M' M₂ := by
  obtain ⟨X, Y, Z, hX, hM₁, hM', hlt⟩ := h
  exact ⟨X, Y, Z, hX, hp.symm.trans hM₁, hM', hlt⟩

/-- One removed job `x` pays finitely many inserted jobs `Y`, each `r`-below it. -/
theorem dmStepR_replace (x : α) (Y Z : List α) (h : ∀ y ∈ Y, r y x) :
    DMStepR r (Y ++ Z) (x :: Z) :=
  ⟨[x], Y, Z, List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨x, List.mem_cons_self _ _, h y hy⟩⟩

/-- One job replaced by one `r`-smaller job. -/
theorem dmStepR_single {y x : α} (h : r y x) (Z : List α) : DMStepR r (y :: Z) (x :: Z) :=
  dmStepR_replace x [y] Z fun z hz => by
    rcases List.mem_cons.mp hz with hzy | hzn
    · subst hzy; exact h
    · exact absurd hzn (List.not_mem_nil _)

/-- Dropping a non-empty part is a step. -/
theorem dmStepR_drop {X Z : List α} (hX : X ≠ []) : DMStepR r Z (X ++ Z) :=
  ⟨X, [], Z, hX, List.Perm.refl _, List.Perm.refl _, fun _ h => absurd h (List.not_mem_nil _)⟩

/-- Accessible points are irreflexive. -/
theorem accR_irrefl {β : Type} {s : β → β → Prop} {a : β} (h : Acc s a) : ¬ s a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

end Generic

/-! ## §4 the instance: the landed `Nat` step, and the source-work multiset -/

/-- The landed `DMStep` is the generic step at `Nat.lt` (definitionally). -/
theorem dmStep_iff_dmStepR (M' M : List Nat) :
    DMStep M' M ↔ DMStepR (fun a b : Nat => a < b) M' M :=
  Iff.rfl

/-- A source key: the atoms and the weight of one pending source job. -/
abbrev SourceKey := List Nat × Nat

/-- The order on source keys: the landed `LexDM` (a `DMStep` on the atoms, else a
    weight drop at equal atoms — the transport strips). -/
abbrev SourceR : SourceKey → SourceKey → Prop := LexDM

/-- **The work coordinate's order (§8.3).** `WorkStep J' J ⟺ ∃ X ≠ [], Y, Z, J ~ X ⊎ Z,
    J' ~ Y ⊎ Z, ∀ y ∈ Y, ∃ x ∈ X, SourceR y x`. -/
abbrev WorkStep : List SourceKey → List SourceKey → Prop := DMStepR SourceR

/-- `WorkStep` is well-founded, independently of any query `Before`. -/
theorem workStep_wf : WellFounded WorkStep := dmStepR_wf lexDM_wf

theorem workStep_irrefl (J : List SourceKey) : ¬ WorkStep J J :=
  accR_irrefl (workStep_wf.apply J)

/-- One job replaced by a `SourceR`-smaller job at an unchanged rest. -/
theorem workStep_of_sourceR {k' k : SourceKey} (h : SourceR k' k) (J : List SourceKey) :
    WorkStep (k' :: J) (k :: J) :=
  dmStepR_single h J

/-- One removed job pays finitely many uses, each `SourceR`-below it. -/
theorem workStep_uses {k : SourceKey} {Y : List SourceKey} (h : ∀ k' ∈ Y, SourceR k' k)
    (J : List SourceKey) : WorkStep (Y ++ J) (k :: J) :=
  dmStepR_replace k Y J h

/-- A weight drop at equal atoms is a `SourceR` step (the transport strips `wk`,
    `linst`, `ewk`). -/
theorem sourceR_of_wt_lt {M : List Nat} {w' w : Nat} (h : w' < w) : SourceR (M, w') (M, w) :=
  Prod.Lex.right _ h

/-- A `DMStep` on the atoms is a `SourceR` step at any weights. -/
theorem sourceR_of_dm {M' M : List Nat} {w' w : Nat} (h : DMStep M' M) : SourceR (M', w') (M, w) :=
  Prod.Lex.left _ _ h

/-! ## §5 pins -/

/-- PIN (§9 double materialization, the work side): the public `esub` root's one
    source job `([7, 11, 1], 20)` pays **two** uses of the shared packet
    `([1, 11, 1], 13)` — two jobs, one primary occurrence. -/
theorem pin_workStep_two_uses :
    WorkStep [([1, 11, 1], 13), ([1, 11, 1], 13)] [([7, 11, 1], 20)] := by
  have hdm : DMStep [1, 11, 1] [7, 11, 1] :=
    ⟨[7], [1], [11, 1], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
      fun y hy => ⟨7, List.mem_cons_self _ _, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega⟩⟩
  refine workStep_uses (Y := [([1, 11, 1], 13), ([1, 11, 1], 13)]) ?_ []
  intro k' hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
  rcases hk' with rfl | rfl <;> exact sourceR_of_dm hdm

/-- PIN (sharpness): no job, no step. -/
theorem pin_workStep_irrefl_nil : ¬ WorkStep [] [] := workStep_irrefl []

end Rcic.Syn

#print axioms Rcic.Syn.cutExpR_wf
#print axioms Rcic.Syn.split_owners
#print axioms Rcic.Syn.transGR_of_dominated
#print axioms Rcic.Syn.dmR_of_dmStepR
#print axioms Rcic.Syn.dmStepR_wf
#print axioms Rcic.Syn.dmStep_iff_dmStepR
#print axioms Rcic.Syn.workStep_wf
#print axioms Rcic.Syn.workStep_irrefl
#print axioms Rcic.Syn.workStep_of_sourceR
#print axioms Rcic.Syn.workStep_uses
#print axioms Rcic.Syn.pin_workStep_two_uses
#print axioms Rcic.Syn.pin_workStep_irrefl_nil
