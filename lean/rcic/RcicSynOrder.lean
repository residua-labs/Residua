import rcic.RcicSynLevel

/-!
# Syntactic sortRow, build step 1b — O1, the order of the mutual induction

`research/rcic/semantic/S1_ORDER_ENRICHED_LEVELS.md` §3. The mutual induction (ES / CL / EUT / PB /
GenSpine) recurses on **multisets of atom weights**. An atom is a non-transport enriched derivation or
a transport parameter (`RcicConvPlus`); its weight is a `Nat` (`TyP.wt`). A recursive call is
admissible when it is a Dershowitz–Manna step. It removes at least one atom of the caller and adds
finitely many atoms, each lighter than a removed one. Copies are allowed, which is why a single `Nat`
(sum or max) is not enough: an explicit substitution's argument is shared by the two halves of a
Π-inversion, and both halves can enter one call. `S1` §3.2 gives that case.

This module proves the order well-founded, constructively. The base order is `Nat.lt`.
* `CutExp M' M`: one step. Some `a` is removed from `M` and replaced by finitely many elements `< a`.
  Multisets are `List Nat` up to `List.Perm`.
* `cutExp_wf`: `WellFounded CutExp`, by Nipkow's argument. Every `a :: M` with `M` accessible is
  accessible, by strong induction on `a` and then by accessibility of `M`.
* `dmStep_wf`: the multi-element step used by the call table. Remove a non-empty `X`, add `Y`, with
  every element of `Y` below some element of `X`. It lies in the transitive closure of `CutExp`
  (`dm_of_dmStep`), which is well-founded (`transGen_wf`).
No `Classical.choice`: the one core lemma that needs it (`List.perm_cons_erase`) is replaced by
`perm_cons_of_mem`, by induction on membership.
-/

namespace Rcic.Syn

/-- one Dershowitz–Manna step on `Nat` multisets (as lists up to permutation): `M'` arises from `M` by
    removing one `a` and adding finitely many elements, each `< a`. -/
def CutExp (M' M : List Nat) : Prop :=
  ∃ (a : Nat) (rest new : List Nat), M.Perm (a :: rest) ∧ M'.Perm (new ++ rest) ∧ ∀ y ∈ new, y < a

theorem cutExp_perm_right {K M M₁ : List Nat} (hp : M.Perm M₁) (h : CutExp K M) : CutExp K M₁ := by
  obtain ⟨a, rest, new, h1, h2, h3⟩ := h
  exact ⟨a, rest, new, hp.symm.trans h1, h2, h3⟩

theorem cutExp_perm_left {K K₁ M : List Nat} (hp : K.Perm K₁) (h : CutExp K M) : CutExp K₁ M := by
  obtain ⟨a, rest, new, h1, h2, h3⟩ := h
  exact ⟨a, rest, new, h1, hp.symm.trans h2, h3⟩

theorem acc_cutExp_perm {M M₁ : List Nat} (hp : M.Perm M₁) (h : Acc CutExp M) : Acc CutExp M₁ :=
  Acc.intro _ fun _ hK => h.inv (cutExp_perm_right hp.symm hK)

/-- a member can be brought to the front. Core's `List.perm_cons_erase` uses `Classical.choice`. -/
theorem perm_cons_of_mem {c : Nat} : ∀ {M : List Nat}, c ∈ M → ∃ rest, M.Perm (c :: rest)
  | _, .head as => ⟨as, List.Perm.refl _⟩
  | _, .tail b h =>
      let ⟨rest, hp⟩ := perm_cons_of_mem h
      ⟨b :: rest, (hp.cons b).trans (List.Perm.swap c b rest)⟩

/-- where the removed element of `a :: M` sits: it is `a` itself, or it lies in `M`. -/
theorem perm_cons_split {a c : Nat} {M rest : List Nat} (h : (a :: M).Perm (c :: rest)) :
    (c = a ∧ M.Perm rest) ∨ ∃ rest', M.Perm (c :: rest') ∧ rest.Perm (a :: rest') := by
  have hc : c ∈ a :: M := h.symm.mem_iff.mp (List.mem_cons_self c rest)
  rcases List.mem_cons.mp hc with hca | hcM
  · subst hca
    exact Or.inl ⟨rfl, h.cons_inv⟩
  · obtain ⟨rest', hp⟩ := perm_cons_of_mem hcM
    refine Or.inr ⟨rest', hp, ?_⟩
    have h1 : (a :: M).Perm (c :: a :: rest') := (hp.cons a).trans (List.Perm.swap c a _)
    exact (h.symm.trans h1).cons_inv

/-- prepending elements below `a` keeps accessibility, given the claim for every `b < a`. -/
theorem acc_append_of_lt {a : Nat}
    (P : ∀ b, b < a → ∀ N, Acc CutExp N → Acc CutExp (b :: N)) :
    ∀ (new : List Nat), (∀ y ∈ new, y < a) → ∀ M, Acc CutExp M → Acc CutExp (new ++ M)
  | [], _, _, hM => hM
  | b :: new, hlt, M, hM =>
      P b (hlt b (List.mem_cons_self b new)) _
        (acc_append_of_lt P new (fun y hy => hlt y (List.mem_cons_of_mem b hy)) M hM)

/-- Nipkow's lemma: `a :: M` is accessible whenever `M` is. -/
theorem acc_cons_of_acc (a : Nat) : ∀ (M : List Nat), Acc CutExp M → Acc CutExp (a :: M) := by
  induction a using Nat.strongRecOn with
  | _ a iha =>
    intro M hM
    induction hM with
    | intro M hacc ihM =>
      refine Acc.intro _ ?_
      intro K hK
      obtain ⟨c, rest, new, hp, hK', hlt⟩ := hK
      rcases perm_cons_split hp with ⟨hca, hMr⟩ | ⟨rest', hMc, hra⟩
      · subst hca
        have hA : Acc CutExp (new ++ M) :=
          acc_append_of_lt (fun b hb N hN => iha b hb N hN) new hlt M (Acc.intro M hacc)
        exact acc_cutExp_perm ((List.Perm.append_left new hMr.symm).symm.trans hK'.symm) hA
      · have hstep : CutExp (new ++ rest') M := ⟨c, rest', new, hMc, List.Perm.refl _, hlt⟩
        have hA : Acc CutExp (a :: (new ++ rest')) := ihM _ hstep
        have hpK : K.Perm (a :: (new ++ rest')) :=
          hK'.trans ((List.Perm.append_left new hra).trans List.perm_middle)
        exact acc_cutExp_perm hpK.symm hA

/-- O1: the one-step Dershowitz–Manna order on `Nat` multisets is well-founded. -/
theorem cutExp_wf : WellFounded CutExp :=
  ⟨fun M => by
    induction M with
    | nil =>
        refine Acc.intro _ fun K hK => ?_
        obtain ⟨a, rest, new, hp, _, _⟩ := hK
        have h : 0 = rest.length + 1 := hp.length_eq
        exact Nat.noConfusion h
    | cons a M ih => exact acc_cons_of_acc a M ih⟩

/-! ## the multi-element step, through the transitive closure -/

/-- transitive closure. -/
inductive TransG {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {a b : α} (h : r a b) : TransG r a b
  | tail {a b c : α} (h1 : TransG r a b) (h2 : r b c) : TransG r a c

theorem transG_acc {α : Type} {r : α → α → Prop} {x : α} (h : Acc r x) : Acc (TransG r) x := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro _ fun y hy => ?_
    cases hy with
    | single h => exact ih y h
    | tail h1 h2 => exact (ih _ h2).inv h1

theorem transG_wf {α : Type} {r : α → α → Prop} (h : WellFounded r) : WellFounded (TransG r) :=
  ⟨fun x => transG_acc (h.apply x)⟩

/-- the multi-element Dershowitz–Manna step the call table uses. `M = X ++ Z`, `M' ~ Y ++ Z`, `X`
    non-empty, and every element of `Y` lies below some element of `X`. -/
def DMStep (M' M : List Nat) : Prop :=
  ∃ X Y Z : List Nat, X ≠ [] ∧ M.Perm (X ++ Z) ∧ M'.Perm (Y ++ Z) ∧ ∀ y ∈ Y, ∃ x ∈ X, y < x

/-- dropping an element is one `CutExp` step (it is replaced by nothing). -/
theorem cutExp_drop (x : Nat) (Z : List Nat) : CutExp Z (x :: Z) :=
  ⟨x, Z, [], List.Perm.refl _, List.Perm.refl _, fun _ h => absurd h (List.not_mem_nil _)⟩

/-- the elements of `Y` dominated by one `x` are added in one step. -/
theorem cutExp_replace (x : Nat) (Y Z : List Nat) (h : ∀ y ∈ Y, y < x) : CutExp (Y ++ Z) (x :: Z) :=
  ⟨x, Z, Y, List.Perm.refl _, List.Perm.refl _, h⟩

/-- the elements of `Y` dominated by `x`, and the rest. -/
def splitBelow (x : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | y :: Y =>
      let p := splitBelow x Y
      if y < x then (y :: p.1, p.2) else (p.1, y :: p.2)

theorem splitBelow_perm (x : Nat) : ∀ Y : List Nat,
    Y.Perm ((splitBelow x Y).1 ++ (splitBelow x Y).2)
  | [] => List.Perm.refl _
  | y :: Y => by
      have ih := splitBelow_perm x Y
      simp only [splitBelow]
      split
      · exact ih.cons y
      · exact (ih.cons y).trans List.perm_middle.symm

theorem splitBelow_fst_lt (x : Nat) : ∀ Y : List Nat, ∀ y ∈ (splitBelow x Y).1, y < x
  | [] => fun _ h => absurd h (List.not_mem_nil _)
  | y :: Y => by
      intro z hz
      simp only [splitBelow] at hz
      split at hz
      · rcases List.mem_cons.mp hz with h | h
        · subst h; assumption
        · exact splitBelow_fst_lt x Y z h
      · exact splitBelow_fst_lt x Y z hz

theorem splitBelow_snd_of_mem (x : Nat) : ∀ Y : List Nat, ∀ y ∈ (splitBelow x Y).2, y ∈ Y ∧ ¬ y < x
  | [] => fun _ h => absurd h (List.not_mem_nil _)
  | y :: Y => by
      intro z hz
      simp only [splitBelow] at hz
      split at hz
      · have ⟨h1, h2⟩ := splitBelow_snd_of_mem x Y z hz
        exact ⟨List.mem_cons_of_mem y h1, h2⟩
      · rename_i hy
        rcases List.mem_cons.mp hz with h | h
        · subst h; exact ⟨List.mem_cons_self _ _, hy⟩
        · have ⟨h1, h2⟩ := splitBelow_snd_of_mem x Y z h
          exact ⟨List.mem_cons_of_mem y h1, h2⟩

theorem transG_cutExp_perm_right {K M M₁ : List Nat} (hp : M.Perm M₁)
    (h : TransG CutExp K M) : TransG CutExp K M₁ := by
  cases h with
  | single h => exact .single (cutExp_perm_right hp h)
  | tail h1 h2 => exact .tail h1 (cutExp_perm_right hp h2)

theorem transG_cutExp_perm_left {K K₁ M : List Nat} (hp : K.Perm K₁)
    (h : TransG CutExp K M) : TransG CutExp K₁ M := by
  induction h with
  | single h => exact .single (cutExp_perm_left hp h)
  | tail _ h2 ih => exact .tail ih h2

/-- `X ++ Z` steps to `Y ++ Z` in the transitive closure of `CutExp`, when every element of `Y` lies
    below some element of the non-empty `X`. The induction is on `X`: its head takes the part of `Y`
    it dominates, and the tail takes the rest. -/
theorem transG_of_dominated : ∀ (X : List Nat), X ≠ [] → ∀ (Y Z : List Nat),
    (∀ y ∈ Y, ∃ x ∈ X, y < x) → TransG CutExp (Y ++ Z) (X ++ Z)
  | [], hX, _, _, _ => absurd rfl hX
  | [x], _, Y, Z, hY => by
      refine .single (cutExp_replace x Y Z fun y hy => ?_)
      obtain ⟨x', hx', hlt⟩ := hY y hy
      rcases List.mem_cons.mp hx' with h | h
      · subst h; exact hlt
      · exact absurd h (List.not_mem_nil _)
  | x :: x₂ :: X, _, Y, Z, hY => by
      have hrest : ∀ y ∈ (splitBelow x Y).2, ∃ x' ∈ x₂ :: X, y < x' := by
        intro y hy
        have ⟨hyY, hnot⟩ := splitBelow_snd_of_mem x Y y hy
        obtain ⟨x', hx', hlt⟩ := hY y hyY
        rcases List.mem_cons.mp hx' with h | h
        · subst h; exact absurd hlt hnot
        · exact ⟨x', h, hlt⟩
      -- the tail `x₂ :: X` takes the part of `Y` that `x` does not dominate
      have ih := transG_of_dominated (x₂ :: X) (List.cons_ne_nil _ _) (splitBelow x Y).2
        ((splitBelow x Y).1 ++ Z) hrest
      -- the head `x` takes the part it dominates, in one step
      have hstep : CutExp ((splitBelow x Y).1 ++ ((x₂ :: X) ++ Z)) (x :: ((x₂ :: X) ++ Z)) :=
        cutExp_replace x _ _ (splitBelow_fst_lt x Y)
      have ih' : TransG CutExp (Y ++ Z) ((splitBelow x Y).1 ++ ((x₂ :: X) ++ Z)) := by
        refine transG_cutExp_perm_left ?_
          (transG_cutExp_perm_right (List.perm_append_comm_assoc _ _ _) ih)
        refine (List.perm_append_comm_assoc _ _ _).trans ?_
        rw [← List.append_assoc]
        exact (List.Perm.append_right Z (splitBelow_perm x Y)).symm
      exact .tail ih' hstep

/-- every multi-element step is in the transitive closure of `CutExp`. -/
theorem dm_of_dmStep {M' M : List Nat} (h : DMStep M' M) : TransG CutExp M' M := by
  obtain ⟨X, Y, Z, hX, hM, hM', hY⟩ := h
  exact transG_cutExp_perm_left hM'.symm
    (transG_cutExp_perm_right hM.symm (transG_of_dominated X hX Y Z hY))

theorem subrel_acc {α : Type} {r s : α → α → Prop} (hsub : ∀ {a b}, r a b → s a b) {x : α}
    (h : Acc s x) : Acc r x := by
  induction h with
  | intro x _ ih => exact Acc.intro _ fun y hy => ih y (hsub hy)

/-- O1: the multi-element Dershowitz–Manna step is well-founded. Every recursive call of the mutual
    induction is a `DMStep` on the multiset of atom weights (`S1` §3). -/
theorem dmStep_wf : WellFounded DMStep :=
  ⟨fun M => subrel_acc dm_of_dmStep ((transG_wf cutExp_wf).apply M)⟩

/-- a sub-multiset call: dropping a non-empty part `X` is a step. -/
theorem dmStep_drop {X Z : List Nat} (hX : X ≠ []) : DMStep Z (X ++ Z) :=
  ⟨X, [], Z, hX, List.Perm.refl _, List.Perm.refl _, fun _ h => absurd h (List.not_mem_nil _)⟩

/-- THE TWO-SIDED CALL (`S1` §3.4). Each side gives up one atom (`x₁`, `x₂`) and contributes parts
    below it (`Y₁`, `Y₂`). Each side's rest (`Z₁`, `Z₂`) is kept once, which is where an outer
    transport's parameters sit. -/
theorem dmStep_two_sided {x₁ x₂ : Nat} {Y₁ Y₂ Z₁ Z₂ : List Nat} (h₁ : ∀ y ∈ Y₁, y < x₁)
    (h₂ : ∀ y ∈ Y₂, y < x₂) : DMStep ((Y₁ ++ Z₁) ++ (Y₂ ++ Z₂)) ((x₁ :: Z₁) ++ (x₂ :: Z₂)) := by
  refine ⟨[x₁, x₂], Y₁ ++ Y₂, Z₁ ++ Z₂, List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · show (x₁ :: (Z₁ ++ x₂ :: Z₂)).Perm (x₁ :: x₂ :: (Z₁ ++ Z₂))
    exact (List.perm_middle).cons x₁
  · show (Y₁ ++ Z₁ ++ (Y₂ ++ Z₂)).Perm (Y₁ ++ Y₂ ++ (Z₁ ++ Z₂))
    rw [List.append_assoc, List.append_assoc]
    refine List.Perm.append_left Y₁ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right Z₂ List.perm_append_comm
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨x₁, List.mem_cons_self _ _, h₁ y hy⟩
    · exact ⟨x₂, List.mem_cons_of_mem _ (List.mem_cons_self _ _), h₂ y hy⟩

/-- THE FULL ORDER (`S1` §3.5): the multiset step, then a `Nat` (the summed weight). The second
    component pays for stripping a parameterless transport (`wk`, `linst`, `ewk`), which leaves the
    atom multiset literally unchanged. -/
theorem lexDM_wf : WellFounded (Prod.Lex DMStep (fun a b : Nat => a < b)) :=
  ⟨fun ⟨M, k⟩ => Prod.lexAccessible (dmStep_wf.apply M) (fun b => (Nat.lt_wfRel.wf).apply b) k⟩

/-! ## pins -/

/-- PIN: one atom of weight 5 is replaced by three copies of weight 4 and one of weight 0. Copies are
    allowed, which a `Nat` sum would refuse here: `4 + 4 + 4 + 0 > 5`. -/
theorem pin_dmStep_copies : DMStep [4, 4, 4, 0, 7] [5, 7] :=
  ⟨[5], [4, 4, 4, 0], [7], List.cons_ne_nil _ _, List.Perm.refl _, List.Perm.refl _,
    fun y hy => ⟨5, List.mem_cons_self _ _, by
      rcases List.mem_cons.mp hy with h | h
      · subst h; decide
      rcases List.mem_cons.mp h with h | h
      · subst h; decide
      rcases List.mem_cons.mp h with h | h
      · subst h; decide
      rcases List.mem_cons.mp h with h | h
      · subst h; decide
      · exact absurd h (List.not_mem_nil _)⟩⟩

/-- PIN (sharpness): the empty step is not a step, since `X` must be non-empty. -/
theorem pin_dmStep_irrefl_nil : ¬ DMStep [] [] := by
  intro ⟨X, _, _, hX, hM, _, _⟩
  have h := hM.length_eq
  rw [List.length_append] at h
  cases X with
  | nil => exact hX rfl
  | cons x X =>
      have h' : 0 = X.length + 1 + _ := h
      exact absurd h' (by omega)

end Rcic.Syn

#print axioms Rcic.Syn.cutExp_perm_right
#print axioms Rcic.Syn.cutExp_perm_left
#print axioms Rcic.Syn.acc_cutExp_perm
#print axioms Rcic.Syn.perm_cons_of_mem
#print axioms Rcic.Syn.perm_cons_split
#print axioms Rcic.Syn.acc_append_of_lt
#print axioms Rcic.Syn.acc_cons_of_acc
#print axioms Rcic.Syn.cutExp_wf
#print axioms Rcic.Syn.transG_acc
#print axioms Rcic.Syn.transG_wf
#print axioms Rcic.Syn.cutExp_drop
#print axioms Rcic.Syn.cutExp_replace
#print axioms Rcic.Syn.splitBelow_perm
#print axioms Rcic.Syn.splitBelow_fst_lt
#print axioms Rcic.Syn.splitBelow_snd_of_mem
#print axioms Rcic.Syn.transG_cutExp_perm_right
#print axioms Rcic.Syn.transG_cutExp_perm_left
#print axioms Rcic.Syn.transG_of_dominated
#print axioms Rcic.Syn.dm_of_dmStep
#print axioms Rcic.Syn.subrel_acc
#print axioms Rcic.Syn.dmStep_wf
#print axioms Rcic.Syn.dmStep_drop
#print axioms Rcic.Syn.dmStep_two_sided
#print axioms Rcic.Syn.lexDM_wf
#print axioms Rcic.Syn.pin_dmStep_copies
#print axioms Rcic.Syn.pin_dmStep_irrefl_nil
