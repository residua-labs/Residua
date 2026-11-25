-- provenance: ours (searched: Mathlib v4.14.0 PFunctor/WType/QPF — they reach a concrete inductive only through a hand-written Equiv per type; lean/nf-compose, lean/hyper/algorithms, semantics/NF — no recursion law over ExecModel; shape after Malcolm 1990 fold fusion and Plotkin 1973 fundamental lemma)
import NfCompose.HopCompose

/-!
RecCompose: the recursive composition law of MST-NF.

Encoding. A tree is any type `T` with a *tree view* `TreeSig T`: the children
of a node (`kids : T → List T`) and a size that every child is below. The
view is chosen over Mathlib's `PFunctor`/`WType`/`QPF` because it is stated
on the concrete type itself: nested inductives (children in a `List`, such as
`Lrc.N`, `Wasm0.Instr`) give `kids` as a field or a one-line match, mutual
and indexed families (`BootExpr`/`Args`/`Branches`) as a sum carrier, and the
size is Lean's derived `sizeOf` in every case. No equivalence to a W-type is
built per instance; the per-instance work is the view and the local lemmas.

* `TreeSig.induction` — induction over the view; `TreeSig.fold` — the
  catamorphism, `fold_eq` its equation, `eq_fold` uniqueness (any function
  satisfying the equations is the fold), `fold_fusion` fold fusion.
* A. `recModel` — a model whose raw inputs and classes are trees, built
  from a `LocalStep` (evaluation, admission, residue, representative per
  node from the children's results). `rho` is the first failing node in
  post-order (children left to right, then the node), with its path (child
  indices from the root) and its local residue. `recModel_profile`: the
  local Tier-1 laws give `hasMSTNFProfile`. `recModel_rho_none_iff`:
  residue emptiness is admission. `recModel_rho_path`: the residue names a
  node, at its path, whose local admission fails with that residue.
* B. `hopCorrect_of_rel` — fundamental lemma: a per-node relation closed
  under the local laws, with a root adequacy, gives `hopCorrect`.
  `hopCorrect_of_localSquares` — the per-constructor square of a hop
  commutes at every node, so the hop is `hopCorrect` (stated with
  `hopModel`/`hopCorrect` of `NfCompose.Hop`). `hopCorrect_of_fusion` — the
  same in algebra form (fold fusion).
* C. `TreeSig.step_induction`, `clockHopCorrect_of_stepRel` — the
  step-indexed form (Appel–McAllester): the local law may use the relation at
  every smaller clock for any node (calls, jumps, loops) and at the same
  clock for the children; stated with HopCompose's `Fam` and
  `clockHopCorrect` (no second clock family).
* D. `Necessity` — one witness per hypothesis of A, B and C: every other
  hypothesis holds, the dropped one fails at one constructor, and the
  conclusion fails.
-/

namespace NfCompose.Rec

open MSTNecessityExecModelMWE

/-- a tree view of `T`: the children of each node, and a size that every
    child is below. -/
structure TreeSig (T : Type) where
  kids : T → List T
  size : T → Nat
  kids_lt : ∀ t s, s ∈ kids t → size s < size t

namespace TreeSig

theorem induction {T : Type} (S : TreeSig T) {P : T → Prop}
    (step : ∀ t, (∀ s ∈ S.kids t, P s) → P t) (t : T) : P t := by
  suffices h : ∀ n, ∀ t, S.size t < n → P t from h _ t (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro t h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro t h
      exact step t fun s hs => ih s (by have := S.kids_lt t s hs; omega)

/-- the fold with explicit depth bound. -/
def foldN {T R : Type} (S : TreeSig T) (alg : T → List R → R) : Nat → T → R
  | 0, t => alg t []
  | n + 1, t => alg t ((S.kids t).map (foldN S alg n))

/-- the catamorphism of the view. -/
def fold {T R : Type} (S : TreeSig T) (alg : T → List R → R) (t : T) : R :=
  foldN S alg (S.size t + 1) t

theorem map_congr_mem {α β : Type} {f g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.map_cons]
      rw [h a (by simp), map_congr_mem (fun b hb => h b (by simp [hb]))]

theorem foldN_stable {T R : Type} (S : TreeSig T) (alg : T → List R → R) :
    ∀ n m t, S.size t < n → S.size t < m → foldN S alg n t = foldN S alg m t
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, m + 1, t, hn, hm => by
      simp only [foldN]
      congr 1
      apply map_congr_mem
      intro s hs
      have := S.kids_lt t s hs
      exact foldN_stable S alg n m s (by omega) (by omega)

/-- the fold equation. -/
theorem fold_eq {T R : Type} (S : TreeSig T) (alg : T → List R → R) (t : T) :
    fold S alg t = alg t ((S.kids t).map (fold S alg)) := by
  show foldN S alg (S.size t + 1) t = _
  simp only [foldN]
  congr 1
  apply map_congr_mem
  intro s hs
  have := S.kids_lt t s hs
  exact foldN_stable S alg _ _ s this (by omega)

/-- uniqueness: a function satisfying the fold equations is the fold. -/
theorem eq_fold {T R : Type} (S : TreeSig T) (alg : T → List R → R) (f : T → R)
    (hf : ∀ t, f t = alg t ((S.kids t).map f)) (t : T) : f t = fold S alg t :=
  S.induction (P := fun t => f t = fold S alg t) (fun t ih => by
    dsimp only
    rw [hf t, fold_eq S alg t]
    congr 1
    exact map_congr_mem ih) t

/-- fold fusion (Malcolm 1990): `h ∘ fold alg₁ = fold alg₂` when `h` commutes
    with the two algebras. -/
theorem fold_fusion {T R₁ R₂ : Type} (S : TreeSig T) (alg₁ : T → List R₁ → R₁)
    (alg₂ : T → List R₂ → R₂) (h : R₁ → R₂)
    (hcomm : ∀ t rs, h (alg₁ t rs) = alg₂ t (rs.map h)) (t : T) :
    h (fold S alg₁ t) = fold S alg₂ t :=
  eq_fold S alg₂ (h ∘ fold S alg₁) (fun t => by
    show h (fold S alg₁ t) = _
    rw [fold_eq S alg₁ t, hcomm, List.map_map]) t

end TreeSig

open TreeSig

/-! ## List helpers -/

theorem forall_mem_map {α β : Type} (f : α → β) (P : β → Prop) :
    ∀ l : List α, (∀ b ∈ l.map f, P b) ↔ ∀ a ∈ l, P (f a)
  | [] => by simp
  | a :: l => by simp [forall_mem_map f P l]

theorem all_eq_true' {α : Type} (p : α → Bool) :
    ∀ l : List α, l.all p = true ↔ ∀ a ∈ l, p a = true
  | [] => by simp
  | a :: l => by simp [List.all_cons, all_eq_true' p l]

/-- the first `some` of a list of child residues, its child index prepended. -/
def firstFail {E : Type} : Nat → List (Option (List Nat × E)) → Option (List Nat × E)
  | _, [] => none
  | i, none :: rs => firstFail (i + 1) rs
  | i, some (p, e) :: _ => some (i :: p, e)

theorem firstFail_eq_none {E : Type} :
    ∀ (i : Nat) (xs : List (Option (List Nat × E))),
      firstFail i xs = none ↔ ∀ x ∈ xs, x = none
  | _, [] => by simp [firstFail]
  | i, none :: rs => by simp [firstFail, firstFail_eq_none (i + 1) rs]
  | i, some (p, e) :: rs => by simp [firstFail]

/-- the result list when every entry is `some`. -/
def allSome {P : Type} : List (Option P) → Option (List P)
  | [] => some []
  | none :: _ => none
  | some p :: rs => (allSome rs).map (p :: ·)

theorem allSome_eq_none {P : Type} :
    ∀ xs : List (Option P), allSome xs = none ↔ ∃ x ∈ xs, x = none
  | [] => by simp [allSome]
  | none :: _ => by simp [allSome]
  | some p :: rs => by simp [allSome, allSome_eq_none rs]

/-! ## A. The profile under recursion -/

/-- the bottom-up result of a class subtree. -/
structure Bundle (O P E : Type) where
  out : O
  adm : Bool
  rho : Option (List Nat × E)
  sig : Option P

/-- one node's step, from the children's results. `evalR` on raw nodes,
    the rest on class nodes. -/
structure LocalStep (T C : Type) where
  Out : Type
  Rep : Type
  LRes : Type
  evalR : T → List Out → Out
  evalC : C → List Out → Out
  adm : C → List Out → Bool
  rho : C → List Out → Option LRes
  sig : C → List Out → List Rep → Option Rep

/-- the node part of the residue: a failing child first, else the node's
    own residue when its local admission fails. -/
def combineRho {E : Type} (ff : Option (List Nat × E)) (a : Bool) (r : Option E) :
    Option (List Nat × E) :=
  match ff with
  | some x => some x
  | none => if a then none else r.map (fun e => ([], e))

theorem combineRho_eq_none {E : Type} (ff : Option (List Nat × E)) (a : Bool)
    (r : Option E) : combineRho ff a r = none ↔ ff = none ∧ (a = false → r = none) := by
  cases ff <;> cases a <;> cases r <;> simp [combineRho]

variable {T C : Type}

/-- the class-level algebra of a `LocalStep`. -/
def stepAlg (L : LocalStep T C) (c : C) (rs : List (Bundle L.Out L.Rep L.LRes)) :
    Bundle L.Out L.Rep L.LRes where
  out := L.evalC c (rs.map (·.out))
  adm := L.adm c (rs.map (·.out)) && rs.all (·.adm)
  rho := combineRho (firstFail 0 (rs.map (·.rho))) (L.adm c (rs.map (·.out)))
    (L.rho c (rs.map (·.out)))
  sig := (allSome (rs.map (·.sig))).bind (L.sig c (rs.map (·.out)))

/-- the recursive model: evaluation of raw trees by the raw fold, every
    class-side component by the class fold of `stepAlg`. -/
def recModel (ST : TreeSig T) (SC : TreeSig C) (q : T → C) (L : LocalStep T C) :
    ExecModel where
  Raw := T
  Class := C
  Rep := L.Rep
  Residue := List Nat × L.LRes
  Outcome := L.Out
  q := q
  evalRaw := ST.fold L.evalR
  evalClass := fun c => (SC.fold (stepAlg L) c).out
  admissible := fun c => (SC.fold (stepAlg L) c).adm
  rho := fun c => (SC.fold (stepAlg L) c).rho
  sigma := fun c => (SC.fold (stepAlg L) c).sig

/-- `q` is a tree homomorphism on children. -/
def QKids (ST : TreeSig T) (SC : TreeSig C) (q : T → C) : Prop :=
  ∀ t, SC.kids (q t) = (ST.kids t).map q

/-- local R1: a raw node's step factors through its class node. -/
def LocalQF (q : T → C) (L : LocalStep T C) : Prop :=
  ∀ t outs, L.evalR t outs = L.evalC (q t) outs

/-- local R2: a node with a local representative is locally admitted. -/
def LocalAS (L : LocalStep T C) : Prop :=
  ∀ c outs reps rep, L.sig c outs reps = some rep → L.adm c outs = true

/-- local Φ5: a locally refused node names a local residue. -/
def LocalRT (L : LocalStep T C) : Prop :=
  ∀ c outs, L.adm c outs = false → L.rho c outs ≠ none

/-- local Φ2b: a locally admitted node builds a representative from its
    children's representatives. -/
def LocalRP (L : LocalStep T C) : Prop :=
  ∀ c outs reps, L.adm c outs = true → L.sig c outs reps ≠ none

section A

variable (ST : TreeSig T) (SC : TreeSig C) (q : T → C) (L : LocalStep T C)

theorem stepAlg_out (c : C) (rs) :
    (stepAlg L c rs).out = L.evalC c (rs.map (·.out)) := rfl
theorem stepAlg_adm (c : C) (rs) :
    (stepAlg L c rs).adm = (L.adm c (rs.map (·.out)) && rs.all (·.adm)) := rfl
theorem stepAlg_rho (c : C) (rs) :
    (stepAlg L c rs).rho = combineRho (firstFail 0 (rs.map (·.rho)))
      (L.adm c (rs.map (·.out))) (L.rho c (rs.map (·.out))) := rfl
theorem stepAlg_sig (c : C) (rs) :
    (stepAlg L c rs).sig = (allSome (rs.map (·.sig))).bind (L.sig c (rs.map (·.out))) := rfl

theorem rec_qf (hq : QKids ST SC q) (hqf : LocalQF q L) (t : T) :
    ST.fold L.evalR t = (SC.fold (stepAlg L) (q t)).out := by
  refine ST.induction (P := fun t => ST.fold L.evalR t = (SC.fold (stepAlg L) (q t)).out)
    (fun t ih => ?_) t
  dsimp only
  rw [ST.fold_eq L.evalR t, SC.fold_eq (stepAlg L) (q t), stepAlg_out, hqf t, hq t,
    List.map_map, List.map_map]
  congr 1
  exact map_congr_mem ih

/-- exactness under recursion: no residue iff admitted. -/
theorem rec_rho_none_iff (hRT : LocalRT L) (c : C) :
    (SC.fold (stepAlg L) c).rho = none ↔ (SC.fold (stepAlg L) c).adm = true := by
  refine SC.induction (P := fun c =>
    (SC.fold (stepAlg L) c).rho = none ↔ (SC.fold (stepAlg L) c).adm = true)
    (fun c ih => ?_) c
  dsimp only
  rw [SC.fold_eq (stepAlg L) c, stepAlg_rho, stepAlg_adm, combineRho_eq_none,
    firstFail_eq_none, Bool.and_eq_true, all_eq_true']
  simp only [forall_mem_map]
  have hkids : (∀ s ∈ SC.kids c, (SC.fold (stepAlg L) s).rho = none) ↔
      (∀ s ∈ SC.kids c, (SC.fold (stepAlg L) s).adm = true) :=
    ⟨fun h s hs => (ih s hs).mp (h s hs), fun h s hs => (ih s hs).mpr (h s hs)⟩
  rw [hkids]
  have hloc := hRT c ((SC.kids c).map (SC.fold (stepAlg L)) |>.map (·.out))
  cases ha : L.adm c (((SC.kids c).map (SC.fold (stepAlg L))).map (·.out)) with
  | true => exact ⟨fun ⟨h, _⟩ => ⟨rfl, h⟩, fun ⟨_, h⟩ => ⟨h, fun hf => by cases hf⟩⟩
  | false =>
      have := hloc ha
      constructor
      · intro ⟨_, h⟩; exact absurd (h rfl) this
      · intro ⟨h, _⟩; cases h

theorem rec_as (hAS : LocalAS L) (c : C) (rep : L.Rep)
    (h : (SC.fold (stepAlg L) c).sig = some rep) : (SC.fold (stepAlg L) c).adm = true := by
  revert rep
  refine SC.induction (P := fun c => ∀ rep,
    (SC.fold (stepAlg L) c).sig = some rep → (SC.fold (stepAlg L) c).adm = true)
    (fun c ih => ?_) c
  intro rep h
  rw [SC.fold_eq (stepAlg L) c] at h ⊢
  rw [stepAlg_sig] at h
  rw [stepAlg_adm, Bool.and_eq_true, all_eq_true', forall_mem_map]
  cases hs : allSome (((SC.kids c).map (SC.fold (stepAlg L))).map (·.sig)) with
  | none => rw [hs] at h; simp at h
  | some reps =>
      rw [hs] at h
      refine ⟨hAS c _ reps rep h, fun s hs' => ?_⟩
      have hne : allSome (((SC.kids c).map (SC.fold (stepAlg L))).map (·.sig)) ≠ none := by
        rw [hs]; simp
      rw [Ne, allSome_eq_none] at hne
      cases hsig : (SC.fold (stepAlg L) s).sig with
      | none =>
          have hmem : (SC.fold (stepAlg L) s).sig ∈
              ((SC.kids c).map (SC.fold (stepAlg L))).map (·.sig) :=
            List.mem_map_of_mem (·.sig) (List.mem_map_of_mem (SC.fold (stepAlg L)) hs')
          exact absurd ⟨_, hmem, hsig⟩ hne
      | some r => exact ih s hs' r hsig

theorem rec_rt (hRT : LocalRT L) (c : C) (h : (SC.fold (stepAlg L) c).adm = false) :
    (SC.fold (stepAlg L) c).rho ≠ none := by
  intro hr
  have := (rec_rho_none_iff SC L hRT c).mp hr
  rw [h] at this
  cases this

theorem rec_rp (hRP : LocalRP L) (c : C) (h : (SC.fold (stepAlg L) c).adm = true) :
    (SC.fold (stepAlg L) c).sig ≠ none := by
  revert h
  refine SC.induction (P := fun c =>
    (SC.fold (stepAlg L) c).adm = true → (SC.fold (stepAlg L) c).sig ≠ none)
    (fun c ih => ?_) c
  intro h
  rw [SC.fold_eq (stepAlg L) c] at h ⊢
  rw [stepAlg_adm, Bool.and_eq_true, all_eq_true', forall_mem_map] at h
  rw [stepAlg_sig]
  have hall : allSome (((SC.kids c).map (SC.fold (stepAlg L))).map (·.sig)) ≠ none := by
    rw [Ne, allSome_eq_none]
    rintro ⟨x, hx, rfl⟩
    rw [List.map_map, List.mem_map] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    exact ih s hs (h.2 s hs) hsx
  cases hs : allSome (((SC.kids c).map (SC.fold (stepAlg L))).map (·.sig)) with
  | none => exact absurd hs hall
  | some reps =>
      simp only [Option.some_bind]
      exact hRP c _ reps h.1

/-- **A.** the local Tier-1 laws give the profile of the recursive model. -/
theorem recModel_profile (hq : QKids ST SC q) (hqf : LocalQF q L) (hAS : LocalAS L)
    (hRT : LocalRT L) (hRP : LocalRP L) : hasMSTNFProfile (recModel ST SC q L) :=
  ⟨fun r => rec_qf ST SC q L hq hqf r,
   fun c rep h => rec_as SC L hAS c rep h,
   fun c _ h => rec_rt SC L hRT c h,
   fun c _ h => rec_rp SC L hRP c h⟩

/-- exactness of the recursive model. -/
theorem recModel_rho_none_iff (hRT : LocalRT L) (c : C) :
    (recModel ST SC q L).rho c = none ↔ (recModel ST SC q L).admissible c = true :=
  rec_rho_none_iff SC L hRT c

/-- the node at a path of child indices. -/
def nodeAt (V : TreeSig C) : C → List Nat → Option C
  | c, [] => some c
  | c, i :: p => match (V.kids c).get? i with
    | some d => nodeAt V d p
    | none => none

theorem firstFail_some {α E : Type} (g : α → Option (List Nat × E)) :
    ∀ (l : List α) (i : Nat) (p : List Nat) (e : E),
      firstFail i (l.map g) = some (p, e) →
        ∃ j a p', p = (i + j) :: p' ∧ l.get? j = some a ∧ g a = some (p', e)
  | [], _, _, _, h => by simp [firstFail] at h
  | a :: l, i, p, e, h => by
      cases hg : g a with
      | none =>
          rw [List.map_cons, hg] at h
          simp only [firstFail] at h
          obtain ⟨j, b, p', hp, hb, hgb⟩ := firstFail_some g l (i + 1) p e h
          exact ⟨j + 1, b, p', by rw [hp]; congr 1; omega, by simpa using hb, hgb⟩
      | some x =>
          obtain ⟨p', e'⟩ := x
          rw [List.map_cons, hg] at h
          simp only [firstFail, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hp, he⟩ := h
          subst he
          exact ⟨0, a, p', by rw [← hp, Nat.add_zero], rfl, hg⟩

/-- the residue names a node: at its path sits a node whose local admission
    fails, with that local residue. -/
theorem recModel_rho_path (c : C) (p : List Nat) (e : L.LRes)
    (h : (recModel ST SC q L).rho c = some (p, e)) :
    ∃ d, nodeAt SC c p = some d ∧
      L.adm d (((SC.kids d).map (SC.fold (stepAlg L))).map (·.out)) = false ∧
      L.rho d (((SC.kids d).map (SC.fold (stepAlg L))).map (·.out)) = some e := by
  revert p
  refine SC.induction (P := fun c => ∀ p, (SC.fold (stepAlg L) c).rho = some (p, e) →
    ∃ d, nodeAt SC c p = some d ∧
      L.adm d (((SC.kids d).map (SC.fold (stepAlg L))).map (·.out)) = false ∧
      L.rho d (((SC.kids d).map (SC.fold (stepAlg L))).map (·.out)) = some e)
    (fun c ih => ?_) c
  intro p h
  rw [SC.fold_eq (stepAlg L) c, stepAlg_rho] at h
  cases hff : firstFail 0 (((SC.kids c).map (SC.fold (stepAlg L))).map (·.rho)) with
  | some x =>
      rw [hff] at h
      simp only [combineRho, Option.some.injEq] at h
      subst h
      rw [List.map_map] at hff
      obtain ⟨j, s, p', hp, hs, hgs⟩ := firstFail_some _ _ 0 p e hff
      have hmem : s ∈ SC.kids c := List.get?_mem hs
      obtain ⟨d, hd, had, hrd⟩ := ih s hmem p' hgs
      refine ⟨d, ?_, had, hrd⟩
      rw [hp, Nat.zero_add]
      simp only [nodeAt, hs]
      exact hd
  | none =>
      rw [hff] at h
      simp only [combineRho] at h
      cases ha : L.adm c (((SC.kids c).map (SC.fold (stepAlg L))).map (·.out)) with
      | true => rw [ha] at h; simp at h
      | false =>
          rw [ha] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hr : L.rho c (((SC.kids c).map (SC.fold (stepAlg L))).map (·.out)) with
          | none => rw [hr] at h; simp at h
          | some e' =>
              rw [hr] at h
              simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hp, he⟩ := h
              subst hp; subst he
              exact ⟨c, rfl, ha, hr⟩

end A

/-! ## B. Correctness under recursion -/

section B

variable (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
  (obs : M_B.Outcome → M_A.Outcome) (eqA : M_A.Outcome → M_A.Outcome → Bool)

/-- the square of a hop at a representative tree `r`: the translated
    program lands in B's admission and B's evaluation of it, observed, is the
    A-side meaning of `r`. -/
def Square (semA : M_A.Rep → M_A.Outcome) (r : M_A.Rep) : Prop :=
  M_B.admissible (M_B.q (T r)) = true ∧ obs (M_B.evalRaw (T r)) = semA r

/-- A's representatives mean what their class means. -/
def RepAdequate (semA : M_A.Rep → M_A.Outcome) : Prop :=
  ∀ c rep, M_A.sigma c = some rep → M_A.evalClass c = semA rep

/-- **B, fundamental-lemma form.** A relation `P` on a tree carrier `X`,
    closed under the local laws, whose value at the embedded representative
    gives the hop square, makes the hop correct. -/
theorem hopCorrect_of_rel {X : Type} (S : TreeSig X)
    (heqA : ∀ x y, eqA x y = true ↔ x = y)
    (hRP : representativePrecision M_A)
    (P : X → Prop) (hloc : ∀ x, (∀ y ∈ S.kids x, P y) → P x)
    (embed : M_A.Rep → X)
    (hroot : ∀ c rep, activeClass M_A c → M_A.admissible c = true →
      M_A.sigma c = some rep → P (embed rep) →
      M_B.admissible (M_B.q (T rep)) = true ∧
        obs (M_B.evalRaw (T rep)) = M_A.evalClass c) :
    hopCorrect M_A M_B T obs eqA := by
  unfold hopCorrect noResidueOn
  intro c hact ha
  have hsig := hRP c hact ha
  cases hs : M_A.sigma c with
  | none => exact absurd hs hsig
  | some rep =>
      obtain ⟨hadmB, heval⟩ := hroot c rep hact ha hs (S.induction hloc (embed rep))
      apply (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mpr
      simp only [hopModel, hs, hadmB, Bool.true_and]
      exact (heqA _ _).mpr heval

/-- **B.** the per-constructor square commutes at every node (local hop
    correctness), so the hop is correct as a whole. -/
theorem hopCorrect_of_localSquares (S : TreeSig M_A.Rep)
    (heqA : ∀ x y, eqA x y = true ↔ x = y)
    (hRP : representativePrecision M_A)
    (semA : M_A.Rep → M_A.Outcome) (hrep : RepAdequate M_A semA)
    (hloc : ∀ r, (∀ s ∈ S.kids r, Square M_A M_B T obs semA s) →
      Square M_A M_B T obs semA r) :
    hopCorrect M_A M_B T obs eqA :=
  hopCorrect_of_rel M_A M_B T obs eqA S heqA hRP (Square M_A M_B T obs semA) hloc id
    (fun c rep _ _ hs hsq => ⟨hsq.1, hsq.2.trans (hrep c rep hs).symm⟩)

/-- the per-form split: the local law, given per node form. -/
theorem local_of_forms {X F : Type} (S : TreeSig X) (form : X → F) (P : X → Prop)
    (hf : ∀ f x, form x = f → (∀ y ∈ S.kids x, P y) → P x) :
    ∀ x, (∀ y ∈ S.kids x, P y) → P x :=
  fun x => hf (form x) x rfl

/-- fold fusion for a hop: the observed B evaluation of the translation is
    the A meaning when B's evaluation of translated trees is compositional
    and the algebra square commutes. -/
theorem obs_eval_of_fusion (S : TreeSig M_A.Rep) (semA : M_A.Rep → M_A.Outcome)
    (algA : M_A.Rep → List M_A.Outcome → M_A.Outcome)
    (hsemA : ∀ r, semA r = algA r ((S.kids r).map semA))
    (algB : M_A.Rep → List M_B.Outcome → M_B.Outcome)
    (hevalB : ∀ r, M_B.evalRaw (T r) =
      algB r ((S.kids r).map (fun s => M_B.evalRaw (T s))))
    (hsq : ∀ r ys, obs (algB r ys) = algA r (ys.map obs)) (r : M_A.Rep) :
    obs (M_B.evalRaw (T r)) = semA r := by
  have h1 := S.eq_fold algB (fun s => M_B.evalRaw (T s)) hevalB r
  have h2 := S.eq_fold algA semA hsemA r
  rw [h1, h2]
  exact S.fold_fusion algB algA obs hsq r

/-- **B, algebra form (fold fusion).** -/
theorem hopCorrect_of_fusion (S : TreeSig M_A.Rep)
    (heqA : ∀ x y, eqA x y = true ↔ x = y)
    (hRP : representativePrecision M_A)
    (semA : M_A.Rep → M_A.Outcome) (hrep : RepAdequate M_A semA)
    (algA : M_A.Rep → List M_A.Outcome → M_A.Outcome)
    (hsemA : ∀ r, semA r = algA r ((S.kids r).map semA))
    (algB : M_A.Rep → List M_B.Outcome → M_B.Outcome)
    (hevalB : ∀ r, M_B.evalRaw (T r) =
      algB r ((S.kids r).map (fun s => M_B.evalRaw (T s))))
    (hsq : ∀ r ys, obs (algB r ys) = algA r (ys.map obs))
    (hadmB : ∀ r, (∀ s ∈ S.kids r, M_B.admissible (M_B.q (T s)) = true) →
      M_B.admissible (M_B.q (T r)) = true) :
    hopCorrect M_A M_B T obs eqA :=
  hopCorrect_of_localSquares M_A M_B T obs eqA S heqA hRP semA hrep (fun r ih =>
    ⟨hadmB r (fun s hs => (ih s hs).1),
     obs_eval_of_fusion M_A M_B T obs S semA algA hsemA algB hevalB hsq r⟩)

end B

/-! ## C. Step-indexed form -/

/-- induction over clocks and the tree: at clock `k` a node may use every
    node at a smaller clock and its children at clock `k`. -/
theorem TreeSig.step_induction {X : Type} (S : TreeSig X) {P : Nat → X → Prop}
    (hloc : ∀ k x, (∀ j < k, ∀ y, P j y) → (∀ y ∈ S.kids x, P k y) → P k x)
    (k : Nat) (x : X) : P k x := by
  suffices h : ∀ n, ∀ k, k < n → ∀ x, P k x from h (k + 1) k (Nat.lt_succ_self k) x
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ n ih =>
      intro k hk
      exact S.induction (P := P k) (fun x ihx => hloc k x (fun j hj y => ih j (by omega) y) ihx)

/-- **C.** the step-indexed fundamental lemma for a clocked hop. -/
theorem clockHopCorrect_of_stepRel {KB X : Type} (A : Clocked) (B : Fam KB)
    (T : A.Rep → B.Raw) (obs : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (lim : B.Outcome → Bool) (S : TreeSig X)
    (hRP : ∀ c, A.active c → A.admissible c = true → A.sigma c ≠ none)
    (P : Nat → X → Prop)
    (hloc : ∀ k x, (∀ j < k, ∀ y, P j y) → (∀ y ∈ S.kids x, P k y) → P k x)
    (embed : A.Rep → X)
    (hroot : ∀ c rep k, A.active c → A.admissible c = true → A.sigma c = some rep →
      P k (embed rep) → ∃ kB, B.admissible (B.q (T rep)) = true ∧
        (eqA (obs (B.runRaw kB (T rep))) (A.runClass k c) = true ∨
          lim (B.runRaw kB (T rep)) = true)) :
    clockHopCorrect A B T obs eqA lim := by
  intro c hact ha kA
  have hsig := hRP c hact ha
  cases hs : A.sigma c with
  | none => exact absurd hs hsig
  | some rep =>
      obtain ⟨kB, hadm, hv⟩ :=
        hroot c rep kA hact ha hs (S.step_induction hloc kA (embed rep))
      exact ⟨kB, (clock_resourceOk_iff A B T obs eqA lim kA kB c).mpr ⟨rep, hs, hadm, hv⟩⟩

/-! ## D. Necessity: one witness per hypothesis -/

namespace Necessity

noncomputable section

/-- a nested toy syntax: `add` has its children in a list. -/
inductive Tm where
  | lit (n : Nat)
  | add (args : List Tm)
  | neg (a : Tm)

inductive Form where
  | lit | add | neg
  deriving DecidableEq

def Tm.form : Tm → Form
  | .lit _ => .lit
  | .add _ => .add
  | .neg _ => .neg

def Tm.kids : Tm → List Tm
  | .lit _ => []
  | .add as => as
  | .neg a => [a]

def tmSig : TreeSig Tm where
  kids := Tm.kids
  size := sizeOf
  kids_lt := by
    intro t s h
    cases t with
    | lit n => simp [Tm.kids] at h
    | add as =>
        have := List.sizeOf_lt_of_mem (show s ∈ as from h)
        simp only [Tm.add.sizeOf_spec]
        omega
    | neg a =>
        simp only [Tm.kids, List.mem_singleton] at h
        subst h
        simp only [Tm.neg.sizeOf_spec]
        omega

def sumL : List Int → Int
  | [] => 0
  | y :: ys => y + sumL ys

/-- the toy meaning. -/
def algA : Tm → List Int → Int
  | .lit n, _ => n
  | .add _, ys => sumL ys
  | .neg _, ys => -(ys.headD 0)

/-- the meaning with form `f` misinterpreted. -/
def algBad (f : Form) : Tm → List Int → Int := fun r ys =>
  if r.form = f then
    match r with
    | .lit n => n + 1
    | .add _ => sumL ys + 1
    | .neg _ => ys.headD 0
  else algA r ys

def eqInt : Int → Int → Bool := fun x y => decide (x = y)

theorem eqInt_iff : ∀ x y, eqInt x y = true ↔ x = y := by
  intro x y; simp [eqInt]

/-- the A layer: classes and representatives are terms. -/
def layerA (sem : Tm → Int) (sig : Tm → Option Tm) : ExecModel where
  Raw := Tm
  Class := Tm
  Rep := Tm
  Residue := Unit
  Outcome := Int
  q := id
  evalRaw := sem
  evalClass := sem
  admissible := fun _ => true
  rho := fun _ => none
  sigma := sig

/-- the B layer: the same syntax under evaluator `ev` and admission `adm`. -/
def layerB (ev : Tm → Int) (adm : Tm → Bool) : ExecModel where
  Raw := Tm
  Class := Tm
  Rep := Tm
  Residue := Unit
  Outcome := Int
  q := id
  evalRaw := ev
  evalClass := ev
  admissible := adm
  rho := fun t => if adm t then none else some ()
  sigma := fun t => if adm t then some t else none

def semA : Tm → Int := tmSig.fold algA

abbrev A0 := layerA semA some
abbrev B0 := layerB semA (fun _ => true)
abbrev idT : Tm → Tm := id
abbrev idO : Int → Int := id

/-! ### the generic hypotheses, for the correct toy -/

theorem good_rp (sem : Tm → Int) : representativePrecision (layerA sem some) := by
  intro c _ _; simp [layerA]

theorem good_rep (sem : Tm → Int) : RepAdequate (layerA sem some) sem := by
  intro c rep h; simp only [layerA, Option.some.injEq] at h; subst h; rfl

theorem good_semA : ∀ r, semA r = algA r ((tmSig.kids r).map semA) :=
  tmSig.fold_eq algA

theorem good_evalB (alg : Tm → List Int → Int) (adm : Tm → Bool) :
    ∀ r, (layerB (tmSig.fold alg) adm).evalRaw (idT r) =
      alg r ((tmSig.kids r).map (fun s => (layerB (tmSig.fold alg) adm).evalRaw (idT s))) :=
  tmSig.fold_eq alg

theorem good_sq : ∀ r (ys : List Int), idO (algA r ys) = algA r (ys.map idO) := by
  intro r ys; simp [idO]

theorem good_admB (ev : Tm → Int) : ∀ r, (∀ s ∈ tmSig.kids r,
    (layerB ev (fun _ => true)).admissible ((layerB ev (fun _ => true)).q (idT s)) = true) →
    (layerB ev (fun _ => true)).admissible ((layerB ev (fun _ => true)).q (idT r)) = true :=
  fun _ _ => rfl

theorem correct_hop : hopCorrect A0 B0 idT idO eqInt :=
  hopCorrect_of_fusion A0 B0 idT idO eqInt tmSig eqInt_iff (good_rp semA) semA (good_rep semA)
    algA good_semA algA (good_evalB algA _) good_sq (good_admB semA)

/-- refuting `hopCorrect` at one class through the exactness reading. -/
theorem not_hopCorrect_at (MA MB : ExecModel) (T : MA.Rep → MB.Raw)
    (obs : MB.Outcome → MA.Outcome) (eqA : MA.Outcome → MA.Outcome → Bool)
    (c : MA.Class) (hact : activeClass MA c) (ha : MA.admissible c = true)
    (hno : (hopModel MA MB T obs eqA).admissible c = false) :
    ¬ hopCorrect MA MB T obs eqA := by
  intro h
  have := (hopCorrect_iff_exact MA MB T obs eqA).mp h c hact ha
  rw [hno] at this
  cases this

/-! ### B witnesses -/

/-- the per-constructor square, dropped at form `f`: every other form's
    square holds, `f`'s fails, and the hop is not correct. -/
theorem sq_other (f : Form) : ∀ r ys, r.form ≠ f → idO (algBad f r ys) = algA r (ys.map idO) := by
  intro r ys h; simp [algBad, h, idO]

def badTerm : Form → Tm
  | .lit => .lit 0
  | .add => .add []
  | .neg => .neg (.lit 1)

theorem sq_fails (f : Form) : idO (algBad f (badTerm f) ((tmSig.kids (badTerm f)).map semA)) ≠
    algA (badTerm f) (((tmSig.kids (badTerm f)).map semA).map idO) := by
  cases f <;> decide

theorem sq_needed (f : Form) :
    ¬ hopCorrect A0 (layerB (tmSig.fold (algBad f)) (fun _ => true)) idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (badTerm f) ⟨_, rfl⟩ rfl (by cases f <;> decide)

/-- B's admission, local law dropped at `neg`. -/
def admNoNeg : Tm → Bool := fun t => t.form != .neg

theorem admB_other : ∀ r, r.form ≠ .neg → (∀ s ∈ tmSig.kids r,
    (layerB semA admNoNeg).admissible ((layerB semA admNoNeg).q (idT s)) = true) →
    (layerB semA admNoNeg).admissible ((layerB semA admNoNeg).q (idT r)) = true := by
  intro r h _; simp [layerB, admNoNeg, h]

theorem admB_fails : ¬ ((∀ s ∈ tmSig.kids (.neg (.lit 1)),
    (layerB semA admNoNeg).admissible ((layerB semA admNoNeg).q (idT s)) = true) →
    (layerB semA admNoNeg).admissible ((layerB semA admNoNeg).q (idT (.neg (.lit 1)))) = true) := by
  decide

theorem admB_needed : ¬ hopCorrect A0 (layerB semA admNoNeg) idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (.neg (.lit 1)) ⟨_, rfl⟩ rfl (by decide)

/-- A's representative precision dropped: no representatives. -/
theorem rp_fails : ¬ representativePrecision (layerA semA (fun _ => none)) := by
  intro h; exact h (.lit 0) ⟨_, rfl⟩ rfl rfl

theorem rp_rep : RepAdequate (layerA semA (fun _ => none)) semA := by
  intro c rep h; cases h

theorem rp_needed : ¬ hopCorrect (layerA semA (fun _ => none)) B0 idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (.lit 0) ⟨_, rfl⟩ rfl (by decide)

/-- A's representative adequacy dropped: every class picks `lit 0`. -/
def sigZero : Tm → Option Tm := fun _ => some (.lit 0)

theorem rep_rp : representativePrecision (layerA semA sigZero) := by
  intro c _ _; simp [layerA, sigZero]

theorem rep_fails : ¬ RepAdequate (layerA semA sigZero) semA := by
  intro h
  have : semA (.lit 1) = semA (.lit 0) := h (.lit 1) (.lit 0) rfl
  revert this; decide

theorem rep_needed : ¬ hopCorrect (layerA semA sigZero) B0 idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (.lit 1) ⟨_, rfl⟩ rfl (by decide)

/-- the outcome equality dropped: `eqA` never holds. -/
def eqNever : Int → Int → Bool := fun _ _ => false

theorem eq_fails : ¬ (∀ x y, eqNever x y = true ↔ x = y) := by
  intro h; exact absurd ((h 0 0).mpr rfl) (by decide)

theorem eq_needed : ¬ hopCorrect A0 B0 idT idO eqNever :=
  not_hopCorrect_at _ _ _ _ _ (.lit 0) ⟨_, rfl⟩ rfl (by decide)

/-- A's meaning not the fold (`hsemA` dropped): `lit 0` means 7. -/
def semOdd : Tm → Int
  | .lit 0 => 7
  | t => semA t

theorem semA_fails : ¬ (∀ r, semOdd r = algA r ((tmSig.kids r).map semOdd)) := by
  intro h; have := h (.lit 0); revert this; decide

theorem semA_needed : ¬ hopCorrect (layerA semOdd some) B0 idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (.lit 0) ⟨_, rfl⟩ rfl (by decide)

/-- B's evaluation not compositional on translated trees (`hevalB` dropped). -/
def evOdd : Tm → Int
  | .neg (.lit 1) => 5
  | t => semA t

theorem evalB_fails : ¬ (∀ r, (layerB evOdd (fun _ => true)).evalRaw (idT r) =
    algA r ((tmSig.kids r).map (fun s => (layerB evOdd (fun _ => true)).evalRaw (idT s)))) := by
  intro h
  have : evOdd (.neg (.lit 1)) = algA (.neg (.lit 1)) ((tmSig.kids (.neg (.lit 1))).map evOdd) :=
    h (.neg (.lit 1))
  revert this; decide

theorem evalB_needed : ¬ hopCorrect A0 (layerB evOdd (fun _ => true)) idT idO eqInt :=
  not_hopCorrect_at _ _ _ _ _ (.neg (.lit 1)) ⟨_, rfl⟩ rfl (by decide)

/-! ### C witnesses -/

/-- a term has no `neg` node. -/
def noNeg : Tm → Bool := tmSig.fold (fun t bs => (t.form != .neg) && bs.all id)

theorem noNeg_eq (t : Tm) : noNeg t = ((t.form != .neg) && ((tmSig.kids t).map noNeg).all id) :=
  tmSig.fold_eq _ t

/-- the step-indexed local law, dropped at `neg`: it holds at every other
    form, fails at `neg`, and the conclusion fails. -/
theorem step_loc_other : ∀ (k : Nat) (x : Tm), x.form ≠ .neg →
    (∀ j < k, ∀ y, noNeg y = true) → (∀ y ∈ tmSig.kids x, noNeg y = true) → noNeg x = true := by
  intro _ x hx _ hk
  rw [noNeg_eq, Bool.and_eq_true, bne_iff_ne, all_eq_true', forall_mem_map]
  exact ⟨hx, hk⟩

theorem step_loc_fails : ¬ ((∀ j < 0, ∀ y, noNeg y = true) →
    (∀ y ∈ tmSig.kids (.neg (.lit 0)), noNeg y = true) → noNeg (.neg (.lit 0)) = true) := by
  intro h
  have h1 : noNeg (.neg (.lit 0)) = true := h (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun y hy => by
      simp only [tmSig, Tm.kids, List.mem_singleton] at hy
      subst hy
      rw [noNeg_eq]; rfl)
  revert h1; decide

theorem step_loc_needed : ¬ ∀ (k : Nat) (x : Tm), noNeg x = true := by
  intro h; have := h 0 (.neg (.lit 0)); revert this; decide

/-- A's representative precision dropped, clocked. -/
theorem step_rp_needed : ¬ clockHopCorrect (Fam.const (layerA semA (fun _ => none)) : Clocked)
    (Fam.const B0 : Clocked) idT idO eqInt (fun _ => false) :=
  fun h => rp_needed ((clock_const_iff _ _ _ _ _).mp h)

/-- the root adequacy dropped, clocked: with `P` true the local law holds,
    and a translation wrong at `lit` breaks the conclusion. -/
theorem step_root_needed :
    (∀ (k : Nat) (x : Tm), (∀ j < k, ∀ _ : Tm, True) → (∀ y ∈ tmSig.kids x, True) → True) ∧
    ¬ clockHopCorrect (Fam.const A0 : Clocked)
      (Fam.const (layerB (tmSig.fold (algBad .lit)) (fun _ => true)) : Clocked)
      idT idO eqInt (fun _ => false) :=
  ⟨fun _ _ _ _ => trivial, fun h => sq_needed .lit ((clock_const_iff _ _ _ _ _).mp h)⟩

/-- the outcome equality dropped, clocked. -/
theorem step_eq_needed : ¬ clockHopCorrect (Fam.const A0 : Clocked) (Fam.const B0 : Clocked)
    idT idO eqNever (fun _ => false) :=
  fun h => eq_needed ((clock_const_iff _ _ _ _ _).mp h)

/-! ### A witnesses: the recursive model on `Tm`, classes = terms -/

def stepOf (evalR evalC : Tm → List Nat → Nat) (adm : Tm → List Nat → Bool)
    (rho : Tm → List Nat → Option Unit) (sig : Tm → List Nat → List Unit → Option Unit) :
    LocalStep Tm Tm where
  Out := Nat
  Rep := Unit
  LRes := Unit
  evalR := evalR
  evalC := evalC
  adm := adm
  rho := rho
  sig := sig

/-- node count. -/
def countC : Tm → List Nat → Nat := fun _ outs => outs.foldr (· + ·) 1

def isNeg (t : Tm) : Bool := t.form == .neg

def okStep : LocalStep Tm Tm :=
  stepOf countC countC (fun _ _ => true) (fun _ _ => none) (fun _ _ _ => some ())

theorem qkids_id : QKids tmSig tmSig id := by intro t; simp
theorem ok_qf : LocalQF id okStep := fun _ _ => rfl
theorem ok_as : LocalAS okStep := fun _ _ _ _ _ => rfl
theorem ok_rt : LocalRT okStep := fun _ _ h => by simp [okStep, stepOf] at h
theorem ok_rp : LocalRP okStep := fun _ _ _ _ => by simp [okStep, stepOf]

theorem ok_profile : hasMSTNFProfile (recModel tmSig tmSig id okStep) :=
  recModel_profile tmSig tmSig id okStep qkids_id ok_qf ok_as ok_rt ok_rp

/-- QKids dropped at `neg`: `q` forgets the child of `neg`. -/
def qNeg : Tm → Tm
  | .neg _ => .lit 0
  | t => t

def qStep : LocalStep Tm Tm :=
  stepOf (fun t outs => countC (qNeg t) outs) countC (fun _ _ => true) (fun _ _ => none)
    (fun _ _ _ => some ())

theorem qkids_fails : ¬ QKids tmSig tmSig qNeg := by
  intro h
  have := congrArg List.length (h (.neg (.lit 0)))
  revert this; decide

theorem q_qf : LocalQF qNeg qStep := fun _ _ => rfl
theorem q_as : LocalAS qStep := fun _ _ _ _ _ => rfl
theorem q_rt : LocalRT qStep := fun _ _ h => by simp [qStep, stepOf] at h
theorem q_rp : LocalRP qStep := fun _ _ _ _ => by simp [qStep, stepOf]

theorem qkids_needed : ¬ hasMSTNFProfile (recModel tmSig tmSig qNeg qStep) := by
  intro h
  have h1 : tmSig.fold countC (Tm.neg (.lit 0)) =
      (tmSig.fold (stepAlg qStep) (qNeg (.neg (.lit 0)))).out := h.1 (.neg (.lit 0))
  revert h1; decide

/-- LocalQF dropped at `neg`: a raw `neg` node evaluates to 0. -/
def qfStep : LocalStep Tm Tm :=
  stepOf (fun t outs => if isNeg t then 0 else countC t outs) countC (fun _ _ => true)
    (fun _ _ => none) (fun _ _ _ => some ())

theorem qf_fails : ¬ LocalQF id qfStep := by
  intro h
  have : (if isNeg (Tm.neg (.lit 0)) then 0 else countC (Tm.neg (.lit 0)) [1]) =
      countC (Tm.neg (.lit 0)) [1] := h (.neg (.lit 0)) ([1] : List Nat)
  revert this; decide

theorem qf_as : LocalAS qfStep := fun _ _ _ _ _ => rfl
theorem qf_rt : LocalRT qfStep := fun _ _ h => by simp [qfStep, stepOf] at h
theorem qf_rp : LocalRP qfStep := fun _ _ _ _ => by simp [qfStep, stepOf]

theorem qf_needed : ¬ hasMSTNFProfile (recModel tmSig tmSig id qfStep) := by
  intro h
  have h1 : tmSig.fold (fun t outs => if isNeg t then 0 else countC t outs) (Tm.neg (.lit 0)) =
      (tmSig.fold (stepAlg qfStep) (Tm.neg (.lit 0))).out := h.1 (.neg (.lit 0))
  revert h1; decide

/-- LocalAS dropped at `neg`: `neg` refused but given a representative. -/
def asStep : LocalStep Tm Tm :=
  stepOf countC countC (fun t _ => !isNeg t) (fun t _ => if isNeg t then some () else none)
    (fun _ _ _ => some ())

theorem as_fails : ¬ LocalAS asStep := by
  intro h; have := h (.neg (.lit 0)) [] [] () rfl; revert this; decide

theorem as_qf : LocalQF id asStep := fun _ _ => rfl
theorem as_rt : LocalRT asStep := by
  intro c outs h; cases c <;> simp_all [asStep, stepOf, isNeg, Tm.form]
theorem as_rp : LocalRP asStep := fun _ _ _ _ => by simp [asStep, stepOf]

theorem as_needed : ¬ hasMSTNFProfile (recModel tmSig tmSig id asStep) := by
  intro h
  have hs : (tmSig.fold (stepAlg asStep) (Tm.neg (.lit 0))).sig = some () := by rfl
  have := h.2.1 (Tm.neg (.lit 0)) () hs
  have h1 : (tmSig.fold (stepAlg asStep) (Tm.neg (.lit 0))).adm = true := this
  revert h1; decide

/-- LocalRT dropped at `neg`: `neg` refused with no residue. -/
def rtStep : LocalStep Tm Tm :=
  stepOf countC countC (fun t _ => !isNeg t) (fun _ _ => none)
    (fun t _ _ => if isNeg t then none else some ())

theorem rt_fails : ¬ LocalRT rtStep := by
  intro h; exact h (.neg (.lit 0)) [] rfl rfl

theorem rt_qf : LocalQF id rtStep := fun _ _ => rfl
theorem rt_as : LocalAS rtStep := by
  intro c outs reps rep h; cases c <;> simp_all [rtStep, stepOf, isNeg, Tm.form]
theorem rt_rp : LocalRP rtStep := by
  intro c outs reps h; cases c <;> simp_all [rtStep, stepOf, isNeg, Tm.form]

theorem rt_needed : ¬ hasMSTNFProfile (recModel tmSig tmSig id rtStep) := by
  intro h
  have ha : (tmSig.fold (stepAlg rtStep) (Tm.neg (.lit 0))).adm = false := by decide
  have hr : (tmSig.fold (stepAlg rtStep) (Tm.neg (.lit 0))).rho = none := by rfl
  exact h.2.2.1 (Tm.neg (.lit 0)) ⟨_, rfl⟩ ha hr

/-- LocalRP dropped at `neg`: `neg` admitted with no representative. -/
def rpStep : LocalStep Tm Tm :=
  stepOf countC countC (fun _ _ => true) (fun _ _ => none)
    (fun t _ _ => if isNeg t then none else some ())

theorem rp_fails' : ¬ LocalRP rpStep := by
  intro h; exact h (.neg (.lit 0)) [] [] rfl rfl

theorem rp_qf : LocalQF id rpStep := fun _ _ => rfl
theorem rp_as : LocalAS rpStep := fun _ _ _ _ _ => rfl
theorem rp_rt : LocalRT rpStep := fun _ _ h => by simp [rpStep, stepOf] at h

theorem rp_needed' : ¬ hasMSTNFProfile (recModel tmSig tmSig id rpStep) := by
  intro h
  have ha : (tmSig.fold (stepAlg rpStep) (Tm.neg (.lit 0))).adm = true := by decide
  have hs : (tmSig.fold (stepAlg rpStep) (Tm.neg (.lit 0))).sig = none := by rfl
  exact h.2.2.2 (Tm.neg (.lit 0)) ⟨_, rfl⟩ ha hs

/-- the rho path on a concrete tree: `add [lit 0, neg (lit 0)]` under
    `rtStep`'s admission with a residue fails at path `[1]`. -/
def pathStep : LocalStep Tm Tm :=
  stepOf countC countC (fun t _ => !isNeg t) (fun t _ => if isNeg t then some () else none)
    (fun t _ _ => if isNeg t then none else some ())

theorem path_rho :
    (tmSig.fold (stepAlg pathStep) (Tm.add [.lit 0, .neg (.lit 0)])).rho = some ([1], ()) := by
  rfl

end

end Necessity

end NfCompose.Rec

#print axioms NfCompose.Rec.TreeSig.induction
#print axioms NfCompose.Rec.TreeSig.fold_eq
#print axioms NfCompose.Rec.TreeSig.eq_fold
#print axioms NfCompose.Rec.TreeSig.fold_fusion
#print axioms NfCompose.Rec.recModel_profile
#print axioms NfCompose.Rec.recModel_rho_none_iff
#print axioms NfCompose.Rec.recModel_rho_path
#print axioms NfCompose.Rec.hopCorrect_of_rel
#print axioms NfCompose.Rec.hopCorrect_of_localSquares
#print axioms NfCompose.Rec.hopCorrect_of_fusion
#print axioms NfCompose.Rec.TreeSig.step_induction
#print axioms NfCompose.Rec.clockHopCorrect_of_stepRel
#print axioms NfCompose.Rec.Necessity.step_loc_needed
#print axioms NfCompose.Rec.Necessity.step_loc_fails
#print axioms NfCompose.Rec.Necessity.step_rp_needed
#print axioms NfCompose.Rec.Necessity.step_root_needed
#print axioms NfCompose.Rec.Necessity.step_eq_needed
#print axioms NfCompose.Rec.Necessity.correct_hop
#print axioms NfCompose.Rec.Necessity.ok_profile
#print axioms NfCompose.Rec.Necessity.sq_needed
#print axioms NfCompose.Rec.Necessity.admB_needed
#print axioms NfCompose.Rec.Necessity.rp_needed
#print axioms NfCompose.Rec.Necessity.rep_needed
#print axioms NfCompose.Rec.Necessity.eq_needed
#print axioms NfCompose.Rec.Necessity.semA_needed
#print axioms NfCompose.Rec.Necessity.evalB_needed
#print axioms NfCompose.Rec.Necessity.qkids_needed
#print axioms NfCompose.Rec.Necessity.qf_needed
#print axioms NfCompose.Rec.Necessity.as_needed
#print axioms NfCompose.Rec.Necessity.rt_needed
#print axioms NfCompose.Rec.Necessity.rp_needed'
#print axioms NfCompose.Rec.Necessity.path_rho
