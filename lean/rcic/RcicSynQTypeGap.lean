import rcic.RcicSynRegStep
import rcic.RcicSynInst

/-!
# Syntactic sortRow, S19 — the qType MixedCL step under the lookup gap

`research/rcic/sortrow/S19_QTYPE_MIXED_CL.md` (#7412) §1–§3.

Setup (§1): `Σ[j]? = some (assumption t)` (or `letBinding t v`), `Γ = substRemove v j Σ`,
`a = lift 0 j v`, `T = lift 0 j t`, `U = lift 0 (j+1) t`; `G : TyP E n Σ U (sort w)`,
`V : TyP E n Γ a T`, `W : TyP E n Γ T (sort s)`. The qType request is a `MixedCL`
comparison between `τ-view(G)` and `target-view(W)` whose goal is
`τ-view(G).ε₊ ↔ W.ε₊`. The kernel of this module is:

- `qType_subject_eq` — `instantiate j a U = T`, straight from `instantiate_lift_cancel`.
- `qType_outer_hole_absent` / `qType_under_binder_hole_absent` — the deleted slot `j`
  (tracked as `j + d` at binder depth `d`) never occurs in `U`; every free bvar of
  `U` is above the hole. Forward lift facts only — no inverse weakening.
- `qType_bvar_above_hole` — if `U`'s root is a bvar it is `bvar (j+1+k)` and `T`'s
  root is `bvar (j+k)`.

§3 real fixture: `Σ = [x : T]`, `T = pi S₀ S₀`, `Γ = []`, `G` wt 3 (a `pi` node over
two direct sort fields), `V = λP:S₀. P` wt 5, `W` wt 8 (a `pi` node whose domain
carries the six-node `.conv`-over-`.refl` sort typing, `S₀ : S₁` by conversion).
The original qType table `at(G) ++ at(V) ++ at(W)` computes to `[3,5,8]`; the three
controls are bound to the real tables: `[3,5,8] → [5,8]` (PB-first keeps `V`,`W`),
`[3,5,8] → [1,5,6]` (reading both Π domains pays `G.hA`'s `1` under `3` and
`W.hA`'s `6` under `8`, keeping `V`'s `5`), and `¬ DMStep [1,5,8,6] [3,5,8]` —
keeping `W`'s `8` while additionally reading its `6` cannot be paid. The esub/let
twins at cutoff 0 give the AP inputs (`[4,5,8]` moved rows).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the deleted slot never occurs in the qType subject -/

/-- Occurrence of the tracked slot `j` inside `e`, seen at binder depth `d`:
a `.bvar (j + d)` at depth `d` is a free occurrence of outer slot `j`
(indices `m < d` are bound inside `e` and cannot equal `j + d`).
Under each original binder `d` increments, so the deleted slot tracks to `j + d`. -/
def holeOccursAt (j d : Nat) : Expr Nat → Prop
  | .bvar m => m = j + d
  | .app f x => holeOccursAt j d f ∨ holeOccursAt j d x
  | .lam A b => holeOccursAt j d A ∨ holeOccursAt j (d + 1) b
  | .pi A b => holeOccursAt j d A ∨ holeOccursAt j (d + 1) b
  | .letE A v b => holeOccursAt j d A ∨ holeOccursAt j d v ∨ holeOccursAt j (d + 1) b
  | .sort _ | .const _ _ | .lit _ => False

/-- the forward gap fact: `lift (c + d) a` never produces `.bvar (j + d)` when
`j` lies inside the shifted range `c … c+a` — the inserted `a` variables open
exactly that gap at every depth. No inverse weakening is used or needed. -/
theorem lift_hole_absent {c j a : Nat} (hc : c ≤ j) (hj : j < a + c) :
    ∀ {d : Nat} {t : Expr Nat}, ¬ holeOccursAt j d (lift (c + d) a t) := by
  intro d t
  induction t generalizing d with
  | bvar m =>
      simp only [lift]
      split
      · intro h
        simp only [holeOccursAt] at h
        omega
      · intro h
        simp only [holeOccursAt] at h
        omega
  | sort l => exact fun h => h
  | const r ls => exact fun h => h
  | app f x ihf ihx =>
      simp only [lift, holeOccursAt]
      rintro (h | h)
      · exact ihf h
      · exact ihx h
  | lam A b ihA ihb =>
      simp only [lift, holeOccursAt]
      rintro (h | h)
      · exact ihA h
      · exact ihb h
  | pi A b ihA ihb =>
      simp only [lift, holeOccursAt]
      rintro (h | h)
      · exact ihA h
      · exact ihb h
  | letE A v b ihA ihv ihb =>
      simp only [lift, holeOccursAt]
      rintro (h | h | h)
      · exact ihA h
      · exact ihv h
      · exact ihb h
  | lit n => exact fun h => h

/-- §1: instantiating the lookup type `U` at the deleted slot cancels the `+1`
lift — `instantiate j a U = T` — the forward `instantiate_lift_cancel` step. -/
theorem qType_subject_eq (j : Nat) (v t : Expr Nat) :
    instantiate j (lift 0 j v) (lift 0 (j + 1) t) = lift 0 j t :=
  instantiate_lift_cancel (j + 1) 0 j (lift 0 j v) (Nat.zero_le j) (by omega) t

/-- §1: no free variable of `U = lift 0 (j+1) t` lies in `0…j` — every free
bvar of `U` is above the hole, so the deleted slot cannot occur in it. -/
theorem qType_outer_hole_absent {j i : Nat} {t : Expr Nat} (hi : i ≤ j) :
    ¬ holeOccursAt i 0 (lift 0 (j + 1) t) :=
  lift_hole_absent (Nat.zero_le i) (Nat.lt_succ_of_le hi)

/-- §1: if `U`'s root is a bvar it lies above the hole — `U = bvar (j+1+k)` —
and `T`'s root is the same bvar shifted down one, `T = bvar (j+k)`. -/
theorem qType_bvar_above_hole {j i : Nat} {t : Expr Nat}
    (h : lift 0 (j + 1) t = .bvar i) :
    ∃ k, i = j + 1 + k ∧ lift 0 j t = .bvar (j + k) := by
  cases t with
  | bvar m =>
      simp only [lift, Nat.zero_le, ↓reduceIte] at h ⊢
      obtain rfl : m + (j + 1) = i := by injection h
      exact ⟨m, by omega, congrArg _ (Nat.add_comm m j)⟩
  | sort l => exact absurd h (by simp [lift])
  | const r ls => exact absurd h (by simp [lift])
  | app f x => exact absurd h (by simp [lift])
  | lam A B => exact absurd h (by simp [lift])
  | pi A B => exact absurd h (by simp [lift])
  | letE A v b => exact absurd h (by simp [lift])
  | lit n => exact absurd h (by simp [lift])

/-- §1: the same constraint tracked by binder depth — under `d` original
binders the deleted slot is `j + d`, and inside `U`'s depth-`d` subterm
`lift d (j+1) t` no free bvar lies in `d … j+d`. -/
theorem qType_under_binder_hole_absent {j d i : Nat} {t : Expr Nat} (hi : i ≤ j) :
    ¬ holeOccursAt i d (lift d (j + 1) t) := by
  have h := lift_hole_absent (Nat.zero_le i) (Nat.lt_succ_of_le hi) (d := d) (t := t)
  rwa [Nat.zero_add] at h

/-! ## §3 the real fixture `Σ = [x : T]`, `T = pi S₀ S₀`, `Γ = []` -/

private abbrev l0 : Level := .zero
private abbrev l1 : Level := .succ .zero
private abbrev l2 : Level := .succ (.succ .zero)
private abbrev s0 : Expr Nat := .sort l0
private abbrev s1 : Expr Nat := .sort l1
private abbrev s2 : Expr Nat := .sort l2
private abbrev s19T : Expr Nat := .pi s0 s0
private abbrev s19v : Expr Nat := .lam s0 (.bvar 0)

/-- `Σ = [x : T]` — the esub source. -/
def s19Src : LCtx := [.assumption s19T]
/-- `Σ = [x := V : T]` — the lsub source. -/
def s19SrcLet : LCtx := [.letBinding s19T s19v]
/-- `Γ = []` — `substRemove v 0` of either source. -/
def s19Tgt : LCtx := []

/-- a direct `S₀ : S₁` sort typing in `Γ'` (the fixture's wt-1 fields). -/
def s19s0 (Γ : LCtx) : TyP emptyEnv 0 Γ s0 s1 :=
  .sort _ _ _ l0 l1 (eqN_refl _)

/-- `G`'s Π domain field: `S₀ : S₁` in `Σ`, wt 1. -/
def s19GhA : TyP emptyEnv 0 s19Src s0 s1 := s19s0 s19Src
/-- `G`'s Π body field: `S₀ : S₁` under the `S₀` binder, wt 1. -/
def s19GhB : TyP emptyEnv 0 (.assumption s0 :: s19Src) s0 s1 :=
  s19s0 (.assumption s0 :: s19Src)
/-- `G : T : sort (imax 1 1)` in `Σ` — the `pi` node, wt `1 + 1 + 1 = 3`. -/
def s19G : TyP emptyEnv 0 s19Src s19T (.sort (.imax l1 l1)) :=
  .pi _ _ _ s0 l1 s0 l1 s19GhA s19GhB
/-- the let twin's `G` over `Σ_let` — same shape, wt 3. -/
def s19Glet : TyP emptyEnv 0 s19SrcLet s19T (.sort (.imax l1 l1)) :=
  .pi _ _ _ s0 l1 s0 l1 (s19s0 s19SrcLet) (s19s0 (.assumption s0 :: s19SrcLet))

/-- `V`'s domain field: `S₀ : S₁` in `Γ = []`, wt 1. -/
def s19Vdom : TyP emptyEnv 0 s19Tgt s0 s1 := s19s0 s19Tgt
/-- `V`'s body-type field: `S₀ : S₁` under the `S₀` binder, wt 1. -/
def s19VbodyTy : TyP emptyEnv 0 [.assumption s0] s0 s1 := s19s0 [.assumption s0]
/-- `P = bvar 0 : S₀` under the binder — `bvar` node, wt `1 + 1 = 2`. -/
def s19Vbody : TyP emptyEnv 0 [.assumption s0] (.bvar 0) s0 :=
  .bvar _ _ _ 0 s0 l1 rfl s19VbodyTy
/-- `V = λP:S₀. P : T` in `Γ` — `lam` node, wt `1 + 1 + 2 + 1 = 5`. -/
def s19V : TyP emptyEnv 0 s19Tgt s19v s19T :=
  .lam _ _ _ s0 l1 (.bvar 0) s0 l1 s19Vdom s19Vbody s19VbodyTy

/-- the level-`S₁ : S₂` typing feeding `W`'s heavy domain, wt 1. -/
def s19WdomS2 : TyP emptyEnv 0 s19Tgt s1 s2 := .sort _ _ _ l1 l2 (eqN_refl _)
/-- `W`'s six-node heavy Π domain typing: `S₀ : S₁` by `.conv` over `.refl`
(S17's shape), wt `1 + 1 + (1 + 1 + 1 + 1) = 6`. -/
def s19Wdom : TyP emptyEnv 0 s19Tgt s0 s1 :=
  .conv _ _ _ s0 s1 s1 l2 (s19s0 s19Tgt)
    (.refl _ _ _ s1 s2 s19WdomS2 s19WdomS2 s19WdomS2)
/-- `W`'s Π body field: `S₀ : S₁` under the binder, wt 1. -/
def s19Wbody : TyP emptyEnv 0 [.assumption s0] s0 s1 := s19s0 [.assumption s0]
/-- `W : T : sort (imax 1 1)` in `Γ` — `pi` node, wt `1 + 6 + 1 = 8`. -/
def s19W : TyP emptyEnv 0 s19Tgt s19T (.sort (.imax l1 l1)) :=
  .pi _ _ _ s0 l1 s0 l1 s19Wdom s19Wbody

/-- `x`'s typing in the esub source: `bvar 0 : T`, wt `1 + 3 = 4`. -/
def s19D : TyP emptyEnv 0 s19Src (.bvar 0) s19T :=
  .bvar _ _ _ 0 s19T (.imax l1 l1) rfl s19G
/-- `x`'s typing in the lsub source — same shape, wt 4. -/
def s19Dlet : TyP emptyEnv 0 s19SrcLet (.bvar 0) s19T :=
  .bvar _ _ _ 0 s19T (.imax l1 l1) rfl s19Glet
/-- the esub AP input at cutoff 0: `esub D hget V W : TyP [] V T`. -/
def s19HEs : TyP emptyEnv 0 s19Tgt s19v s19T :=
  .esub _ _ _ _ _ s19T s19v 0 (.imax l1 l1) s19D rfl s19V s19W
/-- the lsub AP input at cutoff 0: `lsub D hget V W : TyP [] V T`. -/
def s19HLs : TyP emptyEnv 0 s19Tgt s19v s19T :=
  .lsub _ _ _ _ _ s19T s19v 0 (.imax l1 l1) s19Dlet rfl s19V s19W

/-! ### §3 kernel pins: the fixture's weights and atom tables compute literally -/

theorem s19G_wt (Aw : Nat → Nat) : s19G.wt Aw = 3 := rfl
theorem s19V_wt (Aw : Nat → Nat) : s19V.wt Aw = 5 := rfl
theorem s19W_wt (Aw : Nat → Nat) : s19W.wt Aw = 8 := rfl
theorem s19GhA_wt (Aw : Nat → Nat) : s19GhA.wt Aw = 1 := rfl
theorem s19Wdom_wt (Aw : Nat → Nat) : s19Wdom.wt Aw = 6 := rfl

/-- the original qType table `at(G) ++ at(V) ++ at(W)` on the real fixture. -/
theorem s19qType_atoms (Aw : Nat → Nat) :
    s19G.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw = [3, 5, 8] := rfl
/-- the moved esub row `at(D) ++ at(V) ++ at(W)`. -/
theorem s19HEs_atoms (Aw : Nat → Nat) : s19HEs.atoms Aw = [4, 5, 8] := rfl
/-- the moved lsub row. -/
theorem s19HLs_atoms (Aw : Nat → Nat) : s19HLs.atoms Aw = [4, 5, 8] := rfl

/-- the PB-first table `at(V) ++ at(W)`. -/
theorem s19qPrep_table (Aw : Nat → Nat) :
    s19V.atoms Aw ++ s19W.atoms Aw = [5, 8] := rfl
/-- the both-domains table `at(G.hA) ++ at(V) ++ at(W.hA)` — reads `G.hA`'s `1`
under `G`'s `3` and `W.hA`'s `6` under `W`'s `8`. -/
theorem s19qDom_table (Aw : Nat → Nat) :
    s19GhA.atoms Aw ++ s19V.atoms Aw ++ s19Wdom.atoms Aw = [1, 5, 6] := rfl
/-- the overspending inventory `at(G.hA) ++ at(V) ++ at(W) ++ at(W.hA)` —
keeps `W`'s `8` while additionally reading its `6`. -/
theorem s19qOver_table (Aw : Nat → Nat) :
    s19GhA.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw ++ s19Wdom.atoms Aw
      = [1, 5, 8, 6] := rfl

/-! ### §3 the three controls -/

/-- §3(a): finish the replacement PB-first — `[3,5,8] → [5,8]` drops `G`'s
atom, keeping `V`'s `5` and `W`'s `8`. -/
theorem s19qPrep_dm : DMStep [5, 8] [3, 5, 8] :=
  dmStep_drop (X := [3]) (Z := [5, 8]) (List.cons_ne_nil _ _)

/-- §3(b): the right request reads both Π domains — `[3,5,8] → [1,5,6]` is
strict: `G.hA`'s `1` pays under `G`'s `3`, `W.hA`'s `6` pays under `W`'s `8`,
`V`'s `5` is kept. -/
theorem s19qDom_dm : DMStep [1, 5, 6] [3, 5, 8] :=
  ⟨[3, 8], [1, 6], [5], List.cons_ne_nil _ _,
    List.Perm.cons 3 (List.perm_append_comm (l₁ := [5]) (l₂ := [8])),
    List.Perm.cons 1 (List.perm_append_comm (l₁ := [5]) (l₂ := [6])),
    fun y hy => by
      rcases List.mem_cons.mp hy with h | h
      · subst h; exact ⟨3, by decide, by decide⟩
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact ⟨8, by decide, by decide⟩
        · exact absurd h (List.not_mem_nil _)⟩

/-- §3(c): the wrong implementation keeping `W`'s `8` while additionally
reading its `6` does not descend — `X` can spend `8` either on `6` or on `8`,
never both, and `M` has only one `8`. -/
theorem s19qOver_not_dm : ¬ DMStep [1, 5, 8, 6] [3, 5, 8] := by
  rintro ⟨X, Y, Z, _, hM, hM', hdom⟩
  have h6Y : 6 ∈ Y := by
    have h1 : List.count 6 (X ++ Z) = 0 := hM.symm.count_eq 6
    rw [List.count_append] at h1
    have h2 : List.count 6 (Y ++ Z) = 1 := hM'.symm.count_eq 6
    rw [List.count_append] at h2
    exact List.count_pos_iff.mp (by omega)
  obtain ⟨x, hxX, hlt⟩ := hdom 6 h6Y
  have hxM : x ∈ [3, 5, 8] := (List.Perm.mem_iff hM).mpr (List.mem_append_left Z hxX)
  have hx8 : x = 8 := by
    rcases List.mem_cons.mp hxM with h | h
    · omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exact absurd h (List.not_mem_nil _)
  have h8X : 8 ∈ X := hx8 ▸ hxX
  have h8Z : List.count 8 Z = 0 := by
    have h1 : List.count 8 (X ++ Z) = 1 := hM.symm.count_eq 8
    rw [List.count_append] at h1
    have hc : 0 < List.count 8 X := List.count_pos_iff.mpr h8X
    omega
  have h8Y : 8 ∈ Y := by
    have h2 : List.count 8 (Y ++ Z) = 1 := hM'.symm.count_eq 8
    rw [List.count_append, h8Z] at h2
    exact List.count_pos_iff.mp (by omega)
  obtain ⟨x', hx'X, hlt'⟩ := hdom 8 h8Y
  have hx'M : x' ∈ [3, 5, 8] := (List.Perm.mem_iff hM).mpr (List.mem_append_left Z hx'X)
  rcases List.mem_cons.mp hx'M with h | h
  · omega
  · rcases List.mem_cons.mp h with h | h
    · omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · exact absurd h (List.not_mem_nil _)

/-- §2's qPrep edge at a general kept caller prefix `K`: deleting the nonempty
`at(G)` block while keeping `K` and the `at(V) ++ at(W)` tail is a DMStep. -/
theorem s19qPrep_dm_K (Aw : Nat → Nat) (K : List Nat) :
    DMStep (K ++ s19V.atoms Aw ++ s19W.atoms Aw)
      (K ++ s19G.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw) := by
  have hG : s19G.atoms Aw = [3] := rfl
  have hV : s19V.atoms Aw = [5] := rfl
  have hW : s19W.atoms Aw = [8] := rfl
  rw [hG, hV, hW]
  refine ⟨[3], [], K ++ [5] ++ [8], List.cons_ne_nil _ _, ?_,
    List.Perm.refl _, fun y hy => absurd hy (List.not_mem_nil _)⟩
  simp only [List.append_assoc]
  exact List.perm_middle (l₁ := K) (a := 3) (l₂ := [5] ++ [8])

/-- §3(a) bound to the real tables: `at(V) ++ at(W)` descends from
`at(G) ++ at(V) ++ at(W)`. -/
theorem s19qPrep_dm_bound (Aw : Nat → Nat) :
    DMStep (s19V.atoms Aw ++ s19W.atoms Aw)
      (s19G.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw) :=
  s19qPrep_dm

/-- §3(b) bound to the real tables: `at(G.hA) ++ at(V) ++ at(W.hA)` descends
from `at(G) ++ at(V) ++ at(W)`. -/
theorem s19qDom_dm_bound (Aw : Nat → Nat) :
    DMStep (s19GhA.atoms Aw ++ s19V.atoms Aw ++ s19Wdom.atoms Aw)
      (s19G.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw) :=
  s19qDom_dm

/-- §3(c) bound to the real overspending inventory. -/
theorem s19qOver_not_dm_bound (Aw : Nat → Nat) :
    ¬ DMStep (s19GhA.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw ++ s19Wdom.atoms Aw)
      (s19G.atoms Aw ++ s19V.atoms Aw ++ s19W.atoms Aw) :=
  s19qOver_not_dm

/-- the overspend also fails inside `LexDM` — the same `DMStep` argument at
its left coordinate. -/
theorem s19qOver_not_lex {k k' : Nat} :
    ¬ LexDM ([1, 5, 8, 6], k) ([3, 5, 8], k') := by
  intro h
  cases h with
  | left _ _ hdm => exact s19qOver_not_dm hdm

end Rcic.Syn

#print axioms Rcic.Syn.holeOccursAt
#print axioms Rcic.Syn.lift_hole_absent
#print axioms Rcic.Syn.qType_subject_eq
#print axioms Rcic.Syn.qType_outer_hole_absent
#print axioms Rcic.Syn.qType_bvar_above_hole
#print axioms Rcic.Syn.qType_under_binder_hole_absent
#print axioms Rcic.Syn.s19Src
#print axioms Rcic.Syn.s19SrcLet
#print axioms Rcic.Syn.s19Tgt
#print axioms Rcic.Syn.s19s0
#print axioms Rcic.Syn.s19GhA
#print axioms Rcic.Syn.s19GhB
#print axioms Rcic.Syn.s19G
#print axioms Rcic.Syn.s19Glet
#print axioms Rcic.Syn.s19Vdom
#print axioms Rcic.Syn.s19VbodyTy
#print axioms Rcic.Syn.s19Vbody
#print axioms Rcic.Syn.s19V
#print axioms Rcic.Syn.s19WdomS2
#print axioms Rcic.Syn.s19Wdom
#print axioms Rcic.Syn.s19Wbody
#print axioms Rcic.Syn.s19W
#print axioms Rcic.Syn.s19D
#print axioms Rcic.Syn.s19Dlet
#print axioms Rcic.Syn.s19HEs
#print axioms Rcic.Syn.s19HLs
#print axioms Rcic.Syn.s19G_wt
#print axioms Rcic.Syn.s19V_wt
#print axioms Rcic.Syn.s19W_wt
#print axioms Rcic.Syn.s19GhA_wt
#print axioms Rcic.Syn.s19Wdom_wt
#print axioms Rcic.Syn.s19qType_atoms
#print axioms Rcic.Syn.s19HEs_atoms
#print axioms Rcic.Syn.s19HLs_atoms
#print axioms Rcic.Syn.s19qPrep_table
#print axioms Rcic.Syn.s19qDom_table
#print axioms Rcic.Syn.s19qOver_table
#print axioms Rcic.Syn.s19qPrep_dm
#print axioms Rcic.Syn.s19qDom_dm
#print axioms Rcic.Syn.s19qOver_not_dm
#print axioms Rcic.Syn.s19qPrep_dm_K
#print axioms Rcic.Syn.s19qPrep_dm_bound
#print axioms Rcic.Syn.s19qDom_dm_bound
#print axioms Rcic.Syn.s19qOver_not_dm_bound
#print axioms Rcic.Syn.s19qOver_not_lex
