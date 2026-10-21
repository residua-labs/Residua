import rcic.RcicSynSubst

/-!
# ER1 repair, batch R1 — `piSlot`, the proof-domain Π codomain placeholder

`research/rcic/sortrow/S12_ER1_REPAIR.md` §1–2 (option (a); design in PR #7364), driven by
the kernel-checked counterexample of `RcicERPiDropWk` (#7362): `TyP.eps`'s Π clause emits
an `ETm.pi` binder, yet the proof-domain codomain erases at `.drop :: ρ` — no slot — so an
outer `wk` lift shifts the stale codomain index (`Dw.eps = pi (bvar 1) (bvar 0)` against
the direct `pi (bvar 1) (bvar 1)`).

Option (a) keeps `ETm.pi`'s single-slot binding and pads only the proof-domain codomain:
`piSlot true q = q.lift 0 1`. The λ/let drop branches produce no erased binder and take
no pad (S12 §4–5). The R2 semantic switch of `TyP.eps.pi` consumes this module, so it is
kept strictly below `RcicSynErase` in the cone (`RcicSynSubst` only). The `ConvMod`
pad/unpad lemmas, which need `TableClosed` and therefore `RcicSynES`, live in
`RcicERPiSlotConv`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The pad: `true` marks a proof-domain Π codomain — the erased Π still binds one slot,
    so the codomain body is lifted once at cutoff 0. `false` leaves the term untouched:
    relevant-domain codomains really use the binder. -/
def piSlot : Bool → ETm → ETm
  | true, q => q.lift 0 1
  | false, q => q

/-- `d(b)` of S12 §2: the cutoff offset `piSlot b` introduces under an outer binder. The
    pad itself occupies the slot at `true` (offset 0); at `false` the Π binder still
    consumes one (offset 1). -/
def piSlotD : Bool → Nat
  | true => 0
  | false => 1

theorem piSlot_true (q : ETm) : piSlot true q = q.lift 0 1 := rfl

theorem piSlot_false (q : ETm) : piSlot false q = q := rfl

/-- Lift exchange (S12 §2): `lift (c+1) k (piSlot b q) = piSlot b (lift (c+d b) k q)`.
    `false` is `rfl`; `true` is the `lift_lift_permute` exchange. -/
theorem piSlot_lift (b : Bool) (c k : Nat) (q : ETm) :
    ETm.lift (c + 1) k (piSlot b q) = piSlot b (ETm.lift (c + piSlotD b) k q) := by
  cases b
  · rfl
  · show ETm.lift (c + 1) k (q.lift 0 1) = ETm.lift 0 1 (q.lift c k)
    rw [ETm.lift_lift_permute 1 k c 0 (Nat.zero_le c) q, Nat.add_comm 1 c]

/-- Inst exchange (S12 §2): `inst (c+1) r↑ (piSlot b q) = piSlot b (inst (c+d b) s q)`
    with `s = r` inside the pad (the slot eats the bump) and `s = r↑` under a live
    binder. `false` is `rfl`; `true` is `lift_inst_high`. -/
theorem piSlot_inst (b : Bool) (c : Nat) (r q : ETm) :
    ETm.inst (c + 1) (r.lift 0 1) (piSlot b q) =
      piSlot b (ETm.inst (c + piSlotD b) (cond b r (r.lift 0 1)) q) := by
  cases b
  · rfl
  · show ETm.inst (c + 1) (r.lift 0 1) (q.lift 0 1) = ETm.lift 0 1 (ETm.inst c r q)
    rw [ETm.lift_inst_high 1 0 c r (Nat.zero_le c) q, Nat.add_comm 1 c]

/-- The padded slot is unused: instantiating at it is the identity
    (`ETm.inst_lift_id`); no new inverse-substitution principle. -/
theorem piSlot_inst_id (r q : ETm) : ETm.inst 0 r (piSlot true q) = q :=
  ETm.inst_lift_id 0 r q

/-- `≈` congruence through the pad (`LvlEq.lift'` on the `true` branch). -/
theorem piSlot_lvlEq {b : Bool} {q q' : ETm} (h : LvlEq q q') :
    LvlEq (piSlot b q) (piSlot b q') := by
  cases b
  · exact h
  · exact h.lift' 0 1

/-- The `ETm.closedAt_lift` induction, kept local: `RcicSynTable`'s version lives above
    `RcicSynErase`, and this module must stay importable by the R2 switch. -/
private theorem closedAt_lift_add (c n : Nat) :
    {k : Nat} → {e : ETm} → ETm.ClosedAt k e → ETm.ClosedAt (k + n) (e.lift c n)
  | _, .bvar _, hc => by
      simp only [ETm.lift]
      split
      · exact Nat.add_lt_add_right hc n
      · exact Nat.lt_of_lt_of_le hc (Nat.le_add_right _ n)
  | _, .star, _ => trivial
  | _, .sort _, _ => trivial
  | _, .const _ _, _ => trivial
  | _, .app _ _, hc => ⟨closedAt_lift_add c n hc.1, closedAt_lift_add c n hc.2⟩
  | k, .lam _, hc => by
      have ih := closedAt_lift_add (c + 1) n (k := k + 1) hc
      rwa [Nat.add_right_comm k 1 n] at ih
  | k, .pi _ _, hc => by
      have ihb := closedAt_lift_add (c + 1) n (k := k + 1) hc.2
      rw [Nat.add_right_comm k 1 n] at ihb
      exact ⟨closedAt_lift_add c n hc.1, ihb⟩

/-- ClosedAt preservation (S12 §2): `ClosedAt k q → ClosedAt (k+1) (piSlot true q)`. -/
theorem piSlot_closedAt {k : Nat} {q : ETm} (h : ETm.ClosedAt k q) :
    ETm.ClosedAt (k + 1) (piSlot true q) :=
  closedAt_lift_add 0 1 h

/-- `instLevels` commutes with `lift` on `ETm` (level instantiation touches only
    `sort`/`const`; `lift` touches only `bvar`). -/
theorem ETm.instLevels_lift (ls : List Level) (c k : Nat) (e : ETm) :
    (e.lift c k).instLevels ls = (e.instLevels ls).lift c k := by
  induction e generalizing c with
  | bvar i =>
      simp only [ETm.lift, ETm.instLevels]
      split <;> rfl
  | star => rfl
  | sort l => rfl
  | const r ms => rfl
  | app f a ihf iha => simp only [ETm.lift, ETm.instLevels, ihf, iha]
  | lam b ih => simp only [ETm.lift, ETm.instLevels, ih]
  | pi a b iha ihb => simp only [ETm.lift, ETm.instLevels, iha, ihb]

/-- Level instantiation commutes with `piSlot` for a *fixed* bit (S12 §2). The `linst`
    consumer recomputes `b = levelIsZero (σ (instLevel ls u))`; this lemma never claims
    the bit itself is instantiation-invariant. -/
theorem piSlot_instLevels (b : Bool) (ls : List Level) (q : ETm) :
    (piSlot b q).instLevels ls = piSlot b (q.instLevels ls) := by
  cases b
  · rfl
  · exact ETm.instLevels_lift ls 0 1 q

end Rcic.Syn

#print axioms Rcic.Syn.piSlot
#print axioms Rcic.Syn.piSlotD
#print axioms Rcic.Syn.piSlot_true
#print axioms Rcic.Syn.piSlot_false
#print axioms Rcic.Syn.piSlot_lift
#print axioms Rcic.Syn.piSlot_inst
#print axioms Rcic.Syn.piSlot_inst_id
#print axioms Rcic.Syn.piSlot_lvlEq
#print axioms Rcic.Syn.piSlot_closedAt
#print axioms Rcic.Syn.ETm.instLevels_lift
#print axioms Rcic.Syn.piSlot_instLevels
