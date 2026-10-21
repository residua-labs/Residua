import rcic.RcicSynBvarEsub
import rcic.RcicERLocalize

/-!
# SCOPE-0 — pure ETm/display algebra for the shifted-value scope (S14, #7369)

S14's route to W-ER2-SHIFTED-VALUE-SCOPE begins with a premise-free fact:
restoring a prefix after `localize` only *deletes* free variables, never
adds one. This module seals that algebra on the existing `ETm`/`Disp`
operations — no `TyP`, no `eps`, no `AssumpPref`, no hcoh.

- `NFree`/`EFree` (§2): free de Bruijn index predicates. Source λ/Π/letE
  annotations count toward source support (the erasure may not use them);
  `const` refs and level parameters never do.
- `localize`/`restore` (S13 §2, S14 §4): `localize k` is `k` iterations of
  `ETm.inst 0 ETm.star`; `restore k r := (localize k r).lift 0 k`.
- `free_restore_iff` (§4): `EFree i (restore k r) ↔ EFree i r ∧ k ≤ i`,
  for every `r`, no premise.
- `AvoidPrefix` (S13 §2) and its algebra: `localize k (r.lift 0 k) = r`,
  `AvoidPrefix k 0 r → restore k r = r`, the `star` control, and the
  binder-step `localize (k+1) (r.lift 0 1) = localize k r`.
- `resolve_suffix` (§6): `resolve ρ (j+i)` resolves in the suffix and
  lifts by `countKeep (ρ.take j)` — the erased count κ, never the native
  slot j. Two controls pin the boundary: an out-of-range `insertDisp`/
  `removeAt` pair does not cancel (S8's range-free-cancellation refusal),
  and `[drop, keep]` at `j = 2` has `κ = 1`, not `j`.
-/

namespace Rcic.Syn
open Rcic.Declarative

/-- §2: free de Bruijn index `i` of a source term. λ/Π/letE annotations and
    the letE value count at the ambient depth; λ/Π/letE bodies raise the
    index by one; `const` refs and levels are not term free variables. -/
def NFree (i : Nat) : Expr Nat → Prop
  | .bvar j => i = j
  | .sort _ => False
  | .const _ _ => False
  | .app f a => NFree i f ∨ NFree i a
  | .lam A b => NFree i A ∨ NFree (i + 1) b
  | .pi A B => NFree i A ∨ NFree (i + 1) B
  | .letE A v b => NFree i A ∨ NFree i v ∨ NFree (i + 1) b
  | .lit _ => False

/-- §2: free de Bruijn index `i` of an erased term. λ bodies raise the
    index; Π domains count at the ambient depth, codomains at +1. -/
def EFree (i : Nat) : ETm → Prop
  | .bvar j => i = j
  | .star => False
  | .sort _ => False
  | .const _ _ => False
  | .app f a => EFree i f ∨ EFree i a
  | .lam b => EFree (i + 1) b
  | .pi a b => EFree i a ∨ EFree (i + 1) b

/-- S14 §4: lift the localized term back across the removed prefix. -/
def restore (k : Nat) (r : ETm) : ETm := (localize k r).lift 0 k

/-- S13 §2: no free index lands in the prefix window `[d, d + k)` at binder
    depth `d`. λ bodies and Π codomains raise `d` by one; Π domains and
    both `app` children keep `d`; `star`/`sort`/`const` hold directly. -/
def AvoidPrefix (k d : Nat) : ETm → Prop
  | .bvar i => i < d ∨ d + k ≤ i
  | .star => True
  | .sort _ => True
  | .const _ _ => True
  | .app f a => AvoidPrefix k d f ∧ AvoidPrefix k d a
  | .lam b => AvoidPrefix k (d + 1) b
  | .pi a b => AvoidPrefix k d a ∧ AvoidPrefix k (d + 1) b

/-! ## Free-index algebra of `inst`/`lift`/`localize` -/

/-- `inst j star` never *adds* a free index: index `i` of the result was
    either an untouched low slot (`i < j`) or came down one from `i + 1`
    (`j ≤ i`). The hit slot `j` itself is gone (its image `star` is
    free-variable-free). -/
theorem efree_inst_star {i : Nat} {r : ETm} :
    ∀ j : Nat, EFree i (ETm.inst j .star r) ↔
      (i < j ∧ EFree i r) ∨ (j ≤ i ∧ EFree (i + 1) r) := by
  induction r generalizing i with
  | bvar m =>
      intro j
      simp only [ETm.inst]
      split
      · simp only [EFree, false_iff]; omega
      · split <;> simp only [EFree] <;>
          constructor <;>
            first
            | (intro hi; exact .inr ⟨by omega, by omega⟩)
            | (intro hi; exact .inl ⟨by omega, hi⟩)
            | (rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  | star =>
      intro j
      simp only [ETm.inst, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | sort l =>
      intro j
      simp only [ETm.inst, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | const c ls =>
      intro j
      simp only [ETm.inst, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | app f a ihf iha =>
      intro j
      simp only [ETm.inst, EFree, ihf, iha]
      constructor
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
        · exact .inl ⟨h1, .inl h2⟩
        · exact .inr ⟨h1, .inl h2⟩
        · exact .inl ⟨h1, .inr h2⟩
        · exact .inr ⟨h1, .inr h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inl ⟨h1, h2⟩)
          · exact .inr (.inl ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inr ⟨h1, h2⟩)
          · exact .inr (.inr ⟨h1, h2⟩)
  | lam b ihb =>
      intro j
      simp only [ETm.inst, ETm.lift, EFree, ihb]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨by omega, h2⟩
        · exact .inr ⟨by omega, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨by omega, h2⟩
        · exact .inr ⟨by omega, h2⟩
  | pi a b iha ihb =>
      intro j
      simp only [ETm.inst, ETm.lift, EFree, iha, ihb]
      constructor
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
        · exact .inl ⟨h1, .inl h2⟩
        · exact .inr ⟨h1, .inl h2⟩
        · exact .inl ⟨by omega, .inr h2⟩
        · exact .inr ⟨by omega, .inr h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inl ⟨h1, h2⟩)
          · exact .inr (.inl ⟨by omega, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inr ⟨h1, h2⟩)
          · exact .inr (.inr ⟨by omega, h2⟩)

/-- `lift c k` adds `k` to every free index at or above the cutoff: a free
    `i` of the lifted term is either a low slot (`i < c`, unchanged) or a
    high slot that came from `i - k` (`c + k ≤ i`). -/
theorem efree_lift {r : ETm} {k : Nat} :
    ∀ (i c : Nat), EFree i (ETm.lift c k r) ↔
      (i < c ∧ EFree i r) ∨ (c + k ≤ i ∧ EFree (i - k) r) := by
  induction r with
  | bvar m =>
      intro i c
      simp only [ETm.lift]
      split <;> simp only [EFree] <;>
        constructor <;>
          first
          | (intro hi; exact .inr ⟨by omega, by omega⟩)
          | (intro hi; exact .inl ⟨by omega, hi⟩)
          | (rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  | star =>
      intro i c
      simp only [ETm.lift, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | sort l =>
      intro i c
      simp only [ETm.lift, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | const c' ls =>
      intro i c
      simp only [ETm.lift, EFree]
      constructor
      · intro h; exact h.elim
      · rintro (⟨-, hF⟩ | ⟨-, hF⟩) <;> exact hF.elim
  | app f a ihf iha =>
      intro i c
      simp only [ETm.lift, EFree, ihf, iha]
      constructor
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
        · exact .inl ⟨h1, .inl h2⟩
        · exact .inr ⟨h1, .inl h2⟩
        · exact .inl ⟨h1, .inr h2⟩
        · exact .inr ⟨h1, .inr h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inl ⟨h1, h2⟩)
          · exact .inr (.inl ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inr ⟨h1, h2⟩)
          · exact .inr (.inr ⟨h1, h2⟩)
  | lam b ihb =>
      intro i c
      simp only [ETm.lift, EFree, ihb]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨by omega, h2⟩
        · exact .inr ⟨by omega, by
            rw [show i - k + 1 = i + 1 - k from by omega]; exact h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨by omega, h2⟩
        · exact .inr ⟨by omega, by
            rw [show i + 1 - k = i - k + 1 from by omega]; exact h2⟩
  | pi a b iha ihb =>
      intro i c
      simp only [ETm.lift, EFree, iha, ihb]
      constructor
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
        · exact .inl ⟨h1, .inl h2⟩
        · exact .inr ⟨h1, .inl h2⟩
        · exact .inl ⟨by omega, .inr h2⟩
        · exact .inr ⟨by omega, by
            rw [show i - k + 1 = i + 1 - k from by omega]; exact .inr h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inl ⟨h1, h2⟩)
          · exact .inr (.inl ⟨by omega, h2⟩)
        · rcases h2 with h2 | h2
          · exact .inl (.inr ⟨h1, h2⟩)
          · exact .inr (.inr ⟨by omega, by
              rw [show i + 1 - k = i - k + 1 from by omega]; exact h2⟩)

/-- `localize k` deletes exactly the `k` front ambient slots: free index `i`
    of the result is free index `i + k` of the input. Premise-free. -/
theorem efree_localize {i : Nat} {r : ETm} (k : Nat) :
    EFree i (localize k r) ↔ EFree (i + k) r := by
  induction k generalizing i r with
  | zero => exact Iff.rfl
  | succ k ih =>
      show EFree i (localize k (ETm.inst 0 .star r)) ↔ EFree (i + (k + 1)) r
      rw [ih, efree_inst_star]
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 (Nat.not_lt_zero _)
        · exact h2
      · intro h
        exact .inr ⟨Nat.zero_le _, h⟩

/-- §4, the unconditional support-deletion theorem: `restore`'s free
    indices are exactly the free indices of `r` at or above `k`. Holds for
    every `r` — no `AvoidPrefix` premise. -/
theorem free_restore_iff (i k : Nat) (r : ETm) :
    EFree i (restore k r) ↔ EFree i r ∧ k ≤ i := by
  show EFree i ((localize k r).lift 0 k) ↔ EFree i r ∧ k ≤ i
  rw [efree_lift]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
    · exact absurd h1 (Nat.not_lt_zero _)
    · rw [efree_localize] at h2
      rw [Nat.sub_add_cancel (by omega : k ≤ i)] at h2
      exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩
    refine .inr ⟨by omega, ?_⟩
    rw [efree_localize, Nat.sub_add_cancel h2]
    exact h1

/-! ## `localize`/`restore` equations -/

/-- `localize k` undoes a `k`-lift at cutoff 0 — iterating
    `inst_lift_cancel`, never re-derived here. -/
theorem localize_lift (k : Nat) (r : ETm) :
    localize k (r.lift 0 k) = r := by
  induction k generalizing r with
  | zero => exact ETm.lift_zero 0 r
  | succ k ih =>
      show localize k (ETm.inst 0 .star (r.lift 0 (k + 1))) = r
      rw [ETm.inst_lift_cancel (k + 1) 0 0 .star (Nat.le_refl 0)
        (Nat.zero_lt_succ k) r]
      exact ih r

/-- Pushing a `localize` step under a kept binder: the extra front slot is
    exactly the binder's own slot — `inst_lift_id` deletes it. -/
theorem localize_succ_lift (k : Nat) (r : ETm) :
    localize (k + 1) (r.lift 0 1) = localize k r := by
  show localize k (ETm.inst 0 .star (ETm.lift 0 1 r)) = localize k r
  rw [ETm.inst_lift_id]

/-- Shrinking the forbidden window is always safe. -/
theorem avpfx_mono {r : ETm} {k k' : Nat} (hkk : k' ≤ k) :
    ∀ d : Nat, AvoidPrefix k d r → AvoidPrefix k' d r := by
  induction r with
  | bvar m =>
      intro d h
      simp only [AvoidPrefix] at h ⊢
      rcases h with h | h <;> omega
  | star => intro _ _; trivial
  | sort l => intro _ _; trivial
  | const c ls => intro _ _; trivial
  | app f a ihf iha =>
      intro d h
      simp only [AvoidPrefix] at h ⊢
      exact ⟨ihf d h.1, iha d h.2⟩
  | lam b ihb =>
      intro d h
      simp only [AvoidPrefix] at h ⊢
      exact ihb (d + 1) h
  | pi a b iha ihb =>
      intro d h
      simp only [AvoidPrefix] at h ⊢
      exact ⟨iha d h.1, ihb (d + 1) h.2⟩

/-- `inst d star` shortens the forbidden window by one: if `r` avoids
    `[d, d + k + 1)`, its image avoids `[d, d + k)`. -/
theorem avpfx_inst {r : ETm} {k : Nat} :
    ∀ d : Nat, AvoidPrefix (k + 1) d r →
      AvoidPrefix k d (ETm.inst d .star r) := by
  induction r with
  | bvar m =>
      intro d h
      simp only [AvoidPrefix] at h
      simp only [ETm.inst]
      split
      · rcases h with h | h <;> simp only [AvoidPrefix] <;> omega
      · split <;> rcases h with h | h <;> simp only [AvoidPrefix] <;> omega
  | star => intro _ _; trivial
  | sort l => intro _ _; trivial
  | const c ls => intro _ _; trivial
  | app f a ihf iha =>
      intro d h
      simp only [ETm.inst, AvoidPrefix] at h ⊢
      exact ⟨ihf d h.1, iha d h.2⟩
  | lam b ihb =>
      intro d h
      simp only [ETm.inst, ETm.lift, AvoidPrefix] at h ⊢
      exact ihb (d + 1) h
  | pi a b iha ihb =>
      intro d h
      simp only [ETm.inst, ETm.lift, AvoidPrefix] at h ⊢
      exact ⟨iha d h.1, ihb (d + 1) h.2⟩

/-- If slot `d` is unused (`AvoidPrefix 1`), `inst d` followed by `lift d 1`
    is the identity — the replacement `star` is never read. -/
theorem lift_inst_star_id {r : ETm} :
    ∀ d : Nat, AvoidPrefix 1 d r → ETm.lift d 1 (ETm.inst d .star r) = r := by
  induction r with
  | bvar m =>
      intro d h
      simp only [AvoidPrefix] at h
      rcases h with h | h <;> etm_bvar_leaves
  | star => intro _ _; rfl
  | sort l => intro _ _; rfl
  | const c ls => intro _ _; rfl
  | app f a ihf iha =>
      intro d h
      simp only [AvoidPrefix] at h
      simp only [ETm.inst, ETm.lift, ihf d h.1, iha d h.2]
  | lam b ihb =>
      intro d h
      simp only [AvoidPrefix] at h
      simp only [ETm.inst, ETm.lift, ihb (d + 1) h]
  | pi a b iha ihb =>
      intro d h
      simp only [AvoidPrefix] at h
      simp only [ETm.inst, ETm.lift, iha d h.1, ihb (d + 1) h.2]

/-- S13 §2: `restore` is the identity on prefix-avoiding terms —
    `localize` is lossless on exactly the `AvoidPrefix` domain. -/
theorem restore_eq (r : ETm) (k : Nat) :
    AvoidPrefix k 0 r → restore k r = r := by
  induction k generalizing r with
  | zero =>
      intro _
      exact ETm.lift_zero 0 r
  | succ k ih =>
      intro h
      have h1 : AvoidPrefix 1 0 r := avpfx_mono (by omega : 1 ≤ k + 1) 0 h
      have hk : AvoidPrefix k 0 (ETm.inst 0 .star r) := avpfx_inst 0 h
      have hih := ih (ETm.inst 0 .star r) hk
      simp only [restore] at hih ⊢
      show ETm.lift 0 (k + 1) (localize k (ETm.inst 0 .star r)) = r
      rw [← ETm.lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le k)]
      rw [hih]
      exact lift_inst_star_id 0 h1

/-- `localize` preserves `star`. -/
theorem localize_star (k : Nat) : localize k .star = .star := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show localize k (ETm.inst 0 .star .star) = .star
      exact ih

/-- §4 control: on the `AvoidPrefix` domain, `localize` reads `star` iff
    the input is `star` — the path gate can never be re-chosen by the
    localizer. -/
theorem localize_star_iff (k : Nat) {r : ETm} (h : AvoidPrefix k 0 r) :
    localize k r = .star ↔ r = .star := by
  constructor
  · intro hstar
    have hres := restore_eq r k h
    simp only [restore] at hres
    rw [hstar] at hres
    exact hres.symm
  · intro hstar
    rw [hstar]
    exact localize_star k

/-! ## `resolve` suffix equation (§6) and the two controls -/

/-- §6: resolving `j + i` in the full display is resolving `i` in the
    suffix and lifting by the prefix's erased count `countKeep (ρ.take j)`
    — `keep` adds a lift, `drop`/`inline` skip. Premise is only the real
    range bound `j ≤ ρ.length`. -/
theorem resolve_suffix (ρ : List Disp) (j i : Nat) (hj : j ≤ ρ.length) :
    resolve ρ (j + i) = (resolve (ρ.drop j) i).lift 0 (countKeep (ρ.take j)) := by
  induction j generalizing ρ i with
  | zero =>
      rw [Nat.zero_add]
      exact (ETm.lift_zero 0 _).symm
  | succ j ih =>
      cases ρ with
      | nil =>
          simp only [List.length_nil] at hj
          exact absurd hj (Nat.not_succ_le_zero j)
      | cons d ρ' =>
          have hj' : j ≤ ρ'.length := by
            simp only [List.length_cons] at hj; omega
          rw [show j + 1 + i = (j + i) + 1 from by omega,
            show (d :: ρ').take (j + 1) = d :: ρ'.take j from rfl,
            show (d :: ρ').drop (j + 1) = ρ'.drop j from rfl]
          cases d with
          | keep =>
              rw [resolve_keep_succ, ih ρ' i hj']
              simp only [countKeep]
              exact ETm.lift_lift_merge 1 _ 0 0 (Nat.le_refl 0)
                (Nat.zero_le _) _
          | drop =>
              rw [resolve_drop_succ, ih ρ' i hj']
              rfl
          | inline v =>
              rw [resolve_inline_succ, ih ρ' i hj']
              rfl

/-- Control — the cancellation is NOT range-free: inserting at `j = 1`
    into the empty display keeps the entry (the `insertDisp`/`removeAt`
    pair does not disappear past the end). -/
theorem removeAt_insertDisp_oob_ne_nil (d : Disp) :
    removeAt (insertDisp d 1 []) 1 ≠ [] :=
  List.cons_ne_nil d []

/-- Control — the lift amount is the erased count `κ`, never the native
    slot `j`: at `ρ = [drop, keep]`, `j = 2` gives `κ = 1`. -/
theorem resolve_suffix_drop_keep_kappa (i : Nat) :
    resolve [.drop, .keep] (2 + i) = (resolve [] i).lift 0 1 := by
  rw [show 2 + i = (i + 1) + 1 from by omega, resolve_drop_succ,
    resolve_keep_succ]

/-- and lifting by the native `j = 2` would be wrong. -/
theorem resolve_suffix_native_j_neq (i : Nat) :
    resolve [.drop, .keep] (2 + i) ≠ (resolve [] i).lift 0 2 := by
  intro h
  rw [resolve_suffix_drop_keep_kappa, resolve_nil] at h
  simp only [ETm.lift, if_pos (Nat.zero_le _)] at h
  exact absurd (ETm.bvar.inj h) (by omega)

/-! ## Seal-canonical names over `def AvoidPrefix`

Main's `RcicERLocalize` ships an `inductive AvoidPrefix` with these theorem
names in its seal. This module's `def AvoidPrefix` is the same predicate in
primitive form (identical per-ctor clauses); the sealed names are provided as
wrappers over the `avpfx_*`/`lift_inst_star_id`/`restore_eq`/`localize_star_iff`
algebra so both namesets resolve to proved statements — no statement is lost. -/

namespace AvoidPrefix

/-- Weakening the prefix bound (`avpfx_mono`). -/
theorem mono {k₁ k₂ : Nat} (hk : k₁ ≤ k₂) {d : Nat} {r : ETm}
    (h : AvoidPrefix k₂ d r) : AvoidPrefix k₁ d r :=
  avpfx_mono hk d h

/-- One `inst d star` step shrinks the avoided prefix by one (`avpfx_inst`). -/
theorem inst_star {k d : Nat} {r : ETm} (h : AvoidPrefix (k + 1) d r) :
    AvoidPrefix k d (ETm.inst d .star r) :=
  avpfx_inst d h

/-- `inst d star` never manufactures `star` from a non-`star` term that avoids
    slot `d` — derived from the round-trip `lift_inst_star_id`. -/
theorem inst_star_eq_star {d : Nat} {r : ETm} (h : AvoidPrefix 1 d r) :
    ETm.inst d .star r = .star ↔ r = .star := by
  constructor
  · intro hi
    have hrt := lift_inst_star_id d h
    rw [hi] at hrt
    exact hrt.symm
  · intro hr
    subst hr
    simp [ETm.inst]

/-- The per-step round trip (`lift_inst_star_id`). -/
theorem lift_inst_star_cancel {d : Nat} {r : ETm} (h : AvoidPrefix 1 d r) :
    (ETm.inst d .star r).lift d 1 = r :=
  lift_inst_star_id d h

end AvoidPrefix

/-- `localize` under `AvoidPrefix` returns the suffix-local form — lifting the
    result back by `k` restores `r` (`restore_eq` unfolded). -/
theorem localize_lift_cancel {k : Nat} {r : ETm} (h : AvoidPrefix k 0 r) :
    (localize k r).lift 0 k = r :=
  restore_eq r k h

/-- Under `AvoidPrefix`, `localize` never manufactures `star`
    (`localize_star_iff`). -/
theorem localize_eq_star {k : Nat} {r : ETm} (h : AvoidPrefix k 0 r) :
    localize k r = .star ↔ r = .star :=
  localize_star_iff k h

end Rcic.Syn

#print axioms Rcic.Syn.free_restore_iff
#print axioms Rcic.Syn.restore_eq
#print axioms Rcic.Syn.resolve_suffix
#print axioms Rcic.Syn.AvoidPrefix.mono
#print axioms Rcic.Syn.AvoidPrefix.inst_star
#print axioms Rcic.Syn.AvoidPrefix.inst_star_eq_star
#print axioms Rcic.Syn.AvoidPrefix.lift_inst_star_cancel
#print axioms Rcic.Syn.localize_lift_cancel
#print axioms Rcic.Syn.localize_eq_star
