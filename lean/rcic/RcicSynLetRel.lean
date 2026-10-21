import rcic.RcicERPiSlotConv
import rcic.RcicSynClauseAlg
import rcic.RcicSynPBitAll
import rcic.RcicERScope0
import rcic.RcicSynTable

/-!
# Wall 2 (changed-declaration letRight), step 1 — the relation `Rel` and its algebra

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Relation".

`Rel tbl s t` is conversion modulo `≈` together with star-status synchronization,
`s = ★ ↔ t = ★`. The status component is what the LetBridge induction must *produce*
(arbitrary conversion does not synchronize collapse tests), and what the clauses of
`TyP.eps` (`appClause`, `lamClause`, `letDisp`) consume.

Contents:
* `Rel`: refl / symm / trans, `≈`-cast, lift (under `TableClosed`), `inst` with non-★
  related replacements (congruence plus `inst_eq_star` on both sides), `appClause`,
  `lamClause` / `lamErasure`, `pi`, and the R2 `piSlot` pad.
* `DispRel`: the keep-to-keep display relation (non-keep leaves compared by `Rel`,
  `drop` = ★, `inline r` = `r`); it preserves `countKeep` prefixes and gives `Rel` of
  `resolve`.
* `EAct` / `applyActs`: the pending erased actions of a transport stack (`lift κ 1`,
  `inst κ r`), innermost first, with the clause commutations under non-★ replacements
  and the binder shift `shiftActs`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the relation -/

/-- Part III "Relation": `s ≈ t` (conversion modulo `≈`) and the same star status. -/
structure Rel (tbl : List CRule) (s t : ETm) : Prop where
  conv : ConvMod (EStep tbl) LvlEq s t
  star_iff : s = .star ↔ t = .star

theorem Rel.refl (tbl : List CRule) (s : ETm) : Rel tbl s s := ⟨.refl s, Iff.rfl⟩

theorem Rel.of_eq (tbl : List CRule) {s t : ETm} (h : s = t) : Rel tbl s t :=
  h ▸ Rel.refl tbl s

theorem Rel.symm {tbl : List CRule} {s t : ETm} (h : Rel tbl s t) : Rel tbl t s :=
  ⟨ConvMod.symm' LvlEq.symm' h.conv, h.star_iff.symm⟩

theorem Rel.trans {tbl : List CRule} {s t u : ETm} (h1 : Rel tbl s t) (h2 : Rel tbl t u) :
    Rel tbl s u :=
  ⟨h1.conv.trans h2.conv, h1.star_iff.trans h2.star_iff⟩

theorem Rel.star (tbl : List CRule) : Rel tbl .star .star := Rel.refl tbl .star

theorem Rel.eq_star {tbl : List CRule} {s t : ETm} (h : Rel tbl s t) (hs : s = .star) :
    t = .star := h.star_iff.mp hs

theorem Rel.eq_star' {tbl : List CRule} {s t : ETm} (h : Rel tbl s t) (ht : t = .star) :
    s = .star := h.star_iff.mpr ht

theorem Rel.ne_star {tbl : List CRule} {s t : ETm} (h : Rel tbl s t) (hs : s ≠ .star) :
    t ≠ .star := fun ht => hs (h.star_iff.mpr ht)

theorem Rel.ne_star' {tbl : List CRule} {s t : ETm} (h : Rel tbl s t) (ht : t ≠ .star) :
    s ≠ .star := fun hs => ht (h.star_iff.mp hs)

/-- `≈` is shape-preserving, so it is a `Rel`. -/
theorem Rel.of_lvlEq (tbl : List CRule) {s t : ETm} (h : LvlEq s t) : Rel tbl s t :=
  ⟨.eqv h, by
    constructor
    · intro hs; subst hs; cases h; rfl
    · intro ht; subst ht; cases h; rfl⟩

/-- Rewrite both sides by equalities. -/
theorem Rel.cast {tbl : List CRule} {s s' t t' : ETm} (hs : s = s') (ht : t = t')
    (h : Rel tbl s t) : Rel tbl s' t' := hs ▸ ht ▸ h

/-! ## §2 congruences -/

/-- `lift` preserves `Rel` (`convMod_lift` needs the real `TableClosed`). -/
theorem rel_lift {tbl : List CRule} (hcl : TableClosed tbl) {s t : ETm} (h : Rel tbl s t)
    (c k : Nat) : Rel tbl (s.lift c k) (t.lift c k) :=
  ⟨convMod_lift hcl h.conv c k, by
    rw [etm_lift_eq_star_iff, etm_lift_eq_star_iff]
    exact h.star_iff⟩

/-- `inst` with non-★ related replacements: conversion congruence plus `inst_eq_star`
    on both sides. The right replacement is non-★ by the status of `hr`. -/
theorem rel_inst {tbl : List CRule} (hcl : TableClosed tbl) {M M' r r' : ETm}
    (hM : Rel tbl M M') (hr : Rel tbl r r') (hne : r ≠ .star) (j : Nat) :
    Rel tbl (ETm.inst j r M) (ETm.inst j r' M') :=
  ⟨convMod_inst hcl hM.conv hr.conv j, by
    rw [etm_inst_eq_star_iff j hne, etm_inst_eq_star_iff j (hr.ne_star hne)]
    exact hM.star_iff⟩

theorem rel_appClause {tbl : List CRule} {f f' a a' : ETm} (hf : Rel tbl f f')
    (ha : Rel tbl a a') : Rel tbl (appClause f a) (appClause f' a') := by
  by_cases hfs : f = .star
  · have hfs' : f' = .star := hf.eq_star hfs
    subst hfs; subst hfs'
    exact Rel.star tbl
  · have hfs' : f' ≠ .star := hf.ne_star hfs
    by_cases has : a = .star
    · have has' : a' = .star := ha.eq_star has
      subst has; subst has'
      rw [appClause_right_star, appClause_right_star]
      exact hf
    · have has' : a' ≠ .star := ha.ne_star has
      rw [appClause_app hfs has, appClause_app hfs' has']
      exact ⟨convMod_app hf.conv ha.conv, by constructor <;> intro h <;> cases h⟩

theorem rel_lamClause {tbl : List CRule} {b b' : ETm} (h : Rel tbl b b') :
    Rel tbl (lamClause b) (lamClause b') := by
  by_cases hb : b = .star
  · have hb' : b' = .star := h.eq_star hb
    subst hb; subst hb'
    exact Rel.star tbl
  · have hb' : b' ≠ .star := h.ne_star hb
    rw [lamClause_of_ne hb, lamClause_of_ne hb']
    exact ⟨convMod_lam h.conv, by constructor <;> intro h <;> cases h⟩

theorem rel_lamErasure {tbl : List CRule} (proofDom : Bool) {b b' : ETm} (h : Rel tbl b b') :
    Rel tbl (lamErasure proofDom b) (lamErasure proofDom b') := by
  cases proofDom
  · exact rel_lamClause h
  · exact h

theorem rel_pi {tbl : List CRule} {a a' b b' : ETm} (ha : Rel tbl a a') (hb : Rel tbl b b') :
    Rel tbl (.pi a b) (.pi a' b') :=
  ⟨convMod_pi ha.conv hb.conv, by constructor <;> intro h <;> cases h⟩

/-- The R2 Π clause once the domain gates agree: the pad is `rel_lift`. -/
theorem rel_piSlot {tbl : List CRule} (hcl : TableClosed tbl) (bit : Bool) {q q' : ETm}
    (h : Rel tbl q q') : Rel tbl (piSlot bit q) (piSlot bit q') := by
  cases bit
  · exact h
  · exact rel_lift hcl h 0 1

theorem rel_app {tbl : List CRule} {f f' a a' : ETm} (hf : Rel tbl f f') (ha : Rel tbl a a') :
    Rel tbl (.app f a) (.app f' a') :=
  ⟨convMod_app hf.conv ha.conv, by constructor <;> intro h <;> cases h⟩

theorem rel_lam {tbl : List CRule} {b b' : ETm} (h : Rel tbl b b') :
    Rel tbl (.lam b) (.lam b') :=
  ⟨convMod_lam h.conv, by constructor <;> intro h <;> cases h⟩

/-! ## §3 the display relation -/

/-- Keep only to keep; a non-keep leaf is compared by `Rel` (`drop` = ★, `inline r` = `r`).
    `drop`/`inline` never mix: a `Rel` to ★ is ★ by status. -/
inductive DispRel (tbl : List CRule) : List Disp → List Disp → Prop where
  | nil : DispRel tbl [] []
  | keep {ρ ρ' : List Disp} : DispRel tbl ρ ρ' → DispRel tbl (.keep :: ρ) (.keep :: ρ')
  | drop {ρ ρ' : List Disp} : DispRel tbl ρ ρ' → DispRel tbl (.drop :: ρ) (.drop :: ρ')
  | inline {v v' : ETm} {ρ ρ' : List Disp} :
      Rel tbl v v' → DispRel tbl ρ ρ' → DispRel tbl (.inline v :: ρ) (.inline v' :: ρ')

theorem DispRel.refl (tbl : List CRule) : (ρ : List Disp) → DispRel tbl ρ ρ
  | [] => .nil
  | .keep :: ρ => .keep (DispRel.refl tbl ρ)
  | .drop :: ρ => .drop (DispRel.refl tbl ρ)
  | .inline v :: ρ => .inline (Rel.refl tbl v) (DispRel.refl tbl ρ)

theorem DispRel.length_eq {tbl : List CRule} {ρ ρ' : List Disp} (h : DispRel tbl ρ ρ') :
    ρ.length = ρ'.length := by
  induction h with
  | nil => rfl
  | keep _ ih => exact congrArg Nat.succ ih
  | drop _ ih => exact congrArg Nat.succ ih
  | inline _ _ ih => exact congrArg Nat.succ ih

theorem DispRel.countKeep_eq {tbl : List CRule} {ρ ρ' : List Disp} (h : DispRel tbl ρ ρ') :
    countKeep ρ = countKeep ρ' := by
  induction h with
  | nil => rfl
  | keep _ ih => exact congrArg Nat.succ ih
  | drop _ ih => exact ih
  | inline _ _ ih => exact ih

theorem DispRel.take {tbl : List CRule} {ρ ρ' : List Disp} (h : DispRel tbl ρ ρ') :
    (i : Nat) → DispRel tbl (ρ.take i) (ρ'.take i)
  | 0 => .nil
  | i + 1 => by
      cases h with
      | nil => exact .nil
      | keep h' => exact .keep (h'.take i)
      | drop h' => exact .drop (h'.take i)
      | inline hv h' => exact .inline hv (h'.take i)

theorem DispRel.countKeep_take_eq {tbl : List CRule} {ρ ρ' : List Disp} (h : DispRel tbl ρ ρ')
    (i : Nat) : countKeep (ρ.take i) = countKeep (ρ'.take i) :=
  (h.take i).countKeep_eq

theorem DispRel.getElem?_keep_iff {tbl : List CRule} {ρ ρ' : List Disp} (h : DispRel tbl ρ ρ') :
    (c : Nat) → (ρ[c]? = some .keep ↔ ρ'[c]? = some .keep)
  | 0 => by
      cases h with
      | nil => exact Iff.rfl
      | keep _ => simp
      | drop _ => simp
      | inline _ _ => simp
  | c + 1 => by
      cases h with
      | nil => exact Iff.rfl
      | keep h' => simpa using h'.getElem?_keep_iff c
      | drop h' => simpa using h'.getElem?_keep_iff c
      | inline _ h' => simpa using h'.getElem?_keep_iff c

/-- A non-★ value's let disposition is `inline`. -/
theorem letDisp_of_ne_star {a : ETm} (h : a ≠ .star) : letDisp a = .inline a := by
  cases a <;> first | rfl | exact absurd rfl h

theorem letDisp_star : letDisp .star = .drop := rfl

/-- `Rel`-related values give related let dispositions (status synchronizes the branch). -/
theorem DispRel.letDisp {tbl : List CRule} {a a' : ETm} (ha : Rel tbl a a') {ρ ρ' : List Disp}
    (h : DispRel tbl ρ ρ') : DispRel tbl (letDisp a :: ρ) (letDisp a' :: ρ') := by
  by_cases hs : a = .star
  · have hs' : a' = .star := ha.eq_star hs
    subst hs; subst hs'
    exact .drop h
  · have hs' : a' ≠ .star := ha.ne_star hs
    rw [letDisp_of_ne_star hs, letDisp_of_ne_star hs']
    exact .inline ha h

/-- `Rel` of `resolve` along a display relation. -/
theorem rel_resolve {tbl : List CRule} (hcl : TableClosed tbl) {ρ ρ' : List Disp}
    (h : DispRel tbl ρ ρ') : (i : Nat) → Rel tbl (resolve ρ i) (resolve ρ' i) := by
  intro i
  induction h generalizing i with
  | nil => exact Rel.refl tbl _
  | keep _ ih =>
      cases i with
      | zero => exact Rel.refl tbl _
      | succ i =>
          rw [resolve_keep_succ, resolve_keep_succ]
          exact rel_lift hcl (ih i) 0 1
  | drop _ ih =>
      cases i with
      | zero => exact Rel.refl tbl _
      | succ i =>
          rw [resolve_drop_succ, resolve_drop_succ]
          exact ih i
  | inline hv _ ih =>
      cases i with
      | zero => exact hv
      | succ i =>
          rw [resolve_inline_succ, resolve_inline_succ]
          exact ih i

/-! ## §4 pending erased actions of a transport stack -/

/-- One erased action: a `wk` at a kept slot (`lift κ 1`) or a retained `esub`
    (`inst κ r`). Dropped / inlined transports have no erased action. -/
inductive EAct : Type where
  | lift (κ : Nat)
  | inst (κ : Nat) (r : ETm)

def EAct.apply : EAct → ETm → ETm
  | .lift κ, t => t.lift κ 1
  | .inst κ r, t => ETm.inst κ r t

/-- Innermost action first (the head of a transport stack is applied first). -/
def applyActs : List EAct → ETm → ETm
  | [], t => t
  | a :: as, t => applyActs as (a.apply t)

/-- Every `inst` replacement is non-★ (the PB answers of the retained `esub` stages). -/
def EActsNonStar : List EAct → Prop
  | [] => True
  | .lift _ :: as => EActsNonStar as
  | .inst _ r :: as => r ≠ .star ∧ EActsNonStar as

theorem applyActs_nil (t : ETm) : applyActs [] t = t := rfl

theorem applyActs_cons (a : EAct) (as : List EAct) (t : ETm) :
    applyActs (a :: as) t = applyActs as (a.apply t) := rfl

theorem applyActs_star : (as : List EAct) → applyActs as .star = .star
  | [] => rfl
  | .lift _ :: as => applyActs_star as
  | .inst _ _ :: as => applyActs_star as

theorem applyActs_sort (l : Level) : (as : List EAct) → applyActs as (.sort l) = .sort l
  | [] => rfl
  | .lift _ :: as => applyActs_sort l as
  | .inst _ _ :: as => applyActs_sort l as

theorem applyActs_const (r : Nat) (ls : List Level) :
    (as : List EAct) → applyActs as (.const r ls) = .const r ls
  | [] => rfl
  | .lift _ :: as => applyActs_const r ls as
  | .inst _ _ :: as => applyActs_const r ls as

theorem applyActs_eq_star_iff : (as : List EAct) → EActsNonStar as → (t : ETm) →
    (applyActs as t = .star ↔ t = .star)
  | [], _, _ => Iff.rfl
  | .lift κ :: as, hns, t => by
      rw [applyActs_cons, applyActs_eq_star_iff as hns]
      exact etm_lift_eq_star_iff κ 1 t
  | .inst κ r :: as, hns, t => by
      rw [applyActs_cons, applyActs_eq_star_iff as hns.2]
      exact etm_inst_eq_star_iff κ hns.1 t

theorem applyActs_appClause : (as : List EAct) → EActsNonStar as → (f a : ETm) →
    applyActs as (appClause f a) = appClause (applyActs as f) (applyActs as a)
  | [], _, _, _ => rfl
  | .lift κ :: as, hns, f, a => by
      simp only [applyActs_cons, EAct.apply]
      rw [lift_appClause, applyActs_appClause as hns]
  | .inst κ r :: as, hns, f, a => by
      simp only [applyActs_cons, EAct.apply]
      rw [inst_appClause κ hns.1, applyActs_appClause as hns.2]

/-- The binder shift of an action list (under a kept erased binder). -/
def EAct.shift : EAct → EAct
  | .lift κ => .lift (κ + 1)
  | .inst κ r => .inst (κ + 1) (r.lift 0 1)

def shiftActs (as : List EAct) : List EAct := as.map EAct.shift

theorem shiftActs_nil : shiftActs [] = [] := rfl

theorem shiftActs_cons (a : EAct) (as : List EAct) :
    shiftActs (a :: as) = a.shift :: shiftActs as := rfl

theorem eActsNonStar_shift : (as : List EAct) → EActsNonStar as → EActsNonStar (shiftActs as)
  | [], h => h
  | .lift _ :: as, h => eActsNonStar_shift as h
  | .inst _ _ :: as, h => ⟨lift_ne_star h.1, eActsNonStar_shift as h.2⟩

theorem applyActs_lamClause : (as : List EAct) → EActsNonStar as → (b : ETm) →
    applyActs as (lamClause b) = lamClause (applyActs (shiftActs as) b)
  | [], _, _ => rfl
  | .lift κ :: as, hns, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      show applyActs as ((lamClause b).lift κ 1) = lamClause (applyActs (shiftActs as) (b.lift (κ + 1) 1))
      rw [lift_lamClause, applyActs_lamClause as hns]
  | .inst κ r :: as, hns, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      show applyActs as (ETm.inst κ r (lamClause b)) =
        lamClause (applyActs (shiftActs as) (ETm.inst (κ + 1) (r.lift 0 1) b))
      rw [inst_lamClause κ hns.1, applyActs_lamClause as hns.2]

theorem applyActs_lamErasure (proofDom : Bool) (as : List EAct) (hns : EActsNonStar as)
    (b : ETm) :
    applyActs as (lamErasure proofDom b) =
      lamErasure proofDom (applyActs (if proofDom then as else shiftActs as) b) := by
  cases proofDom
  · exact applyActs_lamClause as hns b
  · rfl

theorem applyActs_pi : (as : List EAct) → (a b : ETm) →
    applyActs as (.pi a b) = .pi (applyActs as a) (applyActs (shiftActs as) b)
  | [], _, _ => rfl
  | .lift κ :: as, a, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      show applyActs as (.pi (a.lift κ 1) (b.lift (κ + 1) 1)) = _
      rw [applyActs_pi as]
      rfl
  | .inst κ r :: as, a, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      show applyActs as (.pi (ETm.inst κ r a) (ETm.inst (κ + 1) (r.lift 0 1) b)) = _
      rw [applyActs_pi as]
      rfl

theorem applyActs_app : (as : List EAct) → (f a : ETm) →
    applyActs as (.app f a) = .app (applyActs as f) (applyActs as a)
  | [], _, _ => rfl
  | .lift κ :: as, f, a => by
      rw [applyActs_cons, applyActs_cons, applyActs_cons]
      exact applyActs_app as _ _
  | .inst κ r :: as, f, a => by
      rw [applyActs_cons, applyActs_cons, applyActs_cons]
      exact applyActs_app as _ _

theorem applyActs_lam : (as : List EAct) → (b : ETm) →
    applyActs as (.lam b) = .lam (applyActs (shiftActs as) b)
  | [], _ => rfl
  | .lift κ :: as, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      exact applyActs_lam as _
  | .inst κ r :: as, b => by
      rw [applyActs_cons, shiftActs_cons, applyActs_cons]
      exact applyActs_lam as _

/-- The shifted actions commute with the binder lift. -/
theorem applyActs_shift_lift : (as : List EAct) → (t : ETm) →
    applyActs (shiftActs as) (t.lift 0 1) = (applyActs as t).lift 0 1
  | [], _ => rfl
  | .lift κ :: as, t => by
      simp only [shiftActs_cons, applyActs_cons, EAct.shift, EAct.apply]
      rw [← ETm.lift_lift_one, applyActs_shift_lift as]
  | .inst κ r :: as, t => by
      simp only [shiftActs_cons, applyActs_cons, EAct.shift, EAct.apply]
      rw [← applyActs_shift_lift as, ETm.lift_inst_high 1 0 κ r (Nat.zero_le κ) t,
        Nat.add_comm 1 κ]

/-- The binder's own slot is fixed by the shifted actions. -/
theorem applyActs_shift_bvar_zero : (as : List EAct) →
    applyActs (shiftActs as) (.bvar 0) = .bvar 0
  | [] => rfl
  | .lift κ :: as => by
      rw [shiftActs_cons, applyActs_cons]
      show applyActs (shiftActs as) ((ETm.bvar 0).lift (κ + 1) 1) = _
      have h : (ETm.bvar 0).lift (κ + 1) 1 = .bvar 0 := by
        simp only [ETm.lift]
        rw [if_neg (by omega)]
      rw [h, applyActs_shift_bvar_zero as]
  | .inst κ r :: as => by
      rw [shiftActs_cons, applyActs_cons]
      show applyActs (shiftActs as) (ETm.inst (κ + 1) (r.lift 0 1) (.bvar 0)) = _
      have h : ETm.inst (κ + 1) (r.lift 0 1) (.bvar 0) = .bvar 0 := by
        simp only [ETm.inst]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [h, applyActs_shift_bvar_zero as]

/-- `Rel` through the same action list on both sides (non-★ replacements, related). -/
theorem rel_applyActs {tbl : List CRule} (hcl : TableClosed tbl) :
    (as : List EAct) → EActsNonStar as → {s t : ETm} → Rel tbl s t →
      Rel tbl (applyActs as s) (applyActs as t)
  | [], _, _, _, h => h
  | .lift κ :: as, hns, _, _, h => by
      rw [applyActs_cons, applyActs_cons]
      exact rel_applyActs hcl as hns (rel_lift hcl h κ 1)
  | .inst κ r :: as, hns, _, _, h => by
      rw [applyActs_cons, applyActs_cons]
      exact rel_applyActs hcl as hns.2 (rel_inst hcl h (Rel.refl tbl r) hns.1 κ)

end Rcic.Syn

#print axioms Rcic.Syn.Rel.trans
#print axioms Rcic.Syn.Rel.of_lvlEq
#print axioms Rcic.Syn.rel_lift
#print axioms Rcic.Syn.rel_inst
#print axioms Rcic.Syn.rel_appClause
#print axioms Rcic.Syn.rel_lamClause
#print axioms Rcic.Syn.rel_lamErasure
#print axioms Rcic.Syn.rel_pi
#print axioms Rcic.Syn.rel_piSlot
#print axioms Rcic.Syn.DispRel.letDisp
#print axioms Rcic.Syn.rel_resolve
#print axioms Rcic.Syn.applyActs_eq_star_iff
#print axioms Rcic.Syn.applyActs_appClause
#print axioms Rcic.Syn.applyActs_lamClause
#print axioms Rcic.Syn.applyActs_lamErasure
#print axioms Rcic.Syn.applyActs_pi
#print axioms Rcic.Syn.applyActs_shift_lift
#print axioms Rcic.Syn.applyActs_shift_bvar_zero
#print axioms Rcic.Syn.rel_applyActs
