/-
RCIC Annex 23 unit H-6 / RULING R-LevelDec — `decEqN`, sound and
complete for `eqN` as landed (`RcicDeclarative`).

LEAF: only `rcic.RcicLevelZero` (hence `RcicDeclarative`). No
rank, no `WellFounded` on levels (R-LevelDec (2): the refuted
`levelRank` is not this object). `reduce` is constructor
recursion on children, then local 02-§2 identities
(`imax u 0 = 0`, `imax v v = v`, `max u 0 = u`). `geq` is
constructor recursion on the second level. Calls `eval` /
`eqN` / `levelIsZero` (23.H.0 (5)).

02 §2 equations quoted below; DT-026 (`02` §14) is the owner.
NAMES: `decEqN`, `decEqN_sound`, `decEqN_complete`.
H-6b: `imaxJoin` gains `imax 0 u = u` (the #4343 wall);
`geqParam` of a maybe-zero imax recurses on the second
argument. `decEqN_complete` is not declared (WALL at
`geq` of two non-zero reduced forms that are not
syntactically equal).
H-6c: `nf` / `denote` / `nf_eval` (evaluation lemma on
all partial valuations). Injectivity on `eqN` classes
not declared (attempt 1, separating valuations on
`max`/`imax` nf nodes). `decEqN` not rebased (needs
injectivity).
H-6d: `succCanon` distributes over `max`; `imaxCanon`
distributes over flattened `max` (never-zero and
maybe-zero). Instrument (1) `noneOnly` / `dependsOn`
sealed. `eqN_zero_nf` sealed. `nf_injective` not
declared (attempt 2 object: `nf_idem` at
`maxFromList` commuting with `succCanon`).
`decEqN_complete` not declared.
H-6e: `insertSub` scans the whole list for a
dominator before placing (the mix that made `nf`
not idempotent). `IsCanon` / `isCanonAtom` /
`nf_canonAtom` / `isCanon_of_atom` sealed.
`nf_idem` / `isCanon_nf` / `nf_of_isCanon` (full)
not declared (attempt 2 of `nf_idem`: the
sorted-antichain identity of `foldlIns` did not
close). `nf_injective` not declared (needs
canonicity). `decEqN` not rebased. No sorry,
axiom, Classical, native_decide, bare simp,
bare omega. closure_claim stays 0.
H-6f: antichain invariant of `insertSub`
(preservation; identity when present or
dominated). `levelLt_irrefl` via `Nat.lt_irrefl`
(H-6e's `rfl` on `decide (i < i)`). `nf_of_isCanon`
/ `isCanon_nf` / `nf_idem`; `nf_injective`;
`decEqN_complete` re-based on `nf` if those
close. No rank. closure_claim stays 0.
-/
import rcic.RcicLevelZero

namespace Rcic.Declarative

/-! ## 02 §2 equations (quoted) and DT-026

```
⟦zero⟧ρ       = 0
⟦succ l⟧ρ     = ⟦l⟧ρ + 1
⟦max a b⟧ρ    = max(⟦a⟧ρ, ⟦b⟧ρ)
⟦imax a b⟧ρ   = 0                 if ⟦b⟧ρ = 0
                 max(⟦a⟧ρ, ⟦b⟧ρ)  otherwise
⟦param i⟧ρ    = ρ(i)

l₁ =ₙ l₂  := ∀ρ, ⟦l₁⟧ρ = ⟦l₂⟧ρ
```

Landed `eval` is partial (`Option Nat`): an unbound `param`
evaluates to `none`, and `eqN` compares `Option Nat` at every ρ.
DT-026: level equality is decidable. -/

/-- Dual of `levelIsZero`: never `some 0` (may still be `none`). -/
def levelNeverZero : Level → Bool
  | .zero => false
  | .succ _ => true
  | .max a b => levelNeverZero a || levelNeverZero b
  | .imax _ b => levelNeverZero b
  | .param _ => false

theorem and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases ha : a with
  | false =>
      rw [ha] at h
      exact Bool.noConfusion h
  | true =>
      cases hb : b with
      | false =>
          rw [ha, hb] at h
          exact Bool.noConfusion h
      | true => exact ⟨rfl, rfl⟩

theorem or_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases ha : a with
  | true => exact Or.inl rfl
  | false =>
      cases hb : b with
      | true => exact Or.inr rfl
      | false =>
          rw [ha, hb] at h
          exact Bool.noConfusion h

theorem levelNeverZero_not_zero (l : Level)
    (ρ : Nat → Option Nat) (h : levelNeverZero l = true) :
    eval ρ l ≠ some 0 := by
  induction l generalizing ρ with
  | zero => exact Bool.noConfusion h
  | succ l _ih =>
      intro hz
      simp only [eval] at hz
      cases he : eval ρ l with
      | none =>
          rw [he] at hz
          exact Option.noConfusion hz
      | some x =>
          rw [he] at hz
          injection hz with hz'
          exact Nat.succ_ne_zero x hz'
  | max a b iha ihb =>
      intro hz
      have hm := (eval_max_eq_zero ρ a b).mp hz
      simp only [levelNeverZero] at h
      cases ha : levelNeverZero a with
      | true => exact iha ρ ha hm.left
      | false =>
          cases hb : levelNeverZero b with
          | true => exact ihb ρ hb hm.right
          | false =>
              rw [ha, hb] at h
              exact Bool.noConfusion h
  | imax a b _iha ihb =>
      intro hz
      simp only [levelNeverZero] at h
      exact ihb ρ h ((eval_imax_eq_zero ρ a b).mp hz)
  | param i => exact Bool.noConfusion h

theorem eqN_max_diag (a : Level) : eqN (.max a a) a := by
  intro ρ
  simp only [eval]
  cases ha : eval ρ a with
  | none => rfl
  | some x => exact congrArg some (Nat.max_self x)

theorem eqN_max_zero_left (u : Level) : eqN (.max .zero u) u := by
  intro ρ
  simp only [eval]
  cases hu : eval ρ u with
  | none => rfl
  | some x => exact congrArg some (Nat.zero_max x)

theorem eqN_max_comm (a b : Level) : eqN (.max a b) (.max b a) := by
  intro ρ
  simp only [eval]
  cases ha : eval ρ a with
  | none =>
      cases hb : eval ρ b with
      | none => rfl
      | some _ => rfl
  | some x =>
      cases hb : eval ρ b with
      | none => rfl
      | some y => exact congrArg some (Nat.max_comm x y)

theorem eqN_congr_max {a a' b b' : Level}
    (ha : eqN a a') (hb : eqN b b') :
    eqN (.max a b) (.max a' b') := by
  intro ρ
  simp only [eval, ha ρ, hb ρ]

theorem eqN_congr_imax {a a' b b' : Level}
    (ha : eqN a a') (hb : eqN b b') :
    eqN (.imax a b) (.imax a' b') := by
  intro ρ
  simp only [eval, ha ρ, hb ρ]

theorem eqN_congr_succ {a a' : Level} (h : eqN a a') :
    eqN (.succ a) (.succ a') := by
  intro ρ
  simp only [eval, h ρ]

/-- `imax (imax x b) b =ₙ imax x b` (partial valuations). -/
theorem eqN_imax_nest (x b : Level) :
    eqN (.imax (.imax x b) b) (.imax x b) := by
  intro ρ
  simp only [eval]
  cases hb : eval ρ b with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ y =>
          cases hx : eval ρ x with
          | none => rfl
          | some t =>
              exact congrArg some
                (Nat.max_eq_left (Nat.le_max_right t (y + 1)))

/-- `imax (max x b) b =ₙ imax x b`. -/
theorem eqN_imax_max_snd (x b : Level) :
    eqN (.imax (.max x b) b) (.imax x b) := by
  intro ρ
  simp only [eval]
  cases hb : eval ρ b with
  | none =>
      cases eval ρ x with
      | none => rfl
      | some _ => rfl
  | some y =>
      cases y with
      | zero =>
          cases eval ρ x with
          | none => rfl
          | some _ => rfl
      | succ y =>
          cases hx : eval ρ x with
          | none => rfl
          | some t =>
              exact congrArg some
                (Nat.max_eq_left
                  (Nat.le_max_right t (y + 1)))

/-- `imax (max b y) b =ₙ imax y b`. -/
theorem eqN_imax_max_fst (y b : Level) :
    eqN (.imax (.max b y) b) (.imax y b) := by
  intro ρ
  simp only [eval]
  cases hb : eval ρ b with
  | none => rfl
  | some yb =>
      cases hy : eval ρ y with
      | none =>
          cases yb with
          | zero => rfl
          | succ _ => rfl
      | some t =>
          cases yb with
          | zero => rfl
          | succ yb =>
              have hswap :
                  max (max (yb + 1) t) (yb + 1) =
                    max t (yb + 1) := by
                rw [Nat.max_comm (yb + 1) t]
                exact Nat.max_eq_left
                  (Nat.le_max_right t (yb + 1))
              exact congrArg some hswap

/-- Local join of two already-reduced max arguments. -/
def maxJoin (a b : Level) : Level :=
  match decide (a = b), levelIsZero a, levelIsZero b with
  | true, _, _ => a
  | false, true, _ => b
  | false, false, true => a
  | false, false, false => .max a b

theorem maxJoin_eqN (a b : Level) : eqN (.max a b) (maxJoin a b) := by
  unfold maxJoin
  cases h : decide (a = b) with
  | true =>
      have heq : a = b := of_decide_eq_true h
      subst heq
      exact eqN_max_diag a
  | false =>
      cases ha : levelIsZero a with
      | true =>
          have hz : eqN a .zero := (levelIsZero_iff a).mp ha
          intro ρ
          simp only [eval]
          have haρ := hz ρ
          simp only [eval] at haρ
          rw [haρ]
          cases hb : eval ρ b with
          | none => rfl
          | some x => exact congrArg some (Nat.zero_max x)
      | false =>
          cases hbz : levelIsZero b with
          | true =>
              have hz : eqN b .zero := (levelIsZero_iff b).mp hbz
              intro ρ
              have hmax := eqN_max_zero_right a ρ
              simp only [eval] at hmax
              have hbρ := hz ρ
              simp only [eval] at hbρ
              change eval ρ (.max a b) = eval ρ a
              simp only [eval, hbρ]
              exact hmax
          | false =>
              exact fun _ => rfl

/-- Local 02-§2 identities on already-reduced imax arguments.
H-6's join missed `imax 0 u = u` (`eqN_imax_zero_left`); that is
the #4343 wall (`imax 0 (param i)` vs `param i`). Flatten of
`imax (imax x y) y` and `imax (max x y) y` is one constructor
deep (reduce is bottom-up; no recursive call on a constructed
node). -/
def imaxJoin (a' b' : Level) : Level :=
  match decide (a' = b'), levelIsZero b',
        levelIsZero a', levelNeverZero b' with
  | true, _, _, _ => b'
  | false, true, _, _ => .zero
  | false, false, true, _ => b'
  | false, false, false, true => maxJoin a' b'
  | false, false, false, false =>
      match a' with
      | .imax x y =>
          match decide (y = b') with
          | true =>
              match decide (x = b'), levelIsZero x with
              | true, _ => b'
              | false, true => b'
              | false, false => .imax x b'
          | false => .imax a' b'
      | .max x y =>
          match decide (y = b') with
          | true =>
              match decide (x = b'), levelIsZero x with
              | true, _ => b'
              | false, true => b'
              | false, false => .imax x b'
          | false =>
              match decide (x = b') with
              | true =>
                  match decide (y = b'),
                        levelIsZero y with
                  | true, _ => b'
                  | false, true => b'
                  | false, false => .imax y b'
              | false => .imax a' b'
      | _ => .imax a' b'

/-- Constructor recursion on children, then 02-§2 identities.
Not a rank: no recursive call on the constructed node. -/
def reduce : Level → Level
  | .zero => .zero
  | .succ l => .succ (reduce l)
  | .max a b => maxJoin (reduce a) (reduce b)
  | .imax a b => imaxJoin (reduce a) (reduce b)
  | .param i => .param i

theorem reduce_eqN_imax_flat (a b : Level)
    (iha : eqN a (reduce a)) (ihb : eqN b (reduce b))
    (_h : decide (reduce a = reduce b) = false)
    (_hbz : levelIsZero (reduce b) = false)
    (haz : levelIsZero (reduce a) = false)
    (_hnev : levelNeverZero (reduce b) = false) :
    eqN (.imax a b)
      (match reduce a with
       | .imax x y =>
           match decide (y = reduce b) with
           | true =>
               match decide (x = reduce b),
                     levelIsZero x with
               | true, _ => reduce b
               | false, true => reduce b
               | false, false => .imax x (reduce b)
           | false => .imax (reduce a) (reduce b)
       | .max x y =>
           match decide (y = reduce b) with
           | true =>
               match decide (x = reduce b),
                     levelIsZero x with
               | true, _ => reduce b
               | false, true => reduce b
               | false, false => .imax x (reduce b)
           | false =>
               match decide (x = reduce b) with
               | true =>
                   match decide (y = reduce b),
                         levelIsZero y with
                   | true, _ => reduce b
                   | false, true => reduce b
                   | false, false => .imax y (reduce b)
               | false => .imax (reduce a) (reduce b)
       | _ => .imax (reduce a) (reduce b)) := by
  have hcong := eqN_congr_imax iha ihb
  cases ha' : reduce a with
  | zero =>
      rw [ha'] at haz
      exact Bool.noConfusion haz
  | succ l =>
      simp only [ha']
      intro ρ
      have hc := hcong ρ
      rw [ha'] at hc
      exact hc
  | param i =>
      simp only [ha']
      intro ρ
      have hc := hcong ρ
      rw [ha'] at hc
      exact hc
  | imax x y =>
      simp only [ha']
      cases hy : decide (y = reduce b) with
      | false =>
          intro ρ
          have hc := hcong ρ
          rw [ha'] at hc
          exact hc
      | true =>
          have hyeq : y = reduce b :=
            of_decide_eq_true hy
          cases hx : decide (x = reduce b) with
          | true =>
              have hxeq : x = reduce b :=
                of_decide_eq_true hx
              intro ρ
              have hc := hcong ρ
              rw [ha', hyeq, hxeq] at hc
              have hn :=
                eqN_imax_nest (reduce b) (reduce b) ρ
              have hd := eqN_imax_diag (reduce b) ρ
              exact hc.trans (hn.trans hd)
          | false =>
              cases hxz : levelIsZero x with
              | true =>
                  have hx0 : eqN x .zero :=
                    (levelIsZero_iff x).mp hxz
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hyeq] at hc
                  have hchain :=
                    (eqN_imax_nest x (reduce b) ρ).trans
                      ((eqN_congr_imax hx0
                          (fun _ => rfl) ρ).trans
                        (eqN_imax_zero_left
                          (reduce b) ρ))
                  exact hc.trans hchain
              | false =>
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hyeq] at hc
                  have hn :=
                    eqN_imax_nest x (reduce b) ρ
                  exact hc.trans hn
  | max x y =>
      simp only [ha']
      cases hy : decide (y = reduce b) with
      | true =>
          have hyeq : y = reduce b :=
            of_decide_eq_true hy
          cases hx : decide (x = reduce b) with
          | true =>
              have hxeq : x = reduce b :=
                of_decide_eq_true hx
              intro ρ
              have hc := hcong ρ
              rw [ha', hyeq, hxeq] at hc
              have hm :=
                eqN_imax_max_snd (reduce b) (reduce b) ρ
              have hd := eqN_imax_diag (reduce b) ρ
              exact hc.trans (hm.trans hd)
          | false =>
              cases hxz : levelIsZero x with
              | true =>
                  have hx0 : eqN x .zero :=
                    (levelIsZero_iff x).mp hxz
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hyeq] at hc
                  have hchain :=
                    (eqN_imax_max_snd x (reduce b) ρ).trans
                      ((eqN_congr_imax hx0
                          (fun _ => rfl) ρ).trans
                        (eqN_imax_zero_left
                          (reduce b) ρ))
                  exact hc.trans hchain
              | false =>
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hyeq] at hc
                  have hm :=
                    eqN_imax_max_snd x (reduce b) ρ
                  exact hc.trans hm
      | false =>
          cases hx : decide (x = reduce b) with
          | false =>
              intro ρ
              have hc := hcong ρ
              rw [ha'] at hc
              exact hc
          | true =>
              have hxeq : x = reduce b :=
                of_decide_eq_true hx
              cases hyz : levelIsZero y with
              | true =>
                  have hy0 : eqN y .zero :=
                    (levelIsZero_iff y).mp hyz
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hxeq] at hc
                  have hchain :=
                    (eqN_imax_max_fst y (reduce b) ρ).trans
                      ((eqN_congr_imax hy0
                          (fun _ => rfl) ρ).trans
                        (eqN_imax_zero_left
                          (reduce b) ρ))
                  exact hc.trans hchain
              | false =>
                  intro ρ
                  have hc := hcong ρ
                  rw [ha', hxeq] at hc
                  have hm :=
                    eqN_imax_max_fst y (reduce b) ρ
                  exact hc.trans hm

theorem reduce_eqN (l : Level) : eqN l (reduce l) := by
  induction l with
  | zero => exact fun _ => rfl
  | succ l ih => exact eqN_congr_succ ih
  | max a b iha ihb =>
      intro ρ
      have hm := maxJoin_eqN (reduce a) (reduce b) ρ
      have hc := eqN_congr_max iha ihb ρ
      simp only [reduce]
      exact hc.trans hm
  | imax a b iha ihb =>
      have hcong := eqN_congr_imax iha ihb
      unfold reduce
      unfold imaxJoin
      cases h : decide (reduce a = reduce b) with
      | true =>
          have heq : reduce a = reduce b :=
            of_decide_eq_true h
          have hdiag := eqN_imax_diag (reduce b)
          intro ρ
          have hc := hcong ρ
          simp only [eval] at hc
          rw [heq] at hc
          have hd := hdiag ρ
          simp only [eval] at hd
          exact hc.trans hd
      | false =>
          cases hbz : levelIsZero (reduce b) with
          | true =>
              have hz : eqN (reduce b) .zero :=
                (levelIsZero_iff (reduce b)).mp hbz
              have him :=
                (eqN_imax_zero_iff (reduce a)
                  (reduce b)).mpr hz
              intro ρ
              exact (hcong ρ).trans (him ρ)
          | false =>
              cases haz : levelIsZero (reduce a) with
              | true =>
                  have h0 : eqN (reduce a) .zero :=
                    (levelIsZero_iff (reduce a)).mp haz
                  have hiz :=
                    eqN_imax_zero_left (reduce b)
                  intro ρ
                  have hc := hcong ρ
                  have ha0 := h0 ρ
                  simp only [eval] at ha0
                  have hi := hiz ρ
                  simp only [eval] at hi
                  simp only [eval] at hc
                  rw [ha0] at hc
                  exact hc.trans hi
              | false =>
                  cases hnev :
                    levelNeverZero (reduce b) with
                  | true =>
                      have hm :=
                        maxJoin_eqN (reduce a) (reduce b)
                      intro ρ
                      have hc := hcong ρ
                      have himax_max :
                          eval ρ (.imax (reduce a)
                            (reduce b)) =
                            eval ρ (.max (reduce a)
                              (reduce b)) := by
                        simp only [eval]
                        cases hb : eval ρ (reduce b) with
                        | none =>
                            cases eval ρ (reduce a) with
                            | none => rfl
                            | some _ => rfl
                        | some y =>
                            cases y with
                            | zero =>
                                exact False.elim
                                  (levelNeverZero_not_zero
                                    (reduce b) ρ hnev hb)
                            | succ y =>
                                cases eval ρ (reduce a) with
                                | none => rfl
                                | some _ => rfl
                      exact hc.trans
                        (himax_max.trans (hm ρ))
                  | false =>
                      exact reduce_eqN_imax_flat
                        a b iha ihb h hbz haz hnev
  | param i => exact fun _ => rfl


/-! ## `geq`: `u` dominates `v + k` on defined values.

Structural on the second argument (its subterms). -/

def geqZero : Level → Nat → Bool
  | _, 0 => true
  | .zero, Nat.succ _ => false
  | .succ u, Nat.succ k => geqZero u k
  | .max a b, k => geqZero a k || geqZero b k
  | .imax a b, Nat.succ k =>
      levelNeverZero b &&
        (geqZero a (Nat.succ k) || geqZero b (Nat.succ k))
  | .param _, Nat.succ _ => false

def geqParam : Level → Nat → Nat → Bool
  | .zero, _, _ => false
  | .succ u, j, 0 => geqParam u j 0
  | .succ u, j, Nat.succ k => geqParam u j k
  | .max a b, j, k => geqParam a j k || geqParam b j k
  | .imax a b, j, k =>
      if levelIsZero b then false
      else if levelNeverZero b then
        geqParam a j k || geqParam b j k
      else geqParam b j k
  | .param i, j, k => decide (i = j) && decide (k = 0)

def geq : Level → Level → Nat → Bool
  | u, .succ v, k => geq u v k.succ
  | u, .max a b, k => geq u a k && geq u b k
  | u, .imax a b, k =>
      if levelIsZero b then geqZero u k
      else if levelNeverZero b then geq u a k && geq u b k
      else (geqZero u k && geq u a k) && geq u b k
  | u, .zero, k => geqZero u k
  | u, .param j, k => geqParam u j k

def rigid (l1 l2 : Level) : Bool :=
  match decide (l1 = l2) with
  | true => true
  | false => geq l1 l2 0 && geq l2 l1 0

/- DT-026 decider. R-DecEqNNf: restructured after
`nf` as `decide (nf l1 = nf l2)`. The `reduce`/`geq`
form is retired. -/

theorem geqZero_le (u : Level) (k : Nat) (ρ : Nat → Option Nat)
    (x : Nat) (hu : eval ρ u = some x) (hg : geqZero u k = true) :
    k ≤ x := by
  induction u generalizing k x ρ with
  | zero =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
          simp only [eval] at hu
          injection hu with hu'
          subst hu'
          exact Bool.noConfusion hg
  | succ u ih =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
          simp only [eval] at hu
          cases he : eval ρ u with
          | none =>
              rw [he] at hu
              exact Option.noConfusion hu
          | some y =>
              rw [he] at hu
              injection hu with hu'
              subst hu'
              exact Nat.succ_le_succ (ih k ρ y he hg)
  | max a b iha ihb =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
          simp only [geqZero] at hg
          have hor := or_true hg
          simp only [eval] at hu
          cases hae : eval ρ a with
          | none =>
              rw [hae] at hu
              exact Option.noConfusion hu
          | some xa =>
              cases hbe : eval ρ b with
              | none =>
                  rw [hae, hbe] at hu
                  exact Option.noConfusion hu
              | some xb =>
                  rw [hae, hbe] at hu
                  injection hu with hu'
                  subst hu'
                  cases hor with
                  | inl ha =>
                      exact Nat.le_trans
                        (iha (Nat.succ k) ρ xa hae ha)
                        (Nat.le_max_left xa xb)
                  | inr hb =>
                      exact Nat.le_trans
                        (ihb (Nat.succ k) ρ xb hbe hb)
                        (Nat.le_max_right xa xb)
  | imax a b iha ihb =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
          simp only [geqZero] at hg
          have hand := and_true hg
          have hor := or_true hand.right
          have hnev := hand.left
          have hz := levelNeverZero_not_zero b ρ hnev
          simp only [eval] at hu
          cases hbe : eval ρ b with
          | none =>
              rw [hbe] at hu
              exact Option.noConfusion hu
          | some y =>
              cases y with
              | zero => exact False.elim (hz hbe)
              | succ y =>
                  cases hae : eval ρ a with
                  | none =>
                      rw [hbe, hae] at hu
                      exact Option.noConfusion hu
                  | some xa =>
                      rw [hbe, hae] at hu
                      injection hu with hu'
                      subst hu'
                      cases hor with
                      | inl ha =>
                          exact Nat.le_trans
                            (iha (Nat.succ k) ρ xa hae ha)
                            (Nat.le_max_left xa (y + 1))
                      | inr hb =>
                          exact Nat.le_trans
                            (ihb (Nat.succ k) ρ (y + 1) hbe hb)
                            (Nat.le_max_right xa (y + 1))
  | param i =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k => exact Bool.noConfusion hg

theorem geqParam_le (u : Level) (j k : Nat) (ρ : Nat → Option Nat)
    (x y : Nat) (hu : eval ρ u = some x) (hj : ρ j = some y)
    (hg : geqParam u j k = true) : y + k ≤ x := by
  induction u generalizing k x with
  | zero => exact Bool.noConfusion hg
  | succ u ih =>
      simp only [eval] at hu
      cases he : eval ρ u with
      | none =>
          rw [he] at hu
          exact Option.noConfusion hu
      | some x' =>
          rw [he] at hu
          injection hu with hu'
          subst hu'
          cases k with
          | zero =>
              exact Nat.le_trans (ih 0 x' he hg) (Nat.le_succ x')
          | succ k =>
              exact Nat.succ_le_succ (ih k x' he hg)
  | max a b iha ihb =>
      simp only [geqParam] at hg
      have hor := or_true hg
      simp only [eval] at hu
      cases hae : eval ρ a with
      | none =>
          rw [hae] at hu
          exact Option.noConfusion hu
      | some xa =>
          cases hbe : eval ρ b with
          | none =>
              rw [hae, hbe] at hu
              exact Option.noConfusion hu
          | some xb =>
              rw [hae, hbe] at hu
              injection hu with hu'
              subst hu'
              cases hor with
              | inl ha =>
                  exact Nat.le_trans (iha k xa hae ha)
                    (Nat.le_max_left xa xb)
              | inr hb =>
                  exact Nat.le_trans (ihb k xb hbe hb)
                    (Nat.le_max_right xa xb)
  | imax a b iha ihb =>
      simp only [geqParam] at hg
      cases hbz : levelIsZero b with
      | true =>
          rw [hbz] at hg
          exact Bool.noConfusion hg
      | false =>
          rw [hbz] at hg
          cases hnev : levelNeverZero b with
          | false =>
              rw [hnev] at hg
              simp only [eval] at hu
              cases hbe : eval ρ b with
              | none =>
                  rw [hbe] at hu
                  exact Option.noConfusion hu
              | some yb =>
                  cases yb with
                  | zero =>
                      rw [hbe] at hu
                      injection hu with hu'
                      subst hu'
                      exact ihb k 0 hbe hg
                  | succ yb =>
                      cases hae : eval ρ a with
                      | none =>
                          rw [hbe, hae] at hu
                          exact Option.noConfusion hu
                      | some xa =>
                          rw [hbe, hae] at hu
                          injection hu with hu'
                          subst hu'
                          exact Nat.le_trans
                            (ihb k (yb + 1) hbe hg)
                            (Nat.le_max_right xa (yb + 1))
          | true =>
              rw [hnev] at hg
              have hor := or_true hg
              have hz := levelNeverZero_not_zero b ρ hnev
              simp only [eval] at hu
              cases hbe : eval ρ b with
              | none =>
                  rw [hbe] at hu
                  exact Option.noConfusion hu
              | some yb =>
                  cases yb with
                  | zero => exact False.elim (hz hbe)
                  | succ yb =>
                      cases hae : eval ρ a with
                      | none =>
                          rw [hbe, hae] at hu
                          exact Option.noConfusion hu
                      | some xa =>
                          rw [hbe, hae] at hu
                          injection hu with hu'
                          subst hu'
                          cases hor with
                          | inl ha =>
                              exact Nat.le_trans (iha k xa hae ha)
                                (Nat.le_max_left xa (yb + 1))
                          | inr hb =>
                              exact Nat.le_trans
                                (ihb k (yb + 1) hbe hb)
                                (Nat.le_max_right xa (yb + 1))
  | param i =>
      simp only [geqParam] at hg
      have hand := and_true hg
      have hij : i = j := of_decide_eq_true hand.left
      have hk0 : k = 0 := of_decide_eq_true hand.right
      subst hij
      subst hk0
      simp only [eval] at hu
      rw [hj] at hu
      injection hu with hu'
      subst hu'
      exact Nat.le_refl _

theorem geq_le (u v : Level) (k : Nat) (ρ : Nat → Option Nat)
    (x y : Nat) (hu : eval ρ u = some x) (hv : eval ρ v = some y)
    (hg : geq u v k = true) : y + k ≤ x := by
  induction v generalizing u k x y with
  | succ v ih =>
      simp only [eval] at hv
      cases he : eval ρ v with
      | none =>
          rw [he] at hv
          exact Option.noConfusion hv
      | some y' =>
          rw [he] at hv
          injection hv with hv'
          subst hv'
          simp only [geq] at hg
          have hle := ih u k.succ x y' hu he hg
          have : y' + (k + 1) = y' + 1 + k := by
            rw [Nat.add_comm k 1, Nat.add_assoc]
          rw [← this]
          exact hle
  | max a b iha ihb =>
      simp only [geq] at hg
      have hand := and_true hg
      simp only [eval] at hv
      cases hae : eval ρ a with
      | none =>
          rw [hae] at hv
          exact Option.noConfusion hv
      | some ya =>
          cases hbe : eval ρ b with
          | none =>
              rw [hae, hbe] at hv
              exact Option.noConfusion hv
          | some yb =>
              rw [hae, hbe] at hv
              injection hv with hv'
              have ha := iha u k x ya hu hae hand.left
              have hb := ihb u k x yb hu hbe hand.right
              cases Nat.le_total ya yb with
              | inl hle =>
                  have hy : y = yb :=
                    hv'.symm.trans (Nat.max_eq_right hle)
                  exact hy.symm ▸ hb
              | inr hle =>
                  have hy : y = ya :=
                    hv'.symm.trans (Nat.max_eq_left hle)
                  exact hy.symm ▸ ha
  | imax a b iha ihb =>
      simp only [geq] at hg
      cases hbz : levelIsZero b with
      | true =>
          rw [hbz] at hg
          have hz : eqN b .zero := (levelIsZero_iff b).mp hbz
          have hb0 : eval ρ b = some 0 := by
            have := hz ρ
            simp only [eval] at this
            exact this
          simp only [eval] at hv
          rw [hb0] at hv
          injection hv with hv'
          subst hv'
          have hle := geqZero_le u k ρ x hu hg
          exact (Nat.zero_add k).symm ▸ hle
      | false =>
          rw [hbz] at hg
          cases hnev : levelNeverZero b with
          | true =>
              rw [hnev] at hg
              have hand := and_true hg
              have hnz := levelNeverZero_not_zero b ρ hnev
              simp only [eval] at hv
              cases hbe : eval ρ b with
              | none =>
                  rw [hbe] at hv
                  exact Option.noConfusion hv
              | some yb =>
                  cases yb with
                  | zero => exact False.elim (hnz hbe)
                  | succ yb =>
                      cases hae : eval ρ a with
                      | none =>
                          rw [hbe, hae] at hv
                          exact Option.noConfusion hv
                      | some ya =>
                          rw [hbe, hae] at hv
                          injection hv with hv'
                          have ha := iha u k x ya hu hae hand.left
                          have hb := ihb u k x (yb + 1) hu hbe
                            hand.right
                          cases Nat.le_total ya (yb + 1) with
                          | inl hle =>
                              have hy : y = yb + 1 :=
                                hv'.symm.trans (Nat.max_eq_right hle)
                              exact hy.symm ▸ hb
                          | inr hle =>
                              have hy : y = ya :=
                                hv'.symm.trans (Nat.max_eq_left hle)
                              exact hy.symm ▸ ha
          | false =>
              rw [hnev] at hg
              have h1 := and_true hg
              have h2 := and_true h1.left
              simp only [eval] at hv
              cases hbe : eval ρ b with
              | none =>
                  rw [hbe] at hv
                  exact Option.noConfusion hv
              | some yb =>
                  cases yb with
                  | zero =>
                      rw [hbe] at hv
                      injection hv with hv'
                      subst hv'
                      have hle := geqZero_le u k ρ x hu h2.left
                      exact (Nat.zero_add k).symm ▸ hle
                  | succ yb =>
                      cases hae : eval ρ a with
                      | none =>
                          rw [hbe, hae] at hv
                          exact Option.noConfusion hv
                      | some ya =>
                          rw [hbe, hae] at hv
                          injection hv with hv'
                          have ha := iha u k x ya hu hae h2.right
                          have hb := ihb u k x (yb + 1) hu hbe
                            h1.right
                          cases Nat.le_total ya (yb + 1) with
                          | inl hle =>
                              have hy : y = yb + 1 :=
                                hv'.symm.trans (Nat.max_eq_right hle)
                              exact hy.symm ▸ hb
                          | inr hle =>
                              have hy : y = ya :=
                                hv'.symm.trans (Nat.max_eq_left hle)
                              exact hy.symm ▸ ha
  | zero =>
      simp only [eval] at hv
      injection hv with hv'
      subst hv'
      simp only [geq] at hg
      have hle := geqZero_le u k ρ x hu hg
      exact (Nat.zero_add k).symm ▸ hle
  | param j =>
      simp only [eval] at hv
      simp only [geq] at hg
      exact geqParam_le u j k ρ x y hu hv hg

theorem geqParam_undef (v : Level) (j k : Nat)
    (ρ : Nat → Option Nat) (hj : ρ j = none)
    (hg : geqParam v j k = true) : eval ρ v = none := by
  induction v generalizing k with
  | zero => exact Bool.noConfusion hg
  | succ v ih =>
      cases k with
      | zero =>
          simp only [eval]
          rw [ih 0 hg]
          rfl
      | succ k =>
          simp only [eval]
          rw [ih k hg]
          rfl
  | max a b iha ihb =>
      simp only [geqParam] at hg
      have hor := or_true hg
      simp only [eval]
      cases hor with
      | inl ha =>
          rw [iha k ha]
          rfl
      | inr hb =>
          cases hae : eval ρ a with
          | none => rfl
          | some _ =>
              rw [ihb k hb]
              rfl
  | imax a b iha ihb =>
      simp only [geqParam] at hg
      cases hbz : levelIsZero b with
      | true =>
          rw [hbz] at hg
          exact Bool.noConfusion hg
      | false =>
          rw [hbz] at hg
          cases hnev : levelNeverZero b with
          | false =>
              rw [hnev] at hg
              simp only [eval]
              rw [ihb k hg]
              rfl
          | true =>
              rw [hnev] at hg
              have hor := or_true hg
              simp only [eval]
              cases hor with
              | inl ha =>
                  cases hbe : eval ρ b with
                  | none => rfl
                  | some y =>
                      cases y with
                      | zero =>
                          exact False.elim
                            (levelNeverZero_not_zero b ρ hnev hbe)
                      | succ y =>
                          rw [iha k ha]
                          rfl
              | inr hb =>
                  rw [ihb k hb]
                  rfl
  | param i =>
      simp only [geqParam] at hg
      have hand := and_true hg
      have hij : i = j := of_decide_eq_true hand.left
      subst hij
      simp only [eval, hj]

theorem geq_undef (v u : Level) (k : Nat) (ρ : Nat → Option Nat)
    (hu : eval ρ u = none) (hg : geq v u k = true) :
    eval ρ v = none := by
  induction u generalizing v k with
  | succ u ih =>
      simp only [eval] at hu
      cases he : eval ρ u with
      | none =>
          simp only [geq] at hg
          exact ih v k.succ he hg
      | some x =>
          rw [he] at hu
          exact Option.noConfusion hu
  | max a b iha ihb =>
      simp only [geq] at hg
      have hand := and_true hg
      simp only [eval] at hu
      cases hae : eval ρ a with
      | none => exact iha v k hae hand.left
      | some _ =>
          cases hbe : eval ρ b with
          | none => exact ihb v k hbe hand.right
          | some _ =>
              rw [hae, hbe] at hu
              exact Option.noConfusion hu
  | imax a b iha ihb =>
      simp only [geq] at hg
      cases hbz : levelIsZero b with
      | true =>
          have hz : eqN b .zero := (levelIsZero_iff b).mp hbz
          have hb0 : eval ρ b = some 0 := by
            have := hz ρ
            simp only [eval] at this
            exact this
          simp only [eval] at hu
          rw [hb0] at hu
          exact Option.noConfusion hu
      | false =>
          rw [hbz] at hg
          cases hnev : levelNeverZero b with
          | true =>
              rw [hnev] at hg
              have hand := and_true hg
              simp only [eval] at hu
              cases hbe : eval ρ b with
              | none => exact ihb v k hbe hand.right
              | some y =>
                  cases y with
                  | zero =>
                      exact False.elim
                        (levelNeverZero_not_zero b ρ hnev hbe)
                  | succ y =>
                      cases hae : eval ρ a with
                      | none => exact iha v k hae hand.left
                      | some _ =>
                          rw [hbe, hae] at hu
                          exact Option.noConfusion hu
          | false =>
              rw [hnev] at hg
              have h1 := and_true hg
              have h2 := and_true h1.left
              simp only [eval] at hu
              cases hbe : eval ρ b with
              | none => exact ihb v k hbe h1.right
              | some y =>
                  cases y with
                  | zero =>
                      rw [hbe] at hu
                      exact Option.noConfusion hu
                  | succ y =>
                      cases hae : eval ρ a with
                      | none => exact iha v k hae h2.right
                      | some _ =>
                          rw [hbe, hae] at hu
                          exact Option.noConfusion hu
  | zero =>
      simp only [eval] at hu
      exact Option.noConfusion hu
  | param j =>
      simp only [eval] at hu
      simp only [geq] at hg
      exact geqParam_undef v j k ρ hu hg

theorem rigid_sound {l1 l2 : Level} (h : rigid l1 l2 = true) :
    eqN l1 l2 := by
  intro ρ
  unfold rigid at h
  cases heq : decide (l1 = l2) with
  | true =>
      have h12 : l1 = l2 := of_decide_eq_true heq
      subst h12
      rfl
  | false =>
      rw [heq] at h
      have hand := and_true h
      cases h1 : eval ρ l1 with
      | none =>
          cases h2 : eval ρ l2 with
          | none => rfl
          | some y =>
              have hun := geq_undef l2 l1 0 ρ h1 hand.right
              rw [h2] at hun
              exact Option.noConfusion hun
      | some x =>
          cases h2 : eval ρ l2 with
          | none =>
              have hun := geq_undef l1 l2 0 ρ h2 hand.left
              rw [h1] at hun
              exact Option.noConfusion hun
          | some y =>
              have hxy := geq_le l1 l2 0 ρ x y h1 h2 hand.left
              have hyx := geq_le l2 l1 0 ρ y x h2 h1 hand.right
              rw [Nat.add_zero] at hxy hyx
              exact congrArg some (Nat.le_antisymm hyx hxy)

/- SOUNDNESS moved with `decEqN` (R-DecEqNNf). -/

/-! ## Completeness (H-6b). Start from the #4343 wall:
the unbound `param` under `imax` / `max`. When `eval` is
`some`, filling `none` with `0` preserves the value (the
transport attempt 2 was missing). `eqN` on partial
valuations is the definedness agreement plus the filled
total comparison. -/

def evalTotal (σ : Nat → Nat) : Level → Nat
  | .zero => 0
  | .succ l => evalTotal σ l + 1
  | .max a b =>
      max (evalTotal σ a) (evalTotal σ b)
  | .imax a b =>
      let y := evalTotal σ b
      if y = 0 then 0 else max (evalTotal σ a) y
  | .param i => σ i

theorem eval_total (σ : Nat → Nat) (l : Level) :
    eval (fun i => some (σ i)) l =
      some (evalTotal σ l) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      simp only [eval, evalTotal, ih]
      rfl
  | max a b iha ihb =>
      simp only [eval, evalTotal, iha, ihb]
      rfl
  | imax a b iha ihb =>
      simp only [eval, evalTotal, iha, ihb]
      cases hy : evalTotal σ b with
      | zero => rfl
      | succ _ => rfl
  | param i => rfl

theorem max_le_max {a b c d : Nat}
    (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d := by
  cases Nat.le_total a b with
  | inl h =>
      have hm : max a b = b := Nat.max_eq_right h
      rw [hm]
      exact Nat.le_trans h2 (Nat.le_max_right c d)
  | inr h =>
      have hm : max a b = a := Nat.max_eq_left h
      rw [hm]
      exact Nat.le_trans h1 (Nat.le_max_left c d)

theorem evalTotal_mono (σ τ : Nat → Nat)
    (h : ∀ i, σ i ≤ τ i) (l : Level) :
    evalTotal σ l ≤ evalTotal τ l := by
  induction l with
  | zero => exact Nat.zero_le _
  | succ l ih => exact Nat.succ_le_succ ih
  | max a b iha ihb =>
      exact max_le_max iha ihb
  | imax a b iha ihb =>
      simp only [evalTotal]
      cases hσ : evalTotal σ b with
      | zero => exact Nat.zero_le _
      | succ n =>
          cases hτ : evalTotal τ b with
          | zero =>
              have hle := ihb
              rw [hσ, hτ] at hle
              exact False.elim
                (Nat.succ_ne_zero n
                  (Nat.eq_zero_of_le_zero hle))
          | succ m =>
              have hle := ihb
              rw [hσ, hτ] at hle
              exact max_le_max iha hle
  | param i => exact h i

/-- If `eval` is `some`, the unbound params were not
needed; filling them with `0` keeps the value. This is
the transport #4343 attempt 2 lacked
(`splitParam_none`). -/
theorem eval_some_fill (ρ : Nat → Option Nat)
    (l : Level) (x : Nat)
    (h : eval ρ l = some x) :
    eval (fun i => some ((ρ i).getD 0)) l =
      some x := by
  induction l generalizing x with
  | zero =>
      simp only [eval] at h
      injection h with h'
      subst h'
      rfl
  | succ l ih =>
      simp only [eval] at h
      cases he : eval ρ l with
      | none =>
          rw [he] at h
          exact Option.noConfusion h
      | some x' =>
          rw [he] at h
          injection h with h'
          subst h'
          have ih' := ih x' he
          simp only [eval, ih']
          rfl
  | max a b iha ihb =>
      simp only [eval] at h
      cases ha : eval ρ a with
      | none =>
          rw [ha] at h
          exact Option.noConfusion h
      | some xa =>
          cases hb : eval ρ b with
          | none =>
              rw [ha, hb] at h
              exact Option.noConfusion h
          | some xb =>
              rw [ha, hb] at h
              injection h with h'
              subst h'
              have iha' := iha xa ha
              have ihb' := ihb xb hb
              simp only [eval, iha', ihb']
              rfl
  | imax a b iha ihb =>
      simp only [eval] at h
      cases hb : eval ρ b with
      | none =>
          rw [hb] at h
          exact Option.noConfusion h
      | some y =>
          cases y with
          | zero =>
              rw [hb] at h
              injection h with h'
              subst h'
              have ihb' := ihb 0 hb
              simp only [eval, ihb']
              rfl
          | succ y =>
              cases ha : eval ρ a with
              | none =>
                  rw [hb, ha] at h
                  exact Option.noConfusion h
              | some xa =>
                  rw [hb, ha] at h
                  injection h with h'
                  subst h'
                  have iha' := iha xa ha
                  have ihb' := ihb (y + 1) hb
                  simp only [eval, iha', ihb']
                  rfl
  | param i =>
      simp only [eval] at h
      simp only [eval, h]
      rfl

theorem eval_some_total_le (ρ : Nat → Option Nat)
    (l : Level) (x : Nat)
    (h : eval ρ l = some x) :
    evalTotal (fun _ => 0) l ≤ x := by
  have hf := eval_some_fill ρ l x h
  have ht := eval_total (fun i => (ρ i).getD 0) l
  rw [hf] at ht
  injection ht with ht'
  subst ht'
  exact evalTotal_mono (fun _ => 0)
    (fun i => (ρ i).getD 0)
    (fun _ => Nat.zero_le _) l

theorem neverZero_false_evalTotal0 (l : Level)
    (h : levelNeverZero l = false) :
    evalTotal (fun _ => 0) l = 0 := by
  induction l with
  | zero => rfl
  | succ l _ih => exact Bool.noConfusion h
  | max a b iha ihb =>
      simp only [levelNeverZero] at h
      cases ha : levelNeverZero a with
      | true =>
          rw [ha] at h
          exact Bool.noConfusion h
      | false =>
          cases hb : levelNeverZero b with
          | true =>
              rw [ha, hb] at h
              exact Bool.noConfusion h
          | false =>
              simp only [evalTotal, iha ha, ihb hb]
              rfl
  | imax a b _iha ihb =>
      simp only [levelNeverZero] at h
      simp only [evalTotal, ihb h]
      rfl
  | param i => rfl

theorem geqZero_or_true (a : Bool) :
    (a || true) = true := by
  cases a <;> rfl

theorem geqZero_complete (u : Level) (k : Nat)
    (hval : ∀ ρ x, eval ρ u = some x → k ≤ x) :
    geqZero u k = true := by
  induction u generalizing k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k =>
          exfalso
          have hle := hval (fun _ => some 0) 0 rfl
          exact Nat.not_succ_le_zero k hle
  | succ u ih =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [geqZero]
          refine ih k ?_
          intro ρ x hx
          have hu :
              eval ρ (.succ u) = some (x + 1) := by
            simp only [eval, hx]
            rfl
          have hle := hval ρ (x + 1) hu
          exact Nat.le_of_succ_le_succ hle
  | max a b iha ihb =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [geqZero]
          have hm0 :=
            eval_total (fun _ => 0) (.max a b)
          have hle0 :=
            hval (fun _ => some 0)
              (evalTotal (fun _ => 0) (.max a b)) hm0
          simp only [evalTotal] at hle0
          cases Nat.le_total
              (evalTotal (fun _ => 0) a)
              (evalTotal (fun _ => 0) b) with
          | inl hab =>
              have hb0 : Nat.succ k ≤
                  evalTotal (fun _ => 0) b := by
                have hm :
                    max (evalTotal (fun _ => 0) a)
                      (evalTotal (fun _ => 0) b) =
                      evalTotal (fun _ => 0) b :=
                  Nat.max_eq_right hab
                rw [hm] at hle0
                exact hle0
              have hchild :
                  geqZero b (Nat.succ k) = true :=
                ihb (Nat.succ k) (fun ρ x hx =>
                  Nat.le_trans hb0
                    (eval_some_total_le ρ b x hx))
              simp only [hchild]
              exact geqZero_or_true _
          | inr hba =>
              have ha0 : Nat.succ k ≤
                  evalTotal (fun _ => 0) a := by
                have hm :
                    max (evalTotal (fun _ => 0) a)
                      (evalTotal (fun _ => 0) b) =
                      evalTotal (fun _ => 0) a :=
                  Nat.max_eq_left hba
                rw [hm] at hle0
                exact hle0
              have hchild :
                  geqZero a (Nat.succ k) = true :=
                iha (Nat.succ k) (fun ρ x hx =>
                  Nat.le_trans ha0
                    (eval_some_total_le ρ a x hx))
              simp only [hchild]
              rfl
  | imax a b _iha ihb =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [geqZero]
          cases hnev : levelNeverZero b with
          | false =>
              exfalso
              have hz :=
                neverZero_false_evalTotal0 b hnev
              have hm0 :=
                eval_total (fun _ => 0) (.imax a b)
              have hle0 :=
                hval (fun _ => some 0)
                  (evalTotal (fun _ => 0) (.imax a b))
                  hm0
              simp only [evalTotal, hz] at hle0
              exact Nat.not_succ_le_zero k hle0
          | true =>
              have hm0 :=
                eval_total (fun _ => 0) (.imax a b)
              have hle0 :=
                hval (fun _ => some 0)
                  (evalTotal (fun _ => 0) (.imax a b))
                  hm0
              simp only [evalTotal] at hle0
              have hbpos :
                  evalTotal (fun _ => 0) b ≠ 0 := by
                intro hz
                have hnv :=
                  neverZero_false_evalTotal0 b
                -- neverZero is true, so this does not
                -- apply. Use: imax at zeros with b=0
                -- is 0, contradicting k+1 ≤ imax.
                simp only [hz] at hle0
                exact Nat.succ_ne_zero k
                  (Nat.eq_zero_of_le_zero hle0)
              -- imax = max a b at zeros
              cases hy : evalTotal (fun _ => 0) b with
              | zero => exact False.elim (hbpos hy)
              | succ n =>
                  simp only [hy] at hle0
                  cases Nat.le_total
                      (evalTotal (fun _ => 0) a)
                      (n + 1) with
                  | inl hab =>
                      have hb0 : Nat.succ k ≤
                          evalTotal (fun _ => 0) b := by
                        simp only [hy]
                        have hm :
                            max (evalTotal (fun _ => 0) a)
                              (n + 1) = n + 1 :=
                          Nat.max_eq_right hab
                        rw [hm] at hle0
                        exact hle0
                      have hchild :
                          geqZero b (Nat.succ k) =
                            true :=
                        ihb (Nat.succ k)
                          (fun ρ x hx =>
                            Nat.le_trans hb0
                              (eval_some_total_le
                                ρ b x hx))
                      cases ha :
                          geqZero a (Nat.succ k) with
                      | true =>
                          simp only [ha, hchild]
                          rfl
                      | false =>
                          simp only [ha, hchild]
                          rfl
                  | inr hba =>
                      have ha0 : Nat.succ k ≤
                          evalTotal (fun _ => 0) a := by
                        have hm :
                            max (evalTotal (fun _ => 0) a)
                              (n + 1) =
                              evalTotal (fun _ => 0) a :=
                          Nat.max_eq_left hba
                        rw [hm] at hle0
                        exact hle0
                      -- cannot IH on a (unused). Use
                      -- that neverZero imax is max, so
                      -- the left child dominating zeros
                      -- lifts by fill+mono.
                      have hchild :
                          geqZero a (Nat.succ k) =
                            true :=
                        _iha (Nat.succ k)
                          (fun ρ x hx =>
                            Nat.le_trans ha0
                              (eval_some_total_le
                                ρ a x hx))
                      simp only [hchild]
                      rfl
  | param i =>
      cases k with
      | zero => rfl
      | succ k =>
          exfalso
          have hle :=
            hval (fun _ => some 0) 0 (by
              simp only [eval])
          exact Nat.not_succ_le_zero k hle

theorem evalTotal_lt_param (σ : Nat → Nat)
    (u : Level) (j n : Nat)
    (h : σ j > evalTotal σ u)
    (hle : σ j ≤ n) :
    evalTotal (fun i => if i = j then n else σ i) u =
      evalTotal σ u := by
  induction u with
  | zero => rfl
  | succ u ih =>
      simp only [evalTotal] at h
      have : σ j > evalTotal σ u :=
        Nat.lt_of_succ_lt h
      exact congrArg Nat.succ (ih this)
  | max a b iha ihb =>
      simp only [evalTotal] at h
      have ha : σ j > evalTotal σ a :=
        Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
      have hb : σ j > evalTotal σ b :=
        Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
      simp only [evalTotal]
      rw [iha ha, ihb hb]
  | imax a b iha ihb =>
      simp only [evalTotal]
      cases hb0 : evalTotal σ b with
      | zero =>
          have h0 : σ j > evalTotal σ b := by
            rw [hb0]
            simp only [evalTotal, hb0] at h
            exact h
          have ihb' := ihb h0
          cases hn : evalTotal
              (fun i => if i = j then n else σ i) b with
          | zero => rfl
          | succ m =>
              have eq := ihb'
              rw [hb0, hn] at eq
              exact False.elim (Nat.succ_ne_zero m eq)
      | succ m =>
          have hmax : σ j >
              max (evalTotal σ a) (m + 1) := by
            simp only [evalTotal, hb0] at h
            exact h
          have hb : σ j > evalTotal σ b := by
            simp only [hb0]
            exact Nat.lt_of_le_of_lt
              (Nat.le_max_right _ _) hmax
          have ha : σ j > evalTotal σ a :=
            Nat.lt_of_le_of_lt
              (Nat.le_max_left _ _) hmax
          have ihb' := ihb hb
          have iha' := iha ha
          rw [iha', ihb']
          simp only [hb0]
  | param i =>
      simp only [evalTotal]
      cases hij : decide (i = j) with
      | true =>
          have heq : i = j := of_decide_eq_true hij
          subst heq
          simp only [evalTotal] at h
          exact False.elim (Nat.lt_irrefl _ h)
      | false =>
          have hne : i ≠ j := of_decide_eq_false hij
          simp only [if_neg hne]

theorem eqN_zero_reduce (l : Level) (h : eqN l .zero) :
    reduce l = .zero := by
  induction l with
  | zero => rfl
  | succ l _ih =>
      exfalso
      have hz := h (fun _ => some 0)
      simp only [eval] at hz
      cases he : eval (fun _ => some 0) l with
      | none =>
          rw [he] at hz
          exact Option.noConfusion hz
      | some x =>
          rw [he] at hz
          injection hz with hz'
          exact Nat.succ_ne_zero x hz'
  | param i =>
      exfalso
      have hz := h (fun _ => none)
      simp only [eval] at hz
      exact Option.noConfusion hz
  | max a b iha ihb =>
      have hm : ∀ ρ, eval ρ a = some 0 ∧
          eval ρ b = some 0 :=
        fun ρ => (eval_max_eq_zero ρ a b).mp (h ρ)
      have ra := iha (fun ρ => (hm ρ).left)
      have rb := ihb (fun ρ => (hm ρ).right)
      simp only [reduce, ra, rb]
      unfold maxJoin
      rfl
  | imax a b _iha ihb =>
      have hb : eqN b .zero :=
        (eqN_imax_zero_iff a b).mp h
      have rb := ihb hb
      simp only [reduce, rb]
      unfold imaxJoin
      cases hd : decide (reduce a = .zero) with
      | true => rfl
      | false =>
          simp only [hd, levelIsZero]

/- Completeness WALLED at attempt 1 (H-6b). `eqN_zero_reduce`
closes the zero class after `imaxJoin`'s `imax 0 u = u`.
The remaining rigid arm is `geq` of two non-zero reduced
forms that are not syntactically equal (max commute,
param-vs-imax). `geqParam_complete` for that arm is
attempt 2's object; not declared here. The #4343 wall
(`imax 0 (param i)` vs `param i`) is closed by reduce. -/

/-! ## M-005 closed instances.

equal-by-imax: `eqN (.imax u .zero) .zero` with `u ≠ .zero`
syntactically — the degeneracy tooth against `decEqN :=`
syntactic equality. unequal-params: `param 0` vs `param 1`. -/

theorem m005_imax_not_syntactic :
    (.imax (.succ .zero) .zero) ≠ (.zero : Level) := by
  intro h
  cases h

theorem m005_imax_eqN :
    eqN (.imax (.succ .zero) .zero) .zero :=
  eqN_imax_zero_right (.succ .zero)

theorem m005_param_unequal : ¬ eqN (.param 0) (.param 1) := by
  intro h
  have h0 := h (fun i => if i = 0 then some 0 else some 1)
  simp only [eval] at h0
  split at h0
  · split at h0
    · next h10 => exact absurd h10 (by omega)
    · exact absurd h0 (by intro hc; cases hc)
  · next hf => exact hf trivial

/-- Unbound-parameter instance: `imax 0 (param i) =ₙ param i`.
The #4343 wall; now `true` by `imaxJoin`. -/
theorem m005_unbound_eqN :
    eqN (.imax .zero (.param 0)) (.param 0) :=
  eqN_imax_zero_left (.param 0)

/- M-005 `decEqN` instances and M-002 pins follow
`decEqN` (R-DecEqNNf, after `nf`). -/

/- Completeness WALLED at H-6 / H-6b (two attempts each).
H-6c: unique normal form; completeness by injectivity. -/

/-! ## H-6c: normal form (structural; no rank)

NF is the image of `nf`. `denote` is the inclusion of that
image into `Level`. Evaluation lemma: `eqN l (denote (nf l))`
for the landed partial `eval` (02 §2, LE-R7 laziness). -/

def ctorOrd : Level → Nat
  | .zero => 0
  | .param _ => 1
  | .succ _ => 2
  | .max _ _ => 3
  | .imax _ _ => 4

def levelLt : Level → Level → Bool
  | a, b =>
    if decide (ctorOrd a < ctorOrd b) then true
    else if decide (ctorOrd b < ctorOrd a) then false
    else
      match a, b with
      | .param i, .param j => decide (i < j)
      | .succ x, .succ y => levelLt x y
      | .max x y, .max u v =>
          if levelLt x u then true
          else if decide (x = u) then levelLt y v
          else false
      | .imax x y, .imax u v =>
          if levelLt x u then true
          else if decide (x = u) then levelLt y v
          else false
      | _, _ => false

def peelOff : Level → Nat × Level
  | .succ l =>
      let p := peelOff l
      (p.1 + 1, p.2)
  | .zero => (0, .zero)
  | .param i => (0, .param i)
  | .max a b => (0, .max a b)
  | .imax a b => (0, .imax a b)

/-- Sound subsumption: `dominates u v` ⇒ `max u v =ₙ u`
under partial eval (const always defined; imax dominates
its second argument; same base, higher offset). -/
def dominates (u v : Level) : Bool :=
  match peelOff u, peelOff v with
  | (nu, bu), (nv, bv) =>
      if decide (nv ≤ nu) then
        if decide (bu = bv) then true
        else
          match bv with
          | .zero => true
          | _ =>
              match bu with
              | .imax _ b => decide (b = bv)
              | _ => false
      else false

def flattenMax : Level → List Level
  | .zero => []
  | .max a b => flattenMax a ++ flattenMax b
  | .succ l => [.succ l]
  | .param i => [.param i]
  | .imax a b => [.imax a b]

/-- True if some element of the list dominates `u`.
Needed so an insert at the front (by `levelLt`) still
sees a later dominator (imax of a param vs that param). -/
def anyDominates (u : Level) : List Level → Bool
  | [] => false
  | v :: vs =>
      match dominates v u with
      | true => true
      | false => anyDominates u vs

/-- Drop every element `u` dominates. -/
def dropDominated (u : Level) : List Level → List Level
  | [] => []
  | v :: vs =>
      match dominates u v with
      | true => dropDominated u vs
      | false => v :: dropDominated u vs

/-- Insert into a domination-antichain, sorted by
`levelLt`. Scans the whole list for a dominator of
`u` before placing `u`; otherwise drops everything
`u` dominates and inserts in order. -/
def insertSub (u : Level) : List Level → List Level
  | [] => [u]
  | v :: vs =>
      match anyDominates u (v :: vs) with
      | true => v :: vs
      | false =>
          match dominates u v with
          | true => insertSub u vs
          | false =>
              match levelLt u v with
              | true =>
                  u :: dropDominated u (v :: vs)
              | false => v :: insertSub u vs

def foldlIns : List Level → List Level → List Level
  | acc, [] => acc
  | acc, x :: xs => foldlIns (insertSub x acc) xs

def minOffList : List Level → Nat
  | [] => 0
  | x :: xs =>
      let n := (peelOff x).1
      match xs with
      | [] => n
      | _ =>
          let m := minOffList xs
          if decide (n ≤ m) then n else m

def dropOff : Nat → Level → Level
  | 0, l => l
  | Nat.succ n, .succ l => dropOff n l
  | Nat.succ _, .zero => .zero
  | Nat.succ _, .param i => .param i
  | Nat.succ _, .max a b => .max a b
  | Nat.succ _, .imax a b => .imax a b

def mapDrop (n : Nat) : List Level → List Level
  | [] => []
  | x :: xs => dropOff n x :: mapDrop n xs

def wrapSucc : Nat → Level → Level
  | 0, l => l
  | Nat.succ n, l => .succ (wrapSucc n l)

def maxOfList : List Level → Level
  | [] => .zero
  | x :: xs =>
      match xs with
      | [] => x
      | _ => .max x (maxOfList xs)

def maxFromList (xs : List Level) : Level :=
  maxOfList (foldlIns [] xs)

def mapImaxJoin (a : Level) : List Level → List Level
  | [] => []
  | b :: bs =>
      flattenMax (imaxJoin a b) ++ mapImaxJoin a bs

def pairImax : List Level → List Level → List Level
  | [], _ => []
  | a :: as, bs =>
      mapImaxJoin a bs ++ pairImax as bs

/-- Local 02-§2 identities, then flatten. Never-zero `b`
turns `imax` into `max` and re-sorts; otherwise `imax`
distributes over flattened `max` atoms (02 §2: both
arguments). Zero identities fire first so an empty
flatten of `a` is never paired. -/
def imaxCanon (a b : Level) : Level :=
  match levelIsZero b with
  | true => .zero
  | false =>
      match levelIsZero a with
      | true => b
      | false =>
          match decide (a = b) with
          | true => b
          | false =>
              match levelNeverZero b with
              | true =>
                  maxFromList
                    (flattenMax a ++ flattenMax b)
              | false =>
                  maxFromList
                    (pairImax (flattenMax a)
                      (flattenMax b))

def mapSucc : List Level → List Level
  | [] => []
  | x :: xs => Level.succ x :: mapSucc xs

/-- Successor of an already-nf'd level. Distributes over
`max` so `succ (max a b)` and `max (succ a) (succ b)`
join (uniqueness; 02 §2 `max(x,y)+1 = max(x+1,y+1)`).
Does not distribute over `imax` (`succ (imax a 0) = 1`
and `imax (succ a) 1` disagree when `a ≠ 0`). -/
def succCanon : Level → Level
  | .max a b => .max (succCanon a) (succCanon b)
  | l => .succ l

/-- Structural normal form. No rank: constructor recursion
on children, then local 02-§2 identities on lists. -/
def nf : Level → Level
  | .zero => .zero
  | .succ l => succCanon (nf l)
  | .param i => .param i
  | .max a b =>
      maxFromList
        (flattenMax (nf a) ++ flattenMax (nf b))
  | .imax a b => imaxCanon (nf a) (nf b)

/-- Inclusion of the image of `nf` into `Level`. -/
def denote (n : Level) : Level := n

#eval (if nf (.imax (.succ .zero) .zero) = .zero then 0
  else panic "nf: imax 1 0")
#eval (if nf (.imax .zero (.param 0)) = .param 0 then 0
  else panic "nf: imax 0 u")
#eval (if nf (.max (.param 1) (.param 0)) =
    .max (.param 0) (.param 1) then 0
  else panic "nf: max commute")
#eval (if nf (.max (.succ (.param 0)) (.param 0)) =
    .succ (.param 0) then 0
  else panic "nf: offset subsume")
#eval (if nf (.imax (.param 99) .zero) = .zero then 0
  else panic "nf: LE-R7 form")
#eval (if nf (.max (.max (.param 0) (.param 2))
    (.param 1)) =
    .max (.param 0)
      (.max (.param 1) (.param 2)) then 0
  else panic "nf: max flatten+sort")
#eval (if nf (.succ (.max (.param 0) (.param 1))) =
    nf (.max (.succ (.param 0))
      (.succ (.param 1))) then 0
  else panic "nf: succ-max dist")
#eval (if nf (.imax
    (.max (.param 0) (.param 1))
    (.succ .zero)) =
    nf (.max
      (.max (.param 0) (.param 1))
      (.succ .zero)) then 0
  else panic "nf: imax-neverzero")
#eval (if nf (.imax
    (.max (.param 0) (.param 1))
    (.param 2)) =
    nf (.max
      (.imax (.param 0) (.param 2))
      (.imax (.param 1) (.param 2))) then 0
  else panic "nf: imax-max dist")
/- H-6h measurement (1/2): does `nf` PRODUCE
the nested `imax (imax p q) b`? `isCanonAtom`
is defined later; its #eval sits there. -/
#eval (if nf (.imax
    (.imax (.param 0) (.param 1))
    (.param 2)) =
    .imax
      (.imax (.param 0) (.param 1))
      (.param 2) then 0
  else panic "nf: nested imax produced")

/-! ## Evaluation of the normal form (partial valuations) -/

def evalMaxList (ρ : Nat → Option Nat) :
    List Level → Option Nat
  | [] => some 0
  | x :: xs =>
      match eval ρ x, evalMaxList ρ xs with
      | some u, some v => some (max u v)
      | _, _ => none

theorem evalMaxList_append (ρ : Nat → Option Nat)
    (xs ys : List Level) :
    evalMaxList ρ (xs ++ ys) =
      match evalMaxList ρ xs, evalMaxList ρ ys with
      | some u, some v => some (max u v)
      | _, _ => none := by
  induction xs with
  | nil =>
      rw [List.nil_append]
      cases hy : evalMaxList ρ ys with
      | none =>
          simp only [evalMaxList, hy]
      | some y =>
          simp only [evalMaxList, hy]
          exact congrArg some (Nat.zero_max y).symm
  | cons x xs ih =>
      rw [List.cons_append]
      simp only [evalMaxList]
      rw [ih]
      cases hx : eval ρ x with
      | none =>
          cases evalMaxList ρ xs <;>
            cases evalMaxList ρ ys <;> rfl
      | some u =>
          cases hxs : evalMaxList ρ xs with
          | none =>
              cases evalMaxList ρ ys <;> rfl
          | some v =>
              cases hys : evalMaxList ρ ys with
              | none => rfl
              | some w =>
                  exact congrArg some
                    (Nat.max_assoc u v w).symm

theorem flattenMax_eval (ρ : Nat → Option Nat)
    (l : Level) :
    evalMaxList ρ (flattenMax l) = eval ρ l := by
  induction l with
  | zero => rfl
  | succ l _ih =>
      simp only [flattenMax, evalMaxList]
      cases h : eval ρ (.succ l) with
      | none => rfl
      | some x => exact congrArg some (Nat.max_zero x)
  | param i =>
      simp only [flattenMax, evalMaxList]
      cases h : eval ρ (.param i) with
      | none => rfl
      | some x => exact congrArg some (Nat.max_zero x)
  | max a b iha ihb =>
      simp only [flattenMax]
      rw [evalMaxList_append, iha, ihb]
      simp only [eval]
      cases eval ρ a <;> cases eval ρ b <;> rfl
  | imax a b _iha _ihb =>
      simp only [flattenMax, evalMaxList]
      cases h : eval ρ (.imax a b) with
      | none => rfl
      | some y => exact congrArg some (Nat.max_zero y)

theorem eval_wrapSucc (n : Nat) (l : Level)
    (ρ : Nat → Option Nat) :
    eval ρ (wrapSucc n l) =
      (eval ρ l).map (fun x => x + n) := by
  induction n with
  | zero =>
      simp only [wrapSucc]
      cases eval ρ l with
      | none => rfl
      | some x => exact congrArg some (Nat.add_zero x).symm
  | succ n ih =>
      simp only [wrapSucc, eval, ih]
      cases eval ρ l with
      | none => rfl
      | some x =>
          exact congrArg some (Nat.add_succ x n)

theorem eval_peelOff (ρ : Nat → Option Nat) (l : Level) :
    eval ρ l =
      (eval ρ (peelOff l).2).map
        (fun x => x + (peelOff l).1) := by
  induction l with
  | zero =>
      simp only [peelOff, eval]
      exact congrArg some (Nat.add_zero 0).symm
  | param i =>
      simp only [peelOff, eval]
      cases hi : ρ i with
      | none => rfl
      | some x => exact congrArg some (Nat.add_zero x).symm
  | max a b _ _ =>
      simp only [peelOff]
      cases h : eval ρ (.max a b) with
      | none => rfl
      | some x => exact congrArg some (Nat.add_zero x).symm
  | imax a b _ _ =>
      simp only [peelOff]
      cases h : eval ρ (.imax a b) with
      | none => rfl
      | some x => exact congrArg some (Nat.add_zero x).symm
  | succ l ih =>
      simp only [peelOff, eval]
      cases hp : peelOff l with
      | mk n b =>
          simp only [hp] at ih
          simp only [hp]
          rw [ih]
          cases eval ρ b with
          | none => rfl
          | some x =>
              exact congrArg some (Nat.add_succ x n)

theorem eval_max_none_left (ρ : Nat → Option Nat)
    (u v : Level) (hu : eval ρ u = none) :
    eval ρ (.max u v) = none := by
  simp only [eval]
  rw [hu]
  rfl

theorem eval_max_none_right (ρ : Nat → Option Nat)
    (u v : Level) (x : Nat)
    (hu : eval ρ u = some x) (hv : eval ρ v = none) :
    eval ρ (.max u v) = none := by
  simp only [eval]
  rw [hu, hv]
  rfl

theorem eval_max_some (ρ : Nat → Option Nat)
    (u v : Level) (x y : Nat)
    (hu : eval ρ u = some x) (hv : eval ρ v = some y) :
    eval ρ (.max u v) = some (max x y) := by
  simp only [eval]
  rw [hu, hv]
  rfl

theorem eval_max_match (ρ : Nat → Option Nat)
    (u v : Level) :
    eval ρ (.max u v) =
      match eval ρ u, eval ρ v with
      | some x, some y => some (max x y)
      | _, _ => none := by
  simp only [eval]
  cases eval ρ u with
  | none => rfl
  | some _ =>
      cases eval ρ v with
      | none => rfl
      | some _ => rfl

theorem eval_imax_none_of_snd (ρ : Nat → Option Nat)
    (a b : Level) (hb : eval ρ b = none) :
    eval ρ (.imax a b) = none := by
  simp only [eval]
  rw [hb]
  rfl

theorem eval_imax_ge_snd (ρ : Nat → Option Nat)
    (a b : Level) (x y : Nat)
    (hi : eval ρ (.imax a b) = some x)
    (hb : eval ρ b = some y) : y ≤ x := by
  simp only [eval] at hi
  rw [hb] at hi
  simp only [Option.bind] at hi
  cases y with
  | zero =>
      injection hi with hx
      subst hx
      exact Nat.le_refl 0
  | succ y =>
      cases ha : eval ρ a with
      | none =>
          simp only [ha] at hi
          exact Option.noConfusion hi
      | some xa =>
          simp only [ha] at hi
          injection hi with hx
          subst hx
          exact Nat.le_max_right xa (y + 1)

/-- `max u v =ₙ u` when `dominates u v`. -/
theorem dominates_eqN (u v : Level)
    (h : dominates u v = true) :
    eqN (.max u v) u := by
  intro ρ
  have hu := eval_peelOff ρ u
  have hv := eval_peelOff ρ v
  rw [eval_max_match]
  simp only [dominates] at h
  cases hpu : peelOff u with
  | mk nu bu =>
      cases hpv : peelOff v with
      | mk nv bv =>
          rw [hpu] at hu
          rw [hpv] at hv
          simp only [Prod.fst, Prod.snd] at hu hv
          rw [hpu, hpv] at h
          simp only [Prod.fst, Prod.snd] at h
          cases hle : decide (nv ≤ nu) with
          | false =>
              rw [hle] at h
              exact Bool.noConfusion h
          | true =>
              have hnv : nv ≤ nu :=
                of_decide_eq_true hle
              rw [hle] at h
              cases heq : decide (bu = bv) with
              | true =>
                  have hbubv : bu = bv :=
                    of_decide_eq_true heq
                  subst hbubv
                  rw [hu, hv]
                  cases hbu : eval ρ bu with
                  | none => rfl
                  | some x =>
                      exact congrArg some
                        (Nat.max_eq_left
                          (Nat.add_le_add_left hnv x))
              | false =>
                  rw [heq] at h
                  cases hbv : bv with
                  | zero =>
                      rw [hu, hv]
                      cases hbu : eval ρ bu with
                      | none => rfl
                      | some x =>
                          rw [hbv]
                          simp only [eval]
                          have : 0 + nv ≤ x + nu := by
                            have h0 : 0 + nv = nv :=
                              Nat.zero_add nv
                            rw [h0]
                            exact Nat.le_trans hnv
                              (Nat.le_add_left nu x)
                          exact congrArg some
                            (Nat.max_eq_left this)
                  | succ b' =>
                      cases hbu : bu with
                      | imax a b =>
                          simp only [hbv, hbu] at h
                          have hb : b = .succ b' :=
                            of_decide_eq_true h
                          subst hb
                          rw [hu, hv, hbu, hbv]
                          cases hiu :
                            eval ρ (.imax a (.succ b')) with
                          | none => rfl
                          | some x =>
                              cases hiv :
                                eval ρ (.succ b') with
                              | none =>
                                  have hxnone :=
                                    eval_imax_none_of_snd
                                      ρ a _ hiv
                                  rw [hxnone] at hiu
                                  exact Option.noConfusion hiu
                              | some y =>
                                  have hyx :=
                                    eval_imax_ge_snd ρ a
                                      (.succ b') x y hiu hiv
                                  have :
                                      y + nv ≤ x + nu :=
                                    Nat.le_trans
                                      (Nat.add_le_add_left
                                        hnv y)
                                      (Nat.add_le_add_right
                                        hyx nu)
                                  exact congrArg some
                                    (Nat.max_eq_left this)
                      | zero =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | succ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | max _ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | param _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                  | param i =>
                      cases hbu : bu with
                      | imax a b =>
                          simp only [hbv, hbu] at h
                          have hb : b = .param i :=
                            of_decide_eq_true h
                          subst hb
                          rw [hu, hv, hbu, hbv]
                          cases hiu :
                            eval ρ (.imax a (.param i)) with
                          | none => rfl
                          | some x =>
                              cases hiv :
                                eval ρ (.param i) with
                              | none =>
                                  have hxnone :=
                                    eval_imax_none_of_snd
                                      ρ a _ hiv
                                  rw [hxnone] at hiu
                                  exact Option.noConfusion hiu
                              | some y =>
                                  have hyx :=
                                    eval_imax_ge_snd ρ a
                                      (.param i) x y hiu hiv
                                  have :
                                      y + nv ≤ x + nu :=
                                    Nat.le_trans
                                      (Nat.add_le_add_left
                                        hnv y)
                                      (Nat.add_le_add_right
                                        hyx nu)
                                  exact congrArg some
                                    (Nat.max_eq_left this)
                      | zero =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | succ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | max _ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | param _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                  | max b1 b2 =>
                      cases hbu : bu with
                      | imax a b =>
                          simp only [hbv, hbu] at h
                          have hb : b = .max b1 b2 :=
                            of_decide_eq_true h
                          subst hb
                          rw [hu, hv, hbu, hbv]
                          cases hiu :
                            eval ρ
                              (.imax a (.max b1 b2)) with
                          | none => rfl
                          | some x =>
                              cases hiv :
                                eval ρ (.max b1 b2) with
                              | none =>
                                  have hxnone :=
                                    eval_imax_none_of_snd
                                      ρ a _ hiv
                                  rw [hxnone] at hiu
                                  exact Option.noConfusion hiu
                              | some y =>
                                  have hyx :=
                                    eval_imax_ge_snd ρ a
                                      (.max b1 b2) x y
                                      hiu hiv
                                  have :
                                      y + nv ≤ x + nu :=
                                    Nat.le_trans
                                      (Nat.add_le_add_left
                                        hnv y)
                                      (Nat.add_le_add_right
                                        hyx nu)
                                  exact congrArg some
                                    (Nat.max_eq_left this)
                      | zero =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | succ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | max _ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | param _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                  | imax c d =>
                      cases hbu : bu with
                      | imax a b =>
                          simp only [hbv, hbu] at h
                          have hb : b = .imax c d :=
                            of_decide_eq_true h
                          subst hb
                          rw [hu, hv, hbu, hbv]
                          cases hiu :
                            eval ρ
                              (.imax a (.imax c d)) with
                          | none => rfl
                          | some x =>
                              cases hiv :
                                eval ρ (.imax c d) with
                              | none =>
                                  have hxnone :=
                                    eval_imax_none_of_snd
                                      ρ a _ hiv
                                  rw [hxnone] at hiu
                                  exact Option.noConfusion hiu
                              | some y =>
                                  have hyx :=
                                    eval_imax_ge_snd ρ a
                                      (.imax c d) x y
                                      hiu hiv
                                  have :
                                      y + nv ≤ x + nu :=
                                    Nat.le_trans
                                      (Nat.add_le_add_left
                                        hnv y)
                                      (Nat.add_le_add_right
                                        hyx nu)
                                  exact congrArg some
                                    (Nat.max_eq_left this)
                      | zero =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | succ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | max _ _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h
                      | param _ =>
                          simp only [hbv, hbu] at h
                          exact Bool.noConfusion h

theorem max_left_comm (a b c : Nat) :
    max a (max b c) = max b (max a c) := by
  have h1 : max a (max b c) = max (max a b) c :=
    (Nat.max_assoc a b c).symm
  have h2 : max (max a b) c = max (max b a) c :=
    congrArg (fun t => max t c) (Nat.max_comm a b)
  have h3 : max (max b a) c = max b (max a c) :=
    Nat.max_assoc b a c
  exact h1.trans (h2.trans h3)

theorem evalMaxList_drop_dom (ρ : Nat → Option Nat)
    (u v : Level) (xs : List Level)
    (h : dominates u v = true) :
    evalMaxList ρ (u :: v :: xs) =
      evalMaxList ρ (u :: xs) := by
  have hm := dominates_eqN u v h ρ
  simp only [evalMaxList]
  simp only [eval] at hm
  cases hu : eval ρ u with
  | none =>
      cases eval ρ v with
      | none =>
          cases evalMaxList ρ xs <;> rfl
      | some _ =>
          cases evalMaxList ρ xs <;> rfl
  | some x =>
      cases hv : eval ρ v with
      | none =>
          rw [hu, hv] at hm
          exact Option.noConfusion hm
      | some y =>
          rw [hu, hv] at hm
          injection hm with hxy
          cases hxs : evalMaxList ρ xs with
          | none => rfl
          | some z =>
              have hyx : y ≤ x :=
                Nat.le_trans (Nat.le_max_right x y)
                  (Nat.le_of_eq hxy)
              have hassoc :
                  max x (max y z) = max (max x y) z :=
                (Nat.max_assoc x y z).symm
              have hmax : max (max x y) z = max x z :=
                congrArg (fun t => max t z) hxy
              exact congrArg some
                (hassoc.trans hmax)

theorem evalMaxList_cons
    (ρ : Nat → Option Nat)
    (x : Level) (xs : List Level) :
    evalMaxList ρ (x :: xs) =
      match eval ρ x, evalMaxList ρ xs with
      | some a, some b => some (max a b)
      | _, _ => none := rfl

theorem evalMaxList_cons_swap
    (ρ : Nat → Option Nat)
    (a b : Level) (xs : List Level) :
    evalMaxList ρ (a :: b :: xs) =
      evalMaxList ρ (b :: a :: xs) := by
  rw [evalMaxList_cons ρ a (b :: xs)]
  rw [evalMaxList_cons ρ b (a :: xs)]
  rw [evalMaxList_cons ρ b xs]
  rw [evalMaxList_cons ρ a xs]
  cases eval ρ a with
  | none =>
      cases eval ρ b with
      | none =>
          cases evalMaxList ρ xs <;> rfl
      | some _ =>
          cases evalMaxList ρ xs <;> rfl
  | some x =>
      cases eval ρ b with
      | none =>
          cases evalMaxList ρ xs <;> rfl
      | some y =>
          cases evalMaxList ρ xs with
          | none => rfl
          | some z =>
              exact congrArg some
                (max_left_comm x y z)

theorem evalMaxList_drop_self
    (ρ : Nat → Option Nat)
    (u v : Level) (xs : List Level)
    (h : dominates v u = true) :
    evalMaxList ρ (u :: v :: xs) =
      evalMaxList ρ (v :: xs) := by
  have hm := dominates_eqN v u h ρ
  simp only [eval] at hm
  rw [evalMaxList_cons ρ u (v :: xs)]
  rw [evalMaxList_cons ρ v xs]
  cases hv : eval ρ v with
  | none =>
      cases eval ρ u <;> rfl
  | some y =>
      cases hu : eval ρ u with
      | none =>
          rw [hv, hu] at hm
          exact Option.noConfusion hm
      | some x =>
          rw [hv, hu] at hm
          injection hm with hyx
          cases evalMaxList ρ xs with
          | none => rfl
          | some z =>
              have hxy : x ≤ y :=
                Nat.le_trans
                  (Nat.le_max_right y x)
                  (Nat.le_of_eq hyx)
              exact congrArg some
                (Nat.max_eq_right
                  (Nat.le_trans hxy
                    (Nat.le_max_left y z)))

theorem evalMaxList_anyDom
    (ρ : Nat → Option Nat) (u : Level) :
    ∀ xs : List Level,
      anyDominates u xs = true →
        evalMaxList ρ (u :: xs) =
          evalMaxList ρ xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      exact Bool.noConfusion h
  | cons v vs ih =>
      intro h
      simp only [anyDominates] at h
      cases hd : dominates v u with
      | true =>
          exact evalMaxList_drop_self ρ u v vs hd
      | false =>
          rw [hd] at h
          have ih' := ih h
          rw [evalMaxList_cons_swap]
          rw [evalMaxList_cons ρ v (u :: vs)]
          rw [evalMaxList_cons ρ v vs]
          rw [ih']

theorem max_absorb (x d s y : Nat)
    (h : max x d = max x s) :
    max x (max y d) = max x (max y s) := by
  cases hd : decide (d ≤ x) with
  | true =>
      have hdx : d ≤ x := of_decide_eq_true hd
      have hxd : max x d = x :=
        Nat.max_eq_left hdx
      have hsx : s ≤ x :=
        Nat.le_trans (Nat.le_max_right x s)
          (Nat.le_of_eq (hxd.symm.trans h).symm)
      have h1 : max (max x y) d = max x y :=
        Nat.max_eq_left
          (Nat.le_trans hdx (Nat.le_max_left x y))
      have h2 : max (max x y) s = max x y :=
        Nat.max_eq_left
          (Nat.le_trans hsx (Nat.le_max_left x y))
      exact
        ((Nat.max_assoc x y d).symm.trans h1).trans
          (h2.symm.trans (Nat.max_assoc x y s))
  | false =>
      have hxd : ¬ d ≤ x := of_decide_eq_false hd
      have hlt : x < d := Nat.lt_of_not_le hxd
      have hle : x ≤ d := Nat.le_of_lt hlt
      have hdmax : max x d = d :=
        Nat.max_eq_right hle
      have hds : d = max x s :=
        hdmax.symm.trans h
      cases hxs : decide (x ≤ s) with
      | true =>
          have hxles : x ≤ s :=
            of_decide_eq_true hxs
          have hsmax : max x s = s :=
            Nat.max_eq_right hxles
          have heq : d = s :=
            hds.trans hsmax
          subst heq
          rfl
      | false =>
          have hsx : s ≤ x :=
            Nat.le_of_not_le
              (of_decide_eq_false hxs)
          have hxmax : max x s = x :=
            Nat.max_eq_left hsx
          have hdxx : d = x :=
            hds.trans hxmax
          rw [hdxx] at hlt
          exact False.elim (Nat.lt_irrefl x hlt)

theorem evalMaxList_cons_dropDominated
    (ρ : Nat → Option Nat) (u : Level) :
    ∀ xs : List Level,
      evalMaxList ρ (u :: dropDominated u xs) =
        evalMaxList ρ (u :: xs) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          have hdrop :=
            evalMaxList_drop_dom ρ u v vs hd
          exact ih.trans hdrop.symm
      | false =>
          simp only [dropDominated, hd]
          simp only [evalMaxList]
          cases hu : eval ρ u with
          | none =>
              cases eval ρ v with
              | none =>
                  cases evalMaxList ρ
                    (dropDominated u vs) <;> rfl
              | some _ =>
                  cases evalMaxList ρ
                    (dropDominated u vs) <;> rfl
          | some x =>
              cases hv : eval ρ v with
              | none =>
                  cases evalMaxList ρ
                    (dropDominated u vs) <;> rfl
              | some y =>
                  cases hd' : evalMaxList ρ
                    (dropDominated u vs) with
                  | none =>
                      cases hs : evalMaxList ρ vs with
                      | none => rfl
                      | some _ =>
                          have ih' := ih
                          simp only [evalMaxList, hu, hd',
                            hs] at ih'
                          exact Option.noConfusion ih'
                  | some d =>
                      cases hs : evalMaxList ρ vs with
                      | none =>
                          have ih' := ih
                          simp only [evalMaxList, hu, hd',
                            hs] at ih'
                          exact Option.noConfusion ih'
                      | some s =>
                          have hmax : max x d = max x s := by
                            have ih' := ih
                            simp only [evalMaxList, hu, hd',
                              hs] at ih'
                            injection ih'
                          exact congrArg some
                            (max_absorb x d s y hmax)

theorem insertSub_eval (ρ : Nat → Option Nat)
    (u : Level) (vs : List Level) :
    evalMaxList ρ (insertSub u vs) =
      evalMaxList ρ (u :: vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      cases ha : anyDominates u (v :: vs) with
      | true =>
          simp only [insertSub, ha]
          exact (evalMaxList_anyDom ρ u
            (v :: vs) ha).symm
      | false =>
          cases h1 : dominates u v with
          | true =>
              simp only [insertSub, ha, h1]
              rw [ih]
              exact (evalMaxList_drop_dom
                ρ u v vs h1).symm
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, h1, hlt]
                  exact evalMaxList_cons_dropDominated
                    ρ u (v :: vs)
              | false =>
                  simp only [insertSub, ha, h1, hlt]
                  simp only [evalMaxList]
                  rw [ih]
                  simp only [evalMaxList]
                  cases eval ρ u with
                  | none =>
                      cases eval ρ v with
                      | none =>
                          cases evalMaxList ρ vs <;> rfl
                      | some _ =>
                          cases evalMaxList ρ vs <;> rfl
                  | some x =>
                      cases eval ρ v with
                      | none =>
                          cases evalMaxList ρ vs <;> rfl
                      | some y =>
                          cases evalMaxList ρ vs with
                          | none => rfl
                          | some z =>
                              exact congrArg some
                                (max_left_comm x y z).symm

theorem foldlIns_eval (ρ : Nat → Option Nat)
    (acc xs : List Level) :
    evalMaxList ρ (foldlIns acc xs) =
      evalMaxList ρ (acc ++ xs) := by
  induction xs generalizing acc with
  | nil =>
      rw [List.append_nil]
      rfl
  | cons x xs ih =>
      simp only [foldlIns]
      rw [ih]
      rw [evalMaxList_append]
      rw [insertSub_eval]
      rw [evalMaxList_append]
      simp only [evalMaxList]
      cases eval ρ x with
      | none =>
          cases evalMaxList ρ acc with
          | none =>
              cases evalMaxList ρ xs <;> rfl
          | some _ =>
              cases evalMaxList ρ xs <;> rfl
      | some n =>
          cases evalMaxList ρ acc with
          | none =>
              cases evalMaxList ρ xs <;> rfl
          | some m =>
              cases evalMaxList ρ xs with
              | none => rfl
              | some k =>
                  exact congrArg some
                    ((Nat.max_assoc n m k).trans
                      (max_left_comm n m k))

theorem maxOfList_eval (ρ : Nat → Option Nat)
    (xs : List Level) :
    eval ρ (maxOfList xs) = evalMaxList ρ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [maxOfList, evalMaxList]
          cases eval ρ x with
          | none => rfl
          | some n =>
              exact congrArg some (Nat.max_zero n).symm
      | cons y ys =>
          change eval ρ (.max x (maxOfList (y :: ys))) =
            match eval ρ x, evalMaxList ρ (y :: ys) with
            | some a, some b => some (max a b)
            | _, _ => none
          simp only [eval]
          rw [ih]
          cases hx : eval ρ x with
          | none => rfl
          | some n =>
              simp only [hx, Option.bind]
              cases hy : evalMaxList ρ (y :: ys) with
              | none =>
                  simp only [hy, Option.map]
              | some m =>
                  simp only [hy, Option.map]

theorem maxFromList_eval (ρ : Nat → Option Nat)
    (xs : List Level) :
    eval ρ (maxFromList xs) = evalMaxList ρ xs := by
  simp only [maxFromList]
  rw [maxOfList_eval, foldlIns_eval]
  simp only [List.nil_append]

theorem flatten_empty_zero (ρ : Nat → Option Nat)
    (l : Level) (h : flattenMax l = []) :
    eval ρ l = some 0 := by
  have hf := flattenMax_eval ρ l
  rw [h] at hf
  simp only [evalMaxList] at hf
  exact hf.symm

theorem imax_zero_snd (ρ : Nat → Option Nat)
    (a b : Level) (hb : eval ρ b = some 0) :
    eval ρ (.imax a b) = some 0 := by
  simp only [eval, hb]
  rfl

theorem imax_zero_fst (ρ : Nat → Option Nat)
    (a b : Level) (ha : eval ρ a = some 0) :
    eval ρ (.imax a b) = eval ρ b := by
  simp only [eval, ha]
  cases hb : eval ρ b with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ y => exact congrArg some (Nat.zero_max (y + 1))

theorem imaxJoin_eqN (a b : Level) :
    eqN (.imax a b) (imaxJoin a b) := by
  unfold imaxJoin
  cases h : decide (a = b) with
  | true =>
      have heq : a = b := of_decide_eq_true h
      subst heq
      exact eqN_imax_diag a
  | false =>
      cases hbz : levelIsZero b with
      | true =>
          have hz : eqN b .zero :=
            (levelIsZero_iff b).mp hbz
          exact (eqN_imax_zero_iff a b).mpr hz
      | false =>
          cases haz : levelIsZero a with
          | true =>
              have h0 : eqN a .zero :=
                (levelIsZero_iff a).mp haz
              intro ρ
              have ha0 := h0 ρ
              have hi := eqN_imax_zero_left b ρ
              simp only [eval] at ha0 hi
              simp only [eval]
              rw [ha0]
              exact hi
          | false =>
              cases hnev : levelNeverZero b with
              | true =>
                  have hm := maxJoin_eqN a b
                  intro ρ
                  have himax_max :
                      eval ρ (.imax a b) =
                        eval ρ (.max a b) := by
                    simp only [eval]
                    cases hb : eval ρ b with
                    | none =>
                        cases eval ρ a with
                        | none => rfl
                        | some _ => rfl
                    | some y =>
                        cases y with
                        | zero =>
                            exact False.elim
                              (levelNeverZero_not_zero
                                b ρ hnev hb)
                        | succ y =>
                            cases eval ρ a with
                            | none => rfl
                            | some _ => rfl
                  exact himax_max.trans (hm ρ)
              | false =>
                  simp only [h, hbz, haz, hnev]
                  cases a with
                  | zero => exact Bool.noConfusion haz
                  | succ _ => intro ρ; rfl
                  | param _ => intro ρ; rfl
                  | imax x y =>
                      dsimp
                      cases hy : decide (y = b) with
                      | false => intro ρ; rfl
                      | true =>
                          have hyeq : y = b :=
                            of_decide_eq_true hy
                          cases hx : decide (x = b) with
                          | true =>
                              have hxeq : x = b :=
                                of_decide_eq_true hx
                              intro ρ
                              rw [hyeq, hxeq]
                              have hn :=
                                eqN_imax_nest b b ρ
                              have hd :=
                                eqN_imax_diag b ρ
                              exact hn.trans hd
                          | false =>
                              cases hxz : levelIsZero x with
                              | true =>
                                  have hx0 : eqN x .zero :=
                                    (levelIsZero_iff x).mp hxz
                                  intro ρ
                                  rw [hyeq]
                                  exact
                                    (eqN_imax_nest x b ρ).trans
                                      ((eqN_congr_imax hx0
                                          (fun _ => rfl) ρ).trans
                                        (eqN_imax_zero_left b ρ))
                              | false =>
                                  intro ρ
                                  rw [hyeq]
                                  exact eqN_imax_nest x b ρ
                  | max x y =>
                      dsimp
                      cases hy : decide (y = b) with
                      | true =>
                          have hyeq : y = b :=
                            of_decide_eq_true hy
                          cases hx : decide (x = b) with
                          | true =>
                              have hxeq : x = b :=
                                of_decide_eq_true hx
                              intro ρ
                              rw [hyeq, hxeq]
                              exact
                                (eqN_imax_max_snd b b ρ).trans
                                  (eqN_imax_diag b ρ)
                          | false =>
                              cases hxz : levelIsZero x with
                              | true =>
                                  have hx0 : eqN x .zero :=
                                    (levelIsZero_iff x).mp hxz
                                  intro ρ
                                  rw [hyeq]
                                  exact
                                    (eqN_imax_max_snd x b ρ).trans
                                      ((eqN_congr_imax hx0
                                          (fun _ => rfl) ρ).trans
                                        (eqN_imax_zero_left b ρ))
                              | false =>
                                  intro ρ
                                  rw [hyeq]
                                  exact eqN_imax_max_snd x b ρ
                      | false =>
                          cases hx : decide (x = b) with
                          | false => intro ρ; rfl
                          | true =>
                              have hxeq : x = b :=
                                of_decide_eq_true hx
                              cases hyz : levelIsZero y with
                              | true =>
                                  have hy0 : eqN y .zero :=
                                    (levelIsZero_iff y).mp hyz
                                  intro ρ
                                  rw [hxeq]
                                  exact
                                    (eqN_imax_max_fst y b ρ).trans
                                      ((eqN_congr_imax hy0
                                          (fun _ => rfl) ρ).trans
                                        (eqN_imax_zero_left b ρ))
                              | false =>
                                  intro ρ
                                  rw [hxeq]
                                  exact eqN_imax_max_fst y b ρ

def optionMax : Option Nat → Option Nat → Option Nat
  | some u, some v => some (max u v)
  | _, _ => none

theorem flattenMax_imaxJoin_eval
    (ρ : Nat → Option Nat) (a b : Level) :
    evalMaxList ρ (flattenMax (imaxJoin a b)) =
      eval ρ (.imax a b) := by
  have hf := flattenMax_eval ρ (imaxJoin a b)
  have hj := imaxJoin_eqN a b ρ
  exact hf.trans hj.symm

theorem flattenMax_nil_isZero (l : Level)
    (h : flattenMax l = []) :
    levelIsZero l = true :=
  (levelIsZero_iff l).mpr
    (fun ρ => flatten_empty_zero ρ l h)

theorem max_le_max_of_le (x a b : Nat)
    (h : a ≤ b) : max x a ≤ max x b := by
  cases hx : decide (x ≤ a) with
  | true =>
      have hxa : x ≤ a := of_decide_eq_true hx
      have hxb : x ≤ b := Nat.le_trans hxa h
      rw [Nat.max_eq_right hxa, Nat.max_eq_right hxb]
      exact h
  | false =>
      have hax : a ≤ x :=
        Nat.le_of_not_le (of_decide_eq_false hx)
      rw [Nat.max_eq_left hax]
      exact Nat.le_max_left x b

theorem max_max_left (x a b : Nat) :
    max (max x a) (max x b) = max x (max a b) := by
  cases h : decide (a ≤ b) with
  | true =>
      have hab : a ≤ b := of_decide_eq_true h
      rw [Nat.max_eq_right hab]
      exact Nat.max_eq_right
        (max_le_max_of_le x a b hab)
  | false =>
      have hba : b ≤ a :=
        Nat.le_of_not_le (of_decide_eq_false h)
      rw [Nat.max_eq_left hba]
      rw [Nat.max_comm (max x a) (max x b)]
      exact Nat.max_eq_right
        (max_le_max_of_le x b a hba)

theorem max_add_one (x y : Nat) :
    max (x + 1) (y + 1) = max x y + 1 := by
  cases h : decide (x ≤ y) with
  | true =>
      have hle : x ≤ y := of_decide_eq_true h
      rw [Nat.max_eq_right hle]
      rw [Nat.max_eq_right (Nat.succ_le_succ hle)]
  | false =>
      have hn : ¬ x ≤ y := of_decide_eq_false h
      have hx : y ≤ x := Nat.le_of_not_le hn
      rw [Nat.max_eq_left hx]
      rw [Nat.max_eq_left (Nat.succ_le_succ hx)]

theorem eval_imax_match (ρ : Nat → Option Nat)
    (a b : Level) :
    eval ρ (.imax a b) =
      match eval ρ b with
      | none => none
      | some .zero => some 0
      | some (.succ y) =>
          match eval ρ a with
          | none => none
          | some x => some (max x (y + 1)) := by
  simp only [eval]
  cases eval ρ b with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ y =>
          cases eval ρ a with
          | none => rfl
          | some x => rfl

theorem eval_imax_max_distrib_snd
    (ρ : Nat → Option Nat) (a b c : Level) :
    optionMax (eval ρ (.imax a b))
      (eval ρ (.imax a c)) =
      eval ρ (.imax a (.max b c)) := by
  rw [eval_imax_match ρ a b]
  rw [eval_imax_match ρ a c]
  rw [eval_imax_match ρ a (.max b c)]
  rw [eval_max_match ρ b c]
  cases eval ρ b with
  | none =>
      simp only [optionMax]
  | some yb =>
      cases yb with
      | zero =>
          cases eval ρ c with
          | none => simp only [optionMax]
          | some yc =>
              cases yc with
              | zero =>
                  simp only [optionMax]
                  rw [Nat.max_self (0 : Nat)]
              | succ yc =>
                  cases eval ρ a with
                  | none =>
                      simp only [optionMax]
                      rw [Nat.zero_max (yc + 1)]
                  | some x =>
                      simp only [optionMax]
                      rw [Nat.zero_max (yc + 1)]
                      exact congrArg some
                        (Nat.zero_max
                          (max x (yc + 1)))
      | succ yb =>
          cases eval ρ c with
          | none =>
              simp only [optionMax]
              cases eval ρ a <;> rfl
          | some yc =>
              cases yc with
              | zero =>
                  cases eval ρ a with
                  | none =>
                      simp only [optionMax]
                      rw [Nat.max_zero (yb + 1)]
                  | some x =>
                      simp only [optionMax]
                      rw [Nat.max_zero (yb + 1)]
                      exact congrArg some
                        (Nat.max_zero
                          (max x (yb + 1)))
              | succ yc =>
                  cases eval ρ a with
                  | none =>
                      simp only [optionMax]
                      rw [max_add_one]
                  | some x =>
                      simp only [optionMax]
                      rw [max_add_one]
                      have h :=
                        max_max_left x
                          (yb + 1) (yc + 1)
                      rw [max_add_one] at h
                      exact congrArg some h

theorem eval_imax_max_distrib_fst
    (ρ : Nat → Option Nat) (a c d : Level) :
    optionMax (eval ρ (.imax a d))
      (eval ρ (.imax c d)) =
      eval ρ (.imax (.max a c) d) := by
  rw [eval_imax_match ρ a d]
  rw [eval_imax_match ρ c d]
  rw [eval_imax_match ρ (.max a c) d]
  rw [eval_max_match ρ a c]
  cases eval ρ d with
  | none =>
      simp only [optionMax]
  | some yd =>
      cases yd with
      | zero =>
          simp only [optionMax]
          exact congrArg some
            (Nat.max_self (0 : Nat))
      | succ yd =>
          cases eval ρ a with
          | none =>
              simp only [optionMax]
          | some xa =>
              cases eval ρ c with
              | none => simp only [optionMax]
              | some xc =>
                  simp only [optionMax]
                  have h1 :
                      max xa (yd + 1) =
                        max (yd + 1) xa :=
                    Nat.max_comm _ _
                  have h2 :
                      max xc (yd + 1) =
                        max (yd + 1) xc :=
                    Nat.max_comm _ _
                  have h3 :
                      max (max xa xc) (yd + 1) =
                        max (yd + 1) (max xa xc) :=
                    Nat.max_comm _ _
                  rw [h1, h2, h3]
                  exact congrArg some
                    (max_max_left (yd + 1) xa xc)

theorem evalMaxList_eq_optionMax
    (ρ : Nat → Option Nat)
    (xs ys : List Level) :
    evalMaxList ρ (xs ++ ys) =
      optionMax (evalMaxList ρ xs)
        (evalMaxList ρ ys) := by
  rw [evalMaxList_append]
  rfl

theorem evalMaxList_mapImaxJoin
    (ρ : Nat → Option Nat)
    (a : Level) (bs : List Level) :
    evalMaxList ρ (mapImaxJoin a bs) =
      eval ρ (.imax a (maxOfList bs)) := by
  induction bs with
  | nil =>
      change some 0 =
        eval ρ (.imax a .zero)
      exact (eqN_imax_zero_right a ρ).symm
  | cons b bs ih =>
      have hstep :
          mapImaxJoin a (b :: bs) =
            flattenMax (imaxJoin a b) ++
              mapImaxJoin a bs := rfl
      rw [hstep, evalMaxList_eq_optionMax]
      rw [flattenMax_imaxJoin_eval, ih]
      cases hbs : bs with
      | nil =>
          simp only [maxOfList]
          have hz : eval ρ (.imax a .zero) =
              some 0 :=
            eqN_imax_zero_right a ρ
          rw [hz]
          simp only [optionMax]
          cases eval ρ (.imax a b) with
          | none => rfl
          | some u =>
              exact congrArg some
                (Nat.max_zero u)
      | cons b' bs' =>
          exact eval_imax_max_distrib_snd ρ a b
            (maxOfList (b' :: bs'))

theorem evalMaxList_pairImax_of_cons
    (ρ : Nat → Option Nat)
    (a : Level) (as bs : List Level) :
    evalMaxList ρ (pairImax (a :: as) bs) =
      eval ρ (.imax (maxOfList (a :: as))
        (maxOfList bs)) := by
  induction as generalizing a with
  | nil =>
      have hstep :
          pairImax (a :: []) bs =
            mapImaxJoin a bs ++ [] := rfl
      rw [hstep, List.append_nil]
      simp only [maxOfList]
      exact evalMaxList_mapImaxJoin ρ a bs
  | cons a' as ih =>
      have hstep :
          pairImax (a :: a' :: as) bs =
            mapImaxJoin a bs ++
              pairImax (a' :: as) bs := rfl
      rw [hstep, evalMaxList_eq_optionMax]
      rw [evalMaxList_mapImaxJoin, ih a']
      have hml :
          maxOfList (a :: a' :: as) =
            .max a (maxOfList (a' :: as)) := rfl
      rw [hml]
      exact eval_imax_max_distrib_fst ρ a
        (maxOfList (a' :: as)) (maxOfList bs)

theorem flattenMax_maxOfList_eval
    (ρ : Nat → Option Nat) (l : Level) :
    eval ρ (maxOfList (flattenMax l)) =
      eval ρ l :=
  (maxOfList_eval ρ (flattenMax l)).trans
    (flattenMax_eval ρ l)

theorem imaxCanon_eqN (a b : Level)
    (ρ : Nat → Option Nat) :
    eval ρ (.imax a b) =
      eval ρ (imaxCanon a b) := by
  unfold imaxCanon
  cases hbz : levelIsZero b with
  | true =>
      have hz : eqN b .zero :=
        (levelIsZero_iff b).mp hbz
      exact ((eqN_imax_zero_iff a b).mpr hz) ρ
  | false =>
      cases haz : levelIsZero a with
      | true =>
          have h0 : eqN a .zero :=
            (levelIsZero_iff a).mp haz
          exact
            (by
              have ha0 := h0 ρ
              have hi := eqN_imax_zero_left b ρ
              simp only [eval] at ha0 hi ⊢
              rw [ha0]
              exact hi)
      | false =>
          cases heq : decide (a = b) with
          | true =>
              have hab : a = b :=
                of_decide_eq_true heq
              subst hab
              exact eqN_imax_diag a ρ
          | false =>
              cases hnev : levelNeverZero b with
              | true =>
                  rw [maxFromList_eval]
                  rw [evalMaxList_append]
                  rw [flattenMax_eval, flattenMax_eval]
                  rw [eval_imax_match]
                  cases hb : eval ρ b with
                  | none =>
                      cases eval ρ a <;> rfl
                  | some y =>
                      cases y with
                      | zero =>
                          exact False.elim
                            (levelNeverZero_not_zero
                              b ρ hnev hb)
                      | succ y =>
                          cases eval ρ a <;> rfl
              | false =>
                  rw [maxFromList_eval]
                  cases hfa : flattenMax a with
                  | nil =>
                      have hz :=
                        flattenMax_nil_isZero a hfa
                      rw [haz] at hz
                      exact Bool.noConfusion hz
                  | cons x xs =>
                      have hp :=
                        evalMaxList_pairImax_of_cons
                          ρ x xs (flattenMax b)
                      rw [hp]
                      have hfe :=
                        flattenMax_maxOfList_eval ρ a
                      have hfb :=
                        flattenMax_maxOfList_eval ρ b
                      rw [hfa] at hfe
                      rw [eval_imax_match ρ a b]
                      rw [eval_imax_match ρ
                        (maxOfList (x :: xs))
                        (maxOfList (flattenMax b))]
                      rw [hfe, hfb]

theorem succCanon_eval (ρ : Nat → Option Nat)
    (l : Level) :
    eval ρ (succCanon l) =
      (eval ρ l).map (fun x => x + 1) := by
  induction l with
  | max a b iha ihb =>
      simp only [succCanon, eval]
      rw [iha, ihb]
      cases eval ρ a with
      | none =>
          cases eval ρ b <;> rfl
      | some x =>
          cases eval ρ b with
          | none => rfl
          | some y =>
              exact congrArg some (max_add_one x y)
  | zero => rfl
  | succ _ _ => rfl
  | param _ => rfl
  | imax _ _ _ _ => rfl

/-- Evaluation lemma: `nf` preserves landed `eval` at
every partial valuation (02 §2, including LE-R7). -/
theorem nf_eval (l : Level) (ρ : Nat → Option Nat) :
    eval ρ l = eval ρ (denote (nf l)) := by
  simp only [denote]
  induction l with
  | zero => rfl
  | param i => rfl
  | succ l ih =>
      simp only [nf, eval]
      rw [succCanon_eval, ih]
  | max a b iha ihb =>
      simp only [nf]
      rw [maxFromList_eval, evalMaxList_append]
      rw [flattenMax_eval, flattenMax_eval]
      simp only [eval]
      rw [iha, ihb]
      cases eval ρ (nf a) with
      | none =>
          cases eval ρ (nf b) <;> rfl
      | some _ =>
          cases eval ρ (nf b) <;> rfl
  | imax a b iha ihb =>
      simp only [nf]
      have hj := imaxCanon_eqN (nf a) (nf b) ρ
      simp only [eval] at iha ihb ⊢
      rw [iha, ihb]
      exact hj

theorem nf_eqN (l : Level) : eqN l (denote (nf l)) :=
  nf_eval l

/- R-LevelSplit (4) / H-6k: `decEqN` moved below
`spec` (the split form needs `spec` / `paramsOf`).
M-002 pins moved with it. -/

def rhoOf (xs : List Nat) : Nat → Option Nat :=
  fun i => xs[i]?

/-- Degeneracy tooth: `denote ∘ nf` is not the identity.
`imax 1 0` is `=ₙ` 0 and `nf` sends it to 0. -/
theorem m005_nf_imax :
    nf (.imax (.succ .zero) .zero) = .zero := rfl

theorem m005_nf_unbound :
    nf (.imax .zero (.param 0)) = .param 0 := rfl

/- Injectivity attempt 1 (H-6c) did not elaborate (SPENT).
Attempt 2 object: `nf_idem` / `maxFromList` commuting
with `succCanon` (the succ-max uniqueness identity at
the list form). Not declared as `nf_injective` (the
declaration would rest on that commute). Instrument
(1) `noneOnly`/`dependsOn` closed. `decEqN_complete`
not declared. -/

/-- Valuation that is `none` at exactly `i`, `some 1`
elsewhere. Instrument (1). -/
def noneOnly (i : Nat) : Nat → Option Nat :=
  fun j =>
    match decide (j = i) with
    | true => none
    | false => some 1

/-- Parameters `eval` consults at `noneOnly`, honouring
`imax` laziness: a zero-class right argument is never
consulted. -/
def dependsOn : Level → Nat → Bool
  | .zero, _ => false
  | .succ l, i => dependsOn l i
  | .param j, i => decide (j = i)
  | .max a b, i => dependsOn a i || dependsOn b i
  | .imax a b, i =>
      match levelIsZero b with
      | true => false
      | false => dependsOn a i || dependsOn b i

theorem noneOnly_eq (i j : Nat) :
    noneOnly i j =
      match decide (j = i) with
      | true => none
      | false => some 1 := rfl

theorem eval_noneOnly_zero (i : Nat) :
    eval (noneOnly i) .zero = some 0 := rfl

theorem eval_noneOnly_param_self (i : Nat) :
    eval (noneOnly i) (.param i) = none := by
  unfold eval noneOnly
  rw [decide_eq_true (Eq.refl i)]

theorem eval_noneOnly_param_other
    (i j : Nat) (hne : decide (j = i) = false) :
    eval (noneOnly i) (.param j) = some 1 := by
  simp only [eval, noneOnly]
  rw [hne]

theorem dependsOn_imax_zero (a b : Level) (i : Nat)
    (hz : levelIsZero b = true) :
    dependsOn (.imax a b) i = false := by
  simp only [dependsOn, hz]

/-- At `noneOnly`, a non-zero-class form never evaluates
to `some 0` (params are `1` or `none`; `imax` follows
its right argument). -/
theorem noneOnly_not_zero (l : Level) (i : Nat)
    (hz : levelIsZero l = false) :
    eval (noneOnly i) l ≠ some 0 := by
  induction l with
  | zero => exact Bool.noConfusion hz
  | succ l _ih =>
      intro h
      simp only [eval] at h
      cases he : eval (noneOnly i) l with
      | none =>
          rw [he] at h
          exact Option.noConfusion h
      | some x =>
          rw [he] at h
          injection h with hx
          exact Nat.succ_ne_zero x hx
  | param j =>
      intro h
      simp only [eval, noneOnly] at h
      cases hj : decide (j = i) with
      | true =>
          rw [hj] at h
          exact Option.noConfusion h
      | false =>
          rw [hj] at h
          injection h with hx
          exact Nat.succ_ne_zero 0 hx
  | max a b iha ihb =>
      intro h
      have hm := (eval_max_eq_zero (noneOnly i) a b).mp h
      simp only [levelIsZero] at hz
      cases ha : levelIsZero a with
      | true =>
          cases hb : levelIsZero b with
          | true =>
              rw [ha, hb] at hz
              exact Bool.noConfusion hz
          | false =>
              exact ihb hb hm.right
      | false =>
          exact iha ha hm.left
  | imax a b _iha ihb =>
      intro h
      simp only [levelIsZero] at hz
      exact ihb hz
        ((eval_imax_eq_zero (noneOnly i) a b).mp h)

theorem eval_noneOnly_none_iff :
    ∀ (l : Level) (i : Nat),
      (eval (noneOnly i) l = none) ↔
        (dependsOn l i = true) := by
  intro l i
  induction l with
  | zero =>
      constructor
      · intro h
        exact Option.noConfusion h
      · intro h
        exact Bool.noConfusion h
  | succ l ih =>
      simp only [dependsOn, eval]
      constructor
      · intro h
        cases he : eval (noneOnly i) l with
        | none =>
            exact (ih.mp he)
        | some x =>
            rw [he] at h
            exact Option.noConfusion h
      · intro h
        have hn := ih.mpr h
        rw [hn]
        rfl
  | param j =>
      simp only [dependsOn, eval, noneOnly]
      constructor
      · intro h
        cases hj : decide (j = i) with
        | true => rfl
        | false =>
            rw [hj] at h
            exact Option.noConfusion h
      · intro h
        rw [h]
  | max a b iha ihb =>
      simp only [dependsOn, eval]
      constructor
      · intro h
        cases ha : eval (noneOnly i) a with
        | none =>
            have hd := iha.mp ha
            cases dependsOn b i with
            | true =>
                cases dependsOn a i <;> rfl
            | false =>
                rw [hd]
                rfl
        | some xa =>
            cases hb : eval (noneOnly i) b with
            | none =>
                have hd := ihb.mp hb
                cases dependsOn a i with
                | true => rfl
                | false =>
                    rw [hd]
                    rfl
            | some xb =>
                rw [ha, hb] at h
                exact Option.noConfusion h
      · intro h
        have hor := or_true h
        cases hor with
        | inl ha =>
            have hn := iha.mpr ha
            rw [hn]
            rfl
        | inr hb =>
            have hn := ihb.mpr hb
            cases ha : eval (noneOnly i) a with
            | none => rfl
            | some _ =>
                rw [hn]
                rfl
  | imax a b iha ihb =>
      simp only [dependsOn]
      cases hz : levelIsZero b with
      | true =>
          constructor
          · intro h
            have hb0 : eval (noneOnly i) b =
                some 0 :=
              ((levelIsZero_iff b).mp hz)
                (noneOnly i)
            have him :=
              imax_zero_snd (noneOnly i) a b hb0
            rw [him] at h
            exact Option.noConfusion h
          · intro h
            exact Bool.noConfusion h
      | false =>
          simp only [eval]
          constructor
          · intro h
            cases hb : eval (noneOnly i) b with
            | none =>
                have hd := ihb.mp hb
                cases dependsOn a i with
                | true => rfl
                | false =>
                    rw [hd]
                    rfl
            | some y =>
                cases y with
                | zero =>
                    rw [hb] at h
                    simp only [Option.bind] at h
                    exact Option.noConfusion h
                | succ y =>
                    cases ha :
                      eval (noneOnly i) a with
                    | none =>
                        have hd := iha.mp ha
                        cases dependsOn b i with
                        | true =>
                            cases dependsOn a i <;> rfl
                        | false =>
                            rw [hd]
                            rfl
                    | some xa =>
                        rw [hb, ha] at h
                        exact Option.noConfusion h
          · intro h
            have hor := or_true h
            cases hor with
            | inl ha =>
                have hn := iha.mpr ha
                cases hb : eval (noneOnly i) b with
                | none => rfl
                | some y =>
                    cases y with
                    | zero =>
                        exact False.elim
                          (noneOnly_not_zero b i
                            hz hb)
                    | succ y =>
                        rw [hn]
                        rfl
            | inr hb =>
                have hn := ihb.mpr hb
                rw [hn]
                rfl

theorem eqN_dependsOn {l1 l2 : Level}
    (h : eqN l1 l2) (i : Nat) :
    dependsOn l1 i = dependsOn l2 i := by
  have e : eval (noneOnly i) l1 =
      eval (noneOnly i) l2 := h (noneOnly i)
  cases hd1 : dependsOn l1 i with
  | true =>
      have n1 :=
        (eval_noneOnly_none_iff l1 i).mpr hd1
      have n2 : eval (noneOnly i) l2 = none :=
        e.symm.trans n1
      have hd2 :=
        (eval_noneOnly_none_iff l2 i).mp n2
      rw [hd2]
  | false =>
      cases hd2 : dependsOn l2 i with
      | false => rfl
      | true =>
          have n2 :=
            (eval_noneOnly_none_iff l2 i).mpr hd2
          have n1 : eval (noneOnly i) l1 = none :=
            e.trans n2
          have hd1' :=
            (eval_noneOnly_none_iff l1 i).mp n1
          rw [hd1] at hd1'
          exact Bool.noConfusion hd1'

theorem eqN_zero_nf (l : Level)
    (h : eqN l .zero) : nf l = .zero := by
  induction l with
  | zero => rfl
  | succ l _ih =>
      exfalso
      have hv := h (fun _ => some 0)
      simp only [eval] at hv
      cases he : eval (fun _ => some 0) l with
      | none =>
          rw [he] at hv
          exact Option.noConfusion hv
      | some x =>
          rw [he] at hv
          injection hv with hx
          exact Nat.succ_ne_zero x hx
  | param i =>
      exfalso
      have hv := h (noneOnly i)
      have hn := eval_noneOnly_param_self i
      rw [hn, eval_noneOnly_zero] at hv
      exact Option.noConfusion hv
  | max a b iha ihb =>
      have ha : eqN a .zero :=
        fun ρ =>
          ((eval_max_eq_zero ρ a b).mp (h ρ)).left
      have hb : eqN b .zero :=
        fun ρ =>
          ((eval_max_eq_zero ρ a b).mp (h ρ)).right
      have nfa := iha ha
      have nfb := ihb hb
      simp only [nf]
      rw [nfa, nfb]
      rfl
  | imax a b _iha ihb =>
      have hb : eqN b .zero :=
        (eqN_imax_zero_iff a b).mp h
      have nfb := ihb hb
      simp only [nf, imaxCanon]
      rw [nfb]
      rfl

def isAtom : Level → Bool
  | .zero => false
  | .max _ _ => false
  | _ => true

def allAtoms : List Level → Bool
  | [] => true
  | x :: xs =>
      match isAtom x with
      | true => allAtoms xs
      | false => false

theorem flattenMax_maxOfList_atoms :
    ∀ xs : List Level,
      allAtoms xs = true →
        flattenMax (maxOfList xs) = xs := by
  intro xs
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      cases hx : isAtom x with
      | false =>
          simp only [allAtoms, hx] at h
          exact Bool.noConfusion h
      | true =>
          have htl : allAtoms xs = true := by
            simp only [allAtoms, hx] at h
            exact h
          cases hxs : xs with
          | nil =>
              simp only [maxOfList]
              cases x with
              | zero =>
                  simp only [isAtom] at hx
                  exact Bool.noConfusion hx
              | max _ _ =>
                  simp only [isAtom] at hx
                  exact Bool.noConfusion hx
              | succ _ => rfl
              | param _ => rfl
              | imax _ _ => rfl
          | cons y ys =>
              have ih' := ih
              rw [hxs] at ih' htl
              change flattenMax
                  (.max x (maxOfList (y :: ys))) =
                x :: y :: ys
              simp only [flattenMax]
              rw [ih' htl]
              cases x with
              | zero =>
                  simp only [isAtom] at hx
                  exact Bool.noConfusion hx
              | max _ _ =>
                  simp only [isAtom] at hx
                  exact Bool.noConfusion hx
              | succ _ => rfl
              | param _ => rfl
              | imax _ _ => rfl

-- H-6e: nf idempotence pin (the mix that the pre-fix
-- insertSub failed: a later imax dominating an earlier
-- param, inserted after a smaller param).
#eval (if decide
    (nf (.max
      (.max (.param 1)
        (.imax (.succ (.param 0)) (.param 0)))
      (.param 0)) =
    nf (nf (.max
      (.max (.param 1)
        (.imax (.succ (.param 0)) (.param 0)))
      (.param 0))))
  then 0 else panic "nf: idempotent domination mix")
#eval (if decide
    (nf (.max (.param 0)
      (.imax (.succ (.param 1)) (.param 1))) =
    nf (nf (.max (.param 0)
      (.imax (.succ (.param 1)) (.param 1)))))
  then 0 else panic "nf: idempotent mix 2")

/-! ## H-6e: canonicity of `nf` (`IsCanon`) -/

/-- Canon atoms: not `zero`, not `max`, and `succ`
does not wrap a `max`. An `imax` atom is a remaining
(maybe-zero right) join, not a nest with the same
right argument. -/
def isCanonAtom : Level → Bool
  | .zero => false
  | .max _ _ => false
  | .param _ => true
  | .succ l =>
      match l with
      | .max _ _ => false
      | .zero => true
      | _ => isCanonAtom l
  | .imax a b =>
      match isCanonAtom a, isCanonAtom b with
      | true, true =>
          match levelIsZero a, levelIsZero b,
                decide (a = b), levelNeverZero b with
          | false, false, false, false =>
              match a with
              | .imax _ y =>
                  match decide (y = b) with
                  | false => true
                  | true => false
              | .max _ _ => false
              | _ => true
          | _, _, _, _ => false
      | _, _ => false

def allCanonAtoms : List Level → Bool
  | [] => true
  | x :: xs =>
      match isCanonAtom x with
      | true => allCanonAtoms xs
      | false => false

/-- Adjacent sort: incomparable and `levelLt`. -/
def adjOk (x y : Level) : Bool :=
  match dominates x y, dominates y x, levelLt x y with
  | false, false, true => true
  | _, _, _ => false

def sortedInc : List Level → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs =>
      match adjOk x y with
      | true => sortedInc (y :: xs)
      | false => false

/-- Pairwise: no element of the tail dominates, or
is dominated by, the head; recurse. -/
def noneDominatedBy (u : Level) : List Level → Bool
  | [] => true
  | v :: vs =>
      match dominates u v with
      | true => false
      | false => noneDominatedBy u vs

def antichain : List Level → Bool
  | [] => true
  | x :: xs =>
      match anyDominates x xs, noneDominatedBy x xs with
      | false, true => antichain xs
      | _, _ => false

/-- Structural canonicity of the image of `nf`.
`maxOfList (flattenMax l) = l`, the flattened spine
is canon atoms, sorted, and an antichain. Equivalent
to `nf l = l` once `isCanon_nf` and `nf_of_isCanon`
close. -/
def isCanon (l : Level) : Bool :=
  let xs := flattenMax l
  match allCanonAtoms xs with
  | false => false
  | true =>
      match sortedInc xs, antichain xs,
            decide (maxOfList xs = l) with
      | true, true, true => true
      | _, _, _ => false

def IsCanon (l : Level) : Prop := isCanon l = true

/- H-6h measurement (2/2): does `isCanonAtom`
ACCEPT the nested shape `nf` produces? -/
#eval (if isCanonAtom
    (.imax
      (.imax (.param 0) (.param 1))
      (.param 2)) = true then 0
  else panic "isCanonAtom: nested imax")
#eval (if isCanon
    (nf (.imax
      (.imax (.param 0) (.param 1))
      (.param 2))) = true then 0
  else panic "isCanon: nf nested imax")

theorem isCanonAtom_isAtom (l : Level)
    (h : isCanonAtom l = true) : isAtom l = true := by
  cases l with
  | zero => exact Bool.noConfusion h
  | max _ _ => exact Bool.noConfusion h
  | succ _ => rfl
  | param _ => rfl
  | imax _ _ => rfl

theorem allCanonAtoms_allAtoms :
    ∀ xs : List Level,
      allCanonAtoms xs = true → allAtoms xs = true := by
  intro xs
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      cases hx : isCanonAtom x with
      | false =>
          simp only [allCanonAtoms, hx] at h
          exact Bool.noConfusion h
      | true =>
          have ha := isCanonAtom_isAtom x hx
          have htl : allCanonAtoms xs = true := by
            simp only [allCanonAtoms, hx] at h
            exact h
          simp only [allAtoms, ha]
          exact ih htl

theorem flattenMax_canonAtom (l : Level)
    (h : isCanonAtom l = true) : flattenMax l = [l] := by
  cases l with
  | zero => exact Bool.noConfusion h
  | max _ _ => exact Bool.noConfusion h
  | succ _ => rfl
  | param _ => rfl
  | imax _ _ => rfl

theorem maxFromList_singleton (x : Level) :
    maxFromList [x] = x := rfl

theorem pairImax_singletons (a b : Level) :
    pairImax [a] [b] =
      flattenMax (imaxJoin a b) := by
  simp only [pairImax, mapImaxJoin]
  rw [List.append_nil, List.append_nil]

theorem nf_canonAtom (l : Level)
    (h : isCanonAtom l = true) : nf l = l := by
  induction l with
  | zero => exact Bool.noConfusion h
  | max _ _ _ _ => exact Bool.noConfusion h
  | param i => rfl
  | succ l ih =>
      simp only [nf]
      cases l with
      | max _ _ =>
          simp only [isCanonAtom] at h
          exact Bool.noConfusion h
      | zero => rfl
      | param i => rfl
      | succ l' =>
          simp only [isCanonAtom] at h
          have ih' := ih h
          rw [ih']
          rfl
      | imax a b =>
          simp only [isCanonAtom] at h
          have ih' := ih h
          rw [ih']
          rfl
  | imax a b iha ihb =>
      simp only [nf]
      cases ha : isCanonAtom a with
      | false =>
          simp only [isCanonAtom, ha] at h
          exact Bool.noConfusion h
      | true =>
          cases hb : isCanonAtom b with
          | false =>
              simp only [isCanonAtom, ha, hb] at h
              exact Bool.noConfusion h
          | true =>
              have iha' := iha ha
              have ihb' := ihb hb
              rw [iha', ihb']
              cases hza : levelIsZero a with
              | true =>
                  simp only [isCanonAtom, ha, hb, hza] at h
                  exact Bool.noConfusion h
              | false =>
                  cases hzb : levelIsZero b with
                  | true =>
                      simp only [isCanonAtom, ha, hb,
                        hza, hzb] at h
                      exact Bool.noConfusion h
                  | false =>
                      cases heq : decide (a = b) with
                      | true =>
                          simp only [isCanonAtom, ha, hb,
                            hza, hzb, heq] at h
                          exact Bool.noConfusion h
                      | false =>
                          cases hnv : levelNeverZero b with
                          | true =>
                              simp only [isCanonAtom, ha, hb,
                                hza, hzb, heq, hnv] at h
                              exact Bool.noConfusion h
                          | false =>
                              unfold imaxCanon
                              rw [hzb, hza, heq, hnv]
                              simp only []
                              rw [flattenMax_canonAtom a ha]
                              rw [flattenMax_canonAtom b hb]
                              rw [pairImax_singletons]
                              unfold imaxJoin
                              rw [heq, hzb, hza, hnv]
                              simp only []
                              cases a with
                              | max _ _ =>
                                  exact Bool.noConfusion ha
                              | zero =>
                                  exact Bool.noConfusion ha
                              | imax x y =>
                                  cases hy : decide (y = b) with
                                  | true =>
                                      have hfalse :
                                          isCanonAtom
                                            (.imax (.imax x y) b) =
                                          false := by
                                        change (match
                                            isCanonAtom
                                              (.imax x y),
                                            isCanonAtom b with
                                          | true, true =>
                                            match
                                              levelIsZero
                                                (.imax x y),
                                              levelIsZero b,
                                              decide
                                                (.imax x y = b),
                                              levelNeverZero b with
                                            | false, false,
                                              false, false =>
                                              match decide
                                                (y = b) with
                                              | false => true
                                              | true => false
                                            | _, _, _, _ =>
                                              false
                                          | _, _ => false) =
                                          false
                                        rw [ha, hb, hza, hzb,
                                          heq, hnv, hy]
                                      rw [hfalse] at h
                                      exact Bool.noConfusion h
                                  | false =>
                                      simp only []
                                      rw [hy]
                                      simp only []
                                      rfl
                              | succ l =>
                                  simp only []
                                  rfl
                              | param i =>
                                  simp only []
                                  rfl

theorem isCanon_zero : isCanon .zero = true := rfl

theorem isCanon_of_atom (l : Level)
    (h : isCanonAtom l = true) : isCanon l = true := by
  have hflat : flattenMax l = [l] :=
    flattenMax_canonAtom l h
  have hsort : sortedInc [l] = true := rfl
  have hanti : antichain [l] = true := rfl
  have hmax : maxOfList [l] = l := rfl
  have hall : allCanonAtoms [l] = true := by
    simp only [allCanonAtoms, h]
  simp only [isCanon]
  rw [hflat, hall, hsort, hanti, hmax]
  rw [decide_eq_true (Eq.refl l)]

theorem allCanonAtoms_tail (x : Level)
    (xs : List Level)
    (h : allCanonAtoms (x :: xs) = true) :
    allCanonAtoms xs = true := by
  cases hx : isCanonAtom x with
  | false =>
      simp only [allCanonAtoms, hx] at h
      exact Bool.noConfusion h
  | true =>
      simp only [allCanonAtoms, hx] at h
      exact h

theorem allCanonAtoms_head (x : Level)
    (xs : List Level)
    (h : allCanonAtoms (x :: xs) = true) :
    isCanonAtom x = true := by
  cases hx : isCanonAtom x with
  | false =>
      simp only [allCanonAtoms, hx] at h
      exact Bool.noConfusion h
  | true => rfl

theorem sortedInc_tail (x : Level)
    (xs : List Level)
    (h : sortedInc (x :: xs) = true) :
    sortedInc xs = true := by
  cases xs with
  | nil => rfl
  | cons y ys =>
      cases ha : adjOk x y with
      | false =>
          simp only [sortedInc, ha] at h
          exact Bool.noConfusion h
      | true =>
          simp only [sortedInc, ha] at h
          exact h

theorem antichain_tail (x : Level)
    (xs : List Level)
    (h : antichain (x :: xs) = true) :
    antichain xs = true := by
  cases h1 : anyDominates x xs with
  | true =>
      simp only [antichain, h1] at h
      exact Bool.noConfusion h
  | false =>
      cases h2 : noneDominatedBy x xs with
      | false =>
          simp only [antichain, h1, h2] at h
          exact Bool.noConfusion h
      | true =>
          simp only [antichain, h1, h2] at h
          exact h

/-! ## H-6f: antichain invariant of `insertSub`

H-6e wall: `rfl` on `decide (i < i)` at a variable.
`Nat.lt_irrefl` + `of_decide_eq_true` closes it. -/

theorem ctorOrd_lt_self (a : Level) :
    decide (ctorOrd a < ctorOrd a) = false := by
  cases a with
  | zero => rfl
  | succ _ => rfl
  | max _ _ => rfl
  | imax _ _ => rfl
  | param _ => rfl

theorem dominates_refl (u : Level) :
    dominates u u = true := by
  simp only [dominates]
  cases h : peelOff u with
  | mk n b =>
      cases hle : decide (n ≤ n) with
      | false =>
          exact False.elim
            (of_decide_eq_false hle (Nat.le_refl n))
      | true => rfl

theorem anyDominates_head (u : Level)
    (xs : List Level) :
    anyDominates u (u :: xs) = true := by
  simp only [anyDominates]
  have hr := dominates_refl u
  rw [hr]

theorem insertSub_of_anyDom (u : Level)
    (xs : List Level)
    (h : anyDominates u xs = true) :
    insertSub u xs = xs := by
  cases xs with
  | nil => exact Bool.noConfusion h
  | cons v vs =>
      cases ha : anyDominates u (v :: vs) with
      | true =>
          simp only [insertSub, ha]
      | false =>
          rw [ha] at h
          exact Bool.noConfusion h

theorem insertSub_cons_self (u : Level)
    (xs : List Level) :
    insertSub u (u :: xs) = u :: xs :=
  insertSub_of_anyDom u (u :: xs)
    (anyDominates_head u xs)

theorem false_ne_true : ¬ (false = true) :=
  fun h => nomatch h

theorem true_eq_true : true = true := Eq.refl true

theorem levelLt_irrefl :
    ∀ a : Level, levelLt a a = false
  | .zero => rfl
  | .param i => by
      change decide (i < i) = false
      cases hi : decide (i < i) with
      | true =>
          exact False.elim
            (Nat.lt_irrefl i
              (of_decide_eq_true hi))
      | false => rfl
  | .succ l => levelLt_irrefl l
  | .max x y => by
      have hx := levelLt_irrefl x
      have hy := levelLt_irrefl y
      change (if levelLt x x then true
          else if decide (x = x) then
            levelLt y y
          else false) = false
      rw [hx]
      rw [if_neg false_ne_true]
      cases heq : decide (x = x) with
      | false =>
          exact False.elim
            (of_decide_eq_false heq (Eq.refl x))
      | true =>
          rw [if_pos true_eq_true]
          exact hy
  | .imax x y => by
      have hx := levelLt_irrefl x
      have hy := levelLt_irrefl y
      change (if levelLt x x then true
          else if decide (x = x) then
            levelLt y y
          else false) = false
      rw [hx]
      rw [if_neg false_ne_true]
      cases heq : decide (x = x) with
      | false =>
          exact False.elim
            (of_decide_eq_false heq (Eq.refl x))
      | true =>
          rw [if_pos true_eq_true]
          exact hy

theorem decide_nat_lt_asymm (i j : Nat)
    (h : decide (i < j) = true) :
    decide (j < i) = false := by
  have hij : i < j := of_decide_eq_true h
  have hji : ¬ (j < i) := Nat.lt_asymm hij
  cases hd : decide (j < i) with
  | true =>
      exact False.elim
        (hji (of_decide_eq_true hd))
  | false => rfl

theorem ctorOrd_lt_decide (a b : Level)
    (h : ctorOrd a < ctorOrd b) :
    decide (ctorOrd a < ctorOrd b) = true := by
  cases hd : decide (ctorOrd a < ctorOrd b) with
  | false =>
      exact False.elim (of_decide_eq_false hd h)
  | true => rfl

theorem ctorOrd_lt_levelLt (a b : Level)
    (h : ctorOrd a < ctorOrd b) :
    levelLt a b = true := by
  cases a with
  | zero =>
      cases b with
      | zero => exact False.elim (Nat.lt_irrefl 0 h)
      | param _ => rfl
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => rfl
  | param _ =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero 1 h)
      | param _ => exact False.elim (Nat.lt_irrefl 1 h)
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => rfl
  | succ _ =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero 2 h)
      | param _ => nomatch h
      | succ _ => exact False.elim (Nat.lt_irrefl 2 h)
      | max _ _ => rfl
      | imax _ _ => rfl
  | max _ _ =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero 3 h)
      | param _ => nomatch h
      | succ _ => nomatch h
      | max _ _ => exact False.elim (Nat.lt_irrefl 3 h)
      | imax _ _ => rfl
  | imax _ _ =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero 4 h)
      | param _ => nomatch h
      | succ _ => nomatch h
      | max _ _ => nomatch h
      | imax _ _ => exact False.elim (Nat.lt_irrefl 4 h)

theorem ctorOrd_gt_levelLt_false (a b : Level)
    (h : ctorOrd b < ctorOrd a) :
    levelLt a b = false := by
  cases a with
  | zero =>
      cases b with
      | zero => exact False.elim (Nat.lt_irrefl 0 h)
      | param _ => exact False.elim (Nat.not_lt_zero 1 h)
      | succ _ => exact False.elim (Nat.not_lt_zero 2 h)
      | max _ _ => exact False.elim (Nat.not_lt_zero 3 h)
      | imax _ _ => exact False.elim (Nat.not_lt_zero 4 h)
  | param _ =>
      cases b with
      | zero => rfl
      | param _ => exact False.elim (Nat.lt_irrefl 1 h)
      | succ _ => nomatch h
      | max _ _ => nomatch h
      | imax _ _ => nomatch h
  | succ _ =>
      cases b with
      | zero => rfl
      | param _ => rfl
      | succ _ => exact False.elim (Nat.lt_irrefl 2 h)
      | max _ _ => nomatch h
      | imax _ _ => nomatch h
  | max _ _ =>
      cases b with
      | zero => rfl
      | param _ => rfl
      | succ _ => rfl
      | max _ _ => exact False.elim (Nat.lt_irrefl 3 h)
      | imax _ _ => nomatch h
  | imax _ _ =>
      cases b with
      | zero => rfl
      | param _ => rfl
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => exact False.elim (Nat.lt_irrefl 4 h)

theorem levelLt_ctorOrd_le (a b : Level)
    (h : levelLt a b = true) :
    ctorOrd a ≤ ctorOrd b := by
  cases hlt : decide (ctorOrd a < ctorOrd b) with
  | true =>
      exact Nat.le_of_lt (of_decide_eq_true hlt)
  | false =>
      cases hgt : decide (ctorOrd b < ctorOrd a) with
      | true =>
          have hba : ctorOrd b < ctorOrd a :=
            of_decide_eq_true hgt
          have hf := ctorOrd_gt_levelLt_false a b hba
          rw [hf] at h
          exact Bool.noConfusion h
      | false =>
          have hn : ¬ (ctorOrd b < ctorOrd a) :=
            of_decide_eq_false hgt
          exact Nat.le_of_not_lt hn

theorem levelLt_asymm_lex
    (x y u v : Level)
    (ihx : ∀ b, levelLt x b = true →
      levelLt b x = false)
    (ihy : ∀ b, levelLt y b = true →
      levelLt b y = false)
    (h : (if levelLt x u then true
          else if decide (x = u) then
            levelLt y v
          else false) = true) :
    (if levelLt u x then true
     else if decide (u = x) then
       levelLt v y
     else false) = false := by
  cases hxu : levelLt x u with
  | true =>
      have hux := ihx u hxu
      rw [hux]
      rw [if_neg false_ne_true]
      cases heq : decide (u = x) with
      | true =>
          have huxeq : u = x :=
            of_decide_eq_true heq
          rw [huxeq] at hxu
          have hi := levelLt_irrefl x
          rw [hi] at hxu
          exact Bool.noConfusion hxu
      | false => rfl
  | false =>
      rw [hxu] at h
      rw [if_neg false_ne_true] at h
      cases heq : decide (x = u) with
      | false =>
          rw [heq] at h
          rw [if_neg false_ne_true] at h
          exact Bool.noConfusion h
      | true =>
          rw [heq] at h
          rw [if_pos true_eq_true] at h
          have hvy := ihy v h
          have hxueq : x = u :=
            of_decide_eq_true heq
          rw [hxueq]
          have hi := levelLt_irrefl u
          rw [hi]
          rw [if_neg false_ne_true]
          cases hd : decide (u = u) with
          | false =>
              exact False.elim
                (of_decide_eq_false hd (Eq.refl u))
          | true =>
              rw [if_pos true_eq_true]
              exact hvy

theorem levelLt_asymm (a b : Level)
    (h : levelLt a b = true) :
    levelLt b a = false := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          have hi := levelLt_irrefl Level.zero
          rw [hi] at h
          exact Bool.noConfusion h
      | param _ => rfl
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => rfl
  | param i =>
      cases b with
      | zero => nomatch h
      | param j => exact decide_nat_lt_asymm i j h
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => rfl
  | succ x ih =>
      cases b with
      | zero => nomatch h
      | param _ => nomatch h
      | succ y => exact ih y h
      | max _ _ => rfl
      | imax _ _ => rfl
  | max x y ihx ihy =>
      cases b with
      | zero => nomatch h
      | param _ => nomatch h
      | succ _ => nomatch h
      | max u v =>
          exact levelLt_asymm_lex x y u v
            ihx ihy h
      | imax _ _ => rfl
  | imax x y ihx ihy =>
      cases b with
      | zero => nomatch h
      | param _ => nomatch h
      | succ _ => nomatch h
      | max _ _ => nomatch h
      | imax u v =>
          exact levelLt_asymm_lex x y u v
            ihx ihy h

theorem ctorOrd_eq_zero (a : Level)
    (h : ctorOrd a = 0) : a = Level.zero := by
  cases a with
  | zero => rfl
  | param _ => nomatch h
  | succ _ => nomatch h
  | max _ _ => nomatch h
  | imax _ _ => nomatch h

theorem ctorOrd_eq_param (a : Level)
    (h : ctorOrd a = 1) : ∃ i, a = Level.param i := by
  cases a with
  | zero => nomatch h
  | param i => exact ⟨i, rfl⟩
  | succ _ => nomatch h
  | max _ _ => nomatch h
  | imax _ _ => nomatch h

theorem ctorOrd_eq_succ (a : Level)
    (h : ctorOrd a = 2) : ∃ l, a = Level.succ l := by
  cases a with
  | zero => nomatch h
  | param _ => nomatch h
  | succ l => exact ⟨l, rfl⟩
  | max _ _ => nomatch h
  | imax _ _ => nomatch h

theorem ctorOrd_eq_max (a : Level)
    (h : ctorOrd a = 3) :
    ∃ x y, a = Level.max x y := by
  cases a with
  | zero => nomatch h
  | param _ => nomatch h
  | succ _ => nomatch h
  | max x y => exact ⟨x, y, rfl⟩
  | imax _ _ => nomatch h

theorem ctorOrd_eq_imax (a : Level)
    (h : ctorOrd a = 4) :
    ∃ x y, a = Level.imax x y := by
  cases a with
  | zero => nomatch h
  | param _ => nomatch h
  | succ _ => nomatch h
  | max _ _ => nomatch h
  | imax x y => exact ⟨x, y, rfl⟩

theorem levelLt_trans_lex
    (x y u v p q : Level)
    (ihx : ∀ b c, levelLt x b = true →
      levelLt b c = true →
        levelLt x c = true)
    (ihy : ∀ b c, levelLt y b = true →
      levelLt b c = true →
        levelLt y c = true)
    (h1 : (if levelLt x u then true
           else if decide (x = u) then
             levelLt y v
           else false) = true)
    (h2 : (if levelLt u p then true
           else if decide (u = p) then
             levelLt v q
           else false) = true) :
    (if levelLt x p then true
     else if decide (x = p) then
       levelLt y q
     else false) = true := by
  cases hxu : levelLt x u with
  | true =>
      cases hup : levelLt u p with
      | true =>
          have hxp := ihx u p hxu hup
          rw [hxp]
          rw [if_pos true_eq_true]
      | false =>
          rw [hup] at h2
          rw [if_neg false_ne_true] at h2
          cases heq : decide (u = p) with
          | false =>
              rw [heq] at h2
              rw [if_neg false_ne_true] at h2
              exact Bool.noConfusion h2
          | true =>
              have hup_eq : u = p :=
                of_decide_eq_true heq
              rw [← hup_eq]
              rw [hxu]
              rw [if_pos true_eq_true]
  | false =>
      rw [hxu] at h1
      rw [if_neg false_ne_true] at h1
      cases heq1 : decide (x = u) with
      | false =>
          rw [heq1] at h1
          rw [if_neg false_ne_true] at h1
          exact Bool.noConfusion h1
      | true =>
          have hxueq : x = u :=
            of_decide_eq_true heq1
          rw [heq1] at h1
          rw [if_pos true_eq_true] at h1
          cases hup : levelLt u p with
          | true =>
              rw [hxueq]
              rw [hup]
              rw [if_pos true_eq_true]
          | false =>
              rw [hup] at h2
              rw [if_neg false_ne_true] at h2
              cases heq2 : decide (u = p) with
              | false =>
                  rw [heq2] at h2
                  rw [if_neg false_ne_true] at h2
                  exact Bool.noConfusion h2
              | true =>
                  have hupeq : u = p :=
                    of_decide_eq_true heq2
                  rw [heq2] at h2
                  rw [if_pos true_eq_true] at h2
                  have hyq := ihy v q h1 h2
                  rw [hxueq, hupeq]
                  have hi := levelLt_irrefl p
                  rw [hi]
                  rw [if_neg false_ne_true]
                  cases hd : decide (p = p) with
                  | false =>
                      exact False.elim
                        (of_decide_eq_false hd
                          (Eq.refl p))
                  | true =>
                      rw [if_pos true_eq_true]
                      exact hyq

theorem levelLt_trans (a b c : Level)
    (h1 : levelLt a b = true)
    (h2 : levelLt b c = true) :
    levelLt a c = true := by
  induction a generalizing b c with
  | zero =>
      cases c with
      | zero =>
          have hab :=
            levelLt_ctorOrd_le Level.zero b h1
          have hbc :=
            levelLt_ctorOrd_le b Level.zero h2
          have hb0 : ctorOrd b = 0 :=
            Nat.le_antisymm hbc hab
          have hbz := ctorOrd_eq_zero b hb0
          rw [hbz] at h1
          have hi := levelLt_irrefl Level.zero
          rw [hi] at h1
          exact Bool.noConfusion h1
      | param _ => rfl
      | succ _ => rfl
      | max _ _ => rfl
      | imax _ _ => rfl
  | param i =>
      have hab :=
        levelLt_ctorOrd_le (.param i) b h1
      have hbc := levelLt_ctorOrd_le b c h2
      cases hlt : decide (1 < ctorOrd b) with
      | true =>
          exact ctorOrd_lt_levelLt (.param i) c
            (Nat.lt_of_lt_of_le
              (of_decide_eq_true hlt) hbc)
      | false =>
          have hn : ¬ (1 < ctorOrd b) :=
            of_decide_eq_false hlt
          have heq : ctorOrd b = 1 :=
            Nat.le_antisymm
              (Nat.le_of_not_lt hn) hab
          have ⟨j, hb⟩ := ctorOrd_eq_param b heq
          cases hgt : decide (1 < ctorOrd c) with
          | true =>
              exact ctorOrd_lt_levelLt (.param i) c
                (of_decide_eq_true hgt)
          | false =>
              have hn2 : ¬ (1 < ctorOrd c) :=
                of_decide_eq_false hgt
              have hge : 1 ≤ ctorOrd c := by
                rw [heq] at hbc
                exact hbc
              have heqc : ctorOrd c = 1 :=
                Nat.le_antisymm
                  (Nat.le_of_not_lt hn2) hge
              have ⟨k, hc⟩ := ctorOrd_eq_param c heqc
              rw [hb] at h1
              rw [hb, hc] at h2
              rw [hc]
              have hij : i < j :=
                of_decide_eq_true h1
              have hjk : j < k :=
                of_decide_eq_true h2
              have hik : i < k :=
                Nat.lt_trans hij hjk
              cases hd : decide (i < k) with
              | false =>
                  exact False.elim
                    (of_decide_eq_false hd hik)
              | true => exact hd
  | succ x ih =>
      have hab :=
        levelLt_ctorOrd_le (.succ x) b h1
      have hbc := levelLt_ctorOrd_le b c h2
      cases hlt : decide (2 < ctorOrd b) with
      | true =>
          exact ctorOrd_lt_levelLt (.succ x) c
            (Nat.lt_of_lt_of_le
              (of_decide_eq_true hlt) hbc)
      | false =>
          have hn : ¬ (2 < ctorOrd b) :=
            of_decide_eq_false hlt
          have heq : ctorOrd b = 2 :=
            Nat.le_antisymm
              (Nat.le_of_not_lt hn) hab
          have ⟨y, hb⟩ := ctorOrd_eq_succ b heq
          cases hgt : decide (2 < ctorOrd c) with
          | true =>
              exact ctorOrd_lt_levelLt (.succ x) c
                (of_decide_eq_true hgt)
          | false =>
              have hn2 : ¬ (2 < ctorOrd c) :=
                of_decide_eq_false hgt
              have hge : 2 ≤ ctorOrd c := by
                rw [heq] at hbc
                exact hbc
              have heqc : ctorOrd c = 2 :=
                Nat.le_antisymm
                  (Nat.le_of_not_lt hn2) hge
              have ⟨z, hc⟩ := ctorOrd_eq_succ c heqc
              rw [hb] at h1
              rw [hb, hc] at h2
              rw [hc]
              exact ih y z h1 h2
  | max x y ihx ihy =>
      have hab :=
        levelLt_ctorOrd_le (.max x y) b h1
      have hbc := levelLt_ctorOrd_le b c h2
      cases hlt : decide (3 < ctorOrd b) with
      | true =>
          exact ctorOrd_lt_levelLt (.max x y) c
            (Nat.lt_of_lt_of_le
              (of_decide_eq_true hlt) hbc)
      | false =>
          have hn : ¬ (3 < ctorOrd b) :=
            of_decide_eq_false hlt
          have heq : ctorOrd b = 3 :=
            Nat.le_antisymm
              (Nat.le_of_not_lt hn) hab
          have ⟨u, v, hb⟩ := ctorOrd_eq_max b heq
          cases hgt : decide (3 < ctorOrd c) with
          | true =>
              exact ctorOrd_lt_levelLt (.max x y) c
                (of_decide_eq_true hgt)
          | false =>
              have hn2 : ¬ (3 < ctorOrd c) :=
                of_decide_eq_false hgt
              have hge : 3 ≤ ctorOrd c := by
                rw [heq] at hbc
                exact hbc
              have heqc : ctorOrd c = 3 :=
                Nat.le_antisymm
                  (Nat.le_of_not_lt hn2) hge
              have ⟨p, q, hc⟩ := ctorOrd_eq_max c heqc
              rw [hb] at h1
              rw [hb, hc] at h2
              rw [hc]
              exact levelLt_trans_lex x y u v p q
                ihx ihy h1 h2
  | imax x y ihx ihy =>
      have hab :=
        levelLt_ctorOrd_le (.imax x y) b h1
      have hbc := levelLt_ctorOrd_le b c h2
      cases hlt : decide (4 < ctorOrd b) with
      | true =>
          exact ctorOrd_lt_levelLt (.imax x y) c
            (Nat.lt_of_lt_of_le
              (of_decide_eq_true hlt) hbc)
      | false =>
          have hn : ¬ (4 < ctorOrd b) :=
            of_decide_eq_false hlt
          have heq : ctorOrd b = 4 :=
            Nat.le_antisymm
              (Nat.le_of_not_lt hn) hab
          have ⟨u, v, hb⟩ := ctorOrd_eq_imax b heq
          cases hgt : decide (4 < ctorOrd c) with
          | true =>
              exact ctorOrd_lt_levelLt (.imax x y) c
                (of_decide_eq_true hgt)
          | false =>
              have hn2 : ¬ (4 < ctorOrd c) :=
                of_decide_eq_false hgt
              have hge : 4 ≤ ctorOrd c := by
                rw [heq] at hbc
                exact hbc
              have heqc : ctorOrd c = 4 :=
                Nat.le_antisymm
                  (Nat.le_of_not_lt hn2) hge
              have ⟨p, q, hc⟩ :=
                ctorOrd_eq_imax c heqc
              rw [hb] at h1
              rw [hb, hc] at h2
              rw [hc]
              exact levelLt_trans_lex x y u v p q
                ihx ihy h1 h2

theorem adjOk_lt (x y : Level)
    (h : adjOk x y = true) :
    levelLt x y = true := by
  cases hd1 : dominates x y with
  | true =>
      simp only [adjOk, hd1] at h
      exact Bool.noConfusion h
  | false =>
      cases hd2 : dominates y x with
      | true =>
          simp only [adjOk, hd1, hd2] at h
          exact Bool.noConfusion h
      | false =>
          cases hlt : levelLt x y with
          | false =>
              simp only [adjOk, hd1, hd2, hlt] at h
              exact Bool.noConfusion h
          | true => rfl

theorem noneDominatedBy_last (x u : Level) :
    ∀ xs : List Level,
      noneDominatedBy x (xs ++ [u]) = true →
        dominates x u = false
  | [], h => by
      cases hd : dominates x u with
      | true =>
          simp only [noneDominatedBy, List.nil_append,
            hd] at h
          exact Bool.noConfusion h
      | false => rfl
  | v :: vs, h => by
      cases hd : dominates x v with
      | true =>
          simp only [noneDominatedBy, List.cons_append,
            hd] at h
          exact Bool.noConfusion h
      | false =>
          simp only [noneDominatedBy, List.cons_append,
            hd] at h
          exact noneDominatedBy_last x u vs h

theorem antichain_snoc_anyDom (u : Level) :
    ∀ xs : List Level,
      antichain (xs ++ [u]) = true →
        anyDominates u xs = false
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.cons_append] at h
      cases ha : anyDominates x (xs ++ [u]) with
      | true =>
          simp only [antichain] at h
          rw [ha] at h
          exact Bool.noConfusion h
      | false =>
          cases hn : noneDominatedBy x
              (xs ++ [u]) with
          | false =>
              simp only [antichain] at h
              rw [ha, hn] at h
              exact Bool.noConfusion h
          | true =>
              simp only [antichain] at h
              rw [ha, hn] at h
              have hxu :=
                noneDominatedBy_last x u xs hn
              have ih :=
                antichain_snoc_anyDom u xs h
              simp only [anyDominates, hxu]
              exact ih

theorem anyDominates_false_suffix (u : Level) :
    ∀ xs ys : List Level,
      anyDominates u (xs ++ ys) = false →
        anyDominates u ys = false
  | [], _, h => h
  | x :: xs, ys, h => by
      simp only [anyDominates, List.cons_append]
        at h
      cases hd : dominates x u with
      | true =>
          simp only [hd] at h
          exact Bool.noConfusion h
      | false =>
          rw [hd] at h
          exact anyDominates_false_suffix u xs ys h

theorem antichain_snoc_not_dom (u : Level)
    (x : Level) (xs : List Level)
    (h : antichain ((x :: xs) ++ [u]) = true) :
    dominates u x = false := by
  rw [List.cons_append] at h
  cases ha : anyDominates x (xs ++ [u]) with
  | true =>
      simp only [antichain] at h
      rw [ha] at h
      exact Bool.noConfusion h
  | false =>
      have hsuf :=
        anyDominates_false_suffix x xs [u] ha
      simp only [anyDominates] at hsuf
      cases hd : dominates u x with
      | true =>
          rw [hd] at hsuf
          exact Bool.noConfusion hsuf
      | false => rfl

theorem sortedInc_snoc_head_lt (u : Level)
    (x : Level) :
    ∀ xs : List Level,
      sortedInc ((x :: xs) ++ [u]) = true →
        levelLt x u = true
  | [], h => by
      simp only [List.cons_append, List.nil_append]
        at h
      cases ha : adjOk x u with
      | false =>
          simp only [sortedInc, ha] at h
          exact Bool.noConfusion h
      | true => exact adjOk_lt x u ha
  | y :: ys, h => by
      simp only [List.cons_append] at h
      cases ha : adjOk x y with
      | false =>
          simp only [sortedInc, ha] at h
          exact Bool.noConfusion h
      | true =>
          simp only [sortedInc, ha] at h
          have hxu := adjOk_lt x y ha
          have hyu :=
            sortedInc_snoc_head_lt u y ys h
          exact levelLt_trans x y u hxu hyu

theorem insertSub_snoc (u : Level) :
    ∀ xs : List Level,
      sortedInc (xs ++ [u]) = true →
      antichain (xs ++ [u]) = true →
        insertSub u xs = xs ++ [u]
  | [], _, _ => rfl
  | v :: vs, hsort, hanti => by
      have hany :=
        antichain_snoc_anyDom u (v :: vs) hanti
      have hnd :=
        antichain_snoc_not_dom u v vs hanti
      have hlt :=
        sortedInc_snoc_head_lt u v vs hsort
      have hnlt := levelLt_asymm v u hlt
      cases ha : anyDominates u (v :: vs) with
      | true =>
          rw [ha] at hany
          exact Bool.noConfusion hany
      | false =>
          cases hd : dominates u v with
          | true =>
              rw [hd] at hnd
              exact Bool.noConfusion hnd
          | false =>
              cases hltu : levelLt u v with
              | true =>
                  rw [hltu] at hnlt
                  exact Bool.noConfusion hnlt
              | false =>
                  simp only [insertSub, ha, hd,
                    hltu]
                  have hsort' :
                      sortedInc (vs ++ [u]) =
                        true := by
                    cases vs with
                    | nil => rfl
                    | cons w ws =>
                        simp only [sortedInc]
                          at hsort
                        cases ha2 : adjOk v w with
                        | false =>
                            simp only [ha2]
                              at hsort
                            exact Bool.noConfusion
                              hsort
                        | true =>
                            simp only [ha2]
                              at hsort
                            exact hsort
                  have hanti' :
                      antichain (vs ++ [u]) =
                        true :=
                    antichain_tail v (vs ++ [u])
                      (by
                        simp only
                          [List.cons_append]
                          at hanti
                        exact hanti)
                  have ih :=
                    insertSub_snoc u vs
                      hsort' hanti'
                  rw [ih]
                  rfl

theorem anyDominates_false_prefix (u : Level) :
    ∀ xs ys : List Level,
      anyDominates u (xs ++ ys) = false →
        anyDominates u xs = false
  | [], _, _ => rfl
  | x :: xs, ys, h => by
      simp only [anyDominates, List.cons_append]
        at h
      cases hd : dominates x u with
      | true =>
          simp only [hd] at h
          exact Bool.noConfusion h
      | false =>
          simp only [anyDominates, hd]
          rw [hd] at h
          exact anyDominates_false_prefix u xs ys h

theorem noneDominatedBy_prefix (u : Level) :
    ∀ xs ys : List Level,
      noneDominatedBy u (xs ++ ys) = true →
        noneDominatedBy u xs = true
  | [], _, _ => rfl
  | x :: xs, ys, h => by
      simp only [noneDominatedBy, List.cons_append]
        at h
      cases hd : dominates u x with
      | true =>
          simp only [hd] at h
          exact Bool.noConfusion h
      | false =>
          simp only [noneDominatedBy, hd]
          rw [hd] at h
          exact noneDominatedBy_prefix u xs ys h

theorem sortedInc_prefix :
    ∀ xs ys : List Level,
      sortedInc (xs ++ ys) = true →
        sortedInc xs = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: xs, ys, h => by
      simp only [List.cons_append] at h
      cases ha : adjOk x y with
      | false =>
          simp only [sortedInc, ha] at h
          exact Bool.noConfusion h
      | true =>
          simp only [sortedInc, ha] at h ⊢
          exact sortedInc_prefix (y :: xs) ys h

theorem antichain_prefix :
    ∀ xs ys : List Level,
      antichain (xs ++ ys) = true →
        antichain xs = true
  | [], _, _ => rfl
  | x :: xs, ys, h => by
      simp only [List.cons_append] at h
      cases ha : anyDominates x (xs ++ ys) with
      | true =>
          simp only [antichain, ha] at h
          exact Bool.noConfusion h
      | false =>
          cases hn : noneDominatedBy x
              (xs ++ ys) with
          | false =>
              simp only [antichain, ha, hn] at h
              exact Bool.noConfusion h
          | true =>
              simp only [antichain, ha, hn] at h ⊢
              have ha' :=
                anyDominates_false_prefix x xs ys ha
              have hn' :=
                noneDominatedBy_prefix x xs ys hn
              simp only [ha', hn']
              exact antichain_prefix xs ys h

theorem append_cons_eq (acc : List Level)
    (y : Level) (ys : List Level) :
    (acc ++ [y]) ++ ys = acc ++ (y :: ys) := by
  rw [List.append_assoc]
  rfl

theorem foldlIns_prefix_id :
    ∀ acc ys : List Level,
      sortedInc (acc ++ ys) = true →
      antichain (acc ++ ys) = true →
        foldlIns acc ys = acc ++ ys
  | acc, [], _, _ => by
      rw [List.append_nil]
      rfl
  | acc, y :: ys, hsort, hanti => by
      simp only [foldlIns]
      have heq := append_cons_eq acc y ys
      have hsort' :
          sortedInc (acc ++ [y]) = true := by
        rw [← heq] at hsort
        exact sortedInc_prefix (acc ++ [y]) ys
          hsort
      have hanti' :
          antichain (acc ++ [y]) = true := by
        rw [← heq] at hanti
        exact antichain_prefix (acc ++ [y]) ys
          hanti
      have hins :=
        insertSub_snoc y acc hsort' hanti'
      rw [hins]
      have hsort2 :
          sortedInc ((acc ++ [y]) ++ ys) =
            true := by
        rw [heq]
        exact hsort
      have hanti2 :
          antichain ((acc ++ [y]) ++ ys) =
            true := by
        rw [heq]
        exact hanti
      have ih :=
        foldlIns_prefix_id (acc ++ [y]) ys
          hsort2 hanti2
      rw [ih, heq]

theorem foldlIns_sorted_antichain_id
    (xs : List Level)
    (hs : sortedInc xs = true)
    (ha : antichain xs = true) :
    foldlIns [] xs = xs := by
  have h := foldlIns_prefix_id [] xs
    (by simp only [List.nil_append]; exact hs)
    (by simp only [List.nil_append]; exact ha)
  simp only [List.nil_append] at h
  exact h

theorem isCanon_allCanonAtoms (l : Level)
    (h : isCanon l = true) :
    allCanonAtoms (flattenMax l) = true := by
  simp only [isCanon] at h
  cases h1 : allCanonAtoms (flattenMax l) with
  | false =>
      rw [h1] at h
      exact Bool.noConfusion h
  | true => rfl

theorem isCanon_sortedInc (l : Level)
    (h : isCanon l = true) :
    sortedInc (flattenMax l) = true := by
  have h1 := isCanon_allCanonAtoms l h
  simp only [isCanon] at h
  rw [h1] at h
  cases h2 : sortedInc (flattenMax l) with
  | false =>
      rw [h2] at h
      exact Bool.noConfusion h
  | true => rfl

theorem isCanon_antichain (l : Level)
    (h : isCanon l = true) :
    antichain (flattenMax l) = true := by
  have h1 := isCanon_allCanonAtoms l h
  have h2 := isCanon_sortedInc l h
  simp only [isCanon] at h
  rw [h1, h2] at h
  cases h3 : antichain (flattenMax l) with
  | false =>
      rw [h3] at h
      exact Bool.noConfusion h
  | true => rfl

theorem isCanon_maxOfList (l : Level)
    (h : isCanon l = true) :
    maxOfList (flattenMax l) = l := by
  have h1 := isCanon_allCanonAtoms l h
  have h2 := isCanon_sortedInc l h
  have h3 := isCanon_antichain l h
  simp only [isCanon] at h
  rw [h1, h2, h3] at h
  cases h4 : decide
      (maxOfList (flattenMax l) = l) with
  | false =>
      rw [h4] at h
      exact Bool.noConfusion h
  | true => exact of_decide_eq_true h4

theorem isCanon_destruct (l : Level)
    (h : isCanon l = true) :
    allCanonAtoms (flattenMax l) = true ∧
    sortedInc (flattenMax l) = true ∧
    antichain (flattenMax l) = true ∧
    maxOfList (flattenMax l) = l :=
  ⟨isCanon_allCanonAtoms l h,
    isCanon_sortedInc l h,
    isCanon_antichain l h,
    isCanon_maxOfList l h⟩

theorem nf_maxOfList_canon :
    ∀ xs : List Level,
      allCanonAtoms xs = true →
      sortedInc xs = true →
      antichain xs = true →
        nf (maxOfList xs) = maxOfList xs
  | [], _, _, _ => rfl
  | x :: [], hatoms, _, _ =>
      nf_canonAtom x
        (allCanonAtoms_head x [] hatoms)
  | x :: y :: ys, hatoms, hsort, hanti => by
      have hx :=
        allCanonAtoms_head x (y :: ys) hatoms
      have htl :=
        allCanonAtoms_tail x (y :: ys) hatoms
      have hsort' :=
        sortedInc_tail x (y :: ys) hsort
      have hanti' :=
        antichain_tail x (y :: ys) hanti
      have ih :=
        nf_maxOfList_canon (y :: ys) htl
          hsort' hanti'
      change nf (.max x (maxOfList (y :: ys))) =
        .max x (maxOfList (y :: ys))
      simp only [nf]
      rw [nf_canonAtom x hx]
      rw [ih]
      rw [flattenMax_canonAtom x hx]
      have hat :=
        allCanonAtoms_allAtoms (y :: ys) htl
      rw [flattenMax_maxOfList_atoms (y :: ys) hat]
      simp only [maxFromList]
      have hid :=
        foldlIns_sorted_antichain_id
          (x :: y :: ys) hsort hanti
      change maxOfList
          (foldlIns [] ([x] ++ (y :: ys))) =
        .max x (maxOfList (y :: ys))
      have happ : [x] ++ (y :: ys) =
          x :: y :: ys := rfl
      rw [happ, hid]
      rfl

/-- DT-026 canonicity: a canon level is a fixed
point of `nf`. Induction on the canon list. -/
theorem nf_of_isCanon (l : Level)
    (h : IsCanon l) : nf l = l := by
  have ⟨hatoms, hsort, hanti, hmax⟩ :=
    isCanon_destruct l h
  have hnf :=
    nf_maxOfList_canon (flattenMax l)
      hatoms hsort hanti
  rw [← hmax]
  exact hnf

theorem dropDominated_allCanonAtoms (u : Level) :
    ∀ xs : List Level,
      allCanonAtoms xs = true →
        allCanonAtoms (dropDominated u xs) = true
  | [], _ => rfl
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          exact dropDominated_allCanonAtoms u vs
            (allCanonAtoms_tail v vs h)
      | false =>
          simp only [dropDominated, hd]
          have hv := allCanonAtoms_head v vs h
          simp only [allCanonAtoms, hv]
          exact dropDominated_allCanonAtoms u vs
            (allCanonAtoms_tail v vs h)

theorem insertSub_allCanonAtoms (u : Level)
    (hu : isCanonAtom u = true) :
    ∀ xs : List Level,
      allCanonAtoms xs = true →
        allCanonAtoms (insertSub u xs) = true
  | [], _ => by
      simp only [insertSub, allCanonAtoms, hu]
  | v :: vs, h => by
      cases ha : anyDominates u (v :: vs) with
      | true =>
          simp only [insertSub, ha]
          exact h
      | false =>
          cases hd : dominates u v with
          | true =>
              simp only [insertSub, ha, hd]
              exact insertSub_allCanonAtoms u hu vs
                (allCanonAtoms_tail v vs h)
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  simp only [allCanonAtoms, hu]
                  exact
                    dropDominated_allCanonAtoms
                      u (v :: vs) h
              | false =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  have hv :=
                    allCanonAtoms_head v vs h
                  simp only [allCanonAtoms, hv]
                  exact insertSub_allCanonAtoms
                    u hu vs
                    (allCanonAtoms_tail v vs h)

theorem foldlIns_allCanonAtoms :
    ∀ acc xs : List Level,
      allCanonAtoms acc = true →
      allCanonAtoms xs = true →
        allCanonAtoms (foldlIns acc xs) = true
  | acc, [], hacc, _ => hacc
  | acc, x :: xs, hacc, hxs => by
      simp only [foldlIns]
      have hx := allCanonAtoms_head x xs hxs
      have htl := allCanonAtoms_tail x xs hxs
      have hacc' :=
        insertSub_allCanonAtoms x hx acc hacc
      exact foldlIns_allCanonAtoms
        (insertSub x acc) xs hacc' htl

theorem isCanon_maxOfList_of (xs : List Level)
    (hatoms : allCanonAtoms xs = true)
    (hsort : sortedInc xs = true)
    (hanti : antichain xs = true) :
    isCanon (maxOfList xs) = true := by
  have hall := allCanonAtoms_allAtoms xs hatoms
  have hflat :=
    flattenMax_maxOfList_atoms xs hall
  simp only [isCanon]
  rw [hflat, hatoms, hsort, hanti]
  rw [decide_eq_true (Eq.refl (maxOfList xs))]

def memLevel (u : Level) : List Level → Bool
  | [] => false
  | v :: vs =>
      match decide (u = v) with
      | true => true
      | false => memLevel u vs

theorem memLevel_cons_self (u : Level)
    (xs : List Level) :
    memLevel u (u :: xs) = true := by
  cases heq : decide (u = u) with
  | false =>
      exact False.elim
        (of_decide_eq_false heq (Eq.refl u))
  | true =>
      simp only [memLevel, heq]
      rfl

theorem sortedInc_cons_adj (x y : Level)
    (ys : List Level)
    (h : sortedInc (x :: y :: ys) = true) :
    adjOk x y = true := by
  cases ha : adjOk x y with
  | false =>
      simp only [sortedInc, ha] at h
      exact Bool.noConfusion h
  | true => rfl

theorem sortedInc_mem_lt (x : Level) :
    ∀ xs : List Level,
      sortedInc (x :: xs) = true →
      ∀ y : Level,
        memLevel y xs = true →
          levelLt x y = true
  | [], _, y, hm => Bool.noConfusion hm
  | z :: zs, h, y, hm => by
      have hadj :=
        sortedInc_cons_adj x z zs h
      have hxz := adjOk_lt x z hadj
      have htl := sortedInc_tail x (z :: zs) h
      cases heq : decide (y = z) with
      | true =>
          have hyz : y = z :=
            of_decide_eq_true heq
          rw [hyz]
          exact hxz
      | false =>
          simp only [memLevel, heq] at hm
          have hzl :=
            sortedInc_mem_lt z zs htl y hm
          exact levelLt_trans x z y hxz hzl

theorem anyDominates_drop_false (x u : Level) :
    ∀ xs : List Level,
      anyDominates x xs = false →
        anyDominates x (dropDominated u xs) =
          false
  | [], h => h
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          simp only [anyDominates] at h
          cases hd2 : dominates v x with
          | true =>
              simp only [hd2] at h
              exact Bool.noConfusion h
          | false =>
              rw [hd2] at h
              exact anyDominates_drop_false
                x u vs h
      | false =>
          simp only [dropDominated, hd]
          simp only [anyDominates] at h
          cases hd2 : dominates v x with
          | true =>
              simp only [hd2] at h
              exact Bool.noConfusion h
          | false =>
              simp only [anyDominates, hd2]
              rw [hd2] at h
              exact anyDominates_drop_false
                x u vs h

theorem noneDominatedBy_drop (x u : Level) :
    ∀ xs : List Level,
      noneDominatedBy x xs = true →
        noneDominatedBy x
          (dropDominated u xs) = true
  | [], h => h
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          simp only [noneDominatedBy] at h
          cases hd2 : dominates x v with
          | true =>
              simp only [hd2] at h
              exact Bool.noConfusion h
          | false =>
              rw [hd2] at h
              exact noneDominatedBy_drop x u vs h
      | false =>
          simp only [dropDominated, hd]
          simp only [noneDominatedBy] at h
          cases hd2 : dominates x v with
          | true =>
              simp only [hd2] at h
              exact Bool.noConfusion h
          | false =>
              simp only [noneDominatedBy, hd2]
              rw [hd2] at h
              exact noneDominatedBy_drop x u vs h

theorem noneDominatedBy_drop_self (u : Level) :
    ∀ xs : List Level,
      noneDominatedBy u (dropDominated u xs) =
        true
  | [] => rfl
  | v :: vs => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          exact noneDominatedBy_drop_self u vs
      | false =>
          simp only [dropDominated, hd]
          simp only [noneDominatedBy, hd]
          exact noneDominatedBy_drop_self u vs

theorem dropDominated_antichain (u : Level) :
    ∀ xs : List Level,
      antichain xs = true →
        antichain (dropDominated u xs) = true
  | [], _ => rfl
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          exact dropDominated_antichain u vs
            (antichain_tail v vs h)
      | false =>
          simp only [dropDominated, hd]
          cases ha : anyDominates v vs with
          | true =>
              simp only [antichain, ha] at h
              exact Bool.noConfusion h
          | false =>
              cases hn : noneDominatedBy v vs with
              | false =>
                  simp only [antichain, ha, hn]
                    at h
                  exact Bool.noConfusion h
              | true =>
                  simp only [antichain, ha, hn]
                    at h
                  have ha' :=
                    anyDominates_drop_false
                      v u vs ha
                  have hn' :=
                    noneDominatedBy_drop v u vs hn
                  simp only [antichain, ha', hn']
                  exact dropDominated_antichain
                    u vs h

theorem dropDominated_head_mem (u w : Level) :
    ∀ xs ws : List Level,
      dropDominated u xs = w :: ws →
        memLevel w xs = true
  | [], _, h => nomatch h
  | v :: vs, ws, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd] at h
          have ih :=
            dropDominated_head_mem u w vs ws h
          simp only [memLevel]
          cases heq : decide (w = v) with
          | true => rfl
          | false => exact ih
      | false =>
          simp only [dropDominated, hd] at h
          injection h with hv _
          rw [← hv]
          exact memLevel_cons_self v vs

theorem antichain_noneDom (x : Level)
    (xs : List Level)
    (h : antichain (x :: xs) = true) :
    noneDominatedBy x xs = true := by
  cases ha : anyDominates x xs with
  | true =>
      simp only [antichain, ha] at h
      exact Bool.noConfusion h
  | false =>
      cases hn : noneDominatedBy x xs with
      | false =>
          simp only [antichain, ha, hn] at h
          exact Bool.noConfusion h
      | true => rfl

theorem antichain_anyDom_false (x : Level)
    (xs : List Level)
    (h : antichain (x :: xs) = true) :
    anyDominates x xs = false := by
  cases ha : anyDominates x xs with
  | true =>
      simp only [antichain, ha] at h
      exact Bool.noConfusion h
  | false => rfl

theorem noneDominatedBy_mem (x y : Level) :
    ∀ xs : List Level,
      noneDominatedBy x xs = true →
      memLevel y xs = true →
        dominates x y = false
  | [], _, hm => Bool.noConfusion hm
  | v :: vs, h, hm => by
      cases heq : decide (y = v) with
      | true =>
          have hyv : y = v :=
            of_decide_eq_true heq
          rw [hyv]
          simp only [noneDominatedBy] at h
          cases hd : dominates x v with
          | true =>
              simp only [hd] at h
              exact Bool.noConfusion h
          | false => rfl
      | false =>
          simp only [memLevel, heq] at hm
          simp only [noneDominatedBy] at h
          cases hd : dominates x v with
          | true =>
              simp only [hd] at h
              exact Bool.noConfusion h
          | false =>
              rw [hd] at h
              exact noneDominatedBy_mem x y vs h hm

theorem anyDominates_mem (x y : Level) :
    ∀ xs : List Level,
      memLevel y xs = true →
      dominates y x = true →
        anyDominates x xs = true
  | [], hm, _ => Bool.noConfusion hm
  | v :: vs, hm, hd => by
      cases heq : decide (y = v) with
      | true =>
          have hyv : y = v :=
            of_decide_eq_true heq
          rw [hyv] at hd
          simp only [anyDominates, hd]
      | false =>
          simp only [memLevel, heq] at hm
          simp only [anyDominates]
          cases hd2 : dominates v x with
          | true => rfl
          | false =>
              exact anyDominates_mem x y vs hm hd

theorem adjOk_of_sorted_antichain (v w : Level)
    (vs : List Level)
    (hsort : sortedInc (v :: vs) = true)
    (hanti : antichain (v :: vs) = true)
    (hw : memLevel w vs = true) :
    adjOk v w = true := by
  have hlt := sortedInc_mem_lt v vs hsort w hw
  have hn := antichain_noneDom v vs hanti
  have hnd := noneDominatedBy_mem v w vs hn hw
  have ha := antichain_anyDom_false v vs hanti
  cases hd : dominates w v with
  | true =>
      have hany :=
        anyDominates_mem v w vs hw hd
      rw [hany] at ha
      exact Bool.noConfusion ha
  | false =>
      simp only [adjOk, hnd, hd, hlt]

theorem dropDominated_sortedInc (u : Level) :
    ∀ xs : List Level,
      sortedInc xs = true →
      antichain xs = true →
        sortedInc (dropDominated u xs) = true
  | [], _, _ => rfl
  | v :: vs, hsort, hanti => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          exact dropDominated_sortedInc u vs
            (sortedInc_tail v vs hsort)
            (antichain_tail v vs hanti)
      | false =>
          simp only [dropDominated, hd]
          cases hdrop : dropDominated u vs with
          | nil => rfl
          | cons w ws =>
              have hsort' :=
                dropDominated_sortedInc u vs
                  (sortedInc_tail v vs hsort)
                  (antichain_tail v vs hanti)
              rw [hdrop] at hsort'
              have hw :=
                dropDominated_head_mem u w vs ws
                  hdrop
              have hadj :=
                adjOk_of_sorted_antichain v w vs
                  hsort hanti hw
              simp only [sortedInc, hadj]
              exact hsort'

theorem dropDominated_mem_all (u z : Level) :
    ∀ xs : List Level,
      memLevel z (dropDominated u xs) = true →
        memLevel z xs = true
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd] at h
          have ih :=
            dropDominated_mem_all u z vs h
          simp only [memLevel]
          cases heq : decide (z = v) with
          | true => rfl
          | false => exact ih
      | false =>
          simp only [dropDominated, hd] at h
          simp only [memLevel] at h ⊢
          cases heq : decide (z = v) with
          | true => rfl
          | false =>
              rw [heq] at h
              exact dropDominated_mem_all u z vs h

theorem insertSub_mem (u z : Level) :
    ∀ xs : List Level,
      memLevel z (insertSub u xs) = true →
        decide (z = u) = true ∨
          memLevel z xs = true
  | [], h => by
      simp only [insertSub, memLevel] at h
      cases heq : decide (z = u) with
      | true => exact Or.inl rfl
      | false =>
          simp only [heq] at h
          exact Bool.noConfusion h
  | v :: vs, h => by
      cases ha : anyDominates u (v :: vs) with
      | true =>
          simp only [insertSub, ha] at h
          exact Or.inr h
      | false =>
          cases hd : dominates u v with
          | true =>
              simp only [insertSub, ha, hd] at h
              have ih := insertSub_mem u z vs h
              cases ih with
              | inl hu => exact Or.inl hu
              | inr hvs =>
                  exact Or.inr (by
                    simp only [memLevel]
                    cases heq : decide (z = v) with
                    | true => rfl
                    | false => exact hvs)
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, hd,
                    hlt] at h
                  simp only [memLevel] at h
                  cases heq : decide (z = u) with
                  | true => exact Or.inl rfl
                  | false =>
                      rw [heq] at h
                      exact Or.inr
                        (dropDominated_mem_all
                          u z (v :: vs) h)
              | false =>
                  simp only [insertSub, ha, hd,
                    hlt] at h
                  simp only [memLevel] at h
                  cases heq : decide (z = v) with
                  | true =>
                      exact Or.inr (by
                        simp only [memLevel, heq])
                  | false =>
                      rw [heq] at h
                      have ih :=
                        insertSub_mem u z vs h
                      cases ih with
                      | inl hu => exact Or.inl hu
                      | inr hvs =>
                          exact Or.inr (by
                            simp only [memLevel,
                              heq]
                            exact hvs)

theorem anyDominates_exists (x : Level) :
    ∀ xs : List Level,
      anyDominates x xs = true →
        ∃ z, memLevel z xs = true ∧
          dominates z x = true
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      cases hd : dominates v x with
      | true =>
          exact ⟨v, memLevel_cons_self v vs, hd⟩
      | false =>
          simp only [anyDominates, hd] at h
          have ⟨z, hm, hdz⟩ :=
            anyDominates_exists x vs h
          refine ⟨z, ?_, hdz⟩
          simp only [memLevel]
          cases heq : decide (z = v) with
          | true => rfl
          | false => exact hm

theorem noneDominatedBy_false_exists (x : Level) :
    ∀ xs : List Level,
      noneDominatedBy x xs = false →
        ∃ z, memLevel z xs = true ∧
          dominates x z = true
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      cases hd : dominates x v with
      | true =>
          exact ⟨v, memLevel_cons_self v vs, hd⟩
      | false =>
          simp only [noneDominatedBy, hd] at h
          have ⟨z, hm, hdz⟩ :=
            noneDominatedBy_false_exists x vs h
          refine ⟨z, ?_, hdz⟩
          simp only [memLevel]
          cases heq : decide (z = v) with
          | true => rfl
          | false => exact hm

theorem insertSub_antichain (u : Level) :
    ∀ xs : List Level,
      antichain xs = true →
      anyDominates u xs = false →
        antichain (insertSub u xs) = true
  | [], _, _ => rfl
  | v :: vs, hanti, hany => by
      cases ha : anyDominates u (v :: vs) with
      | true =>
          rw [ha] at hany
          exact Bool.noConfusion hany
      | false =>
          cases hd : dominates u v with
          | true =>
              simp only [insertSub, ha, hd]
              exact insertSub_antichain u vs
                (antichain_tail v vs hanti)
                (anyDominates_false_suffix u [v] vs
                  hany)
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  have hdrop :=
                    dropDominated_antichain u
                      (v :: vs) hanti
                  have hanyd :=
                    anyDominates_drop_false u u
                      (v :: vs) ha
                  have hnd :=
                    noneDominatedBy_drop_self u
                      (v :: vs)
                  simp only [antichain, hanyd,
                    hnd]
                  exact hdrop
              | false =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  have ih :=
                    insertSub_antichain u vs
                      (antichain_tail v vs hanti)
                      (anyDominates_false_suffix
                        u [v] vs hany)
                  have hanyv :=
                    antichain_anyDom_false v vs
                      hanti
                  have hndv :=
                    antichain_noneDom v vs hanti
                  cases hany2 :
                      anyDominates v
                        (insertSub u vs) with
                  | true =>
                      have ⟨z, hm, hdz⟩ :=
                        anyDominates_exists v
                          (insertSub u vs) hany2
                      have hmem :=
                        insertSub_mem u z vs hm
                      cases hmem with
                      | inl hu =>
                          have hzu : z = u :=
                            of_decide_eq_true hu
                          rw [hzu] at hdz
                          rw [hdz] at hd
                          exact Bool.noConfusion hd
                      | inr hvs =>
                          have hany3 :=
                            anyDominates_mem v z
                              vs hvs hdz
                          rw [hany3] at hanyv
                          exact Bool.noConfusion
                            hanyv
                  | false =>
                      cases hnd2 :
                          noneDominatedBy v
                            (insertSub u vs) with
                      | false =>
                          have ⟨z, hm, hdz⟩ :=
                            noneDominatedBy_false_exists
                              v (insertSub u vs)
                              hnd2
                          have hmem :=
                            insertSub_mem u z vs hm
                          cases hmem with
                          | inl hu =>
                              have hzu : z = u :=
                                of_decide_eq_true hu
                              rw [hzu] at hdz
                              have hva :
                                  anyDominates u
                                    (v :: vs) =
                                  true := by
                                simp only
                                  [anyDominates,
                                    hdz]
                              rw [hva] at ha
                              exact Bool.noConfusion
                                ha
                          | inr hvs =>
                              have hnd3 :=
                                noneDominatedBy_mem
                                  v z vs hndv hvs
                              rw [hdz] at hnd3
                              exact Bool.noConfusion
                                hnd3
                      | true =>
                          simp only [antichain,
                            hany2, hnd2]
                          exact ih

theorem insertSub_antichain_of (u : Level)
    (xs : List Level)
    (h : antichain xs = true) :
    antichain (insertSub u xs) = true := by
  cases ha : anyDominates u xs with
  | true =>
      have hid := insertSub_of_anyDom u xs ha
      rw [hid]
      exact h
  | false =>
      exact insertSub_antichain u xs h ha

theorem insertSub_ne_nil (u : Level) :
    ∀ xs : List Level, insertSub u xs ≠ []
  | [] => by
      simp only [insertSub]
      intro h
      nomatch h
  | v :: vs => by
      cases ha : anyDominates u (v :: vs) with
      | true =>
          simp only [insertSub, ha]
          intro h
          nomatch h
      | false =>
          cases hd : dominates u v with
          | true =>
              simp only [insertSub, ha, hd]
              exact insertSub_ne_nil u vs
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  intro h
                  nomatch h
              | false =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  intro h
                  nomatch h

theorem adjOk_u_v_of_insert (u v : Level)
    (vs : List Level)
    (ha : anyDominates u (v :: vs) = false)
    (hd : dominates u v = false)
    (hlt : levelLt u v = true) :
    adjOk u v = true := by
  have hva : dominates v u = false := by
    simp only [anyDominates] at ha
    cases hd2 : dominates v u with
    | true =>
        simp only [hd2] at ha
        exact Bool.noConfusion ha
    | false => rfl
  simp only [adjOk, hd, hva, hlt]

/-! ## H-6g: trichotomy of `levelLt` (rung 1)

H-6f wall: `of_decide_eq_false hne` on
`decide (param i = param j)` vs `decide (i = j)`.
Route: `Nat.lt_trichotomy` on the param index and
constructor injectivity; never unfold `decide` at a
variable equality of `param`. -/

theorem decide_nat_lt_of (i j : Nat)
    (h : i < j) :
    decide (i < j) = true := by
  cases hd : decide (i < j) with
  | false =>
      exact False.elim
        (of_decide_eq_false hd h)
  | true => rfl

theorem levelLt_lex_total
    (x y u v : Level)
    (ihx : levelLt x u = false →
      x ≠ u → levelLt u x = true)
    (ihy : levelLt y v = false →
      y ≠ v → levelLt v y = true)
    (h : (if levelLt x u then true
          else if decide (x = u) then
            levelLt y v
          else false) = false)
    (hne : ¬ (x = u ∧ y = v)) :
    (if levelLt u x then true
     else if decide (u = x) then
       levelLt v y
     else false) = true := by
  cases hxu : levelLt x u with
  | true =>
      rw [hxu] at h
      rw [if_pos true_eq_true] at h
      exact Bool.noConfusion h
  | false =>
      rw [hxu] at h
      rw [if_neg false_ne_true] at h
      cases heq : decide (x = u) with
      | true =>
          have hxueq : x = u :=
            of_decide_eq_true heq
          rw [heq] at h
          rw [if_pos true_eq_true] at h
          have hyv : y ≠ v := by
            intro hy
            exact hne ⟨hxueq, hy⟩
          have hvy := ihy h hyv
          rw [hxueq]
          have hi := levelLt_irrefl u
          rw [hi]
          rw [if_neg false_ne_true]
          cases hd : decide (u = u) with
          | false =>
              exact False.elim
                (of_decide_eq_false hd
                  (Eq.refl u))
          | true =>
              rw [if_pos true_eq_true]
              exact hvy
      | false =>
          have hxune : x ≠ u :=
            of_decide_eq_false heq
          have hux := ihx hxu hxune
          rw [hux]
          rw [if_pos true_eq_true]

theorem levelLt_ne_total_any :
    ∀ u v : Level,
      levelLt u v = false →
      u ≠ v →
        levelLt v u = true
  | .zero, .zero, _, hne =>
      False.elim (hne rfl)
  | .zero, .param _, hlt, _ =>
      Bool.noConfusion hlt
  | .zero, .succ _, hlt, _ =>
      Bool.noConfusion hlt
  | .zero, .max _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .zero, .imax _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .param _, .zero, _, _ => rfl
  | .param i, .param j, hlt, hne => by
      have hij : i ≠ j :=
        fun heq =>
          hne (congrArg Level.param heq)
      change decide (i < j) = false at hlt
      cases Nat.lt_trichotomy i j with
      | inl hltij =>
          have ht :=
            decide_nat_lt_of i j hltij
          rw [ht] at hlt
          exact Bool.noConfusion hlt
      | inr hrest =>
          cases hrest with
          | inl heq =>
              exact False.elim (hij heq)
          | inr hgt =>
              change decide (j < i) = true
              exact decide_nat_lt_of j i hgt
  | .param _, .succ _, hlt, _ =>
      Bool.noConfusion hlt
  | .param _, .max _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .param _, .imax _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .succ _, .zero, _, _ => rfl
  | .succ _, .param _, _, _ => rfl
  | .succ x, .succ y, hlt, hne =>
      levelLt_ne_total_any x y hlt
        (fun heq =>
          hne (congrArg Level.succ heq))
  | .succ _, .max _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .succ _, .imax _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .max _ _, .zero, _, _ => rfl
  | .max _ _, .param _, _, _ => rfl
  | .max _ _, .succ _, _, _ => rfl
  | .max x y, .max u v, hlt, hne =>
      levelLt_lex_total x y u v
        (fun hxu hxune =>
          levelLt_ne_total_any x u hxu hxune)
        (fun hyv hyvne =>
          levelLt_ne_total_any y v hyv hyvne)
        hlt
        (fun hpair =>
          hne (by
            have hx := hpair.left
            have hy := hpair.right
            rw [hx, hy]))
  | .max _ _, .imax _ _, hlt, _ =>
      Bool.noConfusion hlt
  | .imax _ _, .zero, _, _ => rfl
  | .imax _ _, .param _, _, _ => rfl
  | .imax _ _, .succ _, _, _ => rfl
  | .imax _ _, .max _ _, _, _ => rfl
  | .imax x y, .imax u v, hlt, hne =>
      levelLt_lex_total x y u v
        (fun hxu hxune =>
          levelLt_ne_total_any x u hxu hxune)
        (fun hyv hyvne =>
          levelLt_ne_total_any y v hyv hyvne)
        hlt
        (fun hpair =>
          hne (by
            have hx := hpair.left
            have hy := hpair.right
            rw [hx, hy]))

/-- Annex 23 H-6g (1): trichotomy of `levelLt`
on canon atoms. Starts from H-6f's wall. -/
theorem levelLt_ne_total (u v : Level)
    (_hu : isCanonAtom u = true)
    (_hv : isCanonAtom v = true)
    (hlt : levelLt u v = false)
    (hne : u ≠ v) :
    levelLt v u = true :=
  levelLt_ne_total_any u v hlt hne

/-! ## H-6g rung 2: `insertSub` keeps `sortedInc`;
`isCanon_nf`; `nf_idem`. -/

theorem dropDominated_not_dom (u z : Level) :
    ∀ xs : List Level,
      memLevel z (dropDominated u xs) = true →
        dominates u z = false
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd] at h
          exact dropDominated_not_dom u z vs h
      | false =>
          simp only [dropDominated, hd] at h
          simp only [memLevel] at h
          cases heq : decide (z = v) with
          | true =>
              have hzv : z = v :=
                of_decide_eq_true heq
              rw [hzv]
              exact hd
          | false =>
              rw [heq] at h
              exact dropDominated_not_dom
                u z vs h

theorem insertSub_sortedInc (u : Level) :
    ∀ xs : List Level,
      sortedInc xs = true →
      antichain xs = true →
      anyDominates u xs = false →
        sortedInc (insertSub u xs) = true
  | [], _, _, _ => rfl
  | v :: vs, hsort, hanti, hany => by
      cases ha : anyDominates u (v :: vs) with
      | true =>
          rw [ha] at hany
          exact Bool.noConfusion hany
      | false =>
          cases hd : dominates u v with
          | true =>
              simp only [insertSub, ha, hd]
              exact insertSub_sortedInc u vs
                (sortedInc_tail v vs hsort)
                (antichain_tail v vs hanti)
                (anyDominates_false_suffix
                  u [v] vs hany)
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  cases hdrop :
                      dropDominated u
                        (v :: vs) with
                  | nil => rfl
                  | cons w ws =>
                      have hsortD :=
                        dropDominated_sortedInc
                          u (v :: vs)
                          hsort hanti
                      rw [hdrop] at hsortD
                      have hw :=
                        dropDominated_head_mem
                          u w (v :: vs) ws
                          hdrop
                      have hnd :=
                        dropDominated_not_dom
                          u w (v :: vs)
                          (by
                            rw [hdrop]
                            exact
                              memLevel_cons_self
                                w ws)
                      have hwu :
                          dominates w u =
                            false := by
                        cases hd2 :
                            dominates w u with
                        | true =>
                            have hany2 :=
                              anyDominates_mem
                                u w (v :: vs)
                                hw hd2
                            rw [hany2] at ha
                            exact
                              Bool.noConfusion
                                ha
                        | false => rfl
                      have hltuw :
                          levelLt u w =
                            true := by
                        cases heq :
                            decide (w = v) with
                        | true =>
                            have hwv : w = v :=
                              of_decide_eq_true
                                heq
                            rw [hwv]
                            exact hlt
                        | false =>
                            simp only
                              [memLevel, heq]
                              at hw
                            have hvw :=
                              sortedInc_mem_lt
                                v vs hsort w hw
                            exact
                              levelLt_trans
                                u v w hlt hvw
                      have hadj :
                          adjOk u w = true := by
                        simp only [adjOk, hnd,
                          hwu, hltuw]
                      simp only [sortedInc,
                        hadj]
                      exact hsortD
              | false =>
                  simp only [insertSub, ha, hd,
                    hlt]
                  have hne : u ≠ v := by
                    intro heq
                    rw [heq] at hd
                    have hr :=
                      dominates_refl v
                    rw [hr] at hd
                    exact Bool.noConfusion hd
                  have hvu :=
                    levelLt_ne_total_any
                      u v hlt hne
                  have hva :
                      dominates v u =
                        false := by
                    simp only [anyDominates]
                      at ha
                    cases hd2 :
                        dominates v u with
                    | true =>
                        simp only [hd2] at ha
                        exact Bool.noConfusion
                          ha
                    | false => rfl
                  have ih :=
                    insertSub_sortedInc u vs
                      (sortedInc_tail v vs
                        hsort)
                      (antichain_tail v vs
                        hanti)
                      (anyDominates_false_suffix
                        u [v] vs hany)
                  have hnn :=
                    insertSub_ne_nil u vs
                  cases hins :
                      insertSub u vs with
                  | nil =>
                      exact False.elim
                        (hnn hins)
                  | cons w ws =>
                      rw [hins] at ih
                      have hm :=
                        insertSub_mem u w vs
                          (by
                            rw [hins]
                            exact
                              memLevel_cons_self
                                w ws)
                      have hadj :
                          adjOk v w = true := by
                        cases hm with
                        | inl hu =>
                            have hwu : w = u :=
                              of_decide_eq_true
                                hu
                            rw [hwu]
                            simp only [adjOk,
                              hva, hd, hvu]
                        | inr hvs =>
                            exact
                              adjOk_of_sorted_antichain
                                v w vs hsort
                                hanti hvs
                      simp only [sortedInc,
                        hadj]
                      exact ih

theorem insertSub_sortedInc_of (u : Level)
    (xs : List Level)
    (hs : sortedInc xs = true)
    (ha : antichain xs = true) :
    sortedInc (insertSub u xs) = true := by
  cases hany : anyDominates u xs with
  | true =>
      have hid :=
        insertSub_of_anyDom u xs hany
      rw [hid]
      exact hs
  | false =>
      exact insertSub_sortedInc u xs hs ha hany

theorem foldlIns_sortedInc :
    ∀ acc xs : List Level,
      sortedInc acc = true →
      antichain acc = true →
        sortedInc (foldlIns acc xs) = true
  | acc, [], hsort, _ => hsort
  | acc, x :: xs, hsort, hanti => by
      simp only [foldlIns]
      exact foldlIns_sortedInc
        (insertSub x acc) xs
        (insertSub_sortedInc_of x acc
          hsort hanti)
        (insertSub_antichain_of x acc hanti)

theorem foldlIns_antichain :
    ∀ acc xs : List Level,
      antichain acc = true →
        antichain (foldlIns acc xs) = true
  | acc, [], h => h
  | acc, x :: xs, h => by
      simp only [foldlIns]
      exact foldlIns_antichain
        (insertSub x acc) xs
        (insertSub_antichain_of x acc h)

theorem allCanonAtoms_append :
    ∀ xs ys : List Level,
      allCanonAtoms xs = true →
      allCanonAtoms ys = true →
        allCanonAtoms (xs ++ ys) = true
  | [], _, _, hys => hys
  | x :: xs, ys, hxs, hys => by
      have hx :=
        allCanonAtoms_head x xs hxs
      have htl :=
        allCanonAtoms_tail x xs hxs
      simp only [List.cons_append,
        allCanonAtoms, hx]
      exact allCanonAtoms_append
        xs ys htl hys

theorem isCanon_maxFromList (xs : List Level)
    (h : allCanonAtoms xs = true) :
    isCanon (maxFromList xs) = true :=
  isCanon_maxOfList_of (foldlIns [] xs)
    (foldlIns_allCanonAtoms [] xs rfl h)
    (foldlIns_sortedInc [] xs rfl rfl)
    (foldlIns_antichain [] xs rfl)

theorem isCanonAtom_succ (x : Level)
    (h : isCanonAtom x = true) :
    isCanonAtom (.succ x) = true := by
  cases x with
  | zero => exact Bool.noConfusion h
  | max _ _ => exact Bool.noConfusion h
  | param _ => rfl
  | succ _ => exact h
  | imax _ _ => exact h

theorem mapSucc_allCanonAtoms :
    ∀ xs : List Level,
      allCanonAtoms xs = true →
        allCanonAtoms (mapSucc xs) = true
  | [], _ => rfl
  | x :: xs, h => by
      have hx :=
        allCanonAtoms_head x xs h
      have htl :=
        allCanonAtoms_tail x xs h
      have hx' := isCanonAtom_succ x hx
      simp only [mapSucc, allCanonAtoms, hx']
      exact mapSucc_allCanonAtoms xs htl

theorem decide_succ_le (n m : Nat) :
    decide (n + 1 ≤ m + 1) =
      decide (n ≤ m) := by
  cases h : decide (n ≤ m) with
  | true =>
      have hle : n ≤ m :=
        of_decide_eq_true h
      have hle' : n + 1 ≤ m + 1 :=
        Nat.succ_le_succ hle
      cases h2 : decide (n + 1 ≤ m + 1) with
      | false =>
          exact False.elim
            (of_decide_eq_false h2 hle')
      | true => rfl
  | false =>
      have hn : ¬ (n ≤ m) :=
        of_decide_eq_false h
      have hn' : ¬ (n + 1 ≤ m + 1) :=
        fun hle =>
          hn (Nat.le_of_succ_le_succ hle)
      cases h2 : decide (n + 1 ≤ m + 1) with
      | true =>
          exact False.elim
            (hn' (of_decide_eq_true h2))
      | false => rfl

theorem dominates_succ (x y : Level) :
    dominates (.succ x) (.succ y) =
      dominates x y := by
  cases hx : peelOff x with
  | mk nu bu =>
      cases hy : peelOff y with
      | mk nv bv =>
          have hxs :
              peelOff (.succ x) =
                (nu + 1, bu) := by
            simp only [peelOff, hx]
          have hys :
              peelOff (.succ y) =
                (nv + 1, bv) := by
            simp only [peelOff, hy]
          simp only [dominates, hxs, hys,
            hx, hy]
          rw [decide_succ_le nv nu]

theorem adjOk_succ (x y : Level) :
    adjOk (.succ x) (.succ y) = adjOk x y := by
  simp only [adjOk]
  rw [dominates_succ, dominates_succ]
  rfl

theorem mapSucc_sortedInc :
    ∀ xs : List Level,
      sortedInc xs = true →
        sortedInc (mapSucc xs) = true
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: ys, h => by
      have hadj :=
        sortedInc_cons_adj x y ys h
      have htl :=
        sortedInc_tail x (y :: ys) h
      have ih :=
        mapSucc_sortedInc (y :: ys) htl
      have hadj' :
          adjOk (.succ x) (.succ y) = true := by
        rw [adjOk_succ]
        exact hadj
      simp only [mapSucc, sortedInc, hadj']
      exact ih

theorem anyDominates_succ (u : Level) :
    ∀ xs : List Level,
      anyDominates (.succ u) (mapSucc xs) =
        anyDominates u xs
  | [] => rfl
  | x :: xs => by
      simp only [anyDominates, mapSucc]
      rw [dominates_succ]
      cases dominates x u with
      | true => rfl
      | false =>
          exact anyDominates_succ u xs

theorem noneDominatedBy_succ (u : Level) :
    ∀ xs : List Level,
      noneDominatedBy (.succ u) (mapSucc xs) =
        noneDominatedBy u xs
  | [] => rfl
  | x :: xs => by
      simp only [noneDominatedBy, mapSucc]
      rw [dominates_succ]
      cases dominates u x with
      | true => rfl
      | false =>
          exact noneDominatedBy_succ u xs

theorem mapSucc_antichain :
    ∀ xs : List Level,
      antichain xs = true →
        antichain (mapSucc xs) = true
  | [], _ => rfl
  | x :: xs, h => by
      have ha :=
        antichain_anyDom_false x xs h
      have hn := antichain_noneDom x xs h
      have htl := antichain_tail x xs h
      have ih := mapSucc_antichain xs htl
      simp only [antichain, mapSucc]
      rw [anyDominates_succ, noneDominatedBy_succ]
      simp only [ha, hn]
      exact ih

theorem succCanon_atom (x : Level)
    (h : isCanonAtom x = true) :
    succCanon x = .succ x := by
  cases x with
  | zero => exact Bool.noConfusion h
  | max _ _ => exact Bool.noConfusion h
  | param _ => rfl
  | succ _ => rfl
  | imax _ _ => rfl

theorem succCanon_maxOfList :
    ∀ xs : List Level,
      xs ≠ [] →
      allCanonAtoms xs = true →
        succCanon (maxOfList xs) =
          maxOfList (mapSucc xs)
  | [], h, _ => False.elim (h rfl)
  | x :: [], _, hatoms => by
      have hx :=
        allCanonAtoms_head x [] hatoms
      simp only [maxOfList, mapSucc]
      exact succCanon_atom x hx
  | x :: y :: ys, _, hatoms => by
      have hx :=
        allCanonAtoms_head x (y :: ys) hatoms
      have htl :=
        allCanonAtoms_tail x (y :: ys) hatoms
      have ih :=
        succCanon_maxOfList (y :: ys)
          (fun hh => nomatch hh) htl
      have hxsc := succCanon_atom x hx
      change
        succCanon
          (.max x (maxOfList (y :: ys))) =
        maxOfList
          (.succ x :: mapSucc (y :: ys))
      simp only [succCanon]
      rw [hxsc, ih]
      rfl

theorem isCanon_succCanon (l : Level)
    (h : isCanon l = true) :
    isCanon (succCanon l) = true := by
  have ⟨hatoms, hsort, hanti, hmax⟩ :=
    isCanon_destruct l h
  cases hxs : flattenMax l with
  | nil =>
      have hl0 : l = .zero := by
        rw [← hmax, hxs]
        rfl
      rw [hl0]
      exact isCanon_of_atom
        (.succ .zero) rfl
  | cons x xs =>
      rw [← hmax, hxs]
      rw [hxs] at hatoms hsort hanti
      have heq :=
        succCanon_maxOfList (x :: xs)
          (fun hh => nomatch hh) hatoms
      rw [heq]
      exact isCanon_maxOfList_of
        (mapSucc (x :: xs))
        (mapSucc_allCanonAtoms
          (x :: xs) hatoms)
        (mapSucc_sortedInc
          (x :: xs) hsort)
        (mapSucc_antichain
          (x :: xs) hanti)

theorem flattenMax_maxJoin (a b : Level)
    (ha : isCanonAtom a = true)
    (hb : isCanonAtom b = true) :
    allCanonAtoms (flattenMax (maxJoin a b)) =
      true := by
  simp only [maxJoin]
  cases heq : decide (a = b) with
  | true =>
      have hflat :=
        flattenMax_canonAtom a ha
      rw [hflat]
      simp only [allCanonAtoms, ha]
  | false =>
      cases hza : levelIsZero a with
      | true =>
          have hflat :=
            flattenMax_canonAtom b hb
          rw [hflat]
          simp only [allCanonAtoms, hb]
      | false =>
          cases hzb : levelIsZero b with
          | true =>
              have hflat :=
                flattenMax_canonAtom a ha
              rw [hflat]
              simp only [allCanonAtoms, ha]
          | false =>
              have ha' :=
                flattenMax_canonAtom a ha
              have hb' :=
                flattenMax_canonAtom b hb
              simp only [flattenMax, ha', hb']
              simp only [allCanonAtoms, ha, hb]

/- H-6h repair (A): nested `imax (imax x y) b`
with `y ≠ b` is a canon atom (02 §2 has no
identity that rewrites it; measured by the
#eval guards). `flattenMax_imaxJoin` spent
two attempts (H-6g) and is NOT re-attempted.
`imaxJoin_canonAtoms` is the NEW statement
for the accepted shape. -/

theorem allCanonAtoms_singleton (x : Level)
    (h : isCanonAtom x = true) :
    allCanonAtoms [x] = true := by
  simp only [allCanonAtoms, h]

theorem isCanonAtom_imax_eq (a b : Level) :
    isCanonAtom (.imax a b) =
      match isCanonAtom a, isCanonAtom b with
      | true, true =>
          match levelIsZero a, levelIsZero b,
                decide (a = b),
                levelNeverZero b with
          | false, false, false, false =>
              match a with
              | .imax _ y =>
                  match decide (y = b) with
                  | false => true
                  | true => false
              | .max _ _ => false
              | _ => true
          | _, _, _, _ => false
      | _, _ => false :=
  rfl

theorem isCanonAtom_imax_param
    (i : Nat) (b : Level)
    (hb : isCanonAtom b = true)
    (hzb : levelIsZero b = false)
    (hne : decide (.param i = b) = false)
    (hnv : levelNeverZero b = false) :
    isCanonAtom (.imax (.param i) b) =
      true := by
  rw [isCanonAtom_imax_eq]
  have ha : isCanonAtom (.param i) = true :=
    rfl
  have hza : levelIsZero (.param i) = false :=
    rfl
  rw [ha, hb, hza, hzb, hne, hnv]

theorem isCanonAtom_imax_succ
    (l b : Level)
    (ha : isCanonAtom (.succ l) = true)
    (hb : isCanonAtom b = true)
    (hzb : levelIsZero b = false)
    (hne : decide (.succ l = b) = false)
    (hnv : levelNeverZero b = false) :
    isCanonAtom (.imax (.succ l) b) = true := by
  rw [isCanonAtom_imax_eq]
  have hza : levelIsZero (.succ l) = false :=
    rfl
  rw [ha, hb, hza, hzb, hne, hnv]

theorem isCanonAtom_imax_nested
    (x y b : Level)
    (ha : isCanonAtom (.imax x y) = true)
    (hb : isCanonAtom b = true)
    (hza : levelIsZero (.imax x y) = false)
    (hzb : levelIsZero b = false)
    (hne : decide (.imax x y = b) = false)
    (hnv : levelNeverZero b = false)
    (hy : decide (y = b) = false) :
    isCanonAtom
      (.imax (.imax x y) b) = true := by
  change (match
      isCanonAtom (.imax x y),
      isCanonAtom b with
    | true, true =>
      match
        levelIsZero (.imax x y),
        levelIsZero b,
        decide (.imax x y = b),
        levelNeverZero b with
      | false, false, false, false =>
        match decide (y = b) with
        | false => true
        | true => false
      | _, _, _, _ => false
    | _, _ => false) = true
  rw [ha, hb, hza, hzb, hne, hnv, hy]

theorem imaxJoin_imax_eq
    (x y b : Level)
    (heq : decide (.imax x y = b) = false)
    (hbz : levelIsZero b = false)
    (haz : levelIsZero (.imax x y) = false)
    (hnv : levelNeverZero b = false) :
    imaxJoin (.imax x y) b =
      match decide (y = b) with
      | true =>
          match decide (x = b),
                levelIsZero x with
          | true, _ => b
          | false, true => b
          | false, false => .imax x b
      | false =>
          .imax (.imax x y) b := by
  unfold imaxJoin
  rw [heq, hbz, haz, hnv]

/-- NEW statement (repair (A)). The walled
`flattenMax_imaxJoin` is not this name. -/
theorem imaxJoin_canonAtoms (a b : Level)
    (ha : isCanonAtom a = true)
    (hb : isCanonAtom b = true) :
    allCanonAtoms
      (flattenMax (imaxJoin a b)) = true := by
  cases heq : decide (a = b) with
  | true =>
      unfold imaxJoin
      rw [heq]
      simp only []
      have hflat :=
        flattenMax_canonAtom b hb
      rw [hflat]
      exact allCanonAtoms_singleton b hb
  | false =>
      cases hbz : levelIsZero b with
      | true =>
          unfold imaxJoin
          rw [heq, hbz]
          simp only []
          simp only [flattenMax,
            allCanonAtoms]
      | false =>
          cases haz : levelIsZero a with
          | true =>
              unfold imaxJoin
              rw [heq, hbz, haz]
              simp only []
              have hflat :=
                flattenMax_canonAtom b hb
              rw [hflat]
              exact
                allCanonAtoms_singleton
                  b hb
          | false =>
              cases hnv :
                  levelNeverZero b with
              | true =>
                  unfold imaxJoin
                  rw [heq, hbz, haz, hnv]
                  simp only []
                  exact flattenMax_maxJoin
                    a b ha hb
              | false =>
                  cases a with
                  | zero =>
                      exact
                        Bool.noConfusion ha
                  | max _ _ =>
                      exact
                        Bool.noConfusion ha
                  | param i =>
                      unfold imaxJoin
                      rw [heq, hbz, haz, hnv]
                      simp only []
                      have hat :=
                        isCanonAtom_imax_param
                          i b hb hbz heq hnv
                      have hflat :=
                        flattenMax_canonAtom
                          (.imax (.param i) b)
                          hat
                      rw [hflat]
                      exact
                        allCanonAtoms_singleton
                          (.imax (.param i) b)
                          hat
                  | succ l =>
                      unfold imaxJoin
                      rw [heq, hbz, haz, hnv]
                      simp only []
                      have hat :=
                        isCanonAtom_imax_succ
                          l b ha hb hbz heq
                          hnv
                      have hflat :=
                        flattenMax_canonAtom
                          (.imax (.succ l) b)
                          hat
                      rw [hflat]
                      exact
                        allCanonAtoms_singleton
                          (.imax (.succ l) b)
                          hat
                  | imax x y =>
                      rw [imaxJoin_imax_eq
                        x y b heq hbz haz
                        hnv]
                      cases hy :
                          decide (y = b) with
                      | false =>
                          simp only []
                          have hat :=
                            isCanonAtom_imax_nested
                              x y b ha hb
                              haz hbz heq hnv
                              hy
                          have hflat :=
                            flattenMax_canonAtom
                              (.imax
                                (.imax x y) b)
                              hat
                          rw [hflat]
                          exact
                            allCanonAtoms_singleton
                              (.imax
                                (.imax x y) b)
                              hat
                      | true =>
                          simp only []
                          cases hx :
                              decide (x = b) with
                          | true =>
                              simp only []
                              have hflat :=
                                flattenMax_canonAtom
                                  b hb
                              rw [hflat]
                              exact
                                allCanonAtoms_singleton
                                  b hb
                          | false =>
                              cases hxz :
                                  levelIsZero x with
                              | true =>
                                  simp only []
                                  have hflat :=
                                    flattenMax_canonAtom
                                      b hb
                                  rw [hflat]
                                  exact
                                    allCanonAtoms_singleton
                                      b hb
                              | false =>
                                  simp only []
                                  have hyeq :
                                      y = b :=
                                    of_decide_eq_true
                                      hy
                                  rw [← hyeq]
                                  have hflat :=
                                    flattenMax_canonAtom
                                      (.imax x y)
                                      ha
                                  rw [hflat]
                                  exact
                                    allCanonAtoms_singleton
                                      (.imax x y)
                                      ha

theorem mapImaxJoin_canonAtoms
    (a : Level)
    (ha : isCanonAtom a = true) :
    ∀ bs : List Level,
      allCanonAtoms bs = true →
        allCanonAtoms
          (mapImaxJoin a bs) = true
  | [], _ => rfl
  | b :: bs, h => by
      have hb :=
        allCanonAtoms_head b bs h
      have htl :=
        allCanonAtoms_tail b bs h
      simp only [mapImaxJoin]
      exact allCanonAtoms_append
        (flattenMax (imaxJoin a b))
        (mapImaxJoin a bs)
        (imaxJoin_canonAtoms a b ha hb)
        (mapImaxJoin_canonAtoms a ha bs
          htl)

theorem pairImax_canonAtoms :
    ∀ as bs : List Level,
      allCanonAtoms as = true →
      allCanonAtoms bs = true →
        allCanonAtoms
          (pairImax as bs) = true
  | [], _, _, _ => rfl
  | a :: as, bs, has, hbs => by
      have ha :=
        allCanonAtoms_head a as has
      have htl :=
        allCanonAtoms_tail a as has
      simp only [pairImax]
      exact allCanonAtoms_append
        (mapImaxJoin a bs)
        (pairImax as bs)
        (mapImaxJoin_canonAtoms a ha bs
          hbs)
        (pairImax_canonAtoms as bs htl
          hbs)

theorem isCanon_imaxCanon (a b : Level)
    (ha : isCanon a = true)
    (hb : isCanon b = true) :
    isCanon (imaxCanon a b) = true := by
  unfold imaxCanon
  cases hbz : levelIsZero b with
  | true =>
      exact isCanon_zero
  | false =>
      cases haz : levelIsZero a with
      | true =>
          exact hb
      | false =>
          cases heq : decide (a = b) with
          | true =>
              exact hb
          | false =>
              cases hnv :
                  levelNeverZero b with
              | true =>
                  have da :=
                    isCanon_destruct a ha
                  have db :=
                    isCanon_destruct b hb
                  exact isCanon_maxFromList
                    (flattenMax a ++
                      flattenMax b)
                    (allCanonAtoms_append
                      (flattenMax a)
                      (flattenMax b)
                      da.1 db.1)
              | false =>
                  have da :=
                    isCanon_destruct a ha
                  have db :=
                    isCanon_destruct b hb
                  exact isCanon_maxFromList
                    (pairImax
                      (flattenMax a)
                      (flattenMax b))
                    (pairImax_canonAtoms
                      (flattenMax a)
                      (flattenMax b)
                      da.1 db.1)

theorem isCanon_nf (l : Level) :
    IsCanon (nf l) := by
  induction l with
  | zero =>
      exact isCanon_zero
  | param i =>
      exact isCanon_of_atom
        (.param i) rfl
  | succ l ih =>
      simp only [nf]
      exact isCanon_succCanon
        (nf l) ih
  | max a b iha ihb =>
      simp only [nf]
      have da :=
        isCanon_destruct (nf a) iha
      have db :=
        isCanon_destruct (nf b) ihb
      exact isCanon_maxFromList
        (flattenMax (nf a) ++
          flattenMax (nf b))
        (allCanonAtoms_append
          (flattenMax (nf a))
          (flattenMax (nf b))
          da.1 db.1)
  | imax a b iha ihb =>
      simp only [nf]
      exact isCanon_imaxCanon
        (nf a) (nf b) iha ihb

theorem nf_idem (l : Level) :
    nf (nf l) = nf l :=
  nf_of_isCanon (nf l) (isCanon_nf l)

/- H-6h measurement for canon_sep: `imax 1 u =ₙ u`
follows from 02 §2 eval (when u=0 both 0; when
u=n≥1, max(1,n)=n) and `nf` does not apply it.
Both sides are `IsCanon`. Distinct antichains
are therefore NOT separated. `canon_sep` is
WALLED by this measurement, not attempted. -/
#eval (if isCanonAtom
    (.imax (.succ .zero) (.param 0)) = true
    then 0 else panic "imax1-atom")
#eval (if isCanon
    (.imax (.succ .zero) (.param 0)) = true
    then 0 else panic "imax1-canon")
#eval (if isCanon (.param 0) = true
    then 0 else panic "param0-canon")
#eval (if decide
    (.imax (.succ .zero) (.param 0) =
      Level.param 0) = false
    then 0 else panic "imax1-neq")

theorem canon_sep_counter_eqN :
    eqN (.imax (.succ .zero) (.param 0))
      (.param 0) := by
  intro ρ
  simp only [eval]
  cases h : ρ 0 with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ n =>
          exact congrArg some
            (Nat.max_eq_right
              (Nat.succ_le_succ
                (Nat.zero_le n)))

theorem canon_sep_counter_neq :
    (.imax (.succ .zero) (.param 0)) ≠
      Level.param 0 := by
  intro h
  cases h

theorem canon_sep_counter_canon_left :
    IsCanon
      (.imax (.succ .zero) (.param 0)) :=
  isCanon_of_atom
    (.imax (.succ .zero) (.param 0)) rfl

theorem canon_sep_counter_canon_right :
    IsCanon (.param 0) :=
  isCanon_of_atom (.param 0) rfl

theorem isCanonAtom_imax_fst (x y : Level)
    (h : isCanonAtom (.imax x y) = true) :
    isCanonAtom x = true := by
  cases hx : isCanonAtom x with
  | false =>
      simp only [isCanonAtom, hx] at h
      exact Bool.noConfusion h
  | true => rfl

theorem isCanonAtom_imax_snd (x y : Level)
    (h : isCanonAtom (.imax x y) = true) :
    isCanonAtom y = true := by
  have hx := isCanonAtom_imax_fst x y h
  cases hy : isCanonAtom y with
  | false =>
      simp only [isCanonAtom, hx, hy] at h
      exact Bool.noConfusion h
  | true => rfl

/-! ## H-6g rung 4: `canon_sep` (value separation).
`nf_injective` / `decEqN_complete` need `isCanon_nf`
(walled at `flattenMax_imaxJoin`). -/

theorem eqN_param_inj (i j : Nat)
    (h : eqN (.param i) (.param j)) : i = j := by
  cases hd : decide (i = j) with
  | true => exact of_decide_eq_true hd
  | false =>
      have hji : decide (j = i) = false := by
        cases h' : decide (j = i) with
        | true =>
            have heq : j = i :=
              of_decide_eq_true h'
            have hd' :
                decide (i = j) = true :=
              decide_eq_true heq.symm
            rw [hd'] at hd
            exact Bool.noConfusion hd
        | false => rfl
      have e := h (noneOnly i)
      have hi := eval_noneOnly_param_self i
      have hj :=
        eval_noneOnly_param_other i j hji
      rw [hi, hj] at e
      exact Option.noConfusion e

/-! ## H-6i / R-LevelSplit: parameter case-split

Start from the measurement: the H-6h counter
imax 1 (param 0) =ₙ param 0 (both IsCanon)
collapses after spec. sigma = {0}: both sides
zero. sigma = empty: both sides succ (param 0).
canon_sep stays refuted; completeness goes
through the imax-free fragment. -/

def memNat (i : Nat) : List Nat → Bool
  | [] => false
  | j :: js =>
      match decide (i = j) with
      | true => true
      | false => memNat i js

def insertNat (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js =>
      match decide (i = j) with
      | true => j :: js
      | false =>
          match decide (i < j) with
          | true => i :: j :: js
          | false => j :: insertNat i js

def foldInsertNat : List Nat → List Nat → List Nat
  | acc, [] => acc
  | acc, x :: xs =>
      foldInsertNat (insertNat x acc) xs

/-- Sorted, dedup. Syntactic parameters of `l`. -/
def paramsOf : Level → List Nat
  | .zero => []
  | .succ l => paramsOf l
  | .param i => [i]
  | .max a b =>
      foldInsertNat (paramsOf a) (paramsOf b)
  | .imax a b =>
      foldInsertNat (paramsOf a) (paramsOf b)

def unionNat (xs ys : List Nat) : List Nat :=
  foldInsertNat xs ys

/-- param i maps to zero for i in sigma;
otherwise succ (param i) (i ≥ 1, with
param i now naming i − 1). -/
def specParam (σ : List Nat) (i : Nat) : Level :=
  match memNat i σ with
  | true => .zero
  | false => .succ (.param i)

def spec (σ : List Nat) : Level → Level
  | .zero => .zero
  | .succ l => .succ (spec σ l)
  | .max a b => .max (spec σ a) (spec σ b)
  | .imax a b => .imax (spec σ a) (spec σ b)
  | .param i => specParam σ i

def imaxFree : Level → Bool
  | .zero => true
  | .succ l => imaxFree l
  | .param _ => true
  | .max a b => imaxFree a && imaxFree b
  | .imax _ _ => false

/- H-6i MEASUREMENT. Counter of H-6h:
imax (succ zero) (param 0) vs param 0.
After spec, both sigma collapse. -/
#eval (if nf (spec [0]
    (.imax (.succ .zero) (.param 0))) = .zero
  then 0 else panic "H-6i: spec {0} imax1 u")
#eval (if nf (spec [0] (.param 0)) = .zero
  then 0 else panic "H-6i: spec {0} u")
#eval (if nf (spec []
    (.imax (.succ .zero) (.param 0))) =
      .succ (.param 0)
  then 0 else panic "H-6i: spec {} imax1 u")
#eval (if nf (spec [] (.param 0)) =
      .succ (.param 0)
  then 0 else panic "H-6i: spec {} u")

def allImaxFree : List Level → Bool
  | [] => true
  | x :: xs =>
      match imaxFree x with
      | true => allImaxFree xs
      | false => false

def anyNeverZero : List Level → Bool
  | [] => false
  | x :: xs =>
      match levelNeverZero x with
      | true => true
      | false => anyNeverZero xs

theorem not_zero_and_never (l : Level)
    (hz : levelIsZero l = true)
    (hn : levelNeverZero l = true) : False :=
  levelNeverZero_not_zero l (fun _ => some 0) hn
    ((levelIsZero_iff l).mp hz (fun _ => some 0))

theorem isCanonAtom_not_zero (l : Level)
    (h : isCanonAtom l = true) :
    levelIsZero l = false := by
  cases l with
  | zero => exact Bool.noConfusion h
  | max _ _ => exact Bool.noConfusion h
  | succ _ => rfl
  | param _ => rfl
  | imax a b =>
      have ha := isCanonAtom_imax_fst a b h
      have hb := isCanonAtom_imax_snd a b h
      cases hza : levelIsZero a with
      | true =>
          simp only [isCanonAtom, ha, hb, hza] at h
          exact Bool.noConfusion h
      | false =>
          cases hzb : levelIsZero b with
          | true =>
              simp only [isCanonAtom, ha, hb,
                hza, hzb] at h
              exact Bool.noConfusion h
          | false =>
              simp only [levelIsZero]
              exact hzb

theorem isCanon_eq_zero (l : Level)
    (hc : IsCanon l)
    (hz : levelIsZero l = true) : l = .zero := by
  have ⟨hatoms, _, _, hmax⟩ :=
    isCanon_destruct l hc
  cases hxs : flattenMax l with
  | nil =>
      have hml : maxOfList (flattenMax l) =
          .zero := by
        rw [hxs]
        rfl
      rw [hmax] at hml
      exact hml
  | cons x xs =>
      have hx : isCanonAtom x = true :=
        allCanonAtoms_head x xs
          (by rw [hxs] at hatoms; exact hatoms)
      have hxz := isCanonAtom_not_zero x hx
      rw [hxs] at hmax
      rw [← hmax] at hz
      cases xs with
      | nil =>
          simp only [maxOfList] at hz
          rw [hxz] at hz
          exact Bool.noConfusion hz
      | cons y ys =>
          simp only [maxOfList, levelIsZero] at hz
          rw [hxz] at hz
          exact Bool.noConfusion hz

theorem nf_of_isZero (l : Level)
    (h : levelIsZero l = true) : nf l = .zero :=
  eqN_zero_nf l ((levelIsZero_iff l).mp h)

theorem levelNeverZero_succCanon (l : Level) :
    levelNeverZero (succCanon l) = true := by
  induction l with
  | max a b iha _ihb =>
      simp only [succCanon, levelNeverZero, iha]
      rfl
  | zero => rfl
  | succ _ _ => rfl
  | param _ => rfl
  | imax _ _ _ _ => rfl

theorem imaxFree_succCanon (l : Level)
    (h : imaxFree l = true) :
    imaxFree (succCanon l) = true := by
  induction l with
  | max a b iha ihb =>
      simp only [imaxFree] at h
      have ⟨ha, hb⟩ := and_true h
      simp only [succCanon, imaxFree,
        iha ha, ihb hb]
      rfl
  | zero => rfl
  | succ _ _ =>
      simp only [succCanon, imaxFree] at h ⊢
      exact h
  | param _ => rfl
  | imax _ _ _ _ => exact Bool.noConfusion h

theorem allImaxFree_append
    (xs ys : List Level) :
    allImaxFree (xs ++ ys) =
      (allImaxFree xs && allImaxFree ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, allImaxFree]
      cases allImaxFree ys <;> rfl
  | cons x xs ih =>
      simp only [List.cons_append, allImaxFree]
      cases imaxFree x with
      | true => exact ih
      | false => rfl

theorem flattenMax_imaxFree (l : Level)
    (h : imaxFree l = true) :
    allImaxFree (flattenMax l) = true := by
  induction l with
  | zero => rfl
  | param _ => rfl
  | succ l _ih =>
      simp only [flattenMax, allImaxFree]
      simp only [imaxFree] at h ⊢
      rw [h]
  | max a b iha ihb =>
      simp only [imaxFree] at h
      have ⟨ha, hb⟩ := and_true h
      simp only [flattenMax]
      rw [allImaxFree_append,
        iha ha, ihb hb]
      rfl
  | imax _ _ _ _ => exact Bool.noConfusion h

theorem imaxFree_maxOfList :
    ∀ xs : List Level,
      allImaxFree xs = true →
        imaxFree (maxOfList xs) = true
  | [], _ => rfl
  | x :: [], h => by
      simp only [allImaxFree, maxOfList] at h ⊢
      cases hx : imaxFree x with
      | false =>
          rw [hx] at h
          exact Bool.noConfusion h
      | true => rfl
  | x :: y :: ys, h => by
      have hx : imaxFree x = true := by
        cases hx : imaxFree x with
        | false =>
            simp only [allImaxFree, hx] at h
            exact Bool.noConfusion h
        | true => rfl
      have htl : allImaxFree (y :: ys) =
          true := by
        simp only [allImaxFree, hx] at h
        exact h
      simp only [maxOfList, imaxFree, hx]
      exact imaxFree_maxOfList (y :: ys) htl

theorem allImaxFree_dropDominated
    (u : Level) :
    ∀ xs : List Level,
      allImaxFree xs = true →
        allImaxFree (dropDominated u xs) = true
  | [], _ => rfl
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          cases hv : imaxFree v with
          | false =>
              simp only [allImaxFree, hv] at h
              exact Bool.noConfusion h
          | true =>
              simp only [allImaxFree, hv] at h
              exact allImaxFree_dropDominated
                u vs h
      | false =>
          simp only [dropDominated, hd,
            allImaxFree]
          cases hv : imaxFree v with
          | false =>
              simp only [allImaxFree, hv] at h
              exact Bool.noConfusion h
          | true =>
              simp only [allImaxFree, hv] at h
              exact allImaxFree_dropDominated
                u vs h

theorem allImaxFree_insertSub (u : Level)
    (hu : imaxFree u = true) :
    ∀ xs : List Level,
      allImaxFree xs = true →
        allImaxFree (insertSub u xs) = true
  | [], _ => by
      simp only [insertSub, allImaxFree, hu]
  | v :: vs, h => by
      simp only [insertSub]
      cases hd : anyDominates u (v :: vs) with
      | true => exact h
      | false =>
          cases hdom : dominates u v with
          | true =>
              cases hv : imaxFree v with
              | false =>
                  simp only [allImaxFree, hv]
                    at h
                  exact Bool.noConfusion h
              | true =>
                  simp only [allImaxFree, hv]
                    at h
                  exact allImaxFree_insertSub
                    u hu vs h
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [allImaxFree, hu]
                  exact
                    allImaxFree_dropDominated
                      u (v :: vs) h
              | false =>
                  simp only [allImaxFree]
                  cases hv : imaxFree v with
                  | false =>
                      simp only [allImaxFree,
                        hv] at h
                      exact Bool.noConfusion h
                  | true =>
                      simp only [allImaxFree,
                        hv] at h
                      exact
                        allImaxFree_insertSub
                          u hu vs h

theorem allImaxFree_foldlIns :
    ∀ acc xs : List Level,
      allImaxFree acc = true →
      allImaxFree xs = true →
        allImaxFree (foldlIns acc xs) = true
  | acc, [], ha, _ => ha
  | acc, x :: xs, ha, hx => by
      have hxt : imaxFree x = true := by
        cases hxt : imaxFree x with
        | false =>
            simp only [allImaxFree, hxt] at hx
            exact Bool.noConfusion hx
        | true => rfl
      have htl : allImaxFree xs = true := by
        simp only [allImaxFree, hxt] at hx
        exact hx
      exact allImaxFree_foldlIns
        (insertSub x acc) xs
        (allImaxFree_insertSub x hxt acc ha)
        htl

theorem imaxFree_maxFromList
    (xs : List Level)
    (h : allImaxFree xs = true) :
    imaxFree (maxFromList xs) = true :=
  imaxFree_maxOfList (foldlIns [] xs)
    (allImaxFree_foldlIns [] xs rfl h)

theorem peel_offset_zero (l : Level)
    (h : (peelOff l).1 = 0) :
    (peelOff l).2 = l := by
  cases l with
  | succ l =>
      simp only [peelOff] at h
      exact Nat.noConfusion h
  | zero => rfl
  | param _ => rfl
  | max _ _ => rfl
  | imax _ _ => rfl

theorem never_of_peel_succ (l : Level)
    (n : Nat) (b : Level)
    (h : peelOff l = (Nat.succ n, b)) :
    levelNeverZero l = true := by
  cases l with
  | succ _ => rfl
  | zero =>
      simp only [peelOff] at h
      exact Nat.noConfusion
        (congrArg Prod.fst h)
  | param _ =>
      simp only [peelOff] at h
      exact Nat.noConfusion
        (congrArg Prod.fst h)
  | max _ _ =>
      simp only [peelOff] at h
      exact Nat.noConfusion
        (congrArg Prod.fst h)
  | imax _ _ =>
      simp only [peelOff] at h
      exact Nat.noConfusion
        (congrArg Prod.fst h)

theorem peel_zero_id (l b : Level)
    (h : peelOff l = (0, b)) : l = b := by
  have hf : (peelOff l).1 = 0 :=
    congrArg Prod.fst h
  have hs := peel_offset_zero l hf
  rw [h] at hs
  exact hs.symm

theorem dominates_neverZero (u v : Level)
    (hd : dominates u v = true)
    (hv : levelNeverZero v = true) :
    levelNeverZero u = true := by
  cases hu : peelOff u with
  | mk nu bu =>
    cases hvpeel : peelOff v with
    | mk nv bv =>
      simp only [dominates, hu, hvpeel] at hd
      cases hle : decide (nv ≤ nu) with
      | false =>
          have hnot :
              ¬ (decide (nv ≤ nu) = true) := by
            intro ht
            rw [hle] at ht
            exact Bool.noConfusion ht
          rw [if_neg hnot] at hd
          exact Bool.noConfusion hd
      | true =>
          have hlen : nv ≤ nu :=
            of_decide_eq_true hle
          cases nv with
          | succ k =>
              cases nu with
              | zero =>
                  exact False.elim
                    (Nat.not_succ_le_zero k hlen)
              | succ n =>
                  exact never_of_peel_succ
                    u n bu hu
          | zero =>
              have hv_id : v = bv :=
                peel_zero_id v bv hvpeel
              rw [if_pos hle] at hd
              cases heq : decide (bu = bv) with
              | true =>
                  have hbu : bu = bv :=
                    of_decide_eq_true heq
                  cases nu with
                  | succ n =>
                      exact never_of_peel_succ
                        u n bu hu
                  | zero =>
                      have hu_id : u = bu :=
                        peel_zero_id u bu hu
                      rw [hu_id, hbu, ← hv_id]
                      exact hv
              | false =>
                  have hnot :
                      ¬ (decide (bu = bv) =
                        true) := by
                    intro ht
                    rw [heq] at ht
                    exact Bool.noConfusion ht
                  rw [if_neg hnot] at hd
                  cases bv with
                  | zero =>
                      rw [hv_id] at hv
                      exact Bool.noConfusion hv
                  | succ w =>
                      cases bu with
                      | imax x b =>
                          cases hb : decide
                              (b = Level.succ w) with
                          | false =>
                              have hd' :
                                  decide
                                    (b = Level.succ w) =
                                    true := hd
                              rw [hb] at hd'
                              exact
                                Bool.noConfusion hd'
                          | true =>
                              have hbe :
                                  b = Level.succ w :=
                                of_decide_eq_true hb
                              cases nu with
                              | succ n =>
                                  exact
                                    never_of_peel_succ
                                      u n
                                      (.imax x b) hu
                              | zero =>
                                  have hu_id :
                                      u =
                                        .imax x b :=
                                    peel_zero_id
                                      u (.imax x b)
                                      hu
                                  rw [hu_id]
                                  simp only
                                    [levelNeverZero]
                                  rw [hbe, ← hv_id]
                                  exact hv
                      | zero =>
                          exact Bool.noConfusion hd
                      | succ _ =>
                          exact Bool.noConfusion hd
                      | max _ _ =>
                          exact Bool.noConfusion hd
                      | param _ =>
                          exact Bool.noConfusion hd
                  | param i =>
                      cases bu with
                      | imax x b =>
                          cases hb : decide
                              (b = Level.param i) with
                          | false =>
                              have hd' :
                                  decide
                                    (b = Level.param i) =
                                    true := hd
                              rw [hb] at hd'
                              exact
                                Bool.noConfusion hd'
                          | true =>
                              have hbe :
                                  b = Level.param i :=
                                of_decide_eq_true hb
                              cases nu with
                              | succ n =>
                                  exact
                                    never_of_peel_succ
                                      u n
                                      (.imax x b) hu
                              | zero =>
                                  have hu_id :
                                      u =
                                        .imax x b :=
                                    peel_zero_id
                                      u (.imax x b)
                                      hu
                                  rw [hu_id]
                                  simp only
                                    [levelNeverZero]
                                  rw [hbe, ← hv_id]
                                  exact hv
                      | zero =>
                          exact Bool.noConfusion hd
                      | succ _ =>
                          exact Bool.noConfusion hd
                      | max _ _ =>
                          exact Bool.noConfusion hd
                      | param _ =>
                          exact Bool.noConfusion hd
                  | max p q =>
                      cases bu with
                      | imax x b =>
                          cases hb : decide
                              (b = Level.max p q) with
                          | false =>
                              have hd' :
                                  decide
                                    (b = Level.max p q) =
                                    true := hd
                              rw [hb] at hd'
                              exact
                                Bool.noConfusion hd'
                          | true =>
                              have hbe :
                                  b = Level.max p q :=
                                of_decide_eq_true hb
                              cases nu with
                              | succ n =>
                                  exact
                                    never_of_peel_succ
                                      u n
                                      (.imax x b) hu
                              | zero =>
                                  have hu_id :
                                      u =
                                        .imax x b :=
                                    peel_zero_id
                                      u (.imax x b)
                                      hu
                                  rw [hu_id]
                                  simp only
                                    [levelNeverZero]
                                  rw [hbe, ← hv_id]
                                  exact hv
                      | zero =>
                          exact Bool.noConfusion hd
                      | succ _ =>
                          exact Bool.noConfusion hd
                      | max _ _ =>
                          exact Bool.noConfusion hd
                      | param _ =>
                          exact Bool.noConfusion hd
                  | imax p q =>
                      cases bu with
                      | imax x b =>
                          cases hb : decide
                              (b = Level.imax p q) with
                          | false =>
                              have hd' :
                                  decide
                                    (b = Level.imax p q) =
                                    true := hd
                              rw [hb] at hd'
                              exact
                                Bool.noConfusion hd'
                          | true =>
                              have hbe :
                                  b = Level.imax p q :=
                                of_decide_eq_true hb
                              cases nu with
                              | succ n =>
                                  exact
                                    never_of_peel_succ
                                      u n
                                      (.imax x b) hu
                              | zero =>
                                  have hu_id :
                                      u =
                                        .imax x b :=
                                    peel_zero_id
                                      u (.imax x b)
                                      hu
                                  rw [hu_id]
                                  simp only
                                    [levelNeverZero]
                                  rw [hbe, ← hv_id]
                                  exact hv
                      | zero =>
                          exact Bool.noConfusion hd
                      | succ _ =>
                          exact Bool.noConfusion hd
                      | max _ _ =>
                          exact Bool.noConfusion hd
                      | param _ =>
                          exact Bool.noConfusion hd

theorem anyNeverZero_append
    (xs ys : List Level) :
    anyNeverZero (xs ++ ys) =
      (anyNeverZero xs || anyNeverZero ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, anyNeverZero]
      cases anyNeverZero ys <;> rfl
  | cons x xs ih =>
      simp only [List.cons_append, anyNeverZero]
      cases levelNeverZero x with
      | true => rfl
      | false => exact ih

theorem flattenMax_anyNever (l : Level)
    (h : levelNeverZero l = true) :
    anyNeverZero (flattenMax l) = true := by
  induction l with
  | zero => exact Bool.noConfusion h
  | param _ => exact Bool.noConfusion h
  | succ l _ih =>
      simp only [flattenMax, anyNeverZero,
        levelNeverZero]
  | max a b iha ihb =>
      simp only [levelNeverZero] at h
      simp only [flattenMax]
      rw [anyNeverZero_append]
      cases ha : levelNeverZero a with
      | true =>
          rw [iha ha]
          rfl
      | false =>
          cases hb : levelNeverZero b with
          | true =>
              have htb := ihb hb
              rw [htb]
              cases anyNeverZero (flattenMax a)
                <;> rfl
          | false =>
              rw [ha, hb] at h
              exact Bool.noConfusion h
  | imax a b _iha _ihb =>
      simp only [flattenMax, anyNeverZero,
        levelNeverZero] at h ⊢
      cases hzb : levelNeverZero b with
      | true => rfl
      | false =>
          rw [hzb] at h
          exact Bool.noConfusion h

theorem maxOfList_neverZero :
    ∀ xs : List Level,
      anyNeverZero xs = true →
        levelNeverZero (maxOfList xs) = true
  | [], h => Bool.noConfusion h
  | x :: [], h => by
      simp only [anyNeverZero, maxOfList] at h ⊢
      cases hx : levelNeverZero x with
      | false =>
          rw [hx] at h
          exact Bool.noConfusion h
      | true => rfl
  | x :: y :: ys, h => by
      simp only [maxOfList, levelNeverZero]
      simp only [anyNeverZero] at h
      cases hx : levelNeverZero x with
      | true => rfl
      | false =>
          rw [hx] at h
          exact maxOfList_neverZero (y :: ys) h

theorem anyNeverZero_dropDominated
    (u : Level)
    (hu : levelNeverZero u = false) :
    ∀ xs : List Level,
      anyNeverZero xs = true →
        anyNeverZero (dropDominated u xs) = true
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      cases hd : dominates u v with
      | true =>
          simp only [dropDominated, hd]
          cases hv : levelNeverZero v with
          | true =>
              have hu' :=
                dominates_neverZero u v hd hv
              rw [hu] at hu'
              exact Bool.noConfusion hu'
          | false =>
              simp only [anyNeverZero, hv] at h
              exact anyNeverZero_dropDominated
                u hu vs h
      | false =>
          simp only [dropDominated, hd,
            anyNeverZero]
          cases hv : levelNeverZero v with
          | true => rfl
          | false =>
              simp only [anyNeverZero, hv] at h
              exact anyNeverZero_dropDominated
                u hu vs h

theorem anyDominates_anyNever (u : Level)
    (hu : levelNeverZero u = true) :
    ∀ xs : List Level,
      anyDominates u xs = true →
        anyNeverZero xs = true
  | [], h => Bool.noConfusion h
  | v :: vs, h => by
      simp only [anyDominates] at h
      cases hd : dominates v u with
      | true =>
          simp only [anyNeverZero]
          have hv :=
            dominates_neverZero v u hd hu
          rw [hv]
      | false =>
          simp only [hd] at h
          simp only [anyNeverZero]
          cases hv : levelNeverZero v with
          | true => rfl
          | false =>
              exact anyDominates_anyNever
                u hu vs h

theorem anyNeverZero_insertSub (u : Level) :
    ∀ xs : List Level,
      (levelNeverZero u = true ∨
        anyNeverZero xs = true) →
        anyNeverZero (insertSub u xs) = true
  | [], h => by
      simp only [insertSub, anyNeverZero]
      cases h with
      | inl hu =>
          rw [hu]
      | inr hx => exact Bool.noConfusion hx
  | v :: vs, h => by
      simp only [insertSub]
      cases hd : anyDominates u (v :: vs) with
      | true =>
          cases h with
          | inl hu =>
              exact anyDominates_anyNever
                u hu (v :: vs) hd
          | inr hx => exact hx
      | false =>
          cases hdom : dominates u v with
          | true =>
              cases h with
              | inl hu =>
                  exact anyNeverZero_insertSub
                    u vs (Or.inl hu)
              | inr hx =>
                  cases hv : levelNeverZero v with
                  | true =>
                      have hu :=
                        dominates_neverZero
                          u v hdom hv
                      exact
                        anyNeverZero_insertSub
                          u vs (Or.inl hu)
                  | false =>
                      simp only [anyNeverZero,
                        hv] at hx
                      exact
                        anyNeverZero_insertSub
                          u vs (Or.inr hx)
          | false =>
              cases hlt : levelLt u v with
              | true =>
                  simp only [anyNeverZero]
                  cases hu : levelNeverZero u with
                  | true => rfl
                  | false =>
                      have hxs :
                          anyNeverZero
                            (v :: vs) = true := by
                        cases h with
                        | inl hu' =>
                            rw [hu'] at hu
                            exact
                              Bool.noConfusion hu
                        | inr hx => exact hx
                      exact
                        anyNeverZero_dropDominated
                          u hu (v :: vs) hxs
              | false =>
                  simp only [anyNeverZero]
                  cases hv : levelNeverZero v with
                  | true => rfl
                  | false =>
                      have hrest :
                          levelNeverZero u = true ∨
                          anyNeverZero vs =
                            true := by
                        cases h with
                        | inl hu =>
                            exact Or.inl hu
                        | inr hx =>
                            simp only
                              [anyNeverZero, hv]
                              at hx
                            exact Or.inr hx
                      exact
                        anyNeverZero_insertSub
                          u vs hrest

theorem anyNeverZero_foldlIns :
    ∀ acc xs : List Level,
      (anyNeverZero acc = true ∨
        anyNeverZero xs = true) →
        anyNeverZero (foldlIns acc xs) = true
  | acc, [], h => by
      cases h with
      | inl ha => exact ha
      | inr hx => exact Bool.noConfusion hx
  | acc, x :: xs, h => by
      have hacc :
          anyNeverZero (insertSub x acc) =
            true ∨
          anyNeverZero xs = true := by
        cases h with
        | inl ha =>
            exact Or.inl
              (anyNeverZero_insertSub x acc
                (Or.inr ha))
        | inr hx =>
            simp only [anyNeverZero] at hx
            cases hv : levelNeverZero x with
            | true =>
                exact Or.inl
                  (anyNeverZero_insertSub x acc
                    (Or.inl hv))
            | false =>
                rw [hv] at hx
                exact Or.inr hx
      exact anyNeverZero_foldlIns
        (insertSub x acc) xs hacc

theorem maxFromList_neverZero
    (xs : List Level)
    (h : anyNeverZero xs = true) :
    levelNeverZero (maxFromList xs) = true :=
  maxOfList_neverZero (foldlIns [] xs)
    (anyNeverZero_foldlIns [] xs (Or.inr h))

theorem spec_zero_or_never (σ : List Nat) :
    ∀ l : Level,
      levelIsZero (spec σ l) = true ∨
      levelNeverZero (spec σ l) = true
  | .zero => Or.inl rfl
  | .succ l => Or.inr rfl
  | .param i => by
      simp only [spec, specParam]
      cases memNat i σ with
      | true => exact Or.inl rfl
      | false => exact Or.inr rfl
  | .max a b => by
      simp only [spec, levelIsZero,
        levelNeverZero]
      cases spec_zero_or_never σ a with
      | inl ha =>
          cases spec_zero_or_never σ b with
          | inl hb =>
              rw [ha, hb]
              exact Or.inl rfl
          | inr hb =>
              rw [hb]
              exact Or.inr
                (by
                  cases levelNeverZero
                    (spec σ a) <;> rfl)
      | inr ha =>
          rw [ha]
          exact Or.inr rfl
  | .imax a b => by
      simp only [spec, levelIsZero,
        levelNeverZero]
      exact spec_zero_or_never σ b

theorem imaxFree_imaxCanon (a b : Level)
    (ha : imaxFree a = true)
    (hb : imaxFree b = true)
    (hzn : levelIsZero b = true ∨
           levelNeverZero b = true) :
    imaxFree (imaxCanon a b) = true := by
  simp only [imaxCanon]
  cases hbz : levelIsZero b with
  | true => rfl
  | false =>
      cases haz : levelIsZero a with
      | true => exact hb
      | false =>
          cases heq : decide (a = b) with
          | true => exact hb
          | false =>
              cases hnv : levelNeverZero b with
              | true =>
                  exact imaxFree_maxFromList
                    (flattenMax a ++ flattenMax b)
                    (by
                      rw [allImaxFree_append,
                        flattenMax_imaxFree a ha,
                        flattenMax_imaxFree b hb]
                      rfl)
              | false =>
                  cases hzn with
                  | inl hz =>
                      rw [hz] at hbz
                      exact Bool.noConfusion hbz
                  | inr hn =>
                      rw [hn] at hnv
                      exact Bool.noConfusion hnv

theorem nf_spec_imaxFree_and_zn (σ : List Nat) :
    ∀ l : Level,
      imaxFree (nf (spec σ l)) = true ∧
      (levelIsZero (nf (spec σ l)) = true ∨
       levelNeverZero (nf (spec σ l)) = true)
  | .zero => ⟨rfl, Or.inl rfl⟩
  | .param i => by
      simp only [spec, specParam]
      cases memNat i σ with
      | true => exact ⟨rfl, Or.inl rfl⟩
      | false =>
          simp only [nf, succCanon]
          exact ⟨rfl, Or.inr rfl⟩
  | .succ l => by
      simp only [spec, nf]
      have ih := nf_spec_imaxFree_and_zn σ l
      exact ⟨imaxFree_succCanon _ ih.1,
        Or.inr (levelNeverZero_succCanon _)⟩
  | .max a b => by
      simp only [spec, nf]
      have iha := nf_spec_imaxFree_and_zn σ a
      have ihb := nf_spec_imaxFree_and_zn σ b
      have hf : allImaxFree
          (flattenMax (nf (spec σ a)) ++
            flattenMax (nf (spec σ b))) = true := by
        rw [allImaxFree_append,
          flattenMax_imaxFree _ iha.1,
          flattenMax_imaxFree _ ihb.1]
        rfl
      have him := imaxFree_maxFromList _ hf
      refine ⟨him, ?_⟩
      cases iha.2 with
      | inl ha =>
          have ha0 := isCanon_eq_zero
            (nf (spec σ a)) (isCanon_nf _) ha
          cases ihb.2 with
          | inl hb =>
              have hb0 := isCanon_eq_zero
                (nf (spec σ b)) (isCanon_nf _) hb
              rw [ha0, hb0]
              simp only [flattenMax,
                List.nil_append, maxFromList,
                foldlIns, maxOfList]
              exact Or.inl rfl
          | inr hb =>
              rw [ha0]
              simp only [flattenMax,
                List.nil_append]
              exact Or.inr
                (maxFromList_neverZero _
                  (flattenMax_anyNever _ hb))
      | inr ha =>
          exact Or.inr
            (maxFromList_neverZero _
              (by
                rw [anyNeverZero_append,
                  flattenMax_anyNever _ ha]
                rfl))
  | .imax a b => by
      simp only [spec, nf]
      have iha := nf_spec_imaxFree_and_zn σ a
      have ihb := nf_spec_imaxFree_and_zn σ b
      have hc := imaxFree_imaxCanon
        (nf (spec σ a)) (nf (spec σ b))
        iha.1 ihb.1 ihb.2
      refine ⟨hc, ?_⟩
      simp only [imaxCanon]
      cases hbz : levelIsZero
          (nf (spec σ b)) with
      | true => exact Or.inl rfl
      | false =>
          cases haz : levelIsZero
              (nf (spec σ a)) with
          | true => exact ihb.2
          | false =>
              cases heq : decide
                  (nf (spec σ a) =
                    nf (spec σ b)) with
              | true => exact ihb.2
              | false =>
                  cases hnv : levelNeverZero
                      (nf (spec σ b)) with
                  | true =>
                      exact Or.inr
                        (maxFromList_neverZero _
                          (by
                            rw [anyNeverZero_append]
                            have htb :=
                              flattenMax_anyNever
                                (nf (spec σ b)) hnv
                            rw [htb]
                            cases anyNeverZero
                              (flattenMax
                                (nf (spec σ a)))
                              <;> rfl))
                  | false =>
                      cases ihb.2 with
                      | inl hz =>
                          rw [hz] at hbz
                          exact Bool.noConfusion hbz
                      | inr hn =>
                          rw [hn] at hnv
                          exact Bool.noConfusion hnv

theorem nf_spec_imaxFree (σ : List Nat)
    (l : Level) :
    imaxFree (nf (spec σ l)) = true :=
  (nf_spec_imaxFree_and_zn σ l).1

/-! Rung (2): spec_eval. A total valuation ρ with
zero-set σ satisfies
eval ρ l = eval (ρ ∘ pred) (spec σ l). -/

theorem memNat_insertNat (i j : Nat) :
    ∀ xs : List Nat,
      memNat i (insertNat j xs) =
        (decide (i = j) || memNat i xs)
  | [] => by
      simp only [insertNat, memNat]
      cases decide (i = j) <;> rfl
  | x :: xs => by
      simp only [insertNat]
      cases hjx : decide (j = x) with
      | true =>
          have hjx' : j = x :=
            of_decide_eq_true hjx
          simp only [memNat]
          cases hij : decide (i = j) with
          | true =>
              have hix :
                  i = x :=
                (of_decide_eq_true hij).trans
                  hjx'
              cases hixd : decide (i = x) with
              | true => rfl
              | false =>
                  have ht :
                      decide (i = x) = true :=
                    decide_eq_true hix
                  rw [ht] at hixd
                  exact Bool.noConfusion hixd
          | false =>
              cases hixd : decide (i = x) with
              | true =>
                  have hij' :
                      i = j :=
                    (of_decide_eq_true hixd).trans
                      hjx'.symm
                  have ht :
                      decide (i = j) = true :=
                    decide_eq_true hij'
                  rw [ht] at hij
                  exact Bool.noConfusion hij
              | false => rfl
      | false =>
          cases hlt : decide (j < x) with
          | true =>
              simp only [memNat]
              cases decide (i = j) <;> rfl
          | false =>
              simp only [memNat]
              have ih :=
                memNat_insertNat i j xs
              cases hix : decide (i = x) with
              | true =>
                  cases decide (i = j) <;> rfl
              | false =>
                  rw [ih]

theorem memNat_foldInsertNat (i : Nat) :
    ∀ acc xs : List Nat,
      memNat i (foldInsertNat acc xs) =
        (memNat i acc || memNat i xs)
  | acc, [] => by
      simp only [foldInsertNat, memNat]
      cases memNat i acc <;> rfl
  | acc, x :: xs => by
      simp only [foldInsertNat, memNat]
      have ih :=
        memNat_foldInsertNat i
          (insertNat x acc) xs
      rw [ih, memNat_insertNat]
      cases decide (i = x) with
      | true =>
          cases memNat i acc <;> rfl
      | false =>
          cases memNat i acc with
          | true =>
              cases memNat i xs <;> rfl
          | false =>
              cases memNat i xs <;> rfl

theorem memNat_paramsOf_max (i : Nat)
    (a b : Level) :
    memNat i (paramsOf (.max a b)) =
      (memNat i (paramsOf a) ||
        memNat i (paramsOf b)) :=
  memNat_foldInsertNat i
    (paramsOf a) (paramsOf b)

theorem memNat_paramsOf_imax (i : Nat)
    (a b : Level) :
    memNat i (paramsOf (.imax a b)) =
      (memNat i (paramsOf a) ||
        memNat i (paramsOf b)) :=
  memNat_foldInsertNat i
    (paramsOf a) (paramsOf b)

theorem or_true_left (b : Bool) :
    (true || b) = true := by
  cases b <;> rfl

def zeroSetOf (ρ : Nat → Nat) : List Nat → List Nat
  | [] => []
  | i :: is =>
      match decide (ρ i = 0) with
      | true => i :: zeroSetOf ρ is
      | false => zeroSetOf ρ is

theorem memNat_zeroSetOf_subset
    (ρ : Nat → Nat) :
    ∀ xs i,
      memNat i (zeroSetOf ρ xs) = true →
        memNat i xs = true
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [zeroSetOf] at h
      cases hz : decide (ρ x = 0) with
      | true =>
          simp only [hz, memNat] at h ⊢
          cases hix : decide (i = x) with
          | true => rfl
          | false =>
              simp only [hix] at h
              exact memNat_zeroSetOf_subset
                ρ xs i h
      | false =>
          simp only [hz] at h
          have hrest :=
            memNat_zeroSetOf_subset ρ xs i h
          simp only [memNat]
          cases decide (i = x) with
          | true => rfl
          | false => exact hrest

theorem memNat_zeroSetOf (ρ : Nat → Nat) :
    ∀ xs i,
      memNat i xs = true →
        memNat i (zeroSetOf ρ xs) =
          decide (ρ i = 0)
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [memNat] at h
      cases hix : decide (i = x) with
      | true =>
          have hix' : i = x :=
            of_decide_eq_true hix
          simp only [zeroSetOf]
          cases hz : decide (ρ x = 0) with
          | true =>
              simp only [memNat, hix]
              rw [hix']
              exact hz.symm
          | false =>
              rw [hix']
              cases hrest : memNat x xs with
              | true =>
                  exact memNat_zeroSetOf
                    ρ xs x hrest
              | false =>
                  have hnot :
                      memNat x
                        (zeroSetOf ρ xs) =
                        false := by
                    cases hm : memNat x
                        (zeroSetOf ρ xs) with
                    | false => rfl
                    | true =>
                        have hs :=
                          memNat_zeroSetOf_subset
                            ρ xs x hm
                        rw [hrest] at hs
                        exact Bool.noConfusion hs
                  rw [hnot]
                  exact hz.symm
      | false =>
          simp only [hix] at h
          simp only [zeroSetOf]
          cases hz : decide (ρ x = 0) with
          | true =>
              simp only [memNat, hix]
              exact memNat_zeroSetOf ρ xs i h
          | false =>
              exact memNat_zeroSetOf ρ xs i h

theorem spec_eval (σ : List Nat)
    (ρ : Nat → Nat) :
    ∀ l : Level,
      (∀ i, memNat i (paramsOf l) = true →
        memNat i σ = decide (ρ i = 0)) →
      eval (fun i => some (ρ i)) l =
        eval (fun i => some (Nat.pred (ρ i)))
          (spec σ l)
  | .zero, _hσ => rfl
  | .succ l, hσ => by
      have ih := spec_eval σ ρ l hσ
      simp only [spec, eval, ih]
  | .param i, hσ => by
      have hσi : memNat i σ =
          decide (ρ i = 0) := by
        have hin : memNat i
            (paramsOf (.param i)) = true := by
          simp only [paramsOf, memNat]
          cases hii : decide (i = i) with
          | true => rfl
          | false =>
              exact False.elim
                (of_decide_eq_false hii rfl)
        exact hσ i hin
      simp only [spec, specParam, eval]
      cases hm : memNat i σ with
      | true =>
          rw [hm] at hσi
          have hz : ρ i = 0 :=
            of_decide_eq_true hσi.symm
          rw [hz]
          rfl
      | false =>
          rw [hm] at hσi
          simp only [eval]
          cases hn : ρ i with
          | zero =>
              have ht :
                  decide (ρ i = 0) = true := by
                rw [hn]
                rfl
              rw [ht] at hσi
              exact Bool.noConfusion hσi
          | succ n =>
              simp only [Nat.pred]
              rfl
  | .max a b, hσ => by
      have hσa :
          ∀ i, memNat i (paramsOf a) = true →
            memNat i σ = decide (ρ i = 0) := by
        intro i hi
        have hin :
            memNat i (paramsOf (.max a b)) =
              true := by
          rw [memNat_paramsOf_max, hi]
          exact or_true_left _
        exact hσ i hin
      have hσb :
          ∀ i, memNat i (paramsOf b) = true →
            memNat i σ = decide (ρ i = 0) := by
        intro i hi
        have hin :
            memNat i (paramsOf (.max a b)) =
              true := by
          rw [memNat_paramsOf_max]
          cases memNat i (paramsOf a) with
          | true => rfl
          | false =>
              rw [hi]
              rfl
        exact hσ i hin
      have iha := spec_eval σ ρ a hσa
      have ihb := spec_eval σ ρ b hσb
      simp only [spec, eval, iha, ihb]
  | .imax a b, hσ => by
      have hσa :
          ∀ i, memNat i (paramsOf a) = true →
            memNat i σ = decide (ρ i = 0) := by
        intro i hi
        have hin :
            memNat i (paramsOf (.imax a b)) =
              true := by
          rw [memNat_paramsOf_imax, hi]
          exact or_true_left _
        exact hσ i hin
      have hσb :
          ∀ i, memNat i (paramsOf b) = true →
            memNat i σ = decide (ρ i = 0) := by
        intro i hi
        have hin :
            memNat i (paramsOf (.imax a b)) =
              true := by
          rw [memNat_paramsOf_imax]
          cases memNat i (paramsOf a) with
          | true => rfl
          | false =>
              rw [hi]
              rfl
        exact hσ i hin
      have iha := spec_eval σ ρ a hσa
      have ihb := spec_eval σ ρ b hσb
      simp only [spec, eval, iha, ihb]

theorem spec_eval_zeroSet (ρ : Nat → Nat)
    (l : Level) :
    eval (fun i => some (ρ i)) l =
      eval (fun i => some (Nat.pred (ρ i)))
        (spec (zeroSetOf ρ (paramsOf l)) l) :=
  spec_eval (zeroSetOf ρ (paramsOf l)) ρ l
    (fun i hi =>
      memNat_zeroSetOf ρ (paramsOf l) i hi)

/-! Rung (3): canon_sep_imaxFree. Two imax-free
canon forms that agree on every total valuation
are syntactically equal. -/

def isOffAtom (l : Level) : Bool :=
  match (peelOff l).2 with
  | .zero => true
  | .param _ => true
  | _ => false

def allOffAtoms : List Level → Bool
  | [] => true
  | x :: xs =>
      match isOffAtom x with
      | true => allOffAtoms xs
      | false => false

def spike (i big : Nat) : Nat → Nat :=
  fun j =>
    match decide (j = i) with
    | true => big
    | false => 0

def evalMaxListTotal (σ : Nat → Nat) :
    List Level → Nat
  | [] => 0
  | x :: xs =>
      max (evalTotal σ x)
        (evalMaxListTotal σ xs)

def paramOff (i : Nat) : List Level → Option Nat
  | [] => none
  | x :: xs =>
      match (peelOff x).2 with
      | .param j =>
          match decide (j = i) with
          | true => some (peelOff x).1
          | false => paramOff i xs
      | _ => paramOff i xs

def constOff : List Level → Option Nat
  | [] => none
  | x :: xs =>
      match (peelOff x).2 with
      | .zero => some (peelOff x).1
      | _ => constOff xs

def maxOffList : List Level → Nat
  | [] => 0
  | x :: xs =>
      max (peelOff x).1 (maxOffList xs)

theorem peel_reconstruct (l : Level) :
    wrapSucc (peelOff l).1 (peelOff l).2 = l := by
  induction l with
  | succ l ih =>
      simp only [peelOff, wrapSucc]
      cases h : peelOff l with
      | mk n b =>
          simp only [h] at ih
          simp only [h]
          exact congrArg Level.succ ih
  | zero => rfl
  | param _ => rfl
  | max _ _ => rfl
  | imax _ _ => rfl

theorem evalTotal_wrapSucc (σ : Nat → Nat) :
    ∀ n l,
      evalTotal σ (wrapSucc n l) =
        evalTotal σ l + n
  | 0, l => by
      simp only [wrapSucc, evalTotal]
      exact (Nat.add_zero _).symm
  | Nat.succ n, l => by
      simp only [wrapSucc, evalTotal]
      have ih := evalTotal_wrapSucc σ n l
      rw [ih]
      exact Nat.add_succ (evalTotal σ l) n

theorem peelOff_wrapSucc_base (n : Nat)
    (b : Level) (h : (peelOff b).1 = 0) :
    peelOff (wrapSucc n b) = (n, b) := by
  induction n with
  | zero =>
      simp only [wrapSucc]
      have hs := peel_offset_zero b h
      cases hb : peelOff b with
      | mk k c =>
          simp only [hb] at h hs
          rw [h, hs]
  | succ n ih =>
      simp only [wrapSucc, peelOff]
      rw [ih]

theorem evalTotal_offAtom (σ : Nat → Nat)
    (l : Level) (h : isOffAtom l = true) :
    evalTotal σ l =
      (peelOff l).1 +
        match (peelOff l).2 with
        | .zero => 0
        | .param i => σ i
        | _ => 0 := by
  cases hpeel : peelOff l with
  | mk n b =>
      have hr : wrapSucc n b = l := by
        have := peel_reconstruct l
        rw [hpeel] at this
        exact this
      have hb0 : (peelOff b).1 = 0 := by
        simp only [isOffAtom, hpeel] at h
        cases b with
        | zero => rfl
        | param _ => rfl
        | succ _ => exact Bool.noConfusion h
        | max _ _ => exact Bool.noConfusion h
        | imax _ _ => exact Bool.noConfusion h
      have hpw :=
        peelOff_wrapSucc_base n b hb0
      rw [← hr]
      rw [evalTotal_wrapSucc σ n b]
      simp only [hpw, Prod.fst, Prod.snd]
      cases b with
      | zero =>
          simp only [evalTotal]
          exact Nat.add_comm 0 n
      | param i =>
          simp only [evalTotal]
          exact Nat.add_comm (σ i) n
      | succ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | max _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h

theorem imaxFree_canonAtom_off (l : Level)
    (ha : isCanonAtom l = true)
    (hf : imaxFree l = true) :
    isOffAtom l = true := by
  induction l with
  | zero => exact Bool.noConfusion ha
  | max _ _ _ _ => exact Bool.noConfusion ha
  | param _ => rfl
  | succ l ih =>
      simp only [imaxFree] at hf
      cases l with
      | max _ _ =>
          simp only [isCanonAtom] at ha
          exact Bool.noConfusion ha
      | zero => rfl
      | param _ => rfl
      | succ l' =>
          simp only [isCanonAtom] at ha
          exact ih ha hf
      | imax _ _ =>
          exact Bool.noConfusion hf
  | imax _ _ _ _ =>
      simp only [imaxFree] at hf
      exact Bool.noConfusion hf

theorem allOffAtoms_of (xs : List Level)
    (ha : allCanonAtoms xs = true)
    (hf : allImaxFree xs = true) :
    allOffAtoms xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := allCanonAtoms_head x xs ha
      have hxt : imaxFree x = true := by
        cases hxt : imaxFree x with
        | false =>
            simp only [allImaxFree, hxt] at hf
            exact Bool.noConfusion hf
        | true => rfl
      have htlA := allCanonAtoms_tail x xs ha
      have htlF : allImaxFree xs = true := by
        simp only [allImaxFree, hxt] at hf
        exact hf
      simp only [allOffAtoms,
        imaxFree_canonAtom_off x hx hxt]
      exact ih htlA htlF

theorem evalTotal_maxOfList (σ : Nat → Nat) :
    ∀ xs,
      evalTotal σ (maxOfList xs) =
        evalMaxListTotal σ xs
  | [] => rfl
  | x :: [] => by
      simp only [maxOfList, evalMaxListTotal]
      exact (Nat.max_zero (evalTotal σ x)).symm
  | x :: y :: ys => by
      change evalTotal σ
          (.max x (maxOfList (y :: ys))) =
        max (evalTotal σ x)
          (evalMaxListTotal σ (y :: ys))
      simp only [evalTotal]
      rw [evalTotal_maxOfList σ (y :: ys)]

theorem flatten_off_of_canon_imaxFree
    (l : Level)
    (hc : IsCanon l)
    (hf : imaxFree l = true) :
    allOffAtoms (flattenMax l) = true :=
  allOffAtoms_of (flattenMax l)
    (isCanon_allCanonAtoms l hc)
    (flattenMax_imaxFree l hf)

theorem evalTotal_spike_off (i big : Nat)
    (x : Level) (h : isOffAtom x = true) :
    evalTotal (spike i big) x =
      (peelOff x).1 +
        match (peelOff x).2 with
        | .param j =>
            match decide (j = i) with
            | true => big
            | false => 0
        | _ => 0 := by
  rw [evalTotal_offAtom (spike i big) x h]
  simp only [spike]
  cases (peelOff x).2 <;> rfl

theorem evalTotal_canonAtom_pos (y : Level)
    (ha : isCanonAtom y = true)
    (hf : imaxFree y = true) :
    0 < evalTotal (fun _ => 1) y := by
  have ho := imaxFree_canonAtom_off y ha hf
  have hz := isCanonAtom_not_zero y ha
  have he :=
    evalTotal_offAtom (fun _ => 1) y ho
  rw [he]
  cases hb : (peelOff y).2 with
  | zero =>
      simp only [hb]
      cases hn : (peelOff y).1 with
      | zero =>
          have hy0 : y = .zero := by
            have hr := peel_reconstruct y
            rw [hn, hb] at hr
            simp only [wrapSucc] at hr
            exact hr.symm
          rw [hy0] at hz
          exact Bool.noConfusion hz
      | succ n =>
          exact Nat.zero_lt_succ n
  | param j =>
      simp only [hb]
      exact Nat.zero_lt_succ
        (peelOff y).1
  | succ _ =>
      simp only [isOffAtom] at ho
      rw [hb] at ho
      exact Bool.noConfusion ho
  | max _ _ =>
      simp only [isOffAtom] at ho
      rw [hb] at ho
      exact Bool.noConfusion ho
  | imax _ _ =>
      simp only [isOffAtom] at ho
      rw [hb] at ho
      exact Bool.noConfusion ho

theorem flattenMax_nil_eq_zero (l : Level)
    (hc : IsCanon l)
    (h : flattenMax l = []) : l = .zero := by
  have m := isCanon_maxOfList l hc
  rw [h] at m
  exact m.symm

/- Attempt 1 of canon_sep_imaxFree (WALL, not
declared). Statement:

theorem canon_sep_imaxFree (n1 n2 : Level)
    (h1 : IsCanon n1) (h2 : IsCanon n2)
    (f1 : imaxFree n1 = true)
    (f2 : imaxFree n2 = true)
    (h : ∀ σ : Nat → Nat,
      evalTotal σ n1 = evalTotal σ n2) :
    n1 = n2

Last error, well-formed, reached the arm:

error: lean/rcic/RcicLevelDec.lean:8766:22: unsolved goals
case false.cons.cons
⊢ n1 = n2

with hd : decide (flattenMax n1 = flattenMax n2)
= false, flattenMax n1 = x :: xs,
flattenMax n2 = y :: ys.
Nil/nil, nil/cons, cons/nil closed.
Cons/cons (two nonempty imax-free antichains)
not closed. Distinguishing spike on paramOff
not written. -/

/-! H-6j (3′) helper (a): `atomKey` and
`maxOfList_evalTotal` (list induction; the
evaluation of a flattened antichain is the
max of its atoms). -/

/-- Parameter index (`some i`) or the constant
atom (`none`), and the succ-offset `k`. -/
def atomKey (l : Level) : Option Nat × Nat :=
  match (peelOff l).2 with
  | .param i => (some i, (peelOff l).1)
  | _ => (none, (peelOff l).1)

theorem maxOfList_evalTotal (σ : Nat → Nat) :
    ∀ xs : List Level,
      evalTotal σ (maxOfList xs) =
        evalMaxListTotal σ xs :=
  evalTotal_maxOfList σ

/-! H-6j (3′) helper (b): spike evaluation of
off-atoms. `evalTotal (spike i N) (succᵏ (param
i)) = N + k`; every other off-atom is at most
`N` beyond its offset. -/

theorem atomKey_wrap_param (i k : Nat) :
    atomKey (wrapSucc k (.param i)) =
      (some i, k) := by
  have hp :=
    peelOff_wrapSucc_base k (.param i) rfl
  simp only [atomKey, hp]

theorem atomKey_wrap_zero (k : Nat) :
    atomKey (wrapSucc k .zero) = (none, k) := by
  have hp := peelOff_wrapSucc_base k .zero rfl
  simp only [atomKey, hp]

theorem evalTotal_spike_param (i N k : Nat) :
    evalTotal (spike i N)
      (wrapSucc k (.param i)) = N + k := by
  rw [evalTotal_wrapSucc]
  simp only [evalTotal, spike]
  cases hd : decide (i = i) with
  | false =>
      exact False.elim
        (of_decide_eq_false hd (Eq.refl i))
  | true => rfl

theorem evalTotal_spike_zero (i N k : Nat) :
    evalTotal (spike i N)
      (wrapSucc k .zero) = k := by
  rw [evalTotal_wrapSucc]
  simp only [evalTotal]
  exact Nat.zero_add k

theorem evalTotal_spike_other_param
    (i j N k : Nat)
    (hne : decide (j = i) = false) :
    evalTotal (spike i N)
      (wrapSucc k (.param j)) = k := by
  rw [evalTotal_wrapSucc]
  simp only [evalTotal, spike]
  rw [hne]
  exact Nat.zero_add k

theorem evalTotal_spike_off_le (i N : Nat)
    (x : Level) (h : isOffAtom x = true) :
    evalTotal (spike i N) x ≤
      N + (peelOff x).1 := by
  cases hpeel : peelOff x with
  | mk n b =>
      have he := evalTotal_spike_off i N x h
      rw [hpeel] at he
      rw [he]
      cases b with
      | param j =>
          cases hd : decide (j = i) with
          | true =>
              simp only [hpeel, hd]
              exact Nat.le_of_eq (Nat.add_comm n N)
          | false =>
              simp only [hpeel, hd]
              exact Nat.le_trans
                (Nat.le_of_eq (Nat.add_zero n))
                (Nat.le_add_left n N)
      | zero =>
          simp only [hpeel]
          exact Nat.le_trans
            (Nat.le_of_eq (Nat.add_zero n))
            (Nat.le_add_left n N)
      | succ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | max _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h

theorem evalTotal_zero_off (x : Level)
    (h : isOffAtom x = true) :
    evalTotal (fun _ => 0) x =
      (peelOff x).1 := by
  cases hpeel : peelOff x with
  | mk n b =>
      have he :=
        evalTotal_offAtom (fun _ => 0) x h
      rw [hpeel] at he
      rw [he]
      cases b with
      | zero =>
          simp only [hpeel]
          exact Nat.add_zero n
      | param _ =>
          simp only [hpeel]
          exact Nat.add_zero n
      | succ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | max _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at h
          exact Bool.noConfusion h

theorem peel_le_maxOffList (x : Level) :
    ∀ xs : List Level,
      memLevel x xs = true →
        (peelOff x).1 ≤ maxOffList xs
  | [], hm => Bool.noConfusion hm
  | y :: ys, hm => by
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          rw [hxy]
          exact Nat.le_max_left _ _
      | false =>
          simp only [memLevel, heq] at hm
          exact Nat.le_trans
            (peel_le_maxOffList x ys hm)
            (Nat.le_max_right _ _)

/-! H-6j (3′) helper (c): first-difference of
two sorted antichains, then a spike on the
atom present on one side. -/

theorem allOffAtoms_head (x : Level)
    (xs : List Level)
    (h : allOffAtoms (x :: xs) = true) :
    isOffAtom x = true := by
  cases hx : isOffAtom x with
  | false =>
      simp only [allOffAtoms, hx] at h
      exact Bool.noConfusion h
  | true => rfl

theorem allOffAtoms_tail (x : Level)
    (xs : List Level)
    (h : allOffAtoms (x :: xs) = true) :
    allOffAtoms xs = true := by
  cases hx : isOffAtom x with
  | false =>
      simp only [allOffAtoms, hx] at h
      exact Bool.noConfusion h
  | true =>
      simp only [allOffAtoms, hx] at h
      exact h

theorem allOffAtoms_mem (x : Level) :
    ∀ xs : List Level,
      allOffAtoms xs = true →
      memLevel x xs = true →
        isOffAtom x = true
  | [], _, hm => Bool.noConfusion hm
  | y :: ys, h, hm => by
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          rw [hxy]
          exact allOffAtoms_head y ys h
      | false =>
          simp only [memLevel, heq] at hm
          exact allOffAtoms_mem x ys
            (allOffAtoms_tail y ys h) hm

theorem memLevel_cons_tail (x y : Level)
    (xs : List Level)
    (h : memLevel y xs = true) :
    memLevel y (x :: xs) = true := by
  cases heq : decide (y = x) with
  | true =>
      simp only [memLevel, heq]
  | false =>
      simp only [memLevel, heq]
      exact h

theorem evalMaxListTotal_le_mem
    (σ : Nat → Nat) (x : Level) :
    ∀ xs : List Level,
      memLevel x xs = true →
        evalTotal σ x ≤
          evalMaxListTotal σ xs
  | [], hm => Bool.noConfusion hm
  | y :: ys, hm => by
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          rw [hxy]
          exact Nat.le_max_left _ _
      | false =>
          simp only [memLevel, heq] at hm
          exact Nat.le_trans
            (evalMaxListTotal_le_mem σ x ys hm)
            (Nat.le_max_right _ _)

theorem max_lt_of {a b c : Nat}
    (ha : a < c) (hb : b < c) :
    max a b < c := by
  cases Nat.le_total a b with
  | inl h =>
      have hm : max a b = b :=
        Nat.max_eq_right h
      rw [hm]
      exact hb
  | inr h =>
      have hm : max a b = a :=
        Nat.max_eq_left h
      rw [hm]
      exact ha

theorem evalMaxListTotal_lt_of
    (σ : Nat → Nat) (bound : Nat)
    (hb0 : 0 < bound) :
    ∀ xs : List Level,
      (∀ x, memLevel x xs = true →
        evalTotal σ x < bound) →
        evalMaxListTotal σ xs < bound
  | [], _ => hb0
  | x :: xs, h =>
      max_lt_of
        (h x (memLevel_cons_self x xs))
        (evalMaxListTotal_lt_of σ bound hb0 xs
          (fun y hm =>
            h y (memLevel_cons_tail x y xs hm)))

theorem anyDominates_false_mem
    (x y : Level) :
    ∀ xs : List Level,
      anyDominates x xs = false →
      memLevel y xs = true →
        dominates y x = false
  | [], _, hm => Bool.noConfusion hm
  | v :: vs, h, hm => by
      cases heq : decide (y = v) with
      | true =>
          have hyv : y = v :=
            of_decide_eq_true heq
          simp only [anyDominates] at h
          cases hd : dominates v x with
          | true =>
              rw [hd] at h
              exact Bool.noConfusion h
          | false =>
              rw [hyv]
              exact hd
      | false =>
          simp only [memLevel, heq] at hm
          simp only [anyDominates] at h
          cases hd : dominates v x with
          | true =>
              rw [hd] at h
              exact Bool.noConfusion h
          | false =>
              rw [hd] at h
              exact anyDominates_false_mem
                x y vs h hm

theorem offAtom_eq_of_peel (u v : Level)
    (hu : isOffAtom u = true)
    (hv : isOffAtom v = true)
    (h : peelOff u = peelOff v) : u = v := by
  have ru := peel_reconstruct u
  have rv := peel_reconstruct v
  rw [h] at ru
  exact ru.symm.trans rv

theorem dominates_same_param
    (u v : Level) (i nu nv : Nat)
    (hu : peelOff u = (nu, .param i))
    (hv : peelOff v = (nv, .param i)) :
    dominates u v = decide (nv ≤ nu) := by
  simp only [dominates]
  rw [hu, hv]
  cases hle : decide (nv ≤ nu) with
  | false => rfl
  | true =>
      cases heq : decide
          ((.param i : Level) = .param i) with
      | false =>
          exact False.elim
            (of_decide_eq_false heq rfl)
      | true => rfl

theorem dominates_diff_param
    (u v : Level) (i j nu nv : Nat)
    (hne : decide (i = j) = false)
    (hu : peelOff u = (nu, .param i))
    (hv : peelOff v = (nv, .param j)) :
    dominates u v = false := by
  simp only [dominates]
  rw [hu, hv]
  cases hle : decide (nv ≤ nu) with
  | false => rfl
  | true =>
      cases heq : decide
          ((.param i : Level) = .param j) with
      | true =>
          have hij : i = j := by
            injection (of_decide_eq_true heq)
          rw [decide_eq_true hij] at hne
          exact Bool.noConfusion hne
      | false => rfl

theorem dominates_param_const
    (u v : Level) (i nu nv : Nat)
    (hu : peelOff u = (nu, .param i))
    (hv : peelOff v = (nv, .zero)) :
    dominates u v = decide (nv ≤ nu) := by
  simp only [dominates]
  rw [hu, hv]
  cases hle : decide (nv ≤ nu) with
  | false => rfl
  | true =>
      cases heq : decide
          ((.param i : Level) = .zero) with
      | true =>
          cases (of_decide_eq_true heq)
      | false => rfl

theorem dominates_const_param
    (u v : Level) (i nu nv : Nat)
    (hu : peelOff u = (nu, .zero))
    (hv : peelOff v = (nv, .param i)) :
    dominates u v = false := by
  simp only [dominates]
  rw [hu, hv]
  cases hle : decide (nv ≤ nu) with
  | false => rfl
  | true =>
      cases heq : decide
          ((.zero : Level) = .param i) with
      | true =>
          cases (of_decide_eq_true heq)
      | false => rfl

theorem dominates_const_const
    (u v : Level) (nu nv : Nat)
    (hu : peelOff u = (nu, .zero))
    (hv : peelOff v = (nv, .zero)) :
    dominates u v = decide (nv ≤ nu) := by
  simp only [dominates]
  rw [hu, hv]
  cases hle : decide (nv ≤ nu) with
  | false => rfl
  | true =>
      cases heq : decide
          ((.zero : Level) = .zero) with
      | false =>
          exact False.elim
            (of_decide_eq_false heq rfl)
      | true => rfl

theorem maxOffList_append :
    ∀ xs ys : List Level,
      maxOffList (xs ++ ys) =
        max (maxOffList xs) (maxOffList ys)
  | [], ys => by
      have h0 : maxOffList ([] ++ ys) =
          maxOffList ys := rfl
      have hz : maxOffList ([] : List Level) =
          0 := rfl
      rw [h0, hz]
      exact (Nat.max_eq_right
        (Nat.zero_le (maxOffList ys))).symm
  | x :: xs, ys => by
      have ih := maxOffList_append xs ys
      show max (peelOff x).1
          (maxOffList (xs ++ ys)) =
        max (max (peelOff x).1
          (maxOffList xs)) (maxOffList ys)
      rw [ih]
      exact (Nat.max_assoc
        (peelOff x).1 (maxOffList xs)
        (maxOffList ys)).symm

def splitPref : List Level → List Level →
    List Level × List Level × List Level
  | [], ys => ([], [], ys)
  | xs, [] => ([], xs, [])
  | x :: xs, y :: ys =>
      match decide (x = y) with
      | true =>
          let p := splitPref xs ys
          (x :: p.1, p.2.1, p.2.2)
      | false => ([], x :: xs, y :: ys)

theorem splitPref_append (xs ys : List Level) :
    xs = (splitPref xs ys).1 ++
      (splitPref xs ys).2.1 ∧
    ys = (splitPref xs ys).1 ++
      (splitPref xs ys).2.2 := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp only [splitPref]
          exact ⟨rfl, rfl⟩
      | cons _ _ =>
          simp only [splitPref]
          exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [splitPref]
          exact ⟨rfl, rfl⟩
      | cons y ys =>
          cases heq : decide (x = y) with
          | false =>
              simp only [splitPref, heq]
              exact ⟨rfl, rfl⟩
          | true =>
              have hxy : x = y :=
                of_decide_eq_true heq
              have ih' := ih ys
              simp only [splitPref, heq]
              have hp1 :
                  (x :: (splitPref xs ys).1) ++
                    (splitPref xs ys).2.1 =
                  x :: ((splitPref xs ys).1 ++
                    (splitPref xs ys).2.1) :=
                rfl
              have hp2 :
                  (x :: (splitPref xs ys).1) ++
                    (splitPref xs ys).2.2 =
                  x :: ((splitPref xs ys).1 ++
                    (splitPref xs ys).2.2) :=
                rfl
              constructor
              · rw [hp1, ← ih'.left]
              · rw [hp2, hxy, ← ih'.right]

theorem splitPref_heads_ne (xs ys : List Level)
    (x : Level) (xs' : List Level)
    (y : Level) (ys' : List Level)
    (hl : (splitPref xs ys).2.1 = x :: xs')
    (hr : (splitPref xs ys).2.2 = y :: ys') :
    decide (x = y) = false := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp only [splitPref] at hl
          exact List.noConfusion hl
      | cons _ _ =>
          simp only [splitPref] at hl
          exact List.noConfusion hl
  | cons a as ih =>
      cases ys with
      | nil =>
          simp only [splitPref] at hr
          exact List.noConfusion hr
      | cons b bs =>
          cases heq : decide (a = b) with
          | false =>
              simp only [splitPref, heq] at hl hr
              injection hl with hxa _
              injection hr with hyb _
              rw [← hxa, ← hyb]
              exact heq
          | true =>
              simp only [splitPref, heq] at hl hr
              exact ih bs hl hr

theorem memLevel_append_left (x : Level) :
    ∀ xs ys : List Level,
      memLevel x xs = true →
        memLevel x (xs ++ ys) = true
  | [], _, hm => Bool.noConfusion hm
  | a :: as, ys, hm => by
      cases heq : decide (x = a) with
      | true =>
          simp only [List.cons_append, memLevel,
            heq]
      | false =>
          simp only [memLevel, heq] at hm
          simp only [List.cons_append, memLevel,
            heq]
          exact memLevel_append_left x as ys hm

theorem memLevel_append_right (x : Level) :
    ∀ xs ys : List Level,
      memLevel x ys = true →
        memLevel x (xs ++ ys) = true
  | [], ys, hm => hm
  | a :: as, ys, hm => by
      cases heq : decide (x = a) with
      | true =>
          simp only [List.cons_append, memLevel,
            heq]
      | false =>
          simp only [List.cons_append, memLevel,
            heq]
          exact memLevel_append_right x as ys hm

theorem memLevel_append_cons (x : Level)
    (rest : List Level) :
    ∀ vs : List Level,
      memLevel x (vs ++ x :: rest) = true
  | [] => memLevel_cons_self x rest
  | v :: vs => by
      cases heq : decide (x = v) with
      | true =>
          simp only [List.cons_append, memLevel,
            heq]
      | false =>
          simp only [List.cons_append, memLevel,
            heq]
          exact memLevel_append_cons x rest vs

theorem antichain_suffix_anyDom
    (x : Level) (rest : List Level) :
    ∀ pref : List Level,
      antichain (pref ++ x :: rest) = true →
        anyDominates x pref = false
  | [], _ => rfl
  | v :: vs, h => by
      have hnd :=
        antichain_noneDom v (vs ++ x :: rest) h
      have hmem :=
        memLevel_append_cons x rest vs
      have hdvx :=
        noneDominatedBy_mem v x
          (vs ++ x :: rest) hnd hmem
      have htl :=
        antichain_tail v (vs ++ x :: rest) h
      have ih :=
        antichain_suffix_anyDom x rest vs htl
      simp only [anyDominates, hdvx]
      exact ih

theorem sortedInc_suffix (x : Level)
    (rest : List Level) :
    ∀ pref : List Level,
      sortedInc (pref ++ x :: rest) = true →
        sortedInc (x :: rest) = true
  | [], h => h
  | v :: vs, h => by
      have htl :=
        sortedInc_tail v (vs ++ x :: rest) h
      exact sortedInc_suffix x rest vs htl

theorem antichain_suffix (x : Level)
    (rest : List Level) :
    ∀ pref : List Level,
      antichain (pref ++ x :: rest) = true →
        antichain (x :: rest) = true
  | [], h => h
  | v :: vs, h => by
      have htl :=
        antichain_tail v (vs ++ x :: rest) h
      exact antichain_suffix x rest vs htl

theorem allOffAtoms_append :
    ∀ xs ys : List Level,
      allOffAtoms (xs ++ ys) = true →
        allOffAtoms xs = true ∧
        allOffAtoms ys = true
  | [], ys, h => ⟨rfl, h⟩
  | x :: xs, ys, h => by
      have hx := allOffAtoms_head x (xs ++ ys) h
      have htl := allOffAtoms_tail x (xs ++ ys) h
      have ih := allOffAtoms_append xs ys htl
      constructor
      · simp only [allOffAtoms, hx]
        exact ih.left
      · exact ih.right

theorem evalMaxListTotal_zero :
    ∀ xs : List Level,
      allOffAtoms xs = true →
        evalMaxListTotal (fun _ => 0) xs =
          maxOffList xs
  | [], _ => rfl
  | x :: xs, h => by
      have hx := allOffAtoms_head x xs h
      have htl := allOffAtoms_tail x xs h
      have ih := evalMaxListTotal_zero xs htl
      have he := evalTotal_zero_off x hx
      simp only [evalMaxListTotal, maxOffList]
      rw [he, ih]

theorem lt_add_of_lt {a N k : Nat}
    (h : a < N) : a < N + k :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right N k)

theorem max_eq_left_of_lt {a b : Nat}
    (h : b < a) : max a b = a :=
  Nat.max_eq_left (Nat.le_of_lt h)

theorem dominates_param_total
    (u v : Level) (i nu nv : Nat)
    (hu : peelOff u = (nu, .param i))
    (hv : peelOff v = (nv, .param i)) :
    dominates u v = true ∨
      dominates v u = true := by
  cases Nat.le_total nv nu with
  | inl h =>
      have hd :=
        dominates_same_param u v i nu nv hu hv
      rw [decide_eq_true h] at hd
      exact Or.inl hd
  | inr h =>
      have hd :=
        dominates_same_param v u i nv nu hv hu
      rw [decide_eq_true h] at hd
      exact Or.inr hd

theorem no_tail_same_param
    (i k : Nat) (x : Level) (xs : List Level)
    (hx : peelOff x = (k, .param i))
    (hanti : antichain (x :: xs) = true)
    (hoff : allOffAtoms xs = true)
    (y : Level) (hm : memLevel y xs = true) :
    match (peelOff y).2 with
    | .param j => decide (j = i) = false
    | _ => True := by
  cases hpeel : peelOff y with
  | mk n b =>
      cases b with
      | param j =>
          cases hji : decide (j = i) with
          | false =>
              simp only [hpeel]
              exact hji
          | true =>
              have hji' : j = i :=
                of_decide_eq_true hji
              have hy :
                  peelOff y = (n, .param i) := by
                rw [hpeel, hji']
              have htot :=
                dominates_param_total x y i k n
                  hx hy
              cases htot with
              | inl hxy =>
                  have hnd :=
                    antichain_noneDom x xs hanti
                  have hf :=
                    noneDominatedBy_mem x y xs
                      hnd hm
                  rw [hf] at hxy
                  exact Bool.noConfusion hxy
              | inr hyx =>
                  have ha :=
                    antichain_anyDom_false x xs
                      hanti
                  have hany :=
                    anyDominates_mem x y xs hm hyx
                  rw [hany] at ha
                  exact Bool.noConfusion ha
      | zero => trivial
      | succ _ => trivial
      | max _ _ => trivial
      | imax _ _ => trivial

theorem paramOff_cons_hit
    (i k : Nat) (x : Level) (xs : List Level)
    (h : peelOff x = (k, .param i)) :
    paramOff i (x :: xs) = some k := by
  simp only [paramOff]
  rw [h]
  simp only [Prod.snd, Prod.fst]
  cases hd : decide (i = i) with
  | false =>
      exact False.elim
        (of_decide_eq_false hd (Eq.refl i))
  | true => rfl

theorem paramOff_cons_miss
    (i : Nat) (x : Level) (xs : List Level)
    (h : match (peelOff x).2 with
         | .param j => decide (j = i) = false
         | _ => True) :
    paramOff i (x :: xs) = paramOff i xs := by
  simp only [paramOff]
  cases hb : (peelOff x).2 with
  | param j =>
      simp only [hb] at h
      simp only [h]
  | zero => rfl
  | succ _ => rfl
  | max _ _ => rfl
  | imax _ _ => rfl

theorem paramOff_of_mem (i k : Nat)
    (x : Level) :
    ∀ xs : List Level,
      antichain xs = true →
      allOffAtoms xs = true →
      memLevel x xs = true →
      peelOff x = (k, .param i) →
        paramOff i xs = some k
  | [], _, _, hm, _ => Bool.noConfusion hm
  | y :: ys, hanti, hoff, hm, hx => by
      have htl :=
        allOffAtoms_tail y ys hoff
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          rw [← hxy]
          exact paramOff_cons_hit i k x ys hx
      | false =>
          simp only [memLevel, heq] at hm
          have hanti' :=
            antichain_tail y ys hanti
          have ih :=
            paramOff_of_mem i k x ys
              hanti' htl hm hx
          cases hpeel : peelOff y with
          | mk n b =>
              cases b with
              | param j =>
                  cases hji : decide (j = i) with
                  | true =>
                      have hji' : j = i :=
                        of_decide_eq_true hji
                      have hy :
                          peelOff y =
                            (n, .param i) := by
                        rw [hpeel, hji']
                      have hbad :=
                        no_tail_same_param i n
                          y ys hy hanti htl x hm
                      rw [hx] at hbad
                      simp only [Prod.snd] at hbad
                      have ht :
                          decide True = true :=
                        decide_eq_true True.intro
                      rw [ht] at hbad
                      exact Bool.noConfusion hbad
                  | false =>
                      have hmiss :=
                        paramOff_cons_miss i y ys
                          (by
                            simp only [hpeel]
                            exact hji)
                      rw [hmiss]
                      exact ih
              | zero =>
                  have hmiss :=
                    paramOff_cons_miss i y ys
                      (by simp only [hpeel])
                  rw [hmiss]
                  exact ih
              | succ _ =>
                  have hmiss :=
                    paramOff_cons_miss i y ys
                      (by simp only [hpeel])
                  rw [hmiss]
                  exact ih
              | max _ _ =>
                  have hmiss :=
                    paramOff_cons_miss i y ys
                      (by simp only [hpeel])
                  rw [hmiss]
                  exact ih
              | imax _ _ =>
                  have hmiss :=
                    paramOff_cons_miss i y ys
                      (by simp only [hpeel])
                  rw [hmiss]
                  exact ih

theorem paramOff_none_of_no_param (i : Nat) :
    ∀ xs : List Level,
      (∀ y, memLevel y xs = true →
        match (peelOff y).2 with
        | .param j => decide (j = i) = false
        | _ => True) →
        paramOff i xs = none
  | [], _ => rfl
  | x :: xs, h => by
      have hx := h x (memLevel_cons_self x xs)
      have htl :
          ∀ y, memLevel y xs = true →
            match (peelOff y).2 with
            | .param j =>
                decide (j = i) = false
            | _ => True :=
        fun y hm =>
          h y (memLevel_cons_tail x y xs hm)
      have ih :=
        paramOff_none_of_no_param i xs htl
      have hmiss :=
        paramOff_cons_miss i x xs hx
      rw [hmiss]
      exact ih

theorem paramOff_tail_none_of_head_param
    (i k : Nat) (x : Level)
    (xs : List Level)
    (hx : peelOff x = (k, .param i))
    (hanti : antichain (x :: xs) = true)
    (hoff : allOffAtoms xs = true) :
    paramOff i xs = none :=
  paramOff_none_of_no_param i xs
    (fun y hm =>
      no_tail_same_param i k x xs hx
        hanti hoff y hm)

theorem maxOffList_tail_lt (x : Level)
    (xs : List Level) (N : Nat)
    (h : maxOffList (x :: xs) < N) :
    maxOffList xs < N :=
  Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h

theorem maxOffList_head_lt (x : Level)
    (xs : List Level) (N : Nat)
    (h : maxOffList (x :: xs) < N) :
    (peelOff x).1 < N :=
  Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h

theorem evalTotal_spike_of_peel_param
    (i N k : Nat) (x : Level)
    (h : peelOff x = (k, .param i)) :
    evalTotal (spike i N) x = N + k := by
  have hr := peel_reconstruct x
  rw [h] at hr
  rw [← hr]
  exact evalTotal_spike_param i N k

theorem paramOff_head_miss_decide
    (i : Nat) (x : Level)
    (xs : List Level)
    (hp : paramOff i (x :: xs) = none) :
    match (peelOff x).2 with
    | .param j => decide (j = i) = false
    | _ => True := by
  cases hb : (peelOff x).2 with
  | param j =>
      simp only [paramOff, hb] at hp
      cases hd : decide (j = i) with
      | true =>
          simp only [hd] at hp
          exact Option.noConfusion hp
      | false => exact hd
  | zero => trivial
  | succ _ => trivial
  | max _ _ => trivial
  | imax _ _ => trivial

theorem evalTotal_spike_of_peel_other
    (i N : Nat) (x : Level)
    (hx : isOffAtom x = true)
    (h : match (peelOff x).2 with
         | .param j => decide (j = i) = false
         | _ => True) :
    evalTotal (spike i N) x =
      (peelOff x).1 := by
  have he := evalTotal_spike_off i N x hx
  cases hpeel : peelOff x with
  | mk n b =>
      rw [hpeel] at he h
      rw [he]
      cases b with
      | param j =>
          simp only [h]
          exact Nat.add_zero n
      | zero => exact Nat.add_zero n
      | succ _ =>
          simp only [isOffAtom, hpeel] at hx
          exact Bool.noConfusion hx
      | max _ _ =>
          simp only [isOffAtom, hpeel] at hx
          exact Bool.noConfusion hx
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at hx
          exact Bool.noConfusion hx

theorem spike_miss_lt (i N : Nat) :
    ∀ xs : List Level,
      allOffAtoms xs = true →
      maxOffList xs < N →
      paramOff i xs = none →
        evalMaxListTotal (spike i N) xs < N
  | [], _, hN, _ =>
      Nat.lt_of_le_of_lt (Nat.zero_le _) hN
  | x :: xs, hoff, hN, hp => by
      have hx := allOffAtoms_head x xs hoff
      have htl := allOffAtoms_tail x xs hoff
      have hNtl := maxOffList_tail_lt x xs N hN
      have hne :=
        paramOff_head_miss_decide i x xs hp
      have hmiss :=
        paramOff_cons_miss i x xs hne
      rw [hmiss] at hp
      have ih :=
        spike_miss_lt i N xs htl hNtl hp
      have hex :=
        evalTotal_spike_of_peel_other i N x
          hx hne
      have hxn :=
        maxOffList_head_lt x xs N hN
      have hxl :
          evalTotal (spike i N) x < N := by
        rw [hex]
        exact hxn
      exact max_lt_of hxl ih

theorem spike_has_param (i N k : Nat) :
    ∀ xs : List Level,
      antichain xs = true →
      allOffAtoms xs = true →
      maxOffList xs < N →
      paramOff i xs = some k →
        evalMaxListTotal (spike i N) xs =
          N + k
  | [], _, _, _, hp =>
      Option.noConfusion hp
  | x :: xs, hanti, hoff, hN, hp => by
      have hxoff :=
        allOffAtoms_head x xs hoff
      have htl :=
        allOffAtoms_tail x xs hoff
      have hanti' :=
        antichain_tail x xs hanti
      have hNtl :=
        maxOffList_tail_lt x xs N hN
      cases hpeel : peelOff x with
      | mk n b =>
          cases b with
          | param j =>
              cases hji : decide (j = i) with
              | true =>
                  have hji' : j = i :=
                    of_decide_eq_true hji
                  have hxpeel :
                      peelOff x =
                        (n, .param i) := by
                    rw [hpeel, hji']
                  have hp' :=
                    paramOff_cons_hit i n x xs
                      hxpeel
                  rw [hp'] at hp
                  injection hp with hk
                  have hex :=
                    evalTotal_spike_of_peel_param
                      i N n x hxpeel
                  have hnone :=
                    paramOff_tail_none_of_head_param
                      i n x xs hxpeel hanti htl
                  have htlN :=
                    spike_miss_lt i N xs htl
                      hNtl hnone
                  have htlk :
                      evalMaxListTotal
                        (spike i N) xs
                        < N + n :=
                    lt_add_of_lt htlN
                  simp only [evalMaxListTotal]
                  rw [hex, ← hk]
                  exact max_eq_left_of_lt htlk
              | false =>
                  have hne :
                      match (peelOff x).2 with
                      | .param j =>
                          decide (j = i) = false
                      | _ => True := by
                    simp only [hpeel]
                    exact hji
                  have hmiss :=
                    paramOff_cons_miss i x xs hne
                  rw [hmiss] at hp
                  have ih :=
                    spike_has_param i N k xs
                      hanti' htl hNtl hp
                  have hex :=
                    evalTotal_spike_of_peel_other
                      i N x hxoff hne
                  have hxn :=
                    maxOffList_head_lt x xs N hN
                  have hxl :
                      evalTotal (spike i N) x
                        < N := by
                    rw [hex]
                    exact hxn
                  have hxlk :
                      evalTotal (spike i N) x
                        < N + k :=
                    lt_add_of_lt hxl
                  simp only [evalMaxListTotal]
                  rw [hex, ih]
                  exact Nat.max_eq_right
                    (Nat.le_of_lt (lt_add_of_lt hxn))
          | zero =>
              have hne :
                  match (peelOff x).2 with
                  | .param j =>
                      decide (j = i) = false
                  | _ => True := by
                simp only [hpeel]
              have hmiss :=
                paramOff_cons_miss i x xs hne
              rw [hmiss] at hp
              have ih :=
                spike_has_param i N k xs
                  hanti' htl hNtl hp
              have hex :=
                evalTotal_spike_of_peel_other
                  i N x hxoff hne
              have hxn :=
                maxOffList_head_lt x xs N hN
              have hxl :
                  evalTotal (spike i N) x
                    < N := by
                rw [hex]
                exact hxn
              have hxlk :
                  evalTotal (spike i N) x
                    < N + k :=
                lt_add_of_lt hxl
              simp only [evalMaxListTotal]
              rw [hex, ih]
              exact Nat.max_eq_right
                (Nat.le_of_lt (lt_add_of_lt hxn))
          | succ _ =>
              simp only [isOffAtom, hpeel] at hxoff
              exact Bool.noConfusion hxoff
          | max _ _ =>
              simp only [isOffAtom, hpeel] at hxoff
              exact Bool.noConfusion hxoff
          | imax _ _ =>
              simp only [isOffAtom, hpeel] at hxoff
              exact Bool.noConfusion hxoff

theorem maxOffList_le_left (xs ys : List Level) :
    maxOffList xs ≤
      maxOffList (xs ++ ys) := by
  rw [maxOffList_append]
  exact Nat.le_max_left _ _

theorem maxOffList_le_right (xs ys : List Level) :
    maxOffList ys ≤
      maxOffList (xs ++ ys) := by
  rw [maxOffList_append]
  exact Nat.le_max_right _ _

theorem splitPref_both_nil (xs ys : List Level)
    (hl : (splitPref xs ys).2.1 = [])
    (hr : (splitPref xs ys).2.2 = []) :
    xs = ys := by
  have h := splitPref_append xs ys
  rw [hl, hr] at h
  exact h.left.trans h.right.symm

theorem others_not_dom (a : Level) :
    ∀ xs : List Level,
      antichain xs = true →
      memLevel a xs = true →
      ∀ y, memLevel y xs = true →
        decide (y = a) = false →
          dominates y a = false
  | [], _, hm, y, _, _ =>
      Bool.noConfusion hm
  | x :: xs, hanti, hm, y, hym, hne => by
      cases heqa : decide (a = x) with
      | true =>
          have hax : a = x :=
            of_decide_eq_true heqa
          have ha :=
            antichain_anyDom_false x xs hanti
          cases heqy : decide (y = x) with
          | true =>
              have hyx : y = x :=
                of_decide_eq_true heqy
              rw [hyx, ← hax] at hne
              have ht :
                  decide (a = a) = true :=
                decide_eq_true (Eq.refl a)
              rw [ht] at hne
              exact Bool.noConfusion hne
          | false =>
              simp only [memLevel, heqy] at hym
              have hd :=
                anyDominates_false_mem x y xs
                  ha hym
              rw [hax]
              exact hd
      | false =>
          simp only [memLevel, heqa] at hm
          have hanti' :=
            antichain_tail x xs hanti
          cases heqy : decide (y = x) with
          | true =>
              have hyx : y = x :=
                of_decide_eq_true heqy
              have hnd :=
                antichain_noneDom x xs hanti
              have hd :=
                noneDominatedBy_mem x a xs
                  hnd hm
              rw [hyx]
              exact hd
          | false =>
              simp only [memLevel, heqy] at hym
              exact others_not_dom a xs
                hanti' hm y hym hne

theorem spike_sep_param
    (i k N : Nat) (xs ys : List Level)
    (hax : antichain xs = true)
    (hox : allOffAtoms xs = true)
    (hay : antichain ys = true)
    (hoy : allOffAtoms ys = true)
    (hNx : maxOffList xs < N)
    (hNy : maxOffList ys < N)
    (hxs : paramOff i xs = some k)
    (hys : paramOff i ys ≠ some k) :
    evalMaxListTotal (spike i N) xs ≠
      evalMaxListTotal (spike i N) ys := by
  have hxev :=
    spike_has_param i N k xs hax hox hNx hxs
  rw [hxev]
  cases hp : paramOff i ys with
  | none =>
      have hlt :=
        spike_miss_lt i N ys hoy hNy hp
      intro heq
      have hlt' : N + k < N := by
        rw [heq]
        exact hlt
      exact Nat.lt_irrefl N
        (Nat.lt_of_le_of_lt
          (Nat.le_add_right N k) hlt')
  | some k' =>
      have hyev :=
        spike_has_param i N k' ys hay hoy
          hNy hp
      rw [hyev]
      intro heq
      have hk : k = k' :=
        Nat.add_left_cancel heq
      have hp' : paramOff i ys = some k := by
        rw [hp, hk]
      exact hys hp'

theorem nonempty_eval_pos
    (x : Level) (xs : List Level)
    (ha : isCanonAtom x = true)
    (hf : imaxFree x = true) :
    0 < evalMaxListTotal (fun _ => 1)
      (x :: xs) :=
  Nat.lt_of_lt_of_le
    (evalTotal_canonAtom_pos x ha hf)
    (Nat.le_max_left _ _)

theorem allCanonAtoms_head_off
    (x : Level) (xs : List Level)
    (h : allCanonAtoms (x :: xs) = true) :
    isCanonAtom x = true :=
  allCanonAtoms_head x xs h

theorem imaxFree_of_offAtom (l : Level)
    (h : isOffAtom l = true) :
    imaxFree l = true := by
  induction l with
  | zero => rfl
  | param _ => rfl
  | succ l ih =>
      simp only [imaxFree]
      cases hl : isOffAtom l with
      | true => exact ih hl
      | false =>
          simp only [isOffAtom, peelOff] at h
          cases hpeel : peelOff l with
          | mk n b =>
              simp only [hpeel] at h
              cases b with
              | zero =>
                  simp only [isOffAtom, hpeel]
                    at hl
                  exact Bool.noConfusion hl
              | param _ =>
                  simp only [isOffAtom, hpeel]
                    at hl
                  exact Bool.noConfusion hl
              | succ _ => exact Bool.noConfusion h
              | max _ _ =>
                  exact Bool.noConfusion h
              | imax _ _ =>
                  exact Bool.noConfusion h
  | max _ _ =>
      simp only [isOffAtom, peelOff] at h
      exact Bool.noConfusion h
  | imax _ _ =>
      simp only [isOffAtom, peelOff] at h
      exact Bool.noConfusion h

theorem canon_off_const_pos (a : Level)
    (k : Nat)
    (ha : isCanonAtom a = true)
    (h : peelOff a = (k, .zero)) : 0 < k := by
  cases hk : k with
  | zero =>
      have hr := peel_reconstruct a
      rw [h, hk] at hr
      have ha0 : a = .zero := by
        simp only [wrapSucc] at hr
        exact hr.symm
      rw [ha0] at ha
      exact Bool.noConfusion ha
  | succ n => exact Nat.zero_lt_succ n

theorem dominates_off_const
    (y a : Level) (k : Nat)
    (hy : isOffAtom y = true)
    (ha : peelOff a = (k, .zero)) :
    dominates y a =
      decide (k ≤ (peelOff y).1) := by
  cases hpeel : peelOff y with
  | mk n b =>
      cases b with
      | param i =>
          have hd :=
            dominates_param_const y a i n k
              hpeel ha
          simp only [hpeel, Prod.fst]
          exact hd
      | zero =>
          have hd :=
            dominates_const_const y a n k
              hpeel ha
          simp only [hpeel, Prod.fst]
          exact hd
      | succ _ =>
          simp only [isOffAtom, hpeel] at hy
          exact Bool.noConfusion hy
      | max _ _ =>
          simp only [isOffAtom, hpeel] at hy
          exact Bool.noConfusion hy
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at hy
          exact Bool.noConfusion hy

theorem maxOff_lt_of_not_dom_const
    (a : Level) (k : Nat) :
    ∀ ys : List Level,
      peelOff a = (k, .zero) →
      anyDominates a ys = false →
      allOffAtoms ys = true →
      0 < k →
        maxOffList ys < k
  | [], _, _, _, hk => hk
  | y :: ys, ha, hnd, hoff, hk => by
      have hy :=
        allOffAtoms_head y ys hoff
      have htl :=
        allOffAtoms_tail y ys hoff
      simp only [anyDominates] at hnd
      cases hd : dominates y a with
      | true =>
          rw [hd] at hnd
          exact Bool.noConfusion hnd
      | false =>
          rw [hd] at hnd
          have hiy :=
            maxOff_lt_of_not_dom_const a k ys
              ha hnd htl hk
          have hdc :=
            dominates_off_const y a k hy ha
          rw [hdc] at hd
          have hle :
              decide
                (k ≤ (peelOff y).1) = false :=
            hd
          have hlt :
              (peelOff y).1 < k :=
            Nat.lt_of_not_le
              (of_decide_eq_false hle)
          exact max_lt_of hlt hiy

theorem allCanonAtoms_of_append :
    ∀ xs ys : List Level,
      allCanonAtoms (xs ++ ys) = true →
        allCanonAtoms xs = true ∧
        allCanonAtoms ys = true
  | [], ys, h => ⟨rfl, h⟩
  | x :: xs, ys, h => by
      have hx :=
        allCanonAtoms_head x (xs ++ ys) h
      have htl :=
        allCanonAtoms_tail x (xs ++ ys) h
      have ih :=
        allCanonAtoms_of_append xs ys htl
      constructor
      · simp only [allCanonAtoms, hx]
        exact ih.left
      · exact ih.right

theorem mem_of_paramOff (i k : Nat) :
    ∀ xs : List Level,
      paramOff i xs = some k →
        ∃ x, memLevel x xs = true ∧
          (peelOff x).2 = .param i ∧
          (peelOff x).1 = k
  | [], hp => Option.noConfusion hp
  | x :: xs, hp => by
      cases hb : (peelOff x).2 with
      | param j =>
          cases hji : decide (j = i) with
          | true =>
              simp only [paramOff, hb, hji] at hp
              refine ⟨x, ?_⟩
              constructor
              · exact memLevel_cons_self x xs
              · constructor
                · simp only [hb]
                  exact congrArg Level.param
                    (of_decide_eq_true hji)
                · injection hp with hk
          | false =>
              simp only [paramOff, hb, hji] at hp
              have ⟨z, hm, h2, h1⟩ :=
                mem_of_paramOff i k xs hp
              refine ⟨z, ?_⟩
              exact ⟨memLevel_cons_tail x z xs hm,
                h2, h1⟩
      | zero =>
          simp only [paramOff, hb] at hp
          have ⟨z, hm, h2, h1⟩ :=
            mem_of_paramOff i k xs hp
          refine ⟨z, ?_⟩
          exact ⟨memLevel_cons_tail x z xs hm,
            h2, h1⟩
      | succ _ =>
          simp only [paramOff, hb] at hp
          have ⟨z, hm, h2, h1⟩ :=
            mem_of_paramOff i k xs hp
          refine ⟨z, ?_⟩
          exact ⟨memLevel_cons_tail x z xs hm,
            h2, h1⟩
      | max _ _ =>
          simp only [paramOff, hb] at hp
          have ⟨z, hm, h2, h1⟩ :=
            mem_of_paramOff i k xs hp
          refine ⟨z, ?_⟩
          exact ⟨memLevel_cons_tail x z xs hm,
            h2, h1⟩
      | imax _ _ =>
          simp only [paramOff, hb] at hp
          have ⟨z, hm, h2, h1⟩ :=
            mem_of_paramOff i k xs hp
          refine ⟨z, ?_⟩
          exact ⟨memLevel_cons_tail x z xs hm,
            h2, h1⟩

theorem peel_eq_of_parts (x : Level)
    (k : Nat) (i : Nat)
    (h1 : (peelOff x).1 = k)
    (h2 : (peelOff x).2 = .param i) :
    peelOff x = (k, .param i) := by
  cases hpeel : peelOff x with
  | mk n b =>
      simp only [hpeel] at h1 h2
      rw [h1, h2]

theorem sortedInc_asymm_mem
    (a b : Level) (as bs : List Level)
    (hsa : sortedInc (a :: as) = true)
    (hsb : sortedInc (b :: bs) = true)
    (hma : memLevel b as = true)
    (hmb : memLevel a bs = true) : False := by
  have hlt1 :=
    sortedInc_mem_lt a as hsa b hma
  have hlt2 :=
    sortedInc_mem_lt b bs hsb a hmb
  have hf := levelLt_asymm a b hlt1
  rw [hf] at hlt2
  exact Bool.noConfusion hlt2

theorem not_mem_pref_of_suffix
    (a : Level) (rest pref : List Level)
    (hanti : antichain
      (pref ++ a :: rest) = true) :
    memLevel a pref = false := by
  cases hm : memLevel a pref with
  | false => rfl
  | true =>
      have hnd :=
        antichain_suffix_anyDom a rest pref
          hanti
      have hd :=
        anyDominates_false_mem a a pref
          hnd hm
      have hr := dominates_refl a
      rw [hr] at hd
      exact Bool.noConfusion hd

theorem extra_param_sep
    (a : Level) (i k N : Nat)
    (xs ys : List Level)
    (hax : antichain xs = true)
    (hox : allOffAtoms xs = true)
    (hay : antichain ys = true)
    (hoy : allOffAtoms ys = true)
    (hNx : maxOffList xs < N)
    (hNy : maxOffList ys < N)
    (ha : peelOff a = (k, .param i))
    (haoff : isOffAtom a = true)
    (hmem : memLevel a ys = true)
    (hnmem : memLevel a xs = false)
    (h : evalMaxListTotal (spike i N) xs =
      evalMaxListTotal (spike i N) ys) :
    False := by
  have hpys :=
    paramOff_of_mem i k a ys hay hoy hmem ha
  have hne : paramOff i xs ≠ some k := by
    intro hpxs
    have ⟨z, hmz, hz2, hz1⟩ :=
      mem_of_paramOff i k xs hpxs
    have hzoff :=
      allOffAtoms_mem z xs hox hmz
    have hzpeel :=
      peel_eq_of_parts z k i hz1 hz2
    have zeq :=
      offAtom_eq_of_peel a z haoff hzoff
        (ha.trans hzpeel.symm)
    rw [← zeq] at hmz
    rw [hnmem] at hmz
    exact Bool.noConfusion hmz
  exact spike_sep_param i k N ys xs
    hay hoy hax hox hNy hNx hpys hne h.symm

theorem extra_const_sep
    (a : Level) (k : Nat)
    (pref : List Level)
    (xs ys : List Level)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .zero))
    (hcan : isCanonAtom a = true)
    (hnd : anyDominates a pref = false)
    (hop : allOffAtoms pref = true)
    (hxsm : maxOffList xs = maxOffList pref)
    (hley : k ≤ maxOffList ys)
    (h : evalMaxListTotal (fun _ => 0) xs =
      evalMaxListTotal (fun _ => 0) ys) :
    False := by
  have hk0 :=
    canon_off_const_pos a k hcan ha
  have hlt :=
    maxOff_lt_of_not_dom_const a k pref
      ha hnd hop hk0
  have hxz := evalMaxListTotal_zero xs hox
  have hyz := evalMaxListTotal_zero ys hoy
  rw [hxz, hyz, hxsm] at h
  rw [h] at hlt
  exact Nat.lt_irrefl (maxOffList ys)
    (Nat.lt_of_lt_of_le hlt hley)

theorem memLevel_append_or (x : Level) :
    ∀ xs ys : List Level,
      memLevel x (xs ++ ys) = true →
        memLevel x xs = true ∨
          memLevel x ys = true
  | [], ys, h => Or.inr h
  | a :: as, ys, h => by
      cases heq : decide (x = a) with
      | true =>
          simp only [List.cons_append, memLevel,
            heq]
          exact Or.inl True.intro
      | false =>
          simp only [List.cons_append, memLevel,
            heq] at h
          cases memLevel_append_or x as ys h with
          | inl hp =>
              simp only [memLevel, heq]
              exact Or.inl hp
          | inr hq => exact Or.inr hq

theorem extra_const_not_dom
    (a : Level) (k : Nat)
    (xs ys : List Level)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .zero))
    (hcan : isCanonAtom a = true)
    (hnd : anyDominates a ys = false)
    (hmem : memLevel a xs = true)
    (h : evalMaxListTotal (fun _ => 0) xs =
      evalMaxListTotal (fun _ => 0) ys) :
    False := by
  have hk0 :=
    canon_off_const_pos a k hcan ha
  have hlt :=
    maxOff_lt_of_not_dom_const a k ys
      ha hnd hoy hk0
  have hlex :
      k ≤ maxOffList xs := by
    have hp := peel_le_maxOffList a xs hmem
    simp only [ha, Prod.fst] at hp
    exact hp
  have hxz := evalMaxListTotal_zero xs hox
  have hyz := evalMaxListTotal_zero ys hoy
  rw [hxz, hyz] at h
  rw [← h] at hlt
  exact Nat.lt_irrefl (maxOffList xs)
    (Nat.lt_of_lt_of_le hlt hlex)

theorem anyDominates_append (u : Level) :
    ∀ xs ys : List Level,
      anyDominates u (xs ++ ys) =
        match anyDominates u xs with
        | true => true
        | false => anyDominates u ys
  | [], ys => rfl
  | x :: xs, ys => by
      simp only [List.cons_append, anyDominates]
      cases hd : dominates x u with
      | true => rfl
      | false =>
          exact anyDominates_append u xs ys

theorem mem_cons_of_ne (x y : Level)
    (xs : List Level)
    (hne : decide (x = y) = false)
    (h : memLevel x (y :: xs) = true) :
    memLevel x xs = true := by
  simp only [memLevel, hne] at h
  exact h



theorem sep_nil_cons
    (xs ys : List Level) (a : Level)
    (rest : List Level) (N : Nat)
    (hax : antichain xs = true)
    (hox : allOffAtoms xs = true)
    (hay : antichain ys = true)
    (hoy : allOffAtoms ys = true)
    (hcy : allCanonAtoms ys = true)
    (hNx : maxOffList xs < N)
    (hNy : maxOffList ys < N)
    (happ_l : xs = (splitPref xs ys).1 ++ [])
    (happ_r : ys =
      (splitPref xs ys).1 ++ a :: rest)
    (h : ∀ σ : Nat → Nat,
      evalMaxListTotal σ xs =
        evalMaxListTotal σ ys) : False := by
  have hantiY : antichain
      ((splitPref xs ys).1 ++ a :: rest) =
        true := by
    rw [← happ_r]; exact hay
  have hnmem : memLevel a xs = false := by
    rw [happ_l]
    simp only [List.append_nil]
    exact not_mem_pref_of_suffix a rest
      (splitPref xs ys).1 hantiY
  have hmem : memLevel a ys = true := by
    rw [happ_r]
    exact memLevel_append_cons a rest
      (splitPref xs ys).1
  have hoffY :=
    allOffAtoms_append (splitPref xs ys).1
      (a :: rest)
      (by rw [← happ_r]; exact hoy)
  have haoff :=
    allOffAtoms_head a rest hoffY.right
  have hcan :=
    allCanonAtoms_head a rest
      (allCanonAtoms_of_append
        (splitPref xs ys).1 (a :: rest)
        (by rw [← happ_r]; exact hcy)).right
  cases hpeel : peelOff a with
  | mk k b =>
      cases b with
      | param i =>
          exact extra_param_sep a i k N xs ys
            hax hox hay hoy hNx hNy hpeel
            haoff hmem hnmem (h _)
      | zero =>
          have hnd :=
            antichain_suffix_anyDom a rest
              (splitPref xs ys).1 hantiY
          have hnd' : anyDominates a xs =
              false := by
            rw [happ_l]
            simp only [List.append_nil]
            exact hnd
          exact extra_const_not_dom a k ys xs
            hoy hox hpeel hcan hnd' hmem
            (h _).symm
      | succ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff
      | max _ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff


theorem sep_cons_nil
    (xs ys : List Level) (a : Level)
    (rest : List Level) (N : Nat)
    (hax : antichain xs = true)
    (hox : allOffAtoms xs = true)
    (hcx : allCanonAtoms xs = true)
    (hay : antichain ys = true)
    (hoy : allOffAtoms ys = true)
    (hNx : maxOffList xs < N)
    (hNy : maxOffList ys < N)
    (happ_l : xs =
      (splitPref xs ys).1 ++ a :: rest)
    (happ_r : ys = (splitPref xs ys).1 ++ [])
    (h : ∀ σ : Nat → Nat,
      evalMaxListTotal σ xs =
        evalMaxListTotal σ ys) : False := by
  have hantiX : antichain
      ((splitPref xs ys).1 ++ a :: rest) =
        true := by
    rw [← happ_l]; exact hax
  have hnmem : memLevel a ys = false := by
    rw [happ_r]
    simp only [List.append_nil]
    exact not_mem_pref_of_suffix a rest
      (splitPref xs ys).1 hantiX
  have hmem : memLevel a xs = true := by
    rw [happ_l]
    exact memLevel_append_cons a rest
      (splitPref xs ys).1
  have hoffX :=
    allOffAtoms_append (splitPref xs ys).1
      (a :: rest)
      (by rw [← happ_l]; exact hox)
  have haoff :=
    allOffAtoms_head a rest hoffX.right
  have hcan :=
    allCanonAtoms_head a rest
      (allCanonAtoms_of_append
        (splitPref xs ys).1 (a :: rest)
        (by rw [← happ_l]; exact hcx)).right
  cases hpeel : peelOff a with
  | mk k b =>
      cases b with
      | param i =>
          exact extra_param_sep a i k N ys xs
            hay hoy hax hox hNy hNx hpeel
            haoff hmem hnmem (h _).symm
      | zero =>
          have hnd :=
            antichain_suffix_anyDom a rest
              (splitPref xs ys).1 hantiX
          have hnd' : anyDominates a ys =
              false := by
            rw [happ_r]
            simp only [List.append_nil]
            exact hnd
          exact extra_const_not_dom a k xs ys
            hox hoy hpeel hcan hnd' hmem (h _)
      | succ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff
      | max _ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff
      | imax _ _ =>
          simp only [isOffAtom, hpeel] at haoff
          exact Bool.noConfusion haoff


theorem flatten_canon_imaxFree (l : Level)
    (hc : IsCanon l)
    (hf : imaxFree l = true) :
    allCanonAtoms (flattenMax l) = true ∧
    sortedInc (flattenMax l) = true ∧
    antichain (flattenMax l) = true ∧
    allOffAtoms (flattenMax l) = true ∧
    maxOfList (flattenMax l) = l :=
  let d := isCanon_destruct l hc
  ⟨d.left, d.right.left, d.right.right.left,
    flatten_off_of_canon_imaxFree l hc hf,
    d.right.right.right⟩

/- Attempt 2 of canon_sep_imaxFree: first-diff
spike lemmas and prefix-extra (nil/cons,
cons/nil) closed. Remaining arm: cons/cons
of two nonempty remainders after splitPref
(the H-6i false.cons.cons, now at the first
difference of two sorted antichains).
Not declared (attempt 2 spent). R-SepPick
resets the counter: the first-diff pick
was wrong (cross-list dominance). -/

/-! H-6k R-SepPick (a): an undominated atom
exists on one side of two unequal sorted
off-atom antichains. -/

theorem dominates_trans_off
    (u v w : Level)
    (hu : isOffAtom u = true)
    (hv : isOffAtom v = true)
    (hw : isOffAtom w = true)
    (huv : dominates u v = true)
    (hvw : dominates v w = true) :
    dominates u w = true := by
  cases hpu : peelOff u with
  | mk nu bu =>
      cases hpv : peelOff v with
      | mk nv bv =>
          cases hpw : peelOff w with
          | mk nw bw =>
              cases bu with
              | param i =>
                  cases bv with
                  | param j =>
                      cases bw with
                      | param k =>
                          cases hij :
                              decide (i = j) with
                          | false =>
                              have hf :=
                                dominates_diff_param
                                  u v i j nu nv
                                  hij hpu hpv
                              rw [hf] at huv
                              exact Bool.noConfusion
                                huv
                          | true =>
                              have hij' : i = j :=
                                of_decide_eq_true hij
                              have hpv' :
                                  peelOff v =
                                    (nv, .param i) :=
                                by rw [hpv, hij']
                              have hduv :=
                                dominates_same_param
                                  u v i nu nv
                                  hpu hpv'
                              rw [hduv] at huv
                              have hnv :
                                  nv ≤ nu :=
                                of_decide_eq_true huv
                              cases hjk :
                                  decide (j = k) with
                              | false =>
                                  have hf :=
                                    dominates_diff_param
                                      v w j k nv nw
                                      hjk hpv hpw
                                  rw [hf] at hvw
                                  exact Bool.noConfusion
                                    hvw
                              | true =>
                                  have hjk' : j = k :=
                                    of_decide_eq_true hjk
                                  have hik : i = k :=
                                    hij'.trans hjk'
                                  have hpw' :
                                      peelOff w =
                                        (nw, .param i) :=
                                    by rw [hpw, hik]
                                  have hdvw :=
                                    dominates_same_param
                                      v w i nv nw
                                      hpv' hpw'
                                  rw [hdvw] at hvw
                                  have hnw :
                                      nw ≤ nv :=
                                    of_decide_eq_true hvw
                                  have hle :
                                      nw ≤ nu :=
                                    Nat.le_trans hnw hnv
                                  have hduw :=
                                    dominates_same_param
                                      u w i nu nw
                                      hpu hpw'
                                  rw [hduw]
                                  exact decide_eq_true
                                    hle
                      | zero =>
                          cases hij :
                              decide (i = j) with
                          | false =>
                              have hf :=
                                dominates_diff_param
                                  u v i j nu nv
                                  hij hpu hpv
                              rw [hf] at huv
                              exact Bool.noConfusion
                                huv
                          | true =>
                              have hij' : i = j :=
                                of_decide_eq_true hij
                              have hpv' :
                                  peelOff v =
                                    (nv, .param i) :=
                                by rw [hpv, hij']
                              have hduv :=
                                dominates_same_param
                                  u v i nu nv
                                  hpu hpv'
                              rw [hduv] at huv
                              have hnv :
                                  nv ≤ nu :=
                                of_decide_eq_true huv
                              have hdvw :=
                                dominates_param_const
                                  v w i nv nw
                                  hpv' hpw
                              rw [hdvw] at hvw
                              have hnw :
                                  nw ≤ nv :=
                                of_decide_eq_true hvw
                              have hle :
                                  nw ≤ nu :=
                                Nat.le_trans hnw hnv
                              have hduw :=
                                dominates_param_const
                                  u w i nu nw
                                  hpu hpw
                              rw [hduw]
                              exact decide_eq_true hle
                      | succ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | max _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | imax _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                  | zero =>
                      cases bw with
                      | param k =>
                          have hf :=
                            dominates_const_param
                              v w k nv nw
                              hpv hpw
                          rw [hf] at hvw
                          exact Bool.noConfusion hvw
                      | zero =>
                          have hduv :=
                            dominates_param_const
                              u v i nu nv
                              hpu hpv
                          rw [hduv] at huv
                          have hnv : nv ≤ nu :=
                            of_decide_eq_true huv
                          have hdvw :=
                            dominates_const_const
                              v w nv nw
                              hpv hpw
                          rw [hdvw] at hvw
                          have hnw : nw ≤ nv :=
                            of_decide_eq_true hvw
                          have hle : nw ≤ nu :=
                            Nat.le_trans hnw hnv
                          have hduw :=
                            dominates_param_const
                              u w i nu nw
                              hpu hpw
                          rw [hduw]
                          exact decide_eq_true hle
                      | succ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | max _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | imax _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                  | succ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
                  | max _ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
                  | imax _ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
              | zero =>
                  cases bv with
                  | param j =>
                      have hf :=
                        dominates_const_param
                          u v j nu nv
                          hpu hpv
                      rw [hf] at huv
                      exact Bool.noConfusion huv
                  | zero =>
                      cases bw with
                      | param k =>
                          have hf :=
                            dominates_const_param
                              v w k nv nw
                              hpv hpw
                          rw [hf] at hvw
                          exact Bool.noConfusion hvw
                      | zero =>
                          have hduv :=
                            dominates_const_const
                              u v nu nv
                              hpu hpv
                          rw [hduv] at huv
                          have hnv : nv ≤ nu :=
                            of_decide_eq_true huv
                          have hdvw :=
                            dominates_const_const
                              v w nv nw
                              hpv hpw
                          rw [hdvw] at hvw
                          have hnw : nw ≤ nv :=
                            of_decide_eq_true hvw
                          have hle : nw ≤ nu :=
                            Nat.le_trans hnw hnv
                          have hduw :=
                            dominates_const_const
                              u w nu nw
                              hpu hpw
                          rw [hduw]
                          exact decide_eq_true hle
                      | succ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | max _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                      | imax _ _ =>
                          simp only [isOffAtom, hpw]
                            at hw
                          exact Bool.noConfusion hw
                  | succ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
                  | max _ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
                  | imax _ _ =>
                      simp only [isOffAtom, hpv] at hv
                      exact Bool.noConfusion hv
              | succ _ =>
                  simp only [isOffAtom, hpu] at hu
                  exact Bool.noConfusion hu
              | max _ _ =>
                  simp only [isOffAtom, hpu] at hu
                  exact Bool.noConfusion hu
              | imax _ _ =>
                  simp only [isOffAtom, hpu] at hu
                  exact Bool.noConfusion hu

theorem dominates_antisymm_off
    (u v : Level)
    (hu : isOffAtom u = true)
    (hv : isOffAtom v = true)
    (huv : dominates u v = true)
    (hvu : dominates v u = true) :
    u = v := by
  cases hpu : peelOff u with
  | mk nu bu =>
      cases hpv : peelOff v with
      | mk nv bv =>
          cases bu with
          | param i =>
              cases bv with
              | param j =>
                  cases hij : decide (i = j) with
                  | false =>
                      have hf :=
                        dominates_diff_param
                          u v i j nu nv
                          hij hpu hpv
                      rw [hf] at huv
                      exact Bool.noConfusion huv
                  | true =>
                      have hij' : i = j :=
                        of_decide_eq_true hij
                      have hpv' :
                          peelOff v =
                            (nv, .param i) :=
                        by rw [hpv, hij']
                      have hduv :=
                        dominates_same_param
                          u v i nu nv hpu hpv'
                      rw [hduv] at huv
                      have hnv : nv ≤ nu :=
                        of_decide_eq_true huv
                      have hvu' :=
                        dominates_same_param
                          v u i nv nu hpv' hpu
                      rw [hvu'] at hvu
                      have hnu : nu ≤ nv :=
                        of_decide_eq_true hvu
                      have heq : nu = nv :=
                        Nat.le_antisymm hnu hnv
                      have hpeel :
                          peelOff u = peelOff v := by
                        rw [hpu, hpv', heq]
                      exact offAtom_eq_of_peel
                        u v hu hv hpeel
              | zero =>
                  have hf :=
                    dominates_const_param
                      v u i nv nu
                      hpv hpu
                  rw [hf] at hvu
                  exact Bool.noConfusion hvu
              | succ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
              | max _ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
              | imax _ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
          | zero =>
              cases bv with
              | param j =>
                  have hf :=
                    dominates_const_param
                      u v j nu nv
                      hpu hpv
                  rw [hf] at huv
                  exact Bool.noConfusion huv
              | zero =>
                  have hduv :=
                    dominates_const_const
                      u v nu nv hpu hpv
                  rw [hduv] at huv
                  have hnv : nv ≤ nu :=
                    of_decide_eq_true huv
                  have hvu' :=
                    dominates_const_const
                      v u nv nu hpv hpu
                  rw [hvu'] at hvu
                  have hnu : nu ≤ nv :=
                    of_decide_eq_true hvu
                  have heq : nu = nv :=
                    Nat.le_antisymm hnu hnv
                  have hpeel :
                      peelOff u = peelOff v := by
                    rw [hpu, hpv, heq]
                  exact offAtom_eq_of_peel
                    u v hu hv hpeel
              | succ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
              | max _ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
              | imax _ _ =>
                  simp only [isOffAtom, hpv] at hv
                  exact Bool.noConfusion hv
          | succ _ =>
              simp only [isOffAtom, hpu] at hu
              exact Bool.noConfusion hu
          | max _ _ =>
              simp only [isOffAtom, hpu] at hu
              exact Bool.noConfusion hu
          | imax _ _ =>
              simp only [isOffAtom, hpu] at hu
              exact Bool.noConfusion hu

theorem antichain_mem_not_dom
    (x y : Level) :
    ∀ xs : List Level,
      antichain xs = true →
      memLevel x xs = true →
      memLevel y xs = true →
      decide (x = y) = false →
        dominates x y = false
  | [], _, hx, _, _ => Bool.noConfusion hx
  | v :: vs, hanti, hx, hy, hne => by
      have htl := antichain_tail v vs hanti
      cases hex : decide (x = v) with
      | true =>
          have hxv : x = v :=
            of_decide_eq_true hex
          have hyv : decide (y = v) = false := by
            cases hd : decide (y = v) with
            | false => rfl
            | true =>
                have hyv' : y = v :=
                  of_decide_eq_true hd
                have hxy : x = y :=
                  hxv.trans hyv'.symm
                rw [decide_eq_true hxy] at hne
                exact Bool.noConfusion hne
          have hym :=
            mem_cons_of_ne y v vs hyv hy
          have hnd :=
            antichain_noneDom v vs hanti
          have hd :=
            noneDominatedBy_mem v y vs hnd hym
          rw [hxv]
          exact hd
      | false =>
          have hxm :=
            mem_cons_of_ne x v vs hex hx
          cases hey : decide (y = v) with
          | true =>
              have hyv : y = v :=
                of_decide_eq_true hey
              have ha :=
                antichain_anyDom_false v vs
                  hanti
              have hd :=
                anyDominates_false_mem v x vs
                  ha hxm
              rw [hyv]
              exact hd
          | false =>
              have hym :=
                mem_cons_of_ne y v vs hey hy
              exact antichain_mem_not_dom
                x y vs htl hxm hym hne

theorem antichain_dom_eq
    (xs : List Level) (l a : Level)
    (hanti : antichain xs = true)
    (hl : memLevel l xs = true)
    (ha : memLevel a xs = true)
    (hd : dominates l a = true) :
    l = a := by
  cases heq : decide (l = a) with
  | true => exact of_decide_eq_true heq
  | false =>
      have hnd :=
        antichain_mem_not_dom l a xs
          hanti hl ha heq
      rw [hnd] at hd
      exact Bool.noConfusion hd

def firstUndominated :
    List Level → List Level → Option Level
  | [], _ => none
  | a :: rest, ys =>
      match anyDominates a ys with
      | false => some a
      | true => firstUndominated rest ys

theorem firstUndominated_some
    (ys : List Level) (a : Level) :
    ∀ xs : List Level,
      firstUndominated xs ys = some a →
        memLevel a xs = true ∧
          anyDominates a ys = false
  | [], h => Option.noConfusion h
  | x :: xs, h => by
      cases hd : anyDominates x ys with
      | false =>
          simp only [firstUndominated, hd] at h
          injection h with ha
          rw [← ha]
          exact ⟨memLevel_cons_self x xs, hd⟩
      | true =>
          simp only [firstUndominated, hd] at h
          have ih :=
            firstUndominated_some ys a xs h
          exact ⟨memLevel_cons_tail x a xs
            ih.left, ih.right⟩

theorem firstUndominated_none
    (ys : List Level) :
    ∀ xs : List Level,
      firstUndominated xs ys = none →
        ∀ a, memLevel a xs = true →
          anyDominates a ys = true
  | [], _, a, hm => Bool.noConfusion hm
  | x :: xs, h, a, hm => by
      cases hd : anyDominates x ys with
      | false =>
          simp only [firstUndominated, hd] at h
          exact Option.noConfusion h
      | true =>
          simp only [firstUndominated, hd] at h
          cases heq : decide (a = x) with
          | true =>
              have hax : a = x :=
                of_decide_eq_true heq
              rw [hax]
              exact hd
          | false =>
              simp only [memLevel, heq] at hm
              exact firstUndominated_none
                ys xs h a hm

theorem mem_of_mutual_dom
    (xs ys : List Level)
    (hax : antichain xs = true)
    (hay : antichain ys = true)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (hxs : ∀ a, memLevel a xs = true →
      anyDominates a ys = true)
    (hys : ∀ b, memLevel b ys = true →
      anyDominates b xs = true)
    (a : Level)
    (hm : memLevel a xs = true) :
    memLevel a ys = true := by
  have haoff :=
    allOffAtoms_mem a xs hox hm
  have ⟨r, hmr, hdr⟩ :=
    anyDominates_exists a ys (hxs a hm)
  have hroff :=
    allOffAtoms_mem r ys hoy hmr
  have ⟨l, hml, hdl⟩ :=
    anyDominates_exists r xs (hys r hmr)
  have hloff :=
    allOffAtoms_mem l xs hox hml
  have hla :=
    dominates_trans_off l r a
      hloff hroff haoff hdl hdr
  have heq :=
    antichain_dom_eq xs l a hax hml hm hla
  have har : a = r :=
    dominates_antisymm_off a r
      haoff hroff (by rw [← heq]; exact hdl) hdr
  rw [har]
  exact hmr

theorem mem_iff_of_mutual_dom
    (xs ys : List Level)
    (hax : antichain xs = true)
    (hay : antichain ys = true)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (hxs : ∀ a, memLevel a xs = true →
      anyDominates a ys = true)
    (hys : ∀ b, memLevel b ys = true →
      anyDominates b xs = true)
    (a : Level) :
    memLevel a xs = memLevel a ys := by
  cases hxa : memLevel a xs with
  | true =>
      have hya :=
        mem_of_mutual_dom xs ys hax hay
          hox hoy hxs hys a hxa
      rw [hya]
  | false =>
      cases hya : memLevel a ys with
      | false => rfl
      | true =>
          have hxa' :=
            mem_of_mutual_dom ys xs hay hax
              hoy hox hys hxs a hya
          rw [hxa] at hxa'
          exact Bool.noConfusion hxa'

theorem not_mem_sorted_head
    (x : Level) (xs : List Level)
    (h : sortedInc (x :: xs) = true) :
    memLevel x xs = false := by
  cases hm : memLevel x xs with
  | false => rfl
  | true =>
      have hlt :=
        sortedInc_mem_lt x xs h x hm
      have hi := levelLt_irrefl x
      rw [hi] at hlt
      exact Bool.noConfusion hlt

theorem sorted_eq_of_mem_iff :
    ∀ xs ys : List Level,
      sortedInc xs = true →
      sortedInc ys = true →
      (∀ a, memLevel a xs =
        memLevel a ys) →
        xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => by
      have hy :
          memLevel y (y :: ys) = true :=
        memLevel_cons_self y ys
      have hx0 : memLevel y [] = false := rfl
      have hx : memLevel y [] =
          memLevel y (y :: ys) := h y
      rw [hx0, hy] at hx
      exact Bool.noConfusion hx
  | x :: xs, [], _, _, h => by
      have hx :
          memLevel x (x :: xs) = true :=
        memLevel_cons_self x xs
      have hy0 : memLevel x [] = false := rfl
      have hy : memLevel x (x :: xs) =
          memLevel x [] := h x
      rw [hx, hy0] at hy
      exact Bool.noConfusion hy
  | x :: xs, y :: ys, hsx, hsy, h => by
      have hsx' :=
        sortedInc_tail x xs hsx
      have hsy' :=
        sortedInc_tail y ys hsy
      have hxx :
          memLevel x (x :: xs) = true :=
        memLevel_cons_self x xs
      have hyy :
          memLevel y (y :: ys) = true :=
        memLevel_cons_self y ys
      have hxy_mem :
          memLevel x (y :: ys) = true := by
        have hx' : memLevel x (x :: xs) =
            memLevel x (y :: ys) := h x
        rw [hxx] at hx'
        exact hx'.symm
      have hyx_mem :
          memLevel y (x :: xs) = true := by
        have hy' : memLevel y (x :: xs) =
            memLevel y (y :: ys) := h y
        rw [hyy] at hy'
        exact hy'
      cases heq : decide (x = y) with
      | false =>
          have hxm :=
            mem_cons_of_ne x y ys heq
              hxy_mem
          have hyx :
              decide (y = x) = false := by
            cases hd : decide (y = x) with
            | false => rfl
            | true =>
                have hyx' : y = x :=
                  of_decide_eq_true hd
                have hxy : x = y :=
                  hyx'.symm
                rw [decide_eq_true hxy] at heq
                exact Bool.noConfusion heq
          have hym :=
            mem_cons_of_ne y x xs hyx
              hyx_mem
          exact False.elim
            (sortedInc_asymm_mem x y xs ys
              hsx hsy hym hxm)
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          have hnx :=
            not_mem_sorted_head x xs hsx
          have hny :=
            not_mem_sorted_head y ys hsy
          have htl :
              ∀ z, memLevel z xs =
                memLevel z ys :=
            fun z => by
              cases hez : decide (z = x) with
              | true =>
                  have hzx : z = x :=
                    of_decide_eq_true hez
                  rw [hzx, hnx, hxy, hny]
              | false =>
                  have hey :
                      decide (z = y) =
                        false := by
                    cases hd : decide (z = y) with
                    | false => rfl
                    | true =>
                        have hzy : z = y :=
                          of_decide_eq_true hd
                        have hzx : z = x :=
                          hzy.trans hxy.symm
                        rw [decide_eq_true hzx]
                          at hez
                        exact Bool.noConfusion hez
                  have hL :
                      memLevel z (x :: xs) =
                        memLevel z xs := by
                    simp only [memLevel, hez]
                  have hR :
                      memLevel z (y :: ys) =
                        memLevel z ys := by
                    simp only [memLevel, hey]
                  have hall := h z
                  rw [hL, hR] at hall
                  exact hall
          have ih :=
            sorted_eq_of_mem_iff xs ys
              hsx' hsy' htl
          rw [hxy, ih]

def exists_undominated
    (xs ys : List Level)
    (hax : antichain xs = true)
    (hay : antichain ys = true)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (hsx : sortedInc xs = true)
    (hsy : sortedInc ys = true)
    (hne : xs ≠ ys) :
    (Σ' a, memLevel a xs = true ×'
      anyDominates a ys = false) ⊕'
    (Σ' b, memLevel b ys = true ×'
      anyDominates b xs = false) := by
  cases hL : firstUndominated xs ys with
  | some a =>
      have ⟨hm, hnd⟩ :=
        firstUndominated_some ys a xs hL
      exact .inl ⟨a, hm, hnd⟩
  | none =>
      cases hR : firstUndominated ys xs with
      | some b =>
          have ⟨hm, hnd⟩ :=
            firstUndominated_some xs b ys hR
          exact .inr ⟨b, hm, hnd⟩
      | none =>
          have hxs :=
            firstUndominated_none ys xs hL
          have hys :=
            firstUndominated_none xs ys hR
          have heq :=
            sorted_eq_of_mem_iff xs ys hsx hsy
              (fun a =>
                mem_iff_of_mutual_dom xs ys
                  hax hay hox hoy hxs hys a)
          exact False.elim (hne heq)

/-! H-6k R-SepPick (b): an undominated atom
separates at a spike (param) or at the
all-zero valuation (constant). Case split
on `dominates` agrees with `dominates_eqN`
(same-param / param-const / const-const
/ diff-param / const-param). -/

theorem spike_undom_atom_lt
    (a y : Level) (i k N : Nat)
    (ha : peelOff a = (k, .param i))
    (hy : isOffAtom y = true)
    (hd : dominates y a = false)
    (hN : (peelOff y).1 < N) :
    evalTotal (spike i N) y < N + k := by
  cases hpy : peelOff y with
  | mk n b =>
      have hn : n < N := by
        simp only [hpy, Prod.fst] at hN
        exact hN
      cases b with
      | param j =>
          cases hij : decide (j = i) with
          | true =>
              have hij' : j = i :=
                of_decide_eq_true hij
              have hpy' :
                  peelOff y =
                    (n, .param i) := by
                rw [hpy, hij']
              have hds :=
                dominates_same_param y a
                  i n k hpy' ha
              rw [hds] at hd
              have hnk : n < k :=
                Nat.lt_of_not_le
                  (of_decide_eq_false hd)
              have he :=
                evalTotal_spike_of_peel_param
                  i N n y hpy'
              rw [he]
              exact Nat.add_lt_add_left hnk N
          | false =>
              have hne :
                  match (peelOff y).2 with
                  | .param j =>
                      decide (j = i) = false
                  | _ => True := by
                simp only [hpy]
                exact hij
              have he :=
                evalTotal_spike_of_peel_other
                  i N y hy hne
              rw [he]
              simp only [hpy, Prod.fst]
              exact Nat.lt_of_lt_of_le hn
                (Nat.le_add_right N k)
      | zero =>
          have hne :
              match (peelOff y).2 with
              | .param j =>
                  decide (j = i) = false
              | _ => True := by
            simp only [hpy]
          have he :=
            evalTotal_spike_of_peel_other
              i N y hy hne
          rw [he]
          simp only [hpy, Prod.fst]
          exact Nat.lt_of_lt_of_le hn
            (Nat.le_add_right N k)
      | succ _ =>
          simp only [isOffAtom, hpy] at hy
          exact Bool.noConfusion hy
      | max _ _ =>
          simp only [isOffAtom, hpy] at hy
          exact Bool.noConfusion hy
      | imax _ _ =>
          simp only [isOffAtom, hpy] at hy
          exact Bool.noConfusion hy

theorem undominated_param_ys_lt
    (a : Level) (i k N : Nat)
    (ys : List Level)
    (ha : peelOff a = (k, .param i))
    (hnd : anyDominates a ys = false)
    (hoy : allOffAtoms ys = true)
    (hNy : maxOffList ys < N) :
    evalMaxListTotal (spike i N) ys <
      N + k := by
  have hNpos : 0 < N :=
    Nat.lt_of_le_of_lt
      (Nat.zero_le (maxOffList ys)) hNy
  have hb0 : 0 < N + k :=
    Nat.lt_of_lt_of_le hNpos
      (Nat.le_add_right N k)
  exact evalMaxListTotal_lt_of
    (spike i N) (N + k) hb0 ys
    (fun y hm =>
      spike_undom_atom_lt a y i k N ha
        (allOffAtoms_mem y ys hoy hm)
        (anyDominates_false_mem a y ys
          hnd hm)
        (Nat.lt_of_le_of_lt
          (peel_le_maxOffList y ys hm)
          hNy))

theorem undominated_param_xs_ge
    (a : Level) (i k N : Nat)
    (xs : List Level)
    (ha : peelOff a = (k, .param i))
    (hmem : memLevel a xs = true) :
    N + k ≤
      evalMaxListTotal (spike i N) xs := by
  have he :=
    evalTotal_spike_of_peel_param
      i N k a ha
  have hle :=
    evalMaxListTotal_le_mem
      (spike i N) a xs hmem
  rw [he] at hle
  exact hle

theorem undominated_param_spike
    (a : Level) (i k N : Nat)
    (xs ys : List Level)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .param i))
    (hmem : memLevel a xs = true)
    (hnd : anyDominates a ys = false)
    (hNy : maxOffList ys < N) :
    N + k ≤
      evalMaxListTotal (spike i N) xs ∧
      evalMaxListTotal (spike i N) ys <
        N + k :=
  ⟨undominated_param_xs_ge a i k N xs
      ha hmem,
    undominated_param_ys_lt a i k N ys
      ha hnd hoy hNy⟩

theorem undominated_const_zero
    (a : Level) (k : Nat)
    (xs ys : List Level)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .zero))
    (hcan : isCanonAtom a = true)
    (hmem : memLevel a xs = true)
    (hnd : anyDominates a ys = false) :
    k ≤ evalMaxListTotal (fun _ => 0) xs ∧
      evalMaxListTotal (fun _ => 0) ys < k := by
  have hk0 :=
    canon_off_const_pos a k hcan ha
  have hlt :=
    maxOff_lt_of_not_dom_const a k ys
      ha hnd hoy hk0
  have hlex : k ≤ maxOffList xs := by
    have hp := peel_le_maxOffList a xs hmem
    simp only [ha, Prod.fst] at hp
    exact hp
  have hxz := evalMaxListTotal_zero xs hox
  have hyz := evalMaxListTotal_zero ys hoy
  rw [hxz, hyz]
  exact ⟨hlex, hlt⟩

theorem N_beyond_offs (xs ys : List Level) :
    maxOffList xs <
      Nat.succ (maxOffList (xs ++ ys)) ∧
    maxOffList ys <
      Nat.succ (maxOffList (xs ++ ys)) :=
  ⟨Nat.lt_succ_of_le
      (maxOffList_le_left xs ys),
    Nat.lt_succ_of_le
      (maxOffList_le_right xs ys)⟩

/-! H-6k R-SepPick (c): canon_sep_imaxFree
from (a)+(b). Attempt 1 (counter reset). -/

theorem allCanonAtoms_mem (x : Level) :
    ∀ xs : List Level,
      allCanonAtoms xs = true →
      memLevel x xs = true →
        isCanonAtom x = true
  | [], _, hm => Bool.noConfusion hm
  | y :: ys, h, hm => by
      cases heq : decide (x = y) with
      | true =>
          have hxy : x = y :=
            of_decide_eq_true heq
          rw [hxy]
          exact allCanonAtoms_head y ys h
      | false =>
          simp only [memLevel, heq] at hm
          exact allCanonAtoms_mem x ys
            (allCanonAtoms_tail y ys h) hm

theorem sep_by_undom_param
    (a : Level) (i k : Nat)
    (xs ys : List Level)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .param i))
    (hmem : memLevel a xs = true)
    (hnd : anyDominates a ys = false)
    (h : ∀ σ : Nat → Nat,
      evalMaxListTotal σ xs =
        evalMaxListTotal σ ys) : False := by
  have hNy := (N_beyond_offs xs ys).right
  have hge :=
    undominated_param_xs_ge a i k
      (Nat.succ (maxOffList (xs ++ ys)))
      xs ha hmem
  have hlt :=
    undominated_param_ys_lt a i k
      (Nat.succ (maxOffList (xs ++ ys)))
      ys ha hnd hoy hNy
  have heq :=
    h (spike i
      (Nat.succ (maxOffList (xs ++ ys))))
  rw [heq] at hge
  exact Nat.lt_irrefl
    (Nat.succ (maxOffList (xs ++ ys)) + k)
    (Nat.lt_of_le_of_lt hge hlt)

theorem sep_by_undom_const
    (a : Level) (k : Nat)
    (xs ys : List Level)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (ha : peelOff a = (k, .zero))
    (hcan : isCanonAtom a = true)
    (hmem : memLevel a xs = true)
    (hnd : anyDominates a ys = false)
    (h : ∀ σ : Nat → Nat,
      evalMaxListTotal σ xs =
        evalMaxListTotal σ ys) : False := by
  have ⟨hge, hlt⟩ :=
    undominated_const_zero a k xs ys
      hox hoy ha hcan hmem hnd
  have heq := h (fun _ => 0)
  rw [heq] at hge
  exact Nat.lt_irrefl k
    (Nat.lt_of_le_of_lt hge hlt)

theorem sep_by_undom
    (a : Level)
    (xs ys : List Level)
    (hox : allOffAtoms xs = true)
    (hoy : allOffAtoms ys = true)
    (hcx : allCanonAtoms xs = true)
    (hmem : memLevel a xs = true)
    (hnd : anyDominates a ys = false)
    (h : ∀ σ : Nat → Nat,
      evalMaxListTotal σ xs =
        evalMaxListTotal σ ys) : False := by
  have haoff :=
    allOffAtoms_mem a xs hox hmem
  have hcan :=
    allCanonAtoms_mem a xs hcx hmem
  cases hpeel : peelOff a with
  | mk k b =>
      cases b with
      | param i =>
          exact sep_by_undom_param a i k
            xs ys hoy hpeel hmem hnd h
      | zero =>
          exact sep_by_undom_const a k
            xs ys hox hoy hpeel hcan
            hmem hnd h
      | succ _ =>
          simp only [isOffAtom, hpeel]
            at haoff
          exact Bool.noConfusion haoff
      | max _ _ =>
          simp only [isOffAtom, hpeel]
            at haoff
          exact Bool.noConfusion haoff
      | imax _ _ =>
          simp only [isOffAtom, hpeel]
            at haoff
          exact Bool.noConfusion haoff

theorem evalMax_of_canon
    (σ : Nat → Nat) (l : Level)
    (hmax : maxOfList (flattenMax l) = l) :
    evalTotal σ l =
      evalMaxListTotal σ (flattenMax l) := by
  have e :=
    maxOfList_evalTotal σ (flattenMax l)
  rw [hmax] at e
  exact e

theorem canon_sep_imaxFree (n1 n2 : Level)
    (h1 : IsCanon n1) (h2 : IsCanon n2)
    (f1 : imaxFree n1 = true)
    (f2 : imaxFree n2 = true)
    (h : ∀ σ : Nat → Nat,
      evalTotal σ n1 = evalTotal σ n2) :
    n1 = n2 := by
  have d1 :=
    flatten_canon_imaxFree n1 h1 f1
  have d2 :=
    flatten_canon_imaxFree n2 h2 f2
  have hatoms1 := d1.1
  have hsort1 := d1.2.1
  have hanti1 := d1.2.2.1
  have hoff1 := d1.2.2.2.1
  have hmax1 := d1.2.2.2.2
  have hatoms2 := d2.1
  have hsort2 := d2.2.1
  have hanti2 := d2.2.2.1
  have hoff2 := d2.2.2.2.1
  have hmax2 := d2.2.2.2.2
  have hev :
      ∀ σ : Nat → Nat,
        evalMaxListTotal σ
          (flattenMax n1) =
          evalMaxListTotal σ
            (flattenMax n2) :=
    fun σ =>
      (evalMax_of_canon σ n1 hmax1).symm.trans
        ((h σ).trans
          (evalMax_of_canon σ n2 hmax2))
  cases hd :
      decide (flattenMax n1 =
        flattenMax n2) with
  | true =>
      have heq :
          flattenMax n1 = flattenMax n2 :=
        of_decide_eq_true hd
      rw [← hmax1, ← hmax2, heq]
  | false =>
      have hne :
          flattenMax n1 ≠ flattenMax n2 :=
        of_decide_eq_false hd
      have pick :=
        exists_undominated
          (flattenMax n1) (flattenMax n2)
          hanti1 hanti2 hoff1 hoff2
          hsort1 hsort2 hne
      cases pick with
      | inl p =>
          exact False.elim
            (sep_by_undom p.1
              (flattenMax n1)
              (flattenMax n2)
              hoff1 hoff2 hatoms1
              p.2.1 p.2.2 hev)
      | inr p =>
          exact False.elim
            (sep_by_undom p.1
              (flattenMax n2)
              (flattenMax n1)
              hoff2 hoff1 hatoms2
              p.2.1 p.2.2
              (fun σ => (hev σ).symm))

/-! H-6k rung (4): split `decEqN`. T3 MISMATCH
on `decEqN` permitted by R-LevelSplit (4).
`decEqN_sound` re-sealed against the same
decider. -/

theorem dependsOn_mem_params :
    ∀ l : Level, ∀ i : Nat,
      dependsOn l i = true →
        memNat i (paramsOf l) = true
  | .zero, i, h => Bool.noConfusion h
  | .succ l, i, h =>
      dependsOn_mem_params l i h
  | .param j, i, h => by
      have hij : j = i := by
        simp only [dependsOn] at h
        exact of_decide_eq_true h
      simp only [paramsOf, memNat]
      rw [decide_eq_true hij.symm]
  | .max a b, i, h => by
      have hor := or_true h
      have hu :=
        memNat_paramsOf_max i a b
      cases hor with
      | inl ha =>
          have hp :=
            dependsOn_mem_params a i ha
          rw [hu, hp]
          rfl
      | inr hb =>
          have hp :=
            dependsOn_mem_params b i hb
          rw [hu]
          cases memNat i (paramsOf a) with
          | true => rfl
          | false =>
              rw [hp]
              rfl
  | .imax a b, i, h => by
      simp only [dependsOn] at h
      cases hz : levelIsZero b with
      | true =>
          rw [hz] at h
          exact Bool.noConfusion h
      | false =>
          rw [hz] at h
          have hor := or_true h
          have hu :=
            memNat_paramsOf_imax i a b
          cases hor with
          | inl ha =>
              have hp :=
                dependsOn_mem_params a i ha
              rw [hu, hp]
              rfl
          | inr hb =>
              have hp :=
                dependsOn_mem_params b i hb
              rw [hu]
              cases memNat i (paramsOf a) with
              | true => rfl
              | false =>
                  rw [hp]
                  rfl

def filterDepends (l : Level) :
    List Nat → List Nat
  | [] => []
  | i :: is =>
      match dependsOn l i with
      | true =>
          i :: filterDepends l is
      | false => filterDepends l is

def depsOf (l : Level) : List Nat :=
  filterDepends l (paramsOf l)

theorem memNat_filterDepends
    (l : Level) (i : Nat) :
    ∀ xs : List Nat,
      memNat i (filterDepends l xs) =
        (dependsOn l i && memNat i xs)
  | [] => by
      simp only [filterDepends, memNat]
      cases dependsOn l i <;> rfl
  | x :: xs => by
      simp only [filterDepends]
      cases hd : dependsOn l x with
      | true =>
          simp only [memNat]
          cases hix : decide (i = x) with
          | true =>
              have hix' : i = x :=
                of_decide_eq_true hix
              rw [hix', hd]
              rfl
          | false =>
              exact memNat_filterDepends
                l i xs
      | false =>
          have ih :=
            memNat_filterDepends l i xs
          simp only [memNat]
          cases hix : decide (i = x) with
          | true =>
              have hix' : i = x :=
                of_decide_eq_true hix
              rw [hix', hd] at ih
              rw [hix', hd]
              exact ih
          | false => exact ih

theorem depsOf_mem (l : Level) (i : Nat) :
    memNat i (depsOf l) = dependsOn l i := by
  simp only [depsOf]
  rw [memNat_filterDepends]
  cases hd : dependsOn l i with
  | false => rfl
  | true =>
      have hp :=
        dependsOn_mem_params l i hd
      rw [hp]
      rfl

theorem memNat_union (i : Nat)
    (xs ys : List Nat) :
    memNat i (unionNat xs ys) =
      (memNat i xs || memNat i ys) :=
  memNat_foldInsertNat i xs ys

theorem spec_ext (σ τ : List Nat)
    (h : ∀ i, memNat i σ = memNat i τ) :
    ∀ l : Level, spec σ l = spec τ l
  | .zero => rfl
  | .succ l =>
      congrArg Level.succ (spec_ext σ τ h l)
  | .param i => by
      simp only [spec, specParam]
      rw [h i]
  | .max a b => by
      have ha := spec_ext σ τ h a
      have hb := spec_ext σ τ h b
      simp only [spec]
      rw [ha, hb]
  | .imax a b => by
      have ha := spec_ext σ τ h a
      have hb := spec_ext σ τ h b
      simp only [spec]
      rw [ha, hb]

theorem memNat_append (i : Nat) :
    ∀ xs ys : List Nat,
      memNat i (xs ++ ys) =
        (memNat i xs || memNat i ys)
  | [], ys => by
      simp only [List.nil_append, memNat]
      cases memNat i ys <;> rfl
  | x :: xs, ys => by
      have ih := memNat_append i xs ys
      simp only [memNat]
      cases hix : decide (i = x) with
      | true => rfl
      | false => exact ih

def specAgree (l1 l2 : Level)
    (acc : List Nat) : List Nat → Bool
  | [] =>
      decide
        (nf (spec acc l1) =
          nf (spec acc l2))
  | i :: is =>
      match specAgree l1 l2 acc is with
      | false => false
      | true =>
          specAgree l1 l2 (i :: acc) is

theorem specAgree_zeroSet
    (l1 l2 : Level) (acc : List Nat) :
    ∀ rest : List Nat,
      specAgree l1 l2 acc rest = true →
      ∀ ρ : Nat → Nat,
        nf (spec
            (acc ++ zeroSetOf ρ rest) l1) =
          nf (spec
            (acc ++ zeroSetOf ρ rest) l2)
  | [], h, ρ => by
      simp only [specAgree, zeroSetOf,
        List.append_nil] at h ⊢
      exact of_decide_eq_true h
  | i :: is, h, ρ => by
      simp only [specAgree] at h
      cases h0 : specAgree l1 l2 acc is with
      | false =>
          simp only [h0] at h
          exact Bool.noConfusion h
      | true =>
          simp only [h0] at h
          have ih0 :=
            specAgree_zeroSet l1 l2 acc is
              h0
          have ih1 :=
            specAgree_zeroSet l1 l2
              (i :: acc) is h
          simp only [zeroSetOf]
          cases hz : decide (ρ i = 0) with
          | false =>
              exact ih0 ρ
          | true =>
              have hmem :
                  ∀ j,
                    memNat j
                      (acc ++
                        (i :: zeroSetOf ρ is)) =
                      memNat j
                        ((i :: acc) ++
                          zeroSetOf ρ is) :=
                fun j => by
                  rw [memNat_append,
                    memNat_append]
                  simp only [memNat]
                  cases decide (j = i) with
                  | true =>
                      cases memNat j acc <;>
                        cases memNat j
                          (zeroSetOf ρ is) <;>
                          rfl
                  | false =>
                      cases memNat j acc <;>
                        cases memNat j
                          (zeroSetOf ρ is) <;>
                          rfl
              have he1 :=
                spec_ext
                  (acc ++
                    (i :: zeroSetOf ρ is))
                  ((i :: acc) ++
                    zeroSetOf ρ is)
                  hmem l1
              have he2 :=
                spec_ext
                  (acc ++
                    (i :: zeroSetOf ρ is))
                  ((i :: acc) ++
                    zeroSetOf ρ is)
                  hmem l2
              rw [he1, he2]
              exact ih1 ρ

theorem eval_ignore_unused
    (ρ τ : Nat → Option Nat) :
    ∀ l : Level,
      (∀ i, dependsOn l i = true →
        ρ i = τ i) →
        eval ρ l = eval τ l
  | .zero, _ => rfl
  | .succ l, h => by
      have ih :=
        eval_ignore_unused ρ τ l h
      simp only [eval]
      rw [ih]
  | .param j, h => by
      have hj :
          dependsOn (.param j) j = true := by
        simp only [dependsOn]
        exact decide_eq_true True.intro
      have he := h j hj
      simp only [eval]
      exact he
  | .max a b, h => by
      have ha :
          ∀ i, dependsOn a i = true →
            ρ i = τ i :=
        fun i hi =>
          h i (by
            simp only [dependsOn]
            rw [hi]
            exact or_true_left
              (dependsOn b i))
      have hb :
          ∀ i, dependsOn b i = true →
            ρ i = τ i :=
        fun i hi =>
          h i (by
            simp only [dependsOn]
            rw [hi]
            cases dependsOn a i <;> rfl)
      have iha :=
        eval_ignore_unused ρ τ a ha
      have ihb :=
        eval_ignore_unused ρ τ b hb
      simp only [eval]
      rw [iha, ihb]
  | .imax a b, h => by
      cases hz : levelIsZero b with
      | true =>
          have eρ :
              eval ρ (.imax a b) = some 0 :=
            (eval_imax_eq_zero ρ a b).mpr
              ((levelIsZero_iff b).mp hz ρ)
          have eτ :
              eval τ (.imax a b) = some 0 :=
            (eval_imax_eq_zero τ a b).mpr
              ((levelIsZero_iff b).mp hz τ)
          exact eρ.trans eτ.symm
      | false =>
          have h' :
              ∀ i,
                dependsOn a i = true ∨
                  dependsOn b i = true →
                  ρ i = τ i :=
            fun i hor =>
              h i (by
                simp only [dependsOn, hz]
                cases hor with
                | inl ha =>
                    rw [ha]
                    rfl
                | inr hb =>
                    rw [hb]
                    cases dependsOn a i <;>
                      rfl)
          have ha :
              ∀ i, dependsOn a i = true →
                ρ i = τ i :=
            fun i hi => h' i (Or.inl hi)
          have hb :
              ∀ i, dependsOn b i = true →
                ρ i = τ i :=
            fun i hi => h' i (Or.inr hi)
          have iha :=
            eval_ignore_unused ρ τ a ha
          have ihb :=
            eval_ignore_unused ρ τ b hb
          simp only [eval]
          rw [iha, ihb]

def fill0 (ρ : Nat → Option Nat)
    (i : Nat) : Nat :=
  (ρ i).getD 0

theorem fill0_some
    (ρ : Nat → Option Nat) (i n : Nat)
    (h : ρ i = some n) :
    ρ i = some (fill0 ρ i) := by
  simp only [fill0]
  rw [h]
  rfl

theorem fill0_of_not_none
    (ρ : Nat → Option Nat) (i : Nat)
    (h : ρ i ≠ none) :
    ρ i = some (fill0 ρ i) := by
  cases hρ : ρ i with
  | none => exact False.elim (h hρ)
  | some n =>
      simp only [fill0]
      rw [hρ]
      rfl

def firstNoneDep (ρ : Nat → Option Nat)
    (l : Level) : List Nat → Option Nat
  | [] => none
  | i :: is =>
      match dependsOn l i, ρ i with
      | true, none => some i
      | _, _ => firstNoneDep ρ l is

theorem firstNoneDep_some
    (ρ : Nat → Option Nat) (l : Level)
    (j : Nat) :
    ∀ xs : List Nat,
      firstNoneDep ρ l xs = some j →
        dependsOn l j = true ∧
          ρ j = none
  | [], h => Option.noConfusion h
  | i :: is, h => by
      simp only [firstNoneDep] at h
      cases hd : dependsOn l i with
      | false =>
          simp only [hd] at h
          exact firstNoneDep_some ρ l j is h
      | true =>
          simp only [hd] at h
          cases hρ : ρ i with
          | none =>
              simp only [hρ] at h
              injection h with hij
              rw [← hij]
              exact ⟨hd, hρ⟩
          | some n =>
              simp only [hρ] at h
              exact firstNoneDep_some
                ρ l j is h

theorem firstNoneDep_none_mem
    (ρ : Nat → Option Nat) (l : Level) :
    ∀ xs : List Nat,
      firstNoneDep ρ l xs = none →
      ∀ i, memNat i xs = true →
        dependsOn l i = true →
          ρ i ≠ none
  | [], _, i, hm, _ => Bool.noConfusion hm
  | x :: xs, h, i, hm, hd => by
      simp only [firstNoneDep] at h
      cases hdx : dependsOn l x with
      | false =>
          simp only [hdx] at h
          cases hix : decide (i = x) with
          | true =>
              have hix' : i = x :=
                of_decide_eq_true hix
              rw [hix'] at hd
              rw [hdx] at hd
              exact Bool.noConfusion hd
          | false =>
              simp only [memNat, hix] at hm
              exact firstNoneDep_none_mem
                ρ l xs h i hm hd
      | true =>
          simp only [hdx] at h
          cases hρ : ρ x with
          | none =>
              simp only [hρ] at h
              exact Option.noConfusion h
          | some n =>
              simp only [hρ] at h
              cases hix : decide (i = x) with
              | true =>
                  have hix' : i = x :=
                    of_decide_eq_true hix
                  rw [hix']
                  intro hn
                  rw [hρ] at hn
                  exact Option.noConfusion hn
              | false =>
                  simp only [memNat, hix] at hm
                  exact firstNoneDep_none_mem
                    ρ l xs h i hm hd

theorem mem_params_of_union_left
    (i : Nat) (xs ys : List Nat)
    (h : memNat i xs = true) :
    memNat i (unionNat xs ys) = true := by
  rw [memNat_union, h]
  rfl

theorem mem_params_of_union_right
    (i : Nat) (xs ys : List Nat)
    (h : memNat i ys = true) :
    memNat i (unionNat xs ys) = true := by
  rw [memNat_union, h]
  cases memNat i xs <;> rfl

/- R-LevelSplit (4) attempt 1 WALLED at
`decEqN_sound` mixed-lazy: eval some / eval
none while both `firstNoneDep` are `some`.
Split `decEqN` not landed. Helpers kept.
R-DecEqNNf `decEqN` restored.

H-6l / R-LevelNone. The `none` half under
lazy `imax`. START FROM THE MEASUREMENT:
`eval`'s `imax` arm (RcicDeclarative) is

```
| .imax a b =>
    (eval ρ b).bind fun y =>
      if y = 0 then some 0
      else (eval ρ a).map fun x => max x y
```

Mixed-lazy instance: `imax (param 0) (param 1)`
at ρ = {0 ↦ none, 1 ↦ some 0} is `some 0`
(b is zero, a is not consulted). -/
#eval (if eval
    (fun i =>
      if i = 1 then some 0 else none)
    (.imax (.param 0) (.param 1)) = some 0
  then 0 else panic "H-6l: mixed-lazy")

theorem not_false : (!false) = true := rfl
theorem not_true : (!true) = false := rfl
theorem or_false_left (b : Bool) :
    (false || b) = b := by cases b <;> rfl
theorem and_true_left (b : Bool) :
    (true && b) = b := by cases b <;> rfl
theorem and_false_left (b : Bool) :
    (false && b) = false := by
  cases b <;> rfl

theorem memNat_paramsOf_param (i : Nat) :
    memNat i (paramsOf (.param i)) =
      true := by
  simp only [paramsOf, memNat]
  cases h : decide (i = i) with
  | true => rfl
  | false =>
      exact False.elim
        (of_decide_eq_false h rfl)

/-- R-LevelNone (1): `valZero σ b` on N-free
`b` says `b` evaluates to `some 0` under σ
(zero-pattern of the `some` parameters).
`imax` is lazy: only the second argument. -/
def valZero (σ : List Nat) : Level → Bool
  | .zero => true
  | .succ _ => false
  | .param i => memNat i σ
  | .max a b => valZero σ a && valZero σ b
  | .imax _ b => valZero σ b

/-- R-LevelNone (1): `noneOf N σ`. Structural
on `eval`'s `none` cases, including lazy
`imax` (`noneOf b || (!valZero σ b &&
noneOf a)`). -/
def noneOf (N σ : List Nat) : Level → Bool
  | .zero => false
  | .succ l => noneOf N σ l
  | .param i => memNat i N
  | .max a b =>
      noneOf N σ a || noneOf N σ b
  | .imax a b =>
      noneOf N σ b ||
        (!valZero σ b && noneOf N σ a)

def noneSetOf (ρ : Nat → Option Nat) :
    List Nat → List Nat
  | [] => []
  | i :: is =>
      match ρ i with
      | none => i :: noneSetOf ρ is
      | some _ => noneSetOf ρ is

def zeroSetPartial
    (ρ : Nat → Option Nat) :
    List Nat → List Nat
  | [] => []
  | i :: is =>
      match ρ i with
      | some .zero =>
          i :: zeroSetPartial ρ is
      | _ => zeroSetPartial ρ is

theorem memNat_noneSetOf_subset
    (ρ : Nat → Option Nat) :
    ∀ xs i,
      memNat i (noneSetOf ρ xs) = true →
        memNat i xs = true
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [noneSetOf] at h
      cases hρ : ρ x with
      | none =>
          simp only [hρ, memNat] at h ⊢
          cases hix : decide (i = x) with
          | true => rfl
          | false =>
              simp only [hix] at h
              exact memNat_noneSetOf_subset
                ρ xs i h
      | some n =>
          simp only [hρ] at h
          have hrest :=
            memNat_noneSetOf_subset
              ρ xs i h
          simp only [memNat]
          cases decide (i = x) with
          | true => rfl
          | false => exact hrest

theorem memNat_noneSetOf_eq
    (ρ : Nat → Option Nat) :
    ∀ xs i,
      memNat i xs = true →
        memNat i (noneSetOf ρ xs) =
          match ρ i with
          | none => true
          | some _ => false
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [memNat] at h
      cases hix : decide (i = x) with
      | true =>
          have hix' : i = x :=
            of_decide_eq_true hix
          have hρi : ρ i = ρ x :=
            congrArg ρ hix'
          cases hρ : ρ x with
          | none =>
              simp only [noneSetOf, hρ,
                memNat, hix]
              rw [hρi, hρ]
          | some n =>
              simp only [noneSetOf, hρ]
              cases hm : memNat i xs with
              | true =>
                  have ih :=
                    memNat_noneSetOf_eq
                      ρ xs i hm
                  rw [ih, hρi, hρ]
              | false =>
                  have hf :
                      memNat i
                        (noneSetOf ρ xs) =
                          false := by
                    cases hn :
                      memNat i
                        (noneSetOf ρ xs) with
                    | false => rfl
                    | true =>
                        have hs :=
                          memNat_noneSetOf_subset
                            ρ xs i hn
                        rw [hm] at hs
                        exact
                          Bool.noConfusion
                            hs
                  rw [hf, hρi, hρ]
      | false =>
          simp only [hix] at h
          have ih :=
            memNat_noneSetOf_eq ρ xs i h
          cases hρ : ρ x with
          | none =>
              simp only [noneSetOf, hρ,
                memNat, hix]
              exact ih
          | some _ =>
              simp only [noneSetOf, hρ]
              exact ih

theorem memNat_zeroSetPartial_subset
    (ρ : Nat → Option Nat) :
    ∀ xs i,
      memNat i
          (zeroSetPartial ρ xs) = true →
        memNat i xs = true
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [zeroSetPartial] at h
      cases hρ : ρ x with
      | none =>
          simp only [hρ] at h
          have hrest :=
            memNat_zeroSetPartial_subset
              ρ xs i h
          simp only [memNat]
          cases decide (i = x) with
          | true => rfl
          | false => exact hrest
      | some n =>
          cases n with
          | zero =>
              simp only [hρ, memNat] at h ⊢
              cases hix : decide (i = x) with
              | true => rfl
              | false =>
                  simp only [hix] at h
                  exact
                    memNat_zeroSetPartial_subset
                      ρ xs i h
          | succ n =>
              simp only [hρ] at h
              have hrest :=
                memNat_zeroSetPartial_subset
                  ρ xs i h
              simp only [memNat]
              cases decide (i = x) with
              | true => rfl
              | false => exact hrest

theorem memNat_not_filter
    (i : Nat) (ys : List Nat)
    (hm : memNat i ys = false)
    (hs : memNat i ys = true) : False := by
  rw [hm] at hs
  exact Bool.noConfusion hs

theorem memNat_zeroSetPartial_eq
    (ρ : Nat → Option Nat) :
    ∀ xs i,
      memNat i xs = true →
        memNat i (zeroSetPartial ρ xs) =
          match ρ i with
          | some .zero => true
          | _ => false
  | [], i, h => Bool.noConfusion h
  | x :: xs, i, h => by
      simp only [memNat] at h
      cases hix : decide (i = x) with
      | true =>
          have hix' : i = x :=
            of_decide_eq_true hix
          have hρi : ρ i = ρ x :=
            congrArg ρ hix'
          cases hρ : ρ x with
          | none =>
              have hf :
                  memNat i
                    (zeroSetPartial ρ xs) =
                      false := by
                cases hm : memNat i xs with
                | true =>
                    have ih :=
                      memNat_zeroSetPartial_eq
                        ρ xs i hm
                    rw [hρi, hρ] at ih
                    exact ih
                | false =>
                    cases hn :
                      memNat i
                        (zeroSetPartial ρ
                          xs) with
                    | false => rfl
                    | true =>
                        have hs :=
                          memNat_zeroSetPartial_subset
                            ρ xs i hn
                        exact False.elim
                          (memNat_not_filter
                            i xs hm hs)
              simp only [zeroSetPartial,
                hρ]
              rw [hf, hρi, hρ]
          | some n =>
              cases n with
              | zero =>
                  simp only
                    [zeroSetPartial, hρ,
                      memNat, hix]
                  rw [hρi, hρ]
              | succ n =>
                  have hf :
                      memNat i
                        (zeroSetPartial ρ
                          xs) = false := by
                    cases hm : memNat i xs with
                    | true =>
                        have ih :=
                          memNat_zeroSetPartial_eq
                            ρ xs i hm
                        rw [hρi, hρ] at ih
                        exact ih
                    | false =>
                        cases hn :
                          memNat i
                            (zeroSetPartial
                              ρ xs) with
                        | false => rfl
                        | true =>
                            have hs :=
                              memNat_zeroSetPartial_subset
                                ρ xs i hn
                            exact False.elim
                              (memNat_not_filter
                                i xs hm hs)
                  simp only
                    [zeroSetPartial, hρ]
                  rw [hf, hρi, hρ]
      | false =>
          simp only [hix] at h
          have ih :=
            memNat_zeroSetPartial_eq
              ρ xs i h
          cases hρ : ρ x with
          | none =>
              simp only [zeroSetPartial,
                hρ]
              exact ih
          | some n =>
              cases n with
              | zero =>
                  simp only
                    [zeroSetPartial, hρ,
                      memNat, hix]
                  exact ih
              | succ n =>
                  simp only
                    [zeroSetPartial, hρ]
                  exact ih

theorem noneOf_hN_left
    (ρ : Nat → Option Nat)
    (N : List Nat) (a b : Level)
    (hN : ∀ i,
      memNat i
          (paramsOf (.max a b)) = true →
        (memNat i N = true ↔
          ρ i = none)) :
    ∀ i, memNat i (paramsOf a) = true →
      (memNat i N = true ↔ ρ i = none) :=
  fun i hi => hN i (by
    rw [memNat_paramsOf_max, hi]
    exact or_true_left _)

theorem noneOf_hN_right
    (ρ : Nat → Option Nat)
    (N : List Nat) (a b : Level)
    (hN : ∀ i,
      memNat i
          (paramsOf (.max a b)) = true →
        (memNat i N = true ↔
          ρ i = none)) :
    ∀ i, memNat i (paramsOf b) = true →
      (memNat i N = true ↔ ρ i = none) :=
  fun i hi => hN i (by
    rw [memNat_paramsOf_max]
    cases memNat i (paramsOf a) with
    | true => rfl
    | false =>
        rw [hi]
        rfl)

theorem noneOf_hσ_left
    (ρ : Nat → Option Nat)
    (σ : List Nat) (a b : Level)
    (hσ : ∀ i,
      memNat i
          (paramsOf (.max a b)) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0)) :
    ∀ i, memNat i (paramsOf a) = true →
      ρ i ≠ none →
        (memNat i σ = true ↔
          ρ i = some 0) :=
  fun i hi hne => hσ i (by
    rw [memNat_paramsOf_max, hi]
    exact or_true_left _) hne

theorem noneOf_hσ_right
    (ρ : Nat → Option Nat)
    (σ : List Nat) (a b : Level)
    (hσ : ∀ i,
      memNat i
          (paramsOf (.max a b)) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0)) :
    ∀ i, memNat i (paramsOf b) = true →
      ρ i ≠ none →
        (memNat i σ = true ↔
          ρ i = some 0) :=
  fun i hi hne => hσ i (by
    rw [memNat_paramsOf_max]
    cases memNat i (paramsOf a) with
    | true => rfl
    | false =>
        rw [hi]
        rfl) hne

theorem noneOf_hN_imax_left
    (ρ : Nat → Option Nat)
    (N : List Nat) (a b : Level)
    (hN : ∀ i,
      memNat i
          (paramsOf (.imax a b)) = true →
        (memNat i N = true ↔
          ρ i = none)) :
    ∀ i, memNat i (paramsOf a) = true →
      (memNat i N = true ↔ ρ i = none) :=
  fun i hi => hN i (by
    rw [memNat_paramsOf_imax, hi]
    exact or_true_left _)

theorem noneOf_hN_imax_right
    (ρ : Nat → Option Nat)
    (N : List Nat) (a b : Level)
    (hN : ∀ i,
      memNat i
          (paramsOf (.imax a b)) = true →
        (memNat i N = true ↔
          ρ i = none)) :
    ∀ i, memNat i (paramsOf b) = true →
      (memNat i N = true ↔ ρ i = none) :=
  fun i hi => hN i (by
    rw [memNat_paramsOf_imax]
    cases memNat i (paramsOf a) with
    | true => rfl
    | false =>
        rw [hi]
        rfl)

theorem noneOf_hσ_imax_left
    (ρ : Nat → Option Nat)
    (σ : List Nat) (a b : Level)
    (hσ : ∀ i,
      memNat i
          (paramsOf (.imax a b)) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0)) :
    ∀ i, memNat i (paramsOf a) = true →
      ρ i ≠ none →
        (memNat i σ = true ↔
          ρ i = some 0) :=
  fun i hi hne => hσ i (by
    rw [memNat_paramsOf_imax, hi]
    exact or_true_left _) hne

theorem noneOf_hσ_imax_right
    (ρ : Nat → Option Nat)
    (σ : List Nat) (a b : Level)
    (hσ : ∀ i,
      memNat i
          (paramsOf (.imax a b)) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0)) :
    ∀ i, memNat i (paramsOf b) = true →
      ρ i ≠ none →
        (memNat i σ = true ↔
          ρ i = some 0) :=
  fun i hi hne => hσ i (by
    rw [memNat_paramsOf_imax]
    cases memNat i (paramsOf a) with
    | true => rfl
    | false =>
        rw [hi]
        rfl) hne

theorem noneOf_false_of_eval_some
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (hiff : eval ρ l = none ↔
      noneOf N σ l = true)
    (hx : eval ρ l ≠ none) :
    noneOf N σ l = false := by
  cases hn : noneOf N σ l with
  | false => rfl
  | true =>
      have he := hiff.mpr hn
      exact False.elim (hx he)

theorem valZero_of_eval_zero
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (h2 : noneOf N σ l = false →
      (valZero σ l = true ↔
        eval ρ l = some 0))
    (hn : noneOf N σ l = false)
    (hz : eval ρ l = some 0) :
    valZero σ l = true :=
  (h2 hn).mpr hz

theorem eval_zero_of_valZero
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (h2 : noneOf N σ l = false →
      (valZero σ l = true ↔
        eval ρ l = some 0))
    (hn : noneOf N σ l = false)
    (hv : valZero σ l = true) :
    eval ρ l = some 0 :=
  (h2 hn).mp hv

theorem noneOf_valZero
    (ρ : Nat → Option Nat)
    (N σ : List Nat) :
    ∀ l : Level,
      (∀ i,
        memNat i (paramsOf l) = true →
          (memNat i N = true ↔
            ρ i = none)) →
      (∀ i,
        memNat i (paramsOf l) = true →
          ρ i ≠ none →
            (memNat i σ = true ↔
              ρ i = some 0)) →
      (eval ρ l = none ↔
        noneOf N σ l = true) ∧
      (noneOf N σ l = false →
        (valZero σ l = true ↔
          eval ρ l = some 0))
  | .zero, _hN, _hσ => by
      constructor
      · constructor
        · intro h
          exact Option.noConfusion h
        · intro h
          exact Bool.noConfusion h
      · intro _
        constructor
        · intro _
          rfl
        · intro _
          rfl
  | .succ l, hN, hσ => by
      have ih :=
        noneOf_valZero ρ N σ l hN hσ
      constructor
      · simp only [eval, noneOf]
        constructor
        · intro h
          cases he : eval ρ l with
          | none =>
              exact ih.1.mp he
          | some n =>
              rw [he] at h
              exact Option.noConfusion h
        · intro h
          have he : eval ρ l = none :=
            ih.1.mpr h
          rw [he]
          rfl
      · intro hn
        simp only [valZero, eval]
        have nfalse :
            noneOf N σ l = false := hn
        have hne : eval ρ l ≠ none := by
          intro he
          have ht := ih.1.mp he
          rw [ht] at nfalse
          exact Bool.noConfusion nfalse
        cases he : eval ρ l with
        | none =>
            exact False.elim (hne he)
        | some n =>
            constructor
            · intro hvz
              exact Bool.noConfusion hvz
            · intro h0
              injection h0 with h0'
              exact False.elim
                (Nat.succ_ne_zero n h0')
  | .param i, hN, hσ => by
      have hin := memNat_paramsOf_param i
      have hNi := hN i hin
      constructor
      · simp only [eval, noneOf]
        exact Iff.symm hNi
      · intro hn
        simp only [valZero, eval]
        have hne : ρ i ≠ none := by
          intro he
          have ht := hNi.mpr he
          simp only [noneOf] at hn
          rw [ht] at hn
          exact Bool.noConfusion hn
        have hσi := hσ i hin hne
        exact hσi
  | .max a b, hN, hσ => by
      have iha :=
        noneOf_valZero ρ N σ a
          (noneOf_hN_left ρ N a b hN)
          (noneOf_hσ_left ρ σ a b hσ)
      have ihb :=
        noneOf_valZero ρ N σ b
          (noneOf_hN_right ρ N a b hN)
          (noneOf_hσ_right ρ σ a b hσ)
      constructor
      · rw [eval_max_match]
        simp only [noneOf]
        cases ha : eval ρ a with
        | none =>
            have nfa : noneOf N σ a = true :=
              iha.1.mp ha
            constructor
            · intro _
              rw [nfa]
              exact or_true_left _
            · intro _
              rfl
        | some x =>
            cases hb : eval ρ b with
            | none =>
                have nfb :
                    noneOf N σ b = true :=
                  ihb.1.mp hb
                constructor
                · intro _
                  rw [nfb]
                  cases noneOf N σ a <;> rfl
                · intro _
                  rfl
            | some y =>
                have nfa :
                    noneOf N σ a = false :=
                  noneOf_false_of_eval_some
                    ρ N σ a iha.1 (by
                      intro he
                      rw [ha] at he
                      exact
                        Option.noConfusion
                          he)
                have nfb :
                    noneOf N σ b = false :=
                  noneOf_false_of_eval_some
                    ρ N σ b ihb.1 (by
                      intro he
                      rw [hb] at he
                      exact
                        Option.noConfusion
                          he)
                constructor
                · intro he
                  exact Option.noConfusion
                    he
                · intro hn
                  rw [nfa, nfb] at hn
                  exact Bool.noConfusion hn
      · intro hn
        simp only [noneOf] at hn
        have nfa :
            noneOf N σ a = false := by
          cases ha : noneOf N σ a with
          | false => rfl
          | true =>
              rw [ha] at hn
              exact Bool.noConfusion hn
        have nfb :
            noneOf N σ b = false := by
          cases hb : noneOf N σ b with
          | false => rfl
          | true =>
              rw [nfa, hb] at hn
              exact Bool.noConfusion hn
        have hae : eval ρ a ≠ none := by
          intro he
          have ht := iha.1.mp he
          rw [ht] at nfa
          exact Bool.noConfusion nfa
        have hbe : eval ρ b ≠ none := by
          intro he
          have ht := ihb.1.mp he
          rw [ht] at nfb
          exact Bool.noConfusion nfb
        simp only [valZero]
        rw [eval_max_match]
        cases ha : eval ρ a with
        | none => exact False.elim (hae ha)
        | some x =>
            cases hb : eval ρ b with
            | none =>
                exact False.elim (hbe hb)
            | some y =>
                constructor
                · intro hv
                  have ⟨hva, hvb⟩ :=
                    and_true hv
                  have hx :
                      eval ρ a = some 0 :=
                    eval_zero_of_valZero
                      ρ N σ a iha.2 nfa hva
                  have hy :
                      eval ρ b = some 0 :=
                    eval_zero_of_valZero
                      ρ N σ b ihb.2 nfb hvb
                  rw [ha] at hx
                  rw [hb] at hy
                  injection hx with hx'
                  injection hy with hy'
                  rw [hx', hy']
                  rfl
                · intro h0
                  injection h0 with hmax
                  have hx0 : x = 0 := by
                    have hxle :
                        x ≤ max x y :=
                      Nat.le_max_left x y
                    rw [hmax] at hxle
                    cases x with
                    | zero => rfl
                    | succ n =>
                        exact False.elim
                          (Nat.succ_ne_zero
                            n
                            (Nat.le_antisymm
                              hxle
                              (Nat.zero_le
                                _)))
                  have hy0 : y = 0 := by
                    have hyle :
                        y ≤ max x y :=
                      Nat.le_max_right x y
                    rw [hmax] at hyle
                    cases y with
                    | zero => rfl
                    | succ n =>
                        exact False.elim
                          (Nat.succ_ne_zero
                            n
                            (Nat.le_antisymm
                              hyle
                              (Nat.zero_le
                                _)))
                  have hva :
                      valZero σ a = true :=
                    valZero_of_eval_zero
                      ρ N σ a iha.2 nfa (by
                        rw [ha, hx0])
                  have hvb :
                      valZero σ b = true :=
                    valZero_of_eval_zero
                      ρ N σ b ihb.2 nfb (by
                        rw [hb, hy0])
                  rw [hva, hvb]
                  rfl
  | .imax a b, hN, hσ => by
      have iha :=
        noneOf_valZero ρ N σ a
          (noneOf_hN_imax_left ρ N a b hN)
          (noneOf_hσ_imax_left ρ σ a b hσ)
      have ihb :=
        noneOf_valZero ρ N σ b
          (noneOf_hN_imax_right ρ N a b hN)
          (noneOf_hσ_imax_right ρ σ a b hσ)
      constructor
      · rw [eval_imax_match]
        cases hb : eval ρ b with
        | none =>
            have nfb :
                noneOf N σ b = true :=
              ihb.1.mp hb
            constructor
            · intro _
              simp only [noneOf]
              rw [nfb]
              exact or_true_left _
            · intro _
              rfl
        | some y =>
            cases y with
            | zero =>
                have nfb :
                    noneOf N σ b = false :=
                  noneOf_false_of_eval_some
                    ρ N σ b ihb.1 (by
                      intro he
                      rw [hb] at he
                      exact
                        Option.noConfusion
                          he)
                have vzb :
                    valZero σ b = true :=
                  valZero_of_eval_zero
                    ρ N σ b ihb.2 nfb hb
                constructor
                · intro he
                  exact Option.noConfusion
                    he
                · intro hn
                  simp only [noneOf] at hn
                  rw [nfb, vzb, not_true,
                    and_false_left,
                    or_false_left] at hn
                  exact Bool.noConfusion hn
            | succ y =>
                have nfb :
                    noneOf N σ b = false :=
                  noneOf_false_of_eval_some
                    ρ N σ b ihb.1 (by
                      intro he
                      rw [hb] at he
                      exact
                        Option.noConfusion
                          he)
                have nvz :
                    valZero σ b = false := by
                  cases hv : valZero σ b with
                  | false => rfl
                  | true =>
                      have hz :=
                        eval_zero_of_valZero
                          ρ N σ b ihb.2
                          nfb hv
                      rw [hb] at hz
                      injection hz with hz'
                      exact False.elim
                        (Nat.succ_ne_zero
                          y hz')
                constructor
                · intro he
                  cases ha : eval ρ a with
                  | none =>
                      have nfa :
                          noneOf N σ a =
                            true :=
                        iha.1.mp ha
                      simp only [noneOf]
                      rw [nfb, nvz,
                        not_false,
                        and_true_left,
                        or_false_left, nfa]
                  | some x =>
                      rw [ha] at he
                      exact
                        Option.noConfusion
                          he
                · intro hn
                  simp only [noneOf] at hn
                  rw [nfb, nvz, not_false,
                    and_true_left,
                    or_false_left] at hn
                  have ha :
                      eval ρ a = none :=
                    iha.1.mpr hn
                  rw [ha]
      · intro hn
        simp only [noneOf] at hn
        have nfb :
            noneOf N σ b = false := by
          cases hb : noneOf N σ b with
          | false => rfl
          | true =>
              rw [hb] at hn
              exact Bool.noConfusion hn
        simp only [valZero]
        rw [eval_imax_match]
        cases hb : eval ρ b with
        | none =>
            have ht := ihb.1.mp hb
            rw [ht] at nfb
            exact Bool.noConfusion nfb
        | some y =>
            cases y with
            | zero =>
                have vzb :
                    valZero σ b = true :=
                  valZero_of_eval_zero
                    ρ N σ b ihb.2 nfb hb
                constructor
                · intro _
                  rfl
                · intro _
                  exact vzb
            | succ y =>
                have nvz :
                    valZero σ b = false := by
                  cases hv : valZero σ b with
                  | false => rfl
                  | true =>
                      have hz :=
                        eval_zero_of_valZero
                          ρ N σ b ihb.2
                          nfb hv
                      rw [hb] at hz
                      injection hz with hz'
                      exact False.elim
                        (Nat.succ_ne_zero
                          y hz')
                have nfa :
                    noneOf N σ a = false := by
                  rw [nfb, nvz, not_false,
                    and_true_left,
                    or_false_left] at hn
                  exact hn
                have hae : eval ρ a ≠ none :=
                  by
                    intro he
                    have ht := iha.1.mp he
                    rw [ht] at nfa
                    exact Bool.noConfusion
                      nfa
                cases ha : eval ρ a with
                | none =>
                    exact False.elim
                      (hae ha)
                | some x =>
                    constructor
                    · intro hvz
                      rw [nvz] at hvz
                      exact Bool.noConfusion
                        hvz
                    · intro h0
                      injection h0 with hmax
                      have :
                          y + 1 ≤ max x
                            (y + 1) :=
                        Nat.le_max_right
                          x (y + 1)
                      rw [hmax] at this
                      exact False.elim
                        (Nat.succ_ne_zero y
                          (Nat.le_antisymm
                            this
                            (Nat.zero_le
                              _)))

theorem noneSetOf_hN
    (ρ : Nat → Option Nat) (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      (memNat i
          (noneSetOf ρ (paramsOf l)) =
            true ↔
        ρ i = none) :=
  fun i hi => by
    have e :=
      memNat_noneSetOf_eq ρ (paramsOf l)
        i hi
    constructor
    · intro ht
      cases hρ : ρ i with
      | none => rfl
      | some n =>
          rw [hρ] at e
          rw [e] at ht
          exact Bool.noConfusion ht
    · intro hn
      cases hρ : ρ i with
      | none =>
          rw [hρ] at e
          exact e
      | some n =>
          rw [hρ] at hn
          exact Option.noConfusion hn

theorem zeroSetPartial_hσ
    (ρ : Nat → Option Nat) (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      ρ i ≠ none →
        (memNat i
            (zeroSetPartial ρ
              (paramsOf l)) = true ↔
          ρ i = some 0) :=
  fun i hi hne => by
    have e :=
      memNat_zeroSetPartial_eq ρ
        (paramsOf l) i hi
    cases hρ : ρ i with
    | none =>
        exact False.elim (hne hρ)
    | some n =>
        cases n with
        | zero =>
            rw [hρ] at e
            constructor
            · intro _
              rfl
            · intro _
              exact e
        | succ n =>
            rw [hρ] at e
            constructor
            · intro ht
              rw [e] at ht
              exact Bool.noConfusion ht
            · intro h0
              injection h0 with h0'
              exact False.elim
                (Nat.succ_ne_zero n h0')

/-- R-LevelNone (1): `eval ρ l = none` iff
`noneOf` at ρ's none-set and zero-pattern. -/
theorem eval_none_iff
    (ρ : Nat → Option Nat) (l : Level) :
    eval ρ l = none ↔
      noneOf
        (noneSetOf ρ (paramsOf l))
        (zeroSetPartial ρ (paramsOf l))
        l = true :=
  (noneOf_valZero ρ
      (noneSetOf ρ (paramsOf l))
      (zeroSetPartial ρ (paramsOf l)) l
      (noneSetOf_hN ρ l)
      (zeroSetPartial_hσ ρ l)).1

/- R-LevelNone (2): collapse. Replace `imax a b`
whose `b` is N-free and `valZero σ b` by `zero`
(the lazily-skipped `a` disappears); otherwise
recurse. -/

def collapse (N σ : List Nat) : Level → Level
  | .zero => .zero
  | .succ l => .succ (collapse N σ l)
  | .param i => .param i
  | .max a b =>
      .max (collapse N σ a) (collapse N σ b)
  | .imax a b =>
      match noneOf N σ b, valZero σ b with
      | false, true => .zero
      | _, _ =>
          .imax (collapse N σ a)
            (collapse N σ b)

theorem noneOf_imax_snd_false
    (N σ : List Nat) (a b : Level)
    (h : noneOf N σ (.imax a b) = false) :
    noneOf N σ b = false := by
  simp only [noneOf] at h
  cases hb : noneOf N σ b with
  | false => rfl
  | true =>
      rw [hb] at h
      exact Bool.noConfusion h

theorem noneOf_imax_fst_false
    (N σ : List Nat) (a b : Level)
    (h : noneOf N σ (.imax a b) = false)
    (hv : valZero σ b = false) :
    noneOf N σ a = false := by
  have hb := noneOf_imax_snd_false N σ a b h
  simp only [noneOf] at h
  rw [hb, hv, not_false, and_true_left,
    or_false_left] at h
  exact h

theorem noneOf_max_left_false
    (N σ : List Nat) (a b : Level)
    (h : noneOf N σ (.max a b) = false) :
    noneOf N σ a = false := by
  simp only [noneOf] at h
  cases ha : noneOf N σ a with
  | false => rfl
  | true =>
      rw [ha] at h
      exact Bool.noConfusion h

theorem noneOf_max_right_false
    (N σ : List Nat) (a b : Level)
    (h : noneOf N σ (.max a b) = false) :
    noneOf N σ b = false := by
  have ha := noneOf_max_left_false N σ a b h
  simp only [noneOf] at h
  rw [ha] at h
  exact h

theorem eval_ne_none_of_noneOf_false
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (hN : ∀ i,
      memNat i (paramsOf l) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ : ∀ i,
      memNat i (paramsOf l) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hn : noneOf N σ l = false) :
    eval ρ l ≠ none := by
  intro he
  have ht :=
    (noneOf_valZero ρ N σ l hN hσ).1.mp he
  rw [ht] at hn
  exact Bool.noConfusion hn

theorem eval_some_collapse
    (ρ : Nat → Option Nat)
    (N σ : List Nat) :
    ∀ l : Level,
      (∀ i,
        memNat i (paramsOf l) = true →
          (memNat i N = true ↔
            ρ i = none)) →
      (∀ i,
        memNat i (paramsOf l) = true →
          ρ i ≠ none →
            (memNat i σ = true ↔
              ρ i = some 0)) →
      noneOf N σ l = false →
        eval ρ l = eval ρ (collapse N σ l)
  | .zero, _hN, _hσ, _hn => rfl
  | .succ l, hN, hσ, hn => by
      have ih :=
        eval_some_collapse ρ N σ l hN hσ hn
      simp only [eval, collapse]
      rw [ih]
  | .param i, _hN, _hσ, _hn => rfl
  | .max a b, hN, hσ, hn => by
      have nfa :=
        noneOf_max_left_false N σ a b hn
      have nfb :=
        noneOf_max_right_false N σ a b hn
      have iha :=
        eval_some_collapse ρ N σ a
          (noneOf_hN_left ρ N a b hN)
          (noneOf_hσ_left ρ σ a b hσ) nfa
      have ihb :=
        eval_some_collapse ρ N σ b
          (noneOf_hN_right ρ N a b hN)
          (noneOf_hσ_right ρ σ a b hσ) nfb
      simp only [collapse]
      rw [eval_max_match]
      rw [eval_max_match]
      rw [iha, ihb]
  | .imax a b, hN, hσ, hn => by
      have nfb :=
        noneOf_imax_snd_false N σ a b hn
      have ihb_nv :=
        noneOf_valZero ρ N σ b
          (noneOf_hN_imax_right ρ N a b hN)
          (noneOf_hσ_imax_right ρ σ a b hσ)
      cases hvz : valZero σ b with
      | true =>
          have hb0 :
              eval ρ b = some 0 :=
            eval_zero_of_valZero ρ N σ b
              ihb_nv.2 nfb hvz
          simp only [collapse, nfb, hvz,
            eval]
          rw [hb0]
          rfl
      | false =>
          have nfa :=
            noneOf_imax_fst_false N σ a b
              hn hvz
          have iha :=
            eval_some_collapse ρ N σ a
              (noneOf_hN_imax_left ρ N a b
                hN)
              (noneOf_hσ_imax_left ρ σ a b
                hσ) nfa
          have ihb :=
            eval_some_collapse ρ N σ b
              (noneOf_hN_imax_right ρ N a b
                hN)
              (noneOf_hσ_imax_right ρ σ a b
                hσ) nfb
          simp only [collapse, nfb, hvz]
          rw [eval_imax_match,
            eval_imax_match]
          rw [iha, ihb]

theorem collapse_noneOf
    (N σ : List Nat) :
    ∀ l : Level,
      noneOf N σ l = false →
        noneOf N σ (collapse N σ l) = false
  | .zero, _ => rfl
  | .succ l, hn =>
      collapse_noneOf N σ l hn
  | .param i, hn => hn
  | .max a b, hn => by
      have nfa :=
        noneOf_max_left_false N σ a b hn
      have nfb :=
        noneOf_max_right_false N σ a b hn
      have ca :=
        collapse_noneOf N σ a nfa
      have cb :=
        collapse_noneOf N σ b nfb
      simp only [collapse, noneOf]
      rw [ca, cb]
      rfl
  | .imax a b, hn => by
      have nfb :=
        noneOf_imax_snd_false N σ a b hn
      cases hvz : valZero σ b with
      | true =>
          simp only [collapse, nfb, hvz]
          rfl
      | false =>
          have nfa :=
            noneOf_imax_fst_false N σ a b
              hn hvz
          have ca :=
            collapse_noneOf N σ a nfa
          have cb :=
            collapse_noneOf N σ b nfb
          simp only [collapse, nfb, hvz,
            noneOf]
          rw [cb]
          cases valZero σ (collapse N σ b)
            with
          | true =>
              rw [not_true, and_false_left]
              rfl
          | false =>
              rw [not_false, and_true_left,
                or_false_left, ca]

theorem collapse_not_in_N
    (N σ : List Nat) :
    ∀ l : Level,
      noneOf N σ l = false →
      ∀ i,
        memNat i
            (paramsOf (collapse N σ l)) =
              true →
          memNat i N = false
  | .zero, _hn, i, hi =>
      Bool.noConfusion hi
  | .succ l, hn, i, hi =>
      collapse_not_in_N N σ l hn i hi
  | .param j, hn, i, hi => by
      simp only [collapse, paramsOf,
        memNat] at hi hn
      cases hix : decide (i = j) with
      | true =>
          have hix' : i = j :=
            of_decide_eq_true hix
          rw [hix']
          exact hn
      | false =>
          simp only [hix] at hi
          exact Bool.noConfusion hi
  | .max a b, hn, i, hi => by
      have nfa :=
        noneOf_max_left_false N σ a b hn
      have nfb :=
        noneOf_max_right_false N σ a b hn
      simp only [collapse] at hi
      rw [memNat_paramsOf_max] at hi
      cases ha : memNat i
          (paramsOf (collapse N σ a)) with
      | true =>
          exact collapse_not_in_N N σ a
            nfa i ha
      | false =>
          simp only [ha] at hi
          exact collapse_not_in_N N σ b
            nfb i hi
  | .imax a b, hn, i, hi => by
      have nfb :=
        noneOf_imax_snd_false N σ a b hn
      cases hvz : valZero σ b with
      | true =>
          simp only [collapse, nfb, hvz,
            paramsOf, memNat] at hi
          exact Bool.noConfusion hi
      | false =>
          have nfa :=
            noneOf_imax_fst_false N σ a b
              hn hvz
          simp only [collapse, nfb, hvz]
            at hi
          rw [memNat_paramsOf_imax] at hi
          cases ha : memNat i
              (paramsOf
                (collapse N σ a)) with
          | true =>
              exact collapse_not_in_N N σ
                a nfa i ha
          | false =>
              simp only [ha] at hi
              exact collapse_not_in_N N σ
                b nfb i hi

/- R-LevelNone (3): the fourth and final
`decEqN`. All none-sets N ⊆ P and zero-
patterns σ on P ∖ N. Finite: 2^|P| none-
sets, 2^|P∖N| patterns. Installed as
`decEqN` at rung (4) with soundness. -/

def minusNat (N : List Nat) :
    List Nat → List Nat
  | [] => []
  | i :: is =>
      match memNat i N with
      | true => minusNat N is
      | false => i :: minusNat N is

def consEach (i : Nat) :
    List (List Nat) → List (List Nat)
  | [] => []
  | xs :: xss =>
      (i :: xs) :: consEach i xss

def allSubsets : List Nat → List (List Nat)
  | [] => [[]]
  | i :: is =>
      match allSubsets is with
      | rest =>
          rest ++ consEach i rest

def agreeAt (N σ : List Nat)
    (l1 l2 : Level) : Bool :=
  decide (noneOf N σ l1 =
    noneOf N σ l2) &&
    (noneOf N σ l1 ||
      decide
        (nf (spec σ (collapse N σ l1)) =
          nf (spec σ (collapse N σ l2))))

def allSigmaAgree (l1 l2 : Level)
    (N : List Nat) :
    List (List Nat) → Bool
  | [] => true
  | σ :: rest =>
      match agreeAt N σ l1 l2 with
      | false => false
      | true =>
          allSigmaAgree l1 l2 N rest

def allNoneAgree (l1 l2 : Level)
    (P : List Nat) :
    List (List Nat) → Bool
  | [] => true
  | N :: rest =>
      match allSigmaAgree l1 l2 N
          (allSubsets (minusNat N P)) with
      | false => false
      | true =>
          allNoneAgree l1 l2 P rest

/-- R-LevelNone (3): the final decider,
not yet `decEqN` (soundness is rung 4). -/
def decEqNNone (l1 l2 : Level) : Bool :=
  match unionNat (paramsOf l1)
      (paramsOf l2) with
  | P =>
      allNoneAgree l1 l2 P
        (allSubsets P)

#eval (if decEqNNone
    (.imax (.succ .zero) .zero) .zero =
      true then 0
  else panic "H-6l: decider imax")
#eval (if decEqNNone (.param 0) (.param 1) =
    false then 0
  else panic "H-6l: decider params")
#eval (if decEqNNone
    (.imax .zero (.param 0)) (.param 0) =
      true then 0
  else panic "H-6l: decider unbound")

def eqNats : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
      decide (x = y) && eqNats xs ys
  | _, _ => false

theorem eqNats_refl :
    ∀ xs, eqNats xs xs = true
  | [] => rfl
  | x :: xs => by
      simp only [eqNats]
      cases hx : decide (x = x) with
      | true => exact eqNats_refl xs
      | false =>
          exact False.elim
            (of_decide_eq_false hx rfl)

theorem eqNats_cons (i : Nat)
    (xs ys : List Nat) :
    eqNats (i :: xs) (i :: ys) =
      eqNats xs ys := by
  simp only [eqNats]
  cases hi : decide (i = i) with
  | true => cases eqNats xs ys <;> rfl
  | false =>
      exact False.elim
        (of_decide_eq_false hi rfl)

theorem eqNats_eq :
    ∀ xs ys,
      eqNats xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
      simp only [eqNats] at h
      have ⟨hx, ht⟩ := and_true h
      have hxy : x = y :=
        of_decide_eq_true hx
      have htl := eqNats_eq xs ys ht
      rw [hxy, htl]

def memLists (xs : List Nat) :
    List (List Nat) → Bool
  | [] => false
  | ys :: yss =>
      match eqNats xs ys with
      | true => true
      | false => memLists xs yss

theorem memLists_consEach (i : Nat)
    (xs : List Nat) :
    ∀ xss,
      memLists xs xss = true →
        memLists (i :: xs)
          (consEach i xss) = true
  | [], h => Bool.noConfusion h
  | ys :: yss, h => by
      simp only [consEach, memLists]
      rw [eqNats_cons]
      cases heq : eqNats xs ys with
      | true => rfl
      | false =>
          simp only [memLists, heq] at h
          exact memLists_consEach i xs
            yss h

theorem memLists_append_left
    (xs : List Nat) :
    ∀ as bs,
      memLists xs as = true →
        memLists xs (as ++ bs) = true
  | [], bs, h => Bool.noConfusion h
  | a :: as, bs, h => by
      simp only [memLists] at h ⊢
      cases heq : eqNats xs a with
      | true => rfl
      | false =>
          simp only [heq] at h
          exact memLists_append_left xs
            as bs h

theorem memLists_append_right
    (xs : List Nat) :
    ∀ as bs,
      memLists xs bs = true →
        memLists xs (as ++ bs) = true
  | [], bs, h => h
  | a :: as, bs, h => by
      simp only [memLists]
      cases eqNats xs a with
      | true => rfl
      | false =>
          exact memLists_append_right xs
            as bs h

theorem allSubsets_cons (i : Nat)
    (is : List Nat) :
    allSubsets (i :: is) =
      allSubsets is ++
        consEach i (allSubsets is) := rfl

theorem noneSetOf_mem_allSubsets
    (ρ : Nat → Option Nat) :
    ∀ P,
      memLists (noneSetOf ρ P)
        (allSubsets P) = true
  | [] => by
      simp only [noneSetOf, allSubsets,
        memLists, eqNats]
  | i :: is => by
      have ih :=
        noneSetOf_mem_allSubsets ρ is
      rw [allSubsets_cons]
      cases hρ : ρ i with
      | none =>
          simp only [noneSetOf, hρ]
          have hcons :=
            memLists_consEach i
              (noneSetOf ρ is)
              (allSubsets is) ih
          exact memLists_append_right
            (i :: noneSetOf ρ is)
            (allSubsets is)
            (consEach i (allSubsets is))
            hcons
      | some n =>
          simp only [noneSetOf, hρ]
          exact memLists_append_left
            (noneSetOf ρ is)
            (allSubsets is)
            (consEach i (allSubsets is))
            ih

theorem zeroSetPartial_mem_allSubsets
    (ρ : Nat → Option Nat) :
    ∀ P,
      memLists (zeroSetPartial ρ P)
        (allSubsets P) = true
  | [] => by
      simp only [zeroSetPartial,
        allSubsets, memLists, eqNats]
  | i :: is => by
      have ih :=
        zeroSetPartial_mem_allSubsets ρ is
      rw [allSubsets_cons]
      cases hρ : ρ i with
      | none =>
          simp only [zeroSetPartial, hρ]
          exact memLists_append_left
            (zeroSetPartial ρ is)
            (allSubsets is)
            (consEach i (allSubsets is))
            ih
      | some n =>
          cases n with
          | zero =>
              simp only [zeroSetPartial,
                hρ]
              have hcons :=
                memLists_consEach i
                  (zeroSetPartial ρ is)
                  (allSubsets is) ih
              exact memLists_append_right
                (i :: zeroSetPartial ρ is)
                (allSubsets is)
                (consEach i
                  (allSubsets is))
                hcons
          | succ n =>
              simp only [zeroSetPartial,
                hρ]
              exact memLists_append_left
                (zeroSetPartial ρ is)
                (allSubsets is)
                (consEach i
                  (allSubsets is))
                ih

theorem allSigmaAgree_of_mem
    (l1 l2 : Level) (N : List Nat) :
    ∀ σs σ,
      allSigmaAgree l1 l2 N σs = true →
      memLists σ σs = true →
        agreeAt N σ l1 l2 = true
  | [], σ, _, hm => Bool.noConfusion hm
  | σ0 :: rest, σ, h, hm => by
      simp only [allSigmaAgree] at h
      simp only [memLists] at hm
      cases heq : eqNats σ σ0 with
      | true =>
          have hσeq : σ = σ0 :=
            eqNats_eq σ σ0 heq
          cases h0 : agreeAt N σ0 l1 l2 with
          | false =>
              simp only [h0] at h
              exact Bool.noConfusion h
          | true =>
              rw [hσeq]
              exact h0
      | false =>
          simp only [heq] at hm
          cases h0 : agreeAt N σ0 l1 l2 with
          | false =>
              simp only [h0] at h
              exact Bool.noConfusion h
          | true =>
              simp only [h0] at h
              exact allSigmaAgree_of_mem
                l1 l2 N rest σ h hm

theorem allNoneAgree_of_mem
    (l1 l2 : Level) (P : List Nat) :
    ∀ Ns N,
      allNoneAgree l1 l2 P Ns = true →
      memLists N Ns = true →
        allSigmaAgree l1 l2 N
          (allSubsets (minusNat N P)) =
            true
  | [], N, _, hm => Bool.noConfusion hm
  | N0 :: rest, N, h, hm => by
      simp only [allNoneAgree] at h
      simp only [memLists] at hm
      cases heq : eqNats N N0 with
      | true =>
          have hNeq : N = N0 :=
            eqNats_eq N N0 heq
          cases h0 :
            allSigmaAgree l1 l2 N0
              (allSubsets
                (minusNat N0 P)) with
          | false =>
              simp only [h0] at h
              exact Bool.noConfusion h
          | true =>
              rw [hNeq]
              exact h0
      | false =>
          simp only [heq] at hm
          cases h0 :
            allSigmaAgree l1 l2 N0
              (allSubsets
                (minusNat N0 P)) with
          | false =>
              simp only [h0] at h
              exact Bool.noConfusion h
          | true =>
              simp only [h0] at h
              exact allNoneAgree_of_mem
                l1 l2 P rest N h hm

theorem agreeAt_inv
    (N σ : List Nat) (l1 l2 : Level)
    (h : agreeAt N σ l1 l2 = true) :
    noneOf N σ l1 = noneOf N σ l2 ∧
      (noneOf N σ l1 = true ∨
        nf (spec σ (collapse N σ l1)) =
          nf (spec σ (collapse N σ l2))) :=
  by
    simp only [agreeAt] at h
    have ⟨heq, hor⟩ := and_true h
    have hnone :
        noneOf N σ l1 = noneOf N σ l2 :=
      of_decide_eq_true heq
    constructor
    · exact hnone
    · cases hn : noneOf N σ l1 with
      | true => exact Or.inl rfl
      | false =>
          rw [hn] at hor
          rw [or_false_left] at hor
          exact Or.inr
            (of_decide_eq_true hor)

theorem memNat_minusNat (N : List Nat) :
    ∀ xs i,
      memNat i (minusNat N xs) =
        (memNat i xs && !memNat i N)
  | [], i => by
      simp only [minusNat, memNat]
      cases memNat i N <;> rfl
  | x :: xs, i => by
      simp only [minusNat]
      cases hxN : memNat x N with
      | true =>
          have ih :=
            memNat_minusNat N xs i
          simp only [memNat]
          cases hix : decide (i = x) with
          | true =>
              have hix' : i = x :=
                of_decide_eq_true hix
              rw [hix'] at ih ⊢
              rw [ih, hxN]
              cases memNat x xs <;> rfl
          | false => exact ih
      | false =>
          simp only [memNat]
          cases hix : decide (i = x) with
          | true =>
              have hix' : i = x :=
                of_decide_eq_true hix
              rw [hix', hxN]
              rfl
          | false =>
              exact memNat_minusNat N xs i

theorem collapse_params_subset
    (N σ : List Nat) :
    ∀ l i,
      memNat i
          (paramsOf (collapse N σ l)) =
            true →
        memNat i (paramsOf l) = true
  | .zero, i, hi => Bool.noConfusion hi
  | .succ l, i, hi =>
      collapse_params_subset N σ l i hi
  | .param j, i, hi => hi
  | .max a b, i, hi => by
      simp only [collapse] at hi
      rw [memNat_paramsOf_max] at hi ⊢
      cases ha : memNat i
          (paramsOf (collapse N σ a)) with
      | true =>
          have h :=
            collapse_params_subset N σ a
              i ha
          rw [h]
          rfl
      | false =>
          simp only [ha] at hi
          have h :=
            collapse_params_subset N σ b
              i hi
          cases memNat i (paramsOf a) with
          | true => rfl
          | false =>
              rw [h]
              rfl
  | .imax a b, i, hi => by
      cases hb : noneOf N σ b with
      | true =>
          simp only [collapse, hb] at hi
          rw [memNat_paramsOf_imax] at hi ⊢
          cases ha : memNat i
              (paramsOf
                (collapse N σ a)) with
          | true =>
              have h :=
                collapse_params_subset
                  N σ a i ha
              rw [h]
              rfl
          | false =>
              simp only [ha] at hi
              have h :=
                collapse_params_subset
                  N σ b i hi
              cases memNat i
                  (paramsOf a) with
              | true => rfl
              | false =>
                  rw [h]
                  rfl
      | false =>
          cases hvz : valZero σ b with
          | true =>
              simp only [collapse, hb,
                hvz, paramsOf, memNat]
                at hi
              exact Bool.noConfusion hi
          | false =>
              simp only [collapse, hb,
                hvz] at hi
              rw [memNat_paramsOf_imax]
                at hi ⊢
              cases ha : memNat i
                  (paramsOf
                    (collapse N σ a)) with
              | true =>
                  have h :=
                    collapse_params_subset
                      N σ a i ha
                  rw [h]
                  rfl
              | false =>
                  simp only [ha] at hi
                  have h :=
                    collapse_params_subset
                      N σ b i hi
                  cases memNat i
                      (paramsOf a) with
                  | true => rfl
                  | false =>
                      rw [h]
                      rfl

theorem fill0_eq
    (ρ : Nat → Option Nat)
    (i n : Nat) (h : ρ i = some n) :
    fill0 ρ i = n := by
  simp only [fill0]
  rw [h]
  rfl

theorem spec_sigma_of_hσ
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (hN : ∀ i,
      memNat i (paramsOf l) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ : ∀ i,
      memNat i (paramsOf l) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hn : noneOf N σ l = false)
    (i : Nat)
    (hi : memNat i
        (paramsOf (collapse N σ l)) =
          true) :
    memNat i σ = decide (fill0 ρ i = 0) := by
  have hi0 :=
    collapse_params_subset N σ l i hi
  have hiN :
      memNat i N = false :=
    collapse_not_in_N N σ l hn i hi
  have hne : ρ i ≠ none := by
    intro he
    have ht := (hN i hi0).mpr he
    rw [ht] at hiN
    exact Bool.noConfusion hiN
  have hσi := hσ i hi0 hne
  cases hρ : ρ i with
  | none => exact False.elim (hne hρ)
  | some n =>
      have hf := fill0_eq ρ i n hρ
      cases n with
      | zero =>
          rw [hf]
          have ht : memNat i σ = true :=
            hσi.mpr (by rw [hρ])
          rw [ht]
          rfl
      | succ n =>
          rw [hf]
          have hfals :
              memNat i σ = false := by
            cases hs : memNat i σ with
            | false => rfl
            | true =>
                have h0 := hσi.mp hs
                rw [hρ] at h0
                injection h0 with h0'
                exact False.elim
                  (Nat.succ_ne_zero n h0')
          rw [hfals]
          rfl

theorem eval_fill0_collapse
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l : Level)
    (hN : ∀ i,
      memNat i (paramsOf l) = true →
        (memNat i N = true ↔ ρ i = none))
    (_hσ : ∀ i,
      memNat i (paramsOf l) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hn : noneOf N σ l = false) :
    eval ρ (collapse N σ l) =
      eval (fun i => some (fill0 ρ i))
        (collapse N σ l) :=
  eval_ignore_unused ρ
    (fun i => some (fill0 ρ i))
    (collapse N σ l)
    (fun i hd => by
      have hp :=
        dependsOn_mem_params
          (collapse N σ l) i hd
      have hiN :=
        collapse_not_in_N N σ l hn i hp
      have hi0 :=
        collapse_params_subset N σ l i hp
      have hne : ρ i ≠ none := by
        intro he
        have ht := (hN i hi0).mpr he
        rw [ht] at hiN
        exact Bool.noConfusion hiN
      exact fill0_of_not_none ρ i hne)

theorem eval_eq_of_nf_spec
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l1 l2 : Level)
    (hN1 : ∀ i,
      memNat i (paramsOf l1) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ1 : ∀ i,
      memNat i (paramsOf l1) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hN2 : ∀ i,
      memNat i (paramsOf l2) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ2 : ∀ i,
      memNat i (paramsOf l2) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hn1 : noneOf N σ l1 = false)
    (hn2 : noneOf N σ l2 = false)
    (hnf : nf (spec σ (collapse N σ l1)) =
        nf (spec σ (collapse N σ l2))) :
    eval ρ l1 = eval ρ l2 := by
  have e1 :=
    eval_some_collapse ρ N σ l1 hN1 hσ1
      hn1
  have e2 :=
    eval_some_collapse ρ N σ l2 hN2 hσ2
      hn2
  have f1 :=
    eval_fill0_collapse ρ N σ l1 hN1 hσ1
      hn1
  have f2 :=
    eval_fill0_collapse ρ N σ l2 hN2 hσ2
      hn2
  have s1 :=
    spec_eval σ (fill0 ρ)
      (collapse N σ l1)
      (fun i hi =>
        spec_sigma_of_hσ ρ N σ l1 hN1 hσ1
          hn1 i hi)
  have s2 :=
    spec_eval σ (fill0 ρ)
      (collapse N σ l2)
      (fun i hi =>
        spec_sigma_of_hσ ρ N σ l2 hN2 hσ2
          hn2 i hi)
  have n1 :=
    nf_eval (spec σ (collapse N σ l1))
      (fun i => some (Nat.pred (fill0 ρ i)))
  have n2 :=
    nf_eval (spec σ (collapse N σ l2))
      (fun i => some (Nat.pred (fill0 ρ i)))
  rw [e1, e2, f1, f2, s1, s2, n1, n2, hnf]

theorem noneSetOf_hN_subset
    (ρ : Nat → Option Nat)
    (P : List Nat) (l : Level)
    (hsub : ∀ i,
      memNat i (paramsOf l) = true →
        memNat i P = true) :
    ∀ i, memNat i (paramsOf l) = true →
      (memNat i (noneSetOf ρ P) = true ↔
        ρ i = none) :=
  fun i hi => by
    have e :=
      memNat_noneSetOf_eq ρ P i (hsub i hi)
    constructor
    · intro ht
      cases hρ : ρ i with
      | none => rfl
      | some n =>
          rw [hρ] at e
          rw [e] at ht
          exact Bool.noConfusion ht
    · intro hn
      cases hρ : ρ i with
      | none =>
          rw [hρ] at e
          exact e
      | some n =>
          rw [hρ] at hn
          exact Option.noConfusion hn

theorem zeroSet_hσ_subset
    (ρ : Nat → Option Nat)
    (P N σ : List Nat) (l : Level)
    (hσdef : σ = zeroSetPartial ρ
      (minusNat N P))
    (hN : ∀ i,
      memNat i (paramsOf l) = true →
        (memNat i N = true ↔ ρ i = none))
    (hsub : ∀ i,
      memNat i (paramsOf l) = true →
        memNat i P = true) :
    ∀ i, memNat i (paramsOf l) = true →
      ρ i ≠ none →
        (memNat i σ = true ↔
          ρ i = some 0) :=
  fun i hi hne => by
    have hiP := hsub i hi
    have hiN : memNat i N = false := by
      cases hn : memNat i N with
      | false => rfl
      | true =>
          have he := (hN i hi).mp hn
          exact False.elim (hne he)
    have him :
        memNat i (minusNat N P) = true := by
      rw [memNat_minusNat, hiP, hiN]
      rfl
    have e :=
      memNat_zeroSetPartial_eq ρ
        (minusNat N P) i him
    rw [hσdef]
    cases hρ : ρ i with
    | none => exact False.elim (hne hρ)
    | some n =>
        cases n with
        | zero =>
            rw [hρ] at e
            constructor
            · intro _
              rfl
            · intro _
              exact e
        | succ n =>
            rw [hρ] at e
            constructor
            · intro ht
              rw [e] at ht
              exact Bool.noConfusion ht
            · intro h0
              injection h0 with h0'
              exact False.elim
                (Nat.succ_ne_zero n h0')

theorem eval_eq_of_agreeAt
    (ρ : Nat → Option Nat)
    (N σ : List Nat) (l1 l2 : Level)
    (hN1 : ∀ i,
      memNat i (paramsOf l1) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ1 : ∀ i,
      memNat i (paramsOf l1) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (hN2 : ∀ i,
      memNat i (paramsOf l2) = true →
        (memNat i N = true ↔ ρ i = none))
    (hσ2 : ∀ i,
      memNat i (paramsOf l2) = true →
        ρ i ≠ none →
          (memNat i σ = true ↔
            ρ i = some 0))
    (h : agreeAt N σ l1 l2 = true) :
    eval ρ l1 = eval ρ l2 := by
  have ⟨heq, hor⟩ := agreeAt_inv N σ l1 l2 h
  cases hn1 : noneOf N σ l1 with
  | true =>
      have hn2 : noneOf N σ l2 = true := by
        rw [hn1] at heq
        exact heq.symm
      have e1 :=
        (noneOf_valZero ρ N σ l1 hN1
          hσ1).1.mpr hn1
      have e2 :=
        (noneOf_valZero ρ N σ l2 hN2
          hσ2).1.mpr hn2
      rw [e1, e2]
  | false =>
      have hn2 : noneOf N σ l2 = false := by
        rw [hn1] at heq
        exact heq.symm
      have hnf :
          nf (spec σ (collapse N σ l1)) =
            nf (spec σ (collapse N σ l2)) :=
        match hor with
        | Or.inl ht => by
            rw [hn1] at ht
            exact Bool.noConfusion ht
        | Or.inr hnf => hnf
      exact eval_eq_of_nf_spec ρ N σ l1 l2
        hN1 hσ1 hN2 hσ2 hn1 hn2 hnf

/-- R-LevelNone (3)(4): the fourth and
final `decEqN`. T3 MISMATCH permitted
by R-LevelNone (3). -/
def decEqN (l1 l2 : Level) : Bool :=
  decEqNNone l1 l2

theorem decEqN_sound (l1 l2 : Level) :
    decEqN l1 l2 = true → eqN l1 l2 := by
  intro h ρ
  simp only [decEqN, decEqNNone] at h
  let P :=
    unionNat (paramsOf l1) (paramsOf l2)
  let N := noneSetOf ρ P
  let σ :=
    zeroSetPartial ρ (minusNat N P)
  have hP : P =
      unionNat (paramsOf l1)
        (paramsOf l2) := rfl
  have hsub1 : ∀ i,
      memNat i (paramsOf l1) = true →
        memNat i P = true :=
    fun i hi =>
      mem_params_of_union_left i
        (paramsOf l1) (paramsOf l2) hi
  have hsub2 : ∀ i,
      memNat i (paramsOf l2) = true →
        memNat i P = true :=
    fun i hi =>
      mem_params_of_union_right i
        (paramsOf l1) (paramsOf l2) hi
  have hN1 :=
    noneSetOf_hN_subset ρ P l1 hsub1
  have hN2 :=
    noneSetOf_hN_subset ρ P l2 hsub2
  have hσ1 :=
    zeroSet_hσ_subset ρ P N σ l1 rfl hN1
      hsub1
  have hσ2 :=
    zeroSet_hσ_subset ρ P N σ l2 rfl hN2
      hsub2
  have hmemN :=
    noneSetOf_mem_allSubsets ρ P
  have hsig :=
    allNoneAgree_of_mem l1 l2 P
      (allSubsets P) N h hmemN
  have hmemσ :=
    zeroSetPartial_mem_allSubsets ρ
      (minusNat N P)
  have hag :=
    allSigmaAgree_of_mem l1 l2 N
      (allSubsets (minusNat N P)) σ
      hsig hmemσ
  exact eval_eq_of_agreeAt ρ N σ l1 l2
    hN1 hσ1 hN2 hσ2 hag

def rhoNS (N σ : List Nat)
    (i : Nat) : Option Nat :=
  match memNat i N with
  | true => none
  | false =>
      match memNat i σ with
      | true => some 0
      | false => some 1

def rhoNSt (N σ : List Nat)
    (τ : Nat → Nat) (i : Nat) :
    Option Nat :=
  match memNat i N with
  | true => none
  | false =>
      match memNat i σ with
      | true => some 0
      | false => some (τ i + 1)

theorem rhoNS_hN (N σ : List Nat)
    (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      (memNat i N = true ↔
        rhoNS N σ i = none) :=
  fun i _ => by
    constructor
    · intro hN
      simp only [rhoNS, hN]
    · intro hnone
      simp only [rhoNS] at hnone
      cases hN : memNat i N with
      | true => rfl
      | false =>
          simp only [hN] at hnone
          cases hσ : memNat i σ with
          | true =>
              simp only [hσ] at hnone
              exact False.elim
                (Option.noConfusion hnone)
          | false =>
              simp only [hσ] at hnone
              exact False.elim
                (Option.noConfusion hnone)

theorem rhoNS_hσ (N σ : List Nat)
    (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      rhoNS N σ i ≠ none →
        (memNat i σ = true ↔
          rhoNS N σ i = some 0) :=
  fun i _ hne => by
    cases hN : memNat i N with
    | true =>
        simp only [rhoNS, hN] at hne
        exact False.elim (hne rfl)
    | false =>
        constructor
        · intro hσ
          simp only [rhoNS, hN, hσ]
        · intro hz
          simp only [rhoNS, hN] at hz
          cases hσ : memNat i σ with
          | true => rfl
          | false =>
              simp only [hσ] at hz
              injection hz with hz'
              exact False.elim
                (Nat.succ_ne_zero 0 hz')

theorem rhoNSt_hN (N σ : List Nat)
    (τ : Nat → Nat) (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      (memNat i N = true ↔
        rhoNSt N σ τ i = none) :=
  fun i _ => by
    constructor
    · intro hN
      simp only [rhoNSt, hN]
    · intro hnone
      simp only [rhoNSt] at hnone
      cases hN : memNat i N with
      | true => rfl
      | false =>
          simp only [hN] at hnone
          cases hσ : memNat i σ with
          | true =>
              simp only [hσ] at hnone
              exact False.elim
                (Option.noConfusion hnone)
          | false =>
              simp only [hσ] at hnone
              exact False.elim
                (Option.noConfusion hnone)

theorem rhoNSt_hσ (N σ : List Nat)
    (τ : Nat → Nat) (l : Level) :
    ∀ i, memNat i (paramsOf l) = true →
      rhoNSt N σ τ i ≠ none →
        (memNat i σ = true ↔
          rhoNSt N σ τ i = some 0) :=
  fun i _ hne => by
    cases hN : memNat i N with
    | true =>
        simp only [rhoNSt, hN] at hne
        exact False.elim (hne rfl)
    | false =>
        constructor
        · intro hσ
          simp only [rhoNSt, hN, hσ]
        · intro hz
          simp only [rhoNSt, hN] at hz
          cases hσ : memNat i σ with
          | true => rfl
          | false =>
              simp only [hσ] at hz
              injection hz with hz'
              exact False.elim
                (Nat.succ_ne_zero (τ i)
                  hz')

theorem noneOf_eq_of_eqN
    (N σ : List Nat) (l1 l2 : Level)
    (h : eqN l1 l2) :
    noneOf N σ l1 = noneOf N σ l2 := by
  have e := h (rhoNS N σ)
  have i1 :=
    noneOf_valZero (rhoNS N σ) N σ l1
      (rhoNS_hN N σ l1)
      (rhoNS_hσ N σ l1)
  have i2 :=
    noneOf_valZero (rhoNS N σ) N σ l2
      (rhoNS_hN N σ l2)
      (rhoNS_hσ N σ l2)
  cases hn1 : noneOf N σ l1 with
  | true =>
      have en := i1.1.mpr hn1
      rw [e] at en
      have hn2 := i2.1.mp en
      exact hn2.symm
  | false =>
      have hne :
          eval (rhoNS N σ) l1 ≠ none :=
        eval_ne_none_of_noneOf_false
          (rhoNS N σ) N σ l1
          (rhoNS_hN N σ l1)
          (rhoNS_hσ N σ l1) hn1
      have hn2 :
          noneOf N σ l2 = false :=
        noneOf_false_of_eval_some
          (rhoNS N σ) N σ l2 i2.1 (by
            intro he
            rw [← e] at he
            exact hne he)
      exact hn2.symm

theorem paramsOf_spec (σ : List Nat) :
    ∀ l i,
      memNat i (paramsOf (spec σ l)) =
          true →
        memNat i (paramsOf l) = true ∧
          memNat i σ = false
  | .zero, i, hi => Bool.noConfusion hi
  | .succ l, i, hi =>
      paramsOf_spec σ l i hi
  | .param j, i, hi => by
      simp only [spec, specParam] at hi
      cases hm : memNat j σ with
      | true =>
          simp only [hm, paramsOf,
            memNat] at hi
          exact Bool.noConfusion hi
      | false =>
          simp only [hm, paramsOf,
            memNat] at hi
          cases hix : decide (i = j) with
          | true =>
              have hix' : i = j :=
                of_decide_eq_true hix
              rw [hix']
              exact ⟨memNat_paramsOf_param j,
                hm⟩
          | false =>
              simp only [hix] at hi
              exact Bool.noConfusion hi
  | .max a b, i, hi => by
      simp only [spec] at hi
      rw [memNat_paramsOf_max] at hi ⊢
      cases ha : memNat i
          (paramsOf (spec σ a)) with
      | true =>
          have ⟨hp, hn⟩ :=
            paramsOf_spec σ a i ha
          rw [hp]
          exact ⟨rfl, hn⟩
      | false =>
          simp only [ha] at hi
          have ⟨hp, hn⟩ :=
            paramsOf_spec σ b i hi
          constructor
          · cases memNat i (paramsOf a) with
            | true => rfl
            | false => rw [hp]; rfl
          · exact hn
  | .imax a b, i, hi => by
      simp only [spec] at hi
      rw [memNat_paramsOf_imax] at hi ⊢
      cases ha : memNat i
          (paramsOf (spec σ a)) with
      | true =>
          have ⟨hp, hn⟩ :=
            paramsOf_spec σ a i ha
          rw [hp]
          exact ⟨rfl, hn⟩
      | false =>
          simp only [ha] at hi
          have ⟨hp, hn⟩ :=
            paramsOf_spec σ b i hi
          constructor
          · cases memNat i (paramsOf a) with
            | true => rfl
            | false => rw [hp]; rfl
          · exact hn

theorem evalTotal_nf_spec_eq
    (N σ : List Nat) (l1 l2 : Level)
    (h : eqN l1 l2)
    (hn1 : noneOf N σ l1 = false)
    (hn2 : noneOf N σ l2 = false)
    (τ : Nat → Nat) :
    evalTotal τ
        (nf (spec σ (collapse N σ l1))) =
      evalTotal τ
        (nf (spec σ (collapse N σ l2))) := by
  have e := h (rhoNSt N σ τ)
  have e1 :=
    eval_some_collapse (rhoNSt N σ τ) N σ
      l1 (rhoNSt_hN N σ τ l1)
      (rhoNSt_hσ N σ τ l1) hn1
  have e2 :=
    eval_some_collapse (rhoNSt N σ τ) N σ
      l2 (rhoNSt_hN N σ τ l2)
      (rhoNSt_hσ N σ τ l2) hn2
  have f1 :=
    eval_fill0_collapse (rhoNSt N σ τ) N σ
      l1 (rhoNSt_hN N σ τ l1)
      (rhoNSt_hσ N σ τ l1) hn1
  have f2 :=
    eval_fill0_collapse (rhoNSt N σ τ) N σ
      l2 (rhoNSt_hN N σ τ l2)
      (rhoNSt_hσ N σ τ l2) hn2
  have s1 :=
    spec_eval σ (fill0 (rhoNSt N σ τ))
      (collapse N σ l1)
      (fun i hi =>
        spec_sigma_of_hσ (rhoNSt N σ τ)
          N σ l1 (rhoNSt_hN N σ τ l1)
          (rhoNSt_hσ N σ τ l1) hn1 i hi)
  have s2 :=
    spec_eval σ (fill0 (rhoNSt N σ τ))
      (collapse N σ l2)
      (fun i hi =>
        spec_sigma_of_hσ (rhoNSt N σ τ)
          N σ l2 (rhoNSt_hN N σ τ l2)
          (rhoNSt_hσ N σ τ l2) hn2 i hi)
  have n1 :=
    nf_eval (spec σ (collapse N σ l1))
      (fun i => some (τ i))
  have n2 :=
    nf_eval (spec σ (collapse N σ l2))
      (fun i => some (τ i))
  have t1 :=
    eval_total τ
      (nf (spec σ (collapse N σ l1)))
  have t2 :=
    eval_total τ
      (nf (spec σ (collapse N σ l2)))
  have ign1 :=
    eval_ignore_unused
      (fun i =>
        some (Nat.pred
          (fill0 (rhoNSt N σ τ) i)))
      (fun i => some (τ i))
      (spec σ (collapse N σ l1))
      (fun i hd => by
        have hmem :=
          dependsOn_mem_params
            (spec σ (collapse N σ l1))
            i hd
        have ⟨hp, hnσ⟩ :=
          paramsOf_spec σ
            (collapse N σ l1) i hmem
        have hiN :=
          collapse_not_in_N N σ l1 hn1 i
            hp
        have hf :
            fill0 (rhoNSt N σ τ) i =
              τ i + 1 := by
          simp only [fill0, rhoNSt]
          rw [hiN, hnσ]
          rfl
        exact congrArg some (by
          rw [hf]
          rfl))
  have ign2 :=
    eval_ignore_unused
      (fun i =>
        some (Nat.pred
          (fill0 (rhoNSt N σ τ) i)))
      (fun i => some (τ i))
      (spec σ (collapse N σ l2))
      (fun i hd => by
        have hmem :=
          dependsOn_mem_params
            (spec σ (collapse N σ l2))
            i hd
        have ⟨hp, hnσ⟩ :=
          paramsOf_spec σ
            (collapse N σ l2) i hmem
        have hiN :=
          collapse_not_in_N N σ l2 hn2 i
            hp
        have hf :
            fill0 (rhoNSt N σ τ) i =
              τ i + 1 := by
          simp only [fill0, rhoNSt]
          rw [hiN, hnσ]
          rfl
        exact congrArg some (by
          rw [hf]
          rfl))
  have n1' :
      eval (fun i => some (τ i))
          (spec σ (collapse N σ l1)) =
        eval (fun i => some (τ i))
          (nf (spec σ
            (collapse N σ l1))) := by
    simp only [denote] at n1
    exact n1
  have n2' :
      eval (fun i => some (τ i))
          (spec σ (collapse N σ l2)) =
        eval (fun i => some (τ i))
          (nf (spec σ
            (collapse N σ l2))) := by
    simp only [denote] at n2
    exact n2
  have chain1 :
      eval (rhoNSt N σ τ) l1 =
        some (evalTotal τ
          (nf (spec σ
            (collapse N σ l1)))) := by
    simp only [denote] at t1 n1
    rw [e1, f1, s1, ign1, n1, t1]
  have chain2 :
      eval (rhoNSt N σ τ) l2 =
        some (evalTotal τ
          (nf (spec σ
            (collapse N σ l2)))) := by
    simp only [denote] at t2 n2
    rw [e2, f2, s2, ign2, n2, t2]
  rw [chain1] at e
  rw [chain2] at e
  injection e with e'

theorem nf_spec_collapse_eq
    (N σ : List Nat) (l1 l2 : Level)
    (h : eqN l1 l2)
    (hn1 : noneOf N σ l1 = false)
    (hn2 : noneOf N σ l2 = false) :
    nf (spec σ (collapse N σ l1)) =
      nf (spec σ (collapse N σ l2)) :=
  canon_sep_imaxFree
    (nf (spec σ (collapse N σ l1)))
    (nf (spec σ (collapse N σ l2)))
    (isCanon_nf _)
    (isCanon_nf _)
    (nf_spec_imaxFree σ (collapse N σ l1))
    (nf_spec_imaxFree σ (collapse N σ l2))
    (fun τ =>
      evalTotal_nf_spec_eq N σ l1 l2 h
        hn1 hn2 τ)

theorem agreeAt_of_eqN
    (N σ : List Nat) (l1 l2 : Level)
    (h : eqN l1 l2) :
    agreeAt N σ l1 l2 = true := by
  have hnone :=
    noneOf_eq_of_eqN N σ l1 l2 h
  simp only [agreeAt]
  cases hn1 : noneOf N σ l1 with
  | true =>
      have hn2 : noneOf N σ l2 = true := by
        rw [hn1] at hnone
        exact hnone.symm
      rw [hn2]
      rfl
  | false =>
      have hn2 : noneOf N σ l2 = false := by
        rw [hn1] at hnone
        exact hnone.symm
      have hnf :=
        nf_spec_collapse_eq N σ l1 l2 h
          hn1 hn2
      rw [hn2]
      have hdn :
          decide
            (nf (spec σ
                (collapse N σ l1)) =
              nf (spec σ
                (collapse N σ l2))) =
              true := by
        cases hx :
          decide
            (nf (spec σ
                (collapse N σ l1)) =
              nf (spec σ
                (collapse N σ l2))) with
        | true => rfl
        | false =>
            exact False.elim
              (of_decide_eq_false hx hnf)
      have ht :
          decide (false = false) = true :=
        rfl
      rw [ht, or_false_left,
        and_true_left]
      exact hdn

theorem allSigmaAgree_of_eqN
    (l1 l2 : Level) (N : List Nat)
    (h : eqN l1 l2) :
    ∀ σs,
      allSigmaAgree l1 l2 N σs = true
  | [] => rfl
  | σ :: rest => by
      have ha :=
        agreeAt_of_eqN N σ l1 l2 h
      simp only [allSigmaAgree, ha]
      exact allSigmaAgree_of_eqN l1 l2 N
        h rest

theorem allNoneAgree_of_eqN
    (l1 l2 : Level) (P : List Nat)
    (h : eqN l1 l2) :
    ∀ Ns,
      allNoneAgree l1 l2 P Ns = true
  | [] => rfl
  | N :: rest => by
      have hs :=
        allSigmaAgree_of_eqN l1 l2 N h
          (allSubsets (minusNat N P))
      simp only [allNoneAgree, hs]
      exact allNoneAgree_of_eqN l1 l2 P
        h rest

theorem decEqN_complete (l1 l2 : Level) :
    eqN l1 l2 → decEqN l1 l2 = true := by
  intro h
  simp only [decEqN, decEqNNone]
  exact allNoneAgree_of_eqN l1 l2
    (unionNat (paramsOf l1) (paramsOf l2))
    h (allSubsets
      (unionNat (paramsOf l1)
        (paramsOf l2)))

theorem m005_imax_dec :
    decEqN (.imax (.succ .zero) .zero)
      .zero = true := rfl

theorem m005_imax_sound :
    eqN (.imax (.succ .zero) .zero) .zero :=
  decEqN_sound _ _ m005_imax_dec

theorem m005_param_dec :
    decEqN (.param 0) (.param 1) = false :=
  rfl

theorem m005_unbound_dec :
    decEqN (.imax .zero (.param 0))
      (.param 0) = true :=
  rfl

theorem m005_imax_complete :
    decEqN (.imax (.succ .zero) .zero)
      .zero = true :=
  decEqN_complete _ _ m005_imax_eqN

def pinImpl (l r : Level)
    (xs : List Nat) : Bool :=
  match decEqN l r with
  | false => true
  | true =>
      match eval (rhoOf xs) l,
          eval (rhoOf xs) r with
      | none, none => true
      | some x, some y => decide (x = y)
      | _, _ => false

#eval (if pinImpl (.succ (.param 0)) .zero []
  then 0 else panic "pin_row00")
#eval (if pinImpl (.max .zero (.param 2))
    .zero [] then 1 else panic "pin_row01")
#eval (if pinImpl (.param 1) .zero [] then 2
  else panic "pin_row02")
#eval (if pinImpl (.max .zero (.param 2))
    .zero [] then 3 else panic "pin_row03")
#eval (if true then 4 else panic "pin_row04")
#eval (if pinImpl (.succ .zero) .zero [] then 5
  else panic "pin_row05")
#eval (if pinImpl (.param 0) .zero [] then 6
  else panic "pin_row06")
#eval (if pinImpl
    (.max .zero (.succ .zero))
    (.succ .zero) [] then 7
  else panic "pin_row07")
#eval (if pinImpl
    (.imax (.succ .zero) .zero) .zero []
  then 8 else panic "pin_row08")
#eval (if pinImpl
    (.imax (.succ .zero)
      (.succ (.succ .zero)))
    (.succ (.succ .zero)) [] then 9
  else panic "pin_row09")
#eval (if pinImpl
    (.imax (.succ .zero) (.param 0))
    (.succ .zero) [0] then 10
  else panic "pin_row10")
#eval (if pinImpl
    (.imax (.succ .zero) (.param 0))
    (.succ .zero) [1] then 11
  else panic "pin_row11")
#eval (if pinImpl (.succ .zero)
    (.succ (.succ .zero)) [] then 12
  else panic "pin_row12")
#eval (if pinImpl (.succ (.succ .zero))
    (.succ .zero) [] then 13
  else panic "pin_row13")
#eval (if pinImpl (.param 0) .zero [] then 14
  else panic "pin_row14")
#eval (if pinImpl (.succ .zero) .zero []
  then 15 else panic "pin_row15")
#eval (if pinImpl .zero .zero [] then 16
  else panic "pin_row16")
#eval (if pinImpl .zero .zero [] then 17
  else panic "pin_row17")
#eval (if pinImpl (.succ .zero) (.succ .zero)
    [] then 18 else panic "pin_row18")
#eval (if pinImpl .zero .zero [] then 19
  else panic "pin_row19")
end Rcic.Declarative
