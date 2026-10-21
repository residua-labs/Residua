/-
RCIC level zero-ness (00 §20.10, segment 9) — §19.3 prerequisite (1)'s
missing tooth `eqN (.imax u v) .zero ↔ eqN v .zero`, the COMPILED
refutation of the `eqN`-invariant descending rank that prerequisite
names, and `levelIsZero`, the decider of the zero-ness FRAGMENT of `=ₙ`.

LEAF DISCIPLINE (00 §20.10 F7, siting MEASURED not chosen): this file
has `rcic.RcicDeclarative` as its ONLY import, so its rebuild closure
is 2 modules inclusive (itself + `RcicFoundationSeal`). NOT sited in
`RcicLevelCalc` (23 modules strictly downstream, including the 8.12 GiB
`RcicParRedDiamond` — every proof iteration would pay it) nor in
`RcicParRedSortWall` (downstream of `RcicEnv`, so C-6 (2)'s `harity`
leaf could never consume a tooth sited there). No twin is needed in
`RcicRefutations`: a leaf on `RcicDeclarative` does not sit behind the
ParRed edge, and a third copy of `eqN_imax_zero`'s content is what
00 §18.3 rule 6 bounces. MIGRATION: when a consumer needs the tooth the
CONSUMER adds the import; do not pre-emptively move this file.
`eqN_imax_zero` (`RcicParRedSortWall.lean:3572`) and `refutEqN_imax_zero`
(`RcicRefutations.lean:54`) are NOT deleted, moved or re-proved from the
tooth; `eqN_imax_zero_right` below is the local re-proof under a
distinct name.

ONE-LINER FOR CONSUMERS THAT ALREADY IMPORT `rcic.RcicParRedSortWall`:
derive `eqN_imax_succ_ne_zero` there from `eqN_succ_ne_zero`
(`RcicParRedSortWall.lean:3467`) through `eqN_imax_zero_iff` in one
line, rather than importing this leaf for it; the copy here is
self-contained (its `succ` arithmetic lives once, inside
`levelIsZero_iff`'s `.succ` arm) precisely so no third route is minted.

THE RESTRICTED DESCENT IS REFUTED TOO (00 §20.10 T6, §19.7 E-Diag;
found by the Codex review of #3827 after the segment landed). The
landing header called `(∀ u v, levelIsZero v = false → r u < r (.imax
u v))` "refuted by NOTHING below" because the zero collapse has
`levelIsZero .zero = true`. The DIAGONAL collapses it instead:
`.imax v v ≡ v` at every valuation (`eqN_imax_diag`; `y = 0` gives
`some 0 = some 0`, `y ≠ 0` gives `max y y = y`), so at `u := v := .succ
.zero` — where `levelIsZero v = false` by `rfl` — invariance and
descent give `r v < r v`. `levelRank_imax_restricted_descent_refuted`
and its order twin are §6. WHAT THIS CLOSES: the "dispatch on
`levelIsZero v`" route of §19.3 prerequisite (3) for a level-only
measure — no `eqN`-invariant rank descends from `u` into `.imax u v`
on ANY fragment that contains a non-zero diagonal, because
`HasTy.pi`'s sort can be `=ₙ` to its domain's sort (`A : Sort u`,
`B : Sort u`, `Π : Sort (imax u u) ≡ Sort u`). A measure for the
interpretation route must descend on the DERIVATION or the TYPE, not
on the level.

NOT a decision procedure for `=ₙ`: `levelIsZero` decides ONE fragment.
No `sorry`, no `native_decide`, no `Classical`, no `WellFounded`, no
Mathlib, no bare `simp`; axioms ⊆ {propext, Quot.sound}.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

/-! ## §1 The tooth (00 §20.10 T1) -/

/-- `imax` is transparent to zero-ness in its SECOND argument at each
valuation: `u` is never evaluated on the `then` branch and cannot reach
`some 0` on the `else` branch. -/
theorem eval_imax_eq_zero (ρ : Nat → Option Nat) (u v : Level) :
    eval ρ (.imax u v) = some 0 ↔ eval ρ v = some 0 := by
  simp only [eval]
  cases hv : eval ρ v with
  | none =>
      constructor
      · intro h
        exact Option.noConfusion h
      · intro h
        exact Option.noConfusion h
  | some y =>
      cases y with
      | zero =>
          constructor
          · intro _
            rfl
          · intro _
            rfl
      | succ k =>
          constructor
          · intro h
            exfalso
            cases hu : eval ρ u with
            | none =>
                rw [hu] at h
                exact Option.noConfusion h
            | some x =>
                rw [hu] at h
                injection h with h'
                have hle : k + 1 ≤ 0 := h' ▸ Nat.le_max_right x (k + 1)
                exact Nat.succ_ne_zero k (Nat.le_antisymm hle (Nat.zero_le _))
          · intro h
            exfalso
            injection h with h'
            omega

/-- §19.3 prerequisite (1)'s missing tooth, verbatim. -/
theorem eqN_imax_zero_iff (u v : Level) :
    eqN (.imax u v) .zero ↔ eqN v .zero :=
  ⟨fun h ρ => (eval_imax_eq_zero ρ u v).mp (h ρ),
   fun h ρ => (eval_imax_eq_zero ρ u v).mpr (h ρ)⟩

/-- The `max` sibling: zero-ness is CONJUNCTIVE there, so `max` cannot
identify a binary node with a level its arguments do not both reach. -/
theorem eval_max_eq_zero (ρ : Nat → Option Nat) (a b : Level) :
    eval ρ (.max a b) = some 0 ↔ (eval ρ a = some 0 ∧ eval ρ b = some 0) := by
  simp only [eval]
  cases ha : eval ρ a with
  | none =>
      constructor
      · intro h
        exact Option.noConfusion h
      · intro h
        exact Option.noConfusion h.left
  | some x =>
      cases hb : eval ρ b with
      | none =>
          constructor
          · intro h
            exact Option.noConfusion h
          · intro h
            exact Option.noConfusion h.right
      | some y =>
          constructor
          · intro h
            injection h with h'
            have hx : x ≤ 0 := h' ▸ Nat.le_max_left x y
            have hy : y ≤ 0 := h' ▸ Nat.le_max_right x y
            exact ⟨congrArg some (Nat.le_zero.mp hx), congrArg some (Nat.le_zero.mp hy)⟩
          · intro h
            injection h.left with hx
            injection h.right with hy
            subst hx
            subst hy
            rfl

/-! ## §2 The decider (00 §20.10 T3, first half) -/

/-- Zero at EVERY valuation, decided structurally; the `imax` arm ignores
its FIRST argument — `eval_imax_eq_zero` made structural. -/
def levelIsZero : Level → Bool
  | .zero     => true
  | .succ _   => false
  | .max a b  => levelIsZero a && levelIsZero b
  | .imax _ b => levelIsZero b
  | .param _  => false

/-- The decider is exact on the zero-ness fragment. The `.imax` arm uses
the induction hypothesis for `b` ONLY; the unused first-argument IH is
00 §20.10's finding in mechanical form. -/
theorem levelIsZero_iff (l : Level) : levelIsZero l = true ↔ eqN l .zero := by
  induction l with
  | zero =>
      constructor
      · intro _
        exact fun _ρ => rfl
      · intro _
        rfl
  | succ l _ih =>
      constructor
      · intro h
        exact Bool.noConfusion h
      · intro h
        exfalso
        have hv : Option.map (fun n => n + 1) (eval (fun _ => none) l) = some 0 :=
          h (fun _ => none)
        cases he : eval (fun _ => none) l with
        | none =>
            rw [he] at hv
            exact Option.noConfusion hv
        | some x =>
            rw [he] at hv
            injection hv with hv'
            exact Nat.succ_ne_zero x hv'
  | max a b iha ihb =>
      constructor
      · intro h
        simp only [levelIsZero] at h
        cases hA : levelIsZero a with
        | false =>
            rw [hA] at h
            exact Bool.noConfusion h
        | true =>
            cases hB : levelIsZero b with
            | false =>
                rw [hA, hB] at h
                exact Bool.noConfusion h
            | true =>
                intro ρ
                exact (eval_max_eq_zero ρ a b).mpr ⟨(iha.mp hA) ρ, (ihb.mp hB) ρ⟩
      · intro h
        have hm : ∀ ρ, eval ρ a = some 0 ∧ eval ρ b = some 0 :=
          fun ρ => (eval_max_eq_zero ρ a b).mp (h ρ)
        simp only [levelIsZero]
        rw [iha.mpr (fun ρ => (hm ρ).left), ihb.mpr (fun ρ => (hm ρ).right)]
        rfl
  | imax a b _iha ihb =>
      simp only [levelIsZero]
      exact ihb.trans (eqN_imax_zero_iff a b).symm
  | param i =>
      constructor
      · intro h
        exact Bool.noConfusion h
      · intro h
        exfalso
        have hv : (none : Option Nat) = some 0 := h (fun _ => none)
        exact Option.noConfusion hv

/-- C-6 (1)'s "only absent arithmetic"; C-6 (2)'s fourth sub-lemma. -/
theorem eqN_imax_succ_ne_zero (u l : Level) : ¬ eqN (.imax u (.succ l)) .zero := by
  intro h
  have hb : levelIsZero (.succ l) = true :=
    (levelIsZero_iff (.succ l)).mpr ((eqN_imax_zero_iff u (.succ l)).mp h)
  exact Bool.noConfusion hb

/-! ## §3 The collapses (00 §20.10 F5) -/

/-- `imax u .zero` is lazy in `u` and equals `.zero` at every valuation:
`.imax u .zero` and `.zero` are ONE `=ₙ` class at EVERY `u`, an infinite
set of unboundedly large levels. Local re-proof of `eqN_imax_zero`
(`RcicParRedSortWall.lean:3572`) under a distinct name, F7's leaf
discipline (`RcicRefutations.lean:39-42` precedent). -/
theorem eqN_imax_zero_right (u : Level) : eqN (.imax u .zero) .zero :=
  fun _ρ => rfl

/-- `max u .zero` collapses onto `u` — a binary node identified with one
of its OWN arguments, which is why this collapse is NOT impredicative. -/
theorem eqN_max_zero_right (u : Level) : eqN (.max u .zero) u := by
  intro ρ
  simp only [eval]
  cases hu : eval ρ u with
  | none => rfl
  | some x => exact congrArg some (Nat.max_zero x)

/-- `imax .zero v` collapses onto `v`, the codescent twin's witness. -/
theorem eqN_imax_zero_left (v : Level) : eqN (.imax .zero v) v := by
  intro ρ
  simp only [eval]
  cases hv : eval ρ v with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ k => exact congrArg some (Nat.zero_max (k + 1))

/-! ## §4 The rank: one EXISTS, none DESCENDS (00 §20.10 T2/T3) -/

/-- An `eqN`-invariant, computable, `Nat`-valued rank EXISTS — so
invariance is not the obstruction. -/
def zeroRank (l : Level) : Nat := if levelIsZero l then 0 else 1

theorem zeroRank_eqN_invariant {a b : Level} (h : eqN a b) :
    zeroRank a = zeroRank b := by
  have key : levelIsZero a = levelIsZero b := by
    cases hA : levelIsZero a with
    | true =>
        have hB : levelIsZero b = true :=
          (levelIsZero_iff b).mpr
            (fun ρ => (h ρ).symm.trans (((levelIsZero_iff a).mp hA) ρ))
        rw [hB]
    | false =>
        cases hB : levelIsZero b with
        | false => rfl
        | true =>
            exfalso
            have hA' : levelIsZero a = true :=
              (levelIsZero_iff a).mpr
                (fun ρ => (h ρ).trans (((levelIsZero_iff b).mp hB) ρ))
            rw [hA] at hA'
            exact Bool.noConfusion hA'
  simp only [zeroRank, key]

/-- THE SHARP FORM (00 §20.10 T2): invariance + descent into `imax`'s
FIRST argument puts EVERY level strictly below `.zero` — an infinite
descending chain, which is the impredicativity content. -/
theorem levelRank_imax_below_zero
    (r : Level → Nat)
    (hinv : ∀ a b, eqN a b → r a = r b)
    (hdom : ∀ u v, r u < r (.imax u v)) :
    ∀ u, r u < r .zero :=
  fun u => (hinv _ _ (eqN_imax_zero_right u)) ▸ hdom u .zero

theorem levelRank_imax_descent_refuted
    (r : Level → Nat)
    (hinv : ∀ a b, eqN a b → r a = r b)
    (hdom : ∀ u v, r u < r (.imax u v)) : False :=
  Nat.lt_irrefl _ (levelRank_imax_below_zero r hinv hdom .zero)

/-- Codescent (into the SECOND argument) collapses too — but only
trivially, at `u := .zero`, like `max`. -/
theorem levelRank_imax_codescent_refuted
    (r : Level → Nat) (hinv : ∀ a b, eqN a b → r a = r b)
    (hcod : ∀ u v, r v < r (.imax u v)) : False := by
  have h := hcod .zero .zero
  rw [hinv _ _ (eqN_imax_zero_left .zero)] at h
  exact Nat.lt_irrefl _ h

/-- The `max` sibling: descent at `max` is refuted by the SAME three
lines, so the trivial collapse is not `imax`-specific; what IS
`imax`-specific is `levelRank_imax_below_zero`. -/
theorem levelRank_max_descent_refuted
    (r : Level → Nat) (hinv : ∀ a b, eqN a b → r a = r b)
    (hdom : ∀ u v, r u < r (.max u v)) : False := by
  have h := hdom .zero .zero
  rw [hinv _ _ (eqN_max_zero_right .zero)] at h
  exact Nat.lt_irrefl _ h

/-- Not an artefact of `Nat`: any irreflexive relation that respects
`eqN` on its right argument cannot descend at `imax`. -/
theorem levelOrder_imax_descent_refuted
    (lt : Level → Level → Prop)
    (hirr : ∀ l, ¬ lt l l)
    (hresp : ∀ a b c, eqN a b → lt c a → lt c b)
    (hdom : ∀ u v, lt u (.imax u v)) : False :=
  hirr .zero (hresp _ _ _ (eqN_imax_zero_right .zero) (hdom .zero .zero))

/-! ## §5 `instLevel` compatibility and its sharpness witness (T4) -/

/-- Zero-ness survives level instantiation: DT-002 at
`σ := levelParamSubst ls`, with `lvlSubst σ .zero = .zero` by `rfl`. -/
theorem eqN_zero_instLevel {l : Level} (h : eqN l .zero) (ls : List Level) :
    eqN (instLevel ls l) .zero :=
  DT002_levelSubstitution_preserves.1 (levelParamSubst ls) l .zero h

theorem levelIsZero_instLevel (ls : List Level) {l : Level}
    (h : levelIsZero l = true) : levelIsZero (instLevel ls l) = true :=
  (levelIsZero_iff _).mpr (eqN_zero_instLevel ((levelIsZero_iff l).mp h) ls)

/-- SHARPNESS: the converse FAILS — instantiation only makes MORE levels
zero. Pinned by `decide`, never by `#eval … panic` (00 §19.7 E-PANIC). -/
example : levelIsZero (.param 0) = false
        ∧ levelIsZero (instLevel [.zero] (.param 0)) = true := by decide

/-! ## §6 The restricted descent collapses on the diagonal (00 §20.10 T6) -/

/-- `imax v v` is `v` at every valuation: `y = 0` short-circuits to
`some 0`, and otherwise `max y y = y`. -/
theorem eqN_imax_diag (v : Level) : eqN (.imax v v) v := by
  intro ρ
  simp only [eval]
  cases hv : eval ρ v with
  | none => rfl
  | some y =>
      cases y with
      | zero => rfl
      | succ k => exact congrArg some (Nat.max_self (k + 1))

/-- The restricted descent (descend into `imax`'s first argument only
when the second is not zero) is refuted at `u := v := .succ .zero`,
where `levelIsZero v = false` holds by `rfl` — so the zero collapse was
never the only obstruction, and no `eqN`-invariant rank can descend
from `u` into `.imax u v` on any fragment with a non-zero diagonal. -/
theorem levelRank_imax_restricted_descent_refuted
    (r : Level → Nat) (hinv : ∀ a b, eqN a b → r a = r b)
    (hres : ∀ u v, levelIsZero v = false → r u < r (.imax u v)) : False := by
  have h := hres (.succ .zero) (.succ .zero) rfl
  rw [hinv _ _ (eqN_imax_diag (.succ .zero))] at h
  exact Nat.lt_irrefl _ h

/-- Not an artefact of `Nat`, as in §4. -/
theorem levelOrder_imax_restricted_descent_refuted
    (lt : Level → Level → Prop)
    (hirr : ∀ l, ¬ lt l l)
    (hresp : ∀ a b c, eqN a b → lt c a → lt c b)
    (hres : ∀ u v, levelIsZero v = false → lt u (.imax u v)) : False :=
  hirr (.succ .zero)
    (hresp _ _ _ (eqN_imax_diag (.succ .zero))
      (hres (.succ .zero) (.succ .zero) rfl))

end Rcic.Declarative
