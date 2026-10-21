/-
RCIC ParRed, piece 7 of 7: total iota-vs-congr and the pairwise
diamond (Tait-Martin-Lof), attempt 52.

`parRed_foldApps_inductive`, `parRed_familyIdx_total`,
`parRed_rhsArgs_congr_total`, `parRed_iotaRhs_congr_total` under the
witness invariants, `parRedWitness`, and the capstone mutual
`parRedArgs_diamond` / `parRed_diamond_from` / `parRed_diamond`,
with `parRed_strip`, `parRedStar_diamond`, `two_stars_to_sort`.

Depends on neither `RcicParRedSortWall` nor `RcicParRedDevel`: the
diamond never elaborates behind the complete-development material.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.  The `maxHeartbeats 800000` below was a
top-level option in the single file, set immediately above the
now-deleted TRIANGLE route and in force for the total iota-vs-congr
section that follows it; it is re-emitted here unchanged.
-/
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicParRedWeight
import rcic.RcicParRedSubst

namespace Rcic.Declarative

set_option maxHeartbeats 800000

/-! ### Total iota-vs-congr under the witness invariants (architect
takeover per the standing wall protocol). The Option chain's `none`
branches are UNREACHABLE for an inductive-headed spine:

* a root redex on a DirectRec domain is impossible — the domain's head
  is the inductive family (`hfamSpine`): delta needs transparency and
  inductiveM is rigid; beta needs a lam in function position
  (`foldApps_const_ne_lam`); iota / iotaSpine need a recursor head, and
  `E.members` is a function, so one ref cannot be inductiveM and
  recursorM at once;
* kinds-vs-non-Π cursors are killed by `hctorTel` (`isPiTel`), which
  survives the walk because instantiation preserves Π spines. -/

theorem appsSpine_head_foldApps_const (r : Nat) (ls : List Level)
    (xs : List (Expr Nat)) :
    (appsSpine (foldApps (.const r ls) xs)).1 = .const r ls := by
  rw [appsSpine_foldApps, appsSpine_const]

theorem head_eq_of_foldApps_const_eq {r r' : Nat} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)}
    (h : foldApps (.const r ls) xs = foldApps (.const r' ls') xs') :
    r = r' ∧ ls = ls' := by
  have h1 := appsSpine_head_foldApps_const r ls xs
  rw [h, appsSpine_head_foldApps_const] at h1
  injection h1 with hr hls
  exact ⟨hr.symm, hls.symm⟩

theorem spine_eq_of_foldApps_const_eq {r r' : Nat} {ls ls' : List Level}
    {xs xs' : List (Expr Nat)}
    (h : foldApps (.const r ls) xs = foldApps (.const r' ls') xs') :
    xs = xs' := by
  have hs := congrArg appsSpine h
  simp only [appsSpine_foldApps, appsSpine_const, List.nil_append] at hs
  injection hs

/-- TOTAL inversion of ParRed on an inductive-headed const spine. The
redex arms of `parRed_foldApps_const` are impossible here. -/
def parRed_foldApps_inductive {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM) :
    {e t : Expr Nat} →
    ParRed E n Γ e t →
    (xs : List (Expr Nat)) →
    e = foldApps (.const r ls) xs →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        ParRedArgs E n Γ xs xs'
  | _, _, .refl _ e, xs, heq => by
      subst heq
      exact ⟨ls, xs, rfl, eqNList_refl ls, parRedArgs_refl xs⟩
  | _, _, .sortEq _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .consts _ r0 ls0 ls' h, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact ⟨ls', [], rfl, h, ParRedArgs.nil Γ⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .delta _ r0 ls0 m0 b hres0 hbody htr, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr0 _
          subst hr0
          rw [hres] at hres0
          injection hres0 with hm
          rw [← hm, hK] at htr
          exact Bool.noConfusion htr
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .app _ f0 f0' a0 a0' hf ha, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 ha0
          subst hf0
          subst ha0
          let ⟨ls', ys', hfeq, hls, hys⟩ :=
            parRed_foldApps_inductive hres hK hf ys rfl
          subst hfeq
          have hargs : ParRedArgs E n Γ (z :: zs) (ys' ++ [a0']) := by
            rw [hsplit]
            exact parRedArgs_snoc hys ha
          exact ⟨ls', ys' ++ [a0'],
            (foldApps_snoc (.const r ls') a0' ys').symm, hls, hargs⟩
  | _, _, .beta _ A A' body body' arg arg' hA hb ha, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 _
          exact absurd hf0.symm (foldApps_const_ne_lam ys)
  | _, _, .lam _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .letE _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .zeta _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, xs, heq => by
      have heq' :
          foldApps (.const w.recRef lsR)
              (pre ++ [foldApps (.const w.ctorRef lsC) fields]) =
            foldApps (.const r ls) xs := heq
      have ⟨hr0, _⟩ := head_eq_of_foldApps_const_eq heq'
      have hres' := w.hrec
      rw [hr0, hres] at hres'
      injection hres' with hm
      have hcls := w.hrecK
      rw [← hm, hK] at hcls
      exact nomatch hcls
  | _, _, .lit _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq

def parRed_foldApps_constructor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.constructorM) :
    {e t : Expr Nat} →
    (h : ParRed E n Γ e t) →
    (xs : List (Expr Nat)) →
    e = foldApps (.const r ls) xs →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        (hargs : ParRedArgs E n Γ xs xs') ×'
        (parRedArgsW hargs ≤ parRedW h)
  | _, _, .refl _ e, xs, heq => by
      subst heq
      refine ⟨ls, xs, rfl, eqNList_refl ls, parRedArgs_refl xs, ?_⟩
      simp only [parRedW]
      rw [parRedArgsW_refl]
      have hfold := exprSize_foldApps (.const r ls) xs
      have hadd := foldr_exprSize_add 1 xs 0
      simp only [exprSize] at hfold
      rw [Nat.zero_add] at hadd
      omega
  | _, _, .sortEq _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .consts _ r0 ls0 ls' h, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact ⟨ls', [], rfl, h, ParRedArgs.nil Γ,
            by simp only [parRedArgsW, parRedW]; omega⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .delta _ r0 ls0 m0 b hres0 hbody htr, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr0 _
          subst hr0
          rw [hres] at hres0
          injection hres0 with hm
          rw [← hm, hK] at htr
          exact Bool.noConfusion htr
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .app _ f0 f0' a0 a0' hf ha, xs, heq => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 ha0
          subst hf0
          subst ha0
          let ⟨ls', ys', hfeq, hls, hys, hWy⟩ :=
            parRed_foldApps_constructor hres hK hf ys rfl
          subst hfeq
          let hargs0 := parRedArgs_snoc hys ha
          let hargs : ParRedArgs E n Γ (z :: zs) (ys' ++ [a0']) :=
            Eq.rec (motive := fun t _ =>
                ParRedArgs E n Γ t (ys' ++ [a0'])) hargs0 hsplit.symm
          refine ⟨ls', ys' ++ [a0'],
            (foldApps_snoc (.const r ls') a0' ys').symm, hls, hargs, ?_⟩
          rw [parRedArgsW_eq_rec hsplit.symm hargs0]
          rw [parRedArgsW_snoc hys ha]
          simp only [parRedW]
          omega
  | _, _, .beta _ A A' body body' arg arg' hA hb ha, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 _
          exact absurd hf0.symm (foldApps_const_ne_lam ys)
  | _, _, .lam _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .letE _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .zeta _ _ _ _ _ _ _ _ _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, xs, heq => by
      have heq' :
          foldApps (.const w.recRef lsR)
              (pre ++ [foldApps (.const w.ctorRef lsC) fields]) =
            foldApps (.const r ls) xs := heq
      have ⟨hr0, _⟩ := head_eq_of_foldApps_const_eq heq'
      have hres' := w.hrec
      rw [hr0, hres] at hres'
      injection hres' with hm
      have hcls := w.hrecK
      rw [← hm, hK] at hcls
      exact nomatch hcls
  | _, _, .lit _ _, xs, heq => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq

def parRed_foldApps_recursor_short {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {e t : Expr Nat} →
    (h : ParRed E n Γ e t) →
    {r : Nat} → {ls : List Level} → {m : CheckedMember} →
    (hres : E.members r = some m) →
    (hK : m.mclass = MemberClass.recursorM) →
    (xs : List (Expr Nat)) →
    (heq : e = foldApps (.const r ls) xs) →
    (hlen : xs.length < piCount m.mtype) →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        (hargs : ParRedArgs E n Γ xs xs') ×'
        (parRedArgsW hargs ≤ parRedW h)
  | _, _, .refl _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      subst heq
      refine ⟨ls, xs, rfl, eqNList_refl ls, parRedArgs_refl xs, ?_⟩
      simp only [parRedW]
      rw [parRedArgsW_refl]
      have hfold := exprSize_foldApps (.const r ls) xs
      have hadd := foldr_exprSize_add 1 xs 0
      simp only [exprSize] at hfold
      rw [Nat.zero_add] at hadd
      omega
  | _, _, .sortEq _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .consts _ r0 ls0 ls1 q, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr hls
          subst hr
          subst hls
          exact ⟨ls1, [], rfl, q, ParRedArgs.nil Γ,
            by simp only [parRedArgsW, parRedW]; omega⟩
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .delta _ r0 ls0 m0 b hres0 hbody htr, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          injection heq with hr0 _
          subst hr0
          rw [hres] at hres0
          injection hres0 with hm
          rw [← hm, hK] at htr
          exact Bool.noConfusion htr
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .app _ f0 f0' a0 a0' hf ha, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil =>
          simp only [foldApps] at heq
          exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 ha0
          subst hf0
          subst ha0
          have hlen_ys : ys.length < piCount m.mtype := by
            have : (z :: zs).length = ys.length + 1 := by
              rw [hsplit, List.length_append, List.length_singleton]
            omega
          let ⟨ls', ys', hfeq, hls, hys, hWy⟩ :=
            parRed_foldApps_recursor_short hf hres hK ys rfl hlen_ys
          subst hfeq
          let hargs0 := parRedArgs_snoc hys ha
          let hargs : ParRedArgs E n Γ (z :: zs) (ys' ++ [a0']) :=
            Eq.rec (motive := fun t _ =>
                ParRedArgs E n Γ t (ys' ++ [a0'])) hargs0 hsplit.symm
          refine ⟨ls', ys' ++ [a0'],
            (foldApps_snoc (.const r ls') a0' ys').symm, hls, hargs, ?_⟩
          rw [parRedArgsW_eq_rec hsplit.symm hargs0]
          rw [parRedArgsW_snoc hys ha]
          simp only [parRedW]
          omega
  | _, _, .beta _ A A' body body' arg arg' hA hb ha, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons z zs =>
          have hne : z :: zs ≠ ([] : List (Expr Nat)) := by
            intro hh; cases hh
          let ⟨ys, x, hsplit⟩ := list_snoc_of_ne_nil (z :: zs) hne
          have happ : foldApps (.const r ls) (z :: zs) =
              .app (foldApps (.const r ls) ys) x := by
            rw [hsplit, foldApps_snoc]
          rw [happ] at heq
          injection heq with hf0 _
          exact absurd hf0.symm (foldApps_const_ne_lam ys)
  | _, _, .lam _ _ _ _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .letE _ _ _ _ _ _ _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .zeta _ _ _ _ _ _ _ _ _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq
  | _, _, .iotaSpine _ w lsR lsC _ _ pre pre' fields _ hf _ hpreLen _ _,
        r, ls, m, hres, hK, xs, heq, hlen => by
      have heq' :
          foldApps (.const w.recRef lsR)
              (pre ++ [foldApps (.const w.ctorRef lsC) fields]) =
            foldApps (.const r ls) xs := heq
      have ⟨hr0, _⟩ := head_eq_of_foldApps_const_eq heq'
      have hres' := w.hrec
      rw [hr0, hres] at hres'
      injection hres' with hm
      have hxs := spine_eq_of_foldApps_const_eq heq'
      have hlen_xs : xs.length = pre.length + 1 := by
        rw [← hxs, List.length_append, List.length_singleton]
      have hpre_len : pre.length = w.preMajor.length :=
        (parRedArgs_length hf).trans hpreLen
      have hEq : w.preMajor.length + 1 = piCount w.recMember.mtype := by
        rw [w.hpre, w.hnmin]
      have heq_len : xs.length = piCount w.recMember.mtype :=
        (hlen_xs.trans (congrArg (· + 1) hpre_len)).trans hEq
      have hlen' : xs.length < piCount w.recMember.mtype := hm ▸ hlen
      exact False.elim (Nat.lt_irrefl xs.length (heq_len.symm ▸ hlen'))
  | _, _, .lit _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      cases xs with
      | nil => exact nomatch heq
      | cons x xs =>
          let ⟨_, _, happ⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [happ] at heq
          exact nomatch heq

def parRedStar_foldApps_recursor_short {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {e t : Expr Nat} →
    ParRedStar E n Γ e t →
    {r : Nat} → {ls : List Level} → {m : CheckedMember} →
    (hres : E.members r = some m) →
    (hK : m.mclass = MemberClass.recursorM) →
    (xs : List (Expr Nat)) →
    (heq : e = foldApps (.const r ls) xs) →
    (hlen : xs.length < piCount m.mtype) →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        (xs.length = xs'.length)
  | _, _, .refl _ _, r, ls, m, hres, hK, xs, heq, hlen => by
      subst heq
      exact ⟨ls, xs, rfl, eqNList_refl ls, rfl⟩
  | _, _, .tail h0 hs, r, ls, m, hres, hK, xs, heq, hlen => by
      let ⟨ls1, xs1, heq1, q1, hargs, _⟩ :=
        parRed_foldApps_recursor_short h0 hres hK xs heq hlen
      have hlen1 : xs1.length < piCount m.mtype := by
        have := parRedArgs_length hargs
        omega
      let ⟨ls2, xs2, heq2, q2, hlen2⟩ :=
        parRedStar_foldApps_recursor_short hs hres hK xs1 heq1 hlen1
      exact ⟨ls2, xs2, heq2, eqNList_trans q1 q2,
        (parRedArgs_length hargs).trans hlen2⟩

/-- Star inversion of a constructor-headed spine: each step is
`parRed_foldApps_constructor`; length is chained. -/
def parRedStar_foldApps_constructor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.constructorM) :
    {e t : Expr Nat} →
    ParRedStar E n Γ e t →
    (xs : List (Expr Nat)) →
    (heq : e = foldApps (.const r ls) xs) →
    (ls' : List Level) ×'
      (xs' : List (Expr Nat)) ×'
        (t = foldApps (.const r ls') xs') ×'
        eqNList ls ls' ×'
        (xs.length = xs'.length)
  | _, _, .refl _ _, xs, heq => by
      subst heq
      exact ⟨ls, xs, rfl, eqNList_refl ls, rfl⟩
  | _, _, .tail h0 hs, xs, heq => by
      let ⟨ls1, xs1, heq1, q1, hargs, _⟩ :=
        parRed_foldApps_constructor hres hK h0 xs heq
      let ⟨ls2, xs2, heq2, q2, hlen2⟩ :=
        parRedStar_foldApps_constructor hres hK hs xs1 heq1
      exact ⟨ls2, xs2, heq2, eqNList_trans q1 q2,
        (parRedArgs_length hargs).trans hlen2⟩

theorem list_drop_take_append {α : Type} :
    (n : Nat) → (xs ys : List α) → n ≤ xs.length →
    List.drop n (xs.take n ++ ys) = ys
  | 0, xs, ys, _ => by
      simp only [List.drop, List.take, List.nil_append]
  | n + 1, [], ys, h => by
      simp only [List.length_nil] at h
      exfalso
      omega
  | n + 1, x :: xs, ys, h => by
      simp only [List.take, List.drop, List.cons_append]
      exact list_drop_take_append n xs ys (by
        simp only [List.length_cons] at h; omega)

/-- TOTAL familyIdx inversion for a family-headed domain. -/
def parRed_familyIdx_total {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {lsF : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM)
    (nparams : Nat) {A A' : Expr Nat}
    (hhead : (appsSpine A).1 = .const r lsF)
    (h : ParRed E n Γ A A') :
    ParRedArgs E n Γ (familyIdx nparams A) (familyIdx nparams A') := by
  have heqA : A = foldApps (.const r lsF) (appsSpine A).2 := by
    have hfold := foldApps_appsSpine A
    rw [hhead] at hfold
    exact hfold.symm
  let ⟨ls', xs', heqA', _hls, hargs⟩ :=
    parRed_foldApps_inductive hres hK h (appsSpine A).2 heqA
  subst heqA'
  simp only [familyIdx]
  have hsp' : (appsSpine (foldApps (.const r ls') xs')).2 = xs' := by
    rw [appsSpine_foldApps, appsSpine_const, List.nil_append]
  rw [hsp']
  exact parRedArgs_drop hargs nparams

/-- TOTAL rhsArgs congruence under the witness telescope invariants. -/
def parRed_rhsArgs_congr_total {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {rec rec' : Expr Nat}
    (hrec : ParRed E n Γ rec rec')
    {r : Nat} {lsF : List Level} {m : CheckedMember}
    (hres : E.members r = some m)
    (hK : m.mclass = MemberClass.inductiveM)
    (nparams0 : Nat) (params : List (Expr Nat))
    {pre pre' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ pre pre')
    (nparams nMinors : Nat) :
    {fs fs' : List (Expr Nat)} →
    ParRedArgs E n Γ fs fs' →
    (ks : List RecKind) →
    {T T' : Expr Nat} →
    ParRed E n Γ T T' →
    isPiTel ks.length T = true →
    directRecFamilySpine r lsF nparams0 params ks T fs = true →
    ParRedArgs E n Γ
      (rhsArgs rec pre nparams nMinors fs ks T)
      (rhsArgs rec' pre' nparams nMinors fs' ks T')
  | [], [], _, _ks, _T, _T', _hT, _htel, _hsp => ParRedArgs.nil Γ
  | [], _ :: _, hfs, _, _, _, _, _, _ => nomatch hfs
  | _ :: _, [], hfs, _, _, _, _, _, _ => nomatch hfs
  | _f :: fs, _f' :: fs', .cons hf hfs, ks, T, T', hT, htel, hsp =>
      match ks, htel, hsp with
      | [], _htel, _hsp =>
          .cons hf (parRed_rhsArgs_congr_total hE hrec (lsF := lsF) hres hK
            nparams0 params hpre nparams nMinors hfs [] hT rfl
            (rfl : directRecFamilySpine r lsF nparams0 params [] _ _ = true))
      | .plain :: ks, htel, hsp => by
          match T, htel, hsp with
          | .pi _A B, htel, hsp =>
              have ⟨_A', B', heq, _hA, hB⟩ := parRed_pi hT rfl
              subst heq
              simp only [isPiTel] at htel
              simp only [directRecFamilySpine] at hsp
              have hTnext := parRed_instantiate_both_assump hE hf hB
              exact .cons hf (parRed_rhsArgs_congr_total hE hrec hres hK
                nparams0 params hpre nparams nMinors hfs ks hTnext
                (isPiTel_instantiate 0 _f ks.length B htel) hsp)
          | .bvar _, htel, _ => exact Bool.noConfusion htel
          | .sort _, htel, _ => exact Bool.noConfusion htel
          | .const _ _, htel, _ => exact Bool.noConfusion htel
          | .app _ _, htel, _ => exact Bool.noConfusion htel
          | .lam _ _, htel, _ => exact Bool.noConfusion htel
          | .letE _ _ _, htel, _ => exact Bool.noConfusion htel
          | .lit _, htel, _ => exact Bool.noConfusion htel
      | .directRec :: ks, htel, hsp => by
          match T, htel, hsp with
          | .pi A B, htel, hsp =>
              have ⟨_A', B', heq, hA, hB⟩ := parRed_pi hT rfl
              subst heq
              simp only [isPiTel] at htel
              simp only [directRecFamilySpine, Bool.and_eq_true] at hsp
              obtain ⟨hhead, hrest⟩ := hsp
              cases hhd : (appsSpine A).1 with
              | const r0 lsA =>
                  have hr : r0 = r := of_decide_eq_true (by
                    simp only [hhd] at hhead; exact hhead)
                  subst hr
                  have hidx :=
                    parRed_familyIdx_total (lsF := lsA) hres hK nparams hhd hA
                  have hrc :=
                    parRed_recCallField_congr hrec hpre
                      nparams nMinors hf hidx
                  have hTnext := parRed_instantiate_both_assump hE hf hB
                  exact .cons hf (.cons hrc
                    (parRed_rhsArgs_congr_total hE hrec hres hK
                      nparams0 params hpre nparams nMinors hfs ks hTnext
                      (isPiTel_instantiate 0 _f ks.length B htel) hrest))
              | bvar _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | sort _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | app _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | lam _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | pi _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | letE _ _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | lit _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
          | .bvar _, htel, _ => exact Bool.noConfusion htel
          | .sort _, htel, _ => exact Bool.noConfusion htel
          | .const _ _, htel, _ => exact Bool.noConfusion htel
          | .app _ _, htel, _ => exact Bool.noConfusion htel
          | .lam _ _, htel, _ => exact Bool.noConfusion htel
          | .letE _ _ _, htel, _ => exact Bool.noConfusion htel
          | .lit _, htel, _ => exact Bool.noConfusion htel

/-- Parallel `applyTel`: same closed telescope, pointwise ParRed of
the applied args. Structural on the `ParRedArgs` spine. -/
def parRed_applyTel {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {T T' : Expr Nat}
    (hT : ParRed E n Γ T T')
    {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    {U V : Expr Nat}
    (hu : applyTel xs T = some U)
    (hv : applyTel ys T' = some V) :
    ParRed E n Γ U V :=
  match h with
  | ParRedArgs.nil _ => by
      simp only [applyTel] at hu hv
      injection hu with hu'; injection hv with hv'
      subst hu'; subst hv'
      exact hT
  | ParRedArgs.cons hx ht => by
      let ⟨_A, B, hTeq, hu'⟩ := applyTel_cons_inv _ _ hu
      subst hTeq
      have ⟨_A', B', hT'eq, _hA, hB⟩ := parRed_pi hT rfl
      subst hT'eq
      let ⟨_A2, B2, hT2, hv'⟩ := applyTel_cons_inv _ _ hv
      injection hT2 with _hAeq hBeq
      subst hBeq
      exact parRed_applyTel hE
        (parRed_instantiate_both_assump hE hx hB) (h := ht) hu' hv'

/-- TOTAL spine-arg congruence of `iotaRhsOf`: the iota-vs-congr
engine, no Option. The wall's failing statement, inhabited. -/
def parRed_iotaRhs_congr_total {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {w : IotaWitness E}
    {pre' fields' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ w.preMajor pre')
    (hfs : ParRedArgs E n Γ w.fields fields') :
    Σ' (minor' : Expr Nat),
      (pre'[w.nparams + 1 + w.ctorIdx]? = some minor') ×'
      ParRed E n Γ (iotaRhsOf w)
        (foldApps minor'
          (rhsArgs (.const w.recRef w.ls) pre' w.nparams w.nMinors
            fields' w.kinds w.ctorAfterParams)) :=
  match parRedArgs_get hpre w.hminor with
  | ⟨minor', hmin, hminor⟩ =>
      ⟨minor', hmin,
        parRed_foldApps_congr
          (parRed_rhsArgs_congr_total hE (.refl Γ (.const w.recRef w.ls))
            w.hfam w.hfamK w.nparams (w.preMajor.take w.nparams)
            hpre w.nparams w.nMinors hfs w.kinds
            (.refl _ w.ctorAfterParams) w.hctorTel (envWf_iotaTyping hE w).hfamSpine)
          hminor⟩

/-- Join `iotaRhsOf w` to `iotaRhsOf w2` when the spines ParRed
pointwise, levels `=ₙ`, and the telescope follows the params.
Env fields (nparams/kinds/…) come from `iotaWitness_env_of_same_refs`.
Level drift is one parallel `.consts` inside DirectRec IHs. -/
def parRed_iotaRhs_to_cert {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {w w2 : IotaWitness E}
    (href : w.recRef = w2.recRef)
    (hctor : w.ctorRef = w2.ctorRef)
    (hls : eqNList w.ls w2.ls)
    (hpre : ParRedArgs E n Γ w.preMajor w2.preMajor)
    (hfs : ParRedArgs E n Γ w.fields w2.fields) :
    ParRed E n Γ (iotaRhsOf w) (iotaRhsOf w2) :=
  have hlen : w.preMajor.length = w2.preMajor.length :=
    parRedArgs_length hpre
  have ⟨_hmemr, hmemc, _hfam, hnmin, _hnidx, hnpar, hidx, hk⟩ :=
    iotaWitness_env_of_same_refs href hctor hlen
  have hcap : ParRed E n Γ w.ctorAfterParams w2.ctorAfterParams :=
    -- 00 §20.6: the two `hctorAfter`s are now applications of the SAME
    -- stored type read at `w.ls` and at `w2.ls`; the level drift `hls`
    -- is absorbed by one `parRedInstantiateLevels` step (L4b), where
    -- before the rule change `refl` sufficed.
    parRed_applyTel hE (parRedInstantiateLevels w.ctorMember.mtype hls Γ)
      (parRedArgs_take hpre w.nparams)
      w.hctorAfter
      (by
        have b := w2.hctorAfter
        rw [← hnpar, ← hmemc] at b
        exact b)
  match parRedArgs_get hpre w.hminor with
  | ⟨minor', hmin, hminor⟩ =>
      have hmin2 : w2.preMajor[w.nparams + 1 + w.ctorIdx]? =
          some w2.minor := by
        have := w2.hminor
        rw [← hnpar, ← hidx] at this
        exact this
      have hm : minor' = w2.minor :=
        Option.some.inj (hmin.symm.trans hmin2)
      have hR : ParRed E n Γ (iotaRhsOf w)
          (foldApps minor'
            (rhsArgs (.const w.recRef w2.ls) w2.preMajor w.nparams
              w.nMinors w2.fields w.kinds w2.ctorAfterParams)) := by
        unfold iotaRhsOf
        exact parRed_foldApps_congr
          (parRed_rhsArgs_congr_total hE
            (.consts Γ w.recRef w.ls w2.ls hls)
            w.hfam w.hfamK w.nparams (w.preMajor.take w.nparams)
            hpre w.nparams w.nMinors hfs w.kinds
            hcap w.hctorTel (envWf_iotaTyping hE w).hfamSpine)
          hminor
      have htgt :
          foldApps minor'
            (rhsArgs (.const w.recRef w2.ls) w2.preMajor w.nparams
              w.nMinors w2.fields w.kinds w2.ctorAfterParams) =
          iotaRhsOf w2 := by
        unfold iotaRhsOf
        rw [href, hnpar, hnmin, hk, hm]
      Eq.rec (motive := fun t _ => ParRed E n Γ (iotaRhsOf w) t) hR htgt

/-- One parallel step of iota-rhs congruence at an arbitrary prefix.
`hfs` source is `w.fields` so `hfamSpine` types. Used to star-ify
the total engine along a recursor-prefix star. -/
def parRed_iotaRhs_step {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {w : IotaWitness E}
    {pre pre' : List (Expr Nat)}
    (hpre : ParRedArgs E n Γ pre pre')
    {minor : Expr Nat}
    (hminPos : pre[w.nparams + 1 + w.ctorIdx]? = some minor) :
    Σ' (minor' : Expr Nat),
      (pre'[w.nparams + 1 + w.ctorIdx]? = some minor') ×'
      ParRed E n Γ
        (foldApps minor
          (rhsArgs (.const w.recRef w.ls) pre w.nparams w.nMinors
            w.fields w.kinds w.ctorAfterParams))
        (foldApps minor'
          (rhsArgs (.const w.recRef w.ls) pre' w.nparams w.nMinors
            w.fields w.kinds w.ctorAfterParams)) :=
  match parRedArgs_get hpre hminPos with
  | ⟨minor', hmin, hminor⟩ =>
      ⟨minor', hmin,
        parRed_foldApps_congr
          (parRed_rhsArgs_congr_total hE (.refl Γ (.const w.recRef w.ls))
            w.hfam w.hfamK w.nparams (w.preMajor.take w.nparams)
            hpre w.nparams w.nMinors (parRedArgs_refl w.fields) w.kinds
            (.refl _ w.ctorAfterParams) w.hctorTel (envWf_iotaTyping hE w).hfamSpine)
          hminor⟩

/-- Star of recursor-prefix steps, fields held at `w.fields`. -/
def parRedStar_iotaRhs_congr_pre {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {w : IotaWitness E} :
    {e t : Expr Nat} →
    (hf : ParRedStar E n Γ e t) →
    {ls : List Level} → {pre : List (Expr Nat)} →
    (heq : e = foldApps (.const w.recRef ls) pre) →
    (hlen : pre.length < piCount w.recMember.mtype) →
    {minor : Expr Nat} →
    (hmin : pre[w.nparams + 1 + w.ctorIdx]? = some minor) →
    Σ' (ls' : List Level) (pre' : List (Expr Nat)) (minor' : Expr Nat),
      (t = foldApps (.const w.recRef ls') pre') ×'
      (pre'[w.nparams + 1 + w.ctorIdx]? = some minor') ×'
      ParRedStar E n Γ
        (foldApps minor
          (rhsArgs (.const w.recRef w.ls) pre w.nparams w.nMinors
            w.fields w.kinds w.ctorAfterParams))
        (foldApps minor'
          (rhsArgs (.const w.recRef w.ls) pre' w.nparams w.nMinors
            w.fields w.kinds w.ctorAfterParams))
  | _, _, .refl _ _, ls, pre, heq, _hlen, minor, hmin => by
      subst heq
      exact ⟨ls, pre, minor, rfl, hmin, ParRedStar.refl _ _⟩
  | _, _, .tail h hs, ls, pre, heq, hlen, minor, hmin =>
      let ⟨ls1, pre1, heq1, _q1, hargs, _⟩ :=
        parRed_foldApps_recursor_short h w.hrec w.hrecK pre heq hlen
      let ⟨minor1, hmin1, hstep⟩ :=
        parRed_iotaRhs_step hE hargs hmin
      have hlen1 : pre1.length < piCount w.recMember.mtype := by
        have := parRedArgs_length hargs
        omega
      let ⟨ls2, pre2, minor2, heq2, hmin2, hrest⟩ :=
        parRedStar_iotaRhs_congr_pre hE hs heq1 hlen1 hmin1
      ⟨ls2, pre2, minor2, heq2, hmin2, .tail hstep hrest⟩

/-- Fields step at a fixed prefix: `w.fields` to `fields'`, minor
unchanged. `hfamSpine` types because the `ParRedArgs` source is
`w.fields`. -/
def parRed_iotaRhs_fields_step {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} {w : IotaWitness E}
    (pre : List (Expr Nat)) (minor : Expr Nat)
    {fields' : List (Expr Nat)}
    (hfs : ParRedArgs E n Γ w.fields fields') :
    ParRed E n Γ
      (foldApps minor
        (rhsArgs (.const w.recRef w.ls) pre w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams))
      (foldApps minor
        (rhsArgs (.const w.recRef w.ls) pre w.nparams w.nMinors
          fields' w.kinds w.ctorAfterParams)) :=
  parRed_foldApps_congr
    (parRed_rhsArgs_congr_total hE (.refl Γ (.const w.recRef w.ls))
      w.hfam w.hfamK w.nparams (w.preMajor.take w.nparams)
      (parRedArgs_refl pre) w.nparams w.nMinors hfs w.kinds
      (.refl _ w.ctorAfterParams) w.hctorTel (envWf_iotaTyping hE w).hfamSpine)
    (.refl _ minor)

/-- Collapse a star of length ≤ 1 to a single `ParRed`. Does not
match `.refl` to *build* a star (that is the old elim bug). -/
def parRed_of_star_one {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b : Expr Nat} :
    ParRedStar E n Γ a b → Option (ParRed E n Γ a b)
  | .refl _ e => some (.refl _ e)
  | .tail h hs =>
      match parRedStar_eq_of_refl hs with
      | some ⟨heq⟩ => some (heq ▸ h)
      | none => none

/-! ### Pairwise diamond (Tait–Martin-Löf), attempt 52.

`parRed_iotaRhs_to_cert` is the iota-vs-iotaSpine engine.
`parRed_instantiate_both_assump` is beta's substitution join.
letE/zeta join at the zeta reduct (`instantiate0`), body stays in the
source let (type-irrelevant; value join is `instantiate_arg` then
the same-value `instantiate_let0` after transporting the value). -/

/-- `isPiTel` survives a parallel step (Π-congruence). -/
theorem isPiTel_of_parRed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T T' : Expr Nat} (h : ParRed E n Γ T T') :
    (k : Nat) → isPiTel k T = true → isPiTel k T' = true
  | 0, _ => rfl
  | k + 1, htel => by
      match T, htel with
      | .pi _A B, htel =>
          have ⟨_A', B', heq, _hA, hB⟩ := parRed_pi h rfl
          subst heq
          simp only [isPiTel] at htel ⊢
          exact isPiTel_of_parRed hB k htel
      | .bvar _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .sort _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .const _ _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .app _ _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .lam _ _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .letE _ _ _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel
      | .lit _, htel =>
          simp only [isPiTel] at htel; exact Bool.noConfusion htel

/-- DirectRec family spine along a parallel step of the remaining
ctor telescope. Head is `const fam`; params' ParRed does not move
that const (inductive-headed `parRed_foldApps_inductive`). Copy of
`directRecFamilySpine_lift` / `_instantiate`. -/
def directRecFamilySpine_parRed {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx}
    {fam : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members fam = some m)
    (hK : m.mclass = MemberClass.inductiveM)
    (nparams : Nat) {params params' : List (Expr Nat)}
    (_hp : ParRedArgs E n Γ params params') :
    (ks : List RecKind) → {T T' : Expr Nat} → {fs fs' : List (Expr Nat)} →
    ParRed E n Γ T T' →
    ParRedArgs E n Γ fs fs' →
    isPiTel ks.length T = true →
    directRecFamilySpine fam ls nparams params ks T fs = true →
    directRecFamilySpine fam ls nparams params' ks T' fs' = true
  | [], _T, _T', _fs, _fs', _hT, _hfs, _htel, _hsp => by
      simp only [directRecFamilySpine]
  | .plain :: ks, T, T', fs, fs', hT, hfs, htel, hsp => by
      cases T with
      | pi _A B =>
          match fs, hfs with
          | f :: _fs, .cons hf hfs =>
              have ⟨_A', B', heq, _hA, hB⟩ := parRed_pi hT rfl
              subst heq
              simp only [isPiTel, List.length_cons, directRecFamilySpine]
                at htel hsp ⊢
              have hTnext := parRed_instantiate_both_assump hE hf hB
              exact directRecFamilySpine_parRed hE hres hK nparams _hp
                ks hTnext hfs (isPiTel_instantiate 0 f ks.length B htel) hsp
          | [], ParRedArgs.nil _ =>
              simp only [directRecFamilySpine]
      | bvar _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | sort _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | const _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | app _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | lam _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | letE _ _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | lit _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
  | .directRec :: ks, T, T', fs, fs', hT, hfs, htel, hsp => by
      cases T with
      | pi A B =>
          match fs, hfs with
          | f :: _fs, .cons hf hfs =>
              have ⟨A', B', heq, hA, hB⟩ := parRed_pi hT rfl
              subst heq
              simp only [isPiTel, List.length_cons] at htel
              simp only [directRecFamilySpine, Bool.and_eq_true] at hsp ⊢
              obtain ⟨hhead, hrest⟩ := hsp
              cases hhd : (appsSpine A).1 with
              | const rA lsA =>
                  have hr : rA = fam := of_decide_eq_true (by
                    simp only [hhd] at hhead; exact hhead)
                  have heqA : A = foldApps (.const fam lsA) (appsSpine A).2 := by
                    have hfold := foldApps_appsSpine A
                    rw [hhd, hr] at hfold
                    exact hfold.symm
                  let ⟨_ls', xs', heqA', _hls, _hargs⟩ :=
                    parRed_foldApps_inductive (r := fam) (ls := lsA) hres hK hA
                      (appsSpine A).2 heqA
                  subst heqA'
                  have hhead' :
                      (match (appsSpine (foldApps (.const fam _ls') xs')).1 with
                        | .const r _ => decide (r = fam)
                        | _ => false) = true := by
                    rw [appsSpine_foldApps, appsSpine_const, List.nil_append]
                    exact decide_eq_true rfl
                  have hTnext := parRed_instantiate_both_assump hE hf hB
                  have hrest' :=
                    directRecFamilySpine_parRed (fam := fam) (ls := ls) hE hres hK
                      nparams _hp ks hTnext hfs
                      (isPiTel_instantiate 0 f ks.length B htel) hrest
                  exact ⟨hhead', hrest'⟩
              | bvar _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | sort _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | app _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | lam _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | pi _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | letE _ _ _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
              | lit _ =>
                  simp only [hhd] at hhead; exact Bool.noConfusion hhead
          | [], ParRedArgs.nil _ =>
              simp only [directRecFamilySpine]
      | bvar _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | sort _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | const _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | app _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | lam _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | letE _ _ _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel
      | lit _ =>
          simp only [isPiTel, List.length_cons] at htel
          exact Bool.noConfusion htel

/-- `isFamilyApp` means the spine head is a constant (05 DirectRec). -/
theorem isFamilyApp_spineHeadConst {fam : Nat} {e : Expr Nat}
    (h : isFamilyApp fam e = true) : spineHeadConst e = true := by
  cases hsp : appsSpine e with
  | mk hd args =>
      cases hd with
      | const _ _ => simp only [spineHeadConst, hsp]
      | bvar _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | sort _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | app _ _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | lam _ _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | pi _ _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | letE _ _ _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h
      | lit _ =>
          simp only [isFamilyApp, hsp] at h; exact Bool.noConfusion h

theorem analyzeField_directRec_isFamilyApp {fam : Nat} {T : Expr Nat}
    (h : analyzeField fam T = some RecKind.directRec) :
    isFamilyApp fam T = true := by
  simp only [analyzeField] at h
  split at h
  · injection h with hk
    exact nomatch hk
  · split at h
    · next hf => exact hf
    · exact Option.noConfusion h

def analyzeFields_cons_inv {fam : Nat} {T : Expr Nat}
    {Ts : List (Expr Nat)} {k : RecKind} {ks : List RecKind}
    (h : analyzeFields fam (T :: Ts) = some (k :: ks)) :
    (analyzeField fam T = some k) ×' (analyzeFields fam Ts = some ks) := by
  simp only [analyzeFields] at h
  cases hf : analyzeField fam T with
  | none =>
      simp only [hf] at h
      exact Option.noConfusion h
  | some k' =>
      cases hfs : analyzeFields fam Ts with
      | none =>
          simp only [hf, hfs] at h
          exact Option.noConfusion h
      | some ks' =>
          simp only [hf, hfs] at h
          injection h with hp
          injection hp with hk hks
          subst hk
          subst hks
          exact ⟨rfl, rfl⟩

/-- Original DirectRec domains from `analyzeFields` are family apps,
hence const-headed. Honest source of `hfamTel`: a `_parRed` lemma is
false (delta of a definition can drop the const head). -/
theorem directRecConstHead_of_analyzeFields (fam : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis ks.length T = some (ds, r) →
    analyzeFields fam ds = some ks →
    directRecConstHead ks T = true
  | [], _, _, _, _, _ => rfl
  | k :: ks, T, ds, r, hpeel, hkinds => by
      have ⟨A, B, ds', hT, hds, hpeelB⟩ :=
        peelPis_succ (n := ks.length) hpeel
      subst hT
      subst hds
      have ⟨hA, hrest⟩ := analyzeFields_cons_inv hkinds
      cases k with
      | plain =>
          simp only [directRecConstHead]
          exact directRecConstHead_of_analyzeFields fam ks B hpeelB hrest
      | directRec =>
          simp only [directRecConstHead]
          have hsc :=
            isFamilyApp_spineHeadConst
              (analyzeField_directRec_isFamilyApp hA)
          have ih :=
            directRecConstHead_of_analyzeFields fam ks B hpeelB hrest
          simp only [hsc, ih]
          rfl

/-- Walking `n` leading plains then `ks` on the uninstantiated ctor
type: param binders are not DirectRec (05 AnalyzeField of fields). -/
theorem directRecConstHead_plain_prefix_of_analyzeFields (fam : Nat) :
    (n : Nat) → (ks : List RecKind) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis (n + ks.length) T = some (ds, r) →
    analyzeFields fam (ds.drop n) = some ks →
    directRecConstHead (List.replicate n RecKind.plain ++ ks) T = true
  | 0, ks, T, ds, r, hpeel, hkinds => by
      simp only [Nat.zero_add] at hpeel
      exact directRecConstHead_of_analyzeFields fam ks T hpeel hkinds
  | n + 1, ks, T, ds, r, hpeel, hkinds => by
      have hidx : n + 1 + ks.length = (n + ks.length) + 1 := by omega
      rw [hidx] at hpeel
      have ⟨A, B, ds', hT, hds, hpeelB⟩ :=
        peelPis_succ (n := n + ks.length) hpeel
      subst hT
      subst hds
      simp only [List.replicate, List.cons_append, directRecConstHead]
      exact directRecConstHead_plain_prefix_of_analyzeFields fam n ks B
        hpeelB hkinds

theorem replicate_length (n : Nat) (a : RecKind) :
    (List.replicate n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate, List.length_cons, ih]

/-- `applyTel` of any args through a plain prefix preserves
`directRecConstHead` of the remaining field telescope: DirectRec
domains are already const-headed family apps, and instantiate of a
const-headed spine does not depend on the value. -/
theorem directRecConstHead_applyTel (ks : List RecKind) :
    (xs : List (Expr Nat)) → (T U : Expr Nat) →
    applyTel xs T = some U →
    isPiTel (xs.length + ks.length) T = true →
    directRecConstHead (List.replicate xs.length RecKind.plain ++ ks) T =
      true →
    directRecConstHead ks U = true
  | [], T, U, happ, _, hfam => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      exact hfam
  | x :: xs, T, U, happ, htel, hfam => by
      have ⟨A, B, hT, happ'⟩ := applyTel_cons_inv x xs happ
      subst hT
      simp only [List.length_cons] at htel hfam
      have hsucc : xs.length + 1 + ks.length =
          (xs.length + ks.length) + 1 := by omega
      rw [hsucc] at htel
      simp only [isPiTel] at htel
      simp only [List.replicate, List.cons_append, directRecConstHead]
        at hfam
      have hlenK :
          (List.replicate xs.length RecKind.plain ++ ks).length =
            xs.length + ks.length := by
        simp only [List.length_append, replicate_length]
      have hfamI :=
        directRecConstHead_instantiate 0 x
          (List.replicate xs.length RecKind.plain ++ ks) B
          (hlenK ▸ htel) hfam
      exact directRecConstHead_applyTel ks xs (instantiate0 x B) U happ'
        (isPiTel_instantiate 0 x (xs.length + ks.length) B htel) hfamI

/-- The ctor telescope's RESULT is the peeled `r`, whatever kinds the
walk carries; `isFamilyApp` of `r` (05 §6) makes the base
`spineHeadConst` hold. Honest source of `hresTel`, sibling of
`directRecConstHead_of_analyzeFields` for `hfamTel`. Needs no
`analyzeFields`: only the base of the walk is constrained. -/
theorem resultConstHead_of_peelPis :
    (ks : List RecKind) → (T : Expr Nat) →
    {ds : List (Expr Nat)} → {r : Expr Nat} →
    peelPis ks.length T = some (ds, r) →
    spineHeadConst r = true →
    resultConstHead ks T = true
  | [], T, _ds, r, hpeel, hsc => by
      have hr : T = r := congrArg Prod.snd (Option.some.inj hpeel)
      simp only [resultConstHead, hr]
      exact hsc
  | k :: ks, T, ds, r, hpeel, hsc => by
      have ⟨A, B, ds', hT, hds, hpeelB⟩ :=
        peelPis_succ (n := ks.length) hpeel
      subst hT
      subst hds
      cases k with
      | plain =>
          simp only [resultConstHead]
          exact resultConstHead_of_peelPis ks B hpeelB hsc
      | directRec =>
          simp only [resultConstHead]
          exact resultConstHead_of_peelPis ks B hpeelB hsc

/-- `applyTel` of any args through a plain prefix preserves
`resultConstHead` of the remaining field telescope: the result is a
const-headed family app, and `instantiate` of a const-headed spine
does not depend on the value. Sibling of
`directRecConstHead_applyTel`. -/
theorem resultConstHead_applyTel (ks : List RecKind) :
    (xs : List (Expr Nat)) → (T U : Expr Nat) →
    applyTel xs T = some U →
    isPiTel (xs.length + ks.length) T = true →
    resultConstHead (List.replicate xs.length RecKind.plain ++ ks) T =
      true →
    resultConstHead ks U = true
  | [], T, U, happ, _, hres => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      exact hres
  | x :: xs, T, U, happ, htel, hres => by
      have ⟨A, B, hT, happ'⟩ := applyTel_cons_inv x xs happ
      subst hT
      simp only [List.length_cons] at htel hres
      have hsucc : xs.length + 1 + ks.length =
          (xs.length + ks.length) + 1 := by omega
      rw [hsucc] at htel
      simp only [isPiTel] at htel
      simp only [List.replicate, List.cons_append, resultConstHead] at hres
      have hlenK :
          (List.replicate xs.length RecKind.plain ++ ks).length =
            xs.length + ks.length := by
        simp only [List.length_append, replicate_length]
      have hresI :=
        resultConstHead_instantiate 0 x
          (List.replicate xs.length RecKind.plain ++ ks) B
          (hlenK ▸ htel) hres
      exact resultConstHead_applyTel ks xs (instantiate0 x B) U happ'
        (isPiTel_instantiate 0 x (xs.length + ks.length) B htel) hresI

/-- Witness transport along `ParRedArgs` of the recursor prefix,
ctor fields, and ctor-side params. The two param copies (recursor
`preMajor.take nparams` vs major `ctorParams`) reduce independently;
kernel iota never identifies them. Env fields are copied;
arg-dependent lengths and family-spine/ctor-tel are re-derived.
`lsC` is filled with `lsC'`. Template: `liftWitness` / `instWitness`. -/
def parRedWitness {E : ResolvedEnv} {n : Nat} (_hE : EnvWf E n)
    {Γ : LCtx} (w : IotaWitness E)
    {pre' fields' ctorParams' : List (Expr Nat)}
    (hf : ParRedArgs E n Γ w.preMajor pre')
    (ha : ParRedArgs E n Γ w.fields fields')
    (hc : ParRedArgs E n Γ w.ctorParams ctorParams') :
    Σ' (w' : IotaWitness E),
      (iotaLhsOf w' = recCall (.const w.recRef w.ls) pre'
        (foldApps (.const w.ctorRef w.lsC)
          (ctorParams' ++ fields'))) ×'
      (w'.preMajor = pre') ×'
      (w'.fields = fields') ×'
      (w'.ctorParams = ctorParams') ×'
      (w'.recRef = w.recRef) ×'
      (w'.ctorRef = w.ctorRef) ×'
      (w'.ls = w.ls) ×'
      (w'.lsC = w.lsC) := by
  have hlenP : pre'.length = w.preMajor.length := (parRedArgs_length hf).symm
  have hlenF : fields'.length = w.fields.length := (parRedArgs_length ha).symm
  have htkLen : (pre'.take w.nparams).length = w.nparams := by
    simp only [List.length_take, hlenP, w.hpre]; omega
  -- 00 §20.6: the fresh witness's `hctorAfter` is at the recursor-side
  -- view `instantiateLevels w.ls w.ctorMember.mtype`, so the whole
  -- re-derivation of `ctorAfter'` moves there. `isPiTel` transports by
  -- `peelPis_instantiateLevels`; the two 05 declaration shapes
  -- (`directRecConstHead` / `resultConstHead`) transport by being
  -- level-blind (`*_instantiateLevels`, RcicLevelCalc), so no
  -- `analyzeFields`-invariance lemma is needed.
  have htelC : isPiTel (w.nparams + w.fields.length)
      (instantiateLevels w.ls w.ctorMember.mtype) = true :=
    peelPis_isPiTel _ _ (peelPis_instantiateLevels w.ls _ _ w.hpeel)
  have htelCn : isPiTel w.nparams
      (instantiateLevels w.ls w.ctorMember.mtype) = true :=
    isPiTel_le (by omega) htelC
  have ⟨ctorAfter', hca'⟩ :=
    applyTel_isPiTel w.nparams (instantiateLevels w.ls w.ctorMember.mtype)
      (pre'.take w.nparams) htkLen htelCn
  have hctorTel' : isPiTel w.kinds.length ctorAfter' = true := by
    have hk : w.kinds.length = w.fields.length := w.hlen
    rw [hk]
    exact isPiTel_of_applyTel w.nparams w.fields.length
      (instantiateLevels w.ls w.ctorMember.mtype) (pre'.take w.nparams) htkLen
      (Nat.add_comm w.nparams w.fields.length ▸ htelC) hca'
  have hpeelK : peelPis (w.nparams + w.kinds.length) w.ctorMember.mtype =
      some (w.ctorDoms, w.ctorResult) := by
    rw [w.hlen]; exact w.hpeel
  have hpad :
      directRecConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
    rw [directRecConstHead_instantiateLevels]
    exact directRecConstHead_plain_prefix_of_analyzeFields
      w.familyRef w.nparams w.kinds w.ctorMember.mtype hpeelK w.hkinds
  have ⟨minor', hmin', _hminor⟩ := parRedArgs_get hf w.hminor
  have hfamTel' : directRecConstHead w.kinds ctorAfter' = true :=
    directRecConstHead_applyTel w.kinds (pre'.take w.nparams)
      (instantiateLevels w.ls w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpad)
  have hpadRes :
      resultConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels w.ls w.ctorMember.mtype) = true := by
    rw [resultConstHead_instantiateLevels]
    exact resultConstHead_of_peelPis
      (List.replicate w.nparams RecKind.plain ++ w.kinds)
      w.ctorMember.mtype
      (by
        rw [List.length_append, replicate_length]
        exact hpeelK)
      (isFamilyApp_spineHeadConst w.hfamApp)
  have hresTel' : resultConstHead w.kinds ctorAfter' = true :=
    resultConstHead_applyTel w.kinds (pre'.take w.nparams)
      (instantiateLevels w.ls w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpadRes)
  exact ⟨{
    recRef := w.recRef
    ctorRef := w.ctorRef
    ls := w.ls
    lsC := w.lsC
    recMember := w.recMember
    ctorMember := w.ctorMember
    hrec := w.hrec
    hctor := w.hctor
    hrecK := w.hrecK
    hctorK := w.hctorK
    preMajor := pre'
    fields := fields'
    ctorParams := ctorParams'
    kinds := w.kinds
    minor := minor'
    hlen := w.hlen.trans hlenF.symm
    familyRef := w.familyRef
    famMember := w.famMember
    hfam := w.hfam
    hfamK := w.hfamK
    nparams := w.nparams
    nindices := w.nindices
    nMinors := w.nMinors
    ctorIdx := w.ctorIdx
    hctorParams := by
      have hlenC : ctorParams'.length = w.ctorParams.length :=
        (parRedArgs_length hc).symm
      rw [hlenC]; exact w.hctorParams
    hnpar := by rw [hlenF]; exact w.hnpar
    hnidx := w.hnidx
    hnmin := w.hnmin
    hidx := w.hidx
    hctorIdx := w.hctorIdx
    hrecIdx := w.hrecIdx
    hpre := by rw [hlenP]; exact w.hpre
    hminor := hmin'
    ctorDoms := w.ctorDoms
    ctorResult := w.ctorResult
    hpeel := by rw [hlenF]; exact w.hpeel
    hfamApp := w.hfamApp
    hkinds := w.hkinds
    recDoms := w.recDoms
    recBody := w.recBody
    hpeelRec := w.hpeelRec
    hrecBody := w.hrecBody
    hmajorTy := w.hmajorTy
    hrecClosed := w.hrecClosed
    hctorClosed := w.hctorClosed
    hlsLen := w.hlsLen
    ctorAfterParams := ctorAfter'
    hctorAfter := hca'
    hctorTel := hctorTel'
    hfamTel := hfamTel'
    hresTel := hresTel'
  }, ⟨by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall],
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- TOTAL iota-vs-app is `parRed_iota_vs_app_total` in the diamond
mutual (needs `parRedArgs_diamond` + recert of the joined spine). -/


def parRed_bvar {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRed E n Γ a e → {i : Nat} → a = .bvar i →
    (e = .bvar i) ⊕'
      (Σ' (A v v' : Expr Nat),
        (Γ.get? i = some (.letBinding A v)) ×'
        ParRed E n (Γ.drop (i + 1)) v v' ×'
        (e = lift 0 (i + 1) v'))
  | _, _, _, .refl _ a, i, heq => by
      subst heq
      exact .inl rfl
  | _, _, _, .bvarZeta _ i0 A v v' hlk hv, i, heq => by
      injection heq with hi
      subst hi
      exact .inr ⟨A, v, v', hlk, hv, rfl⟩
  | _, _, _, .sortEq _ _ _ _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, i, heq =>
      (foldApps_snoc_ne_bvar (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim
  | _, _, _, .lit _ _, _, heq => nomatch heq

/-- bvarZeta (inr of `parRed_bvar`): the stored-value premise is paid
by `h`. -/
theorem parRedW_of_bvarZeta {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    (h : ParRed E n Γ a e) → {i : Nat} → (heq : a = .bvar i) →
    (p : Σ' (A v v' : Expr Nat),
      (Γ.get? i = some (.letBinding A v)) ×'
      ParRed E n (Γ.drop (i + 1)) v v' ×'
      (e = lift 0 (i + 1) v')) →
    (hsum : parRed_bvar h heq = .inr p) →
    parRedW p.2.2.2.2.1 ≤ parRedW h
  | _, _, _, .bvarZeta _ i0 A v v' hlk hv, i, heq, p, hsum => by
      injection heq with hi
      subst hi
      simp only [parRed_bvar] at hsum
      injection hsum with hp
      cases hp
      simp only [parRedW]
      omega
  | _, _, _, .refl _ a, i, heq, p, hsum => by
      subst heq
      simp only [parRed_bvar] at hsum
      exact nomatch hsum
  | _, _, _, .sortEq _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .delta .., _, heq, _, _ => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, heq, _, _ => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, i, heq, p, hsum =>
      (foldApps_snoc_ne_bvar (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim
  | _, _, _, .lit _ _, _, heq, _, _ => nomatch heq

def parRed_lit {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRed E n Γ a e → {t : Nat} → a = .lit t →
    (e = .lit t) ⊕' (e = natExpand t)
  | _, _, _, .refl _ a, t, heq => by
      subst heq
      exact .inl rfl
  | _, _, _, .lit _ t0, t, heq => by
      injection heq with ht
      subst ht
      exact .inr rfl
  | _, _, _, .sortEq _ _ _ _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, t, heq =>
      (foldApps_snoc_ne_lit (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim

theorem lookupValue_let_ty_irrel (A A' v : Expr Nat) (Γ : LCtx) (i : Nat) :
    lookupValue (.letBinding A v :: Γ) i =
      lookupValue (.letBinding A' v :: Γ) i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [lookupValue, List.get?, List.get?_cons_succ]

def parRed_replace_let_ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v : Expr Nat} {a b : Expr Nat} :
    ParRed E n (.letBinding A v :: Γ) a b →
    ParRed E n (.letBinding A' v :: Γ) a b :=
  parRed_ctx_lookup (lookupValue_let_ty_irrel A A' v Γ)

/-- Cast a diamond join across an equality on the second reduct. -/
def joinCast {E : ResolvedEnv} {n : Nat} {Γ1 Γ2 : LCtx} {b : Expr Nat}
    {c₀ c₁ : Expr Nat} (heq : c₀ = c₁)
    (j : Σ' (d : Expr Nat), ParRed E n Γ1 b d ×' ParRed E n Γ2 c₀ d) :
    Σ' (d : Expr Nat), ParRed E n Γ1 b d ×' ParRed E n Γ2 c₁ d :=
  Eq.rec (motive := fun t _ =>
      Σ' (d : Expr Nat), ParRed E n Γ1 b d ×' ParRed E n Γ2 t d) j heq

theorem lookupValue_let_succ_irrel (A A' v v' : Expr Nat) (Γ : LCtx)
    (i : Nat) (hi : i ≠ 0) :
    lookupValue (.letBinding A v :: Γ) i =
      lookupValue (.letBinding A' v' :: Γ) i := by
  cases i with
  | zero => exact (hi rfl).elim
  | succ i =>
      simp only [lookupValue, List.get?_cons_succ]

theorem lookupValue_let_zero (A v : Expr Nat) (Γ : LCtx) :
    lookupValue (.letBinding A v :: Γ) 0 = some (lift 0 1 v) := by
  simp only [lookupValue, List.get?_cons_zero]

/-- Free `bvar k` (binders shift the index). Used to relet a derivation
that never reads slot `k`. -/
def exprHasBvar : Nat → Expr Nat → Bool
  | k, .bvar i => decide (i = k)
  | _, .sort _ => false
  | _, .const _ _ => false
  | _, .lit _ => false
  | k, .app f x => exprHasBvar k f || exprHasBvar k x
  | k, .lam A b => exprHasBvar k A || exprHasBvar (k + 1) b
  | k, .pi A b => exprHasBvar k A || exprHasBvar (k + 1) b
  | k, .letE A v b =>
      exprHasBvar k A || exprHasBvar k v || exprHasBvar (k + 1) b

theorem lift_not_bvar_cutoff (c amt : Nat) (hamt : 0 < amt) :
    (e : Expr Nat) → exprHasBvar c (lift c amt e) = false
  | .bvar i => by
      simp only [lift]
      by_cases h : c ≤ i
      · simp only [if_pos h, exprHasBvar, decide_eq_false_iff_not]
        exact fun heq => by omega
      · simp only [if_neg h, exprHasBvar, decide_eq_false_iff_not]
        exact fun heq => by omega
  | .sort _ => by simp only [lift, exprHasBvar]
  | .const _ _ => by simp only [lift, exprHasBvar]
  | .lit _ => by simp only [lift, exprHasBvar]
  | .app f x => by
      simp only [lift, exprHasBvar, lift_not_bvar_cutoff c amt hamt f,
        lift_not_bvar_cutoff c amt hamt x, Bool.or_self]
  | .lam A b => by
      simp only [lift, exprHasBvar, lift_not_bvar_cutoff c amt hamt A,
        lift_not_bvar_cutoff (c + 1) amt hamt b, Bool.or_self]
  | .pi A b => by
      simp only [lift, exprHasBvar, lift_not_bvar_cutoff c amt hamt A,
        lift_not_bvar_cutoff (c + 1) amt hamt b, Bool.or_self]
  | .letE A v b => by
      simp only [lift, exprHasBvar, lift_not_bvar_cutoff c amt hamt A,
        lift_not_bvar_cutoff c amt hamt v,
        lift_not_bvar_cutoff (c + 1) amt hamt b,
        Bool.or_self, Bool.or_false]

theorem lookupValue_let_succ_is_lift (A v : Expr Nat) (Γ : LCtx) (i : Nat)
    {w : Expr Nat}
    (h : lookupValue (.letBinding A v :: Γ) (i + 1) = some w) :
    exprHasBvar 0 w = false := by
  rw [lookupValue_cons_succ] at h
  cases hΓ : lookupValue Γ i with
  | none =>
      simp only [hΓ, Option.map_none'] at h
      exact nomatch h
  | some w0 =>
      simp only [hΓ, Option.map_some'] at h
      injection h with hw
      subst hw
      exact lift_not_bvar_cutoff 0 1 (Nat.succ_pos 0) w0

/-- Slot-0 unused: `drop_let` between two lets that agree off slot 0. -/
def parRed_relet0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} {a b : Expr Nat} :
    ParRed E n (.letBinding A v :: Γ) a b →
    Option (ParRed E n (.letBinding A' v' :: Γ) a b) :=
  parRed_drop_let 0
    (fun i hi => lookupValue_let_succ_irrel A A' v v' Γ i hi)

set_option maxHeartbeats 8000000

mutual

noncomputable def parRedArgs_diamond (E : ResolvedEnv) (n : Nat) (hE : EnvWf E n)
    {Γ Γ1 Γ2 : LCtx} {xs ys zs : List (Expr Nat)}
    (h1 : ParRedArgs E n Γ xs ys) (h2 : ParRedArgs E n Γ xs zs)
    (hΓ1 : ParRedCtx E n Γ Γ1) (hΓ2 : ParRedCtx E n Γ Γ2) :
    Σ' (ws : List (Expr Nat)),
      ParRedArgs E n Γ1 ys ws ×' ParRedArgs E n Γ2 zs ws :=
  match h1 with
  | ParRedArgs.nil _ =>
      match h2 with
      | ParRedArgs.nil _ =>
          ⟨[], ParRedArgs.nil Γ1, ParRedArgs.nil Γ2⟩
  | ParRedArgs.cons hx t1 =>
      match h2 with
      | ParRedArgs.cons hy t2 =>
          have hxpos := parRedW_pos hx
          have hypos := parRedW_pos hy
          have t1pos := parRedArgsW_pos t1
          have t2pos := parRedArgsW_pos t2
          let ⟨d, hd1, hd2⟩ := parRed_diamond E n hE hx hy hΓ1 hΓ2
          let ⟨ds, tL, tR⟩ :=
            parRedArgs_diamond E n hE (h1 := t1) (h2 := t2) hΓ1 hΓ2
          ⟨d :: ds, .cons hd1 tL, .cons hd2 tR⟩
termination_by parRedArgsW h1 + parRedArgsW h2 + parRedCtxW hΓ1 + parRedCtxW hΓ2
decreasing_by
  all_goals simp_all [parRedW, parRedArgsW, parRedCtxW, exprSize]
  all_goals try (have := parRedW_pos (by assumption))
  all_goals try (have := parRedArgsW_pos (by assumption))
  all_goals omega

/-- `h1` is refl: invert `h2`. Congruence recurses on `h2`'s premises
via this function (nested on `h2`, not on a term-follow of ctx).
`refl` vs `refl` is two refls — not let_follow. -/
noncomputable def parRed_diamond_from (E : ResolvedEnv) (n : Nat) (hE : EnvWf E n)
    {Γ Γ1 Γ2 : LCtx} {a c : Expr Nat}
    (h2 : ParRed E n Γ a c)
    (hΓ1 : ParRedCtx E n Γ Γ1) (hΓ2 : ParRedCtx E n Γ Γ2) :
    Σ' (d : Expr Nat), ParRed E n Γ1 a d ×' ParRed E n Γ2 c d :=
  match h2 with
  | .refl _ e => ⟨e, .refl Γ1 e, .refl Γ2 e⟩
  | .sortEq _ l₁ l₂ q =>
      ⟨.sort l₂, .sortEq Γ1 l₁ l₂ q, .refl Γ2 _⟩
  | .consts _ r ls ls' q =>
      ⟨.const r ls', .consts Γ1 r ls ls' q, .refl Γ2 _⟩
  | .lit _ t =>
      ⟨natExpand t, .lit Γ1 t, .refl Γ2 _⟩
  | .app _ f f' x x' hf ha =>
      let ⟨df, hf1, hf2⟩ := parRed_diamond_from E n hE hf hΓ1 hΓ2
      let ⟨dx, hx1, hx2⟩ := parRed_diamond_from E n hE ha hΓ1 hΓ2
      ⟨.app df dx,
        .app Γ1 f df x dx hf1 hx1,
        .app Γ2 f' df x' dx hf2 hx2⟩
  | .lam _ A A' b b' hA hb =>
      let ⟨Aj, hA1, hA2⟩ := parRed_diamond_from E n hE hA hΓ1 hΓ2
      let ⟨bj, hb1, hb2⟩ :=
        parRed_diamond_from E n hE hb
          (.assumption hA hΓ1) (.assumption hA hΓ2)
      ⟨.lam Aj bj,
        .lam Γ1 A Aj b bj hA1
          (@parRed_replace_assump E n Γ1 A' A b bj hb1),
        .lam Γ2 A' Aj b' bj hA2 hb2⟩
  | .pi _ A A' B B' hA hB =>
      let ⟨Aj, hA1, hA2⟩ := parRed_diamond_from E n hE hA hΓ1 hΓ2
      let ⟨Bj, hB1, hB2⟩ :=
        parRed_diamond_from E n hE hB
          (.assumption hA hΓ1) (.assumption hA hΓ2)
      ⟨.pi Aj Bj,
        .pi Γ1 A Aj B Bj hA1
          (@parRed_replace_assump E n Γ1 A' A B Bj hB1),
        .pi Γ2 A' Aj B' Bj hA2 hB2⟩
  | .letE _ A A' v v' b b' hA hv hb =>
      let ⟨Aj, hA1, hA2⟩ := parRed_diamond_from E n hE hA hΓ1 hΓ2
      let ⟨vj, hv1, hv2⟩ := parRed_diamond_from E n hE hv hΓ1 hΓ2
      let ⟨bj, hb1, hb2⟩ :=
        parRed_diamond_from E n hE hb
          (.letBinding (.refl Γ A) (.refl Γ v) hΓ1)
          (.letBinding hA hv hΓ2)
      ⟨.letE Aj vj bj,
        .letE Γ1 A Aj v vj b bj hA1 hv1 hb1,
        .letE Γ2 A' Aj v' vj b' bj hA2 hv2 hb2⟩
  | .beta _ A A' body body' arg arg' hA hb ha =>
      let ⟨Aj, hA1, hA2⟩ := parRed_diamond_from E n hE hA hΓ1 hΓ2
      let ⟨bj, hb1, hb2⟩ :=
        parRed_diamond_from E n hE hb
          (.assumption hA hΓ1) (.assumption hA hΓ2)
      let ⟨xj, hx1, hx2⟩ := parRed_diamond_from E n hE ha hΓ1 hΓ2
      ⟨instantiate0 xj bj,
        .beta Γ1 A Aj body bj arg xj hA1
          (@parRed_replace_assump E n Γ1 A' A body bj hb1) hx1,
        @parRed_instantiate_both_assump E n hE Γ2 A' arg' xj hx2
          body' bj hb2⟩
  | .zeta _ A A' v v' b b' hA hv hb =>
      let ⟨Aj, hA1, hA2⟩ := parRed_diamond_from E n hE hA hΓ1 hΓ2
      let ⟨vj, hv1, hv2⟩ := parRed_diamond_from E n hE hv hΓ1 hΓ2
      let ⟨bj, hb1, hb2⟩ :=
        parRed_diamond_from E n hE hb
          (.letBinding (.refl Γ A) (.refl Γ v) hΓ1)
          (.letBinding hA hv hΓ2)
      ⟨instantiate0 vj bj,
        .zeta Γ1 A Aj v vj b bj hA1 hv1 hb1,
        parRed_instantiate_both_let hE hv2 hb2⟩
  | .delta _ r ls m b hres hbody htr =>
      -- 00 §20.6: the reduct is `instantiateLevels ls b`, so that is the
      -- apex; the `Γ2` leg is still `refl` (nothing moved on that side).
      ⟨instantiateLevels ls b, .delta Γ1 r ls m b hres hbody htr, .refl Γ2 _⟩
  | .bvarZeta _ i A v v' hlk hv => by
      let g1 := parRedCtx_get?_let hΓ1 hlk
      let g2 := parRedCtx_get?_let hΓ2 hlk
      let A1 := g1.1
      let vs1 := g1.2.1
      let hg1 := g1.2.2.1
      let hv1c := g1.2.2.2.1
      let A2 := g2.1
      let vs2 := g2.2.1
      let hg2 := g2.2.2.1
      let hv2c := g2.2.2.2.1
      have hpay1 := parRedCtxW_get?_let hΓ1 hlk
      have hpay2 := parRedCtxW_get?_let hΓ2 hlk
      have ⟨vj, hRtail, hLtail⟩ :=
        parRed_diamond E n hE hv hv1c
          (parRedCtx_drop (i + 1) hΓ2)
          (parRedCtx_drop (i + 1) hΓ1)
      have hpre2 : Γ2.take (i + 1) ++ Γ2.drop (i + 1) = Γ2 :=
        List.take_append_drop (i + 1) Γ2
      have hlen2 : (Γ2.take (i + 1)).length = i + 1 :=
        List.length_take_of_le (Nat.succ_le_of_lt (get?_some_lt hg2))
      have hR := parRed_lift_n hE (Γ2.take (i + 1)) hRtail
      rw [hlen2] at hR
      exact ⟨lift 0 (i + 1) vj,
        .bvarZeta Γ1 i A1 vs1 vj hg1 hLtail,
        hpre2 ▸ hR⟩
  | .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs => by
      have hpreW := parRedArgsW_refl (E := E) (n := n) (Γ := Γ) pre
      have hfsW := parRedArgsW_refl (E := E) (n := n) (Γ := Γ) fields
      have hfold :=
        exprSize_foldApps (.const w2.recRef lsR)
          (pre ++ [foldApps (.const w2.ctorRef lsC) fields])
      have hfoldF :=
        exprSize_foldApps (.const w2.ctorRef lsC) fields
      have hadd1 :=
        foldr_exprSize_add
          (1 + fields.foldr (fun x acc => exprSize x + acc + 1) 0)
          pre 1
      have hadd2 :=
        foldr_exprSize_add
          (fields.foldr (fun x acc => exprSize x + acc + 1) 0 + 1)
          pre 1
      have hseed :
          1 + fields.foldr (fun x acc => exprSize x + acc + 1) 0 + 1 =
            1 + (1 + fields.foldr (fun x acc => exprSize x + acc + 1) 0) :=
        by omega
      have hsnoc :=
        foldr_exprSize_snoc pre
          (foldApps (.const w2.ctorRef lsC) fields) 0
      have hpreLt :
          parRedArgsW (parRedArgs_refl (E := E) (n := n) (Γ := Γ) pre)
            < exprSize (foldApps (.const w2.recRef lsR)
                (pre ++ [foldApps (.const w2.ctorRef lsC) fields])) + 1 := by
        rw [hpreW, hfold, hsnoc, hfoldF]
        simp only [exprSize]
        have hassoc :
            1 + fields.foldr (fun x acc => exprSize x + acc + 1) 0 + 0 + 1 =
              1 + (fields.foldr (fun x acc => exprSize x + acc + 1) 0 + 1) :=
          by omega
        rw [hassoc, hadd2]
        omega
      have hfsLt :
          parRedArgsW (parRedArgs_refl (E := E) (n := n) (Γ := Γ) fields)
            < exprSize (foldApps (.const w2.ctorRef lsC) fields) + 1 := by
        rw [hfsW, hfoldF]
        simp only [exprSize]
        have haddF := foldr_exprSize_add 1 fields 0
        rw [Nat.zero_add] at haddF
        omega
      have hrecSz :
          exprSize (recCall (.const w2.recRef lsR) pre
              (foldApps (.const w2.ctorRef lsC) fields)) =
            exprSize (foldApps (.const w2.recRef lsR)
              (pre ++ [foldApps (.const w2.ctorRef lsC) fields])) := by
        simp only [recCall]
      let ⟨preJ, hf1, hf2⟩ := parRedArgs_diamond E n hE
        (parRedArgs_refl (Γ := Γ) pre) hf hΓ1 hΓ2
      let ⟨fsJ, ha1, ha2⟩ := parRedArgs_diamond E n hE
        (parRedArgs_refl (Γ := Γ) fields) ha hΓ1 hΓ2
      have hpreLenJ : preJ.length = w2.preMajor.length := by
        have h1 := parRedArgs_length hf1
        have h0 := parRedArgs_length hf
        exact h1.symm.trans (h0.trans hpreLen)
      have hfieldsLenJ : fsJ.length =
          (w2.ctorParams ++ w2.fields).length := by
        have h1 := parRedArgs_length ha1
        have h0 := parRedArgs_length ha
        exact h1.symm.trans (h0.trans hfieldsLen)
      have ⟨hlsW0, hpreW0, hlsC0, hfsW0⟩ := iotaLhsOf_recCall_inj hlhs
      have hfW : ParRedArgs E n Γ2 w2.preMajor preJ := hpreW0 ▸ hf2
      have ⟨haW, hcW⟩ :=
        parRedArgs_ctor_split w2.hctorParams hfsW0 ha2
      let ⟨wJ, hlhsJ, hpreJeq, hfsJeq, hcJeq, hrecJ, hctorJ, hlsJeq, hlsCJeq⟩ :=
        parRedWitness hE w2 hfW haW hcW
      have hfsEq : fsJ.take w2.nparams ++ fsJ.drop w2.nparams = fsJ :=
        List.take_append_drop w2.nparams fsJ
      have hlhsJ' : iotaLhsOf wJ =
          recCall (.const wJ.recRef wJ.ls) preJ
            (foldApps (.const wJ.ctorRef wJ.lsC) fsJ) := by
        rw [hlhsJ, hrecJ, hctorJ, hlsJeq, hlsCJeq, hfsEq]
      have hpreLenW : preJ.length = wJ.preMajor.length := by
        rw [hpreJeq]
      have hfieldsLenW : fsJ.length =
          (wJ.ctorParams ++ wJ.fields).length := by
        rw [hcJeq, hfsJeq]
        exact congrArg List.length hfsEq.symm
      have hlsW : eqNList w2.ls wJ.ls :=
        eqNList_of_eq hlsJeq.symm
      have hsrcR :
          recCall (.const wJ.recRef lsR) pre
            (foldApps (.const wJ.ctorRef lsC) fields) =
          recCall (.const w2.recRef lsR) pre
            (foldApps (.const w2.ctorRef lsC) fields) := by
        simp only [recCall]
        rw [hrecJ, hctorJ]
      have hL : ParRed E n Γ1
          (recCall (.const w2.recRef lsR) pre
            (foldApps (.const w2.ctorRef lsC) fields))
          (iotaRhsOf wJ) :=
        Eq.rec (motive := fun t _ =>
            ParRed E n Γ1 t (iotaRhsOf wJ))
          (.iotaSpine Γ1 wJ lsR lsC
            (hlsJeq ▸ hlsR)
            (hlsCJeq ▸ hlsC)
            pre preJ fields fsJ hf1 ha1 hpreLenW hfieldsLenW hlhsJ')
          hsrcR
      exact ⟨iotaRhsOf wJ, hL,
        parRed_iotaRhs_to_cert hE hrecJ.symm hctorJ.symm hlsW
          (hpreJeq ▸ hfW) (hfsJeq ▸ haW)⟩
termination_by exprSize a + 1 + parRedW h2 + parRedCtxW hΓ1 + parRedCtxW hΓ2
decreasing_by
  all_goals simp_all [parRedW, parRedArgsW, parRedCtxW, exprSize]
  all_goals try (rw [hfold])
  all_goals try (rw [hfoldF])
  all_goals try (rw [hsnoc])
  all_goals try (rw [hadd1])
  all_goals try (rw [hadd2])
  all_goals try (rw [hpreW])
  all_goals try (rw [hfsW])
  all_goals try (rw [hseed])
  all_goals try (have := hpreLt)
  all_goals try (have := hfsLt)
  all_goals try (rw [hrecSz])
  all_goals try (rw [Nat.zero_add])
  all_goals try (have := parRedW_pos (by assumption))
  all_goals try (have := parRedArgsW_pos (by assumption))
  all_goals try (have := parRedCtxW_get?_let (by assumption) (by assumption))
  all_goals try (have := parRedCtx_drop_weight (i + 1) (by assumption))
  all_goals omega

noncomputable def parRed_diamond (E : ResolvedEnv) (n : Nat) (hE : EnvWf E n)
    {Γ Γ1 Γ2 : LCtx} {a b c : Expr Nat}
    (h1 : ParRed E n Γ a b) (h2 : ParRed E n Γ a c)
    (hΓ1 : ParRedCtx E n Γ Γ1) (hΓ2 : ParRedCtx E n Γ Γ2) :
    Σ' (d : Expr Nat), ParRed E n Γ1 b d ×' ParRed E n Γ2 c d :=
  match h1 with
  | .refl _ e =>
      parRed_diamond_from E n hE h2 hΓ1 hΓ2
  | .sortEq _ l₁ l₂ q => by
      have ⟨v1, e1, q1⟩ :=
        parRed_sort (E := E) (n := n) (Γ := Γ)
          (a := .sort l₁) (e := .sort l₂)
          (.sortEq Γ l₁ l₂ q) rfl
      have ⟨v2, e2, q2⟩ :=
        parRed_sort (E := E) (n := n) (Γ := Γ)
          (a := .sort l₁) h2 rfl
      injection e1 with hv1
      subst e2
      exact ⟨.sort l₂, .refl Γ1 _,
        .sortEq Γ2 v2 l₂ (eqN_trans (eqN_symm q2) (hv1 ▸ q1))⟩
  | .consts _ r ls ls1 q1 => by
      refine PSum.casesOn (parRed_const (a := .const r ls) h2 rfl)
        (fun p =>
          let ls2 := p.1
          let heq := p.2.1
          let q2 := p.2.2
          ⟨.const r ls1, .refl Γ1 _,
            heq ▸ .consts Γ2 r ls2 ls1 (eqNList_trans (eqNList_symm q2) q1)⟩)
        (fun p =>
          let m := p.1
          let body := p.2.1
          let hres := p.2.2.1
          let hbody := p.2.2.2.1
          let htr := p.2.2.2.2.1
          let heq := p.2.2.2.2.2
          -- 00 §20.6 R-1. Before the rule change both legs landed on the
          -- stored `body` and this one was `refl`. Now `h1` moved the
          -- const to `.const r ls1` and `h2` unfolded it at `ls`, so the
          -- apex is `instantiateLevels ls1 body`: `.delta` at `ls1` on
          -- the left, and ONE `parRedInstantiateLevels` step at
          -- `q1 : eqNList ls ls1` on the right.
          ⟨instantiateLevels ls1 body, .delta Γ1 r ls1 m body hres hbody htr,
            heq ▸ parRedInstantiateLevels (E := E) (n := n) body q1 Γ2⟩)
  | .delta _ r ls m b hres hbody htr => by
      refine PSum.casesOn (parRed_const (a := .const r ls) h2 rfl)
        (fun p => by
          let ls2 := p.1
          let heq := p.2.1
          let q2 := p.2.2
          -- 00 §20.6 R-1, mirror of the `consts × delta` case. `h1`
          -- unfolded at `ls`, `h2` drifted the levels to `ls2`; the apex
          -- is `instantiateLevels ls2 b`, one `parRedInstantiateLevels`
          -- step at `q2 : eqNList ls ls2` from the left leg.
          exact ⟨instantiateLevels ls2 b,
            parRedInstantiateLevels (E := E) (n := n) b q2 Γ1,
            heq ▸ .delta Γ2 r ls2 m b hres hbody htr⟩)
        (fun p => by
          let m2 := p.1
          let body2 := p.2.1
          let hres2 := p.2.2.1
          let hbody2 := p.2.2.2.1
          let heq := p.2.2.2.2.2
          have hm : m2 = m := Option.some.inj (hres2.symm.trans hres)
          have hbody2' : m.body = some body2 :=
            Eq.rec (motive := fun m' _ => m'.body = some body2) hbody2 hm
          have hbod : body2 = b :=
            Option.some.inj (hbody2'.symm.trans hbody)
          exact ⟨instantiateLevels ls b, .refl Γ1 _,
            heq ▸ hbod ▸ .refl Γ2 _⟩)
  | .bvarZeta _ i A v v1 hlk hv1 => by
      match hbvar : parRed_bvar h2 rfl with
      | .inl heq =>
          -- zeta-vs-refl: IH on (h1's `v ⇒ v1`, ctx's `v ⇒ v2`).
          -- Γ2 still zetas; v2 is the stored value, not a subderivation
          -- of h2 (h2 is refl).
          let g1 := parRedCtx_get?_let hΓ1 hlk
          let g2 := parRedCtx_get?_let hΓ2 hlk
          let A1 := g1.1
          let vs1 := g1.2.1
          let hg1 := g1.2.2.1
          let A2 := g2.1
          let vs2 := g2.2.1
          let hg2 := g2.2.2.1
          let hv2c := g2.2.2.2.1
          have hpay1 := parRedCtxW_get?_let hΓ1 hlk
          have hpay2 := parRedCtxW_get?_let hΓ2 hlk
          have ⟨vstar, hd1, hd2⟩ := parRed_diamond E n hE hv1 hv2c
            (parRedCtx_drop (i + 1) hΓ1) (parRedCtx_drop (i + 1) hΓ2)
          have hpre1 : Γ1.take (i + 1) ++ Γ1.drop (i + 1) = Γ1 :=
            List.take_append_drop (i + 1) Γ1
          have hlen1 : (Γ1.take (i + 1)).length = i + 1 :=
            List.length_take_of_le (Nat.succ_le_of_lt (get?_some_lt hg1))
          have hL := parRed_weaken_lctx hE (Γ1.take (i + 1)) hd1
          rw [hlen1] at hL
          exact joinCast heq.symm
            ⟨lift 0 (i + 1) vstar, hpre1 ▸ hL,
              .bvarZeta Γ2 i A2 vs2 vstar hg2 hd2⟩
      | .inr p =>
          let A2 := p.1
          let v2 := p.2.1
          let v2' := p.2.2.1
          let hlk2 := p.2.2.2.1
          let hv2 := p.2.2.2.2.1
          let heq := p.2.2.2.2.2
          have hWζ := parRedW_of_bvarZeta h2 rfl p hbvar
          have := hWζ
          have hv : v2 = v :=
            (LocalDecl.letBinding.inj
              (Option.some.inj (hlk2.symm.trans hlk))).2
          let hv2' : ParRed E n (Γ.drop (i + 1)) v v2' :=
            Eq.rec (motive := fun t _ =>
                ParRed E n (Γ.drop (i + 1)) t v2') hv2 hv
          have := Nat.le_trans
            (Nat.le_of_eq (parRedW_eq_rec hv p.2.2.2.2.1)) hWζ
          have := parRedCtx_drop_weight (i + 1) hΓ1
          have := parRedCtx_drop_weight (i + 1) hΓ2
          have := parRedCtxW_get?_let hΓ2 hlk2
          have ⟨d, hd1, hd2⟩ := parRed_diamond E n hE hv1
            (Eq.rec (motive := fun t _ =>
                ParRed E n (Γ.drop (i + 1)) t v2') p.2.2.2.2.1 hv)
            (parRedCtx_drop (i + 1) hΓ1) (parRedCtx_drop (i + 1) hΓ2)
          let g1 := parRedCtx_get?_let hΓ1 hlk
          let g2 := parRedCtx_get?_let hΓ2 hlk
          let A1 := g1.1
          let vs1 := g1.2.1
          let hg1 := g1.2.2.1
          let A2' := g2.1
          let vs2 := g2.2.1
          let hg2 := g2.2.2.1
          have hpay1 := parRedCtxW_get?_let hΓ1 hlk
          have hpay2 := parRedCtxW_get?_let hΓ2 hlk
          have hpre1 : Γ1.take (i + 1) ++ Γ1.drop (i + 1) = Γ1 :=
            List.take_append_drop (i + 1) Γ1
          have hpre2 : Γ2.take (i + 1) ++ Γ2.drop (i + 1) = Γ2 :=
            List.take_append_drop (i + 1) Γ2
          have hlen1 : (Γ1.take (i + 1)).length = i + 1 :=
            List.length_take_of_le (Nat.succ_le_of_lt (get?_some_lt hg1))
          have hlen2 : (Γ2.take (i + 1)).length = i + 1 :=
            List.length_take_of_le (Nat.succ_le_of_lt (get?_some_lt hg2))
          have hL := parRed_weaken_lctx hE (Γ1.take (i + 1)) hd1
          have hR := parRed_weaken_lctx hE (Γ2.take (i + 1)) hd2
          rw [hlen1] at hL
          rw [hlen2] at hR
          exact joinCast heq.symm
            ⟨lift 0 (i + 1) d, hpre1 ▸ hL, hpre2 ▸ hR⟩
  | .lit _ t => by
      refine PSum.casesOn (parRed_lit h2 rfl)
        (fun heq =>
          ⟨natExpand t, .refl Γ1 _, heq ▸ .lit Γ2 t⟩)
        (fun heq =>
          ⟨natExpand t, .refl Γ1 _, heq ▸ .refl Γ2 _⟩)
  | .lam _ A A1 b b1 hA1 hb1 => by
      let inv := parRed_lam h2 rfl
      have hW := parRedW_of_lam h2 rfl
      have := hW.1
      have := hW.2
      let A2 := inv.1
      let b2 := inv.2.1
      let heq := inv.2.2.1
      let hA2 := inv.2.2.2.1
      let hb2 := inv.2.2.2.2
      have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 hA2 hΓ1 hΓ2
      have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 hb2
        (.assumption hA1 hΓ1) (.assumption hA2 hΓ2)
      exact ⟨.lam Aj bj,
        .lam Γ1 A1 Aj b1 bj hAj1 hbj1,
        heq ▸ .lam Γ2 A2 Aj b2 bj hAj2 hbj2⟩
  | .pi _ A A1 B B1 hA1 hB1 => by
      let inv := parRed_pi h2 rfl
      have hW := parRedW_of_pi h2 rfl
      have := hW.1
      have := hW.2
      let A2 := inv.1
      let B2 := inv.2.1
      let heq := inv.2.2.1
      let hA2 := inv.2.2.2.1
      let hB2 := inv.2.2.2.2
      have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 hA2 hΓ1 hΓ2
      have ⟨Bj, hBj1, hBj2⟩ := parRed_diamond E n hE hB1 hB2
        (.assumption hA1 hΓ1) (.assumption hA2 hΓ2)
      exact ⟨.pi Aj Bj,
        .pi Γ1 A1 Aj B1 Bj hAj1 hBj1,
        heq ▸ .pi Γ2 A2 Aj B2 Bj hAj2 hBj2⟩
  | .app _ f f1 x x1 hf1 ha1 => by
      match happ : parRed_appW h2 rfl with
      | .inl p =>
          let f2 := p.1
          let x2 := p.2.1
          let heq := p.2.2.1
          let hf2 := p.2.2.2.1
          let ha2 := p.2.2.2.2.1
          have := p.2.2.2.2.2.1
          have := p.2.2.2.2.2.2
          have ⟨fj, hf1j, hf2j⟩ := parRed_diamond E n hE hf1 hf2 hΓ1 hΓ2
          have ⟨xj, ha1j, ha2j⟩ := parRed_diamond E n hE ha1 ha2 hΓ1 hΓ2
          exact ⟨.app fj xj,
            .app Γ1 f1 fj x1 xj hf1j ha1j,
            heq ▸ .app Γ2 f2 fj x2 xj hf2j ha2j⟩
      | .inr rest =>
          match hrest : rest with
          | .inl p =>
              let A := p.1
              let body := p.2.1
              let A2 := p.2.2.1
              let body2 := p.2.2.2.1
              let arg2 := p.2.2.2.2.1
              let hflam := p.2.2.2.2.2.1
              let hA2 := p.2.2.2.2.2.2.1
              let hb2 := p.2.2.2.2.2.2.2.1
              let ha2 := p.2.2.2.2.2.2.2.2.1
              let heq := p.2.2.2.2.2.2.2.2.2.1
              have := p.2.2.2.2.2.2.2.2.2.2.1
              have := p.2.2.2.2.2.2.2.2.2.2.2.1
              have := p.2.2.2.2.2.2.2.2.2.2.2.2
              have := parRedW_eq_rec hflam hf1
              have hWlam := parRedW_of_lam
                (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hflam) rfl
              have := Nat.le_trans hWlam.1
                (Nat.le_of_eq (parRedW_eq_rec hflam hf1))
              have := Nat.le_trans hWlam.2
                (Nat.le_of_eq (parRedW_eq_rec hflam hf1))
              let inv1 := parRed_lam
                (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hflam) rfl
              let A1 := inv1.1
              let b1 := inv1.2.1
              let hf1eq := inv1.2.2.1
              have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE
                (parRed_lam
                  (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hflam)
                  rfl).2.2.2.1
                p.2.2.2.2.2.2.1 hΓ1 hΓ2
              have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE
                (parRed_lam
                  (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hflam)
                  rfl).2.2.2.2
                p.2.2.2.2.2.2.2.1
                (.assumption
                  (parRed_lam
                    (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hflam)
                    rfl).2.2.2.1 hΓ1)
                (.assumption p.2.2.2.2.2.2.1 hΓ2)
              have ⟨xj, hx1j, hx2j⟩ := parRed_diamond E n hE
                ha1 p.2.2.2.2.2.2.2.2.1 hΓ1 hΓ2
              exact ⟨instantiate0 xj bj,
                hf1eq ▸ .beta Γ1 A1 Aj b1 bj x1 xj hAj1 hbj1 hx1j,
                heq ▸ parRed_instantiate_both_assump hE hx2j hbj2⟩
          | .inr p =>
                  let pre := p.1
                  let pre' := p.2.1
                  let fields := p.2.2.1
                  let fields' := p.2.2.2.1
                  let hf := p.2.2.2.2.1
                  let ha := p.2.2.2.2.2.1
                  have := p.2.2.2.2.2.2.1.1
                  have := p.2.2.2.2.2.2.1.2
                  let w := p.2.2.2.2.2.2.2.1
                  let lsR := p.2.2.2.2.2.2.2.2.1
                  let lsC := p.2.2.2.2.2.2.2.2.2.1
                  let hlsR := p.2.2.2.2.2.2.2.2.2.2.1
                  let hlsC := p.2.2.2.2.2.2.2.2.2.2.2.1
                  let hpreLen := p.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let hfieldsLen := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let hlhs := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let hsrc := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let heq := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have happ := foldApps_snoc (.const w.recRef lsR)
                    (foldApps (.const w.ctorRef lsC) fields) pre
                  have hfx :
                      (foldApps (.const w.recRef lsR) pre).app
                        (foldApps (.const w.ctorRef lsC) fields) =
                      f.app x := happ.symm.trans hsrc
                  injection hfx with hf_eq hx_eq
                  let hf1' : ParRed E n Γ
                      (foldApps (.const w.recRef lsR) pre) f1 :=
                    Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hf_eq.symm
                  let ha1' : ParRed E n Γ
                      (foldApps (.const w.ctorRef lsC) fields) x1 :=
                    Eq.rec (motive := fun t _ => ParRed E n Γ t x1) ha1 hx_eq.symm
                  have hlen_pre : pre.length < piCount w.recMember.mtype := by
                    have := parRedArgs_length hf
                    rw [this, hpreLen, w.hpre, ← w.hnmin]; omega
                  let ⟨ls2, pre2, heq2, q2, hargs2, hWargs⟩ :=
                    parRed_foldApps_recursor_short
                      (Eq.rec (motive := fun t _ => ParRed E n Γ t f1) hf1 hf_eq.symm)
                      w.hrec w.hrecK pre rfl hlen_pre
                  let ⟨lsC2, fs2, heqc, qc, hfs2, hWfs⟩ :=
                    parRed_foldApps_constructor w.hctor w.hctorK
                      (Eq.rec (motive := fun t _ => ParRed E n Γ t x1) ha1 hx_eq.symm)
                      fields rfl
                  have := Nat.le_trans hWargs
                    (Nat.le_of_eq (parRedW_eq_rec hf_eq.symm hf1))
                  have := Nat.le_trans hWfs
                    (Nat.le_of_eq (parRedW_eq_rec hx_eq.symm ha1))
                  have ⟨preJ, hfJ1, hfJ2⟩ := parRedArgs_diamond E n hE hargs2
                    p.2.2.2.2.1 hΓ1 hΓ2
                  have ⟨fsJ, haJ1, haJ2⟩ := parRedArgs_diamond E n hE hfs2
                    p.2.2.2.2.2.1 hΓ1 hΓ2
                  have ⟨_, hpreW0, _, hfsW0⟩ := iotaLhsOf_recCall_inj hlhs
                  have hfW : ParRedArgs E n Γ2 w.preMajor preJ :=
                    hpreW0 ▸ hfJ2
                  have ⟨haW, hcW⟩ :=
                    parRedArgs_ctor_split w.hctorParams hfsW0 haJ2
                  let ⟨wJ, hlhsJ, hpreJeq, hfsJeq, hcJeq,
                      hrecJ, hctorJ, hlsJeq, hlsCJeq⟩ :=
                    parRedWitness hE w hfW haW hcW
                  have hfsEq :
                      fsJ.take w.nparams ++ fsJ.drop w.nparams = fsJ :=
                    List.take_append_drop w.nparams fsJ
                  have hlhsJ' : iotaLhsOf wJ =
                      recCall (.const wJ.recRef wJ.ls) preJ
                        (foldApps (.const wJ.ctorRef wJ.lsC) fsJ) := by
                    rw [hlhsJ, hrecJ, hctorJ, hlsJeq, hlsCJeq, hfsEq]
                  have hpreLenW : preJ.length = wJ.preMajor.length := by
                    rw [hpreJeq]
                  have hfieldsLenW : fsJ.length =
                      (wJ.ctorParams ++ wJ.fields).length := by
                    rw [hcJeq, hfsJeq]
                    exact congrArg List.length hfsEq.symm
                  have hlsRp : eqNList w.ls lsR := hlsR
                  have hlsCp : eqNList w.lsC lsC := hlsC
                  have hlsW : eqNList w.ls wJ.ls :=
                    eqNList_of_eq hlsJeq.symm
                  have hcongr' :=
                    parRed_iotaRhs_to_cert hE hrecJ.symm hctorJ.symm hlsW
                      (hpreJeq ▸ hfW) (hfsJeq ▸ haW)
                  have hRsp : ParRed E n Γ1
                      (recCall (.const wJ.recRef ls2) pre2
                        (foldApps (.const wJ.ctorRef lsC2) fs2))
                      (iotaRhsOf wJ) :=
                    .iotaSpine Γ1 wJ ls2 lsC2
                      (hlsJeq ▸ eqNList_trans hlsRp q2)
                      (hlsCJeq ▸ eqNList_trans hlsCp qc)
                      pre2 preJ fs2 fsJ hfJ1 haJ1
                      hpreLenW hfieldsLenW hlhsJ'
                  have hsrcR :
                      recCall (.const wJ.recRef ls2) pre2
                        (foldApps (.const wJ.ctorRef lsC2) fs2) =
                      recCall (.const w.recRef ls2) pre2
                        (foldApps (.const w.ctorRef lsC2) fs2) := by
                    simp only [recCall]
                    rw [hrecJ, hctorJ]
                  have hsrc_app :
                      recCall (.const w.recRef ls2) pre2
                        (foldApps (.const w.ctorRef lsC2) fs2) =
                      f1.app x1 := by
                    have heq2' : f1 =
                        foldApps (.const w.recRef ls2) pre2 := heq2
                    have heqc' : x1 =
                        foldApps (.const w.ctorRef lsC2) fs2 := heqc
                    simp only [recCall]
                    rw [foldApps_snoc, heq2', heqc']
                  have hRapp : ParRed E n Γ1 (f1.app x1) (iotaRhsOf wJ) :=
                    Eq.rec (motive := fun t _ =>
                        ParRed E n Γ1 t (iotaRhsOf wJ))
                      (Eq.rec (motive := fun t _ =>
                          ParRed E n Γ1 t (iotaRhsOf wJ))
                        hRsp hsrcR) hsrc_app
                  exact joinCast heq.symm ⟨iotaRhsOf wJ, hRapp, hcongr'⟩
  | .beta _ A A1 body body1 arg arg1 hA1 hb1 ha1 => by
      match hlamapp : parRed_lam_app h2 rfl with
      | .inl p =>
          let A2 := p.1
          let b2 := p.2.1
          let x2 := p.2.2.1
          let heq := p.2.2.2.1
          let hA2 := p.2.2.2.2.1
          let hb2 := p.2.2.2.2.2.1
          let hx2 := p.2.2.2.2.2.2
          have hW := parRedW_of_lam_app_congr h2 rfl p hlamapp
          have := hW.1
          have := hW.2.1
          have := hW.2.2
          have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 hA2 hΓ1 hΓ2
          have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 hb2
            (.assumption hA1 hΓ1) (.assumption hA2 hΓ2)
          have ⟨xj, hx1j, hx2j⟩ := parRed_diamond E n hE ha1 hx2 hΓ1 hΓ2
          exact ⟨instantiate0 xj bj,
            parRed_instantiate_both_assump hE hx1j hbj1,
            heq ▸ .beta Γ2 A2 Aj b2 bj x2 xj hAj2 hbj2 hx2j⟩
      | .inr p =>
          let A2 := p.1
          let b2 := p.2.1
          let x2 := p.2.2.1
          let hA2 := p.2.2.2.1
          let hb2 := p.2.2.2.2.1
          let hx2 := p.2.2.2.2.2.1
          let heq := p.2.2.2.2.2.2
          have hW := parRedW_of_lam_app_beta h2 rfl p hlamapp
          have := hW.1
          have := hW.2.1
          have := hW.2.2
          have ⟨_Aj, _hAj1, _hAj2⟩ := parRed_diamond E n hE hA1 hA2 hΓ1 hΓ2
          have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 hb2
            (.assumption hA1 hΓ1) (.assumption hA2 hΓ2)
          have ⟨xj, hx1j, hx2j⟩ := parRed_diamond E n hE ha1 hx2 hΓ1 hΓ2
          exact ⟨instantiate0 xj bj,
            parRed_instantiate_both_assump hE hx1j hbj1,
            heq ▸ parRed_instantiate_both_assump hE hx2j hbj2⟩
  | .iotaSpine _ w lsR lsC hlsR hlsC pre pre' fields fields'
        hf1 ha1 hpreLen hfieldsLen hlhs => by
      have happ := foldApps_snoc (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre
      have h2eq : recCall (.const w.recRef lsR) pre
          (foldApps (.const w.ctorRef lsC) fields) =
          (foldApps (.const w.recRef lsR) pre).app
            (foldApps (.const w.ctorRef lsC) fields) := by
        simp only [recCall]; exact happ
      let h2' : ParRed E n Γ
          ((foldApps (.const w.recRef lsR) pre).app
            (foldApps (.const w.ctorRef lsC) fields)) c :=
        Eq.rec (motive := fun t _ => ParRed E n Γ t c) h2 h2eq
      have := parRedW_eq_rec h2eq h2
      have h2'le : parRedW h2' ≤ parRedW h2 :=
        Nat.le_of_eq ((rfl : parRedW h2' =
            parRedW (Eq.rec (motive := fun t _ => ParRed E n Γ t c) h2 h2eq)).trans
          (parRedW_eq_rec h2eq h2))
      match happ2 : parRed_appW h2' rfl with
      | .inl p =>
          let f2 := p.1
          let x2 := p.2.1
          let heq := p.2.2.1
          let hf2 := p.2.2.2.1
          let ha2 := p.2.2.2.2.1
          have := p.2.2.2.2.2.1
          have := p.2.2.2.2.2.2
          have hf2le : parRedW hf2 ≤ parRedW h2 :=
            Nat.le_trans (Nat.le_of_eq (rfl : parRedW hf2 = parRedW p.2.2.2.1))
              (Nat.le_trans p.2.2.2.2.2.1 h2'le)
          have ha2le : parRedW ha2 ≤ parRedW h2 :=
            Nat.le_trans (Nat.le_of_eq (rfl : parRedW ha2 = parRedW p.2.2.2.2.1))
              (Nat.le_trans p.2.2.2.2.2.2 h2'le)
          have hlen_pre : pre.length < piCount w.recMember.mtype := by
            have := parRedArgs_length hf1
            rw [this, hpreLen, w.hpre, ← w.hnmin]; omega
          have inv2 :=
            parRed_foldApps_recursor_short hf2 w.hrec w.hrecK
              pre rfl hlen_pre
          let ⟨ls2, pre2, heq2, q2, hargs2, hWargs⟩ := inv2
          have invc :=
            parRed_foldApps_constructor w.hctor w.hctorK ha2 fields rfl
          let ⟨lsC2, fs2, heqc, qc, hfs2, hWfs⟩ := invc
          have := hWargs
          have := hWfs
          have := Nat.le_trans hWargs hf2le
          have := Nat.le_trans hWfs ha2le
          have ⟨preJ, hfJ1, hfJ2⟩ := parRedArgs_diamond E n hE hf1 hargs2 hΓ1 hΓ2
          have ⟨fsJ, haJ1, haJ2⟩ := parRedArgs_diamond E n hE ha1 hfs2 hΓ1 hΓ2
          have ⟨_, hpreW0, _, hfsW0⟩ := iotaLhsOf_recCall_inj hlhs
          have hfW : ParRedArgs E n Γ1 w.preMajor preJ :=
            hpreW0 ▸ hfJ1
          have ⟨haW, hcW⟩ :=
            parRedArgs_ctor_split w.hctorParams hfsW0 haJ1
          let ⟨wJ, hlhsJ, hpreJeq, hfsJeq, hcJeq,
              hrecJ, hctorJ, hlsJeq, hlsCJeq⟩ :=
            parRedWitness hE w hfW haW hcW
          have hfsEq :
              fsJ.take w.nparams ++ fsJ.drop w.nparams = fsJ :=
            List.take_append_drop w.nparams fsJ
          have hlhsJ' : iotaLhsOf wJ =
              recCall (.const wJ.recRef wJ.ls) preJ
                (foldApps (.const wJ.ctorRef wJ.lsC) fsJ) := by
            rw [hlhsJ, hrecJ, hctorJ, hlsJeq, hlsCJeq, hfsEq]
          have hpreLenW : preJ.length = wJ.preMajor.length := by
            rw [hpreJeq]
          have hfieldsLenW : fsJ.length =
              (wJ.ctorParams ++ wJ.fields).length := by
            rw [hcJeq, hfsJeq]
            exact congrArg List.length hfsEq.symm
          have hlsW : eqNList w.ls wJ.ls :=
            eqNList_of_eq hlsJeq.symm
          have hcongr' :=
            parRed_iotaRhs_to_cert hE hrecJ.symm hctorJ.symm hlsW
              (hpreJeq ▸ hfW) (hfsJeq ▸ haW)
          have hRsp : ParRed E n Γ2
              (recCall (.const wJ.recRef ls2) pre2
                (foldApps (.const wJ.ctorRef lsC2) fs2))
              (iotaRhsOf wJ) :=
            .iotaSpine Γ2 wJ ls2 lsC2
              (hlsJeq ▸ eqNList_trans hlsR q2)
              (hlsCJeq ▸ eqNList_trans hlsC qc)
              pre2 preJ fs2 fsJ hfJ2 haJ2
              hpreLenW hfieldsLenW hlhsJ'
          have hsrcR :
              recCall (.const wJ.recRef ls2) pre2
                (foldApps (.const wJ.ctorRef lsC2) fs2) =
              recCall (.const w.recRef ls2) pre2
                (foldApps (.const w.ctorRef lsC2) fs2) := by
            simp only [recCall]
            rw [hrecJ, hctorJ]
          have hsrc_app :
              recCall (.const w.recRef ls2) pre2
                (foldApps (.const w.ctorRef lsC2) fs2) =
              f2.app x2 := by
            have heq2' : f2 =
                foldApps (.const w.recRef ls2) pre2 := heq2
            have heqc' : x2 =
                foldApps (.const w.ctorRef lsC2) fs2 := heqc
            simp only [recCall]
            rw [foldApps_snoc, heq2', heqc']
          have hRapp : ParRed E n Γ2 (f2.app x2) (iotaRhsOf wJ) :=
            Eq.rec (motive := fun t _ =>
                ParRed E n Γ2 t (iotaRhsOf wJ))
              (Eq.rec (motive := fun t _ =>
                  ParRed E n Γ2 t (iotaRhsOf wJ))
                hRsp hsrcR) hsrc_app
          exact joinCast heq.symm ⟨iotaRhsOf wJ, hcongr', hRapp⟩
      | .inr rest =>
          match hrest : rest with
          | .inl p =>
              exact (foldApps_const_ne_lam pre p.2.2.2.2.2.1).elim
          | .inr p =>
                  let pre0s := p.1
                  let pre0' := p.2.1
                  let fields0 := p.2.2.1
                  let fields0' := p.2.2.2.1
                  let hf0 := p.2.2.2.2.1
                  let ha0 := p.2.2.2.2.2.1
                  have := p.2.2.2.2.2.2.1.1
                  have := p.2.2.2.2.2.2.1.2
                  let w0 := p.2.2.2.2.2.2.2.1
                  let lsR0 := p.2.2.2.2.2.2.2.2.1
                  let lsC0 := p.2.2.2.2.2.2.2.2.2.1
                  let hlsR0 := p.2.2.2.2.2.2.2.2.2.2.1
                  let hlhs0 := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let hsrc0 := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  let heq := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have happS := foldApps_snoc (.const w.recRef lsR)
                    (foldApps (.const w.ctorRef lsC) fields) pre
                  have hsrcEq :
                      recCall (.const w0.recRef lsR0) pre0s
                        (foldApps (.const w0.ctorRef lsC0) fields0) =
                      recCall (.const w.recRef lsR) pre
                        (foldApps (.const w.ctorRef lsC) fields) := by
                    simp only [recCall]
                    exact hsrc0.trans happS.symm
                  have hpre0s : pre0s = pre := by
                    have hs := congrArg appsSpine hsrcEq
                    rw [appsSpine_recCall, appsSpine_recCall] at hs
                    injection hs with _hhead hsp
                    exact (list_snoc_inj hsp).1
                  have hfs0s : fields0 = fields := by
                    have hs := congrArg appsSpine hsrcEq
                    rw [appsSpine_recCall, appsSpine_recCall] at hs
                    injection hs with _hhead hsp
                    have hmaj := (list_snoc_inj hsp).2
                    have hs2 := congrArg appsSpine hmaj
                    rw [appsSpine_foldApps, appsSpine_const, List.nil_append,
                      appsSpine_foldApps, appsSpine_const, List.nil_append]
                      at hs2
                    injection hs2 with _hhead2 hfields
                    try exact hfields
                  have := parRedArgsW_eq_rec hpre0s p.2.2.2.2.1
                  have := parRedArgsW_eq_rec hfs0s p.2.2.2.2.2.1
                  have := Nat.le_trans
                    (Nat.le_of_eq (parRedArgsW_eq_rec hpre0s p.2.2.2.2.1))
                    (Nat.le_trans p.2.2.2.2.2.2.1.1 h2'le)
                  have := Nat.le_trans
                    (Nat.le_of_eq (parRedArgsW_eq_rec hfs0s p.2.2.2.2.2.1))
                    (Nat.le_trans p.2.2.2.2.2.2.1.2 h2'le)
                  have ⟨preJ, hfJ1, hfJ2⟩ := parRedArgs_diamond E n hE hf1
                    (Eq.rec (motive := fun t _ =>
                        ParRedArgs E n Γ t pre0') p.2.2.2.2.1 hpre0s)
                    hΓ1 hΓ2
                  have ⟨fsJ, haJ1, haJ2⟩ := parRedArgs_diamond E n hE ha1
                    (Eq.rec (motive := fun t _ =>
                        ParRedArgs E n Γ t fields0') p.2.2.2.2.2.1 hfs0s)
                    hΓ1 hΓ2
                  have ⟨hlsW0, hpreW, _, hfsW⟩ := iotaLhsOf_recCall_inj hlhs
                  have ⟨hls00, hpre0, _, hfs0⟩ := iotaLhsOf_recCall_inj hlhs0
                  have hfWL : ParRedArgs E n Γ1 w.preMajor preJ :=
                    hpreW ▸ hfJ1
                  have ⟨haWL, hcWL⟩ :=
                    parRedArgs_ctor_split w.hctorParams hfsW haJ1
                  have href0w : w0.recRef = w.recRef :=
                    (Expr.const.inj (Prod.mk.inj (by
                      have hs := congrArg appsSpine hsrcEq
                      rw [appsSpine_recCall, appsSpine_recCall] at hs
                      exact hs)).1).1
                  have hlsR0 : lsR0 = lsR :=
                    (Expr.const.inj (Prod.mk.inj (by
                      have hs := congrArg appsSpine hsrcEq
                      rw [appsSpine_recCall, appsSpine_recCall] at hs
                      exact hs)).1).2
                  have hctor0w : w0.ctorRef = w.ctorRef := by
                    have hs := congrArg appsSpine hsrcEq
                    rw [appsSpine_recCall, appsSpine_recCall] at hs
                    have hmaj := (list_snoc_inj (Prod.mk.inj hs).2).2
                    have hs2 := congrArg appsSpine hmaj
                    rw [appsSpine_foldApps, appsSpine_const, List.nil_append,
                      appsSpine_foldApps, appsSpine_const, List.nil_append]
                      at hs2
                    exact (Expr.const.inj (Prod.mk.inj hs2).1).1
                  have hlenW0 : w.preMajor.length = w0.preMajor.length := by
                    have h1 := parRedArgs_length hf1
                    have h2 := parRedArgs_length
                      (Eq.rec (motive := fun t _ =>
                          ParRedArgs E n Γ t pre0') p.2.2.2.2.1 hpre0s)
                    rw [hpreW, hpre0, ← h1, ← h2]
                  have ⟨_, _, _, _, _, hnpar, _, _⟩ :=
                    iotaWitness_env_of_same_refs href0w.symm hctor0w.symm
                      hlenW0
                  let ⟨wJ, hlhsJ, hpreJeq, hfsJeq, hcJeq,
                      hrecJ, hctorJ, hlsJeq, hlsCJeq⟩ :=
                    parRedWitness hE w hfWL haWL hcWL
                  have hL :=
                    parRed_iotaRhs_to_cert hE hrecJ.symm hctorJ.symm
                      (eqNList_of_eq hlsJeq.symm)
                      (hpreJeq ▸ hfWL) (hfsJeq ▸ haWL)
                  have hfWR : ParRedArgs E n Γ2 w0.preMajor preJ :=
                    hpre0 ▸ hfJ2
                  have ⟨haWR, _hcWR⟩ :=
                    parRedArgs_ctor_split w0.hctorParams hfs0 haJ2
                  have haWR' : ParRedArgs E n Γ2 w0.fields
                      (fsJ.drop w.nparams) := hnpar ▸ haWR
                  have hlsR0p : eqNList w0.ls lsR0 :=
                    p.2.2.2.2.2.2.2.2.2.2.1
                  have hR :=
                    parRed_iotaRhs_to_cert hE
                      (href0w.trans hrecJ.symm)
                      (hctor0w.trans hctorJ.symm)
                      (hlsJeq ▸ eqNList_trans hlsR0p
                        (eqNList_trans (eqNList_of_eq hlsR0)
                          (eqNList_symm hlsR)))
                      (hpreJeq ▸ hfWR) (hfsJeq ▸ haWR')
                  exact joinCast heq.symm ⟨iotaRhsOf wJ, hL, hR⟩
  | .letE _ A A1 v v1 b b1 hA1 hv1 hb1 => by
      match hlet : parRed_letE h2 rfl with
      | .inl p =>
        have hW := parRedW_of_letE_congr h2 rfl p hlet
        have := hW.1
        have := hW.2.1
        have := hW.2.2.1
        have := hW.2.2.2
        let A2 := p.1
        let v2 := p.2.1
        let b2 := p.2.2.1
        let heq := p.2.2.2.1
        let hA2 := p.2.2.2.2.1
        let hv2 := p.2.2.2.2.2.1
        let hb2 := p.2.2.2.2.2.2
        have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 p.2.2.2.2.1 hΓ1 hΓ2
        have ⟨vj, hv1j, hv2j⟩ := parRed_diamond E n hE hv1 p.2.2.2.2.2.1 hΓ1 hΓ2
        have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 p.2.2.2.2.2.2
          (.letBinding hA1 hv1 hΓ1)
          (.letBinding p.2.2.2.2.1 p.2.2.2.2.2.1 hΓ2)
        exact ⟨.letE Aj vj bj,
          .letE Γ1 A1 Aj v1 vj b1 bj hAj1 hv1j hbj1,
          heq ▸ .letE Γ2 A2 Aj v2 vj b2 bj hAj2 hv2j hbj2⟩
      | .inr p =>
        let A2 := p.1
        let v2 := p.2.1
        let b2 := p.2.2.1
        let hA2 := p.2.2.2.1
        let hv2 := p.2.2.2.2.1
        let hb2 := p.2.2.2.2.2.1
        let heq := p.2.2.2.2.2.2
        have hWz := parRedW_of_letE_zeta h2 rfl p hlet
        have := hWz.1
        have := hWz.2.1
        have := hWz.2.2.1
        have := hWz.2.2.2
        have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 p.2.2.2.1 hΓ1 hΓ2
        have ⟨vj, hv1j, hv2j⟩ := parRed_diamond E n hE hv1 p.2.2.2.2.1 hΓ1 hΓ2
        have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 p.2.2.2.2.2.1
          (.letBinding hA1 hv1 hΓ1)
          (.letBinding p.2.2.2.1 p.2.2.2.2.1 hΓ2)
        exact ⟨instantiate0 vj bj,
          .zeta Γ1 A1 Aj v1 vj b1 bj hAj1 hv1j hbj1,
          heq ▸ parRed_instantiate_both_let hE hv2j hbj2⟩
  | .zeta _ A A1 v v1 b b1 hA1 hv1 hb1 => by
      match hlet : parRed_letE h2 rfl with
      | .inl p =>
        have hW := parRedW_of_letE_congr h2 rfl p hlet
        have := hW.1
        have := hW.2.1
        have := hW.2.2.1
        have := hW.2.2.2
        let A2 := p.1
        let v2 := p.2.1
        let b2 := p.2.2.1
        let heq := p.2.2.2.1
        let hA2 := p.2.2.2.2.1
        let hv2 := p.2.2.2.2.2.1
        let hb2 := p.2.2.2.2.2.2
        have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 p.2.2.2.2.1 hΓ1 hΓ2
        have ⟨vj, hv1j, hv2j⟩ := parRed_diamond E n hE hv1 p.2.2.2.2.2.1 hΓ1 hΓ2
        have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 p.2.2.2.2.2.2
          (.letBinding hA1 hv1 hΓ1)
          (.letBinding p.2.2.2.2.1 p.2.2.2.2.2.1 hΓ2)
        exact ⟨instantiate0 vj bj,
          parRed_instantiate_both_let hE hv1j hbj1,
          heq ▸ .zeta Γ2 A2 Aj v2 vj b2 bj hAj2 hv2j hbj2⟩
      | .inr p =>
        let A2 := p.1
        let v2 := p.2.1
        let b2 := p.2.2.1
        let hA2 := p.2.2.2.1
        let hv2 := p.2.2.2.2.1
        let hb2 := p.2.2.2.2.2.1
        let heq := p.2.2.2.2.2.2
        have hWz := parRedW_of_letE_zeta h2 rfl p hlet
        have := hWz.1
        have := hWz.2.1
        have := hWz.2.2.1
        have := hWz.2.2.2
        have ⟨Aj, hAj1, hAj2⟩ := parRed_diamond E n hE hA1 p.2.2.2.1 hΓ1 hΓ2
        have ⟨vj, hv1j, hv2j⟩ := parRed_diamond E n hE hv1 p.2.2.2.2.1 hΓ1 hΓ2
        have ⟨bj, hbj1, hbj2⟩ := parRed_diamond E n hE hb1 p.2.2.2.2.2.1
          (.letBinding hA1 hv1 hΓ1)
          (.letBinding p.2.2.2.1 p.2.2.2.2.1 hΓ2)
        exact ⟨instantiate0 vj bj,
          parRed_instantiate_both_let hE hv1j hbj1,
          heq ▸ parRed_instantiate_both_let hE hv2j hbj2⟩
termination_by parRedW h1 + parRedW h2 + parRedCtxW hΓ1 + parRedCtxW hΓ2 + 1
decreasing_by
  all_goals simp [parRedW, parRedArgsW, parRedCtxW, exprSize]
  all_goals try (have := parRedW_pos (by assumption))
  all_goals try (have := parRedArgsW_pos (by assumption))
  all_goals try (have := parRedCtxW_get?_let (by assumption) (by assumption))
  all_goals try (have := parRedCtx_drop_weight (i + 1) (by assumption))
  all_goals omega

end

/-- Strip lemma: one parallel step vs a star. Lives after the
diamond mutual (iterates diamond along the star). -/
noncomputable def parRed_strip {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {a b c : Expr Nat} →
    (h : ParRed E n Γ a b) →
    (hs : ParRedStar E n Γ a c) →
    Σ' (d : Expr Nat),
      ParRedStar E n Γ b d ×' ParRedStar E n Γ c d
  | _, _, _, _, h, .refl _ _ =>
      ⟨_, ParRedStar.refl _ _, parRedStar_one h⟩
  | _, _, _, _, h, .tail h0 hs =>
      let ⟨m, hm1, hm2⟩ := parRed_diamond E n hE h h0 (parRedCtx_refl _) (parRedCtx_refl _)
      let ⟨d, hd1, hd2⟩ := parRed_strip hE hm2 hs
      ⟨d, .tail hm1 hd1, hd2⟩

/-- Star diamond from the one-step diamond. -/
noncomputable def parRedStar_diamond {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {a b c : Expr Nat} →
    ParRedStar E n Γ a b →
    ParRedStar E n Γ a c →
    Σ' (d : Expr Nat),
      ParRedStar E n Γ b d ×' ParRedStar E n Γ c d
  | _, _, _, _, .refl _ _, s2 =>
      ⟨_, s2, .refl _ _⟩
  | _, _, _, _, .tail h hs, s2 =>
      let ⟨m, hm1, hm2⟩ := parRed_strip hE h s2
      let ⟨d, hd1, hd2⟩ := parRedStar_diamond hE hs hm1
      ⟨d, hd1, parRedStar_trans hm2 hd2⟩

/-- Two stars to sorts, any source: strip to the sort fragment. -/
theorem two_stars_to_sort {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    {Γ : LCtx} {a : Expr Nat} {w w' : Level}
    (h1 : ParRedStar E n Γ a (.sort w))
    (h2 : ParRedStar E n Γ a (.sort w')) : eqN w w' :=
  let ⟨d, hd1, hd2⟩ := parRedStar_diamond hE h1 h2
  let ⟨v1, e1, q1⟩ := parRedStar_sort hd1 rfl
  let ⟨v2, e2, q2⟩ := parRedStar_sort hd2 rfl
  by
    have hv : Expr.sort v1 = Expr.sort v2 := e1.symm.trans e2
    injection hv with hvv
    subst hvv
    exact eqN_trans q1 (eqN_symm q2)

end Rcic.Declarative
