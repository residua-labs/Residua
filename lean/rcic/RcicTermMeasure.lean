/-
RCIC term measure (Annex 22 UNIT B-a, RANK 3) — `bvarCount` and
`exprSize_instantiate_bound`, the one ring-free arithmetic name of
the B-a decomposition.

LEAF DISCIPLINE (22.B.6 B-a.4, siting MEASURED not chosen): this file
has `rcic.RcicParRedWeight` as its ONLY import. `RcicParRedWeight`
has Diamond in its rebuild set, so stating the bound INSIDE that file
makes every proof iteration pay a whole-library build. A leaf below
it has ONE dependent once registered (`RcicFoundationSeal`).

WHAT THIS FILE IS. A bound on `instantiate`'s size blow-up that the
tree does not hold and that any later measure work consumes. It
closes NO row, NO arm, NO face, and no prerequisite. `00` §20.8 S-8:
the `irr` arm is not closed; no `00` §19.2 row moves; `closure_claim`
stays `0`.

WHAT THIS FILE IS NOT. It does not introduce `TermNormal`,
`TermHeadNormal`, `WnTyped`, `WhnTypes`, `parRed_exprSize_bound`, or
the three `_of_normalizing` discharges (those live only on
`wip/rcic-term-measure-probe` and never reach `main`, 22.B.6 B-a.4 /
B-a.5 (v)). It does not reach `propRefine`, `levelIsZero`, or
`NoSortProp` (22.B.7 R-1). It does not refute normalization: the
ranking line of 22.B.1, used verbatim, is (a) UNOWNED (O-3; `02` §14
lists no normalization metatheorem, `00` §4's conjunct list contains
none) and ARGUED insufficient for the `irr` arm; its LEVEL-MEASURE
form REFUTED (five sealed names).

No `sorry`, no `axiom`, no `Classical`, no `native_decide`, no
`admit`. No bare `simp`. `omega` only on genuinely arithmetic goals
(`00` §18.3 rules 3 and 9). `bvarCount` is a data `def` and is NOT
sealed (famProp* precedent, A1-R8 / 22.B.3).
-/
import rcic.RcicParRedWeight

namespace Rcic.Declarative

/-- Occurrence count of de Bruijn index `i` in a term. Data; consumed
by `exprSize_instantiate_bound` in this same file (22.B.7 R-2). Not
sealed. -/
def bvarCount (i : Nat) : Expr Nat → Nat
  | .bvar j      => if j = i then 1 else 0
  | .sort _      => 0
  | .const _ _   => 0
  | .app f a     => bvarCount i f + bvarCount i a
  | .lam a b     => bvarCount i a + bvarCount (i + 1) b
  | .pi a b      => bvarCount i a + bvarCount (i + 1) b
  | .letE a v b  => bvarCount i a + bvarCount i v + bvarCount (i + 1) b
  | .lit _       => 0

/-- Size blow-up of `instantiate`: each occurrence of `bvar i` in `t`
is replaced by `r` (lifted under binders, and `exprSize_lift` says
the lift does not change size). Annex 22 B-a-2. -/
theorem exprSize_instantiate_bound :
    (t : Expr Nat) → (i : Nat) → (r : Expr Nat) →
    exprSize (instantiate i r t)
      ≤ exprSize t + bvarCount i t * exprSize r := by
  intro t i r
  induction t generalizing i r with
  | bvar j =>
      simp only [instantiate, exprSize, bvarCount]
      split
      · omega
      · split <;> (simp only [exprSize]; omega)
  | sort _ =>
      simp only [instantiate, exprSize, bvarCount]
      omega
  | const _ _ =>
      simp only [instantiate, exprSize, bvarCount]
      omega
  | lit _ =>
      simp only [instantiate, exprSize, bvarCount]
      omega
  | app f a ihf iha =>
      simp only [instantiate, exprSize, bvarCount]
      have hf := ihf i r
      have ha := iha i r
      simp only [Nat.add_mul]
      omega
  | lam a b iha ihb =>
      simp only [instantiate, exprSize, bvarCount]
      have hA := iha i r
      have hB := ihb (i + 1) (lift 0 1 r)
      simp only [exprSize_lift] at hB
      simp only [Nat.add_mul]
      omega
  | pi a b iha ihb =>
      simp only [instantiate, exprSize, bvarCount]
      have hA := iha i r
      have hB := ihb (i + 1) (lift 0 1 r)
      simp only [exprSize_lift] at hB
      simp only [Nat.add_mul]
      omega
  | letE a v b iha ihv ihb =>
      simp only [instantiate, exprSize, bvarCount]
      have hA := iha i r
      have hV := ihv i r
      have hB := ihb (i + 1) (lift 0 1 r)
      simp only [exprSize_lift] at hB
      simp only [Nat.add_mul]
      omega

end Rcic.Declarative
