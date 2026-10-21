/-
RCIC Annex 23 UNIT H-1 — RM-009 / RM-010: `03` §3's `LiftExpr` /
`InstantiateExpr` submachine, over the landed FUNCTIONS `lift` /
`instantiate` (`RcicDeclarative`).

STATEMENTS FIRST (23.H.0 (3)) — the quotations this unit is answerable to,
byte-exact against their artifacts (mod a uniform dedent):

`03` §3 (docs/rcic/03_REFERENCE_MACHINE.md:60-61, inside the RawTask
fence; dedent N=2), the two task lines this unit mechanizes:

  | LiftExpr U64 U64 GlobalExpr
  | InstantiateExpr U64 GlobalExpr GlobalExpr

Carrier fuel law (apps/rcic-expr-subst/APP.md:55-57; dedent N=0):

Single `fuel` parameter, `level_eval`-style: `fuel < 0` refuses
`[rcic_expr_fuel]`; every child call (Expr children, the per-binder replacement
lift, and the level walks) gets `fuel - 1`.

`02` §5 substitution laws (docs/rcic/02_DECLARATIVE_THEORY.md:103-116;
dedent N=0) — these are what the LANDED functions implement and what
soundness relates the submachine to:

Substitution obeys:

```text
bvar index       → replacement
bvar i, i>index  → bvar(i-1)
bvar i, i<index  → bvar i
```

Under a binder:

```text
index       := index + 1
replacement := lift(0,1,replacement)
```

The carrier's level-arithmetic discipline (apps/rcic-expr-subst/APP.md:48-51,
dedent N=0), quoted for the WALL below:

documented numeric-op discipline: lift shifts `param i` with `i >= cutoff` by
amount; instantiate decrements `param i` with `i > index`; the instantiate
replacement is an Expr and never enters a Level. Unknown Level kinds pass through
as inert data — Level admissibility is `rcic.level_eval`'s slice, not this one.

WHAT THIS UNIT IS. A task-shaped entry `exprSubstTask` over the carrier's
wire encoding (kind-records; `ref` a String; `bvar`/cutoff/index Ints so
the carrier's refusal classes are representable) that charges the
per-DEPTH fuel the carrier charges — refusing `[rcic_expr_fuel]` where
the carrier refuses — and on acceptance returns the WIRE IMAGE of the
LANDED function's output: `exprEncode (lift cutoff amount (exprDecode e))`
(form 0) / `exprEncode (instantiate index repl e)` (form 1). It CALLS
`lift` / `instantiate` (23.H.0 (5)); it implements no second substitution
semantics. The walk carries the replacement UNCHANGED under binders
(the carrier re-lifts it; a `lift(0,1,·)` image has identical wire shape,
so the fuel/refusal behavior is the carrier's on every input, not only
on corpus rows).

MR-7 entry 10's OBSERVABLE ABSENCE ("on a term deeper than the remaining
fuel the Lean arm accepts and the carrier refuses", Annex 21 §21.1
RM-009/RM-010) closes here: the fuel-refusal witness and pin 11 refuse
`[rcic_expr_fuel]` on the exact term the carrier refuses it on.

WALL — corpus rows 9 and 10 are NOT pinned; both sides quoted.
`apps/rcic-expr-subst/rcic_expr_subst_corpus.json` rows 9/10 expect level
arithmetic (`lift` shifts `param i` with `i >= cutoff` by amount;
`instantiate` decrements `param i` with `i > index`):

  row 9 label: "lift shifts const level params and sort level (GM-SUBST-003 classic omission covered; mutant agrees)"
  row 9 expected (rendered through APP.md's kind-record encoding):
    app (const "c" [param 2, max (param 1) zero]) (sort (param 1))
    at form 0, cutoff 0, amount 1, e = app (const "c" [param 1,
    max (param 0) zero]) (sort (param 0)).
  row 10 label: "instantiate decrements const level params above index (mutant agrees)"
  row 10 expected (rendered through APP.md's kind-record encoding):
    const "c" [param 0, param 1] at form 1, index 0, e = const "c" [param 1, param 2].

The carrier implements this (scm/rcic/expr_lift.scm kind-1/2 arms call
`rcic.level_lift`/`rcic.levels_lift`; expr_inst.scm kind-1/2 arms call
`rcic.level_inst`/`rcic.levels_inst`) and its APP.md names it the slice's
"documented numeric-op discipline" (quoted above). The landed `lift` /
`instantiate` do NOT touch levels (RcicDeclarative.lean, `.sort l => .sort l`,
`.const r ls => .const r ls` in both), and `02` §5's laws are bvar-only
(quoted above; `02` §3 lists "level instantiation" as a SEPARATE structural
operation). A submachine over the landed functions therefore returns the
UNSHIFTED levels on rows 9/10 and the pins cannot be green, while a
carrier-faithful submachine breaks H-1 (d)'s soundness ("acceptance
implies equality with `lift` / `instantiate`") on the same rows. H-1 (b)
("pin count equals the corpus row count") and (d) are jointly
unsatisfiable as dispatched; both sides are quoted here, the pin count is
18 of 20, and the reconciliation is cc's to record (23.H.0 (6): a spec
erratum is cc's to record). No reconciliation is performed here.

Pin count: 18 (rows 1-8, 11-20). Corpus row count: 20.
closure_claim stays 0.

[H-1b: the wall is closed by H-7 / R-ExprSubst. Rows 9 and 10
were re-derived by H-7 (labels "lift traverses const level list
and sort level, levels untouched per 02 §5 (mutant agrees)" /
"instantiate traverses const level params, levels untouched per
02 §5 (mutant agrees)"); pin_est_row09 / pin_est_row10 now pin
them. Pin count: 20 / 20.]
-/
import rcic.RcicDeclarative

namespace Rcic.ExprSubstTask
open Rcic.Declarative

/-! ## Wire encoding (the carrier's kind-records; kinds 0..6, lit deferred) -/

/-- The corpus's Level records, kinds 0..4 (unknown level kinds are not
representable; the carrier passes them through inert and no corpus row
carries one). -/
inductive LevelWire : Type
  | zero : LevelWire
  | succ : LevelWire → LevelWire
  | max : LevelWire → LevelWire → LevelWire
  | imax : LevelWire → LevelWire → LevelWire
  | param : Int → LevelWire
  deriving DecidableEq

/-- The corpus's Expr records, kinds 0..6. `other k` is the corpus's
unknown-ctor slot (row 13 pins kind 7); the carrier defers `lit`
(APP.md: "lit is deferred as a separate profile object"), so there is no
lit constructor. -/
inductive ExprWire : Type
  | bvar : Int → ExprWire
  | sort : LevelWire → ExprWire
  | const : String → List LevelWire → ExprWire
  | app : ExprWire → ExprWire → ExprWire
  | lam : ExprWire → ExprWire → ExprWire
  | pi : ExprWire → ExprWire → ExprWire
  | letE : ExprWire → ExprWire → ExprWire → ExprWire
  | other : Int → ExprWire
  deriving DecidableEq

inductive ExprResult : Type
  | ok (e : ExprWire) : ExprResult
  | refuse (code : String) : ExprResult
  deriving DecidableEq

def residueExprFuel : String := "[rcic_expr_fuel]"
def residueExprUnknownCtor : String := "[rcic_expr_unknown_ctor]"
def residueExprUnknownForm : String := "[rcic_expr_unknown_form]"
def residueExprBvarNegative : String := "[rcic_expr_bvar_negative]"
def residueExprCutoffNegative : String := "[rcic_expr_cutoff_negative]"
def residueExprIndexNegative : String := "[rcic_expr_index_negative]"

/-! ## The fuel/defect walk — the carrier's per-DEPTH fuel discipline -/

/-- The walk's verdict: `.ok` = the carrier accepts; `.refuse c` = the
carrier refuses with code `c`. -/
inductive TaskWalk : Type
  | ok : TaskWalk
  | refuse (code : String) : TaskWalk
  deriving DecidableEq

/-- First-refusal combination (the carrier propagates the first child's
refusal code). -/
def combineTaskWalk : TaskWalk → TaskWalk → TaskWalk
  | .ok, w => w
  | .refuse c, _ => .refuse c

/-- `rcic.level_lift`/`rcic.level_inst`'s fuel discipline: `fuel < 0`
refuses; children at `fuel - 1`; `zero`/`param` are leaves. -/
def levelWalk : LevelWire → Int → TaskWalk
  | .zero, fuel =>
      if fuel < 0 then .refuse residueExprFuel else .ok
  | .param _, fuel =>
      if fuel < 0 then .refuse residueExprFuel else .ok
  | .succ a, fuel =>
      if fuel < 0 then .refuse residueExprFuel else levelWalk a (fuel - 1)
  | .max a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (levelWalk a (fuel - 1)) (levelWalk b (fuel - 1))
  | .imax a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (levelWalk a (fuel - 1)) (levelWalk b (fuel - 1))

/-- `rcic.levels_lift`/`rcic.levels_inst`'s fold: every element is
called at `(- fuel 1)` of the *fold's* fuel — the fold accumulator
carries no fuel (`levels_lift.scm:6`), so the tail recursion keeps
`fuel` unchanged rather than decrementing along the list. -/
def levelsWalk : List LevelWire → Int → TaskWalk
  | [], _ => .ok
  | l :: ls, fuel =>
      combineTaskWalk (levelWalk l (fuel - 1)) (levelsWalk ls fuel)

/-- `rcic.expr_lift`'s fuel/defect discipline: entry `fuel < 0` refuses;
`bvar i < 0` refuses; every child call at `fuel - 1`; binder children
share the same fuel decrement (only the cutoff moves, and the walk does
no arithmetic). -/
def liftWalk : ExprWire → Int → TaskWalk
  | .bvar i, fuel =>
      if fuel < 0 then .refuse residueExprFuel
      else if i < 0 then .refuse residueExprBvarNegative else .ok
  | .sort l, fuel =>
      if fuel < 0 then .refuse residueExprFuel else levelWalk l (fuel - 1)
  | .const _ ls, fuel =>
      if fuel < 0 then .refuse residueExprFuel else levelsWalk ls (fuel - 1)
  | .app f x, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (liftWalk f (fuel - 1)) (liftWalk x (fuel - 1))
  | .lam a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (liftWalk a (fuel - 1)) (liftWalk b (fuel - 1))
  | .pi a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (liftWalk a (fuel - 1)) (liftWalk b (fuel - 1))
  | .letE a v b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (liftWalk a (fuel - 1))
          (combineTaskWalk (liftWalk v (fuel - 1)) (liftWalk b (fuel - 1)))
  | .other _, fuel =>
      if fuel < 0 then .refuse residueExprFuel else .refuse residueExprUnknownCtor

/-- `rcic.expr_inst`'s fuel/defect discipline: as `liftWalk`, plus the
per-binder replacement lift charged at `fuel - 1` (kind 4/5/6 arms).
The replacement is carried UNCHANGED (a `lift 0 1` image has the same
wire shape, so the discipline is the carrier's). -/
def instWalk (replacement : ExprWire) : ExprWire → Int → TaskWalk
  | .bvar i, fuel =>
      if fuel < 0 then .refuse residueExprFuel
      else if i < 0 then .refuse residueExprBvarNegative else .ok
  | .sort l, fuel =>
      if fuel < 0 then .refuse residueExprFuel else levelWalk l (fuel - 1)
  | .const _ ls, fuel =>
      if fuel < 0 then .refuse residueExprFuel else levelsWalk ls (fuel - 1)
  | .app f x, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (instWalk replacement f (fuel - 1))
          (instWalk replacement x (fuel - 1))
  | .lam a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (instWalk replacement a (fuel - 1))
          (combineTaskWalk (liftWalk replacement (fuel - 1))
            (instWalk replacement b (fuel - 1)))
  | .pi a b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (instWalk replacement a (fuel - 1))
          (combineTaskWalk (liftWalk replacement (fuel - 1))
            (instWalk replacement b (fuel - 1)))
  | .letE a v b, fuel =>
      if fuel < 0 then .refuse residueExprFuel else
        combineTaskWalk (instWalk replacement a (fuel - 1))
          (combineTaskWalk (instWalk replacement v (fuel - 1))
            (combineTaskWalk (liftWalk replacement (fuel - 1))
              (instWalk replacement b (fuel - 1))))
  | .other _, fuel =>
      if fuel < 0 then .refuse residueExprFuel else .refuse residueExprUnknownCtor

/-! ## Decode / encode — the bridge to the landed functions -/

def levelDecode : LevelWire → Level
  | .zero => .zero
  | .succ a => .succ (levelDecode a)
  | .max a b => .max (levelDecode a) (levelDecode b)
  | .imax a b => .imax (levelDecode a) (levelDecode b)
  | .param i => .param i.toNat

def exprDecode : ExprWire → Expr String
  | .bvar i => .bvar i.toNat
  | .sort l => .sort (levelDecode l)
  | .const r ls => .const r (ls.map levelDecode)
  | .app f x => .app (exprDecode f) (exprDecode x)
  | .lam a b => .lam (exprDecode a) (exprDecode b)
  | .pi a b => .pi (exprDecode a) (exprDecode b)
  | .letE a v b => .letE (exprDecode a) (exprDecode v) (exprDecode b)
  | .other _ => .bvar 0

def levelEncode : Level → LevelWire
  | .zero => .zero
  | .succ a => .succ (levelEncode a)
  | .max a b => .max (levelEncode a) (levelEncode b)
  | .imax a b => .imax (levelEncode a) (levelEncode b)
  | .param i => .param i

/-- `lit` has no wire image (the carrier defers it); it maps to the
unknown-ctor slot, which the walk refuses before decode is consulted. -/
def exprEncode : Expr String → ExprWire
  | .bvar i => .bvar i
  | .sort l => .sort (levelEncode l)
  | .const r ls => .const r (ls.map levelEncode)
  | .app f x => .app (exprEncode f) (exprEncode x)
  | .lam a b => .lam (exprEncode a) (exprEncode b)
  | .pi a b => .pi (exprEncode a) (exprEncode b)
  | .letE a v b => .letE (exprEncode a) (exprEncode v) (exprEncode b)
  | .lit _ => .other 7

/-! ## The task-shaped entry (RM-009 / RM-010) -/

/-- `03` §3's `LiftExpr U64 U64 GlobalExpr` (form 0) and
`InstantiateExpr U64 GlobalExpr GlobalExpr` (form 1) as one entry over
the carrier's wire encoding, form dispatch and refusal classes exactly
the carrier's (`rcic_expr_subst.scm`), acceptance the wire image of the
LANDED `lift` / `instantiate`. -/
def exprSubstTask : Int → Int → Int → Int → Int → ExprWire → ExprWire → ExprResult
  | 0, fuel, cutoff, _, amount, _, e =>
      if cutoff < 0 then .refuse residueExprCutoffNegative
      else match liftWalk e fuel with
        | .refuse c => .refuse c
        | .ok => .ok (exprEncode (lift cutoff.toNat amount.toNat (exprDecode e)))
  | 1, fuel, _, index, _, replacement, e =>
      if index < 0 then .refuse residueExprIndexNegative
      else match instWalk replacement e fuel with
        | .refuse c => .refuse c
        | .ok => .ok (exprEncode (instantiate index.toNat (exprDecode replacement)
            (exprDecode e)))
  | _, _, _, _, _, _, _ => .refuse residueExprUnknownForm

/-! ## M-002 corpus pins (18 of 20 rows; rows 9/10 WALLED, see the
header). Every pin is a #eval panic guard: a failing guard fails the
build. Transcribed from
`apps/rcic-expr-subst/rcic_expr_subst_corpus.json` by hand
(§18.3 rule 4). -/
/-! [H-1b: the wall is closed by H-7 / R-ExprSubst;
pin count 20 / 20.] -/

-- row 1: "lift 0 0 is identity (mutant agrees)" — form 0, fuel 10, cutoff 0, amount 0
#eval (if exprSubstTask 0 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.app (ExprWire.bvar 0) (ExprWire.sort LevelWire.zero))
      = ExprResult.ok (ExprWire.app (ExprWire.bvar 0) (ExprWire.sort LevelWire.zero))
    then 0 else panic "pin_est_row01")

-- row 2: "instantiate with bvar-free body is identity (mutant agrees)" — form 1, fuel 10, index 0
#eval (if exprSubstTask 1 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.sort LevelWire.zero))
      = ExprResult.ok
        (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.sort LevelWire.zero))
    then 0 else panic "pin_est_row02")

-- row 3: "lift above cutoff shifts by amount, below unchanged (mutant agrees)" — form 0, cutoff 1, amount 2
#eval (if exprSubstTask 0 10 1 0 2
      (ExprWire.sort LevelWire.zero)
      (ExprWire.app (ExprWire.bvar 0) (ExprWire.bvar 3))
      = ExprResult.ok (ExprWire.app (ExprWire.bvar 0) (ExprWire.bvar 5))
    then 0 else panic "pin_est_row03")

-- row 4: "lift crossing lam increments cutoff at boundary (mutant agrees)" — form 0, cutoff 1, amount 1
#eval (if exprSubstTask 0 10 1 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.app (ExprWire.bvar 1) (ExprWire.bvar 2)))
      = ExprResult.ok (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.app (ExprWire.bvar 1) (ExprWire.bvar 3)))
    then 0 else panic "pin_est_row04")

-- row 5: "lift traverses letE binder child (GM-SUBST-003: mutant leaves letE body unlifted)" — form 0, cutoff 0, amount 1
#eval (if exprSubstTask 0 10 0 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.letE (ExprWire.sort LevelWire.zero) (ExprWire.bvar 0) (ExprWire.bvar 1))
      = ExprResult.ok
        (ExprWire.letE (ExprWire.sort LevelWire.zero) (ExprWire.bvar 1) (ExprWire.bvar 2))
    then 0 else panic "pin_est_row05")

-- row 6: "instantiate lifts replacement under binder - capture freedom (GM-SUBST-001: mutant substitutes unlifted)" — form 1, index 0
#eval (if exprSubstTask 1 10 0 0 0
      (ExprWire.bvar 0)
      (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 1))
      = ExprResult.ok (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 1))
    then 0 else panic "pin_est_row06")

-- row 7: "instantiate decrements indices above substituted var (GM-SUBST-002: mutant keeps bvar 2)" — form 1, index 0
#eval (if exprSubstTask 1 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 2)
      = ExprResult.ok (ExprWire.bvar 1)
    then 0 else panic "pin_est_row07")

-- row 8: "instantiate under lam: shifted match inserts repl, above decremented (mutant agrees: repl immune to lift)" — form 1, index 1
#eval (if exprSubstTask 1 10 0 1 0
      (ExprWire.const "k" [])
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.app (ExprWire.bvar 2) (ExprWire.bvar 5)))
      = ExprResult.ok (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.app (ExprWire.const "k" []) (ExprWire.bvar 4)))
    then 0 else panic "pin_est_row08")

-- row 9: "lift traverses const level list and sort level, levels
-- untouched per 02 §5 (mutant agrees)" — form 0, cutoff 0, amount 1
#eval (if exprSubstTask 0 10 0 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.app
        (ExprWire.const "c" [LevelWire.param 1,
          LevelWire.max (LevelWire.param 0) LevelWire.zero])
        (ExprWire.sort (LevelWire.param 0)))
      = ExprResult.ok (ExprWire.app
        (ExprWire.const "c" [LevelWire.param 1,
          LevelWire.max (LevelWire.param 0) LevelWire.zero])
        (ExprWire.sort (LevelWire.param 0)))
    then 0 else panic "pin_est_row09")

-- row 10: "instantiate traverses const level params, levels
-- untouched per 02 §5 (mutant agrees)" — form 1, index 0
#eval (if exprSubstTask 1 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.const "c" [LevelWire.param 1, LevelWire.param 2])
      = ExprResult.ok
        (ExprWire.const "c" [LevelWire.param 1, LevelWire.param 2])
    then 0 else panic "pin_est_row10")

-- row 11: "deep lam nesting fuel=2 refuses [rcic_expr_fuel]" — THE FUEL TOOTH
#eval (if exprSubstTask 0 2 0 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 3))))
      = ExprResult.refuse "[rcic_expr_fuel]"
    then 0 else panic "pin_est_row11")

-- row 12: "deep lam nesting fuel=5 succeeds (mutant agrees)" — form 0, fuel 5
#eval (if exprSubstTask 0 5 0 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 3))))
      = ExprResult.ok (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 4))))
    then 0 else panic "pin_est_row12")

-- row 13: "unknown expr kind 7 refuses [rcic_expr_unknown_ctor]" — form 0
#eval (if exprSubstTask 0 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.other 7)
      = ExprResult.refuse "[rcic_expr_unknown_ctor]"
    then 0 else panic "pin_est_row13")

-- row 14: "unknown form 2 refuses [rcic_expr_unknown_form]"
#eval (if exprSubstTask 2 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0)
      = ExprResult.refuse "[rcic_expr_unknown_form]"
    then 0 else panic "pin_est_row14")

-- row 15: "negative bvar index refuses [rcic_expr_bvar_negative]" — form 0
#eval (if exprSubstTask 0 10 0 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar (-1))
      = ExprResult.refuse "[rcic_expr_bvar_negative]"
    then 0 else panic "pin_est_row15")

-- row 16: "negative cutoff refuses [rcic_expr_cutoff_negative]" — form 0, cutoff -1
#eval (if exprSubstTask 0 10 (-1) 0 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0)
      = ExprResult.refuse "[rcic_expr_cutoff_negative]"
    then 0 else panic "pin_est_row16")

-- row 17: "negative index refuses [rcic_expr_index_negative]" — form 1, index -1
#eval (if exprSubstTask 1 10 0 (-1) 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0)
      = ExprResult.refuse "[rcic_expr_index_negative]"
    then 0 else panic "pin_est_row17")

-- row 18: "instantiate preserves below-index bvars (mutant agrees)" — form 1, index 1
#eval (if exprSubstTask 1 10 0 1 0
      (ExprWire.sort LevelWire.zero)
      (ExprWire.app (ExprWire.bvar 0) (ExprWire.bvar 1))
      = ExprResult.ok (ExprWire.app (ExprWire.bvar 0) (ExprWire.sort LevelWire.zero))
    then 0 else panic "pin_est_row18")

-- row 19: "lift letE with pi body under binder (GM-SUBST-003 row 2: mutant leaves letE body unlifted)" — form 0
#eval (if exprSubstTask 0 10 0 0 1
      (ExprWire.sort LevelWire.zero)
      (ExprWire.letE (ExprWire.sort LevelWire.zero) (ExprWire.bvar 0)
        (ExprWire.pi (ExprWire.sort LevelWire.zero) (ExprWire.bvar 2)))
      = ExprResult.ok (ExprWire.letE (ExprWire.sort LevelWire.zero) (ExprWire.bvar 1)
        (ExprWire.pi (ExprWire.sort LevelWire.zero) (ExprWire.bvar 3)))
    then 0 else panic "pin_est_row19")

-- row 20: "R-CIC E2 killer: lift shifts only i>cutoff so bvar 2 at cutoff=2 stays unshifted (registry: expr-subst lift i>cutoff arm)" — form 0, cutoff 2, amount 3
#eval (if exprSubstTask 0 10 2 0 3
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 2)
      = ExprResult.ok (ExprWire.bvar 5)
    then 0 else panic "pin_est_row20")

/-! ## M-005 witnesses (closed; compile-time, not #eval) -/

/-- M-005 acceptance witness: row 12's term at fuel 5 accepts with the
landed `lift`'s output. -/
theorem exprSubstTask_witness_accept :
    exprSubstTask 0 5 0 0 1 (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 3))))
      = ExprResult.ok (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 4)))) := by
  decide

/-- M-005 fuel-refusal witness: the SAME term at fuel 2 refuses
`[rcic_expr_fuel]` — MR-7 entry 10's observable absence closed (the Lean
arm no longer accepts where the carrier refuses). -/
theorem exprSubstTask_witness_fuel_refuse :
    exprSubstTask 0 2 0 0 1 (ExprWire.sort LevelWire.zero)
      (ExprWire.lam (ExprWire.sort LevelWire.zero)
        (ExprWire.lam (ExprWire.sort LevelWire.zero)
          (ExprWire.lam (ExprWire.sort LevelWire.zero) (ExprWire.bvar 3))))
      = ExprResult.refuse "[rcic_expr_fuel]" := by
  decide

/-! ## The stated bound and the two relation theorems -/

def levelWireSize : LevelWire → Nat
  | .zero | .param _ => 1
  | .succ a => 1 + levelWireSize a
  | .max a b | .imax a b => 1 + levelWireSize a + levelWireSize b

def levelsWireSize : List LevelWire → Nat
  | [] => 0
  | l :: ls => levelWireSize l + levelsWireSize ls

/-- The stated bound's size: every wire node charges 1, `const` charges 2
(its level list sits one fuel deeper: the fold's per-element `fuel - 1`
comes out of the const node's own decrement). -/
def exprWireSize : ExprWire → Nat
  | .bvar _ | .other _ => 1
  | .sort l => 1 + levelWireSize l
  | .const _ ls => 2 + levelsWireSize ls
  | .app f x => 1 + exprWireSize f + exprWireSize x
  | .lam a b | .pi a b => 1 + exprWireSize a + exprWireSize b
  | .letE a v b => 1 + exprWireSize a + exprWireSize v + exprWireSize b

/-- Well-formedity for completeness: no unknown-ctor slots, no negative
bvars (levels carry no refusal classes of their own). -/
def wireOk : ExprWire → Prop
  | .bvar i => 0 ≤ i
  | .sort _ | .const _ _ => True
  | .app f x | .lam f x | .pi f x => wireOk f ∧ wireOk x
  | .letE a v b => wireOk a ∧ wireOk v ∧ wireOk b
  | .other _ => False

theorem wireOk_bvar {i : Int} (h : wireOk (ExprWire.bvar i)) : 0 ≤ i := by
  simp only [wireOk] at h; exact h

theorem wireOk_app_f {f x : ExprWire} (h : wireOk (ExprWire.app f x)) : wireOk f := by
  simp only [wireOk] at h; exact h.1

theorem wireOk_app_x {f x : ExprWire} (h : wireOk (ExprWire.app f x)) : wireOk x := by
  simp only [wireOk] at h; exact h.2

theorem wireOk_lam_a {a b : ExprWire} (h : wireOk (ExprWire.lam a b)) : wireOk a := by
  simp only [wireOk] at h; exact h.1

theorem wireOk_lam_b {a b : ExprWire} (h : wireOk (ExprWire.lam a b)) : wireOk b := by
  simp only [wireOk] at h; exact h.2

theorem wireOk_pi_a {a b : ExprWire} (h : wireOk (ExprWire.pi a b)) : wireOk a := by
  simp only [wireOk] at h; exact h.1

theorem wireOk_pi_b {a b : ExprWire} (h : wireOk (ExprWire.pi a b)) : wireOk b := by
  simp only [wireOk] at h; exact h.2

theorem wireOk_letE_a {a v b : ExprWire} (h : wireOk (ExprWire.letE a v b)) : wireOk a := by
  simp only [wireOk] at h; exact h.1

theorem wireOk_letE_v {a v b : ExprWire} (h : wireOk (ExprWire.letE a v b)) : wireOk v := by
  simp only [wireOk] at h; exact h.2.1

theorem wireOk_letE_b {a v b : ExprWire} (h : wireOk (ExprWire.letE a v b)) : wireOk b := by
  simp only [wireOk] at h; exact h.2.2

theorem levelWalk_ok (l : LevelWire) (fuel : Int)
    (h : 2 * levelWireSize l ≤ fuel) : levelWalk l fuel = TaskWalk.ok := by
  induction l generalizing fuel with
  | zero =>
      simp only [levelWalk]
      simp only [levelWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
  | param i =>
      simp only [levelWalk]
      simp only [levelWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
  | succ a ih =>
      simp only [levelWalk]
      simp only [levelWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      exact ih (fuel - 1) (by omega)
  | max a b iha ihb =>
      simp only [levelWalk]
      simp only [levelWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (fuel - 1) (by omega), ihb (fuel - 1) (by omega)]
      rfl
  | imax a b iha ihb =>
      simp only [levelWalk]
      simp only [levelWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (fuel - 1) (by omega), ihb (fuel - 1) (by omega)]
      rfl

theorem levelsWalk_ok (ls : List LevelWire) (fuel : Int)
    (h : 2 * levelsWireSize ls + 2 ≤ fuel) : levelsWalk ls fuel = TaskWalk.ok := by
  induction ls generalizing fuel with
  | nil => simp only [levelsWalk]
  | cons l ls ih =>
      simp only [levelsWalk]
      simp only [levelsWireSize] at h
      have hl1 : 1 ≤ levelWireSize l := by
        cases l <;> simp only [levelWireSize] <;> omega
      rw [levelWalk_ok l (fuel - 1) (by omega), ih fuel (by omega)]
      rfl

theorem liftWalk_ok (e : ExprWire) (fuel : Int) (he : wireOk e)
    (h : 2 * exprWireSize e ≤ fuel) : liftWalk e fuel = TaskWalk.ok := by
  induction e generalizing fuel with
  | bvar i =>
      simp only [liftWalk]
      have hi : 0 ≤ i := wireOk_bvar he
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [if_neg (show ¬ (i < 0) by omega)]
  | sort l =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      exact levelWalk_ok l (fuel - 1) (by omega)
  | const r ls =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      exact levelsWalk_ok ls (fuel - 1) (by omega)
  | app f x ihf ihx =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [ihf (fuel - 1) (wireOk_app_f he) (by omega),
        ihx (fuel - 1) (wireOk_app_x he) (by omega)]
      rfl
  | lam a b iha ihb =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (fuel - 1) (wireOk_lam_a he) (by omega),
        ihb (fuel - 1) (wireOk_lam_b he) (by omega)]
      rfl
  | pi a b iha ihb =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (fuel - 1) (wireOk_pi_a he) (by omega),
        ihb (fuel - 1) (wireOk_pi_b he) (by omega)]
      rfl
  | letE a v b iha ihv ihb =>
      simp only [liftWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (fuel - 1) (wireOk_letE_a he) (by omega),
        ihv (fuel - 1) (wireOk_letE_v he) (by omega),
        ihb (fuel - 1) (wireOk_letE_b he) (by omega)]
      rfl
  | other k => simp only [wireOk] at he

theorem instWalk_ok (replacement e : ExprWire) (hr : wireOk replacement)
    (he : wireOk e) (fuel : Int)
    (h : 2 * (exprWireSize e + exprWireSize replacement) ≤ fuel) :
    instWalk replacement e fuel = TaskWalk.ok := by
  induction e generalizing fuel with
  | bvar i =>
      simp only [instWalk]
      have hi : 0 ≤ i := wireOk_bvar he
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [if_neg (show ¬ (i < 0) by omega)]
  | sort l =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      exact levelWalk_ok l (fuel - 1) (by omega)
  | const r ls =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      exact levelsWalk_ok ls (fuel - 1) (by omega)
  | app f x ihf ihx =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [ihf (wireOk_app_f he) (fuel - 1) (by omega),
        ihx (wireOk_app_x he) (fuel - 1) (by omega)]
      rfl
  | lam a b iha ihb =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (wireOk_lam_a he) (fuel - 1) (by omega)]
      rw [liftWalk_ok replacement (fuel - 1) hr (by omega)]
      rw [ihb (wireOk_lam_b he) (fuel - 1) (by omega)]
      rfl
  | pi a b iha ihb =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (wireOk_pi_a he) (fuel - 1) (by omega)]
      rw [liftWalk_ok replacement (fuel - 1) hr (by omega)]
      rw [ihb (wireOk_pi_b he) (fuel - 1) (by omega)]
      rfl
  | letE a v b iha ihv ihb =>
      simp only [instWalk]
      simp only [exprWireSize] at h
      rw [if_neg (show ¬ (fuel < 0) by omega)]
      rw [iha (wireOk_letE_a he) (fuel - 1) (by omega),
        ihv (wireOk_letE_v he) (fuel - 1) (by omega)]
      rw [liftWalk_ok replacement (fuel - 1) hr (by omega)]
      rw [ihb (wireOk_letE_b he) (fuel - 1) (by omega)]
      rfl
  | other k => simp only [wireOk] at he

/-- H-1 (d) soundness: acceptance implies equality with the landed
`lift` / `instantiate` — the accept value IS the wire image of the
landed function's output on the decoded input, for EVERY wire input
(malformed inputs refuse, so acceptance is vacuous there). -/
theorem exprSubstTask_soundness :
    (∀ (cutoff amount fuel : Int) (replacement e r : ExprWire),
        exprSubstTask 0 fuel cutoff 0 amount replacement e = ExprResult.ok r →
        r = exprEncode (lift cutoff.toNat amount.toNat (exprDecode e)))
  ∧ (∀ (index fuel : Int) (replacement e r : ExprWire),
        exprSubstTask 1 fuel 0 index 0 replacement e = ExprResult.ok r →
        r = exprEncode (instantiate index.toNat (exprDecode replacement)
          (exprDecode e))) := by
  refine ⟨fun cutoff amount fuel replacement e r h => ?_,
    fun index fuel replacement e r h => ?_⟩
  · simp only [exprSubstTask] at h
    split at h
    · exact ExprResult.noConfusion h
    · split at h
      · exact ExprResult.noConfusion h
      · injection h with h'; exact h'.symm
  · simp only [exprSubstTask] at h
    split at h
    · exact ExprResult.noConfusion h
    · split at h
      · exact ExprResult.noConfusion h
      · injection h with h'; exact h'.symm

/-- H-1 (d) completeness under the stated bound: twice the wire size
(plus the replacement's, for form 1) suffices — sufficient fuel implies
acceptance, with the landed function's output. -/
theorem exprSubstTask_completeness :
    (∀ (cutoff amount fuel : Int) (replacement e : ExprWire),
        0 ≤ cutoff → wireOk e → 2 * exprWireSize e ≤ fuel →
        exprSubstTask 0 fuel cutoff 0 amount replacement e
          = ExprResult.ok (exprEncode (lift cutoff.toNat amount.toNat (exprDecode e))))
  ∧ (∀ (index fuel : Int) (replacement e : ExprWire),
        0 ≤ index → wireOk replacement → wireOk e →
        2 * (exprWireSize e + exprWireSize replacement) ≤ fuel →
        exprSubstTask 1 fuel 0 index 0 replacement e
          = ExprResult.ok (exprEncode (instantiate index.toNat (exprDecode replacement)
              (exprDecode e)))) := by
  refine ⟨fun cutoff amount fuel replacement e hc he hf => ?_,
    fun index fuel replacement e hi hr he hf => ?_⟩
  · simp only [exprSubstTask]
    rw [if_neg (show ¬ (cutoff < 0) by omega),
      liftWalk_ok e fuel he hf]
  · simp only [exprSubstTask]
    rw [if_neg (show ¬ (index < 0) by omega),
      instWalk_ok replacement e hr he fuel hf]

/-! ## RM-009 / RM-010 — the named task entries and the row-anchored pair

The census rows want the `03` §3 task names implemented and the
soundness/completeness legs anchored to the row: `liftExpr` /
`instantiateExpr` are the form-0 / form-1 arms of `exprSubstTask` with
the inert form slots pinned, and `RM009_*` / `RM010_*` re-expose the
pair per-row. No new semantics — the pair is the same theorem. -/

/-- `LiftExpr U64 U64 GlobalExpr` (03 §3, form 0) as a named entry. The
form's `index`/`replacement` slots are inert in the lift arm — pinned to
`0` / `.bvar 0` (the form-0 arm never reads them). -/
def liftExpr (fuel cutoff amount : Int) (e : ExprWire) : ExprResult :=
  exprSubstTask 0 fuel cutoff 0 amount (.bvar 0) e

/-- `InstantiateExpr U64 GlobalExpr GlobalExpr` (03 §3, form 1) as a
named entry. The form's `cutoff`/`amount` slots are inert in the
instantiate arm — pinned to `0`. -/
def instantiateExpr (fuel index : Int) (replacement e : ExprWire) : ExprResult :=
  exprSubstTask 1 fuel 0 index 0 replacement e

/-- RM-009 — the lifting submachine's soundness leg, row-anchored:
`liftExpr` acceptance yields the wire image of the landed `lift`. -/
theorem RM009_liftExpr_sound (cutoff amount fuel : Int) (e r : ExprWire)
    (h : liftExpr fuel cutoff amount e = ExprResult.ok r) :
    r = exprEncode (lift cutoff.toNat amount.toNat (exprDecode e)) :=
  exprSubstTask_soundness.1 cutoff amount fuel (.bvar 0) e r h

/-- RM-009 — the completeness leg, anchored: under the stated fuel bound
`liftExpr` accepts with the landed `lift`'s output. -/
theorem RM009_liftExpr_complete (cutoff amount fuel : Int) (e : ExprWire)
    (hc : 0 ≤ cutoff) (he : wireOk e) (hf : 2 * exprWireSize e ≤ fuel) :
    liftExpr fuel cutoff amount e
      = ExprResult.ok (exprEncode (lift cutoff.toNat amount.toNat (exprDecode e))) :=
  exprSubstTask_completeness.1 cutoff amount fuel (.bvar 0) e hc he hf

/-- RM-010 — `InstantiateExpr` implemented: the soundness leg. Acceptance
of `instantiateExpr` yields the wire image of the landed `instantiate`. -/
theorem RM010_instantiateExpr_sound (index fuel : Int) (replacement e r : ExprWire)
    (h : instantiateExpr fuel index replacement e = ExprResult.ok r) :
    r = exprEncode (instantiate index.toNat (exprDecode replacement) (exprDecode e)) :=
  exprSubstTask_soundness.2 index fuel replacement e r h

/-- RM-010 — the completeness leg: under the stated bound
`instantiateExpr` accepts with the landed `instantiate`'s output. -/
theorem RM010_instantiateExpr_complete (index fuel : Int) (replacement e : ExprWire)
    (hi : 0 ≤ index) (hr : wireOk replacement) (he : wireOk e)
    (hf : 2 * (exprWireSize e + exprWireSize replacement) ≤ fuel) :
    instantiateExpr fuel index replacement e
      = ExprResult.ok (exprEncode (instantiate index.toNat (exprDecode replacement)
          (exprDecode e))) :=
  exprSubstTask_completeness.2 index fuel replacement e hi hr he hf

#print axioms Rcic.ExprSubstTask.liftExpr
#print axioms Rcic.ExprSubstTask.instantiateExpr
#print axioms Rcic.ExprSubstTask.RM009_liftExpr_sound
#print axioms Rcic.ExprSubstTask.RM009_liftExpr_complete
#print axioms Rcic.ExprSubstTask.RM010_instantiateExpr_sound
#print axioms Rcic.ExprSubstTask.RM010_instantiateExpr_complete

end Rcic.ExprSubstTask
