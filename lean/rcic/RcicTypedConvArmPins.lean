import rcic.RcicTypedConvPins
import rcic.RcicSrcEnvV1

/-!
# The conversion checker's three arms, pinned

`RcicTypedConv`'s conversion has three arms that only turn a refusal into a derivation: application
congruence (`appConvWith`), literal expansion (`litAt?`), proof irrelevance (`irrAt?`). For each arm
there is a small closed environment with a check the checker refused before the arms and passes with
them, and a control it still refuses. The refusal before is recorded as a comment: the `#eval` run
against the checker at `2701fd3914`, the commit these arms start from. Each one was refused at fuel 64
as well, so the refusal did not come from a lack of fuel. The pass after is a theorem.

* (1) Application congruence, with δ inside an argument (`apc_admits`): `p : P mk` checked at `P r`,
  where `r := mk` is a definition. Controls (`apc_refuses`): `P mk'` for a second constructor `mk'`,
  and `P r` with `r` an axiom, so that there is no δ step.
* (2) Literal expansion (`lex_admits`): `v : V (succ 1)` checked at `V 2`. Control (`lex_refuses`):
  `V 3`.
* (3) Proof irrelevance (`pir_admits`): `x : F q₁` checked at `F q₂`, for two proofs `q₁ q₂ : Q` of a
  proposition `Q : Prop`. Control (`pir_refuses`): the same over `B : Type`, which is not a proposition.
* The measured case (`srcCct_admits`). In `srcEnvV1` (`RcicSrcEnvV1`), the value of `cctI64Pf` has type
  `CCT (mkRef 3 16 digestI) bytesI`, while its stated type is `CCT i64Ref bytesI` with
  `i64Ref := mkRef 3 16 digestI` (`srcCct_shape`). `vb0` is the same case with the definition
  `boundBool`. The checker refused both before the arms and passes both with them, at fuel 4.

Each check reaches its arm as an argument of an application. Two types reach `convAt?` only through
arm (1) in `tyConv?`. The checker's answers are derivations (`apcTyT`, `lexTyT`, `pirTyT`).

The pins of `RcicTypedConvPins` and `RcicTypedDeltaRecPins` are unchanged and still hold, refusals
included.
-/

namespace Rcic.Declarative

/-! ## (1) application congruence: δ inside an argument -/

/-- `R : Type` at `0`. -/
def apcRMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- a constructor `: R`: `mk` at `1`, `mk'` at `5`. -/
def apcMkMember : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩

/-- `r : R := mk` at `2`, a definition. -/
def apcRefMember : CheckedMember := ⟨.definitionM, 0, .const 0 [], some (.const 1 [])⟩

/-- the same type as an axiom: no body, never unfolded. -/
def apcRefAxMember : CheckedMember := ⟨.axiomM, 0, .const 0 [], none⟩

/-- `P : R → Prop` at `3`. -/
def apcPMember : CheckedMember := ⟨.inductiveM, 0, .pi (.const 0 []) (.sort .zero), none⟩

/-- `p : P mk` at `4`. -/
def apcpMember : CheckedMember := ⟨.axiomM, 0, .app (.const 3 []) (.const 1 []), none⟩

/-- the environment, with `rm` at `2`. -/
def apcBase (rm : CheckedMember) : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv (extendEnv (extendEnv (extendEnv emptyEnv 0 apcRMember) 1 apcMkMember)
    2 rm) 3 apcPMember) 4 apcpMember) 5 apcMkMember

def apcEnv : ResolvedEnv := apcBase apcRefMember
def apcAxEnv : ResolvedEnv := apcBase apcRefAxMember

/-- ARM (1): `p : P r`. The inferred type `P mk` and the type asked for `P r` are applications of
    `P` that head steps leave as they are, since `P` is rigid. Application congruence compares the
    heads, `P` with `P`, and the arguments, `mk` with `r`, where a δ step on `r` gives `mk`.

    BEFORE (`2701fd3914`):
    `#eval (tyAtC apcEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome`
    `-- false` -/
theorem apc_admits : (tyAtC apcEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome = true :=
  rfl

/-- the checker's answer: a derivation of `p : P r`. -/
def apcTyT : HasTyT apcEnv 0 [] (.const 4 []) (.app (.const 3 []) (.const 2 [])) :=
  (tyAtC apcEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).get apc_admits

/-- CONTROLS, refused at fuel 4 and at fuel 16: `P mk'`, because congruence reaches `mk` against `mk'`
    and no arm relates two distinct constructors; `P r` with `r` an axiom, because congruence reaches
    `mk` against `r` and an axiom has no δ step. Both were refused before as well (`#eval` at
    `2701fd3914`: `false`, `false`). -/
theorem apc_refuses :
    (tyAtC apcEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 5 []))).isSome = false ∧
    (tyAtC apcAxEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome = false ∧
    (tyAtC apcEnv 0 16 [] (.const 4 []) (.app (.const 3 []) (.const 5 []))).isSome = false ∧
    (tyAtC apcAxEnv 0 16 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## (2) literal expansion -/

/-- `V : N → Type` at `4`, over Nat (`natEnvU`: `N`, `zero`, `succ` at `0`, `1`, `2`). -/
def lexVMember : CheckedMember := ⟨.inductiveM, 0, .pi (.const 0 []) (.sort (.succ .zero)), none⟩

/-- `v : V (succ 1)` at `5`: the index is `succ` applied to a numeral. -/
def lexvMember : CheckedMember :=
  ⟨.axiomM, 0, .app (.const 4 []) (.app (.const 2 []) (.lit 1)), none⟩

def lexEnv : ResolvedEnv := extendEnv (extendEnv natEnvU 4 lexVMember) 5 lexvMember

/-- ARM (2): `v : V 2`. Application congruence compares the indices `succ 1` and `2` at `N`. The
    numeral `2` converts to its expansion `succ (succ zero)` (`ConvT.lit`). Congruence then compares
    `1` with `succ zero`, and `1` converts to its expansion in the same way.

    BEFORE (`2701fd3914`):
    `#eval (tyAtC lexEnv 0 4 [] (.const 5 []) (.app (.const 4 []) (.lit 2))).isSome`
    `-- false` -/
theorem lex_admits : (tyAtC lexEnv 0 4 [] (.const 5 []) (.app (.const 4 []) (.lit 2))).isSome = true :=
  rfl

/-- the checker's answer: a derivation of `v : V 2`. -/
def lexTyT : HasTyT lexEnv 0 [] (.const 5 []) (.app (.const 4 []) (.lit 2)) :=
  (tyAtC lexEnv 0 4 [] (.const 5 []) (.app (.const 4 []) (.lit 2))).get lex_admits

/-- CONTROL, refused at fuel 4 and at fuel 16: `V 3`. After `3` and `1` are expanded, congruence
    reaches `zero` against `succ zero`, which no arm relates. At fuel 4 the fuel runs out one level
    before that point, so the refusal at fuel 16 is the one that shows it. It was refused before as
    well (`#eval` at `2701fd3914`: `false`). -/
theorem lex_refuses :
    (tyAtC lexEnv 0 4 [] (.const 5 []) (.app (.const 4 []) (.lit 3))).isSome = false ∧
    (tyAtC lexEnv 0 16 [] (.const 5 []) (.app (.const 4 []) (.lit 3))).isSome = false :=
  ⟨rfl, rfl⟩

/-! ## (3) proof irrelevance -/

/-- `Q : Prop` at `0`. -/
def pirQMember : CheckedMember := ⟨.axiomM, 0, .sort .zero, none⟩

/-- a proof `: Q`: `q₁` at `1`, `q₂` at `2`. -/
def pirqMember : CheckedMember := ⟨.axiomM, 0, .const 0 [], none⟩

/-- `F : Q → Type` at `3`. -/
def pirFMember : CheckedMember := ⟨.axiomM, 0, .pi (.const 0 []) (.sort (.succ .zero)), none⟩

/-- `x : F q₁` at `4`. -/
def pirxMember : CheckedMember := ⟨.axiomM, 0, .app (.const 3 []) (.const 1 []), none⟩

/-- the control over a type: `B : Type` at `5`. -/
def pirBMember : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩

/-- an element `: B`: `b₁` at `6`, `b₂` at `7`. -/
def pirbMember : CheckedMember := ⟨.axiomM, 0, .const 5 [], none⟩

/-- `G : B → Type` at `8`. -/
def pirGMember : CheckedMember := ⟨.axiomM, 0, .pi (.const 5 []) (.sort (.succ .zero)), none⟩

/-- `y : G b₁` at `9`. -/
def piryMember : CheckedMember := ⟨.axiomM, 0, .app (.const 8 []) (.const 6 []), none⟩

def pirEnv : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv (extendEnv (extendEnv (extendEnv (extendEnv (extendEnv (extendEnv
    (extendEnv emptyEnv 0 pirQMember) 1 pirqMember) 2 pirqMember) 3 pirFMember) 4 pirxMember)
    5 pirBMember) 6 pirbMember) 7 pirbMember) 8 pirGMember) 9 piryMember

/-- ARM (3): `x : F q₂`. Application congruence compares the arguments `q₁` and `q₂` at `Q`. The
    checker types `Q` at `Sort 0` and both proofs at `Q`, so they convert (`ConvT.irr`).

    BEFORE (`2701fd3914`):
    `#eval (tyAtC pirEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome`
    `-- false` -/
theorem pir_admits : (tyAtC pirEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).isSome = true :=
  rfl

/-- the checker's answer: a derivation of `x : F q₂`. -/
def pirTyT : HasTyT pirEnv 0 [] (.const 4 []) (.app (.const 3 []) (.const 2 [])) :=
  (tyAtC pirEnv 0 4 [] (.const 4 []) (.app (.const 3 []) (.const 2 []))).get pir_admits

/-- CONTROL, refused at fuel 4 and at fuel 16: `y : G b₂`. `B : Type` is not a proposition, so arm (3)
    does not apply at `B`, and no other arm relates the two axioms `b₁` and `b₂`. It was refused before
    as well (`#eval` at `2701fd3914`: `false`). -/
theorem pir_refuses :
    (tyAtC pirEnv 0 4 [] (.const 9 []) (.app (.const 8 []) (.const 7 []))).isSome = false ∧
    (tyAtC pirEnv 0 16 [] (.const 9 []) (.app (.const 8 []) (.const 7 []))).isSome = false :=
  ⟨rfl, rfl⟩

/-! ## the measured case: `srcEnvV1` -/

section
open Rcic.Scm.SrcTV (srcEnvV1 mCctI64Pf mI64Ref mVb0 mBoundBool cst cctE mkRefE vaE mkBoundE)

/-- `cctI64Pf`'s value (slot `35`): `cctI digestI daI`. -/
def srcCctValue : Expr Nat := .app (.app (.const 26 []) (.const 18 [])) (.const 22 [])

/-- `vb0`'s value (slot `45`): `vaB0 boolRef cctBoolPf`. -/
def srcVbValue : Expr Nat := .app (.app (.const 43 []) (.const 32 [])) (.const 36 [])

/-- THE CASE, read off the member table. `cctI64Pf` is stated at `CCT i64Ref bytesI`, and its value's
    type is `CCT (mkRef 3 16 digestI) bytesI`, where `i64Ref := mkRef 3 16 digestI`. `vb0` is stated at
    `ValueAt boundBool bytesB0`, and its value's type is `ValueAt (mkBound boolRef bytesB cctBoolPf)
    bytesB0`, where `boundBool := mkBound boolRef bytesB cctBoolPf`. -/
theorem srcCct_shape :
    srcEnvV1.members 35 = some mCctI64Pf ∧ mCctI64Pf.body = some srcCctValue ∧
    mCctI64Pf.mtype = cctE (cst 31) (cst 12) ∧ mI64Ref.body = some (mkRefE 3 16 (cst 18)) ∧
    inferC srcEnvV1 0 4 [] srcCctValue = some (cctE (mkRefE 3 16 (cst 18)) (cst 12)) ∧
    srcEnvV1.members 45 = some mVb0 ∧ mVb0.body = some srcVbValue ∧
    mVb0.mtype = vaE (cst 40) (cst 16) ∧ mBoundBool.body = some (mkBoundE (cst 32) (cst 13) (cst 36)) ∧
    inferC srcEnvV1 0 4 [] srcVbValue = some (vaE (mkBoundE (cst 32) (cst 13) (cst 36)) (cst 16)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ARM (1) ON THE MEASURED CASE: both values check at their stated types, with δ inside an argument.

    BEFORE (`2701fd3914`):
    `#eval (tyAtC srcEnvV1 0 4 [] srcCctValue mCctI64Pf.mtype).isSome`
    `-- false`
    `#eval (tyAtC srcEnvV1 0 4 [] srcVbValue mVb0.mtype).isSome`
    `-- false` -/
theorem srcCct_admits :
    (tyAtC srcEnvV1 0 4 [] srcCctValue mCctI64Pf.mtype).isSome = true ∧
    (tyAtC srcEnvV1 0 4 [] srcVbValue mVb0.mtype).isSome = true :=
  ⟨rfl, rfl⟩

end

end Rcic.Declarative

#print axioms Rcic.Declarative.apc_admits
#print axioms Rcic.Declarative.apcTyT
#print axioms Rcic.Declarative.apc_refuses
#print axioms Rcic.Declarative.lex_admits
#print axioms Rcic.Declarative.lexTyT
#print axioms Rcic.Declarative.lex_refuses
#print axioms Rcic.Declarative.pir_admits
#print axioms Rcic.Declarative.pirTyT
#print axioms Rcic.Declarative.pir_refuses
#print axioms Rcic.Declarative.srcCct_shape
#print axioms Rcic.Declarative.srcCct_admits
