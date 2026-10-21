import rcic.RcicTypedConv
import rcic.RcicTypedScopeCheckPins

/-!
# W-3 pins — the checker with conversion, calibrated, and a group only it admits

* Calibration on answers computed by hand (`conv_calibration`): δ and β on a binder's type, a level
  equality at a sort, β on an argument's type, δ at a level instance; and four refusals the conversion
  must not rescue.
* `Box`, a family whose parameter's type is an annotation wrapper (`wrap Type`, `wrap := λ α, α`), as
  Lean writes `outParam`. Its constructor's field `x : α` is a type only after δ and β. The reader and
  the test with the conversion checker build its scope (`boxInScopeT`). With the syntactic checker there
  is no reading, and the test refuses the reading the conversion checker gives (`box_syntactic_refused`).
  The same group with an axiom in place of the definition is refused by both (`boxAx_refused`).
* `Box` needs two head steps, δ then β: refused at fuel 1, passed at fuel 2 (`box_fuel`).
* A numeral is typed through its expansion by both checkers (`lit_calibration`). A group whose result index
  is a numeral passes (`lit_passes`); over the family alone, without the profile's `zero` and `succ`, it
  has no reading (`lit_needs_profile`).
* At W-2's seven pins the conversion checker reads the same skeletons (`pins_conv_agree`), and W-2's three
  teeth stand with it (`teeth_conv`).
* Row 1 in the ledger's form (a chain of type conversions as premise) is consumed at Vec's environment
  through the test (`vecEnv_sortsChain_notConv_ofCheck`).
* W-4: `Mir`, whose constructor writes its parameter's type under the wrapper. The reader reads the
  mirror off the constructor (`mirSkel_mirror`); the test converts it to the parameter and passes
  (`mir_passes`, `mirInScopeT`). The mirror check alone: refused as written, converted with conversion, and
  `Sort 2` against `Sort 1` refused by both (`mir_mirrors`).
-/

namespace Rcic.Declarative

open PosList

/-! ## calibration -/

/-- `wrap1 : Sort 1 → Sort 1 := λ α, α`, a definition of arity 0 (00 §20.6). -/
def calWrap1Env : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.definitionM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)),
    some (.lam (.sort (.succ .zero)) (.bvar 0))⟩

/-- the same type as an axiom: no body, never unfolded. -/
def calWrapAxEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.axiomM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩

/-- `wrap.{u} : Sort u → Sort u := λ α, α`, at a level parameter. -/
def calWrapPolyEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 ⟨.definitionM, 1, .pi (.sort (.param 0)) (.sort (.param 0)),
    some (.lam (.sort (.param 0)) (.bvar 0))⟩

/-- `R : Prop`, then `r : (λ (X : Prop), X) R`, innermost first. -/
def calBetaCtx : LCtx :=
  [.assumption (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)), .assumption (.sort .zero)]

/-- CALIBRATION: eight cases computed by hand, four of them refusals. Each case the conversion
    checker answers, the syntactic checker refuses.
    - `Π (x : wrap1 Prop), x : Sort (imax 1 0)`: the codomain's type `wrap1 Prop` is `Prop` after δ and
      β.
    - `(λ (x : Sort (max 1 0)), x) Prop : Sort (max 1 0)`: the argument's type `Sort 1` is the domain up
      to `decEqN`.
    - `(λ (q : R), q) r : R`: the argument's type `(λ X, X) R` is `R` after β.
    - `Π (x : wrap.{1} Prop), x : Sort (imax 1 0)`: δ instantiates the body's level parameter.
    - `(λ (x : Sort 2), x) Prop`: refused, `Sort 1` is not `Sort 2`.
    - `Π (x : wrapAx Prop), x`: refused, an axiom is not unfolded.
    - `Π (x : wrap1 Prop), x` with no fuel: refused, the syntactic checker's answer.
    - `(λ (f : Prop → Prop), f) (λ (x : Prop), Prop)`: refused, the codomains `Sort 1` and `Prop`
      differ. -/
theorem conv_calibration :
    inferC calWrap1Env 0 4 [] (.pi (.app (.const 0 []) (.sort .zero)) (.bvar 0)) =
      some (.sort (.imax (.succ .zero) .zero)) ∧
    inferT calWrap1Env 0 [] (.pi (.app (.const 0 []) (.sort .zero)) (.bvar 0)) = none ∧
    inferC emptyEnv 0 4 [] (.app (.lam (.sort (.max (.succ .zero) .zero)) (.bvar 0)) (.sort .zero)) =
      some (.sort (.max (.succ .zero) .zero)) ∧
    inferT emptyEnv 0 [] (.app (.lam (.sort (.max (.succ .zero) .zero)) (.bvar 0)) (.sort .zero)) = none ∧
    inferC emptyEnv 0 4 calBetaCtx (.app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)) = some (.bvar 1) ∧
    inferT emptyEnv 0 calBetaCtx (.app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)) = none ∧
    inferC calWrapPolyEnv 1 4 [] (.pi (.app (.const 0 [.succ .zero]) (.sort .zero)) (.bvar 0)) =
      some (.sort (.imax (.succ .zero) .zero)) ∧
    inferC emptyEnv 0 4 [] (.app (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) (.sort .zero)) = none ∧
    inferC calWrapAxEnv 0 4 [] (.pi (.app (.const 0 []) (.sort .zero)) (.bvar 0)) = none ∧
    inferC calWrap1Env 0 0 [] (.pi (.app (.const 0 []) (.sort .zero)) (.bvar 0)) = none ∧
    inferC emptyEnv 0 4 []
      (.app (.lam (.pi (.sort .zero) (.sort .zero)) (.bvar 0)) (.lam (.sort .zero) (.sort .zero))) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `Box`: a group only the conversion checker admits -/

/-- `wrap : Sort 2 → Sort 2 := λ α, α` at `0`, arity 0. -/
def boxWrapMember : CheckedMember :=
  ⟨.definitionM, 0, .pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero))),
    some (.lam (.sort (.succ (.succ .zero))) (.bvar 0))⟩

/-- the same type as an axiom. -/
def boxWrapAxMember : CheckedMember :=
  ⟨.axiomM, 0, .pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero))), none⟩

def boxBase : ResolvedEnv := extendEnv emptyEnv 0 boxWrapMember
def boxAxBase : ResolvedEnv := extendEnv emptyEnv 0 boxWrapAxMember

/-- `wrap Type`, the parameter's type. -/
def boxParamTy : Expr Nat := .app (.const 0 []) (.sort (.succ .zero))

/-- `Box : Π (α : wrap Type), Type` at `1`. -/
def boxFamMember : CheckedMember := ⟨.inductiveM, 0, .pi boxParamTy (.sort (.succ .zero)), none⟩

/-- `Box.mk : Π (α : wrap Type) (x : α), Box α` at `2`. -/
def boxMkMember : CheckedMember :=
  ⟨.constructorM, 0, .pi boxParamTy (.pi (.bvar 0) (.app (.const 1 []) (.bvar 1))), none⟩

/-- `Box.rec` at `3`, eliminating into any sort: the views' recursor type. -/
def boxRecMember : CheckedMember :=
  ⟨.recursorM, 1,
    recTypeT 1 [] [(boxParamTy, .succ (.succ .zero))] [] (.param 0) [(2, [.plain (.bvar 0) (.succ .zero)], [])],
    none⟩

/-- the conversion checker's skeleton of `Box`. -/
def boxSkel : Option GroupSkelT := groupSkel? (convChecker 4) boxBase 8 1 boxFamMember [(2, boxMkMember)] boxRecMember 1

/-- the skeleton is the one written by hand: the parameter at level 2, the field `x : α` plain at level 1,
    eliminating into any sort. -/
theorem boxSkel_syntax :
    boxSkel.map GroupSkelT.syntax =
      some ([(boxParamTy, .succ (.succ .zero))], [], .succ .zero,
        [([(boxParamTy, .succ (.succ .zero))], [.plain (.bvar 0) (.succ .zero)], [])], .anySort) := rfl

theorem box_passes :
    groupCheckB (convChecker 4) boxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember (boxSkel.get rfl) = true :=
  rfl

/-- CALIBRATION: `Box` needs two head steps, δ then β. With one it is refused; with two it passes. -/
theorem box_fuel :
    groupCheckB (convChecker 1) boxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember (boxSkel.get rfl) = false ∧
    groupCheckB (convChecker 2) boxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember (boxSkel.get rfl) = true :=
  ⟨rfl, rfl⟩

/-- `Box` in the copy's scope, built by the test: no view written by hand, every typing the conversion
    checker's. -/
def boxInScopeT : GroupInScopeT boxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember :=
  groupInScopeT_of_check _ (by decide) box_passes

/-- TOOTH: with the syntactic checker there is no reading, and the test refuses the conversion
    checker's: the field's type `α` is a type only after δ and β. -/
theorem box_syntactic_refused :
    groupSkel? synChecker boxBase 8 1 boxFamMember [(2, boxMkMember)] boxRecMember 1 = none ∧
    groupCheckB synChecker boxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember (boxSkel.get rfl) = false :=
  ⟨rfl, rfl⟩

/-- TOOTH: with an axiom in place of the definition, the conversion checker has no reading either, and
    refuses its own reading of `Box`. -/
theorem boxAx_refused :
    groupSkel? (convChecker 4) boxAxBase 8 1 boxFamMember [(2, boxMkMember)] boxRecMember 1 = none ∧
    groupCheckB (convChecker 4) boxAxBase 1 boxFamMember [(2, boxMkMember)] 3 boxRecMember (boxSkel.get rfl) =
      false := ⟨rfl, rfl⟩

/-! ## numerals -/

/-- CALIBRATION: a numeral is typed through its expansion (`HasTyT.lit`), by both checkers. In Nat's
    environment, `2 : N`. With only the family at `0`, and no `zero` and `succ` at `1` and `2`, it has
    no typing. -/
theorem lit_calibration :
    inferT natEnvU 0 [] (.lit 2) = some (.const 0 []) ∧
    inferC natEnvU 0 4 [] (.lit 2) = some (.const 0 []) ∧
    inferT (extendEnv emptyEnv 0 natFamMember) 0 [] (.lit 2) = none :=
  ⟨rfl, rfl, rfl⟩

/-- `Lit : N → Type` at `4` over Nat, with `mk : Lit 2` at `5`: a result index that is a numeral. -/
def litFamMember : CheckedMember := ⟨.inductiveM, 0, .pi (.const 0 []) (.sort (.succ .zero)), none⟩
def litMkMember : CheckedMember := ⟨.constructorM, 0, .app (.const 4 []) (.lit 2), none⟩
def litRecMember : CheckedMember :=
  ⟨.recursorM, 1, recTypeT 4 [] [] [(.const 0 [], .succ .zero)] (.param 0) [(5, [], [.lit 2])], none⟩

/-- the group passes with either checker: the result index `2` is typed at `N` through its expansion. -/
theorem lit_passes :
    groupCheckB synChecker natEnvU 4 litFamMember [(5, litMkMember)] 6 litRecMember
      ((groupSkel? synChecker natEnvU 8 4 litFamMember [(5, litMkMember)] litRecMember 0).get rfl) = true ∧
    groupCheckB (convChecker 4) natEnvU 4 litFamMember [(5, litMkMember)] 6 litRecMember
      ((groupSkel? (convChecker 4) natEnvU 8 4 litFamMember [(5, litMkMember)] litRecMember 0).get rfl) = true :=
  ⟨rfl, rfl⟩

/-- TOOTH: over the family alone, the numeral has no typing and the group no reading. -/
theorem lit_needs_profile :
    groupSkel? (convChecker 4) (extendEnv emptyEnv 0 natFamMember) 8 4 litFamMember [(5, litMkMember)]
      litRecMember 0 = none := rfl

/-! ## mirrors up to conversion (W-4) -/

/-- `Mir : Π (α : Type), Type` at `1` over `wrap` at `0`, with `mk : Π (α : wrap Type), Mir α` at `2`:
    the constructor's mirror is the parameter's type under the wrapper (05 §6.1 allows it). -/
def mirFamMember : CheckedMember := ⟨.inductiveM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩
def mirMkMember : CheckedMember := ⟨.constructorM, 0, .pi boxParamTy (.app (.const 1 []) (.bvar 0)), none⟩
def mirRecMember : CheckedMember :=
  ⟨.recursorM, 1, recTypeT 1 [] [(.sort (.succ .zero), .succ (.succ .zero))] [] (.param 0) [(2, [], [])], none⟩

def mirSkel : Option GroupSkelT :=
  groupSkel? (convChecker 4) boxBase 8 1 mirFamMember [(2, mirMkMember)] mirRecMember 1

/-- the reader reads the mirror off the constructor, at the parameter's level. -/
theorem mirSkel_mirror :
    mirSkel.map (fun sk => sk.ctors.map CtorSkelT.mirrors) = some [[(boxParamTy, .succ (.succ .zero))]] := rfl

theorem mir_passes :
    groupCheckB (convChecker 4) boxBase 1 mirFamMember [(2, mirMkMember)] 3 mirRecMember (mirSkel.get rfl) = true :=
  rfl

/-- `Mir` in the copy's scope, its mirror converted to the parameter. -/
def mirInScopeT : GroupInScopeT boxBase 1 mirFamMember [(2, mirMkMember)] 3 mirRecMember :=
  groupInScopeT_of_check _ (by decide) mir_passes

/-- TOOTH: the mirror check alone. The syntactic checker refuses the wrapped mirror; the conversion
    checker converts it; and no checker converts `Sort 2` to the parameter `Sort 1`. -/
theorem mir_mirrors :
    mirrorsCheckB synChecker boxBase 0 [] [(boxParamTy, .succ (.succ .zero))]
      [(.sort (.succ .zero), .succ (.succ .zero))] = false ∧
    mirrorsCheckB (convChecker 4) boxBase 0 [] [(boxParamTy, .succ (.succ .zero))]
      [(.sort (.succ .zero), .succ (.succ .zero))] = true ∧
    mirrorsCheckB (convChecker 4) boxBase 0 [] [(.sort (.succ (.succ .zero)), .succ (.succ .zero))]
      [(.sort (.succ .zero), .succ (.succ .zero))] = false :=
  ⟨rfl, rfl, rfl⟩

/-! ## W-2's seven pins with the conversion checker -/

/-- CALIBRATION against W-2: at the seven pins the conversion checker reads the syntactic checker's
    skeletons, and they pass its test. -/
theorem pins_conv_agree :
    groupSkel? (convChecker 4) emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU 0 =
      groupSkel? synChecker emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU 0 ∧
    groupSkel? (convChecker 4) emptyEnv 8 0 falseFamMember [] falseRecMemberU 0 =
      groupSkel? synChecker emptyEnv 8 0 falseFamMember [] falseRecMemberU 0 ∧
    groupSkel? (convChecker 4) emptyEnv 8 0 trueFamMember [(1, trueIntroMember)] trueRecMemberU 0 =
      groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, trueIntroMember)] trueRecMemberU 0 ∧
    groupSkel? (convChecker 4) emptyEnv 8 0 trueFamMember [(1, structMkMember)] structRecMemberU 0 =
      groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, structMkMember)] structRecMemberU 0 ∧
    groupSkel? (convChecker 4) emptyEnv 8 0 andFamMember [(1, andIntroMember)] andRecMemberU 2 =
      groupSkel? synChecker emptyEnv 8 0 andFamMember [(1, andIntroMember)] andRecMemberU 2 ∧
    groupSkel? (convChecker 4) natEnvU 8 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] listURecMember 1 =
      groupSkel? synChecker natEnvU 8 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] listURecMember 1 ∧
    groupSkel? (convChecker 4) natEnvU 8 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] vecRecMemberU 1 =
      groupSkel? synChecker natEnvU 8 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] vecRecMemberU 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- TEETH: W-2's three refusals stand with the conversion checker. Its derivations are in the
    environment it is given, so the family still has no typing in the base; `Loop` eliminating into any
    sort is still refused by its profile alone; a negative occurrence still has no reading. -/
theorem teeth_conv :
    ctorCheckB (convChecker 4) emptyEnv 0 natFamMember
      ((groupSkel? (convChecker 4) emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU
        0).get rfl)
      (2, natSuccMember) ⟨[], [.plain (.const 0 []) (.succ .zero)], [], .imax (.succ .zero) (.succ .zero)⟩ = false ∧
    (groupSkel? (convChecker 4) emptyEnv 8 0 loopFamMember [(1, loopMkMember)] loopRecAnyMember 0).map
      (fun sk => (famCheckB (convChecker 4) emptyEnv loopFamMember sk,
        ctorsCheckB (convChecker 4) emptyEnv 0 loopFamMember sk [(1, loopMkMember)] sk.ctors,
        recCheckB (convChecker 4) emptyEnv 0 loopFamMember [(1, loopMkMember)] 2 loopRecAnyMember sk,
        profileCheckB (convChecker 4) sk)) = some (true, true, true, false) ∧
    groupSkel? (convChecker 4) emptyEnv 8 0 natFamMember [(1, negMkMember)] natRecMemberU 0 = none :=
  ⟨rfl, rfl, rfl⟩

/-- ROW 1 in the ledger's form, consumed at Vec's environment through the test: no chain of type
    conversions joins `Sort 0` and `Sort 1` there. -/
theorem vecEnv_sortsChain_notConv_ofCheck {n : Nat} (h : TyConvT vecEnvUT n [] (.sort .zero) (.sort (.succ .zero))) :
    False :=
  refutEqN_zero_succ_false ((typedRowsWf_of_scopeCheck vecEnvUWfT vecEnvUWfT_scopeCheck n).sortRow .nil h)

end Rcic.Declarative

#print axioms Rcic.Declarative.conv_calibration
#print axioms Rcic.Declarative.boxSkel_syntax
#print axioms Rcic.Declarative.box_passes
#print axioms Rcic.Declarative.box_fuel
#print axioms Rcic.Declarative.boxInScopeT
#print axioms Rcic.Declarative.box_syntactic_refused
#print axioms Rcic.Declarative.boxAx_refused
#print axioms Rcic.Declarative.lit_calibration
#print axioms Rcic.Declarative.lit_passes
#print axioms Rcic.Declarative.lit_needs_profile
#print axioms Rcic.Declarative.mirSkel_mirror
#print axioms Rcic.Declarative.mir_passes
#print axioms Rcic.Declarative.mirInScopeT
#print axioms Rcic.Declarative.mir_mirrors
#print axioms Rcic.Declarative.pins_conv_agree
#print axioms Rcic.Declarative.teeth_conv
#print axioms Rcic.Declarative.vecEnv_sortsChain_notConv_ofCheck
