import rcic.RcicTypedScopeCheck
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec

/-!
# W-2 pins — the seven hand-written scopes, derived

At each of the seven environments whose views were written by hand (Nat, `False`, `True`, `S`, `And`,
List, Vec), the reader's skeleton passes the test, so each is in the copy's scope with no view written by
hand (`*_scopeCheck`, `*_inScope_ofCheck`). The skeletons are the syntax of the hand-written views,
levels included (`pins_skeletons_agree`). Row 1 is consumed at Vec's and List's environments through the
test (`vecEnv_sorts_notConv_ofCheck`, `listEnv_sorts_notConv_ofCheck`).

Vec is an indexed family. Its recursive field sits at an index, and its result index follows that field.
The checker types the index and the result index in the plain context directly, so Vec needs no context
strengthening.

Teeth:
* `Loop : Prop` with `mk : Loop → Loop`, eliminating into any sort, is read, typed and built, and refused
  by its profile alone (`loopAny_refused_by_profile`). Eliminating into `Prop` only, it passes
  (`loopProp_passes`).
* `succ`'s field written as a plain field gives the same constructor type. The test refuses it: the
  family has no typing in the base (`natSucc_plainField_refused`).
* A negative occurrence has no reading (`neg_unread`).
-/

namespace Rcic.Declarative

open PosList

/-! ## the checker, calibrated on answers computed by hand -/

/-- an axiom with one universe parameter: `C.{u} : Sort u`. -/
def calAxiomEnv : ResolvedEnv := extendEnv emptyEnv 0 ⟨.axiomM, 1, .sort (.param 0), none⟩

/-- CALIBRATION: eight cases computed by hand, five of them refusals.
    - `Π (P : Prop), P : Sort (imax 1 0)`.
    - `λ (A : Prop) (x : A), x : Π (A : Prop), Π (x : A), A`, the result's `A` one binder deeper.
    - `Prop Prop`: refused, the head's type is a sort.
    - `(λ (x : Prop), x) y` with `y : Type`: refused, the argument's type is not the domain.
    - an absent constant: refused.
    - `C` at no universe: refused. `C.{u}` at level parameter `u`: `Sort u`.
    - `C.{u}` with no level parameter in scope: refused. -/
theorem checker_calibration :
    inferT emptyEnv 0 [] (.pi (.sort .zero) (.bvar 0)) = some (.sort (.imax (.succ .zero) .zero)) ∧
    inferT emptyEnv 0 [] (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))) =
      some (.pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))) ∧
    inferT emptyEnv 0 [] (.app (.sort .zero) (.sort .zero)) = none ∧
    inferT emptyEnv 0 [.assumption (.sort (.succ .zero))] (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) = none ∧
    inferT emptyEnv 0 [] (.const 7 []) = none ∧
    inferT calAxiomEnv 1 [] (.const 0 []) = none ∧
    inferT calAxiomEnv 1 [] (.const 0 [.param 0]) = some (.sort (.param 0)) ∧
    inferT calAxiomEnv 0 [] (.const 0 [.param 0]) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## pins: the seven hand-written scopes, derived -/

theorem natEnvUWfT_scopeCheck : natEnvUWfT.ScopeCheck :=
  ⟨trivial, synChecker,
    (groupSkel? synChecker emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU 0).get rfl,
    rfl, by decide⟩

theorem falseEnvUWfT_scopeCheck : falseEnvUWfT.ScopeCheck :=
  ⟨trivial, synChecker, (groupSkel? synChecker emptyEnv 8 0 falseFamMember [] falseRecMemberU 0).get rfl, rfl, by decide⟩

theorem trueEnvUWfT_scopeCheck : trueEnvUWfT.ScopeCheck :=
  ⟨trivial, synChecker,
    (groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, trueIntroMember)] trueRecMemberU 0).get rfl, rfl, by decide⟩

theorem structEnvUWfT_scopeCheck : structEnvUWfT.ScopeCheck :=
  ⟨trivial, synChecker,
    (groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, structMkMember)] structRecMemberU 0).get rfl, rfl, by decide⟩

theorem andEnvUWfT_scopeCheck : andEnvUWfT.ScopeCheck :=
  ⟨trivial, synChecker,
    (groupSkel? synChecker emptyEnv 8 0 andFamMember [(1, andIntroMember)] andRecMemberU 2).get rfl, rfl, by decide⟩

theorem listEnvUWfT_scopeCheck : listEnvUWfT.ScopeCheck :=
  ⟨natEnvUWfT_scopeCheck, synChecker,
    (groupSkel? synChecker natEnvU 8 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] listURecMember 1).get rfl,
    rfl, by decide⟩

theorem vecEnvUWfT_scopeCheck : vecEnvUWfT.ScopeCheck :=
  ⟨natEnvUWfT_scopeCheck, synChecker,
    (groupSkel? synChecker natEnvU 8 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] vecRecMemberU 1).get rfl,
    rfl, by decide⟩

theorem natEnvUWfT_inScope_ofCheck : natEnvUWfT.InScope := natEnvUWfT.inScope_of_scopeCheck natEnvUWfT_scopeCheck
theorem falseEnvUWfT_inScope_ofCheck : falseEnvUWfT.InScope :=
  falseEnvUWfT.inScope_of_scopeCheck falseEnvUWfT_scopeCheck
theorem trueEnvUWfT_inScope_ofCheck : trueEnvUWfT.InScope := trueEnvUWfT.inScope_of_scopeCheck trueEnvUWfT_scopeCheck
theorem structEnvUWfT_inScope_ofCheck : structEnvUWfT.InScope :=
  structEnvUWfT.inScope_of_scopeCheck structEnvUWfT_scopeCheck
theorem andEnvUWfT_inScope_ofCheck : andEnvUWfT.InScope := andEnvUWfT.inScope_of_scopeCheck andEnvUWfT_scopeCheck
theorem listEnvUWfT_inScope_ofCheck : listEnvUWfT.InScope := listEnvUWfT.inScope_of_scopeCheck listEnvUWfT_scopeCheck
theorem vecEnvUWfT_inScope_ofCheck : vecEnvUWfT.InScope := vecEnvUWfT.inScope_of_scopeCheck vecEnvUWfT_scopeCheck

/-- ROW 1 consumed at Vec's environment through the test: `Sort 0` and `Sort 1` are not convertible
    there. No view of Vec is written by hand on this path. -/
theorem vecEnv_sorts_notConv_ofCheck {n : Nat} {T : Expr Nat}
    (h : ConvT vecEnvUT n [] (.sort .zero) (.sort (.succ .zero)) T) : False :=
  refutEqN_zero_succ_false (sortConvCharT_scopeCheck vecEnvUWfT vecEnvUWfT_scopeCheck .nil h)

/-- ROW 1 consumed at List's environment (Nat, then List) through the test. -/
theorem listEnv_sorts_notConv_ofCheck {n : Nat} {T : Expr Nat}
    (h : ConvT listEnvUT n [] (.sort .zero) (.sort (.succ .zero)) T) : False :=
  refutEqN_zero_succ_false (sortConvCharT_scopeCheck listEnvUWfT listEnvUWfT_scopeCheck .nil h)

/-! ## teeth -/

/-- `Loop : Prop` with `mk : Loop → Loop` (O1-c-0's shape), its recursor built from its views at a
    motive level `w`. -/
def loopFamMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def loopMkMember : CheckedMember := ⟨.constructorM, 0, .pi (.const 0 []) (.const 0 []), none⟩
def loopRecTypeAt (w : Level) : Expr Nat := recTypeT 0 [] [] [] w [(1, [.drec []], [])]
def loopRecAnyMember : CheckedMember := ⟨.recursorM, 1, loopRecTypeAt (.param 0), none⟩
def loopRecPropMember : CheckedMember := ⟨.recursorM, 0, loopRecTypeAt .zero, none⟩

/-- TOOTH: Loop eliminating into any sort is read, typed and built, and refused by its profile alone. -/
theorem loopAny_refused_by_profile :
    (groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)] loopRecAnyMember 0).map
      (fun sk => (famCheckB synChecker emptyEnv loopFamMember sk,
        ctorsCheckB synChecker emptyEnv 0 loopFamMember sk [(1, loopMkMember)] sk.ctors,
        recCheckB synChecker emptyEnv 0 loopFamMember [(1, loopMkMember)] 2 loopRecAnyMember sk,
        profileCheckB synChecker sk)) =
      some (true, true, true, false) := rfl

/-- … and eliminating into `Prop` only, it passes. -/
theorem loopProp_passes :
    groupCheckB synChecker emptyEnv 0 loopFamMember [(1, loopMkMember)] 2 loopRecPropMember
      ((groupSkel? synChecker emptyEnv 8 0 loopFamMember [(1, loopMkMember)] loopRecPropMember 0).get rfl) = true := rfl

/-- TOOTH: the family cannot pass as a plain field. `succ`'s field written as a plain field gives the
    same constructor type, but the family has no typing in the base. -/
theorem natSucc_plainField_refused :
    ctorCheckB synChecker emptyEnv 0 natFamMember
      ((groupSkel? synChecker emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU 0).get rfl)
      (2, natSuccMember) ⟨[], [.plain (.const 0 []) (.succ .zero)], [], .imax (.succ .zero) (.succ .zero)⟩ = false ∧
    natSuccMember.mtype = ctorTypeT 0 [] [] [.plain (.const 0 []) (.succ .zero)] [] := ⟨rfl, rfl⟩

/-- TOOTH: a negative occurrence has no reading: the field mentions the family and is no recursive
    field. -/
def negMkMember : CheckedMember := ⟨.constructorM, 0, .pi (.pi (.const 0 []) (.const 0 [])) (.const 0 []), none⟩
theorem neg_unread : groupSkel? synChecker emptyEnv 8 0 natFamMember [(1, negMkMember)] natRecMemberU 0 = none := rfl

/-! ## the reader recovers the hand-written views -/

/-- a skeleton's syntax: the family's telescope and sort, each constructor's mirrors, fields and
    result indices in candidate order, the elimination policy. -/
def GroupSkelT.syntax (sk : GroupSkelT) :=
  (sk.params, sk.indices, sk.sort, sk.ctors.map (fun k => (k.mirrors, k.fields, k.res)), sk.elim)

/-- the same syntax read off a scope. -/
def GroupInScopeT.syntax {E : ResolvedEnv} {f : Nat} {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    {rr : Nat} {rm : CheckedMember} (g : GroupInScopeT E f fm ctors rr rm) :=
  (g.fv.params, g.fv.indices, g.fv.sort,
    g.cs.reverse.map (fun c => (c.view.mirrors, c.view.fields, c.view.res)), g.grec.elim)

/-- CALIBRATION: at each of the seven pins, the skeleton read off the members is the syntax of the
    views written by hand (M3-e-2, M3-e-4, M3-e-5, O1-a, O1-b-2, W-1 (e-3)). -/
theorem pins_skeletons_agree :
    (groupSkel? synChecker emptyEnv 8 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] natRecMemberU 0).map
      GroupSkelT.syntax = some natInScopeT.syntax ∧
    (groupSkel? synChecker emptyEnv 8 0 falseFamMember [] falseRecMemberU 0).map GroupSkelT.syntax =
      some falseInScopeT.syntax ∧
    (groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, trueIntroMember)] trueRecMemberU 0).map GroupSkelT.syntax =
      some trueInScopeT.syntax ∧
    (groupSkel? synChecker emptyEnv 8 0 trueFamMember [(1, structMkMember)] structRecMemberU 0).map GroupSkelT.syntax =
      some structInScopeT.syntax ∧
    (groupSkel? synChecker emptyEnv 8 0 andFamMember [(1, andIntroMember)] andRecMemberU 2).map GroupSkelT.syntax =
      some andInScopeT.syntax ∧
    (groupSkel? synChecker natEnvU 8 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] listURecMember 1).map
      GroupSkelT.syntax = some listInScopeT.syntax ∧
    (groupSkel? synChecker natEnvU 8 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] vecRecMemberU 1).map
      GroupSkelT.syntax = some vecInScopeT.syntax :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.checker_calibration
#print axioms Rcic.Declarative.natEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.falseEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.trueEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.structEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.andEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.listEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.vecEnvUWfT_scopeCheck
#print axioms Rcic.Declarative.natEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.falseEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.trueEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.structEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.andEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.listEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.vecEnvUWfT_inScope_ofCheck
#print axioms Rcic.Declarative.vecEnv_sorts_notConv_ofCheck
#print axioms Rcic.Declarative.listEnv_sorts_notConv_ofCheck
#print axioms Rcic.Declarative.loopAny_refused_by_profile
#print axioms Rcic.Declarative.loopProp_passes
#print axioms Rcic.Declarative.natSucc_plainField_refused
#print axioms Rcic.Declarative.neg_unread
#print axioms Rcic.Declarative.pins_skeletons_agree
