import rcic.RcicF8OMEtaKAnnot

/-! Actual, well-typed original forks. Distinct Pi annotations and a nonempty
untouched frame test the exact caller/index. Equal fields retain multiplicity.
No global X is implemented by the fixture. closure_claim=0. -/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.EtaKAnnot.Pins

abbrev A : Expr Nat := .sort .zero
abbrev A' : Expr Nat := .sort (.max .zero .zero)
abbrev B : Expr Nat := .sort .zero
abbrev piL : Expr Nat := .pi A B
abbrev piR : Expr Nat := .pi A' B
abbrev term : Expr Nat := .lam A (.bvar 0)

def termTy : HasTyT emptyEnv 0 [] term piL :=
  .lam [] A (.succ .zero) (.bvar 0) B (.sort [] .zero)
    (.bvar [.assumption A] 0 B rfl)

def piConversion : ConvT emptyEnv 0 [] piL piR
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] A A' B B (.succ .zero) (.succ .zero)
    (.sorts [] .zero (.max .zero .zero) (fun _ => rfl))
    (.sorts [.assumption A] .zero .zero (fun _ => rfl))

def termTyR : HasTyT emptyEnv 0 [] term piR :=
  .conv [] term piL piR (.imax (.succ .zero) (.succ .zero)) termTy piConversion

def dL : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] term term piL :=
  .refl [] term piL termTy

def dR : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] term term piR :=
  .refl [] term piR termTyR

def cL : TyConvT emptyEnv 0 [] piL piL := .refl [] piL

def cR : TyConvT emptyEnv 0 [] piR piL :=
  .of [] piR piL (.imax (.succ .zero) (.succ .zero))
    (.symm [] piL piR (.sort (.imax (.succ .zero) (.succ .zero))) piConversion)

def frame : List (Jd emptyEnv 0) := [.ty (HasTyT.sort [] .zero)]

def request : EvTc (removedAtoms dL dR cL cR) [] piL piR :=
  annotRequest dL dR cL cR

theorem annotations_distinct : A ≠ A' := by decide

theorem actual_leaves : request.leaves = [.tc cL, .tc cR] := rfl

theorem actual_caller : callerAtoms dL dR cL cR frame =
    [.pr (.conv [] term term piL piL dL cL),
     .pr (.conv [] term term piR piL dR cR), .ty (HasTyT.sort [] .zero)] := rfl

theorem actual_edge :
    OM3_edge (callerAtoms dL dR cL cR frame) (request.leaves ++ frame) :=
  OM_etaK_annot dL dR cL cR frame

theorem actual_materialization :
    request.val (envClosed_of_envWfT EnvWfT.empty)
      (envWfT_subst_inst EnvWfT.empty) =
      TyConvT.trans [] piL piL piR cL cR.symmT := rfl

/-- Duplication is real multiplicity, not a deduplicated support set. -/
theorem repeated_field_leaves :
    (annotRequest dL dL cL cL).leaves = [.tc cL, .tc cL] := rfl

theorem repeated_field_edge :
    OM3_edge (callerAtoms dL dL cL cL frame)
      ((annotRequest dL dL cL cL).leaves ++ frame) :=
  OM_etaK_annot dL dL cL cL frame

/-- Exact LEFT binder index on X's codomain output; hX stays explicit. -/
theorem contracted_X_edge
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X) :
    let ans : EvTc (removedAtoms dL dR cL cR) [] A A' ×
      EvTc (removedAtoms dL dR cL cR) [.assumption A] B B :=
        X (removedAtoms dL dR cL cR) request
    OM3_edge (callerAtoms dL dR cL cR frame)
      ((ans.1.leaves ++ ans.2.leaves) ++ frame) :=
  X_outputs_edge dL dR cL cR X hX frame

end Rcic.Declarative.F8Measure.EtaKAnnot.Pins

#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.A
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.A'
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.B
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.piL
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.piR
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.term
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.termTy
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.piConversion
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.termTyR
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.dL
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.dR
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.cL
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.cR
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.frame
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.request
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.annotations_distinct
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.actual_leaves
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.actual_caller
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.actual_edge
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.actual_materialization
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.repeated_field_leaves
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.repeated_field_edge
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.Pins.contracted_X_edge
