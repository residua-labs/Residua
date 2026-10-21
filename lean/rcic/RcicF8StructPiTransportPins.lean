import rcic.RcicF8StructPiPins

/-! B3b reuse controls on wk/esub inputs. Extra literal inputs in the esub
fixture are explicitly named roots; no edge below the singleton SP-1 root is
claimed for that different fixture. -/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.SP1.TransportPins
open SP1.Pins

def wkLeft : EvTy input.removed [.assumption A'] (.pi A B) idx :=
  .wk (.assumption A') 0 input.leftOriginal
def wkRight : EvTy input.removed [.assumption A'] (.pi A' B) idx :=
  .wk (.assumption A') 0 input.rightOriginal

def wkExtract := extract wkLeft wkRight

theorem wk_support (x : Jd emptyEnv 0)
    (hx : x ∈ wkExtract.1.leaves ++ wkExtract.2.leaves) :
    ∃ y ∈ input.leftOriginal.leaves ++ input.rightOriginal.leaves, SubEq x y :=
  extract_leaves wkLeft wkRight x hx

def paramSort : HasTyT emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)

/-- The original fixture bundle includes the argument and its sort typing. -/
def testRoots : List (Jd emptyEnv 0) := input.removed ++ [.ty hA', .ty paramSort]

def rootIncl : ∀ x ∈ input.removed, x ∈ testRoots :=
  fun _ hx => List.mem_append.mpr (.inl hx)

def param : EvTy testRoots [] A' (.sort (.succ .zero)) :=
  .lit hA' ⟨_, .tail _ (.head _), .inl rfl⟩
def paramTy : EvTy testRoots [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .lit paramSort ⟨_, .tail _ (.tail _ (.head _)), .inl rfl⟩

def esubLeft : EvTy testRoots [] (.pi A B) idx :=
  .esub (t := .sort (.succ .zero)) (v := A') 0 (.succ (.succ .zero))
    (.wk (.assumption (.sort (.succ .zero))) 0 (input.leftOriginal.widen rootIncl))
    rfl param paramTy

def esubRight : EvTy testRoots [] (.pi A' B) idx :=
  .esub (t := .sort (.succ .zero)) (v := A') 0 (.succ (.succ .zero))
    (.wk (.assumption (.sort (.succ .zero))) 0 (input.rightOriginal.widen rootIncl))
    rfl param paramTy

def esubExtract := extract esubLeft esubRight

theorem esub_support (x : Jd emptyEnv 0)
    (hx : x ∈ esubExtract.1.leaves ++ esubExtract.2.leaves) :
    ∃ y ∈ esubLeft.leaves ++ esubRight.leaves, SubEq x y :=
  extract_leaves esubLeft esubRight x hx

theorem refl_keeps_typing_leaves : (EvCv.refl esubLeft).leaves = esubLeft.leaves := rfl

theorem refl_materializes :
    (EvCv.refl esubLeft).val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty) =
      ConvT.refl [] (.pi A B) idx
        (esubLeft.val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)) := rfl

theorem refl_size_exact : (EvCv.refl esubLeft).size = 1 + esubLeft.size := rfl

end Rcic.Declarative.F8Measure.SP1.TransportPins

#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.wkLeft
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.wkRight
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.wkExtract
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.wk_support
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.paramSort
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.testRoots
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.rootIncl
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.param
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.paramTy
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.esubLeft
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.esubRight
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.esubExtract
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.esub_support
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.refl_keeps_typing_leaves
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.refl_materializes
#print axioms Rcic.Declarative.F8Measure.SP1.TransportPins.refl_size_exact
