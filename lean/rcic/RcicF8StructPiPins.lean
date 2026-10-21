import rcic.RcicF8StructPiFront

/-! SP-1 pins. Distinct annotations and a dependent bvar codomain exercise
extraction and concrete binder transport. The complete nonempty producer pin
uses reflexive P replies; arbitrary P/H4 is not silently supplied. -/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.SP1.Pins

def l : Level := .max .zero .zero
def A : Expr Nat := .sort l
def A' : Expr Nat := .sort .zero
def B : Expr Nat := .bvar 0
def idx : Expr Nat := .sort (.imax (.succ l) .zero)
def hA : HasTyT emptyEnv 0 [] A (.sort (.succ l)) := .sort [] l
def hA' : HasTyT emptyEnv 0 [] A' (.sort (.succ .zero)) := .sort [] .zero
def domainConversion : ConvT emptyEnv 0 [] A A' (.sort (.succ l)) :=
  .sorts [] l .zero (fun _ => rfl)
def leftBody : HasTyT emptyEnv 0 [.assumption A] B (.sort .zero) :=
  .conv [.assumption A] B A A' (.succ l)
    (.bvar _ 0 A rfl) (.sorts _ l .zero (fun _ => rfl))
def rightBody : HasTyT emptyEnv 0 [.assumption A'] B (.sort .zero) :=
  .bvar _ 0 A' rfl
def leftPi : HasTyT emptyEnv 0 [] (.pi A B) idx :=
  .pi [] A (.succ l) B .zero hA leftBody
def rightPi : HasTyT emptyEnv 0 [] (.pi A' B) idx :=
  .conv [] (.pi A' B) (.sort (.imax (.succ .zero) .zero)) idx
    (.succ (.imax (.succ .zero) .zero))
    (.pi [] A' (.succ .zero) B .zero hA' rightBody)
    (.sorts [] (.imax (.succ .zero) .zero) (.imax (.succ l) .zero) (fun _ => rfl))

def input : Input emptyEnv 0 [] A B A' B idx :=
  ⟨.sort [] l .zero (fun _ => rfl), .bvar [.assumption A] 0, leftPi, rightPi⟩

theorem annotations_distinct : A ≠ A' := by decide
theorem dependent_body : B = .bvar 0 := rfl
theorem domain_index_exact : (domainRequest input).u = .succ l := by
  change (input.leftOriginal.invPiT rfl).u = _
  rw [EvTy.invPiT_agree input.leftOriginal rfl rfl]
  rfl
theorem right_domain_index_exact : (domainRequest input).v = .succ .zero := by
  change (input.rightOriginal.invPiT rfl).u = _
  rw [EvTy.invPiT_agree input.rightOriginal rfl rfl]
  rfl

def frame : List (Jd emptyEnv 0) := [.ty hA]
theorem original_domain_edge :
    OM3_edge (input.removed ++ frame) ((domainRequest input).leaves ++ frame) :=
  domain_edge input frame

/-- Original-only complete non-vacuity case. No global P processor supplied. -/
def sameInput : Input emptyEnv 0 [] A B A B idx :=
  ⟨.sort [] l l (fun _ => rfl), .bvar [.assumption A] 0, leftPi, leftPi⟩
def sameDom : EvCv sameInput.removed [] A A (.sort sameInput.leftView.u) :=
  .refl sameInput.leftView.hA
def sameCod : EvCv sameInput.removed [.assumption A] B B (.sort sameInput.leftView.v) :=
  .refl sameInput.leftView.hB

theorem sameDom_supported : Supported sameDom.leaves (domainRequest sameInput).leaves := by
  intro x hx
  refine ⟨x, ?_, .inl rfl⟩
  exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hx)))

theorem sameCod_supported :
    Supported sameCod.leaves (codomainRequest sameInput sameDom).leaves := by
  intro x hx
  refine ⟨x, ?_, .inl rfl⟩
  exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hx)))

def tile : DTile sameInput.removed := emittedTile EnvWfT.empty sameInput sameDom sameCod

theorem original_codomain_edge :
    OM3_edge (sameInput.removed ++ frame)
      ((codomainRequest sameInput sameDom).leaves ++ frame) :=
  codomain_edge sameInput sameDom sameDom_supported frame

theorem actual_output_edge :
    OM3_edge (sameInput.removed ++ frame)
      ((emitted sameInput sameDom sameCod).leaves ++ frame) :=
  emitted_edge sameInput sameDom sameDom_supported sameCod sameCod_supported frame

theorem actual_output_materialization : tile.step =
    structPiStep (sameInput.leftView.hA.val (envClosed_of_envWfT EnvWfT.empty)
      (envWfT_subst_inst EnvWfT.empty))
      (sameDom.val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty))
      (sameInput.leftView.hB.val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty))
      (sameCod.val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty))
      ((payload sameInput sameDom sameCod).hrt.val (envClosed_of_envWfT EnvWfT.empty)
        (envWfT_subst_inst EnvWfT.empty))
      (sameInput.leftView.hc.val (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)) := rfl

theorem actual_output_not_source : tile.step ≠ sameInput.source :=
  emitted_not_input sameInput sameDom sameCod
    (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)

theorem actual_output_no_occurrences : F8Occurrences.occurrences tile.step = [] := rfl

theorem actual_output_has_support : (emitted sameInput sameDom sameCod).leaves ≠ [] := by
  have hp : 0 < sameInput.leftView.hA.leaves.length := by
    change 0 < (sameInput.leftOriginal.invPiT rfl).hA.leaves.length
    rw [EvTy.invPiT_agree sameInput.leftOriginal rfl rfl]
    decide
  intro he
  have hn := congrArg List.length he
  simp only [emitted, EvPar.leaves, payload, StructPiPayload.leaves,
    List.length_append, List.length_nil] at hn
  omega

/-- Standalone alignment operation on ORIGINAL input atoms. This is not a claim
that the unequal-annotation P reply has been derived from input.removed. -/
def binderRoots : List (Jd emptyEnv 0) :=
  [.cv domainConversion, .ty leftBody, .ty rightBody, .pe (PEqT.bvar [.assumption A] 0)]
def binder : BinderRequest binderRoots [] A A' B B where
  u := .succ l
  v := .zero
  vRight := .zero
  raw := .bvar [.assumption A] 0
  rawSub := ⟨_, .tail _ (.tail _ (.tail _ (.head _))), .inl rfl⟩
  left := .lit leftBody ⟨_, .tail _ (.head _), .inl rfl⟩
  domain := .lit domainConversion ⟨_, .head _, .inl rfl⟩
  right := .lit rightBody ⟨_, .tail _ (.tail _ (.head _)), .inl rfl⟩

def binder_aligned : HasTyT emptyEnv 0 [.assumption A] B (.sort .zero) :=
  binder.rightAligned (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)

theorem binder_materialization_exact : binder_aligned =
    hasTyTConvAssump (envClosed_of_envWfT EnvWfT.empty) domainConversion rightBody := rfl

theorem binder_leaves_exact : binder.leaves =
    [.pe (PEqT.bvar [.assumption A] 0), .ty leftBody, .cv domainConversion, .ty rightBody] := rfl

end Rcic.Declarative.F8Measure.SP1.Pins

#print axioms Rcic.Declarative.F8Measure.SP1.Pins.l
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.A
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.A'
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.B
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.idx
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.hA
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.hA'
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.domainConversion
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.leftBody
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.rightBody
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.leftPi
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.rightPi
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.input
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.annotations_distinct
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.dependent_body
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.domain_index_exact
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.right_domain_index_exact
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.frame
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.original_domain_edge
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.sameInput
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.sameDom
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.sameCod
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.sameDom_supported
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.sameCod_supported
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.tile
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.original_codomain_edge
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.actual_output_edge
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.actual_output_materialization
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.actual_output_not_source
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.actual_output_no_occurrences
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.actual_output_has_support
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.binderRoots
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.binder
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.binder_aligned
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.binder_materialization_exact
#print axioms Rcic.Declarative.F8Measure.SP1.Pins.binder_leaves_exact
