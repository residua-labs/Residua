import rcic.RcicIARecUnique
import rcic.ScmSrcGroupsRecIdx
import rcic.ScmSrcGroupsEnvWfTAux

/-!
# IA-rec segment C: the GM-IND-001 tooth at a real cell, and the parameter count's necessity

* **GM-IND-001** (`docs/rcic/GLOBAL_MUTANT_REGISTRY.md:54`, "Caller-supplied recursor/iota descriptor
  overrides kernel derivation"). At srcEnvG slot 128 (`recNEL`), a caller supplies a recursor whose
  minors are NEL's two minors in the other order. Everything else is the real admission's: family,
  constructors, views, policy. `tooth_GM_IND_001_NEL` shows that this recursor admits no
  `MinorPremisesMatch`, at any analysis bound. The proof is `IA021T_recursor_unique` against the real
  admission (`admRecNEL05.h12`): any matching minors would force the decoy's type to equal `recNEL`'s,
  and the two types differ (`decide`). A second instrument, independent of the theorem, evaluates the
  real cell at its own bound: the minor admission derives for NEL's first constructor is not the
  decoy's first minor.
* **The parameter count is necessary.** The empty family `I : Type → Type` (`emptyFamEnv`) is admitted
  by the full `IndGroupAdmitted.recursor` judgment with 0 parameters and with 1 parameter, at the same
  `(E, r)` and with the same policy. The two recursor types differ (`decide`), and the checker types
  both. So `IA021T_recursor_unique` cannot drop its equal-parameter-count premise. The count is the
  candidate's datum (05 §2), and the admission records no candidate.

`closure_claim` 0.
-/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192

namespace Rcic.Declarative

/-! ## GM-IND-001 at srcEnvG slot 128 -/

/-- the caller-supplied recursor: NEL's minors swapped. -/
def recNELSwapped : CheckedMember :=
  ⟨.recursorM, recNEL.arity, policyRecursorType aRecNEL.family aRecNEL.minorTypes.reverse aRecNEL.policy,
    none⟩

/-- its elimination record: the real admission's family, constructors, views and policy. -/
def aRecNELSwapped : RecursorEliminationAdmitted (envPre 128) 128 recNELSwapped where
  family := aRecNEL.family
  constructors := aRecNEL.constructors
  constructorViews := aRecNEL.constructorViews
  constructorsPresent := aRecNEL.constructorsPresent
  recursorRef := aRecNEL.recursorRef
  minorTypes := aRecNEL.minorTypes.reverse
  minorCount := by rw [List.length_reverse]; exact aRecNEL.minorCount
  policy := aRecNEL.policy
  selected := aRecNEL.selected
  recursorArity := aRecNEL.recursorArity
  recursorType := rfl

theorem recNEL_ne_swapped : recNEL.mtype ≠ recNELSwapped.mtype := by decide

/-- TOOTH (GM-IND-001): the caller-supplied recursor admits no minor match at any bound. -/
theorem tooth_GM_IND_001_NEL : ¬ MinorPremisesMatch aRecNELSwapped := fun h =>
  recNEL_ne_swapped (IA021T_recursor_unique aRecNEL aRecNELSwapped admRecNEL05.h12 h rfl rfl).1

/- SECOND INSTRUMENT (GM-IND-001): at the cell's own bound and shapes, the minor admission derives for
   constructor 0 is the real one and not the decoy's. -/
kernel_rfl_theorem pin_GM_IND_001_NEL_derived :
    (derivedMinor aRecNEL ⟨0, by decide⟩ 96 shapesNelNil == aRecNEL.minorTypes[0]?,
      derivedMinor aRecNEL ⟨0, by decide⟩ 96 shapesNelNil == aRecNELSwapped.minorTypes[0]?) = (true, false)

/-! ## the parameter count: one empty family, two admissions -/

/-- `I : Type → Type`, no constructors. -/
def emptyFamMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩

def emptyFamEnv : ResolvedEnv := extendEnv emptyEnv 0 emptyFamMember

private def typeDomTyping (ds : List (Expr Nat)) (hds : ds = [.sort (.succ .zero)]) :
    PolicyTelescopeTyping emptyFamEnv 0 ds where
  levels := fun _ => .succ (.succ .zero)
  bounded := fun _ => rfl
  hasType := fun i => by
    subst hds
    match i with
    | ⟨0, _⟩ => exact HasTy.sort _ _

/-- the family read with one parameter. -/
def emptyFamView1 : PolicyFamilyView emptyFamEnv where
  ref := 0
  member := emptyFamMember
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero)]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := typeDomTyping _ rfl

/-- the family read with one index. -/
def emptyFamView0 : PolicyFamilyView emptyFamEnv where
  ref := 0
  member := emptyFamMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.sort (.succ .zero)]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := typeDomTyping _ rfl

def emptyRec1 : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort, policyRecursorType emptyFamView1 [] .anySort, none⟩

def emptyRec0 : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort, policyRecursorType emptyFamView0 [] .anySort, none⟩

def emptyAdm (v : PolicyFamilyView emptyFamEnv) (hv : v.ref = 0) (hl : v.resultLevel = .succ .zero)
    (hm : v.member = emptyFamMember) :
    RecursorEliminationAdmitted emptyFamEnv 1
      ⟨.recursorM, policyRecursorArity 0 .anySort, policyRecursorType v [] .anySort, none⟩ where
  family := v
  constructors := []
  constructorViews := fun i => i.elim0
  constructorsPresent := fun i => i.elim0
  recursorRef := by rw [hv]; rfl
  minorTypes := []
  minorCount := rfl
  policy := .anySort
  selected := .uniformType (hl ▸ uniformType_succ_zero)
  recursorArity := by rw [hm]; rfl
  recursorType := rfl

theorem emptyCensus : CtorCensus emptyFamEnv 0 1 := by
  refine ⟨Nat.le_refl _, fun c => ⟨?_, fun h => absurd h (by omega)⟩⟩
  rintro ⟨cm, hc, hk, _⟩
  by_cases h0 : c = 0
  · subst h0
    simp only [emptyFamEnv, extendEnv, if_pos rfl] at hc
    cases hc
    exact MemberClass.noConfusion hk
  · simp only [emptyFamEnv, extendEnv, if_neg h0, emptyEnv] at hc
    exact Option.noConfusion hc

/-- the full admission judgment, at either reading. -/
def emptyRecAdmitted (v : PolicyFamilyView emptyFamEnv) (hv : v.ref = 0)
    (hl : v.resultLevel = .succ .zero) (hm : v.member = emptyFamMember) :
    IndGroupAdmitted emptyFamEnv 1
      ⟨.recursorM, policyRecursorArity 0 .anySort, policyRecursorType v [] .anySort, none⟩ :=
  .recursor (emptyAdm v hv hl hm) rfl (by show CtorCensus emptyFamEnv v.ref 1; rw [hv]; exact emptyCensus)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    ⟨rfl, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem emptyRec_ne : emptyRec0.mtype ≠ emptyRec1.mtype := by decide

/- both recursor types are typed, by the checker. -/
kernel_rfl_theorem emptyRec0_typed : (sortTyAtC emptyFamEnv emptyRec0.arity 96 [] emptyRec0.mtype).isSome = true
kernel_rfl_theorem emptyRec1_typed : (sortTyAtC emptyFamEnv emptyRec1.arity 96 [] emptyRec1.mtype).isSome = true

/-- PIN (the parameter count is necessary): one family, one ref, one policy, both readings admitted by
    the full judgment, two different recursor types. -/
theorem pin_IA021T_nparams_needed :
    Nonempty (IndGroupAdmitted emptyFamEnv 1 emptyRec0) ∧
      Nonempty (IndGroupAdmitted emptyFamEnv 1 emptyRec1) ∧
      emptyFamView0.parameters.length ≠ emptyFamView1.parameters.length ∧
      emptyRec0.mtype ≠ emptyRec1.mtype :=
  ⟨⟨emptyRecAdmitted emptyFamView0 rfl rfl rfl⟩, ⟨emptyRecAdmitted emptyFamView1 rfl rfl rfl⟩,
    by decide, emptyRec_ne⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.tooth_GM_IND_001_NEL
#print axioms Rcic.Declarative.pin_GM_IND_001_NEL_derived
#print axioms Rcic.Declarative.pin_IA021T_nparams_needed
#print axioms Rcic.Declarative.emptyRec0_typed
#print axioms Rcic.Declarative.emptyRec1_typed
