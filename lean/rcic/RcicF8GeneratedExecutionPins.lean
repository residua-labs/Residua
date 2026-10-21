import rcic.RcicF8GeneratedExecution
import rcic.RcicF8JTransPins

/-!
Kernel pins for G0 of ChatGPT's #7160 design (specification #7203).
These freeze the landed J5a.Pins inputs, select their actual calls and output
addresses, and check the exact read object and owner-side certificate. They
construct no generation event or whole-output origin supplier. closure_claim=0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JExecution.Pins

open PEqTProofFront PEqLeafTPropPins DExecution DAddresses

/-- The original fixture contains only original data and source evidence. -/
def original : JInput emptyEnv 0 J5a.Pins.roots where
  ctx := []
  left := q
  right := J5a.Pins.third
  index := aliasP
  ctxWf := .nil
  literal := J5a.Pins.input
  admitted := J5a.Pins.admissible_input
  source := J5a.Pins.cert

def rootTrans : TransCall original :=
  ⟨q, p, J5a.Pins.third, aliasP, J5a.Pins.h₁, J5a.Pins.h₂, .root⟩

def wrapped : JInput emptyEnv 0 J5a.Pins.roots where
  ctx := []
  left := J5a.Pins.third
  right := q
  index := aliasP
  ctxWf := .nil
  literal := J5a.Pins.wrapper
  admitted := rfl
  source := ⟨.cv J5a.Pins.wrapper, .head _, .inl rfl⟩

/-- The same trans is reached through the original symm recursive call. -/
def nestedTrans : TransCall wrapped :=
  ⟨q, p, J5a.Pins.third, aliasP, J5a.Pins.h₁, J5a.Pins.h₂, .symmBody .root⟩

def firstIrrPos : JCallPos original.literal J5a.Pins.pq :=
  .tyConvBody (.symmBody (.transLeft .root))

def secondIrrPos : JCallPos original.literal J5a.Pins.ps :=
  .tyConvBody (.transRight .root)

theorem first_original_source : firstIrrPos.source original.source = J5a.Pins.certPQ := rfl

theorem second_original_source : secondIrrPos.source original.source = J5a.Pins.certPS := rfl

theorem first_original_result (su : F8A2Support.SortUnique emptyEnv 0) :
    firstIrrPos.result EnvWfT.empty su original =
      J3.irrResult EnvWfT.empty J5a.Pins.tyP J5a.Pins.typ J5a.Pins.tyq
        J5a.Pins.certPQ := rfl

theorem computed_first (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.p₁ EnvWfT.empty su = J5a.Pins.first := rfl

theorem computed_second (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.p₂ EnvWfT.empty su = J5a.Pins.second := rfl

theorem computed_whole_result (su : F8A2Support.SortUnique emptyEnv 0) :
    original.result EnvWfT.empty su =
      J5a.transResult EnvWfT.empty su CtxWfT.nil J5a.Pins.first J5a.Pins.second := rfl

theorem computed_run_result (su : F8A2Support.SortUnique emptyEnv 0) :
    (buildRun EnvWfT.empty su original).result = original.result EnvWfT.empty su :=
  buildRun_result EnvWfT.empty su original

theorem actual_root_query (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.rootQuery EnvWfT.empty su =
      .star J5a.Pins.first.valley.right.spine J5a.Pins.second.valley.left.spine := rfl

theorem actual_D_output (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.K EnvWfT.empty su = J5a.Pins.groundD :=
  J5a.Pins.actual_D_branch su

def secondStep : DStep J5a.Pins.roots [] p J5a.Pins.third aliasP :=
  .conv (.base J5a.Pins.secondBase) J5a.Pins.secondIndex

def secondSpine : DSpine J5a.Pins.roots [] aliasP p J5a.Pins.third :=
  .tail secondStep (.refl J5a.Pins.secondRead.rightTy)

/-- All positions start at the actual computed root, with no arbitrary jump. -/
def stripPos (su : F8A2Support.SortUnique emptyEnv 0) :
    DCallPos EnvWfT.empty su rootTrans (.strip J5a.Pins.wrappedStep secondSpine) :=
  .starStrip .root

def diamondPos (su : F8A2Support.SortUnique emptyEnv 0) :
    DCallPos EnvWfT.empty su rootTrans (.step J5a.Pins.wrappedStep secondStep) :=
  .stripDiamond (stripPos su)

def tailPos (su : F8A2Support.SortUnique emptyEnv 0) :
    DCallPos EnvWfT.empty su rootTrans
      (.star (.refl J5a.Pins.firstRead.rightTy)
        ((DQuery.strip J5a.Pins.wrappedStep secondSpine).result
          EnvWfT.empty su CtxWfT.nil).left) :=
  .starTail .root

/-- This live diamond ends in stay, so it has no recursive strip-tail call. -/
theorem diamond_right_stays (su : F8A2Support.SortUnique emptyEnv 0) :
    (diamondPos su).result.right = .stay J5a.Pins.secondRead.rightTy := rfl

theorem diamond_has_no_strip_tail (su : F8A2Support.SortUnique emptyEnv 0)
    (u : DStep J5a.Pins.roots [] J5a.Pins.third (diamondPos su).result.d aliasP) :
    (diamondPos su).result.right ≠ .step u := by
  intro h
  cases h

theorem diamond_run_result (su : F8A2Support.SortUnique emptyEnv 0) :
    DQuery.Run.result EnvWfT.empty su CtxWfT.nil (diamondPos su).run =
      (diamondPos su).result := (diamondPos su).run_result

theorem complete_run_contains_diamond (su : F8A2Support.SortUnique emptyEnv 0) :
    DQuery.Run.result EnvWfT.empty su CtxWfT.nil
      ((buildRun EnvWfT.empty su original).dRuns rootTrans
        (.step J5a.Pins.wrappedStep secondStep) (diamondPos su)) =
      (diamondPos su).result := rfl

/-- This is a head address in K's actual closing spine. -/
def closingOutput (su : F8A2Support.SortUnique emptyEnv 0) :
    DOutputPos EnvWfT.empty su rootTrans :=
  .left (.head (s := .base J5a.Pins.closingStep)
    (rest := .refl J5a.Pins.secondRead.rightTy))

section ClosingPins

-- The address constructors fix the selected step before converting K's type.
set_option maxHeartbeats 2000000

theorem closing_selected (su : F8A2Support.SortUnique emptyEnv 0) :
    (closingOutput su).selected =
      ⟨q, J5a.Pins.third, .base J5a.Pins.closingStep⟩ := rfl

theorem closing_emission_exact (su : F8A2Support.SortUnique emptyEnv 0) :
    (closingOutput su).emit.selected =
      ⟨q, J5a.Pins.third, J5a.Pins.closingStep.val J5a.Pins.cl J5a.Pins.ss⟩ := by
  exact (closingOutput su).emit_read_exact.trans
    (congrArg (SpineStep.read J5a.Pins.cl J5a.Pins.ss) (closing_selected su))

theorem closing_emission_certificate (su : F8A2Support.SortUnique emptyEnv 0) :
    HEq (closingOutput su).emit.certificate
      (J5a.baseCertificate J5a.Pins.cl J5a.Pins.ss
        [.cv J5a.Pins.input] J5a.Pins.closingStep) := by
  have h := (closingOutput su).emit_certificate_exact
  rw [closing_selected su] at h
  exact h

theorem closing_owner_caller (su : F8A2Support.SortUnique emptyEnv 0) :
    (closingOutput su).emit.certificate.tile.X = [.cv J5a.Pins.input] := rfl

theorem closing_root_route (su : F8A2Support.SortUnique emptyEnv 0) :
    (closingOutput su).finalOutput = some (closingOutput su).emit := rfl

def nestedClosingOutput (su : F8A2Support.SortUnique emptyEnv 0) :
    DOutputPos EnvWfT.empty su nestedTrans :=
  .left (.head (s := .base J5a.Pins.closingStep)
    (rest := .refl J5a.Pins.secondRead.rightTy))

theorem single_tail_pos_unique
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {s : ParRedT (PEqLeafT E n) E n Γ a b T} {hb : HasTyT E n Γ b T}
    (p₁ p₂ : StarPos (.tail s (.refl Γ b T hb))) : p₁ = p₂ := by
  cases p₁ with
  | head =>
      cases p₂ with
      | head => rfl
      | tail p₂ => cases p₂
  | tail p₁ => cases p₁

/-- Transport a right-leg address through a proved valley equation. -/
def rightValleyPos
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {a b T : Expr Nat}
    (cl : EnvClosed E) (ss : EnvMembersSubstStable E)
    {V W : Valley R Γ a b T} (h : V = W)
    (p : StarPos (W.right.val cl ss)) : StarPos (V.right.val cl ss) := by
  cases h
  exact p

theorem rightValleyPos_selected
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {a b T : Expr Nat}
    (cl : EnvClosed E) (ss : EnvMembersSubstStable E)
    {V W : Valley R Γ a b T} (h : V = W)
    (p : StarPos (W.right.val cl ss)) :
    (rightValleyPos cl ss h p).selected = p.selected := by
  cases h
  rfl

/-- Equality transport preserves address uniqueness without reducing the worker. -/
theorem rightValleyPos_unique
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {a b T : Expr Nat}
    (cl : EnvClosed E) (ss : EnvMembersSubstStable E)
    {V W : Valley R Γ a b T} (h : V = W)
    (hu : ∀ p₁ p₂ : StarPos (W.right.val cl ss), p₁ = p₂)
    (p₁ p₂ : StarPos (V.right.val cl ss)) : p₁ = p₂ := by
  cases h
  exact hu p₁ p₂

/-- Unfold only the original symm call, then reuse the landed worker equation. -/
theorem actual_wrapped_valley
    (su : F8A2Support.SortUnique emptyEnv 0) :
    (wrapped.result EnvWfT.empty su).valley = J5a.Pins.groundValley.symm := by
  change (J5a.buildFragment EnvWfT.empty su J5a.Pins.roots CtxWfT.nil
    J5a.Pins.input J5a.Pins.admissible_input J5a.Pins.cert).valley.symm = _
  exact congrArg Valley.symm (J5a.Pins.actual_worker su)

/-- This address is checked solely against the closed ground valley. -/
def groundSymmRightHead :
    StarPos (J5a.Pins.groundValley.symm.right.val J5a.Pins.cl J5a.Pins.ss) :=
  StarPos.head
    (s := J5a.Pins.closingStep.val J5a.Pins.cl J5a.Pins.ss)
    (rest := .refl [] J5a.Pins.third aliasP
      (J5a.Pins.secondRead.rightTy.val J5a.Pins.cl J5a.Pins.ss))

theorem groundSymmRight_unique
    (p₁ p₂ : StarPos
      (J5a.Pins.groundValley.symm.right.val J5a.Pins.cl J5a.Pins.ss)) : p₁ = p₂ :=
  single_tail_pos_unique
    (s := J5a.Pins.closingStep.val J5a.Pins.cl J5a.Pins.ss)
    (hb := J5a.Pins.secondRead.rightTy.val J5a.Pins.cl J5a.Pins.ss) p₁ p₂

/-- The exact final head is transported by the computed valley equation. -/
def closingSymmOutput (su : F8A2Support.SortUnique emptyEnv 0) :
    OutputPos EnvWfT.empty su wrapped :=
  .right (rightValleyPos J5a.Pins.cl J5a.Pins.ss
    (actual_wrapped_valley su) groundSymmRightHead)

/-- The transported address selects the exact concrete closing producer. -/
theorem closing_symm_selected (su : F8A2Support.SortUnique emptyEnv 0) :
    (closingSymmOutput su).selected =
      ⟨q, J5a.Pins.third, J5a.Pins.closingStep.val J5a.Pins.cl J5a.Pins.ss⟩ := by
  exact (rightValleyPos_selected J5a.Pins.cl J5a.Pins.ss
    (actual_wrapped_valley su) groundSymmRightHead).trans rfl

/-- The original symm ancestor repositions this left emission onto its right. -/
theorem closing_symm_route (su : F8A2Support.SortUnique emptyEnv 0) :
    (nestedClosingOutput su).finalOutput = some (closingSymmOutput su) := by
  change some (OutputPos.right _) = some (closingSymmOutput su)
  apply congrArg (fun p => some (OutputPos.right
    (hW := EnvWfT.empty) (su := su) (i := wrapped) p))
  exact rightValleyPos_unique J5a.Pins.cl J5a.Pins.ss
    (actual_wrapped_valley su) groundSymmRight_unique _ _

/-- The actual base owner certificate, typed at the packed read step. -/
def spineReadCertificate
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {T : Expr Nat}
    (cl : EnvClosed E) (ss : EnvMembersSubstStable E)
    (X : List (Jd E n)) (s : SpineStep R Γ T) :
    J3.StepCertificate R X (s.read cl ss).step :=
  J5a.baseCertificate cl ss X s.step.read

theorem spineReadCertificate_exact
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {Γ : LCtx} {T : Expr Nat}
    (cl : EnvClosed E) (ss : EnvMembersSubstStable E)
    (X : List (Jd E n)) (s : SpineStep R Γ T) :
    HEq (spineReadCertificate cl ss X s)
      (J5a.baseCertificate cl ss X s.step.read) := HEq.rfl

/-- The generic exact owner theorem with the packed-read type made explicit. -/
theorem finalOutput_spineReadCertificate_exact
    {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
    {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
    {i : JInput E n R} {F : TransCall i}
    (o : DOutputPos hW su F) (dst : OutputPos hW su i)
    (h : o.finalOutput = some dst) :
    HEq dst.certificate
      (F.atCall.transportCertificate hW i
        (o.selected.read (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW))
        (spineReadCertificate (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW) F.localCaller o.selected)) :=
  o.finalOutput_certificate_exact dst h

theorem closing_symm_certificate (su : F8A2Support.SortUnique emptyEnv 0) :
    HEq (closingSymmOutput su).certificate
      (nestedTrans.atCall.transportCertificate EnvWfT.empty wrapped
        (a := q) (b := J5a.Pins.third) (T := aliasP) (h := J5a.Pins.input)
        ((nestedClosingOutput su).selected.read J5a.Pins.cl J5a.Pins.ss)
        (spineReadCertificate J5a.Pins.cl J5a.Pins.ss
          nestedTrans.localCaller (nestedClosingOutput su).selected)) :=
  finalOutput_spineReadCertificate_exact
    (nestedClosingOutput su) (closingSymmOutput su) (closing_symm_route su)

end ClosingPins

def firstConsumedOutput (su : F8A2Support.SortUnique emptyEnv 0) :
    OutputPos EnvWfT.empty su (rootTrans.leftPos.input original) := .right .head

def secondConsumedOutput (su : F8A2Support.SortUnique emptyEnv 0) :
    OutputPos EnvWfT.empty su (rootTrans.rightPos.input original) := .left .head

/-- These original legs become the actual D inputs and have no direct splice. -/
theorem first_consumed_route (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.leftPos.liftOutput EnvWfT.empty su original (firstConsumedOutput su) = none := rfl

theorem second_consumed_route (su : F8A2Support.SortUnique emptyEnv 0) :
    rootTrans.rightPos.liftOutput EnvWfT.empty su original (secondConsumedOutput su) = none := rfl

theorem local_caller_differs_from_top :
    nestedTrans.localCaller ≠ nestedTrans.topCaller := by
  intro h
  have heq : Jd.cv J5a.Pins.input = .cv J5a.Pins.wrapper := (List.cons.inj h).1
  have hlt := child_wt_lt (x := Jd.cv J5a.Pins.input)
    (y := Jd.cv J5a.Pins.wrapper) (by
      change Jd.cv J5a.Pins.input ∈ [Jd.cv J5a.Pins.input]
      exact List.mem_cons_self ..)
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Use the proved address round trip, rather than assuming a spine equality. -/
def wrappedSpineHead : SpinePos J5a.Pins.emittedSpine := .head

theorem wrapped_toStar_spine_address :
    wrappedSpineHead.toStarSpine.selected = wrappedSpineHead.selected :=
  wrappedSpineHead.toStarSpine_exact

def wrappedOriginalHead : StarPos (J5a.Pins.wrappedStep.star1.val
    J5a.Pins.cl J5a.Pins.ss) := .head

def wrappedReadHead : StarPos ((J5a.readOutput J5a.Pins.emittedSpine.toStar).val
    J5a.Pins.cl J5a.Pins.ss) := wrappedSpineHead.emit J5a.Pins.cl J5a.Pins.ss

theorem wrapped_emission_exact : wrappedReadHead.selected =
    wrappedSpineHead.selected.read J5a.Pins.cl J5a.Pins.ss :=
  DAddresses.emit_read_exact J5a.Pins.cl J5a.Pins.ss wrappedSpineHead

/-- The original conversion wrapper is a different actual proof object. -/
theorem wrapped_original_differs_from_read :
    ¬ HEq wrappedOriginalHead.step wrappedReadHead.step := by
  intro h
  have hread := DAddresses.emit_read_step_exact J5a.Pins.cl J5a.Pins.ss wrappedSpineHead
  have heq := eq_of_heq (HEq.trans h hread)
  cases heq

end Rcic.Declarative.F8Measure.JExecution.Pins

#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.computed_whole_result
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.diamond_run_result
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.complete_run_contains_diamond
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.closing_emission_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.closing_emission_certificate
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.closing_symm_selected
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.closing_symm_route
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.spineReadCertificate_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.finalOutput_spineReadCertificate_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.closing_symm_certificate
#print axioms Rcic.Declarative.F8Measure.JExecution.Pins.wrapped_original_differs_from_read
