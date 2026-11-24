import NfCompose.Basic

/-!
Sequential composition. Stage 2's raw input is built from stage 1's
representative (`feed : M1.Rep → M2.Raw`), which is a function of the class.
`seq_profile` therefore needs no hypothesis beyond the two profiles.

`RespectsClasses` is the extra hypothesis for a raw observation
`observe : M1.Raw → M2.Raw`: a class-indexed raw that lands in the same
stage-2 class. It is the constructive form of "stage 2 respects stage 1's
classes". Choosing one raw per class would be `Classical.choice`; the caller
supplies `classRaw` instead. `observe_does_not_factor` is the countermodel
where no such function exists.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

inductive SeqResidue (R1 R2 : Type) where
  | stage1 (r : R1)
  | stage2 (r : R2)
  deriving DecidableEq

inductive SeqRep (P1 P2 : Type) where
  | both (p1 : P1) (p2 : P2)
  deriving DecidableEq

inductive SeqOutcome (O1 O2 : Type) where
  | stage1 (o : O1)
  | stage2 (o : O2)
  deriving DecidableEq

def seqEvalOf {O1 O2 R : Type} (o1 : O1) (sig : Option R) (cont : R → O2) :
    SeqOutcome O1 O2 :=
  match sig with
  | none => .stage1 o1
  | some rep => .stage2 (cont rep)

def seqAdmOf {R C2 : Type} (adm1 : Bool) (sig : Option R)
    (adm2 : R → C2 → Bool) (q2 : R → C2) : Bool :=
  match adm1, sig with
  | true, some rep => adm2 rep (q2 rep)
  | _, _ => false

def seqRhoOf {R1 R2 R : Type} (adm1 : Bool) (sig : Option R) (rho1 : Option R1)
    (adm2 : R → Bool) (rho2 : R → Option R2) : Option (SeqResidue R1 R2) :=
  match adm1, sig with
  | false, _ => rho1.map .stage1
  | true, none => none
  | true, some rep =>
      if adm2 rep then none else (rho2 rep).map .stage2

def seqSigmaOf {P1 P2 : Type} (adm1 : Bool) (sig : Option P1)
    (sig2 : P1 → Option P2) : Option (SeqRep P1 P2) :=
  match adm1, sig with
  | true, some rep1 =>
      match sig2 rep1 with
      | some rep2 => some (.both rep1 rep2)
      | none => none
  | _, _ => none

variable (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)

def seqModel : ExecModel where
  Raw := M1.Raw
  Class := M1.Class
  Rep := SeqRep M1.Rep M2.Rep
  Residue := SeqResidue M1.Residue M2.Residue
  Outcome := SeqOutcome M1.Outcome M2.Outcome
  q := M1.q
  evalRaw := fun r =>
    seqEvalOf (M1.evalRaw r) (M1.sigma (M1.q r)) (fun rep => M2.evalRaw (feed rep))
  evalClass := fun c =>
    seqEvalOf (M1.evalClass c) (M1.sigma c) (fun rep => M2.evalRaw (feed rep))
  admissible := fun c =>
    seqAdmOf (M1.admissible c) (M1.sigma c)
      (fun rep _ => M2.admissible (M2.q (feed rep))) (fun rep => M2.q (feed rep))
  rho := fun c =>
    seqRhoOf (M1.admissible c) (M1.sigma c) (M1.rho c)
      (fun rep => M2.admissible (M2.q (feed rep)))
      (fun rep => M2.rho (M2.q (feed rep)))
  sigma := fun c =>
    seqSigmaOf (M1.admissible c) (M1.sigma c)
      (fun rep => M2.sigma (M2.q (feed rep)))

theorem seq_profile (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2) :
    hasMSTNFProfile (seqModel M1 M2 feed) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    simp only [seqModel]
    cases hs : M1.sigma (M1.q r) with
    | none =>
        simp only [seqEvalOf, hs]
        exact congrArg SeqOutcome.stage1 (h1.1 r)
    | some _ =>
        simp only [seqEvalOf, hs]
  · intro c rep hs
    cases ha : M1.admissible c with
    | false =>
        cases hsig : M1.sigma c with
        | none => simp [seqModel, seqSigmaOf, ha, hsig] at hs
        | some _ => simp [seqModel, seqSigmaOf, ha, hsig] at hs
    | true =>
        cases hsig : M1.sigma c with
        | none => simp [seqModel, seqSigmaOf, ha, hsig] at hs
        | some rep1 =>
            cases h2s : M2.sigma (M2.q (feed rep1)) with
            | none => simp [seqModel, seqSigmaOf, ha, hsig, h2s] at hs
            | some rep2 =>
                have hadm2 := h2.2.1 (M2.q (feed rep1)) rep2 h2s
                simp [seqModel, seqAdmOf, ha, hsig, hadm2]
  · intro c hc hadm
    cases ha : M1.admissible c with
    | false =>
        have hrho := h1.2.2.1 c hc ha
        cases hr : M1.rho c with
        | none => exact absurd hr hrho
        | some _ =>
            intro hnone
            simp [seqModel, seqRhoOf, ha, hr] at hnone
    | true =>
        cases hsig : M1.sigma c with
        | none => exact absurd hsig (h1.2.2.2 c hc ha)
        | some rep =>
            have hc2 : activeClass M2 (M2.q (feed rep)) := ⟨feed rep, rfl⟩
            have hadm2 : M2.admissible (M2.q (feed rep)) = false := by
              cases hb : M2.admissible (M2.q (feed rep)) with
              | false => rfl
              | true =>
                  have : (seqModel M1 M2 feed).admissible c = true := by
                    simp [seqModel, seqAdmOf, ha, hsig, hb]
                  cases hadm.symm.trans this
            have hrho2 := h2.2.2.1 _ hc2 hadm2
            cases hr : M2.rho (M2.q (feed rep)) with
            | none => exact absurd hr hrho2
            | some _ =>
                intro hnone
                simp [seqModel, seqRhoOf, ha, hsig, hadm2, hr] at hnone
  · intro c hc hadm
    cases ha : M1.admissible c with
    | false =>
        have : (seqModel M1 M2 feed).admissible c = false := by
          cases hsig : M1.sigma c <;> simp [seqModel, seqAdmOf, ha, hsig]
        cases hadm.symm.trans this
    | true =>
        cases hsig : M1.sigma c with
        | none =>
            have : (seqModel M1 M2 feed).admissible c = false := by
              simp [seqModel, seqAdmOf, ha, hsig]
            cases hadm.symm.trans this
        | some rep =>
            have hadm2 : M2.admissible (M2.q (feed rep)) = true := by
              simpa [seqModel, seqAdmOf, ha, hsig] using hadm
            have hc2 : activeClass M2 (M2.q (feed rep)) := ⟨feed rep, rfl⟩
            have hsig2 := h2.2.2.2 _ hc2 hadm2
            cases h2s : M2.sigma (M2.q (feed rep)) with
            | none => exact absurd h2s hsig2
            | some _ =>
                intro hnone
                simp [seqModel, seqSigmaOf, ha, hsig, h2s] at hnone

/-- Class-indexed witness that a raw observation factors through stage 1's `q`. -/
structure RespectsClasses (observe : M1.Raw → M2.Raw) where
  classRaw : M1.Class → M2.Raw
  respects : ∀ r, M2.q (observe r) = M2.q (classRaw (M1.q r))

def seqObserveModel (observe : M1.Raw → M2.Raw)
    (respect : RespectsClasses M1 M2 observe) : ExecModel where
  Raw := M1.Raw
  Class := M1.Class
  Rep := SeqRep M1.Rep M2.Rep
  Residue := SeqResidue M1.Residue M2.Residue
  Outcome := SeqOutcome M1.Outcome M2.Outcome
  q := M1.q
  evalRaw := fun r =>
    seqEvalOf (M1.evalRaw r) (M1.sigma (M1.q r))
      (fun _ => M2.evalRaw (observe r))
  evalClass := fun c =>
    seqEvalOf (M1.evalClass c) (M1.sigma c)
      (fun _ => M2.evalRaw (respect.classRaw c))
  admissible := fun c =>
    seqAdmOf (M1.admissible c) (M1.sigma c)
      (fun _ _ => M2.admissible (M2.q (respect.classRaw c)))
      (fun _ => M2.q (respect.classRaw c))
  rho := fun c =>
    seqRhoOf (M1.admissible c) (M1.sigma c) (M1.rho c)
      (fun _ => M2.admissible (M2.q (respect.classRaw c)))
      (fun _ => M2.rho (M2.q (respect.classRaw c)))
  sigma := fun c =>
    seqSigmaOf (M1.admissible c) (M1.sigma c)
      (fun _ => M2.sigma (M2.q (respect.classRaw c)))

theorem seqObserve_profile (observe : M1.Raw → M2.Raw)
    (respect : RespectsClasses M1 M2 observe)
    (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2) :
    hasMSTNFProfile (seqObserveModel M1 M2 observe respect) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    simp only [seqObserveModel]
    cases hs : M1.sigma (M1.q r) with
    | none =>
        simp only [seqEvalOf, hs]
        exact congrArg SeqOutcome.stage1 (h1.1 r)
    | some _ =>
        simp only [seqEvalOf, hs]
        exact congrArg SeqOutcome.stage2
          (by rw [h2.1 (observe r), h2.1 (respect.classRaw (M1.q r)), respect.respects r])
  · intro c rep hs
    cases ha : M1.admissible c with
    | false =>
        cases hsig : M1.sigma c <;> simp [seqObserveModel, seqSigmaOf, ha, hsig] at hs
    | true =>
        cases hsig : M1.sigma c with
        | none => simp [seqObserveModel, seqSigmaOf, ha, hsig] at hs
        | some _ =>
            cases h2s : M2.sigma (M2.q (respect.classRaw c)) with
            | none => simp [seqObserveModel, seqSigmaOf, ha, hsig, h2s] at hs
            | some rep2 =>
                have hadm2 := h2.2.1 _ rep2 h2s
                simp [seqObserveModel, seqAdmOf, ha, hsig, hadm2]
  · intro c hc hadm
    cases ha : M1.admissible c with
    | false =>
        have hrho := h1.2.2.1 c hc ha
        cases hr : M1.rho c with
        | none => exact absurd hr hrho
        | some _ =>
            intro hnone
            simp [seqObserveModel, seqRhoOf, ha, hr] at hnone
    | true =>
        cases hsig : M1.sigma c with
        | none => exact absurd hsig (h1.2.2.2 c hc ha)
        | some _ =>
            have hc2 : activeClass M2 (M2.q (respect.classRaw c)) :=
              ⟨respect.classRaw c, rfl⟩
            have hadm2 : M2.admissible (M2.q (respect.classRaw c)) = false := by
              cases hb : M2.admissible (M2.q (respect.classRaw c)) with
              | false => rfl
              | true =>
                  have : (seqObserveModel M1 M2 observe respect).admissible c = true := by
                    simp [seqObserveModel, seqAdmOf, ha, hsig, hb]
                  cases hadm.symm.trans this
            have hrho2 := h2.2.2.1 _ hc2 hadm2
            cases hr : M2.rho (M2.q (respect.classRaw c)) with
            | none => exact absurd hr hrho2
            | some _ =>
                intro hnone
                simp [seqObserveModel, seqRhoOf, ha, hsig, hadm2, hr] at hnone
  · intro c hc hadm
    cases ha : M1.admissible c with
    | false =>
        have : (seqObserveModel M1 M2 observe respect).admissible c = false := by
          cases hsig : M1.sigma c <;> simp [seqObserveModel, seqAdmOf, ha, hsig]
        cases hadm.symm.trans this
    | true =>
        cases hsig : M1.sigma c with
        | none =>
            have : (seqObserveModel M1 M2 observe respect).admissible c = false := by
              simp [seqObserveModel, seqAdmOf, ha, hsig]
            cases hadm.symm.trans this
        | some _ =>
            have hadm2 : M2.admissible (M2.q (respect.classRaw c)) = true := by
              simpa [seqObserveModel, seqAdmOf, ha, hsig] using hadm
            have hc2 : activeClass M2 (M2.q (respect.classRaw c)) :=
              ⟨respect.classRaw c, rfl⟩
            have hsig2 := h2.2.2.2 _ hc2 hadm2
            cases h2s : M2.sigma (M2.q (respect.classRaw c)) with
            | none => exact absurd h2s hsig2
            | some _ =>
                intro hnone
                simp [seqObserveModel, seqSigmaOf, ha, hsig, h2s] at hnone

/-! Raw observation that does not respect the stage-1 class.
Both models have `hasMSTNFProfile`. `a` and `b` share a class. Their images
under `observe` have different stage-2 outcomes, so no `evalClass` factors
the natural sequential outcome, and no `RespectsClasses` exists. -/

inductive ORaw | a | b
  deriving DecidableEq

inductive OClass | c
  deriving DecidableEq

inductive ORep | rep
  deriving DecidableEq

inductive ORes | res
  deriving DecidableEq

inductive OOut | ok
  deriving DecidableEq

def observeM1 : ExecModel where
  Raw := ORaw
  Class := OClass
  Rep := ORep
  Residue := ORes
  Outcome := OOut
  q := fun _ => .c
  evalRaw := fun _ => .ok
  evalClass := fun _ => .ok
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some .rep

inductive TRaw | x | y
  deriving DecidableEq

inductive TClass | cx | cy
  deriving DecidableEq

inductive TOut | ox | oy
  deriving DecidableEq

def observeM2 : ExecModel where
  Raw := TRaw
  Class := TClass
  Rep := Unit
  Residue := Unit
  Outcome := TOut
  q := fun r => match r with | .x => .cx | .y => .cy
  evalRaw := fun r => match r with | .x => .ox | .y => .oy
  evalClass := fun c => match c with | .cx => .ox | .cy => .oy
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some ()

def observeRaw : ORaw → TRaw
  | .a => .x
  | .b => .y

def observeEval (r : ORaw) : TOut :=
  observeM2.evalRaw (observeRaw r)

theorem observeM1_profile : hasMSTNFProfile observeM1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; cases r <;> rfl
  · intro cls rp _; cases cls; cases rp; rfl
  · intro _ _ hadm
    simp [observeM1] at hadm
  · intro _ _ _
    intro h
    simp [observeM1] at h

theorem observeM2_profile : hasMSTNFProfile observeM2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; cases r <;> rfl
  · intro c rep hs; cases c <;> cases rep <;> rfl
  · intro _ _ hadm
    simp [observeM2] at hadm
  · intro c _ _
    cases c <;> intro h <;> simp [observeM2] at h

theorem observe_does_not_factor :
    ¬ ∃ evalClass : OClass → TOut, ∀ r, observeEval r = evalClass (observeM1.q r) := by
  intro ⟨ev, h⟩
  have : observeEval .a = observeEval .b := by
    rw [h .a, h .b]
    simp [observeM1]
  simp [observeEval, observeRaw, observeM2] at this

theorem observe_no_respects (classRaw : OClass → TRaw) :
    ¬ ∀ r, observeM2.q (observeRaw r) = observeM2.q (classRaw (observeM1.q r)) := by
  intro h
  have : observeM2.q (observeRaw .a) = observeM2.q (observeRaw .b) := by
    rw [h .a, h .b]
    simp [observeM1]
  simp [observeRaw, observeM2] at this

def observeClass (r : ORaw) : OClass := observeM1.q r

def observeImageClass (r : ORaw) : TClass := observeM2.q (observeRaw r)

#guard decide (observeClass .a = observeClass .b)
#guard decide (ORaw.a ≠ ORaw.b)
#guard decide (observeEval .a ≠ observeEval .b)
#guard decide (observeImageClass .a ≠ observeImageClass .b)

end NfCompose
