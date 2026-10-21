import rcic.RcicNativeTypedModelCovRArrow

/-!
# A Prop-valued candidate quantifier at a sort binder

The native type argument is supplied to an explicit lexical-body callback.
The callback also receives its candidate predicate, whose closure proof is
quantified within Prop. There is no domain compact code or selected row at
this binder. Ordinary Pi interpretation belongs to a separate construction.
The shared function-shape gate excludes atomic compacts with no non-bottom
application behavior.

This is a same-type-argument clause: both endpoints are applied to the same
native `T`. It is not a supplier for arbitrary native application or conversion
between two different type arguments. Every compact action is tested, with no
demand-admissibility premise. Consequently these closure theorems do not prove
that every natively typed polymorphic lambda satisfies the clause. Ordinary
neutral compacts do satisfy it whenever the lexical body is a false-tagged
candidate, by the body's explicit neutral reflection law. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovPAudit

abbrev CovRForallBody := Expr Nat → CovRRel → CovRRel

/-- The closure premise is independent of a native typing witness. This
allows a lexical interpretation to prove it by structural induction. -/
def CovRForallBodyCandidates (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (inputPositive outputPositive : Bool) (Body : CovRForallBody) : Prop :=
  ∀ T S, CandidateCov E (WhStepCK2 E n) Γ inputPositive S →
    CandidateCov E (WhStepCK2 E n) Γ outputPositive (Body T S)

/-- Same native type argument at the two endpoints; the candidate quantifier
is Prop-valued and is independent of any finite type-code size. -/
def covRForall (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (sortLevel : Level)
    (inputPositive outputPositive : Bool) (Body : CovRForallBody) : CovRRel :=
  fun x y c => CovRFunctionShape c ∧ (outputPositive = true → c = .bot) ∧
    ∀ ds out, CovXCompactAction E c ds out →
      ∀ T, HasTyT E n Γ T (.sort sortLevel) →
        ∀ S, CandidateCov E (WhStepCK2 E n) Γ inputPositive S →
          Body T S (.app x T) (.app y T) out

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {sortLevel : Level}
  {inputPositive outputPositive : Bool} {Body : CovRForallBody}

theorem covRForall_intro {x y : Expr Nat} {c : CptT}
    (hshape : CovRFunctionShape c)
    (hc : outputPositive = true → c = .bot)
    (hbody : ∀ ds out, CovXCompactAction E c ds out →
      ∀ T, HasTyT E n Γ T (.sort sortLevel) →
        ∀ S, CandidateCov E (WhStepCK2 E n) Γ inputPositive S →
          Body T S (.app x T) (.app y T) out) :
    covRForall E n Γ sortLevel inputPositive outputPositive Body x y c :=
  ⟨hshape, hc, hbody⟩

theorem covRForall_shape {x y : Expr Nat} {c : CptT}
    (h : covRForall E n Γ sortLevel inputPositive outputPositive Body x y c) :
    CovRFunctionShape c := h.1

/-- Elimination consumes the actual compact action, native sort typing and
candidate proof. It supplies only this displayed same-argument body instance. -/
theorem covRForall_apply {x y : Expr Nat} {c out : CptT} {ds : List CptT}
    (h : covRForall E n Γ sortLevel inputPositive outputPositive Body x y c)
    (ha : CovXCompactAction E c ds out) (T : Expr Nat)
    (hT : HasTyT E n Γ T (.sort sortLevel)) (S : CovRRel)
    (hS : CandidateCov E (WhStepCK2 E n) Γ inputPositive S) :
    Body T S (.app x T) (.app y T) out :=
  h.2.2 ds out ha T hT S hS

/-- Candidate closure follows from the closure of the lexical body. Endpoint
readback uses actual CK2 congruence under application to the same type. -/
theorem covRForall_isCandidate
    (hBody : CovRForallBodyCandidates E n Γ inputPositive outputPositive Body) :
    CandidateCov E (WhStepCK2 E n) Γ outputPositive
      (covRForall E n Γ sortLevel inputPositive outputPositive Body) where
  symm := by
    intro x y c h
    refine ⟨h.1, h.2.1, ?_⟩
    intro ds out ha T hT S hS
    exact (hBody T S hS).symm (h.2.2 ds out ha T hT S hS)
  trans := by
    intro x y z c hxy hyz
    refine ⟨hxy.1, hxy.2.1, ?_⟩
    intro ds out ha T hT S hS
    exact (hBody T S hS).trans
      (hxy.2.2 ds out ha T hT S hS) (hyz.2.2 ds out ha T hT S hS)
  readback := by
    intro x x' y c hx
    constructor
    · intro h
      refine ⟨h.1, h.2.1, ?_⟩
      intro ds out ha T hT S hS
      exact ((hBody T S hS).readback
        (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mp
          (h.2.2 ds out ha T hT S hS)
    · intro h
      refine ⟨h.1, h.2.1, ?_⟩
      intro ds out ha T hT S hS
      exact ((hBody T S hS).readback
        (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mpr
          (h.2.2 ds out ha T hT S hS)
  bot := by
    intro x y
    refine ⟨Or.inl rfl, fun _ => rfl, ?_⟩
    intro ds out ha T hT S hS
    cases ha with
    | bot => exact (hBody T S hS).bot _ _
  neutral := by
    intro he x y r us hh
    refine ⟨Or.inr (Or.inr ⟨r, us, rfl⟩), ?_, ?_⟩
    · intro hp
      exact Bool.noConfusion (he.symm.trans hp)
    · intro ds out ha T hT S hS
      cases ha with
      | bot => exact (hBody T S hS).bot _ _
      | appSpine harg => exact (hBody T S hS).neutral he _ _ _ _ hh
  collapse := by
    intro he x y c h
    exact h.2.1 he

theorem covRForall_bot
    (hBody : CovRForallBodyCandidates E n Γ inputPositive outputPositive Body)
    (x y : Expr Nat) :
    covRForall E n Γ sortLevel inputPositive outputPositive Body x y .bot :=
  (covRForall_isCandidate hBody).bot x y

theorem covRForall_neutral
    (hBody : CovRForallBodyCandidates E n Γ inputPositive false Body)
    (x y : Expr Nat) (r : Nat) (us : List CptT) (hh : NeutralHeadP E r) :
    covRForall E n Γ sortLevel inputPositive false Body x y (.spine r us) :=
  (covRForall_isCandidate hBody).neutral rfl x y r us hh

theorem covRForall_readback
    (hBody : CovRForallBodyCandidates E n Γ inputPositive outputPositive Body)
    {x x' y y' : Expr Nat} {c : CptT}
    (hx : RedR (WhStepCK2 E n) Γ x x')
    (hy : RedR (WhStepCK2 E n) Γ y y') :
    covRForall E n Γ sortLevel inputPositive outputPositive Body x y c ↔
      covRForall E n Γ sortLevel inputPositive outputPositive Body x' y' c :=
  (covRForall_isCandidate hBody).readback_both hx hy

theorem covRForall_positive_iff_bot
    (hBody : CovRForallBodyCandidates E n Γ inputPositive true Body)
    (x y : Expr Nat) (c : CptT) :
    covRForall E n Γ sortLevel inputPositive true Body x y c ↔ c = .bot :=
  (covRForall_isCandidate hBody).positive_iff_bot x y c

/-- At Sort 1, native Prop and its exact `.prop` candidate jointly inhabit
the two quantified argument classes. No native sort-uniqueness rule is used. -/
theorem covRForall_prop_argument_inhabited (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) :
    ∃ (T : Expr Nat) (S : CovRRel),
      Nonempty (HasTyT E n Γ T (.sort (.succ .zero))) ∧
        CandidateCov E (WhStepCK2 E n) Γ false S :=
  ⟨.sort .zero, covRCodeRel E .prop, ⟨.sort Γ .zero⟩,
    covRProp_isCandidate E (WhStepCK2 E n) Γ⟩

/-- Specialize the actual quantifier at Prop and its supplied candidate. -/
theorem covRForall_apply_prop {x y : Expr Nat} {c out : CptT} {ds : List CptT}
    (h : covRForall E n Γ (.succ .zero) false outputPositive Body x y c)
    (ha : CovXCompactAction E c ds out) :
    Body (.sort .zero) (covRCodeRel E .prop)
      (.app x (.sort .zero)) (.app y (.sort .zero)) out :=
  covRForall_apply h ha (.sort .zero) (.sort Γ .zero)
    (covRCodeRel E .prop) (covRProp_isCandidate E (WhStepCK2 E n) Γ)

/-- A lexical body consisting of the bound candidate itself is closed.
This is variable lookup, not a chosen finite code for the type argument. -/
theorem covRForall_variable_body (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (positive : Bool) :
    CovRForallBodyCandidates E n Γ positive positive (fun _ S => S) :=
  fun _ _ hS => hS

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_FORALL_ROOTS
#print axioms CovRForallBody
#print axioms CovRForallBodyCandidates
#print axioms covRForall
#print axioms covRForall_intro
#print axioms covRForall_shape
#print axioms covRForall_apply
#print axioms covRForall_isCandidate
#print axioms covRForall_bot
#print axioms covRForall_neutral
#print axioms covRForall_readback
#print axioms covRForall_positive_iff_bot
#print axioms covRForall_prop_argument_inhabited
#print axioms covRForall_apply_prop
#print axioms covRForall_variable_body
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_FORALL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
