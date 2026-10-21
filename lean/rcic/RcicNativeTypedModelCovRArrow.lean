import rcic.RcicNativeTypedModelCovRCandidate

/-!
# An ordinary arrow with an actual semantic covering row

The domain and codomain are supplied predicates. The codomain predicate is
chosen before native arguments, and is the output of the singleton semantic
row `[([], B)]`. Coverage and typed applicative behavior are distinct fields;
coverage is not silently dropped when finite type codes are replaced.

No finite code budget is passed to a candidate through a type-variable
lookup. The operator below has a function-shape gate, stored-row support,
positive-collapse guard, support coverage, and typed application behavior. It does not infer
a native type from these fields or assert a general native-case supplier.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovXAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovZMeasureAudit

/-- The compact support of a supplied binary candidate relation. -/
def covRSupport (S : CovRRel) (c : CptT) : Prop :=
  ∃ x y, S x y c

theorem covRSupport_intro {S : CovRRel} {x y : Expr Nat} {c : CptT}
    (h : S x y c) : covRSupport S c :=
  ⟨x, y, h⟩

theorem covRSupport_bot {E : ResolvedEnv} {R : Readback} {Γ : LCtx}
    {positive : Bool} {S : CovRRel} (hS : CandidateCov E R Γ positive S) :
    covRSupport S .bot :=
  ⟨.sort .zero, .sort .zero, hS.bot _ _⟩

/-- The output predicate of the one empty-demand row covers every compact
action whose demands lie in the supplied domain's support. -/
def CovRArrowCoverage (E : ResolvedEnv) (D B : CovRRel) (c : CptT) : Prop :=
  ∀ ds out, CovXCompactAction E c ds out →
    (∀ u ∈ ds, covRSupport D u) → covRSupport B out

/-- Typed applications use the same codomain predicate on both endpoints.
The native domain and actual conversion premises remain explicit. -/
def CovRArrowAction (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Dty : Expr Nat) (D B : CovRRel) (x y : Expr Nat) (c : CptT) : Prop :=
  ∀ ds out, CovXCompactAction E c ds out →
    ∀ N N', HasTyT E n Γ N Dty → HasTyT E n Γ N' Dty →
    Nonempty (ConvT E n Γ N N' Dty) →
    (∀ u ∈ ds, D N N' u) → B (.app x N) (.app y N') out

/-- Nonfunctional leaves cannot qualify by having only bottom actions. -/
def CovRFunctionShape (c : CptT) : Prop :=
  c = .bot ∨ (∃ f, c = .lam f) ∨ (∃ r us, c = .spine r us)

/-- Every stored lambda row has supported demands and a supported output,
including rows whose demands are not exercised by a particular action. -/
def CovRLambdaRows (D B : CovRRel) (c : CptT) : Prop :=
  match c with
  | .lam rows => ∀ row ∈ rows,
      (∀ u ∈ row.1, covRSupport D u) ∧ covRSupport B row.2
  | _ => True

def covRArrow (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (positive : Bool)
    (Dty : Expr Nat) (D B : CovRRel) : CovRRel :=
  fun x y c => CovRFunctionShape c ∧ CovRLambdaRows D B c ∧
    (positive = true → c = .bot) ∧
    CovRArrowCoverage E D B c ∧ CovRArrowAction E n Γ Dty D B x y c

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  {positive domainPositive : Bool} {Dty : Expr Nat} {D B : CovRRel}

theorem covRArrow_intro {x y : Expr Nat} {c : CptT}
    (hs : CovRFunctionShape c)
    (hrows : CovRLambdaRows D B c)
    (hp : positive = true → c = .bot)
    (hc : CovRArrowCoverage E D B c)
    (ha : CovRArrowAction E n Γ Dty D B x y c) :
    covRArrow E n Γ positive Dty D B x y c :=
  ⟨hs, hrows, hp, hc, ha⟩

theorem covRArrow_shape {x y : Expr Nat} {c : CptT}
    (h : covRArrow E n Γ positive Dty D B x y c) : CovRFunctionShape c :=
  h.1

theorem covRArrow_rows {x y : Expr Nat} {c : CptT}
    (h : covRArrow E n Γ positive Dty D B x y c) : CovRLambdaRows D B c :=
  h.2.1

theorem covRArrow_coverage {x y : Expr Nat} {c : CptT}
    (h : covRArrow E n Γ positive Dty D B x y c) :
    CovRArrowCoverage E D B c :=
  h.2.2.2.1

/-- This is the literal finite-row witness represented by the coverage
field. Its output is a predicate rather than a finite descendant code. -/
theorem covRArrow_singleton_coverage {x y : Expr Nat} {c : CptT}
    (h : covRArrow E n Γ positive Dty D B x y c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction E c ds out)
    (hd : ∀ u ∈ ds, covRSupport D u) :
    ∃ row : List CptT × CovRRel, row ∈ [([], B)] ∧
      (∀ u ∈ row.1, u ∈ ds) ∧ covRSupport row.2 out :=
  ⟨([], B), List.mem_singleton_self _,
    (fun u hu => (List.not_mem_nil u hu).elim), h.2.2.2.1 ds out ha hd⟩

theorem covRArrow_apply {x y : Expr Nat} {c : CptT}
    (h : covRArrow E n Γ positive Dty D B x y c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction E c ds out)
    (N N' : Expr Nat) (hN : HasTyT E n Γ N Dty) (hN' : HasTyT E n Γ N' Dty)
    (hconv : Nonempty (ConvT E n Γ N N' Dty))
    (hd : ∀ u ∈ ds, D N N' u) : B (.app x N) (.app y N') out :=
  h.2.2.2.2 ds out ha N N' hN hN' hconv hd

theorem covRArrow_bot
    (hB : CandidateCov E (WhStepCK2 E n) Γ positive B) (x y : Expr Nat) :
    covRArrow E n Γ positive Dty D B x y .bot := by
  refine ⟨Or.inl rfl, trivial, fun _ => rfl, ?_, ?_⟩
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _

/-- Reflection supplies both coverage and every typed neutral application.
It needs no term inhabitant of the domain and no arbitrary-result axiom. -/
theorem covRArrow_neutral
    (hB : CandidateCov E (WhStepCK2 E n) Γ false B)
    (x y : Expr Nat) (r : Nat) (us : List CptT) (hh : NeutralHeadP E r) :
    covRArrow E n Γ false Dty D B x y (.spine r us) := by
  refine ⟨Or.inr (Or.inr ⟨r, us, rfl⟩), trivial, ?_, ?_, ?_⟩
  · intro he
    cases he
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
    | appSpine _ => exact covRSupport_intro (hB.neutral rfl x y r _ hh)
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _
    | appSpine _ => exact hB.neutral rfl _ _ r _ hh

/-- The ordinary arrow is a candidate. Transitivity uses a diagonal domain
witness and the same middle argument, so it needs no join of code tables. -/
theorem covRArrow_isCandidate
    (hD : CandidateCov E (WhStepCK2 E n) Γ domainPositive D)
    (hB : CandidateCov E (WhStepCK2 E n) Γ positive B) :
    CandidateCov E (WhStepCK2 E n) Γ positive
      (covRArrow E n Γ positive Dty D B) where
  symm := by
    intro x y c h
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    intro ds out ha N N' hN hN' hconv hd
    obtain ⟨hc⟩ := hconv
    exact hB.symm (h.2.2.2.2 ds out ha N' N hN' hN
      ⟨.symm _ _ _ _ hc⟩ (fun u hu => hD.symm (hd u hu)))
  trans := by
    intro x y z c hxy hyz
    refine ⟨hxy.1, hxy.2.1, hxy.2.2.1, hxy.2.2.2.1, ?_⟩
    intro ds out ha N N' hN hN' hconv hd
    have hleft := hxy.2.2.2.2 ds out ha N N hN hN ⟨.refl _ _ _ hN⟩
      (fun u hu => hD.self_left (hd u hu))
    have hright := hyz.2.2.2.2 ds out ha N N' hN hN' hconv hd
    exact hB.trans hleft hright
  readback := by
    intro x x' y c hx
    constructor
    · intro h
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
      intro ds out ha N N' hN hN' hconv hd
      exact (hB.readback (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mp
        (h.2.2.2.2 ds out ha N N' hN hN' hconv hd)
    · intro h
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
      intro ds out ha N N' hN hN' hconv hd
      exact (hB.readback (redR_appHead (readbackLaws_whStepCK2 E n) hx)).mpr
        (h.2.2.2.2 ds out ha N N' hN hN' hconv hd)
  bot := covRArrow_bot hB
  neutral := by
    intro he x y r us hh
    subst positive
    exact covRArrow_neutral hB x y r us hh
  collapse := by
    intro he x y c h
    exact h.2.2.1 he

/-- A concrete ordinary-arrow instance of the rigid identity. Its native
typing and observation are imported certificates; its arrow membership is
supplied by the new candidate operator, without an old CoreY result. -/
theorem covRArrow_rigidProp_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.app (.const 0 []) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero))) ∧
    Nonempty (ConvT covZRigidIdEnv n []
      (.app (.const 0 []) (.sort .zero)) (.app (.const 0 []) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero))) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.app (.const 0 []) (.sort .zero))
      (.spine 0 [.bot]) ∧
    covRArrow covZRigidIdEnv n [] false (.sort .zero)
      (covRCodeRel covZRigidIdEnv .prop) (covRCodeRel covZRigidIdEnv .prop)
      (.app (.const 0 []) (.sort .zero)) (.app (.const 0 []) (.sort .zero))
      (.spine 0 [.bot]) ∧
    CovXCompactAction covZRigidIdEnv (.spine 0 [.bot]) []
      (.spine 0 [.bot, .bot]) ∧
    covRCodeRel covZRigidIdEnv .prop
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.spine 0 [.bot, .bot]) ∧
    (CptT.spine 0 [.bot]) ≠ .bot ∧ (CptT.spine 0 [.bot, .bot]) ≠ .bot := by
  obtain ⟨⟨ht⟩, ho⟩ := covZRigidId_application_control n [] EnvT.bot
  have hB := covRProp_isCandidate covZRigidIdEnv (WhStepCK2 covZRigidIdEnv n) []
  have hrel := covRArrow_neutral
    (Dty := Expr.sort .zero) (D := covRCodeRel covZRigidIdEnv .prop) hB
    (.app (.const 0 []) (.sort .zero)) (.app (.const 0 []) (.sort .zero))
    0 [.bot] covPIdentity_neutral_head
  have ha : CovXCompactAction covZRigidIdEnv (.spine 0 [.bot]) []
      (.spine 0 [.bot, .bot]) := AppCptT.appSpine (.bot _ _)
  have hN := hasTyT_idPiProp_ctx covZRigidIdEnv n []
  have hout := covRArrow_apply hrel ha idPiProp idPiProp hN hN
    ⟨.refl _ _ _ hN⟩ (fun u hu => (List.not_mem_nil u hu).elim)
  exact ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    ho, hrel, ha, hout, CptT.noConfusion, CptT.noConfusion⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_ARROW_ROOTS
#print axioms covRSupport
#print axioms covRSupport_intro
#print axioms covRSupport_bot
#print axioms CovRArrowCoverage
#print axioms CovRArrowAction
#print axioms CovRFunctionShape
#print axioms CovRLambdaRows
#print axioms covRArrow
#print axioms covRArrow_intro
#print axioms covRArrow_shape
#print axioms covRArrow_rows
#print axioms covRArrow_coverage
#print axioms covRArrow_singleton_coverage
#print axioms covRArrow_apply
#print axioms covRArrow_bot
#print axioms covRArrow_neutral
#print axioms covRArrow_isCandidate
#print axioms covRArrow_rigidProp_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_ARROW_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
