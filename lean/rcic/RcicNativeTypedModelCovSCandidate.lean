import rcic.RcicNativeTypedModelCovRCandidate

/-!
# Candidate closure with total positive propositions

This additive interface preserves the PER, readback, bottom and data-neutral
laws of the R candidate interface. Its positive law is totality. It does not
assert bottom-only observation of proofs and does not change ApproxTK, CTyS,
the saturated K guard, or any landed statement. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovPAudit TypedModelCovRAudit

universe u

abbrev CovSRel := CovRRel

/-- A supplied positive proposition relates every pair at every compact.
The false-tag neutral rule retains the earlier body-free-head boundary. -/
structure CandidateCovS (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) (S : CovSRel) : Prop where
  symm : ∀ {x y c}, S x y c → S y x c
  trans : ∀ {x y z c}, S x y c → S y z c → S x z c
  readback : ∀ {x x' y c}, RedR R Γ x x' → (S x y c ↔ S x' y c)
  bot : ∀ x y, S x y .bot
  neutral : positive = false → ∀ x y r us,
    NeutralHeadP E r → S x y (.spine r us)
  positive_total : positive = true → ∀ x y c, S x y c

variable {E : ResolvedEnv} {R : Readback} {Γ : LCtx}
  {positive : Bool} {S : CovSRel}

theorem CandidateCovS.readback_right (hS : CandidateCovS E R Γ positive S)
    {x y y' : Expr Nat} {c : CptT} (hy : RedR R Γ y y') :
    S x y c ↔ S x y' c := by
  constructor
  · intro h
    exact hS.symm ((hS.readback hy).mp (hS.symm h))
  · intro h
    exact hS.symm ((hS.readback hy).mpr (hS.symm h))

theorem CandidateCovS.readback_both (hS : CandidateCovS E R Γ positive S)
    {x x' y y' : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y') :
    S x y c ↔ S x' y' c :=
  (hS.readback hx).trans (hS.readback_right hy)

theorem CandidateCovS.self_left (hS : CandidateCovS E R Γ positive S)
    {x y : Expr Nat} {c : CptT} (h : S x y c) : S x x c :=
  hS.trans h (hS.symm h)

theorem CandidateCovS.self_right (hS : CandidateCovS E R Γ positive S)
    {x y : Expr Nat} {c : CptT} (h : S x y c) : S y y c :=
  hS.trans (hS.symm h) h

theorem CandidateCovS.positive_iff_true (hS : CandidateCovS E R Γ true S)
    (x y : Expr Nat) (c : CptT) : S x y c ↔ True :=
  ⟨fun _ => trivial, fun _ => hS.positive_total rfl x y c⟩

/-- The canonical total PER. False-tag use expresses lack of information;
positive use expresses proof irrelevance, without erasing observations. -/
def covSTotalRel : CovSRel := fun _ _ _ => True

theorem covSTotal_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) : CandidateCovS E R Γ positive covSTotalRel where
  symm := fun _ => trivial
  trans := fun _ _ => trivial
  readback := fun _ => Iff.rfl
  bot := fun _ _ => trivial
  neutral := fun _ _ _ _ _ _ => trivial
  positive_total := fun _ _ _ _ => trivial

/-- Embedding at the unchanged false tag. No positive R candidate is
silently relabeled as total, and no ordinary-arrow clause is modified. -/
theorem candidateCovS_of_R_false (hS : CandidateCov E R Γ false S) :
    CandidateCovS E R Γ false S where
  symm := hS.symm
  trans := hS.trans
  readback := hS.readback
  bot := hS.bot
  neutral := hS.neutral
  positive_total := by
    intro he
    cases he

/-- At the false tag the two interfaces have the same fields. This named
inverse permits reuse of an old data operator without changing its clause. -/
theorem candidateCovR_of_S_false (hS : CandidateCovS E R Γ false S) :
    CandidateCov E R Γ false S where
  symm := hS.symm
  trans := hS.trans
  readback := hS.readback
  bot := hS.bot
  neutral := hS.neutral
  collapse := by
    intro he
    cases he

/-- Pointwise intersection, with a possibly empty index sort. -/
def covSMeet {ι : Sort u} (F : ι → CovSRel) : CovSRel :=
  fun x y c => ∀ i, F i x y c

/-- Totality is closed under arbitrary intersection, including the empty
one. No chosen index or nonempty-index premise is required. -/
theorem covSMeet_isCandidate {ι : Sort u} {F : ι → CovSRel}
    (hF : ∀ i, CandidateCovS E R Γ positive (F i)) :
    CandidateCovS E R Γ positive (covSMeet F) where
  symm := fun h i => (hF i).symm (h i)
  trans := fun h₁ h₂ i => (hF i).trans (h₁ i) (h₂ i)
  readback := by
    intro x x' y c hx
    constructor
    · intro h i
      exact ((hF i).readback hx).mp (h i)
    · intro h i
      exact ((hF i).readback hx).mpr (h i)
  bot := fun x y i => (hF i).bot x y
  neutral := fun hp x y r us hh i => (hF i).neutral hp x y r us hh
  positive_total := fun hp x y c i => (hF i).positive_total hp x y c

theorem CandidateCovS.positive_eq_total (hS : CandidateCovS E R Γ true S) :
    S = covSTotalRel := by
  funext x y c
  exact propext (hS.positive_iff_true x y c)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_CANDIDATE_ROOTS
#print axioms CovSRel
#print axioms CandidateCovS
#print axioms CandidateCovS.readback_right
#print axioms CandidateCovS.readback_both
#print axioms CandidateCovS.self_left
#print axioms CandidateCovS.self_right
#print axioms CandidateCovS.positive_iff_true
#print axioms covSTotalRel
#print axioms covSTotal_isCandidate
#print axioms candidateCovS_of_R_false
#print axioms candidateCovR_of_S_false
#print axioms covSMeet
#print axioms covSMeet_isCandidate
#print axioms CandidateCovS.positive_eq_total
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_CANDIDATE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
