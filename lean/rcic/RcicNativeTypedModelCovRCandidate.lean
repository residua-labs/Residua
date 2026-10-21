import rcic.RcicNativeTypedModelCovQUniverse
import rcic.RcicNativeTypedModelCovRImpredicative

/-!
# Prop-valued candidates and their actual compact-typing leaves

A candidate is a supplied relation together with a proposition asserting its
closure laws. Quantification ranges over those predicates and proofs inside
Prop; it does not construct a recursive universe of Type-valued candidates.

The Boolean classifies the interpreted type: `true` is a positive proposition
and collapses every admitted compact to bottom; `false` accepts ordinary
body-free neutral compacts. The universe code `.prop` is in the latter class.
No theorem here infers this Boolean from native universe typing.

The concrete leaves retain exactly `CTyCovQ` at their displayed code. They are
endpoint-independent compact-typing relations, with nontrivial acceptance and
rejection properties. They do not assert native conversion or a global native
adequacy theorem. Ordinary Pi rows and syntax interpretation are separate.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovPAudit TypedModelCovQAudit

universe u

abbrev CovRRel := Expr Nat → Expr Nat → CptT → Prop

/-- Closure is a proposition about a predicate supplied independently. The
neutral rule concerns the candidate's tag, not positivity of its value compact. -/
structure CandidateCov (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) (S : CovRRel) : Prop where
  symm : ∀ {x y c}, S x y c → S y x c
  trans : ∀ {x y z c}, S x y c → S y z c → S x z c
  readback : ∀ {x x' y c}, RedR R Γ x x' → (S x y c ↔ S x' y c)
  bot : ∀ x y, S x y .bot
  neutral : positive = false → ∀ x y r us,
    NeutralHeadP E r → S x y (.spine r us)
  collapse : positive = true → ∀ {x y c}, S x y c → c = .bot

variable {E : ResolvedEnv} {R : Readback} {Γ : LCtx}
  {positive : Bool} {S : CovRRel}

theorem CandidateCov.readback_right (hS : CandidateCov E R Γ positive S)
    {x y y' : Expr Nat} {c : CptT} (hy : RedR R Γ y y') :
    S x y c ↔ S x y' c := by
  constructor
  · intro h
    exact hS.symm ((hS.readback hy).mp (hS.symm h))
  · intro h
    exact hS.symm ((hS.readback hy).mpr (hS.symm h))

theorem CandidateCov.readback_both (hS : CandidateCov E R Γ positive S)
    {x x' y y' : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y') :
    S x y c ↔ S x' y' c :=
  (hS.readback hx).trans (hS.readback_right hy)

theorem CandidateCov.self_left (hS : CandidateCov E R Γ positive S)
    {x y : Expr Nat} {c : CptT} (h : S x y c) : S x x c :=
  hS.trans h (hS.symm h)

theorem CandidateCov.self_right (hS : CandidateCov E R Γ positive S)
    {x y : Expr Nat} {c : CptT} (h : S x y c) : S y y c :=
  hS.trans (hS.symm h) h

theorem CandidateCov.positive_iff_bot (hS : CandidateCov E R Γ true S)
    (x y : Expr Nat) (c : CptT) : S x y c ↔ c = .bot := by
  constructor
  · exact hS.collapse rfl
  · intro h
    subst c
    exact hS.bot x y

/-- An optional data package. The closure predicate remains Prop-valued, and
the quantifier below uses the relation and its proof directly. -/
def CovRCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) := {S : CovRRel // CandidateCov E R Γ positive S}

/-- Impredicative universal quantification over all candidates of one tag. -/
def candidateAll (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) (Body : CovRRel → Prop) : Prop :=
  ∀ S : CovRRel, CandidateCov E R Γ positive S → Body S

theorem candidateAll_elim {Body : CovRRel → Prop}
    (h : candidateAll E R Γ positive Body)
    (hS : CandidateCov E R Γ positive S) : Body S :=
  h S hS

/-- Lift an actual compact predicate without imposing endpoint conditions. -/
def covRCompactRel (G : CptT → Prop) : CovRRel := fun _ _ c => G c

theorem covRCandidate_compact (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) (G : CptT → Prop) (hb : G .bot)
    (hn : positive = false → ∀ r us, NeutralHeadP E r → G (.spine r us))
    (hp : positive = true → ∀ c, G c → c = .bot) :
    CandidateCov E R Γ positive (covRCompactRel G) where
  symm := fun h => h
  trans := fun h _ => h
  readback := fun _ => Iff.rfl
  bot := fun _ _ => hb
  neutral := fun he _ _ r us hh => hn he r us hh
  collapse := by
    intro he x y c h
    exact hp he c h

/-- A positive candidate admits exactly bottom, at every endpoint pair. -/
def covRPositiveRel : CovRRel := covRCompactRel (fun c => c = .bot)

theorem covRPositive_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx) :
    CandidateCov E R Γ true covRPositiveRel := by
  apply covRCandidate_compact
  · rfl
  · intro h
    cases h
  · intro _ _ h
    exact h

/-- The leaf predicate is literally the repaired compact typing at `a`. -/
def covRCodeRel (E : ResolvedEnv) (a : CptT) : CovRRel :=
  covRCompactRel (fun c => CTyCovQ E c a)

theorem covRCodeRel_iff (E : ResolvedEnv) (a c : CptT) (x y : Expr Nat) :
    covRCodeRel E a x y c ↔ CTyCovQ E c a := Iff.rfl

theorem covRProp_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx) :
    CandidateCov E R Γ false (covRCodeRel E .prop) := by
  apply covRCandidate_compact
  · exact ctyCovQ_bot E .prop
  · intro _ r us hh
    exact ctyCovQ_univNeutral hh
  · intro h
    cases h

theorem covRSort_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx) :
    CandidateCov E R Γ false (covRCodeRel E .sort) := by
  apply covRCandidate_compact
  · exact ctyCovQ_bot E .sort
  · intro _ r us _
    exact ctyCovQ_univType (.spine r us)
  · intro h
    cases h

theorem covRSpine_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (r : Nat) (us : List CptT) (hnp : ¬ IsPropCTP E (.spine r us)) :
    CandidateCov E R Γ false (covRCodeRel E (.spine r us)) := by
  apply covRCandidate_compact
  · exact ctyCovQ_bot E (.spine r us)
  · intro _ r' us' _
    exact ctyCovQ_of_P (CTyCovP2.spine hnp)
  · intro h
    cases h

theorem covRPositiveCode_isCandidate (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (a : CptT) (hp : IsPropCTP E a) :
    CandidateCov E R Γ true (covRCodeRel E a) := by
  apply covRCandidate_compact
  · exact ctyCovQ_bot E a
  · intro h
    cases h
  · intro _ c hc
    exact ctyCovQ_prop_bot hp hc

theorem covRProp_rejects_lam (E : ResolvedEnv) (x y : Expr Nat)
    (f : List (List CptT × CptT)) : ¬ covRCodeRel E .prop x y (.lam f) := by
  intro h
  rcases ctyCovQ_prop_inv h with hb | hp | ⟨r, us, he, _⟩
  · exact CptT.noConfusion hb
  · cases hp
  · exact CptT.noConfusion he

theorem covRSort_rejects_lam (E : ResolvedEnv) (x y : Expr Nat)
    (f : List (List CptT × CptT)) : ¬ covRCodeRel E .sort x y (.lam f) := by
  intro h
  rcases ctyCovQ_sort_inv h with hb | ht
  · exact CptT.noConfusion hb
  · cases ht

theorem covRSpine_rejects_lam (E : ResolvedEnv) (x y : Expr Nat)
    (r : Nat) (us : List CptT) (f : List (List CptT × CptT)) :
    ¬ covRCodeRel E (.spine r us) x y (.lam f) := by
  intro h
  rcases ctyCovQ_spine_inv h with hb | ⟨r', us', he⟩
  · exact CptT.noConfusion hb
  · exact CptT.noConfusion he

/-- This accepted compact is non-bottom; the universe leaf is not the
positive-proposition candidate. -/
theorem covRSort_accepts_prop (E : ResolvedEnv) (x y : Expr Nat) :
    covRCodeRel E .sort x y .prop :=
  ctyCovQ_univType .prop

/-- Every tag has an explicit candidate; universal quantification is never
made vacuous by an empty candidate class. -/
theorem covRCandidate_inhabited (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) : ∃ S : CovRRel, CandidateCov E R Γ positive S := by
  cases positive with
  | false => exact ⟨covRCodeRel E .prop, covRProp_isCandidate E R Γ⟩
  | true => exact ⟨covRPositiveRel, covRPositive_isCandidate E R Γ⟩

/-- Nonempty intersections preserve the positive-collapse condition as well
as the other candidate laws. An empty positive intersection would not. -/
def candidateMeet {ι : Type u} (F : ι → CovRRel) : CovRRel :=
  fun x y c => ∀ i, F i x y c

theorem candidateMeet_isCandidate {ι : Type u} (F : ι → CovRRel)
    (hi : Nonempty ι) (hF : ∀ i, CandidateCov E R Γ positive (F i)) :
    CandidateCov E R Γ positive (candidateMeet F) where
  symm := by
    intro x y c h i
    exact (hF i).symm (h i)
  trans := by
    intro x y z c hxy hyz i
    exact (hF i).trans (hxy i) (hyz i)
  readback := by
    intro x x' y c hx
    constructor
    · intro h i
      exact ((hF i).readback hx).mp (h i)
    · intro h i
      exact ((hF i).readback hx).mpr (h i)
  bot := by
    intro x y i
    exact (hF i).bot x y
  neutral := by
    intro he x y r us hh i
    exact (hF i).neutral he x y r us hh
  collapse := by
    intro he x y c h
    rcases hi with ⟨i⟩
    exact (hF i).collapse he (h i)

/-- The actual intersection of all candidates, quantified within Prop. -/
def candidateIntersection (E : ResolvedEnv) (R : Readback) (Γ : LCtx)
    (positive : Bool) : CovRRel :=
  fun x y c => candidateAll E R Γ positive (fun S => S x y c)

theorem candidateIntersection_isCandidate (E : ResolvedEnv) (R : Readback)
    (Γ : LCtx) (positive : Bool) :
    CandidateCov E R Γ positive (candidateIntersection E R Γ positive) where
  symm := by
    intro x y c h S hS
    exact hS.symm (h S hS)
  trans := by
    intro x y z c hxy hyz S hS
    exact hS.trans (hxy S hS) (hyz S hS)
  readback := by
    intro x x' y c hx
    constructor
    · intro h S hS
      exact (hS.readback hx).mp (h S hS)
    · intro h S hS
      exact (hS.readback hx).mpr (h S hS)
  bot := by
    intro x y S hS
    exact hS.bot x y
  neutral := by
    intro he x y r us hh S hS
    exact hS.neutral he x y r us hh
  collapse := by
    intro he x y c h
    obtain ⟨S, hS⟩ := covRCandidate_inhabited E R Γ positive
    exact hS.collapse he (h S hS)

theorem candidateIntersection_elim (hS : CandidateCov E R Γ positive S)
    {x y : Expr Nat} {c : CptT}
    (h : candidateIntersection E R Γ positive x y c) : S x y c :=
  h S hS

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_CANDIDATE_ROOTS
#print axioms CovRRel
#print axioms CandidateCov
#print axioms CandidateCov.readback_right
#print axioms CandidateCov.readback_both
#print axioms CandidateCov.self_left
#print axioms CandidateCov.self_right
#print axioms CandidateCov.positive_iff_bot
#print axioms CovRCandidate
#print axioms candidateAll
#print axioms candidateAll_elim
#print axioms covRCompactRel
#print axioms covRCandidate_compact
#print axioms covRPositiveRel
#print axioms covRPositive_isCandidate
#print axioms covRCodeRel
#print axioms covRCodeRel_iff
#print axioms covRProp_isCandidate
#print axioms covRSort_isCandidate
#print axioms covRSpine_isCandidate
#print axioms covRPositiveCode_isCandidate
#print axioms covRProp_rejects_lam
#print axioms covRSort_rejects_lam
#print axioms covRSpine_rejects_lam
#print axioms covRSort_accepts_prop
#print axioms covRCandidate_inhabited
#print axioms candidateMeet
#print axioms candidateMeet_isCandidate
#print axioms candidateIntersection
#print axioms candidateIntersection_isCandidate
#print axioms candidateIntersection_elim
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_CANDIDATE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
