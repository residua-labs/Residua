import rcic.RcicF8JTotality
import rcic.RcicF8JSameOutput

/-!
JT-2: certified answers on independently named subsets of the fixed pre-answer
X demand. Design credit: ChatGPT, S0_J_TOTALITY (#7194), sections 6 and 8.
These adapters call the landed J fronts; they introduce no traversal and never
filter NeedW. Wf answers require their own source context witness. Via answers
retain the request's original v, h, hs and occurrence address.
The full-domain obligation below is only an interface; JT-3/4 remain separate.
W-SEPALL-UNCOND remains owned by packaging. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JTotality
variable {E : ResolvedEnv} {n : Nat}

/-- Availability, strict support and exact certificates for this actual output.
The Option index prevents substituting another valley with matching endpoints. -/
structure CertifiedAnswer (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T)
    (answer : Option (Valley R Γ a b T)) where
  valley : Valley R Γ a b T
  returned : answer = some valley
  strict : ∀ l ∈ valley.leaves, SubOf l (.cv h)
  tiles : SameOutputStepCertificates hW R h valley

abbrev AnswerAtW (hW : EnvWfT E) (J : ∀ R : List (Jd E n), JProcViaP R)
    {C : XEntryW E n} (q : JRequestW C) :=
  CertifiedAnswer hW C.R q.h (q.answer J)

/-- Source Wf is supplied explicitly; the target proof in q.v is insufficient. -/
abbrev AnswerAtWf (hW : EnvWfT E) (J : ∀ R : List (Jd E n), JProcWfP R)
    {C : XEntryW E n} (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :=
  CertifiedAnswer hW C.R q.h (J C.R hΓ q.h q.hs)

/-- Future whole-domain contract, not asserted for any current partial front. -/
def AnswerOnDemandW (hW : EnvWfT E) (J : ∀ R : List (Jd E n), JProcViaP R) : Type :=
  ∀ (C : XEntryW E n) (q : JRequestW C), NeedW C q → AnswerAtW hW J q

/-- Fixed source grammars intersect the original demand; success is not an input. -/
def J1Domain {C : XEntryW E n} (q : JRequestW C) : Prop :=
  NeedW C q ∧ J1.isBase q.h = true

def J3Domain {C : XEntryW E n} (q : JRequestW C) : Prop :=
  NeedW C q ∧ J3.supported q.h = true

def J5aDomain {C : XEntryW E n} (q : JRequestW C) : Prop :=
  NeedW C q ∧ J5a.fragment q.h = true

private def present {α : Type} (o : Option α) (h : o.isSome = true) :
    {a : α // o = some a} := by
  cases he : o with
  | none => simp [he] at h
  | some a => exact ⟨a, rfl⟩

variable {C : XEntryW E n}

/-- Construct the actual J1 answer without choice. -/
def answerJ1 (hW : EnvWfT E) (q : JRequestW C)
    (hf : J1.isBase q.h = true) : AnswerAtW hW (j1Via hW) q := by
  let p := present (J1.dispatchVia hW C.R q.v q.h q.hs)
    ((J1.dispatchVia_coverage hW C.R q.v q.h q.hs).trans hf)
  exact ⟨p.val.valley, by simp [JRequestW.answer, j1Via, p.property],
    p.val.strict, p.val.sameOutput⟩

def answerJ3 (hW : EnvWfT E) (q : JRequestW C)
    (hf : J3.supported q.h = true) : AnswerAtW hW (j3Via hW) q := by
  let p := present (J3.dispatchVia hW C.R q.v q.h q.hs)
    ((J3.dispatchVia_coverage hW C.R q.v q.h q.hs).trans hf)
  exact ⟨p.val.valley, by simp [JRequestW.answer, j3Via, p.property],
    p.val.strict, p.val.sameOutput⟩

/-- Uses the landed Via-trans builder, including its actual D execution/read. -/
def answerJ5a (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (hf : J5a.fragment q.h = true) :
    AnswerAtW hW (j5aVia hW su) q := by
  let p := J5aVia.buildFragment hW su C.R q.v q.h hf q.hs
  exact ⟨p.valley, by simp [JRequestW.answer, j5aVia, J5aVia.dispatchVia, hf, p],
    p.strict, p.sameOutput⟩

/-- Restricting availability never changes the source-independent demand. -/
def answerOnJ1Domain (hW : EnvWfT E) (q : JRequestW C) (hq : J1Domain q) :
    AnswerAtW hW (j1Via hW) q := answerJ1 hW q hq.2

def answerOnJ3Domain (hW : EnvWfT E) (q : JRequestW C) (hq : J3Domain q) :
    AnswerAtW hW (j3Via hW) q := answerJ3 hW q hq.2

def answerOnJ5aDomain (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (hq : J5aDomain q) : AnswerAtW hW (j5aVia hW su) q :=
  answerJ5a hW su q hq.2

theorem j1_answer_coverage (hW : EnvWfT E) (q : JRequestW C) :
    (q.answer (j1Via hW)).isSome = J1.isBase q.h := by
  simp only [JRequestW.answer, j1Via, Option.isSome_map']
  exact J1.dispatchVia_coverage hW C.R q.v q.h q.hs

theorem j3_answer_coverage (hW : EnvWfT E) (q : JRequestW C) :
    (q.answer (j3Via hW)).isSome = J3.supported q.h := by
  simp only [JRequestW.answer, j3Via, Option.isSome_map']
  exact J3.dispatchVia_coverage hW C.R q.v q.h q.hs

theorem j5a_answer_coverage (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) :
    (q.answer (j5aVia hW su)).isSome = J5a.fragment q.h := by
  simp only [JRequestW.answer, j5aVia, Option.isSome_map']
  exact J5aVia.dispatchVia_coverage hW su C.R q.v q.h q.hs

theorem j1_exact_answered_domain (hW : EnvWfT E) (q : JRequestW C) :
    (NeedW C q ∧ (q.answer (j1Via hW)).isSome = true) ↔ J1Domain q := by
  rw [j1_answer_coverage]; rfl

theorem j3_exact_answered_domain (hW : EnvWfT E) (q : JRequestW C) :
    (NeedW C q ∧ (q.answer (j3Via hW)).isSome = true) ↔ J3Domain q := by
  rw [j3_answer_coverage]; rfl

theorem j5a_exact_answered_domain (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) :
    (NeedW C q ∧ (q.answer (j5aVia hW su)).isSome = true) ↔ J5aDomain q := by
  rw [j5a_answer_coverage]; rfl

theorem j1_certified_answered_domain (hW : EnvWfT E)
    (q : JRequestW C) :
    (NeedW C q ∧ Nonempty (AnswerAtW hW (j1Via hW) q)) ↔ J1Domain q := by
  constructor
  · rintro ⟨hn, ⟨p⟩⟩
    apply (j1_exact_answered_domain hW q).mp
    exact ⟨hn, by rw [p.returned]; rfl⟩
  · intro hq
    exact ⟨hq.1, ⟨answerOnJ1Domain hW q hq⟩⟩

theorem j3_certified_answered_domain (hW : EnvWfT E)
    (q : JRequestW C) :
    (NeedW C q ∧ Nonempty (AnswerAtW hW (j3Via hW) q)) ↔ J3Domain q := by
  constructor
  · rintro ⟨hn, ⟨p⟩⟩
    apply (j3_exact_answered_domain hW q).mp
    exact ⟨hn, by rw [p.returned]; rfl⟩
  · intro hq
    exact ⟨hq.1, ⟨answerOnJ3Domain hW q hq⟩⟩

theorem j5a_certified_answered_domain (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) :
    (NeedW C q ∧ Nonempty (AnswerAtW hW (j5aVia hW su) q)) ↔ J5aDomain q := by
  constructor
  · rintro ⟨hn, ⟨p⟩⟩
    apply (j5a_exact_answered_domain hW su q).mp
    exact ⟨hn, by rw [p.returned]; rfl⟩
  · intro hq
    exact ⟨hq.1, ⟨answerOnJ5aDomain hW su q hq⟩⟩

/-- Every successful output has certificates for that same returned valley. -/
def certifyJ1Returned (hW : EnvWfT E) (q : JRequestW C)
    (V : Valley C.R q.Γ₀ q.a q.b q.T) (he : q.answer (j1Via hW) = some V) :
    SameOutputStepCertificates hW C.R q.h V := by
  have hf : J1.isBase q.h = true := by
    rw [← j1_answer_coverage hW q, he]; rfl
  let p := answerJ1 hW q hf
  have hv : p.valley = V := Option.some.inj (p.returned.symm.trans he)
  exact hv ▸ p.tiles

def certifyJ3Returned (hW : EnvWfT E) (q : JRequestW C)
    (V : Valley C.R q.Γ₀ q.a q.b q.T) (he : q.answer (j3Via hW) = some V) :
    SameOutputStepCertificates hW C.R q.h V := by
  have hf : J3.supported q.h = true := by
    rw [← j3_answer_coverage hW q, he]; rfl
  let p := answerJ3 hW q hf
  have hv : p.valley = V := Option.some.inj (p.returned.symm.trans he)
  exact hv ▸ p.tiles

def certifyJ5aReturned (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (V : Valley C.R q.Γ₀ q.a q.b q.T)
    (he : q.answer (j5aVia hW su) = some V) :
    SameOutputStepCertificates hW C.R q.h V := by
  have hf : J5a.fragment q.h = true := by
    rw [← j5a_answer_coverage hW su q, he]; rfl
  let p := answerJ5a hW su q hf
  have hv : p.valley = V := Option.some.inj (p.returned.symm.trans he)
  exact hv ▸ p.tiles

/-- Wf restriction at the original source context, with exact original fronts. -/
def j1Wf (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => (J1.dispatchWf hW R hΓ h hs).map (·.valley)

def j3Wf (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => (J3.dispatchWf hW R hΓ h hs).map (·.valley)

def j5aWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => (J5a.dispatchWf hW su R hΓ h hs).map (·.valley)

theorem j1_wf_restriction (hW : EnvWfT E)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    JProcViaP.toWfP (j1Via hW) C.R hΓ q.h q.hs =
      j1Wf hW C.R hΓ q.h q.hs := by
  unfold JProcViaP.toWfP j1Via j1Wf
  rw [J1.dispatchVia_ofWf]

theorem j3_wf_restriction (hW : EnvWfT E)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    JProcViaP.toWfP (j3Via hW) C.R hΓ q.h q.hs =
      j3Wf hW C.R hΓ q.h q.hs := by
  unfold JProcViaP.toWfP j3Via j3Wf
  rw [J3.dispatchVia_ofWf]

theorem j5a_wf_restriction (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    JProcViaP.toWfP (j5aVia hW su) C.R hΓ q.h q.hs =
      j5aWf hW su C.R hΓ q.h q.hs := by
  unfold JProcViaP.toWfP j5aVia j5aWf
  rw [J5aVia.dispatchVia_ofWf]

def answerJ1Wf (hW : EnvWfT E) (q : JRequestW C)
    (hΓ : CtxWfT E n q.Γ₀) (hf : J1.isBase q.h = true) :
    AnswerAtWf hW (j1Wf hW) q hΓ := by
  let p := present (J1.dispatchWf hW C.R hΓ q.h q.hs)
    ((J1.dispatchWf_coverage hW hΓ q.h q.hs).trans hf)
  exact ⟨p.val.valley, by simp [j1Wf, p.property], p.val.strict, p.val.sameOutput⟩

def answerJ3Wf (hW : EnvWfT E) (q : JRequestW C)
    (hΓ : CtxWfT E n q.Γ₀) (hf : J3.supported q.h = true) :
    AnswerAtWf hW (j3Wf hW) q hΓ := by
  let p := present (J3.dispatchWf hW C.R hΓ q.h q.hs)
    ((J3.dispatchWf_coverage hW hΓ q.h q.hs).trans hf)
  exact ⟨p.val.valley, by simp [j3Wf, p.property], p.val.strict, p.val.sameOutput⟩

def answerJ5aWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) (hf : J5a.fragment q.h = true) :
    AnswerAtWf hW (j5aWf hW su) q hΓ := by
  let p := J5a.buildFragment hW su C.R hΓ q.h hf q.hs
  exact ⟨p.valley, by simp [j5aWf, J5a.dispatchWf, hf, p], p.strict, p.sameOutput⟩

theorem j1_wf_exact_answered_domain (hW : EnvWfT E)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    (NeedW C q ∧ (j1Wf hW C.R hΓ q.h q.hs).isSome = true) ↔ J1Domain q := by
  have hc : (j1Wf hW C.R hΓ q.h q.hs).isSome = J1.isBase q.h := by
    simp only [j1Wf, Option.isSome_map']
    exact J1.dispatchWf_coverage hW hΓ q.h q.hs
  rw [hc]; rfl

theorem j3_wf_exact_answered_domain (hW : EnvWfT E)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    (NeedW C q ∧ (j3Wf hW C.R hΓ q.h q.hs).isSome = true) ↔ J3Domain q := by
  have hc : (j3Wf hW C.R hΓ q.h q.hs).isSome = J3.supported q.h := by
    simp only [j3Wf, Option.isSome_map']
    exact J3.dispatchWf_coverage hW hΓ q.h q.hs
  rw [hc]; rfl

theorem j5a_wf_exact_answered_domain (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (q : JRequestW C) (hΓ : CtxWfT E n q.Γ₀) :
    (NeedW C q ∧ (j5aWf hW su C.R hΓ q.h q.hs).isSome = true) ↔ J5aDomain q := by
  have hc : (j5aWf hW su C.R hΓ q.h q.hs).isSome = J5a.fragment q.h := by
    simp only [j5aWf, Option.isSome_map']
    exact J5a.dispatchWf_coverage hW su C.R hΓ q.h q.hs
  rw [hc]; rfl

theorem j1Wf_contract (hW : EnvWfT E) : JContractWfP (j1Wf (n := n) hW) := by
  intro R Γ a b T hΓ h hs V he
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some'.mp he
  exact p.strict

theorem j3Wf_contract (hW : EnvWfT E) : JContractWfP (j3Wf (n := n) hW) := by
  intro R Γ a b T hΓ h hs V he
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some'.mp he
  exact p.strict

theorem j5aWf_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    JContractWfP (j5aWf hW su) := by
  intro R Γ a b T hΓ h hs V he
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some'.mp he
  exact p.strict

#print axioms answerJ1
#print axioms answerJ3
#print axioms answerJ5a
#print axioms j5a_exact_answered_domain
#print axioms certifyJ5aReturned
#print axioms answerJ5aWf
end Rcic.Declarative.F8Measure.JTotality
