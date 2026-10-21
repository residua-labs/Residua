import rcic.RcicPiSourceOrigin
import rcic.RcicPEqLeafTIntro

/-!
# One-U origin consumers and answered generated leaves

There are two different ways to consume a located proof root.

* A bounded uniqueness induction hypothesis is called once, on exactly
  the original pair extracted by OriginTrace. Its input cost is strictly
  below the sum of the two ACTUAL peak derivation sizes. This is a local
  call-edge certificate, not a proof of the induction hypothesis or of
  its availability after J/D generated either peak input.
* The existing proof-index producer ALREADY has that answer. We return
  an OriginTrace indexed by its actual emitted step together with the
  existing chain. Reindexing and iotaSpine preserve this answer. These
  generated leaves need no uniqueness call or decrease claim at all.

The independently proved introduction-spine comparison can also answer
origins in its own syntax class. Pi syntax is outside that class; this
last consumer does not answer the unrestricted Pi-escape request.

Original judgments and producers are unchanged. closure_claim=0.
-/

namespace Rcic.Declarative.F8PiSourceOrigin
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {a b c T U P : Expr Nat}

/-- Only comparisons of THIS source below a given bound are available.
This is an induction-hypothesis interface, not global uniqueness. -/
abbrev SourceUniqueBelow (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a : Expr Nat) (bound : Nat) : Type :=
  ∀ {R S : Expr Nat} (hR : HasTyT E n Γ a R) (hS : HasTyT E n Γ a S),
    hasTyTSize hR + hasTyTSize hS < bound → TyConvT E n Γ R S

/-- One actual call, on the left peak input's original typing fields.
The generated index continuation and join are never recursive inputs. -/
def finish_peak_below_left
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T)
    (ht : OriginTrace h₁)
    (hU : SourceUniqueBelow E n Γ a (stepSize h₁ + stepSize h₂)) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  let o := ht.origin
  let ans := hU o.originTyping o.proofTyping
    (Nat.lt_of_lt_of_le ht.cost_lt (Nat.le_add_right _ _))
  o.finish_peak ans h₁ h₂

/-- The same output orientation when the proof origin is on the right.
Only the original right pair is passed to the bounded hypothesis. -/
def finish_peak_below_right
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T)
    (ht : OriginTrace h₂)
    (hU : SourceUniqueBelow E n Γ a (stepSize h₁ + stepSize h₂)) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  let o := ht.origin
  let ans := hU o.originTyping o.proofTyping
    (Nat.lt_of_lt_of_le ht.cost_lt (Nat.le_add_left _ _))
  o.finish_peak ans h₁ h₂

/-- Actual Pi-source peak dispatch: either both target heads remain Pi,
or a single bounded uniqueness call completes the whole peak. The first
outcome deliberately contains only shapes, not component conversions. -/
def pi_peak_dispatch_below {A B : Expr Nat}
    (h₁ : ParRedT (PEqLeafT E n) E n Γ (.pi A B) b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ (.pi A B) c T)
    (hU : SourceUniqueBelow E n Γ (.pi A B) (stepSize h₁ + stepSize h₂)) :
    Sum (PiHead b × PiHead c)
      (ParRedT (PEqLeafT E n) E n Γ b c T ×'
        (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T)) :=
  match pi_source_head_or_origin h₁ rfl with
  | .inr ht => .inr (finish_peak_below_left h₁ h₂ ht hU)
  | .inl head₁ =>
      match pi_source_head_or_origin h₂ rfl with
      | .inr ht => .inr (finish_peak_below_right h₁ h₂ ht hU)
      | .inl head₂ => .inl ⟨head₁, head₂⟩

/-- A concrete origin occurrence together with its ALREADY CONSTRUCTED
answer. Unlike a bounded callback this is data at this exact step. -/
abbrev AnsweredOrigin {a b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) : Type :=
  Σ' ht : OriginTrace h, ht.origin.Answer

/-- The answer to the origin created by the existing leaf producer is
exactly its supplied hTP. No equality testing or uniqueness is needed. -/
def generated_leaf_origin_answer
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
    AnsweredOrigin (.peq Γ a b T (peqLeafT_reconcile_propIndex hP hTP ha hb).1) :=
  ⟨.proof hP hP (hasTyT_of_tyConvT ha hTP) (hasTyT_of_tyConvT hb hTP) ha hb, hTP⟩

/-- Bound to the ACTUAL left output of the previously checked diamond
producer, not to a separately reimplemented model of that producer. -/
def generated_peak_origin_answer
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T) :
    AnsweredOrigin (parRedT_propIndex_diamond_data hP hTP h₁ h₂).1 :=
  generated_leaf_origin_answer hP hTP
    (parRedT_sr_peqT_val h₁) (parRedT_sr_peqT_val h₂)

/-- Original type fields remain unchanged when the step is reindexed;
its old answer is therefore still the answer to the traced origin. -/
def answered_origin_conv {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hc : TyConvT E n Γ T U) (known : AnsweredOrigin h) :
    AnsweredOrigin (.conv Γ a b T U h hc) :=
  let ⟨ht, answer⟩ := known
  ⟨.conv hc ht, answer⟩

/-- The source-preserving iota wrapper also retains the known answer.
The actual iota and endpoint premises must still be supplied. -/
def answered_origin_iotaSpine {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hi : DerivedIotaU E b c) (hb : HasTyT E n Γ b T)
    (hc : HasTyT E n Γ c T) (known : AnsweredOrigin h) :
    AnsweredOrigin (.iotaSpine Γ a b c T h hi hb hc) :=
  let ⟨ht, answer⟩ := known
  ⟨.iotaSpine hi hb hc ht, answer⟩

/-- A generated known origin is terminal, regardless of its size.
No bounded/global uniqueness argument is requested at this call site. -/
def finish_peak_answered
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T)
    (known : AnsweredOrigin h₁) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  let ⟨ht, answer⟩ := known
  ht.origin.finish_peak answer h₁ h₂

/-- Independent local solver for the already certified intro-spine
class. It compares the two original fields, not retyped copies. -/
def Origin.answer_intro (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (o : Origin E n Γ a T) (hs : introTypeSpine a = true) : o.Answer :=
  introTypeSpine_unique hcl hinst hs o.originTyping o.proofTyping

/-- Direct origin-to-join consumer with NO index-chain or U answer
input, when the origin's source has the independently proved intro spine. -/
def finish_origin_intro (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T)
    (ht : OriginTrace h₁) (hs : introTypeSpine a = true) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  ht.origin.finish_peak (ht.origin.answer_intro hcl hinst hs) h₁ h₂

end Rcic.Declarative.F8PiSourceOrigin
