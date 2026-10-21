import rcic.RcicPiSourceOrigin
import rcic.RcicPEqLeafTPropPins

/-! Native-checked source/occurrence tests.
The first group uses actual proof terms; the second is a type-level Pi
comparison with a genuine proof leaf INSIDE its domain. That second
comparison must keep its Pi head, not be misclassified as a proof-root
origin. None of these definitions changes the original reduction.
-/

namespace Rcic.Declarative.F8PiSourceOrigin.Pins

open PEqTProofFront

private abbrev Γ₀ : LCtx := []

/-- Actual root proof leaf, with common endpoint index P. -/
def proofStep : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ p q P :=
  .peq Γ₀ p q P
    ⟨.proof Γ₀ p q P P (P_ty Γ₀) (P_ty Γ₀) (p_ty Γ₀) (q_ty Γ₀),
      p_ty Γ₀, q_ty Γ₀⟩

def proofOrigin : OriginTrace proofStep :=
  .proof (P_ty Γ₀) (P_ty Γ₀) (p_ty Γ₀) (q_ty Γ₀) (p_ty Γ₀) (q_ty Γ₀)

/-- For this concrete origin the single uniqueness answer is refl. -/
def proofAnswer : proofOrigin.origin.Answer := .refl Γ₀ P

example : proofOrigin.origin.originTyping = p_ty Γ₀ := rfl
example : proofOrigin.origin.proofTyping = p_ty Γ₀ := rfl
example : proofOrigin.origin.cost < stepSize proofStep := proofOrigin.cost_lt

/-- Two actual outer index wrappers. The first uses a nonliteral
beta-expanded proposition index from the previously checked pins. -/
def wrappedStep :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ p q PEqLeafTPropPins.aliasP :=
  .conv Γ₀ p q PEqLeafTPropPins.aliasP PEqLeafTPropPins.aliasP
    (.conv Γ₀ p q P PEqLeafTPropPins.aliasP proofStep
      PEqLeafTPropPins.alias_chain.symmT)
    (.refl Γ₀ PEqLeafTPropPins.aliasP)

def wrappedOrigin : OriginTrace wrappedStep :=
  .conv (.refl Γ₀ PEqLeafTPropPins.aliasP)
    (.conv PEqLeafTPropPins.alias_chain.symmT proofOrigin)

/-- The original inputs are preserved literally; only `back` changes. -/
example : wrappedOrigin.origin.originTyping = proofOrigin.origin.originTyping := rfl
example : wrappedOrigin.origin.proofTyping = proofOrigin.origin.proofTyping := rfl
example : wrappedOrigin.origin.cost = proofOrigin.origin.cost := rfl
example : wrappedOrigin.origin.cost < stepSize wrappedStep := wrappedOrigin.cost_lt

def wrappedOther :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ p p PEqLeafTPropPins.aliasP :=
  .refl Γ₀ p PEqLeafTPropPins.aliasP
    (hasTyT_of_tyConvT (p_ty Γ₀) PEqLeafTPropPins.alias_chain.symmT)

/-- Join plus reconciliation at the original nonliteral index. -/
def wrappedJoined :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ q p PEqLeafTPropPins.aliasP ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ p p PEqLeafTPropPins.aliasP ×'
        ConvT emptyEnv 0 Γ₀ q p PEqLeafTPropPins.aliasP) :=
  wrappedOrigin.origin.finish_peak (.refl Γ₀ P) wrappedStep wrappedOther

/-! A real type-level structural Pi leaf with proof-bearing domain.
K = fun z : P => Prop; A_p = K p; A_q = K q.
Both Pi types below have the same SORT index, not a proof index.
-/

def K : Expr Nat := .lam P (.sort .zero)
def domain (a : Expr Nat) : Expr Nat := .app K a

def K_ty (Γ : LCtx) :
    HasTyT emptyEnv 0 Γ K (.pi P (.sort (.succ .zero))) :=
  .lam Γ P .zero (.sort .zero) (.sort (.succ .zero))
    (P_ty Γ) (.sort (.assumption P :: Γ) .zero)

def domain_ty (Γ : LCtx) (a : Expr Nat) (ha : HasTyT emptyEnv 0 Γ a P) :
    HasTyT emptyEnv 0 Γ (domain a) (.sort (.succ .zero)) :=
  .app Γ K a P (.sort (.succ .zero)) (K_ty Γ) ha

def piSource : Expr Nat := .pi (domain p) (.sort .zero)
def piTarget : Expr Nat := .pi (domain q) (.sort .zero)
def piIndex : Expr Nat := .sort (.imax (.succ .zero) (.succ .zero))

def piSource_ty : HasTyT emptyEnv 0 Γ₀ piSource piIndex :=
  .pi Γ₀ (domain p) (.succ .zero) (.sort .zero) (.succ .zero)
    (domain_ty Γ₀ p (p_ty Γ₀)) (.sort [.assumption (domain p)] .zero)

def piTarget_ty : HasTyT emptyEnv 0 Γ₀ piTarget piIndex :=
  .pi Γ₀ (domain q) (.succ .zero) (.sort .zero) (.succ .zero)
    (domain_ty Γ₀ q (q_ty Γ₀)) (.sort [.assumption (domain q)] .zero)

def domainRaw : PEqT emptyEnv 0 Γ₀ (domain p) (domain q) :=
  .app Γ₀ K K p q (PEqT.refl K)
    (.proof Γ₀ p q P P (P_ty Γ₀) (P_ty Γ₀) (p_ty Γ₀) (q_ty Γ₀))

def piRaw : PEqT emptyEnv 0 Γ₀ piSource piTarget :=
  .pi Γ₀ (domain p) (domain q) (.sort .zero) (.sort .zero) domainRaw
    (.sort [.assumption (domain p)] .zero .zero (fun _ => rfl))

def piStructuralStep :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ₀ piSource piTarget piIndex :=
  .peq Γ₀ piSource piTarget piIndex ⟨piRaw, piSource_ty, piTarget_ty⟩

/-- A proof below the type's domain is NOT a proof of the whole source. -/
example : pi_source_head_or_origin piStructuralStep rfl =
    Sum.inl (PiHead.mk (domain q) (.sort .zero) rfl) := rfl

theorem structural_pi_not_origin (ht : OriginTrace piStructuralStep) : False := by
  cases ht

/-- A generic exact interface check: an actual head escape gives a
local strict bound, without adding a global U hypothesis. -/
example {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ (.pi A B) b T)
    (hescape : ∀ C D : Expr Nat, b ≠ .pi C D) :
    (pi_escape_origin h hescape).origin.cost < stepSize h :=
  (pi_escape_origin h hescape).cost_lt

/-- The iota wrapper propagates source provenance without retyping its
origin fields. This is a generic constructor test, not a concrete claim
that a Pi-source escape exists in an admitted environment. -/
example {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c T : Expr Nat}
    {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hi : DerivedIotaU E b c) (hb : HasTyT E n Γ b T) (hc : HasTyT E n Γ c T)
    (ht : OriginTrace h) :
    (OriginTrace.iotaSpine hi hb hc ht).origin.cost = ht.origin.cost := rfl

end Rcic.Declarative.F8PiSourceOrigin.Pins
