import rcic.RcicProducerPositionCerts
import rcic.RcicDT0709EnvWf

/-!
A literal ConvT proof-index spine certifies the exact output of the existing
peqLeafT_reconcile_propIndex producer. Endpoint data come from the landed,
constructive endpoints3 package; the Prop-valued DT009 facade is not eliminated
into Type. No U/row oracle, new reduction producer or replacement EvPar is added.
The app/lam/pi fields of a general J remain unimplemented; the trace only follows
irr, symmetry, either transitivity branch and index conversion. closure_claim=0.
-/

namespace Rcic.Declarative.F8ConvProofProducer
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- A literal proof-index occurrence along an EXISTING ConvT spine.
This is occurrence evidence, not a replacement conversion relation. -/
inductive Trace : {a b T : Expr Nat} → ConvT E n Γ a b T → Type where
  | irr {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
      (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
      Trace (.irr Γ P p q hP hp hq)
  | symm {a b T : Expr Nat} {h : ConvT E n Γ a b T} (ht : Trace h) :
      Trace (.symm Γ a b T h)
  | transLeft {a b c T : Expr Nat} {h : ConvT E n Γ a b T}
      (k : ConvT E n Γ b c T) (ht : Trace h) : Trace (.trans Γ a b c T h k)
  | transRight {a b c T : Expr Nat} (h : ConvT E n Γ a b T)
      {k : ConvT E n Γ b c T} (ht : Trace k) : Trace (.trans Γ a b c T h k)
  | tyConv {a b T U : Expr Nat} {u : Level} {h : ConvT E n Γ a b T}
      (hc : ConvT E n Γ T U (.sort u)) (ht : Trace h) :
      Trace (.tyConv Γ a b T U u h hc)

structure PropIndex (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T : Expr Nat) where
  proposition : Expr Nat
  typing : HasTyT E n Γ proposition (.sort .zero)
  chain : TyConvT E n Γ T proposition

/-- Follow only original proof/index-preserving fields. An index exchange
is inverted as a chain; its result never becomes a new U input. -/
def Trace.certificate : {a b T : Expr Nat} → {h : ConvT E n Γ a b T} →
    Trace h → PropIndex E n Γ T
  | _, _, _, _, .irr hP _ _ => ⟨_, hP, .refl _ _⟩
  | _, _, _, _, .symm ht => ht.certificate
  | _, _, _, _, .transLeft _ ht => ht.certificate
  | _, _, _, _, .transRight _ ht => ht.certificate
  | _, _, _, _, .tyConv hc ht =>
      let c := ht.certificate
      ⟨c.proposition, c.typing,
        .trans _ _ _ _ (.of _ _ _ _ (.symm _ _ _ _ hc)) c.chain⟩

open F8Occurrences

/-- A certificate on the EXACT existing proof-index producer. No new ParRedT
producer is introduced; no global J or EvPar admissibility is asserted. -/
def Trace.outputRequests (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (ht : Trace h) :
    let c := ht.certificate
    let ep := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW) hΓ h
    Requests (.peq Γ a b T (peqLeafT_reconcile_propIndex c.typing c.chain ep.1 ep.2.1).1) :=
  let c := ht.certificate
  let ep := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ h
  rootRequests c.typing c.chain ep.1 ep.2.1

def Trace.outputAnswers (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (ht : Trace h) :
    let c := ht.certificate
    let ep := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW) hΓ h
    AnsweredOrigins (.peq Γ a b T (peqLeafT_reconcile_propIndex c.typing c.chain ep.1 ep.2.1).1)
      (ht.outputRequests hW hΓ) :=
  let c := ht.certificate
  let ep := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ h
  rootAnswers c.typing c.chain ep.1 ep.2.1

/-- The position index is the original ConvT index T on BOTH output sides. -/
theorem Trace.output_index (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (ht : Trace h)
    (side : Side) : (ht.outputRequests hW hΓ PUnit.unit side).index = T := by
  cases side <;> rfl

/-- Answers are the chain read off the original conversion spine, not a new
uniqueness request on materialized endpoint typings. -/
theorem Trace.output_answer (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (ht : Trace h)
    (side : Side) : HEq (ht.outputAnswers hW hΓ PUnit.unit side) ht.certificate.chain := by
  cases side <;> rfl

end Rcic.Declarative.F8ConvProofProducer
