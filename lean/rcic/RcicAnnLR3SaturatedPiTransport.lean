import rcic.RcicAnnLR3CandidateActionProducts

/-!
Paired product transport changes the domain relation, erasure and retained
body codes. Actual source Pi images and proof-product neutral closure
are retained. Product algebra only: no source Ty_pi/Conv_pi or complete
model is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedPiTransport
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction CandidateActionProducts
universe u v

theorem propositionPi_domain_transport
    {α : Type u} {erase erase' : α → Value}
    {D D' : α → α → Prop} (hD : RelLaws D) (hD' : RelLaws D')
    (hDD' : ∀ x y, D x y ↔ D' x y)
    (he : ∀ x, ValueEq (erase x) (erase' x))
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    (hne' : ∀ x, D' x x → CandidatePi.NonemptyValue (erase' x))
    {E : ResolvedEnvA} {F G : EnvironmentEval.FamilySyntax} {ν μ : Valuation}
    {ρ σ : EnvI} {B B' : ExprA} (A A' : ExprA) (lA lB lA' lB' : Level)
    (hB : eval ν lB = some 0) (hB' : eval μ lB' = some 0)
    (b : Body α erase D E F ν ρ B 0)
    (c : Body α erase' D' E G μ σ B' 0)
    (hbc : ∀ x, D x x → CodeRel (b.run x) (c.run x)) :
    CodeRel (propositionPi hD hne A lA lB hB b)
      (propositionPi hD' hne' A' lA' lB' hB' c) := by
  apply (zero_related_iff _ _).mpr
  have hdom := CandidatePi.functionPER_same erase hD hDD'
    (fun x hx => (hbc x hx).transport)
  have herase := CandidatePi.functionPER_erase_congr he D'
    (fun x => (view 0 (c.run x).code).relation)
  intro f g
  exact (propositionPi_el hD hne A lA lB hB b f g).trans
    ((hdom f g).trans ((herase f g).trans
      (propositionPi_el hD' hne' A' lA' lB' hB' c f g).symm))

theorem proof_product_saturated
    {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D)
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (b : Body α erase D E F ν ρ B 0)
    {f : Value} (hf : CandidatePi.Neutral f) :
    Member (proofCandidate hD hne b).relation f :=
  (proofCandidate hD hne b).reflect hf

theorem proof_product_reflected_application
    {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D)
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (b : Body α erase D E F ν ρ B 0)
    {f : Value} (hf : CandidatePi.Neutral f) {x y : α} (hxy : D x y) :
    (view 0 (b.run x).code).relation
      (NeutralPi.applyValue f (erase x)) (NeutralPi.applyValue f (erase y)) :=
  proof_product_saturated hD hne b hf x y hxy

end Rcic.Declarative.Ann.LR3.SaturatedPiTransport
