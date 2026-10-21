import rcic.RcicNativeTypedModelProbe
import rcic.RcicNativePiProbeAlgebra
import rcic.RcicNativePiProbeModelBoundary

/-!
# The typed relation supplies specified probe observations

`LRSCoreS` is the superseding relation from `RcicNativeTypedModelRelS`.
Only its universe and bottom-domain, empty-graph Pi clauses are observed
here. The caller's Pi reduct is identified with the relation's witness
using normal uniqueness; the subsequent chain consumer threads that
same witness without transporting a compact through a middle term.

The source-model realization ports below are pointwise. They do not
assert raw backward `ApproxT` transport, or a global Fundamental lemma.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- The two model universe codes have exactly the sort readback clause.
Using `sortCode` keeps the proposition universe's `.prop` code. -/
theorem lrSCoreS_sortCode_iffT {Γ : LCtx} {M N I : Expr Nat} (u : Level) :
    LRSCoreS R E n Γ M N I (sortCode u) ↔ SortClauseT R Γ M N I := by
  rcases sortCode_prop_or_sort u with h | h
  · rw [h, lrSCoreS_prop_iff]
  · rw [h, lrSCoreS_sort_iff]

/-- A relation fact identifies the caller's exact left Pi observation.
This is a readback uniqueness argument, not a native Pi-injectivity call. -/
theorem piRead_of_lrSCoreS_leftT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {M N I A B : Expr Nat}
    (hrel : LRSCoreS R E n Γ M N I (.pi .bot []))
    (hread : RedR R Γ M (.pi A B)) :
    ∃ A' B', RedR R Γ N (.pi A' B') ∧
      Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  rw [LRSCoreS.eq_def] at hrel
  obtain ⟨_, A₁, B₁, A₂, B₂, hM, hN, _, hA, hB, _⟩ := hrel
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hread hM
  subst A₁
  subst B₁
  exact ⟨A₂, B₂, hN, hA, hB⟩

/-- Forward observation transport reads only the two selected relation
facts. The domain-context guard is passed to the relation supplier. -/
theorem probeTransport_of_lrSCoreS_probesT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {M N I : Expr Nat}
    (hsort : ∀ u, RedR R Γ M (.sort u) →
      LRSCoreS R E n Γ M N I (sortCode u))
    (hpi : ∀ A B, RedR R Γ M (.pi A B) →
      CtxWfT E n (.assumption A :: Γ) →
      LRSCoreS R E n Γ M N I (.pi .bot [])) :
    ProbeTransportT R E n Γ M N := by
  constructor
  · rintro ⟨u, hread⟩
    obtain ⟨_, _, v, _, hN⟩ := (lrSCoreS_sortCode_iffT u).mp (hsort u hread)
    exact ⟨v, hN⟩
  · intro A B hread hΓA
    exact piRead_of_lrSCoreS_leftT hL hNU (hpi A B hread hΓA) hread

/-- Both directions use the same endpoint relation supplier. Pi symmetry
is the imported bottom-probe theorem, with no ConvArgs/PER premises. -/
theorem probeEquiv_of_lrSCoreS_probesT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hsort : ∀ u, (RedR R Γ M (.sort u) ∨ RedR R Γ N (.sort u)) →
      LRSCoreS R E n Γ M N I (sortCode u))
    (hpi : ∀ A B, (RedR R Γ M (.pi A B) ∨ RedR R Γ N (.pi A B)) →
      CtxWfT E n (.assumption A :: Γ) →
      LRSCoreS R E n Γ M N I (.pi .bot [])) :
    ProbeEquivT R E n Γ M N := by
  refine ⟨probeTransport_of_lrSCoreS_probesT hL hNU
    (fun u hu => hsort u (Or.inl hu))
    (fun A B hread hΓA => hpi A B (Or.inl hread) hΓA), ?_⟩
  apply probeTransport_of_lrSCoreS_probesT hL hNU (I := I)
  · intro u hread
    apply (lrSCoreS_sortCode_iffT u).mpr
    obtain ⟨hi, v, w, hM, hN⟩ :=
      (lrSCoreS_sortCode_iffT u).mp (hsort u (Or.inr hread))
    exact ⟨hi, w, v, hN, hM⟩
  · intro A B hread hΓA
    exact piProbeS_symm hW hΓ (hpi A B (Or.inr hread) hΓA)

/-- Realize an observation of a substituted term in its original model
environment. The substitution and model environment remain explicit;
realizing the substituted expression alone does not supply this input.
Typed wrappers supply native typings and related substitutions separately. -/
structure ModelProbeAtSubstT (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (σ : SubstT) (e : Expr Nat) : Prop where
  sorts : ∀ u, RedR R Γ (substT σ e) (.sort u) → M.Ap ρ e (sortCode u)
  pis : ∀ A B, RedR R Γ (substT σ e) (.pi A B) →
    CtxWfT E n (.assumption A :: Γ) → M.Ap ρ e (.pi .bot [])

/-- The reusable related-substitution read-off. `hrel` is exactly a
FundTyAt/FundConvAt instance after selecting a related substitution;
the two realization inputs provide its disjunctive compact seed. -/
theorem probeEquiv_of_fundRelationT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {M : CtxModelT E}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ ρ' : EnvT} {σ σ' : SubstT}
    {e e' I : Expr Nat}
    (hleft : ModelProbeAtSubstT M R n Γ ρ σ e)
    (hright : ModelProbeAtSubstT M R n Γ ρ' σ' e')
    (hrel : ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e' c →
      LRSCoreS R E n Γ (substT σ e) (substT σ' e') I c) :
    ProbeEquivT R E n Γ (substT σ e) (substT σ' e') := by
  apply probeEquiv_of_lrSCoreS_probesT hL hNU hW hΓ (I := I)
  · intro u hread
    apply hrel (sortCode u)
    exact hread.elim (fun h => Or.inl (hleft.sorts u h))
      (fun h => Or.inr (hright.sorts u h))
  · intro A B hread hΓA
    apply hrel (.pi .bot [])
    exact hread.elim (fun h => Or.inl (hleft.pis A B h hΓA))
      (fun h => Or.inr (hright.pis A B h hΓA))

/-- Existing context realization is the identity-substitution instance. -/
theorem modelProbeAtSubst_id_of_realizedT {Γ : LCtx} {e : Expr Nat}
    (h : ProbeRealizedAtT R E n Γ e) :
    ModelProbeAtSubstT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ) SubstT.id e := by
  constructor
  · intro u hread
    exact h.1 u (by simpa only [substT_id] using hread)
  · intro A B hread hΓA
    exact h.2 A B (by simpa only [substT_id] using hread) hΓA

/-- Read the existing local conversion motive at the identity package.
The conversion's type is arbitrary, so this adapter also covers an old
index in `tyConv` without asserting that index has syntactic sort shape. -/
theorem probeEquiv_of_fundConvAtT (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (hId : RelSubstIdT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ))
    (hF : FundConvAt (ctxModelT_approxT E) R n Γ a b A)
    (ha : ProbeRealizedAtT R E n Γ a) (hb : ProbeRealizedAtT R E n Γ b) :
    ProbeEquivT R E n Γ a b := by
  have h := probeEquiv_of_fundRelationT hL hNU hW hΓ
    (modelProbeAtSubst_id_of_realizedT ha)
    (modelProbeAtSubst_id_of_realizedT hb)
    (fun c hc => hF hΓ hId c hc)
  simpa only [substT_id] using h

-- BEGIN RCIC_PI_PROBE_REL_BRIDGE_ROOTS
#print axioms lrSCoreS_sortCode_iffT
#print axioms piRead_of_lrSCoreS_leftT
#print axioms probeTransport_of_lrSCoreS_probesT
#print axioms probeEquiv_of_lrSCoreS_probesT
#print axioms ModelProbeAtSubstT
#print axioms probeEquiv_of_fundRelationT
#print axioms modelProbeAtSubst_id_of_realizedT
#print axioms probeEquiv_of_fundConvAtT
-- END RCIC_PI_PROBE_REL_BRIDGE_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit
