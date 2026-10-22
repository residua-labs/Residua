import rcic.RcicAnnLR3IrrQueryDescent
import rcic.RcicAnnLR3Sort

/-!
# The strengthened query IH, and the application query it does not supply

An irrelevance node does not need a rank bound on an independently given
sort-synthesis witness.  The appropriate smaller-typing predicate quantifies
over every such witness.  With existence included, the smaller-stage IH
supplies the direct irrelevance key.  These are conditional induction arms;
no global key or erasure theorem is claimed.

For a broader typing/inference agreement predicate, the declarative `conv`
arm merely composes the existing type conversions.  In the `app` arm the
function IH and the actual typed synthesis chain supply a conversion between
the two Pi types.  What remains is exactly agreement of their instantiated
codomains.  That conversion is a newly composed result of the IH and a
synthesis chain, not a literal conversion premise of the application rule.
This module records the query without claiming it cannot descend under a
stronger induction.  `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Boolean sort agreement at an arbitrary declarative sort typing.  This
stronger form also handles a stored proposition telescope typed at a
possibly converted sort, rather than assuming the latter is already zero. -/
def SortTypingQueryA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) {Γ : LCtxA} {A : ExprA} {u : Level}
    (_hA : HasTyA E I n Γ A (.sort u)) : Prop :=
  (∃ v, SortOfA3 E I n H Γ A v) ∧
    ∀ v, SortOfA3 E I n H Γ A v → isZero u = isZero v

/-- The arbitrary-sort version of the smaller-typing query stage. -/
def SortTypingQueriesBelowA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) (bound : Nat) : Prop :=
  ∀ {Γ : LCtxA} {A : ExprA} {u : Level} (hA : HasTyA E I n Γ A (.sort u)),
    hasTyDerivationRankA3 hA < bound → CtxWfA E I n Γ → SortTypingQueryA3 H hA

/-- The smaller-typing obligation at an irrelevance proposition: existence
and agreement with every synthesis witness, without a witness-rank bound. -/
def PropTypingQueryA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) {Γ : LCtxA} {P : ExprA}
    (_hP : HasTyA E I n Γ P (.sort .zero)) : Prop :=
  (∃ v, SortOfA3 E I n H Γ P v) ∧
    ∀ v, SortOfA3 E I n H Γ P v → isZero v = true

/-- A stage of the strengthened typing IH. Context well-formedness remains
an explicit premise; it is not inferred merely from a typing derivation. -/
def PropTypingQueriesBelowA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) (bound : Nat) : Prop :=
  ∀ {Γ : LCtxA} {P : ExprA} (hP : HasTyA E I n Γ P (.sort .zero)),
    hasTyDerivationRankA3 hP < bound → CtxWfA E I n Γ → PropTypingQueryA3 H hP

theorem propTypingQueryA3_of_sortTypingQuery
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    {Γ : LCtxA} {P : ExprA} {hP : HasTyA E I n Γ P (.sort .zero)}
    (h : SortTypingQueryA3 H hP) : PropTypingQueryA3 H hP :=
  ⟨h.1, fun v hv => (h.2 v hv).symm⟩

theorem propTypingQueriesBelowA3_of_sortTypingQueries
    {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat} {H : HeadLayerA3 E I n}
    (ih : SortTypingQueriesBelowA3 H k) : PropTypingQueriesBelowA3 H k :=
  fun hP hlt hΓ => propTypingQueryA3_of_sortTypingQuery (ih hP hlt hΓ)

/-- A known syntactic zero key answers the arbitrary declarative level at
this same smaller typing query; no bound on the synthesis witness is used. -/
theorem sortTypingQueryA3_zero_of_synthesis
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    {Γ : LCtxA} {A : ExprA} {u v : Level}
    {hA : HasTyA E I n Γ A (.sort u)} (h : SortTypingQueryA3 H hA)
    (hs : SortOfA3 E I n H Γ A v) (hv : isZero v = true) : isZero u = true :=
  (h.2 v hs).trans hv

theorem propTypingQueryA3_key {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {Γ : LCtxA} {P : ExprA}
    {hP : HasTyA E I n Γ P (.sort .zero)} (h : PropTypingQueryA3 H hP) :
    IsPropTyA3 E I n H Γ P := by
  obtain ⟨⟨v, hv⟩, hc⟩ := h
  exact ⟨v, hv, hc v hv⟩

/-- Every collected query can consume that earlier-stage IH. -/
theorem collectedIrrKeyA3_of_earlier {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat}
    {H : HeadLayerA3 E I n} (ih : PropTypingQueriesBelowA3 H k)
    (q : IrrQueryBelowA3 E I n k) (hΓ : CtxWfA E I n q.context) :
    IsPropTyA3 E I n H q.context q.proposition :=
  propTypingQueryA3_key (ih q.typing q.descends hΓ)

/-- Every actual typing-trace query has its context premise supplied from
the original context. No additional per-query context hypothesis is needed. -/
theorem hasTyIrrKeysA3_of_earlier
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {e A : ExprA} (d : HasTyA E I n Γ e A)
    (ih : PropTypingQueriesBelowA3 H (hasTyDerivationRankA3 d)) :
    ∀ q ∈ hasTyIrrQueriesA3 d, IsPropTyA3 E I n H q.context q.proposition := by
  intro q hq
  obtain ⟨hctx⟩ := hasTyIrrQueriesA3_contexts hE hI hR hIS d hΓ q hq
  exact collectedIrrKeyA3_of_earlier ih q hctx

/-- Every actual conversion-trace query, including those inside endpoint
typings, has its context and strict derivation descent supplied. -/
theorem convIrrKeysA3_of_earlier
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {a b A : ExprA} (d : ConvA E I n Γ a b A)
    (ih : PropTypingQueriesBelowA3 H (convDerivationRankA3 d)) :
    ∀ q ∈ convIrrQueriesA3 d, IsPropTyA3 E I n H q.context q.proposition := by
  intro q hq
  obtain ⟨hctx⟩ := convIrrQueriesA3_contexts hE hI hR hIS d hΓ q hq
  exact collectedIrrKeyA3_of_earlier ih q hctx

/-- The immediate irrelevance key is supplied by the strictly smaller hP
stage. There is no rank premise on an independent synthesis witness. -/
theorem irrKeyA3_of_smallerTypingIH {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {Γ : LCtxA} {P p q : ExprA}
    (hΓ : CtxWfA E I n Γ) (hP : HasTyA E I n Γ P (.sort .zero))
    (hp : HasTyA E I n Γ p P) (hq : HasTyA E I n Γ q P)
    (ih : PropTypingQueriesBelowA3 H
      (convDerivationRankA3 (.irr Γ P p q hP hp hq))) :
    IsPropTyA3 E I n H Γ P := by
  apply propTypingQueryA3_key (ih hP ?_ hΓ)
  simp only [convDerivationRankA3]
  omega

/-- The same smaller hP stage answers every independently supplied sort
witness. Only the declarative premise is measured. -/
theorem irrSynthesizedKeyA3_of_smallerTypingIH
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {Γ : LCtxA} {P p q : ExprA}
    (hΓ : CtxWfA E I n Γ) (hP : HasTyA E I n Γ P (.sort .zero))
    (hp : HasTyA E I n Γ p P) (hq : HasTyA E I n Γ q P)
    (ih : PropTypingQueriesBelowA3 H
      (convDerivationRankA3 (.irr Γ P p q hP hp hq)))
    {v : Level} (hv : SortOfA3 E I n H Γ P v) : isZero v = true := by
  have hlt : hasTyDerivationRankA3 hP <
      convDerivationRankA3 (.irr Γ P p q hP hp hq) := by
    simp only [convDerivationRankA3]
    omega
  exact (ih hP hlt hΓ).2 v hv

/-- A useful stronger induction predicate: every inference witness agrees
with the type in this particular declarative typing. -/
def TypingInferAgreementA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) {Γ : LCtxA} {e A : ExprA}
    (_h : HasTyA E I n Γ e A) : Prop :=
  ∀ U, InferA3 E I n H Γ e U → Nonempty (TyConvA E I n Γ U A)

/-- The typing conversion arm composes its child IH with the conversion
already present in the rule; it generates no injectivity query. -/
theorem typingInferAgreementA3_conv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {Γ : LCtxA} {e A B : ExprA} {l u : Level}
    (h : HasTyA E I n Γ e A) (hAl : HasTyA E I n Γ A (.sort l))
    (hlu : eqN l u) (hB : HasTyA E I n Γ B (.sort u))
    (hc : ConvA E I n Γ A B (.sort u)) (ih : TypingInferAgreementA3 H h) :
    TypingInferAgreementA3 H (.conv Γ e A B l u h hAl hlu hB hc) := by
  intro U hi
  obtain ⟨hu⟩ := ih U hi
  exact ⟨.trans Γ U A B hu (.of Γ A B l u u hAl hlu hB (eqNA_refl u) hc)⟩

/-- If coherence is attempted through typing/inference agreement, the
actual residual query is this conversion to `sort 0`. Its derivation is
composed from the IH output and the independent synthesis chain. -/
theorem propSortQueryA3_of_inferenceAgreement
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {P : ExprA} (hP : HasTyA E I n Γ P (.sort .zero))
    (ih : TypingInferAgreementA3 H hP) {v : Level}
    (hs : SortOfA3 E I n H Γ P v) :
    Nonempty (TyConvA E I n Γ (.sort v) (.sort .zero)) := by
  obtain ⟨T, hi, hw⟩ := hs
  obtain ⟨ht⟩ := ih T hi
  obtain ⟨hwc⟩ := whTyA3_tyConv hE hI hR hIS hΓ hw
  exact ⟨.trans Γ _ T _ hwc.symm ht⟩

/-- The function IH and synthesis chain supply the Pi conversion that an
application arm must use. No Pi injectivity is used to construct it. -/
theorem applicationPiQueryA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {f a A B U : ExprA} {u v : Level}
    (hf : HasTyA E I n Γ f (.pi A u B v))
    (ih : TypingInferAgreementA3 H hf)
    (hi : InferA3 E I n H Γ (.app f a) U) :
    ∃ (Tf D C : ExprA) (u' v' : Level),
      InferA3 E I n H Γ f Tf ∧
      WhTyA3 E I n H Γ Tf (.pi D u' C v') ∧
      U = instantiate0A a C ∧
      Nonempty (TyConvA E I n Γ (.pi D u' C v') (.pi A u B v)) := by
  cases hi with
  | app hfi hpi =>
      obtain ⟨hfa⟩ := ih _ hfi
      obtain ⟨hfp⟩ := whTyA3_tyConv hE hI hR hIS hΓ hpi
      exact ⟨_, _, _, _, _, hfi, hpi, rfl, ⟨.trans Γ _ _ _ hfp.symm hfa⟩⟩

/-- The exact codomain-instantiation slice needed after that alignment.
It is a named query, not a supplied Pi row or a rank-decrease assertion. -/
def AppCodomainAgreementQueryA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (a B C : ExprA) : Prop :=
  Nonempty (TyConvA E I n Γ (instantiate0A a C) (instantiate0A a B))

/-- The application arm consumes only this instantiated-codomain slice
for the actual inferred Pi. The missing query is explicit in `hquery`. -/
theorem typingInferAgreementA3_app_of_queries
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {f a A B : ExprA} {u v w : Level}
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (hf : HasTyA E I n Γ f (.pi A u B v)) (ha : HasTyA E I n Γ a A)
    (ih : TypingInferAgreementA3 H hf)
    (hquery : ∀ (Tf D C : ExprA) (u' v' : Level),
      InferA3 E I n H Γ f Tf → WhTyA3 E I n H Γ Tf (.pi D u' C v') →
      TyConvA E I n Γ (.pi D u' C v') (.pi A u B v) →
      AppCodomainAgreementQueryA3 E I n Γ a B C) :
    TypingInferAgreementA3 H (.app Γ f a A B u v w hB hTy hf ha) := by
  intro U hi
  obtain ⟨Tf, D, C, u', v', hfi, hpi, he, ⟨hc⟩⟩ :=
    applicationPiQueryA3 hE hI hR hIS hΓ hf ih hi
  cases he
  exact hquery Tf D C u' v' hfi hpi hc

#print axioms SortTypingQueryA3
#print axioms SortTypingQueriesBelowA3
#print axioms PropTypingQueryA3
#print axioms PropTypingQueriesBelowA3
#print axioms propTypingQueryA3_of_sortTypingQuery
#print axioms propTypingQueriesBelowA3_of_sortTypingQueries
#print axioms sortTypingQueryA3_zero_of_synthesis
#print axioms propTypingQueryA3_key
#print axioms collectedIrrKeyA3_of_earlier
#print axioms hasTyIrrKeysA3_of_earlier
#print axioms convIrrKeysA3_of_earlier
#print axioms irrKeyA3_of_smallerTypingIH
#print axioms irrSynthesizedKeyA3_of_smallerTypingIH
#print axioms TypingInferAgreementA3
#print axioms typingInferAgreementA3_conv
#print axioms propSortQueryA3_of_inferenceAgreement
#print axioms applicationPiQueryA3
#print axioms AppCodomainAgreementQueryA3
#print axioms typingInferAgreementA3_app_of_queries

end Rcic.Declarative.Ann.LR3
