import rcic.RcicNativeReadbackCK2ModelObstruction

/-!
# Exact transports for a refinement of the typed compact model

The existing model consumers do not all inspect the same expressions.
`RelSubstAtT` inspects only the source context's let values; `EnvTypedAtT`
inspects its lookup types.  The fundamental motives inspect their source
terms, while the substituted terms occur only in the unchanged relation.
The local equivalences below record precisely those dependencies.

Every transport composes the existing definitions.  In particular, there
is no induction over `HasTyT`, `ConvT`, or a Fundamental supplier here.
Global consumers are transported only under agreement on every expression;
pointwise inclusion alone is not asserted to transport a global supplier.

The indexed proposition-recursion criterion uses the existing structured
witness.  It does not confuse `PropFamilyS` with either zero indices or the
readback's singleton-canon eligibility predicate.  The native Eq and Nat
controls carry non-bottom, semantically typed compacts in admitted environments.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKTransportAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

variable {E : ResolvedEnv} {M N P : CtxModelT E} {R : Readback} {n : Nat}

/-! ## The exact expressions inspected by each consumer -/

/-- Two models agree at one source expression, in every semantic environment. -/
def ModelAgreementAtT (M N : CtxModelT E) (e : Expr Nat) : Prop :=
  ∀ (ρ : EnvT) (c : CptT), M.Ap ρ e c ↔ N.Ap ρ e c

/-- Agreement on all values returned by the source context's value lookup. -/
def ValueAgreementT (M N : CtxModelT E) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v → ModelAgreementAtT M N v

/-- Agreement on all types returned by the source context's type lookup. -/
def TypeAgreementT (M N : CtxModelT E) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ModelAgreementAtT M N A

theorem modelAgreementAtT_refl (M : CtxModelT E) (e : Expr Nat) :
    ModelAgreementAtT M M e := fun _ _ => Iff.rfl

theorem modelAgreementAtT_symm {e : Expr Nat} (h : ModelAgreementAtT M N e) :
    ModelAgreementAtT N M e := fun ρ c => (h ρ c).symm

theorem modelAgreementAtT_trans {e : Expr Nat}
    (hMN : ModelAgreementAtT M N e) (hNP : ModelAgreementAtT N P e) :
    ModelAgreementAtT M P e := fun ρ c => (hMN ρ c).trans (hNP ρ c)

/-- An assumption-only source context has no model-dependent substitution field. -/
theorem valueAgreementT_of_no_values {Γ : LCtx}
    (h : ∀ i, lookupValue Γ i = none) : ValueAgreementT M N Γ := by
  intro i v hv
  rw [h i] at hv
  cases hv

/-- All related-substitution fields are retained, including all four let-value pairs. -/
theorem relSubstAtT_congr {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hV : ValueAgreementT M N Γ) :
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ ↔ RelSubstAtT N R n Δ ρ ρ' σ σ' Γ := by
  constructor
  · rintro ⟨hσ, hσ', hconv, hvars, hvals⟩
    refine ⟨hσ, hσ', hconv, hvars, ?_⟩
    intro i v A hv hA c hc
    apply hvals i v A hv hA c
    rcases hc with hc | hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inl ((hV i v hv ρ c).mpr hc)))
    · exact Or.inr (Or.inr (Or.inr ((hV i v hv ρ' c).mpr hc)))
  · rintro ⟨hσ, hσ', hconv, hvars, hvals⟩
    refine ⟨hσ, hσ', hconv, hvars, ?_⟩
    intro i v A hv hA c hc
    apply hvals i v A hv hA c
    rcases hc with hc | hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inl ((hV i v hv ρ c).mp hc)))
    · exact Or.inr (Or.inr (Or.inr ((hV i v hv ρ' c).mp hc)))

theorem relSubstIdT_congr {Γ : LCtx} {ρ : EnvT} (hV : ValueAgreementT M N Γ) :
    RelSubstIdT M R n Γ ρ ↔ RelSubstIdT N R n Γ ρ :=
  relSubstAtT_congr hV

/-- Only the source term and source-context values need model agreement. -/
theorem fundTyAt_congr {Γ : LCtx} {e A : Expr Nat}
    (hV : ValueAgreementT M N Γ) (he : ModelAgreementAtT M N e) :
    FundTyAt M R n Γ e A ↔ FundTyAt N R n Γ e A := by
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hS c hc
    apply h hΔ ((relSubstAtT_congr hV).mpr hS) c
    exact hc.elim (fun hc => Or.inl ((he ρ c).mpr hc))
      (fun hc => Or.inr ((he ρ' c).mpr hc))
  · intro h Δ ρ ρ' σ σ' hΔ hS c hc
    apply h hΔ ((relSubstAtT_congr hV).mp hS) c
    exact hc.elim (fun hc => Or.inl ((he ρ c).mp hc))
      (fun hc => Or.inr ((he ρ' c).mp hc))

/-- All substitutions and both endpoint environments remain quantified. -/
theorem fundConvAt_congr {Γ : LCtx} {a b A : Expr Nat}
    (hV : ValueAgreementT M N Γ) (ha : ModelAgreementAtT M N a)
    (hb : ModelAgreementAtT M N b) :
    FundConvAt M R n Γ a b A ↔ FundConvAt N R n Γ a b A := by
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hS c hc
    apply h hΔ ((relSubstAtT_congr hV).mpr hS) c
    exact hc.elim (fun hc => Or.inl ((ha ρ c).mpr hc))
      (fun hc => Or.inr ((hb ρ' c).mpr hc))
  · intro h Δ ρ ρ' σ σ' hΔ hS c hc
    apply h hΔ ((relSubstAtT_congr hV).mp hS) c
    exact hc.elim (fun hc => Or.inl ((ha ρ c).mp hc))
      (fun hc => Or.inr ((hb ρ' c).mp hc))

theorem tyValidAt_congr {Γ : LCtx} {A : Expr Nat}
    (hV : ValueAgreementT M N Γ) (hA : ModelAgreementAtT M N A) :
    TyValidAt M R n Γ A ↔ TyValidAt N R n Γ A := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (fundTyAt_congr hV hA).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (fundTyAt_congr hV hA).mpr hu⟩

theorem ctxValidAt_congr {Γ : LCtx} (hV : ValueAgreementT M N Γ)
    (hT : TypeAgreementT M N Γ) :
    CtxValidAt M R n Γ ↔ CtxValidAt N R n Γ := by
  constructor
  · intro h i A hA
    exact (tyValidAt_congr hV (hT i A hA)).mp (h i A hA)
  · intro h i A hA
    exact (tyValidAt_congr hV (hT i A hA)).mpr (h i A hA)

/-- Environment typing reads lookup types, independently of source-context values. -/
theorem envTypedAtT_congr {Γ : LCtx} {ρ : EnvT} (hT : TypeAgreementT M N Γ) :
    EnvTypedAtT M Γ ρ ↔ EnvTypedAtT N Γ ρ := by
  constructor
  · intro h i A hA c hc
    obtain ⟨a, ha, hca⟩ := h i A hA c hc
    exact ⟨a, (hT i A hA ρ a).mp ha, hca⟩
  · intro h i A hA c hc
    obtain ⟨a, ha, hca⟩ := h i A hA c hc
    exact ⟨a, (hT i A hA ρ a).mpr ha, hca⟩

theorem relSubstTypedAtT_congr {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    RelSubstTypedAtT M R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstTypedAtT N R n Δ ρ ρ' σ σ' Γ := by
  exact and_congr (relSubstAtT_congr hV)
    (and_congr (envTypedAtT_congr hT) (envTypedAtT_congr hT))

theorem typingAt_congr {ρ ρ' : EnvT} {a b A : Expr Nat}
    (ha : ModelAgreementAtT M N a) (hb : ModelAgreementAtT M N b)
    (hA : ModelAgreementAtT M N A) :
    TypingAt M ρ ρ' a b A ↔ TypingAt N ρ ρ' a b A := by
  constructor
  · intro h c hc
    obtain ⟨a₀, hcode, htyped⟩ := h c
      (hc.elim (fun hc => Or.inl ((ha ρ c).mpr hc))
        (fun hc => Or.inr ((hb ρ' c).mpr hc)))
    exact ⟨a₀, hcode.elim (fun hc => Or.inl ((hA ρ a₀).mp hc))
      (fun hc => Or.inr ((hA ρ' a₀).mp hc)), htyped⟩
  · intro h c hc
    obtain ⟨a₀, hcode, htyped⟩ := h c
      (hc.elim (fun hc => Or.inl ((ha ρ c).mp hc))
        (fun hc => Or.inr ((hb ρ' c).mp hc)))
    exact ⟨a₀, hcode.elim (fun hc => Or.inl ((hA ρ a₀).mpr hc))
      (fun hc => Or.inr ((hA ρ' a₀).mpr hc)), htyped⟩

theorem modelConvSoundAt_congr {ρ : EnvT} {a b : Expr Nat}
    (ha : ModelAgreementAtT M N a) (hb : ModelAgreementAtT M N b) :
    ModelConvSoundAt M ρ a b ↔ ModelConvSoundAt N ρ a b := by
  constructor
  · intro h c
    exact (ha ρ c).symm.trans ((h c).trans (hb ρ c))
  · intro h c
    exact (ha ρ c).trans ((h c).trans (hb ρ c).symm)

theorem hybridSeed_congr {Δ : LCtx} {ρ : EnvT} {σ : SubstT}
    {a A : Expr Nat} {c : CptT} (ha : ModelAgreementAtT M N a)
    (hA : ModelAgreementAtT M N A) :
    HybridSeed M R n Δ ρ σ a A c ↔ HybridSeed N R n Δ ρ σ a A c := by
  constructor
  · rintro ⟨⟨a₀, hcode, htyped⟩, hseed⟩
    exact ⟨⟨a₀, (hA ρ a₀).mp hcode, htyped⟩,
      hseed.elim (fun hc => Or.inl ((ha ρ c).mp hc)) Or.inr⟩
  · rintro ⟨⟨a₀, hcode, htyped⟩, hseed⟩
    exact ⟨⟨a₀, (hA ρ a₀).mpr hcode, htyped⟩,
      hseed.elim (fun hc => Or.inl ((ha ρ c).mpr hc)) Or.inr⟩

/-! ## Global consumers require global agreement -/

/-- Extensional model equality is used only when every expression agrees. -/
theorem ctxModelT_eq_of_agreement (h : ∀ e, ModelAgreementAtT M N e) : M = N := by
  cases M with
  | mk apM =>
    cases N with
    | mk apN =>
      have heq : apM = apN := funext (fun ρ => funext (fun e =>
        funext (fun c => propext (h e ρ c))))
      cases heq
      rfl

theorem ctxModelTLaws_congr (h : ∀ e, ModelAgreementAtT M N e) :
    CtxModelTLaws M ↔ CtxModelTLaws N := by
  rw [ctxModelT_eq_of_agreement h]

theorem ctxModelTLaws'_congr (h : ∀ e, ModelAgreementAtT M N e) :
    CtxModelTLaws' M ↔ CtxModelTLaws' N := by
  rw [ctxModelT_eq_of_agreement h]

theorem modelBetaExpandT_congr (h : ∀ e, ModelAgreementAtT M N e) :
    ModelBetaExpandT M ↔ ModelBetaExpandT N := by
  rw [ctxModelT_eq_of_agreement h]

theorem typingLemmaEnvT_congr (h : ∀ e, ModelAgreementAtT M N e) :
    TypingLemmaEnvT M n ↔ TypingLemmaEnvT N n := by
  rw [ctxModelT_eq_of_agreement h]

theorem fundamentalSAtT_congr (h : ∀ e, ModelAgreementAtT M N e) :
    FundamentalSAtT M R n ↔ FundamentalSAtT N R n := by
  rw [ctxModelT_eq_of_agreement h]

theorem fundCases_congr (h : ∀ e, ModelAgreementAtT M N e) :
    FundCases M R n ↔ FundCases N R n := by
  rw [ctxModelT_eq_of_agreement h]

theorem ihBelow_congr {k : Nat} (h : ∀ e, ModelAgreementAtT M N e) :
    TypedModelAudit.IHBelow M R n k ↔ TypedModelAudit.IHBelow N R n k := by
  rw [ctxModelT_eq_of_agreement h]

/-! ## Indexed proposition recursion and nondegenerate controls -/

/-- The precise recursor references whose proposition clause has nonempty indices.
This condition says nothing about singleton-canon eligibility or native conversion. -/
def IndexedPropRecT (E : ResolvedEnv) (r : Nat) : Prop :=
  ∃ w : IotaWitnessS E, w.recRef = r ∧ PropFamilyS w ∧ w.nindices ≠ 0

theorem indexedPropRecT_eqRec : IndexedPropRecT eqEnvT 65 := by
  obtain ⟨w, hr⟩ := eqRec_structured_exists
  have hm : w.recMember = eqRecT := by
    have hw := w.hrec
    rw [hr] at hw
    exact (Option.some.inj hw).symm
  have hd := IotaWitnessS.recData_admitted eqGroupAdm (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  refine ⟨w, hr, (eqRec_model_schema w hr).1, ?_⟩
  rw [hd.2.2.2.1]
  decide

/-- Nat's recursor uses the strict clause: its family is declared into `Sort 1`. -/
theorem not_indexedPropRecT_natEnvU (r : Nat) : ¬ IndexedPropRecT natEnvU r := by
  rintro ⟨w, _, hP, _⟩
  have hd := natEnvU_witness_refs (fun _ _ h => h)
    w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  change piBody w.famMember.mtype = .sort .zero at hP
  rw [hd.1.2] at hP
  cases hP

/-- The proposition clause at True.rec has no indices and is outside this criterion. -/
theorem not_indexedPropRecT_trueRec : ¬ IndexedPropRecT trueEnvU 2 := by
  rintro ⟨w, hr, _, hni⟩
  have hp := (trueEnvU_recRef_propFamily w hr).2
  have hpre := w.hpre
  have hminor := w.hidx
  omega

/-- A native term with a non-bottom model compact typed at an actual code of its type. -/
def TypedCompactWitnessT (M : CtxModelT E) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (e A : Expr Nat) (c a : CptT) : Prop :=
  Nonempty (CtxWfT E n Γ) ∧ Nonempty (HasTyT E n Γ e A) ∧
    M.Ap ρ e c ∧ M.Ap ρ A a ∧ CTyS E c a ∧ c ≠ .bot

theorem typedCompactWitnessT_congr {Γ : LCtx} {ρ : EnvT}
    {e A : Expr Nat} {c a : CptT} (he : ModelAgreementAtT M N e)
    (hA : ModelAgreementAtT M N A) :
    TypedCompactWitnessT M n Γ ρ e A c a ↔ TypedCompactWitnessT N n Γ ρ e A c a := by
  constructor
  · rintro ⟨hΓ, ht, hc, hcode, htyped, hnb⟩
    exact ⟨hΓ, ht, (he ρ c).mp hc, (hA ρ a).mp hcode, htyped, hnb⟩
  · rintro ⟨hΓ, ht, hc, hcode, htyped, hnb⟩
    exact ⟨hΓ, ht, (he ρ c).mpr hc, (hA ρ a).mpr hcode, htyped, hnb⟩

/-- Native typing of the existing closed Eq proposition used by the separating audit. -/
def eqControl_ty (n : Nat) : HasTyT eqEnvT n [] apartRight (.sort .zero) :=
  .app _ _ _ _ _
    (eqFamilyPartialTy (fun _ _ h => h) (.sort [] .zero) (apartLeft_ty n []))
    (apartLeft_ty n [])

theorem eq_typed_compact_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT eqEnvT) ∧
      TypedCompactWitnessT (ctxModelT_approxT eqEnvT) n [] ρ
        apartRight (.sort .zero) (.spine 63 [.bot, .bot, .bot]) .prop := by
  exact ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩, ⟨eqControl_ty n⟩, apartRight_model ρ,
    approxT_sort_code eqEnvT ρ .zero, apart_separating_compacts_typed.2,
    fun h => CptT.noConfusion h⟩

private theorem nat_zero_rigid : RigidConst natEnvU 1 := by
  intro m hm
  have he : m = natZeroMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem nat_zero_not_propCtor : ¬ PropCtorT natEnvU 1 := by
  rintro ⟨m, fam, fm, hm, _, hh, hf, hP⟩
  have he : m = natZeroMember := Option.some.inj hm.symm
  subst m
  have hfr : fam = 0 := (Option.some.inj hh).symm
  subst fam
  have hfm : fm = natFamMember := Option.some.inj hf.symm
  subst fm
  cases hP

private theorem nat_family_not_propCtor : ¬ PropCtorT natEnvU 0 := by
  rintro ⟨m, _, _, hm, hc, _⟩
  have he : m = natFamMember := Option.some.inj hm.symm
  subst m
  cases hc

private theorem nat_family_not_propCode : ¬ IsPropCT natEnvU (.spine 0 []) := by
  intro h
  cases h with
  | spine hm hP =>
    have he : _ = natFamMember := Option.some.inj hm.symm
    rw [he] at hP
    cases hP

/-- Zero's compact is a constructor spine, semantically typed at the Nat family spine. -/
theorem nat_typed_compact_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧
      TypedCompactWitnessT (ctxModelT_approxT natEnvU) n [] ρ
        (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) := by
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    ⟨.const [] 1 [] natZeroMember rfl rfl rfl⟩,
    .const ρ 1 [] nat_zero_rigid nat_zero_not_propCtor,
    .const ρ 0 [] (rigidConst_of_inductiveM natEnvUWfT rfl rfl) nat_family_not_propCtor,
    ?_, fun h => CptT.noConfusion h⟩
  rw [CTyS]
  exact Or.inr ⟨⟨1, [], rfl⟩, nat_family_not_propCode⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_TRANSPORT_ROOTS
#print axioms ModelAgreementAtT
#print axioms ValueAgreementT
#print axioms TypeAgreementT
#print axioms modelAgreementAtT_refl
#print axioms modelAgreementAtT_symm
#print axioms modelAgreementAtT_trans
#print axioms valueAgreementT_of_no_values
#print axioms relSubstAtT_congr
#print axioms relSubstIdT_congr
#print axioms fundTyAt_congr
#print axioms fundConvAt_congr
#print axioms tyValidAt_congr
#print axioms ctxValidAt_congr
#print axioms envTypedAtT_congr
#print axioms relSubstTypedAtT_congr
#print axioms typingAt_congr
#print axioms modelConvSoundAt_congr
#print axioms hybridSeed_congr
#print axioms ctxModelT_eq_of_agreement
#print axioms ctxModelTLaws_congr
#print axioms ctxModelTLaws'_congr
#print axioms modelBetaExpandT_congr
#print axioms typingLemmaEnvT_congr
#print axioms fundamentalSAtT_congr
#print axioms fundCases_congr
#print axioms ihBelow_congr
#print axioms IndexedPropRecT
#print axioms indexedPropRecT_eqRec
#print axioms not_indexedPropRecT_natEnvU
#print axioms not_indexedPropRecT_trueRec
#print axioms TypedCompactWitnessT
#print axioms typedCompactWitnessT_congr
#print axioms eqControl_ty
#print axioms eq_typed_compact_control
#print axioms nat_typed_compact_control
-- END RCIC_NATIVE_TYPED_MODEL_K_TRANSPORT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
