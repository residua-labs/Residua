import rcic.RcicNativeReadbackCK2ModelObstruction

/-!
# Exact boundaries of the guarded model's inherited interfaces

These results use the landed compact typing, relation, fundamental motives,
and CK2 fixtures.  They do not reproduce a fundamental constructor induction.

The raw beta factorization already fails on syntax containing no recursor.
Retaining the old five-argument Eq prefix together with raw application
would restore the rejected, natively typed saturated Eq call.  The alternative
saturated repair therefore abandons that prefix; its old application
inversion fails instead.  The last
section records a separate native beta conversion that discards that call;
any guard inherited from every syntax child must account for this conversion.

Every negative result below specifies its exact model premises.  In particular,
none assumes a global model-law package merely to extract one of its fields.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Only the lambda shape at `cexD`, the zero-variable inversion, and
one Pi probe are needed to refute the landed raw beta factorization. -/
theorem not_modelBetaExpandT_of_minimal_inversions {M : CtxModelT E} {ρ : EnvT}
    (hlam : ∀ {ρ₀ : EnvT} {a : CptT}, M.Ap ρ₀ cexD a →
      a = .bot ∨ ∃ g, a = .lam g)
    (hbvar : ∀ {ρ₀ : EnvT} {us : List CptT} {c : CptT},
      M.Ap (EnvT.cons (demandT us) ρ₀) (.bvar 0) c → c = .bot ∨ c ∈ us)
    (hprobe : M.Ap ρ cexP (.pi .bot [])) : ¬ ModelBetaExpandT M := by
  intro hβ
  obtain ⟨a, us, hA, htyped, _, hbody⟩ :=
    hβ (A := cexD) (arg := cexP) (body := .bvar 0) hprobe
  rcases hbvar hbody with hbot | hmem
  · exact CptT.noConfusion hbot
  · have hty := htyped (.pi .bot []) hmem
    rcases hlam hA with rfl | ⟨g, rfl⟩
    · exact CptT.noConfusion (ctyS_bot_inv hty)
    · exact CptT.noConfusion (ctyS_lam_inv hty)

/-- A forgetful map and preservation of this one recursor-free probe
suffice.  No global `CtxModelTLaws` premise is hidden in the statement. -/
theorem not_modelBetaExpandT_of_approxT_projection {M : CtxModelT E} {ρ : EnvT}
    (hforget : ∀ {ρ₀ : EnvT} {e : Expr Nat} {c : CptT},
      M.Ap ρ₀ e c → ApproxT E ρ₀ e c)
    (hprobe : M.Ap ρ cexP (.pi .bot [])) : ¬ ModelBetaExpandT M := by
  apply not_modelBetaExpandT_of_minimal_inversions (ρ := ρ) (hprobe := hprobe)
  · intro ρ₀ a h
    rcases approxT_lam_inv (hforget h) with hbot | ⟨a', g, rfl, _⟩
    · exact Or.inl hbot
    · exact Or.inr ⟨g, rfl⟩
  · intro ρ₀ us c h
    simpa only [EnvT.cons, demandT] using approxT_bvar_inv (hforget h)

/-- The original model itself meets the concrete premises of the raw
beta refutation, uniformly in the resolved environment. -/
theorem not_modelBetaExpandT_approxT (E : ResolvedEnv) :
    ¬ ModelBetaExpandT (ctxModelT_approxT E) :=
  not_modelBetaExpandT_of_approxT_projection
    (fun h => h) (approxT_pi_bot_nil E EnvT.bot _ _)

/-- A nonbottom application whose immediate function has only bottom
cannot satisfy the landed three-way application inversion.  This is the
precise boundary for a model with an additional saturated computation rule. -/
theorem not_raw_app_inv_of_bot_function {M : CtxModelT E} {ρ : EnvT}
    {f x : Expr Nat}
    (hf : ∀ {c : CptT}, M.Ap ρ f c → c = .bot)
    (happ : M.Ap ρ (.app f x) .prop) :
    ¬ (∀ {ρ₀ : EnvT} {f₀ x₀ : Expr Nat} {c : CptT},
      M.Ap ρ₀ (.app f₀ x₀) c → c = .bot ∨
      (∃ g s, c = s.2 ∧ M.Ap ρ₀ f₀ (.lam g) ∧ s ∈ g ∧
        ∀ u ∈ s.1, M.Ap ρ₀ x₀ u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧
        M.Ap ρ₀ f₀ (.spine r args) ∧ M.Ap ρ₀ x₀ u)) := by
  intro hinv
  rcases hinv happ with hbot | ⟨g, s, _, hfg, _⟩ | ⟨r, args, u, he, _⟩
  · exact CptT.noConfusion hbot
  · exact CptT.noConfusion (hf hfg)
  · exact CptT.noConfusion he

/-- Thus a saturated computation cannot be supplied through the entire
landed context-free model-law record when its proper prefix is bottom. -/
theorem not_ctxModelTLaws_of_bot_function {M : CtxModelT E} {ρ : EnvT}
    {f x : Expr Nat}
    (hf : ∀ {c : CptT}, M.Ap ρ f c → c = .bot)
    (happ : M.Ap ρ (.app f x) .prop) : ¬ CtxModelTLaws M :=
  fun hM => not_raw_app_inv_of_bot_function hf happ hM.app_inv

/-- The exact five-argument prefix of the existing typed apart fixture. -/
def apartPrefix : Expr Nat :=
  foldApps (.const 65 [.succ (.succ .zero)])
    [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight]

theorem apartRec_eq_app_prefix : apartRec = .app apartPrefix (.bvar 0) := rfl

private theorem approxT_emptyDemand {ρ : EnvT} {f x : Expr Nat} {c : CptT}
    (h : ApproxT E ρ f (.lam [([], c)])) : ApproxT E ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl) (fun u hu => (List.not_mem_nil u hu).elim)

/-- The admitted Eq schema supplies this precise empty-major-demand
prefix compact.  The structured witness and schema are imported from CK2. -/
theorem apartPrefix_model (ρ : EnvT) :
    ApproxT eqEnvT ρ apartPrefix (.lam [([], .prop)]) := by
  obtain ⟨w, hw⟩ := eqRec_structured_exists
  obtain ⟨hP, hpre, hfields, hschema⟩ := eqRec_model_schema w hw
  have hrec : ApproxT eqEnvT ρ (.const 65 [.succ (.succ .zero)])
      (curryStepT [[], [], [], [.prop], [], []] .prop) := by
    rw [← hw]
    apply ApproxT.recursorProp (us_pre := [[], [], [], [.prop], []])
      [.succ (.succ .zero)] hP
    · exact hpre.symm
    · rw [hfields, List.map_nil, List.append_nil, hschema]
      exact ApproxT.bvar (List.mem_singleton.mpr rfl)
  have h0 := approxT_emptyDemand (x := .sort .zero) hrec
  have h1 := approxT_emptyDemand (x := idPiProp) h0
  have h2 := approxT_emptyDemand (x := apartMot) h1
  have h3 : ApproxT eqEnvT ρ
      (.app (.app (.app (.app (.const 65 [.succ (.succ .zero)])
        (.sort .zero)) idPiProp) apartMot) (.sort .zero))
      (curryStepT [[], []] .prop) :=
    .app h2 (List.mem_singleton.mpr rfl) (fun u hu => by
      obtain rfl := List.mem_singleton.mp hu
      exact approxT_sort_code eqEnvT ρ .zero)
  exact approxT_emptyDemand (x := apartRight) h3

/-- Prefix semantics and native typing of the full source are independent
facts.  In particular the final application is not an untyped example. -/
theorem apartPrefix_native_control (n : Nat) (ρ : EnvT) :
    ApproxT eqEnvT ρ apartPrefix (.lam [([], .prop)]) ∧
      Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) :=
  ⟨apartPrefix_model ρ, apartRec_typed n⟩

/-- Retaining this prefix and the old raw application constructor would
restore the saturated observation that the native guard must exclude. -/
theorem not_raw_app_intro_of_apartPrefix {M : CtxModelT eqEnvT} {ρ : EnvT}
    (hprefix : M.Ap ρ apartPrefix (.lam [([], .prop)]))
    (hblocked : ¬ M.Ap ρ apartRec .prop) :
    ¬ (∀ {ρ₀ : EnvT} {f x : Expr Nat} {g : List (List CptT × CptT)}
      {s : List CptT × CptT}, M.Ap ρ₀ f (.lam g) → s ∈ g →
      (∀ u ∈ s.1, M.Ap ρ₀ x u) → M.Ap ρ₀ (.app f x) s.2) := by
  intro happ
  apply hblocked
  rw [apartRec_eq_app_prefix]
  exact happ hprefix (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

/-- The same local failure refutes the reconstruction direction of the
landed `AppCptT` factorization; its final argument demand is empty. -/
theorem not_appCpt_reconstruction_of_apartPrefix {M : CtxModelT eqEnvT} {ρ : EnvT}
    (hprefix : M.Ap ρ apartPrefix (.lam [([], .prop)]))
    (hblocked : ¬ M.Ap ρ apartRec .prop) :
    ¬ (∀ {f x : Expr Nat} {c : CptT},
      (∃ d, M.Ap ρ f d ∧ AppCptT eqEnvT ρ d x c) → M.Ap ρ (.app f x) c) := by
  intro happ
  apply hblocked
  rw [apartRec_eq_app_prefix]
  exact happ ⟨_, hprefix, .app (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)⟩

/-- The normal-proposition-compact boundary is model-parametric.  It
consumes the full landed related-substitution motive at its actual identity. -/
theorem not_fundTyAt_of_normal_prop {M : CtxModelT E} {Γ : LCtx}
    {e I : Expr Nat} {ρ : EnvT} (hΓ : CtxWfT E n Γ)
    (hId : RelSubstIdT M R n Γ ρ) (hmodel : M.Ap ρ e .prop)
    (hnormal : NormalR R Γ e) (hshape : ∀ u, e ≠ .sort u) :
    ¬ FundTyAt M R n Γ e I := by
  intro hF
  have hrel := hF hΓ hId .prop (Or.inl hmodel)
  simp only [substT_id] at hrel
  obtain ⟨_, u, _, hr, _⟩ := (lrSCoreS_prop_iff _ _ _ _).mp hrel
  exact hshape u (redR_of_normal hnormal hr).symm

theorem not_fundamentalSAtT_of_normal_prop {M : CtxModelT E} {Γ : LCtx}
    {e I : Expr Nat} {ρ : EnvT} (hΓ : CtxWfT E n Γ)
    (ht : HasTyT E n Γ e I) (hId : RelSubstIdT M R n Γ ρ)
    (hmodel : M.Ap ρ e .prop) (hnormal : NormalR R Γ e)
    (hshape : ∀ u, e ≠ .sort u) : ¬ FundamentalSAtT M R n :=
  fun hF => not_fundTyAt_of_normal_prop hΓ hId hmodel hnormal hshape (hF.1 hΓ ht)

/-- The actual apart context has no let declarations, so its imported
identity package is valid for every model, with no global model laws. -/
theorem apartCtx_identity_model (M : CtxModelT eqEnvT) (R : Readback) (n : Nat) :
    RelSubstIdT M R n apartCtx EnvT.bot := by
  have h := apartCtx_identity R n
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro i v A hv
  cases i <;> simp [apartCtx, lookupValue] at hv

/-- Keeping both the exact prefix compact and the raw application
constructor prevents a global fundamental supplier for the index readback. -/
theorem not_fundamentalSAtT_of_raw_app_prefix (M : CtxModelT eqEnvT) (n : Nat)
    (hprefix : M.Ap EnvT.bot apartPrefix (.lam [([], .prop)]))
    (happ : ∀ {ρ₀ : EnvT} {f x : Expr Nat} {g : List (List CptT × CptT)}
      {s : List CptT × CptT}, M.Ap ρ₀ f (.lam g) → s ∈ g →
      (∀ u ∈ s.1, M.Ap ρ₀ x u) → M.Ap ρ₀ (.app f x) s.2) :
    ¬ FundamentalSAtT M (WhStepIndexCK2 eqEnvT) n := by
  obtain ⟨ht⟩ := apartRec_typed n
  apply not_fundamentalSAtT_of_normal_prop (apartCtx_wf n) ht
    (apartCtx_identity_model M (WhStepIndexCK2 eqEnvT) n)
    (hnormal := apartRec_normalIndex) (hshape := fun _ he => Expr.noConfusion he)
  rw [apartRec_eq_app_prefix]
  exact happ hprefix (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

/-- A native beta redex discarding the typed apart call. -/
def discardApartRec : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) apartRec

/-- This conversion is natively typed, at the same nonempty admitted
context as the rejected call; no equality of its apart indices is used. -/
theorem discardApartRec_beta (n : Nat) :
    Nonempty (ConvT eqEnvT n apartCtx discardApartRec (.sort .zero)
      (.sort (.succ .zero))) := by
  obtain ⟨harg⟩ := apartRec_typed n
  exact ⟨.beta apartCtx (.sort (.succ .zero)) (.sort .zero) apartRec
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort _ _) (.sort _ _) harg⟩

/-- If a syntactic guard is inherited from every child, exclusion of the
discarded source must not be mistaken for model invariance of native beta. -/
theorem not_modelConvSoundAt_discardApartRec {M : CtxModelT eqEnvT} {ρ : EnvT}
    (hblocked : ¬ M.Ap ρ discardApartRec .prop)
    (hsort : M.Ap ρ (.sort .zero) .prop) :
    ¬ ModelConvSoundAt M ρ discardApartRec (.sort .zero) :=
  fun h => hblocked ((h .prop).mpr hsort)

/-- Exact global conversion-soundness failure from that one typed beta
instance.  The model exclusion premise is explicit. -/
theorem not_global_model_conv_sound_of_discardApartRec
    (M : CtxModelT eqEnvT) (n : Nat) {ρ : EnvT}
    (hblocked : ¬ M.Ap ρ discardApartRec .prop)
    (hsort : M.Ap ρ (.sort .zero) .prop) :
    ¬ (∀ {Γ : LCtx} {a b A : Expr Nat}, CtxWfT eqEnvT n Γ →
      ConvT eqEnvT n Γ a b A → ∀ ρ₀, ModelConvSoundAt M ρ₀ a b) := by
  intro hsound
  obtain ⟨hβ⟩ := discardApartRec_beta n
  exact not_modelConvSoundAt_discardApartRec hblocked hsort
    (hsound (apartCtx_wf n) hβ ρ)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_OBSTRUCTION_ROOTS
#print axioms not_modelBetaExpandT_of_minimal_inversions
#print axioms not_modelBetaExpandT_of_approxT_projection
#print axioms not_modelBetaExpandT_approxT
#print axioms not_raw_app_inv_of_bot_function
#print axioms not_ctxModelTLaws_of_bot_function
#print axioms apartPrefix
#print axioms apartRec_eq_app_prefix
#print axioms apartPrefix_model
#print axioms apartPrefix_native_control
#print axioms not_raw_app_intro_of_apartPrefix
#print axioms not_appCpt_reconstruction_of_apartPrefix
#print axioms not_fundTyAt_of_normal_prop
#print axioms not_fundamentalSAtT_of_normal_prop
#print axioms apartCtx_identity_model
#print axioms not_fundamentalSAtT_of_raw_app_prefix
#print axioms discardApartRec
#print axioms discardApartRec_beta
#print axioms not_modelConvSoundAt_discardApartRec
#print axioms not_global_model_conv_sound_of_discardApartRec
-- END RCIC_NATIVE_TYPED_MODEL_K_OBSTRUCTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit
