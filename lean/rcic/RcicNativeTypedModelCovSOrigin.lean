import rcic.RcicNativeTypedModelCovRFixtureSyntax

/-!
# The information absent from raw type observations

Two distinct native type variables observe the same nonbottom compact in
one finite-joint typed, let-coherent valuation. A decoder of the compact
alone cannot recover their distinct lexical indices. Likewise, an actual
sort-domain Pi and an actual Nat-domain Pi both observe `pi bot []`.
The stronger literal-sort versus variable-domain control observes
`pi prop []` in one typed valuation: even a nonbottom observed domain
does not certify the native binder's origin.
Even the two positive native universe levels below have the same `sort`
observation. These are representation boundaries, not failures of a
decoder that also receives native syntax or an explicit origin certificate.

The generic decoder statements work for any proposed extended syntax or
tag type with distinct designated labels. No approximation order on CptT
is assumed or introduced. No total type readback or native fundamental
result is used. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovPAudit

universe u

def covSOriginCtx : LCtx :=
  [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]

/-- Both declared type variables receive the actual Prop universe compact.
Values at indices outside the context do not enter environment typing. -/
def covSOriginEnv : EnvT := fun _ c => c = .prop

def covSOriginCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n covSOriginCtx :=
  .assumption _ _ _
    (.assumption [] _ _ .nil (.sort [] (.succ .zero)))
    (.sort _ (.succ .zero))

theorem covSOrigin_lookup {i : Nat} {A : Expr Nat}
    (h : lookupType covSOriginCtx i = some A) : A = .sort (.succ .zero) := by
  cases i with
  | zero => exact (Option.some.inj h).symm
  | succ i =>
      cases i with
      | zero => exact (Option.some.inj h).symm
      | succ i => simp [covSOriginCtx, lookupType] at h

/-- This is the old finite-joint model-typing obligation, actually supplied
for the same valuation used by both observations. -/
theorem covSOrigin_env_typed (E : ResolvedEnv) (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK E n covSOriginCtx) covSOriginCtx covSOriginEnv := by
  intro i A hA us hus
  obtain rfl := covSOrigin_lookup hA
  refine ⟨.sort, ?_, ?_⟩
  · simpa only [sortCode_succ] using
      approxTK_sort_code E n covSOriginCtx covSOriginEnv (.succ .zero)
  · intro c hc
    have he : c = .prop := hus c hc
    subst c
    exact ctyS_prop_sort E

theorem covSOrigin_ctx_coherent (E : ResolvedEnv) (n : Nat) :
    CtxEnvM (ctxModelT_approxTK E n covSOriginCtx) covSOriginCtx covSOriginEnv := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i => simp [covSOriginCtx, lookupValue] at hv

def covSOrigin_var0_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSOriginCtx (.bvar 0) (.sort (.succ .zero)) :=
  .bvar _ 0 _ rfl

def covSOrigin_var1_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSOriginCtx (.bvar 1) (.sort (.succ .zero)) :=
  .bvar _ 1 _ rfl

theorem covSOrigin_var0_observed (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n covSOriginCtx covSOriginEnv (.bvar 0) .prop :=
  .free (kFreeT_bvar E 0) (.bvar rfl)

theorem covSOrigin_var1_observed (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n covSOriginCtx covSOriginEnv (.bvar 1) .prop :=
  .free (kFreeT_bvar E 1) (.bvar rfl)

/-- Any proposed target syntax with distinct variable labels encounters
the same collision. The failing observation is nonbottom. -/
theorem covSOrigin_no_variable_decoder_generic {α : Type u} (n : Nat)
    (label : Nat → α) (hne : label 0 ≠ label 1) :
    ¬ ∃ decode : CptT → α,
      ∀ i c, i < 2 → ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar i) c →
        c ≠ .bot → decode c = label i := by
  rintro ⟨decode, hd⟩
  have h0 := hd 0 .prop (by decide) (covSOrigin_var0_observed emptyEnv n)
    (fun h => CptT.noConfusion h)
  have h1 := hd 1 .prop (by decide) (covSOrigin_var1_observed emptyEnv n)
    (fun h => CptT.noConfusion h)
  exact hne (h0.symm.trans h1)

theorem covSOrigin_no_variable_decoder (n : Nat) :
    ¬ ∃ decode : CptT → Option Nat,
      ∀ i c, i < 2 → ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar i) c →
        c ≠ .bot → decode c = some i :=
  covSOrigin_no_variable_decoder_generic n some (by decide)

/-- Native context, both typings, both self conversions, old environment
typing, let coherence, and both colliding observations are inhabited. -/
theorem covSOrigin_variable_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n covSOriginCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSOriginCtx)
      covSOriginCtx covSOriginEnv ∧
    CtxEnvM (ctxModelT_approxTK emptyEnv n covSOriginCtx) covSOriginCtx covSOriginEnv ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx (.bvar 1) (.sort (.succ .zero))) ∧
    Nonempty (ConvT emptyEnv n covSOriginCtx (.bvar 0) (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT emptyEnv n covSOriginCtx (.bvar 1) (.bvar 1) (.sort (.succ .zero))) ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar 0) .prop ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar 1) .prop ∧
    (CptT.prop) ≠ .bot ∧
    ¬ ∃ decode : CptT → Option Nat,
      ∀ i c, i < 2 → ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar i) c →
        c ≠ .bot → decode c = some i :=
  ⟨⟨.empty⟩, ⟨covSOriginCtx_wf emptyEnv n⟩,
    covSOrigin_env_typed emptyEnv n, covSOrigin_ctx_coherent emptyEnv n,
    ⟨covSOrigin_var0_hasTy emptyEnv n⟩, ⟨covSOrigin_var1_hasTy emptyEnv n⟩,
    ⟨.refl _ _ _ (covSOrigin_var0_hasTy emptyEnv n)⟩,
    ⟨.refl _ _ _ (covSOrigin_var1_hasTy emptyEnv n)⟩,
    covSOrigin_var0_observed emptyEnv n, covSOrigin_var1_observed emptyEnv n,
    CptT.noConfusion, covSOrigin_no_variable_decoder n⟩

def covSOriginNatArrow : Expr Nat := .pi (.const 0 []) (.const 0 [])

def covSOriginNatArrow_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covSOriginNatArrow (.sort (.succ .zero)) :=
  .conv Γ covSOriginNatArrow (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi Γ (.const 0 []) (.succ .zero) (.const 0 []) (.succ .zero)
      (hasTyT_natEnvU_nat n Γ) (hasTyT_natEnvU_nat n (.assumption (.const 0 []) :: Γ)))
    (.sorts Γ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

/-- The same nonbottom Pi observation has a sort domain at one native type
and an ordinary Nat domain at the other. The unknown domain code is real. -/
theorem covSOrigin_pi_observations (n : Nat) :
    ApproxTK natEnvU n [] EnvT.bot covPPropArrow (.pi .bot []) ∧
    ApproxTK natEnvU n [] EnvT.bot covSOriginNatArrow (.pi .bot []) :=
  ⟨approxTK_pi_bot_nil natEnvU n [] EnvT.bot _ _,
    approxTK_pi_bot_nil natEnvU n [] EnvT.bot _ _⟩

theorem covSOrigin_no_pi_decoder_generic {α : Type u} (n : Nat)
    (sortBinder ordinaryBinder : α) (hne : sortBinder ≠ ordinaryBinder) :
    ¬ ∃ decode : CptT → α,
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covPPropArrow c →
        c ≠ .bot → decode c = sortBinder) ∧
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covSOriginNatArrow c →
        c ≠ .bot → decode c = ordinaryBinder) := by
  rintro ⟨decode, hs, ho⟩
  obtain ⟨hps, hpo⟩ := covSOrigin_pi_observations n
  exact hne ((hs _ hps CptT.noConfusion).symm.trans (ho _ hpo CptT.noConfusion))

theorem covSOrigin_no_pi_decoder (n : Nat) :
    ¬ ∃ decode : CptT → Bool,
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covPPropArrow c →
        c ≠ .bot → decode c = true) ∧
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covSOriginNatArrow c →
        c ≠ .bot → decode c = false) :=
  covSOrigin_no_pi_decoder_generic n true false (by decide)

theorem covSOrigin_pi_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 0 []) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT natEnvU n [] covPPropArrow (.sort (.succ .zero))) ∧
    Nonempty (HasTyT natEnvU n [] covSOriginNatArrow (.sort (.succ .zero))) ∧
    ApproxTK natEnvU n [] EnvT.bot covPPropArrow (.pi .bot []) ∧
    ApproxTK natEnvU n [] EnvT.bot covSOriginNatArrow (.pi .bot []) ∧
    (CptT.pi .bot []) ≠ .bot ∧
    ¬ ∃ decode : CptT → Bool,
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covPPropArrow c →
        c ≠ .bot → decode c = true) ∧
      (∀ c, ApproxTK natEnvU n [] EnvT.bot covSOriginNatArrow c →
        c ≠ .bot → decode c = false) :=
  ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨.sort [] .zero⟩, ⟨hasTyT_natEnvU_nat n []⟩,
    ⟨covPPropArrow_hasTy natEnvU n []⟩, ⟨covSOriginNatArrow_hasTy n []⟩,
    (covSOrigin_pi_observations n).1, (covSOrigin_pi_observations n).2,
    CptT.noConfusion, covSOrigin_no_pi_decoder n⟩

/-- The domain is a lexical type variable, not a native sort expression. -/
def covSOriginVarArrow : Expr Nat := .pi (.bvar 0) (.sort .zero)

def covSOriginVarArrow_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSOriginCtx covSOriginVarArrow (.sort (.succ .zero)) :=
  .conv covSOriginCtx covSOriginVarArrow
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi covSOriginCtx (.bvar 0) (.succ .zero) (.sort .zero) (.succ .zero)
      (covSOrigin_var0_hasTy E n) (.sort (.assumption (.bvar 0) :: covSOriginCtx) .zero))
    (.sorts covSOriginCtx (.imax (.succ .zero) (.succ .zero))
      (.succ .zero) (fun _ => rfl))

/-- Literal Prop and a type variable have the same nonbottom domain
observation, and their Pi types share `pi prop []` in this same valuation. -/
theorem covSOrigin_prop_domain_observations (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n covSOriginCtx covSOriginEnv (.sort .zero) .prop ∧
    ApproxTK E n covSOriginCtx covSOriginEnv (.bvar 0) .prop ∧
    ApproxTK E n covSOriginCtx covSOriginEnv covPPropArrow (.pi .prop []) ∧
    ApproxTK E n covSOriginCtx covSOriginEnv covSOriginVarArrow (.pi .prop []) := by
  have hs : ApproxTK E n covSOriginCtx covSOriginEnv (.sort .zero) .prop := by
    simpa only [sortCode_zero] using
      approxTK_sort_code E n covSOriginCtx covSOriginEnv .zero
  have hv := covSOrigin_var0_observed E n
  exact ⟨hs, hv,
    .pi hs (by intro row hrow; cases hrow) (by intro row hrow; cases hrow),
    .pi hv (by intro row hrow; cases hrow) (by intro row hrow; cases hrow)⟩

/-- Even restricting the proposed classifier to Pi observations with
nonbottom domain `.prop` cannot distinguish literal-sort and variable
domains. The labels describe native origin, not observed shape. -/
theorem covSOrigin_no_prop_domain_decoder_generic {α : Type u} (n : Nat)
    (literalSort variableDomain : α) (hne : literalSort ≠ variableDomain) :
    ¬ ∃ decode : CptT → α,
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covPPropArrow (.pi .prop rows) → decode (.pi .prop rows) = literalSort) ∧
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covSOriginVarArrow (.pi .prop rows) → decode (.pi .prop rows) = variableDomain) := by
  rintro ⟨decode, hs, hv⟩
  obtain ⟨_, _, hps, hpv⟩ := covSOrigin_prop_domain_observations emptyEnv n
  exact hne ((hs [] hps).symm.trans (hv [] hpv))

theorem covSOrigin_no_prop_domain_decoder (n : Nat) :
    ¬ ∃ decode : CptT → Bool,
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covPPropArrow (.pi .prop rows) → decode (.pi .prop rows) = true) ∧
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covSOriginVarArrow (.pi .prop rows) → decode (.pi .prop rows) = false) :=
  covSOrigin_no_prop_domain_decoder_generic n true false (by decide)

/-- All native, valuation, and observation premises use the same admitted
context. The variable domain is syntactically distinct from every sort.
Both the domain compact and the shared Pi compact are nonbottom. -/
theorem covSOrigin_prop_domain_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n covSOriginCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSOriginCtx)
      covSOriginCtx covSOriginEnv ∧
    CtxEnvM (ctxModelT_approxTK emptyEnv n covSOriginCtx) covSOriginCtx covSOriginEnv ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx covPPropArrow (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n covSOriginCtx covSOriginVarArrow (.sort (.succ .zero))) ∧
    Nonempty (ConvT emptyEnv n covSOriginCtx covPPropArrow covPPropArrow
      (.sort (.succ .zero))) ∧
    Nonempty (ConvT emptyEnv n covSOriginCtx covSOriginVarArrow covSOriginVarArrow
      (.sort (.succ .zero))) ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.sort .zero) .prop ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv (.bvar 0) .prop ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv covPPropArrow (.pi .prop []) ∧
    ApproxTK emptyEnv n covSOriginCtx covSOriginEnv covSOriginVarArrow (.pi .prop []) ∧
    (∀ l : Level, (Expr.bvar 0 : Expr Nat) ≠ .sort l) ∧
    (CptT.prop) ≠ .bot ∧ (CptT.pi .prop []) ≠ .bot ∧
    ¬ ∃ decode : CptT → Bool,
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covPPropArrow (.pi .prop rows) → decode (.pi .prop rows) = true) ∧
      (∀ rows, ApproxTK emptyEnv n covSOriginCtx covSOriginEnv
        covSOriginVarArrow (.pi .prop rows) → decode (.pi .prop rows) = false) := by
  obtain ⟨hs, hv, hps, hpv⟩ := covSOrigin_prop_domain_observations emptyEnv n
  exact ⟨⟨.empty⟩, ⟨covSOriginCtx_wf emptyEnv n⟩,
    covSOrigin_env_typed emptyEnv n, covSOrigin_ctx_coherent emptyEnv n,
    ⟨.sort covSOriginCtx .zero⟩, ⟨covSOrigin_var0_hasTy emptyEnv n⟩,
    ⟨covPPropArrow_hasTy emptyEnv n covSOriginCtx⟩,
    ⟨covSOriginVarArrow_hasTy emptyEnv n⟩,
    ⟨.refl _ _ _ (covPPropArrow_hasTy emptyEnv n covSOriginCtx)⟩,
    ⟨.refl _ _ _ (covSOriginVarArrow_hasTy emptyEnv n)⟩,
    hs, hv, hps, hpv, (fun _ => Expr.noConfusion), CptT.noConfusion,
    CptT.noConfusion, covSOrigin_no_prop_domain_decoder n⟩

/-- Nonzero universe levels are also erased, independently of Pi rows. -/
theorem covSOrigin_sort_level_observations (n : Nat) :
    ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ .zero)) .sort ∧
    ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ (.succ .zero))) .sort := by
  constructor
  · simpa only [sortCode_succ] using
      approxTK_sort_code emptyEnv n [] EnvT.bot (.succ .zero)
  · simpa only [sortCode_succ] using
      approxTK_sort_code emptyEnv n [] EnvT.bot (.succ (.succ .zero))

theorem covSOrigin_no_sort_level_decoder (n : Nat) :
    ¬ ∃ decode : CptT → Level,
      (∀ c, ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ .zero)) c →
        c ≠ .bot → decode c = .succ .zero) ∧
      (∀ c, ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ (.succ .zero))) c →
        c ≠ .bot → decode c = .succ (.succ .zero)) := by
  rintro ⟨decode, h1, h2⟩
  obtain ⟨ho1, ho2⟩ := covSOrigin_sort_level_observations n
  have he := (h1 _ ho1 CptT.noConfusion).symm.trans (h2 _ ho2 CptT.noConfusion)
  exact Level.noConfusion (Level.succ.inj he)

theorem covSOrigin_sort_level_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] (.sort (.succ .zero))
      (.sort (.succ (.succ .zero)))) ∧
    Nonempty (HasTyT emptyEnv n [] (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ (.succ .zero))))) ∧
    ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ .zero)) .sort ∧
    ApproxTK emptyEnv n [] EnvT.bot (.sort (.succ (.succ .zero))) .sort ∧
    (CptT.sort) ≠ .bot :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨.sort [] (.succ .zero)⟩, ⟨.sort [] (.succ (.succ .zero))⟩,
    (covSOrigin_sort_level_observations n).1, (covSOrigin_sort_level_observations n).2,
    CptT.noConfusion⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_ORIGIN_ROOTS
#print axioms covSOriginCtx
#print axioms covSOriginEnv
#print axioms covSOriginCtx_wf
#print axioms covSOrigin_lookup
#print axioms covSOrigin_env_typed
#print axioms covSOrigin_ctx_coherent
#print axioms covSOrigin_var0_hasTy
#print axioms covSOrigin_var1_hasTy
#print axioms covSOrigin_var0_observed
#print axioms covSOrigin_var1_observed
#print axioms covSOrigin_no_variable_decoder_generic
#print axioms covSOrigin_no_variable_decoder
#print axioms covSOrigin_variable_control
#print axioms covSOriginNatArrow
#print axioms covSOriginNatArrow_hasTy
#print axioms covSOrigin_pi_observations
#print axioms covSOrigin_no_pi_decoder_generic
#print axioms covSOrigin_no_pi_decoder
#print axioms covSOrigin_pi_control
#print axioms covSOriginVarArrow
#print axioms covSOriginVarArrow_hasTy
#print axioms covSOrigin_prop_domain_observations
#print axioms covSOrigin_no_prop_domain_decoder_generic
#print axioms covSOrigin_no_prop_domain_decoder
#print axioms covSOrigin_prop_domain_control
#print axioms covSOrigin_sort_level_observations
#print axioms covSOrigin_no_sort_level_decoder
#print axioms covSOrigin_sort_level_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_ORIGIN_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
