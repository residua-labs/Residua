import rcic.RcicNativeTypedModelCovVAligned
import rcic.RcicNativeTypedModelCovVRealized
import rcic.RcicNativeTypedModelCovUSoundness

/-!
# The previous higher-order Prop counterexample is bottom-only after alignment

The native environment, native self-loop, and explicit empty-context realizer
are unchanged. The new observation grammar cannot observe this recursor at any
non-bottom compact, because every structured witness has a Prop family while
neither native K eligibility predicate is inhabited. This supplies the actual
bottom observation and preserves all native premises; it makes no normalization
claim for the still-diverging type. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCKAudit ReadbackCK2Audit FamModelLRSAudit
open TypedModelCovTAudit

/-- Every structured witness at the actual higher-order recursor has its
declared Prop family. No witness is supplied by an unproved recognition port. -/
theorem covVHo_rec_family_prop (w : IotaWitnessS covUHoEnv)
    (hr : w.recRef = 65) : PropFamilyS w := by
  have hm : w.recMember = covUHoRec := by
    have hh := w.hrec
    rw [hr] at hh
    exact (Option.some.inj hh).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
  have hi := w.hidx
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hnm : w.nMinors = 1 := by omega
  have hfr : w.familyRef = 63 := by have hh := w.hrecIdx; omega
  have hf : w.famMember = covUHoFam := by
    have hh := w.hfam
    rw [hfr] at hh
    exact (Option.some.inj hh).symm
  unfold PropFamilyS
  rw [hf]
  rfl

/-- Alignment blocks the entire recursor constant, including unused curried
rows. This is stronger than rejecting only the old `.prop` output. -/
theorem covVHo_const_only_bot {ρ : EnvT} {r : Nat} {ls : List Level}
    {c : CptT} (hr : r = 65)
    (h : ApproxTN covUHoEnv ρ (.const r ls) c) : c = .bot := by
  cases h with
  | bot => rfl
  | const _ _ _ hrigid _ =>
      subst r
      exact (not_rigidConst_of_recursor covUHoWitness hrigid).elim
  | delta hd _ =>
      subst r
      exact (not_deltaConst_of_recursor covUHoWitness hd).elim
  | recursor _ hnp _ _ _ =>
      exact (hnp (covVHo_rec_family_prop _ hr)).elim
  | recursorProp _ _ hn _ _ =>
      rw [hr] at hn
      exact hn.elim (fun hk => (covUHo_not_kFreeRec hk).elim)
        (fun hk => (covUHo_not_kProjRec hk).elim)

/-- An application cannot create information from a function whose only
aligned observation is bottom. -/
theorem covV_app_only_bot {E : ResolvedEnv} {ρ : EnvT}
    {f a : Expr Nat} {c : CptT}
    (hf : ∀ u, ApproxTN E ρ f u → u = .bot)
    (h : ApproxTN E ρ (.app f a) c) : c = .bot := by
  cases h with
  | bot => rfl
  | app hf' _ _ => cases hf _ hf'
  | appSpine hf' _ => cases hf _ hf'

/-- Every application of this particular recursor remains bottom-only. -/
theorem covVHo_foldApps_only_bot (ρ : EnvT) (ls : List Level)
    (args : List (Expr Nat)) {c : CptT}
    (h : ApproxTN covUHoEnv ρ (foldApps (.const 65 ls) args) c) : c = .bot := by
  have hprop : ∀ (f : Expr Nat),
      (∀ u, ApproxTN covUHoEnv ρ f u → u = .bot) →
      ∀ u, ApproxTN covUHoEnv ρ (foldApps f args) u → u = .bot := by
    clear h
    induction args with
    | nil => intro f hf u hu; exact hf u hu
    | cons a args ih =>
        intro f hf u hu
        exact ih (Expr.app f a) (fun _ hh => covV_app_only_bot hf hh) u hu
  exact hprop (.const 65 ls) (fun _ hh => covVHo_const_only_bot rfl hh) c h

/-- The actual native type from the previous counterexample is bottom-only. -/
theorem covVHo_type_only_bot {ρ : EnvT} {c : CptT}
    (h : ApproxTN covUHoEnv ρ covUHoType c) : c = .bot :=
  covVHo_foldApps_only_bot ρ [.succ (.succ .zero)]
    [covUHoMotive, covUHoMinor, covUHoMajor] h

/-- Guarded rules cannot reintroduce an old source observation: each carries
an aligned source and therefore forgets into the same bottom-only relation. -/
theorem covVHo_type_guarded_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKN covUHoEnv n Γ ρ covUHoType c) : c = .bot :=
  covVHo_type_only_bot (approxTKN_forgetN h)

theorem covVHo_type_bot (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN covUHoEnv n Γ ρ covUHoType .bot := .bot _ _ _

/-- An explicit finite observation exists; the iff is a derived measurement. -/
theorem covVHo_type_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT) :
    ApproxTKN covUHoEnv n Γ ρ covUHoType c ↔ c = .bot := by
  constructor
  · exact covVHo_type_guarded_only_bot
  · intro hc
    subst c
    exact covVHo_type_bot n Γ ρ

/-- Every native and valuation premise remains inhabited. The explicit fixed
realizer is supplied in the aligned relation itself, at the same stage. -/
theorem covVHo_repaired_instance (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    CovVRealized covUHoEnv n 1 [] EnvT.bot SubstT.id ∧
    EnvTypedFinAtT (ctxModelT_approxTK covUHoEnv n []) [] EnvT.bot ∧
    CtxEnvM (ctxModelT_approxTK covUHoEnv n []) [] EnvT.bot ∧
    Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) ∧
    ApproxTKNStage covUHoEnv n 1 [] EnvT.bot covUHoType .bot ∧
    (∀ c, ApproxTKN covUHoEnv n [] EnvT.bot covUHoType c → c = .bot) ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N := by
  exact ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, covV_realized_nil covUHoEnv n 1,
    envTypedFinAtT_nil _ _, (fun _ _ hv => Option.noConfusion hv),
    ⟨covUHoType_hasTy n []⟩, approxTKNStage_bot covUHoEnv n 1 [] EnvT.bot covUHoType,
    (fun _ h => covVHo_type_guarded_only_bot h), covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_HO_ROOTS
#print axioms covVHo_rec_family_prop
#print axioms covVHo_const_only_bot
#print axioms covV_app_only_bot
#print axioms covVHo_foldApps_only_bot
#print axioms covVHo_type_only_bot
#print axioms covVHo_type_guarded_only_bot
#print axioms covVHo_type_bot
#print axioms covVHo_type_observation_iff
#print axioms covVHo_repaired_instance
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_HO_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
