import rcic.RcicNativeTypedModelCovVHo
import rcic.RcicNativeTypedModelW6Iota

/-!
# Every ineligible Prop recursor is bottom-only in the aligned model

The retained higher-order singleton is an instance of this general restriction.
The statement concerns all finite application spines of an ineligible Prop
recursor, not merely one chosen nonbottom observation. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit ReadbackCKAudit TypedModelW6IotaAudit PiModelDeltaIotaAudit

/-- No Prop observation rule remains at an ineligible recursor reference. -/
theorem covV_ineligible_prop_const_only_bot {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    {ρ : EnvT} {r : Nat} {ls : List Level} {c : CptT} (hr : r = w.recRef)
    (h : ApproxTN E ρ (.const r ls) c) : c = .bot := by
  cases h with
  | bot => rfl
  | const _ _ _ hrigid _ =>
      subst r
      exact (not_rigidConst_of_recursor w hrigid).elim
  | delta hd _ =>
      subst r
      exact (not_deltaConst_of_recursor w hd).elim
  | recursor _ hnp _ _ _ =>
      exact (hnp ((propFamilyS_iff_recRef_eq hr).mpr hP)).elim
  | recursorProp _ _ hn _ _ =>
      rw [hr] at hn
      exact hn.elim (fun h => (hnF h).elim) (fun h => (hnP h).elim)

/-- A finite application spine cannot create information from a bottom-only head. -/
theorem covV_foldApps_only_bot {E : ResolvedEnv} {ρ : EnvT}
    (args : List (Expr Nat)) : ∀ f : Expr Nat,
    (∀ u, ApproxTN E ρ f u → u = .bot) →
    ∀ c, ApproxTN E ρ (foldApps f args) c → c = .bot := by
  induction args with
  | nil => intro f hf c hc; exact hf c hc
  | cons a args ih =>
      intro f hf c hc
      exact ih (Expr.app f a) (fun _ h => covV_app_only_bot hf h) c hc

/-- This is the promised global exclusion measurement, with actual bottom supply. -/
theorem covV_ineligible_prop_spine {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) (ls : List Level) (args : List (Expr Nat)) :
    ApproxTKN E n Γ ρ (foldApps (.const w.recRef ls) args) .bot ∧
    ∀ c, ApproxTKN E n Γ ρ (foldApps (.const w.recRef ls) args) c → c = .bot := by
  refine ⟨.bot _ _ _, ?_⟩
  intro c hc
  exact covV_foldApps_only_bot args (.const w.recRef ls)
    (fun _ h => covV_ineligible_prop_const_only_bot w hP hnF hnP rfl h)
    c (approxTKN_forgetN hc)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_RESTRICTION_ROOTS
#print axioms covV_ineligible_prop_const_only_bot
#print axioms covV_foldApps_only_bot
#print axioms covV_ineligible_prop_spine
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_RESTRICTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
