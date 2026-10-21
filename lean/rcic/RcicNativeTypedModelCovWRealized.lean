import rcic.RcicNativeTypedModelCovWAligned
import rcic.RcicNativeTypedModelCovVRealized

/-!
# Concrete environments and realized valuations after per-call alignment

All stage bounds are the existing compact-information budget. The raw
substitution result obtained by forgetting is explicitly the older aligned
relation; no general guarded substitution is claimed here.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKTransportAudit TypedModelKFragmentAudit
open TypedModelKIndexFreeAudit ReadbackCKAudit ReadbackCK2IndexAudit
open ReadbackCK2InputsAudit PiProbeModelBoundaryAudit
open TypedModelCovVAudit TypedModelCovTAudit

theorem covW_eq_prop_indexed : CovWPropRecIndexed eqEnvT := by
  intro w _
  have hr : w.recRef = 65 := by
    by_cases hr : w.recRef = 65
    · exact hr
    · have hm := w.hrec
      by_cases h64 : w.recRef = 64
      · rw [eqEnvT_mem, if_neg hr, if_pos h64] at hm
        have he : w.recMember = eqReflT := (Option.some.inj hm).symm
        have hc := w.hrecK
        rw [he] at hc
        cases hc
      · by_cases h63 : w.recRef = 63
        · rw [eqEnvT_mem, if_neg hr, if_neg h64, if_pos h63] at hm
          have he : w.recMember = eqFamT := (Option.some.inj hm).symm
          have hc := w.hrecK
          rw [he] at hc
          cases hc
        · rw [eqEnvT_mem, if_neg hr, if_neg h64, if_neg h63] at hm
          cases hm
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hd := IotaWitnessS.recData_admitted eqGroupAdm (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  rw [hd.2.2.2.1]
  decide

theorem covW_nat_prop_indexed : CovWPropRecIndexed natEnvU := by
  intro w hp
  have hd := natEnvU_witness_refs (fun _ _ h => h)
    w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  change piBody w.famMember.mtype = .sort .zero at hp
  rw [hd.1.2] at hp
  cases hp

theorem covW_empty_prop_indexed : CovWPropRecIndexed emptyEnv := by
  intro w _
  have h := w.hrec
  cases h

theorem covW_from_old {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    (hV : CovVPropHeadsNative E) (hW : CovWPropRecIndexed E)
    {e : Expr Nat} {c : CptT} (h : ApproxTK E n Γ ρ e c) :
    ApproxTKW E n Γ ρ e c :=
  covW_guarded_of_indexed_prop hW (covV_approxTK_of_native_heads hV h)

theorem covW_forget_old {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {e : Expr Nat} {c : CptT} (h : ApproxTKW E n Γ ρ e c) :
    ApproxTK E n Γ ρ e c := approxTKN_forget (approxTKW_forget h)

def ApproxTKWStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) (c : CptT) : Prop :=
  ApproxTKW E arity Γ ρ e c ∧ covTObservationBudget c ≤ stage

theorem ApproxTKWStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKWStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKWStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

theorem covW_stage_of_indexed_prop {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (hE : CovWPropRecIndexed E) (h : ApproxTKNStage E arity stage Γ ρ e c) :
    ApproxTKWStage E arity stage Γ ρ e c :=
  ⟨covW_guarded_of_indexed_prop hE h.1, h.2⟩

structure CovWRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ i c, ρ i c → ApproxTKWStage E arity stage [] EnvT.bot (σ i) c

theorem CovWRealized.forget {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (h : CovWRealized E arity stage Γ ρ σ) :
    CovVRealized E arity stage Γ ρ σ :=
  ⟨h.typing, fun i c hc => ⟨approxTKW_forget (h.observed i c hc).1,
    (h.observed i c hc).2⟩⟩

theorem covW_realized_of_indexed_prop {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (hE : CovWPropRecIndexed E) (h : CovVRealized E arity stage Γ ρ σ) :
    CovWRealized E arity stage Γ ρ σ :=
  ⟨h.typing, fun i c hc => covW_stage_of_indexed_prop hE (h.observed i c hc)⟩

theorem covW_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovWRealized E arity stage [] EnvT.bot SubstT.id :=
  ⟨(covV_realized_nil E arity stage).typing, fun _ c hc => by
    have he : c = .bot := hc
    subst c
    exact ⟨.bot _ _ _, by simp [covTObservationBudget]⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_REALIZED_ROOTS
#print axioms covW_eq_prop_indexed
#print axioms covW_nat_prop_indexed
#print axioms covW_empty_prop_indexed
#print axioms covW_from_old
#print axioms covW_forget_old
#print axioms ApproxTKWStage
#print axioms ApproxTKWStage.mono
#print axioms covW_stage_of_indexed_prop
#print axioms CovWRealized
#print axioms CovWRealized.forget
#print axioms covW_realized_of_indexed_prop
#print axioms covW_realized_nil
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_REALIZED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
