import rcic.RcicNativeTypedModelCovWRigidSpines

/-! Composition with the landed grammar in contexts without local definitions.
The reverse direction additionally requires every admitted recursor to have a
legacy witness. These are observation transports, not fundamental suppliers. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

def CovWRigidLocalFree (Γ : LCtx) : Prop := ∀ i, lookupValue Γ i = none

theorem covWRigid_localFree_nil : CovWRigidLocalFree [] := by
  intro i
  rfl

theorem covWRigid_localFree_cons {Γ : LCtx} (A : Expr Nat)
    (h : CovWRigidLocalFree Γ) : CovWRigidLocalFree (.assumption A :: Γ) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    rw [lookupValue_cons_succ, h i]
    rfl

/-- All old observations survive in contexts without let entries. -/
theorem covWRigid_of_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (ho : ApproxTKWConv E n Γ ρ e c) :
    CovWRigidLocalFree Γ → ApproxTKWRigid E n Γ ρ e c := by
  induction ho with
  | bot => intro hN; exact .bot _ _ _
  | bvar h => intro hN; exact .bvar (hN _) h
  | sort Γ ρ l => intro hN; exact .sort _ _ _
  | const Γ ρ r ls hr hp => intro hN; exact .const _ _ _ _ hr hp
  | recursor ls hi hp hpre hf h ih =>
    intro hN
    exact .recursor ls hi hp hpre hf (ih covWRigid_localFree_nil)
  | pi hA ht hb ihA ihb =>
    intro hN
    exact .pi (ihA hN) ht (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))
  | lam hA ht hn hb ihA ihb =>
    intro hN
    exact .lam (ihA hN) ht hn (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))
  | app hf hs ha ihf iha =>
    intro hN
    exact .app (ihf hN) hs (fun u hu => iha u hu hN)
  | appSpine hf ha hslot hfield ihf iha =>
    intro hN
    exact .appSpine (ihf hN) (iha hN) hslot hfield
  | delta hd h ih => intro hN; exact .delta hd (ih covWRigid_localFree_nil)
  | letE h ih => intro hN; exact .letE (ih hN)
  | lit h ih => intro hN; exact .lit (ih hN)
  | iota w hl hr h ih => intro hN; exact .iota w hl hr (ih hN)
  | recursorPropK w x hk h ih => intro hN; exact .recursorPropK w x hk (ih hN)
  | eta he hD ht hn hb ihD ihb =>
    intro hN
    exact .eta (fun i _ => hN i) he (ihD hN) ht hn
      (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))

/-- In a legacy-only environment, local-free observations gain no additional
constructors. The no-rigid-head premise is checked by the caller. -/
theorem covWRigid_to_conv {E : ResolvedEnv} {n : Nat}
    (hR : ∀ r, ¬ CovWRigidRecursor E r) {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (ho : ApproxTKWRigid E n Γ ρ e c) :
    CovWRigidLocalFree Γ → ApproxTKWConv E n Γ ρ e c := by
  induction ho with
  | bot => intro hN; exact .bot _ _ _
  | bvar hl h => intro hN; exact .bvar h
  | zetaLocal hv h ih =>
    intro hN
    rw [hN _] at hv
    cases hv
  | sort Γ ρ l => intro hN; exact .sort _ _ _
  | const Γ ρ r ls hr hp => intro hN; exact .const _ _ _ _ hr hp
  | rigidRecursor Γ ρ r ls hr => intro hN; exact (hR r hr).elim
  | recursor ls hi hp hpre hf h ih =>
    intro hN
    exact .recursor ls hi hp hpre hf (ih covWRigid_localFree_nil)
  | pi hA ht hb ihA ihb =>
    intro hN
    exact .pi (ihA hN) ht (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))
  | lam hA ht hn hb ihA ihb =>
    intro hN
    exact .lam (ihA hN) ht hn (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))
  | app hf hs ha ihf iha =>
    intro hN
    exact .app (ihf hN) hs (fun u hu => iha u hu hN)
  | appSpine hf ha hslot hfield ihf iha =>
    intro hN
    exact .appSpine (ihf hN) (iha hN) hslot hfield
  | delta hd h ih => intro hN; exact .delta hd (ih covWRigid_localFree_nil)
  | letE h ih => intro hN; exact .letE (ih hN)
  | lit h ih => intro hN; exact .lit (ih hN)
  | iota w hl hr h ih => intro hN; exact .iota w hl hr (ih hN)
  | recursorPropK w x hk h ih => intro hN; exact .recursorPropK w x hk (ih hN)
  | eta hh he hD ht hn hb ihD ihb =>
    intro hN
    exact .eta he (ihD hN) ht hn
      (fun s hs => ihb s hs (covWRigid_localFree_cons _ hN))

theorem covWRigid_observations_of_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConv}
    (hN : CovWRigidLocalFree Γ) (ho : CovWConvObservation E n Γ ρ e c) :
    CovWRigidObservation E n Γ ρ e c := by
  obtain ⟨d, hd, ho⟩ := ho
  exact ⟨d, hd, covWRigid_of_conv ho hN⟩

theorem covWRigid_empty_no_recursors (r : Nat) : ¬ CovWRigidRecursor emptyEnv r := by
  rintro ⟨m, hm, hk, hw⟩
  cases hm

theorem covWRigid_empty_observations_iff {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConv}
    (hN : CovWRigidLocalFree Γ) :
    CovWRigidObservation emptyEnv n Γ ρ e c ↔ CovWConvObservation emptyEnv n Γ ρ e c := by
  constructor
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWRigid_to_conv covWRigid_empty_no_recursors ho hN⟩
  · exact covWRigid_observations_of_conv hN

/-- Bare universes remain complete by the landed level-code theorem. -/
def covWRigid_sort_complete {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {u v : Level} (hN : CovWRigidLocalFree Γ)
    (h : ∀ c, CovWRigidObservation emptyEnv n Γ ρ (.sort u) c ↔
      CovWRigidObservation emptyEnv n Γ ρ (.sort v) c) :
    ConvT emptyEnv n Γ (.sort u) (.sort v) (.sort (.succ u)) :=
  covWConv_sort_complete (fun c =>
    (covWRigid_empty_observations_iff hN).symm.trans
      ((h c).trans (covWRigid_empty_observations_iff hN)))

/-- The landed Pi-of-universes fragment composes without changing its target. -/
def covWRigid_pi_sort_complete {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {u v u' v' : Level} (hN : CovWRigidLocalFree Γ)
    (h : ∀ c,
      CovWRigidObservation emptyEnv n Γ ρ (.pi (.sort u) (.sort v)) c ↔
      CovWRigidObservation emptyEnv n Γ ρ (.pi (.sort u') (.sort v')) c) :
    ConvT emptyEnv n Γ (.pi (.sort u) (.sort v)) (.pi (.sort u') (.sort v'))
      (.sort (.imax (.succ u) (.succ v))) :=
  covWConv_pi_sort_complete (fun c =>
    (covWRigid_empty_observations_iff hN).symm.trans
      ((h c).trans (covWRigid_empty_observations_iff hN)))

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLocalFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_of_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_to_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observations_of_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_no_recursors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_observations_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_sort_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_pi_sort_complete
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
