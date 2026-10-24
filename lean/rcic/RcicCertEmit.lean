import rcic.RcicCertKernel

/-!
# RcicCertEmit — first-order entry points of the derivation-carrying cert machine (F1)

`certStep` (RcicCertKernel) takes a `CertState` whose environment is a *function*
(`ResolvedEnv.members`). An emitted scm module cannot receive a function, so the entries
below take the environment as a **lookup table** (`envOfTable`) and return a `Summ`: the
data of the verdict (accept/refuse/suspend and the terms it names) without the derivation.

The three entries are `certStep` itself under three tasks; nothing here re-implements the
checker. `Rcic.Machine.RM014T'_whnf_conv`, `RM017T'_conv`, `RM017T'_tyConv` are about the
derivation that an accepted `certStep` carries; `summ_accepted_whnf` etc. below pin that the
entries return exactly the accepted payload's data, so those soundness theorems transfer.

Emission target: `lean/rcic/RcicCertEmitGenerate.lean` (a `run_cmd` writer, not a lake root).
closure_claim 0.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-- the environment as data -/
def envOfTable (tbl : List (Nat × CheckedMember)) : ResolvedEnv :=
  ⟨fun r => (tbl.find? fun p => p.1 == r).map (·.2)⟩

/-- verdict data of a cert run (no derivation) -/
inductive Summ : Type
  | whnfed (e w T : Expr Nat)
  | converted (l r T : Expr Nat)
  | tyConverted (A B : Expr Nat)
  | refused (residue : String)
  | suspended
  deriving DecidableEq

def summ {amb : Ambient} : CertResult amb → Summ
  | .accepted (.whnfed e w T _) => .whnfed e w T
  | .accepted (.converted l r T _) => .converted l r T
  | .accepted (.tyConverted A B _) => .tyConverted A B
  | .refused s => .refused s
  | .suspended => .suspended

def certState (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (task : CertTask) (budget : Nat) : CertState :=
  ⟨⟨envOfTable tbl, univs, ctx⟩, task, budget⟩

/-- `certStep` under a `whnfT T e` task -/
def certWhnfS (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (T e : Expr Nat) (budget : Nat) : Summ :=
  summ (certStep (certState tbl univs ctx (.whnfT T e) budget))

/-- `certStep` under a `convT T l r` task -/
def certConvS (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (T l r : Expr Nat) (budget : Nat) : Summ :=
  summ (certStep (certState tbl univs ctx (.convT T l r) budget))

/-- `certStep` under a `tyConvT A B` task -/
def certTyConvS (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (A B : Expr Nat) (budget : Nat) : Summ :=
  summ (certStep (certState tbl univs ctx (.tyConvT A B) budget))

/-- an accepted whnf entry carries the soundness derivation of `RM014T'_whnf_conv` -/
theorem certWhnfS_sound (tbl univs ctx T e w budget)
    (h : certWhnfS tbl univs ctx T e budget = .whnfed e w T) :
    Nonempty (ConvT (envOfTable tbl) univs ctx e w T) := by
  unfold certWhnfS at h
  generalize hr : certStep (certState tbl univs ctx (.whnfT T e) budget) = r at h
  cases r with
  | accepted p =>
      cases p with
      | whnfed e' w' T' c =>
          simp only [summ, Summ.whnfed.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨c⟩
      | converted _ _ _ _ => simp [summ] at h
      | tyConverted _ _ _ => simp [summ] at h
  | refused s => simp [summ] at h
  | suspended => simp [summ] at h

theorem certConvS_sound (tbl univs ctx T l r budget)
    (h : certConvS tbl univs ctx T l r budget = .converted l r T) :
    Nonempty (ConvT (envOfTable tbl) univs ctx l r T) := by
  unfold certConvS at h
  generalize hr : certStep (certState tbl univs ctx (.convT T l r) budget) = x at h
  cases x with
  | accepted p =>
      cases p with
      | converted l' r' T' c =>
          simp only [summ, Summ.converted.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨c⟩
      | whnfed _ _ _ _ => simp [summ] at h
      | tyConverted _ _ _ => simp [summ] at h
  | refused s => simp [summ] at h
  | suspended => simp [summ] at h

theorem certTyConvS_sound (tbl univs ctx A B budget)
    (h : certTyConvS tbl univs ctx A B budget = .tyConverted A B) :
    Nonempty (TyConvT (envOfTable tbl) univs ctx A B) := by
  unfold certTyConvS at h
  generalize hr : certStep (certState tbl univs ctx (.tyConvT A B) budget) = x at h
  cases x with
  | accepted p =>
      cases p with
      | tyConverted A' B' c =>
          simp only [summ, Summ.tyConverted.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨c⟩
      | whnfed _ _ _ _ => simp [summ] at h
      | converted _ _ _ _ => simp [summ] at h
  | refused s => simp [summ] at h
  | suspended => simp [summ] at h

end Rcic.Machine

#print axioms Rcic.Machine.certWhnfS_sound
#print axioms Rcic.Machine.certConvS_sound
#print axioms Rcic.Machine.certTyConvS_sound
