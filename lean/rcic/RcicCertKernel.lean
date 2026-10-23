import rcic.RcicTypedMachine
import rcic.RcicTypedMachineAccept

/-!
# CertKernel — derivation-carrying whnf / conversion acceptance

`RcicTypedMachine` carries the derivation in the payload for infer and check
(`RM015T_infer_sound`, `RM016T_check_sound`). This module extends that pattern,
in a new layer beside it (nothing landed is edited), to head-reduction and
conversion tasks:

* `.whnfT T e` — head steps on `e` at the type `T` asked for;
* `.convT T l r` — `l` and `r` converted at `T`;
* `.tyConvT A B` — two types converted.

The accepted payload IS the `ConvT` / `TyConvT` derivation. The proof of the
read-off rows unfolds the arm and takes the payload; it uses no subject
reduction, no `EnvWfT`, no `InScope`, no row.

WHY β NEEDS NO Π-INJECTIVITY HERE. `ConvT.beta`'s premises are `hA : A : Sort u`,
`hbody : body : B` (under `A`) and `harg : arg : A`. They are NOT obtained by
inverting a typing of the redex (that goes through `HasTyT.conv`, so the λ's
domain and the application's domain agree only up to conversion, which is
Π-injectivity, i.e. RK-01 math). They are produced by the checker on the three
parts (`headStep?`: `checkT`, `checkT`, `synCheck`). The step is then moved to
the asked-for type by a `tyConv?` the machine runs and the payload records
(`stepAt?`). A pair the checker cannot type is refused, never accepted.

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-! ## task, state, payload -/

inductive CertTask : Type
  | whnfT (T e : Expr Nat)
  | convT (T l r : Expr Nat)
  | tyConvT (A B : Expr Nat)

structure CertState where
  ambient : Ambient
  task : CertTask
  budget : Nat

/-- The accepted payload: the conversion derivation itself. -/
inductive CertAccepted (amb : Ambient) : Type
  | whnfed (e w T : Expr Nat) (c : ConvT amb.env amb.univs amb.ctx e w T) :
      CertAccepted amb
  | converted (l r T : Expr Nat) (c : ConvT amb.env amb.univs amb.ctx l r T) :
      CertAccepted amb
  | tyConverted (A B : Expr Nat) (c : TyConvT amb.env amb.univs amb.ctx A B) :
      CertAccepted amb

inductive CertResult (amb : Ambient) : Type
  | accepted (p : CertAccepted amb)
  | refused (residue : String)
  | suspended

/-! ## head steps, each carrying its `ConvT` -/

/-- Up to `steps` head steps on `e` (`stepAt?`: β/δ with the checker-typed
    premises, moved to `T`), chained by `ConvT.trans`; the chain ends in
    `ConvT.refl` at a typing of the last term. -/
def certWhnf (E : ResolvedEnv) (n k : Nat) (Γ : LCtx) (T : Expr Nat) :
    Nat → (e : Expr Nat) → Option (Σ w, ConvT E n Γ e w T)
  | 0, e => (tyAtC E n k Γ e T).map fun d => ⟨e, .refl Γ e T d⟩
  | s + 1, e =>
      match stepAt? E n (tyConv? E n k) Γ e T with
      | some ⟨e', c⟩ =>
          (certWhnf E n k Γ T s e').map fun ⟨w, c2⟩ => ⟨w, .trans Γ e e' w T c c2⟩
      | none => (tyAtC E n k Γ e T).map fun d => ⟨e, .refl Γ e T d⟩

/-! ## the step and the run -/

def certStep (s : CertState) : CertResult s.ambient :=
  match s.budget with
  | 0 => .suspended
  | _ + 1 =>
    match s.task with
    | .whnfT T e =>
        match certWhnf s.ambient.env s.ambient.univs s.budget s.ambient.ctx T s.budget e with
        | some ⟨w, c⟩ => .accepted (.whnfed e w T c)
        | none => .refused "[rcic_cert_whnf_refused]"
    | .convT T l r =>
        match convAt? s.ambient.env s.ambient.univs s.budget s.ambient.ctx l r T with
        | some c => .accepted (.converted l r T c)
        | none => .refused "[rcic_cert_conv_refused]"
    | .tyConvT A B =>
        match tyConv? s.ambient.env s.ambient.univs s.budget s.ambient.ctx A B with
        | some c => .accepted (.tyConverted A B c)
        | none => .refused "[rcic_cert_tyconv_refused]"

def certRun : Nat → (s : CertState) → CertResult s.ambient
  | 0, _ => .suspended
  | _ + 1, s => certStep s

/-! ## acceptance soundness — read off the payload; no env/scope premise -/

/-- RM014T': an accepted whnf carries the conversion from the input to the
    result at the asked-for type. -/
def RM014T'_whnf_conv (s : CertState) (T e w : Expr Nat)
    (htask : s.task = .whnfT T e)
    (hacc : Σ' c, certStep s = .accepted (.whnfed e w T c)) :
    ConvT s.ambient.env s.ambient.univs s.ambient.ctx e w T := by
  obtain ⟨c, hd⟩ := hacc
  cases hb : s.budget with
  | zero => simp only [certStep, htask, hb] at hd; nomatch hd
  | succ b =>
      simp only [certStep, htask, hb] at hd
      split at hd
      · rename_i w' c' _
        simp only [CertResult.accepted.injEq, CertAccepted.whnfed.injEq] at hd
        obtain ⟨_, rfl, _, h⟩ := hd
        exact c'
      · nomatch hd

/-- RM017T': an accepted conversion carries the `ConvT`. -/
def RM017T'_conv (s : CertState) (T l r : Expr Nat)
    (htask : s.task = .convT T l r)
    (hacc : Σ' c, certStep s = .accepted (.converted l r T c)) :
    ConvT s.ambient.env s.ambient.univs s.ambient.ctx l r T := by
  obtain ⟨c, hd⟩ := hacc
  cases hb : s.budget with
  | zero => simp only [certStep, htask, hb] at hd; nomatch hd
  | succ b =>
      simp only [certStep, htask, hb] at hd
      split at hd
      · rename_i c' _
        simp only [CertResult.accepted.injEq, CertAccepted.converted.injEq] at hd
        exact c'
      · nomatch hd

/-- RM017T' for types. -/
def RM017T'_tyConv (s : CertState) (A B : Expr Nat)
    (htask : s.task = .tyConvT A B)
    (hacc : Σ' c, certStep s = .accepted (.tyConverted A B c)) :
    TyConvT s.ambient.env s.ambient.univs s.ambient.ctx A B := by
  obtain ⟨c, hd⟩ := hacc
  cases hb : s.budget with
  | zero => simp only [certStep, htask, hb] at hd; nomatch hd
  | succ b =>
      simp only [certStep, htask, hb] at hd
      split at hd
      · rename_i c' _
        simp only [CertResult.accepted.injEq, CertAccepted.tyConverted.injEq] at hd
        exact c'
      · nomatch hd

def RM014T'_run_whnf_conv (k : Nat) (s : CertState) (T e w : Expr Nat)
    (htask : s.task = .whnfT T e)
    (hacc : Σ' c, certRun (k + 1) s = .accepted (.whnfed e w T c)) :
    ConvT s.ambient.env s.ambient.univs s.ambient.ctx e w T :=
  RM014T'_whnf_conv s T e w htask hacc

/-! ## pins — real acceptances (runs by `rfl`), consumed through the rows -/

def pinCertWhnfState : CertState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .whnfT (instantiate0 (.sort .zero) (.sort (.succ .zero))) pinBetaRedex
  budget := 3

def pin_certRun_whnf :
    Σ' c, certRun 3 pinCertWhnfState = .accepted (.whnfed pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) c) := ⟨_, rfl⟩

def pin_RM014T'_whnf :
    ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) :=
  RM014T'_run_whnf_conv 2 pinCertWhnfState _ _ _ rfl pin_certRun_whnf

def pinCertConvState : CertState where
  ambient := ⟨natEnvU, 1, []⟩
  task := .convT (instantiate0 (.sort .zero) (.sort (.succ .zero))) pinBetaRedex pinBetaReduct
  budget := 3

def pin_certStep_conv :
    Σ' c, certStep pinCertConvState = .accepted (.converted pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) c) := ⟨_, rfl⟩

def pin_RM017T'_conv :
    ConvT natEnvU 1 [] pinBetaRedex pinBetaReduct
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) :=
  RM017T'_conv pinCertConvState _ _ _ rfl pin_certStep_conv

/-- REFUSAL tooth: the cert checker refuses this conversion (`Sort 0` against `Sort 1`, as types). -/
def pinCertRefuseState : CertState where
  ambient := ⟨emptyEnv, 1, []⟩
  task := .tyConvT (.sort .zero) (.sort (.succ .zero))
  budget := 3

theorem pin_certStep_tyConv_refused :
    certStep pinCertRefuseState = .refused "[rcic_cert_tyconv_refused]" := rfl

end Rcic.Machine

#print axioms Rcic.Machine.RM014T'_whnf_conv
#print axioms Rcic.Machine.RM017T'_conv
#print axioms Rcic.Machine.RM017T'_tyConv
#print axioms Rcic.Machine.pin_RM014T'_whnf
#print axioms Rcic.Machine.pin_RM017T'_conv
#print axioms Rcic.Machine.pin_certStep_tyConv_refused
