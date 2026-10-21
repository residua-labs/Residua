import rcic.RcicF8UAppDemand
import rcic.RcicF8XValleyVia
import rcic.RcicPEqTProofFront
import rcic.RcicTypedWeaken

/-!
# `RcicF8UAppDemandPins` — actual supplied-chain U→X controls

ChatGPT's fixture design from `S0_UX_REENTRY_DEMAND.md` §4. The second
typing of the same variable contains two real `HasTyT.conv` layers,
using the existing `betaRedexConv` transported into the actual context.
`cActual` is obtained from the original `suppliedChain` result. Its
shape, flattening, segmentation and admission are proved about that
result; the existing `betaMiddleT` admission theorem is not reused.

The positive control also runs the original `suppliedChain`; its actual
X path is empty Stratum A and answers with the real declining supplier
bundle. Neither control uses `UProcXPins.pinX`. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure.UAppDemandPins

open Rcic.Syn
open PEqTProofFront

def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty

def ss : EnvMembersSubstStable emptyEnv := envMembersSubstStable_of_envWfT EnvWfT.empty

abbrev uX : Level := .imax (.succ .zero) (.succ .zero)

def ctx : LCtx := [.assumption piX]

def ctxWf : CtxWfT emptyEnv 0 ctx :=
  .assumption [] piX uX .nil (pinPiT emptyEnv 0)

def via : CtxWfVia emptyEnv 0 ctx := .ofWf ctxWf

def functionTy : HasTyT emptyEnv 0 ctx (.bvar 0) piX :=
  .bvar ctx 0 piX rfl

def argumentTy : HasTyT emptyEnv 0 ctx P (.sort .zero) := P_ty ctx

/-- Reuse the existing β proof, in exactly the context of both apps. -/
def betaInCtx : ConvT emptyEnv 0 ctx betaRedex piX sX :=
  convTWeaken (.assumption piX) cl (c := 0) betaRedexConv

def betaToRedex : ConvT emptyEnv 0 ctx piX betaRedex sX :=
  .symm ctx betaRedex piX sX betaInCtx

/-- The first real conversion layer, Π→application. -/
def functionAtRedex : HasTyT emptyEnv 0 ctx (.bvar 0) betaRedex :=
  .conv ctx (.bvar 0) piX betaRedex uX functionTy betaToRedex

/-- The second real conversion layer, application→Π. -/
def functionDetour : HasTyT emptyEnv 0 ctx (.bvar 0) piX :=
  .conv ctx (.bvar 0) betaRedex piX uX functionAtRedex betaInCtx

def leftTyping : HasTyT emptyEnv 0 ctx (.app (.bvar 0) P) (.sort .zero) :=
  .app ctx (.bvar 0) P (.sort .zero) (.sort .zero) functionTy argumentTy

def rightTyping : HasTyT emptyEnv 0 ctx (.app (.bvar 0) P) (.sort .zero) :=
  .app ctx (.bvar 0) P (.sort .zero) (.sort .zero) functionDetour argumentTy

def roots : List (Jd emptyEnv 0) := [.ty leftTyping, .ty rightTyping]

def leftCert : ∃ r ∈ roots, SubEq (.ty leftTyping) r :=
  ⟨.ty leftTyping, .head _, .inl rfl⟩

def rightCert : ∃ r ∈ roots, SubEq (.ty rightTyping) r :=
  ⟨.ty rightTyping, .tail _ (.head _), .inl rfl⟩

def left : EvTy roots ctx (.app (.bvar 0) P) (.sort .zero) := .lit leftTyping leftCert

def right : EvTy roots ctx (.app (.bvar 0) P) (.sort .zero) := .lit rightTyping rightCert

/-- Certificates extracted from the original right application typing. -/
def detourCert : ∃ r ∈ roots, SubEq (.ty functionDetour) r :=
  certOfChild (appChildFst functionDetour argumentTy) rightCert

def middleCert : ∃ r ∈ roots, SubEq (.ty functionAtRedex) r :=
  certOfChild (convChildFst functionAtRedex betaInCtx) detourCert

def betaFirstCert : ∃ r ∈ roots, SubEq (.cv betaToRedex) r :=
  certOfChild (convChildSnd functionTy betaToRedex) middleCert

def betaSecondCert : ∃ r ∈ roots, SubEq (.cv betaInCtx) r :=
  certOfChild (convChildSnd functionAtRedex betaInCtx) detourCert

/-- This is the original supplier call, not a chosen endpoint chain. -/
def actualResult : Option (EvTc roots ctx piX piX) :=
  suppliedChain cl ss functionTy argumentTy leftCert functionDetour argumentTy rightCert

theorem actualResult_isSome : actualResult.isSome = true := rfl

/-- Extract only the chain returned by the actual supplier call. -/
def cActual : EvTc roots ctx piX piX := actualResult.get actualResult_isSome

theorem suppliedChain_actual :
    suppliedChain cl ss functionTy argumentTy leftCert functionDetour argumentTy rightCert =
      some cActual := rfl

/-- Correspondence to the actual detour evidence retained by inversion. -/
theorem actual_chain_shape :
    cActual =
      .trans (.trans (.refl ctx piX) (.ofCv uX (.lit betaToRedex betaFirstCert)))
        (.ofCv uX (.lit betaInCtx betaSecondCert)) := rfl

theorem actual_chain_leaves : cActual.leaves = [.cv betaToRedex, .cv betaInCtx] := rfl

theorem actual_not_piSpined : piSpinedTc cActual = false := rfl

theorem actual_flat_length : (flattenTc cActual).length = 2 := rfl

/-- `splitPi` selects the two-link prefix with the real app in the middle. -/
theorem actual_segment_prefix_length :
    ((flattenTc cActual).splitPi rfl).2.2.1.length = 2 := rfl

theorem actual_segment_remainder_length :
    ((flattenTc cActual).splitPi rfl).2.2.2.length = 0 := rfl

theorem actual_segment_interior :
    ((flattenTc cActual).splitPi rfl).2.2.1.interiorNonPi = true := rfl

/-- Admission is checked on the actual supplied result. -/
theorem actual_xAdm : xAdm cActual = true := rfl

theorem actual_xAdmW : xAdmW cActual = true := xAdmW_of_xAdm cActual actual_xAdm

theorem actual_pre_isSome : (uAppPre cl ss left right).isSome = true := rfl

def actualAwait : UAppAwaitX cl ss left right :=
  (uAppPre cl ss left right).get actual_pre_isSome

theorem actual_pre : uAppPre cl ss left right = some actualAwait := rfl

theorem actual_await_chain : actualAwait.chain = cActual := rfl

/-- The real X path refuses when its first actual J callback declines. -/
theorem actual_X_declines (hsep : SepAll emptyEnv 0) :
    xValleySVia? (SuppliersVia.declining hsep) ctxWf cActual actual_xAdmW = none := rfl

/-! ### Stratum A: original function typings without the detour -/

def stratumAResult : Option (EvTc roots ctx piX piX) :=
  suppliedChain cl ss functionTy argumentTy leftCert functionTy argumentTy leftCert

theorem stratumAResult_isSome : stratumAResult.isSome = true := rfl

def cStratumA : EvTc roots ctx piX piX := stratumAResult.get stratumAResult_isSome

theorem suppliedChain_stratumA :
    suppliedChain cl ss functionTy argumentTy leftCert functionTy argumentTy leftCert =
      some cStratumA := rfl

theorem stratumA_chain_shape : cStratumA = .refl ctx piX := rfl

theorem stratumA_flat : flattenTc cStratumA = .nil piX := rfl

theorem stratumA_piSpined : piSpinedTc cStratumA = true := rfl

theorem stratumA_xAdm : xAdm cStratumA = true := rfl

theorem stratumA_xAdmW : xAdmW cStratumA = true := xAdmW_of_xAdm cStratumA stratumA_xAdm

theorem stratumA_pre_isSome : (uAppPre cl ss left left).isSome = true := rfl

def stratumAAwait : UAppAwaitX cl ss left left :=
  (uAppPre cl ss left left).get stratumA_pre_isSome

theorem stratumA_pre : uAppPre cl ss left left = some stratumAAwait := rfl

theorem stratumA_await_chain : stratumAAwait.chain = cStratumA := rfl

/-- Actual X execution with declining suppliers succeeds on the empty
Stratum-A path. The totality layer uses `stratumA_flat` to rule out
phantom J demand on this same entry. -/
theorem stratumA_X_answers (hsep : SepAll emptyEnv 0) :
    (xValleySVia? (SuppliersVia.declining hsep) ctxWf cStratumA stratumA_xAdmW).isSome = true := rfl

end Rcic.Declarative.F8Measure.UAppDemandPins
