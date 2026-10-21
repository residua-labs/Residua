/-
Family reference of a stored constructor or recursor type.

These four functions used to sit in `RcicEnv`, above `EnvWf`. The
admission judgment names `memberFamRef`, and `EnvWf` names the
judgment, so the functions have to be below `EnvWf`. They are pure
reads of a telescope; nothing here imports `RcicEnv`.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

/-- Innermost body of a Π-telescope. -/
def piResult : Expr Nat → Expr Nat
  | .pi _ B => piResult B
  | T => T

/-- LAST domain of a Π-telescope; `none` when the type has no binder. -/
def piLastDom : Expr Nat → Option (Expr Nat)
  | .pi A B =>
      match piLastDom B with
      | some D => some D
      | none => some A
  | _ => none

/-- Head reference of an application spine, when the head is a `const`. -/
def spineHeadRef (e : Expr Nat) : Option Nat :=
  match (appsSpine e).1 with
  | .const r _ => some r
  | _ => none

/-- The family a stored type DECLARES itself to belong to. A
constructor's is the head of its telescope RESULT (05 §6: `I params
idx`); a recursor's is the head of its LAST domain, the major premise
(05 §13: `Π … (I params indices), motive indices major`). Determinate
from `m.mtype` alone, hence checkable at admission — and identifiable
with an `IotaWitness`'s `familyRef`, because `hfamApp` fixes the ctor
result's head and `hmajorTy` fixes the recursor's last domain
(`piResult_of_peelPis` / `piLastDom_of_peelPis` below). -/
def memberFamRef (m : CheckedMember) : Option Nat :=
  match m.mclass with
  | .constructorM => spineHeadRef (piResult m.mtype)
  | .recursorM =>
      match piLastDom m.mtype with
      | some D => spineHeadRef D
      | none => none
  | _ => none

end Rcic.Declarative
