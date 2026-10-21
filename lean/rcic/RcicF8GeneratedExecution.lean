import rcic.RcicF8JExecution
import rcic.RcicF8DExecution
import rcic.RcicF8DAddresses

/-!
G0 of ChatGPT's generated/transported provenance design (#7160, spec #7203).
The execution is frozen by an original JInput.  All D queries below are the
actual recursive calls in its selected original trans; results and certificates
are computed, never supplied as completed traces.  G1 generation events and
G2 whole-output origins are deliberately later stages.  closure_claim=0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JExecution

open DExecution DAddresses

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

namespace TransCall

variable {i : JInput E n R}

def rootQuery (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) : DQuery R i.ctx F.T :=
  .star (F.dLeft hW su).spine (F.dRight hW su).spine

def rootJoin (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) := (F.rootQuery hW su).result hW su i.ctxWf

/-- The actual D root includes the same original middle and index, by type,
and the exact output spines materialized by the landed D procedure. -/
theorem rootJoin_exact (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (F : TransCall i) :
    F.K hW su = ⟨(F.rootJoin hW su).d,
      (F.rootJoin hW su).left.toStar, (F.rootJoin hW su).right.toStar⟩ := rfl

end TransCall

/-- Closed recursive addresses, rooted in this original trans's computed D call.
The right strip tail is present only when the actual diamond returns a step.
The ancestry argument keeps paths distinct even when query values coincide. -/
inductive DCallPos (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {i : JInput E n R} (F : TransCall i) : DQuery R i.ctx F.T → Type where
  | root : DCallPos hW su F (F.rootQuery hW su)
  | starStrip {a b c e : Expr Nat} {s : DStep R i.ctx a b F.T}
      {rest : DSpine R i.ctx F.T b c} {ys : DSpine R i.ctx F.T a e} :
      DCallPos hW su F (.star (.tail s rest) ys) →
      DCallPos hW su F (.strip s ys)
  | starTail {a b c e : Expr Nat} {s : DStep R i.ctx a b F.T}
      {rest : DSpine R i.ctx F.T b c} {ys : DSpine R i.ctx F.T a e} :
      DCallPos hW su F (.star (.tail s rest) ys) →
      DCallPos hW su F (.star rest
        ((DQuery.strip s ys).result hW su i.ctxWf).left)
  | stripDiamond {a b c e : Expr Nat} {s : DStep R i.ctx a b F.T}
      {t : DStep R i.ctx a c F.T} {rest : DSpine R i.ctx F.T c e} :
      DCallPos hW su F (.strip s (.tail t rest)) →
      DCallPos hW su F (.step s t)
  | stripTail {a b c e : Expr Nat} {s : DStep R i.ctx a b F.T}
      {t : DStep R i.ctx a c F.T} {rest : DSpine R i.ctx F.T c e}
      {u : DStep R i.ctx c ((DQuery.step s t).result hW su i.ctxWf).d F.T} :
      DCallPos hW su F (.strip s (.tail t rest)) →
      ((DQuery.step s t).result hW su i.ctxWf).right = .step u →
      DCallPos hW su F (.strip u rest)

namespace DCallPos

variable {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
variable {i : JInput E n R} {F : TransCall i} {q : DQuery R i.ctx F.T}

/-- Reading an execution address always computes the existing worker result. -/
def result (_p : DCallPos hW su F q) : q.Result := q.result hW su i.ctxWf

theorem result_exact (p : DCallPos hW su F q) :
    p.result = q.result hW su i.ctxWf := rfl

/-- A selected call has the certificate built by its actual worker. -/
def run (_p : DCallPos hW su F q) : q.Run hW su i.ctxWf :=
  q.buildRun hW su i.ctxWf

theorem run_result (p : DCallPos hW su F q) :
    DQuery.Run.result hW su i.ctxWf p.run = p.result := rfl

end DCallPos

/-- Addresses in the actual two closing legs returned by this trans's D call. -/
inductive DOutputPos (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {i : JInput E n R} (F : TransCall i) : Type where
  | left (p : SpinePos (F.K hW su).2.1.spine) : DOutputPos hW su F
  | right (p : SpinePos (F.K hW su).2.2.spine) : DOutputPos hW su F

namespace DOutputPos

variable {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
variable {i : JInput E n R} {F : TransCall i}

def selected : DOutputPos hW su F → SpineStep R i.ctx F.T
  | .left p => p.selected
  | .right p => p.selected

/-- Route a worker spine position through the actual toStar/spine conversion. -/
def fromLeftRun (p : SpinePos (F.rootJoin hW su).left) : DOutputPos hW su F :=
  .left p.toStarSpine

def fromRightRun (p : SpinePos (F.rootJoin hW su).right) : DOutputPos hW su F :=
  .right p.toStarSpine

theorem fromLeftRun_exact (p : SpinePos (F.rootJoin hW su).left) :
    (fromLeftRun p).selected = p.selected := p.toStarSpine_exact

theorem fromRightRun_exact (p : SpinePos (F.rootJoin hW su).right) :
    (fromRightRun p).selected = p.selected := p.toStarSpine_exact

/-- The connector emits readOutput, after the original child's outer leg. -/
def emit : DOutputPos hW su F → OutputPos hW su (F.atCall.input i)
  | .left p => .left (StarPos.spliceRight
      ((F.p₁ hW su).valley.left.val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
      (p.readOutput (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)))
  | .right p => .right (StarPos.spliceRight
      ((F.p₂ hW su).valley.right.val
        (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW))
      (p.readOutput (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)))

/-- Equality includes the endpoints and the exact materialized proof object. -/
theorem emit_read_exact (o : DOutputPos hW su F) :
    o.emit.selected = o.selected.read
      (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) := by
  cases o with
  | left p =>
      exact (StarPos.spliceRight_exact _ _).trans (p.readOutput_exact _ _)
  | right p =>
      exact (StarPos.spliceRight_exact _ _).trans (p.readOutput_exact _ _)

/-- Reposition the local emission along the original J ancestors. Consumed
legs have no direct embedding; their later D route belongs to G2. -/
def finalOutput (o : DOutputPos hW su F) : Option (OutputPos hW su i) :=
  F.atCall.liftOutput hW su i o.emit

theorem finalOutput_selected (o : DOutputPos hW su F)
    (dst : OutputPos hW su i) (h : o.finalOutput = some dst) :
    dst.selected = F.atCall.transportStep hW i
      (o.selected.read (envClosed_of_envWfT hW)
        (envMembersSubstStable_of_envWfT hW)) := by
  exact (F.atCall.liftOutput_selected hW su i o.emit dst h).trans
    (congrArg (F.atCall.transportStep hW i) o.emit_read_exact)

/-- This is the stored owner-side base certificate, at the exact emitted
local output address, before the closed ancestor transports below. -/
theorem emit_certificate_exact (o : DOutputPos hW su F) :
    HEq o.emit.certificate
      (J5a.baseCertificate (envClosed_of_envWfT hW)
        (envMembersSubstStable_of_envWfT hW) F.localCaller o.selected.step.read) := by
  cases o with
  | left p =>
      exact HEq.trans (StarPos.spliceRight_certificate_exact _ _ _ _)
        (p.readOutput_certificate_exact _ _ _)
  | right p =>
      exact HEq.trans (StarPos.spliceRight_certificate_exact _ _ _ _)
        (p.readOutput_certificate_exact _ _ _)

/-- The selected final certificate is exactly the owner certificate moved by
the closed, actual caller/reindex operations along this original ancestry. -/
theorem finalOutput_certificate_exact (o : DOutputPos hW su F)
    (dst : OutputPos hW su i) (h : o.finalOutput = some dst) :
    HEq dst.certificate
      (F.atCall.transportCertificate hW i
        (o.selected.read (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW))
        (J5a.baseCertificate (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW) F.localCaller o.selected.step.read)) :=
  HEq.trans (F.atCall.liftOutput_certificate_exact hW su i o.emit dst h)
    (F.atCall.transportCertificate_congr hW i o.emit_read_exact
      o.emit_certificate_exact)

end DOutputPos

/-- G0's execution certificate covers every actual D position in every
original trans. It contains no supplied output or completed trace. -/
structure Run (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) where
  dRuns : (F : TransCall i) → (q : DQuery R i.ctx F.T) →
    DCallPos hW su F q → q.Run hW su i.ctxWf

def buildRun (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) : Run hW su i where
  dRuns := fun _ q _ => q.buildRun hW su i.ctxWf

def Run.result {hW : EnvWfT E} {su : F8A2Support.SortUnique E n}
    {i : JInput E n R} (_run : Run hW su i) : J3.Result hW R i.literal :=
  i.result hW su

/-- Equality of the whole actual Result, including both certificate families. -/
theorem buildRun_result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (i : JInput E n R) : (buildRun hW su i).result = i.result hW su := rfl

end Rcic.Declarative.F8Measure.JExecution

#print axioms Rcic.Declarative.F8Measure.JExecution.TransCall.rootJoin_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.DCallPos.run_result
#print axioms Rcic.Declarative.F8Measure.JExecution.DOutputPos.emit_read_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.DOutputPos.emit_certificate_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.DOutputPos.finalOutput_selected
#print axioms Rcic.Declarative.F8Measure.JExecution.DOutputPos.finalOutput_certificate_exact
#print axioms Rcic.Declarative.F8Measure.JExecution.buildRun_result
