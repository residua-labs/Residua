import Residua.Bootstrap.SCM

/-!
# Cached signature audit for SCM source export

The complete signature table has the same value at every node of an
intrinsically typed SCM program. Passing its audit result through the walk
avoids traversing that table once per expression, argument, and branch node.
The remaining index and key checks retain the original order and result.
This module does not change `SCM.lean` or any production entry point.

`closure_claim = 0`.
-/

namespace Residua.Bootstrap.SCM

open Residua.Bootstrap.IR

private def auditBothCached
    (a b : Except SCMIdentifierError Unit) :
    Except SCMIdentifierError Unit :=
  match a with
  | .error e => .error e
  | .ok _ => b

mutual

/-- Audit an expression with a precomputed complete signature audit. -/
def auditExprCached (sigAudit : Except SCMIdentifierError Unit)
    (e : SCMExpr S G t) : Except SCMIdentifierError Unit :=
  auditBothCached sigAudit
    (auditBothCached (auditCtx G)
      (auditBothCached (auditBootTy t) (match e with
        | .litI _ | .litB _ | .litS _ | .var _ | .emptyList | .recNil |
            .noneE | .residueE _ => .ok ()
        | .neg a | .notE a | .strLen a | .strToInt a | .listSingleton a |
            .listLen a | .listFirst a | .fstE a | .sndE a | .someE a |
            .isSomeE a | .unwrapSome a | .okE a | .isResidueE a |
            .getResidue a | .getOk a | .packBytes a | .bytesLen a |
            .contentHash a => auditExprCached sigAudit a
        | .let1 a b | .add a b | .sub a b | .mul a b | .divE a b |
            .modE a b | .lt a b | .gt a b | .eqE a b | .andE a b |
            .orE a b | .strSplit a b | .listAppend a b | .listDrop a b |
            .pairE a b | .bytesConcat a b =>
            auditBothCached (auditExprCached sigAudit a) (auditExprCached sigAudit b)
        | .ifE a b c | .strSubstring a b c | .bytesSlice a b c |
            .boundedFold a b c =>
            auditBothCached (auditExprCached sigAudit a)
              (auditBothCached (auditExprCached sigAudit b) (auditExprCached sigAudit c))
        | .boundedFix stop step init bound =>
            auditBothCached (auditExprCached sigAudit stop)
              (auditBothCached (auditExprCached sigAudit step)
                (auditBothCached (auditExprCached sigAudit init)
                  (auditExprCached sigAudit bound)))
        | .inj _ a => auditExprCached sigAudit a
        | .matchE a bs =>
            auditBothCached (auditExprCached sigAudit a) (auditBranchesCached sigAudit bs)
        | .recCons key a rest =>
            auditBothCached (auditRecordKey key)
              (auditBothCached (auditExprCached sigAudit a) (auditExprCached sigAudit rest))
        | .field (fs := fs) a i =>
            auditBothCached (auditRecordKey (fs.get i).1) (auditExprCached sigAudit a)
        | .call _ args => auditArgsCached sigAudit args)))

/-- Audit arguments with the same precomputed signature audit. -/
def auditArgsCached (sigAudit : Except SCMIdentifierError Unit)
    (args : SCMArgs S G ts) : Except SCMIdentifierError Unit :=
  auditBothCached sigAudit
    (auditBothCached (auditCtx G)
      (auditBothCached (auditBootTys ts) (match args with
        | .nil => .ok ()
        | .cons a rest =>
            auditBothCached (auditExprCached sigAudit a) (auditArgsCached sigAudit rest))))

/-- Audit branches with the same precomputed signature audit. -/
def auditBranchesCached (sigAudit : Except SCMIdentifierError Unit)
    (branches : SCMBranches S G ts r) : Except SCMIdentifierError Unit :=
  auditBothCached sigAudit
    (auditBothCached (auditCtx G)
      (auditBothCached (auditBootTys ts)
        (auditBothCached (auditBootTy r) (match branches with
          | .nil => .ok ()
          | .cons b rest =>
              auditBothCached (auditExprCached sigAudit b)
                (auditBranchesCached sigAudit rest)))))

end

private def auditProgramBodiesCached (sigAudit : Except SCMIdentifierError Unit) :
    SCMPrograms S T → Except SCMIdentifierError Unit
  | .nil => .ok ()
  | .cons body rest =>
      auditBothCached (auditExprCached sigAudit body)
        (auditProgramBodiesCached sigAudit rest)

/-- Audit the source signature table once for the entire program collection. -/
def auditProgramsCached (programs : SCMPrograms S T) :
    Except SCMIdentifierError Unit :=
  let sigAudit := auditSigTable S
  auditBothCached sigAudit
    (auditBothCached (auditSigTable T)
      (auditProgramBodiesCached sigAudit programs))

set_option maxHeartbeats 1000000 in
theorem auditExprCached_eq (e : SCMExpr S G t) :
    auditExprCached (auditSigTable S) e = auditSCMExpr e := by
  induction e using SCMExpr.rec
    (motive_2 := fun G ts args =>
      auditArgsCached (auditSigTable S) args = auditSCMArgs args)
    (motive_3 := fun G ts r branches =>
      auditBranchesCached (auditSigTable S) branches = auditSCMBranches branches)
    <;> intros
    <;> simp_all only [auditExprCached, auditSCMExpr,
      auditArgsCached, auditSCMArgs, auditBranchesCached, auditSCMBranches]
    <;> rfl

set_option maxHeartbeats 1000000 in
theorem auditArgsCached_eq (args : SCMArgs S G ts) :
    auditArgsCached (auditSigTable S) args = auditSCMArgs args := by
  induction args using SCMArgs.rec
    (motive_1 := fun G t e =>
      auditExprCached (auditSigTable S) e = auditSCMExpr e)
    (motive_3 := fun G ts r branches =>
      auditBranchesCached (auditSigTable S) branches = auditSCMBranches branches)
    <;> intros
    <;> simp_all only [auditExprCached, auditSCMExpr,
      auditArgsCached, auditSCMArgs, auditBranchesCached, auditSCMBranches]
    <;> rfl

set_option maxHeartbeats 1000000 in
theorem auditBranchesCached_eq (branches : SCMBranches S G ts r) :
    auditBranchesCached (auditSigTable S) branches = auditSCMBranches branches := by
  induction branches using SCMBranches.rec
    (motive_1 := fun G t e =>
      auditExprCached (auditSigTable S) e = auditSCMExpr e)
    (motive_2 := fun G ts args =>
      auditArgsCached (auditSigTable S) args = auditSCMArgs args)
    <;> intros
    <;> simp_all only [auditExprCached, auditSCMExpr,
      auditArgsCached, auditSCMArgs, auditBranchesCached, auditSCMBranches]
    <;> rfl

theorem auditProgramsCached_eq (programs : SCMPrograms S T) :
    auditProgramsCached programs = auditSCMPrograms programs := by
  induction programs with
  | nil => rfl
  | cons body rest ih =>
      rename_i signature tail
      cases hS : auditSigTable S with
      | error e =>
          simp [auditProgramsCached, auditSCMPrograms, auditBothCached, hS]
          rfl
      | ok sourceUnit =>
          cases hT : auditSigTable (signature :: tail) with
          | error e =>
              simp [auditProgramsCached, auditSCMPrograms, auditBothCached, hS, hT]
              rfl
          | ok targetUnit =>
              have hTail : auditSigTable tail = .ok () := by
                change (match auditCtx signature.1 with
                  | .error e => Except.error e
                  | .ok _ => match auditBootTy signature.2 with
                    | .error e => Except.error e
                    | .ok _ => auditSigTable tail) = .ok () at hT
                cases hParams : auditCtx signature.1 <;>
                  cases hResult : auditBootTy signature.2 <;>
                  simp_all
              simp only [auditProgramsCached, auditSCMPrograms,
                auditProgramBodiesCached, auditExprCached_eq, hS, hT, hTail] at ih ⊢
              dsimp [auditBothCached] at ih ⊢
              rw [ih]
              rw [← hS, auditExprCached_eq]
              rw [hS]
              rfl

end Residua.Bootstrap.SCM
