/-
Content identity for a translated declaration.

Encoding provenance: newly defined here. On main, `ExprWire` /
`encExprWireScm` does not round-trip `Expr Nat` (`const : String`, no `lit`).
`showE` is lossy. `Scm.Wire.encExpr` is SCM `RawExpr`. `ScmStepRefines.encExpr`
emits `Val`, not bytes. `stmt_q` / `body_q` are `Residua.SHA256.sha256Hex`
of the payloads below.

§6 dependency class used for the brief's δ edge: `realization`.
`docs/rcic/09` §6 has no class named δ. A definition body is the realization
of its statement, so a const-ref whose target is `definitionM` stores that
target's `body_q` under `realization`. A `theoremM` target stores `stmt_q`
under `logical` and does not store `body_q`.
-/
import rcic.RcicLeanImport
import Residua.SHA256

namespace Rcic.LeanImport

open Rcic.Declarative (MemberClass)

def section6DeltaClass : String := "realization"

def encNat (n : Nat) : String := toString n

def encLevel : Rcic.Declarative.Level → List String
  | .zero => ["Z"]
  | .succ l => "S(" :: encLevel l ++ [")"]
  | .max a b => "M(" :: encLevel a ++ ("," :: encLevel b ++ [")"])
  | .imax a b => "I(" :: encLevel a ++ ("," :: encLevel b ++ [")"])
  | .param i => ["P(", encNat i, ")"]

def encLevels (ls : List Rcic.Declarative.Level) : List String :=
  match ls with
  | [] => []
  | l :: ls => encLevel l ++ (";" :: encLevels ls)

/-- Tagged grammar. Pieces are concatenated once by `encExpr`. -/
def encExprParts : RCExpr → List String
  | .bvar i => ["B(", encNat i, ")"]
  | .sort l => "U(" :: encLevel l ++ [")"]
  | .const r ls => "C(" :: encNat r :: "," :: encLevels ls ++ [")"]
  | .app f x => "A(" :: encExprParts f ++ ("," :: encExprParts x ++ [")"])
  | .lam a b => "L(" :: encExprParts a ++ ("," :: encExprParts b ++ [")"])
  | .pi a b => "P(" :: encExprParts a ++ ("," :: encExprParts b ++ [")"])
  | .letE a v b =>
      "E(" :: encExprParts a ++ ("," :: encExprParts v ++ ("," :: encExprParts b ++ [")"]))
  | .lit n => ["T(", encNat n, ")"]

def encExpr (e : RCExpr) : String :=
  String.join (encExprParts e)

def encParamNames : List Lean.Name → List String
  | [] => []
  | n :: ns => n.toString :: "," :: encParamNames ns

/-- Type plus level-parameter names. The body is not an argument. -/
def stmtPayload (ps : List Lean.Name) (ty : RCExpr) : String :=
  String.join ("stmt|" :: encNat ps.length :: "|" :: encParamNames ps ++ ("|" :: encExprParts ty))

def bodyPayload : Option RCExpr → String
  | none => "body|none"
  | some b => "body|" ++ encExpr b

def stmtQ (ps : List Lean.Name) (ty : RCExpr) : String :=
  Residua.SHA256.sha256Hex (stmtPayload ps ty)

def bodyQ (b : Option RCExpr) : String :=
  Residua.SHA256.sha256Hex (bodyPayload b)

def declStmtQ (d : TranslatedDecl) : String := stmtQ d.levelParams d.mtype
def declBodyQ (d : TranslatedDecl) : String := bodyQ d.body

structure QMember where
  refId : Nat
  mclass : MemberClass
  stmtQ : String
  bodyQ : String
  deriving BEq

def qMemberOf (d : TranslatedDecl) : QMember where
  refId := d.refId
  mclass := d.mclass
  stmtQ := declStmtQ d
  bodyQ := declBodyQ d

/-- `(class, targetQ)`. Definition → `realization` / `body_q`.
    Every other class → `logical` / `stmt_q`. -/
def classifyTarget (cls : MemberClass) (targetStmt targetBody : String) : String × String :=
  match cls with
  | .definitionM => (section6DeltaClass, targetBody)
  | _ => ("logical", targetStmt)

structure DepEdge where
  depClass : String
  targetQ : String
  deriving BEq, Repr, DecidableEq

def constRefs : RCExpr → List Nat
  | .bvar _ => []
  | .sort _ => []
  | .const r _ => [r]
  | .app f x => constRefs f ++ constRefs x
  | .lam a b => constRefs a ++ constRefs b
  | .pi a b => constRefs a ++ constRefs b
  | .letE a v b => constRefs a ++ constRefs v ++ constRefs b
  | .lit _ => []

def lookupQ (env : List QMember) (r : Nat) : Option QMember :=
  match env with
  | [] => none
  | m :: ms => if m.refId == r then some m else lookupQ ms r

def edgeOfRef (env : List QMember) (r : Nat) : Option DepEdge :=
  match lookupQ env r with
  | none => none
  | some m =>
      let (c, q) := classifyTarget m.mclass m.stmtQ m.bodyQ
      some { depClass := c, targetQ := q }

def edgesOfExpr (env : List QMember) (e : RCExpr) : List DepEdge :=
  (constRefs e).filterMap (edgeOfRef env)

def edgesOfDecl (env : List QMember) (d : TranslatedDecl) : List DepEdge :=
  let fromType := edgesOfExpr env d.mtype
  let fromBody :=
    match d.body with
    | none => []
    | some b => edgesOfExpr env b
  fromType ++ fromBody

def countLetE : RCExpr → Nat
  | .letE a v b => countLetE a + countLetE v + countLetE b + 1
  | .app f x => countLetE f + countLetE x
  | .lam a b => countLetE a + countLetE b
  | .pi a b => countLetE a + countLetE b
  | _ => 0

def hasNonemptyLevels : RCExpr → Bool
  | .const _ ls => !ls.isEmpty || false
  | .app f x => hasNonemptyLevels f || hasNonemptyLevels x
  | .lam a b => hasNonemptyLevels a || hasNonemptyLevels b
  | .pi a b => hasNonemptyLevels a || hasNonemptyLevels b
  | .letE a v b => hasNonemptyLevels a || hasNonemptyLevels v || hasNonemptyLevels b
  | _ => false

theorem li_delta_class_realization : section6DeltaClass = "realization" := by
  rfl

theorem li_def_edge_realization (sq bq : String) :
    classifyTarget .definitionM sq bq = ("realization", bq) := by
  rfl

theorem li_thm_edge_logical (sq bq : String) :
    classifyTarget .theoremM sq bq = ("logical", sq) := by
  rfl

theorem li_stmtQ_type_levels (ps : List Lean.Name) (ty : RCExpr) :
    stmtQ ps ty = Residua.SHA256.sha256Hex (stmtPayload ps ty) := by
  rfl

theorem li_bodyQ_payload (b : Option RCExpr) :
    bodyQ b = Residua.SHA256.sha256Hex (bodyPayload b) := by
  rfl

theorem li_enc_lit (n : Nat) : encExprParts (.lit n) = ["T(", encNat n, ")"] := by
  rfl

end Rcic.LeanImport
