import rcic.RcicFabricQ

/-!
# Agent proof fabric — a fact as a Conflux patch proposal (P2)

ADR draft #7925 §2a (second correction): the fabric defines no admission, merge or CI path of its own.
It submits each proof fact as a **Conflux patch** (`docs/CHARTER_CONFLUX.md` P2,
`patch = {target_id, expected_q, new_subtree}`, admitted by content), with `expected_q` = the statement
and the closure the fact relies on. This module defines the two fields the fabric, as the patch's author,
supplies; admission, the patch receipt (`admitted_patch_q`, `resulting_q`, `witness_q`) and merging are
Conflux's.

- `expectedQ stmt deps axioms` — what the fact relies on: its own `stmt_q`; every constant its statement
  or evidence mentions, in first-occurrence order, each with its class and `q` (`logical`: a theorem or
  opaque constant, by `stmt_q`, proof irrelevance; `delta`: a definition, by `body_q`, since dependents
  unfold it; `proj`: a structure projection function, by `stmt_q`, since its body is generated from its
  structure and #7927 refuses projections; `type`: any other constant, by `stmt_q`); and its axiom closure. If any of these changes,
  the patch's `expected_q` no longer matches: the content check that replaces a rebase.
- `factQ stmt body axioms` — the new subtree: the fact itself.

Both are SHA-256 over length-prefixed fields (`encStrs`), composed with `RcicFabricQ`'s digests; no
other encoding is defined here. The target addressing (`target_id`, Conflux B3's `path_id`) is not
defined for a fact: Conflux's patch targets are nodes of a code tree, and a fact store has no such node.
The fabric names the target by `goal_q` and leaves its addressing to Conflux. `closure_claim = 0`.
-/

namespace Rcic.Fabric.Patch

/-- Length-prefixed strings, so that no field can run into the next. -/
def encStrs : List String → String
  | [] => ""
  | s :: ss => toString s.length ++ ":" ++ s ++ encStrs ss

/-- A constant the fact relies on. `cls` is `logical`, `delta`, `proj` or `type`. -/
structure Dep where
  cls : String
  name : String
  q : String
  deriving DecidableEq, Repr

def encDeps (ds : List Dep) : String := encStrs (ds.flatMap fun d => [d.cls, d.name, d.q])

def expectedQ (stmtQ : String) (deps : List Dep) (axioms : List String) : String :=
  Residua.SHA256.sha256Hex
    ("fabric.expected|" ++ encStrs [stmtQ] ++ "|" ++ encDeps deps ++ "|" ++ encStrs axioms)

def factQ (stmtQ bodyQ : String) (axioms : List String) : String :=
  Residua.SHA256.sha256Hex ("fabric.fact|" ++ encStrs [stmtQ, bodyQ] ++ "|" ++ encStrs axioms)

/-- The hashed input of `expectedQ` is exactly these three encodings. -/
theorem expectedQ_input (s : String) (ds : List Dep) (ax : List String) :
    expectedQ s ds ax =
      Residua.SHA256.sha256Hex
        ("fabric.expected|" ++ encStrs [s] ++ "|" ++ encDeps ds ++ "|" ++ encStrs ax) := rfl

end Rcic.Fabric.Patch
