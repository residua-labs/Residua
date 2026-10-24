/-
P5.4 statement keys. `closure_claim = 0`.

FC-TCACHE-EMBED: an assay ground goal is embedded into `RCExpr`, and the
statement q is the landed `Rcic.LeanImport.stmtQ` of that type. This file
does not define a second statement encoder.

* `atom i` is `Expr.lit i`
* `app f a b` is `Expr.app (Expr.app (Expr.lit f) a) b`
* an equation `l = r` is `Expr.app (Expr.app (Expr.const 0 []) l) r`
* level parameters are `[]`

`const 0` is the equation tag. Term encodings use `lit` and `app` only.
The 20 goals are the ground goals of `apps/assay-egraph/assay_eg_search_corpus.json`,
in corpus order. Function symbols are the corpus `f` fields (the nested
row's outer and inner symbols are both 7).
-/
import rcic.RcicLeanImportQ

namespace Rcic.Assay.Tcache

open Rcic.LeanImport

def atom (i : Nat) : RCExpr := .lit i

def appT (f : Nat) (a b : RCExpr) : RCExpr :=
  .app (.app (.lit f) a) b

def eqTy (l r : RCExpr) : RCExpr :=
  .app (.app (.const 0 []) l) r

def goals : List RCExpr := [
  eqTy (atom 0) (atom 0),
  eqTy (atom 0) (atom 1),
  eqTy (atom 1) (atom 0),
  eqTy (atom 1) (atom 2),
  eqTy (atom 2) (atom 1),
  eqTy (atom 0) (atom 2),
  eqTy (atom 2) (atom 0),
  eqTy (appT 7 (atom 0) (atom 0)) (appT 7 (atom 1) (atom 1)),
  eqTy (appT 7 (atom 0) (atom 2)) (appT 7 (atom 1) (atom 1)),
  eqTy (appT 7 (atom 0) (atom 0)) (appT 7 (atom 2) (atom 2)),
  eqTy (appT 7 (atom 0) (atom 1)) (appT 7 (atom 2) (atom 0)),
  eqTy (appT 7 (appT 7 (atom 0) (atom 0)) (atom 0))
       (appT 7 (appT 7 (atom 1) (atom 1)) (atom 0)),
  eqTy (atom 0) (atom 3),
  eqTy (atom 3) (atom 0),
  eqTy (appT 7 (atom 0) (atom 3)) (appT 7 (atom 3) (atom 0)),
  eqTy (atom 3) (atom 4),
  eqTy (appT 7 (atom 3) (atom 0)) (appT 7 (atom 4) (atom 1)),
  eqTy (appT 8 (appT 7 (appT 7 (atom 0) (atom 0)) (atom 0)) (atom 0))
       (appT 8 (appT 7 (appT 7 (atom 1) (atom 1)) (atom 0)) (atom 0)),
  eqTy (appT 8 (appT 7 (appT 7 (atom 0) (atom 0)) (atom 0)) (atom 0))
       (appT 8 (appT 7 (appT 7 (atom 2) (atom 2)) (atom 0)) (atom 0)),
  eqTy
    (appT 7
      (appT 7
        (appT 7
          (appT 7 (appT 7 (atom 3) (atom 4)) (atom 5))
          (atom 6))
        (atom 7))
      (atom 8))
    (atom 9)
]

/-- Digests printed by `#eval goals.map (stmtQ [])`. Each entry is
`stmtQ []` of `goals[i]`, corpus order. -/
def pinnedStmtQ : List String := [
  "0704daf0b8fc0c5ad408e4b0c6fa5466513bb39ac95e72d23272ba1bfe41085d",
  "52c98e32926228f1e51574f8851654a000ce4862145dd4d02315c29673242bd4",
  "0d04ada66adbd5d72ccb358cd2350ce2084a34902ab81e2d5ceeb9d53730940a",
  "5001df1ad7f0fc547f1e10f436fad4df2a182b2e78c86078a63c6b450de49eb1",
  "41c094668e35a12abd5147888b3c39f470369cc2fdd2b492c50a5bda9a720051",
  "c25e078e95cba248d61e292b2bc7aa8756a96fb932b162dc78a6b7a279a84455",
  "4fa66cb1cdc61138a75bbf28ba4f9f2d992a534f476934b707503f0bf58a0739",
  "e13142387a9802ee1da6c042dd628c6e72d625ffdb609df14d5ed3996c939565",
  "13d4342adf11bbab2c458c994b6c70ff8a718833241ef602d9a2a58e0b285022",
  "2f774931f515d94479e89e4c73e580819c12764059d72a37f90b438f7028309b",
  "d561c29e511e7eff59ec849235cb4722710bfe131a7cd5928e0a7ee7269667f2",
  "91ae9e77b4312d52e8a948ee914efb221d48e3ddf1f1b7a797118ba82be97114",
  "38a1c53b8cb793055575c7e9dd87441ec5c3be7a12d99f7a846f711e0dc0aca4",
  "0202cd2fd635c62141a8c10028e859cde669b31128c2216f28fb288e09d9c49e",
  "04f5b56ff1b66235f8e54a80c41c0926a44b80b7e39c5d6b5eed73ca09e43fdd",
  "6111fefb2e6f2d731e2d119dd15b7e5ed2242e798edbb5cf8a8af645a915f15b",
  "f1cc98f2697b1d5afa6c7db31242e6925344249489e9def26cc722e46d77edc4",
  "a499fbc5226985611961c7d978cfc6d0daf322e66be7eafdf04593b7a1ae4ee9",
  "acd172cebb9b6f5fc08b49e64951991b5bc45088d90af590b6b7304d5271b381",
  "08049beb568e5e977beabfa860ac2d3862b2f2a50e8d5a2aee4c32a99144cc89"
]

-- `sha256Hex` reduces only with the same depth and heartbeat budget as
-- `Residua.SHA256.sha256Hex_abc`. `native_decide` is not used.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000000 in
theorem tcache_stmtq_pins :
    goals.map (stmtQ []) = pinnedStmtQ := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem tcache_stmtq_distinct :
    pinnedStmtQ.eraseDups.length = 20 := by
  decide

end Rcic.Assay.Tcache
