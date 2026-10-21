/-
RCIC 06 §13–§14 — the typed first-order wire of configurations, final
outcomes and run results: the codec of `apps/rcic-scm-config` (#6029 K3b,
segment 3), `rcic.scm_cfg_obj_dec` / `rcic.scm_cfg_obj_enc` and the tagged
items under them.

Owner text: 06 §13 "The first-order wire configuration stores closed tags and
payloads. Its decoder reconstructs a raw configuration and validates the
frame-chain typing before producing the typed semantic configuration."
06 §14 `SCMFinal T := returned (CoreVal T) | raised r (CoreVal (PayloadType
r))`, `SCMRunResult T := done (SCMFinal T) | suspended SCMConfig`.
00 §19.7 E-06Wire: the same grammar family as the §17 core wire, closed
control and frame tags following `apps/rcic-scm-core`'s kinds.

Kinds 22 configuration, 23 final outcome and 24 run result are registered in
`docs/rcic/SEMANTIC_OBJECT_KIND_REGISTRY.md`. The encoding is the carrier's
recorded choice: a control or a frame is a tag
followed by items in the core wire's element grammar (`ScmWire.decSeq`); a
frame's first two items are its input and output types, an environment is a
context of types and a list of values. A configuration is `C`, its result
type, the control's bytes, and the list of frame bytes; a final outcome is
`F`, its type, a tag and its payload; a run result is `D`, a tag, and its
member's bytes. The typing of these objects is `ScmConfigAt`.
-/
import rcic.ScmWire

namespace Rcic.Scm.CfgWire
open Rcic.Scm Rcic.Scm.Wire

deriving instance BEq for CatalogEntry
deriving instance BEq for ExtSig
deriving instance BEq for RawFnDef
deriving instance BEq for RawProg
deriving instance BEq for Item

/-- A control (`what` 0), a frame (1) or a final payload (2): a tag and its
    items. -/
structure Tagged where
  tag : Int
  xs : List Item
  deriving BEq

structure CfgO where
  t : CoreTy
  ctl : Tagged
  k : List Tagged
  deriving BEq

structure FinO where
  t : CoreTy
  tag : Int
  xs : List Item
  deriving BEq

/-- A decoded configuration, final outcome or run result (whose member is a
    final outcome for tag 0 and a configuration for tag 1). -/
inductive CX where
  | cfg (c : CfgO)
  | fin (f : FinO)
  | run (tag : Int) (m : CX)
  deriving BEq

/-! ## Item schemas (`rcic.scm_cfg_kinds`) -/

/-- Element kinds as in `decSeq`: 0 type, 1 value, 2 expression, 4 string,
    5 natural number, `10 + k` a list of kind `k`. -/
def frameKinds : List (List Nat) :=
  [[0, 0, 10, 11, 2], [0, 0, 10, 11, 2, 2], [0, 0, 10, 11, 2], [0, 0, 1], [0, 0], [0, 0], [0, 0, 5],
   [0, 0, 10, 11, 12], [0, 0, 10, 11, 11, 12], [0, 0, 5], [0, 0, 10, 11, 2], [0, 0, 1], [0, 0, 10, 11, 2, 2],
   [0, 0, 0, 10, 11, 11, 2], [0, 0, 10, 11, 2, 2, 2], [0, 0, 10, 11, 1, 2, 2], [0, 0, 10, 11, 1, 5, 5, 2, 2],
   [0, 0, 10, 11, 5, 5, 2, 2], [0, 0, 10, 11, 5, 4, 5, 11, 12], [0, 0], [0, 0, 4, 10, 11, 2], [0, 0, 4]]
def ctlKinds : List (List Nat) := [[10, 11, 2], [0, 1], [0, 4, 1]]
def finKinds : List (List Nat) := [[1], [4, 1]]

def kindsOf (what tag : Int) : Option (List Nat) :=
  let rows := if what = 0 then ctlKinds else if what = 2 then finKinds else frameKinds
  if tag < 0 then none else rows.get? tag.toNat

/-! ## Encoder (`rcic.scm_cfg_enc_items`, `_enc_tagged`, `_obj_enc`) -/

def encBase (k : Nat) (x : Item) : String :=
  match k with
  | 0 => encTy (asTy x)
  | 1 => encVal (asVal x)
  | 2 => encExpr (asExpr x)
  | 4 => encStr (asStr x)
  | 5 => encNat (asNum x)
  | _ => ""

def encItem (k : Nat) (x : Item) : String :=
  if k ≥ 10 then encNat (asList x).length ++ String.join ((asList x).map (encBase (k - 10)))
  else encBase k x

def encItems : List Nat → List Item → String
  | [], _ => ""
  | k :: ks, xs => encItem k (xs.headD default) ++ encItems ks (xs.drop 1)

def encTagged (what : Int) (g : Tagged) : String :=
  encNat g.tag ++ encItems ((kindsOf what g.tag).getD []) g.xs

def encCfg (c : CfgO) : String :=
  "C" ++ encTy c.t ++ encStr (encTagged 0 c.ctl) ++ encNat c.k.length ++
    String.join (c.k.map (fun f => encStr (encTagged 1 f)))

def encFin (f : FinO) : String := "F" ++ encTy f.t ++ encTagged 2 ⟨f.tag, f.xs⟩

def cxEnc : CX → String
  | .cfg c => encCfg c
  | .fin f => encFin f
  | .run tag m =>
    "D" ++ encNat tag ++ encStr (match m with
      | .cfg c => encCfg c
      | .fin f => encFin f
      | .run _ _ => "")

/-! ## Decoder (`rcic.scm_cfg_dec_tagged`, `_obj_dec`) -/

/-- A tag at `p`, then the items of its schema. -/
def decTagged (cs : Array Char) (g : Nat) (what fuel : Int) (p : Nat) : Except String (Tagged × Nat) := do
  let (t, q) ← decNat cs p
  match kindsOf what t with
  | none => .error "[rcic_scm_cf_tag]"
  | some ks =>
    let (xs, q') ← decSeq cs g fuel q ks
    pure (⟨t, xs⟩, q')

/-- An embedded tagged string, decoded from its start. -/
def decTaggedStr (what fuel : Int) (s : String) : Except String Tagged :=
  let cs := s.toList.toArray
  (decTagged cs (gasFor fuel cs.size) what fuel 0).map Prod.fst

def decCfg (fuel : Int) (s : String) : Except String (CfgO × Nat) :=
  let cs := s.toList.toArray
  match charAt cs 0 with
  | none => wErr "truncated"
  | some c =>
    if c ≠ 'C' then wErr "tag" else do
      let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 [0, 4, 14]
      let ctl ← decTaggedStr 0 fuel (asStr ((xs.drop 1).headD default))
      let frames ← ((asList ((xs.drop 2).headD default)).map asStr).mapM (decTaggedStr 1 fuel)
      pure (⟨asTy (xs.headD default), ctl, frames⟩, q)

def decFin (fuel : Int) (s : String) : Except String (FinO × Nat) :=
  let cs := s.toList.toArray
  match charAt cs 0 with
  | none => wErr "truncated"
  | some c =>
    if c ≠ 'F' then wErr "tag" else do
      let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 [0]
      let (g, q') ← decTagged cs (gasFor fuel cs.size) 2 fuel q
      pure (⟨asTy (xs.headD default), g.tag, g.xs⟩, q')

/-- `rcic.scm_cfg_obj_dec kind s fuel`: kind 22 configuration, 23 final
    outcome, otherwise run result. -/
def cxDec (kind : Int) (s : String) (fuel : Int) : Except String (CX × Nat) :=
  let cs := s.toList.toArray
  match charAt cs 0 with
  | none => wErr "truncated"
  | some c =>
    if kind = 22 then (decCfg fuel s).map (fun (x, q) => (.cfg x, q))
    else if kind = 23 then (decFin fuel s).map (fun (x, q) => (.fin x, q))
    else if c ≠ 'D' then wErr "tag" else do
      let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 [5, 4]
      let tag := asNum (xs.headD default)
      if tag < 2 then
        let mb := asStr ((xs.drop 1).headD default)
        if tag = 0 then
          let (f, _) ← decFin (fuel - 1) mb
          pure (.run tag (.fin f), q)
        else
          let (cf, _) ← decCfg (fuel - 1) mb
          pure (.run tag (.cfg cf), q)
      else .error "[rcic_scm_cf_tag]"

end Rcic.Scm.CfgWire
