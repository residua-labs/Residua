import Effect.Format
import Effect.Wire

namespace Effect.ABI

open Format

abbrev Path := List Bytes

def walkName (name : Bytes) : Bool :=
  !name.isEmpty && Wire.validText name && !name.contains 47 && name != ascii "."

def newName (name : Bytes) : Bool := walkName name && name != ascii ".."

def traverse (path : Path) (name : Bytes) : Path :=
  if name == ascii ".." then path.dropLast else path ++ [name]

def pathPrefixes (path : Path) (names : List Bytes) : List Path :=
  match names with
  | [] => []
  | name :: rest =>
    let next := traverse path name
    next :: pathPrefixes next rest

private def before : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && before xs ys)

inductive Access where
  | walk | read | write | create | clunk | remove | stat | wstat | trunc | rclose
  deriving DecidableEq, Repr

def Access.code : Access → I64
  | .walk => 0 | .read => 1 | .write => 2 | .create => 3 | .clunk => 4
  | .remove => 5 | .stat => 6 | .wstat => 7 | .trunc => 8 | .rclose => 9

inductive Grammar where
  | raw
  | exact (records : List Bytes)
  | u64Line
  deriving DecidableEq, Repr

def Grammar.schema : Schema := .sum2 .bytes (.sum2 (.list .bytes) .bytes)

def Grammar.value : Grammar → Grammar.schema.Value
  | .raw => .inl []
  | .exact records => .inr (.inl records)
  | .u64Line => .inr (.inr [])

private def canonicalDecimal (bytes : Bytes) : Option Nat := do
  let first ← bytes.head?
  if (first == 48 && bytes.length != 1) || !bytes.all (fun b => 48 ≤ b && b ≤ 57) then
    none
  else
    let n := bytes.foldl (fun n b => n * 10 + (b.toNat - 48)) 0
    if n < 2^64 then some n else none

def Grammar.accepts : Grammar → Bytes → Bool
  | .raw, _ => true
  | .exact records, bytes => records.contains bytes
  | .u64Line, bytes => bytes.getLast? == some 10 && (canonicalDecimal bytes.dropLast).isSome

structure Transfer where
  limit : I64
  atomic : Bool := false
  recordLimit : I64 := 0
  eof : Bool := true
  grammar : Grammar := .raw
  deriving DecidableEq, Repr

def Transfer.schema : Schema := record
  [("limit", .i64), ("atomic", .bool), ("record_limit", .i64), ("eof", .bool),
    ("grammar", Grammar.schema)]

def Transfer.value (tr : Transfer) : Transfer.schema.Value :=
  (tr.limit, tr.atomic, tr.recordLimit, tr.eof, tr.grammar.value, ())

def Transfer.valid (tr : Transfer) : Bool :=
  tr.limit.toNat < 2^32 && tr.recordLimit.toNat ≤ tr.limit.toNat &&
    let bound := if tr.atomic then tr.recordLimit.toNat else tr.limit.toNat
    match tr.grammar with
    | .raw => true
    | .exact records => !records.isEmpty && records.all (fun r => r.length ≤ bound)
    | .u64Line => 21 ≤ bound

structure Rule where
  path : Path
  descendants : Bool
  access : List Access
  read : Transfer
  write : Transfer
  deriving DecidableEq, Repr

def Rule.schema : Schema := record
  [("prefix", .list .bytes), ("descendants", .bool), ("access", .list .i64),
    ("read", Transfer.schema), ("write", Transfer.schema)]

def Rule.value (rule : Rule) : Rule.schema.Value :=
  (rule.path, rule.descendants, rule.access.map Access.code, rule.read.value, rule.write.value, ())

def Rule.matches (rule : Rule) (path : Path) : Bool :=
  rule.path == path || (rule.descendants && rule.path.isPrefixOf path)

structure Transition where
  source : I64
  op : Access
  path : Path
  target : I64
  d1 : Bool
  deriving DecidableEq, Repr

def Transition.schema : Schema := record
  [("source", .i64), ("op", .i64), ("prefix", .list .bytes), ("target", .i64), ("d1", .bool)]

def Transition.value (edge : Transition) : Transition.schema.Value :=
  (edge.source, edge.op.code, edge.path, edge.target, edge.d1, ())

structure Contract where
  revision : I64
  item : String
  rules : List Rule
  initial : I64
  successful : List Transition
  effectQ : Bytes
  corpusQ : Bytes
  deriving DecidableEq, Repr

def Contract.schema : Schema := record
  [("revision", .i64), ("item", .str), ("rules", .list Rule.schema), ("initial", .i64),
    ("successful", .list Transition.schema), ("effect_q", .bytes), ("corpus_q", .bytes)]

def Contract.q (c : Contract) : Bytes := Format.q Contract.schema
  (c.revision, c.item, c.rules.map Rule.value, c.initial, c.successful.map Transition.value,
    c.effectQ, c.corpusQ, ())

def Contract.ruleFor (c : Contract) (path : Path) : Option Rule :=
  c.rules.foldl (fun best rule =>
    if rule.matches path && (best.all (fun found : Rule => found.path.length < rule.path.length))
      then some rule else best) none

def Contract.step (c : Contract) (state : I64) (op : Access) (path : Path) : Option I64 :=
  (c.successful.find? fun e => e.source == state && e.op == op && e.path.isPrefixOf path).map
    Transition.target

def Contract.valid (c : Contract) : Bool :=
  c.revision == 1 && !c.item.isEmpty && c.effectQ.length == 32 && c.corpusQ.length == 32 &&
    !c.rules.isEmpty && (c.rules.map Rule.path).eraseDups.length == c.rules.length &&
    c.rules.all (fun r => r.path.all newName && r.read.valid && r.write.valid) &&
    c.successful.all (fun e => e.path.all newName)

structure Config where
  revision : I64
  authorityQ : Bytes
  paths : List Path
  deriving DecidableEq, Repr

def Config.schema : Schema := record
  [("revision", .i64), ("authority_q", .bytes), ("paths", .list (.list .bytes))]

def Config.q (c : Config) : Bytes := Format.q Config.schema
  (c.revision, c.authorityQ, c.paths, ())

def Config.valid (c : Config) : Bool :=
  c.revision == 1 && c.authorityQ.length == 32 && !c.paths.isEmpty &&
    c.paths.all (fun path => path.all newName) && c.paths.eraseDups.length == c.paths.length

def Config.authorizes (c : Config) (path : Path) : Bool :=
  c.paths.any fun anchor => anchor.isPrefixOf path

def Config.traversalAncestor (c : Config) (path : Path) : Bool :=
  c.paths.any fun anchor => path.length < anchor.length && path.isPrefixOf anchor

structure Mount where
  name : Bytes
  contractQ : Bytes
  configQ : Bytes
  deriving DecidableEq, Repr

def Mount.schema : Schema := record
  [("name", .bytes), ("contract_q", .bytes), ("config_q", .bytes)]

def Mount.value (m : Mount) : Mount.schema.Value := (m.name, m.contractQ, m.configQ, ())

structure Namespace where
  revision : I64
  mounts : List Mount
  deriving DecidableEq, Repr

def Namespace.schema : Schema := record [("revision", .i64), ("mounts", .list Mount.schema)]

def Namespace.q (ns : Namespace) : Bytes := Format.q Namespace.schema
  (ns.revision, ns.mounts.map Mount.value, ())

/-- The verifier supplies registrations indexed by the exact typed object q's.
Physical authority remains with the registered actuator. -/
structure Registration where
  contract : Contract
  config : Config

abbrev Registry := List Registration

def Registry.resolve (registry : Registry) (mount : Mount) : Option Registration :=
  registry.find? fun entry =>
    entry.contract.q == mount.contractQ && entry.config.q == mount.configQ

def Namespace.valid (ns : Namespace) (registry : Registry) : Bool :=
  ns.revision == 1 && sorted (ns.mounts.map Mount.name) &&
    ns.mounts.all (fun m => newName m.name && m.contractQ.length == 32 && m.configQ.length == 32 &&
      (Registry.resolve registry m).any (fun entry => entry.contract.valid && entry.config.valid))
where
  sorted : List Bytes → Bool
    | [] | [_] => true
    | x :: (ys@(y :: _)) => before x y && sorted ys

inductive PathAuthority where
  | virtualRoot
  | traversal (rule : Rule)
  | target (rule : Rule)

def PathAuthority.policy : PathAuthority → Option Rule
  | .target rule => some rule
  | _ => none

def Namespace.authority (ns : Namespace) (registry : Registry) : Path → Option PathAuthority
  | [] => some .virtualRoot
  | name :: tail => do
    let mount ← ns.mounts.find? fun m => m.name == name
    let resolved ← Registry.resolve registry mount
    let rule ← resolved.contract.ruleFor tail
    if resolved.config.authorizes tail then some (.target rule)
    else if resolved.config.traversalAncestor tail then some (.traversal rule)
    else none

end Effect.ABI
