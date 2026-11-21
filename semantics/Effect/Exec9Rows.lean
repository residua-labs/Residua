import Effect.Monitor
import Effect.Fixtures
import Lib.Exec9Core

/-! E4 replay of socket observations through the repaired Exec9 source and
the EFFECT-ABI-0 monitor. The plan inputs are fixed by the fixture names;
the wire observations do not supply the next request or the result. -/
namespace Effect.ABI.E4.Exec9

open Format Wire
open Lib.Exec9 (StepReply ACT_SEND ACT_READ ACT_OK ACT_REFUSE)

private def hex (b : Bytes) : String :=
  String.mk ((lowerHex b).map (Char.ofNat ∘ UInt8.toNat))

private def ints (b : Bytes) : List Int := b.map (Int.ofNat ∘ UInt8.toNat)

private def bytes (b : List Int) : Bytes := b.map (UInt8.ofNat ∘ Int.toNat)

private def fromHex : List Char → Option Bytes
  | [] => some []
  | a :: b :: rest => do
    return UInt8.ofNat (16 * (← digit a) + (← digit b)) :: (← fromHex rest)
  | [_] => none
where
  digit c :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else none

private def fs : Registration :=
  { contract := ⟨1, "exec9-e4-fs",
      [⟨[], true, [.walk, .read, .write, .create, .clunk], {limit := 8168}, {limit := 8168}⟩],
      0, [], Format.q .str abiId, Format.q .str "exec9-e4-local-ramfs-r1"⟩
    config := ⟨1, Format.q .str "exec9-e4-isolated-memfs-r1", [[ascii "work"]]⟩ }

private def ns : Namespace := ⟨1, [⟨ascii "fs", fs.contract.q, fs.config.q⟩]⟩
private def registry : Registry := [fs]
private def profile : Profile := ⟨1, 8192, 32, 8168, 400⟩

private def blobQ (b : Bytes) : Bytes :=
  Format.hashCanonical (ascii ("blob " ++ toString b.length) ++ [0] ++ b)

private structure Input where
  sel : I64
  nsQ : Bytes
  a1 : Bytes := []
  a2 : Bytes := []
  a3 : Bytes := []

private def selector (n : I64) : Int := Format.signed n

private def cold (i : Input) (st reply : List Int) : StepReply :=
  Effect.Exec9Entry.cold (selector i.sel) (ints i.nsQ) (ints i.a1) (ints i.a2) (ints i.a3) st reply

private def header (i : Input) (st : List Int) : Option StepReply :=
  let next := cold i st []
  if next.act == ACT_READ && next.out == [4] then some next else none

private def exchange (i : Input) (st : List Int) (r : Bytes) : Option StepReply := do
  let first ← header i st
  let body := cold i first.st (0 :: ints (r.take 4))
  let tail := ints (r.drop 4)
  if r.length < 7 || body.act != ACT_READ || body.out != [Int.ofNat tail.length] then none
  else some (cold i body.st (0 :: tail))

private def programType : Schema := .pair .bytes .i64
private def inputType : Schema := .pair .bytes (.pair .bytes (.pair .bytes .bytes))
private def stateType : Schema := .list .i64
private def resultType : Schema := .pair .i64 .bytes

private def model (sourceQ : Bytes) : Core where
  modelQ := sourceQ
  invocationCodecQ := Format.q .str "residua.effect.exec9-cold-7.r1"
  programType := programType
  inputType := inputType
  stateType := stateType
  resultType := resultType
  validates := fun (moduleQ, sel) _ i =>
    let n := selector sel
    moduleQ.length == 32 && 1 ≤ n && n ≤ 6 && i.fuel == 1
  invoke := fun (_, sel) (nsQ, a1, a2, a3) _ k =>
    let i : Input := ⟨sel, nsQ, a1, a2, a3⟩
    let step := match k with
      | none => some (cold i [] [])
      | some (st, r) => exchange i (st.map signed) r
    match step with
    | none => .done ((3 : I64), ascii "framing")
    | some step =>
      if step.act == ACT_SEND then
        match step.st.mapM checkedI64 with
        | some st => .send st (bytes step.out)
        | none => .done ((3 : I64), ascii "state-width")
      else .done ((checkedI64 step.act).getD 3, bytes step.out)

private def context (sourceQ moduleQ : Bytes) (i : Input) : Context (model sourceQ) :=
  let program : programType.Value := (moduleQ, i.sel)
  let m : Manifest := ⟨1, Format.q programType program, (model sourceQ).invocationCodecQ, 1, 8192⟩
  let plan : Plan (model sourceQ) := ⟨program, (i.nsQ, i.a1, i.a2, i.a3), m,
    ⟨[], [], [], m.q, Format.q .bytes [], 1⟩⟩
  ⟨abiId, ns.q, profile.q, plan.q, some ns, profile, some plan⟩

private structure Row where
  name : String
  input : Input
  requests : Nat
  replies : Nat

private def rows : List Row :=
  let read leaf parent := (⟨1, ns.q, ascii leaf, ascii parent, []⟩ : Input)
  let wrong := UInt8.ofNat ((ns.q.headD 0).toNat + 1) :: ns.q.drop 1
  let blob := blobQ (ascii "identity")
  [⟨"fs-read", read "known" "fs/work", 7, 7⟩,
   ⟨"fs-write", ⟨2, ns.q, ascii "created", [0, 66, 255], ascii "fs/work"⟩, 11, 11⟩,
   ⟨"missing", read "absent" "fs/work", 3, 3⟩,
   ⟨"confinement", read "protected" "fs/other", 3, 3⟩,
   ⟨"wrong-namespace", { read "known" "fs/work" with nsQ := wrong }, 2, 2⟩,
   ⟨"no-digest", { read "known" "fs/work" with nsQ := [] }, 0, 0⟩,
   ⟨"cmd-fid", ⟨4, ns.q, ascii "fixture-input", [], []⟩, 11, 11⟩,
   ⟨"substitution", ⟨6, ns.q, blob, [], []⟩, 7, 7⟩,
   ⟨"wrong-tag", read "known" "fs/work", 1, 1⟩,
   ⟨"pending-timeout", read "known" "fs/work", 1, 0⟩,
   ⟨"oversize", read "known" "fs/work", 1, 0⟩,
   ⟨"short-frame", read "known" "fs/work", 1, 0⟩]

private abbrev Fields := List (String × String × String)

private def parse (text : String) : Except String Fields := do
  let lines := text.splitOn "\n"
  unless lines.getLast? == some "" do throw "capture lacks final newline"
  let mut fields : Fields := []
  for line in lines.dropLast do
    let [row, key, value] := line.splitOn "\t" | throw "capture columns"
    unless rows.any (fun r => r.name == row) || row == "pin" || row == "tool" do
      throw s!"unexpected capture row {row}"
    unless !(fields.any fun (r, k, _) => r == row && k == key) do throw "duplicate capture key"
    fields := (row, key, value) :: fields
  return fields.reverse

private def field (fields : Fields) (row key : String) : Except String String :=
  match fields.find? (fun (r, k, _) => r == row && k == key) with
  | some (_, _, value) => pure value
  | none => throw s!"missing capture field {row}/{key}"

private def binary (fields : Fields) (row key : String) : Except String Bytes := do
  let value ← field fields row key
  let some b := fromHex value.toList | throw s!"bad hex {row}/{key}"
  return b

private structure Capture where
  t : List Bytes
  r : List Bytes
  act : I64
  out : Bytes
  fragment : Bytes
  closed : String

private def Capture.pairs (c : Capture) : List RawPair :=
  (c.t.zip c.r).map fun (t, r) => ⟨t, r⟩

private def load (fields : Fields) (row : Row) : Except String Capture := do
  let name := row.name
  let tKeys := (List.range row.requests).map fun n => s!"T{n+1}"
  let rKeys := (List.range row.replies).map fun n => s!"R{n+1}"
  let keys := tKeys ++ rKeys ++ ["act", "out", "partial", "closed"] ++
    (if name == "fs-read" then ["before"] else if name == "fs-write" then ["after"]
    else if name == "confinement" then ["protected-before", "protected-after"]
    else if name == "substitution" then ["requested-blob", "served-blob", "requested-q", "served-q"]
    else if name == "pending-timeout" then ["pending"] else [])
  let found := (fields.filter fun (r, _, _) => r == name).map fun (_, k, _) => k
  unless keys.length == found.length && keys.all found.contains do throw s!"capture keys {name}"
  let action ← field fields name "act"
  unless action == "1" || action == "2" do throw s!"bad terminal action {name}"
  let act : I64 := if action == "1" then 1 else 2
  return ⟨← tKeys.mapM (binary fields name), ← rKeys.mapM (binary fields name), act,
    ← binary fields name "out", ← binary fields name "partial", ← field fields name "closed"⟩

private def checkTerminal (c : Capture) (step : StepReply) : Bool :=
  checkedI64 step.act == some c.act && bytes step.out == c.out &&
    step.out.all (fun b => 0 ≤ b && b < 256)

private def sameResult (a b : I64 × Bytes) : Bool := a == b

private def checkSource (row : Row) (c : Capture) : Except String Unit := do
  let mut step := cold row.input [] []
  for (t, r) in c.t.zip c.r do
    unless step.act == ACT_SEND && bytes step.out == t do throw s!"source T {row.name}"
    let some next := exchange row.input step.st r | throw s!"source complete frame {row.name}"
    step := next
  match c.t.drop c.r.length with
  | [] => unless c.fragment.isEmpty do throw "unexpected partial reply"
  | [t] =>
    unless step.act == ACT_SEND && bytes step.out == t do throw s!"source pending T {row.name}"
    let some first := header row.input step.st | throw "source pending header ask"
    step := cold row.input first.st
      ((if row.name == "pending-timeout" then 4 else if row.name == "short-frame" then 1 else 0) :: ints c.fragment)
  | _ => throw "extra pending frames"
  unless checkTerminal c step do throw s!"source terminal {row.name}"

private def verifyClose (sourceQ : Bytes) (ctx : Context (model sourceQ)) (c : Capture)
    (obs : FaultObservation) : Except String Unit := do
  let [t] := c.t | throw "one pending request required"
  let sent := (State.opening ctx).afterSend t
  let out := (Monitor.fault registry ctx sent obs).val
  unless out.residue == some obs.cause && out.state == sent do throw "fault state"
  match out.disposition with
  | .close ev =>
    unless ev.prev == ctx.openingQ && ev.pending == some t && ev.cause == obs.cause &&
        ev.observed == .fault obs do throw "fault close observation"
  | _ => throw "fault did not close"
  match (Monitor.replayFault registry ctx [] t obs).val with
  | .inr replay => unless replay.residue == out.residue && replay.state == sent do throw "fault replay"
  | _ => throw "fault did not replay"
  if obs.cause == .f1 then
    let cp : Checkpoint := ⟨sent.contextQ, sent.prev, sent.q, sent⟩
    let some ⟨.waiting _ next, _⟩ := Monitor.resumeCheckpoint registry ctx [] cp | throw "pending checkpoint"
    let claim : I64 × Bytes := (2, c.out)
    let sealed := (Monitor.sealReceipt registry Fixtures.emptyStore ctx sent
      ⟨[], claim, sent.prev, resultsQ (core := model sourceQ) claim⟩).val
    unless next == t && sealed.residue == some .s1 do throw "pending checkpoint or Seal"

private def selectedNamespace (row : Row) (c : Capture) : Except String Unit := do
  if row.requests ≥ 2 then
    let some ⟨0, .attach 0 afid uname aname⟩ := decodeT (c.t[1]!) | throw "attach bytes"
    unless afid == noFid && uname.isEmpty && aname == lowerHex row.input.nsQ do
      throw "attach namespace"

private def operation (frame : Bytes) : Except String Wire.Request :=
  match decodeT frame with
  | some f => pure f.body
  | none => throw "undecodable T"

private def aliasFree (c : Capture) : Except String Unit := do
  let ops ← c.t.mapM operation
  for op in ops do
    match op with
    | .version .. => pure ()
    | .attach fid afid .. => unless fid == 0 && afid == noFid do throw "attach fid"
    | .walk src dst _ => unless src == 0 && dst == 1 do throw "walk fid"
    | .openFile fid _ | .create fid .. | .read fid .. | .write fid .. | .clunk fid =>
      unless fid == 1 do throw "work fid"
    | _ => throw "unobserved operation"

private def anchor (anchors : String) (name : String) : Except String (Bytes × Bytes × Bytes × Bytes) := do
  let candidates := (anchors.splitOn "\n").filter fun line => (line.splitOn "\t").head? == some name
  let [line] := candidates | throw "anchor count"
  let [_, cq, opening, root, result] := line.splitOn "\t" | throw "anchor columns"
  let some values := [cq, opening, root, result].mapM (fun h => fromHex h.toList) | throw "anchor hex"
  let [cq, opening, root, result] := values | throw "anchor arity"
  unless values.all (fun v => v.length == 32) do throw "anchor q width"
  return (cq, opening, root, result)

private def localRefusal (sourceQ : Bytes) (ctx : Context (model sourceQ)) (c : Capture)
    (pairs : List RawPair) (index : Nat) (cause : Residue) : Except String Unit := do
  let .point before (.send _ next) := (Monitor.replay registry ctx (pairs.take index)).val |
    throw "pre-Send replay"
  unless next == c.t[index]! do throw "pre-Send bytes"
  let refused := (Monitor.send registry ctx before next).val
  unless refused.state == before && refused.residue == some cause do throw "pre-Send cutoff"
  match refused.disposition with
  | .noIO => pure ()
  | _ => throw "refused Send issued"

private def verify (fields : Fields) (anchors : String) (sourceQ moduleQ : Bytes) (row : Row) :
    Except String String := do
  let name := row.name
  let c ← load fields row
  unless c.closed == "1" do throw "host socket did not close"
  checkSource row c
  selectedNamespace row c
  aliasFree c
  let ctx := context sourceQ moduleQ row.input
  let pairs := c.pairs
  let (cq, opening, root, result) ← anchor anchors name
  let outcome : I64 × Bytes := (c.act, c.out)
  let candidate := pairs.foldl (fun prev p => Format.pair prev p.t p.r) ctx.openingQ
  unless cq == ctx.q && opening == ctx.openingQ && root == candidate &&
      result == resultsQ (core := model sourceQ) outcome do throw "independent anchor mismatch"
  let replay := (Monitor.replay registry ctx pairs).val
  let receipt := (Monitor.sealReceipt registry Fixtures.emptyStore ctx (State.opening ctx)
    ⟨pairs.map RawPair.inline, outcome, root, result⟩).val
  let mut disposition := ""
  if name == "fs-read" || name == "fs-write" then
    let fieldName := if name == "fs-read" then "before" else "after"
    let expected : Bytes := if name == "fs-read" then [65] else [0, 66, 255]
    unless c.act == 1 && (← binary fields name fieldName) == expected && c.out == expected do
      throw "independent filesystem observation"
    let .point s (.done got) := replay | throw "successful replay did not finish"
    unless sameResult got outcome && s.pending.isNone && s.prev == root do throw "replay result"
    let .seal output := receipt.disposition | throw "receipt did not seal"
    unless sameResult output outcome && receipt.residue.isNone do throw "sealed result"
    disposition := "sealed"
  else if name == "missing" then
    let .point s (.done got) := replay | throw "failed walk replay did not finish"
    let some r := decodeR c.r[2]! | throw "failed walk response"
    unless sameResult got outcome && c.act == 2 && (match r.body with
      | .walk [_ , _] => c.out == ascii "walk_incomplete"
      | .error b => b == c.out
      | _ => false) && (s.fid 1).isNone && s.prev == root do throw "failed walk bound work fid"
    disposition := "failed-walk"
  else if name == "confinement" || name == "wrong-namespace" || name == "cmd-fid" || name == "substitution" then
    let cause := if name == "wrong-namespace" then Residue.t11 else .t14
    let index := if name == "wrong-namespace" then 1 else 2
    if name == "confinement" then
      unless (← binary fields name "protected-before") == [83] &&
          (← binary fields name "protected-after") == [83] && c.act == 2 do throw "protected bytes"
    if name == "wrong-namespace" then
      unless c.act == 2 && (decodeR c.r[1]!).any (fun r => r.body == .error c.out) do
        throw "namespace server selection"
    if name == "cmd-fid" then
      let ops ← c.t.mapM operation
      unless c.act == 1 && c.out == ascii "fixture-output" &&
          (ops.drop 5).take 3 == [.clunk 1, .walk 0 1 [ascii "out"], .openFile 1 0] do
        throw "CMD work fid reuse"
    if name == "substitution" then
      let expected ← binary fields name "requested-blob"
      let observed ← binary fields name "served-blob"
      let wanted ← binary fields name "requested-q"
      let served ← binary fields name "served-q"
      unless wanted == row.input.a1 && wanted == blobQ expected && served == blobQ observed &&
          wanted != served && c.act == 2 && c.out == ascii "hash_mismatch" &&
          (decodeR c.r[4]!).any (fun r => r.body == .read observed) do throw "content substitution"
    localRefusal sourceQ ctx c pairs index cause
    let .refused first := replay | throw "forbidden exchange replayed"
    unless first == cause && receipt.residue == some cause do throw "forbidden exchange residue"
    disposition := cause.label
  else if name == "no-digest" then
    unless c.act == 2 && c.out == ascii "q_invalid" && c.t.isEmpty && c.r.isEmpty do
      throw "unbound digest issued I/O"
    disposition := "q_invalid"
  else if name == "wrong-tag" then
    let sent := (State.opening ctx).afterSend c.t[0]!
    let out := (Monitor.receive registry ctx sent c.r[0]!).val
    let .refused first := replay | throw "wrong tag replay"
    let .close ev := out.disposition | throw "wrong tag close"
    unless first == .r4 && out.residue == some .r4 && out.state == sent && ev.prev == opening &&
        ev.pending == some c.t[0]! && ev.observed == .reply c.r[0]! do throw "wrong tag residue"
    disposition := first.label
  else
    let obs ← if name == "pending-timeout" then do
        unless (← binary fields name "pending") == c.t[0]! && c.fragment.isEmpty && c.out == ascii "timeout" do
          throw "timeout observation"
        pure (FaultObservation.timeout c.out)
      else if name == "oversize" then do
        unless c.fragment == [8, 32, 0, 0] && c.out == ascii "msize_exceeded" do throw "oversize observation"
        pure (.oversize c.fragment)
      else do
        unless name == "short-frame" && c.fragment == [19, 0] && c.out == ascii "truncated_frame" do
          throw "EOF observation"
        pure (.transport c.fragment)
    verifyClose sourceQ ctx c obs
    disposition := obs.cause.label
  return String.intercalate "\t" [name, toString c.t.length, toString c.r.length,
    toString c.act, disposition, hex root, hex result]

private def control (name : String) (p : Bool) : Except String String :=
  if p then pure s!"{name}\t1" else throw s!"accepted mutation {name}"

private def controls (fields : Fields) (anchors : String) (sourceQ moduleQ : Bytes) :
    Except String (List String) := do
  let row :: _ := rows | throw "no control row"
  let c ← load fields row
  let ctx := context sourceQ moduleQ row.input
  let .point versioned (.send _ attach) := (Monitor.replay registry ctx (c.pairs.take 1)).val |
    throw "versioned control prefix"
  let .point attached (.send _ _) := (Monitor.replay registry ctx (c.pairs.take 2)).val |
    throw "attached control prefix"
  let noIO := fun (s : State) (t : Bytes) (expected : Residue) =>
    let out := (Monitor.send registry ctx s t).val
    out.state == s && out.residue == some expected && (match out.disposition with | .noIO => true | _ => false)
  let fresh := cold row.input [] []
  let changed := cold {row.input with nsQ := List.replicate 32 0} fresh.st []
  let short := cold {row.input with nsQ := row.input.nsQ.take 31} [] []
  let nonbyte := Effect.Exec9Entry.cold 1 (256 :: (ints row.input.nsQ).drop 1) [] [] [] [] []
  let refuses := fun (s : StepReply) => s.act == ACT_REFUSE && s.st.isEmpty && bytes s.out == ascii "q_invalid"
  let (_, _, root, result) ← anchor anchors row.name
  let sealed := fun q r (observed : I64 × Bytes) => (Monitor.sealReceipt registry Fixtures.emptyStore ctx (State.opening ctx)
    ⟨c.pairs.map RawPair.inline, observed, q, r⟩).val.residue
  let swap := fun key v => fields.map fun (r, k, value) =>
    (r, k, if r == row.name && k == key then v else value)
  let refusesObservation := fun key v expected =>
    match verify (swap key v) anchors sourceQ moduleQ row with
    | .ok _ => false
    | .error e => e == expected
  let badAttachment := Fixtures.request (.attach 0 noFid (ascii "user") (lowerHex ns.q))
  let upper := (lowerHex ns.q).map fun b => if 97 ≤ b && b ≤ 102 then b - 32 else b
  [← control "bound-attach" ((Monitor.send registry ctx versioned attach).val.residue.isNone),
   ← control "legacy-uname" (noIO versioned badAttachment .t11),
   ← control "empty-aname" (noIO versioned (Fixtures.request (.attach 0 noFid [] [])) .t11),
   ← control "upper-aname" (noIO versioned (Fixtures.request (.attach 0 noFid [] upper)) .t11),
   ← control "fid-two" (noIO attached (Fixtures.request (.walk 0 2 [ascii "fs", ascii "work"])) .t4),
   ← control "changed-digest" (refuses changed),
   ← control "short-digest" (refuses short),
   ← control "nonbyte-digest" (refuses nonbyte),
   ← control "physical-readback" (refusesObservation "before" "42" "independent filesystem observation"),
   ← control "changed-wire" (refusesObservation "T3" "070000006e0000" "source T fs-read"),
   ← control "changed-root" (sealed (Format.q .bytes []) result (c.act, c.out) == some .s5),
   ← control "changed-results-q" (sealed root (Format.q .bytes []) (c.act, c.out) == some .s6),
   ← control "changed-results-value" (sealed root result (c.act, [66]) == some .s6)] |> pure

def run (args : List String) : IO UInt32 := do
  if args == ["namespace"] then
    IO.println (hex ns.q)
    return 0
  let [verb, capture, anchors] := args | throw (IO.userError "Exec9Rows namespace | MODE CAPTURE ANCHORS")
  let text ← IO.FS.readFile capture
  let anchorText ← if verb == "metadata" then pure "" else IO.FS.readFile anchors
  let result : Except String (List String) := do
    let fields ← parse text
    let sourceQ ← binary fields "pin" "source-bundle"
    let moduleQ ← binary fields "pin" "native"
    unless sourceQ.length == 32 && moduleQ.length == 32 do throw "artifact pin width"
    if verb == "metadata" then
      return rows.map fun row =>
        let ctx := context sourceQ moduleQ row.input
        String.intercalate "\t" [row.name, hex ctx.nsQ, hex ctx.profileQ, hex ctx.planQ]
    unless (anchorText.splitOn "\n").length == rows.length + 1 do throw "anchor denominator"
    if verb == "controls" then controls fields anchorText sourceQ moduleQ
    else if verb == "verify" then rows.mapM (verify fields anchorText sourceQ moduleQ)
    else throw "unknown mode"
  match result with
  | .ok lines => for line in lines do IO.println line
  | .error problem => throw (IO.userError problem)
  return 0

end Effect.ABI.E4.Exec9

def main (args : List String) : IO UInt32 := Effect.ABI.E4.Exec9.run args
