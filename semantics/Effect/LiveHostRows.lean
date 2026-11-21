import Effect.Monitor
import Effect.Fixtures

/-! Offline adjudication of exact shipped-Exec9 socket observations. The
literal request core checks E1 admission; it does not prove Exec9 refinement
(E5). FORMAT roots are compared with separately encoded Node SHA-256 anchors.
The mature actuator is ninep 0.6.0; the independent reader is plan9port 9p.
An invalid completed host run is a counterexample, never an admitted receipt. -/
namespace Effect.ABI.E4.Live

open Wire Fixtures

private structure Field where
  row : String
  key : String
  value : String

private def names := ["fs-read", "fs-write", "missing", "wrong-tag",
  "pending-timeout", "oversize", "short-frame", "confinement", "substitution"]

private def hex (bytes : Bytes) : String :=
  String.mk ((Format.lowerHex bytes).map (Char.ofNat ∘ UInt8.toNat))

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def unhex : List Char → Option Bytes
  | [] => some []
  | a :: b :: rest => do
    return UInt8.ofNat (16 * (← nibble a) + (← nibble b)) :: (← unhex rest)
  | [_] => none

private def parse (text : String) : Except String (List Field) := do
  let mut out := []
  let lines := text.splitOn "\n"
  unless lines.getLast? == some "" do throw "missing final newline"
  for line in lines.dropLast do
    let [row, key, value] := line.splitOn "\t" | throw "three columns required"
    unless names.contains row || row == "pin" || row == "tool" do throw "unknown row"
    if out.any (fun f => f.row == row && f.key == key) then throw "duplicate key"
    out := out ++ [⟨row, key, value⟩]
  return out

private def field (fields : List Field) (row key : String) : Except String String :=
  match fields.find? (fun f => f.row == row && f.key == key) with
  | some f => .ok f.value
  | none => .error s!"missing {row}/{key}"

private def bytes (fields : List Field) (row key : String) : Except String Bytes := do
  let value ← field fields row key
  let some value := unhex value.toList | throw s!"bad hex {row}/{key}"
  return value

private def counts (name : String) : Nat × Nat :=
  if name == "fs-read" || name == "substitution" then (7, 7) else if name == "fs-write" then (11, 11)
  else if name == "missing" || name == "confinement" then (3, 3) else if name == "wrong-tag" then (1, 1)
  else (1, 0)

private structure Capture where
  name : String
  ts : List Bytes
  rs : List Bytes
  terminal : Bytes
  fields : List Field

private def load (fields : List Field) (name : String) : Except String Capture := do
  let (nt, nr) := counts name
  let mut ts := []
  let mut rs := []
  for i in List.range nt do ts := ts ++ [← bytes fields name s!"T{i+1}"]
  for i in List.range nr do rs := rs ++ [← bytes fields name s!"R{i+1}"]
  let completed := name == "fs-read" || name == "fs-write"
  let terminal ← bytes fields name (if completed then "done" else "refused")
  let extras := if name == "fs-read" then ["before"] else if name == "fs-write" then ["after"]
    else if name == "confinement" then ["outside-before", "outside-after"]
    else if name == "substitution" then ["expected-q", "observed-q"]
    else if name == "pending-timeout" then ["pending"]
    else if name == "oversize" || name == "short-frame" then ["partial-R"] else []
  let keys := (List.range nt).map (fun i => s!"T{i+1}") ++
    (List.range nr).map (fun i => s!"R{i+1}") ++ ["events", if completed then "done" else "refused"] ++ extras
  unless (fields.filter (fun f => f.row == name)).length == keys.length &&
      (fields.filter (fun f => f.row == name)).all (fun f => keys.contains f.key) do
    throw s!"unexpected fields {name}"
  return ⟨name, ts, rs, terminal, fields⟩

private def usage : Profile := { profile with offer := 8192, timeout := 200 }
private def ctx (a : Capture) := context a.ts usage
private def pairs (a : Capture) : List RawPair := (a.ts.zip a.rs).map (fun (t, r) => ⟨t, r⟩)
private def chain (a : Capture) : Bytes :=
  (pairs a).foldl (fun prev p => Format.pair prev p.t p.r) (ctx a).openingQ

private def checkClose (a : Capture) (sent : State) (out : Outcome fixtureCore)
    (cause : Residue) (observed : CloseObservation) : Bool :=
  out.residue == some cause && out.state == sent &&
  match out.disposition with
  | .close evidence => evidence.prev == (ctx a).openingQ && evidence.pending == some a.ts[0]! &&
      evidence.cause == cause && evidence.observed == observed
  | _ => false

private def issuedFirst (a : Capture) : Except String State := do
  let c := ctx a
  let opening := State.opening c
  let out := (Monitor.send registry c opening a.ts[0]!).val
  unless out.residue.isNone && out.state == opening.afterSend a.ts[0]! do throw "version send"
  match out.disposition with
  | .issue t => unless t == a.ts[0]! do throw "issued bytes"
  | _ => throw "no version I/O"
  return out.state

private def checkAttach (a : Capture) : Except String Unit := do
  let c := ctx a
  let seen := (pairs a).take 1
  unless a.ts[0]! == (versionPair 8192 8192).t && a.rs[0]! == (versionPair 8192 8192).r do
    throw "version exchange changed"
  let .point s (.send _ next) := (Monitor.replay registry c seen).val | throw "version replay"
  unless next == a.ts[1]! && s.isPhase .versioned && s.sentSteps == 1 && s.pending.isNone do
    throw "attach prefix"
  let some ⟨0, .attach 0 afid uname aname⟩ := decodeT next | throw "attach decode"
  unless afid == noFid && !uname.isEmpty && aname.isEmpty do throw "attach premise"
  let out := (Monitor.send registry c s next).val
  unless out.residue == some .t11 && out.state == s do throw "T11/state"
  match out.disposition with | .noIO => pure () | _ => throw "T11 issued I/O"
  match (Monitor.replay registry c (pairs a)).val with
  | .refused .t11 => pure ()
  | _ => throw "whole replay did not refuse at T11"
  let neighbor := (Monitor.send registry c s attachPair.t).val
  unless neighbor.residue.isNone && neighbor.state.pending == some attachPair.t do throw "attach neighbor"
  let sealedAttempt := (Monitor.sealReceipt registry emptyStore c (State.opening c)
    ⟨(pairs a).map RawPair.inline, (42 : Format.I64), chain a,
      resultsQ (core := fixtureCore) (42 : Format.I64)⟩).val
  unless sealedAttempt.residue == some .t11 do throw "unadmitted host completion sealed"
  if a.name == "missing" || a.name == "confinement" then
    unless a.terminal == ascii "unknown file" &&
        (decodeR a.rs[2]!).any (fun r => r.body == .error a.terminal) do throw "missing-file observation"
    if a.name == "confinement" then
      unless (decodeT a.ts[2]!).any (fun t => t.body == .walk 0 1 [ascii "../outside"]) &&
          (← bytes a.fields a.name "outside-before") == [83] &&
          (← bytes a.fields a.name "outside-after") == [83] do throw "confinement observation"
  else if a.name == "substitution" then
    let wanted ← bytes a.fields a.name "expected-q"
    let got ← bytes a.fields a.name "observed-q"
    let fake := ascii "WRONG BYTES FROM FAKE SERVER\n"
    unless wanted == Format.hashCanonical (ascii "blob 1" ++ [0, 65]) &&
        got == Format.hashCanonical (ascii s!"blob {fake.length}" ++ [0] ++ fake) && got != wanted &&
        a.terminal == ascii "hash_mismatch" &&
        (decodeT a.ts[2]!).any (fun t => t.body == .walk 0 1 [ascii "q", Format.lowerHex wanted]) &&
        (decodeR a.rs[4]!).any (fun r => r.body == .read fake) &&
        (decodeR a.rs[5]!).any (fun r => r.body == .read []) do throw "substitution observation"
  else
    let expected : Bytes := if a.name == "fs-read" then [65] else [66]
    let index := if a.name == "fs-read" then 4 else 8
    let physical ← bytes a.fields a.name (if a.name == "fs-read" then "before" else "after")
    unless a.terminal == expected && physical == expected &&
        (decodeR a.rs[index]!).any (fun r => r.body == .read expected) &&
        (decodeR a.rs[index+1]!).any (fun r => r.body == .read []) do throw "independent data observation"
    if a.name == "fs-write" then
      unless (decodeT a.ts[4]!).any (fun t => t.body == .write 1 0 expected) &&
          (decodeR a.rs[4]!).any (fun r => r.body == .write 1) do throw "write/ack"
  unless (← field a.fields a.name "events") == "none" do throw "unexpected filesystem transport event"

private def checkOther (a : Capture) : Except String Residue := do
  unless a.ts == [(versionPair 8192 8192).t] do throw "fault request"
  let sent ← issuedFirst a
  if a.name == "wrong-tag" then
    unless a.terminal == ascii "tag_mismatch" && (← field a.fields a.name "events") == "none" do
      throw "tag host outcome"
    let some ⟨1, .version 8192 v⟩ := decodeR a.rs[0]! | throw "wrong-tag premise"
    unless v == version9P do throw "wrong-tag version"
    unless checkClose a sent (Monitor.receive registry (ctx a) sent a.rs[0]!).val .r4 (.reply a.rs[0]!) do
      throw "wrong-tag close disposition"
    return .r4
  let obs ← if a.name == "pending-timeout" then do
      unless (← bytes a.fields a.name "pending") == a.ts[0]! &&
          (← field a.fields a.name "events") == "timeout" && a.terminal == ascii "timeout" do
        throw "pending/timeout observation"
      unless sent.pending == some a.ts[0]! && sent.sentSteps == 1 && sent.prev == (ctx a).openingQ do
        throw "pending state"
      let cp : Checkpoint := ⟨sent.contextQ, sent.prev, sent.q, sent⟩
      let some ⟨.waiting _ t, _⟩ := Monitor.resumeCheckpoint registry (ctx a) [] cp | throw "pending checkpoint"
      unless t == a.ts[0]! do throw "pending checkpoint bytes"
      let sealedAttempt := (Monitor.sealReceipt registry emptyStore (ctx a) sent
        ⟨[], (42 : Format.I64), sent.prev, resultsQ (core := fixtureCore) (42 : Format.I64)⟩).val
      unless sealedAttempt.residue == some .s1 do throw "pending Seal"
      pure (FaultObservation.timeout a.terminal)
    else if a.name == "oversize" then do
      let fragment ← bytes a.fields a.name "partial-R"
      unless fragment.length ≥ 4 && littleEndian (fragment.take 4) == 8200 &&
          littleEndian (fragment.take 4) > usage.offer.toNat &&
          (← field a.fields a.name "events") == "none" && a.terminal == ascii "msize_exceeded" do
        throw "oversize actuator premise"
      pure (.oversize (fragment.take 4))
    else do
      let fragment ← bytes a.fields a.name "partial-R"
      unless a.name == "short-frame" && fragment == [19, 0] && fragment.length < 4 &&
          (← field a.fields a.name "events") == "end" && a.terminal == ascii "truncated_frame" do
        throw "short-frame EOF premise"
      pure (.transport fragment)
  let out := (Monitor.fault registry (ctx a) sent obs).val
  unless checkClose a sent out obs.cause (.fault obs) do throw "fault close disposition"
  match (Monitor.replayFault registry (ctx a) [] a.ts[0]! obs).val with
  | .inr replay => unless replay.residue == out.residue && replay.state == out.state do throw "fault replay"
  | _ => throw "fault replay refused before observation"
  return obs.cause

private def metadata (a : Capture) : String :=
  let c := ctx a
  String.intercalate "\t" [a.name, hex c.nsQ, hex c.profileQ, hex c.planQ]

private def anchor (text : String) (a : Capture) : Except String Unit := do
  let candidates := (text.splitOn "\n").filter (fun line => (line.splitOn "\t").head? == some a.name)
  let [line] := candidates | throw "anchor count"
  let [_, contextQ, opening, root, result] := line.splitOn "\t" | throw "anchor columns"
  unless contextQ == hex (ctx a).q && opening == hex (ctx a).openingQ && root == hex (chain a) &&
      result == hex (Format.q .bytes a.terminal) do throw s!"independent anchor {a.name}"

private def verify (text anchors : String) : Except String (List String) := do
  let fields ← parse text
  let mut rows := []
  unless (anchors.splitOn "\n").length == names.length + 1 do throw "extra anchor"
  for name in names do
    let a ← load fields name
    let cause ← if ["fs-read", "fs-write", "missing", "confinement", "substitution"].contains name then do
        checkAttach a
        pure Residue.t11
      else checkOther a
    anchor anchors a
    rows := rows ++ [String.intercalate "\t" ["live", name, toString a.ts.length, toString a.rs.length,
      if name == "fs-read" || name == "fs-write" then "host-done" else "host-refused",
      cause.label, hex (Format.q .str (String.intercalate "\n"
        ((fields.filter (fun f => f.row == name)).map (fun f => f.key ++ "\t" ++ f.value)))),
      hex (chain a), hex (Format.q .bytes a.terminal), "1"]]
  return rows

private def replace (text row key value : String) : String :=
  String.intercalate "\n" ((text.splitOn "\n").map fun line =>
    if line.startsWith (row ++ "\t" ++ key ++ "\t") then row ++ "\t" ++ key ++ "\t" ++ value else line)

def run (args : List String) : IO UInt32 := do
  let execute : Except String (List String) → IO UInt32 := fun result => do
    match result with
    | .ok rows => rows.forM IO.println; return 0
    | .error reason => IO.eprintln reason; return 1
  match args with
  | ["metadata", path] =>
    let text ← IO.FS.readFile path
    execute do
      let fields ← parse text
      names.mapM (fun name => return metadata (← load fields name))
  | ["verify", path, expected] => execute (verify (← IO.FS.readFile path) (← IO.FS.readFile expected))
  | ["controls", path, expected] =>
    let text ← IO.FS.readFile path
    let anchors ← IO.FS.readFile expected
    execute do
      let _ ← verify text anchors
      let mutations := [
        ("reply-tag", replace text "fs-read" "R1" "13000000650100002000000600395032303030"),
        ("attach-neighbor", replace text "fs-read" "T2" (hex attachPair.t)),
        ("terminal-data", replace text "fs-write" "done" "43"),
        ("physical-readback", replace text "fs-write" "after" "43"),
        ("outside-modified", replace text "confinement" "outside-after" "54"),
        ("substitution-q", replace text "substitution" "observed-q" "00"),
        ("pending-bytes", replace text "pending-timeout" "pending" "00"),
        ("oversize-below-cap", replace text "oversize" "partial-R" "002000006bffff010078"),
        ("missing-eof", replace text "short-frame" "events" "none"),
        ("malformed-hex", replace text "wrong-tag" "R1" "0"),
        ("duplicate", text ++ "fs-read\tdone\t41\n"),
        ("extra", text ++ "fs-read\tT8\t00\n")]
      let mut rows := []
      for (name, mutated) in mutations do
        unless mutated != text && (verify mutated anchors).toOption.isNone do throw s!"surviving mutant {name}"
        rows := rows ++ [s!"control\t{name}\t1"]
      for key in [2, 3, 4] do
        let lines := anchors.splitOn "\n"
        let first := (lines.head!).splitOn "\t"
        let changed := String.intercalate "\t" (first.zip (List.range first.length) |>.map fun (v, i) => if i == key then "00" else v)
        let mutated := String.intercalate "\n" (changed :: lines.tail!)
        unless mutated != anchors && (verify text mutated).toOption.isNone do throw "surviving anchor mutant"
        rows := rows ++ [s!"control\tanchor-{key}\t1"]
      return rows
  | _ => IO.eprintln "usage: LiveHostRows metadata capture | verify/controls capture anchors"; return 2

end Effect.ABI.E4.Live

def main := Effect.ABI.E4.Live.run
