import Effect.Conformance

/-! Plans for the isolated go9p differential. The expected replies specify
standard success/error, data and fid observations independently of replay. -/
namespace Effect.ABI.E3.Oracle

open Wire Fixtures Conformance

private inductive ReplyCheck where
  | exact (r : Wire.Reply)
  | attachRoot
  | walk (directories : List Bool)
  | openAt (previous : Nat)
  | created
  | statAt (previous : Nat) (name : Bytes) (length : Nat)
  | walkFileAt (previous : Nat)
  | error

private structure Command where
  t : Bytes
  expect : ReplyCheck

private structure Session where
  name : String
  commands : List Command

private def command (t : Wire.Request) (expect : ReplyCheck) : Command := ⟨request t, expect⟩

private def start : List Command :=
  [⟨versionPair.t, .exact (.version 256 version9P)⟩, ⟨attachPair.t, .attachRoot⟩]

private def cleanUp : List Command :=
  [command (.clunk 1) (.exact .clunk), command (.clunk 0) (.exact .clunk)]

private def sessions : List Session :=
  let file := ascii "file"
  let fresh := ascii "new"
  let data := ascii "BP"
  [⟨"file-read", start ++
     [command (.walk 0 1 (fsPath ++ [file])) (.walk [true, true, false]),
      command (.openFile 1 0) (.openAt 2),
      command (.read 1 0 1) (.exact (.read (ascii "A"))),
      command (.read 1 1 1) (.exact (.read [])),
      command (.stat 1) (.statAt 2 file 1)] ++ cleanUp⟩,
   ⟨"create-remove", start ++
     [command (.walk 0 1 fsPath) (.walk [true, true]),
      command (.create 1 fresh 0x1ff 2) .created,
      command (.write 1 0 data) (.exact (.write 2)),
      command (.read 1 0 2) (.exact (.read data)),
      command (.stat 1) (.statAt 3 fresh 2),
      command (.clunk 1) (.exact .clunk),
      command (.walk 0 1 (fsPath ++ [fresh])) (.walkFileAt 3),
      command (.remove 1) (.exact .remove),
      command (.walk 0 1 (fsPath ++ [fresh])) .error,
      command (.clunk 0) (.exact .clunk)]⟩]

private def hex (bytes : Bytes) : String :=
  String.mk ((Format.lowerHex bytes).map (Char.ofNat ∘ UInt8.toNat))

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def unhex : List Char → Option Bytes
  | [] => some []
  | hi :: lo :: rest => do
    return UInt8.ofNat (16 * (← nibble hi) + (← nibble lo)) :: (← unhex rest)
  | [_] => none

private def qids : Wire.Reply → List Wire.Qid
  | .attach q | .openFile q _ | .create q _ => [q]
  | .walk qs => qs
  | .stat st => [st.qid]
  | _ => []

private def sameObject (a b : Wire.Qid) : Bool := a.path == b.path && a.kind == b.kind

private def previousObject (history : List Wire.Reply) (index : Nat) (q : Wire.Qid) : Bool :=
  (history[index]?.bind (fun r => (qids r).getLast?)).any (sameObject q)

private def namedObjects (history : List Wire.Reply) (qs : List Wire.Qid) (expected : List Bool) : Bool :=
  let paths := qs.map Wire.Qid.path
  qs.map Wire.Qid.directory == expected && paths.eraseDups == paths &&
    (history[1]?.bind (fun r => (qids r).head?)).any (fun root => !paths.contains root.path)

private def checkReply (history : List Wire.Reply) (r : Wire.Reply) : ReplyCheck → Bool
  | .exact value => r == value
  | .attachRoot => match r with | .attach q => q.directory | _ => false
  | .walk dirs => match r with | .walk qs => namedObjects history qs dirs | _ => false
  | .openAt index => match r with
    | .openFile q iounit => previousObject history index q && iounit == 16384
    | _ => false
  | .created => match r with
    | .create q iounit => !q.directory && iounit == 16384 &&
        !(history.flatMap qids).any (fun old => old.path == q.path)
    | _ => false
  | .statAt index name length => match r with
    | .stat st => st.name == name && st.length == length && previousObject history index st.qid
    | _ => false
  | .walkFileAt index => match r with
    | .walk qs => namedObjects history qs [true, true, false] &&
        qs.getLast?.any (previousObject history index) &&
        (history[2]?.map qids).any (fun dirs =>
          (dirs.zip (qs.take 2)).all (fun (before, after) => sameObject before after))
    | _ => false
  | .error => match r with | .error _ => true | _ => false

private def collect (name : String) (lines : List String)
    (commands : List Command) (ordinal : Nat := 1) (history : List Wire.Reply := []) :
    Except String (List RawPair × List String) := do
  match commands, lines with
  | [], rest => return ([], rest)
  | cmd :: next, line :: rest =>
    let [session, index, t, r] := line.splitOn "\t" | throw s!"{name}/{ordinal} columns"
    unless session == name && index == toString ordinal && t == hex cmd.t do
      throw s!"{name}/{ordinal} request identity"
    let some raw := unhex r.toList | throw s!"{name}/{ordinal} reply hex"
    let some frame := decodeR raw | throw s!"{name}/{ordinal} reply framing"
    let expectedTag := if ordinal == 1 then noTag else 0
    unless frame.tag == expectedTag && checkReply history frame.body cmd.expect do
      throw s!"{name}/{ordinal} standard observation {repr frame.body}"
    let (pairs, after) ← collect name rest next (ordinal + 1) (history ++ [frame.body])
    return (⟨cmd.t, raw⟩ :: pairs, after)
  | _ :: _, [] => throw s!"{name}/{ordinal} transcript exhausted"

private def verify (lines : List String) : Except String (List String) := do
  let mut remaining := lines
  let mut rows := []
  for session in sessions do
    let (pairs, rest) ← collect session.name remaining session.commands
    remaining := rest
    let c := context (session.commands.map (·.t))
    let root := rootFor c pairs
    let some s := (match (Monitor.replay registry c pairs).val with
      | .point s (.done result) =>
        if resultsQ (core := fixtureCore) result == Format.q .i64 (42 : Format.I64) then some s else none
      | _ => none) | throw s!"{session.name} replay did not finish"
    unless s.isPhase .ended && s.msize == 256 && s.sentSteps.toNat == pairs.length &&
        s.root.isNone && s.work.isNone && s.pending.isNone && s.prev == root do
      throw s!"{session.name} terminal state"
    rows := rows ++ [String.intercalate "\t" ["oracle", session.name, toString pairs.length,
      hex c.q, hex root, hex (Format.q .i64 (42 : Format.I64)), "1"]]
  unless remaining.isEmpty do throw "extra oracle transaction"
  return rows

def run (args : List String) : IO UInt32 := do
  match args with
  | ["requests"] =>
    for session in sessions do
      let mut ordinal := 1
      for cmd in session.commands do
        IO.println (String.intercalate "\t" [session.name, toString ordinal, hex cmd.t])
        ordinal := ordinal + 1
    return 0
  | ["verify", path] =>
    let input ← IO.FS.readFile path
    let lines := input.splitOn "\n"
    let lines := if lines.getLast? == some "" then lines.dropLast else lines
    match verify lines with
    | .ok rows => for row in rows do IO.println row
    | .error reason =>
      IO.eprintln reason
      return 1
    return 0
  | _ =>
    IO.eprintln "usage: OracleRows.lean requests | verify <transcript.tsv>"
    return 2

end Effect.ABI.E3.Oracle

def main := Effect.ABI.E3.Oracle.run
