import Effect.ConformanceSeeds

/-! Ports of the legacy host fixture premises to full E1 wire observations.
The fixtures below supply replies as data and use no actuator. -/
namespace Effect.ABI.E4

open Wire Fixtures Conformance

private def resultCore : Core :=
  { modelQ := Format.q .str "residua.effect.host-fixture.observed-results.r1"
    invocationCodecQ := Format.q .str "residua.effect.host-fixture.bytes-results.r1"
    programType := .pair (.list .bytes) .bytes
    inputType := .record .nil
    stateType := .pair (.list .bytes) .bytes
    resultType := .bytes
    validates := fun _ _ invocation => invocation.fuel == 1
    invoke := fun program _ _ continuation =>
      let (rest, prior) := (continuation.map Prod.fst).getD program
      let data := (continuation.bind (decodeR ∘ Prod.snd)).map Wire.Frame.body
      let acc : Bytes := match data with | some (.read bytes) => (show Bytes from prior) ++ bytes | _ => prior
      match rest with
      | [] => .done acc
      | t :: ts => .send (ts, acc) t }

private def resultContext (pairs : List RawPair) (initial : Bytes := []) : Context resultCore :=
  let program : resultCore.programType.Value := (pairs.map RawPair.t, initial)
  let m : Manifest := ⟨1, Format.q resultCore.programType program, resultCore.invocationCodecQ, 1, 8192⟩
  let plan : Plan resultCore := ⟨program, (), m, ⟨[], [], [], m.q, Format.q .bytes [], 1⟩⟩
  ⟨abiId, fixtureNS.q, profile.q, plan.q, some fixtureNS, profile, some plan⟩

private def chain {core : Core} (c : Context core) (pairs : List RawPair) : Bytes :=
  pairs.foldl (fun prev pair => Format.pair prev pair.t pair.r) c.openingQ

private def awaiting {core : Core} (c : Context core) (seen : List RawPair)
    (check : State → core.stateType.Value → Bytes → Bool) : Bool :=
  match (Monitor.replay registry c seen).val with
  | .point s (.send k raw) =>
    s.prev == chain c seen && s.pending.isNone && s.sentSteps.toNat == seen.length && check s k raw
  | _ => false

private def atDone {core : Core} (c : Context core) (seen : List RawPair)
    (expected : core.resultType.Value) (check : State → Bool := fun _ => true) : Bool :=
  match (Monitor.replay registry c seen).val with
  | .point s (.done got) =>
    Format.canonical core.resultType got == Format.canonical core.resultType expected && s.pending.isNone &&
      s.prev == chain c seen && s.sentSteps.toNat == seen.length && check s
  | _ => false

private def refutes {core : Core} (c : Context core) (pairs : List RawPair) (cause : Residue) : Bool :=
  match (Monitor.replay registry c pairs).val with
  | .refused got => got == cause
  | _ => false

private def checkSeal {core : Core} (c : Context core) (pairs : List RawPair)
    (root : Bytes) (result : core.resultType.Value) : Outcome core :=
  (Monitor.sealReceipt registry emptyStore c (State.opening c)
    ⟨pairs.map RawPair.inline, result, root, resultsQ (core := core) result⟩).val

private def sealIs {core : Core} (c : Context core) (pairs : List RawPair)
    (root : Bytes) (result : core.resultType.Value) (cause : Option Residue := none) : Bool :=
  let out := checkSeal c pairs root result
  out.state == State.opening c && out.residue == cause &&
    match out.disposition, cause with
    | .seal got, none => Format.canonical core.resultType got == Format.canonical core.resultType result
    | .noIO, some _ => true
    | _, _ => false

private def clunk : RawPair := ⟨request (.clunk 0), reply .clunk⟩
private def stat : RawPair := ⟨request (.stat 0), reply (.stat (statOf rootQid []))⟩
private def statError : RawPair := { stat with r := reply (.error (ascii "missing info")) }
private def attachError : RawPair := { attachPair with r := reply (.error (ascii "refused")) }

private def history : List RawPair := prefixPairs ++ [stat, clunk]
private def altHistory : List RawPair := prefixPairs ++ [statError, clunk]
private def badHistory : List RawPair := [versionPair, attachError, stat, clunk]
private def historyContext := resultContext history [0]

private def withoutValidation (plan : Plan resultCore) :
    Step resultCore.stateType resultCore.resultType → List RawPair → Option Bytes
  | .done result, [] => some result
  | .send k t, pair :: rest =>
    if t == pair.t then withoutValidation plan (plan.invoke (some (k, pair.r))) rest else none
  | _, _ => none

private def capCase : Probe :=
  let usage : Profile := { profile with maxSteps := 8 }
  let tape := versionPair :: List.replicate 7 attachError
  { send tape attachPair.t (.refuse .t10) usage with
    premise := fun s => s.sentSteps == 8 && s.pending.isNone && s.isPhase .versioned }

private def openFile (name : Bytes) (mode : Nat := 0) : List RawPair :=
  prefixPairs ++ [walkPair,
    ⟨request (.walk 1 1 [name]), reply (.walk [fileQid])⟩, openPair mode]

private def readFrame (data : Bytes) : RawPair :=
  ⟨request (.read 1 0 3), reply (.read data)⟩

private def echo : List RawPair :=
  openFile (ascii "1") ++ [[1, 2, 3], [4, 5, 6], [7]].map readFrame

private def echoContext := resultContext echo

private def replayDropped : Bool :=
  let dropped := echo.take 5 ++ echo.drop 6
  awaiting echoContext dropped (fun _ (_, acc) next =>
    (show Bytes from acc) == [4, 5, 6, 7] && next == (readFrame []).t) &&
    sealIs echoContext dropped (chain echoContext dropped) [4, 5, 6, 7] (some .s4)

private def changedPath : List RawPair :=
  openFile (ascii "2") ++ echo.drop 5

private def compareIgnoringWalkNames (expected got : RawPair) : Bool :=
  expected.r == got.r &&
    match decodeT expected.t, decodeT got.t with
    | some ⟨a, .walk fid newFid _⟩, some ⟨b, .walk otherFid otherNewFid _⟩ =>
      a == b && fid == otherFid && newFid == otherNewFid
    | _, _ => expected.t == got.t

private def replayTampered : Bool :=
  echo != changedPath && (echo.zip changedPath).all (fun (expected, got) =>
    compareIgnoringWalkNames expected got) && refutes echoContext changedPath .s4

private def checkpoint : Option Checkpoint := do
  let .point s (.send ..) := (Monitor.replay registry historyContext prefixPairs).val | none
  return ⟨s.contextQ, s.prev, s.q, s⟩

private def resume (cp : Checkpoint) : Option (State × Bytes) := do
  let ⟨.ready step, _⟩ ← Monitor.resumeCheckpoint registry historyContext prefixPairs cp | none
  let plan ← historyContext.plan
  let .point endState (.done result) :=
    (Monitor.replayFrom registry historyContext plan cp.state step (history.drop 2)).val | none
  return (endState, result)

private def checkpointMatches : Bool :=
  checkpoint.any fun cp =>
    (resume cp).any fun (state, result) =>
      (match (Monitor.replay registry historyContext history).val with
      | .point straight (.done expected) => straight == state && (show Bytes from expected) == result
      | _ => false) && cp.state.sentSteps == 2 && state.sentSteps == 4 &&
        result == [0] && state.prev == chain historyContext history

private def wrongCheckpoint : Bool :=
  checkpoint.any fun cp =>
    match cp.prev with
    | first :: rest =>
      let changed := (first ^^^ 1) :: rest
      changed != cp.prev && (resume cp).isSome &&
        (Monitor.resumeCheckpoint registry historyContext prefixPairs { cp with prev := changed }).isNone
    | [] => false

private def overCap : Probe :=
  let version := versionPair 8192 8192
  let obs := FaultObservation.oversize (littleEndianBytes 4 8193)
  { context := context [version.t, attachPair.t] { profile with offer := 8192 }
    point := .waiting [version] attachPair.t
    event := .fault obs
    expected := .refuse .f3
    premise := fun s => s.msize == 8192 && s.root.isNone && s.sentSteps == 2 }

private def content : Bytes := [9, 8, 7]
private def contentQ := Format.hashCanonical content
private def contentQHex := "06df4f7e1394f1c57cc6583fba4d8060a5a66f4f4771c14aeff6b9af8a28c9b3"
private def contentTrace := openFile (Format.lowerHex contentQ) ++ [readFrame content]

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

private def alteredContent : Bool :=
  hex contentQ == contentQHex && Format.hashCanonical [8, 8, 7] != contentQ

private structure Row where
  id : String
  kind : String
  input : List Bytes
  pass : Bool

private def synthetic (id : String) (input : List Bytes) (pass : Bool) : Row :=
  ⟨id, "synthetic", input, pass⟩

private def zero (id : String) (input : List Bytes) (pass : Bool) : Row :=
  ⟨id, "zero", input, pass⟩

private def historyInput := historyContext.q :: pairBytes history
private def echoInput := echoContext.q :: pairBytes echo

private def fixtureRows : List Row :=
  let c := historyContext
  let pinned := chain c history
  let alternative := chain c altHistory
  let complete := atDone c history [0] (fun s => s.isPhase .ended && s.root.isNone)
  let unchecked := c.plan.any fun plan =>
    withoutValidation plan (plan.invoke none) badHistory == some [0] &&
      sealIs c badHistory (chain c badHistory) [0] (some .t4)
  let prefixOne := awaiting c prefixPairs (fun s _ t => s.root.isSome && t == stat.t)
  let prefixDead := awaiting c (badHistory.take 2) (fun s _ t =>
    s.isPhase .versioned && s.root.isNone && t == stat.t)
  let prefixTwo := awaiting c history.dropLast (fun s _ t => s.root.isSome && t == clunk.t)
  let echoComplete := atDone echoContext echo [1, 2, 3, 4, 5, 6, 7] &&
    awaiting echoContext echo.dropLast (fun _ (_, acc) _ => (show Bytes from acc) == [1, 2, 3, 4, 5, 6]) &&
    sealIs echoContext echo (chain echoContext echo) [1, 2, 3, 4, 5, 6, 7]
  let roots := historyInput ++ pairBytes altHistory ++ [pinned, alternative]
  let cap := capCase.run
  let oversize := overCap.run
  let otherUsage := { profile with offer := 4096 }
  let opening := exactContext history
  let otherOpening := exactContext history otherUsage
  let noPrev := fun (rows : List RawPair) => rows.foldl (fun _ p => Format.pair [] p.t p.r) []
  let noC0 := history.foldl (fun prev p => Format.pair prev p.t p.r) []
  [synthetic "ex_refused_cap" [cap.witnessQ] cap.valid,
   synthetic "ex_attach_ok_next" historyInput prefixOne,
   synthetic "ex_attach_err_next" (c.q :: pairBytes badHistory) (prefixDead && refutes c badHistory .t4),
   synthetic "ex_stat_live_next" historyInput prefixTwo,
   synthetic "ex_clunk_value" historyInput complete,
   synthetic "b3_read_q" (contentQ :: (resultContext contentTrace).q :: pairBytes contentTrace)
     (hex contentQ == contentQHex && atDone (resultContext contentTrace) contentTrace content),
   zero "b3_rewrite_fails_q" [content, [8, 8, 7], contentQ] alteredContent,
   synthetic "b5_ok_history" historyInput (prefixOne && prefixTwo && complete),
   zero "b5_ok_receipt" (pinned :: historyInput) (sealIs c history pinned [0]),
   synthetic "b5_bad_record" (c.q :: pairBytes badHistory)
     (badHistory.length == 4 && unchecked),
   zero "b5_r9_accepts_bad" (c.q :: pairBytes badHistory) unchecked,
   synthetic "b5_oversize" [oversize.witnessQ] oversize.valid,
   synthetic "b5_run1" echoInput echoComplete,
   zero "b5_dropped" echoInput replayDropped,
   zero "b5_tampered" (echoInput ++ pairBytes changedPath) replayTampered,
   zero "b5_empty_awaiting" [c.q]
     (awaiting c [] (fun _ _ t => t == versionPair.t) && sealIs c [] c.openingQ [] (some .s4)),
   zero "b5_c_ok" (pinned :: historyInput) (sealIs c history pinned [0]),
   zero "b5_c_alt_under_ok" roots
     (pinned != alternative && sealIs c altHistory alternative [0] && sealIs c altHistory pinned [0] (some .s5)),
   zero "b5_c_forger" roots (pinned != alternative && sealIs c altHistory alternative [0]),
   zero "b5_c_bad_any_root" ([c.q, pinned, chain c badHistory] ++ pairBytes badHistory)
     (sealIs c badHistory pinned [0] (some .t4) &&
      sealIs c badHistory (chain c badHistory) [0] (some .t4)),
   synthetic "b6_split_equals" historyInput checkpointMatches,
   synthetic "b6_root_mismatch" historyInput wrongCheckpoint,
   synthetic "b6_reset_inplace" echoInput
     (echoComplete && awaiting echoContext [] (fun s (_, acc) next =>
      s.root.isNone && s.work.isNone && acc.isEmpty && next == versionPair.t) &&
       awaiting echoContext (echo.take 5) (fun s (_, acc) next =>
         s.isPhase .attached && s.work.isSome && acc.isEmpty && next == (readFrame []).t)),
   synthetic "out_value" historyInput complete,
   synthetic "out_refused" [cap.witnessQ] cap.valid,
   zero "mut_noprev" roots (pinned != alternative && noPrev history == noPrev altHistory),
   zero "mut_noc0" ([opening.q, otherOpening.q, noC0] ++ pairBytes history)
     (opening.openingQ != otherOpening.openingQ &&
       rootFor opening history != rootFor otherOpening history &&
       noC0 != rootFor opening history && noC0 != rootFor otherOpening history),
   zero "mut_replay_dropped" echoInput replayDropped,
   zero "mut_replay_tampered" (echoInput ++ pairBytes changedPath) replayTampered]

private def output (row : Row) : String :=
  let digest := Format.q (.list .bytes) ([ascii row.id, ascii row.kind] ++ row.input)
  String.intercalate "\t" ["fixture", row.id, row.kind, hex digest, if row.pass then "1" else "0"]

def rows : List String := fixtureRows.map output

def exec9Row (actions : String) : Option String := do
  let [first, second, third, fourth, parsed, ""] := actions.splitOn "\n" | none
  let ["attach", "0", "0", "4294967295", unameHex, ""] := parsed.splitOn "\t" | none
  let some uname := unhex unameHex.toList | none
  let version := versionPair 8192 8192
  let actualAttach := request (.attach 0 noFid uname [])
  let payload := fun bytes => "00" ++ hex bytes
  if first.splitOn "\t" != ["f155", "1", "0", hex version.t, ""] ||
      second.splitOn "\t" != ["f155", "2", "3", "04", ""] ||
      third.splitOn "\t" != ["f155", "3", "3", "0f", payload (version.r.take 4)] ||
      fourth.splitOn "\t" != ["f155", "4", "0", hex actualAttach, payload (version.r.drop 4)] then none else
    let usage := { profile with offer := 8192 }
    let refuses := send [version] actualAttach (.refuse .t11) usage
    let admits := send [version] attachPair.t (.issue attachPair.t) usage
    let bad := refuses.run
    let good := admits.run
    if bad.valid && good.valid then
      some (String.intercalate "\t" ["exec9-diagnostic", "attach", bad.got,
        hex bad.witnessQ, good.got, hex good.witnessQ, "1"])
    else none

end Effect.ABI.E4

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => Effect.ABI.E4.rows.forM IO.println
  | ["exec9", path] =>
    let input ← IO.FS.readFile path
    if let some row := Effect.ABI.E4.exec9Row input then IO.println row else
      IO.eprintln "compiled Exec9 attach diagnostic disagrees"
      return 1
  | _ =>
    IO.eprintln "usage: HostFixtureRows.lean [exec9 <actions.tsv>]"
    return 2
  return 0
