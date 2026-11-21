import Effect.ConformanceBounds

namespace Effect.ABI.E3

open Wire Fixtures Conformance

private def filePath : Path := fsPath ++ [ascii "file"]

private def bindWork (fid : Fid) (s : State) : State := { s with work := some fid }

private def releaseWork (s : State) : State := { s with work := none }

private def pair (t : Wire.Request) (r : Wire.Reply) : RawPair := ⟨request t, reply r⟩

def statRootPair : RawPair := pair (.stat 0) (.stat (statOf rootQid []))

def clunkRootPair : RawPair := ⟨clunkRoot, clunkReply⟩

private def error : Wire.Reply := .error (ascii "fixture-error")

private def transaction (name : String) (pairs : List RawPair) (p : RawPair)
    (change : State → State := id) : CaseResult :=
  check "transition" name (commit pairs p.t p.r change)

private def directoryCases : List CaseResult :=
  let opened := (Fid.unopened fsPath dirQid).openAs dirQid 0 0
  let openDir := pair (.openFile 1 0) (.openFile dirQid 0)
  let live := walked ++ [openDir]
  let entry := (Build.stat (statOf fileQid)).getD []
  let readDir := pair (.read 1 0 128) (.read entry)
  let advanced := live ++ [readDir]
  let next := pair (.read 1 entry.length 128) (.read entry)
  let eof := pair (.read 1 entry.length 128) (.read [])
  let offset := fun n => bindWork { opened with dirOffset := littleEndianBytes 8 n }
  [transaction "open-directory" walked openDir (bindWork opened),
   transaction "directory-first-entry" live readDir (offset entry.length),
   transaction "directory-follow-offset" advanced next (offset (2 * entry.length)),
   transaction "directory-eof" advanced eof (offset entry.length),
   transaction "directory-rewind" (advanced ++ [next]) readDir (offset entry.length),
   check "transition" "directory-wrong-offset"
     (send advanced (request (.read 1 (entry.length + 1) 128)) (.refuse .t8)),
   check "transition" "directory-incomplete-stat"
     (receive live readDir.t (reply (.read entry.dropLast)) (.refuse .r8)),
   check "transition" "directory-write-mode"
     (send walked (request (.openFile 1 1)) (.refuse .t8))]

def transitionCases : List CaseResult :=
  let created := pair (.create 1 (ascii "new") 0x1ff 2) (.create fileQid 32)
  let newer : Wire.Qid := { fileQid with version := 2 }
  let opened := (Fid.unopened filePath fileQid).openAs newer 2 32
  let openWork := pair (.openFile 1 2) (.openFile newer 32)
  let renamed := pair (.wstat 1 { noStatChange with name := ascii "new" }) .wstat
  let newPath := fsPath ++ [ascii "new"]
  let clone := pair (.walk 0 1 []) (.walk [])
  let clamp := pair (.walk 0 1 [ascii ".."]) (.walk [rootQid])
  let partialWalk := pair (.walk 0 1 fsPath) (.walk [fsQid])
  let partialInPlace := pair (.walk 1 1 [ascii "..", ascii "root"]) (.walk [fsQid])
  let clunk := pair (.clunk 1) .clunk
  let read := pair (.read 1 0 1) (.read [0x41])
  let write := pair (.write 1 0 [0x41, 0x42]) (.write 1)
  let live := unopenedFile ++ [openWork]
  let stat := pair (.stat 1) (.stat (statOf newer))
  [transaction "version" [] versionPair (atVersion 256),
   transaction "attach" [versionPair] attachPair atAttach,
   transaction "attach-error" [versionPair] { attachPair with r := reply error },
   transaction "walk" prefixPairs walkPair (bindWork (Fid.unopened fsPath dirQid)),
   transaction "walk-clone" prefixPairs clone (bindWork (Fid.unopened [] rootQid)),
   transaction "walk-clamp-root" prefixPairs clamp (bindWork (Fid.unopened [] rootQid)),
   transaction "walk-in-place" walked filePair (bindWork (Fid.unopened filePath fileQid)),
   transaction "walk-partial" prefixPairs partialWalk,
   transaction "walk-partial-in-place" walked partialInPlace,
   transaction "walk-reuse-after-partial" (prefixPairs ++ [partialWalk]) walkPair
     (bindWork (Fid.unopened fsPath dirQid)),
   transaction "walk-error" prefixPairs { walkPair with r := reply error },
   transaction "open" unopenedFile openWork (bindWork opened),
   transaction "open-error" unopenedFile { openWork with r := reply error },
   transaction "create" walked created (bindWork ((Fid.unopened newPath fileQid).openAs fileQid 2 32)),
   transaction "create-error" walked { created with r := reply error },
   transaction "read" live read,
   transaction "read-error" live { read with r := reply error },
   transaction "write-short" live write,
   transaction "write-error" live { write with r := reply error },
   transaction "stat" unopenedFile stat (bindWork (Fid.unopened filePath newer)),
   transaction "stat-error" unopenedFile { stat with r := reply error },
   transaction "wstat" unopenedFile renamed (bindWork (Fid.unopened newPath fileQid)),
   transaction "wstat-length" unopenedFile (pair (.wstat 1 { noStatChange with length := 7 }) .wstat),
   transaction "wstat-error" unopenedFile { renamed with r := reply error },
   transaction "clunk-work" live clunk releaseWork,
   transaction "clunk-work-error" live { clunk with r := reply error } releaseWork,
   transaction "clunk-root" (live ++ [clunk]) clunkRootPair afterRootClunk,
   transaction "clunk-root-error" prefixPairs { clunkRootPair with r := reply error } afterRootClunk,
   transaction "remove" unopenedFile (pair (.remove 1) .remove) releaseWork,
   transaction "remove-error" unopenedFile (pair (.remove 1) error) releaseWork,
   check "transition" "fid-2" (send prefixPairs (request (.stat 2)) (.refuse .t4)),
   check "transition" "fid-root-last" (send live clunkRoot (.refuse .t4)),
   check "transition" "after-ended" (send (prefixPairs ++ [clunkRootPair]) statRoot (.refuse .t4)),
   check "transition" "already-open" (send live openWork.t (.refuse .t8)),
   check "transition" "walk-on-open" (send live (request (.walk 1 1 [])) (.refuse .t8)),
   check "transition" "in-flight" {
     context := context (prefixPairs.map RawPair.t ++ [statRoot])
     point := .waiting prefixPairs statRoot
     event := .send statRoot
     expected := .refuse .t5 }] ++
    directoryCases

private def failed (tests : List Test) (cause : Residue) : Bool :=
  tests.any (fun test => test.cause == cause && test.fails)

private def applicable (probe : Probe) (a b : Residue) (s : State) : Bool :=
  let list := match probe.event with
    | .openSession => contextTests registry probe.context s true
    | .send raw => sendTests registry probe.context s raw
    | .receive raw => receiveTests registry probe.context s raw
    | _ => []
  failed list a && failed list b

private def overlap (name : String) (probe : Probe) (a b : Residue) : CaseResult :=
  check "precedence" name { probe with
    expected := .refuse a
    premise := fun s => probe.premise s && applicable probe a b s }

def priorityCases : List CaseResult :=
  let ns := { fixtureNS with mounts := fixtureNS.mounts ++ fixtureNS.mounts }
  let c := context [] profile ns
  let small := { profile with maxSteps := 2 }
  let large := request (.write 1 0 (List.replicate 234 0x41))
  let over := request (.write 1 0 (List.replicate 129 0x41))
  let invalidStat := request (.wstat 1 { noStatChange with mode := 1, name := ascii "d/e" })
  let badWalk := request (.walk 0 1 [ascii "fs/root"])
  let badQids := reply (.walk [fileQid, fsQid, dirQid])
  [overlap "C1/C2" (openAt { c with nsQ := [] }) .c1 .c2,
   overlap "C5/C6" { openAt (context []) (.ready []) with
     varyState := fun s => { s with contextQ := [] } } .c5 .c6,
   overlap "T2/T4" (sendOK [] (request (.flush 0))) .t2 .t4,
   overlap "T3/T9" (sendOK (readable 0) large) .t3 .t9,
   overlap "T4/T5" (sendOK [] (request (.attach 0 noFid [] (Format.lowerHex fixtureNS.q)) 1)) .t4 .t5,
   overlap "T5/T6" (sendOK prefixPairs (request (.stat 1) 1)) .t5 .t6,
   overlap "T8/T9" (sendOK unopenedFile over) .t8 .t9,
   overlap "T9/T10" (sendOK prefixPairs (namedWalk 17) small) .t9 .t10,
   overlap "T12/T13" (sendOK walked invalidStat) .t12 .t13,
   overlap "T13/T14" (sendOK prefixPairs badWalk) .t13 .t14,
   overlap "R2/R4" (commit prefixPairs statRoot (reply (.error (List.replicate 248 0x65)) 1)) .r2 .r4,
   overlap "R4/R5" (commit prefixPairs statRoot (reply .clunk 1)) .r4 .r5,
   overlap "R6/R7" (commit [] versionPair.t (reply (.version 255 (ascii "unknown")) noTag)) .r6 .r7,
   overlap "R8/R9" (commit prefixPairs walkPair.t badQids) .r8 .r9,
   overlap "R8/R10" (commit commandReady echoWrite (reply (.write 6))) .r8 .r10]

end Effect.ABI.E3
