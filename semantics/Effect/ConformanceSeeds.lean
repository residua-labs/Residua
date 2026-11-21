import Effect.Conformance

namespace Effect.ABI.E3

open Wire Fixtures Conformance Format

structure Seed where
  id : String
  negative : Probe
  neighbor : Probe

def walked : List RawPair := prefixPairs ++ [walkPair]

def unopenedFile : List RawPair := walked ++ [filePair]

def readable (iounit : Nat := 0) : List RawPair := unopenedFile ++ [openPair 2 iounit]

def commandReady : List RawPair := prefixPairs ++ [cmdPair, openPair 1]

def readOne : Bytes := request (.read 1 0 1)

def readReply : Bytes := reply (.read [0x41])

def statRoot : Bytes := request (.stat 0)

def clunkRoot : Bytes := request (.clunk 0)

def clunkReply : Bytes := reply .clunk

def atVersion (size : Nat) (s : State) : State :=
  { s with phase := Phase.versioned.code, msize := UInt64.ofNat size }

def atAttach (s : State) : State :=
  { s with phase := Phase.attached.code, root := some (Fid.unopened [] rootQid) }

def afterRootClunk (s : State) : State := { s with phase := Phase.ended.code, root := none }

def openAt (c : Context fixtureCore) (point : Point := .pre)
    (expected : Expectation := .opened) : Probe :=
  { context := c, point, event := .openSession, expected }

def sendOK (pairs : List RawPair) (raw : Bytes) (usage : Profile := profile) : Probe :=
  send pairs raw (.issue raw) usage

def versionAt (p : Profile) : Bytes :=
  request (.version p.offer.toNat version9P) noTag

def negotiated (p : Profile) (n : Nat) : Probe :=
  commit [] (versionAt p) (reply (.version n version9P) noTag) (atVersion n) p

def namedWalk (n : Nat) : Bytes :=
  request (.walk 0 1 (fsPath ++ List.replicate (n - fsPath.length) (ascii "..")))

def errorFrame (n : Nat) : Bytes := reply (.error (List.replicate (n - 9) 0x65))

def commandWrite (data : Bytes) (offset : Nat := 0) : Bytes := request (.write 1 offset data)

def echoWrite : Bytes := commandWrite execLine

private def contextSeeds : List Seed :=
  let c := context []
  let pre := openAt c
  let twoMounts := { fixtureNS with mounts := fixtureNS.mounts ++ fixtureNS.mounts }
  [⟨"C1", openAt { c with nsQ := c.nsQ.dropLast } .pre (.refuse .c1), pre⟩,
   ⟨"C2", openAt (context [] profile twoMounts) .pre (.refuse .c2), pre⟩,
   ⟨"C3", openAt (context [] { profile with offer := 255 }) .pre (.refuse .c3),
     openAt (context [] { profile with maxSteps := 0 })⟩,
   ⟨"C4", openAt { c with plan := none } .pre (.refuse .c4), pre⟩,
   ⟨"C5", { openAt c (.ready []) (.refuse .c5) with
     varyState := fun s => { s with contextQ := List.replicate 32 0 } }, pre⟩,
   ⟨"C6", openAt c (.ready []) (.refuse .c6), pre⟩]

private def sendSeeds : List Seed :=
  let auth := request (.auth 0 [] [])
  let large := commandWrite (List.replicate 234 0x41)
  let bounded := commandWrite (List.replicate 128 0x41)
  let changedN := request (.attach 0 noFid [] (List.replicate 64 0x30))
  let wstat := request (.wstat 1 noStatChange)
  let badWstat := request (.wstat 1 { noStatChange with mode := 511 })
  let max := { profile with maxSteps := 2 }
  [⟨"T1", send (readable 0) readOne.dropLast (.refuse .t1), sendOK (readable 0) readOne⟩,
   ⟨"T2", send [] auth (.refuse .t2), sendOK [] versionPair.t⟩,
   ⟨"T3", { send (readable 0) large (.refuse .t3) with
       premise := fun s => (decodeT large).isSome && large.length == s.msize.toNat + 1 },
     sendOK (readable 0) bounded⟩,
   ⟨"T4", send [] attachPair.t (.refuse .t4), sendOK [versionPair] attachPair.t⟩,
   ⟨"T5", send prefixPairs (request (.stat 0) 1) (.refuse .t5), sendOK prefixPairs statRoot⟩,
   ⟨"T6", send prefixPairs (request (.stat 1)) (.refuse .t6),
     sendOK walked (request (.stat 1))⟩,
   ⟨"T7", send walked walkPair.t (.refuse .t7), sendOK walked filePair.t⟩,
   ⟨"T8", send unopenedFile readOne (.refuse .t8), sendOK (readable 0) readOne⟩,
   ⟨"T9", { send prefixPairs (namedWalk 17) (.refuse .t9) with
       premise := fun _ => match decodeT (namedWalk 17) with
         | some ⟨_, .walk _ _ names⟩ => names.length == 17
         | _ => false }, sendOK prefixPairs (namedWalk 16)⟩,
   ⟨"T10", send prefixPairs statRoot (.refuse .t10) max,
     sendOK prefixPairs statRoot { max with maxSteps := 3 }⟩,
   ⟨"T11", send [versionPair] changedN (.refuse .t11), sendOK [versionPair] attachPair.t⟩,
   ⟨"T12", send walked badWstat (.refuse .t12), sendOK walked wstat⟩,
   ⟨"T13", send prefixPairs (request (.walk 0 1 [ascii "fs/root"])) (.refuse .t13),
     sendOK prefixPairs walkPair.t⟩,
   ⟨"T14", send prefixPairs (request (.walk 0 1 [ascii "unmounted"])) (.refuse .t14),
     sendOK prefixPairs walkPair.t⟩,
   ⟨"T15", send commandReady (commandWrite (ascii "execX\n")) (.refuse .t15),
     sendOK commandReady echoWrite⟩]

private def receiveSeeds : List Seed :=
  let reads := readable 0
  let malformed := (Build.frame 117 0 [2, 0, 0, 0, 0x41]).getD []
  let closeOK := commit prefixPairs clunkRoot clunkReply afterRootClunk
  let versionOK := negotiated profile 256
  let versionReply := fun n v => reply (.version n (ascii v)) noTag
  [⟨"R1", receive reads readOne malformed (.refuse .r1), commit reads readOne readReply⟩,
   ⟨"R2", { receive prefixPairs statRoot (errorFrame 257) (.refuse .r2) with
       premise := fun s => (errorFrame 257).length == s.msize.toNat + 1 &&
         (decodeR (errorFrame 257)).isSome },
     commit prefixPairs statRoot (errorFrame 256)⟩,
   ⟨"R3", { closeOK with point := .ready prefixPairs, expected := .refuse .r3 }, closeOK⟩,
   ⟨"R4", receive prefixPairs clunkRoot (reply .clunk 1) (.refuse .r4), closeOK⟩,
   ⟨"R5", receive reads readOne (reply (.write 1)) (.refuse .r5), commit reads readOne readReply⟩,
   ⟨"R6", receive [] versionPair.t (versionReply 256 "unknown") (.refuse .r6), versionOK⟩,
   ⟨"R7", receive [] versionPair.t (versionReply 257 "9P2000") (.refuse .r7), versionOK⟩,
   ⟨"R8", receive reads readOne (reply (.read [0x41, 0x42])) (.refuse .r8),
     commit reads readOne readReply⟩,
   ⟨"R9", receive [versionPair] attachPair.t (reply (.attach fileQid)) (.refuse .r9),
     commit [versionPair] attachPair.t attachPair.r atAttach⟩,
   ⟨"R10", receive commandReady echoWrite (reply (.write 4)) (.refuse .r10),
     commit commandReady echoWrite (reply (.write 5))⟩]

private def faultSeeds : List Seed :=
  let reads := readable 0
  let truncatedReply := readReply.dropLast
  let header := littleEndianBytes 4 257
  [⟨"F1", fault reads readOne (.timeout [0x54]) (fun s => s.pending == some readOne),
     commit reads readOne readReply⟩,
   ⟨"F2", fault reads readOne (.transport truncatedReply)
       (fun _ => 4 ≤ truncatedReply.length && truncatedReply.length < littleEndian (truncatedReply.take 4)),
     commit reads readOne readReply⟩,
   ⟨"F3", fault prefixPairs statRoot (.oversize header)
       (fun s => header.length == 4 && s.msize.toNat < littleEndian header),
     commit prefixPairs statRoot (errorFrame 256)⟩]

private def sealSeeds : List Seed :=
  let rows := walked
  let c := exactContext rows
  let good := receipt c rows
  let accepted := sealProbe c good .sealed
  let refs := rows.map fun p => Transaction.mk (withRef p.t) (withRef p.r)
  let objects := (pairBytes rows).map fun b => (Format.q .bytes b, b)
  let viaRef := { good with trace := refs }
  let wrongLength := { viaRef with trace := ⟨withRef versionPair.t (versionPair.t.length + 1),
    withRef versionPair.r⟩ :: refs.drop 1 }
  let changed := { walkPair with t := request (.walk 0 1 []) }
  [⟨"S1", { accepted with point := .waiting [] versionPair.t, expected := .refuse .s1 }, accepted⟩,
   ⟨"S2", sealProbe c viaRef (.refuse .s2) (objects.drop 1), sealProbe c viaRef .sealed objects⟩,
   ⟨"S3", sealProbe c wrongLength (.refuse .s3) objects, sealProbe c viaRef .sealed objects⟩,
   ⟨"S4", sealProbe c { good with trace := (prefixPairs ++ [changed]).map RawPair.inline } (.refuse .s4),
     accepted⟩,
   ⟨"S5", sealProbe c { good with root := List.replicate 32 0 } (.refuse .s5), accepted⟩,
   ⟨"S6", sealProbe c { good with resultsQ := Format.q .i64 (41 : Format.I64) } (.refuse .s6), accepted⟩]

def seeds : List Seed := contextSeeds ++ sendSeeds ++ receiveSeeds ++ faultSeeds ++ sealSeeds

end Effect.ABI.E3
