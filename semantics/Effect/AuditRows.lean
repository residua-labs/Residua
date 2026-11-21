import Effect.Fixtures
import Effect.Monitor

namespace Effect.ABI.AuditRows

open Wire Fixtures

structure Row where
  id : String
  passed : Bool
  observed : String
  q : Bytes

private def step (reg : Registry) (c : Context fixtureCore) (s : State)
    (event : Event fixtureCore) : Outcome fixtureCore :=
  Monitor.step reg emptyStore c ⟨s, event⟩

private def stateAt (reg : Registry) (c : Context fixtureCore) (pairs : List RawPair) : Option State := do
  let start := step reg c State.pre .openSession
  if start.residue.isSome then none else
    pairs.foldlM (fun s pair => do
      let sent := step reg c s (.send pair.t)
      if sent.residue.isSome then none else
        let received := step reg c sent.state (.receive pair.r)
        if received.residue.isSome then none else some received.state) start.state

private def firstFailure (tests : List Test) : Option Residue := (tests.find? Test.fails).map Test.cause

private def row (id : String) (c : Context fixtureCore) (s : State) (event : Event fixtureCore)
    (out : Outcome fixtureCore) (passed : Bool) : Row :=
  ⟨id, passed, out.residue.elim "admit" Residue.label, inputQ c s event⟩

private def issuedAs (s : State) (t : Bytes) (out : Outcome fixtureCore) : Bool :=
  out.residue.isNone && out.state == { s with pending := some t, sentSteps := s.sentSteps + 1 } &&
  (match out.disposition with | .issue raw => raw == t | _ => false)

private def send (reg : Registry) (c : Context fixtureCore) (id : String) (s : State)
    (req : Wire.Request) (cause : Option Residue) : Row :=
  let raw := request req
  let out := step reg c s (.send raw)
  row id c s (.send raw) out (match cause with
    | none => issuedAs s raw out
    | some residue => out.residue == some residue && out.state == s &&
        (match out.disposition with | .noIO => true | _ => false))

private def commit (reg : Registry) (c : Context fixtureCore) (id : String) (s : State)
    (pair : RawPair) (change : State → State) : Row :=
  let sent := step reg c s (.send pair.t)
  let out := step reg c sent.state (.receive pair.r)
  let next := { change s with sentSteps := s.sentSteps + 1, prev := Format.pair s.prev pair.t pair.r }
  row id c sent.state (.receive pair.r) out (issuedAs s pair.t sent && out.residue.isNone &&
    out.state == next && (firstFailure (contextTests reg c out.state false)).isNone &&
    (match out.disposition with | .commit raw => raw == pair | _ => false))

private def fsFixture (paths : List Path) : Registry × Context fixtureCore × List RawPair :=
  let entry : Registration := { fs with config := { fs.config with paths } }
  let ns : Namespace := ⟨1, [⟨ascii "fs", entry.contract.q, entry.config.q⟩]⟩
  let pairs := [versionPair, attachPair ns]
  ([entry], context (pairs.map RawPair.t) profile ns, pairs)

private def mountWalk : RawPair := ⟨request (.walk 0 1 [ascii "fs"]), reply (.walk [fsQid])⟩

private def bindWork (path : Path) (qid : Wire.Qid) (s : State) : State :=
  { s with work := some (Fid.unopened path qid) }

private def authorityRows : Option (List Row) := do
  let c := exampleContext
  let mount ← stateAt registry c (prefixPairs ++ [mountWalk])
  let file ← stateAt registry c (prefixPairs ++ [walkPair, filePair])
  let enterRoot : RawPair := ⟨request (.walk 1 1 [ascii "root"]), reply (.walk [dirQid])⟩
  let (subReg, subCtx, subPrefix) := fsFixture [[ascii "work", ascii "sub"]]
  let workPath := [ascii "fs", ascii "work"]
  let workWalk : RawPair := ⟨request (.walk 0 1 workPath), reply (.walk [fsQid, dirQid])⟩
  let work ← stateAt subReg subCtx (subPrefix ++ [workWalk])
  let enterSub : RawPair := ⟨request (.walk 1 1 [ascii "sub"]), reply (.walk [rootQid])⟩
  let sub ← stateAt subReg subCtx (subPrefix ++ [workWalk, enterSub])
  let (renameReg, renameCtx, renamePrefix) := fsFixture
    [[ascii "root"], [ascii "other", ascii "leaf"], [ascii "peer"]]
  let root ← stateAt renameReg renameCtx (renamePrefix ++ [walkPair])
  let rename := fun name => Wire.Request.wstat 1 { noStatChange with name := ascii name }
  let truncate := Wire.Request.wstat 1 { noStatChange with length := 0 }
  let reject := fun reg c id s req cause => send reg c id s req (some cause)
  return [
    reject registry c "mount-remove" mount (.remove 1) .t8,
    reject registry c "mount-create" mount (.create 1 (ascii "root") 511 1) .t8,
    reject registry c "mount-open" mount (.openFile 1 0) .t8,
    reject registry c "mount-stat" mount (.stat 1) .t8,
    reject registry c "mount-truncate" mount truncate .t12,
    send registry c "mount-clunk" mount (.clunk 1) none,
    commit registry c "mount-to-anchor" mount enterRoot (bindWork fsPath dirQid),
    reject subReg subCtx "nested-remove" work (.remove 1) .t8,
    reject subReg subCtx "nested-create" work (.create 1 (ascii "sub") 511 1) .t8,
    reject subReg subCtx "nested-truncate" work truncate .t12,
    commit subReg subCtx "nested-to-anchor" work enterSub (bindWork (workPath ++ [ascii "sub"]) rootQid),
    send subReg subCtx "anchor-remove" sub (.remove 1) none,
    reject renameReg renameCtx "rename-to-ancestor" root (rename "other") .t12,
    reject renameReg renameCtx "rename-across-anchors" root (rename "peer") .t12,
    commit registry c "rename-in-authorized-parent" file ⟨request (rename "new"), reply .wstat⟩
      (bindWork (fsPath ++ [ascii "new"]) fileQid)]

private def forged (c : Context fixtureCore) (id : String) (s : State) (t r : Bytes)
    (sendCause : Residue) : Row :=
  let sent := s.afterSend t
  let out := step registry c sent (.receive r)
  row id c sent (.receive r) out (
    firstFailure (sendTests registry c s t) == some sendCause &&
    firstFailure (contextTests registry c sent false) == some .c5 &&
    out.residue == some .c5 && out.state == sent &&
    (match out.disposition with
    | .close evidence => evidence == ⟨inputQ c sent (.receive r), sent.prev, some t, .reply r, .c5⟩
    | _ => false))

private def pendingRows : Option (List Row) := do
  let c := exampleContext
  let fresh ← stateAt registry c []
  let versioned ← stateAt registry c [versionPair]
  let attached ← stateAt registry c prefixPairs
  let walked ← stateAt registry c (prefixPairs ++ [walkPair])
  let ancestor ← stateAt registry c (prefixPairs ++ [mountWalk])
  let file ← stateAt registry c (prefixPairs ++ [walkPair, filePair])
  let writable ← stateAt registry c (prefixPairs ++ [walkPair, filePair, openPair 2])
  let command ← stateAt registry c (prefixPairs ++ [cmdPair, openPair 1])
  let tight := exactContext prefixPairs { profile with maxSteps := 2 }
  let atLimit ← stateAt registry tight prefixPairs
  let last := exactContext prefixPairs { profile with maxSteps := 3 }
  let beforeLast ← stateAt registry last prefixPairs
  let one := exactContext [versionPair] { profile with maxSteps := 1 }
  let oneFresh ← stateAt registry one []
  let statRoot : RawPair := ⟨request (.stat 0), reply (.stat (statOf rootQid []))⟩
  let readT := request (.read 1 0 4)
  let bad := forged c
  return [
    bad "missing-fid" attached readT (reply (.read [1, 2, 3, 4])) .t6,
    bad "unopened-write" file (request (.write 1 0 [65])) (reply (.write 1)) .t8,
    bad "execute-open" walked (request (.openFile 1 3)) (reply (.openFile dirQid 0)) .t2,
    bad "directory-write-open" walked (request (.openFile 1 1)) (reply (.openFile dirQid 0)) .t8,
    bad "slash-walk" attached (request (.walk 0 1 [ascii "a/b"])) (reply (.walk [dirQid])) .t13,
    bad "busy-walk-target" walked walkPair.t walkPair.r .t7,
    bad "wrong-permission" walked (request (.create 1 (ascii "new") 512 0))
      (reply (.create fileQid 0)) .t2,
    bad "over-msize" writable (request (.write 1 0 (List.replicate 234 65))) (reply (.write 234)) .t3,
    bad "attach-identity" versioned (request (.attach 0 noFid [] [])) attachPair.r .t11,
    bad "version-offer" fresh (request (.version 257 version9P) noTag) versionPair.r .t2,
    bad "tag" attached (request (.stat 0) 1) (reply (.stat (statOf rootQid [])) 1) .t5,
    bad "walk-count" attached (request (.walk 0 1 (List.replicate 17 (ascii ".."))))
      (reply (.walk [rootQid])) .t9,
    forged tight "step-count" atLimit statRoot.t statRoot.r .t10,
    bad "undeclared-walk" attached (request (.walk 0 1 [ascii "unmounted"])) (reply (.walk [dirQid])) .t14,
    bad "ancestor-remove" ancestor (request (.remove 1)) (reply .remove) .t8,
    bad "command-grammar" command (request (.write 1 0 (ascii "other\n"))) (reply (.write 6)) .t15,
    bad "before-reply-framing" attached readT [] .t6,
    commit registry one "version-at-step-limit" oneFresh versionPair
      (fun s => { s with phase := Phase.versioned.code, msize := 256 }),
    commit registry last "stat-at-step-limit" beforeLast statRoot id]

private def printRows (family : String) (rows : List Row) : IO Unit :=
  for r in rows do
    let q := String.mk ((Format.lowerHex r.q).map (Char.ofNat ∘ UInt8.toNat))
    IO.println s!"{family}\t{r.id}\t{if r.passed then 1 else 0}\t{r.observed}\t{q}"

def run : IO UInt32 := do
  match authorityRows, pendingRows with
  | some authority, some pending =>
    printRows "ancestor-authority" authority
    printRows "pending-invariants" pending
    return if authority.all Row.passed && pending.all Row.passed then 0 else 1
  | _, _ =>
    IO.eprintln "an audit fixture failed to reach its setup state"
    return 2

end Effect.ABI.AuditRows

def main : IO UInt32 := Effect.ABI.AuditRows.run
