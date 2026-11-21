import Effect.Fixtures
import Effect.MonitorLaws

namespace Effect.ABI.E2

open Fixtures Wire

private def run (c : Context fixtureCore) (s : State) (event : Event fixtureCore)
    (store : ObjectStore := emptyStore) : Outcome fixtureCore :=
  Monitor.step registry store c ⟨s, event⟩

private def closeMatches (c : Context fixtureCore) (s : State) (event : Event fixtureCore)
    (observation : CloseObservation) (cause : Residue) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .close evidence => out.state == s && out.residue == some cause &&
    evidence == ⟨inputQ c s event, s.prev, s.pending, observation, cause⟩
  | _ => false

private def refusedWithoutIO (s : State) (cause : Residue) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .noIO => out.state == s && out.residue == some cause
  | _ => false

private def swappedTagPhase : List Test → List Test
  | a :: b :: rest =>
    if a.cause == .t4 && b.cause == .t5 then b :: a :: rest else a :: swappedTagPhase (b :: rest)
  | rest => rest

private def firstFailure (tests : List Test) : Option Residue :=
  (tests.find? (fun t => t.fails)).map Test.cause

private def localRows : List (String × Bool) :=
  let stat : RawPair := ⟨request (.stat 0), reply (.stat (statOf rootQid []))⟩
  let c := exactContext (prefixPairs ++ [stat])
  let fresh := State.opening c
  let badTag := request (.stat 0) 1
  let early := sendTests registry c fresh badTag
  let swapped := firstFailure (swappedTagPhase early) == some .t5 &&
    refusedWithoutIO fresh .t4 (run c fresh (.send badTag))
  match (Monitor.replay registry c prefixPairs).val with
  | .refused _ => [("reachable-typed-prefix", false)]
  | .point s next =>
    let atExpectedSend := match next with
      | .send _ raw => raw == stat.t
      | _ => false
    let omitted := firstFailure ((sendTests registry c s badTag).filter (·.cause != .t5)) == none &&
      refusedWithoutIO s .t5 (run c s (.send badTag))
    let issued := run c s (.send stat.t)
    let paired := run c issued.state (.receive stat.r)
    let committed := match issued.disposition, paired.disposition with
      | .issue raw, .commit pair => raw == stat.t && pair == stat && paired.residue.isNone &&
        paired.state.prev == Format.pair s.prev stat.t stat.r && paired.state.pending.isNone
      | _, _ => false
    let lost := { issued.state with pending := none }
    let lostDetected := issued.state.pending == some stat.t &&
      closeMatches c lost (.receive stat.r) (.reply stat.r) .r3 (run c lost (.receive stat.r))
    let malformed := stat.r.dropLast
    let rejected := closeMatches c issued.state (.receive malformed) (.reply malformed) .r1
      (run c issued.state (.receive malformed))
    let timeout := FaultObservation.timeout [0x42]
    let faulted := match (Monitor.replayFault registry c prefixPairs stat.t timeout).val with
      | .inl _ => false
      | .inr out => closeMatches c issued.state (.fault timeout) (.fault timeout) .f1 out
    let input : Monitor.RawInput fixtureCore := ⟨⟨s, [([1], [2])], "different allocation"⟩, .send stat.t⟩
    let rep := (Monitor.classify input).embed
    let invariant := inputPreimage c (sigma input.state) input.event ==
        inputPreimage c (sigma rep.state) rep.event &&
      inputQ c (sigma input.state) input.event == inputQ c (sigma rep.state) rep.event &&
      (Monitor.run registry emptyStore c input).state == (Monitor.run registry emptyStore c rep).state
    [("reachable-typed-prefix", atExpectedSend), ("omitted-t5", omitted), ("swapped-t4-t5", swapped),
      ("lost-pending-t", lostDetected), ("commits-exact-pair", committed),
      ("malformed-receive-closes", rejected), ("fault-replay-closes", faulted),
      ("cache-projection-q", invariant)]

private def ref (raw : Bytes) : FrameRef := .reference (Format.q .bytes raw) (UInt64.ofNat raw.length)

private def refs (pair : RawPair) : Transaction := ⟨ref pair.t, ref pair.r⟩

private def sealMatches (s : State) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .seal result => out.state == s && out.residue.isNone && resultsQ (core := fixtureCore) result ==
    Format.q .i64 (42 : Format.I64)
  | _ => false

private def checkpoint (s : State) : Checkpoint := ⟨s.contextQ, s.prev, s.q, s⟩

private def receiptRows : List (String × Bool) :=
  let rows := prefixPairs ++ [walkPair]
  let c := exactContext rows
  let start := State.opening c
  let root := rows.foldl (fun prev pair => Format.pair prev pair.t pair.r) c.openingQ
  let inlined : SealRequest fixtureCore := ⟨rows.map RawPair.inline, (42 : Format.I64), root,
    Format.q .i64 (42 : Format.I64)⟩
  let byRef := { inlined with trace := rows.map refs }
  let objects := (rows.flatMap fun p => [p.t, p.r]).map fun b => (Format.q .bytes b, b)
  let store : ObjectStore := fun q => (objects.find? (fun entry => entry.1 == q)).map Prod.snd
  let badStore : ObjectStore := fun q =>
    if q == Format.q .bytes versionPair.t then some (versionPair.t ++ [0]) else store q
  let incompleteStore : ObjectStore := fun q =>
    if q == Format.q .bytes walkPair.r then none else badStore q
  let inlineAndRef := sealMatches start (run c start (.seal inlined)) &&
    sealMatches start (run c start (.seal byRef) store)
  let missingWins := refusedWithoutIO start .s2 (run c start (.seal byRef) incompleteStore)
  let wrongObject := refusedWithoutIO start .s3 (run c start (.seal byRef) badStore)
  let wrongRoot := { inlined with root := List.replicate 32 0 }
  let wrongResult := { inlined with results := (41 : Format.I64) }
  let wrongResultQ := { inlined with resultsQ := Format.q .i64 (41 : Format.I64) }
  let anchors := refusedWithoutIO start .s5 (run c start (.seal wrongRoot)) &&
    refusedWithoutIO start .s6 (run c start (.seal wrongResult)) &&
    refusedWithoutIO start .s6 (run c start (.seal wrongResultQ))
  let short := { inlined with trace := inlined.trace.dropLast }
  let long := { inlined with trace := inlined.trace ++ [walkPair.inline] }
  let exhaustion := refusedWithoutIO start .s4 (run c start (.seal short)) &&
    refusedWithoutIO start .s4 (run c start (.seal long))
  let resumed := match (Monitor.replay registry c prefixPairs).val with
    | .point s (.send _ raw) =>
      let cp := checkpoint s
      let sent := checkpoint (s.afterSend raw)
      match Monitor.resumeCheckpoint registry c prefixPairs cp,
            Monitor.resumeCheckpoint registry c prefixPairs sent with
      | some ⟨.ready (.send _ next), _⟩, some ⟨.waiting _ issued, _⟩ =>
        next == walkPair.t && issued == walkPair.t &&
        (Monitor.resumeCheckpoint registry c prefixPairs { cp with prev := List.replicate 32 0 }).isNone
      | _, _ => false
    | _ => false
  [("inline-reference-seal", inlineAndRef), ("unavailable-before-bad-q", missingWins),
   ("substitution-refused", wrongObject), ("external-anchors", anchors),
   ("exact-exhaustion", exhaustion), ("checkpoint-prefix", resumed)]

def rows : List (String × Bool) := localRows ++ receiptRows

#print axioms Monitor.sound
#print axioms Monitor.complete
#print axioms Monitor.exact_outcome
#print axioms Monitor.admit_exact
#print axioms Monitor.replay_exact
#print axioms Monitor.projection_idempotent
#print axioms Monitor.q_invariant
#print axioms Monitor.rejected_send
#print axioms Monitor.rejected_receive
#print axioms Monitor.rejected_fault
#print axioms Monitor.valid_receive

end Effect.ABI.E2

def main : IO UInt32 := do
  let rows := Effect.ABI.E2.rows
  for (id, ok) in rows do
    IO.println s!"monitor\t{id}\t{if ok then 1 else 0}"
  pure (if rows.length == 14 && rows.all Prod.snd then 0 else 1)
