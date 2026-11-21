import Effect.Fixtures

namespace Effect.ABI

namespace E1

open Fixtures

private def openWitness (c : Context fixtureCore) :
    Option {out // LocalJudgment registry c State.pre .openSession out} :=
  match certifyGuards (contextTests registry c State.pre true) with
  | .pass p => some ⟨opened c, .openSession p⟩
  | .refuse .. => none

def sendWitness (c : Context fixtureCore) (s : State) (raw : Bytes) :
    {out // LocalJudgment registry c s (.send raw) out} :=
  match certifyGuards (sendTests registry c s raw) with
  | .pass p => ⟨issued s raw, .send p⟩
  | .refuse cause p => ⟨refused c s (.send raw) cause, .refuse p⟩

def receiveWitness (c : Context fixtureCore) (s : State) (raw : Bytes) :
    Option {out // LocalJudgment registry c s (.receive raw) out} :=
  match certifyGuards (receiveTests registry c s raw) with
  | .refuse cause p => some ⟨refused c s (.receive raw) cause, .refuse p⟩
  | .pass p =>
    match ht : s.pending, hr : Wire.decodeR raw with
    | some t, some r =>
      match hd : Wire.decodeT t with
      | some decoded => some ⟨committed s t raw decoded.body r.body, .receive p ht hd hr⟩
      | none => none
    | _, _ => none

private def faultWitness (c : Context fixtureCore) (s : State) (obs : FaultObservation) :
    Option {out // LocalJudgment registry c s (.fault obs) out} :=
  match certifyGuards (localTests registry c s (.fault obs)) with
  | .refuse cause p => some ⟨refused c s (.fault obs) cause, .refuse p⟩
  | .pass _ => none

def consume (c : Context fixtureCore) (s : State) (row : RawPair) : Option State := do
  let sent := (sendWitness c s row.t).val
  if sent.residue.isSome then none else
    let got ← receiveWitness c sent.state row.r
    if got.val.residue.isSome then none else some got.val.state

def stateAt (c : Context fixtureCore) (rows : List RawPair) : Option State := do
  let start ← openWitness c
  rows.foldlM (consume c) start.val.state

theorem send_rule (c : Context fixtureCore) (s : State) (t : Bytes)
    (p : Passes (sendTests registry c s t)) :
    LocalJudgment registry c s (.send t) ⟨s.afterSend t, none, .issue t⟩ := .send p

theorem partialWalkSlots (s : State) (src dst : Nat) (names : List Bytes) (qids : List Wire.Qid)
    (short : names.length ≠ qids.length) (t r : Bytes) :
    let next := s.afterReceive t r (.walk src dst names) (.walk qids)
    next.root = s.root ∧ next.work = s.work ∧ next.pending = none ∧
      next.prev = Format.pair s.prev t r := by
  simp [State.afterReceive, State.applyReply, short]

theorem failedRootClunk (s : State) (t r ename : Bytes) :
    let next := s.afterReceive t r (.clunk 0) (.error ename)
    next.root = none ∧ next.phase = Phase.ended.code ∧ next.pending = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem failedWorkRemove (s : State) (t r ename : Bytes) :
    let next := s.afterReceive t r (.remove 1) (.error ename)
    next.work = none ∧ next.pending = none := by
  exact ⟨rfl, rfl⟩

private def committedPair (before : State) (want : RawPair) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .commit pair => pair == want && out.residue.isNone && out.state.pending.isNone &&
      out.state.prev == Format.pair before.prev want.t want.r
  | _ => false

private def isClosed (before : State) (obs : CloseObservation) (cause : Residue)
    (event : Event fixtureCore) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .close evidence => out.state == before && out.residue == some cause &&
      evidence == ⟨inputQ exampleContext before event, before.prev, before.pending, obs, cause⟩
  | _ => false

private def noIO (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .noIO => true
  | _ => false

private def observationRows : Option (List (String × Bool)) := do
  let c := exampleContext
  let fresh ← stateAt c []
  let attached ← stateAt c prefixPairs
  let walked ← stateAt c (prefixPairs ++ [walkPair])
  let longT := request (.walk 0 1 (List.replicate 17 (ascii "..")))
  let long := (sendWitness c attached longT).val
  let partialR := reply (.walk [fsQid])
  let walkPending := (sendWitness c attached walkPair.t).val
  let partialOut ← receiveWitness c walkPending.state partialR

  let clunkT := request (.clunk 0)
  let removeT := request (.remove 1)
  let failedR := reply (.error (ascii "fixture failure"))
  let rootPending := (sendWitness c attached clunkT).val
  let workPending := (sendWitness c walked removeT).val
  let failedClunk ← receiveWitness c rootPending.state failedR
  let failedRemove ← receiveWitness c workPending.state failedR
  let malformed := failedR.dropLast
  let badR ← receiveWitness c rootPending.state malformed
  let timeout := FaultObservation.timeout (ascii "deadline")
  let fault ← faultWitness c rootPending.state timeout

  let goodT := request (.stat 0)
  let wrongTagT := request (.stat 0) 1
  let good := (sendWitness c attached goodT).val
  let badTag := (sendWitness c attached wrongTagT).val
  let outOfPhase := (sendWitness c fresh wrongTagT).val
  let tagOnly :=
    match Wire.decodeT goodT, Wire.decodeT wrongTagT with
    | some a, some b => a.body == b.body && a.tag == 0 && b.tag == 1
    | _, _ => false
  return [
    ("twalk-17-t9", (Wire.decodeT longT).any (fun t =>
      match t.body with | .walk _ _ names => names.length == 17 | _ => false) &&
      long.residue == some .t9 && noIO long && long.state == attached),
    ("partial-rwalk", walkPending.residue.isNone &&
      committedPair walkPending.state ⟨walkPair.t, partialR⟩ partialOut.val &&
      partialOut.val.state.root == attached.root && partialOut.val.state.work == attached.work),
    ("failed-clunk-root-ends", rootPending.residue.isNone &&
      committedPair rootPending.state ⟨clunkT, failedR⟩ failedClunk.val &&
      failedClunk.val.state.root.isNone && failedClunk.val.state.isPhase .ended),
    ("failed-remove-clears-work", workPending.residue.isNone &&
      committedPair workPending.state ⟨removeT, failedR⟩ failedRemove.val &&
      failedRemove.val.state.work.isNone && failedRemove.val.state.root == walked.root),
    ("valid-error-malformed-fault", failedClunk.val.residue.isNone &&
      isClosed rootPending.state (.reply malformed) .r1 (.receive malformed) badR.val &&
      isClosed rootPending.state (.fault timeout) .f1 (.fault timeout) fault.val &&
      inputQ c rootPending.state (.receive malformed) != inputQ c rootPending.state (.fault timeout)),
    ("tag-only-t5", tagOnly && good.residue.isNone && good.state.pending == some goodT &&
      badTag.residue == some .t5 && noIO badTag && badTag.state == attached),
    ("t4-before-t5", (sendTests registry c fresh wrongTagT).any (fun g => g.cause == .t5 && g.fails) &&
      outOfPhase.residue == some .t4 && noIO outOfPhase && outOfPhase.state == fresh)]

private def authorityRows : Option (List (String × Bool × Bytes)) := do
  let c := exampleContext
  let attached ← stateAt c prefixPairs
  let clone : RawPair := ⟨request (.walk 0 1 []), reply (.walk [])⟩
  let rootAlias ← consume c attached clone
  let cmdWork ← consume c attached cmdPair
  let readOnly := request (.openFile 1 0)
  let unmounted := request (.walk 0 1 [ascii "unmounted"])
  let accept := (sendWitness c rootAlias readOnly).val
  let refuses (s : State) (raw : Bytes) (cause : Residue) :=
    let out := (sendWitness c s raw).val
    out.residue == some cause && out.state == s && noIO out
  let denied (id : String) (s : State) (raw : Bytes) (cause : Residue) :=
    (id, refuses s raw cause, inputQ c s (.send raw))
  return [
    ("virtual-root-read-open", rootAlias.work == attached.root && c.declares registry [] &&
      (c.policy registry []).isNone && accept.residue.isNone &&
      (match accept.disposition with | .issue t => t == readOnly | _ => false),
      inputQ c rootAlias (.send readOnly)),
    denied "virtual-root-create" rootAlias (request (.create 1 (ascii "fs") 511 0)) .t8,
    denied "virtual-root-remove" rootAlias (request (.remove 1)) .t8,
    denied "virtual-root-orclose" rootAlias (request (.openFile 1 64)) .t8,
    denied "declared-mount-denies-access" cmdWork readOnly .t8,
    denied "undeclared-mount-t14" attached unmounted .t14]

private def vectorRow (id : String) (type : Format.Schema) (value : type.Value) : String :=
  let hex := fun raw => String.mk ((Format.lowerHex raw).map (Char.ofNat ∘ UInt8.toNat))
  String.intercalate "\t" ["format", id, hex (Format.canonical type value), hex (Format.q type value)]

def formatRows : List String :=
  let ns : Bytes := List.replicate 32 0
  let p : Bytes := List.replicate 32 17
  let plan : Bytes := List.replicate 32 34
  let v := versionPair 8192 8192
  let smaller := versionPair 8192 4096
  let prev := Format.opening abiId ns p 8192 plan
  [vectorRow "opening" Format.openingSchema (abiId, ns, p, (8192 : Format.I64), plan, ()),
   vectorRow "pair-version-8192" Format.pairSchema (prev, v.t, v.r, ()),
   vectorRow "pair-version-4096" Format.pairSchema (prev, v.t, smaller.r, ()),
   vectorRow "frame-reference-object" .bytes v.r,
   vectorRow "results-i64-42" .i64 (42 : Format.I64)]

end E1
end Effect.ABI

open Effect.ABI.E1

def main : IO UInt32 := do
  match Effect.ABI.E1.observationRows, Effect.ABI.E1.authorityRows with
  | some cases, some authority => do
    let hex := fun raw => String.mk ((Effect.Format.lowerHex raw).map (Char.ofNat ∘ UInt8.toNat))
    for row in formatRows do IO.println row
    for (id, pass) in cases do IO.println s!"witness\t{id}\t{if pass then 1 else 0}"
    for (id, pass, q) in authority do IO.println s!"authority\t{id}\t{if pass then 1 else 0}\t{hex q}"
    return if cases.all Prod.snd && authority.all (fun (_, pass, _) => pass) then 0 else 1
  | _, _ => do
    IO.eprintln "fixture could not establish a relation premise"
    return 1

#print axioms Effect.ABI.Context.policy_declared
#print axioms Effect.ABI.E1.send_rule
#print axioms Effect.ABI.E1.partialWalkSlots
#print axioms Effect.ABI.E1.failedRootClunk
#print axioms Effect.ABI.E1.failedWorkRemove
