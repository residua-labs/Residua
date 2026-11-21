import Effect.Guards

namespace Effect.ABI

open Wire

def State.afterSend (s : State) (raw : Bytes) : State :=
  { s with pending := some raw, sentSteps := UInt64.ofNat (s.sentSteps.toNat + 1) }

private def release (s : State) (fid : Nat) : State :=
  let next := s.putFid fid none
  if fid == 0 then { next with phase := Phase.ended.code } else next

private def updateFid (s : State) (fid : Nat) (update : Fid → Fid) : State :=
  s.putFid fid ((s.fid fid).map update)

/-- Fid changes are selected by the admitted request and the validated reply.
The partial-walk and repeated-error cases leave the slots untouched. -/
def State.applyReply (s : State) (t : Wire.Request) (r : Wire.Reply) : State :=
  match t, r with
  | .version .., .version msize _ =>
    { s with phase := Phase.versioned.code, msize := UInt64.ofNat msize }
  | .attach .., .attach qid =>
    { s with phase := Phase.attached.code, root := some (Fid.unopened [] qid) }
  | .walk src dst names, .walk qids =>
    if names.length != qids.length then s else
      match s.fid src with
      | none => s
      | some f =>
        let next := { f with
          path := names.foldl traverse f.path
          qid := (qids.getLast?.map Wire.Qid.bytes).getD f.qid }
        s.putFid dst (some next)
  | .openFile fid mode, .openFile qid iounit =>
    updateFid s fid fun f => f.openAs qid mode iounit
  | .create fid name _ mode, .create qid iounit =>
    updateFid s fid fun f =>
      (Fid.unopened (f.path ++ [name]) qid).openAs qid mode iounit
  | .read fid offset _, .read data =>
    updateFid s fid fun f =>
      if f.directory then
        { f with dirOffset := littleEndianBytes 8 (offset + data.length) }
      else f
  | .stat fid, .stat info =>
    updateFid s fid fun f => { f with qid := info.qid.bytes }
  | .wstat fid info, .wstat =>
    if info.name.isEmpty then s else
      updateFid s fid fun f => { f with path := f.path.dropLast ++ [info.name] }
  | .clunk fid, .clunk | .clunk fid, .error _
  | .remove fid, .remove | .remove fid, .error _ => release s fid
  | _, _ => s

def State.afterReceive (s : State) (rawT rawR : Bytes) (t : Wire.Request) (r : Wire.Reply) : State :=
  { (s.applyReply t r) with pending := none, prev := Format.pair s.prev rawT rawR }

inductive FaultObservation where
  | timeout (diagnostic : Bytes)
  | transport (observed : Bytes)
  | oversize (header : Bytes)
  deriving DecidableEq, Repr

def FaultObservation.cause : FaultObservation → Residue
  | .timeout _ => .f1
  | .transport _ => .f2
  | .oversize _ => .f3

def FaultObservation.schema : Format.Schema := .sum2 .bytes (.sum2 .bytes .bytes)

def FaultObservation.value : FaultObservation → FaultObservation.schema.Value
  | .timeout diagnostic => .inl diagnostic
  | .transport observed => .inr (.inl observed)
  | .oversize header => .inr (.inr header)

inductive FrameRef where
  | inline (raw : Bytes)
  | reference (frameQ : Bytes) (length : Format.I64)
  deriving DecidableEq, Repr

def FrameRef.schema : Format.Schema :=
  .sum2 .bytes (Format.record [("frame_q", .bytes), ("length", .i64)])

def FrameRef.value : FrameRef → FrameRef.schema.Value
  | .inline raw => .inl raw
  | .reference digest length => .inr (digest, length, ())

structure Transaction where
  t : FrameRef
  r : FrameRef
  deriving DecidableEq, Repr

def Transaction.schema : Format.Schema :=
  Format.record [("t", FrameRef.schema), ("r", FrameRef.schema)]

def Transaction.value (pair : Transaction) : Transaction.schema.Value :=
  (pair.t.value, pair.r.value, ())

structure RawPair where
  t : Bytes
  r : Bytes
  deriving DecidableEq, Repr

def RawPair.inline (pair : RawPair) : Transaction := ⟨.inline pair.t, .inline pair.r⟩

/-- Raw byte objects are resolved against the verifier's object store. -/
abbrev ObjectStore := Bytes → Option Bytes

def FrameRef.resolve (store : ObjectStore) : FrameRef → Option Bytes
  | .inline raw => some raw
  | .reference q _ => store q

def FrameRef.matches (raw : Bytes) : FrameRef → Bool
  | .inline original => raw == original
  | .reference q length => raw.length == length.toNat && raw.length ≤ maxSigned &&
    Format.q .bytes raw == q

def Transaction.resolve (store : ObjectStore) (pair : Transaction) : Option RawPair := do
  return ⟨← pair.t.resolve store, ← pair.r.resolve store⟩

def Transaction.matches (pair : Transaction) (raw : RawPair) : Bool :=
  pair.t.matches raw.t && pair.r.matches raw.r

def payloadsMatch : List Transaction → List RawPair → Bool
  | [], [] => true
  | pair :: trace, raw :: rest => pair.matches raw && payloadsMatch trace rest
  | _, _ => false

structure SealRequest (core : Core) where
  trace : List Transaction
  results : Result core.resultType
  root : Bytes
  resultsQ : Bytes

def SealRequest.schema (core : Core) : Format.Schema := Format.record
  [("trace", .list Transaction.schema), ("results", core.resultType),
   ("root", .bytes), ("results_q", .bytes)]

def SealRequest.value {core : Core} (request : SealRequest core) : (SealRequest.schema core).Value :=
  (request.trace.map Transaction.value, request.results, request.root, request.resultsQ, ())

inductive Event (core : Core) where
  | openSession
  | send (raw : Bytes)
  | receive (raw : Bytes)
  | fault (observed : FaultObservation)
  | seal (request : SealRequest core)

def Event.schema (core : Core) : Format.Schema :=
  .sum2 Format.contextSchema (.sum2 .bytes (.sum2 .bytes
    (.sum2 FaultObservation.schema (SealRequest.schema core))))

def Event.value {core : Core} (c : Context core) : Event core → (Event.schema core).Value
  | .openSession => .inl c.value
  | .send raw => .inr (.inl raw)
  | .receive raw => .inr (.inr (.inl raw))
  | .fault observed => .inr (.inr (.inr (.inl observed.value)))
  | .seal request => .inr (.inr (.inr (.inr request.value)))

def inputPreimage {core : Core} (c : Context core) (s : State) (event : Event core) : Bytes :=
  Format.canonical
    (Format.record [("context_q", .bytes), ("state_q", .bytes), ("event", Event.schema core)])
    (c.q, s.q, event.value c, ())

def inputQ {core : Core} (c : Context core) (s : State) (event : Event core) : Bytes :=
  Format.hashCanonical (inputPreimage c s event)

def resultsQ {core : Core} (result : Result core.resultType) : Bytes :=
  Format.q core.resultType result

inductive CloseObservation where
  | reply (raw : Bytes)
  | fault (observed : FaultObservation)
  deriving DecidableEq, Repr

structure CloseEvidence where
  q : Bytes
  prev : Bytes
  pending : Option Bytes
  observed : CloseObservation
  cause : Residue
  deriving DecidableEq, Repr

inductive Disposition (core : Core) where
  | noIO
  | issue (t : Bytes)
  | commit (pair : RawPair)
  | close (evidence : CloseEvidence)
  | seal (results : Result core.resultType)

structure Outcome (core : Core) where
  state : State
  residue : Option Residue
  disposition : Disposition core

def refused {core : Core} (c : Context core) (s : State) (event : Event core)
    (cause : Residue) : Outcome core :=
  let closed := fun observed => Disposition.close ⟨inputQ c s event, s.prev, s.pending, observed, cause⟩
  let disposition := match event with
    | .receive raw => closed (.reply raw)
    | .fault observed => closed (.fault observed)
    | _ => .noIO
  ⟨s, some cause, disposition⟩

def opened {core : Core} (c : Context core) : Outcome core := ⟨State.opening c, none, .noIO⟩

def issued {core : Core} (s : State) (t : Bytes) : Outcome core :=
  ⟨s.afterSend t, none, .issue t⟩

def committed {core : Core} (s : State) (rawT rawR : Bytes) (t : Wire.Request) (r : Wire.Reply) : Outcome core :=
  ⟨s.afterReceive rawT rawR t r, none, .commit ⟨rawT, rawR⟩⟩

def sealed {core : Core} (s : State) (result : Result core.resultType) : Outcome core :=
  ⟨s, none, .seal result⟩

end Effect.ABI
