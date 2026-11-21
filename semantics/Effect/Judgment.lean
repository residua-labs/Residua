import Effect.Transition

namespace Effect.ABI

def localTests {core : Core} (registry : Registry) (c : Context core) (s : State) :
    Event core → List Test
  | .openSession => contextTests registry c s true
  | .send raw => sendTests registry c s raw
  | .receive raw => receiveTests registry c s raw
  | .fault obs => contextTests registry c s false ++ [⟨obs.cause, true⟩]
  | .seal _ => contextTests registry c s false

inductive LocalJudgment {core : Core} (registry : Registry) (c : Context core) :
    State → Event core → Outcome core → Prop where
  | refuse : First cause (localTests registry c s event) →
      LocalJudgment registry c s event (refused c s event cause)
  | openSession : Passes (contextTests registry c s true) →
      LocalJudgment registry c s .openSession (opened c)
  | send : Passes (sendTests registry c s raw) →
      LocalJudgment registry c s (.send raw) (issued s raw)
  | receive : Passes (receiveTests registry c s rawR) →
      s.pending = some rawT → Wire.decodeT rawT = some t → Wire.decodeR rawR = some r →
      LocalJudgment registry c s (.receive rawR) (committed s rawT rawR t.body r.body)

inductive ReplayBoundary (core : Core) where
  | point (state : State) (step : Step core.stateType core.resultType)
  | refused (cause : Residue)

/-- A replay derives a point at the end of a finite tape, or a first
refusal. The next step starts with the verifier's pure invocation. -/
inductive ReplayFrom {core : Core} (registry : Registry) (c : Context core)
    (plan : Plan core) : State → Step core.stateType core.resultType →
      List RawPair → ReplayBoundary core → Prop where
  | boundary : ReplayFrom registry c plan s step [] (.point s step)
  | extra : ReplayFrom registry c plan s (.done result) (pair :: rest) (.refused .s4)
  | requestMismatch : raw ≠ pair.t →
      ReplayFrom registry c plan s (.send k raw) (pair :: rest) (.refused .s4)
  | sendRefused : raw = pair.t → First cause (sendTests registry c s raw) →
      ReplayFrom registry c plan s (.send k raw) (pair :: rest) (.refused cause)
  | receiveRefused : raw = pair.t → Passes (sendTests registry c s raw) →
      First cause (receiveTests registry c (s.afterSend raw) pair.r) →
      ReplayFrom registry c plan s (.send k raw) (pair :: rest) (.refused cause)
  | transaction : raw = pair.t → Passes (sendTests registry c s raw) →
      Passes (receiveTests registry c (s.afterSend raw) pair.r) →
      Wire.decodeT raw = some t → Wire.decodeR pair.r = some r →
      ReplayFrom registry c plan ((s.afterSend raw).afterReceive raw pair.r t.body r.body)
        (plan.invoke (some (k, pair.r))) rest verdict →
      ReplayFrom registry c plan s (.send k raw) (pair :: rest) verdict

inductive Replay {core : Core} (registry : Registry) (c : Context core) :
    List RawPair → ReplayBoundary core → Prop where
  | openRefused : First cause (contextTests registry c State.pre true) →
      Replay registry c pairs (.refused cause)
  | start : Passes (contextTests registry c State.pre true) → c.plan = some p →
      ReplayFrom registry c p (State.opening c) (p.invoke none) pairs verdict →
      Replay registry c pairs verdict

/-- A failed run carries its terminal observation separately from the
completed-pair prefix. The issued request must agree with the next pure step. -/
inductive FaultReplay {core : Core} (registry : Registry) (c : Context core)
    (pairs : List RawPair) (raw : Bytes) (obs : FaultObservation) :
    Sum Residue (Outcome core) → Prop where
  | prefixRefused : Replay registry c pairs (.refused cause) →
      FaultReplay registry c pairs raw obs (.inl cause)
  | extra : Replay registry c pairs (.point s (.done result)) →
      FaultReplay registry c pairs raw obs (.inl .s4)
  | mismatch : Replay registry c pairs (.point s (.send k next)) → next ≠ raw →
      FaultReplay registry c pairs raw obs (.inl .s4)
  | sendRefused : Replay registry c pairs (.point s (.send k raw)) →
      First cause (sendTests registry c s raw) →
      FaultReplay registry c pairs raw obs (.inl cause)
  | observe : Replay registry c pairs (.point s (.send k raw)) →
      Passes (sendTests registry c s raw) →
      LocalJudgment registry c (s.afterSend raw) (.fault obs) out →
      FaultReplay registry c pairs raw obs (.inr out)

structure LoadedTrace {core : Core} (registry : Registry) (store : ObjectStore)
    (c : Context core) (s : State) (request : SealRequest core) (rows : List RawPair) : Prop where
  contextValid : Passes (contextTests registry c s false)
  clear : s.pending = none
  available : request.trace.mapM (Transaction.resolve store) = some rows
  verified : payloadsMatch request.trace rows = true

inductive SealJudgment {core : Core} (registry : Registry) (store : ObjectStore)
    (c : Context core) (s : State) (request : SealRequest core) : Outcome core → Prop where
  | pending : Passes (contextTests registry c s false) → s.pending = some raw →
      SealJudgment registry store c s request (refused c s (.seal request) .s1)
  | missing : Passes (contextTests registry c s false) → s.pending = none →
      request.trace.mapM (Transaction.resolve store) = none →
      SealJudgment registry store c s request (refused c s (.seal request) .s2)
  | digest : Passes (contextTests registry c s false) → s.pending = none →
      request.trace.mapM (Transaction.resolve store) = some rows →
      payloadsMatch request.trace rows = false →
      SealJudgment registry store c s request (refused c s (.seal request) .s3)
  | replayRefused : LoadedTrace registry store c s request rows →
      Replay registry c rows (.refused cause) →
      SealJudgment registry store c s request (refused c s (.seal request) cause)
  | incomplete : LoadedTrace registry store c s request rows →
      Replay registry c rows (.point last (.send k raw)) →
      SealJudgment registry store c s request (refused c s (.seal request) .s4)
  | root : LoadedTrace registry store c s request rows →
      Replay registry c rows (.point last (.done result)) → last.pending = none →
      last.prev ≠ request.root →
      SealJudgment registry store c s request (refused c s (.seal request) .s5)
  | results : LoadedTrace registry store c s request rows →
      Replay registry c rows (.point last (.done result)) → last.pending = none →
      last.prev = request.root →
      (resultsQ result ≠ request.resultsQ ∨ resultsQ request.results ≠ request.resultsQ) →
      SealJudgment registry store c s request (refused c s (.seal request) .s6)
  | accept : LoadedTrace registry store c s request rows →
      Replay registry c rows (.point last (.done result)) → last.pending = none →
      last.prev = request.root → resultsQ result = request.resultsQ →
      resultsQ request.results = request.resultsQ →
      SealJudgment registry store c s request (sealed s result)

inductive Admission {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core) :
    State → Event core → Outcome core → Prop where
  | local : LocalJudgment registry c s event out → Admission registry store c s event out
  | seal : SealJudgment registry store c s req out → Admission registry store c s (.seal req) out

structure Checkpoint where
  contextQ : Bytes
  prev : Bytes
  stateQ : Bytes
  state : State

def Checkpoint.valid (cp : Checkpoint) (s : State) : Prop :=
  cp.state = s ∧ cp.contextQ = s.contextQ ∧ cp.prev = s.prev ∧ cp.stateQ = s.q

inductive CheckpointPoint (core : Core) where
  | ready (step : Step core.stateType core.resultType)
  | waiting (k : core.stateType.Value) (t : Bytes)

/-- Reconstruct the continuation from the bound prefix. A checkpoint can
also name one admitted send beyond its last completed pair. -/
inductive CheckpointReplay {core : Core} (registry : Registry) (c : Context core)
    (pairs : List RawPair) (cp : Checkpoint) : CheckpointPoint core → Prop where
  | ready : Replay registry c pairs (.point s step) → cp.valid s →
      CheckpointReplay registry c pairs cp (.ready step)
  | waiting : Replay registry c pairs (.point s (.send k raw)) →
      Passes (sendTests registry c s raw) → cp.valid (s.afterSend raw) →
      CheckpointReplay registry c pairs cp (.waiting k raw)

end Effect.ABI
