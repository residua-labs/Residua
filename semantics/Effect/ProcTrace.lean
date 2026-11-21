import Std

/-!
Finite stateful FFI semantics for the value boundary of `lib/Proc.rsd`.
The state and observation interface follows CakeML's FFI model
(Guéneau et al., ESOP 2017, https://cakeml.org/esop17.pdf).
An oracle observes the routed authority and the complete request. It supplies
the read events for that request and advances its own state. The pure machine
exposes a successful result, a named failure, or a request at a finite cut.

The pure entry and dispatch are fixed for a program. Their correspondence
with execution below the WAIST-0 boundary is a separate obligation (E5).
-/

namespace Effect

abbrev Bytes := List UInt8

def ascii (s : String) : Bytes := s.toUTF8.data.toList

structure Digest where
  bytes : Bytes
  width : bytes.length = 32
  deriving DecidableEq, Repr

inductive Device where
  | env | fs | store | clock | cmd
  deriving DecidableEq, Repr

def Device.token : Device → Bytes
  | .env => ascii "env"
  | .fs => ascii "fs"
  | .store => ascii "store"
  | .clock => ascii "clock"
  | .cmd => ascii "cmd"

structure Authority where
  device : Device
  contract : Digest
  config : Digest
  deriving DecidableEq, Repr

structure Context where
  namespaceQ : Digest
  profileQ : Digest
  planQ : Digest
  resolve : Device → Option Authority
  invocationFuel : Nat
  continuationBudget : Nat := 600
  hostSteps : Nat := 100000

structure Request where
  authority : Authority
  frame : Bytes
  deriving DecidableEq, Repr

structure Cont where
  code : Int
  ints : List Int := []
  bytes : List Bytes := []
  deriving DecidableEq, Repr

inductive Proc where
  | done (result : Bytes)
  | await (routed : Bytes) (frames : List Cont)
  | resume (value : Bytes) (frames : List Cont)
  | refuse (residue : Bytes)
  | invalid
  deriving DecidableEq, Repr

def Proc.seq (p : Proc) (older : List Cont) : Proc :=
  match p with
  | .done value =>
    match older with
    | [] => p
    | _ :: _ => .resume value older
  | .await bytes frames => .await bytes (frames ++ older)
  | .resume bytes frames => .resume bytes (frames ++ older)
  | .refuse _ | .invalid => p

def Proc.bind (p : Proc) (k : Cont) : Proc :=
  p.seq [k]

inductive TransportFault where
  | unavailable | endOfStream | truncated | closed | timeout | unknownEvent
  | badFrameSize | msizeExceeded | sizeMismatch
  deriving DecidableEq, Repr

inductive InvocationFailure where
  | fuel | capacity | stuck | trap | refused (residue : Bytes)
  deriving DecidableEq, Repr

inductive Terminal where
  | success (exit : UInt8) (stdout : Bytes)
  | refused (residue : Bytes)
  | invocation (failure : InvocationFailure)
  | continuationBudget | hostStepLimit | invalidProc | invalidExit | unresolvedDevice
  | transport (fault : TransportFault)
  deriving DecidableEq, Repr

inductive ReadEvent where
  | data (bytes : Bytes)
  | eof (bytes : Bytes)
  | closed (bytes : Bytes)
  | timeout (bytes : Bytes)
  | unknownEvent (tag : Int) (bytes : Bytes)
  deriving DecidableEq, Repr

/-- `resume` is the pure call input to the warm `drive9`. -/
inductive Call where
  | cold (p : Proc)
  | afterSend (p : Proc)
  | resume (p : Proc) (need : Nat) (acc : Bytes) (reply : ReadEvent)

structure Program where
  initial : Nat → Except InvocationFailure Proc
  apply : Cont → Bytes → Proc
  invoke : Nat → Call → Except InvocationFailure Unit

private def splitRoute (wire : Bytes) (name : Bytes) : Option (Bytes × Bytes) :=
  match wire with
  | [] => none
  | b :: tail =>
    if b == 10 then some (name.reverse, tail) else splitRoute tail (b :: name)

def route (ctx : Context) (wire : Bytes) : Option Request := do
  let (name, frame) ← splitRoute wire []
  let dev ← [Device.env, .fs, .store, .clock, .cmd].find? (·.token == name)
  let authority ← ctx.resolve dev
  if authority.device = dev then some ⟨authority, frame⟩ else none

private def feed (p : Program) (value : Bytes) : List Cont → Proc
  | [] => p.apply ⟨-1, [], []⟩ value
  | k :: older => (p.apply k value).seq older

inductive Action where
  | stop (outcome : Terminal)
  | send (wire : Bytes) (frames : List Cont)

def settle (p : Program) : Nat → Proc → Action
  | 0, _ => .stop .continuationBudget
  | n + 1, proc =>
    match proc with
    | .done [] => .stop .invalidExit
    | .done (exit :: stdout) => .stop (.success exit stdout)
    | .await wire frames => .send wire frames
    | .resume value frames => settle p n (feed p value frames)
    | .refuse residue => .stop (.refused residue)
    | .invalid => .stop .invalidProc

structure Pending where
  request : Request
  proc : Proc
  remaining : Nat

inductive Frontier where
  | terminal (outcome : Terminal)
  | request (request : Request)
  | reading (request : Request) (received remaining : Nat)
  deriving DecidableEq, Repr

inductive Boundary where
  | stop (outcome : Terminal)
  | send (pending : Pending)
  | reading (request : Request) (received remaining : Nat)

def Boundary.frontier : Boundary → Frontier
  | .stop result => .terminal result
  | .send pending => .request pending.request
  | .reading request received remaining => .reading request received remaining

private def expose (ctx : Context) (remaining : Nat) : Action → Boundary
  | .stop o => .stop o
  | .send wire frames =>
    match route ctx wire with
    | none => .stop .unresolvedDevice
    | some request => .send ⟨request, .await wire frames, remaining⟩

def start (p : Program) (ctx : Context) : Boundary :=
  match p.initial ctx.invocationFuel with
  | .error failure => .stop (.invocation failure)
  | .ok proc =>
    match ctx.hostSteps with
    | 0 => .stop .hostStepLimit
    | n + 1 =>
      match p.invoke ctx.invocationFuel (.cold proc) with
      | .error failure => .stop (.invocation failure)
      | .ok () => expose ctx n (settle p ctx.continuationBudget proc)

private def uintLE : Bytes → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * uintLE rest

inductive FrameStep where
  | read (need : Nat) (acc : Bytes)
  | frame (bytes : Bytes)
  | fault (fault : TransportFault)

private def frameStep (need : Nat) (acc : Bytes) : ReadEvent → FrameStep
  | .eof bytes => .fault (if acc.isEmpty && bytes.isEmpty then .endOfStream else .truncated)
  | .closed _ => .fault .closed
  | .timeout _ => .fault .timeout
  | .unknownEvent _ _ => .fault .unknownEvent
  | .data bytes =>
    let all := acc ++ bytes
    if all.length < need then .read need all
    else
      let size := if need == 4 then uintLE (all.take 4) else need
      if size < 7 then .fault .badFrameSize
      else if size > 8192 then .fault .msizeExceeded
      else if all.length == size then .frame all
      else if all.length < size then .read size all
      else .fault .sizeMismatch

inductive Observation where
  | connectFailed
  | reads (events : List ReadEvent)
  deriving DecidableEq, Repr

inductive TapeError where
  | requestMismatch (expected recorded : Request)
  | missing (next : Frontier)
  | extra
  | extraRead
  deriving DecidableEq, Repr

private def receive (p : Program) (ctx : Context) (pending : Pending) :
    List ReadEvent → Nat → Nat → Bytes → Except TapeError Boundary
  | events, 0, _, _ =>
    if events.isEmpty then .ok (.stop .hostStepLimit) else .error .extraRead
  | [], _ + 1, need, acc => .ok (.reading pending.request acc.length (need - acc.length))
  | event :: tail, n + 1, need, acc =>
    let finish (boundary : Boundary) :=
      if tail.isEmpty then .ok boundary else .error .extraRead
    match p.invoke ctx.invocationFuel (.resume pending.proc need acc event) with
    | .error failure => finish (.stop (.invocation failure))
    | .ok () =>
      match frameStep need acc event with
      | .fault fault => finish (.stop (.transport fault))
      | .frame bytes =>
        match pending.proc with
        | .await _ frames => finish (expose ctx n (settle p ctx.continuationBudget (feed p bytes frames)))
        | _ => finish (.stop .invalidProc)
      | .read next acc' => receive p ctx pending tail n next acc'

def deliver (p : Program) (ctx : Context) (pending : Pending) :
    Observation → Except TapeError Boundary
  | .connectFailed => .ok (.stop (.transport .unavailable))
  | .reads events =>
    let finish (boundary : Boundary) :=
      if events.isEmpty then .ok boundary else .error .extraRead
    match pending.remaining with
    | 0 => finish (.stop .hostStepLimit)
    | n + 1 =>
      match p.invoke ctx.invocationFuel (.afterSend pending.proc) with
      | .error failure => finish (.stop (.invocation failure))
      | .ok () => receive p ctx pending events n 4 []

structure Event where
  request : Request
  observation : Observation
  deriving DecidableEq, Repr

abbrev Trace := List Event
abbrev Oracle (State : Type) := State → Request → Option (Observation × State)

/-- Finite execution of the program with a stateful oracle. None marks an
observation cut at the emitted T; it is different from carrying a fault. -/
inductive Execution (p : Program) (ctx : Context) {State : Type} (oracle : Oracle State) :
    Boundary → State → Trace → Frontier → State → Prop where
  | stopped (s result) : Execution p ctx oracle (.stop result) s [] (.terminal result) s
  | reading (s request received remaining) :
      Execution p ctx oracle (.reading request received remaining) s [] (.reading request received remaining) s
  | suspended (s pending) :
      oracle s pending.request = none →
      Execution p ctx oracle (.send pending) s [] (.request pending.request) s
  | observed (s pending observation next s' s'' trace out) :
      oracle s pending.request = some (observation, s') →
      deliver p ctx pending observation = .ok next →
      Execution p ctx oracle next s' trace out s'' →
      Execution p ctx oracle (.send pending) s (⟨pending.request, observation⟩ :: trace) out s''

def interpret (p : Program) (ctx : Context) :
    List Observation → Boundary → Except TapeError (Trace × Frontier)
  | [], boundary => .ok ([], boundary.frontier)
  | observation :: tail, .send pending => do
    let next ← deliver p ctx pending observation
    let (trace, out) ← interpret p ctx tail next
    pure (⟨pending.request, observation⟩ :: trace, out)
  | _ :: _, _ => .error .extra

def replay (p : Program) (ctx : Context) : Trace → Boundary → Except TapeError Frontier
  | [], boundary => .ok boundary.frontier
  | event :: tail, .send pending =>
    if pending.request = event.request then do
      let next ← deliver p ctx pending event.observation
      replay p ctx tail next
    else .error (.requestMismatch pending.request event.request)
  | _ :: _, _ => .error .extra

def replayComplete (p : Program) (ctx : Context) (trace : Trace) : Except TapeError Terminal := do
  match ← replay p ctx trace (start p ctx) with
  | .terminal o => pure o
  | next => .error (.missing next)

theorem interpret_execution {p ctx State oracle boundary s trace out s'}
    (h : @Execution p ctx State oracle boundary s trace out s') :
    interpret p ctx (trace.map Event.observation) boundary = .ok (trace, out) := by
  induction h with
  | stopped | reading | suspended => rfl
  | observed _ pending observation next _ _ trace _ _ delivered _ ih =>
    simp only [List.map_cons, interpret, delivered]
    change (fun a : Trace × Frontier => (⟨pending.request, observation⟩ :: a.1, a.2)) <$>
      interpret p ctx (trace.map Event.observation) next = _
    rw [ih] <;> rfl

theorem replay_execution {p ctx State oracle boundary s trace out s'}
    (h : @Execution p ctx State oracle boundary s trace out s') :
    replay p ctx trace boundary = .ok out := by
  induction h with
  | stopped | reading | suspended => rfl
  | observed _ _ _ _ _ _ _ _ _ delivered _ ih =>
    simp only [replay, if_pos rfl, delivered]
    exact ih

theorem replay_completed_execution {p ctx State oracle s trace out s'}
    (h : @Execution p ctx State oracle (start p ctx) s trace (.terminal out) s') :
    replayComplete p ctx trace = .ok out := by
  unfold replayComplete
  rw [replay_execution h]
  rfl

theorem observations_determine_execution {p ctx S₁ S₂ oracle₁ oracle₂ boundary s₁ s₂
    t₁ t₂ f₁ f₂ s₁' s₂'}
    (h₁ : @Execution p ctx S₁ oracle₁ boundary s₁ t₁ f₁ s₁')
    (h₂ : @Execution p ctx S₂ oracle₂ boundary s₂ t₂ f₂ s₂')
    (observations : t₁.map Event.observation = t₂.map Event.observation) :
    t₁ = t₂ ∧ f₁ = f₂ := by
  have same := interpret_execution h₁
  rw [observations, interpret_execution h₂] at same
  exact Prod.mk.inj (Except.ok.inj same).symm

#print axioms replay_execution
#print axioms replay_completed_execution
#print axioms observations_determine_execution

end Effect
