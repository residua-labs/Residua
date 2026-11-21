import Effect.Fixtures
import Effect.Monitor

/-! Finite experiments over reachable prefixes of the fixture program. -/
namespace Effect.ABI.Conformance

open Fixtures Wire Format

abbrev Objects := List (Bytes × Bytes)

def store (objects : Objects) : ObjectStore := fun q =>
  (objects.find? fun (key, _) => key == q).map Prod.snd

def step (c : Context fixtureCore) (s : State) (event : Event fixtureCore)
    (objects : Objects := []) : Outcome fixtureCore :=
  Monitor.step registry (store objects) c ⟨s, event⟩

def issuedAs (s : State) (t : Bytes) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .issue raw => out.residue.isNone && raw == t &&
      out.state == { s with pending := some t, sentSteps := s.sentSteps + 1 }
  | _ => false

def committedAs (s : State) (r : Bytes) (change : State → State) (out : Outcome fixtureCore) : Bool :=
  match s.pending, out.disposition with
  | some t, .commit pair => out.residue.isNone && pair == ⟨t, r⟩ &&
      out.state == { change s with pending := none, prev := Format.pair s.prev t r }
  | _, _ => false

def refusedAs (c : Context fixtureCore) (s : State) (event : Event fixtureCore) (cause : Residue)
    (out : Outcome fixtureCore) : Bool :=
  let closeAs := fun obs evidence =>
    evidence == CloseEvidence.mk (inputQ c s event) s.prev s.pending obs cause
  out.state == s && out.residue == some cause &&
    match event, out.disposition with
    | .receive r, .close evidence => closeAs (.reply r) evidence
    | .fault obs, .close evidence => closeAs (.fault obs) evidence
    | .openSession, .noIO | .send _, .noIO | .seal _, .noIO => true
    | _, _ => false

def openedAs (c : Context fixtureCore) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .noIO => out.residue.isNone && out.state == State.opening c
  | _ => false

def sealedAs (s : State) (out : Outcome fixtureCore) : Bool :=
  match out.disposition with
  | .seal result => out.residue.isNone && out.state == s &&
    (show Format.I64 from result) == 42
  | _ => false

inductive Point where
  | pre
  | ready (prefixPairs : List RawPair)
  | waiting (prefixPairs : List RawPair) (raw : Bytes)

def Point.pairs : Point → List RawPair
  | .pre => []
  | .ready pairs | .waiting pairs _ => pairs

def Point.project (c : Context fixtureCore) (point : Point)
    (event : Event fixtureCore) : Option State :=
  match point with
  | .pre => some State.pre
  | .ready pairs =>
    match (Monitor.replay registry c pairs).val, event with
    | .point s (.send _ next), .send raw => if raw == next then some s else none
    | .point _ (.done _), .send _ => none
    | .point s _, _ => some s
    | .refused _, _ => none
  | .waiting pairs t =>
    match (Monitor.replay registry c pairs).val with
    | .point s (.send _ next) =>
      if next != t then none else
      let out := step c s (.send t)
      if issuedAs s t out then some out.state else none
    | _ => none

inductive Expectation where
  | refuse (cause : Residue)
  | opened
  | issue (t : Bytes)
  | commit (r : Bytes) (change : State → State)
  | sealed

def Expectation.label : Expectation → String
  | .refuse cause => cause.label
  | .opened => "open"
  | .issue _ => "issue"
  | .commit .. => "commit"
  | .sealed => "seal"

def Expectation.check (c : Context fixtureCore) (s : State) (event : Event fixtureCore)
    (out : Outcome fixtureCore) : Expectation → Bool
  | .refuse cause => refusedAs c s event cause out
  | .opened => openedAs c out
  | .issue t => issuedAs s t out
  | .commit r change => committedAs s r change out
  | .sealed => sealedAs s out

structure Probe where
  context : Context fixtureCore
  point : Point
  event : Event fixtureCore
  expected : Expectation
  objects : Objects := []
  varyState : State → State := id
  premise : State → Bool := fun _ => true

def pairBytes (pairs : List RawPair) : List Bytes := pairs.flatMap (fun p => [p.t, p.r])

def Probe.inputQ (probe : Probe) (s : State) : Bytes :=
  Format.q (.list .bytes)
    ([probe.context.q, Effect.ABI.inputQ probe.context s probe.event,
      [if probe.context.ns.isSome then 1 else 0, if probe.context.plan.isSome then 1 else 0],
      [match probe.point with | .pre => 0 | .ready _ => 1 | .waiting .. => 2]] ++
      [Format.q (.list .bytes) (pairBytes probe.point.pairs)] ++
      probe.objects.flatMap (fun (key, bytes) => [key, bytes]))

structure Verdict where
  expected : String
  got : String
  witnessQ : Bytes
  ok : Bool

def Verdict.valid (v : Verdict) : Bool :=
  v.ok && v.expected == v.got && v.witnessQ.length == 32

private def dispositionLabel (out : Outcome fixtureCore) : String :=
  match out.residue, out.disposition with
  | some cause, _ => cause.label
  | none, .noIO => "open"
  | none, .issue _ => "issue"
  | none, .commit _ => "commit"
  | none, .seal _ => "seal"
  | none, .close _ => "close"

def Probe.run (probe : Probe) : Verdict :=
  match probe.point.project probe.context probe.event with
  | none => ⟨probe.expected.label, "unreachable-prefix", [], false⟩
  | some state =>
    let s := probe.varyState state
    let out := step probe.context s probe.event probe.objects
    ⟨probe.expected.label, dispositionLabel out, probe.inputQ s,
      probe.premise s && probe.expected.check probe.context s probe.event out⟩

def send (pairs : List RawPair) (t : Bytes) (expected : Expectation)
    (usage : Profile := profile) : Probe :=
  ⟨context (pairs.map RawPair.t ++ [t]) usage, .ready pairs, .send t, expected, [], id, fun _ => true⟩

def receive (pairs : List RawPair) (t r : Bytes) (expected : Expectation)
    (usage : Profile := profile) : Probe :=
  ⟨context (pairs.map RawPair.t ++ [t]) usage, .waiting pairs t, .receive r, expected, [], id, fun _ => true⟩

def commit (pairs : List RawPair) (t r : Bytes) (change : State → State := id)
    (usage : Profile := profile) : Probe :=
  receive pairs t r (.commit r change) usage

def fault (pairs : List RawPair) (t : Bytes) (obs : FaultObservation) (premise : State → Bool) : Probe :=
  { context := context (pairs.map RawPair.t ++ [t]), point := .waiting pairs t,
    event := .fault obs, expected := .refuse obs.cause, premise }

def rootFor (c : Context fixtureCore) (pairs : List RawPair) : Bytes :=
  pairs.foldl (fun prev p => Format.pair prev p.t p.r) c.openingQ

def receipt (c : Context fixtureCore) (pairs : List RawPair) : SealRequest fixtureCore :=
  ⟨pairs.map RawPair.inline, (42 : Format.I64), rootFor c pairs, Format.q .i64 (42 : Format.I64)⟩

def sealProbe (c : Context fixtureCore) (request : SealRequest fixtureCore) (expected : Expectation)
    (objects : Objects := []) : Probe :=
  { context := c, point := .ready [], event := .seal request, expected, objects }

def withRef (b : Bytes) (length : Nat := b.length) : FrameRef :=
  .reference (Format.q .bytes b) (UInt64.ofNat length)

/-- Shrink a counterexample in an ordered, finite domain only through inputs
that still satisfy the caller's applicability and target premise. -/
def shrink (candidates : List α) (premise failed : α → Bool) : Option α :=
  candidates.find? (fun candidate => premise candidate && failed candidate)

end Effect.ABI.Conformance
