import Effect.Judgment

/-! Executable derivations of the EFFECT-ABI-0 judgments.
The dependent branch result follows MSTNF3FormMWE at
residua-labs/MST-NF@4432a34a62fade06d98e33b29b13b18e57604f9b. -/
namespace Effect.ABI

private theorem passesNever (p : Passes (⟨cause, true⟩ :: rest)) : False := by
  cases p with
  | cons h _ => cases h

private theorem replyPresent {core : Core} {registry : Registry} {c : Context core}
    {s : State} {raw : Bytes} (p : Passes (receiveTests registry c s raw)) :
    Wire.decodeR raw ≠ none := by
  intro h
  have tail := p.drop (contextTests registry c s false)
  change Passes (match Wire.decodeR raw with
    | none => [⟨.r1, true⟩]
    | some _ => _) at tail
  rw [h] at tail
  exact passesNever tail

private theorem pendingPresent {core : Core} {registry : Registry} {c : Context core}
    {s : State} {raw : Bytes} (p : Passes (receiveTests registry c s raw))
    (decoded : Wire.decodeR raw = some r) : s.pendingFrame ≠ none := by
  intro h
  unfold receiveTests at p
  rw [decoded] at p
  have afterSize := (p.drop (contextTests registry c s false)).tail
  rw [h] at afterSize
  exact passesNever afterSize

structure ReceiveFrames (s : State) (rawR : Bytes) where
  rawT : Bytes
  t : Wire.Frame Wire.Request
  r : Wire.Frame Wire.Reply
  pending : s.pending = some rawT
  request : Wire.decodeT rawT = some t
  reply : Wire.decodeR rawR = some r

private def receiveFrames {core : Core} {registry : Registry} {c : Context core}
    {s : State} {raw : Bytes} (p : Passes (receiveTests registry c s raw)) : ReceiveFrames s raw :=
  match hr : Wire.decodeR raw with
  | none => False.elim (replyPresent p hr)
  | some r =>
    match ht : s.pending with
    | none => False.elim (pendingPresent p hr (by simp [State.pendingFrame, ht]))
    | some rawT =>
      match hd : Wire.decodeT rawT with
      | none => False.elim (pendingPresent p hr (by simp [State.pendingFrame, ht, hd]))
      | some t => ⟨rawT, t, r, ht, hd, hr⟩

private theorem planPresent {core : Core} {registry : Registry} {c : Context core}
    {s : State} {opening : Bool} (p : Passes (contextTests registry c s opening)) :
    c.plan ≠ none := by
  intro h
  unfold contextTests at p
  rw [h] at p
  exact passesNever p.tail.tail.tail

namespace Monitor

def openSession {core : Core} (registry : Registry) (c : Context core) (s : State) :
    {out // LocalJudgment registry c s .openSession out} :=
  match certifyGuards (contextTests registry c s true) with
  | .pass p => ⟨opened c, .openSession p⟩
  | .refuse cause p => ⟨refused c s .openSession cause, .refuse p⟩

def send {core : Core} (registry : Registry) (c : Context core) (s : State) (raw : Bytes) :
    {out // LocalJudgment registry c s (.send raw) out} :=
  match certifyGuards (sendTests registry c s raw) with
  | .pass p => ⟨issued s raw, .send p⟩
  | .refuse cause p => ⟨refused c s (.send raw) cause, .refuse p⟩

def receive {core : Core} (registry : Registry) (c : Context core) (s : State) (raw : Bytes) :
    {out // LocalJudgment registry c s (.receive raw) out} :=
  match certifyGuards (receiveTests registry c s raw) with
  | .refuse cause p => ⟨refused c s (.receive raw) cause, .refuse p⟩
  | .pass p =>
    let frames := receiveFrames p
    ⟨committed s frames.rawT raw frames.t.body frames.r.body,
      .receive p frames.pending frames.request frames.reply⟩

def fault {core : Core} (registry : Registry) (c : Context core) (s : State)
    (obs : FaultObservation) : {out // LocalJudgment registry c s (.fault obs) out} :=
  match certifyGuards (localTests registry c s (.fault obs)) with
  | .refuse cause p => ⟨refused c s (.fault obs) cause, .refuse p⟩
  | .pass p => False.elim (passesNever (p.drop (contextTests registry c s false)))

def replayFrom {core : Core} (registry : Registry) (c : Context core) (plan : Plan core) :
    (s : State) → (step : Step core.stateType core.resultType) → (pairs : List RawPair) →
      {v // ReplayFrom registry c plan s step pairs v}
  | s, step, [] => ⟨.point s step, .boundary⟩
  | _, .done _, _ :: _ => ⟨.refused .s4, .extra⟩
  | s, .send k raw, pair :: rest =>
    if h : raw = pair.t then
      match certifyGuards (sendTests registry c s raw) with
      | .refuse cause p => ⟨.refused cause, .sendRefused h p⟩
      | .pass ps =>
        let sent := s.afterSend raw
        match certifyGuards (receiveTests registry c sent pair.r) with
        | .refuse cause p => ⟨.refused cause, .receiveRefused h ps p⟩
        | .pass pr =>
          let frames := receiveFrames pr
          have exactT : raw = frames.rawT := Option.some.inj frames.pending
          have tDecoded : Wire.decodeT raw = some frames.t := by
            rw [exactT]
            exact frames.request
          let next := sent.afterReceive raw pair.r frames.t.body frames.r.body
          let verdict := replayFrom registry c plan next (plan.invoke (some (k, pair.r))) rest
          ⟨verdict.val, .transaction h ps pr tDecoded frames.reply verdict.property⟩
    else ⟨.refused .s4, .requestMismatch h⟩

def replay {core : Core} (registry : Registry) (c : Context core) (pairs : List RawPair) :
    {v // Replay registry c pairs v} :=
  match certifyGuards (contextTests registry c State.pre true) with
  | .refuse cause p => ⟨.refused cause, .openRefused p⟩
  | .pass p =>
    match hp : c.plan with
    | none => False.elim (planPresent p hp)
    | some plan =>
      let verdict := replayFrom registry c plan (State.opening c) (plan.invoke none) pairs
      ⟨verdict.val, .start p hp verdict.property⟩

def replayFault {core : Core} (registry : Registry) (c : Context core) (pairs : List RawPair)
    (raw : Bytes) (obs : FaultObservation) : {v // FaultReplay registry c pairs raw obs v} :=
  match replay registry c pairs with
  | ⟨.refused cause, p⟩ => ⟨.inl cause, .prefixRefused p⟩
  | ⟨.point _ (.done _), p⟩ => ⟨.inl .s4, .extra p⟩
  | ⟨.point s (.send k next), p⟩ =>
    if h : next = raw then
      have same : Replay registry c pairs (.point s (.send k raw)) := by simpa only [h] using p
      match certifyGuards (sendTests registry c s raw) with
      | .refuse cause bad => ⟨.inl cause, .sendRefused same bad⟩
      | .pass ok =>
        let out := fault registry c (s.afterSend raw) obs
        ⟨.inr out.val, .observe same ok out.property⟩
    else ⟨.inl .s4, .mismatch p h⟩

private instance (cp : Checkpoint) (s : State) : Decidable (cp.valid s) :=
  inferInstanceAs (Decidable (cp.state = s ∧ cp.contextQ = s.contextQ ∧
    cp.prev = s.prev ∧ cp.stateQ = s.q))

def resumeCheckpoint {core : Core} (registry : Registry) (c : Context core) (pairs : List RawPair)
    (cp : Checkpoint) : Option {point // CheckpointReplay registry c pairs cp point} :=
  match replay registry c pairs with
  | ⟨.refused _, _⟩ => none
  | ⟨.point s step, p⟩ =>
    if h : cp.valid s then some ⟨.ready step, .ready p h⟩ else
      match step with
      | .done _ => none
      | .send k raw =>
        match certifyGuards (sendTests registry c s raw) with
        | .refuse .. => none
        | .pass ok =>
          if issued : cp.valid (s.afterSend raw) then some ⟨.waiting k raw, .waiting p ok issued⟩
          else none

end Monitor

private def ReplayBoundary.clear {core : Core} : ReplayBoundary core → Prop
  | .point s _ => s.pending = none
  | .refused _ => True

theorem ReplayFrom.pendingClear {core : Core} {registry : Registry} {c : Context core}
    {plan : Plan core} {s : State} {step : Step core.stateType core.resultType}
    {pairs : List RawPair} {v : ReplayBoundary core}
    (j : ReplayFrom registry c plan s step pairs v) (h : s.pending = none) :
    v.clear := by
  induction j with
  | boundary => exact h
  | transaction _ _ _ _ _ _ ih => exact ih rfl
  | _ => trivial

theorem Replay.pendingClear {core : Core} {registry : Registry} {c : Context core}
    {v : ReplayBoundary core} (j : Replay registry c pairs v) : v.clear := by
  cases j with
  | openRefused => trivial
  | start _ _ prefixReplay => exact prefixReplay.pendingClear rfl

namespace Monitor

def sealReceipt {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core) (s : State)
    (req : SealRequest core) : {out // Admission registry store c s (.seal req) out} :=
  let refuse := refused c s (.seal req)
  match certifyGuards (contextTests registry c s false) with
  | .refuse cause p => ⟨refuse cause, .local (.refuse p)⟩
  | .pass p =>
    match hp : s.pending with
    | some _ => ⟨refuse .s1, .seal (.pending p hp)⟩
    | none =>
      match hr : req.trace.mapM (Transaction.resolve store) with
      | none => ⟨refuse .s2, .seal (.missing p hp hr)⟩
      | some rows =>
        match hv : payloadsMatch req.trace rows with
        | false => ⟨refuse .s3, .seal (.digest p hp hr hv)⟩
        | true =>
          let loaded : LoadedTrace registry store c s req rows := ⟨p, hp, hr, hv⟩
          match replay registry c rows with
          | ⟨.refused cause, j⟩ => ⟨refuse cause, .seal (.replayRefused loaded j)⟩
          | ⟨.point _ (.send ..), j⟩ => ⟨refuse .s4, .seal (.incomplete loaded j)⟩
          | ⟨.point last (.done result), j⟩ =>
            if root : last.prev = req.root then
              if q : resultsQ result = req.resultsQ then
                if expected : resultsQ req.results = req.resultsQ then
                  ⟨sealed s result, .seal (.accept loaded j j.pendingClear root q expected)⟩
                else ⟨refuse .s6, .seal (.results loaded j j.pendingClear root (.inr expected))⟩
              else ⟨refuse .s6, .seal (.results loaded j j.pendingClear root (.inl q))⟩
            else ⟨refuse .s5, .seal (.root loaded j j.pendingClear root)⟩

private def evaluate {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (s : State) : (event : Event core) → {out // Admission registry store c s event out}
  | .openSession => let v := openSession registry c s; ⟨v.val, .local v.property⟩
  | .send raw => let v := send registry c s raw; ⟨v.val, .local v.property⟩
  | .receive raw => let v := receive registry c s raw; ⟨v.val, .local v.property⟩
  | .fault obs => let v := fault registry c s obs; ⟨v.val, .local v.property⟩
  | .seal req => sealReceipt registry store c s req

end Monitor

theorem LocalJudgment.refusal {core : Core} {registry : Registry} {c : Context core}
    {s : State} {event : Event core} {out : Outcome core}
    (j : LocalJudgment registry c s event out) (r : out.residue = some cause) :
    out = refused c s event cause := by
  cases j <;> simp_all [opened, issued, committed, refused]

theorem Admission.refusal {core : Core} {registry : Registry} {store : ObjectStore}
    {c : Context core} {s : State} {event : Event core} {out : Outcome core}
    (j : Admission registry store c s event out)
    (r : out.residue = some cause) :
    out = refused c s event cause := by
  cases j with
  | «local» j => exact j.refusal r
  | «seal» j => cases j <;> simp_all [refused, sealed]

namespace Monitor

structure RawInput (core : Core) where
  state : RuntimeState
  event : Event core

structure Class (core : Core) where
  state : State
  event : Event core

def classify {core : Core} (raw : RawInput core) : Class core := ⟨sigma raw.state, raw.event⟩

def Class.embed {core : Core} (canonical : Class core) : RawInput core :=
  ⟨⟨canonical.state, [], ""⟩, canonical.event⟩

def Lambda {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) :
    Sum {out // Admission registry store c input.state input.event out ∧ out.residue = none}
      {cause // Admission registry store c input.state input.event
        (refused c input.state input.event cause)} :=
  let v := evaluate registry store c input.state input.event
  match h : v.val.residue with
  | none => .inl ⟨v.val, v.property, h⟩
  | some cause => .inr ⟨cause, v.property.refusal h ▸ v.property⟩

def stepCertified {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : {out // Admission registry store c input.state input.event out} :=
  match Lambda registry store c input with
  | .inl r => ⟨r.val, r.property.1⟩
  | .inr f => ⟨refused c input.state input.event f.val, f.property⟩

def step {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : Outcome core := (stepCertified registry store c input).val

def run {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (raw : RawInput core) : Outcome core := step registry store c (classify raw)

def residue? {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : Option Residue :=
  match Lambda registry store c input with
  | .inl _ => none
  | .inr f => some f.val

def admit {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : Bool := (residue? registry store c input).isNone

def representative {core : Core} (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : Option (Outcome core) :=
  match Lambda registry store c input with
  | .inl r => some r.val
  | .inr _ => none

end Monitor
end Effect.ABI
