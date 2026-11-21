import Effect.Context

namespace Effect.ABI

open Format Wire

def modeValid (mode : Nat) : Bool :=
  mode &&& 0x53 == mode && mode % 4 != 3

def modeReads (mode : Nat) : Bool := mode % 4 == 0 || mode % 4 == 2

def modeWrites (mode : Nat) : Bool := mode % 4 == 1 || mode % 4 == 2

inductive Phase where
  | fresh | versioned | attached | ended | faulted
  deriving DecidableEq, Repr

def Phase.code : Phase → I64
  | .fresh => 0 | .versioned => 1 | .attached => 2 | .ended => 3 | .faulted => 4

structure Fid where
  path : Path
  qid : Bytes
  opened : Option I64
  iounit : I64
  dirOffset : Bytes
  deriving DecidableEq, Repr

def Fid.schema : Schema := record
  [("path", .list .bytes), ("qid", .bytes), ("opened", .option .i64), ("iounit", .i64),
    ("dir_offset", .bytes)]

def Fid.value (f : Fid) : Fid.schema.Value := (f.path, f.qid, f.opened, f.iounit, f.dirOffset, ())

def Fid.unopened (path : Path) (qid : Wire.Qid) : Fid :=
  ⟨path, qid.bytes, none, 0, List.replicate 8 0⟩

def Fid.qidValue (fid : Fid) : Option Wire.Qid := decodeQid fid.qid

def Fid.directory (f : Fid) : Bool := f.qidValue.any Wire.Qid.directory

def Fid.openAs (f : Fid) (qid : Wire.Qid) (mode iounit : Nat) : Fid :=
  { f with qid := qid.bytes, opened := some (UInt64.ofNat mode), iounit := UInt64.ofNat iounit }

def Fid.valid (f : Fid) : Bool :=
  f.path.all newName && f.qidValue.isSome && f.dirOffset.length == 8 && f.iounit.toNat < 2^32 &&
  match f.opened with
  | none => f.iounit == 0 && littleEndian f.dirOffset == 0
  | some mode => modeValid mode.toNat && (!f.directory || mode == 0)

structure State where
  contextQ : Bytes
  phase : I64
  msize : I64
  sentSteps : I64
  root : Option Fid
  work : Option Fid
  pending : Option Bytes
  prev : Bytes
  deriving DecidableEq, Repr

def State.schema : Schema := record
  [("context_q", .bytes), ("phase", .i64), ("msize", .i64), ("sent_steps", .i64),
    ("root", .option Fid.schema), ("work", .option Fid.schema), ("pending", .option .bytes),
    ("prev", .bytes)]

def State.value (s : State) : State.schema.Value :=
  (s.contextQ, s.phase, s.msize, s.sentSteps, s.root.map Fid.value, s.work.map Fid.value,
    s.pending, s.prev, ())

def State.q (s : State) : Bytes := Format.q State.schema s.value

def State.pre : State := ⟨[], 0, 0, 0, none, none, none, []⟩

def State.opening {core : Core} (c : Context core) : State :=
  { State.pre with contextQ := c.q, prev := c.openingQ }

def State.isPhase (s : State) (p : Phase) : Bool := s.phase == p.code

def State.effective (s : State) (profile : Profile) : Nat :=
  if s.msize == 0 then profile.offer.toNat else s.msize.toNat

def State.fid (s : State) : Nat → Option Fid
  | 0 => s.root
  | 1 => s.work
  | _ => none

def State.putFid (s : State) (fid : Nat) (value : Option Fid) : State :=
  match fid with
  | 0 => { s with root := value }
  | 1 => { s with work := value }
  | _ => s

def State.pendingFrame (s : State) : Option (Wire.Frame Wire.Request) := s.pending.bind decodeT

def _root_.Effect.Wire.Request.primaryFid : Wire.Request → Option Nat
  | .version .. | .auth .. | .flush .. => none
  | .attach fid .. | .walk fid .. | .openFile fid .. | .create fid ..
  | .read fid .. | .write fid .. | .clunk fid | .remove fid | .stat fid
  | .wstat fid .. => some fid

def _root_.Effect.Wire.Request.requiredFid (req : Wire.Request) : Option Nat :=
  match req with
  | .attach .. => none
  | _ => req.primaryFid

def _root_.Effect.Wire.Request.expectedTag (req : Wire.Request) : Nat := if req.code == 100 then noTag else 0

def _root_.Effect.Wire.Request.fidsValid (req : Wire.Request) (s : State) : Bool :=
  (req.primaryFid.all (fun fid => fid ≤ 1)) &&
  match req with
  | .walk _ newFid _ => newFid == 1
  | .openFile fid _ | .create fid .. | .read fid .. | .write fid .. | .remove fid => fid == 1
  | .clunk fid => fid != 0 || s.work.isNone
  | _ => true

def _root_.Effect.Wire.Request.phaseValid (req : Wire.Request) (s : State) : Bool :=
  match req with
  | .version .. => s.isPhase .fresh && s.sentSteps == 0
  | .attach .. => s.isPhase .versioned
  | .auth .. | .flush .. => false
  | _ => s.isPhase .attached

def State.shapeValid {core : Core} (c : Context core) (s : State) (opening : Bool) : Bool :=
  if opening && s == State.pre then true else
  s.contextQ.length == 32 && s.contextQ == c.q && s.prev.length == 32 &&
  s.sentSteps.toNat ≤ c.profile.maxSteps.toNat &&
  s.root.all (fun f => f.valid && f.path.isEmpty && f.directory && f.opened.isNone) &&
  s.work.all Fid.valid &&
  if s.isPhase .fresh then
    s.msize == 0 && s.root.isNone && s.work.isNone &&
    s.sentSteps == (if s.pending.isSome then 1 else 0)
  else
    256 ≤ s.msize.toNat && s.msize.toNat ≤ c.profile.offer.toNat &&
    if s.isPhase .versioned then
      1 + (if s.pending.isSome then 1 else 0) ≤ s.sentSteps.toNat && s.root.isNone && s.work.isNone
    else if s.isPhase .attached then
      2 + (if s.pending.isSome then 1 else 0) ≤ s.sentSteps.toNat && s.root.isSome
    else
      s.isPhase .ended && s.root.isNone && s.work.isNone && s.pending.isNone

structure RuntimeState where
  semantic : State
  cache : List (Bytes × Bytes)
  diagnostic : String

def sigma (s : RuntimeState) : State := s.semantic

end Effect.ABI
