import Effect.ProcTrace

namespace Effect.Wire

structure Qid where
  kind : Nat
  version : Nat
  path : Nat
  deriving DecidableEq, Repr

def Qid.directory (q : Qid) : Bool := q.kind / 128 % 2 == 1

structure Stat where
  kind : Nat
  dev : Nat
  qid : Qid
  mode : Nat
  atime : Nat
  mtime : Nat
  length : Nat
  name : Bytes
  uid : Bytes
  gid : Bytes
  muid : Bytes
  deriving DecidableEq, Repr

inductive Request where
  | version (msize : Nat) (version : Bytes)
  | auth (afid : Nat) (uname aname : Bytes)
  | attach (fid afid : Nat) (uname aname : Bytes)
  | flush (oldTag : Nat)
  | walk (fid newFid : Nat) (names : List Bytes)
  | openFile (fid mode : Nat)
  | create (fid : Nat) (name : Bytes) (perm mode : Nat)
  | read (fid offset count : Nat)
  | write (fid offset : Nat) (data : Bytes)
  | clunk (fid : Nat)
  | remove (fid : Nat)
  | stat (fid : Nat)
  | wstat (fid : Nat) (stat : Stat)
  deriving DecidableEq, Repr

inductive Reply where
  | version (msize : Nat) (version : Bytes)
  | auth (qid : Qid)
  | attach (qid : Qid)
  | error (ename : Bytes)
  | flush
  | walk (qids : List Qid)
  | openFile (qid : Qid) (iounit : Nat)
  | create (qid : Qid) (iounit : Nat)
  | read (data : Bytes)
  | write (count : Nat)
  | clunk
  | remove
  | stat (stat : Stat)
  | wstat
  deriving DecidableEq, Repr

structure Frame (α : Type) where
  tag : Nat
  body : α
  deriving DecidableEq, Repr

def littleEndian : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * littleEndian bs

def littleEndianBytes (width val : Nat) : Bytes :=
  match width with
  | 0 => []
  | n + 1 => UInt8.ofNat (val % 256) :: littleEndianBytes n (val / 256)

def validText (s : Bytes) : Bool :=
  !s.contains 0 && (String.fromUTF8? ⟨s.toArray⟩).isSome

abbrev Decoder := StateT Bytes Option

private def reject : Decoder α := fun _ => none

private def takeBytes (n : Nat) : Decoder Bytes := do
  let (head, tail) := (← get : Bytes).splitAt n
  if head.length ≠ n then reject else
    set tail
    pure head

private def uint (width : Nat) : Decoder Nat := littleEndian <$> takeBytes width

private def text : Decoder Bytes := do
  let bytes ← takeBytes (← uint 2)
  if validText bytes then pure bytes else reject

private def exact (decode : Decoder α) (bytes : Bytes) : Option α := do
  let (value, rest) ← decode.run bytes
  if rest.isEmpty then some value else none

private def sized (decode : Decoder α) : Decoder α := do
  let bytes ← takeBytes (← uint 2)
  fun rest => (exact decode bytes).map (·, rest)

private def counted (decode : Decoder α) (width : Nat) : Decoder (List α) := do
  let count ← uint width
  loop count []
where
  loop : Nat → List α → Decoder (List α)
    | 0, acc => pure acc.reverse
    | n + 1, acc => do
      let next ← decode
      loop n (next :: acc)

private def qid : Decoder Qid := do
  return ⟨← uint 1, ← uint 4, ← uint 8⟩

def decodeQid : Bytes → Option Qid := exact qid

def Qid.bytes (q : Qid) : Bytes :=
  littleEndianBytes 1 q.kind ++ littleEndianBytes 4 q.version ++ littleEndianBytes 8 q.path

private def statEntry : Decoder Stat := sized do
  return ⟨← uint 2, ← uint 4, ← qid, ← uint 4, ← uint 4, ← uint 4, ← uint 8,
    ← text, ← text, ← text, ← text⟩

def directoryEntries (bytes : Bytes) : Bool := loop bytes.length bytes
where
  loop : Nat → Bytes → Bool
    | _, [] => true
    | 0, _ => false
    | fuel + 1, bytes =>
      match statEntry.run bytes with
      | none => false
      | some (_, rest) => loop fuel rest

private def request (kind : Nat) : Decoder Request := do
  match kind with
  | 100 => return .version (← uint 4) (← text)
  | 102 => return .auth (← uint 4) (← text) (← text)
  | 104 => return .attach (← uint 4) (← uint 4) (← text) (← text)
  | 108 => return .flush (← uint 2)
  | 110 => return .walk (← uint 4) (← uint 4) (← counted text 2)
  | 112 => return .openFile (← uint 4) (← uint 1)
  | 114 => return .create (← uint 4) (← text) (← uint 4) (← uint 1)
  | 116 => return .read (← uint 4) (← uint 8) (← uint 4)
  | 118 => return .write (← uint 4) (← uint 8) (← takeBytes (← uint 4))
  | 120 => return .clunk (← uint 4)
  | 122 => return .remove (← uint 4)
  | 124 => return .stat (← uint 4)
  | 126 => return .wstat (← uint 4) (← sized statEntry)
  | _ => reject

private def reply (kind : Nat) : Decoder Reply := do
  match kind with
  | 101 => return .version (← uint 4) (← text)
  | 103 => return .auth (← qid)
  | 105 => return .attach (← qid)
  | 107 => return .error (← text)
  | 109 => return .flush
  | 111 => return .walk (← counted qid 2)
  | 113 => return .openFile (← qid) (← uint 4)
  | 115 => return .create (← qid) (← uint 4)
  | 117 => return .read (← takeBytes (← uint 4))
  | 119 => return .write (← uint 4)
  | 121 => return .clunk
  | 123 => return .remove
  | 125 => return .stat (← sized statEntry)
  | 127 => return .wstat
  | _ => reject

private def frame (body : Nat → Decoder α) (raw : Bytes) : Option (Frame α) :=
  exact (do
    let size ← uint 4
    if size < 7 || size != raw.length then reject else
      let kind ← uint 1
      let tag ← uint 2
      return ⟨tag, ← body kind⟩) raw

def decodeT : Bytes → Option (Frame Request) := frame request

def decodeR : Bytes → Option (Frame Reply) := frame reply

def Request.code : Request → Nat
  | .version .. => 100
  | .auth .. => 102
  | .attach .. => 104
  | .flush .. => 108
  | .walk .. => 110
  | .openFile .. => 112
  | .create .. => 114
  | .read .. => 116
  | .write .. => 118
  | .clunk .. => 120
  | .remove .. => 122
  | .stat .. => 124
  | .wstat .. => 126

def Reply.code : Reply → Nat
  | .version .. => 101
  | .auth .. => 103
  | .attach .. => 105
  | .error .. => 107
  | .flush => 109
  | .walk .. => 111
  | .openFile .. => 113
  | .create .. => 115
  | .read .. => 117
  | .write .. => 119
  | .clunk => 121
  | .remove => 123
  | .stat .. => 125
  | .wstat => 127

end Effect.Wire
