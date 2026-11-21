import Effect.Wire

/-! A checked frame builder for experiments. The decoder has its own
wire inventory and does not depend on these construction functions. -/
namespace Effect.Wire

namespace Build

def uint (width n : Nat) : Option Bytes :=
  if n < 256^width then some (littleEndianBytes width n) else none

def text (bytes : Bytes) : Option Bytes := do
  if !validText bytes then none else
    return (← uint 2 bytes.length) ++ bytes

def data (bytes : Bytes) : Option Bytes := do
  return (← uint 4 bytes.length) ++ bytes

def qid (q : Qid) : Option Bytes := do
  return (← uint 1 q.kind) ++ (← uint 4 q.version) ++ (← uint 8 q.path)

def stat (s : Stat) : Option Bytes := do
  let body := (← uint 2 s.kind) ++ (← uint 4 s.dev) ++ (← qid s.qid) ++
    (← uint 4 s.mode) ++ (← uint 4 s.atime) ++ (← uint 4 s.mtime) ++ (← uint 8 s.length) ++
    (← text s.name) ++ (← text s.uid) ++ (← text s.gid) ++ (← text s.muid)
  return (← uint 2 body.length) ++ body

private def wrappedStat (s : Stat) : Option Bytes := do
  let raw ← stat s
  return (← uint 2 raw.length) ++ raw

private def vector (xs : List α) (f : α → Option Bytes) : Option Bytes := do
  return (← uint 2 xs.length) ++ (← xs.mapM f).flatten

def frame (code tag : Nat) (payload : Bytes) : Option Bytes := do
  return (← uint 4 (payload.length + 7)) ++ (← uint 1 code) ++ (← uint 2 tag) ++ payload

def requestBody : Request → Option Bytes
  | .version msize version => do return (← uint 4 msize) ++ (← text version)
  | .auth afid uname aname => do return (← uint 4 afid) ++ (← text uname) ++ (← text aname)
  | .attach fid afid uname aname => do
    return (← uint 4 fid) ++ (← uint 4 afid) ++ (← text uname) ++ (← text aname)
  | .flush oldTag => uint 2 oldTag
  | .walk fid newFid names => do
    return (← uint 4 fid) ++ (← uint 4 newFid) ++ (← vector names text)
  | .openFile fid mode => do return (← uint 4 fid) ++ (← uint 1 mode)
  | .create fid name perm mode => do
    return (← uint 4 fid) ++ (← text name) ++ (← uint 4 perm) ++ (← uint 1 mode)
  | .read fid offset count => do
    return (← uint 4 fid) ++ (← uint 8 offset) ++ (← uint 4 count)
  | .write fid offset raw => do return (← uint 4 fid) ++ (← uint 8 offset) ++ (← data raw)
  | .clunk fid | .remove fid | .stat fid => uint 4 fid
  | .wstat fid info => do return (← uint 4 fid) ++ (← wrappedStat info)

def replyBody : Reply → Option Bytes
  | .version msize version => do return (← uint 4 msize) ++ (← text version)
  | .auth q | .attach q => qid q
  | .error ename => text ename
  | .walk qids => vector qids qid
  | .openFile q iounit | .create q iounit => do return (← qid q) ++ (← uint 4 iounit)
  | .read raw => data raw
  | .write count => uint 4 count
  | .stat info => wrappedStat info
  | .flush | .clunk | .remove | .wstat => some []

def request (t : Request) (tag : Nat) : Option Bytes := do frame t.code tag (← requestBody t)

def reply (r : Reply) (tag : Nat) : Option Bytes := do frame r.code tag (← replyBody r)

end Build
end Effect.Wire
