import Effect.State

namespace Effect.ABI

open Wire

inductive Residue where
  | c1 | c2 | c3 | c4 | c5 | c6
  | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8 | t9 | t10 | t11 | t12 | t13 | t14 | t15
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10
  | f1 | f2 | f3
  | s1 | s2 | s3 | s4 | s5 | s6
  deriving DecidableEq, Repr

def Residue.label : Residue → String
  | .c1 => "nf_context_digest_invalid"
  | .c2 => "nf_namespace_invalid"
  | .c3 => "nf_profile_bounds_invalid"
  | .c4 => "nf_plan_invalid"
  | .c5 => "nf_state_invalid"
  | .c6 => "nf_session_already_open"
  | .t1 => "nf_t_malformed"
  | .t2 => "nf_t_not_in_profile"
  | .t3 => "nf_t_msize_exceeded"
  | .t4 => "nf_t_session_state"
  | .t5 => "nf_t_tag_busy"
  | .t6 => "nf_t_fid_unknown"
  | .t7 => "nf_t_fid_in_use"
  | .t8 => "nf_t_fid_mode"
  | .t9 => "nf_t_count_over_cap"
  | .t10 => "nf_t_steps_over_cap"
  | .t11 => "nf_t_attach_ns_mismatch"
  | .t12 => "nf_t_wstat_scope"
  | .t13 => "nf_t_walk_name_invalid"
  | .t14 => "nf_t_path_not_declared"
  | .t15 => "nf_t_device_grammar_invalid"
  | .r1 => "nf_r_malformed"
  | .r2 => "nf_r_msize_exceeded"
  | .r3 => "nf_r_without_request"
  | .r4 => "nf_r_tag_mismatch"
  | .r5 => "nf_r_type_mismatch"
  | .r6 => "nf_r_version_unsupported"
  | .r7 => "nf_r_msize_invalid"
  | .r8 => "nf_r_count_over_request"
  | .r9 => "nf_r_qid_inconsistent"
  | .r10 => "nf_r_device_contract_invalid"
  | .f1 => "nf_effect_step_timeout"
  | .f2 => "nf_effect_transport_failure"
  | .f3 => "nf_effect_frame_over_cap"
  | .s1 => "nf_receipt_pending_request"
  | .s2 => "nf_receipt_payload_missing"
  | .s3 => "nf_receipt_payload_digest_mismatch"
  | .s4 => "nf_receipt_request_mismatch"
  | .s5 => "nf_receipt_root_mismatch"
  | .s6 => "nf_receipt_results_mismatch"

structure Test where
  cause : Residue
  fails : Bool

inductive Passes : List Test → Prop where
  | nil : Passes []
  | cons : test.fails = false → Passes tests → Passes (test :: tests)

inductive First (cause : Residue) : List Test → Prop where
  | here : test.fails = true → test.cause = cause → First cause (test :: tests)
  | later : test.fails = false → First cause tests → First cause (test :: tests)

theorem Passes.tail (h : Passes (test :: tests)) : Passes tests := by
  cases h with
  | cons _ h => exact h

theorem Passes.drop (earlier : List Test) (h : Passes (earlier ++ suffix)) : Passes suffix := by
  induction earlier with
  | nil => exact h
  | cons _ _ ih => exact ih h.tail

theorem Passes.noFirst (p : Passes tests) (f : First cause tests) : False := by
  induction p with
  | nil => cases f
  | cons ok _ ih =>
    cases f with
    | here bad _ => simp_all
    | later _ f => exact ih f

theorem First.unique (a : First cause tests) (b : First other tests) : cause = other := by
  induction a with
  | here ha ea =>
    cases b with
    | here _ eb => exact ea.symm.trans eb
    | later hb _ => simp_all
  | later ha _ ih =>
    cases b with
    | here hb _ => simp_all
    | later _ b => exact ih b

/-- Evaluate the ordered tests and retain the premise of the selected rule. -/
inductive GuardVerdict (tests : List Test) where
  | pass (evidence : Passes tests)
  | refuse (cause : Residue) (evidence : First cause tests)

def certifyGuards : (tests : List Test) → GuardVerdict tests
  | [] => .pass .nil
  | test :: rest =>
    match h : test.fails with
    | true => .refuse test.cause (.here h rfl)
    | false =>
      match certifyGuards rest with
      | .pass p => .pass (.cons h p)
      | .refuse cause p => .refuse cause (.later h p)

private def requestProfile (p : Profile) : Wire.Request → Bool
  | .auth .. | .flush .. => false
  | .version offer version => offer == p.offer.toNat && version == version9P
  | .openFile _ mode => modeValid mode
  | .create _ _ perm mode => modeValid mode && perm &&& 0xe40001ff == perm
  | _ => true

private def fidFor (s : State) (req : Wire.Request) : Option Fid := req.primaryFid.bind s.fid

private def policyFor {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Option Rule := do
  let fid ← fidFor s req
  c.policy registry fid.path

private def fidBusy (s : State) : Wire.Request → Bool
  | .attach .. => s.root.isSome
  | .walk src dst _ => src != dst && (s.fid dst).isSome
  | _ => false

private def dmdir (perm : Nat) : Bool := perm &&& 0x80000000 != 0

private def fidMode (s : State) (req : Wire.Request) : Bool :=
  (fidFor s req).all fun fid =>
    match req with
    | .walk _ _ names => fid.opened.isNone && (names.isEmpty || fid.directory)
    | .openFile _ mode => fid.opened.isNone && (!fid.directory || mode == 0)
    | .create _ _ perm mode => fid.directory && fid.opened.isNone && (!dmdir perm || mode == 0)
    | .read _ offset count =>
      (fid.opened.any fun mode => modeReads mode.toNat) &&
        (!fid.directory || ((offset == 0 || offset == littleEndian fid.dirOffset) &&
          offset + count < 2^64))
    | .write .. => !fid.directory && (fid.opened.any fun mode => modeWrites mode.toNat)
    | _ => true

private def modeAccess (r : Rule) (mode : Nat) : Bool :=
  (!modeReads mode || r.access.contains .read) && (!modeWrites mode || r.access.contains .write) &&
  (mode &&& 16 == 0 || r.access.contains .trunc) && (mode &&& 64 == 0 || r.access.contains .rclose)

private def deviceAccess (rule : Rule) : Wire.Request → Bool
  | .walk .. => rule.access.contains .walk
  | .openFile _ mode => modeAccess rule mode
  | .create _ _ _ mode => rule.access.contains .create && modeAccess rule mode
  | .read .. => rule.access.contains .read
  | .write .. => rule.access.contains .write
  | .clunk .. => rule.access.contains .clunk
  | .remove .. => rule.access.contains .remove
  | .stat .. => rule.access.contains .stat
  | .wstat .. => rule.access.contains .wstat
  | _ => true

private def virtualRootAccess : Wire.Request → Bool
  | .openFile _ mode => mode == 0
  | .walk .. | .read .. | .clunk .. | .stat .. => true
  | .wstat .. => true  -- The scope test at T12 rejects this path.
  | _ => false

private def traversalAccess (fid : Fid) (rule : Rule) (req : Wire.Request) : Bool :=
  match req with
  | .walk .. => deviceAccess rule req
  | .clunk .. => fid.opened.isNone && deviceAccess rule req
  | .wstat .. => true  -- The scope test at T12 rejects this path.
  | _ => false

private def declaredAccess {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Bool :=
  (fidFor s req).all fun fid =>
    let permits := fun path => (c.authority registry path).all fun authority =>
      match authority with
      | .virtualRoot => virtualRootAccess req
      | .traversal rule => traversalAccess fid rule req
      | .target rule => deviceAccess rule req
    permits fid.path &&
    match req with
    | .walk _ _ names => (pathPrefixes fid.path names).all permits
    | .create _ name .. => permits (fid.path ++ [name])
    | _ => true

def transferCap (s : State) (p : Profile) (fid : Option Fid) : Nat :=
  let base := min p.maxData.toNat (s.effective p - 24)
  match fid with
  | some f => if f.iounit == 0 then base else min base f.iounit.toNat
  | none => base

private def countValid {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Bool :=
  let cap := transferCap s c.profile (fidFor s req)
  let rule := policyFor registry c s req
  match req with
  | .walk _ _ names => names.length ≤ 16
  | .read _ _ count => count ≤ cap && (rule.all fun r => count ≤ r.read.limit.toNat)
  | .write _ _ data => data.length ≤ cap &&
    (rule.all fun r => data.length ≤ r.write.limit.toNat &&
      (!r.write.atomic || data.length ≤ r.write.recordLimit.toNat))
  | _ => true

private def attachValid {core : Core} (c : Context core) : Wire.Request → Bool
  | .attach fid afid uname aname =>
    fid == 0 && afid == noFid && uname.isEmpty && aname == Format.lowerHex c.nsQ
  | _ => true

def noLengthChange : Nat := 2^64 - 1

private def wstatFields (st : Wire.Stat) : Bool :=
  st.kind == 65535 && st.dev == noFid && st.qid.kind == 255 && st.qid.version == noFid &&
    st.qid.path == noLengthChange && st.mode == noFid && st.atime == noFid && st.mtime == noFid &&
    st.uid.isEmpty && st.gid.isEmpty && st.muid.isEmpty

private def wstatScope {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Bool :=
  match req with
  | .wstat fid info =>
    fid == 1 && wstatFields info && (s.fid fid).any (fun f =>
      f.path.head? == some (ascii "fs") && 2 ≤ f.path.length && (c.policy registry f.path).isSome &&
      (!f.directory || info.length == 0 || info.length == noLengthChange) &&
      (info.name.isEmpty || !newName info.name ||
        let parent := f.path.dropLast
        (c.policy registry parent).isSome && (c.policy registry (parent ++ [info.name])).isSome))
  | _ => true

private def namesValid : Wire.Request → Bool
  | .walk _ _ names => names.all walkName
  | .create _ name .. => newName name
  | .wstat _ info => info.name.isEmpty || newName info.name
  | _ => true

private def pathsDeclared {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Bool :=
  (fidFor s req).all fun fid =>
    c.declares registry fid.path &&
    match req with
    | .walk _ _ names => (pathPrefixes fid.path names).all (c.declares registry)
    | .create _ name .. => c.declares registry (fid.path ++ [name])
    | _ => true

private def grammarValid {core : Core} (registry : Registry) (c : Context core) (s : State)
    (req : Wire.Request) : Bool :=
  (policyFor registry c s req).all fun rule =>
    match req with
    | .write _ offset data =>
      (!(rule.write.atomic || rule.write.grammar != .raw) || offset == 0) &&
      rule.write.grammar.accepts data
    | .read _ offset count => !rule.read.atomic || (offset == 0 && rule.read.recordLimit.toNat ≤ count)
    | _ => true

private def requestTests {core : Core} (registry : Registry) (c : Context core)
    (s : State) (raw : Bytes) : List Test :=
  match decodeT raw with
  | none => [⟨.t1, true⟩]
  | some t =>
    let req := t.body
    [⟨.t2, !requestProfile c.profile req⟩,
     ⟨.t3, s.effective c.profile < raw.length⟩,
     ⟨.t4, !(req.phaseValid s && req.fidsValid s)⟩,
     ⟨.t5, s.pending.isSome || t.tag != req.expectedTag⟩,
     ⟨.t6, !(req.requiredFid.all fun fid => (s.fid fid).isSome)⟩,
     ⟨.t7, fidBusy s req⟩,
     ⟨.t8, !fidMode s req || !declaredAccess registry c s req⟩,
     ⟨.t9, !countValid registry c s req⟩,
     ⟨.t10, c.profile.maxSteps.toNat ≤ s.sentSteps.toNat⟩,
     ⟨.t11, !attachValid c req⟩,
     ⟨.t12, !wstatScope registry c s req⟩,
     ⟨.t13, !namesValid req⟩,
     ⟨.t14, !pathsDeclared registry c s req⟩,
     ⟨.t15, !grammarValid registry c s req⟩]

/-- A pending T has already consumed one step. Recheck the Send guards on
the fields as they stood immediately before that count and pending update. -/
def State.pendingValid {core : Core} (s : State) (registry : Registry) (c : Context core) : Bool :=
  s.pending.all fun raw =>
    0 < s.sentSteps.toNat &&
    let prior := { s with sentSteps := UInt64.ofNat (s.sentSteps.toNat - 1), pending := none }
    (requestTests registry c prior raw).all fun test => !test.fails

def State.localValid {core : Core} (s : State) (registry : Registry) (c : Context core)
    (opening : Bool) : Bool :=
  s.shapeValid c opening && s.pendingValid registry c

def contextTests {core : Core} (registry : Registry) (c : Context core) (s : State)
    (opening : Bool) : List Test :=
  [⟨.c1, !c.digestsValid⟩,
   ⟨.c2, !(c.ns.any fun ns => ns.valid registry)⟩,
   ⟨.c3, !c.profile.valid⟩,
   ⟨.c4, !(c.plan.any Plan.valid)⟩,
   ⟨.c5, !s.localValid registry c opening⟩,
   ⟨.c6, opening && s != State.pre⟩]

def sendTests {core : Core} (registry : Registry) (c : Context core) (s : State) (raw : Bytes) : List Test :=
  contextTests registry c s false ++ requestTests registry c s raw

private def paired (t : Wire.Request) (r : Wire.Reply) : Bool :=
  r.code == t.code + 1 || (r.code == 107 && t.code != 100)

private def replyVersion : Wire.Reply → Bool
  | .version _ version => version == version9P
  | _ => true

private def replyMsize (p : Profile) : Wire.Reply → Bool
  | .version msize _ => 256 ≤ msize && msize ≤ p.offer.toNat
  | _ => true

private def replyCount (s : State) (t : Wire.Request) (r : Wire.Reply) : Bool :=
  match t, r with
  | .walk _ _ names, .walk qids =>
    qids.isEmpty == names.isEmpty && qids.length ≤ names.length && qids.length ≤ 16
  | .read fid _ count, .read data =>
    data.length ≤ count && ((s.fid fid).all fun f => !f.directory || directoryEntries data)
  | .write _ _ data, .write count => count ≤ data.length
  | _, _ => true

private def qidConsistent (s : State) (t : Wire.Request) (r : Wire.Reply) : Bool :=
  match t, r with
  | .attach .., .attach qid => qid.directory
  | .walk .., .walk qids => qids.dropLast.all Wire.Qid.directory
  | .openFile _ _, .openFile qid _ =>
    ((fidFor s t).bind Fid.qidValue).any fun old => old.path == qid.path && old.directory == qid.directory
  | .create _ _ perm _, .create qid _ => dmdir perm == qid.directory
  | .stat _, .stat stat =>
    ((fidFor s t).bind Fid.qidValue).any fun old => old.path == stat.qid.path && old.kind == stat.qid.kind
  | _, _ => true

private def replyGrammar {core : Core} (registry : Registry) (c : Context core) (s : State)
    (t : Wire.Request) (r : Wire.Reply) : Bool :=
  (policyFor registry c s t).all fun rule =>
    match t, r with
    | .write _ _ data, .write count =>
      !(rule.write.atomic || rule.write.grammar != .raw) || count == data.length
    | .read .., .read data =>
      !rule.read.atomic || (data.isEmpty && rule.read.eof) ||
        (data.length ≤ rule.read.recordLimit.toNat && rule.read.grammar.accepts data)
    | _, _ => true

def receiveTests {core : Core} (registry : Registry) (c : Context core) (s : State) (raw : Bytes) : List Test :=
  contextTests registry c s false ++
  match decodeR raw with
  | none => [⟨.r1, true⟩]
  | some r => [⟨.r2, s.effective c.profile < raw.length⟩] ++
    match s.pendingFrame with
    | none => [⟨.r3, true⟩]
    | some t =>
      [⟨.r4, r.tag != t.tag⟩,
       ⟨.r5, !paired t.body r.body⟩,
       ⟨.r6, !replyVersion r.body⟩,
       ⟨.r7, !replyMsize c.profile r.body⟩,
       ⟨.r8, !replyCount s t.body r.body⟩,
       ⟨.r9, !qidConsistent s t.body r.body⟩,
       ⟨.r10, !replyGrammar registry c s t.body r.body⟩]

end Effect.ABI
