import Effect.ProcTrace

namespace Effect.TraceWitness

private def sampleQ (b : UInt8) : Digest := ⟨List.replicate 32 b, by simp⟩

def authority : Authority := ⟨.fs, sampleQ 1, sampleQ 2⟩

def invocationFuel : Nat := 3000000000

def ctx : Context :=
  { namespaceQ := sampleQ 3, profileQ := sampleQ 4, planQ := sampleQ 5
    resolve := fun d => if d = .fs then some authority else none
    invocationFuel := invocationFuel, hostSteps := 64 }

def request (fid : UInt8) : Request := ⟨authority, [11,0,0,0,124,0,0,fid,0,0,0]⟩

private def send (fid : UInt8) : Proc := .await (ascii "fs" ++ [10] ++ (request fid).frame) []

private def byteAt (bytes : Bytes) (i : Nat) : UInt8 := bytes[i]?.getD 0

/- Continuation labels identify the three do-bind sites of TraceSubject.rsd.
The first captures fid, the second the first reply, and the outer
continuation captures neither. -/
private def dispatch (k : Cont) (value : Bytes) : Proc :=
  match k.code with
  | 0 =>
    let fid := UInt8.ofNat (k.ints.headD 0).toNat
    let marker := byteAt value 9
    (send (if marker == 65 then fid else fid + 1)).bind ⟨1, k.ints, [value]⟩
  | 1 => .done [byteAt value 9, byteAt (k.bytes.headD []) 9]
  | 2 => .done (37 :: value)
  | _ => .refuse (ascii "qmiss")

def program (lifo : Bool := false) : Program :=
  { initial := fun fuel =>
      if fuel = 1 then .error .fuel
      else
        let inner : Cont := ⟨0, [1], []⟩
        let outer : Cont := ⟨2, [], []⟩
        if lifo then .ok (.await (ascii "fs" ++ [10] ++ (request 1).frame) [outer, inner])
        else .ok (((send 1).bind inner).bind outer)
    apply := dispatch
    invoke := fun _ _ => .ok () }

def response (marker : UInt8) : Observation :=
  .reads [.data [10,0,0,0], .data [107,0,0,1,0,marker]]

def observations : List Observation := [response 65, response 66]

def completeTrace : Trace := [⟨request 1, response 65⟩, ⟨request 1, response 66⟩]

def completeResult : Terminal := .success 37 [66,65]

-- The two identical requests get different replies because the oracle
-- selects by state. State 2 has exhausted the tape.
def oracle : Oracle Nat
  | 0, _ => some (response 65, 1)
  | 1, _ => some (response 66, 2)
  | _, _ => none

theorem completion :
    Execution (program false) ctx oracle (start (program false) ctx)
      0 completeTrace (.terminal completeResult) 2 := by
  apply Execution.observed
  · rfl
  · rfl
  · apply Execution.observed
    · rfl
    · rfl
    · exact Execution.stopped _ _

theorem suspension :
    Execution (program false) ctx (fun i r => if i = 0 then oracle i r else none)
      (start (program false) ctx) 0 [⟨request 1, response 65⟩] (.request (request 1)) 1 := by
  apply Execution.observed
  · rfl
  · rfl
  · apply Execution.suspended
    rfl

theorem completeReplay :
    replayComplete (program false) ctx completeTrace = .ok completeResult :=
  replay_completed_execution completion

theorem suspendedReplay :
    replay (program false) ctx [⟨request 1, response 65⟩] (start (program false) ctx) =
      .ok (.request (request 1)) :=
  replay_execution suspension

theorem missingResponse :
    replayComplete (program false) ctx (completeTrace.take 1) =
      .error (.missing (.request (request 1))) := rfl

theorem extraResponse :
    replayComplete (program false) ctx (completeTrace ++ completeTrace) = .error .extra := rfl

theorem changedRequest :
    replayComplete (program false) ctx [⟨request 2, response 65⟩] =
      .error (.requestMismatch (request 1) (request 2)) := rfl

private def otherAuthority : Request :=
  { request 1 with authority := { authority with config := sampleQ 9 } }

theorem changedAuthority :
    replayComplete (program false) ctx [⟨otherAuthority, response 65⟩] =
      .error (.requestMismatch (request 1) otherAuthority) := rfl

theorem changedReply :
    replayComplete (program false) ctx [⟨request 1, response 90⟩, ⟨request 1, response 66⟩] =
      .error (.requestMismatch (request 2) (request 1)) := rfl

theorem eofOutcome :
    interpret (program false) ctx [response 65, .reads [.eof []]] (start (program false) ctx) =
      .ok ([⟨request 1, response 65⟩, ⟨request 1, .reads [.eof []]⟩], .terminal (.transport .endOfStream)) :=
  rfl

theorem partialRead :
    replay (program false) ctx [⟨request 1, .reads [.data [10,0,0,0]]⟩] (start (program false) ctx) =
      .ok (.reading (request 1) 4 6) := rfl

theorem fueledStop :
    replayComplete (program false) { ctx with invocationFuel := 1 } [] = .ok (.invocation .fuel) := rfl

theorem continuationLimit :
    replayComplete (program false) { ctx with continuationBudget := 0 } [] = .ok .continuationBudget := rfl

theorem hostLimit :
    replayComplete (program false) { ctx with hostSteps := 0 } [] = .ok .hostStepLimit := rfl

#print axioms completion
#print axioms suspension

end Effect.TraceWitness
