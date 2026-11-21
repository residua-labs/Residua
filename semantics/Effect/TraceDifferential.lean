import Effect.TraceWitness

namespace Effect.TraceDifferential

open TraceWitness

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def decodeHex : List Char → Option Bytes
  | [] => some []
  | a :: b :: rest => do
    let hi ← nibble a
    let lo ← nibble b
    pure (UInt8.ofNat (16 * hi + lo) :: (← decodeHex rest))
  | _ => none

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

private def hex (bytes : Bytes) : String :=
  String.mk (bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

private def finishRequest (request : Option Request) (reads : List ReadEvent) (trace : Trace) :
    Trace :=
  match request with
  | none => trace
  | some wire => ⟨wire, .reads reads.reverse⟩ :: trace

private def readTape : List String → Option Request → List ReadEvent → Trace → Except String Trace
  | [], request, reads, trace => .ok (finishRequest request reads trace).reverse
  | line :: rest, request, reads, trace => do
    match line.splitOn "\t" with
    | ["T", token, bytes] =>
      let some frame := decodeHex bytes.toList | .error "tape_request_hex"
      let some wire := route ctx (ascii token ++ [10] ++ frame) | .error "tape_authority"
      readTape rest (some wire) [] (finishRequest request reads trace)
    | ["R", tag, bytes] =>
      let some _ := request | .error "tape_read_without_request"
      let some code := tag.toInt? | .error "tape_read_tag"
      let some data := decodeHex bytes.toList | .error "tape_read_hex"
      let event := match code with
        | 0 => ReadEvent.data data
        | 1 => .eof data
        | 2 => .closed data
        | 4 => .timeout data
        | _ => .unknownEvent code data
      readTape rest request (event :: reads) trace
    | _ => .error "tape_row"

structure Receipt where
  trace : Trace
  exit : UInt32
  stdout : Bytes
  stderr : Bytes
  deriving DecidableEq

private def capture (runner dir : String) (fuel : Nat) (marker : String) (eof : Bool) : IO Receipt := do
  IO.FS.createDirAll dir
  let out := dir ++ "/stdout"
  let tapeFile := dir ++ "/tape.tsv"
  let args := #[toString fuel, marker, if eof then "1" else "0", out, tapeFile]
  let status ← IO.Process.output { cmd := runner, args }
  unless status.stdout.isEmpty do throw (IO.userError "trace_runner_stdout")
  IO.FS.writeFile (dir ++ "/exit") (toString status.exitCode ++ "\n")
  IO.FS.writeFile (dir ++ "/stderr") status.stderr
  let tape ← IO.FS.readFile tapeFile
  let lines := (tape.splitOn "\n").filter (! ·.isEmpty)
  let trace ← match readTape lines none [] [] with
    | .error name => throw (IO.userError name)
    | .ok trace => pure trace
  pure ⟨trace, status.exitCode, (← IO.FS.readBinFile out).data.toList, ascii status.stderr⟩

private def expectedTerminal : Terminal → Option (UInt32 × Bytes × Bytes)
  | .success exit out => some (exit.toNat.toUInt32, out, [])
  | .invocation .fuel => some (50, [], ascii "[fuel]\n")
  | .transport .endOfStream => some (56, [], ascii "[end_of_stream]\n")
  | _ => none

private def require (test : Bool) (name : String) : IO Unit :=
  if test then pure () else throw (IO.userError name)

private def compare (name : String) (p : Program) (c : Context) (receipt : Receipt)
    (count : Nat) : IO Unit := do
  let observations := receipt.trace.map Event.observation
  let .ok (trace, .terminal outcome) := interpret p c observations (start p c)
    | throw (IO.userError s!"{name}_interpret exit={receipt.exit} stderr={hex receipt.stderr}")
  require (decide (trace = receipt.trace)) (name ++ "_tape_mismatch")
  require (decide (trace.length = count)) (name ++ "_request_count")
  require (decide (expectedTerminal outcome = some (receipt.exit, receipt.stdout, receipt.stderr)))
    (name ++ "_terminal_mismatch")
  match replayComplete p c receipt.trace with
  | .ok o => require (decide (o = outcome)) (name ++ "_replay_outcome")
  | .error _ => throw (IO.userError (name ++ "_replay"))
  IO.println s!"{name}\t{count}\t{receipt.exit}\t{hex receipt.stdout}\t{hex receipt.stderr}"

def run (args : List String) : IO UInt32 := do
  let [baselineRunner, mutantRunner, out] := args
    | throw (IO.userError "trace_differential_usage")
  IO.println "row\trequests\texit\tstdout_hex\tstderr_hex"
  let baseline ← capture baselineRunner (out ++ "/base") invocationFuel "A" false
  compare "base" (program false) ctx baseline 2
  require (decide (baseline.trace = completeTrace)) "base_trace_target"
  let mutant ← capture mutantRunner (out ++ "/fifo") invocationFuel "A" false
  compare "fifo" (program true) ctx mutant 2
  require (decide (baseline.trace.map Event.request ≠ mutant.trace.map Event.request)) "fifo_survived"
  let changed ← capture baselineRunner (out ++ "/reply") invocationFuel "Z" false
  compare "reply" (program false) ctx changed 2
  require (decide (baseline.trace.map Event.request ≠ changed.trace.map Event.request)) "reply_survived"
  let fault ← capture baselineRunner (out ++ "/eof") invocationFuel "A" true
  compare "eof" (program false) ctx fault 2
  let [first, later] := fault.trace | throw (IO.userError "prefix_trace_length")
  match replay (program false) ctx [first] (start (program false) ctx) with
  | .ok (.request next) => require (decide (next = later.request)) "prefix_request_mismatch"
  | _ => throw (IO.userError "prefix_frontier")
  IO.println "prefix\t1\t-\t-\t-"
  let fuel ← capture baselineRunner (out ++ "/fuel") 1 "A" false
  compare "fuel" (program false) { ctx with invocationFuel := 1 } fuel 0
  return 0

end Effect.TraceDifferential

def main := Effect.TraceDifferential.run
