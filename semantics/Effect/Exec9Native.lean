import Lib.Exec9Core

/- Native process boundary for the E4 socket actuator. Each list crosses
   as signed decimal words, including the negative unbound-fid sentinel. -/
private def words (s : String) : Option (List Int) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM String.toInt?

def main (argv : List String) : IO UInt32 := do
  let [sel, ns, a, b, c, st, r] := argv | return 2
  let some selector := sel.toInt? | return 2
  let some [n, x, y, z, state, reply] := [ns, a, b, c, st, r].mapM words | return 2
  let step := Effect.Exec9Entry.cold selector n x y z state reply
  IO.println ("[" ++ reprStr step.st ++ "," ++ toString step.act ++ "," ++ reprStr step.out ++ "]")
  return 0
