import Effect.ConformanceReceipts

namespace Effect.ABI.E3

open Conformance

def hex (bytes : Bytes) : String :=
  String.mk ((Format.lowerHex bytes).map (Char.ofNat ∘ UInt8.toNat))

def bit (ok : Bool) : String := if ok then "1" else "0"

def seedRow (seed : Seed) : String :=
  let negative := seed.negative.run
  let neighbor := seed.neighbor.run
  String.intercalate "\t" ["seed", seed.id, negative.expected, negative.got,
    hex negative.witnessQ, neighbor.expected, neighbor.got, hex neighbor.witnessQ,
    bit (negative.valid && neighbor.valid)]

def obligationRow (test : CaseResult) : String :=
  let result := test.verdict
  String.intercalate "\t" ["obligation", test.group, test.id, result.expected,
    result.got, hex result.witnessQ, bit result.valid]

end Effect.ABI.E3

def main (args : List String) : IO UInt32 := do
  if let ["q", path] := args then
    let bytes ← IO.FS.readBinFile path
    IO.println (Effect.ABI.E3.hex (Effect.Format.q .bytes bytes.data.toList))
    return 0
  let sample := args == ["sample"]
  if !sample && !args.isEmpty then
    IO.eprintln "usage: ConformanceRows.lean [sample | q <rows.tsv>]"
    return 2
  for seed in Effect.ABI.E3.seeds do
    IO.println (Effect.ABI.E3.seedRow seed)
  let groups := [Effect.ABI.E3.boundaryCases, Effect.ABI.E3.transitionCases,
    Effect.ABI.E3.priorityCases, Effect.ABI.E3.receiptCases, Effect.ABI.E3.mutantCases]
  for test in (if sample then groups.flatMap (·.take 3) else groups.flatten) do
    IO.println (Effect.ABI.E3.obligationRow test)
  return 0
