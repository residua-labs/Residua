import Effect.ConformanceTransitions

namespace Effect.ABI.E3

open Conformance Fixtures Wire

private def addTrace (req : SealRequest fixtureCore) (rows : List RawPair) : SealRequest fixtureCore :=
  { req with trace := rows.map RawPair.inline }

def receiptCases : List CaseResult :=
  let base := prefixPairs ++ [statRootPair, clunkRootPair]
  let c := exactContext base
  let pin := receipt c base
  let empty := context []
  let refs := base.map fun p => Transaction.mk (withRef p.t) (withRef p.r)
  let byRef := { pin with trace := refs }
  let firstRef : Transaction := ⟨withRef versionPair.t, .inline versionPair.r⟩
  let partialRef := { pin with trace := firstRef :: pin.trace.drop 1 }
  let objects := (pairBytes base).map fun b => (Format.q .bytes b, b)
  let tMismatch := { statRootPair with t := request (.stat 1) }
  let different := { rootQid with version := 1 }
  let rChanged := { statRootPair with r := reply (.stat (statOf different [])) }
  let rWrongQid := { statRootPair with r := reply (.stat (statOf { rootQid with path := 0 } [])) }
  let rBadTag := { statRootPair with r := reply (.stat (statOf rootQid [])) 1 }
  let rBadCount := { attachPair with r := ((Build.frame 105 0 rootQid.bytes.dropLast).getD []) }
  let variant := prefixPairs ++ [rChanged, clunkRootPair]
  let wrongLength := { pin with trace :=
    ⟨withRef versionPair.t (versionPair.t.length + 1), .inline versionPair.r⟩ :: refs.drop 1 }
  let wrongObject := (Format.q .bytes versionPair.t, versionPair.r) :: objects.drop 1
  let lastTwo := fun a b => addTrace pin (prefixPairs ++ [a, b])
  let mutate := fun id req expected => check "receipt" id (sealProbe c req expected)
  [check "receipt" "empty-done" (sealProbe empty (receipt empty []) .sealed),
   mutate "empty-awaiting" (addTrace pin []) (.refuse .s4),
   mutate "inline" pin .sealed,
   check "receipt" "reference" (sealProbe c byRef .sealed objects),
   check "receipt" "partial-reference" (sealProbe c partialRef .sealed objects),
   mutate "changed-T" (lastTwo tMismatch clunkRootPair) (.refuse .s4),
   mutate "changed-valid-R" (addTrace pin variant) (.refuse .s5),
   mutate "bad-reply-tag" (lastTwo rBadTag clunkRootPair) (.refuse .r4),
   mutate "bad-reply-frame" (addTrace pin [versionPair, rBadCount, statRootPair, clunkRootPair]) (.refuse .r1),
   mutate "bad-reply-qid" (lastTwo rWrongQid clunkRootPair) (.refuse .r9),
   mutate "extra" (addTrace pin (base ++ [clunkRootPair])) (.refuse .s4),
   mutate "dropped" (addTrace pin (prefixPairs ++ [clunkRootPair])) (.refuse .s4),
   mutate "reordered" (lastTwo clunkRootPair statRootPair) (.refuse .s4),
   mutate "partial" (addTrace pin base.dropLast) (.refuse .s4),
   mutate "wrong-external-root" { pin with root := List.replicate 32 0 } (.refuse .s5),
   mutate "wrong-external-results-q" { pin with resultsQ := Format.q .i64 (0 : Format.I64) } (.refuse .s6),
   mutate "wrong-external-result-value" { pin with results := (41 : Format.I64) } (.refuse .s6),
   check "receipt" "missing-object" (sealProbe c byRef (.refuse .s2) (objects.drop 1)),
   check "receipt" "substituted-object" (sealProbe c byRef (.refuse .s3) wrongObject),
   check "receipt" "reference-length" (sealProbe c wrongLength (.refuse .s3) objects),
   check "precedence" "S2/S3" (sealProbe c wrongLength (.refuse .s2) (objects.take 1)),
   check "precedence" "S5/S6" (sealProbe c { pin with root := [], resultsQ := [] } (.refuse .s5)),
   inspect "receipt" "same-result-different-root" [pin.root, rootFor c variant, pin.resultsQ]
     (pin.root != rootFor c variant && (sealProbe c (receipt c variant) .sealed).run.ok &&
       (sealProbe c (addTrace pin variant) (.refuse .s5)).run.ok)]

private def resultOf (tests : List Test) : Option Residue :=
  match certifyGuards tests with
  | .pass _ => none
  | .refuse reason _ => some reason

def mutantCases : List CaseResult :=
  let probe := send prefixPairs (namedWalk 19) (.refuse .t9)
  let state := (probe.point.project probe.context probe.event).getD State.pre
  let tests := sendTests registry probe.context state (namedWalk 19)
  let omitted := tests.filter (fun test => test.cause != .t9)
  let admitsWrongly := probe.run.ok && (resultOf omitted).isNone
  let good := sendOK prefixPairs statRoot
  let admitted := good.run
  let goodState := (good.point.project good.context good.event).getD State.pre
  let noPending : Outcome fixtureCore := ⟨goodState, none, .issue statRoot⟩
  let applicable := fun n => 16 < n && (decodeT (namedWalk n)).isSome
  let persists := fun n =>
    let t := namedWalk n
    let p := send prefixPairs t (.refuse .t9)
    (p.point.project p.context p.event).any fun s =>
      let withoutT9 := (sendTests registry p.context s t).filter (fun test => test.cause != .t9)
      p.run.ok && (resultOf withoutT9).isNone
  [inspect "mutant" "suppress-T9" [probe.inputQ state] admitsWrongly,
   inspect "mutant" "admit-all" [probe.inputQ state] (probe.run.ok &&
     !probe.expected.check probe.context state probe.event ⟨state.afterSend (namedWalk 19), none, .issue (namedWalk 19)⟩),
   inspect "mutant" "reject-all" [admitted.witnessQ] (admitted.ok &&
     !good.expected.check good.context goodState good.event (refused good.context goodState good.event .t1)),
   inspect "mutant" "unnamed-failure" [admitted.witnessQ, ascii "extra"]
     (admitted.valid && !({ admitted with got := "nf_unpublished" }).valid),
   inspect "mutant" "lost-pending-T" [admitted.witnessQ]
     (admitted.ok && !good.expected.check good.context goodState good.event noPending),
   inspect "mutant" "shrink-preserves-cap-premise" [probe.inputQ state, namedWalk 17]
     (admitsWrongly && shrink [16, 17, 18] applicable persists == some 17)]

end Effect.ABI.E3
