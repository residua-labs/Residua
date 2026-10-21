/-
RCIC 06 §13–§15 — M-002a pins of the INTRINSIC machine: every form-2 (entry
run) row of apps/rcic-scm-core/rcic_scm_core_corpus.json is reproduced by
`entryI` (intrinsic bodies, intrinsic arguments, `runLoopI` on typed
configurations, then erasure). 23 rows: 0–8 and 10–23. Rows 9 and 24–39
are form 0/1/3 rows over raw configurations; they pin the raw machine
(`ScmMachinePins.lean`) and are not representable as typed configurations
in general (06 §13: the wire decoder validates frame-chain typing first).

Expected values are the same corpus transcription as `ScmMachinePins.lean`
(its program images and record constructors are reused, not re-stated).
-/
import rcic.ScmMachine
import rcic.ScmMachinePins

namespace Rcic.Scm.MachineIPins
open Rcic.Scm Rcic.Scm.Raw Rcic.Scm.MachinePins

def runI (p : RawProg) (args : List Val) (steps : Int) : Out := entryI 256 p args steps

-- 0 entry run of a local call returns the sum
#guard runI PR0 [] 64 == done1 (.i 3) 11
-- 1 fold evaluates list then initial then elements left to right
#guard runI PR1 [lst [1, 2, 3]] 200 == done1 (.i 6) 23
-- 2 bounded fix checks stop before the limit and returns converged state steps
#guard runI PR2 [.i 0] 400 == done1 (.r [.b 1, .i 6, .i 6]) 83
-- 3 fold body sees the element at 0 and the accumulator at 1
#guard runI PR3 [lst [1, 2, 3]] 200 == done1 (.i 2) 23
-- 4 bounded fix at limit 0 with stop already true converges in zero steps
#guard runI PR4 [] 64 == done1 (.r [.b 1, .i 3, .i 0]) 7
-- 5 bounded fix with a negative limit raises negative_loop_bound
#guard runI PR5 [] 64 == done2 "negative_loop_bound" unitRaw 5
-- 6 general recursion through a local call runs to completion
#guard runI PR6 [.i 4] 400 == done1 (.i 10) 84
-- 7 match evaluates the selected branch with the payload bound
#guard runI PR7 [.j 1 (.b 1)] 64 == done1 (.i 1) 7
-- 8 an injection keeps its summand index through a match
#guard runI PR8 [] 64 == done1 (.i 1) 9
-- 10 field projection of a record argument
#guard runI PR10 [.r [.i 3, .b 1]] 64 == done1 (.b 1) 3
-- 11 pair and cons build values in evaluation order
#guard runI PR11 [] 64 == done1 (.p (.i 7) (lst [1, 2])) 13
-- 12 snd projects the second component
#guard runI PR12 [] 64 == done1 (.b 1) 7
-- 13 record fields evaluate in schema order
#guard runI PR13 [] 64 == done1 (.r [.s "s", .i 2]) 5
-- 14 matching handler catches the raised residue and sees its payload
#guard runI PR14 [.i 7] 64 == done1 (.i 7) 6
-- 15 nonmatching handler is skipped and the residue becomes the final raised outcome
#guard runI PR15 [] 64 == done2 "range_violation" (.i 1) 8
-- 16 primitive overflow raises through a let frame to the final outcome
#guard runI PR16 [] 64 == done2 "signed_overflow" unitRaw 8
-- 17 primitive overflow caught by a matching handler
#guard runI PR17 [] 64 == done1 (.i (-1)) 8
-- 18 a raised ref outside the program's residue catalog refused (residue-row safety)
#guard runI PR18 [] 64 == ref "[rcic_scm_core_row_safety]"
-- 19 a raised payload not of its catalog type refused (payload typing)
#guard runI PR19 [] 64 == ref "[rcic_scm_core_payload]"
-- 20 entry arguments not of the entry parameter types refused
#guard runI PR1 [.i 1] 64 == ref "[rcic_scm_core_ill_typed_args]"
-- 21 an ill-typed program refused before it runs
#guard runI PR20 [] 64 == ref "[rcic_scm_typing_mismatch]"
-- 22 an external call has no body in this bundle refused
#guard runI PR21 [] 64 == ref "[rcic_scm_core_external_call]"
-- 23 budget exhausted mid-run is suspended with the current config
#guard runI PR6 [.i 4] 5 == susp
  ⟨.retC (.i 1),
   [.argsF [.i 4] 0 "lt" 0 [.i 4] [],
    .ifF [.i 4] (li 0) (.prim "add" [v 0, .call (.local 0) [.prim "sub" [v 0, li 1]]])]⟩ 5

end Rcic.Scm.MachineIPins
