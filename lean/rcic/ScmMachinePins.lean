/-
RCIC 06 §10, §12–§15 — M-002 pins of the raw machine `Raw.scmCore` to
apps/rcic-scm-core/rcic_scm_core_corpus.json (40 rows, all transcribed).

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with its
"SCM-00x 06 sNN " prefix dropped. Programs PR0–PR22 are the corpus' distinct
`prog` images; all share the catalog `C4` and the external signature list
`extP` except PR18 (no `signed_overflow`) and PR19 (`signed_overflow : i64`).
Form-2 rows carry the unused default config `unitCfg`.
-/
import rcic.ScmMachineRaw

namespace Rcic.Scm.MachinePins
open Rcic.Scm Rcic.Scm.Raw

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def li (n : Int) : RawExpr := .lit (.i n) .i64
def lb (b : Int) : RawExpr := .lit (.b b) .bool
def ls (s : String) : RawExpr := .lit (.s s) .str
def v (i : Int) : RawExpr := .var i
def MAX : Int := 9223372036854775807
def fixRec : CoreTy := .record [("converged", B), ("state", I), ("steps", I)]
def recAB : CoreTy := .record [("a", I), ("b", B)]

def extP : List ExtSig := [⟨"ext.len", [Str], I⟩]
def C4 : List CatalogEntry :=
  [⟨"bad_input", unitTy⟩, ⟨"negative_loop_bound", unitTy⟩, ⟨"range_violation", I⟩, ⟨"signed_overflow", unitTy⟩]
def mk (fns : List RawFnDef) (entry : Int) : RawProg := ⟨fns, extP, C4, entry⟩

def fAdd : RawFnDef := ⟨[I, I], I, .prim "add" [v 0, v 1]⟩
def recBody : RawExpr :=
  .ifE (.prim "lt" [v 0, li 1]) (li 0) (.prim "add" [v 0, .call (.local 0) [.prim "sub" [v 0, li 1]]])
def ovfBody : RawExpr := .letE (li MAX) (.prim "add" [v 0, li 1])

def PR0 := mk [fAdd, ⟨[], I, .call (.local 0) [li 1, li 2]⟩] 1
def PR1 := mk [⟨[.list I], I, .fold (v 0) (li 0) (.prim "add" [v 0, v 1])⟩] 0
def PR2 := mk [⟨[I], fixRec, .fix (v 0) (li 10) (.prim "lt" [li 5, v 0]) (.prim "add" [v 0, li 1])⟩] 0
def PR3 := mk [⟨[.list I], I, .fold (v 0) (li 0) (.prim "sub" [v 0, v 1])⟩] 0
def PR4 := mk [⟨[], fixRec, .fix (li 3) (li 0) (lb 1) (v 0)⟩] 0
def PR5 := mk [⟨[], fixRec, .fix (li 0) (li (-1)) (lb 1) (v 0)⟩] 0
def PR6 := mk [⟨[I], I, recBody⟩] 0
def PR7 := mk [⟨[.sum [I, B]], I, .matchE (v 0) [v 0, .ifE (v 0) (li 1) (li 0)]⟩] 0
def PR8 := mk [⟨[], I, .matchE (.inj 1 [I, B] (lb 1)) [v 0, .ifE (v 0) (li 1) (li 0)]⟩] 0
def PR9 := mk [⟨[I], I, v 1⟩] 0
def PR10 := mk [⟨[recAB], B, .field (v 0) 1⟩] 0
def PR11 := mk [⟨[], .pair I (.list I), .pair (li 7) (.cons (li 1) (.cons (li 2) (.nil I)))⟩] 0
def PR12 := mk [⟨[], B, .snd (.pair (li 7) (lb 1))⟩] 0
def PR13 := mk [⟨[], .record [("x", Str), ("y", I)], .recordE ["x", "y"] [ls "s", li 2]⟩] 0
def PR14 := mk [⟨[I], I, .handle "range_violation" (.raise "range_violation" (v 0) I) (v 0)⟩] 0
def PR15 := mk [⟨[], I, .handle "bad_input" (.letE (li 1) (.raise "range_violation" (v 0) I)) (li 0)⟩] 0
def PR16 := mk [⟨[], I, ovfBody⟩] 0
def PR17 := mk [⟨[], I, .handle "signed_overflow" (.prim "add" [li MAX, li 1]) (li (-1))⟩] 0
def PR18 : RawProg :=
  ⟨[⟨[], I, ovfBody⟩], extP, [⟨"bad_input", unitTy⟩, ⟨"negative_loop_bound", unitTy⟩, ⟨"range_violation", I⟩], 0⟩
def PR19 : RawProg :=
  ⟨[⟨[], I, ovfBody⟩], extP,
   [⟨"bad_input", unitTy⟩, ⟨"negative_loop_bound", unitTy⟩, ⟨"range_violation", I⟩, ⟨"signed_overflow", I⟩], 0⟩
def PR20 := mk [⟨[], B, li 1⟩] 0
def PR21 := mk [⟨[], I, .call (.ext "ext.len") [ls "abc"]⟩] 0
def PR22 := mk [fAdd] 0

def retCfg (x : Val) : Config := ⟨.retC x, []⟩
def done1 (x : Val) (steps : Int) : Out := ⟨1, 1, retCfg x, x, "", some steps, none, ""⟩
def done2 (r : String) (x : Val) (steps : Int) : Out := ⟨1, 2, ⟨.raiseC r x, []⟩, x, r, some steps, none, ""⟩
def susp (c : Config) (steps : Int) : Out := ⟨1, 3, c, unitRaw, "", some steps, none, ""⟩
def fin1 (x : Val) : Out := ⟨1, 1, retCfg x, x, "", none, none, ""⟩
def fin2 (r : String) (x : Val) : Out := ⟨1, 2, ⟨.raiseC r x, []⟩, x, r, none, none, ""⟩
def ref (code : String) : Out := refuse code
def lst (ns : List Int) : Val := .l (ns.map Val.i)

/-- Form-2 rows: `scmCore 2 256 prog unitCfg args steps 0`. -/
def runE (p : RawProg) (args : List Val) (steps : Int) : Out := scmCore 2 256 p unitCfg args steps 0

-- 0 entry run of a local call returns the sum
#guard runE PR0 [] 64 == done1 (.i 3) 11
-- 1 fold evaluates list then initial then elements left to right
#guard runE PR1 [lst [1, 2, 3]] 200 == done1 (.i 6) 23
-- 2 bounded fix checks stop before the limit and returns converged state steps
#guard runE PR2 [.i 0] 400 == done1 (.r [.b 1, .i 6, .i 6]) 83
-- 3 fold body sees the element at 0 and the accumulator at 1
#guard runE PR3 [lst [1, 2, 3]] 200 == done1 (.i 2) 23
-- 4 bounded fix at limit 0 with stop already true converges in zero steps
#guard runE PR4 [] 64 == done1 (.r [.b 1, .i 3, .i 0]) 7
-- 5 bounded fix with a negative limit raises negative_loop_bound
#guard runE PR5 [] 64 == done2 "negative_loop_bound" unitRaw 5
-- 6 general recursion through a local call runs to completion
#guard runE PR6 [.i 4] 400 == done1 (.i 10) 84
-- 7 match evaluates the selected branch with the payload bound
#guard runE PR7 [.j 1 (.b 1)] 64 == done1 (.i 1) 7
-- 8 an injection keeps its summand index through a match
#guard runE PR8 [] 64 == done1 (.i 1) 9
-- 9 a callee environment holds exactly the argument values (06 L218)
#guard scmCore 1 256 PR9 ⟨.evalC [.i 8, .i 9] (.call (.local 0) [li 5]), []⟩ [] 16 0
  == ref "[rcic_scm_core_stuck]"
-- 10 field projection of a record argument
#guard runE PR10 [.r [.i 3, .b 1]] 64 == done1 (.b 1) 3
-- 11 pair and cons build values in evaluation order
#guard runE PR11 [] 64 == done1 (.p (.i 7) (lst [1, 2])) 13
-- 12 snd projects the second component
#guard runE PR12 [] 64 == done1 (.b 1) 7
-- 13 record fields evaluate in schema order
#guard runE PR13 [] 64 == done1 (.r [.s "s", .i 2]) 5
-- 14 matching handler catches the raised residue and sees its payload
#guard runE PR14 [.i 7] 64 == done1 (.i 7) 6
-- 15 nonmatching handler is skipped and the residue becomes the final raised outcome
#guard runE PR15 [] 64 == done2 "range_violation" (.i 1) 8
-- 16 primitive overflow raises through a let frame to the final outcome
#guard runE PR16 [] 64 == done2 "signed_overflow" unitRaw 8
-- 17 primitive overflow caught by a matching handler
#guard runE PR17 [] 64 == done1 (.i (-1)) 8
-- 18 a raised ref outside the program's residue catalog refused (residue-row safety)
#guard runE PR18 [] 64 == ref "[rcic_scm_core_row_safety]"
-- 19 a raised payload not of its catalog type refused (payload typing)
#guard runE PR19 [] 64 == ref "[rcic_scm_core_payload]"
-- 20 entry arguments not of the entry parameter types refused
#guard runE PR1 [.i 1] 64 == ref "[rcic_scm_core_ill_typed_args]"
-- 21 an ill-typed program refused before it runs
#guard runE PR20 [] 64 == ref "[rcic_scm_typing_mismatch]"
-- 22 an external call has no body in this bundle refused
#guard runE PR21 [] 64 == ref "[rcic_scm_core_external_call]"
-- 23 budget exhausted mid-run is suspended with the current config
#guard runE PR6 [.i 4] 5 == susp
  ⟨.retC (.i 1),
   [.argsF [.i 4] 0 "lt" 0 [.i 4] [],
    .ifF [.i 4] (li 0) (.prim "add" [v 0, .call (.local 0) [.prim "sub" [v 0, li 1]]])]⟩ 5
-- 24 one step on let pushes one frame and evaluates the value
#guard scmCore 0 256 PR22 ⟨.evalC [] (.letE (li 1) (v 0)), []⟩ [] 0 0
  == next ⟨.evalC [] (li 1), [.letF [] (v 0)]⟩
-- 25 one step returning into a pair-left frame pushes pair-right
#guard scmCore 0 256 PR22 ⟨.retC (.i 1), [.pairL [] (li 2)]⟩ [] 0 0
  == next ⟨.evalC [] (li 2), [.pairR (.i 1)]⟩
-- 26 a raising control pops one ordinary frame per step
#guard scmCore 0 256 PR22 ⟨.raiseC "bad_input" unitRaw, [.letF [] (li 1), .letF [] (li 2)]⟩ [] 0 0
  == next ⟨.raiseC "bad_input" unitRaw, [.letF [] (li 2)]⟩
-- 27 a raising control enters a matching handler with the payload bound
#guard scmCore 0 256 PR22 ⟨.raiseC "bad_input" unitRaw, [.handleF "bad_input" [] (v 0)]⟩ [] 0 0
  == next ⟨.evalC [unitRaw] (v 0), []⟩
-- 28 a raising control skips a nonmatching handler
#guard scmCore 0 256 PR22 ⟨.raiseC "bad_input" unitRaw, [.handleF "range_violation" [] (li 0)]⟩ [] 0 0
  == next ⟨.raiseC "bad_input" unitRaw, []⟩
-- 29 a returned value at the empty continuation is final
#guard scmCore 0 256 PR22 ⟨.retC (.i 5), []⟩ [] 0 0 == fin1 (.i 5)
-- 30 a raising control at the empty continuation is the final raised outcome
#guard scmCore 0 256 PR22 ⟨.raiseC "bad_input" unitRaw, []⟩ [] 0 0 == fin2 "bad_input" unitRaw
-- 31 a variable outside its environment is stuck refused as integrity
#guard scmCore 0 256 PR22 ⟨.evalC [] (v 0), []⟩ [] 0 0 == ref "[rcic_scm_core_stuck]"
-- 32 finality is checked before the budget run of a final config at zero steps
#guard scmCore 1 256 PR22 ⟨.retC (.i 5), []⟩ [] 0 0 == done1 (.i 5) 0
-- 33 run with exactly the needed steps completes
#guard scmCore 1 256 PR22 ⟨.evalC [.i 2, .i 3] (.prim "add" [v 0, v 1]), []⟩ [] 5 0 == done1 (.i 5) 5
-- 34 run one step short is suspended never a residue
#guard scmCore 1 256 PR22 ⟨.evalC [.i 2, .i 3] (.prim "add" [v 0, v 1]), []⟩ [] 4 0
  == susp ⟨.retC (.i 3), [.argsF [.i 2, .i 3] 0 "add" 0 [.i 2] []]⟩ 4
-- 35 negative step budget refused
#guard scmCore 1 256 PR22 ⟨.evalC [] (li 1), []⟩ [] (-1) 0 == ref "[rcic_scm_core_budget]"
-- 36 step budget above the 4096 bound refused not decided
#guard scmCore 1 256 PR22 ⟨.evalC [] (li 1), []⟩ [] 4097 0 == ref "[rcic_scm_core_bound]"
-- 37 resume law run m+n equals continue n after run m
#guard scmCore 3 256 PR6 ⟨.evalC [.i 4] recBody, []⟩ [] 7 100
  == ⟨1, 1, retCfg (.i 10), .i 10, "", some 84, some 1, ""⟩
-- 38 a primitive outside the closed pure enum cannot execute
#guard scmCore 0 256 PR22 ⟨.retC (.i 1), [.argsF [] 0 "read_file" 0 [] []]⟩ [] 0 0
  == ref "[rcic_scm_core_stuck]"
-- 39 unknown form refused
#guard scmCore 9 256 PR0 unitCfg [] 0 0 == ref "[rcic_scm_core_unknown_form]"

end Rcic.Scm.MachinePins
