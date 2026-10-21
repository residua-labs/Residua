/-
RCIC 06 §6–§9 — M-002 pins of `scmTyping` to
apps/rcic-scm-typing/rcic_scm_typing_corpus.json (63 rows, all transcribed).

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with its prefix
("SCM-012 06 s8 ", "SCM-012 06 s6 " or "SCM-002 06 s7 ") dropped. The shared program image
`P` is the corpus' `prog` of row 0; rows 1–4 differ from it in exactly the
field noted. `ok t` / `no code` are the two record shapes of the carrier
(`{ok 1, t, code ""}` / `{ok 0, t unit, code}`).
-/
import rcic.ScmExpr

namespace Rcic.Scm.ExprPins
open Rcic.Scm

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def li (n : Int) : RawExpr := .lit (.i n) .i64
def lb (b : Int) : RawExpr := .lit (.b b) .bool
def ls (s : String) : RawExpr := .lit (.s s) .str
def v (i : Int) : RawExpr := .var i
def ok (t : CoreTy) : TyOut := ⟨1, t, ""⟩
def no (code : String) : TyOut := ⟨0, unitTy, code⟩
def recAB : CoreTy := .record [("a", I), ("b", B)]
def fixRec : CoreTy := .record [("converged", B), ("state", I), ("steps", I)]

def catalogP : List CatalogEntry := [⟨"bad_input", unitTy⟩, ⟨"range_violation", I⟩]
def extP : List ExtSig := [⟨"ext.len", [Str], I⟩]

def fnsHead : List RawFnDef := [
  ⟨[I, I], I, .prim "add" [v 0, v 1]⟩,
  ⟨[I], I, .handle "range_violation" (.raise "range_violation" (v 0) I) (v 0)⟩,
  ⟨[.list I], I, .fold (v 0) (li 0) (.prim "add" [v 0, v 1])⟩,
  ⟨[I], fixRec, .fix (v 0) (li 10) (.prim "lt" [li 5, v 0]) (.prim "add" [v 0, li 1])⟩,
  ⟨[], I, .call (.local 0) [li 1, li 2]⟩,
  ⟨[Str], I, .call (.ext "ext.len") [v 0]⟩,
  ⟨[.sum [I, B]], I, .matchE (v 0) [v 0, .ifE (v 0) (li 1) (li 0)]⟩,
  ⟨[], recAB, .recordE ["a", "b"] [li 1, lb 1]⟩,
  ⟨[recAB], B, .field (v 0) 1⟩,
  ⟨[], .list I, .cons (li 1) (.nil I)⟩]
def fn10 (result : CoreTy) : RawFnDef := ⟨[], result, .letE (li 41) (.prim "add" [v 0, li 1])⟩

def P : RawProg := ⟨fnsHead ++ [fn10 I], extP, catalogP, 4⟩

def deep : RawExpr := .letE (li 1) (.letE (li 2) (.letE (li 3) (.letE (li 4) (v 0))))
def rxy : RawExpr := .recordE ["x", "y"] [ls "s", li 2]
def u : RawExpr := li 0  -- the unused `e` of form-0 rows

-- 0 well-typed program with every constructor family accepted, entry result type
#guard scmTyping 0 64 P [] u == ok I
-- 1 program whose function body type differs from its declared result refused  (fn 10 result bool)
#guard scmTyping 0 64 ⟨fnsHead ++ [fn10 B], extP, catalogP, 4⟩ [] u == no "[rcic_scm_typing_mismatch]"
-- 2 residue catalog not canonical sorted refused  (catalog reversed)
#guard scmTyping 0 64 ⟨P.fns, extP, [⟨"range_violation", I⟩, ⟨"bad_input", unitTy⟩], 4⟩ [] u
  == no "[rcic_scm_typing_catalog]"
-- 3 residue catalog with a duplicate ref refused
#guard scmTyping 0 64 ⟨P.fns, extP, [⟨"bad_input", unitTy⟩, ⟨"bad_input", unitTy⟩], 4⟩ [] u
  == no "[rcic_scm_typing_catalog]"
-- 4 entry function ref outside the group refused  (entry 11)
#guard scmTyping 0 64 ⟨P.fns, extP, catalogP, 11⟩ [] u == no "[rcic_scm_typing_entry]"
-- 5 variable in scope has its context type
#guard scmTyping 1 64 P [B, I] (v 1) == ok I
-- 6 variable outside the context refused
#guard scmTyping 1 64 P [B, I] (v 2) == no "[rcic_scm_typing_var_scope]"
-- 7 let binds the value at index 0 of the body context
#guard scmTyping 1 64 P [] (.letE (lb 1) (v 0)) == ok B
-- 8 if condition must be bool
#guard scmTyping 1 64 P [] (.ifE (li 1) (li 1) (li 2)) == no "[rcic_scm_typing_mismatch]"
-- 9 if branches must have one type
#guard scmTyping 1 64 P [] (.ifE (lb 1) (li 1) (lb 0)) == no "[rcic_scm_typing_mismatch]"
-- 10 if with bool condition and equal branches accepted
#guard scmTyping 1 64 P [] (.ifE (lb 1) (li 1) (li 2)) == ok I
-- 11 pair and snd accepted
#guard scmTyping 1 64 P [] (.snd (.pair (li 1) (lb 0))) == ok B
-- 12 fst of a non-pair refused
#guard scmTyping 1 64 P [] (.fst (li 1)) == no "[rcic_scm_typing_shape]"
-- 13 injection into a sum accepted
#guard scmTyping 1 64 P [] (.inj 1 [I, B] (lb 1)) == ok (.sum [I, B])
-- 14 injection index outside the sum refused
#guard scmTyping 1 64 P [] (.inj 2 [I, B] (lb 1)) == no "[rcic_scm_typing_shape]"
-- 15 injection payload not of the summand type refused
#guard scmTyping 1 64 P [] (.inj 0 [I, B] (lb 1)) == no "[rcic_scm_typing_mismatch]"
-- 16 match branch sees the payload at index 0
#guard scmTyping 1 64 P [] (.matchE (.inj 1 [I, B] (lb 1)) [v 0, .ifE (v 0) (li 1) (li 0)]) == ok I
-- 17 match with fewer branches than summands refused
#guard scmTyping 1 64 P [] (.matchE (.inj 0 [I, B] (li 3)) [v 0]) == no "[rcic_scm_typing_shape]"
-- 18 match branches of different types refused
#guard scmTyping 1 64 P [] (.matchE (.inj 0 [I, B] (li 3)) [v 0, v 0]) == no "[rcic_scm_typing_mismatch]"
-- 19 match on a non-sum refused
#guard scmTyping 1 64 P [] (.matchE (li 1) [v 0]) == no "[rcic_scm_typing_shape]"
-- 20 match with no branches on a nonempty sum refused
#guard scmTyping 1 64 P [] (.matchE (.inj 0 [I] (li 3)) []) == no "[rcic_scm_typing_shape]"
-- 21 match on the empty sum has no result type refused
#guard scmTyping 1 64 P [.sum []] (.matchE (v 0) []) == no "[rcic_scm_typing_shape]"
-- 22 record in schema order accepted
#guard scmTyping 1 64 P [] rxy == ok (.record [("x", Str), ("y", I)])
-- 23 record with a duplicate field key refused
#guard scmTyping 1 64 P [] (.recordE ["x", "x"] [ls "s", li 2]) == no "[rcic_scm_typing_record_keys]"
-- 24 record with fewer keys than fields refused
#guard scmTyping 1 64 P [] (.recordE ["x"] [ls "s", li 2]) == no "[rcic_scm_typing_shape]"
-- 25 field projection accepted
#guard scmTyping 1 64 P [] (.field rxy 1) == ok I
-- 26 field index outside the record refused
#guard scmTyping 1 64 P [] (.field rxy 2) == no "[rcic_scm_typing_shape]"
-- 27 field of a non-record refused
#guard scmTyping 1 64 P [] (.field (li 1) 0) == no "[rcic_scm_typing_shape]"
-- 28 cons onto a list of the head type accepted
#guard scmTyping 1 64 P [] (.cons (li 1) (.cons (li 2) (.nil I))) == ok (.list I)
-- 29 cons of a head not of the list element type refused
#guard scmTyping 1 64 P [] (.cons (lb 1) (.nil I)) == no "[rcic_scm_typing_mismatch]"
-- 30 fold body sees element at 0 and accumulator at 1
#guard scmTyping 1 64 P [] (.fold (.cons (lb 1) (.nil B)) (li 0) (.ifE (v 0) (v 1) (li 9))) == ok I
-- 31 fold body not of the accumulator type refused
#guard scmTyping 1 64 P [] (.fold (.cons (li 1) (.nil I)) (li 0) (lb 1)) == no "[rcic_scm_typing_mismatch]"
-- 32 fold over a non-list refused
#guard scmTyping 1 64 P [] (.fold (li 1) (li 0) (v 1)) == no "[rcic_scm_typing_shape]"
-- 33 bounded fix returns converged state steps record
#guard scmTyping 1 64 P [] (.fix (li 0) (li 10) (.prim "lt" [li 5, v 0]) (.prim "add" [v 0, li 1])) == ok fixRec
-- 34 bounded fix limit must be i64
#guard scmTyping 1 64 P [] (.fix (li 0) (lb 1) (lb 1) (v 0)) == no "[rcic_scm_typing_mismatch]"
-- 35 bounded fix stop must be bool
#guard scmTyping 1 64 P [] (.fix (li 0) (li 10) (v 0) (v 0)) == no "[rcic_scm_typing_mismatch]"
-- 36 bounded fix step must return the state type
#guard scmTyping 1 64 P [] (.fix (li 0) (li 10) (lb 1) (lb 0)) == no "[rcic_scm_typing_mismatch]"
-- 37 primitive typed by its closed signature
#guard scmTyping 1 64 P [] (.prim "lt" [li 1, li 2]) == ok B
-- 38 primitive outside the closed enum refused
#guard scmTyping 1 64 P [] (.prim "sha256" [li 1]) == no "[rcic_scm_typing_prim]"
-- 39 primitive argument of the wrong type refused
#guard scmTyping 1 64 P [] (.prim "add" [li 1, lb 1]) == no "[rcic_scm_typing_mismatch]"
-- 40 local call typed by the callee signature
#guard scmTyping 1 64 P [] (.call (.local 0) [li 1, li 2]) == ok I
-- 41 local call ref outside the group refused
#guard scmTyping 1 64 P [] (.call (.local 11) []) == no "[rcic_scm_typing_local_ref]"
-- 42 local call with wrong argument types refused
#guard scmTyping 1 64 P [] (.call (.local 0) [li 1]) == no "[rcic_scm_typing_mismatch]"
-- 43 external call typed by its complete function ref
#guard scmTyping 1 64 P [] (.call (.ext "ext.len") [ls "abc"]) == ok I
-- 44 external call to an unresolved ref refused
#guard scmTyping 1 64 P [] (.call (.ext "ext.missing") [ls "abc"]) == no "[rcic_scm_typing_external_ref]"
-- 45 raise typed by its annotated result and catalog payload
#guard scmTyping 1 64 P [] (.raise "bad_input" (.recordE [] []) B) == ok B
-- 46 raise of a ref outside the catalog refused
#guard scmTyping 1 64 P [] (.raise "stale_ref" (.recordE [] []) B) == no "[rcic_scm_typing_residue_ref]"
-- 47 raise payload not of the catalog payload type refused
#guard scmTyping 1 64 P [] (.raise "range_violation" (lb 1) B) == no "[rcic_scm_typing_mismatch]"
-- 48 handler sees the residue payload at index 0
#guard scmTyping 1 64 P [Str] (.handle "range_violation" (li 1) (v 0)) == ok I
-- 49 handle of a ref outside the catalog refused
#guard scmTyping 1 64 P [] (.handle "stale_ref" (li 1) (li 0)) == no "[rcic_scm_typing_residue_ref]"
-- 50 handler of a different type than the body refused
#guard scmTyping 1 64 P [] (.handle "range_violation" (li 1) (lb 1)) == no "[rcic_scm_typing_mismatch]"
-- 51 literal whose value is not of its type refused
#guard scmTyping 1 64 P [] (.lit (.i 1) B) == no "[rcic_scm_typing_mismatch]"
-- 52 unknown expression kind refused
#guard scmTyping 1 64 P [] (.unknown 99) == no "[rcic_scm_typing_unknown_expr]"
-- 53 fuel exhausted on a deep expression refused not decided
#guard scmTyping 1 3 P [] deep == no "[rcic_scm_typing_fuel]"
-- 54 the same deep expression with enough fuel accepted
#guard scmTyping 1 16 P [] deep == ok I
-- 55 unknown form refused
#guard scmTyping 2 64 P [] (li 0) == no "[rcic_scm_typing_unknown_form]"
-- 56 if branches records differing only in a key refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.recordE ["a"] [li 1]) (.recordE ["b"] [li 1])) == no "[rcic_scm_typing_mismatch]"
-- 57 if branches records differing only in a field type refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.recordE ["a"] [li 1]) (.recordE ["a"] [lb 1])) == no "[rcic_scm_typing_mismatch]"
-- 58 if branches records where the else branch has an extra field refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.recordE ["a"] [li 1]) (.recordE ["a", "b"] [li 1, li 2]))
  == no "[rcic_scm_typing_mismatch]"
-- 59 if branches records where the then branch has an extra field refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.recordE ["a", "b"] [li 1, li 2]) (.recordE ["a"] [li 1]))
  == no "[rcic_scm_typing_mismatch]"
-- 60 if branches pairs differing only in the first component refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.pair (li 1) (li 2)) (.pair (lb 1) (li 2))) == no "[rcic_scm_typing_mismatch]"
-- 61 if branches pairs differing only in the second component refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.pair (li 1) (li 2)) (.pair (li 1) (lb 1))) == no "[rcic_scm_typing_mismatch]"
-- 62 if branches sums differing only in one summand refused
#guard scmTyping 1 64 P [] (.ifE (lb 1) (.inj 0 [I, B] (li 1)) (.inj 0 [I, Str] (li 1))) == no "[rcic_scm_typing_mismatch]"

/-! Instance witnesses (M-005): a closed intrinsic expression for every
    judgment form the pins exercise is built by `elabE` above; one is
    exhibited directly. -/
example : CoreExpr (sigOf P) [] .i64 :=
  .letE (.lit (.i64V 41 ⟨by decide, by decide⟩))
    (.prim .add (.cons (.var 0 rfl) (.cons (.lit (.i64V 1 ⟨by decide, by decide⟩)) .nil)))

end Rcic.Scm.ExprPins
