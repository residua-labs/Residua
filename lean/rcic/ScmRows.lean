/-
RCIC 06 §6–§7 — derived residue rows as a least fixed point (SCM-003/004).

Owner text (06 §7, 06:118-150): "Candidate signatures contain parameter and
result types only. Their residue rows are derived as the least fixed point
over: direct raises, primitive rows, external call rows, local recursive
call equations, handler removal. A recursive call cycle cannot mint a
residue absent from every direct/external source." §6: "ResidueRow :=
canonical sorted unique list ResidueRef".

PIN (M-002): `residueRows` is `rcic.residue_rows form functions target fuel`
of `apps/rcic-residue-rows` (15 rows below). Each function is
`{name, direct, external, handled}`: `direct` its own raises (primitive rows
included), `external` the callees whose rows it absorbs, `handled` the refs
its handlers remove. The fixed point iterates from the direct rows; a pass
that leaves the table unchanged confirms it, and every pass, the confirming
one included, costs one unit of fuel (GM-OUT-004).

TRANSCRIPTION TABLE (06 → Lean):
  §6 ResidueRow canonical sorted unique          → `rowInsert` / `rowCanon`
  §7 direct raises (+ primitive rows)            → `RowFn.direct`
  §7 external call rows / local call equations   → `RowFn.external`, `rowPassOne`
  §7 handler removal                             → `RowFn.handled`, `rowMinus`
  §7 least fixed point                           → `rowFix` from `rowInit`
-/
import rcic.ScmCore

namespace Rcic.Scm.Rows

structure RowFn where
  name : String
  direct : List String
  external : List String
  handled : List String

structure RowEntry where
  name : String
  row : List String
  deriving BEq

/-- `rcic.residue_rows_insert`: insert into a strictly ascending row. -/
def rowInsert (r : String) : List String → List String
  | [] => [r]
  | y :: ys => if r = y then y :: ys else if r < y then r :: y :: ys else y :: rowInsert r ys

def rowCanon (xs : List String) : List String := xs.foldl (fun acc r => rowInsert r acc) []
def rowUnion (xs ys : List String) : List String := ys.foldl (fun acc r => rowInsert r acc) xs
def rowMinus (xs drop : List String) : List String := xs.filter (fun r => !drop.contains r)

def rowAt (table : List RowEntry) (name : String) : List String :=
  match table.find? (fun e => e.name = name) with
  | some e => e.row
  | none => []

def rowExtUnion (table : List RowEntry) (callees : List String) : List String :=
  callees.foldl (fun acc c => rowUnion acc (rowAt table c)) []

def rowPassOne (table : List RowEntry) (f : RowFn) : List String :=
  rowMinus (rowUnion (rowCanon f.direct) (rowExtUnion table f.external)) f.handled

def rowInit (fns : List RowFn) : List RowEntry := fns.map (fun f => ⟨f.name, rowCanon f.direct⟩)
def rowPass (fns : List RowFn) (table : List RowEntry) : List RowEntry :=
  fns.map (fun f => ⟨f.name, rowPassOne table f⟩)

/-- Iterate to the least fixed point; every pass costs one unit. -/
def rowFix (fns : List RowFn) : List RowEntry → Nat → Option (List RowEntry)
  | _, 0 => none
  | table, n + 1 =>
    let next := rowPass fns table
    if table == next then some next else rowFix fns next n

structure RowsOut where
  ok : Int
  target : String
  row : List String
  code : String
  deriving BEq

def residueRows (form : Int) (fns : List RowFn) (target : String) (fuel : Int) : RowsOut :=
  if form ≠ 0 then ⟨0, target, [], "[rcic_residue_rows_unknown_form]"⟩ else
  match fns.find? (fun f => f.name = target) with
  | none => ⟨0, target, [], "[rcic_residue_rows_target_not_found]"⟩
  | some _ =>
    if fuel < 0 then ⟨0, target, [], "[rcic_residue_rows_fuel]"⟩ else
    match rowFix fns (rowInit fns) fuel.toNat with
    | some t => ⟨1, target, rowAt t target, ""⟩
    | none => ⟨0, target, [], "[rcic_residue_rows_fuel]"⟩

/-! ## Pins: apps/rcic-residue-rows/rcic_residue_rows_corpus.json, 15 rows -/

namespace Pins
def solo : List RowFn := [⟨"solo", ["[signed_overflow]", "[bad_split]"], [], []⟩]
def fgh (z : String) (hExt : List String) : List RowFn :=
  [⟨"f", [], ["g"], []⟩, ⟨"g", [], ["h"], []⟩, ⟨"h", [z], hExt, []⟩]
def fgCycle : List RowFn := [⟨"f", [], ["g"], []⟩, ⟨"g", ["[io_short_read]"], ["f"], []⟩]
def ok (t : String) (row : List String) : RowsOut := ⟨1, t, row, ""⟩
def no (t code : String) : RowsOut := ⟨0, t, [], code⟩

-- 0 SCM-003 single function direct raises only row is canonical sorted direct
#guard residueRows 0 solo "solo" 8 == ok "solo" ["[bad_split]", "[signed_overflow]"]
-- 1 GM-SCM-001 two-hop f->g->h h raises [range_violation] f row gains it only after iteration to fixpoint
#guard residueRows 0 (fgh "[range_violation]" []) "f" 8 == ok "f" ["[range_violation]"]
-- 2 handler removal g raises two f handles [stale_ref] away row keeps [ok_passthrough]
#guard residueRows 0 [⟨"f", [], ["g"], ["[stale_ref]"]⟩, ⟨"g", ["[stale_ref]", "[ok_passthrough]"], [], []⟩] "f" 8
  == ok "f" ["[ok_passthrough]"]
-- 3 GM-SCM-002 cycle f<->g no direct raises anywhere both rows empty cycle mints nothing
#guard residueRows 0 [⟨"f", [], ["g"], []⟩, ⟨"g", [], ["f"], []⟩] "f" 8 == ok "f" []
-- 4 SCM-004 cycle with one direct source propagates around without minting
#guard residueRows 0 fgCycle "f" 8 == ok "f" ["[io_short_read]"]
-- 5 SCM-004 self-recursion without direct raise row is empty
#guard residueRows 0 [⟨"f", [], ["f"], []⟩] "f" 8 == ok "f" []
-- 6 SCM-003 fixpoint idempotence tight fuel same row
#guard residueRows 0 fgCycle "f" 2 == ok "f" ["[io_short_read]"]
-- 7 SCM-003 fixpoint idempotence ample fuel same row
#guard residueRows 0 fgCycle "f" 9 == ok "f" ["[io_short_read]"]
-- 8 GM-OUT-004 adjacency fuel exhaustion mid-iteration is suspension never a cached partial row
#guard residueRows 0 (fgh "[range_violation]" []) "f" 0 == no "f" "[rcic_residue_rows_fuel]"
-- 9 negative fuel refused as fuel suspension
#guard residueRows 0 solo "solo" (-1) == no "solo" "[rcic_residue_rows_fuel]"
-- 10 unknown target refused
#guard residueRows 0 solo "zzz_missing" 8 == no "zzz_missing" "[rcic_residue_rows_target_not_found]"
-- 11 unknown form refused
#guard residueRows 7 solo "solo" 8 == no "solo" "[rcic_residue_rows_unknown_form]"
-- 12 GM-OUT-004 single function confirming fixpoint pass is charged fuel zero refuses
#guard residueRows 0 solo "solo" 0 == no "solo" "[rcic_residue_rows_fuel]"
-- 13 GM-OUT-004 single function one fuel unit pays the confirming pass accepts
#guard residueRows 0 solo "solo" 1 == ok "solo" ["[bad_split]", "[signed_overflow]"]
-- 14 V4 stop-when-target-row-stable killer: 3-cycle f->g->h->f with direct [z] on h, target f
#guard residueRows 0 (fgh "[z]" ["f"]) "f" 8 == ok "f" ["[z]"]
end Pins

end Rcic.Scm.Rows
