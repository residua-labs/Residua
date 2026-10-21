/-
RCIC apex: the row identifiers of the mandatory chapters, and `GlobalRows`
(Annex 24 §24.2).

Owner text:
  Annex 24 §24.2 (`docs/rcic/00_ANNEX_24_CONJUNCT_BODIES.md:68-70`):
    "GlobalRows := the RF rows of 01 §15 ('Normative theorem interfaces')
     ∪ the AH rows of 10 §23 other than AH-003 and AH-004".
  `AxisCommon` (A24:58-66) quantifies over "every row in `rows`", per axis, and
  over every row in `GlobalRows`.

A `RowId` is an identifier only: the chapter prefix and the row number. It
does not transcribe the row's proposition; that proposition is the subject of
the row's own mechanization (00 §16 M-001). The rows below are the
theorem-interface lists of the mandatory chapters (00 §5; chapters 11 and 13 are
optional axes and are excluded). In each chapter the ids are `PREFIX-001` …
`PREFIX-N`, consecutive. That was measured on main `853a371b6c`; the line
ranges are:

  RF 01:451-471 (21)   DT 02:376-401 (26)   RM 03:367-391 (25)
  EG 04:346-370 (25)   IA 05:344-371 (28)   SCM 06:452-470 (19)
  CT 07:537-559 (23)   WX 08:423-442 (20)   CG 09:490-509 (20)
  AH 10:470-490 (21)   RR 12:536-560 (25)   total 253

The counts below are checked by `decide`. `closure_claim` stays 0.
-/

namespace Rcic.Apex

/-- The row prefixes of the mandatory chapters 01…10 and 12. -/
inductive Chapter where
  | RF | DT | RM | EG | IA | SCM | CT | WX | CG | AH | RR
  deriving DecidableEq, Repr

/-- The number of rows in each chapter's theorem-interface list (see the header for the line ranges). -/
def Chapter.rowCount : Chapter → Nat
  | .RF => 21 | .DT => 26 | .RM => 25 | .EG => 25 | .IA => 28 | .SCM => 19
  | .CT => 23 | .WX => 20 | .CG => 20 | .AH => 21 | .RR => 25

/-- A row id `PREFIX-NNN`: the chapter and the row number. -/
structure RowId where
  ch : Chapter
  n : Nat
  deriving DecidableEq, Repr

/-- The rows of one chapter: `PREFIX-001` … `PREFIX-N`. -/
def rowsOf (ch : Chapter) : List RowId := (List.range ch.rowCount).map fun i => ⟨ch, i + 1⟩

/-- The rows numbered `a` through `b` (inclusive) of one chapter, e.g. SCM-001 … SCM-012. -/
def rowsBetween (ch : Chapter) (a b : Nat) : List RowId :=
  (rowsOf ch).filter fun r => a ≤ r.n && r.n ≤ b

/-- The mandatory chapters (00 §5). -/
def chapters : List Chapter := [.RF, .DT, .RM, .EG, .IA, .SCM, .CT, .WX, .CG, .AH, .RR]

/-- All rows of all mandatory chapters. -/
def allRows : List RowId := chapters.foldr (fun ch acc => rowsOf ch ++ acc) []

/-- A24:68-70: the RF rows, together with the AH rows other than AH-003 and AH-004. -/
def GlobalRows : List RowId :=
  rowsOf .RF ++ (rowsOf .AH).filter fun r => r.n != 3 && r.n != 4

theorem rowsOf_length (ch : Chapter) : (rowsOf ch).length = ch.rowCount := by
  simp [rowsOf]

theorem allRows_length : allRows.length = 253 := by
  simp [allRows, chapters, rowsOf_length, Chapter.rowCount]

theorem globalRows_length : GlobalRows.length = 40 := by decide

/-- AH-003 and AH-004 are outside `GlobalRows`; `BootstrapClosed` names them itself (A24:125). -/
theorem AH003_AH004_not_global :
    (⟨.AH, 3⟩ : RowId) ∉ GlobalRows ∧ (⟨.AH, 4⟩ : RowId) ∉ GlobalRows := by decide

/-- Every RF row, and every other AH row, is in `GlobalRows`. -/
theorem RF021_AH021_global : (⟨.RF, 21⟩ : RowId) ∈ GlobalRows ∧ (⟨.AH, 21⟩ : RowId) ∈ GlobalRows := by
  decide

/-- The SCM split of S-1 (A24:270-274): rows 001…012 go to the semantics and 013…019 to the embedding. -/
theorem scm_split_length :
    (rowsBetween .SCM 1 12).length = 12 ∧ (rowsBetween .SCM 13 19).length = 7 := by decide

end Rcic.Apex
