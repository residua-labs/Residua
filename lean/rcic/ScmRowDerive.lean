/-
RCIC 06 §6–§7, §16 — the scoped residue-row derivation over core programs
(SCM-003 / SCM-004; #6029 K4 precondition).

Owner text:
  06 §7 (06:128-138) "Candidate signatures contain parameter and result types
      only. Their residue rows are derived as the least fixed point over:
      direct raises, primitive rows, external call rows, local recursive call
      equations, handler removal. A recursive call cycle cannot mint a residue
      absent from every direct/external source."
  06 §6 (06:110-114) "ResidueRow := canonical sorted unique list ResidueRef".
  06 §9 (06:198) "A nonmatching raised residue propagates unchanged."
  06 §11 (06:222) "Each op has exact argument/result types, direct residue
      row, mathematical law, and explicit machine implementation."
  06 §12 (06:240) "A negative limit SCM-raises `negative_loop_bound`."
  06 §16 (06:311) "residue-row safety: every raised ref is in the derived
      entry row".
  06 §17 (06:336-337) "4. decode typed bodies; 5. derive residue least fixed
      points".
  00 §19.7 errata: E-06HandlerScope (a handler removes its ref from its own
  body's row only), E-06LenRows (`str_len` / `bytes_len` have the direct row
  {`signed_overflow`}), E-06RaiseSources (raised residues come from `raise`
  and from the §11 / §12 SCM-raise outcomes).

PIN (M-002): `scmRows` is `rcic.scm_rows form fuel prog tbl` of
`apps/rcic-scm-rows` (49 rows in `Pins`, hand-transcribed, §18.3 rule 4). The
carrier types the program (`rcic.scm_ty_prog`, here `progCheck`), refuses an
external call, then form 0 derives the table by exactly
`|fns| * (|catalog| + 8) + 1` passes from the empty table and form 1 decides
whether a presented table is a prefixpoint. The multi-group entry `scmRowsCl`
is the §7 bundle analogue: it derives/decides the same equation with external
names resolved through `ExtResolve` and refuses an unresolvable one.

TRANSCRIPTION TABLE (06 → Lean):
  §7 direct raises                       → `rowL` `raise` case (`rowInsert r'`)
  §7 primitive rows, §11 direct row      → `rowL` `prim` case (`primRow op`)
  §7 local recursive call equations      → `rowL` local `call` case (`t.getD i []`)
  §7 handler removal (E-06HandlerScope)  → `rowL` `handle` case: `rowMinus` on
        the body's row only; the handler expression's row is kept
  §12 SCM-raise of a negative limit      → `rowL` `boundedFix` case
        (`negative_loop_bound`, whatever the limit expression)
  §7 external call rows                  → `rowL` external `call` case:
        `rowUnion args.rowL (xr n)` — the callee's row enters through the
        external resolver `xr` (single-group carrier keeps `xr = ∅` and
        refuses `[rcic_scm_rows_external_call]` on `Bodies.hasExt`;
        `deriveRowsCl` over a `RowGrp` bundle resolves `n` to a
        `(group, member)` cell via `ExtResolve`, and `scmRowsCl` refuses
        `[rcic_scm_rows_external_ref]` on any name `resolve` leaves open)
  §6 canonical sorted unique             → `Rows.rowInsert` / `rowUnion` /
        `rowMinus` (the modules `rcic.residue_rows_insert/union/minus`,
        reused by the carrier); canonicity is decided per instance by the pins
  §7 least fixed point                   → `deriveRows`; `derive_prefix` (it is
        a prefixpoint of the equations) and `derive_least` (it lies below every
        prefixpoint): it is THE least fixed point, hence unique (SCM-003)
  §7 a cycle cannot mint                 → `derive_no_mint` (SCM-004): every
        derived ref has a direct source in some body
  §16 residue-row safety                 → `derive_row_safety`,
        `derive_empty_no_raise` (through `RowSafety.residue_row_safety`)
  §17 rows after typed bodies            → `scmRows` runs `progCheck` first;
        `scmRows_form0_sound`
-/
import rcic.ScmRowSafety
import rcic.ScmRows

namespace Rcic.Scm.RowDerive
open Rcic.Scm Rcic.Scm.Rows

/-- A row table: row `i` belongs to the function at group index `i`. -/
abbrev Tbl := List (List String)

/-- A table read as a row assignment (the `ρ` of `CoreExpr.Row`). -/
abbrev tblRho (t : Tbl) : Nat → RaisedRef → Prop := fun i r => r ∈ t.getD i []

/-- An external-row resolver read as a row assignment (the `ρx` of
    `CoreExpr.Row`): it names the callee's derived row for an external
    reference. -/
abbrev xrRho (xr : String → List String) : String → RaisedRef → Prop := fun n r => r ∈ xr n

/-! ## Membership of the canonical row operations -/

theorem mem_rowInsert (x r : String) : ∀ (ys : List String), x ∈ rowInsert r ys ↔ x = r ∨ x ∈ ys
  | [] => by
      show x ∈ [r] ↔ x = r ∨ x ∈ ([] : List String)
      exact ⟨fun h => Or.inl (List.mem_singleton.mp h),
        fun h => h.elim (fun e => List.mem_singleton.mpr e) (fun h' => absurd h' (List.not_mem_nil x))⟩
  | y :: ys => by
      show x ∈ (if r = y then y :: ys else if r < y then r :: y :: ys else y :: rowInsert r ys) ↔
        x = r ∨ x ∈ y :: ys
      by_cases h1 : r = y
      · rw [if_pos h1, ← h1]
        exact ⟨Or.inr, fun h => h.elim (fun e => by rw [e]; exact List.mem_cons_self r ys) id⟩
      · rw [if_neg h1]
        by_cases h2 : r < y
        · rw [if_pos h2]
          exact List.mem_cons
        · rw [if_neg h2, List.mem_cons, mem_rowInsert x r ys, List.mem_cons]
          exact ⟨fun h => h.elim (fun e => Or.inr (Or.inl e)) (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inr h''))),
            fun h => h.elim (fun e => Or.inr (Or.inl e)) (fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inr h'')))⟩

theorem mem_rowUnion (x : String) : ∀ (ys xs : List String), x ∈ rowUnion xs ys ↔ x ∈ xs ∨ x ∈ ys
  | [], xs => by
      show x ∈ xs ↔ x ∈ xs ∨ x ∈ ([] : List String)
      exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd h' (List.not_mem_nil x))⟩
  | y :: ys, xs => by
      show x ∈ rowUnion (rowInsert y xs) ys ↔ x ∈ xs ∨ x ∈ y :: ys
      rw [mem_rowUnion x ys (rowInsert y xs), mem_rowInsert, List.mem_cons]
      exact ⟨fun h => h.elim (fun h1 => h1.elim (fun e => Or.inr (Or.inl e)) Or.inl) (fun h2 => Or.inr (Or.inr h2)),
        fun h => h.elim (fun h1 => Or.inl (Or.inr h1)) (fun h2 => h2.elim (fun e => Or.inl (Or.inl e)) Or.inr)⟩

theorem mem_rowMinus (x : String) (xs drop : List String) : x ∈ rowMinus xs drop ↔ x ∈ xs ∧ x ∉ drop := by
  show x ∈ xs.filter (fun r => !drop.contains r) ↔ x ∈ xs ∧ x ∉ drop
  rw [List.mem_filter]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, fun hd => ?_⟩
    have hc : drop.contains x = true := List.elem_iff.mpr hd
    rw [hc] at h2
    exact absurd h2 (by decide)
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases hc : drop.contains x with
    | false => rfl
    | true => exact absurd (List.elem_iff.mp hc) h2

theorem not_mem_singleton {x r : String} : x ∉ [r] ↔ x ≠ r :=
  ⟨fun h e => h (List.mem_singleton.mpr e), fun h m => h (List.mem_singleton.mp m)⟩

end Rcic.Scm.RowDerive

namespace Rcic.Scm
open Rcic.Scm.Rows Rcic.Scm.RowDerive

/-! ## The row of an expression under a table (computable) -/

section Rows
variable {S : Sig} (t : Tbl) (xr : String → List String)

mutual
/-- The row equations of `CoreExpr.Row`, computed over a table: a raise adds
    its ref, a primitive its direct row, a bounded fix `negative_loop_bound`,
    a local call the callee's table row, and a handler removes its ref from
    its BODY's row only. -/
def CoreExpr.rowL : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → List String
  | _, _, .lit _ => []
  | _, _, .var _ _ => []
  | _, _, .letE a b => rowUnion a.rowL b.rowL
  | _, _, .ifE c th el => rowUnion c.rowL (rowUnion th.rowL el.rowL)
  | _, _, .pairE a b => rowUnion a.rowL b.rowL
  | _, _, .fstE a => a.rowL
  | _, _, .sndE a => a.rowL
  | _, _, .injE _ _ _ a => a.rowL
  | _, _, .matchSum s bs _ => rowUnion s.rowL bs.rowL
  | _, _, .recordE xs _ => xs.rowL
  | _, _, .fieldE _ _ _ e => e.rowL
  | _, _, .nilE => []
  | _, _, .consE h tl => rowUnion h.rowL tl.rowL
  | _, _, .foldList l init body => rowUnion l.rowL (rowUnion init.rowL body.rowL)
  | _, _, .boundedFix init limit stop step =>
      rowUnion init.rowL (rowUnion limit.rowL (rowUnion stop.rowL (rowUnion step.rowL ["negative_loop_bound"])))
  | _, _, .prim op args => rowUnion (primRow op) args.rowL
  | _, _, .call (.local i _ _) args => rowUnion (t.getD i []) args.rowL
  | _, _, .call (.external n _ _) args => rowUnion args.rowL (xr n)
  | _, _, .raise r' _ p => rowInsert r' p.rowL
  | _, _, .handle r' _ body hd => rowUnion (rowMinus body.rowL [r']) hd.rowL
def Branches.rowL : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → List String
  | _, _, _, .nil => []
  | _, _, _, .cons b bs => rowUnion b.rowL bs.rowL
def Fields.rowL : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → List String
  | _, _, .nil => []
  | _, _, .cons _ x xs => rowUnion x.rowL xs.rowL
def Args.rowL : {Γ ps : List CoreTy} → Args S Γ ps → List String
  | _, _, .nil => []
  | _, _, .cons x xs => rowUnion x.rowL xs.rowL
end

/-- One pass: the row of every body under the table, in group order. -/
def Bodies.rowsL : {fs : List FnSig} → Bodies S fs → Tbl
  | _, .nil => []
  | _, .cons b bs => b.rowL t xr :: Bodies.rowsL bs

end Rows

section Ext
variable {S : Sig}

mutual
/-- An external call occurs somewhere in the expression. -/
def CoreExpr.hasExt : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → Bool
  | _, _, .lit _ => false
  | _, _, .var _ _ => false
  | _, _, .letE a b => a.hasExt || b.hasExt
  | _, _, .ifE c th el => c.hasExt || th.hasExt || el.hasExt
  | _, _, .pairE a b => a.hasExt || b.hasExt
  | _, _, .fstE a => a.hasExt
  | _, _, .sndE a => a.hasExt
  | _, _, .injE _ _ _ a => a.hasExt
  | _, _, .matchSum s bs _ => s.hasExt || bs.hasExt
  | _, _, .recordE xs _ => xs.hasExt
  | _, _, .fieldE _ _ _ e => e.hasExt
  | _, _, .nilE => false
  | _, _, .consE h tl => h.hasExt || tl.hasExt
  | _, _, .foldList l init body => l.hasExt || init.hasExt || body.hasExt
  | _, _, .boundedFix init limit stop step => init.hasExt || limit.hasExt || stop.hasExt || step.hasExt
  | _, _, .prim _ args => args.hasExt
  | _, _, .call (.local _ _ _) args => args.hasExt
  | _, _, .call (.external _ _ _) _ => true
  | _, _, .raise _ _ p => p.hasExt
  | _, _, .handle _ _ body hd => body.hasExt || hd.hasExt
def Branches.hasExt : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → Bool
  | _, _, _, .nil => false
  | _, _, _, .cons b bs => b.hasExt || bs.hasExt
def Fields.hasExt : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → Bool
  | _, _, .nil => false
  | _, _, .cons _ x xs => x.hasExt || xs.hasExt
def Args.hasExt : {Γ ps : List CoreTy} → Args S Γ ps → Bool
  | _, _, .nil => false
  | _, _, .cons x xs => x.hasExt || xs.hasExt
end

def Bodies.hasExt : {fs : List FnSig} → Bodies S fs → Bool
  | _, .nil => false
  | _, .cons b bs => b.hasExt || Bodies.hasExt bs

mutual
/-- The external reference names a body calls (§7 external call rows). -/
def CoreExpr.extNames : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → List String
  | _, _, .lit _ => []
  | _, _, .var _ _ => []
  | _, _, .letE a b => a.extNames ++ b.extNames
  | _, _, .ifE c th el => c.extNames ++ th.extNames ++ el.extNames
  | _, _, .pairE a b => a.extNames ++ b.extNames
  | _, _, .fstE a => a.extNames
  | _, _, .sndE a => a.extNames
  | _, _, .injE _ _ _ a => a.extNames
  | _, _, .matchSum s bs _ => s.extNames ++ bs.extNames
  | _, _, .recordE xs _ => xs.extNames
  | _, _, .fieldE _ _ _ e => e.extNames
  | _, _, .nilE => []
  | _, _, .consE h tl => h.extNames ++ tl.extNames
  | _, _, .foldList l init body => l.extNames ++ init.extNames ++ body.extNames
  | _, _, .boundedFix init limit stop step => init.extNames ++ limit.extNames ++ stop.extNames ++ step.extNames
  | _, _, .prim _ args => args.extNames
  | _, _, .call (.local _ _ _) args => args.extNames
  | _, _, .call (.external n _ _) args => n :: args.extNames
  | _, _, .raise _ _ p => p.extNames
  | _, _, .handle _ _ body hd => body.extNames ++ hd.extNames
def Branches.extNames : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → List String
  | _, _, _, .nil => []
  | _, _, _, .cons b bs => b.extNames ++ bs.extNames
def Fields.extNames : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → List String
  | _, _, .nil => []
  | _, _, .cons _ x xs => x.extNames ++ xs.extNames
def Args.extNames : {Γ ps : List CoreTy} → Args S Γ ps → List String
  | _, _, .nil => []
  | _, _, .cons x xs => x.extNames ++ xs.extNames
end

def Bodies.extNames : {fs : List FnSig} → Bodies S fs → List String
  | _, .nil => []
  | _, .cons b bs => b.extNames ++ Bodies.extNames bs

end Ext

end Rcic.Scm

namespace Rcic.Scm.RowDerive
open Rcic.Scm Rcic.Scm.Rows

/-! ## The derivation: Kleene iteration from the empty table -/

def iterN {α : Type} (F : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => F (iterN F n x)

/-- The pass count of the carrier: `|fns| * (|catalog| + 8) + 1`. -/
def passes (S : Sig) : Nat := S.fns.length * (S.catalog.length + 8) + 1

/-- The `n`-th Kleene iterate from the empty table.  A one-group bundle has
    no callee group, so the external resolver is empty (`hasExt`-free
    programs never consult it). -/
def seq {S : Sig} (bs : Bodies S S.fns) (n : Nat) : Tbl :=
  iterN (fun x => bs.rowsL x (fun _ => [])) n (List.replicate S.fns.length [])

/-- The derived table (06 §7): exactly `passes S` passes from the empty table. -/
def deriveRows {S : Sig} (bs : Bodies S S.fns) : Tbl := seq bs (passes S)

/-! ## The carrier entry point -/

structure DeriveOut where
  ok : Int
  rows : Tbl
  row : List String
  pfx : Int
  idx : Int
  code : String
  deriving BEq

def refuse (c : String) : DeriveOut := ⟨0, [], [], 0, -1, c⟩

/-- The first index (from `i`) whose pass row has a ref outside the table's
    row at that index; `-1` when there is none. -/
def firstFail (t : Tbl) : Nat → Tbl → Int
  | _, [] => -1
  | i, p :: ps => if p.all (fun r => (t.getD i []).contains r) then firstFail t (i + 1) ps else i

def scmRows (form fuel : Int) (p : RawProg) (tbl : Tbl) : DeriveOut :=
  if form < 0 then refuse "[rcic_scm_rows_unknown_form]" else
  if form > 1 then refuse "[rcic_scm_rows_unknown_form]" else
  match progCheck fuel p with
  | .error c => refuse c
  | .ok ⟨bs, _⟩ =>
    if bs.hasExt then refuse "[rcic_scm_rows_external_call]" else
    if form = 0 then
      let t := deriveRows bs
      ⟨1, t, t.getD p.entry.toNat [], 1, -1, ""⟩
    else
      if tbl.length ≠ p.fns.length then refuse "[rcic_scm_rows_table]" else
      if !(tbl.all (fun r => rowCanon r == r)) then refuse "[rcic_scm_rows_table]" else
      let i := firstFail tbl 0 (bs.rowsL tbl (fun _ => []))
      ⟨1, tbl, tbl.getD p.entry.toNat [], if i = -1 then 1 else 0, i, ""⟩


end Rcic.Scm.RowDerive

/-! ## The row equations computed = the row equations stated -/

namespace Rcic.Scm
open Rcic.Scm.Rows Rcic.Scm.RowDerive

section RowIff
variable {S : Sig} (t : Tbl) (xr : String → List String)

mutual
theorem CoreExpr.rowL_iff : ∀ {Γ : List CoreTy} {T : CoreTy} (e : CoreExpr S Γ T) (r : String),
    r ∈ e.rowL t xr ↔ e.Row (tblRho t) (xrRho xr) r
  | _, _, .lit _, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, .var _ _, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, .letE a b, r => by
      show r ∈ rowUnion (a.rowL t xr) (b.rowL t xr) ↔ a.Row (tblRho t) (xrRho xr) r ∨ b.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff a r, CoreExpr.rowL_iff b r]
  | _, _, .ifE c th el, r => by
      show r ∈ rowUnion (c.rowL t xr) (rowUnion (th.rowL t xr) (el.rowL t xr)) ↔
        c.Row (tblRho t) (xrRho xr) r ∨ th.Row (tblRho t) (xrRho xr) r ∨ el.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, mem_rowUnion, CoreExpr.rowL_iff c r, CoreExpr.rowL_iff th r, CoreExpr.rowL_iff el r]
  | _, _, .pairE a b, r => by
      show r ∈ rowUnion (a.rowL t xr) (b.rowL t xr) ↔ a.Row (tblRho t) (xrRho xr) r ∨ b.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff a r, CoreExpr.rowL_iff b r]
  | _, _, .fstE a, r => CoreExpr.rowL_iff a r
  | _, _, .sndE a, r => CoreExpr.rowL_iff a r
  | _, _, .injE _ _ _ a, r => CoreExpr.rowL_iff a r
  | _, _, .matchSum s bs _, r => by
      show r ∈ rowUnion (s.rowL t xr) (bs.rowL t xr) ↔ s.Row (tblRho t) (xrRho xr) r ∨ bs.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff s r, Branches.rowL_iff bs r]
  | _, _, .recordE xs _, r => Fields.rowL_iff xs r
  | _, _, .fieldE _ _ _ e, r => CoreExpr.rowL_iff e r
  | _, _, .nilE, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, .consE h tl, r => by
      show r ∈ rowUnion (h.rowL t xr) (tl.rowL t xr) ↔ h.Row (tblRho t) (xrRho xr) r ∨ tl.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff h r, CoreExpr.rowL_iff tl r]
  | _, _, .foldList l init body, r => by
      show r ∈ rowUnion (l.rowL t xr) (rowUnion (init.rowL t xr) (body.rowL t xr)) ↔
        l.Row (tblRho t) (xrRho xr) r ∨ init.Row (tblRho t) (xrRho xr) r ∨ body.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, mem_rowUnion, CoreExpr.rowL_iff l r, CoreExpr.rowL_iff init r,
        CoreExpr.rowL_iff body r]
  | _, _, .boundedFix init limit stop step, r => by
      show r ∈ rowUnion (init.rowL t xr) (rowUnion (limit.rowL t xr) (rowUnion (stop.rowL t xr)
          (rowUnion (step.rowL t xr) ["negative_loop_bound"]))) ↔
        init.Row (tblRho t) (xrRho xr) r ∨ limit.Row (tblRho t) (xrRho xr) r ∨ stop.Row (tblRho t) (xrRho xr) r ∨
          step.Row (tblRho t) (xrRho xr) r ∨ r = "negative_loop_bound"
      rw [mem_rowUnion, mem_rowUnion, mem_rowUnion, mem_rowUnion, List.mem_singleton,
        CoreExpr.rowL_iff init r, CoreExpr.rowL_iff limit r, CoreExpr.rowL_iff stop r,
        CoreExpr.rowL_iff step r]
  | _, _, .prim op args, r => by
      show r ∈ rowUnion (primRow op) (args.rowL t xr) ↔ r ∈ primRow op ∨ args.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, Args.rowL_iff args r]
  | _, _, .call (.local i _ _) args, r => by
      show r ∈ rowUnion (t.getD i []) (args.rowL t xr) ↔ tblRho t i r ∨ args.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, Args.rowL_iff args r]
  | _, _, .call (.external n _ _) args, r => by
      show r ∈ rowUnion (args.rowL t xr) (xr n) ↔ args.Row (tblRho t) (xrRho xr) r ∨ xrRho xr n r
      rw [mem_rowUnion, Args.rowL_iff args r]
  | _, _, .raise r' _ p, r => by
      show r ∈ rowInsert r' (p.rowL t xr) ↔ r = r' ∨ p.Row (tblRho t) (xrRho xr) r
      rw [mem_rowInsert, CoreExpr.rowL_iff p r]
  | _, _, .handle r' _ body hd, r => by
      show r ∈ rowUnion (rowMinus (body.rowL t xr) [r']) (hd.rowL t xr) ↔
        (body.Row (tblRho t) (xrRho xr) r ∧ r ≠ r') ∨ hd.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, mem_rowMinus, not_mem_singleton, CoreExpr.rowL_iff body r, CoreExpr.rowL_iff hd r]
theorem Branches.rowL_iff : ∀ {Γ ts : List CoreTy} {T : CoreTy} (bs : Branches S Γ ts T) (r : String),
    r ∈ bs.rowL t xr ↔ bs.Row (tblRho t) (xrRho xr) r
  | _, _, _, .nil, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, _, .cons b bs, r => by
      show r ∈ rowUnion (b.rowL t xr) (bs.rowL t xr) ↔ b.Row (tblRho t) (xrRho xr) r ∨ bs.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff b r, Branches.rowL_iff bs r]
theorem Fields.rowL_iff : ∀ {Γ : List CoreTy} {fs : List (String × CoreTy)} (xs : Fields S Γ fs) (r : String),
    r ∈ xs.rowL t xr ↔ xs.Row (tblRho t) (xrRho xr) r
  | _, _, .nil, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, .cons _ x xs, r => by
      show r ∈ rowUnion (x.rowL t xr) (xs.rowL t xr) ↔ x.Row (tblRho t) (xrRho xr) r ∨ xs.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff x r, Fields.rowL_iff xs r]
theorem Args.rowL_iff : ∀ {Γ ps : List CoreTy} (xs : Args S Γ ps) (r : String),
    r ∈ xs.rowL t xr ↔ xs.Row (tblRho t) (xrRho xr) r
  | _, _, .nil, r => ⟨fun h => absurd h (List.not_mem_nil r), fun h => h.elim⟩
  | _, _, .cons x xs, r => by
      show r ∈ rowUnion (x.rowL t xr) (xs.rowL t xr) ↔ x.Row (tblRho t) (xrRho xr) r ∨ xs.Row (tblRho t) (xrRho xr) r
      rw [mem_rowUnion, CoreExpr.rowL_iff x r, Args.rowL_iff xs r]
end

end RowIff

section Mono
variable {S : Sig} {ρ ρ' : Nat → RaisedRef → Prop} {ρx ρx' : String → RaisedRef → Prop}

mutual
/-- The row equations are monotone in the row assignment. -/
theorem CoreExpr.Row_mono (hρ : ∀ i r, ρ i r → ρ' i r) (hρx : ∀ n r, ρx n r → ρx' n r) : ∀ {Γ : List CoreTy} {T : CoreTy}
    (e : CoreExpr S Γ T) (r : String), e.Row ρ ρx r → e.Row ρ' ρx' r
  | _, _, .lit _, _, h => h
  | _, _, .var _ _, _, h => h
  | _, _, .letE a b, r, h => Or.imp (CoreExpr.Row_mono hρ hρx a r) (CoreExpr.Row_mono hρ hρx b r) h
  | _, _, .ifE c th el, r, h =>
      Or.imp (CoreExpr.Row_mono hρ hρx c r) (Or.imp (CoreExpr.Row_mono hρ hρx th r) (CoreExpr.Row_mono hρ hρx el r)) h
  | _, _, .pairE a b, r, h => Or.imp (CoreExpr.Row_mono hρ hρx a r) (CoreExpr.Row_mono hρ hρx b r) h
  | _, _, .fstE a, r, h => CoreExpr.Row_mono hρ hρx a r h
  | _, _, .sndE a, r, h => CoreExpr.Row_mono hρ hρx a r h
  | _, _, .injE _ _ _ a, r, h => CoreExpr.Row_mono hρ hρx a r h
  | _, _, .matchSum s bs _, r, h => Or.imp (CoreExpr.Row_mono hρ hρx s r) (Branches.Row_mono hρ hρx bs r) h
  | _, _, .recordE xs _, r, h => Fields.Row_mono hρ hρx xs r h
  | _, _, .fieldE _ _ _ e, r, h => CoreExpr.Row_mono hρ hρx e r h
  | _, _, .nilE, _, h => h
  | _, _, .consE hd tl, r, h => Or.imp (CoreExpr.Row_mono hρ hρx hd r) (CoreExpr.Row_mono hρ hρx tl r) h
  | _, _, .foldList l init body, r, h =>
      Or.imp (CoreExpr.Row_mono hρ hρx l r) (Or.imp (CoreExpr.Row_mono hρ hρx init r) (CoreExpr.Row_mono hρ hρx body r)) h
  | _, _, .boundedFix init limit stop step, r, h =>
      Or.imp (CoreExpr.Row_mono hρ hρx init r) (Or.imp (CoreExpr.Row_mono hρ hρx limit r)
        (Or.imp (CoreExpr.Row_mono hρ hρx stop r) (Or.imp (CoreExpr.Row_mono hρ hρx step r) id))) h
  | _, _, .prim _ args, r, h => Or.imp id (Args.Row_mono hρ hρx args r) h
  | _, _, .call (.local i _ _) args, r, h => Or.imp (hρ i r) (Args.Row_mono hρ hρx args r) h
  | _, _, .call (.external n _ _) args, r, h => Or.imp (Args.Row_mono hρ hρx args r) (hρx n r) h
  | _, _, .raise _ _ p, r, h => Or.imp id (CoreExpr.Row_mono hρ hρx p r) h
  | _, _, .handle _ _ body hd, r, h =>
      match h with
      | .inl ⟨hb, hne⟩ => .inl ⟨CoreExpr.Row_mono hρ hρx body r hb, hne⟩
      | .inr hh => .inr (CoreExpr.Row_mono hρ hρx hd r hh)
theorem Branches.Row_mono (hρ : ∀ i r, ρ i r → ρ' i r) (hρx : ∀ n r, ρx n r → ρx' n r) : ∀ {Γ ts : List CoreTy} {T : CoreTy}
    (bs : Branches S Γ ts T) (r : String), bs.Row ρ ρx r → bs.Row ρ' ρx' r
  | _, _, _, .nil, _, h => h
  | _, _, _, .cons b bs, r, h => Or.imp (CoreExpr.Row_mono hρ hρx b r) (Branches.Row_mono hρ hρx bs r) h
theorem Fields.Row_mono (hρ : ∀ i r, ρ i r → ρ' i r) (hρx : ∀ n r, ρx n r → ρx' n r) : ∀ {Γ : List CoreTy} {fs : List (String × CoreTy)}
    (xs : Fields S Γ fs) (r : String), xs.Row ρ ρx r → xs.Row ρ' ρx' r
  | _, _, .nil, _, h => h
  | _, _, .cons _ x xs, r, h => Or.imp (CoreExpr.Row_mono hρ hρx x r) (Fields.Row_mono hρ hρx xs r) h
theorem Args.Row_mono (hρ : ∀ i r, ρ i r → ρ' i r) (hρx : ∀ n r, ρx n r → ρx' n r) : ∀ {Γ ps : List CoreTy}
    (xs : Args S Γ ps) (r : String), xs.Row ρ ρx r → xs.Row ρ' ρx' r
  | _, _, .nil, _, h => h
  | _, _, .cons x xs, r, h => Or.imp (CoreExpr.Row_mono hρ hρx x r) (Args.Row_mono hρ hρx xs r) h
end

end Mono

section Src
variable {S : Sig}

mutual
/-- `r` has a DIRECT source in the expression (06 §7 "direct/external
    source"): a raise of `r`, a primitive whose direct row holds `r`, or a
    bounded fix when `r` is `negative_loop_bound`. Calls and handlers add no
    source. -/
def CoreExpr.Src : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → RaisedRef → Prop
  | _, _, .lit _, _ => False
  | _, _, .var _ _, _ => False
  | _, _, .letE a b, r => a.Src r ∨ b.Src r
  | _, _, .ifE c th el, r => c.Src r ∨ th.Src r ∨ el.Src r
  | _, _, .pairE a b, r => a.Src r ∨ b.Src r
  | _, _, .fstE a, r => a.Src r
  | _, _, .sndE a, r => a.Src r
  | _, _, .injE _ _ _ a, r => a.Src r
  | _, _, .matchSum s bs _, r => s.Src r ∨ bs.Src r
  | _, _, .recordE xs _, r => xs.Src r
  | _, _, .fieldE _ _ _ e, r => e.Src r
  | _, _, .nilE, _ => False
  | _, _, .consE h tl, r => h.Src r ∨ tl.Src r
  | _, _, .foldList l init body, r => l.Src r ∨ init.Src r ∨ body.Src r
  | _, _, .boundedFix init limit stop step, r =>
      init.Src r ∨ limit.Src r ∨ stop.Src r ∨ step.Src r ∨ r = "negative_loop_bound"
  | _, _, .prim op args, r => r ∈ primRow op ∨ args.Src r
  | _, _, .call _ args, r => args.Src r
  | _, _, .raise r' _ p, r => r = r' ∨ p.Src r
  | _, _, .handle _ _ body hd, r => body.Src r ∨ hd.Src r
def Branches.Src : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → RaisedRef → Prop
  | _, _, _, .nil, _ => False
  | _, _, _, .cons b bs, r => b.Src r ∨ bs.Src r
def Fields.Src : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → RaisedRef → Prop
  | _, _, .nil, _ => False
  | _, _, .cons _ x xs, r => x.Src r ∨ xs.Src r
def Args.Src : {Γ ps : List CoreTy} → Args S Γ ps → RaisedRef → Prop
  | _, _, .nil, _ => False
  | _, _, .cons x xs, r => x.Src r ∨ xs.Src r
end

variable {ρ : Nat → RaisedRef → Prop} {ρx : String → RaisedRef → Prop}

mutual
/-- A ref in a row has a direct source in the expression or comes from a
    callee's assigned row. -/
theorem CoreExpr.Row_src : ∀ {Γ : List CoreTy} {T : CoreTy} (e : CoreExpr S Γ T) (r : String),
    e.Row ρ ρx r → e.Src r ∨ (∃ i, ρ i r) ∨ (∃ n, ρx n r)
  | _, _, .lit _, _, h => h.elim
  | _, _, .var _ _, _, h => h.elim
  | _, _, .letE a b, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src a r h).imp Or.inl id
      | .inr h => (CoreExpr.Row_src b r h).imp Or.inr id
  | _, _, .ifE c th el, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src c r h).imp Or.inl id
      | .inr (.inl h) => (CoreExpr.Row_src th r h).imp (fun s => Or.inr (Or.inl s)) id
      | .inr (.inr h) => (CoreExpr.Row_src el r h).imp (fun s => Or.inr (Or.inr s)) id
  | _, _, .pairE a b, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src a r h).imp Or.inl id
      | .inr h => (CoreExpr.Row_src b r h).imp Or.inr id
  | _, _, .fstE a, r, h => CoreExpr.Row_src a r h
  | _, _, .sndE a, r, h => CoreExpr.Row_src a r h
  | _, _, .injE _ _ _ a, r, h => CoreExpr.Row_src a r h
  | _, _, .matchSum s bs _, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src s r h).imp Or.inl id
      | .inr h => (Branches.Row_src bs r h).imp Or.inr id
  | _, _, .recordE xs _, r, h => Fields.Row_src xs r h
  | _, _, .fieldE _ _ _ e, r, h => CoreExpr.Row_src e r h
  | _, _, .nilE, _, h => h.elim
  | _, _, .consE hd tl, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src hd r h).imp Or.inl id
      | .inr h => (CoreExpr.Row_src tl r h).imp Or.inr id
  | _, _, .foldList l init body, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src l r h).imp Or.inl id
      | .inr (.inl h) => (CoreExpr.Row_src init r h).imp (fun s => Or.inr (Or.inl s)) id
      | .inr (.inr h) => (CoreExpr.Row_src body r h).imp (fun s => Or.inr (Or.inr s)) id
  | _, _, .boundedFix init limit stop step, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src init r h).imp Or.inl id
      | .inr (.inl h) => (CoreExpr.Row_src limit r h).imp (fun s => Or.inr (Or.inl s)) id
      | .inr (.inr (.inl h)) => (CoreExpr.Row_src stop r h).imp (fun s => Or.inr (Or.inr (Or.inl s))) id
      | .inr (.inr (.inr (.inl h))) =>
          (CoreExpr.Row_src step r h).imp (fun s => Or.inr (Or.inr (Or.inr (Or.inl s)))) id
      | .inr (.inr (.inr (.inr e))) => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr e))))
  | _, _, .prim _ args, r, h =>
      match h with
      | .inl hm => Or.inl (Or.inl hm)
      | .inr h => (Args.Row_src args r h).imp Or.inr id
  | _, _, .call (.local i _ _) args, r, h =>
      match h with
      | .inl hi => Or.inr (Or.inl ⟨i, hi⟩)
      | .inr h => Args.Row_src args r h
  | _, _, .call (.external n _ _) args, r, h =>
      match h with
      | .inl h => Args.Row_src args r h
      | .inr hn => Or.inr (Or.inr (Exists.intro n hn))
  | _, _, .raise _ _ p, r, h =>
      match h with
      | .inl e => Or.inl (Or.inl e)
      | .inr h => (CoreExpr.Row_src p r h).imp Or.inr id
  | _, _, .handle _ _ body hd, r, h =>
      match h with
      | .inl ⟨hb, _⟩ => (CoreExpr.Row_src body r hb).imp Or.inl id
      | .inr h => (CoreExpr.Row_src hd r h).imp Or.inr id
theorem Branches.Row_src : ∀ {Γ ts : List CoreTy} {T : CoreTy} (bs : Branches S Γ ts T) (r : String),
    bs.Row ρ ρx r → bs.Src r ∨ (∃ i, ρ i r) ∨ (∃ n, ρx n r)
  | _, _, _, .nil, _, h => h.elim
  | _, _, _, .cons b bs, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src b r h).imp Or.inl id
      | .inr h => (Branches.Row_src bs r h).imp Or.inr id
theorem Fields.Row_src : ∀ {Γ : List CoreTy} {fs : List (String × CoreTy)} (xs : Fields S Γ fs) (r : String),
    xs.Row ρ ρx r → xs.Src r ∨ (∃ i, ρ i r) ∨ (∃ n, ρx n r)
  | _, _, .nil, _, h => h.elim
  | _, _, .cons _ x xs, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src x r h).imp Or.inl id
      | .inr h => (Fields.Row_src xs r h).imp Or.inr id
theorem Args.Row_src : ∀ {Γ ps : List CoreTy} (xs : Args S Γ ps) (r : String),
    xs.Row ρ ρx r → xs.Src r ∨ (∃ i, ρ i r) ∨ (∃ n, ρx n r)
  | _, _, .nil, _, h => h.elim
  | _, _, .cons x xs, r, h =>
      match h with
      | .inl h => (CoreExpr.Row_src x r h).imp Or.inl id
      | .inr h => (Args.Row_src xs r h).imp Or.inr id
end

end Src

end Rcic.Scm

namespace Rcic.Scm.RowDerive
open Rcic.Scm Rcic.Scm.Rows

/-! ## The ref universe of a program -/

/-- The refs a primitive's direct row can name (06 §11 with E-06LenRows). -/
def primU : List String :=
  ["byte_out_of_range", "division_by_zero", "empty_separator", "index_out_of_range",
   "malformed_integer", "nonexact_division", "signed_overflow"]

/-- Every ref a derived row can hold: the catalog refs (raises are typed by
    the catalog), `negative_loop_bound`, and the primitive refs. -/
def refU (S : Sig) : List String := S.catalog.map CatalogEntry.ref ++ ("negative_loop_bound" :: primU)

theorem refU_length (S : Sig) : (refU S).length = S.catalog.length + 8 := by
  unfold refU
  rw [List.length_append, List.length_map]
  rfl

theorem catalogPt_mem {c : List CatalogEntry} {r : RaisedRef} {P : CoreTy} (h : catalogPt c r = some P) :
    r ∈ c.map CatalogEntry.ref := by
  unfold catalogPt at h
  cases hf : c.find? (fun e => e.ref == r) with
  | none => rw [hf] at h; exact Option.noConfusion h
  | some e =>
    have hm : e ∈ c := List.mem_of_find?_eq_some hf
    have hp := List.find?_some (p := fun x : CatalogEntry => x.ref == r) (a := e) hf
    have he : e.ref = r := beq_iff_eq.mp hp
    rw [← he]
    exact List.mem_map_of_mem CatalogEntry.ref hm

theorem primRow_primU (op : PrimOp) (r : String) (h : r ∈ primRow op) : r ∈ primU := by
  have key : (primRow op).all (fun s => primU.contains s) = true := by cases op <;> decide
  exact List.elem_iff.mp (List.all_eq_true.mp key r h)

end Rcic.Scm.RowDerive

namespace Rcic.Scm
open Rcic.Scm.RowDerive

section SrcU
variable {S : Sig}

mutual
/-- Every direct source names a ref of the program's universe. -/
theorem CoreExpr.Src_U : ∀ {Γ : List CoreTy} {T : CoreTy} (e : CoreExpr S Γ T) (r : String),
    e.Src r → r ∈ refU S
  | _, _, .lit _, _, h => h.elim
  | _, _, .var _ _, _, h => h.elim
  | _, _, .letE a b, r, h => Or.elim h (CoreExpr.Src_U a r) (CoreExpr.Src_U b r)
  | _, _, .ifE c th el, r, h =>
      Or.elim h (CoreExpr.Src_U c r) (fun h => Or.elim h (CoreExpr.Src_U th r) (CoreExpr.Src_U el r))
  | _, _, .pairE a b, r, h => Or.elim h (CoreExpr.Src_U a r) (CoreExpr.Src_U b r)
  | _, _, .fstE a, r, h => CoreExpr.Src_U a r h
  | _, _, .sndE a, r, h => CoreExpr.Src_U a r h
  | _, _, .injE _ _ _ a, r, h => CoreExpr.Src_U a r h
  | _, _, .matchSum s bs _, r, h => Or.elim h (CoreExpr.Src_U s r) (Branches.Src_U bs r)
  | _, _, .recordE xs _, r, h => Fields.Src_U xs r h
  | _, _, .fieldE _ _ _ e, r, h => CoreExpr.Src_U e r h
  | _, _, .nilE, _, h => h.elim
  | _, _, .consE hd tl, r, h => Or.elim h (CoreExpr.Src_U hd r) (CoreExpr.Src_U tl r)
  | _, _, .foldList l init body, r, h =>
      Or.elim h (CoreExpr.Src_U l r) (fun h => Or.elim h (CoreExpr.Src_U init r) (CoreExpr.Src_U body r))
  | _, _, .boundedFix init limit stop step, r, h =>
      Or.elim h (CoreExpr.Src_U init r) (fun h => Or.elim h (CoreExpr.Src_U limit r)
        (fun h => Or.elim h (CoreExpr.Src_U stop r) (fun h => Or.elim h (CoreExpr.Src_U step r)
          (fun e => by
            rw [e]
            exact List.mem_append_right _ (List.mem_cons_self _ _)))))
  | _, _, .prim op args, r, h =>
      Or.elim h (fun hm => List.mem_append_right _ (List.mem_cons_of_mem _ (primRow_primU op r hm)))
        (Args.Src_U args r)
  | _, _, .call _ args, r, h => Args.Src_U args r h
  | _, _, .raise r' hr' p, r, h =>
      Or.elim h (fun e => by rw [e]; exact List.mem_append_left _ (catalogPt_mem hr')) (CoreExpr.Src_U p r)
  | _, _, .handle _ _ body hd, r, h => Or.elim h (CoreExpr.Src_U body r) (CoreExpr.Src_U hd r)
theorem Branches.Src_U : ∀ {Γ ts : List CoreTy} {T : CoreTy} (bs : Branches S Γ ts T) (r : String),
    bs.Src r → r ∈ refU S
  | _, _, _, .nil, _, h => h.elim
  | _, _, _, .cons b bs, r, h => Or.elim h (CoreExpr.Src_U b r) (Branches.Src_U bs r)
theorem Fields.Src_U : ∀ {Γ : List CoreTy} {fs : List (String × CoreTy)} (xs : Fields S Γ fs) (r : String),
    xs.Src r → r ∈ refU S
  | _, _, .nil, _, h => h.elim
  | _, _, .cons _ x xs, r, h => Or.elim h (CoreExpr.Src_U x r) (Fields.Src_U xs r)
theorem Args.Src_U : ∀ {Γ ps : List CoreTy} (xs : Args S Γ ps) (r : String),
    xs.Src r → r ∈ refU S
  | _, _, .nil, _, h => h.elim
  | _, _, .cons x xs, r, h => Or.elim h (CoreExpr.Src_U x r) (Args.Src_U xs r)
end

end SrcU

end Rcic.Scm

namespace Rcic.Scm.RowDerive
open Rcic.Scm Rcic.Scm.Rows

variable {S : Sig}

/-! ## Passes over a program -/

theorem rowsL_at (t : Tbl) (xr : String → List String) : ∀ {sigs : List FnSig} (bs : Bodies S sigs) (i : Nat) (f : FnSig)
    (h : sigs.get? i = some f), (bs.rowsL t xr).getD i [] = (bs.at i f h).rowL t xr
  | _ :: _, .cons b _, 0, _, h => by
      have e := Option.some.inj h
      subst e
      rfl
  | _ :: _, .cons _ bs, n + 1, f, h => rowsL_at t xr bs n f h
  | [], .nil, _, _, h => nomatch h

theorem mem_rowsL (t : Tbl) (xr : String → List String) : ∀ {sigs : List FnSig} (bs : Bodies S sigs) (i : Nat) (r : String),
    r ∈ (bs.rowsL t xr).getD i [] → ∃ f, ∃ h : sigs.get? i = some f, r ∈ (bs.at i f h).rowL t xr
  | f :: _, .cons _ _, 0, _, hr => ⟨f, rfl, hr⟩
  | _ :: _, .cons _ bs, n + 1, r, hr => mem_rowsL t xr bs n r hr
  | [], .nil, _, r, hr => absurd hr (List.not_mem_nil r)

theorem rowsL_length (t : Tbl) (xr : String → List String) : ∀ {sigs : List FnSig} (bs : Bodies S sigs), (bs.rowsL t xr).length = sigs.length
  | _, .nil => rfl
  | _, .cons _ bs => congrArg Nat.succ (rowsL_length t xr bs)

/-- Row-wise inclusion of tables. -/
def Sub (a b : Tbl) : Prop := ∀ i r, r ∈ a.getD i [] → r ∈ b.getD i []

theorem rowL_mono {a b : Tbl} (hab : Sub a b) {xr xr' : String → List String}
    (hxr : ∀ n r, r ∈ xr n → r ∈ xr' n) {Γ : List CoreTy} {T : CoreTy}
    (e : CoreExpr S Γ T) (r : String) (h : r ∈ e.rowL a xr) : r ∈ e.rowL b xr' :=
  (CoreExpr.rowL_iff b xr' e r).mpr (CoreExpr.Row_mono hab (fun n r h => hxr n r h) e r ((CoreExpr.rowL_iff a xr e r).mp h))

theorem rowsL_mono {sigs : List FnSig} (bs : Bodies S sigs) {a b : Tbl} (hab : Sub a b)
    {xr xr' : String → List String} (hxr : ∀ n r, r ∈ xr n → r ∈ xr' n) :
    Sub (bs.rowsL a xr) (bs.rowsL b xr') := by
  intro i r hr
  obtain ⟨f, hf, h⟩ := mem_rowsL a xr bs i r hr
  rw [rowsL_at b xr' bs i f hf]
  exact rowL_mono hab hxr _ r h

/-- A table that one pass does not grow is a prefixpoint of the scoped row
    equations (`RowPrefix`, `ScmRowSafety`). -/
theorem prefix_of_fix (bs : Bodies S S.fns) (t : Tbl) (xr : String → List String)
    (hfix : Sub (bs.rowsL t xr) t) :
    RowPrefix (tblRho t) (xrRho xr) bs := by
  intro i f hf r hr
  have h1 : r ∈ (bs.at i f hf).rowL t xr := (CoreExpr.rowL_iff t xr (bs.at i f hf) r).mpr hr
  rw [← rowsL_at t xr bs i f hf] at h1
  exact hfix i r h1

/-! ## The Kleene iterates -/

theorem getD_replicate_nil : ∀ (n i : Nat), (List.replicate n ([] : List String)).getD i [] = []
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, i + 1 => getD_replicate_nil n i

theorem seq_zero_empty (bs : Bodies S S.fns) (i : Nat) (r : String) (h : r ∈ (seq bs 0).getD i []) : False := by
  have h' : r ∈ (List.replicate S.fns.length ([] : List String)).getD i [] := h
  rw [getD_replicate_nil] at h'
  exact List.not_mem_nil r h'

theorem seq_length (bs : Bodies S S.fns) : ∀ n, (seq bs n).length = S.fns.length
  | 0 => List.length_replicate _ _
  | _ + 1 => rowsL_length _ _ bs

theorem seq_chain (bs : Bodies S S.fns) : ∀ n, Sub (seq bs n) (seq bs (n + 1))
  | 0 => fun i r h => (seq_zero_empty bs i r h).elim
  | n + 1 => rowsL_mono bs (seq_chain bs n) (fun _ _ h => h)

/-- Every iterate lies below every prefixpoint. -/
theorem seq_least (bs : Bodies S S.fns) {ρ' : Nat → RaisedRef → Prop} {ρx' : String → RaisedRef → Prop}
    (hpre : RowPrefix ρ' ρx' bs) :
    ∀ n i r, r ∈ (seq bs n).getD i [] → ρ' i r
  | 0, i, r, h => (seq_zero_empty bs i r h).elim
  | n + 1, i, r, h => by
      obtain ⟨f, hf, h1⟩ := mem_rowsL (seq bs n) (fun _ => []) bs i r h
      exact hpre i f hf r (CoreExpr.Row_mono (seq_least bs hpre n)
        (fun _ _ h => absurd h (List.not_mem_nil _)) _ r ((CoreExpr.rowL_iff _ _ _ r).mp h1))

/-- Every ref of an iterate has a direct source in some body. -/
theorem seq_no_mint (bs : Bodies S S.fns) : ∀ n i r, r ∈ (seq bs n).getD i [] →
    ∃ j f, ∃ hf : S.fns.get? j = some f, (bs.at j f hf).Src r
  | 0, i, r, h => (seq_zero_empty bs i r h).elim
  | n + 1, i, r, h => by
      obtain ⟨f, hf, h1⟩ := mem_rowsL (seq bs n) (fun _ => []) bs i r h
      cases CoreExpr.Row_src _ r ((CoreExpr.rowL_iff _ _ _ r).mp h1) with
      | inl hs => exact ⟨i, f, hf, hs⟩
      | inr he =>
        cases he with
        | inl he2 =>
          obtain ⟨j, hj⟩ := he2
          exact seq_no_mint bs n j r hj
        | inr he3 =>
          obtain ⟨_, hn⟩ := he3
          exact absurd hn (List.not_mem_nil r)

theorem seq_support (bs : Bodies S S.fns) (n i : Nat) (r : String) (h : r ∈ (seq bs n).getD i []) :
    r ∈ refU S := by
  obtain ⟨_, _, _, hs⟩ := seq_no_mint bs n i r h
  exact CoreExpr.Src_U _ r hs

/-! ## The measure: how many universe refs the rows hold -/

def cnt (U row : List String) : Nat := (U.filter (fun u => row.contains u)).length

def mu (U : List String) : Tbl → Nat
  | [] => 0
  | row :: rest => cnt U row + mu U rest

theorem filter_length_mono {p q : String → Bool} (hpq : ∀ u, p u = true → q u = true) :
    ∀ (l : List String), (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl 0
  | u :: l => by
      cases hp : p u with
      | true =>
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (hpq u hp)]
        exact Nat.succ_le_succ (filter_length_mono hpq l)
      | false =>
        rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
        cases hq : q u with
        | true =>
          rw [List.filter_cons_of_pos hq]
          exact Nat.le_succ_of_le (filter_length_mono hpq l)
        | false =>
          rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]
          exact filter_length_mono hpq l

theorem filter_length_strict {p q : String → Bool} (hpq : ∀ u, p u = true → q u = true) {w : String}
    (hp : p w = false) (hq : q w = true) :
    ∀ (l : List String), w ∈ l → (l.filter p).length < (l.filter q).length
  | [], hw => absurd hw (List.not_mem_nil w)
  | u :: l, hw => by
      cases List.mem_cons.mp hw with
      | inl e =>
        rw [← e, List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.filter_cons_of_pos hq]
        exact Nat.lt_succ_of_le (filter_length_mono hpq l)
      | inr hl =>
        have ih := filter_length_strict hpq hp hq l hl
        cases hpu : p u with
        | true =>
          rw [List.filter_cons_of_pos hpu, List.filter_cons_of_pos (hpq u hpu)]
          exact Nat.succ_lt_succ ih
        | false =>
          rw [List.filter_cons_of_neg (by rw [hpu]; exact Bool.false_ne_true)]
          cases hqu : q u with
          | true =>
            rw [List.filter_cons_of_pos hqu]
            exact Nat.lt_succ_of_lt ih
          | false =>
            rw [List.filter_cons_of_neg (by rw [hqu]; exact Bool.false_ne_true)]
            exact ih

theorem cnt_mono (U : List String) {a b : List String} (h : ∀ r, r ∈ a → r ∈ b) : cnt U a ≤ cnt U b :=
  filter_length_mono (fun u hu => List.elem_iff.mpr (h u (List.elem_iff.mp hu))) U

theorem cnt_strict (U : List String) {a b : List String} (h : ∀ r, r ∈ a → r ∈ b) {w : String}
    (hwU : w ∈ U) (hwb : w ∈ b) (hwa : w ∉ a) : cnt U a < cnt U b :=
  filter_length_strict (fun u hu => List.elem_iff.mpr (h u (List.elem_iff.mp hu)))
    (Bool.eq_false_iff.mpr (fun hc => hwa (List.elem_iff.mp hc))) (List.elem_iff.mpr hwb) U hwU

theorem mu_le (U : List String) : ∀ x : Tbl, mu U x ≤ x.length * U.length
  | [] => Nat.zero_le _
  | row :: rest => by
      show cnt U row + mu U rest ≤ (rest.length + 1) * U.length
      have h1 : cnt U row ≤ U.length := List.length_filter_le _ _
      have h2 := mu_le U rest
      calc cnt U row + mu U rest ≤ U.length + rest.length * U.length := Nat.add_le_add h1 h2
        _ = (rest.length + 1) * U.length := by rw [Nat.succ_mul, Nat.add_comm]

theorem mu_mono (U : List String) : ∀ (a b : Tbl), a.length = b.length → Sub a b → mu U a ≤ mu U b
  | [], [], _, _ => Nat.le_refl 0
  | x :: a, y :: b, hl, h => by
      show cnt U x + mu U a ≤ cnt U y + mu U b
      exact Nat.add_le_add (cnt_mono U (fun r hr => h 0 r hr))
        (mu_mono U a b (Nat.succ.inj hl) (fun i r hr => h (i + 1) r hr))
  | [], _ :: _, hl, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], hl, _ => (Nat.succ_ne_zero _ hl).elim

theorem mu_strict (U : List String) : ∀ (a b : Tbl), a.length = b.length → Sub a b →
    ∀ (i : Nat) (w : String), w ∈ U → w ∈ b.getD i [] → w ∉ a.getD i [] → mu U a < mu U b
  | x :: a, y :: b, hl, h, 0, _, hU, hb, ha => by
      show cnt U x + mu U a < cnt U y + mu U b
      exact Nat.add_lt_add_of_lt_of_le (cnt_strict U (fun r hr => h 0 r hr) hU hb ha)
        (mu_mono U a b (Nat.succ.inj hl) (fun i r hr => h (i + 1) r hr))
  | x :: a, y :: b, hl, h, i + 1, w, hU, hb, ha => by
      show cnt U x + mu U a < cnt U y + mu U b
      exact Nat.add_lt_add_of_le_of_lt (cnt_mono U (fun r hr => h 0 r hr))
        (mu_strict U a b (Nat.succ.inj hl) (fun j r hr => h (j + 1) r hr) i w hU hb ha)
  | [], [], _, _, _, w, _, hb, _ => absurd hb (List.not_mem_nil w)
  | [], _ :: _, hl, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hl.symm).elim
  | _ :: _, [], hl, _, _, _, _, _, _ => (Nat.succ_ne_zero _ hl).elim

/-! ## Convergence within `passes S` -/

/-- Either some earlier pass did not grow the table, or the measure has
    grown at every pass so far. -/
theorem seq_progress (bs : Bodies S S.fns) : ∀ k,
    (∃ j, j < k ∧ Sub (seq bs (j + 1)) (seq bs j)) ∨ k ≤ mu (refU S) (seq bs k)
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      cases seq_progress bs k with
      | inl h =>
        obtain ⟨j, hj, hs⟩ := h
        exact Or.inl ⟨j, Nat.lt_succ_of_lt hj, hs⟩
      | inr hk =>
        have hlen : (seq bs k).length = (seq bs (k + 1)).length :=
          (seq_length bs k).trans (seq_length bs (k + 1)).symm
        have hle : mu (refU S) (seq bs k) ≤ mu (refU S) (seq bs (k + 1)) :=
          mu_mono _ _ _ hlen (seq_chain bs k)
        by_cases heq : mu (refU S) (seq bs (k + 1)) = mu (refU S) (seq bs k)
        · refine Or.inl ⟨k, Nat.lt_succ_self k, fun i r hr => ?_⟩
          by_cases hm : r ∈ (seq bs k).getD i []
          · exact hm
          · have hlt := mu_strict (refU S) _ _ hlen (seq_chain bs k) i r (seq_support bs (k + 1) i r hr) hr hm
            exact absurd heq (Nat.ne_of_gt hlt)
        · have hlt : mu (refU S) (seq bs k) < mu (refU S) (seq bs (k + 1)) :=
            Nat.lt_of_le_of_ne hle (fun e => heq e.symm)
          exact Or.inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk hlt))

theorem seq_stable_from (bs : Bodies S S.fns) {j : Nat} (hj : Sub (seq bs (j + 1)) (seq bs j)) :
    ∀ d, Sub (seq bs (j + d + 1)) (seq bs (j + d))
  | 0 => hj
  | d + 1 => rowsL_mono bs (seq_stable_from bs hj d) (fun _ _ h => h)

/-- 06 §7 / SCM-003, existence: the derived table is a prefixpoint of the
    scoped row equations. -/
theorem derive_prefix (bs : Bodies S S.fns) : RowPrefix (tblRho (deriveRows bs)) (xrRho (fun _ => [])) bs := by
  cases seq_progress bs (passes S) with
  | inr h =>
    have h1 := mu_le (refU S) (seq bs (passes S))
    rw [seq_length, refU_length] at h1
    exact absurd (Nat.le_trans h h1) (Nat.not_succ_le_self _)
  | inl h =>
    obtain ⟨j, hj, hs⟩ := h
    have hstab := seq_stable_from bs hs (passes S - j)
    have e : j + (passes S - j) = passes S := Nat.add_sub_cancel' (Nat.le_of_lt hj)
    rw [e] at hstab
    exact prefix_of_fix bs (deriveRows bs) (fun _ => []) hstab

/-- 06 §7 / SCM-003, leastness (hence uniqueness): the derived table lies
    below every prefixpoint. -/
theorem derive_least (bs : Bodies S S.fns) {ρ' : Nat → RaisedRef → Prop} {ρx' : String → RaisedRef → Prop}
    (hpre : RowPrefix ρ' ρx' bs)
    (i : Nat) (r : String) (h : r ∈ (deriveRows bs).getD i []) : ρ' i r :=
  seq_least bs hpre (passes S) i r h

/-- 06 §7 / SCM-004: a derived ref has a direct source in some body; a call
    cycle mints nothing. -/
theorem derive_no_mint (bs : Bodies S S.fns) (i : Nat) (r : String) (h : r ∈ (deriveRows bs).getD i []) :
    ∃ j f, ∃ hf : S.fns.get? j = some f, (bs.at j f hf).Src r :=
  seq_no_mint bs (passes S) i r h

/-- 06 §16 residue-row safety for the derived rows: a run from an entry body
    that ends in a final raised outcome raises a ref of the entry's derived row. -/
theorem derive_row_safety (bs : Bodies S S.fns) (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
    (args : CoreVals f.params) {n : Nat} {cf : Config S f.result}
    (hr : SCMRuns bs n ⟨f.result, .evalC args (bs.at i f hf), .nil⟩ cf)
    {r : RaisedRef} {P : CoreTy} {hP : catalogPt S.catalog r = some P} {v : CoreVal P}
    (hfin : stepI bs cf = .final (.raised r hP v)) : r ∈ (deriveRows bs).getD i [] :=
  RowSafety.residue_row_safety (tblRho (deriveRows bs)) (xrRho (fun _ => [])) bs (derive_prefix bs) i f hf args hr hfin

/-- An entry whose derived row is empty never ends in a final raised outcome. -/
theorem derive_empty_no_raise (bs : Bodies S S.fns) (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
    (h0 : (deriveRows bs).getD i [] = []) (args : CoreVals f.params) {n : Nat} {cf : Config S f.result}
    (hr : SCMRuns bs n ⟨f.result, .evalC args (bs.at i f hf), .nil⟩ cf)
    {r : RaisedRef} {P : CoreTy} {hP : catalogPt S.catalog r = some P} {v : CoreVal P} :
    stepI bs cf ≠ .final (.raised r hP v) := fun hfin => by
  have h := derive_row_safety bs i f hf args hr hfin
  rw [h0] at h
  exact List.not_mem_nil r h

/-! ## The carrier's form 0 is the derivation -/

theorem scmRows_form0_ok (fuel : Int) (p : RawProg) (tbl : Tbl) (bs : Bodies (sigOf p) (sigOf p).fns)
    (T : CoreTy) (hpc : progCheck fuel p = .ok ⟨bs, T⟩) (hx : bs.hasExt = false) :
    scmRows 0 fuel p tbl = ⟨1, deriveRows bs, (deriveRows bs).getD p.entry.toNat [], 1, -1, ""⟩ := by
  unfold scmRows
  rw [if_neg (by decide), if_neg (by decide), hpc]
  dsimp only
  rw [if_neg (by rw [hx]; exact Bool.false_ne_true), if_pos rfl]

theorem scmRows_form0_accepts (fuel : Int) (p : RawProg) (tbl : Tbl) (h : (scmRows 0 fuel p tbl).ok = 1) :
    ∃ bs T, progCheck fuel p = .ok ⟨bs, T⟩ ∧ bs.hasExt = false := by
  unfold scmRows at h
  rw [if_neg (by decide), if_neg (by decide)] at h
  cases hpc : progCheck fuel p with
  | error c =>
    rw [hpc] at h
    dsimp only at h
    have h' : (0 : Int) = 1 := h
    exact absurd h' (by decide)
  | ok v =>
    obtain ⟨bs, T⟩ := v
    rw [hpc] at h
    dsimp only at h
    cases hx : bs.hasExt with
    | false => exact ⟨bs, T, rfl, hx⟩
    | true =>
      rw [if_pos hx] at h
      have h' : (0 : Int) = 1 := h
      exact absurd h' (by decide)

/-- An accepting form-0 answer of the carrier is the derived table of the
    bodies typing returns, so `derive_prefix` / `derive_least` /
    `derive_no_mint` / `derive_row_safety` apply to it. -/
theorem scmRows_form0_sound (fuel : Int) (p : RawProg) (tbl : Tbl) (h : (scmRows 0 fuel p tbl).ok = 1) :
    ∃ bs T, progCheck fuel p = .ok ⟨bs, T⟩ ∧ (scmRows 0 fuel p tbl).rows = deriveRows bs := by
  obtain ⟨bs, T, hpc, hx⟩ := scmRows_form0_accepts fuel p tbl h
  exact ⟨bs, T, hpc, by rw [scmRows_form0_ok fuel p tbl bs T hpc hx]⟩

/-! ## 06 §7 over a multi-group bundle: the external-call clause (SCM-003/004)

The one-group development above is the `resolve = ∅` instance of the equation
below. A `RowGrp` is a signature with its typed bodies; a bundle is a list of
them; `resolve` maps an external reference name (the `ExtSig.ref` the callee
was admitted under, `ScmBoundProgramCl`) to its `(group, member)` cell. -/

open Rcic.Scm Rcic.Scm.Rows

/-- One function group of a bundle: a signature and bodies typed in it. -/
abbrev RowGrp := Sigma (fun S : Sig => Bodies S S.fns)

/-- An external resolver: reference name ↦ (group index, member index). -/
abbrev ExtResolve := String → Option (Nat × Nat)

/-- The callee row an external call sees through `resolve`: the resolved
    member's row in the table list; an unresolved reference sees no row. -/
def xrOf (ts : List Tbl) (resolve : ExtResolve) (n : String) : List String :=
  ((resolve n).map (fun gm => (ts.getD gm.1 []).getD gm.2 [])).getD []

theorem xrOf_some (ts : List Tbl) (resolve : ExtResolve) (n : String) (g' m' : Nat)
    (hres : resolve n = some ⟨g', m'⟩) :
    xrOf ts resolve n = (ts.getD g' []).getD m' [] := by
  unfold xrOf; rw [hres]; rfl

theorem xrOf_none (ts : List Tbl) (resolve : ExtResolve) (n : String)
    (hres : resolve n = none) : xrOf ts resolve n = [] := by
  unfold xrOf; rw [hres]; rfl

/-- One pass over every group: each group's own table feeds its local calls,
    the resolved cells feed its external calls. -/
def rowsLCl.go (resolve : ExtResolve) (ts : List Tbl) : List RowGrp → Nat → List Tbl
  | [], _ => []
  | gp :: rest, g => gp.2.rowsL (ts.getD g []) (xrOf ts resolve) :: rowsLCl.go resolve ts rest (g + 1)

def rowsLCl (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl) : List Tbl :=
  rowsLCl.go resolve ts gs 0

/-- The `n`-th Kleene iterate of the bundle equation. -/
def seqCl (gs : List RowGrp) (resolve : ExtResolve) (n : Nat) : List Tbl :=
  iterN (rowsLCl gs resolve) n (gs.map (fun gp => List.replicate gp.1.fns.length []))

/-- The bundle's ref universe: every group's universe (catalog refs,
    `negative_loop_bound`, primitive refs). -/
def refUAll (gs : List RowGrp) : List String := (gs.map (fun gp => refU gp.1)).flatten

/-- The pass count of the bundle equation: total members times universe. -/
def passesCl (gs : List RowGrp) : Nat :=
  (gs.map (fun gp => gp.1.fns.length)).sum * (refUAll gs).length + 1

/-- 06 §7 over the bundle: the derived table list. -/
def deriveRowsCl (gs : List RowGrp) (resolve : ExtResolve) : List Tbl :=
  seqCl gs resolve (passesCl gs)

/-- Row-wise inclusion of table lists. -/
def SubCl (a b : List Tbl) : Prop :=
  ∀ g i r, r ∈ (a.getD g []).getD i [] → r ∈ (b.getD g []).getD i []

/-- A table list that one pass does not grow is a prefixpoint of the bundle
    equations. -/
def RowPrefixClOf (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl) : Prop :=
  ∀ (g : Nat) (gp : RowGrp), gs.get? g = some gp →
    ∀ (i : Nat) (f : FnSig) (hf : gp.1.fns.get? i = some f) (r : RaisedRef),
    (gp.2.at i f hf).Row (tblRho (ts.getD g [])) (xrRho (xrOf ts resolve)) r →
    r ∈ (ts.getD g []).getD i []

/-- The prop-level bundle prefixpoint: prop-valued row assignments for local
    cells and external references. -/
def RowPrefixCl (gs : List RowGrp) (_resolve : ExtResolve)
    (ρ : Nat → Nat → RaisedRef → Prop) (ρx : String → RaisedRef → Prop) : Prop :=
  ∀ (g : Nat) (gp : RowGrp), gs.get? g = some gp →
    ∀ (i : Nat) (f : FnSig) (hf : gp.1.fns.get? i = some f) (r : RaisedRef),
    (gp.2.at i f hf).Row (ρ g) ρx r → ρ g i r

/-! ## cells of the iterate -/

theorem getD_mapReplicate_nil : ∀ (gs : List RowGrp) (g i : Nat),
    ((gs.map fun gp => List.replicate gp.1.fns.length ([] : List String)).getD g []).getD i [] = []
  | [], _, _ => rfl
  | _ :: _, 0, _ => getD_replicate_nil _ _
  | _ :: gs, g + 1, i => getD_mapReplicate_nil gs g i

theorem seqCl_zero_empty (gs : List RowGrp) (resolve : ExtResolve) (g i : Nat) (r : String)
    (h : r ∈ ((seqCl gs resolve 0).getD g []).getD i []) : False := by
  have h' : r ∈ ((gs.map fun gp => List.replicate gp.1.fns.length ([] : List String)).getD g []).getD i [] := h
  rw [getD_mapReplicate_nil] at h'
  exact List.not_mem_nil r h'

theorem rowsLCl_go_length (resolve : ExtResolve) (ts : List Tbl) : ∀ (rest : List RowGrp) (g : Nat),
    (rowsLCl.go resolve ts rest g).length = rest.length
  | [], _ => rfl
  | _ :: rest, g => congrArg Nat.succ (rowsLCl_go_length resolve ts rest (g + 1))

theorem rowsLCl_length (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl) :
    (rowsLCl gs resolve ts).length = gs.length := rowsLCl_go_length resolve ts gs 0

theorem seqCl_length (gs : List RowGrp) (resolve : ExtResolve) : ∀ n,
    (seqCl gs resolve n).length = gs.length
  | 0 => List.length_map _ _
  | n + 1 => rowsLCl_length gs resolve (seqCl gs resolve n)

/-- The cell of a pass over the tail list. -/
theorem rowsLCl_go_at (resolve : ExtResolve) (ts : List Tbl) : ∀ (rest : List RowGrp) (g j : Nat),
    (rowsLCl.go resolve ts rest g).getD j [] =
      ((rest.get? j).map (fun gp => gp.2.rowsL (ts.getD (g + j) []) (xrOf ts resolve))).getD []
  | [], _, _ => rfl
  | _ :: _, _, 0 => rfl
  | _ :: rest, g, j + 1 => by
    show (rowsLCl.go resolve ts rest (g + 1)).getD j [] =
        ((rest.get? j).map (fun gp' => gp'.2.rowsL (ts.getD (g + (j + 1)) []) (xrOf ts resolve))).getD []
    rw [rowsLCl_go_at resolve ts rest (g + 1) j]
    cases rest.get? j with
    | none => rfl
    | some _ =>
      have e : g + 1 + j = g + (j + 1) := by omega
      rw [e]

theorem rowsLCl_at (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl) (g : Nat)
    (gp : RowGrp) (hg : gs.get? g = some gp) :
    (rowsLCl gs resolve ts).getD g [] = gp.2.rowsL (ts.getD g []) (xrOf ts resolve) := by
  have h := rowsLCl_go_at resolve ts gs 0 g
  rw [hg, Nat.zero_add] at h
  exact h

theorem mem_rowsLCl (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl) (g i : Nat) (r : String)
    (h : r ∈ ((rowsLCl gs resolve ts).getD g []).getD i []) :
    ∃ gp, gs.get? g = some gp ∧ r ∈ (gp.2.rowsL (ts.getD g []) (xrOf ts resolve)).getD i [] := by
  cases hg : gs.get? g with
  | none =>
    have h2 := rowsLCl_go_at resolve ts gs 0 g
    rw [hg, Nat.zero_add] at h2
    have h3 : (rowsLCl gs resolve ts).getD g [] = [] := h2
    rw [h3] at h
    exact absurd h (List.not_mem_nil r)
  | some gp =>
    refine ⟨gp, rfl, ?_⟩
    rw [rowsLCl_at gs resolve ts g gp hg] at h
    exact h

/-! ## monotonicity -/

theorem xrOf_mono {a b : List Tbl} (hab : SubCl a b) (resolve : ExtResolve) :
    ∀ n r, r ∈ xrOf a resolve n → r ∈ xrOf b resolve n := by
  intro n r h
  cases hres : resolve n with
  | none => rw [xrOf_none _ _ _ hres] at h; exact absurd h (List.not_mem_nil r)
  | some gm =>
    obtain ⟨g', m'⟩ := gm
    rw [xrOf_some _ _ _ _ _ hres] at h ⊢
    exact hab g' m' r h

theorem rowsLCl_mono (gs : List RowGrp) (resolve : ExtResolve) {a b : List Tbl} (hab : SubCl a b) :
    SubCl (rowsLCl gs resolve a) (rowsLCl gs resolve b) := by
  intro g i r h
  obtain ⟨gp, hgp, hr⟩ := mem_rowsLCl gs resolve a g i r h
  have hsub : Sub (a.getD g []) (b.getD g []) := fun i r hr => hab g i r hr
  have := rowsL_mono gp.2 hsub (xrOf_mono hab resolve) i r hr
  rw [← rowsLCl_at gs resolve b g gp hgp] at this
  exact this

theorem seqCl_chain (gs : List RowGrp) (resolve : ExtResolve) : ∀ n,
    SubCl (seqCl gs resolve n) (seqCl gs resolve (n + 1))
  | 0 => fun g i r h => (seqCl_zero_empty gs resolve g i r h).elim
  | n + 1 => rowsLCl_mono gs resolve (seqCl_chain gs resolve n)

/-- A fixed point of the pass is a bundle prefixpoint. -/
theorem prefixCl_of_fix (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl)
    (hfix : SubCl (rowsLCl gs resolve ts) ts) : RowPrefixClOf gs resolve ts := by
  intro g gp hg i f hf r hr
  have h1 : r ∈ (gp.2.at i f hf).rowL (ts.getD g []) (xrOf ts resolve) :=
    (CoreExpr.rowL_iff _ _ _ _).mpr hr
  rw [← rowsL_at (ts.getD g []) (xrOf ts resolve) gp.2 i f hf] at h1
  rw [← rowsLCl_at gs resolve ts g gp hg] at h1
  exact hfix g i r h1

/-! ## leastness -/

theorem seqCl_least (gs : List RowGrp) (resolve : ExtResolve)
    {ρ : Nat → Nat → RaisedRef → Prop} {ρx : String → RaisedRef → Prop}
    (hpre : RowPrefixCl gs resolve ρ ρx)
    (hxr : ∀ n' g' m' r, resolve n' = some ⟨g', m'⟩ → ρ g' m' r → ρx n' r) :
    ∀ n g i r, r ∈ ((seqCl gs resolve n).getD g []).getD i [] → ρ g i r
  | 0, g, i, r, h => (seqCl_zero_empty gs resolve g i r h).elim
  | n + 1, g, i, r, h => by
    obtain ⟨gp, hgp, hr⟩ := mem_rowsLCl gs resolve (seqCl gs resolve n) g i r h
    obtain ⟨f, hf, h2⟩ := mem_rowsL ((seqCl gs resolve n).getD g []) (xrOf (seqCl gs resolve n) resolve)
      gp.2 i r hr
    have hρ : ∀ i r, tblRho ((seqCl gs resolve n).getD g []) i r → ρ g i r :=
      fun i r hm => seqCl_least gs resolve hpre hxr n g i r hm
    have hρx : ∀ n' r, xrRho (xrOf (seqCl gs resolve n) resolve) n' r → ρx n' r := by
      intro n' r' hm
      have hm : r' ∈ xrOf (seqCl gs resolve n) resolve n' := hm
      cases hres : resolve n' with
      | none => rw [xrOf_none _ _ _ hres] at hm; exact absurd hm (List.not_mem_nil r')
      | some gm =>
        obtain ⟨g', m'⟩ := gm
        rw [xrOf_some _ _ _ _ _ hres] at hm
        exact hxr n' g' m' r' hres (seqCl_least gs resolve hpre hxr n g' m' r' hm)
    have hrow : (gp.2.at i f hf).Row (ρ g) ρx r :=
      CoreExpr.Row_mono hρ hρx _ r ((CoreExpr.rowL_iff _ _ _ _).mp h2)
    exact hpre g gp hgp i f hf r hrow

/-! ## no minted refs -/

/-- Every ref of an iterate has a direct source in some body of the bundle:
    local calls re-enter the same iterate, external calls re-enter through the
    resolved cell — neither mints. -/
theorem seqCl_no_mint (gs : List RowGrp) (resolve : ExtResolve) :
    ∀ n g i r, r ∈ ((seqCl gs resolve n).getD g []).getD i [] →
    ∃ g' gp, gs.get? g' = some gp ∧ ∃ j f, ∃ hf : gp.1.fns.get? j = some f,
      (gp.2.at j f hf).Src r
  | 0, g, i, r, h => (seqCl_zero_empty gs resolve g i r h).elim
  | n + 1, g, i, r, h => by
    obtain ⟨gp, hgp, hr⟩ := mem_rowsLCl gs resolve (seqCl gs resolve n) g i r h
    obtain ⟨f, hf, h2⟩ := mem_rowsL ((seqCl gs resolve n).getD g []) (xrOf (seqCl gs resolve n) resolve)
      gp.2 i r hr
    cases CoreExpr.Row_src _ r ((CoreExpr.rowL_iff _ _ _ _).mp h2) with
    | inl hs => exact ⟨g, gp, hgp, i, f, hf, hs⟩
    | inr he =>
      cases he with
      | inl he2 =>
        obtain ⟨j, hj⟩ := he2
        exact seqCl_no_mint gs resolve n g j r hj
      | inr he3 =>
        obtain ⟨n', hn'⟩ := he3
        have hn' : r ∈ xrOf (seqCl gs resolve n) resolve n' := hn'
        cases hres : resolve n' with
        | none => rw [xrOf_none _ _ _ hres] at hn'; exact absurd hn' (List.not_mem_nil r)
        | some gm =>
          obtain ⟨g', m'⟩ := gm
          rw [xrOf_some _ _ _ _ _ hres] at hn'
          exact seqCl_no_mint gs resolve n g' m' r hn'

/-! ## the measure over the bundle -/

/-- The bundle measure: the per-table measure summed over cells. -/
def muAll (U : List String) (ts : List Tbl) : Nat := (ts.map (mu U)).sum

theorem mapReplicate_length : ∀ (gs : List RowGrp),
    (gs.map (fun gp => List.replicate gp.1.fns.length ([] : List String))).map
      (fun t => t.length) =
      gs.map (fun gp => gp.1.fns.length)
  | [] => rfl
  | gp :: gs => by
    show (List.replicate gp.1.fns.length ([] : List String)).length ::
        ((gs.map fun gp' => List.replicate gp'.1.fns.length ([] : List String)).map
          (fun t => t.length)) =
        gp.1.fns.length :: gs.map (fun gp' => gp'.1.fns.length)
    rw [List.length_replicate]
    exact congrArg (gp.1.fns.length :: ·) (mapReplicate_length gs)

theorem rowsLCl_go_map_length (resolve : ExtResolve) (ts : List Tbl) : ∀ (rest : List RowGrp) (g : Nat),
    (rowsLCl.go resolve ts rest g).map (fun t => t.length) = rest.map (fun gp => gp.1.fns.length)
  | [], _ => rfl
  | gp :: rest, g => by
    show (gp.2.rowsL (ts.getD g []) (xrOf ts resolve)).length ::
        (rowsLCl.go resolve ts rest (g + 1)).map (fun t => t.length) = _
    rw [rowsL_length (ts.getD g []) (xrOf ts resolve) gp.2,
        rowsLCl_go_map_length resolve ts rest (g + 1)]
    rfl

theorem seqCl_map_length (gs : List RowGrp) (resolve : ExtResolve) : ∀ n,
    (seqCl gs resolve n).map (fun t => t.length) = gs.map (fun gp => gp.1.fns.length)
  | 0 => mapReplicate_length gs
  | n + 1 => by
    show (rowsLCl.go resolve (seqCl gs resolve n) gs 0).map (fun t => t.length) = _
    exact rowsLCl_go_map_length resolve (seqCl gs resolve n) gs 0

theorem muAll_le (U : List String) : ∀ ts : List Tbl,
    muAll U ts ≤ (ts.map (fun t => t.length)).sum * U.length
  | [] => Nat.zero_le _
  | t :: ts => by
    show mu U t + muAll U ts ≤ (t.length + (ts.map (fun t => t.length)).sum) * U.length
    rw [Nat.add_mul]
    exact Nat.add_le_add (mu_le U t) (muAll_le U ts)

theorem muAll_mono (U : List String) : ∀ (a b : List Tbl),
    a.map (fun t => t.length) = b.map (fun t => t.length) → SubCl a b → muAll U a ≤ muAll U b
  | [], [], _, _ => Nat.le_refl 0
  | x :: a, y :: b, hl, h => by
    rw [List.map_cons, List.map_cons] at hl
    obtain ⟨hl1, hl2⟩ := List.cons.inj hl
    exact Nat.add_le_add
      (mu_mono U x y hl1 (fun i r hr => h 0 i r hr))
      (muAll_mono U a b hl2 (fun g i r hr => h (g + 1) i r hr))
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl

theorem muAll_strict (U : List String) : ∀ (a b : List Tbl),
    a.map (fun t => t.length) = b.map (fun t => t.length) → SubCl a b →
    ∀ (g i : Nat) (w : String), w ∈ U → w ∈ (b.getD g []).getD i [] →
    w ∉ (a.getD g []).getD i [] → muAll U a < muAll U b
  | x :: a, y :: b, hl, h, 0, i, w, hU, hb, ha => by
    rw [List.map_cons, List.map_cons] at hl
    obtain ⟨hl1, hl2⟩ := List.cons.inj hl
    show mu U x + muAll U a < mu U y + muAll U b
    exact Nat.add_lt_add_of_lt_of_le
      (mu_strict U x y hl1 (fun i r hr => h 0 i r hr) i w hU hb ha)
      (muAll_mono U a b hl2 (fun g i r hr => h (g + 1) i r hr))
  | x :: a, y :: b, hl, h, g + 1, i, w, hU, hb, ha => by
    rw [List.map_cons, List.map_cons] at hl
    obtain ⟨hl1, hl2⟩ := List.cons.inj hl
    show mu U x + muAll U a < mu U y + muAll U b
    exact Nat.add_lt_add_of_le_of_lt
      (mu_mono U x y hl1 (fun i r hr => h 0 i r hr))
      (muAll_strict U a b hl2 (fun g i r hr => h (g + 1) i r hr) g i w hU hb ha)
  | _, [], _, _, _, _, w, _, hb, _ => by
    have hb : w ∈ ([] : List String) := hb
    exact absurd hb (List.not_mem_nil w)
  | [], _ :: _, hl, _, _, _, _, _, _, _ => by cases hl

theorem seqCl_support (gs : List RowGrp) (resolve : ExtResolve) (n g i : Nat) (r : String)
    (h : r ∈ ((seqCl gs resolve n).getD g []).getD i []) : r ∈ refUAll gs := by
  obtain ⟨g', gp, hgp, j, f, hf, hs⟩ := seqCl_no_mint gs resolve n g i r h
  have hU : r ∈ refU gp.1 := CoreExpr.Src_U _ r hs
  have hgm : gp ∈ gs := List.get?_mem hgp
  exact List.mem_flatten.mpr ⟨refU gp.1, List.mem_map_of_mem (fun gp' => refU gp'.1) hgm, hU⟩

/-! ## Convergence within `passesCl gs` -/

theorem seqCl_progress (gs : List RowGrp) (resolve : ExtResolve) : ∀ k,
    (∃ j, j < k ∧ SubCl (seqCl gs resolve (j + 1)) (seqCl gs resolve j)) ∨
    k ≤ muAll (refUAll gs) (seqCl gs resolve k)
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    cases seqCl_progress gs resolve k with
    | inl h =>
      obtain ⟨j, hj, hs⟩ := h
      exact Or.inl ⟨j, Nat.lt_succ_of_lt hj, hs⟩
    | inr hk =>
      have hl : (seqCl gs resolve k).map (fun t => t.length) = (seqCl gs resolve (k + 1)).map (fun t => t.length) :=
        (seqCl_map_length gs resolve k).trans (seqCl_map_length gs resolve (k + 1)).symm
      have hle : muAll (refUAll gs) (seqCl gs resolve k) ≤
          muAll (refUAll gs) (seqCl gs resolve (k + 1)) :=
        muAll_mono _ _ _ hl (seqCl_chain gs resolve k)
      by_cases heq : muAll (refUAll gs) (seqCl gs resolve (k + 1)) =
          muAll (refUAll gs) (seqCl gs resolve k)
      · refine Or.inl ⟨k, Nat.lt_succ_self k, fun g i r hr => ?_⟩
        by_cases hm : r ∈ ((seqCl gs resolve k).getD g []).getD i []
        · exact hm
        · have hlt := muAll_strict (refUAll gs) _ _ hl (seqCl_chain gs resolve k) g i r
            (seqCl_support gs resolve (k + 1) g i r hr) hr hm
          exact absurd heq (Nat.ne_of_gt hlt)
      · have hlt : muAll (refUAll gs) (seqCl gs resolve k) <
            muAll (refUAll gs) (seqCl gs resolve (k + 1)) :=
          Nat.lt_of_le_of_ne hle (fun e => heq e.symm)
        exact Or.inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk hlt))

theorem seqCl_stable_from (gs : List RowGrp) (resolve : ExtResolve) {j : Nat}
    (hj : SubCl (seqCl gs resolve (j + 1)) (seqCl gs resolve j)) :
    ∀ d, SubCl (seqCl gs resolve (j + d + 1)) (seqCl gs resolve (j + d))
  | 0 => hj
  | d + 1 => rowsLCl_mono gs resolve (seqCl_stable_from gs resolve hj d)

/-- 06 §7 / SCM-003 over the bundle, existence: the derived table list is a
    prefixpoint of the multi-group row equations (the external-call clause
    transcribed). -/
theorem deriveCl_prefix (gs : List RowGrp) (resolve : ExtResolve) :
    RowPrefixClOf gs resolve (deriveRowsCl gs resolve) := by
  cases seqCl_progress gs resolve (passesCl gs) with
  | inr h =>
    have h1 := muAll_le (refUAll gs) (seqCl gs resolve (passesCl gs))
    rw [seqCl_map_length] at h1
    exact absurd (Nat.le_trans h h1) (Nat.not_succ_le_self _)
  | inl h =>
    obtain ⟨j, hj, hs⟩ := h
    have hstab := seqCl_stable_from gs resolve hs (passesCl gs - j)
    have e : j + (passesCl gs - j) = passesCl gs := Nat.add_sub_cancel' (Nat.le_of_lt hj)
    rw [e] at hstab
    exact prefixCl_of_fix gs resolve (deriveRowsCl gs resolve) hstab

/-- 06 §7 / SCM-003 over the bundle, leastness: the derived table lies below
    every bundle prefixpoint whose external resolver is consistent with
    `resolve`. -/
theorem deriveCl_least (gs : List RowGrp) (resolve : ExtResolve)
    {ρ : Nat → Nat → RaisedRef → Prop} {ρx : String → RaisedRef → Prop}
    (hpre : RowPrefixCl gs resolve ρ ρx)
    (hxr : ∀ n' g' m' r, resolve n' = some ⟨g', m'⟩ → ρ g' m' r → ρx n' r)
    (g i : Nat) (r : String) (h : r ∈ ((deriveRowsCl gs resolve).getD g []).getD i []) : ρ g i r :=
  seqCl_least gs resolve hpre hxr (passesCl gs) g i r h

/-- 06 §7 / SCM-004 over the bundle: a derived ref has a direct source in some
    body of the bundle; no call cycle — local or cross-group — mints. -/
theorem deriveCl_no_mint (gs : List RowGrp) (resolve : ExtResolve) (g i : Nat) (r : String)
    (h : r ∈ ((deriveRowsCl gs resolve).getD g []).getD i []) :
    ∃ g' gp, gs.get? g' = some gp ∧ ∃ j f, ∃ hf : gp.1.fns.get? j = some f,
      (gp.2.at j f hf).Src r :=
  seqCl_no_mint gs resolve (passesCl gs) g i r h

/-! ## The multi-group carrier entry point -/

structure DeriveOutCl where
  ok : Int
  rows : List Tbl
  row : List String
  pfx : Int
  idx : Int
  code : String
  deriving BEq

def refuseCl (c : String) : DeriveOutCl := ⟨0, [], [], 0, -1, c⟩

/-- The first failing (group, member) flattened as `g * 1000000 + i`; `-1` when
    the presented table list is a prefixpoint. -/
def firstFailCl (ts : List Tbl) : Nat → List Tbl → Int
  | _, [] => -1
  | g, p :: ps =>
    let i := firstFail (ts.getD g []) 0 p
    if i = -1 then firstFailCl ts (g + 1) ps else (g : Int) * 1000000 + i

/-- The bundle row carrier: `form 0` derives the table list, `form 1` decides
    whether a presented one is a prefixpoint (`entry` names the `(group,
    member)` whose row is reported). An external reference the resolver does
    not name is refused `[rcic_scm_rows_external_ref]` — §7's clause never
    silently drops a callee row. -/
def scmRowsCl (form : Int) (gs : List RowGrp) (resolve : ExtResolve) (ts : List Tbl)
    (entry : Nat × Nat) : DeriveOutCl :=
  if form < 0 then refuseCl "[rcic_scm_rows_unknown_form]" else
  if form > 1 then refuseCl "[rcic_scm_rows_unknown_form]" else
  let unresolved := (gs.map (fun gp => gp.2.extNames)).flatten.any (fun n =>
    match resolve n with
    | some ⟨g, m⟩ =>
      match gs.get? g with
      | some gp => !(m < gp.1.fns.length)
      | none => true
    | none => true)
  if unresolved then refuseCl "[rcic_scm_rows_external_ref]" else
  if form = 0 then
    let t := deriveRowsCl gs resolve
    ⟨1, t, (t.getD entry.1 []).getD entry.2 [], 1, -1, ""⟩
  else
    if ts.length ≠ gs.length then refuseCl "[rcic_scm_rows_table]" else
    if !(ts.all (fun t => t.all (fun r => rowCanon r == r))) then refuseCl "[rcic_scm_rows_table]" else
    let i := firstFailCl ts 0 (rowsLCl gs resolve ts)
    ⟨1, ts, (ts.getD entry.1 []).getD entry.2 [], if i = -1 then 1 else 0, i, ""⟩

end Rcic.Scm.RowDerive

/-! ## Instance witnesses (M-005) -/

namespace Rcic.Scm.RowDerive.Witness
open Rcic.Scm Rcic.Scm.RowDerive

def Scex : Sig := ⟨[⟨[], .i64⟩], [], [⟨"range_violation", .i64⟩]⟩
def one : CoreVal .i64 := .i64V 1 ⟨by decide, by decide⟩
def two : CoreVal .i64 := .i64V 2 ⟨by decide, by decide⟩

/-- The E-06HandlerScope counterexample: `let _ = handle range_violation
    (raise range_violation 1) (var 0) in raise range_violation 2`. -/
def cexBody : CoreExpr Scex [] .i64 :=
  .letE (.handle "range_violation" rfl (.raise "range_violation" rfl (.lit one)) (.var 0 rfl))
    (.raise "range_violation" rfl (.lit two))
def cexProg : Bodies Scex Scex.fns := .cons cexBody .nil

theorem cex_derived : deriveRows cexProg = [["range_violation"]] := by decide

example : RowPrefix (tblRho (deriveRows cexProg)) (xrRho (fun _ => [])) cexProg := derive_prefix cexProg

example : ∀ i r, r ∈ (deriveRows cexProg).getD i [] → tblRho (deriveRows cexProg) i r :=
  derive_least cexProg (derive_prefix cexProg)

example : ∃ j f, ∃ hf : Scex.fns.get? j = some f, (cexProg.at j f hf).Src "range_violation" :=
  derive_no_mint cexProg 0 "range_violation" (by rw [cex_derived]; exact List.Mem.head _)

/-- The whole-function-removal row of `apps/rcic-residue-rows` (empty) is
    not a prefixpoint of the scoped equations. -/
theorem cex_standin_not_prefix : ¬ RowPrefix (tblRho [[]]) (xrRho (fun _ => [])) cexProg := by
  intro h
  have hm : "range_violation" ∈ (cexProg.at 0 ⟨[], .i64⟩ rfl).rowL [[]] (fun _ => []) := by decide
  exact List.not_mem_nil _ (h 0 ⟨[], .i64⟩ rfl "range_violation" ((CoreExpr.rowL_iff [[]] (fun _ => []) _ _).mp hm))

/-- A handler that catches its body's only raise: the derived row is empty,
    so no run of the entry ends raised. -/
def caughtBody : CoreExpr Scex [] .i64 :=
  .handle "range_violation" rfl (.raise "range_violation" rfl (.lit one)) (.lit two)
def caughtProg : Bodies Scex Scex.fns := .cons caughtBody .nil

theorem caught_empty : (deriveRows caughtProg).getD 0 [] = [] := by decide

example {n : Nat} {cf : Config Scex .i64}
    (hr : SCMRuns caughtProg n ⟨.i64, .evalC .nil (caughtProg.at 0 ⟨[], .i64⟩ rfl), .nil⟩ cf)
    {r : RaisedRef} {P : CoreTy} {hP : catalogPt Scex.catalog r = some P} {v : CoreVal P} :
    stepI caughtProg cf ≠ .final (.raised r hP v) :=
  derive_empty_no_raise caughtProg 0 ⟨[], .i64⟩ rfl caught_empty .nil hr

end Rcic.Scm.RowDerive.Witness

/-! ## Pins: apps/rcic-scm-rows/rcic_scm_rows_corpus.json, 49 rows

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with its prefix
("SCM-003 06 s7 ", "SCM-003 06 s11 " or "SCM-004 06 s7 ") dropped. Form-0
rows pass the empty table; every row runs at typing fuel 64 except row 37.
`ok rows e` / `no code` are the carrier's two record shapes. -/

namespace Rcic.Scm.RowDerive.Pins
open Rcic.Scm Rcic.Scm.RowDerive

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def u : RawExpr := .lit (.r []) unitTy
def li (n : Int) : RawExpr := .lit (.i n) .i64
def lb (b : Int) : RawExpr := .lit (.b b) .bool
def ls (s : String) : RawExpr := .lit (.s s) .str
def v (i : Int) : RawExpr := .var i
def rz (r : String) (t : CoreTy) : RawExpr := .raise r u t
def fn (ps : List CoreTy) (rt : CoreTy) (b : RawExpr) : RawFnDef := ⟨ps, rt, b⟩
def callL (i : Int) (args : List RawExpr) : RawExpr := .call (.local i) args
def fixRec : CoreTy := .record [("converged", B), ("state", I), ("steps", I)]
def unitCat (refs : List String) : List CatalogEntry := refs.map (fun r => ⟨r, unitTy⟩)
def cat4 : List CatalogEntry :=
  [⟨"bad_input", unitTy⟩, ⟨"negative_loop_bound", unitTy⟩, ⟨"range_violation", I⟩, ⟨"signed_overflow", unitTy⟩]
def prog (fns : List RawFnDef) (entry : Int := 0) (cat : List CatalogEntry := cat4) (ext : List ExtSig := []) :
    RawProg := ⟨fns, ext, cat, entry⟩
def ok (rows : Tbl) (e : Nat := 0) (pfx : Int := 1) (idx : Int := -1) : DeriveOut :=
  ⟨1, rows, rows.getD e [], pfx, idx, ""⟩
def no (c : String) : DeriveOut := ⟨0, [], [], 0, -1, c⟩
def rv : String := "range_violation"
def bad : String := "bad_input"
def ovf : String := "signed_overflow"

def fDirect : RawFnDef := fn [] unitTy (rz bad unitTy)
def fCex : RawFnDef := fn [] I (.letE (.handle rv (.raise rv (li 1) I) (v 0)) (.raise rv (li 2) I))
def gRv : RawFnDef := fn [I] I (.raise rv (v 0) I)
def fTo (i : Int) : RawFnDef := fn [] unitTy (callL i [])
def fRec : RawFnDef :=
  fn [I] I (.ifE (.prim "lt" [v 0, li 1]) (li 0) (.prim "add" [v 0, callL 0 [.prim "sub" [v 0, li 1]]]))
def twoHop : RawProg := prog [fTo 1, fTo 2, fDirect]
def cyc0 : RawProg := prog [fn [] I (callL 1 []), fn [] I (callL 0 [])]
def inHandler : RawProg := prog [gRv, fn [] I (.handle rv (callL 0 [li 1]) (li 0))] 1
def opRow (op : String) (rt : CoreTy) (args : List RawExpr) : RawProg := prog [fn [] rt (.prim op args)]

def p1 : RawExpr :=
  .letE (.letE (rz "p_let_a" I) (rz "p_let_b" I))
  (.letE (.ifE (rz "p_if_c" B) (rz "p_if_th" I) (rz "p_if_el" I))
  (.letE (.pair (rz "p_pair_a" I) (rz "p_pair_b" B))
  (.letE (.fst (rz "p_fst" (.pair I I)))
  (.letE (.snd (rz "p_snd" (.pair I I)))
  (.letE (.inj 0 [I, B] (rz "p_inj" I))
  (.letE (.field (rz "p_field" (.record [("a", I)])) 0)
    (.cons (rz "p_cons_h" I) (rz "p_cons_tl" (.list I)))))))))
def r1 : List String :=
  ["p_cons_h", "p_cons_tl", "p_field", "p_fst", "p_if_c", "p_if_el", "p_if_th", "p_inj", "p_let_a",
   "p_let_b", "p_pair_a", "p_pair_b", "p_snd"]
def p2 : RawExpr :=
  .letE (.matchE (rz "p_match_s" (.sum [I, B])) [rz "p_match_b0" I, rz "p_match_b1" I])
  (.letE (.recordE ["a", "b"] [rz "p_rec_f0" I, rz "p_rec_f1" B])
  (.letE (.fold (rz "p_fold_l" (.list I)) (rz "p_fold_init" I) (rz "p_fold_body" I))
  (.letE (.fix (rz "p_fix_init" I) (rz "p_fix_limit" I) (rz "p_fix_stop" B) (rz "p_fix_step" I))
  (.letE (.prim "lt" [rz "p_prim_a0" I, rz "p_prim_a1" I])
  (.letE (callL 1 [rz "p_call_a0" I, rz "p_call_a1" I])
  (.letE (.raise "p_raise_r" (rz "p_raise_p" unitTy) I)
    (.handle "p_handle_r" (li 0) (rz "p_handle_h" I))))))))
def r2cat : List String :=
  ["p_call_a0", "p_call_a1", "p_fix_init", "p_fix_limit", "p_fix_step", "p_fix_stop", "p_fold_body",
   "p_fold_init", "p_fold_l", "p_handle_h", "p_handle_r", "p_match_b0", "p_match_b1", "p_match_s",
   "p_prim_a0", "p_prim_a1", "p_raise_p", "p_raise_r", "p_rec_f0", "p_rec_f1"]
def r2row : List String :=
  ["negative_loop_bound", "p_call_a0", "p_call_a1", "p_fix_init", "p_fix_limit", "p_fix_step",
   "p_fix_stop", "p_fold_body", "p_fold_init", "p_fold_l", "p_handle_h", "p_match_b0", "p_match_b1",
   "p_match_s", "p_prim_a0", "p_prim_a1", "p_raise_p", "p_raise_r", "p_rec_f0", "p_rec_f1"]

-- 0 a direct raise is in the row of its function
#guard scmRows 0 64 (prog [fDirect]) [] == ok [[bad]]
-- 1 E-06HandlerScope a ref handled in one place and raised outside the handler stays in the row
#guard scmRows 0 64 (prog [fCex]) [] == ok [[rv]]
-- 2 E-06HandlerScope a handler removes its ref from its own body's row
#guard scmRows 0 64 (prog [fn [] I (.handle rv (.raise rv (li 1) I) (li 0))]) [] == ok [[]]
-- 3 E-06HandlerScope a handler keeps its handler expression's row even for its own ref
#guard scmRows 0 64 (prog [fn [] I (.handle rv (.raise rv (li 1) I) (.raise rv (v 0) I))]) [] == ok [[rv]]
-- 4 a nonmatching handler leaves the raised ref in the row
#guard scmRows 0 64 (prog [fn [] I (.handle bad (.raise rv (li 1) I) (li 0))]) [] == ok [[rv]]
-- 5 nested handlers each remove only their own ref from their own body
#guard scmRows 0 64 (prog [fn [] I (.handle bad (.handle rv (.letE (rz bad I) (.raise rv (li 1) I)) (li 0))
    (rz ovf I))]) [] == ok [[ovf]]
-- 6 add contributes its direct row
#guard scmRows 0 64 (opRow "add" I [li 1, li 2]) [] == ok [[ovf]]
-- 7 sub contributes its direct row
#guard scmRows 0 64 (opRow "sub" I [li 1, li 2]) [] == ok [[ovf]]
-- 8 mul contributes its direct row
#guard scmRows 0 64 (opRow "mul" I [li 1, li 2]) [] == ok [[ovf]]
-- 9 neg contributes its direct row
#guard scmRows 0 64 (opRow "neg" I [li 1]) [] == ok [[ovf]]
-- 10 div contributes its direct row
#guard scmRows 0 64 (opRow "div" I [li 4, li 2]) [] ==
  ok [["division_by_zero", "nonexact_division", ovf]]
-- 11 mod contributes its direct row
#guard scmRows 0 64 (opRow "mod" I [li 4, li 3]) [] == ok [["division_by_zero"]]
-- 12 lt contributes its direct row
#guard scmRows 0 64 (opRow "lt" B [li 1, li 2]) [] == ok [[]]
-- 13 eq contributes its direct row
#guard scmRows 0 64 (opRow "eq" B [li 1, li 2]) [] == ok [[]]
-- 14 str_len contributes its direct row (E-06LenRows)
#guard scmRows 0 64 (opRow "str_len" I [ls "abc"]) [] == ok [[ovf]]
-- 15 str_slice contributes its direct row
#guard scmRows 0 64 (opRow "str_slice" Str [ls "abc", li 0, li 1]) [] == ok [["index_out_of_range"]]
-- 16 str_split contributes its direct row
#guard scmRows 0 64 (opRow "str_split" (.list Str) [ls "a,b", ls ","]) [] == ok [["empty_separator"]]
-- 17 str_to_i64 contributes its direct row
#guard scmRows 0 64 (opRow "str_to_i64" I [ls "12"]) [] == ok [["malformed_integer", ovf]]
-- 18 bytes_pack contributes its direct row
#guard scmRows 0 64 (opRow "bytes_pack" .bytes [.cons (li 1) (.nil I)]) [] == ok [["byte_out_of_range"]]
-- 19 bytes_len contributes its direct row (E-06LenRows)
#guard scmRows 0 64 (opRow "bytes_len" I [.lit (.y [1, 2]) .bytes]) [] == ok [[ovf]]
-- 20 a primitive overflow caught by a matching handler leaves the row empty
#guard scmRows 0 64 (prog [fn [] I (.handle ovf (.prim "add" [li 9223372036854775807, li 1]) (li (-1)))]) []
  == ok [[]]
-- 21 a bounded fix contributes negative_loop_bound even with a positive literal limit (06 s12)
#guard scmRows 0 64 (prog [fn [] fixRec (.fix (li 0) (li 10) (lb 1) (v 0))]) [] == ok [["negative_loop_bound"]]
-- 22 a local call contributes the callee's row
#guard scmRows 0 64 (prog [gRv, fn [] I (callL 0 [li 1])] 1) [] == ok [[rv], [rv]] 1
-- 23 E-06HandlerScope a call inside a handler for the callee's ref leaves the caller's row empty while the callee keeps it
#guard scmRows 0 64 inHandler [] == ok [[rv], []] 1
-- 24 E-06HandlerScope the same call outside the handler keeps the ref
#guard scmRows 0 64 (prog [gRv, fn [] I (.letE (.handle rv (callL 0 [li 1]) (li 0)) (callL 0 [li 2]))] 1) []
  == ok [[rv], [rv]] 1
-- 25 GM-SCM-001 a two-hop chain f to g to h reaches f only by iteration
#guard scmRows 0 64 twoHop [] == ok [[bad], [bad], [bad]]
-- 26 a chain of four functions carries the far end's raise to the entry
#guard scmRows 0 64 (prog [fTo 1, fTo 2, fTo 3, fDirect]) [] == ok [[bad], [bad], [bad], [bad]]
-- 27 GM-SCM-002 a call cycle with no raise anywhere derives empty rows
#guard scmRows 0 64 cyc0 [] == ok [[], []]
-- 28 a call cycle carrying one direct raise propagates exactly that raise
#guard scmRows 0 64 (prog [fn [] I (callL 1 []), fn [] I (.ifE (lb 1) (rz bad I) (callL 0 []))]) []
  == ok [[bad], [bad]]
-- 29 self-recursion mints nothing beyond its primitives' rows
#guard scmRows 0 64 (prog [fRec]) [] == ok [[ovf]]
-- 30 a self-loop with no raise derives the empty row
#guard scmRows 0 64 (prog [fn [] I (callL 0 [])]) [] == ok [[]]
-- 31 the entry row is the entry function's row
#guard scmRows 0 64 (prog [fDirect, fn [] I (li 0)] 1) [] == ok [[bad], []] 1
-- 32 every child position of let if pair fst snd inj field and cons contributes its row
#guard scmRows 0 64 (prog [fn [] (.list I) p1] 0 (unitCat r1)) [] == ok [r1]
-- 33 every child position of match record fold fix prim call raise and handler contributes its row
#guard scmRows 0 64 (prog [fn [] I p2, fn [I, I] I (v 0)] 0 (unitCat r2cat)) [] == ok [r2row, []]
-- 34 an external call refused its callee group is not in this bundle
#guard scmRows 0 64 (prog [fn [] I (.handle bad (li 0) (.call (.ext "ext.len") [ls "a"]))] 0 cat4
    [⟨"ext.len", [Str], I⟩]) [] == no "[rcic_scm_rows_external_call]"
-- 35 an ill-typed program refused before rows are derived
#guard scmRows 0 64 (prog [fn [] B (rz bad I)]) [] == no "[rcic_scm_typing_mismatch]"
-- 36 a raise of a ref outside the catalog refused by typing
#guard scmRows 0 64 (prog [fn [] I (rz "zz_missing" I)]) [] == no "[rcic_scm_typing_residue_ref]"
-- 37 typing fuel exhausted refused not decided  (fuel 1)
#guard scmRows 0 1 (prog [fn [] I (.letE (li 1) (.letE (li 2) (.letE (li 3) (v 0))))]) []
  == no "[rcic_scm_typing_fuel]"
-- 38 unknown form 2 refused
#guard scmRows 2 64 (prog [fDirect]) [] == no "[rcic_scm_rows_unknown_form]"
-- 39 unknown form -1 refused
#guard scmRows (-1) 64 (prog [fDirect]) [] == no "[rcic_scm_rows_unknown_form]"
-- 40 form 1 the derived table of a call inside a handler is a prefixpoint under the scoped equations
#guard scmRows 1 64 inHandler [[rv], []] == ok [[rv], []] 1
-- 41 form 1 E-06HandlerScope the whole-function-removal table of the counterexample is not a prefixpoint
#guard scmRows 1 64 (prog [fCex]) [[]] == ok [[]] 0 0 0
-- 42 form 1 a strict superset of the least table is also a prefixpoint
#guard scmRows 1 64 (prog [fCex]) [[bad, rv]] == ok [[bad, rv]]
-- 43 form 1 a table missing a callee-propagated ref fails at the caller
#guard scmRows 1 64 (prog [gRv, fn [] I (callL 0 [li 1])] 1) [[rv], []] == ok [[rv], []] 1 0 1
-- 44 form 1 the first failing function is reported
#guard scmRows 1 64 (prog [fDirect, fn [] I (li 0), fDirect] 1) [[], [], []] == ok [[], [], []] 1 0 0
-- 45 form 1 the empty table is a prefixpoint of a raise-free cycle
#guard scmRows 1 64 cyc0 [[], []] == ok [[], []]
-- 46 form 1 a table of the wrong length refused
#guard scmRows 1 64 twoHop [[bad]] == no "[rcic_scm_rows_table]"
-- 47 form 1 an unsorted row refused
#guard scmRows 1 64 (prog [fCex]) [[rv, bad]] == no "[rcic_scm_rows_table]"
-- 48 form 1 a row with a duplicate ref refused
#guard scmRows 1 64 (prog [fCex]) [[rv, rv]] == no "[rcic_scm_rows_table]"

/-! ## Multi-group pins (`scmRowsCl` — 06 §7 external-call clause over a
`RowGrp` bundle; the resolver names a `(group, member)` cell). -/

/-- The caller group: one function whose body is the external call `g1.f0`. -/
def Scal : Sig := ⟨[⟨[], .i64⟩], [⟨"g1.f0", [], .i64⟩], cat4⟩
def ecal : CoreExpr Scal [] .i64 := .call (.external "g1.f0" ⟨"g1.f0", [], .i64⟩ rfl) .nil
def scalProg : Bodies Scal Scal.fns := .cons ecal .nil

/-- The caller group with an i64-typed external argument that itself raises. -/
def ScalA : Sig := ⟨[⟨[], .i64⟩], [⟨"g1.f0", [.i64], .i64⟩], cat4 ++ [⟨"arg_err", .i64⟩]⟩
def ecalA : CoreExpr ScalA [] .i64 :=
  .call (.external "g1.f0" ⟨"g1.f0", [.i64], .i64⟩ rfl)
    (.cons (.raise "arg_err" (P := .i64) rfl (.lit Witness.one)) .nil)
def scalAProg : Bodies ScalA ScalA.fns := .cons ecalA .nil

/-- The callee group: member 0 raises `range_violation`. -/
def Srv : Sig := ⟨[⟨[], .i64⟩], [], cat4⟩
def erv : CoreExpr Srv [] .i64 := .raise rv (P := .i64) rfl (.lit Witness.one)
def srvProg : Bodies Srv Srv.fns := .cons erv .nil

/-- Two raise-free groups calling each other through external names. -/
def Scyc : Sig := ⟨[⟨[], .i64⟩], [⟨"g1.f0", [], .i64⟩], []⟩
def cycB : CoreExpr Scyc [] .i64 := .call (.external "g1.f0" ⟨"g1.f0", [], .i64⟩ rfl) .nil
def Sdyc : Sig := ⟨[⟨[], .i64⟩], [⟨"g0.f0", [], .i64⟩], []⟩
def dycB : CoreExpr Sdyc [] .i64 := .call (.external "g0.f0" ⟨"g0.f0", [], .i64⟩ rfl) .nil

def clgs : List RowGrp := [⟨Scal, scalProg⟩, ⟨Srv, srvProg⟩]
def clarg : List RowGrp := [⟨ScalA, scalAProg⟩, ⟨Srv, srvProg⟩]
def clcyc : List RowGrp := [⟨Scyc, .cons cycB .nil⟩, ⟨Sdyc, .cons dycB .nil⟩]

/-- `g1.f0` resolves to group 1 member 0; every other name is open. -/
def resG : ExtResolve := fun n => if n == "g1.f0" then some ⟨1, 0⟩ else none
/-- The cross-group cycle's resolver. -/
def resCyc : ExtResolve := fun n =>
  if n == "g1.f0" then some ⟨1, 0⟩ else if n == "g0.f0" then some ⟨0, 0⟩ else none

def okCl (rows : List Tbl) (row : List String) (pfx : Int := 1) (idx : Int := -1) : DeriveOutCl :=
  ⟨1, rows, row, pfx, idx, ""⟩
def noCl (c : String) : DeriveOutCl := ⟨0, [], [], 0, -1, c⟩

-- 49 form 0 an external call resolved across groups carries the callee row
#guard scmRowsCl 0 clgs resG [] (0, 0) == okCl [[[rv]], [[rv]]] [rv]
-- 50 form 0 an external name the resolver leaves open refused
#guard scmRowsCl 0 clgs (fun _ => none) [] (0, 0) == noCl "[rcic_scm_rows_external_ref]"
-- 51 form 0 a resolved name pointing outside the bundle refused
#guard scmRowsCl 0 clgs (fun _ => some ⟨5, 0⟩) [] (0, 0) == noCl "[rcic_scm_rows_external_ref]"
-- 52 form 0 a resolved member index out of the callee group refused
#guard scmRowsCl 0 clgs (fun _ => some ⟨1, 3⟩) [] (0, 0) == noCl "[rcic_scm_rows_external_ref]"
-- 53 form 0 an external argument raise unions with the callee row
#guard scmRowsCl 0 clarg resG [] (0, 0) == okCl [[["arg_err", rv]], [[rv]]] ["arg_err", rv]
-- 54 form 0 a raise-free cross-group external cycle mints nothing (SCM-004)
#guard scmRowsCl 0 clcyc resCyc [] (0, 0) == okCl [[[]], [[]]] []
-- 55 form 1 the derived bundle table is a prefixpoint
#guard scmRowsCl 1 clgs resG [[[rv]], [[rv]]] (0, 0) == okCl [[[rv]], [[rv]]] [rv]
-- 56 form 1 a table missing the callee-propagated ref fails at the caller cell
#guard scmRowsCl 1 clgs resG [[[]], [[rv]]] (0, 0) == okCl [[[]], [[rv]]] [] 0 0
-- 57 form 1 a table missing the callee's own ref fails at the group-1 cell
#guard scmRowsCl 1 clgs resG [[[rv]], [[]]] (0, 0) == okCl [[[rv]], [[]]] [rv] 0 1000000
-- 58 form 1 a table of the wrong length refused
#guard scmRowsCl 1 clgs resG [[[rv]]] (0, 0) == noCl "[rcic_scm_rows_table]"
-- 59 form 1 an unsorted row in a presented table refused
#guard scmRowsCl 1 clgs resG [[[rv, rv]], [[rv]]] (0, 0) == noCl "[rcic_scm_rows_table]"
-- 60 unknown form 2 refused
#guard scmRowsCl 2 clgs resG [] (0, 0) == noCl "[rcic_scm_rows_unknown_form]"
-- 61 unknown form -1 refused
#guard scmRowsCl (-1) clgs resG [] (0, 0) == noCl "[rcic_scm_rows_unknown_form]"

end Rcic.Scm.RowDerive.Pins
