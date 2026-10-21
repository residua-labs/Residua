import rcic.ScmSrcGroupsAdm
import rcic.RcicDTMetaTypedEmbed
import rcic.RcicFixtures

/-!
# Finite no-recursor supplier for DT-020

The finite table check pays the complete `no DerivedIota` premise of the
typed embedding theorem. Distinct keys and the absence of recursors remain
explicit hypotheses; this does not establish coverage of the lambda profile.
The mutant below deletes only the no-recursor check. It accepts the landed
Nat table, which carries the actual landed `wZero` iota witness.
-/

namespace Rcic.Declarative

/-- A checked finite table cannot supply the recursor member required by
    any derived iota witness. -/
theorem noDerivedIota_foldEnv_of_noRecursors
    {tbl : List (Nat × CheckedMember)}
    (hnd : (tbl.map (·.1)).Nodup)
    (hno : tbl.all
      (fun p => decide (p.2.mclass ≠ MemberClass.recursorM)) = true)
    (lhs rhs : Expr Nat) :
    DerivedIota (Rcic.Scm.SrcG.foldEnv tbl) lhs rhs → False := by
  intro hd
  cases hd with
  | of w =>
      have hmem := w.hrec
      rw [Rcic.Scm.SrcG.foldEnv_members hnd] at hmem
      obtain ⟨q, hf, hq2⟩ := Option.map_eq_some'.mp hmem
      have hqmem : q ∈ tbl := List.mem_of_find?_eq_some hf
      have hb := (List.all_eq_true.mp hno) q hqmem
      have hclass : q.2.mclass ≠ MemberClass.recursorM := of_decide_eq_true hb
      exact hclass ((congrArg CheckedMember.mclass hq2).trans w.hrecK)

/-- Compose the finite supplier with the landed typed embedding theorem;
    no independently assumed universal no-iota premise remains. -/
theorem DT020T_noRecursorTable
    {tbl : List (Nat × CheckedMember)}
    (hnd : (tbl.map (·.1)).Nodup)
    (hno : tbl.all
      (fun p => decide (p.2.mclass ≠ MemberClass.recursorM)) = true)
    {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT (Rcic.Scm.SrcG.foldEnv tbl) n Γ e A) :
    NoIotaTy h :=
  DT020T_lambda_embeds_into_iota
    (noDerivedIota_foldEnv_of_noRecursors hnd hno) h

/-- The executable conjunction of the supplier's two finite premises. -/
def forall8NoRecursorTableCheckB (tbl : List (Nat × CheckedMember)) : Bool :=
  decide (tbl.map (·.1)).Nodup &&
    tbl.all (fun p => decide (p.2.mclass ≠ MemberClass.recursorM))

/-- Mutant: delete the no-recursor conjunct, preserving distinct keys. -/
def forall8NoRecursorTableCheckB_dropNoRecursor
    (tbl : List (Nat × CheckedMember)) : Bool :=
  decide (tbl.map (·.1)).Nodup

/-- A nonempty table of the landed Nat family and constructors. -/
def forall8NoRecursorPrefix : List (Nat × CheckedMember) :=
  [(0, natFamMember), (1, natZeroMember), (2, natSuccMember)]

/-- Add the landed Nat recursor to the same table. -/
def forall8RecursorTable : List (Nat × CheckedMember) :=
  forall8NoRecursorPrefix ++ [(3, natRecMember)]

theorem pin_forall8_noRecursorPrefix_accepts :
    forall8NoRecursorTableCheckB forall8NoRecursorPrefix = true := by decide

/-- The supplier is inhabited at a nonempty table, for every redex pair. -/
theorem pin_forall8_noRecursorPrefix_noIota (lhs rhs : Expr Nat) :
    DerivedIota (Rcic.Scm.SrcG.foldEnv forall8NoRecursorPrefix) lhs rhs → False :=
  noDerivedIota_foldEnv_of_noRecursors (by decide) (by decide) lhs rhs

theorem pin_forall8_noRecursorPrefix_typed {n : Nat} :
    NoIotaTy (pinSortT (Rcic.Scm.SrcG.foldEnv forall8NoRecursorPrefix) n) :=
  DT020T_noRecursorTable (by decide) (by decide)
    (pinSortT (Rcic.Scm.SrcG.foldEnv forall8NoRecursorPrefix) n)

/-- The no-check mutant wrongly accepts a distinct-key table that actually
    has derived iota. This is a semantic counterexample, not only a flag. -/
theorem pin_forall8_dropNoRecursor_wrongly_accepts :
    forall8NoRecursorTableCheckB forall8RecursorTable = false ∧
    forall8NoRecursorTableCheckB_dropNoRecursor forall8RecursorTable = true ∧
    Nonempty (DerivedIota (Rcic.Scm.SrcG.foldEnv forall8RecursorTable)
      (iotaLhsOf wZero) (iotaRhsOf wZero)) :=
  ⟨by decide, by decide, ⟨DerivedIota.of wZero⟩⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.noDerivedIota_foldEnv_of_noRecursors
#print axioms Rcic.Declarative.DT020T_noRecursorTable
#print axioms Rcic.Declarative.pin_forall8_noRecursorPrefix_accepts
#print axioms Rcic.Declarative.pin_forall8_noRecursorPrefix_noIota
#print axioms Rcic.Declarative.pin_forall8_noRecursorPrefix_typed
#print axioms Rcic.Declarative.pin_forall8_dropNoRecursor_wrongly_accepts
