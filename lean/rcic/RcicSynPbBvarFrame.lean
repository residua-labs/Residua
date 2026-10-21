import rcic.RcicSynStepSkeleton
import rcic.RcicSynCLFromBelow
import rcic.RcicSynSpineComb

/-!
# Design point B — the `pb_bvar_bitCoh` request descends at every frame

Brief `~/.residua-devin-below/BRIEF.md` item 2, after the #7564 measure
(`pb_bvar_bitCoh_before`): the landed row `Issues.pb_bvar_bitCoh` (`RcicSynP2Shared` §E) issues
`.bitCoh hA DT S σ ρ` from `.pb (TyP.bvar … hA) DT S σ ρ` at **any** frame
`S : ScopedCtx Eₐ E₀ n₀ Γ₀`, but the landed descent `bvar_bit_request_below`
(`RcicSynRouteSlot` §2.1) is stated only for the frame `S : ScopedCtx Eₐ E n Γ` whose context is
the derivation's own. #7564 recorded "a proper prefix scope `Γ₀ ≠ Γ` is not provable". It is
provable; the restriction was in the instrument, not in the measure. `closure_claim = 0`.

**Why the descent is frame-independent.** Both queries carry the same frame, so their first
rank coordinate is the same `Γ₀.length` and their local keys are `combMeas` over the same frame
spine `enrichCtxWfT_of_envWfT S.env S.ctx`. `lexDM_combMeas_mono` (`RcicSynStepSkeleton` §1)
is stated for a spine of *any* indices, so only the payload step matters:
`hA.atoms ++ DT.atoms` against `[(bvar … hA).wt] ++ DT.atoms`, a `DMStep` because the bvar node
is a single atom heavier than `hA` (`dmStep_wt_lt_singleton`, `TyP.wt` of `bvar` is
`1 + hA.wt`). The landed `combLexDM_pbit_bvar_sort` proves the same step but fixes its spine to
`CtxP E n Γ`, which is what tied `bvar_bit_request_below` to the derivation's own frame.

Delivered (all compiled):
* `pb_bvar_bitCoh_before_frame` — the descent at every frame (the landed lemma is its
  `Γ₀ = Γ` instance);
* `pb_issued_bvar_bitCoh_frame` — the row answered from `StepIH` at every frame;
* `pb_bvar_caseStep_frame` — the `pb_case` bvar branch at every frame, composed with the landed
  `pbit_bvar_spine`. Its three remaining premises are the bvar branch's own residuals, read
  against a spine `C : CtxP E n Γ` of the **derivation's** context (not the frame): the display
  correspondence `DispForC σ C ρ`, the entry sort `C.entrySort i = some u`, and the let-entry value
  bit `SpineLetPBit σ C ρ i`. They are `pb_case`'s (grok-pbmix lane), not discharged here.

So `pb_case`'s demand needs no restatement for the bvar request: every demanded
`.pb (TyP.bvar …) DT S σ ρ` gets its `BitCoh σ hA DT` from the IH, at whatever frame it was
issued. Nothing here edits a landed declaration.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- **The proper-prefix-scope descent.** At every frame `S : ScopedCtx Eₐ E₀ n₀ Γ₀` — the
    derivation's own context, a proper prefix of it, or any other frame the row was issued
    under — the bvar's `BitCoh` request is `Before` its `.pb` issuer: same frame length, and a
    strict `LexDM` step on the local key over the shared frame spine. -/
theorem pb_bvar_bitCoh_before_frame (Aw : Nat → Nat)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s)) :
    Before Aw (.bitCoh hA DT S σ ρ)
      (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) :=
  before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _
      (lex_of_dm
        (dmStep_append_right
          (dmStep_wt_lt_singleton Aw hA (TyP.bvar E n Γ i A u hlook hA) rfl
            (by simp only [TyP.wt]; omega))
          (DT.atoms Aw))))

/-- The `pb_bvar_bitCoh` row, answered from the IH at every frame. -/
theorem pb_issued_bvar_bitCoh_frame (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {DT : TyP E n Γ A (.sort s)}
    (hq : Demand (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ))
    (ih : StepIH Aw tbl (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ)) :
    BitCoh σ hA DT :=
  ih_issue Aw tbl hq ih _ Issues.pb_bvar_bitCoh
    (pb_bvar_bitCoh_before_frame Aw S σ ρ hlook hA DT)

/-- **The `pb_case` bvar branch at every frame.** The issued `BitCoh` (above) composed with the
    landed `pbit_bvar_spine`; the three named premises are the branch's own residuals over a
    spine `C` of the derivation's context `Γ` (display, entry sort, let-entry value bit). -/
theorem pb_bvar_caseStep_frame (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {DT : TyP E n Γ A (.sort s)}
    (C : CtxP E n Γ) (hC : DispForC σ C ρ) (hsort : C.entrySort i = some u)
    (hlet : SpineLetPBit σ C ρ i) :
    CaseStep Aw tbl (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) := fun hq ih =>
  pbit_bvar_spine hC hsort hlet (pb_issued_bvar_bitCoh_frame Aw tbl hq ih)

end Rcic.Syn
