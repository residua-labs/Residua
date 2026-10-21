import rcic.RcicSynStepPbCase

/-!
# Port-free `pb` heads — `closure_claim = 0`

`pb_const_closed` and `pb_lit_closed` are `CaseStep` for one `PbHead` each.
Each proof is landed `pb_case` at that constructor: `const` reads `BitCoh` from
`Issues.occ_bitCoh` at `(0,[0])×(1,[])`, and `lit` reads the expansion `PBit`
from `Issues.occ_pb` at the same address (`pbit_lit_iff`). Neither constructor
stores a `PBit`, `BitCoh`, or frame port.

This is not unconditional `pb_case` and not `AllBelowScoped`. The per-head
census (discharged / IH answer / open) is in the PR body, not a theorem.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `TyP.const` `pb`, from `Demand` and `StepIH`. No stored port. -/
theorem pb_const_closed {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u s : Level}
    {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    {DT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort s)}
    (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.pb (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT S σ ρ) := by
  intro hq ih
  exact (pb_case Aw tbl PbHead.const) hq ih

/-- `TyP.lit` `pb`, from `Demand` and `StepIH`. No stored port. -/
theorem pb_lit_closed {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {t : Nat} {T : Expr Nat} {s : Level}
    {hexp : TyP E n Γ (natExpand t) T}
    {DT : TyP E n Γ T (.sort s)}
    (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.pb (TyP.lit E n Γ t T hexp) DT S σ ρ) := by
  intro hq ih
  exact (pb_case Aw tbl PbHead.lit) hq ih

end Rcic.Syn

#check Rcic.Syn.pb_const_closed
#print axioms Rcic.Syn.pb_const_closed
#check Rcic.Syn.pb_lit_closed
#print axioms Rcic.Syn.pb_lit_closed
