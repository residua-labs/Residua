import rcic.RcicSynPiLamRight
import rcic.RcicSynSortRow
import rcic.RcicEREraseOld
import rcic.RcicSynInlineRefute
import rcic.RcicSynSpineComb
import rcic.RcicSynCLFromBelow

/-!
# Kernel check — ER1 counterexample W-ERASURE-PI-DROP-WK (ChatGPT)

Kernel-check of the ER1 counterexample: a `TyP.wk` node's `eps` erases its
child at the *un-widened* `ρ` and lifts the resulting `ETm`
(`eps_wk_keep`), while a proof-domain `Π` erases its codomain at
`.drop :: ρ` (`RcicSynErase` :172). A derivation `Dw` built by `wk` and the
same judgment `Dd` built directly in the widened context erase
*differently*.

Objects (`emptyEnv`, arity 0, `s₀ = sort zero`):
- `ctxP = [P : s₀]`, `ctxQP = [Q : s₀, P : s₀]` (displays `[.keep]` and
  `[.keep, .keep]`).
- `D₀` : `pi (bvar 0) (bvar 1) : sort (imax 0 0)` in `ctxP`, direct
  bvar/sort/pi rules, `wt 5`.
- `Dw` := `TyP.wk` at cutoff 0 inserting `Q : s₀`.
- `Dd` := the same judgment `pi (bvar 1) (bvar 2) : sort (imax 0 0)` built
  directly in `ctxQP`.

Sealed computations:
1. `D₀`, `Dw`, `Dd` all satisfy `AssumpPref`.
2. `D₀.eps id [.keep] = pi (bvar 0) (bvar 0)`;
   `Dw.eps id [.keep,.keep] = pi (bvar 1) (bvar 0)`;
   `Dd.eps id [.keep,.keep] = pi (bvar 1) (bvar 1)`.
3. `no_cl_pi_drop_wk`: `¬ CL tbl id [.keep,.keep] Dw Dd` for every
   `TableWF tbl` — `convE_pi_inv_wf` + `not_convMod_bvar_ne` only (no
   PiRow/SortUnique).
4. `readPi` on `Dw` returns `.yes g` whose `piClauseOf g id [.keep,.keep]`
   is `pi (bvar 1) (bvar 1)` — the *direct* erasure — and therefore
   `≠ Dw.eps id [.keep,.keep]`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `s₀`: both context entries' type — `sort zero`, a proof-proposition sort. -/
abbrev erS : Expr Nat := .sort .zero

/-- `Γ = [P : s₀]`. -/
abbrev erCtxP : LCtx := [.assumption erS]

/-- `Δ = [Q : s₀, P : s₀]`. -/
abbrev erCtxQP : LCtx := [.assumption erS, .assumption erS]

/-- `P : s₀` in `Γ`: the `bvar` node typing `.bvar 0` at `sort zero`. -/
def erP_ty : TyP emptyEnv 0 erCtxP (.bvar 0) erS :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `Γ⁺ = [x : P, P : s₀]` — the binder context of `D₀`'s codomain. -/
abbrev erCtxPb : LCtx := .assumption (.bvar 0) :: erCtxP

/-- `P : s₀` as `.bvar 1` in `Γ⁺`. -/
def erP_ty_b : TyP emptyEnv 0 erCtxPb (.bvar 1) erS :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `D₀`: `Π (x : P). P : sort (imax 0 0)` in `Γ` — a proof-domain Π. -/
def erD₀ : TyP emptyEnv 0 erCtxP (.pi (.bvar 0) (.bvar 1))
    (.sort (.imax .zero .zero)) :=
  .pi _ _ _ _ .zero _ .zero erP_ty erP_ty_b

/-- `Dw`: `D₀` weakened at cutoff `0`, inserting `Q : s₀` — same judgment
    `Π (x : P). P` in `Δ`, but derived through the `wk` transport node. -/
def erDw : TyP emptyEnv 0 erCtxQP (.pi (.bvar 1) (.bvar 2))
    (.sort (.imax .zero .zero)) :=
  .wk emptyEnv 0 erCtxP (.pi (.bvar 0) (.bvar 1)) (.sort (.imax .zero .zero))
    (.assumption erS) 0 erD₀

/-- `P : s₀` as `.bvar 1` in `Δ`. -/
def erP_ty_Δ : TyP emptyEnv 0 erCtxQP (.bvar 1) erS :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `Δ⁺ = [x : P, Q : s₀, P : s₀]` — the binder context of `Dd`'s codomain. -/
abbrev erCtxQPb : LCtx := .assumption (.bvar 1) :: erCtxQP

/-- `P : s₀` as `.bvar 2` in `Δ⁺`. -/
def erP_ty_Δb : TyP emptyEnv 0 erCtxQPb (.bvar 2) erS :=
  .bvar _ _ _ _ _ _ rfl (.sort _ _ _ _ _ (eqN_refl _))

/-- `Dd`: the same judgment `Π (x : P). P : sort (imax 0 0)` built directly
    in `Δ`. -/
def erDd : TyP emptyEnv 0 erCtxQP (.pi (.bvar 1) (.bvar 2))
    (.sort (.imax .zero .zero)) :=
  .pi _ _ _ _ .zero _ .zero erP_ty_Δ erP_ty_Δb

/-- `p : P` in `Γ⁺` — the body of the proof-id λ. -/
def erBody : TyP emptyEnv 0 erCtxPb (.bvar 0) (.bvar 1) :=
  .bvar _ _ _ _ _ _ rfl erP_ty_b

/-- `λp:P.p` in `Γ` — the proof-id, typing `Π (x : P). P`. -/
def erLam : TyP emptyEnv 0 erCtxP (.lam (.bvar 0) (.bvar 0))
    (.pi (.bvar 0) (.bvar 1)) :=
  .lam _ _ _ _ .zero _ _ .zero erP_ty erBody erP_ty_b

/-- `λp:P.p` weakened into `Δ` — the object whose *regularity* is `Dw`'s
    shape. -/
def erLamW : TyP emptyEnv 0 erCtxQP (.lam (.bvar 1) (.bvar 0))
    (.pi (.bvar 1) (.bvar 2)) :=
  .wk emptyEnv 0 erCtxP (.lam (.bvar 0) (.bvar 0)) (.pi (.bvar 0) (.bvar 1))
    (.assumption erS) 0 erLam

/-! ## §1 admissibility -/

/-- `D₀` carries no transport nodes. -/
theorem erD₀_assumpPref : erD₀.AssumpPref := ⟨trivial, trivial⟩

/-- `Dw`: the `wk` node's `AssumptionPrefix` at cutoff `0` is vacuous. -/
theorem erDw_assumpPref : erDw.AssumpPref :=
  ⟨assumptionPrefix_zero erCtxP, erD₀_assumpPref⟩

/-- `Dd` carries no transport nodes. -/
theorem erDd_assumpPref : erDd.AssumpPref := ⟨trivial, trivial⟩

/-- `λp:P.p` carries no transport nodes. -/
theorem erLam_assumpPref : erLam.AssumpPref := ⟨trivial, trivial, trivial⟩

/-- Its weakening: `AssumptionPrefix` at cutoff `0` is vacuous. -/
theorem erLamW_assumpPref : erLamW.AssumpPref :=
  ⟨assumptionPrefix_zero erCtxP, erLam_assumpPref⟩

/-! ## §2 weight -/

/-- `D₀` weighs `5` (`1 + (1+1) + (1+1)`). -/
theorem erD₀_wt : erD₀.wt (fun w => w) = 5 := rfl

/-! ## §3 erasures -/

/-- `D₀` erases to `Π (_ : bvar 0). bvar 0` at display `[keep]` under the
    **frozen** pre-R2 erasure: the proof-domain binder is dropped from the
    codomain's `ρ`, so the source codomain `bvar 1` resolves to display
    slot `0`. -/
theorem erD₀_eps : erD₀.epsOld id [.keep] = .pi (.bvar 0) (.bvar 0) := by decide

/-- `Dw` erases by *un-widened* erase + `ETm.lift` under the frozen erasure:
    `(pi b0 b0).lift 0 1` keeps the codomain `bvar 0` (the `+1` cutoff under
    the Π binder shields it) — `pi (bvar 1) (bvar 0)`. -/
theorem erDw_eps : erDw.epsOld id [.keep, .keep] = .pi (.bvar 1) (.bvar 0) := by decide

/-- `Dd` erases at display `[keep, keep]` directly under the frozen erasure:
    codomain `bvar 2` resolves through `[drop, keep, keep]` to display
    slot `1` — `pi (bvar 1) (bvar 1)`. -/
theorem erDd_eps : erDd.epsOld id [.keep, .keep] = .pi (.bvar 1) (.bvar 1) := by decide

/-! ## §3b positive pins — the R2 `piSlot` fix -/

/-- `D₀` under the fixed erasure: `piSlot true` re-inserts the dropped
    binder slot into the codomain — `pi (bvar 0) (bvar 1)`. -/
theorem erD₀_eps_fixed : erD₀.eps id [.keep] = .pi (.bvar 0) (.bvar 1) := by decide

/-- `Dw` under the fixed erasure: `(pi b0 (b0↑)).lift 0 1` — the codomain's
    restored slot lifts with it — `pi (bvar 1) (bvar 2)`. -/
theorem erDw_eps_fixed : erDw.eps id [.keep, .keep] = .pi (.bvar 1) (.bvar 2) := by decide

/-- `Dd` under the fixed erasure: the codomain's own `piSlot` pad —
    `pi (bvar 1) (bvar 2)` — identical to `Dw`'s. -/
theorem erDd_eps_fixed : erDd.eps id [.keep, .keep] = .pi (.bvar 1) (.bvar 2) := by decide

/-- The frozen and fixed erasures of `Dw` diverge — the bug is real and
    the fix changed the value: `pi (bvar 1) (bvar 0) ≠ pi (bvar 1) (bvar 2)`. -/
theorem erDw_eps_ne_epsOld :
    erDw.eps id [.keep, .keep] ≠ erDw.epsOld id [.keep, .keep] := by decide

/-! ## §4 `CL` refusal (frozen) and agreement (fixed) -/

/-- The weakened and the directly-built derivations of the same judgment are
    NOT `CLold`-related under the frozen erasure: their erased codomains are
    `bvar 0` vs `bvar 1`, and Π-injectivity in `E` plus `bvar` rigidity
    refuse. -/
theorem no_cl_pi_drop_wk {tbl : List CRule} (hW : TableWF tbl) :
    ¬ CLold tbl id [.keep, .keep] erDw erDd := by
  intro h
  unfold CLold at h
  obtain ⟨_, hc⟩ := convE_pi_inv_wf hW h
  exact not_convMod_bvar_ne hW (by decide : (0 : Nat) ≠ 1) hc

/-- Under the fixed erasure they ARE `CL`-related — both erase to
    `pi (bvar 1) (bvar 2)`. This is the R2 positive pin: the wk'd and
    direct derivations of one proof-domain Π judgment now erase alike. -/
theorem cl_pi_drop_wk {tbl : List CRule} (hW : TableWF tbl) :
    CL tbl id [.keep, .keep] erDw erDd := by
  unfold CL
  rw [erDw_eps_fixed, erDd_eps_fixed]
  exact .refl _

/-! ## §5 readPi through the wk -/

/-- `erDw.atoms` is the single atom `[erD₀.wt]` (the `wk` transport exposes
    its child's atoms), so `src = erD₀.wt + 1` bounds it. -/
theorem erDw_atoms_bound :
    ∀ y ∈ erDw.atoms (fun w => w), y < erD₀.wt (fun w => w) + 1 := by
  intro y hy
  have hy' : y = erD₀.wt (fun w => w) := List.mem_singleton.mp hy
  omega

/-- `readPi` through `Dw`'s `wk` node returns `.yes` — and the read-back Π
    clause is `pi (bvar 1) (bvar 2)`, which disagrees with `Dw`'s *frozen*
    `epsOld` (`pi (bvar 1) (bvar 0)`). The read machinery recomputes the
    clause from the un-weakened `Π` node — under the fixed semantics it now
    lands on the same value `Dw.eps` produces. -/
theorem erDw_readPi_clause_ne_eps :
    ∃ g : PiGot (fun w => w) (erD₀.wt (fun w => w) + 1) emptyEnv 0 erCtxQP
        (.bvar 1) (.bvar 2),
        readPi (envExt_refl emptyEnv) (fun w => w) (erD₀.wt (fun w => w) + 1)
          erDw rfl erDw_atoms_bound = .yes g ∧
        piClauseOf g id [.keep, .keep] = .pi (.bvar 1) (.bvar 2) ∧
        piClauseOf g id [.keep, .keep] ≠ erDw.epsOld id [.keep, .keep] := by
  refine ⟨_, rfl, ?_, ?_⟩
  · decide
  · decide

/-- `erLamW.reg.2`'s atoms are `erDw`'s (the `wk` transport exposes its
    child's), so the same `src` bound applies. -/
theorem erLamW_reg_atoms_bound :
    ∀ y ∈ erLamW.reg.2.atoms (fun w => w), y < erD₀.wt (fun w => w) + 1 := by
  intro y hy
  have hy' : y = erD₀.wt (fun w => w) := List.mem_singleton.mp hy
  omega

/-- The spec's part-4 tooth, frozen side: `readPi` on the regularity of the
    *weakened* `λp:P.p` returns `.yes` — and `piClauseOf g` disagrees with
    `Dw`'s frozen `epsOld`, `pi (bvar 1) (bvar 2) ≠ pi (bvar 1) (bvar 0)`. -/
theorem erLamW_reg_readPi_clause_ne_eps :
    ∃ g : PiGot (fun w => w) (erD₀.wt (fun w => w) + 1) emptyEnv 0 erCtxQP
        (.bvar 1) (.bvar 2),
        readPi (envExt_refl emptyEnv) (fun w => w) (erD₀.wt (fun w => w) + 1)
          erLamW.reg.2 rfl erLamW_reg_atoms_bound = .yes g ∧
        piClauseOf g id [.keep, .keep] ≠ erDw.epsOld id [.keep, .keep] := by
  refine ⟨_, rfl, ?_⟩
  decide

/-! ## §6 readPi agreement (fixed) -/

/-- `readPi` through `Dw`'s `wk` still returns `.yes`, and the read-back Π
    clause now agrees with `Dw`'s own `eps` — `pi (bvar 1) (bvar 2)` — under
    the fixed erasure. The recomputed clause and the transport produce the
    same value; the ER1 mismatch is gone. -/
theorem erDw_readPi_clause_eq_eps_fixed :
    ∃ g : PiGot (fun w => w) (erD₀.wt (fun w => w) + 1) emptyEnv 0 erCtxQP
        (.bvar 1) (.bvar 2),
        readPi (envExt_refl emptyEnv) (fun w => w) (erD₀.wt (fun w => w) + 1)
          erDw rfl erDw_atoms_bound = .yes g ∧
        piClauseOf g id [.keep, .keep] = erDw.eps id [.keep, .keep] := by
  refine ⟨_, rfl, ?_⟩
  decide

/-- The same agreement through the weakened `λp:P.p` regularity. -/
theorem erLamW_reg_readPi_clause_eq_eps_fixed :
    ∃ g : PiGot (fun w => w) (erD₀.wt (fun w => w) + 1) emptyEnv 0 erCtxQP
        (.bvar 1) (.bvar 2),
        readPi (envExt_refl emptyEnv) (fun w => w) (erD₀.wt (fun w => w) + 1)
          erLamW.reg.2 rfl erLamW_reg_atoms_bound = .yes g ∧
        piClauseOf g id [.keep, .keep] = erDw.eps id [.keep, .keep] := by
  refine ⟨_, rfl, ?_⟩
  decide

end Rcic.Syn

#print axioms Rcic.Syn.erS
#print axioms Rcic.Syn.erCtxP
#print axioms Rcic.Syn.erCtxQP
#print axioms Rcic.Syn.erCtxPb
#print axioms Rcic.Syn.erCtxQPb
#print axioms Rcic.Syn.erP_ty
#print axioms Rcic.Syn.erP_ty_b
#print axioms Rcic.Syn.erP_ty_Δ
#print axioms Rcic.Syn.erP_ty_Δb
#print axioms Rcic.Syn.erD₀
#print axioms Rcic.Syn.erDw
#print axioms Rcic.Syn.erDd
#print axioms Rcic.Syn.erBody
#print axioms Rcic.Syn.erLam
#print axioms Rcic.Syn.erLamW
#print axioms Rcic.Syn.erD₀_assumpPref
#print axioms Rcic.Syn.erDw_assumpPref
#print axioms Rcic.Syn.erDd_assumpPref
#print axioms Rcic.Syn.erLam_assumpPref
#print axioms Rcic.Syn.erLamW_assumpPref
#print axioms Rcic.Syn.erD₀_wt
#print axioms Rcic.Syn.erD₀_eps
#print axioms Rcic.Syn.erDw_eps
#print axioms Rcic.Syn.erDd_eps
#print axioms Rcic.Syn.no_cl_pi_drop_wk
#print axioms Rcic.Syn.erDw_atoms_bound
#print axioms Rcic.Syn.erDw_readPi_clause_ne_eps
#print axioms Rcic.Syn.erLamW_reg_atoms_bound
#print axioms Rcic.Syn.erLamW_reg_readPi_clause_ne_eps
