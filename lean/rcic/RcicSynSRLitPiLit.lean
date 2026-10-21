import rcic.RcicSynClosedUconstlit
import rcic.RcicSynTableOfIFull
import rcic.RcicSynStarLift
import rcic.RcicSynFamRigid
import rcic.RcicSynCR

/-!
# RcicSynSRLitPiLit — sortRow row 7 (`es_lit`): `lit_surfaceCL` REFUTED

Census row 7 (`TABLEOFI_SUPPLIER_CENSUS.md`): `es_lit_closed` retains the
single (d) wall `hL : CL tbl σ ρ dl (litSurface hlit hexp)` at arbitrary
`dl : TyP E n Γ (.lit t) T` ("missing: `lit_surfaceCL`, arbitrary `dl`").
This module gives the kernel refutation at the `natEnvU` fixture, `t := 0`,
`T := .const 0 []`, `tbl := tableOfI natEnvUWfT`, `ρ := []`:

* `hexp := sr2_zeroTy` types `zero` through the family node, whose `const`
  cutoff universe is literally `.succ .zero`;
* the tooth `dl := sr2_litTooth` types `zero` through a `sort`-conversion
  `sr2_sortsConv : sort 1 ≡ sort (max 1 0)` (legal: `eqN` is semantic, and
  `max 1 0` evaluates to `1` at every valuation), so its `const` cutoff is
  literally `.max (.succ .zero) .zero`;
* `σ := sr2_σ` zeroes `.succ .zero` and fixes every other level. Then
  `levelIsZero (σ (.succ .zero)) = true` but
  `levelIsZero (σ (.max (.succ .zero) .zero)) = false`, so the surface
  erases to `.star` and the tooth to `.const 1 []`;
* `★` is E-normal (`eStep_star_normal`), `const 1` is rigid in
  `tableOfI natEnvUWfT` (`noHeadRule_tableOfI_nat_one`), and `≈` relates
  `★` only to `★` — the erasures are not convertible in `E ∪ ≈`
  (`not_convMod_star_const`, via the landed Church–Rosser join).

`eqN` does not constrain `σ`: the substitution is applied to the STORED
cutoff syntax, and `σ 1 ≠ σ (max 1 0)` — that is the whole tooth. Every
other premise of `es_lit_closed` at this fixture is inhabited
(`sr2_lit_row_premises_nonvacuous`); the row is REFUTED, not discharged.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 level/erasure helpers -/

theorem sr2_eqN_max_zero (l : Level) : eqN (.max l .zero) l := by
  intro ρ
  cases hev : Declarative.eval ρ l with
  | none => simp [Declarative.eval, hev]
  | some x => simp [Declarative.eval, hev, Nat.max_zero]

theorem sr2_eqN_succ {l l' : Level} (h : eqN l l') : eqN (.succ l) (.succ l') := by
  intro ρ
  simp only [Declarative.eval, h ρ]

/-- `¬ ★ ↔*_{E ∪ ≈} (const r ls)` at a well-formed table with no `r`-headed
    rule: both sides are E-normal, so the Church–Rosser join collapses to
    `≈`, which relates `★` only to `★`. -/
theorem not_convMod_star_const {tbl : List CRule} (hW : TableWF tbl)
    {r : Nat} {ls : List Level} (hN : NoHeadRule tbl r) :
    ¬ ConvMod (EStep tbl) LvlEq .star (.const r ls) := by
  intro hc
  obtain ⟨c, d, hc', hq, hd'⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr)
      (confluent_eStep_wf hW) hc
  have e1 : c = .star := rstar_of_normal (eStep_star_normal tbl) hc'
  have e2 : d = .const r ls := by
    have hd'' : RStar (EStep tbl) (ETm.appN (.const r ls) []) d := hd'
    obtain ⟨xs, hxs, hlen, _⟩ := rstar_eStep_appN_const_inv hN hd''
    have hnil : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => exact absurd hlen (by simp)
    rw [hnil] at hxs
    exact hxs
  subst e1
  subst e2
  nomatch hq

/-! ## §2 the `natEnvU` fixture: two zero-typings, one separating `σ` -/

/-- `N = const 0 [] : sort 1` in any context (the family const node over
    `sort 1 : sort 2`). -/
def sr2_famTy (Γ : LCtx) : TyP natEnvU 0 Γ (.const 0 []) (.sort (.succ .zero)) :=
  TyP.const natEnvU 0 Γ 0 [] [] natFamMember (.succ (.succ .zero))
    (rfl : natEnvU.members 0 = some natFamMember) rfl
    (rfl : levelsBounded 0 [] = true) (eqNList_refl [])
    (TyP.sort natEnvU 0 Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `zero = const 1 [] : N` through the family node — the canonical
    expansion typing (the row's `hexp` side). Its `const` cutoff is
    `.succ .zero`. -/
def sr2_zeroTy : TyP natEnvU 0 [] (.const 1 []) (.const 0 []) :=
  TyP.const natEnvU 0 [] 1 [] [] natZeroMember (.succ .zero)
    (rfl : natEnvU.members 1 = some natZeroMember) rfl
    (rfl : levelsBounded 0 [] = true) (eqNList_refl []) (sr2_famTy [])

/-- The legal sort conversion `sort 1 ≡ sort (max 1 0)` at `sort 2`:
    `eqN` is semantic (`max 1 0` evaluates to `1` everywhere,
    `sr2_eqN_max_zero`), so `CvP.sorts` accepts it. -/
def sr2_sortsConv :
    CvP natEnvU 0 [] (.sort (.succ .zero)) (.sort (.max (.succ .zero) .zero))
      (.sort (.succ (.succ .zero))) :=
  CvP.sorts natEnvU 0 [] (.succ .zero) (.max (.succ .zero) .zero)
    (fun ρ => (sr2_eqN_max_zero (.succ .zero) ρ).symm)
    (TyP.sort natEnvU 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort natEnvU 0 [] (.max (.succ .zero) .zero) (.succ (.succ .zero))
      (sr2_eqN_succ (fun ρ => (sr2_eqN_max_zero (.succ .zero) ρ).symm)))

/-- `N = const 0 [] : sort (max 1 0)` — the family typing retyped through
    `sr2_sortsConv`. -/
def sr2_famTyMax : TyP natEnvU 0 [] (.const 0 []) (.sort (.max (.succ .zero) .zero)) :=
  TyP.conv natEnvU 0 [] (.const 0 []) (.sort (.succ .zero))
    (.sort (.max (.succ .zero) .zero)) (.succ (.succ .zero)) (sr2_famTy [])
    sr2_sortsConv

/-- `zero = const 1 [] : N` through the converted family typing — the
    tooth's expansion typing. Its `const` cutoff is
    `.max (.succ .zero) .zero`. -/
def sr2_zeroTyMax : TyP natEnvU 0 [] (.const 1 []) (.const 0 []) :=
  TyP.const natEnvU 0 [] 1 [] [] natZeroMember (.max (.succ .zero) .zero)
    (rfl : natEnvU.members 1 = some natZeroMember) rfl
    (rfl : levelsBounded 0 [] = true) (eqNList_refl []) sr2_famTyMax

/-- The refuting `dl`: the `.lit 0` node over `sr2_zeroTyMax`. -/
def sr2_litTooth : TyP natEnvU 0 [] (.lit 0) (.const 0 []) :=
  TyP.lit natEnvU 0 [] 0 (.const 0 []) sr2_zeroTyMax

/-- The separating level substitution: zeroes `.succ .zero`, fixes every
    other level — in particular `.max (.succ .zero) .zero`. -/
def sr2_σ : Level → Level
  | .succ .zero => .zero
  | l => l

/-! ## §3 erasures -/

/-- At `sr2_σ` the surface's cutoff `.succ .zero` zeroes, so the canonical
    expansion erases to `★`. -/
theorem sr2_surface_eps :
    (litSurface (LiteralExpansion.of 0) sr2_zeroTy).eps sr2_σ [] = .star := rfl

/-- At `sr2_σ` the tooth's cutoff `.max (.succ .zero) .zero` survives
    (`sr2_σ` fixes `max` nodes), so the tooth erases to `const 1 []`. -/
theorem sr2_tooth_eps : sr2_litTooth.eps sr2_σ [] = .const 1 [] := rfl

/-- `tableOfI natEnvUWfT = [natZeroRule, natSuccRule]` has only `3`-headed
    rules, so `const 1` (zero) is a rigid head. -/
theorem noHeadRule_tableOfI_nat_one : NoHeadRule (tableOfI natEnvUWfT) 1 := by
  intro ρ hρ
  rw [tableOfI_nat] at hρ
  simp only [List.mem_cons, List.not_mem_nil, false_or, or_false] at hρ
  rcases hρ with hρ | hρ
  · subst hρ; decide
  · subst hρ; decide

/-! ## §4 the wall, restated and refuted -/

/-- Census row 7's retained wall — the missing lemma `lit_surfaceCL`
    (arbitrary `dl`) — restated as ONE named Prop at the row instantiation
    `tbl := tableOfI natEnvUWfT`, `σ := sr2_σ`, `ρ := []`, `t := 0`,
    `T := .const 0 []`: every `dl : TyP natEnvU 0 [] (.lit 0) (.const 0 [])`
    is CL to the canonical surface. -/
def sr2_lit_surfaceCL_wall : Prop :=
  ∀ dl : TyP natEnvU 0 [] (.lit 0) (.const 0 []),
    CL (tableOfI natEnvUWfT) sr2_σ [] dl
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy)

theorem sr2_not_cl_litTooth :
    ¬ CL (tableOfI natEnvUWfT) sr2_σ [] sr2_litTooth
      (litSurface (LiteralExpansion.of 0) sr2_zeroTy) := by
  intro h
  unfold CL at h
  rw [sr2_tooth_eps, sr2_surface_eps] at h
  exact not_convMod_star_const (tableWF_tableOfI_full natEnvUWfT)
    noHeadRule_tableOfI_nat_one (ConvMod.symm' LvlEq.symm' h)

/-- **Row 7 refuted**: the `lit.surfaceCL` wall is not provable — at the
    inhabited fixture it FAILS at `dl := sr2_litTooth`. -/
theorem sr2_lit_surfaceCL_refuted : ¬ sr2_lit_surfaceCL_wall :=
  fun h => sr2_not_cl_litTooth (h sr2_litTooth)

/-- Non-vacuity: every OTHER premise of the row's closer `es_lit_closed`
    is inhabited at this fixture — `hlit := LiteralExpansion.of 0`,
    `hexp := dr := sr2_zeroTy` — and the `dl` side is inhabited (by the
    refuting tooth itself). Only the wall `hL` fails. -/
theorem sr2_lit_row_premises_nonvacuous :
    Nonempty ((LiteralExpansion 0 (natExpand 0)) ×
      (TyP natEnvU 0 [] (natExpand 0) (.const 0 [])) ×
        (TyP natEnvU 0 [] (.lit 0) (.const 0 []))) :=
  ⟨(LiteralExpansion.of 0, sr2_zeroTy, sr2_litTooth)⟩

#print axioms Rcic.Syn.sr2_eqN_max_zero
#print axioms Rcic.Syn.sr2_eqN_succ
#print axioms Rcic.Syn.not_convMod_star_const
#print axioms Rcic.Syn.sr2_famTy
#print axioms Rcic.Syn.sr2_zeroTy
#print axioms Rcic.Syn.sr2_sortsConv
#print axioms Rcic.Syn.sr2_famTyMax
#print axioms Rcic.Syn.sr2_zeroTyMax
#print axioms Rcic.Syn.sr2_litTooth
#print axioms Rcic.Syn.sr2_σ
#print axioms Rcic.Syn.sr2_surface_eps
#print axioms Rcic.Syn.sr2_tooth_eps
#print axioms Rcic.Syn.noHeadRule_tableOfI_nat_one
#print axioms Rcic.Syn.sr2_not_cl_litTooth
#print axioms Rcic.Syn.sr2_lit_surfaceCL_refuted
#print axioms Rcic.Syn.sr2_lit_row_premises_nonvacuous
