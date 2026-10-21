import rcic.RcicSynSRLitPiLit
import rcic.RcicSynClosedEspi

/-!
# RcicSynSRLitPiPi — sortRow row 10 (`es_pi`): `pi_leftSurface_cl` REFUTED

Census row 10 (`TABLEOFI_SUPPLIER_CENSUS.md`): `es_pi_field_of_tableWF`
retains four walls; `tableWFI_build` is discharged by `tableWF_tableOfI_full`
(the merged `devin/swe-tableicompat`), and this module kernel-refutes the
first missing lemma `pi_leftSurface_cl` (arbitrary
`dl : TyP E n Γ (.pi A B) (.sort (imax u v))` is CL to
`piLeftSurface hA hB`) at the `natEnvU` fixture with `A = B = N`:

* the surface `piLeftSurface sr2_piA sr2_piB` stores the family const node
  `sr2_famTy` as the domain typing, whose internal `const` cutoff universe
  is literally `.succ (.succ .zero)`;
* the tooth `sr2_piTooth` is a `TyP.pi` at the SAME indices whose domain
  typing is `sr2_famMaxC` — the SAME family typing through the semantic
  conversion `sort 2 ≡ sort (max 2 0)` (`sr2_eqN_max_zero`), so its cutoff
  is literally `.max (.succ (.succ .zero)) .zero`;
* `σ := sr2_σ2` zeroes `.succ (.succ .zero)` and fixes every other level,
  so the surface's components erase to `★ ★` while the tooth's survive as
  `const 0 []`, i.e. `ETm.pi .star .star` vs `ETm.pi (.const 0 []) (.const 0 [])`;
* both sides are E-normal (`eStep_pi_normal` over `eStep_star_normal` /
  `eStep_const_normal`; `const 0` is rigid in `tableOfI natEnvUWfT` —
  `noHeadRule_tableOfI_nat_zero`), so the Church–Rosser join collapses to
  `≈`, whose `pi` constructor requires componentwise `≈` — `const 0 []`
  is never `≈` to `★`.

Every other premise of `es_pi_field_of_tableWF` at this fixture is
inhabited (`sr2_pi_row_premises_nonvacuous`); the row is REFUTED, not
discharged. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `pi`-headed erasures are E-normal -/

theorem appN_ne_pi (a b : ETm) (xs : List ETm) (f : ETm) (hf : f ≠ ETm.pi a b) :
    ETm.appN f xs ≠ ETm.pi a b := by
  cases xs with
  | nil => exact hf
  | cons x xs =>
      intro h
      exact appN_ne_pi a b xs (.app f x) (by intro h2; cases h2) h

theorem rStep_pi_normal (tbl : List CRule) {a b t : ETm}
    (ha : ∀ x, ¬ EStep tbl a x) (hb : ∀ x, ¬ EStep tbl b x) :
    ¬ RStep tbl (ETm.pi a b) t := by
  intro h
  generalize hs : ETm.pi a b = s at h
  cases h with
  | beta => cases hs
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      exact appN_ne_pi a b xs (.const c ls) (by intro h; cases h) hs.symm
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL _ h' => cases hs; exact ha _ (.inl h')
  | piR _ h' => cases hs; exact hb _ (.inl h')

theorem etaStep_pi_normal {tbl : List CRule} {a b t : ETm}
    (ha : ∀ x, ¬ EStep tbl a x) (hb : ∀ x, ¬ EStep tbl b x) :
    ¬ EtaStep (ETm.pi a b) t := by
  intro h
  generalize hs : ETm.pi a b = s at h
  cases h with
  | eta => cases hs
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL _ h' => cases hs; exact ha _ (.inr h')
  | piR _ h' => cases hs; exact hb _ (.inr h')

theorem eStep_pi_normal (tbl : List CRule) {a b t : ETm}
    (ha : ∀ x, ¬ EStep tbl a x) (hb : ∀ x, ¬ EStep tbl b x) :
    ¬ EStep tbl (ETm.pi a b) t
  | .inl h => rStep_pi_normal tbl ha hb h
  | .inr h => etaStep_pi_normal ha hb h

/-- A rigid `const r ls` has no outgoing `EStep`: the one-step spine
    inversion `eStep_appN_const_inv` would need a `OneStep` out of `[]`. -/
theorem eStep_const_normal (tbl : List CRule) {r : Nat} (hN : NoHeadRule tbl r)
    {ls : List Level} (x : ETm) : ¬ EStep tbl (.const r ls) x := by
  intro h
  have h' : EStep tbl (ETm.appN (.const r ls) []) x := h
  obtain ⟨xs', _, hone⟩ := eStep_appN_const_inv hN h'
  nomatch hone

/-- `¬ (pi (const 0 []) (const 0 [])) ↔*_{E ∪ ≈} (pi ★ ★)` at a well-formed
    table where `const 0` is rigid: both sides are E-normal, so the
    Church–Rosser join collapses to `≈`, whose `pi` constructor requires
    componentwise `≈` — and `const 0 []` is never `≈` to `★`. -/
theorem not_convMod_pi_const_star {tbl : List CRule} (hW : TableWF tbl)
    (hN0 : NoHeadRule tbl 0) :
    ¬ ConvMod (EStep tbl) LvlEq (ETm.pi (.const 0 []) (.const 0 []))
      (.pi .star .star) := by
  intro hc
  obtain ⟨c, d, hc', hq, hd'⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr)
      (confluent_eStep_wf hW) hc
  have e1 : c = ETm.pi (.const 0 []) (.const 0 []) :=
    rstar_of_normal
      (fun x => @eStep_pi_normal tbl _ _ x (eStep_const_normal tbl hN0)
        (eStep_const_normal tbl hN0)) hc'
  have e2 : d = .pi .star .star :=
    rstar_of_normal
      (fun x => @eStep_pi_normal tbl _ _ x (eStep_star_normal tbl)
        (eStep_star_normal tbl)) hd'
  subst e1
  subst e2
  cases hq with
  | pi hf _ => nomatch hf

/-! ## §2 the fixture: one domain typing, two stored cutoffs -/

/-- `sort 1 : sort (max 2 0)` — `TyP.sort 1 2` retyped through the legal
    semantic conversion `sort 2 ≡ sort (max 2 0)`. -/
def sr2_sort2max (Γ : LCtx) : TyP natEnvU 0 Γ (.sort (.succ .zero))
    (.sort (.max (.succ (.succ .zero)) .zero)) :=
  TyP.conv natEnvU 0 Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (.sort (.max (.succ (.succ .zero)) .zero)) (.succ (.succ (.succ .zero)))
    (TyP.sort natEnvU 0 Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (CvP.sorts natEnvU 0 Γ (.succ (.succ .zero))
        (.max (.succ (.succ .zero)) .zero)
      (fun ρ => (sr2_eqN_max_zero (.succ (.succ .zero)) ρ).symm)
      (TyP.sort natEnvU 0 Γ (.succ (.succ .zero))
        (.succ (.succ (.succ .zero))) (eqN_refl _))
      (TyP.sort natEnvU 0 Γ (.max (.succ (.succ .zero)) .zero)
        (.succ (.succ (.succ .zero)))
        (sr2_eqN_succ
          (fun ρ => (sr2_eqN_max_zero (.succ (.succ .zero)) ρ).symm))))

/-- `N = const 0 [] : sort 1` as a `const` node whose internal cutoff
    universe is `.max (.succ (.succ .zero)) .zero` (same type index as
    `sr2_famTy`, different stored cutoff). -/
def sr2_famMaxC (Γ : LCtx) : TyP natEnvU 0 Γ (.const 0 []) (.sort (.succ .zero)) :=
  TyP.const natEnvU 0 Γ 0 [] [] natFamMember (.max (.succ (.succ .zero)) .zero)
    (rfl : natEnvU.members 0 = some natFamMember) rfl
    (rfl : levelsBounded 0 [] = true) (eqNList_refl []) (sr2_sort2max Γ)

/-- The rule's domain conversion `N ≡ N : sort 1` (both sides canonical). -/
def sr2_piA : CvP natEnvU 0 [] (.const 0 []) (.const 0 []) (.sort (.succ .zero)) :=
  CvP.refl natEnvU 0 [] (.const 0 []) (.sort (.succ .zero)) (sr2_famTy [])
    (sr2_famTy []) (sr2_famTy [])

/-- The rule's codomain conversion `N ≡ N : sort 1` under the `N` binder. -/
def sr2_piB : CvP natEnvU 0 [.assumption (.const 0 [])] (.const 0 []) (.const 0 [])
    (.sort (.succ .zero)) :=
  CvP.refl natEnvU 0 [.assumption (.const 0 [])] (.const 0 [])
    (.sort (.succ .zero)) (sr2_famTy _) (sr2_famTy _) (sr2_famTy _)

/-- The refuting `dl`: `Π N, N` at the same indices, but the domain typing
    is `sr2_famMaxC` (cutoff `.max (.succ (.succ .zero)) .zero`). -/
def sr2_piTooth : TyP natEnvU 0 [] (.pi (.const 0 []) (.const 0 []))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  TyP.pi natEnvU 0 [] (.const 0 []) (.succ .zero) (.const 0 []) (.succ .zero)
    (sr2_famMaxC []) (sr2_famMaxC [.assumption (.const 0 [])])

/-- The separating level substitution: zeroes `.succ (.succ .zero)`, fixes
    every other level — in particular `.max (.succ (.succ .zero)) .zero`
    and `.succ .zero`. -/
def sr2_σ2 : Level → Level
  | .succ (.succ .zero) => .zero
  | l => l

/-! ## §3 erasures -/

/-- The surface's domain typing `sr2_famTy` stores the cutoff
    `.succ (.succ .zero)`, which `sr2_σ2` zeroes — both components erase
    to `★`. -/
theorem sr2_piLeftSurface_eps :
    (piLeftSurface sr2_piA sr2_piB).eps sr2_σ2 [] = ETm.pi .star .star := rfl

/-- The tooth's domain typing `sr2_famMaxC` stores the cutoff
    `.max (.succ (.succ .zero)) .zero`, which `sr2_σ2` fixes — both
    components survive as `const 0 []`. -/
theorem sr2_piTooth_eps :
    sr2_piTooth.eps sr2_σ2 [] = ETm.pi (.const 0 []) (.const 0 []) := rfl

/-- `tableOfI natEnvUWfT = [natZeroRule, natSuccRule]` has only `3`-headed
    rules, so `const 0` (the family) is a rigid head. -/
theorem noHeadRule_tableOfI_nat_zero : NoHeadRule (tableOfI natEnvUWfT) 0 := by
  intro ρ hρ
  rw [tableOfI_nat] at hρ
  simp only [List.mem_cons, List.not_mem_nil, false_or, or_false] at hρ
  rcases hρ with hρ | hρ
  · subst hρ; decide
  · subst hρ; decide

/-! ## §4 the wall, restated and refuted -/

/-- Census row 10's first retained wall — the missing lemma
    `pi_leftSurface_cl` (arbitrary `dl`) — restated as ONE named Prop at the
    row instantiation `tbl := tableOfI natEnvUWfT`, `σ := sr2_σ2`,
    `ρ := []`, `A = A' = B = B' = N`: every
    `dl : TyP natEnvU 0 [] (.pi N N) (.sort (imax 1 1))` is CL to the
    canonical left surface. -/
def sr2_pi_leftSurfaceCL_wall : Prop :=
  ∀ dl : TyP natEnvU 0 [] (.pi (.const 0 []) (.const 0 []))
      (.sort (.imax (.succ .zero) (.succ .zero))),
    CL (tableOfI natEnvUWfT) sr2_σ2 [] dl (piLeftSurface sr2_piA sr2_piB)

theorem sr2_not_cl_piTooth :
    ¬ CL (tableOfI natEnvUWfT) sr2_σ2 [] sr2_piTooth
      (piLeftSurface sr2_piA sr2_piB) := by
  intro h
  unfold CL at h
  rw [sr2_piTooth_eps, sr2_piLeftSurface_eps] at h
  exact not_convMod_pi_const_star (tableWF_tableOfI_full natEnvUWfT)
    noHeadRule_tableOfI_nat_zero h

/-- **Row 10 wall 1 (`pi_leftSurface_cl`) refuted**: at the inhabited
    fixture it FAILS at `dl := sr2_piTooth`. -/
theorem sr2_pi_leftSurfaceCL_refuted : ¬ sr2_pi_leftSurfaceCL_wall :=
  fun h => sr2_not_cl_piTooth (h sr2_piTooth)

/-- Non-vacuity: every OTHER premise of the row's closer
    `es_pi_field_of_tableWF` is inhabited at this fixture — `hA := sr2_piA`,
    `hB := sr2_piB`, `dr := piLeftSurface sr2_piA sr2_piB` (a legitimate
    right-side Π typing) — and the `dl` side is inhabited (by the refuting
    tooth itself). Only the walls fail. -/
theorem sr2_pi_row_premises_nonvacuous :
    Nonempty ((CvP natEnvU 0 [] (.const 0 []) (.const 0 []) (.sort (.succ .zero))) ×
      (CvP natEnvU 0 [.assumption (.const 0 [])] (.const 0 []) (.const 0 [])
        (.sort (.succ .zero))) ×
      (TyP natEnvU 0 [] (.pi (.const 0 []) (.const 0 []))
        (.sort (.imax (.succ .zero) (.succ .zero)))) ×
      (TyP natEnvU 0 [] (.pi (.const 0 []) (.const 0 []))
        (.sort (.imax (.succ .zero) (.succ .zero))))) :=
  ⟨(sr2_piA, sr2_piB, sr2_piTooth, piLeftSurface sr2_piA sr2_piB)⟩

#print axioms Rcic.Syn.appN_ne_pi
#print axioms Rcic.Syn.rStep_pi_normal
#print axioms Rcic.Syn.etaStep_pi_normal
#print axioms Rcic.Syn.eStep_pi_normal
#print axioms Rcic.Syn.eStep_const_normal
#print axioms Rcic.Syn.not_convMod_pi_const_star
#print axioms Rcic.Syn.sr2_sort2max
#print axioms Rcic.Syn.sr2_famMaxC
#print axioms Rcic.Syn.sr2_piA
#print axioms Rcic.Syn.sr2_piB
#print axioms Rcic.Syn.sr2_piTooth
#print axioms Rcic.Syn.sr2_σ2
#print axioms Rcic.Syn.sr2_piLeftSurface_eps
#print axioms Rcic.Syn.sr2_piTooth_eps
#print axioms Rcic.Syn.noHeadRule_tableOfI_nat_zero
#print axioms Rcic.Syn.sr2_not_cl_piTooth
#print axioms Rcic.Syn.sr2_pi_leftSurfaceCL_refuted
#print axioms Rcic.Syn.sr2_pi_row_premises_nonvacuous
