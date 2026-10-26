import rcic.RcicFamAppLiftBack
import rcic.RcicClassCRevealedRows
import rcic.RcicAnnLRRows
import rcic.RcicAnnRecSem
import rcic.RcicAnnTypedRows
import rcic.RcicAnnIotaSR
import rcic.RcicAnnViewTySem

/-!
# fable-famapp — sort/Π disjointness over every scoped environment, hence at `RI`; the second route

cc-classc's `typedRowsWf_ri_of_rows12` (RcicClassCRevealedRows) gives `TypedRowsWf riEnv n` from the
sort row, the Π row and `SortPiDisj riEnv n` (no chain `Sort l ≡* Π A B`), by `RI`'s own recursor
reading the field off the constructor. `SortPiDisj` is not a consequence of the three rows (their
premises are same-shape conversions), but it is a consequence of the copy's fundamental theorem: no
`EqKA` clause relates a sort to a Π (`eqKA_sort_pi_absurd`). Exported along the landed bridge
(`notSortPiT` ← `sortConvCharT`'s script, `_semPrefix`, `_scopeCheck`), it holds over every
`EnvWfT` environment that passes the scope test (`sortPiDisj_scopeCheck`), and at `riEnv`
unconditionally through the consistent twin's shadow (`riSortPiDisj`: the statement is negative, so
no lift-back is needed). `riTypedRowsWf_of_piRow'` is then the headline of `RcicFamAppLiftBack` by a
second, independent route. closure_claim = 0.
-/

namespace Rcic.Declarative.Ann

section CopySide

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- no `EqKA` clause relates a sort to a Π: each clause's two sides share a weak-head shape. -/
theorem eqKA_sort_pi_absurd {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {l : Level}
    {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    (h : EqKA E I n ρ₀ k LE LT Γ (.sort l) (.pi D u C v)) : False := by
  cases h with
  | sort _ hB _ _ _ =>
      have e := whTyA_det hB (whTyA_self hB) (hStepFnA_sort E I.fn Γ _) (hStepFnA_pi E I.fn Γ D u C v)
      cases e
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_sort E I.fn Γ l)
      cases e
  | fam hA _ hnA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hnA (hStepFnA_sort E I.fn Γ l)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 (hStepFnA_sort E I.fn Γ l)
      subst e
      exact (tripleLikeA_not_sort hN).elim

/-- sort/Π disjointness on the copy, from the fundamental theorem (`sortConvCharA`'s script). -/
theorem notSortPiA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀) {Γ : LCtxA} {l : Level} {D : ExprA} {u : Level} {C : ExprA} {v w : Level}
    (hΓ : CtxWfA E I n Γ) (h : ConvA E I n Γ (.sort l) (.pi D u C v) (.sort w)) : False := by
  obtain ⟨k₀, hk⟩ := fund_tyEq hE hI hIS hEN hNC hR hS hρ hΓ h
  have := hk k₀ (Nat.le_refl _)
  rw [LREqA_eq] at this
  exact eqKA_sort_pi_absurd this

/-- at the concrete ι, under the profile (`sortConvCharA_rec`'s script). -/
theorem notSortPiA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} {l : Level} {D : ExprA} {u : Level} {C : ExprA} {v w : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (h : ConvA E (iotaIfaceA E) n Γ (.sort l) (.pi D u C v) (.sort w)) : False :=
  notSortPiA (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (envWfA_normCtorType hW)
    (envWfA_normClosed hW) (iotaFnA_recHead E) (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ hΓ h

end CopySide

section TypedBridge

variable {E : ResolvedEnvA} {n : Nat}

/-- sort/Π disjointness ON THE TYPED JUDGMENT (`sortConvCharT`'s script: annotate, read the two
    shapes off the erasure, put the conversion at the sort's own sort by type uniqueness). -/
theorem notSortPiT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {l : Level} {A B T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ (.sort l) (.pi A B) T) : False := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, _, ⟨c⟩⟩ := annConvT C hSR hn h hΓA hctx
  obtain rfl := erase_eq_sort ha
  obtain ⟨AA, u, BA, v, rfl, -, -⟩ := erase_eq_pi hb
  obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
    (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA c) (.sort ΓA l)
  obtain ⟨hW⟩ := C.wf
  exact notSortPiA_rec hW posValA_one C.small C.propElim hΓA (convA_of_tyConvA c t)

theorem notSortPiT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {l : Level} {A B T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ (.sort l) (.pi A B) T) : False :=
  notSortPiT C (iotaSRA C) hn hΓ h

end TypedBridge

/-- over `EnvWfT` in the copy's scope, from the semantic prefix (`sortConvCharT_semPrefix`'s script). -/
theorem notSortPiT_semPrefix {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l : Level} {A B T : Expr Nat}
    (h : ConvT E n Γ (.sort l) (.pi A B) T) : False := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact notSortPiT' C hn hΓ h

end Rcic.Declarative.Ann

namespace Rcic.Syn.FamApp

open Rcic.Declarative
open Rcic.Syn
open Rcic.Syn.ClassC

/-- sort/Π disjointness of a conversion, over every `EnvWfT` environment that passes the scope test. -/
theorem notSortPiT_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l : Level} {A B T : Expr Nat}
    (h : ConvT E n Γ (.sort l) (.pi A B) T) : False :=
  Ann.notSortPiT_semPrefix hW (hW.inScope_of_scopeCheck hC) hΓ h

/-- **`SortPiDisj` over every scoped environment**: a type-conversion CHAIN from a sort to a Π is
    one conversion at the sort's sort (sort uniqueness from the two landed rows), refuted above. -/
theorem sortPiDisj_scopeCheck {E : ResolvedEnv} (hW : EnvWfT E) (hC : hW.ScopeCheck) (n : Nat) :
    SortPiDisj E n := by
  intro Γ hΓ l A B h
  have rows := typedRowsWf_of_scopeCheck hW hC n
  have hSU : ∀ {Γ' : LCtx} {T : Expr Nat} {u v : Level}, CtxWfT E n Γ' →
      HasTyT E n Γ' T (.sort u) → HasTyT E n Γ' T (.sort v) → eqN u v := by
    intro Γ' T u v hΓ' hu hv
    obtain ⟨c⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW rows.sortRow rows.piRow hΓ' hu hv
    exact rows.sortRow hΓ' c
  obtain ⟨c⟩ := F8EtaK.convT_of_tyConvT_sort_of_sortUniq hW hSU hΓ (.sort Γ l) h
  exact notSortPiT_scopeCheck hW hC hΓ c

/-- **sort/Π disjointness at `riEnv`, unconditionally**, through the consistent twin's shadow: the
    chain translates into `cEnv` (`trTyConvW`), where the scoped statement refutes it. -/
theorem riSortPiDisj {n : Nat} : SortPiDisj riEnv n := by
  intro Γ hΓ l A B h
  obtain ⟨hΓc⟩ := cTwin.trCtxWfW hΓ
  obtain ⟨c⟩ := cTwin.trTyConvW h hΓc
  exact sortPiDisj_scopeCheck cEnvWfT cEnvWfT_scopeCheck n hΓc c

/-- **the second route to `RcicFamAppLiftBack`'s headline**: cc-classc's internal injectivity of `RI`
    (`typedRowsWf_ri_of_rows12`, which reads the spine with `SortPiDisj`), its `SortPiDisj` premise
    now a theorem. -/
theorem riTypedRowsWf_of_piRow' {n : Nat} (hpi : PiRowField riEnv n) : TypedRowsWf riEnv n :=
  typedRowsWf_ri_of_rows12 (fun {_} hΓ {_ _} h => riSortRow_chain hΓ h) hpi riSortPiDisj

end Rcic.Syn.FamApp

#print axioms Rcic.Declarative.Ann.eqKA_sort_pi_absurd
#print axioms Rcic.Declarative.Ann.notSortPiT_semPrefix
#print axioms Rcic.Syn.FamApp.sortPiDisj_scopeCheck
#print axioms Rcic.Syn.FamApp.riSortPiDisj
#print axioms Rcic.Syn.FamApp.riTypedRowsWf_of_piRow'
