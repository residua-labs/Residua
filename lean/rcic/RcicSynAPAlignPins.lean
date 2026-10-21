import rcic.RcicSynAPAlign

/-!
# AP-alignment pins — W-COV-AP-SORT-EXPOSURE + controls (ChatGPT S2, #7311)

Spec §5's `Σ/Δ/Γ` instance, pinned executable:

- `Σ = [x : Y, Y : s₁]` = `[.assumption (.bvar 0), .assumption s₁]`,
- `Δ = [P : s₀]` = `[.assumption s₀]`,
- `Γ = [z : P, P : s₀]` = `[.assumption (.bvar 0), .assumption s₀]`.

The `esub` at `j = 1` removes `Y` from `Σ`, substituting `s₀` for it: its source
child `DX : Σ ⊢ bvar 0 : bvar 1` has the **non-sort** type `bvar 1`, while the
output `Q : Δ ⊢ bvar 0 : s₀` IS sort-typed — the shape
"esub sort output ⇒ sort-typed source child" is false (W-COV-AP-SORT-EXPOSURE).
`hA = wk Q : Γ ⊢ bvar 1 : s₀` is AP (`AssumptionPrefix Σ 1` holds; `wk` at `c = 0`
is vacuous). `C_Γ`'s entry-0 provider IS `Q` itself (`u₀ = 0`), distinct from
`hA` — the provider is bound to `C`'s stored field, never `hA = P`.

Controls: the old heavy-entry refusal `not_combLexDM_pbit_bvar` stays; the
correct pre-paid edge at introduction passes via `intro_align_pair_below`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §5 fixture derivations and spines -/

abbrev apExpS0 : Expr Nat := .sort .zero
abbrev apExpS1 : Expr Nat := .sort (.succ .zero)
abbrev apExpS2 : Expr Nat := .sort (.succ (.succ .zero))

/-- `Σ = [x : Y, Y : s₁]` (newest first). -/
abbrev apExpSigma : LCtx := [.assumption (.bvar 0), .assumption apExpS1]
/-- `Δ = [P : s₀]`. -/
abbrev apExpDelta : LCtx := [.assumption apExpS0]
/-- `Γ = [z : P, P : s₀]`. -/
abbrev apExpGamma : LCtx := [.assumption (.bvar 0), .assumption apExpS0]

/-- `DY : Σ ⊢ bvar 1 : s₁` (the `Y` entry). -/
def apExpDY : TyP emptyEnv 0 apExpSigma (.bvar 1) apExpS1 :=
  TyP.bvar emptyEnv 0 apExpSigma 1 apExpS1 (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 apExpSigma (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `DX : Σ ⊢ bvar 0 : bvar 1` — the `esub` source child; `bvar 1` is NOT a sort. -/
def apExpDX : TyP emptyEnv 0 apExpSigma (.bvar 0) (.bvar 1) :=
  TyP.bvar emptyEnv 0 apExpSigma 0 (.bvar 1) (.succ .zero) rfl apExpDY

/-- `Q : Δ ⊢ bvar 0 : s₀` — the `esub` output; `s₀` IS a sort. -/
def apExpQ : TyP emptyEnv 0 apExpDelta (.bvar 0) apExpS0 :=
  TyP.esub emptyEnv 0 apExpSigma (.bvar 0) (.bvar 1) apExpS1 apExpS0 1
    (.succ (.succ .zero)) apExpDX rfl
    (TyP.sort emptyEnv 0 apExpDelta .zero (.succ .zero) (eqN_refl _))
    (TyP.sort emptyEnv 0 apExpDelta (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `hA : Γ ⊢ bvar 1 : s₀` — the sort-typing the public `z : P` bvar carries. -/
def apExpHA : TyP emptyEnv 0 apExpGamma (.bvar 1) apExpS0 :=
  TyP.wk emptyEnv 0 apExpDelta (.bvar 0) apExpS0 (.assumption (.bvar 0)) 0 apExpQ

/-- The public lookup `lookupType Γ 0 = some (bvar 1)` — `z`'s type is `P`. -/
def apExpLookupZ : lookupType apExpGamma 0 = some (.bvar 1) := rfl

/-- `z : P` — `Γ ⊢ bvar 0 : bvar 1`, carrying `hA` at `u = 0`. -/
def apExpDvar : TyP emptyEnv 0 apExpGamma (.bvar 0) (.bvar 1) :=
  TyP.bvar emptyEnv 0 apExpGamma 0 (.bvar 1) .zero apExpLookupZ apExpHA

/-- `C_Δ`. -/
def apExpDeltaC : CtxP emptyEnv 0 apExpDelta :=
  CtxP.assumption emptyEnv 0 [] apExpS0 (.succ .zero) (CtxP.nil emptyEnv 0)
    (TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _))

/-- `C_Σ`: the provider at index 0 types x's stored domain `bvar 0` at `sort 1`. -/
def apExpSigmaC : CtxP emptyEnv 0 apExpSigma :=
  CtxP.assumption emptyEnv 0 [.assumption apExpS1] (.bvar 0) (.succ .zero)
    (CtxP.assumption emptyEnv 0 [] apExpS1 (.succ (.succ .zero)) (CtxP.nil emptyEnv 0)
      (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar emptyEnv 0 [.assumption apExpS1] 0 apExpS1 (.succ (.succ .zero)) rfl
      (TyP.sort emptyEnv 0 [.assumption apExpS1] (.succ .zero) (.succ (.succ .zero))
        (eqN_refl _)))

/-- `C_Γ`: the provider at index 0 is `Q` itself (stored domain `bvar 0` typed at
    `sort 0` by the `esub` output — the provider is the ORIGINAL `Q`, while the
    carried `hA` is `wk Q`; they are distinct derivations of one bit). -/
def apExpGammaC : CtxP emptyEnv 0 apExpGamma :=
  CtxP.assumption emptyEnv 0 apExpDelta (.bvar 0) .zero apExpDeltaC apExpQ

/-- `Σ` is natively well-formed. -/
def apExpSigmaWf : CtxWfT emptyEnv 0 apExpSigma :=
  .assumption [.assumption apExpS1] (.bvar 0) (.succ .zero)
    (.assumption [] apExpS1 (.succ (.succ .zero)) .nil (.sort [] (.succ .zero)))
    (.bvar [.assumption apExpS1] 0 apExpS1 rfl)

/-- `Δ` is natively well-formed. -/
def apExpDeltaWf : CtxWfT emptyEnv 0 apExpDelta :=
  .assumption [] apExpS0 (.succ .zero) .nil (.sort [] .zero)

/-- `Γ` is natively well-formed. -/
def apExpGammaWf : CtxWfT emptyEnv 0 apExpGamma :=
  .assumption apExpDelta (.bvar 0) .zero apExpDeltaWf (.bvar apExpDelta 0 apExpS0 rfl)

/-! ## §5 pins -/

/-- (a) The source child's ascribed type `bvar 1` is not a sort: no `v` makes it
    `.sort v`. Refutes the shape "esub sort output ⇒ sort-typed source child". -/
theorem wCovApSortExposure_source_not_sort :
    ∀ v : Level, (Expr.bvar 1 : Expr Nat) ≠ .sort v := by
  intro v h; injection h

/-- (b) The `esub` output type IS a sort: `instantiate 1 (lift 0 1 s₀) (bvar 1)`
    computes to `s₀ = .sort 0`. -/
theorem wCovApSortExposure_output_is_sort :
    instantiate 1 (lift 0 1 apExpS0) (.bvar 1) = .sort .zero := rfl

/-- (c) The context is an assumption-prefix at the cutoffs: `AssumptionPrefix`
    holds at `j = 1` in `Σ`, so `hA.AssumpPref` holds. -/
theorem assumptionPrefix_apExpSigma_one : AssumptionPrefix apExpSigma 1 := by
  intro d hd
  refine ⟨.bvar 0, ?_⟩
  simpa [apExpSigma] using hd

/-- `hA` is a real AP derivation (wk at `c = 0` is vacuous; the `esub` at
    `j = 1` sits on an assumption-only prefix). -/
theorem wCovApSortExposure_hA_ap : apExpHA.AssumpPref := by
  simp only [apExpHA, apExpQ, apExpDX, apExpDY, TyP.AssumpPref]
  exact ⟨assumptionPrefix_zero _, assumptionPrefix_apExpSigma_one, trivial, trivial,
    trivial⟩

/-- (d) `C_Γ`'s entry sort at index 0 is `.zero` — and `lookupProvider_entrySort`
    reads the same field through `ctxP_lookupType_sort`. -/
theorem wCovApSortExposure_entrySort : apExpGammaC.entrySort 0 = some .zero := rfl

/-- The provider's sort level at `Γ`'s index 0 is `.zero`. -/
theorem wCovApSortExposure_provider :
    (ctxP_lookupType_sort apExpGammaC apExpLookupZ).1 = .zero := rfl

/-- (e) The final bit is correct: `levelIsZero (σ uEntry) = levelIsZero (σ u)`
    for `uEntry = u = .zero`. -/
theorem wCovApSortExposure_bit :
    ∀ σ : Level → Level,
      levelIsZero (σ (ctxP_lookupType_sort apExpGammaC apExpLookupZ).1) =
        levelIsZero (σ .zero) :=
  fun _ => rfl

/-- The bvar-erasure consequence: `PBit` on the original `z : P`/`hA` along
    `C_Γ.disp id`, discharged by `pbit_bvar_reg_of_lookupProvider`. -/
theorem wCovApSortExposure_pbit :
    PBit id (apExpGammaC.disp id) apExpDvar apExpHA :=
  pbit_bvar_reg_of_lookupProvider apExpLookupZ apExpHA
    (dispForC_ctxP_id apExpGammaC) trivial rfl

/-! ## Controls -/

/-- The old heavy-entry refusal stays: same-rank `(P, hA)` `BitCoh` on the
    `pbitWall` P-bit bvar still increases `combMeas` (`[6,2,1]` → `[6,6,1]`). -/
theorem apAlign_heavyEntry_still_refused (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    ¬ LexDM
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n)))
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitVar E n) (pbitSort E n))) :=
  not_combLexDM_pbit_bvar Aw E n

/-- The `PairLexDM` refusal of the same edge stays too. -/
theorem apAlign_heavyEntry_still_refused_pair (Aw : Nat → Nat) (E : ResolvedEnv)
    (n : Nat) :
    ¬ PairLexDM
      (ctxMeas Aw (pbitWallCtxP E n),
        tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n))
      (ctxMeas Aw (pbitWallCtxP E n),
        tyPairMeas Aw (pbitVar E n) (pbitSort E n)) :=
  not_pairLexDM_pbit_bvar Aw E n

/-! ## The correct pre-paid edge at introduction passes -/

/-- Domain typing `[] ⊢ s₀ : s₁` for the intro fixture. -/
def apIntroDom : TyP emptyEnv 0 [] apExpS0 (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)

/-- Body `[x : s₀] ⊢ bvar 0 : s₀` for the intro fixture. -/
def apIntroBody : TyP emptyEnv 0 [.assumption apExpS0] (.bvar 0) apExpS0 :=
  TyP.bvar emptyEnv 0 [.assumption apExpS0] 0 apExpS0 (.succ .zero) rfl
    (TyP.sort emptyEnv 0 [.assumption apExpS0] .zero (.succ .zero) (eqN_refl _))

/-- `N = lam s₀ (bvar 0) : pi s₀ s₀`, `wt = 5`. -/
def apIntroN : TyP emptyEnv 0 [] (.lam apExpS0 (.bvar 0)) (.pi apExpS0 apExpS0) :=
  TyP.lam emptyEnv 0 [] apExpS0 (.succ .zero) (.bvar 0) apExpS0 (.succ .zero)
    apIntroDom apIntroBody
    (TyP.sort emptyEnv 0 [.assumption apExpS0] .zero (.succ .zero) (eqN_refl _))

/-- The body's `hA` — a sort-typing of `lift 0 1 s₀ = s₀` in the introduced
    context, `wt = 1 < 5`. -/
def apIntroHA : TyP emptyEnv 0 [.assumption apExpS0] (lift 0 1 apExpS0)
    (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 [.assumption apExpS0] .zero (.succ .zero) (eqN_refl _)

/-- The introduced context's spine `.assumption [] hI` over `CtxP.nil`. -/
def apIntroCI : CtxP emptyEnv 0 [.assumption apExpS0] :=
  CtxP.assumption emptyEnv 0 [] apExpS0 (.succ .zero) (CtxP.nil emptyEnv 0) apIntroDom

/-- The correct pre-paid edge at introduction actually descends on `combMeas`
    (positive control next to the refusal pins). -/
theorem apIntroPair_passes (Aw : Nat → Nat) :
    LexDM
      (combMeas Aw apIntroCI
        (tyPairMeas Aw (wkAtZero (A := apExpS0) apIntroDom) apIntroHA))
      (combMeas Aw (CtxP.nil emptyEnv 0)
        (tyPairMeas Aw apIntroN
          (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))) :=
  intro_align_pair_below Aw (CtxP.nil emptyEnv 0) apIntroDom apIntroBody
    (TyP.sort emptyEnv 0 [.assumption apExpS0] .zero (.succ .zero) (eqN_refl _))
    (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    apIntroHA
    (by simp only [apIntroN, apIntroHA, apIntroDom, apIntroBody, TyP.wt]; omega)

end Rcic.Syn

#print axioms Rcic.Syn.wCovApSortExposure_source_not_sort
#print axioms Rcic.Syn.wCovApSortExposure_output_is_sort
#print axioms Rcic.Syn.assumptionPrefix_apExpSigma_one
#print axioms Rcic.Syn.wCovApSortExposure_hA_ap
#print axioms Rcic.Syn.wCovApSortExposure_entrySort
#print axioms Rcic.Syn.wCovApSortExposure_provider
#print axioms Rcic.Syn.wCovApSortExposure_bit
#print axioms Rcic.Syn.wCovApSortExposure_pbit
#print axioms Rcic.Syn.apAlign_heavyEntry_still_refused
#print axioms Rcic.Syn.apAlign_heavyEntry_still_refused_pair
#print axioms Rcic.Syn.apIntroPair_passes
