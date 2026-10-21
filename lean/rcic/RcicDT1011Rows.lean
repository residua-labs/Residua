import rcic.RcicStepsSREnvWf
import rcic.RcicDT008Equiv
import rcic.RcicAnnIotaSR
import rcic.RcicAnnSemPrefixRows
import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedGroupPinsList

namespace Rcic.Declarative

/-!
# DT-010 / DT-011 modulo the rows

cc ruling (#6293, 05:15Z): theorems conditional on `TypedRowsWf` are recorded
as "decided modulo the rows conjecture". The sealed fronts are
`DT010T_one_step_subject_reduction` / `DT011T_multi_step_subject_reduction`
(`RcicDTMetaTypedSR.lean`), both taking `hP : hW.InScope`. This module states
and proves them with `hrows : TypedRowsWf E n` (plus `hiota : IotaSRTΓ E n`,
the named ι front) **instead of** `InScope`.

Where `InScope` went inside `oneStepSRT`, per arm:

| `oneStepSRT` consumer | `InScope` use | this module |
|---|---|---|
| `.beta` | `typedRowsWf_of_envWfT_semPrefix` → `piRow`; `Ann.convT_of_tyConvT_sort` | `hrows.piRow`; `convT_of_tyConvT_sort_rows` |
| `.zeta` | `DT009T_endpoints_inScope` | `step_zeta_srT` (EnvWfT — `hasTyT_substLet0_of_envWfT`) |
| `.zetaLocal` | none (context walk) | `step_zetaLocal_srT` (EnvWfT) |
| `.delta` | none (`envWfT_bodyTyped`) | `step_delta_srT` (EnvWfT) |
| `.iota` | `hasTyT_iota_sr` (Ann bridge) | `hiota : IotaSRTN` — named front, DT-019's own row |
| `.lit` | none | `step_lit_srT` (no env premise) |

The β arm's collapse `TyConvT A B → ConvT A B (sort u)` is
`convT_of_tyConvT_sort` (`RcicTyConvTSort.lean:69`) with its two leaves paid
at `EnvWfT` + rows: `hEnd` = `DT009T_endpoints_envWfT`'s left half (#6425,
unconditional) and `hUniq` = `DT012T_type_uniqueness_of_typedRowsWf`
(`RcicDT008Equiv.lean:192`, the rows-conditional uniqueness). The collapse
needs a `Nonempty`-valued `hUniq` variant — `piRow`'s existence form cannot
eliminate into `Type`, so `convT_of_tyConvT_sort`'s raw-`TyConvT` front is
unfeedable; `convT_of_tyConvT_sortN` is the same induction at `Nonempty`.

`IotaSRTN` is the ι premise (not bare `IotaSRT`): the dispatcher's own
output is `Nonempty`-wrapped, so the front only ever needs `Nonempty`-strength
data — and `Nonempty` is exactly what the one extant producer delivers
(`iotaPreserveT`/`hasTyT_iota_sr` under `InScope`; the Ann erasure cannot
project to `Type`, so raw `IotaSRT` is unfeedable by it). `IotaSRT` and
`IotaSRTΓ` both promote into `IotaSRTN` below; the `CorrCertsBelow`-gated
sibling (`iotaPreserveTT`, the corr union) feeds it the same way.
`closure_claim = 0`.
-/

/-- `convT_of_tyConvT_sort` with `hUniq` at `Nonempty` — the shape
    `DT012T_type_uniqueness_of_typedRowsWf` actually returns. Same chain
    walk: `.of` retypes through uniqueness-of-sort, `.trans` seeds the
    middle endpoint off the left segment. -/
def convT_of_tyConvT_sortN {E : ResolvedEnv} {n : Nat}
    (hEnd : ∀ {Γ' : LCtx} {a b : Expr Nat} {v : Level},
      CtxWfT E n Γ' → ConvT E n Γ' a b (.sort v) →
      Nonempty (HasTyT E n Γ' a (.sort v)))
    (hUniq : ∀ {Γ' : LCtx} {a A B : Expr Nat}, CtxWfT E n Γ' →
      HasTyT E n Γ' a A → HasTyT E n Γ' a B →
      Nonempty (TyConvT E n Γ' A B))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ a (.sort u)) (h : TyConvT E n Γ a b) :
    Nonempty (ConvT E n Γ a b (.sort u)) := by
  induction h with
  | refl => exact ⟨.refl _ _ _ hA⟩
  | of _ _ v h =>
      obtain ⟨hav⟩ := hEnd hΓ h
      obtain ⟨hU⟩ := hUniq hΓ hA hav
      exact ⟨convT_of_tyConv h hU.symmT⟩
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨c1⟩ := ih1 hA
      obtain ⟨hmid⟩ := hEnd hΓ c1.symm
      obtain ⟨c2⟩ := ih2 hmid
      exact ⟨.trans _ _ _ _ _ c1 c2⟩

/-- the collapse, paid at `EnvWfT` + `TypedRowsWf`: `hEnd` from DT-009's left
    endpoint (unconditional since #6425), `hUniq` from DT-012 modulo rows. -/
def convT_of_tyConvT_sort_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ a (.sort u)) (h : TyConvT E n Γ a b) :
    Nonempty (ConvT E n Γ a b (.sort u)) :=
  convT_of_tyConvT_sortN
    (fun {_ _ _ _} hΓ' hc => (DT009T_endpoints_envWfT hW hΓ' hc).1)
    (fun {_ _ _ _} hΓ' h1 h2 =>
      DT012T_type_uniqueness_of_typedRowsWf hW hrows hΓ' h1 h2)
    hΓ hA h

/-- β under rows — `step_beta_srT`'s twin with `hrows.piRow` in place of
    `PiRowInjT`: the domain leg collapses at the lam-domain's own sort
    (`hA0ty`), the codomain leg at the sort `DT007T` reads off the body.
    `PiRowInjT` itself cannot be produced from `piRow` — its `Σ'`-level
    output has no sort-typing seed on a `TyConvT.refl` chain — so this arm
    is restated at the row, not the front. -/
def step_beta_srT_rows (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A0 body arg S : Expr Nat}
    (h : HasTyT E n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ (instantiate0 arg body) B ×'
      TyConvT E n Γ S B) := by
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u0, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
  obtain ⟨w, ⟨hBw⟩⟩ := DT007T_typing_regularity_of_envWfT hW
    (.assumption Γ A0 u0 hΓ hA0ty) hbody
  obtain ⟨cdom⟩ := convT_of_tyConvT_sort_rows hW hrows hΓ hA0ty hBdom
  obtain ⟨ccod⟩ := convT_of_tyConvT_sort_rows hW hrows
    (.assumption Γ A0 u0 hΓ hA0ty) hBw hBcod
  have ha' : HasTyT E n Γ arg A0 :=
    HasTyT.conv _ _ _ _ u0 ha (ConvT.symm _ _ _ _ cdom)
  have hsub := hasTyT_subst0_of_envWfT hW hbody ha'
  have hcod' : ConvT E n Γ (instantiate0 arg B_lam) (instantiate0 arg B1)
      (.sort w) :=
    convT_subst0_of_envWfT hW ccod ha'
  exact ⟨_, hsub,
    .trans _ _ _ _ (TyConvT.symmT hcv) (TyConvT.symmT (.of _ _ _ _ hcod'))⟩

/-- the `Nonempty`-strength ι front — `IotaSRT`'s shape with the output at
    `Nonempty` (the form `iotaPreserveT` delivers and `IotaSRT` promotes to).
    `Prop`-sorted: `Nonempty` is the erasure the Ann route can produce. -/
def IotaSRTN (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {lhs rhs S : Expr Nat}, DerivedIota E lhs rhs →
    HasTyT E n Γ lhs S →
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ rhs B ×' TyConvT E n Γ S B)

/-- the canonical sealed front promotes: `IotaSRT`'s `Σ'` output packs into
    `Nonempty` for free. -/
def iotaSRTN_of_iotaSRT {E : ResolvedEnv} {n : Nat} (h : IotaSRT E n) :
    IotaSRTN E n :=
  fun {_} _ {_ _ _} hd hl => ⟨h hd hl⟩

/-- the Γ-fronted variant promotes the same way. -/
def iotaSRTN_of_iotaSRTΓ {E : ResolvedEnv} {n : Nat} (h : IotaSRTΓ E n) :
    IotaSRTN E n :=
  fun {_} hΓ {_ _ _} hd hl => ⟨h hΓ hd hl⟩

/-- the `InScope` producer: `iotaPreserveT` keeps the reduct at the source's
    own type (`TyConvT.refl` for the conversion leg). -/
def iotaSRTN_of_inScope {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} : IotaSRTN E n :=
  fun {_} hΓ {_ _ S} hd h =>
    Nonempty.elim (iotaPreserveT hW hP hΓ hd h) fun h' => ⟨S, h', .refl _ _⟩

/-- DT-010 modulo the rows: `step_srT`'s dispatch with the β arm at
    `hrows.piRow`. Premises: `TypedRowsWf` (the rows conjecture) and
    `IotaSRTN` (DT-019's named ι front). No `InScope` anywhere. -/
def step_srT_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) (hiota : IotaSRTN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) :=
  match hs with
  | .beta _ _ _ _ => step_beta_srT_rows hW hrows hΓ h
  | .zeta _ _ _ _ =>
      step_zeta_srT (fun hv hb => hasTyT_substLet0_of_envWfT hW hb hv) h
  | .zetaLocal _ i v hlv => step_zetaLocal_srT hW hΓ hlv h
  | .delta _ _ _ _ _ hres hbody _ => step_delta_srT hW hres hbody h
  | .iota _ _ _ hd => hiota hΓ hd h
  | .lit _ _ _ hlexp => step_lit_srT hlexp h

/-- DT-011 modulo the rows: `Steps` induction through `step_srT_rows`,
    chained by `TyConvT.trans`. -/
def steps_srT_rows {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (hrows : TypedRowsWf E n) (hiota : IotaSRTN E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) := by
  induction hs generalizing S with
  | refl _ => exact ⟨S, h, TyConvT.refl _ _⟩
  | step a b c h1 h2 ih =>
      obtain ⟨B1, hb1, hc1⟩ := step_srT_rows hW hrows hiota hΓ h h1
      obtain ⟨B2, hb2, hc2⟩ := ih hb1
      exact ⟨B2, hb2, .trans _ _ _ _ hc1 hc2⟩

/-- DT-010, census-facing modulo the rows conjecture: one-step subject
    reduction on the typed judgment, `TypedRowsWf` + `IotaSRTN` premises in
    place of `hW.InScope`. The reduct is typed at a type convertible with
    the source's. -/
theorem DT010T_one_step_subject_reduction_of_typedRowsWf {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    (hiota : IotaSRTN E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  (step_srT_rows hW hrows hiota hΓ h hs).elim fun ⟨B, h1, h2⟩ =>
    ⟨B, ⟨h1⟩, ⟨h2⟩⟩

/-- DT-011, census-facing modulo the rows conjecture: the multi-step chain,
    same premises. -/
theorem DT011T_multi_step_subject_reduction_of_typedRowsWf {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    (hiota : IotaSRTN E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) := by
  induction hs generalizing S with
  | refl _ => exact ⟨S, ⟨h⟩, ⟨TyConvT.refl _ _⟩⟩
  | step a b c h1 h2 ih =>
      obtain ⟨B1, hb1, hc1⟩ := step_srT_rows hW hrows hiota hΓ h h1
      obtain ⟨B2, hb2, hc2⟩ := ih hb1
      exact ⟨B2, hb2, hc2.elim fun hc2' =>
        ⟨TyConvT.trans _ _ _ _ hc1 hc2'⟩⟩

/-! ## non-vacuity

The conditional-theorem discipline wants a non-refutability witness for each
premise. `TypedRowsWf`'s producer on main is
`Ann.typedRowsWf_of_envWfT_semPrefix` at `hW.InScope`; `IotaSRTN`'s producer is
`iotaSRTN_of_inScope` above (`iotaPreserveT` at the same scope). The pins below
run DT-010/011 at `listEnvUT`'s real β-redex with both premises supplied — the
premises are inhabitable where the conjecture holds, so the conditional
statement is not vacuous. (The fronts stay independent of `InScope`: the
semantic model is expected to produce `TypedRowsWf`/`IotaSRT` directly.) -/

/-- PIN (non-vacuity tooth): DT-010 modulo the rows consumed at `listEnvUT`'s
    real β-redex — `TypedRowsWf` and `IotaSRTN` both supplied through the
    `InScope` lane (their inhabitability where the conjecture holds). -/
theorem pin_DT010T_rows_beta {n : Nat} :
    ∃ B, Nonempty (HasTyT listEnvUT n []
        (instantiate0 (.sort .zero) (.bvar 0)) B) ∧
      Nonempty (TyConvT listEnvUT n [] (.sort (.succ .zero)) B) :=
  DT010T_one_step_subject_reduction_of_typedRowsWf listEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix listEnvUWfT listEnvUWfT_inScope n)
    (iotaSRTN_of_inScope listEnvUWfT listEnvUWfT_inScope)
    CtxWfT.nil (pinBetaApp listEnvUT n)
    (Step.beta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero))

/-- PIN (multi-step): the same redex through the `Steps.step` chain —
    DT-011's inductive arm, modulo the rows. -/
theorem pin_DT011T_rows_beta {n : Nat} :
    ∃ B, Nonempty (HasTyT listEnvUT n [] (.sort .zero) B) ∧
      Nonempty (TyConvT listEnvUT n [] (.sort (.succ .zero)) B) :=
  DT011T_multi_step_subject_reduction_of_typedRowsWf listEnvUWfT
    (Ann.typedRowsWf_of_envWfT_semPrefix listEnvUWfT listEnvUWfT_inScope n)
    (iotaSRTN_of_inScope listEnvUWfT listEnvUWfT_inScope)
    CtxWfT.nil (pinBetaApp listEnvUT n)
    (Steps.step _ _ _ _
      (Step.beta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero))
      (Steps.refl [] (instantiate0 (.sort .zero) (.bvar 0))))

#print axioms Rcic.Declarative.convT_of_tyConvT_sortN
#print axioms Rcic.Declarative.convT_of_tyConvT_sort_rows
#print axioms Rcic.Declarative.step_beta_srT_rows
#print axioms Rcic.Declarative.step_srT_rows
#print axioms Rcic.Declarative.steps_srT_rows
#print axioms Rcic.Declarative.DT010T_one_step_subject_reduction_of_typedRowsWf
#print axioms Rcic.Declarative.DT011T_multi_step_subject_reduction_of_typedRowsWf
#print axioms Rcic.Declarative.IotaSRTN
#print axioms Rcic.Declarative.iotaSRTN_of_iotaSRT
#print axioms Rcic.Declarative.iotaSRTN_of_iotaSRTΓ
#print axioms Rcic.Declarative.iotaSRTN_of_inScope
#print axioms Rcic.Declarative.pin_DT010T_rows_beta
#print axioms Rcic.Declarative.pin_DT011T_rows_beta

end Rcic.Declarative
