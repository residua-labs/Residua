import rcic.RcicNativeValleyDecoTransfer
import rcic.RcicNativeStepTransferProducer

/-!
# RcicNativePiInjConfluence — `PiInj` from star confluence, without `CDiamond`

The only producers of `PiInj E n` on the tree (`piInj_of_diamond_sortRetype`,
`piInj_of_diamond_sortUniq`) take an ordinary `CDiamond`, and `PiInj` is consumed by
every uniqueness / transfer result (`uniq_of_piInj_sortUniq`, `stepDecoTransferT_proofLeaf`,
…).  This module locates exactly where `CDiamond` enters that route and removes it.

`CDiamond` is used twice in `piInj_of_diamond_sortRetype`: to produce a valley for each
link of the `TyConvT` chain (`valleyOf_diamond`), and to compose the links' valleys at
the chain's middle terms (`CValley.trans`).  Both are instances of ONE operation, star
confluence at a common index (`StepTransferProducerAudit.StarConfluence`), and #7600's
producer `valleyOf_confluence` already runs on it.  Hence:

* `cvalley_of_tyConvT_of_confluence` — a `TyConvT` chain out of a sort-typed `X`
  collapses to one `CValley` at that sort from `StarConfluence` and `SortRetype` (the
  index alignment of the links; supplied by `SortUniq` or `Uniq`);
* `convT_pi_inv_of_confluence`, `piInj_of_confluence_sortRetype`,
  `piInj_of_confluence_sortUniq`, `sortCoh_of_confluence_sortRetype` — the Π- and
  sort-inversion results of `RcicNativeValleyDecoTransfer` with `StarConfluence` in place
  of `CDiamond`; the Π-head invariance of certified stars under `ZeroSortCoherence`
  (`cvalley_pi_inv_of_zsc`) is unchanged.

So the circular edge `PiInj ← CDiamond` becomes `PiInj ← StarConfluence`, and star
confluence is what the coherent machinery targets (`confluenceOf_coherentDiamond`, and
`RcicNativeLeafPeakConfluence.starConfluence_of_leafPeakDiamond` for the leaf-adjusted
diamond).  No route to `PiInj` that avoids star confluence at the chain's middles is
claimed: the middle terms of a `TyConvT` between two Π-types are unrestricted, and the
Π-head invariance only speaks about stars OUT OF a Π-type.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiInjConfluenceAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open StepTransferProducerAudit (StarConfluence valleyOf_confluence valleyTrans_of_confluence)

/-- A `TyConvT` chain out of `X : .sort w` collapses to one `CValley` at `.sort w`: each
    link's valley by `valleyOf_confluence`, reindexed to `.sort w` by `SortRetype`, the
    links composed by `valleyTrans_of_confluence`.  `cvalley_of_tyConvT_of_sortRetype`
    with `StarConfluence` in place of `CDiamond`. -/
def cvalley_of_tyConvT_of_confluence (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (sr : SortRetype E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {X Y : Expr Nat} → {w : Level} → HasTyT E n Γ X (.sort w) →
    TyConvT E n Γ X Y → CValley E n PEq Γ X Y (.sort w)
  | _, _, _, hX, .refl _ _ => CValley.refl hX
  | _, _, _, hX, .of _ _ _ _ hc =>
      let V := valleyOf_confluence hW L F hΓ hc
      let hXu := V.left.leftTyped L hΓ
      V.reindex (sr hΓ hXu hX)
  | _, _, _, hX, .trans _ _ _ _ c₁ c₂ =>
      let V₁ := cvalley_of_tyConvT_of_confluence hW L F sr hΓ hX c₁
      let hM := V₁.right.leftTyped L hΓ
      let V₂ := cvalley_of_tyConvT_of_confluence hW L F sr hΓ hM c₂
      valleyTrans_of_confluence F hΓ V₁ V₂

/-- A single `ConvT` between two sorts gives `eqN` from `StarConfluence` and
    `ZeroSortCoherence`. -/
theorem convT_sort_inv_of_confluence (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u₁ u₂ : Level} {T : Expr Nat}
    (c : ConvT E n Γ (.sort u₁) (.sort u₂) T) : eqN u₁ u₂ :=
  cvalley_sort_inv_of_zsc hW L zsc hΓ (valleyOf_confluence hW L F hΓ c)

/-- A single `ConvT` between two Π-types gives the domain and codomain chains from
    `StarConfluence` and `ZeroSortCoherence`. -/
def convT_pi_inv_of_confluence (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ T : Expr Nat}
    (c : ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ :=
  cvalley_pi_inv_of_zsc hW L zsc hΓ (valleyOf_confluence hW L F hΓ c)

/-- Full `SortCoh` from `StarConfluence`, `SortRetype` and `ZeroSortCoherence`. -/
theorem sortCoh_of_confluence_sortRetype (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : SortCoh E n :=
  fun {Γ} hΓ {u _} c =>
    let V := cvalley_of_tyConvT_of_confluence hW L F sr hΓ (.sort Γ u) c
    cvalley_sort_inv_of_zsc hW L zsc hΓ V

/-- Full `PiInj` from `StarConfluence`, `SortRetype` and `ZeroSortCoherence`: a pure
    reflexivity chain is split by `Expr.pi.inj`; otherwise the first link types `.pi A₁ B₁`
    at a sort, the chain collapses to a `CValley` there, and `cvalley_pi_inv_of_zsc`
    extracts the component chains.  No `CDiamond`. -/
def piInj_of_confluence_sortRetype (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : PiInj E n :=
  fun {Γ} hΓ {A₁ B₁ A₂ B₂} c =>
    match tyConvT_firstOf_data c with
    | .inl heq => by
        injection heq with hA hB
        subst hA; subst hB
        exact (.refl Γ A₁, .refl (.assumption A₁ :: Γ) B₁)
    | .inr ⟨_, u, hc₀, _⟩ =>
        let hPi : HasTyT E n Γ (.pi A₁ B₁) (.sort u) := (convEnds hW hΓ hc₀).1
        let V := cvalley_of_tyConvT_of_confluence hW L F sr hΓ hPi c
        cvalley_pi_inv_of_zsc hW L zsc hΓ V

/-- `PiInj` from `StarConfluence` and `SortUniq`. -/
def piInj_of_confluence_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (su : SortUniq E n) : PiInj E n :=
  piInj_of_confluence_sortRetype hW L F (sortRetype_of_sortUniq su) (zsc_of_sortUniq su)

/-- The route through the coherent diamond, for the record: `CoherentDiamond` gives star
    confluence (#7600), hence `PiInj` with `SortUniq`.  (`CoherentDiamond` is refuted on the
    η/leaf peak modulo `NotProof`; this is conditional algebra.) -/
noncomputable def piInj_of_coherentDiamond_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : DecoStarAudit.CoherentDiamond L) (su : SortUniq E n) : PiInj E n :=
  piInj_of_confluence_sortUniq hW L (StepTransferAudit.confluenceOf_coherentDiamond hW L D) su

/-- `Uniq` (DT-012's shape) from `StarConfluence` and `SortUniq`, through `PiInj`. -/
noncomputable def uniq_of_confluence_sortUniq (hW : EnvWfT E) (L : LeafIface E n PEq)
    (F : StarConfluence E n PEq) (su : SortUniq E n) : Uniq E n :=
  uniq_of_piInj_sortUniq hW (piInj_of_confluence_sortUniq hW L F su) su

#print axioms cvalley_of_tyConvT_of_confluence
#print axioms convT_sort_inv_of_confluence
#print axioms convT_pi_inv_of_confluence
#print axioms sortCoh_of_confluence_sortRetype
#print axioms piInj_of_confluence_sortRetype
#print axioms piInj_of_confluence_sortUniq
#print axioms piInj_of_coherentDiamond_sortUniq
#print axioms uniq_of_confluence_sortUniq

end Rcic.Declarative.NativeValleys.PiInjConfluenceAudit
