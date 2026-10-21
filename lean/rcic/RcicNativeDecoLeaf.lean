import rcic.RcicNativeValleyEtaLeaf
import rcic.RcicNativeValleyDeco
import rcic.RcicNativeDecoStrip

/-!
# The eta/proof-leaf peak's source decoration and conditional obstruction

The original `b ⇒ d` and `b ⇒ f` steps share the decoration extracted
from their actual source typings, for every `LeafIface`. The opaque typing
returned by the leaf interface is a typing of a variable, whose decoration
is forced even through conversion layers.

The source-equality calculation needs no diamond, type-uniqueness, Pi-row,
zero-sort-coherence, or `NotProof` hypothesis. The conditional obstruction
still takes the three `NotProof` premises of the landed `etaLeaf_no_join`;
this module does not supply an admitted-environment countermodel to diamond.

The explicit two-step fixture repair is supplied by concurrent PR #7588,
`RcicNativeValleyDecoRows.etaLeaf_valleyJoin`, and is not duplicated here.

Dependency pin: `0849f7ec4117`.
`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.DecoLeafAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

private theorem decoOf_bvar {Γ : LCtx} {i : Nat} :
    {T : Expr Nat} → (h : HasTyT E n Γ (.bvar i) T) → decoOf h = .bvar i
  | _, .bvar _ _ _ _ => rfl
  | _, .conv _ _ _ _ _ h _ => decoOf_bvar h

/-- The source decorations of the actual landed lambda and eta steps are
equal.  This also states equality of `CStep.leftTyped` decorations, since
that projection is definitionally `parRedT_hasTy_left`.  No restriction on
the typings supplied by `L.typed` is needed. -/
theorem peak_source_deco_eq (L : LeafIface E n PEq) :
    decoOf (parRedT_hasTy_left L.typed etaLeafCtx_wf (etaLeafLamStep L)) =
      decoOf (parRedT_hasTy_left L.typed etaLeafCtx_wf
        (etaLeafEtaStep (PEq := PEq) (E := E) (n := n))) := by
  simp only [etaLeafLamStep, etaLeafEtaStep, etaLeafBodyStep, etaLeafInnerStep,
    parRedT_hasTy_left, parRedT_typed, hasTyT_of_tyConvT,
    etaLeafB_ty, etaLeafBody_ty, etaLeafLiftF_ty, decoOf,
    etaLeafX_var₁, etaLeafY_var₁, etaLeafP_var₁, decoOf_bvar]

/-- The existing three negative premises also obstruct the coherent
source-decorated one-step diamond. This is a conditional corollary, not
an admitted-environment countermodel: the three `NotProof` inputs remain. -/
theorem coherentDiamond_false_of_notProof (L : LeafIface E n PEq)
    (hnpd : NotProof E n etaLeafCtx (.lam etaLeafP etaLeafBody'))
    (hnpf : NotProof E n etaLeafCtx etaLeafF)
    (hnpx : NotProof E n etaLeafCtx (.bvar 1))
    (D : DecoStarAudit.CoherentDiamond L) : False := by
  let j := D etaLeafCtx_wf
    ⟨etaLeafLamStep L, etaLeafLamCert L⟩ ⟨etaLeafEtaStep, etaLeafEtaCert⟩
    (peak_source_deco_eq L)
  exact etaLeaf_no_join L hnpd hnpf hnpx ⟨j.centre, j.left, j.right⟩

end Rcic.Declarative.NativeValleys.DecoLeafAudit
