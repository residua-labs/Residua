import rcic.RcicPEqT
import rcic.RcicCtxConvT

/-!
# Context transport for the existing plain `PEqT`

A supplied `CtxConvT` transports `PEqT` by structural recursion.
Binder bodies retain their left declaration, so the context conversion
extends with `CtxConvT.same`.  At a proof leaf, the four existing
typing witnesses are transported by `hasTyT_ctx`.

This is transport under an already available context conversion.  It
does not construct `CtxConvT` from a `PEqT` domain equality, establish
general `PEqT` symmetry/transitivity, or assert that foundations or
derivation sizes are preserved by the transport.
-/

namespace Rcic.Declarative

/-- The original `PEqT` judgment transports across an existing
    pointwise-convertible context, keeping both expression indices. -/
def PEqT.ctx {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    {Γ Γ' : LCtx} → CtxConvT E n Γ Γ' → {a b : Expr Nat} →
      PEqT E n Γ a b → PEqT E n Γ' a b
  | _, Γ', _, _, _, .bvar _ i => .bvar Γ' i
  | _, Γ', _, _, _, .sort _ l l' h => .sort Γ' l l' h
  | _, Γ', _, _, _, .const _ r ls ls' h => .const Γ' r ls ls' h
  | _, Γ', hcc, _, _, .app _ f f' a a' hf ha =>
      .app Γ' f f' a a' (PEqT.ctx hcl hcc hf) (PEqT.ctx hcl hcc ha)
  | _, Γ', hcc, _, _, .lam _ A A' b b' hA hb =>
      .lam Γ' A A' b b' (PEqT.ctx hcl hcc hA)
        (PEqT.ctx hcl (.same (.assumption A) hcc) hb)
  | _, Γ', hcc, _, _, .pi _ A A' B B' hA hB =>
      .pi Γ' A A' B B' (PEqT.ctx hcl hcc hA)
        (PEqT.ctx hcl (.same (.assumption A) hcc) hB)
  | _, Γ', hcc, _, _, .letE _ A A' v v' b b' hA hv hb =>
      .letE Γ' A A' v v' b b' (PEqT.ctx hcl hcc hA) (PEqT.ctx hcl hcc hv)
        (PEqT.ctx hcl (.same (.letBinding A v) hcc) hb)
  | _, Γ', _, _, _, .lit _ t => .lit Γ' t
  | _, Γ', hcc, _, _, .proof _ p q P Q hP hQ hp hq =>
      .proof Γ' p q P Q
        (hasTyT_ctx hcl hcc hP) (hasTyT_ctx hcl hcc hQ)
        (hasTyT_ctx hcl hcc hp) (hasTyT_ctx hcl hcc hq)

#print axioms PEqT.ctx

end Rcic.Declarative
