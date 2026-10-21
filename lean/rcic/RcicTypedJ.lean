import rcic.RcicDeclarative

/-!
# M3-b GLM-2 — `RcicTypedJ` as a FORWARDING ENTRY

Since GLM-2 the typed judgment (`HasTyT` / `ConvT` / `TyConvT` / `CtxWfT` /
`ConvArgsT`, with `pinSortT` / `pinPiT`) is DEFINED at the root, `RcicDeclarative`
(single owner; see its "GLM-2 — the typed judgment, LANDED at the root" section).
This file re-exports it so every existing `import rcic.RcicTypedJ` keeps resolving
unchanged. There is NO second inductive here.

Why not the reverse (this file keeps the definitions)? `RcicTypedJ` imports
`RcicLevelCalc`, which imports `RcicDeclarative`; a `RcicDeclarative → RcicTypedJ`
edge would close the cycle the M3-b dispatch forbids. Level-boundedness was sunk to
the root for the same reason (`HasTyT.const` reads it).
-/

namespace Rcic.Declarative

-- names resolve directly: this file imports RcicDeclarative, which defines them

end Rcic.Declarative

#print axioms Rcic.Declarative.HasTyT
#print axioms Rcic.Declarative.TyConvT
