import rcic.RcicAnnAnnotate
import rcic.RcicAnnFamAppAny
import rcic.RcicAnnViewTySem

/-!
# RcicCoreRelation — core layer 5: the annotated copy and its logical relation

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

Key definitions and theorems of the layer:

* `Rcic.Declarative.Ann.ExprA` / `Rcic.Declarative.Ann.erase` / `Rcic.Declarative.Ann.ResolvedEnvA` — the annotated copy and erasure
* `Rcic.Declarative.Ann.HasTyA` / `Rcic.Declarative.Ann.ConvA` / `Rcic.Declarative.Ann.TyConvA` / `Rcic.Declarative.Ann.CtxWfA` / `Rcic.Declarative.Ann.EnvWfA` — the judgment family on the copy
* `Rcic.Declarative.Ann.IotaIfaceA` / `Rcic.Declarative.Ann.iotaIfaceA` — the copy's ι interface
* `Rcic.Declarative.Ann.inferA` / `Rcic.Declarative.Ann.whnfA` — synthesis and weak-head reduction on the copy
* `Rcic.Declarative.Ann.EqKA` / `Rcic.Declarative.Ann.TyKA` / `Rcic.Declarative.Ann.LREqA` — the logical relation
* `Rcic.Declarative.Ann.AnnEnvA` — the annotated environment package
* `Rcic.Declarative.Ann.erase_hasTyA` / `Rcic.Declarative.Ann.erase_convA` — erasure of the copy's derivations
* `Rcic.Declarative.Ann.hasTyA_sort_gen` / `Rcic.Declarative.Ann.hasTyA_const_gen` — sort uniqueness (DT-012) on the copy

Layer members: the `RcicAnn*` modules in the core except the rows suppliers
(`RcicAnnRowsSupply`, `RcicAnnSemPrefixRows`, `RcicAnnTypedRows`, which form
the rows layer).
-/
