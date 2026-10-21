import rcic.RcicF8EvPar
import rcic.RcicCtxMorphStack
import rcic.RcicF8IrrProducerPins
import rcic.RcicParRedTConv
import rcic.RcicPEqTSubst
import rcic.RcicTypedInvert
import rcic.RcicTypedEnvEntry

/-!
# `RcicF8EvParStar` — provenance stars, valleys, and the J/D interface (X tile S2b)

The interface the X tile consumes from the D/J tiles (S0 §5.5, #7026; cc ruling Q4: X
builds the interface, the owners build on it). No D/J content, no new producer.

`EvParStar R Γ a b T` is the star of provenance steps at one index, with `refl` carrying
the endpoint typing as `ParRedTStar.refl` does, plus lazy concatenation `trans` (`parRedTStar_trans`, so
valleys compose without pushing a continuation under `wk`) and the two lazy transports X needs
(S0 §5.1, §5.4): the index conversion `conv` (`parRedTStar_conv`, `ParRedT.conv`
step-wise) and weakening `wk` (`parRedTStar_lift`, whose `PEq` lift supplier is
`peqLeafT_lift` here: `PEqT.liftT` plus `hasTyTWeaken` on the two carried typings).
Materialization needs only `EnvClosed` / `EnvMembersSubstStable`, as `EvPar.val` does.

The lazy `subst0`/`substLet` constructors materialize through a stack of context
morphisms. Each producer is re-applied to its transported payload pieces by
`hasTyT_substS` / `convT_substS` / `tyConvT_substS` and their let and weakening twins.
The five landed producers (`proofIndex`, `structPi`, `sortEq`, `consts`, `lit`) and
`refl` all follow this route; no generic `ParRedT` substitution supplier is assumed.

`Valley R Γ M₁ M₂ T` is a join at index `T` with both endpoint typings carried (X's
U-alignment at middles reads them); it has `symm`, `conv`, `wk`. `DProc`/`DContract` (the
diamond on stars at a common index) and `JProcWf`/`JContractWf` (bare `ConvT` literals in a
WELL-FORMED context, strict leaves — cc Q3 and the 2026-10-14 ruling on #7035) are the
statements X's S3 consumes; `XProcWf`/`XContractWf` is the additive sibling of the sealed
`XProc` that Stratum B delivers. The Γ-unconditional `JProc`/`JContract` are kept as the
REFUTED statements, with the refutation sealed (`JTileS0.no_jproc_supplier`): no supplier
exists, so nothing is built against them. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### the `PEqLeafT` lift supplier -/

/-- `PEqLeafT` under weakening: the `≈P` by `PEqT.liftT`, the two carried typings by
    `hasTyTWeaken`. The `hPEqL` supplier `parRedT_lift`/`parRedTStar_lift` read. -/
def peqLeafT_lift (hcl : EnvClosed E) {Γ : LCtx} {p q T : Expr Nat} {d : LocalDecl}
    {c : Nat} (h : PEqLeafT E n Γ p q T) :
    PEqLeafT E n (insertAt d c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T) :=
  ⟨PEqT.liftT hcl d h.1, hasTyTWeaken d hcl h.2.1, hasTyTWeaken d hcl h.2.2⟩

/-! ### producers under a pending stack of context morphisms (W-X-SUBST S0 §5, #7107) -/

/-- the `structPi` producer under a stack: the six pieces transported (the codomain pieces by the
    shifted stack), the SAME `structPiStep`, both Π endpoints re-read by `apply_pi`. -/
def structPiValS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T)
    (σ : CtxMorph E n Γ Γ') :
    ParRedT (PEqLeafT E n) E n Γ' (σ.apply (.pi A B)) (σ.apply (.pi A' B')) (σ.apply T) :=
  parRedT_cast (σ.apply_pi hcl A B A).symm (σ.apply_pi hcl A' B' A).symm
    (structPiStep
      (hasTyT_castE (σ.apply_sort p.u) (σ.hasTyT hcl hinst (p.hA.val hcl hinst)))
      (convT_castT (σ.apply_sort p.u) (σ.convT hcl hinst (p.hc.val hcl hinst)))
      (hasTyT_castE ((σ.under hcl A).apply_sort p.v)
        ((σ.under hcl A).hasTyT hcl hinst (p.hB.val hcl hinst)))
      (convT_castT ((σ.under hcl A).apply_sort p.v)
        ((σ.under hcl A).convT hcl hinst (p.hcB.val hcl hinst)))
      (hasTyT_castEA (σ.apply_pi hcl A' B' A) (σ.apply_sort _)
        (σ.hasTyT hcl hinst (p.hrt.val hcl hinst)))
      (tyConvT_castL (σ.apply_sort _) (σ.tyConvT hcl hinst (p.idx.val hcl hinst))))

/-- Sort equality under a pending stack, using the same canonical producer on transported pieces. -/
def sortEqValS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} {l₁ l₂ : Level} {T : Expr Nat} (p : SortEqPayload R Γ l₁ l₂ T)
    (σ : CtxMorph E n Γ Γ') :
    ParRedT (PEqLeafT E n) E n Γ' (σ.apply (.sort l₁)) (σ.apply (.sort l₂)) (σ.apply T) :=
  parRedT_cast (σ.apply_sort l₁).symm (σ.apply_sort l₂).symm
    (sortEqStep p.h
      (hasTyT_castEA (σ.apply_sort l₁) rfl (σ.hasTyT hcl hinst (p.hl.val hcl hinst)))
      (hasTyT_castEA (σ.apply_sort l₂) rfl (σ.hasTyT hcl hinst (p.hr.val hcl hinst)))
      (σ.tyConvT hcl hinst (p.idx.val hcl hinst)))

/-- Constant-level equality under a pending stack, reusing `constsStep`. -/
def constsValS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) (σ : CtxMorph E n Γ Γ') :
    ParRedT (PEqLeafT E n) E n Γ' (σ.apply (.const r ls)) (σ.apply (.const r ls')) (σ.apply T) :=
  parRedT_cast (σ.apply_const r ls).symm (σ.apply_const r ls').symm
    (constsStep p.h
      (hasTyT_castEA (σ.apply_const r ls) rfl (σ.hasTyT hcl hinst (p.hl.val hcl hinst)))
      (hasTyT_castEA (σ.apply_const r ls') rfl (σ.hasTyT hcl hinst (p.hr.val hcl hinst)))
      (σ.tyConvT hcl hinst (p.idx.val hcl hinst)))

/-- Reflexivity under a pending stack: the typing and the index conversion move by
    `CtxMorph.hasTyT` / `tyConvT`, then the same `reflStep`. -/
def reflValS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} {a T : Expr Nat} (p : ReflPayload R Γ a T)
    (σ : CtxMorph E n Γ Γ') :
    ParRedT (PEqLeafT E n) E n Γ' (σ.apply a) (σ.apply a) (σ.apply T) :=
  reflStep
    (σ.hasTyT hcl hinst (p.h.val hcl hinst))
    (σ.tyConvT hcl hinst (p.idx.val hcl hinst))

/-- Literal expansion under a pending stack, reusing `litStep` and the closed expansion law. -/
def litValS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} {t : Nat} {T : Expr Nat} (p : LitPayload R Γ t T)
    (σ : CtxMorph E n Γ Γ') :
    ParRedT (PEqLeafT E n) E n Γ' (σ.apply (.lit t)) (σ.apply (natExpand t)) (σ.apply T) :=
  parRedT_cast (σ.apply_lit t).symm (σ.apply_natExpand t).symm
    (litStep
      (hasTyT_castEA (σ.apply_natExpand t) rfl (σ.hasTyT hcl hinst (p.hexp.val hcl hinst)))
      (σ.tyConvT hcl hinst (p.idx.val hcl hinst)))

/-- the producer's EXACT output under a pending stack: every piece is transported along the stack
    by its landed lemma (`CtxMorph.hasTyT`/`convT`/`tyConvT`, i.e. `hasTyT_substS`/`…substLetS`/
    `hasTyTWeaken` entry-wise), then the SAME producer is applied. `hcl`/`hinst` only. This is the
    `substVal` of the five landed producers and `refl` (`EvPar.substVal` below is the one-entry case). -/
def EvPar.valS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → {a b T : Expr Nat} → EvPar R Γ a b T → (σ : CtxMorph E n Γ Γ') →
      ParRedT (PEqLeafT E n) E n Γ' (σ.apply a) (σ.apply b) (σ.apply T)
  | _, _, _, _, _, .proofIndex p, σ => .peq _ _ _ _
      (peqLeafT_reconcile_propIndex
        (hasTyT_castE (σ.apply_sort .zero) (σ.hasTyT hcl hinst (p.propTy.val hcl hinst)))
        (σ.tyConvT hcl hinst (p.chain.val hcl hinst))
        (σ.hasTyT hcl hinst (p.leftTy.val hcl hinst))
        (σ.hasTyT hcl hinst (p.rightTy.val hcl hinst))).1
  | _, _, _, _, _, .structPi p, σ => structPiValS hcl hinst p σ
  | _, _, _, _, _, .sortEq p, σ => sortEqValS hcl hinst p σ
  | _, _, _, _, _, .consts p, σ => constsValS hcl hinst p σ
  | _, _, _, _, _, .lit p, σ => litValS hcl hinst p σ
  | _, _, _, _, _, .refl p, σ => reflValS hcl hinst p σ

theorem EvPar.valS_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ Γ' : LCtx} (σ : CtxMorph E n Γ Γ') {a b T : Expr Nat} (D : EvPar R Γ a b T) :
    (D.widen hr).valS hcl hinst σ = D.valS hcl hinst σ := by
  cases D with
  | proofIndex p =>
      simp only [EvPar.widen, EvPar.valS, ProofIndexPayload.widen, evTyVal_widen, evTcVal_widen]
  | structPi p =>
      simp only [EvPar.widen, EvPar.valS, structPiValS, StructPiPayload.widen, evTyVal_widen,
        evCvVal_widen, evTcVal_widen]
  | sortEq p =>
      simp only [EvPar.widen, EvPar.valS, sortEqValS, SortEqPayload.widen, evTyVal_widen,
        evTcVal_widen]
  | consts p =>
      simp only [EvPar.widen, EvPar.valS, constsValS, ConstsPayload.widen, evTyVal_widen,
        evTcVal_widen]
  | lit p =>
      simp only [EvPar.widen, EvPar.valS, litValS, LitPayload.widen, evTyVal_widen,
        evTcVal_widen]
  | refl p =>
      simp only [EvPar.widen, EvPar.valS, reflValS, ReflPayload.widen, evTyVal_widen,
        evTcVal_widen]

/-- the one-entry case: a producer under ONE assumption substitution at `j` — never
    `PEqT.instantiate_pair`, the producer re-applied to its substituted pieces. -/
def EvPar.substVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) (h : EvPar R Γ a b T) :
    ParRedT (PEqLeafT E n) E n (substRemove v j Γ) (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T) :=
  h.valS hcl hinst (.sub j hget hv .nil)

/-- `substVal` at `proofIndex` IS the reconciliation of the four substituted pieces. -/
theorem EvPar.substVal_proofIndex (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (p : ProofIndexPayload R Γ a b T) :
    (EvPar.proofIndex p).substVal hcl hinst j hget hv = .peq _ _ _ _
      (peqLeafT_reconcile_propIndex
        (hasTyT_substS hcl hinst v t (p.propTy.val hcl hinst) hget hv)
        (tyConvT_substS hcl hinst v t (p.chain.val hcl hinst) hget hv)
        (hasTyT_substS hcl hinst v t (p.leftTy.val hcl hinst) hget hv)
        (hasTyT_substS hcl hinst v t (p.rightTy.val hcl hinst) hget hv)).1 := by
  unfold EvPar.substVal EvPar.valS
  rfl

/-! ### the star -/

/-- the star of provenance steps at one index. `refl` carries the endpoint typing
    (`ParRedTStar.refl`'s `h`); `conv` and `wk` are the lazy transports. -/
inductive EvParStar (R : List (Jd E n)) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | refl {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) : EvParStar R Γ a a T
  | tail {Γ : LCtx} {a b c T : Expr Nat} (h : EvPar R Γ a b T)
      (hs : EvParStar R Γ b c T) : EvParStar R Γ a c T
  | conv {Γ : LCtx} {a b T T' : Expr Nat} (hs : EvParStar R Γ a b T)
      (c : EvTc R Γ T T') : EvParStar R Γ a b T'
  | wk {Γ : LCtx} {a b T : Expr Nat} (d : LocalDecl) (c : Nat)
      (hs : EvParStar R Γ a b T) :
      EvParStar R (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | trans {Γ : LCtx} {a b c T : Expr Nat} (h₁ : EvParStar R Γ a b T)
      (h₂ : EvParStar R Γ b c T) : EvParStar R Γ a c T
  /-- lazy substitution of an assumption (W-X-SUBST S0 §5): `hv` carried ONCE; materialized by
      pushing the substitution to the producers through the morphism stack (`valS`). -/
  | subst0 {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (hs : EvParStar R Γ a b T)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      EvParStar R (substRemove v j Γ) (instantiate j (lift 0 j v) a)
        (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  /-- lazy substitution of a let binding by its own value (`EvTc.substLet`'s star twin). -/
  | substLet {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat) (hs : EvParStar R Γ a b T)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
      EvParStar R (substRemove w j Γ) (instantiate j (lift 0 j w) a)
        (instantiate j (lift 0 j w) b) (instantiate j (lift 0 j w) T)

/-- the star under a pending stack: `wk` and the two substitutions push an entry and recurse —
    nothing is ever commuted (the `j < c` wall of pushing a substitution through a weakening is
    not met, because the weakening is never pushed; it is queued). -/
def EvParStar.valS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T → (σ : CtxMorph E n Γ Γ') →
      ParRedTStar (PEqLeafT E n) E n Γ' (σ.apply a) (σ.apply b) (σ.apply T)
  | _, _, _, _, _, .refl h, σ => .refl _ _ _ (σ.hasTyT hcl hinst (h.val hcl hinst))
  | _, _, _, _, _, .tail h hs, σ => .tail (h.valS hcl hinst σ) (hs.valS hcl hinst σ)
  | _, _, _, _, _, .conv hs c, σ =>
      parRedTStar_conv (σ.tyConvT hcl hinst (c.val hcl hinst)) (hs.valS hcl hinst σ)
  | _, _, _, _, _, .wk d c hs, σ => hs.valS hcl hinst (.ins d c σ)
  | _, _, _, _, _, .trans h₁ h₂, σ => parRedTStar_trans (h₁.valS hcl hinst σ) (h₂.valS hcl hinst σ)
  | _, _, _, _, _, .subst0 j hs hget hv, σ => hs.valS hcl hinst (.sub j hget (hv.val hcl hinst) σ)
  | _, _, _, _, _, .substLet j hs hget hv, σ =>
      hs.valS hcl hinst (.subLet j hget (hv.val hcl hinst) σ)

/-- materialization: `ParRedTStar.refl`/`tail`, `parRedTStar_conv`, `parRedTStar_lift`
    with `peqLeafT_lift`. -/
def EvParStar.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T →
    ParRedTStar (PEqLeafT E n) E n Γ a b T
  | _, _, _, _, .refl h => .refl _ _ _ (h.val hcl hinst)
  | _, _, _, _, .tail h hs => .tail (h.val hcl hinst) (hs.val hcl hinst)
  | _, _, _, _, .conv hs c => parRedTStar_conv (c.val hcl hinst) (hs.val hcl hinst)
  | _, _, _, _, .wk d _ hs =>
      parRedTStar_lift d hcl (fun h => peqLeafT_lift hcl h) (hs.val hcl hinst)
  | _, _, _, _, .trans h₁ h₂ => parRedTStar_trans (h₁.val hcl hinst) (h₂.val hcl hinst)
  | _, _, _, _, .subst0 j hs hget hv => hs.valS hcl hinst (.sub j hget (hv.val hcl hinst) .nil)
  | _, _, _, _, .substLet j hs hget hv =>
      hs.valS hcl hinst (.subLet j hget (hv.val hcl hinst) .nil)

/-- literal leaves, with multiplicity, in constructor order. -/
def EvParStar.leaves : {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T →
    List (Jd E n)
  | _, _, _, _, .refl h => h.leaves
  | _, _, _, _, .tail h hs => h.leaves ++ hs.leaves
  | _, _, _, _, .conv hs c => hs.leaves ++ c.leaves
  | _, _, _, _, .wk _ _ hs => hs.leaves
  | _, _, _, _, .trans h₁ h₂ => h₁.leaves ++ h₂.leaves
  | _, _, _, _, .subst0 _ hs _ hv => hs.leaves ++ hv.leaves
  | _, _, _, _, .substLet _ hs _ hv => hs.leaves ++ hv.leaves

/-- the leaf law of the lazy substitution: the star's leaves, then `hv`'s ONCE. -/
theorem EvParStar.leaves_subst0 {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat)
    (hs : EvParStar R Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    (EvParStar.subst0 j hs hget hv).leaves = hs.leaves ++ hv.leaves := rfl

theorem EvParStar.leaves_substLet {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
    (hs : EvParStar R Γ a b T) (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
    (EvParStar.substLet j hs hget hv).leaves = hs.leaves ++ hv.leaves := rfl

/-- constructor count. -/
def EvParStar.size : {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T → Nat
  | _, _, _, _, .refl h => 1 + h.size
  | _, _, _, _, .tail h hs => 1 + h.size + hs.size
  | _, _, _, _, .conv hs c => 1 + hs.size + c.size
  | _, _, _, _, .wk _ _ hs => 1 + hs.size
  | _, _, _, _, .trans h₁ h₂ => 1 + h₁.size + h₂.size
  | _, _, _, _, .subst0 _ hs _ hv => 1 + hs.size + hv.size
  | _, _, _, _, .substLet _ hs _ hv => 1 + hs.size + hv.size

/-- O-M3(a): every leaf is certified into the root bundle. -/
theorem EvParStar.leaves_root : {Γ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ a b T) → ∀ ℓ ∈ hs.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, _, .refl h => h.leaves_root
  | _, _, _, _, .tail h hs => fun ℓ hℓ => by
      simp only [EvParStar.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact h.leaves_root ℓ hℓ
      · exact hs.leaves_root ℓ hℓ
  | _, _, _, _, .conv hs c => fun ℓ hℓ => by
      simp only [EvParStar.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact c.leaves_root ℓ hℓ
  | _, _, _, _, .wk _ _ hs => hs.leaves_root
  | _, _, _, _, .trans h₁ h₂ => fun ℓ hℓ => by
      simp only [EvParStar.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact h₁.leaves_root ℓ hℓ
      · exact h₂.leaves_root ℓ hℓ
  | _, _, _, _, .subst0 _ hs _ hv => fun ℓ hℓ => by
      simp only [EvParStar.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact hv.leaves_root ℓ hℓ
  | _, _, _, _, .substLet _ hs _ hv => fun ℓ hℓ => by
      simp only [EvParStar.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact hv.leaves_root ℓ hℓ

/-- widening the root bundle. -/
def EvParStar.widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → EvParStar R Γ a b T → EvParStar R' Γ a b T
  | _, _, _, _, .refl h => .refl (h.widen hr)
  | _, _, _, _, .tail h hs => .tail (h.widen hr) (hs.widen hr)
  | _, _, _, _, .conv hs c => .conv (hs.widen hr) (c.widen hr)
  | _, _, _, _, .wk d k hs => .wk d k (hs.widen hr)
  | _, _, _, _, .trans h₁ h₂ => .trans (h₁.widen hr) (h₂.widen hr)
  | _, _, _, _, .subst0 j hs hget hv => .subst0 j (hs.widen hr) hget (hv.widen hr)
  | _, _, _, _, .substLet j hs hget hv => .substLet j (hs.widen hr) hget (hv.widen hr)

theorem EvParStar.leaves_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → (hs : EvParStar R Γ a b T) →
    (hs.widen hr).leaves = hs.leaves
  | _, _, _, _, .refl h => h.leaves_widen hr
  | _, _, _, _, .tail h hs => by
      simp only [EvParStar.widen, EvParStar.leaves, h.leaves_widen hr, hs.leaves_widen hr]
  | _, _, _, _, .conv hs c => by
      simp only [EvParStar.widen, EvParStar.leaves, hs.leaves_widen hr,
        EvTc.leaves_widen hr c]
  | _, _, _, _, .wk _ _ hs => hs.leaves_widen hr
  | _, _, _, _, .trans h₁ h₂ => by
      simp only [EvParStar.widen, EvParStar.leaves, h₁.leaves_widen hr, h₂.leaves_widen hr]
  | _, _, _, _, .subst0 _ hs _ hv => by
      simp only [EvParStar.widen, EvParStar.leaves, hs.leaves_widen hr, hv.leaves_widen hr]
  | _, _, _, _, .substLet _ hs _ hv => by
      simp only [EvParStar.widen, EvParStar.leaves, hs.leaves_widen hr, hv.leaves_widen hr]

theorem EvParStar.size_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → (hs : EvParStar R Γ a b T) →
    (hs.widen hr).size = hs.size
  | _, _, _, _, .refl h => by simp only [EvParStar.widen, EvParStar.size, evTySize_widen hr h]
  | _, _, _, _, .tail h hs => by
      simp only [EvParStar.widen, EvParStar.size, h.size_widen hr, hs.size_widen hr]
  | _, _, _, _, .conv hs c => by
      simp only [EvParStar.widen, EvParStar.size, hs.size_widen hr, evTcSize_widen hr c]
  | _, _, _, _, .wk _ _ hs => by simp only [EvParStar.widen, EvParStar.size, hs.size_widen hr]
  | _, _, _, _, .trans h₁ h₂ => by
      simp only [EvParStar.widen, EvParStar.size, h₁.size_widen hr, h₂.size_widen hr]
  | _, _, _, _, .subst0 _ hs _ hv => by
      simp only [EvParStar.widen, EvParStar.size, hs.size_widen hr, evTySize_widen hr hv]
  | _, _, _, _, .substLet _ hs _ hv => by
      simp only [EvParStar.widen, EvParStar.size, hs.size_widen hr, evTySize_widen hr hv]

/-- widening transports the stacked materialization. -/
theorem EvParStar.valS_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ Γ' : LCtx} → {a b T : Expr Nat} → (hs : EvParStar R Γ a b T) → (σ : CtxMorph E n Γ Γ') →
    (hs.widen hr).valS hcl hinst σ = hs.valS hcl hinst σ
  | _, _, _, _, _, .refl h, _ => by
      simp only [EvParStar.widen, EvParStar.valS, evTyVal_widen hr hcl hinst h]
  | _, _, _, _, _, .tail h hs, σ => by
      simp only [EvParStar.widen, EvParStar.valS, h.valS_widen hr hcl hinst σ,
        hs.valS_widen hr hcl hinst σ]
  | _, _, _, _, _, .conv hs c, σ => by
      simp only [EvParStar.widen, EvParStar.valS, hs.valS_widen hr hcl hinst σ,
        evTcVal_widen hr hcl hinst c]
  | _, _, _, _, _, .wk d c hs, σ => by
      simp only [EvParStar.widen, EvParStar.valS, hs.valS_widen hr hcl hinst (.ins d c σ)]
  | _, _, _, _, _, .trans h₁ h₂, σ => by
      simp only [EvParStar.widen, EvParStar.valS, h₁.valS_widen hr hcl hinst σ,
        h₂.valS_widen hr hcl hinst σ]
  | _, _, _, _, _, .subst0 j hs hget hv, σ => by
      show (hs.widen hr).valS hcl hinst (.sub j hget ((hv.widen hr).val hcl hinst) σ) = _
      rw [evTyVal_widen hr hcl hinst hv]
      exact hs.valS_widen hr hcl hinst _
  | _, _, _, _, _, .substLet j hs hget hv, σ => by
      show (hs.widen hr).valS hcl hinst (.subLet j hget ((hv.widen hr).val hcl hinst) σ) = _
      rw [evTyVal_widen hr hcl hinst hv]
      exact hs.valS_widen hr hcl hinst _

/-- widening transports the original materialization. -/
theorem EvParStar.val_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hs : EvParStar R Γ a b T) →
    (hs.widen hr).val hcl hinst = hs.val hcl hinst
  | _, _, _, _, .refl h => by
      simp only [EvParStar.widen, EvParStar.val, evTyVal_widen hr hcl hinst h]
  | _, _, _, _, .tail h hs => by
      simp only [EvParStar.widen, EvParStar.val, h.val_widen hr hcl hinst,
        hs.val_widen hr hcl hinst]
  | _, _, _, _, .conv hs c => by
      simp only [EvParStar.widen, EvParStar.val, hs.val_widen hr hcl hinst,
        evTcVal_widen hr hcl hinst c]
  | _, _, _, _, .wk _ _ hs => by
      simp only [EvParStar.widen, EvParStar.val, hs.val_widen hr hcl hinst]
  | _, _, _, _, .trans h₁ h₂ => by
      simp only [EvParStar.widen, EvParStar.val, h₁.val_widen hr hcl hinst,
        h₂.val_widen hr hcl hinst]
  | _, _, _, _, .subst0 j hs hget hv => by
      show (hs.widen hr).valS hcl hinst (.sub j hget ((hv.widen hr).val hcl hinst) .nil) = _
      rw [evTyVal_widen hr hcl hinst hv]
      exact hs.valS_widen hr hcl hinst _
  | _, _, _, _, .substLet j hs hget hv => by
      show (hs.widen hr).valS hcl hinst (.subLet j hget ((hv.widen hr).val hcl hinst) .nil) = _
      rw [evTyVal_widen hr hcl hinst hv]
      exact hs.valS_widen hr hcl hinst _

/-! ### valleys -/

/-- a join at index `T` with both endpoint typings carried. -/
structure Valley (R : List (Jd E n)) (Γ : LCtx) (M₁ M₂ T : Expr Nat) where
  N : Expr Nat
  left : EvParStar R Γ M₁ N T
  right : EvParStar R Γ M₂ N T
  ty₁ : EvTy R Γ M₁ T
  ty₂ : EvTy R Γ M₂ T

variable {Γ : LCtx} {M₁ M₂ T : Expr Nat}

def Valley.leaves (V : Valley R Γ M₁ M₂ T) : List (Jd E n) :=
  V.left.leaves ++ V.right.leaves ++ V.ty₁.leaves ++ V.ty₂.leaves

theorem Valley.leaves_root (V : Valley R Γ M₁ M₂ T) :
    ∀ ℓ ∈ V.leaves, ∃ r ∈ R, SubEq ℓ r := by
  intro ℓ hℓ
  simp only [Valley.leaves, List.mem_append] at hℓ
  rcases hℓ with ((hℓ | hℓ) | hℓ) | hℓ
  · exact V.left.leaves_root ℓ hℓ
  · exact V.right.leaves_root ℓ hℓ
  · exact V.ty₁.leaves_root ℓ hℓ
  · exact V.ty₂.leaves_root ℓ hℓ

/-- swapping the two legs. -/
def Valley.symm (V : Valley R Γ M₁ M₂ T) : Valley R Γ M₂ M₁ T :=
  ⟨V.N, V.right, V.left, V.ty₂, V.ty₁⟩

/-- index alignment (S0 §5.1 step 2): both legs by `conv`, both typings by `rety`. -/
def Valley.conv {T' : Expr Nat} (V : Valley R Γ M₁ M₂ T) (c : EvTc R Γ T T') :
    Valley R Γ M₁ M₂ T' :=
  ⟨V.N, .conv V.left c, .conv V.right c, .rety V.ty₁ c, .rety V.ty₂ c⟩

/-- weakening. -/
def Valley.wk (d : LocalDecl) (k : Nat) (V : Valley R Γ M₁ M₂ T) :
    Valley R (insertAt d k Γ) (lift k 1 M₁) (lift k 1 M₂) (lift k 1 T) :=
  ⟨lift k 1 V.N, .wk d k V.left, .wk d k V.right, .wk d k V.ty₁, .wk d k V.ty₂⟩

def Valley.widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R') (V : Valley R Γ M₁ M₂ T) :
    Valley R' Γ M₁ M₂ T :=
  ⟨V.N, V.left.widen hr, V.right.widen hr, V.ty₁.widen hr, V.ty₂.widen hr⟩

theorem Valley.symm_leaves (V : Valley R Γ M₁ M₂ T) :
    ∀ ℓ ∈ V.symm.leaves, ℓ ∈ V.leaves := by
  intro ℓ hℓ
  simp only [Valley.symm, Valley.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with ((hℓ | hℓ) | hℓ) | hℓ
  · exact .inl (.inl (.inr hℓ))
  · exact .inl (.inl (.inl hℓ))
  · exact .inr hℓ
  · exact .inl (.inr hℓ)

theorem Valley.conv_leaves {T' : Expr Nat} (V : Valley R Γ M₁ M₂ T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (V.conv c).leaves, ℓ ∈ V.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [Valley.conv, Valley.leaves, EvParStar.leaves, EvTy.leaves,
    List.mem_append] at hℓ ⊢
  rcases hℓ with (((hℓ | hℓ) | (hℓ | hℓ)) | (hℓ | hℓ)) | (hℓ | hℓ)
  · exact .inl (.inl (.inl (.inl hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inl (.inr hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inr hℓ))
  · exact .inr hℓ
  · exact .inl (.inr hℓ)
  · exact .inr hℓ

theorem Valley.wk_leaves (d : LocalDecl) (k : Nat) (V : Valley R Γ M₁ M₂ T) :
    (V.wk d k).leaves = V.leaves := by
  simp only [Valley.wk, Valley.leaves, EvParStar.leaves, EvTy.leaves]

theorem Valley.leaves_widen {R' : List (Jd E n)} (hr : ∀ x ∈ R, x ∈ R')
    (V : Valley R Γ M₁ M₂ T) : (V.widen hr).leaves = V.leaves := by
  simp only [Valley.widen, Valley.leaves, EvParStar.leaves_widen, EvTy.leaves_widen]

/-- substitution of an assumption (W-X-SUBST S0 §5): both legs by the lazy `EvParStar.subst0`,
    both typings by the `hvT`-free `EvTy.subst0`. -/
def Valley.subst0 {t v : Expr Nat} (j : Nat) (V : Valley R Γ M₁ M₂ T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    Valley R (substRemove v j Γ) (instantiate j (lift 0 j v) M₁)
      (instantiate j (lift 0 j v) M₂) (instantiate j (lift 0 j v) T) :=
  ⟨instantiate j (lift 0 j v) V.N, .subst0 j V.left hget hv, .subst0 j V.right hget hv,
    .subst0 j V.ty₁ hget hv, .subst0 j V.ty₂ hget hv⟩

theorem Valley.subst0_leaves {t v : Expr Nat} (j : Nat) (V : Valley R Γ M₁ M₂ T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    ∀ ℓ ∈ (V.subst0 j hget hv).leaves, ℓ ∈ V.leaves ++ hv.leaves := by
  intro ℓ hℓ
  simp only [Valley.subst0, Valley.leaves, EvParStar.leaves, EvTy.leaves,
    List.mem_append] at hℓ ⊢
  rcases hℓ with (((hℓ | hℓ) | (hℓ | hℓ)) | (hℓ | hℓ)) | (hℓ | hℓ)
  · exact .inl (.inl (.inl (.inl hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inl (.inr hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inr hℓ))
  · exact .inr hℓ
  · exact .inl (.inr hℓ)
  · exact .inr hℓ

/-- the let twin: both legs by `EvParStar.substLet`, both typings by `EvTy.substLet`. -/
def Valley.substLet {t w : Expr Nat} (j : Nat) (V : Valley R Γ M₁ M₂ T)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
    Valley R (substRemove w j Γ) (instantiate j (lift 0 j w) M₁)
      (instantiate j (lift 0 j w) M₂) (instantiate j (lift 0 j w) T) :=
  ⟨instantiate j (lift 0 j w) V.N, .substLet j V.left hget hv, .substLet j V.right hget hv,
    .substLet j V.ty₁ hget hv, .substLet j V.ty₂ hget hv⟩

theorem Valley.substLet_leaves {t w : Expr Nat} (j : Nat) (V : Valley R Γ M₁ M₂ T)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
    ∀ ℓ ∈ (V.substLet j hget hv).leaves, ℓ ∈ V.leaves ++ hv.leaves := by
  intro ℓ hℓ
  simp only [Valley.substLet, Valley.leaves, EvParStar.leaves, EvTy.leaves,
    List.mem_append] at hℓ ⊢
  rcases hℓ with (((hℓ | hℓ) | (hℓ | hℓ)) | (hℓ | hℓ)) | (hℓ | hℓ)
  · exact .inl (.inl (.inl (.inl hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inl (.inr hℓ)))
  · exact .inr hℓ
  · exact .inl (.inl (.inr hℓ))
  · exact .inr hℓ
  · exact .inl (.inr hℓ)
  · exact .inr hℓ

/-! ### the J and D interfaces (statements X's S3 consumes; cc Q3 confirmed) -/

/-- H-J: a join for a bare `ConvT` literal certified into `R`, at the literal's own
    index. Called only after X has stripped the lazy transports. -/
abbrev JProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {M₁ M₂ T : Expr Nat} (h : ConvT E n Γ M₁ M₂ T),
    (∃ r ∈ R, SubEq (.cv h) r) → Valley R Γ M₁ M₂ T

/-- H-J's leaf contract: every valley leaf is a STRICT sub-derivation of the literal
    (every step J emits is built from `h`'s children; `literalIrrProducer_dm` is the one
    landed instance). -/
def JContract (J : ∀ R : List (Jd E n), JProc R) : Prop :=
  ∀ R {Γ : LCtx} {M₁ M₂ T : Expr Nat} (h : ConvT E n Γ M₁ M₂ T)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r),
    ∀ ℓ ∈ (J R h hsub).leaves, SubOf ℓ (.cv h)

/-- H-D: the diamond on provenance stars at a common index (strip lemma included). -/
abbrev DProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, EvParStar R Γ a b T → EvParStar R Γ a c T →
    Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T

/-- H-D's leaf contract: the closing legs cite only sub-derivations of the two inputs. -/
def DContract (D : ∀ R : List (Jd E n), DProc R) : Prop :=
  ∀ R {Γ : LCtx} {a b c T : Expr Nat} (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T),
    ∀ ℓ ∈ (D R h₁ h₂).2.1.leaves ++ (D R h₁ h₂).2.2.leaves,
      ∃ ℓ' ∈ h₁.leaves ++ h₂.leaves, SubEq ℓ ℓ'

/-! ### the context-conditional interfaces (cc ruling 2026-10-14 on #7035, binding for #7026)

The Γ-unconditional `JProc` above has NO supplier. At `emptyEnv` (an `EnvWfT`) the ill-formed
context `XTileQ1.illCtx` carries a bare `ConvT` literal at `.sort .zero` whose LEFT endpoint
is typable at no type (the X lane's Q1 fixture, sealed below byte-for-byte), and `Valley.ty₁`
would materialize that typing. The refutation is the J lane's (#7035,
`no_unconditional_left_projection` / `no_valley_provider`, credited), sealed below so the
false form cannot return. H-J is therefore `JProcWf`: the caller supplies `CtxWfT E n Γ`;
`EnvWfT E` is a module-boundary hypothesis of every J supplier; the strict clause covers ALL
output leaves, the endpoint typings included. Stratum B of X calls J, so its deliverable is
the additive sibling `XProcWf` of the sealed `XProc` — whose Stratum-B part has no supplier
on this route (not proven false); Stratum A (S1's `xStruct`, no J) stays unconditional.
`JProc`/`JContract` remain as the refuted statements: definitions only. -/

/-- H-J (context-conditional): a join for a bare `ConvT` literal certified into `R`, at the
    literal's own index, in a well-formed context. -/
abbrev JProcWf (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {M₁ M₂ T : Expr Nat}, CtxWfT E n Γ → (h : ConvT E n Γ M₁ M₂ T) →
    (∃ r ∈ R, SubEq (.cv h) r) → Valley R Γ M₁ M₂ T

/-- H-J's strict leaf contract over ALL valley leaves (legs AND endpoint typings). -/
def JContractWf (J : ∀ R : List (Jd E n), JProcWf R) : Prop :=
  ∀ R {Γ : LCtx} {M₁ M₂ T : Expr Nat} (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ M₁ M₂ T)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r),
    ∀ ℓ ∈ (J R hΓ h hsub).leaves, SubOf ℓ (.cv h)

/-- weak-row X on provenance in a well-formed context: `XProc`'s shape with `CtxWfT`. -/
abbrev XProcWf (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B A' B' : Expr Nat}, CtxWfT E n Γ → EvTc R Γ (.pi A B) (.pi A' B') →
    EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B'

/-- `XContract`'s clause for `XProcWf`: every output leaf is `SubEq` an input leaf. -/
def XContractWf (X : ∀ R : List (Jd E n), XProcWf R) : Prop :=
  ∀ R {Γ : LCtx} {A B A' B' : Expr Nat} (hΓ : CtxWfT E n Γ)
    (c : EvTc R Γ (.pi A B) (.pi A' B')),
    ∀ ℓ ∈ (X R hΓ c).1.leaves ++ (X R hΓ c).2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'

/-! ### non-vacuity pins at the landed irr producer -/

section Pins
set_option autoImplicit false
open Rcic.Declarative.PEqTProofFront Rcic.Declarative.PEqLeafTPropPins IrrPins

private def pinCl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def pinSS : EnvMembersSubstStable emptyEnv := fun _ _ h => Option.noConfusion h

/-- `q`'s typing is the irr node's third child. -/
private theorem qChild : Child (.ty (q_ty [])) IrrPins.root := by
  show (Jd.ty (q_ty []) : Jd emptyEnv 0) ∈
    ([Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] : List (Jd emptyEnv 0))
  exact .tail _ (.tail _ (.head _))

private theorem pChild : Child (.ty (p_ty [])) IrrPins.root := by
  show (Jd.ty (p_ty []) : Jd emptyEnv 0) ∈
    ([Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] : List (Jd emptyEnv 0))
  exact .tail _ (.head _)

/-- a one-step star: the landed irr producer, then `refl` at `q`'s literal typing. -/
def pinStar : EvParStar [IrrPins.root] [] p q P :=
  .tail IrrPins.producer (.refl (.lit (q_ty []) ⟨_, .head _, .inr (.child qChild)⟩))

theorem pinStar_leaves :
    pinStar.leaves = [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty []), Jd.ty (q_ty [])] := rfl

/-- its materialization is the producer's exact output followed by `refl`. -/
theorem pinStar_val :
    pinStar.val pinCl pinSS =
      .tail (IrrPins.producer.val pinCl pinSS) (.refl [] q P (q_ty [])) := rfl

/-- the trivial valley `p ⇉ q ⇇ q` at `P`. -/
def pinValley : Valley [IrrPins.root] [] p q P :=
  ⟨q, pinStar, .refl (.lit (q_ty []) ⟨_, .head _, .inr (.child qChild)⟩),
    .lit (p_ty []) ⟨_, .head _, .inr (.child pChild)⟩,
    .lit (q_ty []) ⟨_, .head _, .inr (.child qChild)⟩⟩

/-- the valley's leaves, in order: the star's four, `refl q`'s one, `ty₁`, `ty₂`. -/
theorem pinValley_leaves :
    pinValley.leaves = [Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty []), Jd.ty (q_ty []),
      Jd.ty (q_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] := rfl

/-- every valley leaf is strictly below the one root — the shape `JContract` demands. -/
theorem pinValley_strict : ∀ ℓ ∈ pinValley.leaves, SubOf ℓ IrrPins.root := by
  intro ℓ hℓ
  rw [pinValley_leaves] at hℓ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .child (by
      show (Jd.ty (P_ty []) : Jd emptyEnv 0) ∈
        ([Jd.ty (P_ty []), Jd.ty (p_ty []), Jd.ty (q_ty [])] : List (Jd emptyEnv 0))
      exact .head _)
  · exact .child pChild
  · exact .child qChild
  · exact .child qChild
  · exact .child qChild
  · exact .child pChild
  · exact .child qChild

/-- the weakened valley keeps its leaves. -/
theorem pinValley_wk_leaves :
    (pinValley.wk (.assumption (.sort .zero)) 0).leaves = pinValley.leaves :=
  Valley.wk_leaves _ _ _

end Pins

end Rcic.Declarative.F8Measure

/-! ### sealed regression pins: the unconditional J has no supplier (#7035; cc 2026-10-14) -/

namespace Rcic.Declarative.XTileQ1

/-! the X lane's Q1 fixture, byte-for-byte from
`research/rcic/x-tile/Q1_SEPALL_ILLCTX_PIN_2026_10_14.lean` (fable/x-tile `12444dbd2e`). -/

/-- `x : const 0 []` — a nonexistent constant used as a type — and
    `f : Π (const 0 []), Sort 0`. Ill-formed: no `CtxWfT emptyEnv 0 illCtx` exists. -/
def illCtx : LCtx := [.assumption (.const 0 []), .assumption (.pi (.const 0 []) (.sort .zero))]

/-- the η-expansion of `f`, applied to `x`. -/
def P₁ : Expr Nat := .app (.lam (.const 0 []) (.app (.bvar 2) (.bvar 0))) (.bvar 0)

/-- `f x`. -/
def P₂ : Expr Nat := .app (.bvar 1) (.bvar 0)

def hf : HasTyT emptyEnv 0 illCtx (.bvar 1) (.pi (.const 0 []) (.sort .zero)) :=
  .bvar _ 1 _ rfl

def hx : HasTyT emptyEnv 0 illCtx (.bvar 0) (.const 0 []) :=
  .bvar _ 0 _ rfl

/-- the right endpoint is a Prop, by the `app` rule on two `bvar` typings. -/
def P₂_prop : HasTyT emptyEnv 0 illCtx P₂ (.sort .zero) :=
  .app illCtx (.bvar 1) (.bvar 0) (.const 0 []) (.sort .zero) hf hx

/-- a conversion at index `.sort .zero`: η on `f`, then `app` congruence with `refl x`. -/
def conv_sort0 : ConvT emptyEnv 0 illCtx P₁ P₂ (.sort .zero) :=
  .app illCtx (.lam (.const 0 []) (.app (.bvar 2) (.bvar 0))) (.bvar 1) (.bvar 0) (.bvar 0)
    (.const 0 []) (.sort .zero)
    (.eta illCtx (.bvar 1) (.const 0 []) (.sort .zero) hf)
    (.refl illCtx (.bvar 0) (.const 0 []) hx)

/-- the left endpoint has NO type at all: inverting `app`, then `lam`, demands a sort
    typing of the domain `const 0 []`, and `emptyEnv` has no member `0`. -/
theorem P₁_untypable (T : Expr Nat) : ¬ Nonempty (HasTyT emptyEnv 0 illCtx P₁ T) := by
  rintro ⟨h⟩
  obtain ⟨A, B, hlam, _, _⟩ := hasTyTInv_app h rfl
  obtain ⟨u, B', hdom, _, _⟩ := hasTyTInv_lam hlam rfl
  obtain ⟨m, hres, _, _, _⟩ := hasTyTInv_const hdom rfl
  exact Option.noConfusion hres

end Rcic.Declarative.XTileQ1

namespace Rcic.Declarative.JTileS0

/-! the J lane's refutation (#7035, `research/rcic/j-tile/J0_ENDPOINT_BOUNDARY_2026_10_14.lean`,
credited), sealed on the X-owned carrier as cc ruled; statements verbatim. -/

open F8Measure XTileQ1

/-- The exact singleton literal caller admitted by S0 JProc. -/
def root : List (Jd emptyEnv 0) := [.cv conv_sort0]

theorem original_literal :
    ∃ r ∈ root, SubEq (Jd.cv conv_sort0) r :=
  ⟨.cv conv_sort0, .head _, .inl rfl⟩

/-- No type, even after forgetting provenance; there is no leaf-measure issue here. -/
theorem no_plain_left : ¬ Nonempty (HasTyT emptyEnv 0 illCtx P₁ (.sort .zero)) :=
  P₁_untypable (.sort .zero)

/-- Arbitrary roots and arbitrary added provenance operations cannot repair
this endpoint while keeping their materialization sound. -/
theorem no_provenance_left (R : List (Jd emptyEnv 0)) :
    ¬ Nonempty (EvTy R illCtx P₁ (.sort .zero)) := by
  rintro ⟨D⟩
  exact no_plain_left ⟨D.val (envClosed_of_envWfT EnvWfT.empty)
    (envMembersSubstStable_of_envWfT EnvWfT.empty)⟩

/-- This is only the ty₁ projection REQUIRED by JProc, not a new J interface. -/
theorem no_unconditional_left_projection :
    ¬ Nonempty (∀ (R : List (Jd emptyEnv 0))
      {Γ : LCtx} {a b T : Expr Nat} (h : ConvT emptyEnv 0 Γ a b T),
      (∃ r ∈ R, SubEq (Jd.cv h) r) → EvTy R Γ a T) := by
  rintro ⟨Jleft⟩
  exact no_provenance_left root ⟨Jleft root conv_sort0 original_literal⟩

/-- Parametric in the X-owned result family. Any result that exposes Valley.ty₁
is impossible on S0's unrestricted literal input, before JContract is required. -/
theorem no_valley_provider
    (V : List (Jd emptyEnv 0) → LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (leftEndpoint : ∀ {R : List (Jd emptyEnv 0)}
      {Γ : LCtx} {a b T : Expr Nat}, V R Γ a b T → EvTy R Γ a T) :
    ¬ Nonempty (∀ (R : List (Jd emptyEnv 0))
      {Γ : LCtx} {a b T : Expr Nat} (h : ConvT emptyEnv 0 Γ a b T),
      (∃ r ∈ R, SubEq (Jd.cv h) r) → V R Γ a b T) := by
  rintro ⟨J⟩
  exact no_provenance_left root ⟨leftEndpoint (J root conv_sort0 original_literal)⟩

/-- the sealed `Valley` instance: no `∀ R, JProc R` exists at `emptyEnv`, an `EnvWfT`. -/
theorem no_jproc_supplier : ¬ Nonempty (∀ R : List (Jd emptyEnv 0), JProc R) :=
  no_valley_provider (fun R Γ a b T => Valley R Γ a b T) (fun V => V.ty₁)

end Rcic.Declarative.JTileS0

#print axioms Rcic.Declarative.F8Measure.peqLeafT_lift
#print axioms Rcic.Declarative.F8Measure.sortEqValS
#print axioms Rcic.Declarative.F8Measure.constsValS
#print axioms Rcic.Declarative.F8Measure.litValS
#print axioms Rcic.Declarative.F8Measure.EvParStar
#print axioms Rcic.Declarative.F8Measure.EvParStar.val
#print axioms Rcic.Declarative.F8Measure.EvParStar.leaves
#print axioms Rcic.Declarative.F8Measure.EvParStar.size
#print axioms Rcic.Declarative.F8Measure.EvParStar.leaves_root
#print axioms Rcic.Declarative.F8Measure.EvParStar.widen
#print axioms Rcic.Declarative.F8Measure.EvParStar.leaves_widen
#print axioms Rcic.Declarative.F8Measure.EvParStar.size_widen
#print axioms Rcic.Declarative.F8Measure.EvParStar.val_widen
#print axioms Rcic.Declarative.F8Measure.Valley
#print axioms Rcic.Declarative.F8Measure.Valley.leaves
#print axioms Rcic.Declarative.F8Measure.Valley.leaves_root
#print axioms Rcic.Declarative.F8Measure.Valley.symm
#print axioms Rcic.Declarative.F8Measure.Valley.conv
#print axioms Rcic.Declarative.F8Measure.Valley.wk
#print axioms Rcic.Declarative.F8Measure.Valley.widen
#print axioms Rcic.Declarative.F8Measure.Valley.symm_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.conv_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.wk_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.leaves_widen
#print axioms Rcic.Declarative.F8Measure.JProc
#print axioms Rcic.Declarative.F8Measure.JContract
#print axioms Rcic.Declarative.F8Measure.DProc
#print axioms Rcic.Declarative.F8Measure.DContract
#print axioms Rcic.Declarative.F8Measure.pinStar
#print axioms Rcic.Declarative.F8Measure.pinStar_leaves
#print axioms Rcic.Declarative.F8Measure.pinStar_val
#print axioms Rcic.Declarative.F8Measure.pinValley
#print axioms Rcic.Declarative.F8Measure.pinValley_leaves
#print axioms Rcic.Declarative.F8Measure.pinValley_strict
#print axioms Rcic.Declarative.F8Measure.pinValley_wk_leaves
#print axioms Rcic.Declarative.F8Measure.JProcWf
#print axioms Rcic.Declarative.F8Measure.JContractWf
#print axioms Rcic.Declarative.F8Measure.XProcWf
#print axioms Rcic.Declarative.F8Measure.XContractWf
#print axioms Rcic.Declarative.XTileQ1.illCtx
#print axioms Rcic.Declarative.XTileQ1.P₁
#print axioms Rcic.Declarative.XTileQ1.P₂
#print axioms Rcic.Declarative.XTileQ1.hf
#print axioms Rcic.Declarative.XTileQ1.hx
#print axioms Rcic.Declarative.XTileQ1.P₂_prop
#print axioms Rcic.Declarative.XTileQ1.conv_sort0
#print axioms Rcic.Declarative.XTileQ1.P₁_untypable
#print axioms Rcic.Declarative.JTileS0.root
#print axioms Rcic.Declarative.JTileS0.original_literal
#print axioms Rcic.Declarative.JTileS0.no_plain_left
#print axioms Rcic.Declarative.JTileS0.no_provenance_left
#print axioms Rcic.Declarative.JTileS0.no_unconditional_left_projection
#print axioms Rcic.Declarative.JTileS0.no_valley_provider
#print axioms Rcic.Declarative.JTileS0.no_jproc_supplier
