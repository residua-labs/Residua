import rcic.RcicNativeValleyDeco
import rcic.RcicNativeValleyEtaLeaf
import rcic.RcicNativeValleyRows
import rcic.RcicNativeDecoStrip
import rcic.RcicNativeDecoLeafIface

/-!
# Root index transport and actual application redecoration

The existing `CStep.reindex` adds a conversion at the root. Both endpoint
decorations are invariant under this operation. Consequently root reindexing
cannot implement a change to an application codomain decoration.

Two explicit fixtures use `emptyEnv`, admitted by `EnvWfT.empty`. A closed
let expression is natively zeta-convertible to `Prop`. Converting the domain
of a function through that alias gives two application typings with the
same decoration and distinct syntactic domains. Converting its codomain
instead gives two typings of one term at one index with different
decorations. Neither fixture is a countermodel to type uniqueness or
native valleys. They refute the two stated syntactic shortcuts only.

`redecorate_app` is the constructive replacement at one application node:
it transports the function child across a supplied codomain chain and then
rebuilds the application using the existing `appSide`. It does not construct
the supplied chain or a global decoration transfer theorem.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.DecoReindexAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Every link of a root type-conversion chain leaves decoration unchanged. -/
theorem decoOf_tyConvT {Γ : LCtx} {e T T' : Expr Nat}
    (h : HasTyT E n Γ e T) : (hc : TyConvT E n Γ T T') →
      decoOf (hasTyT_of_tyConvT h hc) = decoOf h
  | .refl .. => rfl
  | .of .. => rfl
  | .trans _ _ _ _ h₁ h₂ =>
      (decoOf_tyConvT (hasTyT_of_tyConvT h h₁) h₂).trans
        (decoOf_tyConvT h h₁)

/-- Root reindexing preserves the actual source decoration of the step. -/
theorem reindex_left_deco (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e e' T T' : Expr Nat}
    (s : CStep E n PEq Γ e e' T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) := by
  simpa only [CStep.reindex, CStep.leftTyped, parRedT_hasTy_left,
    parRedT_typed] using decoOf_tyConvT (s.leftTyped L hΓ) hc

/-- Root reindexing also preserves the actual target decoration. -/
theorem reindex_right_deco (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e e' T T' : Expr Nat}
    (s : CStep E n PEq Γ e e' T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).rightTyped L hΓ) = decoOf (s.rightTyped L hΓ) := by
  simpa only [CStep.reindex, CStep.rightTyped, parRedT_hasTy_right,
    parRedT_typed] using decoOf_tyConvT (s.rightTyped L hΓ) hc

/-- A desired different source decoration cannot be obtained by any root
reindexing chain, regardless of the destination index. -/
theorem reindex_cannot_redecorate (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {e e' T T' : Expr Nat}
    (s : CStep E n PEq Γ e e' T) (d : Deco e)
    (hd : decoOf (s.leftTyped L hΓ) ≠ d) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).leftTyped L hΓ) ≠ d := by
  rw [reindex_left_deco]
  exact hd

private abbrev propS : Expr Nat := .sort .zero
private abbrev typeS : Expr Nat := .sort (.succ .zero)
private abbrev aliasS : Expr Nat := .letE typeS propS (.bvar 0)
private abbrev idProp : Expr Nat := .lam propS (.bvar 0)

private def aliasTy (Γ : LCtx) : HasTyT E n Γ aliasS typeS :=
  .letE Γ typeS (.succ (.succ .zero)) propS typeS (.bvar 0)
    (.sort Γ (.succ .zero)) (.sort Γ .zero) (.bvar _ 0 _ rfl)

private def aliasConv (Γ : LCtx) : ConvT E n Γ aliasS propS typeS :=
  .zeta Γ typeS propS (.bvar 0) typeS (.succ (.succ .zero))
    (.sort Γ (.succ .zero)) (.sort Γ .zero) (.bvar _ 0 _ rfl)

private def idTy (Γ : LCtx) : HasTyT E n Γ idProp (.pi propS propS) :=
  .lam Γ propS (.succ .zero) (.bvar 0) propS (.sort Γ .zero) (.bvar _ 0 _ rfl)

private def domainConv (Γ : LCtx) :
    ConvT E n Γ (.pi propS propS) (.pi aliasS propS)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ propS aliasS propS propS (.succ .zero) (.succ .zero)
    (.symm _ _ _ _ (aliasConv Γ)) (.refl _ _ _ (.sort _ .zero))

private def codomainConv (Γ : LCtx) :
    ConvT E n Γ (.pi propS propS) (.pi propS aliasS)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ propS propS propS aliasS (.succ .zero) (.succ .zero)
    (.refl _ _ _ (.sort Γ .zero)) (.symm _ _ _ _ (aliasConv _))

private def alternateDomain (Γ : LCtx) : HasTyT E n Γ idProp (.pi aliasS propS) :=
  .conv _ _ _ _ _ (idTy Γ) (domainConv Γ)

private def alternateArgument (Γ : LCtx) : HasTyT E n Γ etaLeafP aliasS :=
  .conv _ _ _ _ _ (etaLeafP_ty Γ) (.symm _ _ _ _ (aliasConv Γ))

private def alternateCodomain (Γ : LCtx) : HasTyT E n Γ idProp (.pi propS aliasS) :=
  .conv _ _ _ _ _ (idTy Γ) (codomainConv Γ)

private def appOriginal (Γ : LCtx) : HasTyT E n Γ (.app idProp etaLeafP) propS :=
  .app Γ idProp etaLeafP propS propS (idTy Γ) (etaLeafP_ty Γ)

private def appAltered (Γ : LCtx) : HasTyT E n Γ (.app idProp etaLeafP) propS :=
  .conv _ _ aliasS propS (.succ .zero)
    (.app Γ idProp etaLeafP propS aliasS (alternateCodomain Γ) (etaLeafP_ty Γ))
    (aliasConv Γ)

private def applicationCodomain {f a : Expr Nat} : Deco (.app f a) → Expr Nat
  | .app _ _ B _ _ => B

private theorem appDecorations_ne (Γ : LCtx) :
    decoOf (appOriginal (E := E) (n := n) Γ) ≠
      decoOf (appAltered (E := E) (n := n) Γ) := by
  intro hd
  have hB : propS = aliasS := congrArg applicationCodomain hd
  cases hB

/-- Admitted-environment counterexample to extracting syntactic equality of
application domains from equality of the complete source decorations. Both
application typings have the very same result index `instantiate0 a B`. -/
theorem admitted_distinct_app_domains :
    Nonempty (EnvWfT emptyEnv) ∧
      ∃ (f a A₀ A₁ B : Expr Nat)
        (hf₀ : HasTyT emptyEnv 0 [] f (.pi A₀ B))
        (hf₁ : HasTyT emptyEnv 0 [] f (.pi A₁ B))
        (ha₀ : HasTyT emptyEnv 0 [] a A₀)
        (ha₁ : HasTyT emptyEnv 0 [] a A₁),
        A₀ ≠ A₁ ∧
        decoOf (HasTyT.app [] f a A₀ B hf₀ ha₀) =
          decoOf (HasTyT.app [] f a A₁ B hf₁ ha₁) := by
  refine ⟨⟨.empty⟩, idProp, etaLeafP, propS, aliasS, propS,
    idTy [], alternateDomain [], etaLeafP_ty [], alternateArgument [], ?_, rfl⟩
  intro h
  cases h

/-- Two actual typings of one closed term at one index in an admitted
environment have different decorations. Every root typing transport of the
first still has a decoration different from the second. -/
theorem admitted_reindex_not_transfer :
    Nonempty (EnvWfT emptyEnv) ∧
      ∃ (e T : Expr Nat) (h₀ h₁ : HasTyT emptyEnv 0 [] e T),
        decoOf h₀ ≠ decoOf h₁ ∧
        ∀ (T' : Expr Nat) (hc : TyConvT emptyEnv 0 [] T T'),
          decoOf (hasTyT_of_tyConvT h₀ hc) ≠ decoOf h₁ := by
  refine ⟨⟨.empty⟩, .app idProp etaLeafP, propS, appOriginal [], appAltered [],
    appDecorations_ne [], ?_⟩
  intro T' hc
  rw [decoOf_tyConvT]
  exact appDecorations_ne []

private def aliasAppStep :
    CStep emptyEnv 0 PEq [] (.app idProp etaLeafP) (.app idProp etaLeafP) propS :=
  let hf := alternateDomain (E := emptyEnv) (n := 0) []
  let ha := alternateArgument (E := emptyEnv) (n := 0) []
  let ht := HasTyT.app [] idProp etaLeafP aliasS propS hf ha
  ⟨.app [] idProp idProp etaLeafP etaLeafP aliasS propS (.pi aliasS propS)
      (.succ .zero) (.succ .zero) (.refl _ _ _ hf) (.refl _ _)
      (.sort _ .zero) (.sort _ .zero) (.refl _ _ _ ha) ht,
    .app (.refl _ _ _ ht) (.refl (.refl _ _ _ hf)) (.refl (.refl _ _ _ ha))⟩

private def identityBetaStep :
    CStep emptyEnv 0 PEq [] (.app idProp etaLeafP) etaLeafP propS :=
  let hb : HasTyT emptyEnv 0 [.assumption propS] (.bvar 0) propS := .bvar _ 0 _ rfl
  let ha := etaLeafP_ty (E := emptyEnv) (n := 0) []
  ⟨.beta [] propS (.bvar 0) (.bvar 0) etaLeafP etaLeafP propS
      (.succ .zero) (.succ .zero) (.succ .zero) (.sort [] .zero)
      (.sort _ .zero) (.sort [] .zero) (.refl _ _ _ hb) (.refl _ _ _ ha) ha,
    .beta (.beta [] propS (.bvar 0) etaLeafP propS (.succ .zero) (.sort [] .zero) hb ha)
      (.refl (.refl _ _ _ hb)) (.refl (.refl _ _ _ ha))⟩

/-- The written domain of an application or beta node, with `false`
tagging application and `true` tagging beta. Other constructors have no
entry. The index-general accessor makes the following concrete shape
counterexample independent of dependent pattern-match elaboration. -/
def appBetaDomain : {Γ : LCtx} → {b e T : Expr Nat} →
    ParRedT PEq E n Γ b e T → Option (Bool × Expr Nat)
  | _, _, _, _, .app _ _ _ _ _ A .. => some (false, A)
  | _, _, _, _, .beta _ A .. => some (true, A)
  | _, _, _, _, _ => none

/-- The domain mismatch occurs in actual certified `app × beta` steps,
with a common source, common index, and equal actual source decorations.
The app node writes a domain distinct from `Prop`; the beta node writes
`Prop`. The lawful leaf interface is concretely instantiated in emptyEnv. -/
theorem admitted_app_beta_domain_mismatch :
    Nonempty (EnvWfT emptyEnv) ∧
    ∃ (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
      (L : LeafIface emptyEnv 0 PEq)
      (p : CStep emptyEnv 0 PEq []
        (.app (.lam (.sort .zero) (.bvar 0)) etaLeafP)
        (.app (.lam (.sort .zero) (.bvar 0)) etaLeafP) (.sort .zero))
      (q : CStep emptyEnv 0 PEq []
        (.app (.lam (.sort .zero) (.bvar 0)) etaLeafP) etaLeafP (.sort .zero)),
      decoOf (p.leftTyped L .nil) = decoOf (q.leftTyped L .nil) ∧
      (∃ A : Expr Nat, appBetaDomain p.step = some (false, A) ∧ A ≠ .sort .zero) ∧
      appBetaDomain q.step = some (true, .sort .zero) := by
  obtain ⟨PEq, L, _, _, _, _, _⟩ := DecoLeafIfaceAudit.irr_source_deco_counterexample
  refine ⟨⟨.empty⟩, PEq, L, aliasAppStep, identityBetaStep, rfl,
    ⟨aliasS, rfl, ?_⟩, rfl⟩
  intro h
  cases h

/-- Coherence is not automatic for existing certified stars. Even a star
of two reflexive pieces may use different typings at its middle term.
This counterexample again supplies its actual lawful leaf interface. -/
theorem admitted_incoherent_star :
    Nonempty (EnvWfT emptyEnv) ∧
    ∃ (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
      (L : LeafIface emptyEnv 0 PEq) (e T : Expr Nat)
      (s : CStar emptyEnv 0 PEq [] e e T),
      ¬ DecoStarAudit.Coherent L .nil s := by
  obtain ⟨PEq, L, _, _, _, _, _⟩ := DecoLeafIfaceAudit.irr_source_deco_counterexample
  let h₀ := appOriginal (E := emptyEnv) (n := 0) []
  let h₁ := appAltered (E := emptyEnv) (n := 0) []
  refine ⟨⟨.empty⟩, PEq, L, .app idProp etaLeafP, propS,
    .tail ⟨.refl _ _ _ h₀, .refl (.refl _ _ _ h₀)⟩ (.refl _ _ _ h₁), ?_⟩
  intro hs
  exact appDecorations_ne [] hs.1

/-- Rebuild an application at a new codomain annotation by transporting its
function child and invoking the existing application constructor. The
codomain chain is supplied; no Pi injectivity or uniqueness is assumed. -/
def redecorate_app (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B B' : Expr Nat} {u v' : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB' : HasTyT E n (.assumption A :: Γ) B' (.sort v'))
    (hc : TyConvT E n (.assumption A :: Γ) B B')
    (sf : CStep E n PEq Γ f g (.pi A B)) (sa : CStep E n PEq Γ a b A) :
    CStep E n PEq Γ (.app f a) (.app g b) (instantiate0 a B') :=
  let sf' := sf.reindex (tyConvT_pi_codom hA hc)
  let hf := sf'.leftTyped L hΓ
  let ha := sa.leftTyped L hΓ
  appSide hW L hΓ (.refl _ f _ hf) (.refl _ _) hB'
    (.refl _ a A ha) (.refl (.refl _ a A ha)) sf' sa

/-- The rebuilt application really changes its source annotation to `B'`;
the two original child source decorations are retained. -/
theorem redecorate_app_source (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B B' : Expr Nat} {u v' : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB' : HasTyT E n (.assumption A :: Γ) B' (.sort v'))
    (hc : TyConvT E n (.assumption A :: Γ) B B')
    (sf : CStep E n PEq Γ f g (.pi A B)) (sa : CStep E n PEq Γ a b A) :
    decoOf ((redecorate_app hW L hΓ hA hB' hc sf sa).leftTyped L hΓ) =
      .app f a B' (decoOf (sf.leftTyped L hΓ)) (decoOf (sa.leftTyped L hΓ)) := by
  unfold redecorate_app appSide
  dsimp only
  simp only [CStep.reindex, CStep.leftTyped, parRedT_hasTy_left,
    parRedT_typed, decoOf_tyConvT, decoOf]

#print axioms decoOf_tyConvT
#print axioms reindex_left_deco
#print axioms reindex_right_deco
#print axioms reindex_cannot_redecorate
#print axioms admitted_distinct_app_domains
#print axioms admitted_reindex_not_transfer
#print axioms admitted_app_beta_domain_mismatch
#print axioms admitted_incoherent_star
#print axioms redecorate_app
#print axioms redecorate_app_source

end Rcic.Declarative.NativeValleys.DecoReindexAudit
