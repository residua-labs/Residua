import rcic.RcicAnnLR3UnitLevels

/-!
# SortUniq, and then ZSC, from exact noncumulative model membership

These are explicitly consumers of source membership soundness and a defined
type-image theorem. Disjointness and exact evaluated-code injectivity are
supplied in UnitLevels. No record of global source soundness is asserted to
be inhabited. In particular the native image is independently indexed by a
raw subject, not by a choice of annotation or typing derivation.

The native conclusion is full `SortUniq`, not just a zero bit. Its ZSC and
decorated-route consequences are compositions with landed consumers. Their
`LeafIface` and `CDiamond` premises remain explicit. No erasure/CL theorem,
`SortOfA3` witness or annotated codomain conversion is obtained here.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys

abbrev AnnImage := Valuation → LCtxA → ExprA → Value
abbrev NativeImage := Valuation → LCtx → Expr Nat → Value

/-- Plain soundness at a sort carrier plus definedness of the type image.
The image function is fixed before, and does not take a typing derivation. -/
def AnnSortMembershipSound (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (V : AnnImage) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (A : ExprA) (u : Level),
    CtxWfA E I n Γ → HasTyA E I n Γ A (.sort u) →
    SortMember (eval ν u) (V ν Γ A) ∧ TypeDefined (V ν Γ A)

/-- Full annotated pairwise sort uniqueness from ordinary model membership.
This is not an instance of `AnnSortMembershipSound`. -/
theorem ann_sortUniq_of_membership {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {V : AnnImage} (hS : AnnSortMembershipSound E I n V)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u v : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (hv : HasTyA E I n Γ A (.sort v)) : eqN u v := by
  intro ν
  have su := hS ν Γ A u hΓ hu
  have sv := hS ν Γ A v hΓ hv
  exact sortMember_unique su.1 sv.1 su.2

theorem ann_zsc_of_membership {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {V : AnnImage} (hS : AnnSortMembershipSound E I n V)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (h0 : HasTyA E I n Γ A (.sort .zero)) : eqN u .zero :=
  ann_sortUniq_of_membership hS hΓ hu h0

/-- The same soundness port on native syntax. No conversion from arbitrary
native typings to a common annotation is assumed silently. -/
def NativeSortMembershipSound (E : ResolvedEnv) (n : Nat) (V : NativeImage) : Prop :=
  EnvWfT E → ∀ (ν : Valuation) (Γ : LCtx) (A : Expr Nat) (u : Level),
    CtxWfT E n Γ → HasTyT E n Γ A (.sort u) →
    SortMember (eval ν u) (V ν Γ A) ∧ TypeDefined (V ν Γ A)

theorem native_sortUniq_of_membership {E : ResolvedEnv} {n : Nat} {V : NativeImage}
    (hW : EnvWfT E) (hS : NativeSortMembershipSound E n V) : SortUniq E n := by
  intro Γ hΓ A u v hu hv ν
  have su := hS hW ν Γ A u hΓ hu
  have sv := hS hW ν Γ A v hΓ hv
  exact sortMember_unique su.1 sv.1 su.2

/-- Exactly the native ZSC interface used by host-Prop and decorated rows. -/
theorem native_zsc_of_membership {E : ResolvedEnv} {n : Nat} {V : NativeImage}
    (hS : NativeSortMembershipSound E n V) : HostPropAudit.ZeroSortCoherence E n := by
  intro hW
  exact zsc_of_sortUniq (native_sortUniq_of_membership hW hS) hW

theorem native_sort_peq_excluded {E : ResolvedEnv} {n : Nat} {V : NativeImage}
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (hW : EnvWfT E) (L : LeafIface E n PEq) (hS : NativeSortMembershipSound E n V)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u : Level} {q T : Expr Nat}
    (h : PEq Γ (.sort u) q T) : False :=
  peq_sort_source_false hW L (native_zsc_of_membership hS) hΓ h

/-- The single-conversion decorated consumer needs ZSC, not annotated
synthesis or Type Exchange. The diamond is still an explicit premise. -/
def native_pi_conversion_of_membership {E : ResolvedEnv} {n : Nat} {V : NativeImage}
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (hW : EnvWfT E) (L : LeafIface E n PEq) (D : CDiamond E n PEq)
    (hS : NativeSortMembershipSound E n V) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' T : Expr Nat} (c : ConvT E n Γ (.pi A B) (.pi A' B') T) :
    TyConvT E n Γ A A' × TyConvT E n (.assumption A :: Γ) B B' :=
  convT_pi_inv_of_diamond hW L D (native_zsc_of_membership hS) hΓ c

/-- For a full heterogeneous type-conversion chain, retain the stronger
SortUniq output and use the landed SortRetype composition. -/
def native_pi_chain_of_membership {E : ResolvedEnv} {n : Nat} {V : NativeImage}
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (hW : EnvWfT E) (L : LeafIface E n PEq) (D : CDiamond E n PEq)
    (hS : NativeSortMembershipSound E n V) : PiInj E n :=
  piInj_of_diamond_sortUniq hW L D (native_sortUniq_of_membership hW hS)

end Rcic.Declarative.Ann.LR3.UnitModel
