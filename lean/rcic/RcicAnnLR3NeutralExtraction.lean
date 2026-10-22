import rcic.RcicAnnLR3TypedArms

/-!
# Generic-context extraction from explicit neutral support

This file composes two separate inputs: a realised-context fundamental
theorem and a code decoder with a type-indexed reflection operation.
It does not construct either input or assert them for all admitted source
environments. In particular this is a conditional extraction consumer,
not a new source-soundness supplier.

The generic environment is a function of the valuation and source context,
independent of their well-formedness derivations. Assumptions receive a
reflected neutral at their interpreted type. Let entries receive their
stored value's image, so their required PER agreement is obtained from the
typing part of the fundamental theorem. No witness selection is used.

The existing exact `SortMember` and `TypeDefined` predicates, annotated
extraction, and independent raw-subject native extraction are preserved.
Native source admission remains an explicit input of its fundamental
theorem and of the resulting `SortUniq` theorem. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NeutralExtraction

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TypedArms

/-- Additional algebra required by generic context realisation. The decoder
returns an element PER, not merely a full-tag observation. Reflection must
belong to every PER assigned to the given type value. -/
structure NeutralSupport (M : AnnSemantics) where
  decode : ∀ {k l : Option Nat} {R : Relation} {x : Value},
    M.Code l (universeValue k) R → Member R x → ∃ S : Relation, M.Code k x S
  reflect : Value → Nat → Value
  reflect_member : ∀ {k : Option Nat} {V : Value} {R : Relation},
    M.Code k V R → ∀ a : Nat, Member R (reflect V a)

/-- The atom label is a context level, stable when later entries are added.
Let entries use their stored value; membership alone would not justify
replacing that value by an unrelated fresh neutral. -/
def generic {M : AnnSemantics} (S : NeutralSupport M) (ν : Valuation) : LCtxA → EnvI
  | [] => EnvI.bot
  | .assumption A :: Γ =>
      let ρ := generic S ν Γ
      EnvI.cons (S.reflect (M.image ν Γ ρ A) Γ.length) ρ
  | .letBinding A v :: Γ =>
      let ρ := generic S ν Γ
      EnvI.cons (M.image ν Γ ρ v) ρ

/-- A compositional coverage theorem. Its typing input is the typing half
of the fundamental theorem, which still has to be supplied by a model. -/
theorem generic_realises_of_typing {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M)
    (hTy : ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E I n Γ e A → TyGoal M E I n Γ e A) :
    ∀ (ν : Valuation) (Γ : LCtxA), CtxWfA E I n Γ →
      Realises M ν Γ (generic S ν Γ) := by
  intro ν Γ hΓ
  induction hΓ with
  | nil => exact .nil _
  | assumption hΓ hA ih =>
      obtain ⟨k, R, hc, _, hm⟩ := hTy hA hΓ ν _ ih
      rw [M.sort_image] at hc
      obtain ⟨T, hT⟩ := S.decode hc hm
      exact .assumption ih hT (S.reflect_member hT _)
  | letBinding hΓ hA hv ih =>
      obtain ⟨k, R, hc, _, hm⟩ := hTy hv hΓ ν _ ih
      exact .letBinding ih hc hm hm

theorem generic_realises {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M) (hF : Fundamental M E I n)
    (ν : Valuation) (Γ : LCtxA) (hΓ : CtxWfA E I n Γ) :
    Realises M ν Γ (generic S ν Γ) :=
  generic_realises_of_typing S hF.1 ν Γ hΓ

theorem generic_representative {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M) (hF : Fundamental M E I n) :
    Representative M E I n (generic S) :=
  generic_realises S hF

def genericImage {M : AnnSemantics} (S : NeutralSupport M) : AnnImage :=
  fun ν Γ e => M.image ν Γ (generic S ν Γ) e

/-- Existing exact membership extraction, with coverage obtained from the
explicit decoder/reflection algebra and fundamental theorem. -/
theorem ann_membership {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M) (hF : Fundamental M E I n) :
    AnnSortMembershipSound E I n (genericImage S) :=
  ann_membership_of_fundamental hF (generic S) (generic_representative S hF)

theorem ann_sortUniq {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M) (hF : Fundamental M E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u v : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (hv : HasTyA E I n Γ A (.sort v)) : eqN u v :=
  ann_sortUniq_of_membership (ann_membership S hF) hΓ hu hv

theorem ann_zsc {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralSupport M) (hF : Fundamental M E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (h0 : HasTyA E I n Γ A (.sort .zero)) :
    eqN u .zero :=
  ann_sortUniq S hF hΓ hu h0

/-- Admission-wide composition retains the actual source admission and
concrete iota interface. The two global producer inputs remain explicit. -/
theorem ann_membership_of_all_admitted_fundamental
    (models : ResolvedEnvA → AnnSemantics)
    (support : ∀ E : ResolvedEnvA, NeutralSupport (models E))
    (hF : AllAdmittedFundamental models) (E : ResolvedEnvA)
    (hE : EnvWfA (iotaIfaceA E) E) (n : Nat) :
    AnnSortMembershipSound E (iotaIfaceA E) n (genericImage (support E)) :=
  ann_membership (support E) (hF E hE n)

/-- The native analogue uses an independently supplied raw-subject model.
No annotation or annotation derivation is selected by this interface. -/
structure NativeNeutralSupport (M : NativeSemantics) where
  decode : ∀ {k l : Option Nat} {R : Relation} {x : Value},
    M.Code l (universeValue k) R → Member R x → ∃ S : Relation, M.Code k x S
  reflect : Value → Nat → Value
  reflect_member : ∀ {k : Option Nat} {V : Value} {R : Relation},
    M.Code k V R → ∀ a : Nat, Member R (reflect V a)

def nativeGeneric {M : NativeSemantics} (S : NativeNeutralSupport M)
    (ν : Valuation) : LCtx → EnvI
  | [] => EnvI.bot
  | .assumption A :: Γ =>
      let ρ := nativeGeneric S ν Γ
      EnvI.cons (S.reflect (M.image ν Γ ρ A) Γ.length) ρ
  | .letBinding A v :: Γ =>
      let ρ := nativeGeneric S ν Γ
      EnvI.cons (M.image ν Γ ρ v) ρ

theorem native_generic_realises_of_typing {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M)
    (hTy : ∀ {Γ : LCtx} {e A : Expr Nat}, CtxWfT E n Γ → HasTyT E n Γ e A →
      ∀ (ν : Valuation) (ρ : EnvI), NativeRealises M ν Γ ρ →
        NativeJudgment M ν Γ ρ e e A) :
    ∀ (ν : Valuation) (Γ : LCtx), CtxWfT E n Γ →
      NativeRealises M ν Γ (nativeGeneric S ν Γ) := by
  intro ν Γ hΓ
  induction hΓ with
  | nil => exact .nil _
  | assumption _ _ _ hΓ hA ih =>
      obtain ⟨k, R, hc, _, hm⟩ := hTy hΓ hA ν _ ih
      rw [M.sort_image] at hc
      obtain ⟨T, hT⟩ := S.decode hc hm
      exact .assumption ih hT (S.reflect_member hT _)
  | letBinding _ _ _ _ hΓ hA hv ih =>
      obtain ⟨k, R, hc, _, hm⟩ := hTy hΓ hv ν _ ih
      exact .letBinding ih hc hm hm

theorem native_generic_realises {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M) (hF : NativeFundamental M E n)
    (hE : EnvWfT E) (ν : Valuation) (Γ : LCtx) (hΓ : CtxWfT E n Γ) :
    NativeRealises M ν Γ (nativeGeneric S ν Γ) :=
  native_generic_realises_of_typing S (hF hE).1 ν Γ hΓ

theorem native_generic_representative {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M) (hF : NativeFundamental M E n) :
    NativeRepresentative M E n (nativeGeneric S) :=
  fun hE => native_generic_realises S hF hE

def nativeGenericImage {M : NativeSemantics} (S : NativeNeutralSupport M) : NativeImage :=
  fun ν Γ e => M.image ν Γ (nativeGeneric S ν Γ) e

theorem native_membership {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M) (hF : NativeFundamental M E n) :
    NativeSortMembershipSound E n (nativeGenericImage S) :=
  native_membership_of_fundamental hF (nativeGeneric S) (native_generic_representative S hF)

theorem native_sortUniq {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M) (hF : NativeFundamental M E n)
    (hE : EnvWfT E) : SortUniq E n :=
  native_sortUniq_of_membership hE (native_membership S hF)

theorem native_zsc {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NativeNeutralSupport M) (hF : NativeFundamental M E n) :
    HostPropAudit.ZeroSortCoherence E n :=
  native_zsc_of_membership (native_membership S hF)

/-- An actual constructor-contract supplier, independent of neutral support
or a global fundamental theorem. Exact level equality identifies the two
sort images in the already supplied sort self-judgment. -/
theorem conv_sorts_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) : Conv_sorts M E I n := by
  intro Γ l₁ l₂ h hΓ ν ρ hρ
  obtain ⟨k, R, hc, hd, hm⟩ := sort_goal M E I n Γ l₁ hΓ ν ρ hρ
  have he : M.image ν Γ ρ (.sort l₁) = M.image ν Γ ρ (.sort l₂) := by
    rw [M.sort_image, M.sort_image, h ν]
  refine ⟨k, R, hc, hd, ?_⟩
  rw [← he]
  exact hm

end Rcic.Declarative.Ann.LR3.NeutralExtraction
