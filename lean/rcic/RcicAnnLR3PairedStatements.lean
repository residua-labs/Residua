import rcic.RcicAnnLR3NeutralExtraction

/-!
# Paired semantic statements and diagonal extraction

The two worlds retain their actual valuations, environments, type images,
and element PERs. A code pair includes an explicit transport equivalence
between those PERs. Paired assumptions carry a cross-world relation; paired
lets additionally agree with their stored values in both worlds.

This file supplies the algebra of this interface and its diagonal
projection. `PairedFundamental` is a statement, not an asserted source
soundness theorem. Generic coverage is derived from the existing explicit
`NeutralSupport` and the diagonal theorem; neither a decoder nor a
representative environment is hidden in the interface. Native extraction
uses its independent raw-subject image and explicit source admission.
No reverse K condition occurs in these statements. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.PairedStatements

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- Agreement at every level variable, retaining the entire `Option Nat`
evaluation domain, including `none`. -/
def ValuationRel (ν μ : Valuation) : Prop := ∀ i : Nat, ν i = μ i

theorem ValuationRel.refl (ν : Valuation) : ValuationRel ν ν := fun _ => rfl

theorem ValuationRel.symm {ν μ : Valuation} (h : ValuationRel ν μ) :
    ValuationRel μ ν := fun i => (h i).symm

theorem ValuationRel.trans {ν μ ξ : Valuation}
    (h : ValuationRel ν μ) (g : ValuationRel μ ξ) : ValuationRel ν ξ :=
  fun i => (h i).trans (g i)

theorem eval_of_valuationRel {ν μ : Valuation} (h : ValuationRel ν μ) (l : Level) :
    eval ν l = eval μ l := by
  induction l <;> simp_all [eval, ValuationRel]

/-- Both type codes have the same exact level. Transport is actual
equivalence of their element relations, rather than an unproved inference
from raw type-image equality or source conversion. -/
structure CodePair (C : CodeSystem) (k : Option Nat) (V W : Value)
    (R S : Relation) : Prop where
  left_code : C.Code k V R
  right_code : C.Code k W S
  transport : Same R S

theorem code_index_unique {C : CodeSystem} {k l : Option Nat}
    {V : Value} {R S : Relation} (h : C.Code k V R) (g : C.Code l V S) : k = l :=
  sortMember_unique (C.level h) (C.level g) (C.defined h)

theorem CodePair.diagonal {C : CodeSystem} {k : Option Nat} {V : Value}
    {R : Relation} (h : C.Code k V R) : CodePair C k V V R R :=
  ⟨h, h, fun _ _ => Iff.rfl⟩

theorem CodePair.symm {C : CodeSystem} {k : Option Nat} {V W : Value}
    {R S : Relation} (h : CodePair C k V W R S) : CodePair C k W V S R :=
  ⟨h.right_code, h.left_code, fun x y => (h.transport x y).symm⟩

theorem CodePair.trans {C : CodeSystem} {k l : Option Nat} {V W Z : Value}
    {R S T U : Relation} (h : CodePair C k V W R S)
    (g : CodePair C l W Z T U) : CodePair C k V Z R U := by
  have hkl : k = l := code_index_unique h.right_code g.left_code
  cases hkl
  refine ⟨h.left_code, g.right_code, ?_⟩
  intro x y
  exact (h.transport x y).trans
    ((C.coherent h.right_code g.left_code x y).trans (g.transport x y))

theorem CodePair.to_right {C : CodeSystem} {k : Option Nat} {V W : Value}
    {R S : Relation} (h : CodePair C k V W R S) {x y : Value} (hr : R x y) : S x y :=
  (h.transport x y).mp hr

theorem CodePair.to_left {C : CodeSystem} {k : Option Nat} {V W : Value}
    {R S : Relation} (h : CodePair C k V W R S) {x y : Value} (hs : S x y) : R x y :=
  (h.transport x y).mpr hs

def RelatedCode (C : CodeSystem) (V W : Value) : Prop :=
  ∃ (k : Option Nat) (R S : Relation), CodePair C k V W R S

theorem RelatedCode.of_code {C : CodeSystem} {k : Option Nat} {V : Value}
    {R : Relation} (h : C.Code k V R) : RelatedCode C V V :=
  ⟨k, R, R, CodePair.diagonal h⟩

theorem RelatedCode.symm {C : CodeSystem} {V W : Value}
    (h : RelatedCode C V W) : RelatedCode C W V := by
  obtain ⟨k, R, S, hc⟩ := h
  exact ⟨k, S, R, hc.symm⟩

theorem RelatedCode.trans {C : CodeSystem} {V W Z : Value}
    (h : RelatedCode C V W) (g : RelatedCode C W Z) : RelatedCode C V Z := by
  obtain ⟨k, R, S, hc⟩ := h
  obtain ⟨l, T, U, hd⟩ := g
  exact ⟨k, R, U, hc.trans hd⟩

/-- Code relatedness transports every presentation of the two element
relations, using coherence at each endpoint. -/
theorem RelatedCode.transport {C : CodeSystem} {V W : Value}
    {k l : Option Nat} {R S : Relation} (h : RelatedCode C V W)
    (hv : C.Code k V R) (hw : C.Code l W S) : Same R S := by
  obtain ⟨j, T, U, hc⟩ := h
  intro x y
  exact (C.coherent hv hc.left_code x y).trans
    ((hc.transport x y).trans (C.coherent hc.right_code hw x y))

/-- A semantic universe relation must decode to related element codes.
This is an explicit additional algebra law, not a source conversion or
fundamental theorem. The conclusion retains the exact universe index. -/
structure UniverseTransport (C : CodeSystem) : Prop where
  relate : ∀ {k : Option Nat} {V W : Value}, C.universePER k V W →
    ∃ R S : Relation, CodePair C k V W R S

/-- Proof irrelevance is an explicit property of the element relation
assigned to a code at exact level zero. -/
structure PropIrrelevance (C : CodeSystem) : Prop where
  relate : ∀ {V : Value} {R : Relation} {x y : Value},
    C.Code (some 0) V R → Member R x → Member R y → R x y

/-- Each declared type is interpreted in its corresponding outer world.
The right stored-value agreement uses the right PER explicitly. -/
inductive PairedRealises (M : AnnSemantics) (ν μ : Valuation) :
    LCtxA → EnvI → EnvI → Prop
  | nil (ρ σ : EnvI) : PairedRealises M ν μ [] ρ σ
  | assumption {Γ : LCtxA} {ρ σ : EnvI} {A : ExprA} {x y : Value}
      {k : Option Nat} {R S : Relation}
      (tail : PairedRealises M ν μ Γ ρ σ)
      (codes : CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S)
      (related : R x y) :
      PairedRealises M ν μ (.assumption A :: Γ) (EnvI.cons x ρ) (EnvI.cons y σ)
  | letBinding {Γ : LCtxA} {ρ σ : EnvI} {A v : ExprA} {x y : Value}
      {k : Option Nat} {R S : Relation}
      (tail : PairedRealises M ν μ Γ ρ σ)
      (codes : CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S)
      (related : R x y)
      (left_value : R x (M.image ν Γ ρ v))
      (right_value : S y (M.image μ Γ σ v)) :
      PairedRealises M ν μ (.letBinding A v :: Γ) (EnvI.cons x ρ) (EnvI.cons y σ)

theorem PairedRealises.left {M : AnnSemantics} {ν μ : Valuation} {Γ : LCtxA}
    {ρ σ : EnvI} (h : PairedRealises M ν μ Γ ρ σ) : Realises M ν Γ ρ := by
  induction h with
  | nil ρ σ => exact .nil ρ
  | assumption tail codes related ih =>
      exact .assumption ih codes.left_code
        (TypedPER.left_member (M.lawful codes.left_code) related)
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.left_code
        (TypedPER.left_member (M.lawful codes.left_code) related) left_value

theorem PairedRealises.right {M : AnnSemantics} {ν μ : Valuation} {Γ : LCtxA}
    {ρ σ : EnvI} (h : PairedRealises M ν μ Γ ρ σ) : Realises M μ Γ σ := by
  induction h with
  | nil ρ σ => exact .nil σ
  | assumption tail codes related ih =>
      exact .assumption ih codes.right_code
        (codes.to_right (TypedPER.right_member (M.lawful codes.left_code) related))
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.right_code
        (codes.to_right (TypedPER.right_member (M.lawful codes.left_code) related)) right_value

theorem PairedRealises.diagonal {M : AnnSemantics} {ν : Valuation} {Γ : LCtxA}
    {ρ : EnvI} (h : Realises M ν Γ ρ) : PairedRealises M ν ν Γ ρ ρ := by
  induction h with
  | nil ρ => exact .nil ρ ρ
  | assumption tail code member ih =>
      exact .assumption ih (CodePair.diagonal code) member
  | letBinding tail code member value ih =>
      exact .letBinding ih (CodePair.diagonal code) member value value

theorem PairedRealises.symm {M : AnnSemantics} {ν μ : Valuation} {Γ : LCtxA}
    {ρ σ : EnvI} (h : PairedRealises M ν μ Γ ρ σ) : PairedRealises M μ ν Γ σ ρ := by
  induction h with
  | nil ρ σ => exact .nil σ ρ
  | assumption tail codes related ih =>
      exact .assumption ih codes.symm (codes.to_right ((M.lawful codes.left_code).symm related))
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.symm (codes.to_right ((M.lawful codes.left_code).symm related))
        right_value left_value

theorem PairedRealises.left_diagonal {M : AnnSemantics} {ν μ : Valuation} {Γ : LCtxA}
    {ρ σ : EnvI} (h : PairedRealises M ν μ Γ ρ σ) : PairedRealises M ν ν Γ ρ ρ :=
  PairedRealises.diagonal h.left

theorem PairedRealises.right_diagonal {M : AnnSemantics} {ν μ : Valuation} {Γ : LCtxA}
    {ρ σ : EnvI} (h : PairedRealises M ν μ Γ ρ σ) : PairedRealises M μ μ Γ σ σ :=
  PairedRealises.diagonal h.right

/-- The paired judgment retains both actual type images and the transport
between their element PERs. Definedness follows from its two code proofs. -/
def PairedJudgment (M : AnnSemantics) (ν μ : Valuation) (Γ : LCtxA) (ρ σ : EnvI)
    (a b A : ExprA) : Prop :=
  ∃ (k : Option Nat) (R S : Relation),
    CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S ∧
      R (M.image ν Γ ρ a) (M.image μ Γ σ b)

theorem PairedJudgment.type_related {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {a b A : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A) :
    RelatedCode M.toCodeSystem (M.image ν Γ ρ A) (M.image μ Γ σ A) := by
  obtain ⟨k, R, S, hc, _⟩ := h
  exact ⟨k, R, S, hc⟩

/-- A judgment between types in a universe gives related type codes only
when the universe-to-element transport law is supplied explicitly. -/
theorem PairedJudgment.related_types {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {A B : ExprA} {u : Level}
    (U : UniverseTransport M.toCodeSystem)
    (h : PairedJudgment M ν μ Γ ρ σ A B (.sort u)) :
    RelatedCode M.toCodeSystem (M.image ν Γ ρ A) (M.image μ Γ σ B) := by
  obtain ⟨l, R, S, hc, hr⟩ := h
  have hcode : M.Code l (universeValue (eval ν u)) R := by
    simpa only [M.sort_image] using hc.left_code
  have hu : M.universePER (eval ν u) (M.image ν Γ ρ A) (M.image μ Γ σ B) :=
    (M.coherent hcode (M.universe_code _) _ _).mp hr
  obtain ⟨T, V, ht⟩ := U.relate hu
  exact ⟨eval ν u, T, V, ht⟩

/-- The two type changes are transported in their corresponding worlds.
No equality of raw type images is assumed. -/
theorem PairedJudgment.transport_type {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {a b A B : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A)
    (left : RelatedCode M.toCodeSystem (M.image ν Γ ρ A) (M.image ν Γ ρ B))
    (right : RelatedCode M.toCodeSystem (M.image μ Γ σ A) (M.image μ Γ σ B)) :
    PairedJudgment M ν μ Γ ρ σ a b B := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  have middle : RelatedCode M.toCodeSystem (M.image ν Γ ρ A) (M.image μ Γ σ A) :=
    ⟨k, R, S, hc⟩
  obtain ⟨l, T, U, hd⟩ := left.symm.trans (middle.trans right)
  exact ⟨l, T, U, hd, (left.transport hc.left_code hd.left_code _ _).mp hr⟩

theorem PairedJudgment.symm {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {a b A : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A) :
    PairedJudgment M μ ν Γ σ ρ b a A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, S, R, hc.symm, hc.to_right ((M.lawful hc.left_code).symm hr)⟩

theorem PairedJudgment.trans {M : AnnSemantics} {ν μ ξ : Valuation}
    {Γ : LCtxA} {ρ σ τ : EnvI} {a b c A : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A)
    (g : PairedJudgment M μ ξ Γ σ τ b c A) :
    PairedJudgment M ν ξ Γ ρ τ a c A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  obtain ⟨l, T, U, hd, hs⟩ := g
  have hmid := (M.coherent hd.left_code hc.right_code _ _).mp hs
  exact ⟨k, R, U, hc.trans hd, (M.lawful hc.left_code).trans hr (hc.to_left hmid)⟩

theorem PairedJudgment.left_typing {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {a b A : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A) : Judgment M ν Γ ρ a a A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, R, hc.left_code, M.defined hc.left_code,
    TypedPER.left_member (M.lawful hc.left_code) hr⟩

theorem PairedJudgment.right_typing {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {a b A : ExprA}
    (h : PairedJudgment M ν μ Γ ρ σ a b A) : Judgment M μ Γ σ b b A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, S, hc.right_code, M.defined hc.right_code,
    hc.to_right (TypedPER.right_member (M.lawful hc.left_code) hr)⟩

theorem PairedJudgment.diagonal {M : AnnSemantics} {ν : Valuation}
    {Γ : LCtxA} {ρ : EnvI} {a b A : ExprA}
    (h : PairedJudgment M ν ν Γ ρ ρ a b A) : Judgment M ν Γ ρ a b A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, R, hc.left_code, M.defined hc.left_code, hr⟩

theorem PairedJudgment.of_diagonal {M : AnnSemantics} {ν : Valuation}
    {Γ : LCtxA} {ρ : EnvI} {a b A : ExprA}
    (h : Judgment M ν Γ ρ a b A) : PairedJudgment M ν ν Γ ρ ρ a b A := by
  obtain ⟨k, R, hc, _, hr⟩ := h
  exact ⟨k, R, R, CodePair.diagonal hc, hr⟩

theorem paired_judgment_diagonal_iff {M : AnnSemantics} {ν : Valuation}
    {Γ : LCtxA} {ρ : EnvI} {a b A : ExprA} :
    PairedJudgment M ν ν Γ ρ ρ a b A ↔ Judgment M ν Γ ρ a b A :=
  ⟨PairedJudgment.diagonal, PairedJudgment.of_diagonal⟩

def PairedTyGoal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (e A : ExprA) : Prop :=
  CtxWfA E I n Γ → ∀ ν μ ρ σ, ValuationRel ν μ →
    PairedRealises M ν μ Γ ρ σ → PairedJudgment M ν μ Γ ρ σ e e A

def PairedConvGoal (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (a b A : ExprA) : Prop :=
  CtxWfA E I n Γ → ∀ ν μ ρ σ, ValuationRel ν μ →
    PairedRealises M ν μ Γ ρ σ → PairedJudgment M ν μ Γ ρ σ a b A

/-- The binary mutual source statement is a producer obligation. -/
def PairedFundamental (M : AnnSemantics) (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  (∀ {Γ e A}, HasTyA E I n Γ e A → PairedTyGoal M E I n Γ e A) ∧
  (∀ {Γ a b A}, ConvA E I n Γ a b A → PairedConvGoal M E I n Γ a b A)

def AllAdmittedPairedFundamental (models : ResolvedEnvA → AnnSemantics) : Prop :=
  ∀ E, EnvWfA (iotaIfaceA E) E → ∀ n, PairedFundamental (models E) E (iotaIfaceA E) n

theorem tyGoal_diagonal {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {e A : ExprA} (h : PairedTyGoal M E I n Γ e A) :
    TyGoal M E I n Γ e A := by
  intro hΓ ν ρ hρ
  exact (h hΓ ν ν ρ ρ (ValuationRel.refl ν) (PairedRealises.diagonal hρ)).diagonal

theorem convGoal_diagonal {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {a b A : ExprA} (h : PairedConvGoal M E I n Γ a b A) :
    ConvGoal M E I n Γ a b A := by
  intro hΓ ν ρ hρ
  exact (h hΓ ν ν ρ ρ (ValuationRel.refl ν) (PairedRealises.diagonal hρ)).diagonal

theorem fundamental_diagonal {M : AnnSemantics} {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} (h : PairedFundamental M E I n) : Fundamental M E I n :=
  ⟨fun ht => tyGoal_diagonal (h.1 ht), fun hc => convGoal_diagonal (h.2 hc)⟩

theorem all_admitted_fundamental_diagonal {models : ResolvedEnvA → AnnSemantics}
    (h : AllAdmittedPairedFundamental models) : AllAdmittedFundamental models :=
  fun E hE n => fundamental_diagonal (h E hE n)

/-- Pairing an existing realization needs no source soundness premise. The
source typing input is consumed separately by `generic_realises`. -/
theorem generic_self_related_of_unary {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralExtraction.NeutralSupport M)
    (hF : Fundamental M E I n) (ν : Valuation) (Γ : LCtxA) (hΓ : CtxWfA E I n Γ) :
    PairedRealises M ν ν Γ (NeutralExtraction.generic S ν Γ) (NeutralExtraction.generic S ν Γ) :=
  PairedRealises.diagonal (NeutralExtraction.generic_realises S hF ν Γ hΓ)

theorem generic_self_related {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralExtraction.NeutralSupport M)
    (hF : PairedFundamental M E I n) (ν : Valuation) (Γ : LCtxA) (hΓ : CtxWfA E I n Γ) :
    PairedRealises M ν ν Γ (NeutralExtraction.generic S ν Γ) (NeutralExtraction.generic S ν Γ) :=
  generic_self_related_of_unary S (fundamental_diagonal hF) ν Γ hΓ

theorem ann_membership_of_paired {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralExtraction.NeutralSupport M)
    (hF : PairedFundamental M E I n) :
    AnnSortMembershipSound E I n (NeutralExtraction.genericImage S) :=
  NeutralExtraction.ann_membership S (fundamental_diagonal hF)

theorem ann_sortUniq_of_paired {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat} (S : NeutralExtraction.NeutralSupport M)
    (hF : PairedFundamental M E I n) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A : ExprA} {u v : Level} (hu : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ A (.sort v)) : eqN u v :=
  ann_sortUniq_of_membership (ann_membership_of_paired S hF) hΓ hu hv

/-- Native paired worlds retain the independently indexed raw image. -/
inductive NativePairedRealises (M : NativeSemantics) (ν μ : Valuation) :
    LCtx → EnvI → EnvI → Prop
  | nil (ρ σ : EnvI) : NativePairedRealises M ν μ [] ρ σ
  | assumption {Γ : LCtx} {ρ σ : EnvI} {A : Expr Nat} {x y : Value}
      {k : Option Nat} {R S : Relation}
      (tail : NativePairedRealises M ν μ Γ ρ σ)
      (codes : CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S)
      (related : R x y) :
      NativePairedRealises M ν μ (.assumption A :: Γ) (EnvI.cons x ρ) (EnvI.cons y σ)
  | letBinding {Γ : LCtx} {ρ σ : EnvI} {A v : Expr Nat} {x y : Value}
      {k : Option Nat} {R S : Relation}
      (tail : NativePairedRealises M ν μ Γ ρ σ)
      (codes : CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S)
      (related : R x y)
      (left_value : R x (M.image ν Γ ρ v))
      (right_value : S y (M.image μ Γ σ v)) :
      NativePairedRealises M ν μ (.letBinding A v :: Γ) (EnvI.cons x ρ) (EnvI.cons y σ)

theorem NativePairedRealises.left {M : NativeSemantics} {ν μ : Valuation} {Γ : LCtx}
    {ρ σ : EnvI} (h : NativePairedRealises M ν μ Γ ρ σ) : NativeRealises M ν Γ ρ := by
  induction h with
  | nil ρ σ => exact .nil ρ
  | assumption tail codes related ih =>
      exact .assumption ih codes.left_code
        (TypedPER.left_member (M.lawful codes.left_code) related)
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.left_code
        (TypedPER.left_member (M.lawful codes.left_code) related) left_value

theorem NativePairedRealises.right {M : NativeSemantics} {ν μ : Valuation} {Γ : LCtx}
    {ρ σ : EnvI} (h : NativePairedRealises M ν μ Γ ρ σ) : NativeRealises M μ Γ σ := by
  induction h with
  | nil ρ σ => exact .nil σ
  | assumption tail codes related ih =>
      exact .assumption ih codes.right_code
        (codes.to_right (TypedPER.right_member (M.lawful codes.left_code) related))
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.right_code
        (codes.to_right (TypedPER.right_member (M.lawful codes.left_code) related)) right_value

theorem NativePairedRealises.diagonal {M : NativeSemantics} {ν : Valuation} {Γ : LCtx}
    {ρ : EnvI} (h : NativeRealises M ν Γ ρ) : NativePairedRealises M ν ν Γ ρ ρ := by
  induction h with
  | nil ρ => exact .nil ρ ρ
  | assumption tail code member ih =>
      exact .assumption ih (CodePair.diagonal code) member
  | letBinding tail code member value ih =>
      exact .letBinding ih (CodePair.diagonal code) member value value

theorem NativePairedRealises.symm {M : NativeSemantics} {ν μ : Valuation} {Γ : LCtx}
    {ρ σ : EnvI} (h : NativePairedRealises M ν μ Γ ρ σ) :
    NativePairedRealises M μ ν Γ σ ρ := by
  induction h with
  | nil ρ σ => exact .nil σ ρ
  | assumption tail codes related ih =>
      exact .assumption ih codes.symm (codes.to_right ((M.lawful codes.left_code).symm related))
  | letBinding tail codes related left_value right_value ih =>
      exact .letBinding ih codes.symm (codes.to_right ((M.lawful codes.left_code).symm related))
        right_value left_value

theorem NativePairedRealises.left_diagonal {M : NativeSemantics} {ν μ : Valuation}
    {Γ : LCtx} {ρ σ : EnvI} (h : NativePairedRealises M ν μ Γ ρ σ) :
    NativePairedRealises M ν ν Γ ρ ρ := NativePairedRealises.diagonal h.left

theorem NativePairedRealises.right_diagonal {M : NativeSemantics} {ν μ : Valuation}
    {Γ : LCtx} {ρ σ : EnvI} (h : NativePairedRealises M ν μ Γ ρ σ) :
    NativePairedRealises M μ μ Γ σ σ := NativePairedRealises.diagonal h.right

def NativePairedJudgment (M : NativeSemantics) (ν μ : Valuation) (Γ : LCtx) (ρ σ : EnvI)
    (a b A : Expr Nat) : Prop :=
  ∃ (k : Option Nat) (R S : Relation),
    CodePair M.toCodeSystem k (M.image ν Γ ρ A) (M.image μ Γ σ A) R S ∧
      R (M.image ν Γ ρ a) (M.image μ Γ σ b)

theorem NativePairedJudgment.symm {M : NativeSemantics} {ν μ : Valuation}
    {Γ : LCtx} {ρ σ : EnvI} {a b A : Expr Nat}
    (h : NativePairedJudgment M ν μ Γ ρ σ a b A) :
    NativePairedJudgment M μ ν Γ σ ρ b a A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, S, R, hc.symm, hc.to_right ((M.lawful hc.left_code).symm hr)⟩

theorem NativePairedJudgment.trans {M : NativeSemantics} {ν μ ξ : Valuation}
    {Γ : LCtx} {ρ σ τ : EnvI} {a b c A : Expr Nat}
    (h : NativePairedJudgment M ν μ Γ ρ σ a b A)
    (g : NativePairedJudgment M μ ξ Γ σ τ b c A) :
    NativePairedJudgment M ν ξ Γ ρ τ a c A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  obtain ⟨l, T, U, hd, hs⟩ := g
  have hmid := (M.coherent hd.left_code hc.right_code _ _).mp hs
  exact ⟨k, R, U, hc.trans hd, (M.lawful hc.left_code).trans hr (hc.to_left hmid)⟩

theorem NativePairedJudgment.diagonal {M : NativeSemantics} {ν : Valuation}
    {Γ : LCtx} {ρ : EnvI} {a b A : Expr Nat}
    (h : NativePairedJudgment M ν ν Γ ρ ρ a b A) : NativeJudgment M ν Γ ρ a b A := by
  obtain ⟨k, R, S, hc, hr⟩ := h
  exact ⟨k, R, hc.left_code, M.defined hc.left_code, hr⟩

theorem NativePairedJudgment.of_diagonal {M : NativeSemantics} {ν : Valuation}
    {Γ : LCtx} {ρ : EnvI} {a b A : Expr Nat}
    (h : NativeJudgment M ν Γ ρ a b A) : NativePairedJudgment M ν ν Γ ρ ρ a b A := by
  obtain ⟨k, R, hc, _, hr⟩ := h
  exact ⟨k, R, R, CodePair.diagonal hc, hr⟩

def NativePairedFundamental (M : NativeSemantics) (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E →
  (∀ {Γ e A}, CtxWfT E n Γ → HasTyT E n Γ e A →
    ∀ ν μ ρ σ, ValuationRel ν μ → NativePairedRealises M ν μ Γ ρ σ →
      NativePairedJudgment M ν μ Γ ρ σ e e A) ∧
  (∀ {Γ a b A}, CtxWfT E n Γ → ConvT E n Γ a b A →
    ∀ ν μ ρ σ, ValuationRel ν μ → NativePairedRealises M ν μ Γ ρ σ →
      NativePairedJudgment M ν μ Γ ρ σ a b A)

theorem native_fundamental_diagonal {M : NativeSemantics} {E : ResolvedEnv} {n : Nat}
    (h : NativePairedFundamental M E n) : NativeFundamental M E n := by
  intro hE
  constructor
  · intro Γ e A hΓ ht ν ρ hρ
    exact ((h hE).1 hΓ ht ν ν ρ ρ (ValuationRel.refl ν)
      (NativePairedRealises.diagonal hρ)).diagonal
  · intro Γ a b A hΓ hc ν ρ hρ
    exact ((h hE).2 hΓ hc ν ν ρ ρ (ValuationRel.refl ν)
      (NativePairedRealises.diagonal hρ)).diagonal

theorem native_generic_self_related_of_unary {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NeutralExtraction.NativeNeutralSupport M)
    (hF : NativeFundamental M E n) (hE : EnvWfT E)
    (ν : Valuation) (Γ : LCtx) (hΓ : CtxWfT E n Γ) :
    NativePairedRealises M ν ν Γ
      (NeutralExtraction.nativeGeneric S ν Γ) (NeutralExtraction.nativeGeneric S ν Γ) :=
  NativePairedRealises.diagonal (NeutralExtraction.native_generic_realises S hF hE ν Γ hΓ)

theorem native_generic_self_related {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NeutralExtraction.NativeNeutralSupport M)
    (hF : NativePairedFundamental M E n) (hE : EnvWfT E)
    (ν : Valuation) (Γ : LCtx) (hΓ : CtxWfT E n Γ) :
    NativePairedRealises M ν ν Γ
      (NeutralExtraction.nativeGeneric S ν Γ) (NeutralExtraction.nativeGeneric S ν Γ) :=
  native_generic_self_related_of_unary S (native_fundamental_diagonal hF) hE ν Γ hΓ

theorem native_membership_of_paired {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NeutralExtraction.NativeNeutralSupport M)
    (hF : NativePairedFundamental M E n) :
    NativeSortMembershipSound E n (NeutralExtraction.nativeGenericImage S) :=
  NeutralExtraction.native_membership S (native_fundamental_diagonal hF)

theorem native_sortUniq_of_paired {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NeutralExtraction.NativeNeutralSupport M)
    (hF : NativePairedFundamental M E n) (hE : EnvWfT E) : SortUniq E n :=
  native_sortUniq_of_membership hE (native_membership_of_paired S hF)

theorem native_zsc_of_paired {M : NativeSemantics} {E : ResolvedEnv}
    {n : Nat} (S : NeutralExtraction.NativeNeutralSupport M)
    (hF : NativePairedFundamental M E n) : HostPropAudit.ZeroSortCoherence E n :=
  native_zsc_of_membership (native_membership_of_paired S hF)

end Rcic.Declarative.Ann.LR3.PairedStatements
