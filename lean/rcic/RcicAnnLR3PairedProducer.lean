import rcic.RcicAnnLR3NeutralCodes
import rcic.RcicAnnLR3PairedStatements
import rcic.RcicAnnLR3PairedArms

/-!
# Concrete neutral-code suppliers for the paired interfaces

The neutral, proof and universe descriptor fragment supplies actual
universe transport, level-zero proof irrelevance and binary reflection.
Eight paired source-constructor contracts are instantiated from that
algebra, uniformly in an attached source image with its sort equation.
No fundamental theorem is a premise of those eight suppliers.

The generic-context and extraction theorems below consume a paired
fundamental theorem for the attached image. Their decoder, reflection,
and reflection-membership inputs are the constructed NeutralCodes
operations, not extra consumer assumptions. Binary generic realization
uses paired typing at each tail, transports the two type interpretations,
and relates the two reflected assumptions. Lets retain both stored images.

This file does not integrate Pi or general-family operators into the
descriptor language, supply the remaining twenty paired source contracts,
or assert an all-admitted fundamental theorem. All source environments,
contexts, exact Option Nat levels and native admission premises remain in
their original statements. No completed K converse is used.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.PairedProducer

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

/-- Actual universe-to-element transport for the descriptor producer. -/
def universeTransport : UniverseTransport NeutralCodes.codeSystem where
  relate := by
    intro k V W h
    obtain ⟨R, S, hv, hw, ht⟩ := NeutralCodes.universe_transport h
    exact ⟨R, S, ⟨hv, hw, ht⟩⟩

/-- Actual irrelevance at every descriptor with exact level zero. -/
def propIrrelevance : PropIrrelevance NeutralCodes.codeSystem where
  relate := NeutralCodes.code_prop_irrelevant

theorem codePair_of_universe {k : Option Nat} {V W : Value}
    (h : NeutralCodes.UniversePER k V W) :
    ∃ R S : Relation, CodePair NeutralCodes.codeSystem k V W R S :=
  universeTransport.relate h

/-- Transport applies to any chosen presentations of the related codes. -/
theorem codePair_of_presentations {k : Option Nat} {V W : Value} {R S : Relation}
    (hv : NeutralCodes.Code k V R) (hw : NeutralCodes.Code k W S)
    (h : NeutralCodes.UniversePER k V W) :
    CodePair NeutralCodes.codeSystem k V W R S :=
  ⟨hv, hw, NeutralCodes.el_transport hv hw h⟩

theorem codePair_reflection {k : Option Nat} {V W : Value} {R S : Relation}
    (h : CodePair NeutralCodes.codeSystem k V W R S) (name : Nat) :
    R (NeutralCodes.reflect V name) (NeutralCodes.reflect W name) :=
  NeutralCodes.reflect_relation h.left_code h.right_code h.transport name

/-- An inhabited transport example with distinct observed type values. -/
theorem distinct_related_code_pair (k : Option Nat) :
    (¬ ValueEq (NeutralCodes.reify (.neutralType k 0))
      (NeutralCodes.reify (.neutralType k 1))) ∧
    CodePair NeutralCodes.codeSystem k
      (NeutralCodes.reify (.neutralType k 0)) (NeutralCodes.reify (.neutralType k 1))
      (NeutralCodes.El (.neutralType k 0)) (NeutralCodes.El (.neutralType k 1)) := by
  obtain ⟨hne, hr, _⟩ := NeutralCodes.distinct_related_neutral_codes k
  exact ⟨hne, codePair_of_presentations
    (NeutralCodes.code (.neutralType k 0)) (NeutralCodes.code (.neutralType k 1)) hr⟩

section Annotated

variable (image : Valuation → LCtxA → EnvI → ExprA → Value)
variable (hs : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l))

theorem ty_sort_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.ty_sort_supplied _ E I n

theorem ty_conv_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_conv (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.ty_conv_supplied _ E I n universeTransport

theorem conv_refl_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_refl (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_refl_supplied _ E I n

theorem conv_symm_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_symm (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_symm_supplied _ E I n

theorem conv_trans_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_trans (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_trans_supplied _ E I n

theorem conv_sorts_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_sorts (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_sorts_supplied _ E I n

theorem conv_tyConv_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_tyConv (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_tyConv_supplied _ E I n universeTransport

theorem conv_irr_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_irr (NeutralCodes.annSemantics image hs) E I n :=
  PairedArms.conv_irr_supplied _ E I n propIrrelevance

/-- These eight exact contracts are supplied; this conjunction is not a
complete `PairedArms.Arms` record. -/
theorem eight_arms_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Ty_conv (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_refl (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_symm (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_trans (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_sorts (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_tyConv (NeutralCodes.annSemantics image hs) E I n ∧
    PairedArms.Conv_irr (NeutralCodes.annSemantics image hs) E I n :=
  ⟨ty_sort_supplied image hs E I n, ty_conv_supplied image hs E I n,
    conv_refl_supplied image hs E I n, conv_symm_supplied image hs E I n,
    conv_trans_supplied image hs E I n, conv_sorts_supplied image hs E I n,
    conv_tyConv_supplied image hs E I n, conv_irr_supplied image hs E I n⟩

/-- The source image and its sort equation are fixed before source typing
evidence is supplied. The environment uses the actual constructed support. -/
def generic : Valuation → LCtxA → EnvI :=
  NeutralExtraction.generic (NeutralCodes.neutralSupport image hs)

def genericImage : AnnImage :=
  NeutralExtraction.genericImage (NeutralCodes.neutralSupport image hs)

/-- A structural binary realization proof, using the paired typing input
at the tail rather than selecting independent unary realizations. -/
theorem generic_related_of_typing {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hTy : ∀ {Γ : LCtxA} {e A : ExprA}, HasTyA E I n Γ e A →
      PairedTyGoal (NeutralCodes.annSemantics image hs) E I n Γ e A) :
    ∀ (ν μ : Valuation), ValuationRel ν μ → ∀ (Γ : LCtxA), CtxWfA E I n Γ →
      PairedRealises (NeutralCodes.annSemantics image hs) ν μ Γ
        (generic image hs ν Γ) (generic image hs μ Γ) := by
  intro ν μ hν Γ hΓ
  induction hΓ with
  | nil => exact .nil _ _
  | assumption hΓ hA ih =>
      obtain ⟨k, R, S, hc⟩ := PairedJudgment.related_types universeTransport
        (hTy hA hΓ ν μ _ _ hν ih)
      exact .assumption ih hc (codePair_reflection hc _)
  | letBinding hΓ hA hv ih =>
      obtain ⟨k, R, S, hc, hr⟩ := hTy hv hΓ ν μ _ _ hν ih
      exact .letBinding ih hc hr
        (TypedPER.left_member (NeutralCodes.code_lawful hc.left_code) hr)
        (hc.to_right (TypedPER.right_member (NeutralCodes.code_lawful hc.left_code) hr))

theorem generic_related {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental (NeutralCodes.annSemantics image hs) E I n)
    (ν μ : Valuation) (hν : ValuationRel ν μ) (Γ : LCtxA) (hΓ : CtxWfA E I n Γ) :
    PairedRealises (NeutralCodes.annSemantics image hs) ν μ Γ
      (generic image hs ν Γ) (generic image hs μ Γ) :=
  generic_related_of_typing image hs hF.1 ν μ hν Γ hΓ

theorem generic_self_related {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental (NeutralCodes.annSemantics image hs) E I n)
    (ν : Valuation) (Γ : LCtxA) (hΓ : CtxWfA E I n Γ) :
    PairedRealises (NeutralCodes.annSemantics image hs) ν ν Γ
      (generic image hs ν Γ) (generic image hs ν Γ) :=
  generic_related image hs hF ν ν (ValuationRel.refl ν) Γ hΓ

theorem ann_membership {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental (NeutralCodes.annSemantics image hs) E I n) :
    AnnSortMembershipSound E I n (genericImage image hs) :=
  ann_membership_of_paired (NeutralCodes.neutralSupport image hs) hF

theorem ann_sortUniq {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental (NeutralCodes.annSemantics image hs) E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u v : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (hv : HasTyA E I n Γ A (.sort v)) : eqN u v :=
  ann_sortUniq_of_membership (ann_membership image hs hF) hΓ hu hv

theorem ann_zsc {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hF : PairedFundamental (NeutralCodes.annSemantics image hs) E I n)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A : ExprA} {u : Level}
    (hu : HasTyA E I n Γ A (.sort u)) (h0 : HasTyA E I n Γ A (.sort .zero)) :
    eqN u .zero := ann_sortUniq image hs hF hΓ hu h0

end Annotated

section Native

variable (image : Valuation → LCtx → EnvI → Expr Nat → Value)
variable (hs : ∀ ν Γ ρ l, image ν Γ ρ (.sort l) = universeValue (eval ν l))

def nativeGeneric : Valuation → LCtx → EnvI :=
  NeutralExtraction.nativeGeneric (NeutralCodes.nativeNeutralSupport image hs)

def nativeGenericImage : NativeImage :=
  NeutralExtraction.nativeGenericImage (NeutralCodes.nativeNeutralSupport image hs)

/-- The native image remains independently indexed by the raw subject. -/
theorem native_related_types {ν μ : Valuation} {Γ : LCtx} {ρ σ : EnvI}
    {A B : Expr Nat} {u : Level}
    (h : NativePairedJudgment (NeutralCodes.nativeSemantics image hs)
      ν μ Γ ρ σ A B (.sort u)) :
    RelatedCode NeutralCodes.codeSystem (image ν Γ ρ A) (image μ Γ σ B) := by
  obtain ⟨l, R, S, hc, hr⟩ := h
  have hv : NeutralCodes.Code l (universeValue (eval ν u)) R := by
    have hv := hc.left_code
    change NeutralCodes.Code l (image ν Γ ρ (.sort u)) R at hv
    rw [hs] at hv
    exact hv
  have hu : NeutralCodes.UniversePER (eval ν u) (image ν Γ ρ A) (image μ Γ σ B) :=
    (NeutralCodes.universe_carrier hv _ _).mp hr
  obtain ⟨T, U, ht⟩ := codePair_of_universe hu
  exact ⟨eval ν u, T, U, ht⟩

theorem native_generic_related_of_typing {E : ResolvedEnv} {n : Nat}
    (hTy : ∀ {Γ : LCtx} {e A : Expr Nat}, CtxWfT E n Γ → HasTyT E n Γ e A →
      ∀ (ν μ : Valuation) (ρ σ : EnvI), ValuationRel ν μ →
        NativePairedRealises (NeutralCodes.nativeSemantics image hs) ν μ Γ ρ σ →
        NativePairedJudgment (NeutralCodes.nativeSemantics image hs) ν μ Γ ρ σ e e A) :
    ∀ (ν μ : Valuation), ValuationRel ν μ → ∀ (Γ : LCtx), CtxWfT E n Γ →
      NativePairedRealises (NeutralCodes.nativeSemantics image hs) ν μ Γ
        (nativeGeneric image hs ν Γ) (nativeGeneric image hs μ Γ) := by
  intro ν μ hν Γ hΓ
  induction hΓ with
  | nil => exact .nil _ _
  | assumption _ _ _ hΓ hA ih =>
      obtain ⟨k, R, S, hc⟩ := native_related_types image hs
        (hTy hΓ hA ν μ _ _ hν ih)
      exact .assumption ih hc (codePair_reflection hc _)
  | letBinding _ _ _ _ hΓ hA hv ih =>
      obtain ⟨k, R, S, hc, hr⟩ := hTy hΓ hv ν μ _ _ hν ih
      exact .letBinding ih hc hr
        (TypedPER.left_member (NeutralCodes.code_lawful hc.left_code) hr)
        (hc.to_right (TypedPER.right_member (NeutralCodes.code_lawful hc.left_code) hr))

theorem native_generic_related {E : ResolvedEnv} {n : Nat}
    (hF : NativePairedFundamental (NeutralCodes.nativeSemantics image hs) E n)
    (hE : EnvWfT E) (ν μ : Valuation) (hν : ValuationRel ν μ)
    (Γ : LCtx) (hΓ : CtxWfT E n Γ) :
    NativePairedRealises (NeutralCodes.nativeSemantics image hs) ν μ Γ
      (nativeGeneric image hs ν Γ) (nativeGeneric image hs μ Γ) :=
  native_generic_related_of_typing image hs (hF hE).1 ν μ hν Γ hΓ

theorem native_generic_self_related {E : ResolvedEnv} {n : Nat}
    (hF : NativePairedFundamental (NeutralCodes.nativeSemantics image hs) E n)
    (hE : EnvWfT E) (ν : Valuation) (Γ : LCtx) (hΓ : CtxWfT E n Γ) :
    NativePairedRealises (NeutralCodes.nativeSemantics image hs) ν ν Γ
      (nativeGeneric image hs ν Γ) (nativeGeneric image hs ν Γ) :=
  native_generic_related image hs hF hE ν ν (ValuationRel.refl ν) Γ hΓ

theorem native_membership {E : ResolvedEnv} {n : Nat}
    (hF : NativePairedFundamental (NeutralCodes.nativeSemantics image hs) E n) :
    NativeSortMembershipSound E n (nativeGenericImage image hs) :=
  native_membership_of_paired (NeutralCodes.nativeNeutralSupport image hs) hF

theorem native_sortUniq {E : ResolvedEnv} {n : Nat}
    (hF : NativePairedFundamental (NeutralCodes.nativeSemantics image hs) E n)
    (hE : EnvWfT E) : SortUniq E n :=
  native_sortUniq_of_membership hE (native_membership image hs hF)

theorem native_zsc {E : ResolvedEnv} {n : Nat}
    (hF : NativePairedFundamental (NeutralCodes.nativeSemantics image hs) E n) :
    HostPropAudit.ZeroSortCoherence E n :=
  native_zsc_of_membership (native_membership image hs hF)

end Native

end Rcic.Declarative.Ann.LR3.PairedProducer
