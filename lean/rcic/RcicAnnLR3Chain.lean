import rcic.RcicAnnLR3HeadLayer
import rcic.RcicAnnLR3RelationalFacts

/-!
# Finite typed LR3 reduction chains

The explicit certified head layer is the parameter of this one LR3 cone.
Its concrete supplied instance is `contextualHeadLayerA3`; future positive
certificate instances reuse these chains and the same LR3 definitions.
Type chains retain the landed per-step sort discipline. Term chains retain
one carrier. Neither chain chooses a successor or asks for a decision about
the K guard. `WhTyA3` additionally carries a positive normal endpoint; this
is the normalization relation consumed by relational sort synthesis.

Normal-form uniqueness composes the concrete head determinism theorem with
finite trace induction. No fuel, evaluator, or steps-or-stuck dichotomy is
used. The declarative conversion relation is shared with the previous stage.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

inductive WhTyChainA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) :
    LCtxA → ExprA → ExprA → Type
  | refl (Γ : LCtxA) (A : ExprA) (u : Level)
      (h : HasTyA E I n Γ A (.sort u)) : WhTyChainA3 E I n H Γ A A
  | cons (Γ : LCtxA) (A A' N : ExprA) (u : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hs : H.step Γ A A' (.sort u))
      (t : WhTyChainA3 E I n H Γ A' N) : WhTyChainA3 E I n H Γ A N

/-- A supplied finite typed chain and its positive terminal certificate. -/
def WhTyA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (A N : ExprA) : Prop :=
  Nonempty (WhTyChainA3 E I n H Γ A N) ∧ H.normal Γ N

inductive TmChainA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (A : ExprA) : ExprA → ExprA → Type
  | refl (a : ExprA) (h : HasTyA E I n Γ a A) : TmChainA3 E I n H Γ A a a
  | cons (a a' N : ExprA) (ha : HasTyA E I n Γ a A)
      (hs : H.step Γ a a' A)
      (t : TmChainA3 E I n H Γ A a' N) : TmChainA3 E I n H Γ A a N

/-- Term chains need not be terminal; the family clause supplies normality. -/
def TyHRedStarA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (a N A : ExprA) : Prop :=
  Nonempty (TmChainA3 E I n H Γ A a N)

section Chain

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n} {Γ : LCtxA}

def HeadStepA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (a b : ExprA) : Prop := ∃ T, H.step Γ a b T

private theorem traceStep_det : LR3Measurement.Deterministic (HeadStepA3 E I n H Γ) := by
  rintro a b c ⟨T, h⟩ ⟨U, h'⟩
  exact H.deterministic h h'

private theorem traceStep_normal {N : ExprA} (h : H.normal Γ N) :
    LR3Measurement.Normal (HeadStepA3 E I n H Γ) N := by
  rintro b ⟨T, hs⟩
  exact H.normal_excludes h hs

theorem whTyChainA3_trace : {A N : ExprA} → WhTyChainA3 E I n H Γ A N →
    LR3Measurement.Trace (HeadStepA3 E I n H Γ) A N
  | _, _, .refl _ A _ _ => .refl A
  | _, _, .cons _ _ _ _ u _ hs t => .cons ⟨.sort u, hs⟩ (whTyChainA3_trace t)

theorem tmChainA3_trace {A : ExprA} : {a N : ExprA} → TmChainA3 E I n H Γ A a N →
    LR3Measurement.Trace (HeadStepA3 E I n H Γ) a N
  | _, _, .refl a _ => .refl a
  | _, _, .cons _ _ _ _ hs t => .cons ⟨A, hs⟩ (tmChainA3_trace t)

/-- Both normal-form uniqueness results follow from direct trace induction. -/
theorem whTyA3_det {A N N' : ExprA}
    (h : WhTyA3 E I n H Γ A N) (h' : WhTyA3 E I n H Γ A N') : N = N' := by
  obtain ⟨⟨t⟩, hN⟩ := h
  obtain ⟨⟨t'⟩, hN'⟩ := h'
  exact LR3Measurement.Trace.normal_unique (R := HeadStepA3 E I n H Γ) traceStep_det
    (whTyChainA3_trace t) (whTyChainA3_trace t')
    (traceStep_normal hN) (traceStep_normal hN')

theorem tyHRedStarA3_det {A a N N' : ExprA}
    (h : TyHRedStarA3 E I n H Γ a N A) (h' : TyHRedStarA3 E I n H Γ a N' A)
    (hN : H.normal Γ N) (hN' : H.normal Γ N') : N = N' := by
  obtain ⟨t⟩ := h
  obtain ⟨t'⟩ := h'
  exact LR3Measurement.Trace.normal_unique (R := HeadStepA3 E I n H Γ) traceStep_det
    (tmChainA3_trace t) (tmChainA3_trace t')
    (traceStep_normal hN) (traceStep_normal hN')

theorem whTyChainA3_hasTy_head {A N : ExprA} : WhTyChainA3 E I n H Γ A N →
    ∃ u, Nonempty (HasTyA E I n Γ A (.sort u))
  | .refl _ _ u h => ⟨u, ⟨h⟩⟩
  | .cons _ _ _ _ u h _ _ => ⟨u, ⟨h⟩⟩

theorem whTyChainA3_hasTy_end : {A N : ExprA} → WhTyChainA3 E I n H Γ A N →
    ∃ u, Nonempty (HasTyA E I n Γ N (.sort u))
  | _, _, .refl _ _ u h => ⟨u, ⟨h⟩⟩
  | _, _, .cons _ _ _ _ _ _ _ t => whTyChainA3_hasTy_end t

theorem tmChainA3_hasTy_head {A a N : ExprA} : TmChainA3 E I n H Γ A a N →
    Nonempty (HasTyA E I n Γ a A)
  | .refl _ h => ⟨h⟩
  | .cons _ _ _ h _ _ => ⟨h⟩

theorem tmChainA3_hasTy_end {A : ExprA} : {a N : ExprA} → TmChainA3 E I n H Γ A a N →
    Nonempty (HasTyA E I n Γ N A)
  | _, _, .refl _ h => ⟨h⟩
  | _, _, .cons _ _ _ _ _ t => tmChainA3_hasTy_end t

def whTyChainA3_trans : {A B N : ExprA} → WhTyChainA3 E I n H Γ A B →
    WhTyChainA3 E I n H Γ B N → WhTyChainA3 E I n H Γ A N
  | _, _, _, .refl _ _ _ _, t => t
  | _, _, _, .cons _ A A' _ u h hs t, t' =>
      .cons Γ A A' _ u h hs (whTyChainA3_trans t t')

def tmChainA3_trans {A : ExprA} : {a b N : ExprA} → TmChainA3 E I n H Γ A a b →
    TmChainA3 E I n H Γ A b N → TmChainA3 E I n H Γ A a N
  | _, _, _, .refl _ _, t => t
  | _, _, _, .cons a a' _ h hs t, t' => .cons a a' _ h hs (tmChainA3_trans t t')

theorem whTyA3_of_hasTy {A : ExprA} {u : Level}
    (h : HasTyA E I n Γ A (.sort u)) (hN : H.normal Γ A) :
    WhTyA3 E I n H Γ A A := ⟨⟨.refl Γ A u h⟩, hN⟩

theorem whTyA3_sort (Γ : LCtxA) (l : Level) : WhTyA3 E I n H Γ (.sort l) (.sort l) :=
  whTyA3_of_hasTy (.sort Γ l) (H.normal_sort Γ l)

theorem whTyA3_cons {A A' N : ExprA} {u : Level}
    (hA : HasTyA E I n Γ A (.sort u)) (hs : H.step Γ A A' (.sort u))
    (h : WhTyA3 E I n H Γ A' N) : WhTyA3 E I n H Γ A N := by
  obtain ⟨⟨t⟩, hn⟩ := h
  exact ⟨⟨.cons Γ A A' N u hA hs t⟩, hn⟩

theorem whTyA3_hasTy_head {A N : ExprA} (h : WhTyA3 E I n H Γ A N) :
    ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  obtain ⟨t⟩ := h.1
  exact whTyChainA3_hasTy_head t

theorem whTyA3_hasTy_end {A N : ExprA} (h : WhTyA3 E I n H Γ A N) :
    ∃ u, Nonempty (HasTyA E I n Γ N (.sort u)) := by
  obtain ⟨t⟩ := h.1
  exact whTyChainA3_hasTy_end t

theorem tyHRedStarA3_refl {A a : ExprA} (h : HasTyA E I n Γ a A) :
    TyHRedStarA3 E I n H Γ a a A := ⟨.refl a h⟩

theorem tyHRedStarA3_cons {A a a' N : ExprA} (ha : HasTyA E I n Γ a A)
    (hs : H.step Γ a a' A) (h : TyHRedStarA3 E I n H Γ a' N A) :
    TyHRedStarA3 E I n H Γ a N A := by
  obtain ⟨t⟩ := h
  exact ⟨.cons a a' N ha hs t⟩

theorem tyHRedStarA3_trans {A a b N : ExprA}
    (h : TyHRedStarA3 E I n H Γ a b A) (h' : TyHRedStarA3 E I n H Γ b N A) :
    TyHRedStarA3 E I n H Γ a N A := by
  obtain ⟨t⟩ := h
  obtain ⟨t'⟩ := h'
  exact ⟨tmChainA3_trans t t'⟩

end Chain

section Conversion

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
variable (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
variable (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)

include hE hI hR hIS hΓ

/-- Every type chain escapes to shared annotated type conversion. -/
theorem whTyChainA3_tyConv : {A N : ExprA} → WhTyChainA3 E I n H Γ A N →
    Nonempty (TyConvA E I n Γ A N)
  | _, _, .refl _ A _ _ => ⟨.refl Γ A⟩
  | _, _, .cons _ A A' N u hA hs t => by
      obtain ⟨hc⟩ := H.sound hE hI hR hIS hΓ hs
      obtain ⟨ht⟩ := whTyChainA3_tyConv t
      exact ⟨.trans Γ A A' N
        (.of Γ A A' u u u hA (eqNA_refl _)
          (convA_hasTy_right hE hI hR hIS hΓ hc) (eqNA_refl _) hc) ht⟩

theorem whTyA3_tyConv {A N : ExprA} (h : WhTyA3 E I n H Γ A N) :
    Nonempty (TyConvA E I n Γ A N) := by
  obtain ⟨t⟩ := h.1
  exact whTyChainA3_tyConv hE hI hR hIS hΓ t

/-- The term-chain escape composes each derived head conversion. -/
theorem tmChainA3_conv {A : ExprA} : {a N : ExprA} → TmChainA3 E I n H Γ A a N →
    Nonempty (ConvA E I n Γ a N A)
  | _, _, .refl a h => ⟨.refl Γ a A h⟩
  | _, _, .cons a a' N _ hs t => by
      obtain ⟨hc⟩ := H.sound hE hI hR hIS hΓ hs
      obtain ⟨ht⟩ := tmChainA3_conv t
      exact ⟨.trans Γ a a' N A hc ht⟩

theorem tyHRedStarA3_conv {A a N : ExprA} (h : TyHRedStarA3 E I n H Γ a N A) :
    Nonempty (ConvA E I n Γ a N A) := by
  obtain ⟨t⟩ := h
  exact tmChainA3_conv hE hI hR hIS hΓ t

end Conversion

#print axioms WhTyChainA3
#print axioms WhTyA3
#print axioms TmChainA3
#print axioms TyHRedStarA3
#print axioms whTyA3_det
#print axioms tyHRedStarA3_det
#print axioms whTyA3_sort
#print axioms whTyA3_tyConv
#print axioms tyHRedStarA3_conv

end Rcic.Declarative.Ann.LR3
