import rcic.RcicAnnLR3IrrQueryDescent
import rcic.RcicAnnLR3ReflInferenceBoundary

/-!
# Original derivation data for the two applications of `refl`

`HeadTypingSourceA3` is indexed by the actual `HasTyA` proof. Its constructors
retain the original app/const rule fields and each original conversion
wrapper. Every queried premise carries a strict rank bound; the rule node
itself has a non-strict bound because the outermost application may be the
input proof itself. Following a function or conversion premise is strict.

`fixedReflOriginalSpineA3` supplies this data for the exact proof subject
used by D1. In particular no composed `TyConvA`, collapsed conversion, or
reconstructed endpoint typing is substituted for an original field. This
does not assert a rank bound for any subsequently constructed Pi query.

The stored constructor telescope and its partial application are also
positively typed at `sort 0`. Their large domains do not make these
proposition-valued telescopes Type-valued. This does not identify the
arbitrary carrier sort of a later conversion without a coherence theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Original head-spine typing data. The index is the input derivation
itself, so a captured field is an original premise, not merely a derivation
of the same judgment. -/
inductive HeadTypingSourceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (bound : Nat) :
    {e A : ExprA} → HasTyA E I n Γ e A → Type
  | const (r : Nat) (ls : List Level) (m : CheckedMemberA) (u : Level)
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hT : HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u))
      (hTRank : hasTyDerivationRankA3 hT < bound)
      (hNodeRank : hasTyDerivationRankA3
        (.const Γ r ls m u hres hlen hwf hT) ≤ bound) :
      HeadTypingSourceA3 E I n Γ bound (.const Γ r ls m u hres hlen hwf hT)
  | app (f a D C : ExprA) (u v w : Level)
      (hC : HasTyA E I n (.assumption D :: Γ) C (.sort v))
      (hResult : HasTyA E I n Γ (instantiate0A a C) (.sort w))
      (hf : HasTyA E I n Γ f (.pi D u C v))
      (ha : HasTyA E I n Γ a D)
      (functionSource : HeadTypingSourceA3 E I n Γ bound hf)
      (hCRank : hasTyDerivationRankA3 hC < bound)
      (hResultRank : hasTyDerivationRankA3 hResult < bound)
      (hfRank : hasTyDerivationRankA3 hf < bound)
      (haRank : hasTyDerivationRankA3 ha < bound)
      (hNodeRank : hasTyDerivationRankA3
        (.app Γ f a D C u v w hC hResult hf ha) ≤ bound) :
      HeadTypingSourceA3 E I n Γ bound (.app Γ f a D C u v w hC hResult hf ha)
  | conv (e A B : ExprA) (l u : Level)
      (h : HasTyA E I n Γ e A)
      (hAl : HasTyA E I n Γ A (.sort l)) (hlu : eqN l u)
      (hB : HasTyA E I n Γ B (.sort u))
      (hc : ConvA E I n Γ A B (.sort u))
      (source : HeadTypingSourceA3 E I n Γ bound h)
      (hRank : hasTyDerivationRankA3 h < bound)
      (hAlRank : hasTyDerivationRankA3 hAl < bound)
      (hBRank : hasTyDerivationRankA3 hB < bound)
      (hcRank : convDerivationRankA3 hc < bound)
      (hNodeRank : hasTyDerivationRankA3
        (.conv Γ e A B l u h hAl hlu hB hc) ≤ bound) :
      HeadTypingSourceA3 E I n Γ bound (.conv Γ e A B l u h hAl hlu hB hc)

private inductive ConstApplicationA3 : ExprA → Type
  | const (r : Nat) (ls : List Level) : ConstApplicationA3 (.const r ls)
  | app {f : ExprA} (a : ExprA) (hf : ConstApplicationA3 f) :
      ConstApplicationA3 (.app f a)

private def headTypingSourceA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {bound : Nat} : {e A : ExprA} →
    (h : HasTyA E I n Γ e A) → ConstApplicationA3 e →
    hasTyDerivationRankA3 h ≤ bound → HeadTypingSourceA3 E I n Γ bound h
  | _, _, .sort _ _, s, _ => nomatch s
  | _, _, .bvar _ _ _ _ _ _, s, _ => nomatch s
  | _, _, .const _ r ls m u hres hlen hwf hT, _, hBound =>
      .const r ls m u hres hlen hwf hT
        (by simp only [hasTyDerivationRankA3] at hBound; omega) hBound
  | _, _, .pi _ _ _ _ _ _ _, s, _ => nomatch s
  | _, _, .lam _ _ _ _ _ _ _ _ _, s, _ => nomatch s
  | _, _, .app _ f a D C u v w hC hResult hf ha, s, hBound => by
      cases s with
      | app _ sf =>
          exact .app f a D C u v w hC hResult hf ha
            (headTypingSourceA3 hf sf
              (by simp only [hasTyDerivationRankA3] at hBound; omega))
            (by simp only [hasTyDerivationRankA3] at hBound; omega)
            (by simp only [hasTyDerivationRankA3] at hBound; omega)
            (by simp only [hasTyDerivationRankA3] at hBound; omega)
            (by simp only [hasTyDerivationRankA3] at hBound; omega)
            hBound
  | _, _, .letE _ _ _ _ _ _ _ _ _ _ _, s, _ => nomatch s
  | _, _, .lit _ _ _ _, s, _ => nomatch s
  | _, _, .conv _ e A B l u h hAl hlu hB hc, s, hBound =>
      .conv e A B l u h hAl hlu hB hc
        (headTypingSourceA3 h s
          (by simp only [hasTyDerivationRankA3] at hBound; omega))
        (by simp only [hasTyDerivationRankA3] at hBound; omega)
        (by simp only [hasTyDerivationRankA3] at hBound; omega)
        (by simp only [hasTyDerivationRankA3] at hBound; omega)
        (by simp only [hasTyDerivationRankA3] at hBound; omega)
        hBound

namespace ReflProvenance

open EqLargeFixture RouteCKContext

/-- The complete original app/const head spine for the fixed D1 subject.
Every original wrapper conversion and every original app/const premise is
recorded with its actual strict bound below the input typing. -/
def fixedReflOriginalSpineA3 {T : ExprA}
    (h : HasTyA env (iotaIfaceA env) 0 assumptionContext (reflAt parameter) T) :
    HeadTypingSourceA3 env (iotaIfaceA env) 0 assumptionContext
      (hasTyDerivationRankA3 h) h :=
  headTypingSourceA3 h (.app parameter (.app (.sort .zero) (.const 64 [])))
    (Nat.le_refl _)

/-- The stored Eq constructor type is proposition-valued, directly from its
admission typing and the annotated `imax` equations. -/
def reflTypePropTypedA3 (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ reflTy (.sort .zero) := by
  have h0 : HasTyA famEnv noIotaA 0 [] reflTy (.sort .zero) :=
    hasTyA_sortEqN reflTyTyped (fun _ => rfl)
  have h1 := hasTyA_env_iface (prefixA_trans fam_in_prefix prefix_in_env)
    (prefix_iface.prefix fam_in_prefix) h0
  exact hasTyClosedWeakenA closed liftIface (fun _ => rfl) (fun _ => rfl) Γ h1

abbrev partialReflPropTypeA3 : ExprA :=
  .pi (.sort .zero) one (eqAt (.bvar 0) (.bvar 0)) .zero

/-- The stored telescope after its first argument is also a proposition,
although its domain is `Prop : Sort 1`. -/
def partialReflTypePropTypedA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ partialReflPropTypeA3 (.sort .zero) := by
  have hv : HasTyA env (iotaIfaceA env) 0 (.assumption (.sort .zero) :: Γ)
      (.bvar 0) (.sort .zero) :=
    .bvar _ 0 (.sort .zero) one rfl (.sort _ .zero)
  exact hasTyA_sortEqN
    (.pi Γ (.sort .zero) one (eqAt (.bvar 0) (.bvar 0)) .zero (.sort Γ .zero)
      (eqTyped (.assumption hΓ (.sort Γ .zero)) hv hv)) (fun _ => rfl)

theorem reflStoredSortHeightA3 (ρ : Nat → Nat) : ht ρ reflSort = 0 := rfl

end ReflProvenance

#print axioms HeadTypingSourceA3
#print axioms HeadTypingSourceA3.const
#print axioms HeadTypingSourceA3.app
#print axioms HeadTypingSourceA3.conv
#print axioms ReflProvenance.fixedReflOriginalSpineA3
#print axioms ReflProvenance.reflTypePropTypedA3
#print axioms ReflProvenance.partialReflPropTypeA3
#print axioms ReflProvenance.partialReflTypePropTypedA3
#print axioms ReflProvenance.reflStoredSortHeightA3

end Rcic.Declarative.Ann.LR3
