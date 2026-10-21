import rcic.RcicF8JLetFixed
/-! # `RcicF8JLetFixedPins` — J-LET-FIXED §7 live mutant: `let` reusing the
    old value.

A `LetELiftPair` bundles two REAL typed objects: an actual child body star
that ran under `.letBinding A vCtx :: Γ`, and a lifted chain centred at
`letE A vCentre`. The weak check accepts any pair whose members exist — it
never compares `vCtx` with `vCentre`. `oldValuePair` is LIVE data: the body
star genuinely ran under the `vNew`-binding while the centre names `vOld`
— the exact predicate refuses it because the stored values differ.

The production lemma `parRedTStar_letE_body` cannot produce this pair: its
TYPE binds the child context and the centre to the same `value`. The mutant
is the weak acceptance of the pairing, not a fake derivation. -/
set_option autoImplicit false
namespace Rcic.Declarative

/-- A claimed letE-lift pairing: an actual child body star under the
    `.letBinding A vCtx` context, and a lifted chain centred at
    `letE A vCentre` with the child's endpoints and index. Both members
    are real typed objects — the check is what pairs them. -/
structure LetELiftPair (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  A : Expr Nat
  vCtx : Expr Nat
  vCentre : Expr Nat
  b : Expr Nat
  N : Expr Nat
  s : Level
  body : ParRedTStar (PEqLeafT E n) E n (.letBinding A vCtx :: Γ) b N (.sort s)
  lifted : ParRedTStar (PEqLeafT E n) E n Γ
    (.letE A vCentre b) (.letE A vCentre N) (.sort s)

/-- The WEAK check (the §7 mutant): the pair is accepted as soon as its two
    members exist — the stored value the body actually ran under is never
    compared with the value the lifted centre names. -/
def weakLetELift {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (_p : LetELiftPair E n Γ) : Prop := True

/-- The exact check: the lifted centre's stored value must be the one the
    child's context actually carried. -/
def exactLetELift {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (p : LetELiftPair E n Γ) : Prop := p.vCentre = p.vCtx

/-- `Sort 1 : Sort 2`, typed — the old stored value, at `A₀ = Sort 2`. -/
def jlf_vOld {E : ResolvedEnv} {n : Nat} :
    HasTyT E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)

/-- `letE (Sort 1) (Sort 0) (Sort 1) : Sort 2`, typed — a second, DISTINCT
    inhabitant of `A₀`, built along its own introduction path. -/
def jlf_vNew {E : ResolvedEnv} {n : Nat} :
    HasTyT E n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.sort (.succ .zero)))
      (.sort (.succ (.succ .zero))) :=
  .letE [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
      (.sort [] (.succ .zero))
      (.sort [] .zero)
      (.sort _ (.succ .zero))

/-- The LIVE wrong pair: the body star ran under `.letBinding A₀ vNew`
    (the actually-stored value is `vNew`), while the lifted centre names
    `vOld` — the "reused old value" shape of §7. Every member is a real
    typed object: `body` is the genuine reflexive chain under the `vNew`
    binding, `lifted` is the production lift applied to the `vOld`-run
    body chain. -/
def jlf_oldValuePair (E : ResolvedEnv) (n : Nat) : LetELiftPair E n [] where
  A := .sort (.succ (.succ .zero))
  vCtx := .letE (.sort (.succ .zero)) (.sort .zero) (.sort (.succ .zero))
  vCentre := .sort (.succ .zero)
  b := .sort (.succ .zero)
  N := .sort (.succ .zero)
  s := .succ (.succ .zero)
  body := .refl _ _ _
    (.sort _ (.succ .zero) :
      HasTyT E n
        (.letBinding (.sort (.succ (.succ .zero)))
          (.letE (.sort (.succ .zero)) (.sort .zero) (.sort (.succ .zero))) :: [])
        (.sort (.succ .zero)) (.sort (.succ (.succ .zero))))
  lifted := parRedTStar_letE_body_sort_peqLeafT .nil
    (.sort [] (.succ (.succ .zero)) :
      HasTyT E n [] (.sort (.succ (.succ .zero))) (.sort (.succ (.succ (.succ .zero)))))
    jlf_vOld
    (.refl _ _ _
      (.sort _ (.succ .zero) :
        HasTyT E n
          (.letBinding (.sort (.succ (.succ .zero))) (.sort (.succ .zero)) :: [])
          (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))))

/-- The mutant ACCEPTS under the weak check: the pair is genuine typed data
    and the weak check never compares the stored values. -/
theorem jlf_mutant_accepts {E : ResolvedEnv} {n : Nat} :
    weakLetELift (jlf_oldValuePair E n) := trivial

/-- The exact check REFUSES the same pair: `vNew ≠ vOld` — the lifted
    centre names a stored value the body never ran under. -/
theorem jlf_exact_refuses {E : ResolvedEnv} {n : Nat} :
    ¬ exactLetELift (jlf_oldValuePair E n) :=
  fun h => Expr.noConfusion h

/-- The production lemma's own output always satisfies the exact check:
    its type binds context and centre to the same `value`. -/
theorem jlf_lift_exact {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A value b b' : Expr Nat} {u s : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ value A)
    (hs : ParRedTStar (PEqLeafT E n) E n (.letBinding A value :: Γ) b b' (.sort s)) :
    exactLetELift
      ⟨A, value, value, b, b', s, hs,
        parRedTStar_letE_body_sort_peqLeafT hΓ hA hv hs⟩ :=
  rfl

end Rcic.Declarative
