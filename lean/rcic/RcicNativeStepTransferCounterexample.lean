import rcic.RcicNativeValleyDecoTransfer
import rcic.RcicNativeDecoLeafIface
import rcic.RcicNativeStepTransfer

/-!
# An admitted counterexample to single-step decoration transfer

The existing `LeafIface` does not prescribe the decorations returned by
`typed`.  Here that function always tags lambda domain sorts by `max u 0`.
This preserves the native typing, but makes syntactic tag `0` unavailable
at every proof leaf.  A non-eta lambda can step to a let expression only
through such a leaf (possibly beneath index conversions and iota spines).
The resulting obstruction concerns *all* alternate certified steps, not
merely `ofIrr` or `CStep.reindex`.

The source and target are closed proofs in `emptyEnv`; no `NotProof`,
consistency, uniqueness, sort row, or diamond hypothesis is used.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StepTransferCounterexample

private theorem max_zero_eq (u : Level) : eqN u (.max u .zero) := by
  intro ρ
  cases h : eval ρ u <;> simp [eval, h]

private def retag {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → HasTyT E n Γ e T
  | _, _, _, .lam Γ A u body B hA hb =>
      .lam Γ A (.max u .zero) body B
        (.conv Γ A (.sort u) (.sort (.max u .zero)) (.succ u) hA
          (.sorts Γ u (.max u .zero) (max_zero_eq u))) hb
  | _, _, _, .conv Γ e A B u h hc => .conv Γ e A B u (retag h) hc
  | _, _, _, h => h

private abbrev ProofData (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (p q P : Expr Nat) : Type :=
  HasTyT E n Γ P (.sort .zero) × (HasTyT E n Γ p P × HasTyT E n Γ q P)

private def taggedIface (E : ResolvedEnv) (n : Nat) :
    LeafIface E n (ProofData E n) where
  typed := fun h => ⟨retag h.2.1, retag h.2.2⟩
  conv := fun h => .irr _ _ _ _ h.1 h.2.1 h.2.2
  prop := fun h => h.1
  ofIrr := fun hP hp hq => ⟨hP, hp, hq⟩

private def lamSort : {e : Expr Nat} → Deco e → Option Level
  | _, .lam _ _ u _ _ => some u
  | _, _ => none

private theorem retag_ne_zero {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (h : HasTyT E n Γ e T) →
    lamSort (decoOf (retag h)) ≠ some .zero
  | _, _, _, .sort .. => by intro h; cases h
  | _, _, _, .bvar .. => by intro h; cases h
  | _, _, _, .const .. => by intro h; cases h
  | _, _, _, .pi .. => by intro h; cases h
  | _, _, _, .lam .. => by intro h; cases h
  | _, _, _, .app .. => by intro h; cases h
  | _, _, _, .letE .. => by intro h; cases h
  | _, _, _, .lit .. => by intro h; cases h
  | _, _, _, .conv _ _ _ _ _ h _ => retag_ne_zero h

/-- The only recursive calls peel the original `Certified.conv` child
or the original `Certified.iotaSpine` child.  The latter child must land
on a lambda, contradicting the native iota source shape. -/
private theorem lamStep_target {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A b : Expr Nat}
    (hne : ∀ g : Expr Nat, b ≠ .app (lift 0 1 g) (.bvar 0)) :
    {x j T : Expr Nat} → {p : ParRedT (ProofData E n) E n Γ x j T} →
    Certified p → x = .lam A b →
    lamSort (stepDeco (taggedIface E n) p) = some .zero →
    ∃ A' b' : Expr Nat, j = .lam A' b'
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx, _ => by
      subst hx
      exact ⟨A, b, rfl⟩
  | _, _, _, _, @Certified.lam _ _ _ _ _ A' _ b' _ _ _ _ _ _ _ _ _ _, _, _ =>
      ⟨A', b', rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, hx, hd =>
      lamStep_target hne ch hx hd
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, _, hd =>
      (retag_ne_zero h.2.1 hd).elim
  | _, _, _, _, @Certified.eta _ _ _ _ g _ _ _ _ _ _ _, hx, _ => by
      injection hx with _ h2
      exact (hne g h2.symm).elim
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, hx, hd => by
      obtain ⟨A', b', e⟩ := lamStep_target hne cs hx hd
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl
  | _, _, _, _, .sortEq .., hx, _ => nomatch hx
  | _, _, _, _, .consts .., hx, _ => nomatch hx
  | _, _, _, _, .bvarZeta .., hx, _ => nomatch hx
  | _, _, _, _, .delta .., hx, _ => nomatch hx
  | _, _, _, _, .app .., hx, _ => nomatch hx
  | _, _, _, _, .beta .., hx, _ => nomatch hx
  | _, _, _, _, .pi .., hx, _ => nomatch hx
  | _, _, _, _, .letE .., hx, _ => nomatch hx
  | _, _, _, _, .zeta .., hx, _ => nomatch hx
  | _, _, _, _, .lit .., hx, _ => nomatch hx

private abbrev I : Expr Nat := .pi etaLeafP etaLeafP
private abbrev p : Expr Nat := .lam etaLeafP (.bvar 0)
private abbrev q : Expr Nat := .letE I p (.bvar 0)

private def hI (Γ : LCtx) : HasTyT emptyEnv 0 Γ I (.sort .zero) :=
  .conv Γ I (.sort (.imax .zero .zero)) (.sort .zero)
    (.succ (.imax .zero .zero))
    (.pi Γ etaLeafP .zero etaLeafP .zero (etaLeafP_ty Γ) (etaLeafP_ty _))
    (.sorts Γ (.imax .zero .zero) .zero (eqN_imax_zero_right .zero))

private def hp : HasTyT emptyEnv 0 [] p I :=
  .lam [] etaLeafP .zero (.bvar 0) etaLeafP (etaLeafP_ty []) (.bvar _ 0 _ rfl)

private def hq : HasTyT emptyEnv 0 [] q I :=
  .letE [] I .zero p I (.bvar 0) (hI []) hp (.bvar _ 0 _ rfl)

private def s : CStep emptyEnv 0 (ProofData emptyEnv 0) [] p q I :=
  CStep.irr (taggedIface emptyEnv 0) (hI []) hp hq

private theorem no_transfer
    (s' : CStep emptyEnv 0 (ProofData emptyEnv 0) [] p q I) :
    stepDeco (taggedIface emptyEnv 0) s'.step ≠ decoOf hp := by
  intro hd
  have hz : lamSort (stepDeco (taggedIface emptyEnv 0) s'.step) = some .zero := by
    rw [hd]
    rfl
  obtain ⟨A', b', heq⟩ := lamStep_target
    (by intro g h; cases h) s'.cert rfl hz
  cases heq

/-- A lawful proof-leaf interface in an explicitly admitted environment
refutes the exact single-step contract of `RcicNativeValleyDecoTransfer`.
The obstruction quantifies over every alternative certified step. -/
theorem admitted_single_step_transfer_false :
    ∃ (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
      (L : LeafIface emptyEnv 0 PEq),
      Nonempty (EnvWfT emptyEnv) ∧ ¬ Nonempty (StepDecoTransfer emptyEnv 0 PEq L) := by
  refine ⟨ProofData emptyEnv 0, taggedIface emptyEnv 0, ⟨.empty⟩, ?_⟩
  intro ⟨transfer⟩
  obtain ⟨s', hs'⟩ := transfer .nil s (decoOf hp) ⟨hp, rfl⟩
  exact no_transfer s' hs'

/-- On exactly the same admitted fixture, the coherent-star replacement
does produce a path with the requested source decoration. -/
theorem admitted_coherent_transfer_survives :
    ∃ (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
      (L : LeafIface emptyEnv 0 PEq)
      (b e T : Expr Nat) (h : HasTyT emptyEnv 0 [] b T)
      (step : CStep emptyEnv 0 PEq [] b e T),
      ¬ (∃ step' : CStep emptyEnv 0 PEq [] b e T, stepDeco L step'.step = decoOf h) ∧
      ∃ star : CStar emptyEnv 0 PEq [] b e T,
        DecoStarAudit.Coherent L .nil star ∧
        decoOf (star.leftTyped L .nil) = decoOf h := by
  refine ⟨ProofData emptyEnv 0, taggedIface emptyEnv 0, p, q, I, hp, s, ?_, ?_⟩
  · rintro ⟨s', hs'⟩
    exact no_transfer s' hs'
  · obtain ⟨star, hstar⟩ := StepTransferAudit.coherentStepOf_typing
      EnvWfT.empty (taggedIface emptyEnv 0) CtxWfT.nil hp s
    exact ⟨star, hstar⟩

#print axioms admitted_single_step_transfer_false
#print axioms admitted_coherent_transfer_survives

end Rcic.Declarative.NativeValleys.StepTransferCounterexample
