import rcic.RcicNativeValleyCert
import rcic.RcicParRedTSubst
import rcic.RcicDTMetaTypedSR

/-!
# Data-valued host-Prop transfer from explicit zero-sort coherence

The main worker recurses only on its original `HasTyT` argument. Inverted
typings, regularity outputs, and substitution outputs are never recursive
subjects. `ZeroSortCoherence` is explicit; no Pi row, same-term type
uniqueness, diamond, valley supplier, or choice is used.

The returned function has the exact type of
`ProofSourceAudit.HostPropData`; no import of that separate audit file is
needed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.HostPropAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The explicit zero fragment of sort coherence. This file does not
    construct it from `EnvWfT`. -/
def ZeroSortCoherence (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E → ∀ {Γ : LCtx} {A : Expr Nat} {u : Level},
    CtxWfT E n Γ → HasTyT E n Γ A (.sort u) →
    HasTyT E n Γ A (.sort .zero) → eqN u .zero

private theorem imax_zero (u : Level) : eqN (.imax u .zero) .zero := by
  intro ρ
  rfl

private theorem imax_zero_right {u v : Level}
    (h : eqN (.imax u v) .zero) : eqN v .zero := by
  intro ρ
  change eval ρ v = some 0
  have hρ := h ρ
  change (eval ρ v).bind (fun k =>
    if k = 0 then some 0 else (eval ρ u).map (fun j => max j k)) = some 0 at hρ
  cases hv : eval ρ v with
  | none => simp [hv] at hρ
  | some k =>
      by_cases hk : k = 0
      · simp [hv, hk]
      · cases hu : eval ρ u with
        | none => simp [hv, hk, hu] at hρ
        | some j =>
            have hz : max j k = 0 := by simpa [hv, hk, hu] using hρ
            have hle := Nat.le_max_right j k
            have hk0 : k = 0 := by omega
            exact (hk hk0).elim

private theorem succ_not_zero (u : Level) : ¬ eqN (.succ u) .zero := by
  intro h
  have hρ := h (fun _ => none)
  change (eval (fun _ => none) u).map (fun k => k + 1) = some 0 at hρ
  cases hu : eval (fun _ => none) u <;> simp [hu] at hρ

/-- Move a sorting along a supplied equality with zero. -/
private def atProp {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hu : eqN u .zero) :
    HasTyT E n Γ A (.sort .zero) :=
  .conv Γ A (.sort u) (.sort .zero) (.succ u) hA (.sorts Γ u .zero hu)

private def regularData (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (h : HasTyT E n Γ e T) :
    Σ' u, HasTyT E n Γ T (.sort u) :=
  regularT_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ h

/-- Prop sorting transports along an original native type chain.
    Recursion is only on that chain's proper `TyConvT` children. -/
def sort_transport0_data (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B →
    HasTyT E n Γ A (.sort .zero) → HasTyT E n Γ B (.sort .zero)
  | _, _, .refl _ _, hA => hA
  | _, _, .of _ _ _ _ c, hA =>
      let ends := endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
        (constsRightDataT_of_envWfT hW) hΓ c
      atProp ends.2.1 (zsc hW hΓ ends.1 hA)
  | _, _, .trans _ _ _ _ c₁ c₂, hA =>
      sort_transport0_data hW zsc hΓ c₂
        (sort_transport0_data hW zsc hΓ c₁ hA)

private theorem sort_not_prop (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u : Level}
    (h : HasTyT E n Γ (.sort u) (.sort .zero)) : False :=
  succ_not_zero u (zsc hW hΓ (.sort Γ u) h)

/-- A Prop-sorted Pi has a Prop-sorted codomain. Its inversion residue
    is unused; zero-sort coherence compares two sortings of this same Pi. -/
def pi_codomain_prop_data (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat}
    (hPi : HasTyT E n Γ (.pi A B) (.sort .zero)) :
    HasTyT E n (.assumption A :: Γ) B (.sort .zero) := by
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hPi rfl
  have hzero := zsc hW hΓ (.pi Γ A u B v hA hB) hPi
  exact atProp hB (imax_zero_right hzero)

private def piProp {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort .zero)) :
    HasTyT E n Γ (.pi A B) (.sort .zero) :=
  atProp (.pi Γ A u B .zero hA hB) (imax_zero u)

private abbrev ProofWitness (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (e : Expr Nat) : Type :=
  Σ' P, HasTyT E n Γ P (.sort .zero) ×' HasTyT E n Γ e P

/-- External proofhood of an application gives external proofhood of its
    function, using only its own application-typing data. -/
private def app_function_proof (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ (.app f a) P) : ProofWitness E n Γ f := by
  obtain ⟨A, B, hf, ha, c⟩ := hasTyTInv_app hp rfl
  obtain ⟨_, hPi⟩ := regularData hW hΓ hf
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hPi rfl
  have hres0 := sort_transport0_data hW zsc hΓ c.symmT hP
  have hres : HasTyT E n Γ (instantiate0 a B) (.sort v) :=
    hasTyT_subst0S (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) hB ha
  have hB0 := atProp hB (zsc hW hΓ hres hres0)
  exact ⟨.pi A B, piProp hA hB0, hf⟩

private def lam_body_proof (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ (.lam A body) P) :
    ProofWitness E n (.assumption A :: Γ) body := by
  obtain ⟨_, B, _, hb, c⟩ := hasTyTInv_lam hp rfl
  have hPi := sort_transport0_data hW zsc hΓ c.symmT hP
  exact ⟨B, pi_codomain_prop_data hW zsc hΓ hPi, hb⟩

/-- The context here uses the original domain and value typings. No
    changed-let context or generated typing is sent to the main recursion. -/
private def let_body_proof (hW : EnvWfT E) (zsc : ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A value body P : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ (.letE A value body) P) :
    ProofWitness E n (.letBinding A value :: Γ) body := by
  obtain ⟨_, B, _, _, hb, c⟩ := hasTyTInv_letE hp rfl
  let hΓL : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A u value hΓ hA hv
  obtain ⟨v, hB⟩ := regularData hW hΓL hb
  have hres0 := sort_transport0_data hW zsc hΓ c.symmT hP
  have hres : HasTyT E n Γ (instantiate0 value B) (.sort v) :=
    hasTyT_substLet0_of_envWfT hW hB hv
  exact ⟨B, atProp hB (zsc hW hΓ hres hres0), hb⟩

/-- The sole host-transfer recursion. Its measured argument is always
    an original typing child: lambda body, function, let body, expansion,
    or conversion premise. -/
private def hostPropWorker (hW : EnvWfT E) (zsc : ZeroSortCoherence E n) :
    {Γ : LCtx} → {e T : Expr Nat} → (D : HasTyT E n Γ e T) →
    CtxWfT E n Γ → {P : Expr Nat} →
    HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ e P →
    HasTyT E n Γ T (.sort .zero)
  | _, _, _, .sort _ _, hΓ, _, hP, hp =>
      sort_transport0_data hW zsc hΓ (hasTyTInv_sortT hp rfl).symmT hP
  | _, _, _, .bvar _ _ _ hlk, hΓ, _, hP, hp => by
      obtain ⟨A', hlk', c⟩ := hasTyTInv_bvar hp rfl
      obtain rfl : A' = _ := Option.some.inj (hlk'.symm.trans hlk)
      exact sort_transport0_data hW zsc hΓ c.symmT hP
  | _, _, _, .const _ _ _ _ hres _ _, hΓ, _, hP, hp => by
      obtain ⟨m', hres', _, _, c⟩ := hasTyTInv_const hp rfl
      obtain rfl : m' = _ := Option.some.inj (hres'.symm.trans hres)
      exact sort_transport0_data hW zsc hΓ c.symmT hP
  | _, _, _, .pi _ _ _ _ _ _ _, hΓ, _, hP, hp => by
      obtain ⟨_, _, _, _, c⟩ := hasTyTInv_pi hp rfl
      exact (sort_not_prop hW zsc hΓ
        (sort_transport0_data hW zsc hΓ c.symmT hP)).elim
  | Γ, _, _, .lam _ A u _ _ hA hb, hΓ, _, hP, hp => by
      obtain ⟨Q, hQ, hbQ⟩ := lam_body_proof hW zsc hΓ hP hp
      have hB0 := hostPropWorker hW zsc hb (.assumption Γ A u hΓ hA) hQ hbQ
      exact piProp hA hB0
  | _, _, _, .app _ _ _ _ _ hf ha, hΓ, _, hP, hp => by
      obtain ⟨Q, hQ, hfQ⟩ := app_function_proof hW zsc hΓ hP hp
      have hPi0 := hostPropWorker hW zsc hf hΓ hQ hfQ
      have hB0 := pi_codomain_prop_data hW zsc hΓ hPi0
      exact hasTyT_subst0S (envClosed_of_envWfT hW)
        (envMembersSubstStable_of_envWfT hW) hB0 ha
  | Γ, _, _, .letE _ A u value _ _ hA hv hb, hΓ, _, hP, hp => by
      obtain ⟨Q, hQ, hbQ⟩ := let_body_proof hW zsc hΓ hA hv hP hp
      have hB0 := hostPropWorker hW zsc hb
        (.letBinding Γ A u value hΓ hA hv) hQ hbQ
      exact hasTyT_substLet0_of_envWfT hW hB0 hv
  | _, _, _, .lit _ _ _ hexp, hΓ, _, hP, hp => by
      obtain ⟨_, hnat, c⟩ := hasTyTInv_lit hp rfl
      exact hostPropWorker hW zsc hexp hΓ hP (hasTyT_of_tyConvT hnat c)
  | _, _, _, .conv _ _ _ _ _ h c, hΓ, _, hP, hp =>
      sort_transport0_data hW zsc hΓ (.of _ _ _ _ c)
        (hostPropWorker hW zsc h hΓ hP hp)
termination_by _ _ _ D _ _ _ _ => sizeOf D
decreasing_by all_goals (simp; omega)

/-- A constructed data-valued host-Prop transfer function, conditional only
    on the explicitly stated zero-sort coherence and admitted environment. -/
def hostPropData_of_zeroSortCoherence (hW : EnvWfT E)
    (zsc : ZeroSortCoherence E n) :
    ∀ {Γ : LCtx} {b T P : Expr Nat},
      CtxWfT E n Γ → HasTyT E n Γ b T →
      HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ b P →
      HasTyT E n Γ T (.sort .zero) :=
  fun hΓ hb hP hbP => hostPropWorker hW zsc hb hΓ hP hbP

#print axioms sort_transport0_data
#print axioms pi_codomain_prop_data
#print axioms hostPropData_of_zeroSortCoherence

end Rcic.Declarative.NativeValleys.HostPropAudit
