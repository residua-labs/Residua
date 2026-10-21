import rcic.RcicAnnFrecWorld

/-!
# R-NoFunRec-1 step 1 (1c-ε2d-L3b-3b): a λ-telescope applied to its arguments, in substitution form

The λ-wrapped recursor call at a function-recursive field is a λ-telescope over the field domain's
inner binders. Its full application to related arguments is the call at those arguments: a chain of
typed β-steps, one per binder. The steps are built in substitution form — a λ-telescope under a typed
substitution `τ` is `lamTelA (substTelA τ ds) (substA (upNA m τ) b)` — by induction on the typed binders
(`lamTel_chain`), the head step lifted through the remaining applications from the explicit Π-telescope
(`tyHRedA_spine`), so no application inversion is needed. A weakening is such a substitution
(`wkSubstA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Beta
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem substA_lamTelA : (ds : List (ExprA × Level)) → (σ : SubstA) → (b : ExprA) →
    substA σ (lamTelA ds b) = lamTelA (substTelA σ ds) (substA (upNA ds.length σ) b)
  | [], _, _ => rfl
  | (D, u) :: ds, σ, b => by
      simp only [lamTelA, substA_lam, substTelA, List.length_cons]
      rw [substA_lamTelA ds σ.up b]
      rfl

/-- the head binder of a substituted λ-telescope instantiated: the telescope under the extended
    substitution. -/
theorem instantiate0A_lamTelA_subst (a : ExprA) (τ : SubstA) (ds : List (ExprA × Level)) (b : ExprA) :
    instantiate0A a (lamTelA (substTelA τ.up ds) (substA (upNA ds.length τ.up) b)) =
      lamTelA (substTelA (SubstA.cons a τ) ds) (substA (upNA ds.length (SubstA.cons a τ)) b) := by
  have hpt : ∀ i, substA (SubstA.cons a SubstA.id) (τ.up i) = SubstA.cons a τ i := fun i => by
    cases i with
    | zero => rfl
    | succ i =>
        show substA (SubstA.cons a SubstA.id) (liftA 0 1 (τ i)) = τ i
        rw [substA_cons_liftA, substA_id]
  rw [instantiate0A_eq_substA_cons, substA_lamTelA, substTelA_length,
    substTelA_substTelA ds τ.up (SubstA.cons a τ) (SubstA.cons a SubstA.id) hpt]
  congr 1
  rw [substA_substA]
  refine substA_ext (fun i => ?_) b
  by_cases hlt : i < ds.length
  · rw [upNA_lt _ _ i hlt, substA_bvar, upNA_lt _ _ i hlt, upNA_lt _ _ i hlt]
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + ds.length := ⟨i - ds.length, by omega⟩
    rw [upNA_add, upNA_add, substA_liftNA, hpt q]


theorem instantiate0A_sort' (a : ExprA) (v : Level) : instantiate0A a (.sort v) = .sort v := rfl

/-- a head step lifted through the applications that follow it, each premise typed from the explicit
    Π-telescope the head's type is (arguments typed along it). -/
theorem tyHRedA_spine (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) :
    {T₀ : ExprA} → {as : List ExprA} → ConvArgsA E I n Δ T₀ as as → {U : ExprA} →
    applyTelA as T₀ = some U → {f f' : ExprA} → HasTyA E I n Δ f T₀ →
    TyHRedA E I n Δ f f' T₀ → Nonempty (TyHRedA E I n Δ (foldAppsA f as) (foldAppsA f' as) U)
  | _, _, .nil _, _, hU, _, _, _, h => by
      injection hU with hU
      subst hU
      exact ⟨h⟩
  | _, _, .cons A u B v x _ xs _ ⟨c⟩ hs, U, hU, f, f', hf, h => by
      obtain ⟨_, hT⟩ := hasTyA_regular hE hI hR hIS hΔ hf
      obtain ⟨⟨hA⟩, ⟨hB⟩⟩ := hasTyA_pi_inv hT
      have hx := convA_hasTy_left hE hI hR hIS hΔ c
      have hTy : HasTyA E I n Δ (instantiate0A x B) (.sort v) := by
        have := hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΔ hB hx hA
        exact this
      have h' := TyHRedA.app Δ f f' x A B (.pi A u B v) u v v h (.refl _ _) hB hTy hx
      exact tyHRedA_spine hE hI hR hIS hΔ hs hU (HasTyA.app Δ f x A B u v v hB hTy hf hx) h'

/-- A λ-TELESCOPE APPLIED TO ITS ARGUMENTS reduces, by typed β-steps one per binder, to its body at them
    (R-NoFunRec-1 step 1 (1c-ε2d-L3b-3b)): under a typed substitution `τ`, the λ-telescope over the
    substituted binders around the substituted body, applied to arguments typed along the substituted
    Π-telescope, is a chain at the instance of the codomain to the body under the arguments. -/
theorem lamTel_chain (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    {Θ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Θ ds → {b B : ExprA} → {w : Level} →
    HasTyA E I n (telCtxA ds ++ Θ) B (.sort w) → HasTyA E I n (telCtxA ds ++ Θ) b B →
    {Δ : LCtxA} → CtxWfA E I n Δ → {τ : SubstA} → SubstTyA E I n Δ τ Θ → {as : List ExprA} →
    as.length = ds.length → ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as →
    Nonempty (TmChainA E I n Δ (substA (consListA as τ) B)
      (foldAppsA (lamTelA (substTelA τ ds) (substA (upNA ds.length τ) b)) as) (substA (consListA as τ) b))
  | _, _, .nil _, b, B, _, _, hb, _, _, _, hτ, as, hl, _ => by
      cases as with
      | nil => exact ⟨.refl _ (hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hτ hb)⟩
      | cons _ _ => exact absurd hl (Nat.succ_ne_zero _)
  | Θ, _, .cons _ D u ds hD tl, b, B, w, hB, hb, Δ, hΔ, τ, hτ, as, hl, hargs => by
      cases as with
      | nil => exact absurd hl.symm (Nat.succ_ne_zero _)
      | cons a as₂ =>
          have hRt := iotaRecHeadTypedA_of hR
          have e := telCtxA_cons_append (D, u) ds Θ
          rw [e] at hB hb
          simp only [piTelA, substA_pi] at hargs
          cases hargs with
          | cons _ _ _ _ _ _ _ _ hca hs =>
              obtain ⟨ca⟩ := hca
              have ha : HasTyA E I n Δ a (substA τ D) := convA_hasTy_left hE hI hR hIS hΔ ca
              have hD' : HasTyA E I n Δ (substA τ D) (.sort u) := hasTyA_substA hE hI hRt hIS hτ hD
              have hτ₁ : SubstTyA E I n Δ (SubstA.cons a τ) (.assumption D :: Θ) := substTyA_cons hτ ha
              have hs' : ConvArgsA E I n Δ (substA (SubstA.cons a τ) (piTelA ds B w).1) as₂ as₂ := by
                rw [← instantiate0A_substA_up]; exact hs
              obtain ⟨ih⟩ := lamTel_chain hE hI hR hIS tl hB hb hΔ hτ₁ (Nat.succ.inj hl) hs'
              obtain ⟨tel', hσ⟩ := TelTyA.subst hE hI hR hIS tl (substTyA_up hE hI hτ hD')
              have hB₂ := hasTyA_substA hE hI hRt hIS hσ hB
              have hb₂ := hasTyA_substA hE hI hRt hIS hσ hb
              have hbody : HasTyA E I n (.assumption (substA τ D) :: Δ)
                  (lamTelA (substTelA τ.up ds) (substA (upNA ds.length τ.up) b))
                  (substA τ.up (piTelA ds B w).1) := by
                rw [substA_piTelA]; exact hasTyA_lamTelA tel' hB₂ hb₂
              have hred : HasTyA E I n Δ
                  (instantiate0A a (lamTelA (substTelA τ.up ds) (substA (upNA ds.length τ.up) b)))
                  (instantiate0A a (substA τ.up (piTelA ds B w).1)) :=
                hasTyA_inst0 hE hI hRt hIS hΔ hbody ha hD'
              have hβ := TyHRedA.beta Δ (substA τ D) u
                (lamTelA (substTelA τ.up ds) (substA (upNA ds.length τ.up) b)) a
                (substA τ.up (piTelA ds B w).1) hD' hbody ha hred
              have hBpi : HasTyA E I n (.assumption (substA τ D) :: Δ) (substA τ.up (piTelA ds B w).1)
                  (.sort (piTelA ds B w).2) := by
                rw [substA_piTelA, ← piTelA_snd_substTelA B (substA (upNA ds.length τ.up) B) w ds τ.up]
                exact hasTyA_piTelA tel' hB₂
              have hlam : HasTyA E I n Δ
                  (.lam (substA τ D) u (lamTelA (substTelA τ.up ds) (substA (upNA ds.length τ.up) b)))
                  (.pi (substA τ D) u (substA τ.up (piTelA ds B w).1) (piTelA ds B w).2) :=
                .lam Δ _ u _ _ _ hD' hBpi hbody
              have hTy : HasTyA E I n Δ (instantiate0A a (substA τ.up (piTelA ds B w).1))
                  (.sort (piTelA ds B w).2) := hasTyA_inst0 hE hI hRt hIS hΔ hBpi ha hD'
              have hf : HasTyA E I n Δ
                  (.app (.lam (substA τ D) u (lamTelA (substTelA τ.up ds)
                    (substA (upNA ds.length τ.up) b))) a)
                  (instantiate0A a (substA τ.up (piTelA ds B w).1)) :=
                .app Δ _ a _ _ u _ _ hBpi hTy hlam ha
              have hU : applyTelA as₂ (instantiate0A a (substA τ.up (piTelA ds B w).1)) =
                  some (substA (consListA as₂ (SubstA.cons a τ)) B) := by
                rw [instantiate0A_substA_up]
                exact applyTelA_piTelA B w ds as₂ (Nat.succ.inj hl) (SubstA.cons a τ)
              obtain ⟨hstep⟩ := tyHRedA_spine hE hI hR hIS hΔ hs hU hf hβ
              obtain ⟨cs⟩ := convA_spine hE hI hR hIS hΔ hs ⟨.refl Δ _ _ hf⟩ _ hU
              have ha₀ := convA_hasTy_left hE hI hR hIS hΔ cs
              rw [instantiate0A_lamTelA_subst] at hstep
              exact ⟨TmChainA.cons _ _ _ ha₀ hstep ih⟩

/-- a chain at `A` expands the relation on the left. -/
theorem LRRelA_expand_chain_left (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A : ExprA} :
    {a N : ExprA} → TmChainA E I n Γ A a N → ∀ {b : ExprA}, LRRelA E I n ρ₀ k Γ A N b →
      LRRelA E I n ρ₀ k Γ A a b
  | _, _, .refl _ _, _, h => h
  | _, _, .cons _ _ _ ha hs t, _, h =>
      LRRelA_expand_left hE hI ⟨⟨ha⟩, ⟨hs⟩⟩ (LRRelA_expand_chain_left hE hI t h)

/-- a chain at `A` expands the relation on the right. -/
theorem LRRelA_expand_chain_right (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A : ExprA} :
    {b N : ExprA} → TmChainA E I n Γ A b N → ∀ {a : ExprA}, LRRelA E I n ρ₀ k Γ A a N →
      LRRelA E I n ρ₀ k Γ A a b
  | _, _, .refl _ _, _, h => h
  | _, _, .cons _ _ _ ha hs t, _, h =>
      LRRelA_expand_right hE hI ⟨⟨ha⟩, ⟨hs⟩⟩ (LRRelA_expand_chain_right hE hI t h)


/-- a chain at `A` is a chain at a convertible type. -/
theorem tmChainA_tyConv {Γ : LCtxA} {A A' : ExprA} (hc : Nonempty (TyConvA E I n Γ A A')) :
    {a N : ExprA} → TmChainA E I n Γ A a N → Nonempty (TmChainA E I n Γ A' a N)
  | _, _, .refl a h => hc.elim fun c => ⟨.refl a (hasTyA_of_tyConvA h c)⟩
  | _, _, .cons a a' N ha hs t => by
      obtain ⟨⟨ha'⟩, ⟨hs'⟩⟩ := stepAtA_tyConv (E := E) (I := I) (n := n) ⟨⟨ha⟩, ⟨hs⟩⟩ hc
      obtain ⟨t'⟩ := tmChainA_tyConv hc t
      exact ⟨.cons a a' N ha' hs' t'⟩

/-- a weakening is a substitution. -/
def wkSubstA (ρ : WkSpecA) : SubstA := fun i => wkExprA ρ (.bvar i)

theorem wkExprA_eq_substA (ρ : WkSpecA) (e : ExprA) : wkExprA ρ e = substA (wkSubstA ρ) e := by
  have h := wkExprA_substA ρ SubstA.id e
  rw [substA_id] at h
  exact h

/-- the weakening substitution is typed. -/
def substTyA_wkSubstA (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ) : SubstTyA E I n (wkCtxA ρ Γ) (wkSubstA ρ) Γ where
  ty := fun i A h => by
    have h1 := (substTyA_id hE hI hΓ).ty i A h
    rw [substA_id] at h1
    have h2 := hasTyA_wk hE hI Γ ρ hρ h1
    rw [wkExprA_eq_substA ρ A] at h2
    exact h2
  val := fun i A v hA hv => by
    have h1 := (substTyA_id hE hI hΓ).val i A v hA hv
    rw [substA_id, substA_id] at h1
    have h2 := convA_wk hE hI Γ ρ hρ h1
    rw [wkExprA_eq_substA ρ A, wkExprA_eq_substA ρ v] at h2
    exact h2

/-- the values past a list's length: a lift by the length is cancelled. -/
theorem substA_consListA_liftNA (as : List ExprA) (τ : SubstA) (e : ExprA) :
    substA (consListA as τ) (liftNA as.length e) = substA τ e := by
  rw [liftNA_eq]; exact substA_consListA_liftA as τ e

/-- THE RELATION EXPANDS ALONG THE λ-TELESCOPE'S APPLICATION, on the left: related at the body under the
    arguments, the application is related there. -/
theorem lrRelA_lamTel_apps_left (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {k : Nat} {Θ : LCtxA} {ds : List (ExprA × Level)} (htel : TelTyA E I n Θ ds)
    {b B : ExprA} {w : Level} (hB : HasTyA E I n (telCtxA ds ++ Θ) B (.sort w))
    (hb : HasTyA E I n (telCtxA ds ++ Θ) b B) {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) {τ : SubstA}
    (hτ : SubstTyA E I n Δ τ Θ) {as : List ExprA} (hl : as.length = ds.length)
    (hargs : ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as) {y : ExprA}
    (h : LRRelA E I n ρ₀ k Δ (substA (consListA as τ) B) (substA (consListA as τ) b) y) :
    LRRelA E I n ρ₀ k Δ (substA (consListA as τ) B)
      (foldAppsA (lamTelA (substTelA τ ds) (substA (upNA ds.length τ) b)) as) y := by
  obtain ⟨c⟩ := lamTel_chain hE hI hR hIS htel hB hb hΔ hτ hl hargs
  exact LRRelA_expand_chain_left hE hI c h

/-- on the right, the chain at its own type moved to the relation's by a type conversion. -/
theorem lrRelA_lamTel_apps_right (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {k : Nat} {Θ : LCtxA} {ds : List (ExprA × Level)} (htel : TelTyA E I n Θ ds)
    {b B : ExprA} {w : Level} (hB : HasTyA E I n (telCtxA ds ++ Θ) B (.sort w))
    (hb : HasTyA E I n (telCtxA ds ++ Θ) b B) {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) {τ : SubstA}
    (hτ : SubstTyA E I n Δ τ Θ) {as : List ExprA} (hl : as.length = ds.length)
    (hargs : ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as) {A x : ExprA}
    (hc : Nonempty (TyConvA E I n Δ (substA (consListA as τ) B) A))
    (h : LRRelA E I n ρ₀ k Δ A x (substA (consListA as τ) b)) :
    LRRelA E I n ρ₀ k Δ A x
      (foldAppsA (lamTelA (substTelA τ ds) (substA (upNA ds.length τ) b)) as) := by
  obtain ⟨c⟩ := lamTel_chain hE hI hR hIS htel hB hb hΔ hτ hl hargs
  obtain ⟨c'⟩ := tmChainA_tyConv hc c
  exact LRRelA_expand_chain_right hE hI c' h


/-- RELATED ARGUMENTS TAKE TWO EQUAL VALID TELESCOPES TO EQUAL INSTANCES (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-3c)): along `T`, then the left arguments at `T` and the right arguments at `T'`: the
    instances are equal. At each Π, the codomains' equality at the left argument twice (`eqKA_pi_inv`),
    then the right telescope's own codomain equality between the two related arguments. -/
theorem lrEqA_applyTelA (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → {T' : ExprA} → {len : Nat} →
    IsPiTelA len T → IsPiTelA len T' → as.length ≤ len → (∃ R, LRTyA E I n ρ₀ k Γ T R) →
    LREqA E I n ρ₀ k Γ T T' → ∀ {C C' : ExprA}, applyTelA as T = some C → applyTelA as' T' = some C' →
    LREqA E I n ρ₀ k Γ C C'
  | _, _, _, .nil _, T', _, _, _, _, _, heq, C, C', hC, hC' => by
      injection hC with hC; injection hC' with hC'
      subst hC; subst hC'
      exact heq
  | _, _, _, .cons A u B v f f' fs fs' h hs, T', len, hpiL, hpiR, hlen, hv, heq, C, C', hC, hC' => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          match T', hpiR with
          | .pi A' u' B' v', ⟨hv', hB'⟩ =>
              obtain ⟨hvL, hBL⟩ := hpiL
              have heq' := heq
              rw [LREqA_eq] at heq'
              obtain ⟨_, _, _, hDeq, RD, hD, hCe⟩ := eqKA_pi_inv hvL heq'
              have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
              have hAA : LREqA E I n ρ₀ k Γ A A' := by rw [LREqA_eq]; exact hDeq [] hρ
              obtain ⟨R, hR, hff⟩ := LRRelA_refl_left hEN h
              have hD0 : LRTyA E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
              rw [LRTyA_unique hR hD0] at hff
              have hBB : LREqA E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f B') := by
                rw [LREqA_eq]; exact hCe [] hρ f f hff
              obtain ⟨R', hR'⟩ := LREqA_valid hEN heq hv
              rw [LRTyA_eq] at hR'
              have hnp' : ¬ IsPropTy E I Γ (.pi A' u' B' v') := fun h' => by
                rw [(isPropTy_pi_iff E I Γ A' u' B' v').1 h'] at hv'
                cases hv'
              obtain ⟨RD', RC', hD', hC'', hCeq', _⟩ := tyKA_pi_inv hR' hnp'
              have hf' : LRRelA E I n ρ₀ k Γ A' f f' := LRRelA_transport' hEN hAA h
              obtain ⟨R'', hR'', hff'⟩ := hf'
              have hD0' : LRTyA E I n ρ₀ k Γ A' (RD' []) := by rw [LRTyA_eq]; exact hD' [] hρ
              rw [LRTyA_unique hR'' hD0'] at hff'
              have hstep : LREqA E I n ρ₀ k Γ (instantiate0A f B') (instantiate0A f' B') := by
                rw [LREqA_eq]; exact hCeq' [] hρ f f' hff'
              obtain ⟨hv₁, hcod⟩ := LRTyA_pi_peel hΓ (by rw [← LRTyA_eq] at hR'; exact hR') hv'
              obtain ⟨R₀, hR₀⟩ := hv
              obtain ⟨_, hcodL⟩ := LRTyA_pi_peel hΓ hR₀ hvL
              obtain ⟨RC₁, hRC₁⟩ := hcodL f f' h
              exact lrEqA_applyTelA hEN hΓ hs (isPiTelA_instantiate len 0 f B hBL)
                (isPiTelA_instantiate len 0 f' B' hB') (Nat.le_of_succ_le_succ hlen) ⟨RC₁, hRC₁⟩
                (LREqA_trans hEN hBB hstep) hC hC'


/-- a typed telescope is typed in a convertible context. -/
theorem telTyA_ctxConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds → {Γ' : LCtxA} →
    CtxConvA E I n Γ Γ' → Nonempty (TelTyA E I n Γ' ds)
  | _, _, .nil _, Γ', _ => ⟨.nil Γ'⟩
  | _, _, .cons Γ D u ds hD tl, Γ', hcc => by
      obtain ⟨hD'⟩ := hasTyA_ctxConv hE hI hR hcc hD
      obtain ⟨tl'⟩ := telTyA_ctxConv hE hI hR tl (.same (.assumption D) hcc)
      exact ⟨.cons Γ' D u ds hD' tl'⟩

/-- a typed telescope's convertible telescope is typed. -/
theorem telTyA_of_telConvA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    {Γ : LCtxA} → {ds ds' : List (ExprA × Level)} → CtxWfA E I n Γ → TelTyA E I n Γ ds →
    TelConvA E I n Γ ds ds' → Nonempty (TelTyA E I n Γ ds')
  | Γ, _, _, _, .nil _, .nil _ => ⟨.nil Γ⟩
  | Γ, _, _, hΓ, .cons _ D u ds hD tl, .cons _ _ D' _ u' _ ds' hu hc tl' => by
      obtain ⟨c⟩ := hc
      have hD'u : HasTyA E I n Γ D' (.sort u) := convA_hasTy_right hE hI hR hIS hΓ c
      have hD'u' := hasTyA_sortEqN hD'u hu
      obtain ⟨tl₂⟩ := telTyA_of_telConvA hE hI hR hIS (.assumption hΓ hD) tl tl'
      obtain ⟨tl₃⟩ := telTyA_ctxConv hE hI (iotaRecHeadTypedA_of hR) tl₂
        (.assumption (ctxConvA_refl Γ) ⟨hD⟩ ⟨hD'u⟩ ⟨c⟩)
      exact ⟨.cons Γ D' u' ds' hD'u' tl₃⟩

/-- convertible telescopes give convertible contexts (the target context well formed). -/
theorem ctxConvA_tel (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    {Γ Γ' : LCtxA} → {ds ds' : List (ExprA × Level)} → CtxConvA E I n Γ Γ' → CtxWfA E I n Γ' →
    TelConvA E I n Γ ds ds' → Nonempty (CtxConvA E I n (telCtxA ds ++ Γ) (telCtxA ds' ++ Γ'))
  | _, _, _, _, hcc, _, .nil _ => ⟨hcc⟩
  | Γ, Γ', _, _, hcc, hΓ', .cons _ D D' u u' ds ds' hu hc tl => by
      obtain ⟨c⟩ := hc
      have hRt := iotaRecHeadTypedA_of hR
      obtain ⟨c'⟩ := convA_ctxConv hE hI hRt hcc c
      have hD₁ := convA_hasTy_left hE hI hR hIS hΓ' c'
      have hD₂ := convA_hasTy_right hE hI hR hIS hΓ' c'
      obtain ⟨ih⟩ := ctxConvA_tel hE hI hR hIS (.assumption hcc ⟨hD₁⟩ ⟨hD₂⟩ ⟨c'⟩)
        (.assumption hΓ' hD₂) tl
      rw [telCtxA_cons_append, telCtxA_cons_append]
      exact ⟨ih⟩

/-- arguments typed along a telescope are typed along a convertible telescope, under one typed
    substitution. -/
theorem convArgsA_telConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    {Θ : LCtxA} → {ds ds' : List (ExprA × Level)} → TelConvA E I n Θ ds ds' → {B B' : ExprA} →
    {w w' : Level} → {Δ : LCtxA} → CtxWfA E I n Δ → {τ : SubstA} → SubstTyA E I n Δ τ Θ →
    {as : List ExprA} → as.length = ds.length →
    ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as →
    Nonempty (ConvArgsA E I n Δ (substA τ (piTelA ds' B' w').1) as as)
  | _, _, _, .nil _, _, _, _, _, _, _, _, _, as, hl, _ => by
      cases as with
      | nil => exact ⟨.nil _⟩
      | cons _ _ => exact absurd hl (Nat.succ_ne_zero _)
  | Θ, _, _, .cons _ D D' u u' ds ds' hu hc tl, B, B', w, w', Δ, hΔ, τ, hτ, as, hl, hargs => by
      cases as with
      | nil => exact absurd hl.symm (Nat.succ_ne_zero _)
      | cons a as₂ =>
          obtain ⟨c⟩ := hc
          simp only [piTelA, substA_pi] at hargs ⊢
          cases hargs with
          | cons _ _ _ _ _ _ _ _ hca hs =>
              obtain ⟨ca⟩ := hca
              have hRt := iotaRecHeadTypedA_of hR
              have ha := convA_hasTy_left hE hI hR hIS hΔ ca
              have hcs := convA_substA hE hI hRt hIS hτ c
              have tc := tyConvA_of_sortConv hE hI hR hIS hΔ hcs
              have ca' := convA_of_tyConvA ca tc
              have hτ₁ : SubstTyA E I n Δ (SubstA.cons a τ) (.assumption D :: Θ) := substTyA_cons hτ ha
              have hs' : ConvArgsA E I n Δ (substA (SubstA.cons a τ) (piTelA ds B w).1) as₂ as₂ := by
                rw [← instantiate0A_substA_up]; exact hs
              obtain ⟨ih⟩ := convArgsA_telConv hE hI hR hIS tl hΔ hτ₁ (Nat.succ.inj hl) hs'
              rw [← instantiate0A_substA_up] at ih
              exact ⟨.cons _ _ _ _ _ _ _ _ ⟨ca'⟩ ih⟩

theorem consListA_length_add : (ys : List ExprA) → (τ : SubstA) → (j : Nat) →
    consListA ys τ (ys.length + j) = τ j
  | [], _, _ => by simp only [consListA, List.length_nil, Nat.zero_add]
  | y :: ys, τ, j => by
      show consListA ys (SubstA.cons y τ) (ys.length + 1 + j) = τ j
      have h := consListA_length_add ys (SubstA.cons y τ) (j + 1)
      rw [Nat.add_assoc, Nat.add_comm 1 j]
      exact h

/-- the bound variables of a binder list, under the arguments, are the arguments. -/
theorem map_substA_consListA_paramLocalsA : (as : List ExprA) → (τ : SubstA) →
    (paramLocalsA as.length).map (substA (consListA as τ)) = as
  | [], _ => rfl
  | a :: as, τ => by
      show substA (consListA as (SubstA.cons a τ)) (.bvar as.length) ::
        (paramLocalsA as.length).map (substA (consListA as (SubstA.cons a τ))) = a :: as
      rw [map_substA_consListA_paramLocalsA as (SubstA.cons a τ)]
      have := consListA_length_add as (SubstA.cons a τ) 0
      rw [Nat.add_zero] at this
      exact congrArg (· :: as) this

/-- closed pieces of a list under the arguments are the substitution's. -/
theorem map_substA_consListA_liftNA (as : List ExprA) (τ : SubstA) (xs : List ExprA) :
    (xs.map (liftNA as.length)).map (substA (consListA as τ)) = xs.map (substA τ) := by
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => substA_consListA_liftNA as τ e)

/-- a weakened Π-telescope applied to arguments reaches the body under the arguments and the weakening
    substitution. -/
theorem applyTelA_wk_piTelA (B : ExprA) (w : Level) (ds : List (ExprA × Level)) (ρ : WkSpecA)
    (as : List ExprA) (hl : as.length = ds.length) :
    applyTelA as (wkExprA ρ (piTelA ds B w).1) = some (substA (consListA as (wkSubstA ρ)) B) := by
  rw [wkExprA_eq_substA]
  exact applyTelA_piTelA B w ds as hl (wkSubstA ρ)

theorem isPiTelA_wk_piTelA (B : ExprA) (w : Level) (hw : isZero w = false) (ds : List (ExprA × Level))
    (ρ : WkSpecA) : IsPiTelA ds.length (wkExprA ρ (piTelA ds B w).1) := by
  rw [wkExprA_eq_substA, substA_piTelA]
  have h := isPiTelA_piTelA (substA (upNA ds.length (wkSubstA ρ)) B) w hw (substTelA (wkSubstA ρ) ds)
  rwa [substTelA_length] at h


/-- the direct call's body under the arguments. -/
theorem substA_recBody (r : Nat) (ls : List Level) (pfx idx : List ExprA) (v : ExprA) (as : List ExprA)
    (τ : SubstA) :
    substA (consListA as τ) (foldAppsA (.const r ls) (pfx.map (liftNA as.length) ++ idx ++
      [foldAppsA (liftNA as.length v) (paramLocalsA as.length)])) =
    foldAppsA (.const r ls) (pfx.map (substA τ) ++ idx.map (substA (consListA as τ)) ++
      [foldAppsA (substA τ v) as]) := by
  rw [substA_foldAppsA, substA_const, List.map_append, List.map_append, List.map_cons, List.map_nil,
    substA_foldAppsA, substA_consListA_liftNA, map_substA_consListA_paramLocalsA,
    map_substA_consListA_liftNA]

/-- the motive instance under the arguments. -/
theorem substA_motBody (mot : ExprA) (idx : List ExprA) (v : ExprA) (as : List ExprA) (τ : SubstA) :
    substA (consListA as τ) (foldAppsA (liftNA as.length mot)
      (idx ++ [foldAppsA (liftNA as.length v) (paramLocalsA as.length)])) =
    foldAppsA (substA τ mot) (idx.map (substA (consListA as τ)) ++ [foldAppsA (substA τ v) as]) := by
  rw [substA_foldAppsA, List.map_append, List.map_cons, List.map_nil, substA_foldAppsA,
    substA_consListA_liftNA, substA_consListA_liftNA, map_substA_consListA_paramLocalsA]

/-- the family application's parameters and indices under the arguments. -/
theorem substA_famBody (f : Nat) (ls : List Level) (qs idx : List ExprA) (as : List ExprA) (τ : SubstA) :
    substA (consListA as τ) (foldAppsA (.const f ls) (qs.map (liftNA as.length) ++ idx)) =
    foldAppsA (.const f ls) (qs.map (substA τ) ++ idx.map (substA (consListA as τ))) := by
  rw [substA_foldAppsA, substA_const, List.map_append, map_substA_consListA_liftNA]


/-- RIGHT ARGUMENTS OF RELATED ARGUMENTS ARE TYPED ALONG THE TELESCOPE with themselves substituted: the
    left tail's relation moves along the codomains' equality at the related pair. -/
theorem convArgsA_right_of_argsRelKA (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → {len : Nat} →
    IsPiTelA len T → as.length ≤ len → (∃ R, LRTyA E I n ρ₀ k Γ T R) →
    Nonempty (ConvArgsA E I n Γ T as' as')
  | _, _, _, .nil _, _, _, _, _ => ⟨.nil _⟩
  | _, _, _, .cons A u B v f f' fs fs' h hs, len, hpi, hlen, hv => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hvz, hBp⟩ := hpi
          obtain ⟨R₀, hR₀⟩ := hv
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have hR₀' := hR₀
          rw [LRTyA_eq] at hR₀'
          have hnp : ¬ IsPropTy E I Γ (.pi A u B v) := fun h' => by
            rw [(isPropTy_pi_iff E I Γ A u B v).1 h'] at hvz
            cases hvz
          obtain ⟨RD, RC, hD, hC, hCeq, _⟩ := tyKA_pi_inv hR₀' hnp
          obtain ⟨R, hR, hff⟩ := h
          have hD0 : LRTyA E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
          rw [LRTyA_unique hR hD0] at hff
          have hstep : LREqA E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f' B) := by
            rw [LREqA_eq]; exact hCeq [] hρ f f' hff
          have hKt := argsRelKA_of_lrEqA hEN hΓ hs (isPiTelA_instantiate len 0 f B hBp)
            (isPiTelA_instantiate len 0 f' B hBp) (Nat.le_of_succ_le_succ hlen) hstep
          obtain ⟨_, hcod⟩ := LRTyA_pi_peel hΓ hR₀ hvz
          have hrr : LRRelA E I n ρ₀ k Γ A f' f' :=
            LRRelA_refl_left hEN
              (LRRelA_symm hEN ⟨R, hR, (by rw [LRTyA_unique hR hD0]; exact hff)⟩)
          obtain ⟨RC', hRC'⟩ := hcod f' f' hrr
          obtain ⟨ih⟩ := convArgsA_right_of_argsRelKA hEN hΓ hKt (isPiTelA_instantiate len 0 f' B hBp)
            (by rw [argsRelKA_length hKt]; exact Nat.le_of_succ_le_succ (by
              rw [← argsRelKA_length hs]; exact hlen)) ⟨RC', hRC'⟩
          obtain ⟨c⟩ := LRRelA_conv hrr
          exact ⟨.cons _ _ _ _ _ _ _ _ ⟨c⟩ ih⟩


/-- the same telescope: related non-empty argument lists take it to equal instances (the first step's
    codomain equality at the related pair is the telescope's own). -/
theorem lrEqA_applyTelA_self (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → {len : Nat} →
    IsPiTelA len T → 0 < as.length → as.length ≤ len → (∃ R, LRTyA E I n ρ₀ k Γ T R) →
    ∀ {C C' : ExprA}, applyTelA as T = some C → applyTelA as' T = some C' →
    LREqA E I n ρ₀ k Γ C C'
  | _, _, _, .nil _, _, _, h0, _, _, _, _, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | _, _, _, .cons A u B v f f' fs fs' h hs, len, hpi, _, hlen, hv, C, C', hC, hC' => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hvz, hBp⟩ := hpi
          obtain ⟨R₀, hR₀⟩ := hv
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have hR₀' := hR₀
          rw [LRTyA_eq] at hR₀'
          have hnp : ¬ IsPropTy E I Γ (.pi A u B v) := fun h' => by
            rw [(isPropTy_pi_iff E I Γ A u B v).1 h'] at hvz
            cases hvz
          obtain ⟨RD, RC, hD, hC₀, hCeq, _⟩ := tyKA_pi_inv hR₀' hnp
          obtain ⟨R, hR, hff⟩ := h
          have hD0 : LRTyA E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
          rw [LRTyA_unique hR hD0] at hff
          have hstep : LREqA E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f' B) := by
            rw [LREqA_eq]; exact hCeq [] hρ f f' hff
          obtain ⟨_, hcod⟩ := LRTyA_pi_peel hΓ hR₀ hvz
          obtain ⟨RC₁, hRC₁⟩ := hcod f f' ⟨R, hR, (by rw [LRTyA_unique hR hD0]; exact hff)⟩
          exact lrEqA_applyTelA hEN hΓ hs (isPiTelA_instantiate len 0 f B hBp)
            (isPiTelA_instantiate len 0 f' B hBp) (Nat.le_of_succ_le_succ hlen) ⟨RC₁, hRC₁⟩ hstep hC hC'

/-- a pointwise conversion's left list, converted with itself. -/
theorem convArgsA_refl_left {Γ : LCtxA} : ∀ {T : ExprA} {xs ys : List ExprA},
    ConvArgsA E I n Γ T xs ys → ConvArgsA E I n Γ T xs xs
  | _, _, _, .nil T => .nil T
  | _, _, _, .cons A u B v f _ fs _ hc hs =>
      .cons A u B v f f fs fs (hc.elim fun c => ⟨.trans _ _ _ _ _ c (.symm _ _ _ _ c)⟩)
        (convArgsA_refl_left hs)

/-- related arguments along a telescope are pointwise convertible along it (escape at each step). -/
theorem convArgsA_of_argsRelKA {k : Nat} {Γ : LCtxA} : ∀ {T : ExprA} {xs ys : List ExprA},
    ArgsRelKA E I n ρ₀ k Γ T xs ys → ConvArgsA E I n Γ T xs ys
  | _, _, _, .nil T => .nil T
  | _, _, _, .cons A u B v f f' fs fs' h hs =>
      .cons A u B v f f' fs fs' (LRRelA_conv h) (convArgsA_of_argsRelKA hs)


/-- the bound variables put for the binders, under the world of those binders' weakening, are the identity. -/
theorem substA_consListA_telWorldA (ds : List (ExprA × Level)) (e : ExprA) :
    substA (consListA (paramLocalsA ds.length) (wkSubstA (telWorldA ds))) e = e := by
  rw [substA_ext (σ := consListA (paramLocalsA ds.length) (wkSubstA (telWorldA ds))) (τ := SubstA.id)
    (fun i => ?_) e, substA_id]
  by_cases hlt : i < ds.length
  · rw [consListA_paramLocalsA_lt _ _ i (by simpa [paramLocalsA_length] using hlt)]; rfl
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + ds.length := ⟨i - ds.length, by omega⟩
    have h := consListA_length_add (paramLocalsA ds.length) (wkSubstA (telWorldA ds)) q
    rw [paramLocalsA_length, Nat.add_comm] at h
    rw [h]
    show wkExprA (telWorldA ds) (.bvar q) = .bvar (q + ds.length)
    rw [wkExprA_telWorldA, liftNA_bvar]

end Beta

#print axioms substA_lamTelA
#print axioms instantiate0A_lamTelA_subst
#print axioms tyHRedA_spine
#print axioms lamTel_chain
#print axioms LRRelA_expand_chain_left
#print axioms LRRelA_expand_chain_right
#print axioms tmChainA_tyConv
#print axioms wkExprA_eq_substA
#print axioms substTyA_wkSubstA
#print axioms substA_consListA_liftNA
#print axioms lrRelA_lamTel_apps_left
#print axioms lrRelA_lamTel_apps_right
#print axioms lrEqA_applyTelA
#print axioms convArgsA_refl_left
#print axioms convArgsA_of_argsRelKA
#print axioms lrEqA_applyTelA_self

#print axioms telTyA_ctxConv
#print axioms telTyA_of_telConvA
#print axioms ctxConvA_tel
#print axioms convArgsA_telConv
#print axioms consListA_length_add
#print axioms map_substA_consListA_paramLocalsA
#print axioms map_substA_consListA_liftNA
#print axioms applyTelA_wk_piTelA
#print axioms isPiTelA_wk_piTelA
#print axioms substA_consListA_telWorldA
#print axioms convArgsA_right_of_argsRelKA
#print axioms substA_recBody
#print axioms substA_motBody
#print axioms substA_famBody

end Rcic.Declarative.Ann
