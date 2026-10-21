import rcic.RcicAnnFrecArm

/-!
# R-NoFunRec-1 step 1 (1c-ε2d-L3b-1): the extension world of a function-recursive field's inner binders

A telescope of inner binders is a Kripke world (`telWorldA`): its context is the telescope's, its
weakening the lift by the binders' count. At that world the bound variables are related to themselves
along the weakened Π-telescope (`argsRelKA_bvarsA`), and a function-recursive field's domain and
induction-hypothesis binder are built telescopes over the same binders (`frecDomA_eq_piTelA`,
`frecIHA_eq_piTelA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section World
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the world inserting a telescope's binders, outermost first, each at the top. -/
def telWorldA (ds : List (ExprA × Level)) : WkSpecA :=
  ds.map fun d => (LocalDeclA.assumption d.1, 0)

theorem wkCtxA_telWorldA : (ds : List (ExprA × Level)) → (Γ : LCtxA) →
    wkCtxA (telWorldA ds) Γ = telCtxA ds ++ Γ
  | [], _ => rfl
  | (D, u) :: ds, Γ => by
      show wkCtxA (telWorldA ds) (.assumption D :: Γ) = _
      rw [wkCtxA_telWorldA ds, telCtxA_cons_append]

theorem wkExprA_telWorldA : (ds : List (ExprA × Level)) → (e : ExprA) →
    wkExprA (telWorldA ds) e = liftNA ds.length e
  | [], _ => rfl
  | (D, u) :: ds, e => by
      show wkExprA (telWorldA ds) (liftA 0 1 e) = _
      rw [wkExprA_telWorldA ds, liftNA_eq, liftNA_eq, List.length_cons,
        liftA_liftA_merge ds.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]

theorem wkSpecA_ok_telWorldA : (ds : List (ExprA × Level)) → (Γ : LCtxA) → WkSpecA.ok (telWorldA ds) Γ
  | [], _ => trivial
  | (D, _) :: ds, Γ => ⟨Nat.zero_le _, wkSpecA_ok_telWorldA ds (.assumption D :: Γ)⟩

theorem wkOkA_telWorldA {Γ : LCtxA} {ds : List (ExprA × Level)} (hds : TelTyA E I n Γ ds)
    (hΓ : Nonempty (CtxWfA E I n Γ)) : WkOkA E I n (telWorldA ds) Γ :=
  ⟨wkSpecA_ok_telWorldA ds Γ, by
    rw [wkCtxA_telWorldA]; exact hΓ.elim fun c => ⟨ctxWfA_telCtx hds c⟩⟩

theorem liftNA_liftA_comm (m : Nat) (e : ExprA) : liftNA m (liftA 0 1 e) = liftNA (m + 1) e := by
  rw [liftNA_eq, liftNA_eq, liftA_liftA_merge m 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]

theorem paramLocalsA_eq_range (m : Nat) : paramLocalsA m = (List.range m).reverse.map ExprA.bvar := by
  induction m with
  | zero => rfl
  | succ m ih => simp [paramLocalsA, List.range_succ, ih]

theorem map_liftNA_liftA (m : Nat) : (pl : List ExprA) →
    (pl.map (liftA 0 1)).map (liftNA m) = pl.map (liftNA (m + 1))
  | [] => rfl
  | p :: pl => by simp only [List.map, liftNA_liftA_comm, map_liftNA_liftA m pl]

/-- a function-recursive field's domain is the telescope over its substituted inner binders, ending in the
    family at the parameter locals past them and the indices under the lifted substitution. -/
theorem frecDomA_eq_piTelA (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    frecDomA f ls w pl σ ds idx =
      piTelA (substTelA σ ds) (foldAppsA (.const f ls)
        (pl.map (liftNA ds.length) ++ idx.map (substA (upNA ds.length σ)))) w
  | [], pl, σ => by
      simp only [frecDomA, substTelA, piTelA, List.length_nil]
      rw [show pl.map (liftNA 0) = pl from List.map_id'' (fun _ => rfl) pl]
      rfl
  | (D, u) :: ds, pl, σ => by
      simp only [frecDomA, substTelA, piTelA, List.length_cons]
      rw [frecDomA_eq_piTelA f ls w idx ds (pl.map (liftA 0 1)) σ.up, map_liftNA_liftA]
      rfl

/-- the induction hypothesis's binder, likewise: the motive (lifted past the inner binders) at the indices
    and at the field `x` (at `j`) applied to the `M` inner variables. -/
theorem frecIHA_eq_piTelA (wM : Level) (idx : List ExprA) (M : Nat) :
    (ds : List (ExprA × Level)) → (mot : ExprA) → (j : Nat) → (σ : SubstA) →
    frecIHA wM mot j σ ds idx M =
      piTelA (substTelA σ ds) (foldAppsA (liftNA ds.length mot)
        (idx.map (substA (upNA ds.length σ)) ++ [foldAppsA (.bvar (j + ds.length)) (paramLocalsA M)])) wM
  | [], mot, j, σ => by
      simp only [frecIHA, substTelA, piTelA, List.length_nil, Nat.add_zero, paramLocalsA_eq_range]
      rfl
  | (D, u) :: ds, mot, j, σ => by
      simp only [frecIHA, substTelA, piTelA, List.length_cons]
      rw [frecIHA_eq_piTelA wM idx M ds (liftA 0 1 mot) (j + 1) σ.up, liftNA_liftA_comm,
        show j + 1 + ds.length = j + (ds.length + 1) by omega]
      rfl

theorem instantiate0A_bvar_liftA_gap (m : Nat) (B : ExprA) :
    instantiate0A (.bvar m) (liftA 1 (m + 1) B) = liftA 0 m B := by
  rw [instantiate0A_eq_substA_cons, substA_liftA_gen 1 (m + 1)]
  have h := substA_liftA_gen 0 m SubstA.id B
  rw [substA_id] at h
  rw [h]
  exact substA_ext (fun i => by cases i <;> simp [SubstA.cons, SubstA.id]) B

theorem lookupValueA_telCtxA_head (D : ExprA) (u : Level) (ds : List (ExprA × Level)) (Θ : LCtxA) :
    lookupValueA (telCtxA ((D, u) :: ds) ++ Θ) ds.length = none := by
  rw [telCtxA_cons_append]
  unfold lookupValueA
  rw [List.get?_eq_getElem?, List.getElem?_append_right (by simp [telCtxA])]
  simp [telCtxA]

/-- THE BOUND VARIABLES ARE RELATED TO THEMSELVES ALONG THE WEAKENED TELESCOPE (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-1)): at the world of a Π-telescope's own binders, the variables are a related argument
    list along the telescope lifted past them (`LRRelA_bvar` at each binder). -/
theorem argsRelKA_bvarsA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I) {k : Nat}
    (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → {Θ₁ : LCtxA} → TelTyA E I n Θ₁ ds →
    Nonempty (CtxWfA E I n (telCtxA ds ++ Θ₁)) → IsPiTelA ds.length (piTelA ds B w).1 →
    {R : ExprA → ExprA → Prop} →
    LRTyA E I n ρ₀ k (telCtxA ds ++ Θ₁) (liftNA ds.length (piTelA ds B w).1) R →
    ArgsRelKA E I n ρ₀ k (telCtxA ds ++ Θ₁) (liftNA ds.length (piTelA ds B w).1)
      (paramLocalsA ds.length) (paramLocalsA ds.length)
  | [], _, _, _, _, _, _ => .nil _
  | (D, u) :: ds, Θ₁, .cons _ _ _ _ hD tl, hΓ, hpi, R, hR => by
      have hlen : (telCtxA ((D, u) :: ds)).length = ds.length + 1 := by
        rw [telCtxA_length, List.length_cons]
      have hAty := hasTyA_liftN hE hI hD (telCtxA ((D, u) :: ds))
      rw [hlen, liftNA_sort, liftNA_eq] at hAty
      have hlk := lookupTypeA_telCtxA_head D u ds Θ₁
      have hpiE : liftNA (ds.length + 1) (piTelA ((D, u) :: ds) B w).1 =
          .pi (liftA 0 (ds.length + 1) D) u (liftA 1 (ds.length + 1) (piTelA ds B w).1)
            (piTelA ds B w).2 := by
        rw [liftNA_eq]; rfl
      simp only [List.length_cons] at hR ⊢
      rw [hpiE] at hR ⊢
      obtain ⟨hv, hpi'⟩ := hpi
      obtain ⟨⟨RD, hRD⟩, hcod⟩ := LRTyA_pi_peel hΓ hR hv
      have hrel : LRRelA E I n ρ₀ k (telCtxA ((D, u) :: ds) ++ Θ₁) (liftA 0 (ds.length + 1) D)
          (.bvar ds.length) (.bvar ds.length) :=
        LRRelA_bvar hE hI hIC (lookupValueA_telCtxA_head D u ds Θ₁) ⟨RD, hRD⟩
          ⟨.bvar _ ds.length _ u hlk hAty⟩
      obtain ⟨RC, hRC⟩ := hcod _ _ hrel
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq] at hRC
      refine .cons _ _ _ _ _ _ _ _ hrel ?_
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq]
      have e := telCtxA_cons_append (D, u) ds Θ₁
      have := argsRelKA_bvarsA hE hI hIC B w ds (Θ₁ := .assumption D :: Θ₁) tl
        (by rw [← e]; exact hΓ) hpi' (R := RC) (by rw [← e]; exact hRC)
      rw [← e] at this
      exact this


theorem isPiTelA_liftN_aux (len : Nat) (m : Nat) {T : ExprA} (h : IsPiTelA len T) :
    IsPiTelA len (liftNA m T) := by
  rw [liftNA_eq]; exact isPiTelA_liftA len 0 m T h

/-- a typed built telescope has typed binders, and (with at least one) a body typed at its sort. -/
theorem telTyA_of_hasTy_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → {Γ : LCtxA} → {s : Level} →
    HasTyA E I n Γ (piTelA ds B w).1 (.sort s) →
    Nonempty (TelTyA E I n Γ ds) ∧
      (0 < ds.length → Nonempty (HasTyA E I n (telCtxA ds ++ Γ) B (.sort w)))
  | [], _, _, _ => ⟨⟨.nil _⟩, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | (D, u) :: ds, Γ, s, h => by
      obtain ⟨⟨hD⟩, ⟨hC⟩⟩ := hasTyA_pi_inv h
      obtain ⟨⟨tl⟩, hb⟩ := telTyA_of_hasTy_piTelA B w ds hC
      refine ⟨⟨.cons Γ D u ds hD tl⟩, fun _ => ?_⟩
      rw [telCtxA_cons_append]
      cases ds with
      | nil => exact ⟨hC⟩
      | cons d ds' => exact hb (Nat.succ_pos _)

/-- THE VARIABLES, RELATED ALONG AN EQUAL TELESCOPE: if the Π-telescope `T` over the binders `ds` is
    valid and equal to `T'`, the bound variables are related to themselves along `T'` lifted past the
    binders (at the world `telWorldA ds`). -/
theorem argsRelKA_bvarsA_of_lrEqA (hE : EnvClosedA E) (hEN : EnvNormClosedA E)
    (hNCT : EnvNormCtorTypeA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) (B : ExprA) (w : Level)
    (hw : isZero w = false) {ds : List (ExprA × Level)} {s : Level}
    (hT : HasTyA E I n Γ (piTelA ds B w).1 (.sort s))
    (hv : ∃ R, LRTyA E I n ρ₀ k Γ (piTelA ds B w).1 R) {T' : ExprA}
    (hT' : IsPiTelA ds.length T') (heq : LREqA E I n ρ₀ k Γ (piTelA ds B w).1 T') :
    ArgsRelKA E I n ρ₀ k (telCtxA ds ++ Γ) (liftNA ds.length T') (paramLocalsA ds.length)
      (paramLocalsA ds.length) := by
  obtain ⟨⟨tl⟩, -⟩ := telTyA_of_hasTy_piTelA B w ds hT
  have hok : WkOkA E I n (telWorldA ds) Γ := wkOkA_telWorldA tl hΓ
  obtain ⟨R, hR⟩ := hv
  obtain ⟨R', hR', -⟩ := LRTyA_wk hE hEN hI hR (telWorldA ds) hok
  rw [wkCtxA_telWorldA, wkExprA_telWorldA] at hR'
  have hctx : Nonempty (CtxWfA E I n (telCtxA ds ++ Γ)) := by
    have := hok.2; rwa [wkCtxA_telWorldA] at this
  have hV := argsRelKA_bvarsA hE hI hIC (ρ₀ := ρ₀) (k := k) B w ds tl hctx
    (isPiTelA_piTelA B w hw ds) hR'
  have hq := LREqA_wk hE hEN hI heq (telWorldA ds) hok
  rw [wkCtxA_telWorldA, wkExprA_telWorldA, wkExprA_telWorldA] at hq
  exact argsRelKA_of_lrEqA hNCT hctx hV (isPiTelA_liftN_aux ds.length _ (isPiTelA_piTelA B w hw ds))
    (isPiTelA_liftN_aux ds.length _ hT') (Nat.le_of_eq (paramLocalsA_length ds.length)) hq

theorem substA_liftNA (m : Nat) (τ : SubstA) (e : ExprA) :
    substA (upNA m τ) (liftNA m e) = liftNA m (substA τ e) := by
  rw [liftNA_eq, liftNA_eq]; exact substA_upNA_liftA m τ e

theorem piTelA_snd_substTelA (B B' : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → (σ : SubstA) →
    (piTelA (substTelA σ ds) B' w).2 = (piTelA ds B w).2
  | [], _ => rfl
  | (D, u) :: ds, σ => by
      simp only [piTelA, substTelA]
      rw [piTelA_snd_substTelA B B' w ds σ.up]

theorem substA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → (τ : SubstA) →
    substA τ (piTelA ds B w).1 = (piTelA (substTelA τ ds) (substA (upNA ds.length τ) B) w).1
  | [], _ => rfl
  | (D, u) :: ds, τ => by
      simp only [piTelA, substA_pi, substTelA, List.length_cons]
      rw [substA_piTelA B w ds τ.up, piTelA_snd_substTelA B _ w ds τ.up]
      rfl

theorem substTelA_substTelA :
    (ds : List (ExprA × Level)) → (σs σ τ : SubstA) → (∀ i, substA τ (σs i) = σ i) →
    substTelA τ (substTelA σs ds) = substTelA σ ds
  | [], _, _, _, _ => rfl
  | (D, u) :: ds, σs, σ, τ, h => by
      simp only [substTelA]
      rw [substA_substA, substA_ext h D]
      have : substTelA τ.up (substTelA σs.up ds) = substTelA σ.up ds :=
        substTelA_substTelA ds σs.up σ.up τ.up (fun i => by
          cases i with
          | zero => rfl
          | succ i =>
              show substA τ.up (liftA 0 1 (σs i)) = liftA 0 1 (σ i)
              rw [substA_up_liftA, h i])
      rw [this]

theorem paramLocalsA_lt (m : Nat) : ∀ x ∈ paramLocalsA m, ∃ i, i < m ∧ x = ExprA.bvar i := by
  induction m with
  | zero => intro x hx; cases hx
  | succ m ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := ih x hx
        exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/-- THE INDUCTION HYPOTHESIS'S BINDER AT THE FIELD (R-NoFunRec-1 step 1 (1c-ε2d-L3b-1)): the field `v`
    put for the field's variable in `frecIHA` (under the plain substitution shifted past it, the motive
    lifted past it) is the telescope over the substituted inner binders ending in the motive at the
    indices and at `v` applied to the inner variables. -/
theorem frecIHA_closed (wM : Level) (idx : List ExprA) (mot v : ExprA) (σ : SubstA)
    (ds : List (ExprA × Level)) :
    substA (SubstA.cons v SubstA.id) (frecIHA wM (liftA 0 1 mot) 0 σ.shift1 ds idx ds.length).1 =
      (piTelA (substTelA σ ds) (foldAppsA (liftNA ds.length mot)
        (idx.map (substA (upNA ds.length σ)) ++ [foldAppsA (liftNA ds.length v) (paramLocalsA ds.length)]))
        wM).1 := by
  rw [frecIHA_eq_piTelA, substA_piTelA, substTelA_length]
  have hτ : ∀ i, substA (SubstA.cons v SubstA.id) (σ.shift1 i) = σ i := fun i => by
    show substA (SubstA.cons v SubstA.id) (liftA 0 1 (σ i)) = σ i
    rw [substA_cons_liftA, substA_id]
  rw [substTelA_substTelA ds σ.shift1 σ _ hτ]
  congr 2
  have hm : substA (upNA ds.length (SubstA.cons v SubstA.id)) (liftNA ds.length (liftA 0 1 mot)) =
      liftNA ds.length mot := by
    rw [substA_liftNA, substA_cons_liftA, substA_id]
  have hi : ∀ e, substA (upNA ds.length (SubstA.cons v SubstA.id)) (substA (upNA ds.length σ.shift1) e) =
      substA (upNA ds.length σ) e := fun e => by
    rw [substA_substA]
    refine substA_ext (fun i => ?_) e
    by_cases hlt : i < ds.length
    · rw [upNA_lt _ _ i hlt, substA_bvar, upNA_lt _ _ i hlt, upNA_lt _ _ i hlt]
    · obtain ⟨p, rfl⟩ : ∃ p, i = p + ds.length := ⟨i - ds.length, by omega⟩
      rw [upNA_add, upNA_add, substA_liftNA]
      congr 1
      exact hτ p
  have hx : substA (upNA ds.length (SubstA.cons v SubstA.id)) (.bvar (0 + ds.length)) =
      liftNA ds.length v := by
    rw [substA_bvar, upNA_add]; rfl
  have hv : (paramLocalsA ds.length).map (substA (upNA ds.length (SubstA.cons v SubstA.id))) =
      paramLocalsA ds.length := by
    refine (List.map_congr_left (g := id) (fun x hx => ?_)).trans (List.map_id _)
    obtain ⟨i, hi', rfl⟩ := paramLocalsA_lt _ x hx
    rw [substA_bvar, upNA_lt _ _ i hi']
    rfl
  rw [substA_foldAppsA, List.map_append, List.map_singleton, substA_foldAppsA, hm, hx, hv]
  congr 2
  rw [List.map_map]
  exact List.map_congr_left (fun e _ => hi e)

/-- the induction hypothesis's binder has no propositional layer. -/
theorem isPiTelA_frecIHA (wM : Level) (hw : isZero wM = false) (idx : List ExprA) (M : Nat)
    (ds : List (ExprA × Level)) (mot : ExprA) (j : Nat) (σ : SubstA) :
    IsPiTelA ds.length (frecIHA wM mot j σ ds idx M).1 := by
  rw [frecIHA_eq_piTelA]
  have h := isPiTelA_piTelA (foldAppsA (liftNA ds.length mot)
    (idx.map (substA (upNA ds.length σ)) ++ [foldAppsA (.bvar (j + ds.length)) (paramLocalsA M)])) wM hw
    (substTelA σ ds)
  rwa [substTelA_length] at h

/-- the same for the field's domain. -/
theorem isPiTelA_frecDomA (f : Nat) (ls : List Level) (w : Level) (hw : isZero w = false)
    (idx : List ExprA) (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) :
    IsPiTelA ds.length (frecDomA f ls w pl σ ds idx).1 := by
  rw [frecDomA_eq_piTelA]
  have h := isPiTelA_piTelA (foldAppsA (.const f ls)
    (pl.map (liftNA ds.length) ++ idx.map (substA (upNA ds.length σ)))) w hw (substTelA σ ds)
  rwa [substTelA_length] at h

/-- arguments related along a function-recursive field's domain are related along the induction
    hypothesis's binder at the field (they read the same inner binders). -/
theorem argsRelKA_frecDomA_closed {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (w : Level)
    (idx : List ExprA) (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) (B' : ExprA)
    (w' : Level) {as as' : List ExprA}
    (h : ArgsRelKA E I n ρ₀ k Γ (frecDomA f ls w pl σ ds idx).1 as as') (hl : as.length = ds.length) :
    ArgsRelKA E I n ρ₀ k Γ (piTelA (substTelA σ ds) B' w').1 as as' := by
  rw [frecDomA_eq_piTelA] at h
  have := argsRelKA_piTelA_body (E := E) (I := I) (n := n) (ρ₀ := ρ₀) _ B' w w' (substTelA σ ds)
    SubstA.id (by rwa [substA_id]) (by rw [substTelA_length]; exact hl)
  rwa [substA_id] at this

theorem eqNA_imax_left {u u' : Level} (v : Level) (h : eqN u u') : eqN (.imax u v) (.imax u' v) := by
  intro ρ
  simp only [eval, h ρ]

/-- a conversion at a sort, moved to an `=ₙ` sort. -/
def convA_sort_retypeA {Γ : LCtxA} {a b : ExprA} {u l : Level} (h : ConvA E I n Γ a b (.sort u))
    (hul : eqN u l) : ConvA E I n Γ a b (.sort l) :=
  .tyConv Γ a b (.sort u) (.sort l) (.succ u) (.succ l) (.succ u) h (.sort Γ u) (eqNA_refl _)
    (.sort Γ l) (eqNA_succ (eqNA_symm hul)) (.sorts Γ u l hul)

/-- THE λ-TELESCOPE CONVERTS ACROSS ANNOTATIONS (R-NoFunRec-1 step 1 (1c-ε2d-L3b-2)): two bodies
    convertible at a codomain under the left binders, the right binders' domains pairwise convertible
    with the left's, give λ-telescopes convertible at the left Π-telescope. At each binder the right λ is
    typed at the left Π: its body typed under the right domain by context conversion (`hasTyA_ctxConv`),
    the Π retyped by the domains' conversion (`ConvA.pi`). -/
theorem convA_lamTelA₂ (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    {Γ : LCtxA} → {ds ds' : List (ExprA × Level)} → CtxWfA E I n Γ → TelTyA E I n Γ ds →
    TelConvA E I n Γ ds ds' → {b b' B : ExprA} → {w : Level} →
    HasTyA E I n (telCtxA ds ++ Γ) B (.sort w) → ConvA E I n (telCtxA ds ++ Γ) b b' B →
    Nonempty (ConvA E I n Γ (lamTelA ds b) (lamTelA ds' b') (piTelA ds B w).1)
  | _, _, _, _, .nil _, .nil _, _, _, _, _, _, hb => ⟨hb⟩
  | Γ, _, _, hΓ, .cons _ D u ds hD tl, .cons _ _ D' _ u' _ ds' hu hcD tl', b, b', B, w, hB, hb => by
      obtain ⟨hcD⟩ := hcD
      have hΓ₁ : CtxWfA E I n (.assumption D :: Γ) := .assumption hΓ hD
      have e := telCtxA_cons_append (D, u) ds Γ
      rw [e] at hB hb
      obtain ⟨ih⟩ := convA_lamTelA₂ hE hI hR hIS hΓ₁ tl tl' hB hb
      have hB₁ : HasTyA E I n (.assumption D :: Γ) (piTelA ds B w).1 (.sort (piTelA ds B w).2) :=
        hasTyA_piTelA tl hB
      have hb₁' := convA_hasTy_right hE hI hR hIS hΓ₁ ih
      have hD' : HasTyA E I n Γ D' (.sort u) := convA_hasTy_right hE hI hR hIS hΓ hcD
      have hD'' : HasTyA E I n Γ D' (.sort u') := hasTyA_sortEqN hD' hu
      have hcc : CtxConvA E I n (.assumption D :: Γ) (.assumption D' :: Γ) :=
        .assumption (ctxConvA_refl Γ) ⟨hD⟩ ⟨hD'⟩ ⟨hcD⟩
      have hRt := iotaRecHeadTypedA_of hR
      obtain ⟨hbody⟩ := hasTyA_ctxConv hE hI hRt hcc hb₁'
      obtain ⟨hB₂⟩ := hasTyA_ctxConv hE hI hRt hcc hB₁
      have hlam : HasTyA E I n Γ (.lam D' u' (lamTelA ds' b'))
          (.pi D' u' (piTelA ds B w).1 (piTelA ds B w).2) :=
        .lam Γ D' u' _ _ _ hD'' hB₂ hbody
      have hpiL : HasTyA E I n Γ (.pi D' u' (piTelA ds B w).1 (piTelA ds B w).2)
          (.sort (.imax u' (piTelA ds B w).2)) := .pi Γ D' u' _ _ hD'' hB₂
      have hpiR : HasTyA E I n Γ (.pi D u (piTelA ds B w).1 (piTelA ds B w).2)
          (.sort (.imax u (piTelA ds B w).2)) := .pi Γ D u _ _ hD hB₁
      have hpiR' := hasTyA_sortEqN hpiR (eqNA_imax_left _ hu)
      have hA'' : ConvA E I n Γ D' D (.sort u') :=
        convA_sort_retypeA (.symm _ _ _ _ hcD) hu
      have hc : ConvA E I n Γ (.pi D' u' (piTelA ds B w).1 (piTelA ds B w).2)
          (.pi D u (piTelA ds B w).1 (piTelA ds B w).2) (.sort (.imax u' (piTelA ds B w).2)) :=
        .pi Γ D' D _ _ u' u _ _ (eqNA_symm hu) (eqNA_refl _) hA'' (.refl _ _ _ hB₂) hpiR'
      have tyc : TyConvA E I n Γ (.pi D' u' (piTelA ds B w).1 (piTelA ds B w).2)
          (.pi D u (piTelA ds B w).1 (piTelA ds B w).2) :=
        .of Γ _ _ _ _ _ hpiL (eqNA_refl _) hpiR' (eqNA_refl _) hc
      exact ⟨.lam Γ D D' _ _ _ u u' _ hu hcD ih (hasTyA_of_tyConvA hlam tyc)⟩

/-- the bound variables applied to the telescope lifted past its own binders reach the body. -/
theorem applyTelA_bvars_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) →
    applyTelA (paramLocalsA ds.length) (liftNA ds.length (piTelA ds B w).1) = some B
  | [] => rfl
  | (D, u) :: ds => by
      have hpiE : liftNA (ds.length + 1) (piTelA ((D, u) :: ds) B w).1 =
          .pi (liftA 0 (ds.length + 1) D) u (liftA 1 (ds.length + 1) (piTelA ds B w).1)
            (piTelA ds B w).2 := by
        rw [liftNA_eq]; rfl
      rw [List.length_cons, hpiE]
      show applyTelA (paramLocalsA ds.length) (instantiate0A (.bvar ds.length) _) = _
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq]
      exact applyTelA_bvars_piTelA B w ds

theorem map_wkExprA_telWorldA (ds : List (ExprA × Level)) (qs : List ExprA) :
    qs.map (wkExprA (telWorldA ds)) = qs.map (liftNA ds.length) :=
  List.map_congr_left (fun e _ => wkExprA_telWorldA ds e)


/-- the domain's shape, the binders' count that of the substituted telescope. -/
theorem frecDomA_eq_piTelA' (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA)
    (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) :
    frecDomA f ls w pl σ ds idx =
      piTelA (substTelA σ ds) (foldAppsA (.const f ls)
        (pl.map (liftNA (substTelA σ ds).length) ++
          idx.map (substA (upNA (substTelA σ ds).length σ)))) w := by
  rw [substTelA_length]; exact frecDomA_eq_piTelA f ls w idx ds pl σ

/-- the induction hypothesis's binder at the field, the binders' count that of the substituted telescope. -/
theorem frecIHA_closed' (wM : Level) (idx : List ExprA) (mot v : ExprA) (σ : SubstA)
    (ds : List (ExprA × Level)) :
    substA (SubstA.cons v SubstA.id) (frecIHA wM (liftA 0 1 mot) 0 σ.shift1 ds idx ds.length).1 =
      (piTelA (substTelA σ ds) (foldAppsA (liftNA (substTelA σ ds).length mot)
        (idx.map (substA (upNA (substTelA σ ds).length σ)) ++
          [foldAppsA (liftNA (substTelA σ ds).length v) (paramLocalsA (substTelA σ ds).length)])) wM).1 := by
  rw [substTelA_length]; exact frecIHA_closed wM idx mot v σ ds

theorem frecIHA_closed_cons (wM : Level) (idx : List ExprA) (mot v : ExprA) (σ : SubstA)
    (d : ExprA × Level) (ds : List (ExprA × Level)) :
    substA (SubstA.cons v SubstA.id) (frecIHA wM (liftA 0 1 mot) 0 σ.shift1 (d :: ds) idx (ds.length + 1)).1 =
      (piTelA (substTelA σ (d :: ds)) (foldAppsA (liftNA (substTelA σ (d :: ds)).length mot)
        (idx.map (substA (upNA (substTelA σ (d :: ds)).length σ)) ++
          [foldAppsA (liftNA (substTelA σ (d :: ds)).length v)
            (paramLocalsA (substTelA σ (d :: ds)).length)])) wM).1 :=
  frecIHA_closed' wM idx mot v σ (d :: ds)

theorem piDomListA_frecDomA (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA)
    (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) :
    piDomListA (frecDomA f ls w pl σ ds idx).1 = substTelA σ ds := by
  rw [frecDomA_eq_piTelA, piDomListA_piTelA, piDomListA_of_not_pi (foldAppsA_const_ne_pi f ls _),
    List.append_nil]


end World

#print axioms telWorldA
#print axioms wkCtxA_telWorldA
#print axioms wkExprA_telWorldA
#print axioms wkOkA_telWorldA
#print axioms frecDomA_eq_piTelA
#print axioms frecIHA_eq_piTelA
#print axioms argsRelKA_bvarsA
#print axioms telTyA_of_hasTy_piTelA
#print axioms argsRelKA_bvarsA_of_lrEqA
#print axioms substA_piTelA
#print axioms frecIHA_closed
#print axioms isPiTelA_frecIHA
#print axioms isPiTelA_frecDomA
#print axioms argsRelKA_frecDomA_closed
#print axioms map_wkExprA_telWorldA
#print axioms applyTelA_bvars_piTelA
#print axioms eqNA_imax_left
#print axioms convA_sort_retypeA
#print axioms convA_lamTelA₂
#print axioms frecDomA_eq_piTelA'
#print axioms frecIHA_closed'
#print axioms frecIHA_closed_cons
#print axioms piDomListA_frecDomA

end Rcic.Declarative.Ann
