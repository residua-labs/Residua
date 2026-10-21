import rcic.RcicAnnRecTel
import rcic.RcicAnnSpineConv
import rcic.RcicAnnFrecDomSyn

/-!
# R-NoFunRec-1 step 1 (1c-ε2d): the typed-telescope toolkit

Typed telescopes (`TelTyA`), the λ- and Π-telescope builders' typing and conversion, the λ-wrapped
recursor call's typing and conversion (`hasTyA_recCallFunA`, `convA_recCallFunA`), one typed β-step
(`stepAtA_beta`), telescopes under typed substitutions (`TelTyA.subst`) and the plain-field walks'
conversions, below the minor walk that reads them (moved verbatim from `RcicAnnRecSem`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Tel
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a telescope's domains typed in order, each at its level, in the context of the earlier ones. -/
inductive TelTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : LCtxA → List (ExprA × Level) → Type
  | nil (Γ : LCtxA) : TelTyA E I n Γ []
  | cons (Γ : LCtxA) (D : ExprA) (u : Level) (ds : List (ExprA × Level))
      (hD : HasTyA E I n Γ D (.sort u)) (tl : TelTyA E I n (.assumption D :: Γ) ds) :
      TelTyA E I n Γ ((D, u) :: ds)

/-- THE TELESCOPE BUILDER IS TYPED: `piTelA` is a chain of `HasTyA.pi` nodes, its levels the `imax`
    chain the rule computes. -/
def hasTyA_piTelA : {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds →
    {B : ExprA} → {w : Level} → HasTyA E I n (telCtxA ds ++ Γ) B (.sort w) →
    HasTyA E I n Γ (piTelA ds B w).1 (.sort (piTelA ds B w).2)
  | _, _, .nil _, _, _, hB => hB
  | _, _, .cons Γ D u ds hD tl, B, w, hB =>
      .pi Γ D u (piTelA ds B w).1 (piTelA ds B w).2 hD
        (hasTyA_piTelA tl ((telCtxA_cons_append (D, u) ds Γ) ▸ hB))

/-- a typed telescope extends a well-formed context. -/
def ctxWfA_telCtx : {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds →
    CtxWfA E I n Γ → CtxWfA E I n (telCtxA ds ++ Γ)
  | _, _, .nil _, hΓ => hΓ
  | _, _, .cons Γ D u ds hD tl, hΓ =>
      (telCtxA_cons_append (D, u) ds Γ) ▸ ctxWfA_telCtx tl (.assumption hΓ hD)

/-- a typed telescope over `xs ++ ys` is `xs` typed, then `ys` typed after it. -/
def TelTyA.split : {Γ : LCtxA} → (xs : List (ExprA × Level)) → {ys : List (ExprA × Level)} →
    TelTyA E I n Γ (xs ++ ys) → TelTyA E I n Γ xs × TelTyA E I n (telCtxA xs ++ Γ) ys
  | _, [], _, h => (.nil _, h)
  | Γ, (D, u) :: xs, _, .cons _ _ _ _ hD tl =>
      let r := TelTyA.split xs tl
      (.cons _ _ _ _ hD r.1, (telCtxA_cons_append (D, u) xs Γ).symm ▸ r.2)

/-- W-1 (c): THE λ-TELESCOPE IS TYPED at the Π-telescope over the same binders, its body typed under
    them at a codomain typed there. -/
def hasTyA_lamTelA : {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds →
    {b B : ExprA} → {w : Level} → HasTyA E I n (telCtxA ds ++ Γ) B (.sort w) →
    HasTyA E I n (telCtxA ds ++ Γ) b B → HasTyA E I n Γ (lamTelA ds b) (piTelA ds B w).1
  | _, _, .nil _, _, _, _, _, hb => hb
  | _, _, .cons Γ D u ds hD tl, b, B, w, hB, hb =>
      .lam Γ D u (lamTelA ds b) (piTelA ds B w).1 (piTelA ds B w).2 hD
        (hasTyA_piTelA tl ((telCtxA_cons_append (D, u) ds Γ) ▸ hB))
        (hasTyA_lamTelA tl ((telCtxA_cons_append (D, u) ds Γ) ▸ hB) ((telCtxA_cons_append (D, u) ds Γ) ▸ hb))

/-- R-NoFunRec-1 step 1 (1c-ε2a): THE λ-TELESCOPE CONVERTS ALONG A TELESCOPE. Two bodies convertible at
    a codomain under the same typed binders give λ-telescopes convertible at the Π-telescope over those
    binders (`ConvA.lam` at each binder, the annotations by reflexivity; the right side typed by
    `hasTyA_lamTelA`). No consumer yet: ε2d and ε2e read it at the function-recursive call. -/
def convA_lamTelA : {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Γ ds →
    {b b' B : ExprA} → {w : Level} → HasTyA E I n (telCtxA ds ++ Γ) B (.sort w) →
    ConvA E I n (telCtxA ds ++ Γ) b b' B → HasTyA E I n (telCtxA ds ++ Γ) b' B →
    ConvA E I n Γ (lamTelA ds b) (lamTelA ds b') (piTelA ds B w).1
  | _, _, .nil _, _, _, _, _, _, hc, _ => hc
  | _, _, .cons Γ D u ds hD tl, b, b', B, w, hB, hc, hb' =>
      .lam Γ D D (lamTelA ds b) (lamTelA ds b') (piTelA ds B w).1 u u (piTelA ds B w).2 (fun _ => rfl)
        (.refl Γ D _ hD)
        (convA_lamTelA tl ((telCtxA_cons_append (D, u) ds Γ) ▸ hB) ((telCtxA_cons_append (D, u) ds Γ) ▸ hc)
          ((telCtxA_cons_append (D, u) ds Γ) ▸ hb'))
        (hasTyA_lamTelA (.cons Γ D u ds hD tl) hB hb')

/-- R-NoFunRec-1 step 1 (1c-ε2a): THE λ-WRAPPED CALL IS TYPED. If the direct call at the field's inner
    binders (the recursor's prefix lifted past them, applied to the indices and to the field applied to
    the inner variables) is typed at a codomain `Bres` under the field's inner domains `piDomListA A`,
    typed as a telescope, then `recCallFunA` is typed at the Π-telescope over those domains ending in
    `Bres`. Identifying that telescope with the minor's `frecIHA` is the consumer's (ε2d, ε2e). No
    consumer yet. -/
def hasTyA_recCallFunA {Γ : LCtxA} (rec : ExprA) (preMajor : List ExprA) (np nm : Nat) (v A : ExprA)
    (td : TelTyA E I n Γ (piDomListA A)) {Bres : ExprA} {w : Level}
    (hB : HasTyA E I n (telCtxA (piDomListA A) ++ Γ) Bres (.sort w))
    (hb : HasTyA E I n (telCtxA (piDomListA A) ++ Γ)
      (recCallFieldA rec (preMajor.map (liftA 0 (piDomListA A).length)) np nm
        (foldAppsA (liftA 0 (piDomListA A).length v) ((List.range (piDomListA A).length).reverse.map ExprA.bvar))
        (piBodyA A)) Bres) :
    HasTyA E I n Γ (recCallFunA rec preMajor np nm v A) (piTelA (piDomListA A) Bres w).1 :=
  hasTyA_lamTelA td hB hb

/-- the two sides' λ-wrapped calls convert when their direct calls do at the inner binders, the right
    one typed there. -/
def convA_recCallFunA {Γ : LCtxA} (rec rec' : ExprA) (preMajor preMajor' : List ExprA) (np nm : Nat)
    (v v' A : ExprA) (td : TelTyA E I n Γ (piDomListA A)) {Bres : ExprA} {w : Level}
    (hB : HasTyA E I n (telCtxA (piDomListA A) ++ Γ) Bres (.sort w))
    (hc : ConvA E I n (telCtxA (piDomListA A) ++ Γ)
      (recCallFieldA rec (preMajor.map (liftA 0 (piDomListA A).length)) np nm
        (foldAppsA (liftA 0 (piDomListA A).length v) ((List.range (piDomListA A).length).reverse.map ExprA.bvar))
        (piBodyA A))
      (recCallFieldA rec' (preMajor'.map (liftA 0 (piDomListA A).length)) np nm
        (foldAppsA (liftA 0 (piDomListA A).length v') ((List.range (piDomListA A).length).reverse.map ExprA.bvar))
        (piBodyA A)) Bres)
    (hb' : HasTyA E I n (telCtxA (piDomListA A) ++ Γ)
      (recCallFieldA rec' (preMajor'.map (liftA 0 (piDomListA A).length)) np nm
        (foldAppsA (liftA 0 (piDomListA A).length v') ((List.range (piDomListA A).length).reverse.map ExprA.bvar))
        (piBodyA A)) Bres) :
    ConvA E I n Γ (recCallFunA rec preMajor np nm v A) (recCallFunA rec' preMajor' np nm v' A)
      (piTelA (piDomListA A) Bres w).1 :=
  convA_lamTelA td hB hc hb'

/-- R-NoFunRec-1 step 1 (1c-ε2a): ONE TYPED β-STEP, as the expansion lemmas take it. The telescope's
    iterated step (the λ-telescope applied to all its arguments) is open: it needs the typed partial
    spine at each binder (`TyHRedA.app`'s premises) and the instantiated telescope's typing. -/
theorem stepAtA_beta (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} {A body arg B : ExprA} {u v w : Level} (hΓ : CtxWfA E I n Γ)
    (hA : HasTyA E I n Γ A (.sort u)) (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hbody : HasTyA E I n (.assumption A :: Γ) body B) (harg : HasTyA E I n Γ arg A)
    (hTy : HasTyA E I n Γ (instantiate0A arg B) (.sort w)) :
    StepAtA E I n Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B) :=
  ⟨⟨.app Γ _ _ A B u v w hB hTy (.lam Γ A u body B v hA hB hbody) harg⟩,
   ⟨.beta Γ A u body arg B hA hbody harg (hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hbody harg hA)⟩⟩

/-- a typed telescope over `xs`, then one more domain typed after it. -/
def TelTyA.snoc : {Γ : LCtxA} → {xs : List (ExprA × Level)} → TelTyA E I n Γ xs → {D : ExprA} → {u : Level} →
    HasTyA E I n (telCtxA xs ++ Γ) D (.sort u) → TelTyA E I n Γ (xs ++ [(D, u)])
  | Γ, _, .nil _, _, _, hD => .cons Γ _ _ [] hD (.nil _)
  | Γ, _, .cons _ D₀ u₀ ds hD₀ tl, D, u, hD =>
      .cons Γ D₀ u₀ (ds ++ [(D, u)]) hD₀ (TelTyA.snoc tl ((telCtxA_cons_append (D₀, u₀) ds Γ) ▸ hD))

/-- a typed telescope's levels instantiated. -/
def TelTyA.instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) {a : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I a Γ ds →
    TelTyA E I n (instCtxA ls Γ) (instDomsA ls ds)
  | _, _, .nil _ => .nil _
  | _, _, .cons _ _ _ _ hD tl => .cons _ _ _ _ (hasTyA_instLevels hEL hIL hls hlen hD) (TelTyA.instLevels hEL hIL hls hlen tl)

/-- a typed telescope read in an extension of the environment. -/
def TelTyA.env {E₀ : ResolvedEnvA} (hpre : PrefixA E₀ E) :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E₀ I n Γ ds → TelTyA E I n Γ ds
  | _, _, .nil _ => .nil _
  | _, _, .cons _ _ _ _ hD tl => .cons _ _ _ _ (hasTyEnvA hpre hD) (TelTyA.env hpre tl)

/-- a typed telescope of PROPOSITIONS extends proof binders by its own. -/
def propExtA_telTyA {Θ : LCtxA} : {Γ : LCtxA} → {m : Nat} → PropExtA E I n Θ Γ m →
    {ds : List (ExprA × Level)} → TelTyA E I n Γ ds → (∀ d ∈ ds, eqN d.2 .zero) →
    PropExtA E I n Θ (telCtxA ds ++ Γ) (m + ds.length)
  | _, _, h, _, .nil _, _ => h
  | Γ, m, h, _, .cons _ D u ds hD tl, hz =>
      have e1 : telCtxA ds ++ (.assumption D :: Γ) = telCtxA ((D, u) :: ds) ++ Γ :=
        (telCtxA_cons_append (D, u) ds Γ).symm
      have e2 : m + 1 + ds.length = m + ((D, u) :: ds).length := by
        simp only [List.length_cons]; omega
      e2 ▸ e1 ▸ propExtA_telTyA (.cons h hD (hz (D, u) (List.mem_cons_self _ _))) tl
        (fun d hd => hz d (List.mem_cons_of_mem _ hd))


/-- `liftNA` is one lift by the count. -/
theorem liftNA_eq (e : ExprA) : (m : Nat) → liftNA m e = liftA 0 m e
  | 0 => (liftA_zero 0 e).symm
  | m + 1 => by
      show liftA 0 1 (liftNA m e) = _
      rw [liftNA_eq e m, liftA_liftA_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _)]

theorem upNA_add : (m : Nat) → (τ : SubstA) → (p : Nat) → upNA m τ (p + m) = liftNA m (τ p)
  | 0, _, _ => rfl
  | m + 1, τ, p => by
      show upNA m τ.up (p + (m + 1)) = liftA 0 1 (liftNA m (τ p))
      rw [show p + (m + 1) = (p + 1) + m by omega, upNA_add m τ.up (p + 1)]
      show liftNA m (liftA 0 1 (τ p)) = liftA 0 1 (liftNA m (τ p))
      rw [liftNA_eq, liftNA_eq, liftA_liftA_merge 1 m 0 0 (Nat.le_refl 0) (Nat.zero_le _),
        liftA_liftA_merge m 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm]

theorem liftNA_bvar (m i : Nat) : liftNA m (.bvar i) = .bvar (i + m) := by
  rw [liftNA_eq]
  show (if 0 ≤ i then ExprA.bvar (i + m) else .bvar i) = _
  rw [if_pos (Nat.zero_le i)]

theorem liftNA_sort (m : Nat) (l : Level) : liftNA m (.sort l) = .sort l := by
  induction m with
  | zero => rfl
  | succ m ih => show liftA 0 1 (liftNA m (.sort l)) = _; rw [ih]; rfl

/-- a telescope's domains under a substitution, each under the earlier binders. -/
def substTelA : SubstA → List (ExprA × Level) → List (ExprA × Level)
  | _, [] => []
  | σ, (D, u) :: ds => (substA σ D, u) :: substTelA σ.up ds

theorem substTelA_length : (σ : SubstA) → (ds : List (ExprA × Level)) → (substTelA σ ds).length = ds.length
  | _, [] => rfl
  | σ, (_, _) :: ds => by simp only [substTelA, List.length_cons, substTelA_length σ.up ds]

/-- A TYPED TELESCOPE UNDER A TYPED SUBSTITUTION: the substituted domains typed, and the substitution
    under the binders typed into the context they extend. -/
def TelTyA.subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) :
    {Θ : LCtxA} → {ds : List (ExprA × Level)} → TelTyA E I n Θ ds → {Δ : LCtxA} → {σ : SubstA} →
    SubstTyA E I n Δ σ Θ →
    TelTyA E I n Δ (substTelA σ ds) ×
      SubstTyA E I n (telCtxA (substTelA σ ds) ++ Δ) (upNA ds.length σ) (telCtxA ds ++ Θ)
  | _, _, .nil _, _, _, hσ => (.nil _, hσ)
  | Θ, _, .cons _ D u ds hD tl, Δ, σ, hσ =>
      let hD' : HasTyA E I n Δ (substA σ D) (.sort u) := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hD
      let r := TelTyA.subst hE hI hR hIS tl (substTyA_up hE hI hσ hD')
      (.cons Δ (substA σ D) u _ hD' r.1,
        (telCtxA_cons_append (D, u) ds Θ).symm ▸ (telCtxA_cons_append (substA σ D, u) (substTelA σ.up ds) Δ).symm ▸ r.2)

theorem consListA_paramLocalsA_lt : (m : Nat) → (X : SubstA) → (i : Nat) → i < m →
    consListA (paramLocalsA m) X i = .bvar i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, X, i, h => by
      show consListA (paramLocalsA m) (SubstA.cons (.bvar m) X) i = .bvar i
      by_cases hi : i < m
      · exact consListA_paramLocalsA_lt m _ i hi
      · obtain rfl : i = m := by omega
        have h1 := consListA_add (paramLocalsA i) (SubstA.cons (.bvar i) X) 0
        rw [paramLocalsA_length, Nat.zero_add] at h1
        rw [h1]
        rfl

theorem consListA_map (g : ExprA → ExprA) : (qs : List ExprA) → (τ : SubstA) → (p : Nat) →
    consListA (qs.map g) (fun i => g (τ i)) p = g (consListA qs τ p)
  | [], _, _ => rfl
  | q :: qs, τ, p => by
      show consListA (qs.map g) (SubstA.cons (g q) (fun i => g (τ i))) p = g (consListA qs (SubstA.cons q τ) p)
      have e : SubstA.cons (g q) (fun i => g (τ i)) = fun i => g (SubstA.cons q τ i) := by
        funext i; cases i <;> rfl
      rw [e, consListA_map g qs]

/-- `m` binders up from a list of values: the bound variables, then the values lifted. -/
theorem upNA_consListA (m : Nat) (qs : List ExprA) (τ : SubstA) (i : Nat) :
    upNA m (consListA qs τ) i =
      consListA (paramLocalsA m) (consListA (qs.map (liftNA m)) (fun j => liftNA m (τ j))) i := by
  by_cases hi : i < m
  · rw [upNA_lt m _ i hi, consListA_paramLocalsA_lt m _ i hi]
  · obtain ⟨p, rfl⟩ : ∃ p, i = p + m := ⟨i - m, by omega⟩
    rw [upNA_add, show p + m = p + (paramLocalsA m).length by rw [paramLocalsA_length], consListA_add,
      consListA_map]

/-- at plain fields ι's arguments are the fields themselves (W-1 (e): ι at a struct group contracts to
    the minor at the constructor's fields). -/
theorem rhsArgsA_plain (rc : ExprA) (PRE : List ExprA) (np K : Nat) (f : Nat) (ls : List Level) (wF : Level)
    (res : List ExprA) (pl : List ExprA) :
    (ds ds' : List (ExprA × Level)) → (σ : SubstA) → (vs : List ExprA) → vs.length = ds.length →
    ds'.length = ds.length →
    rhsArgsA rc PRE np K vs ((ds'.map plainA).map FieldA.shape) (ctorFieldsA f ls wF pl σ (ds.map plainA) res).1 = vs
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, h, _ => (Nat.succ_ne_zero _ h).elim
  | _ :: _, _, _, [], h, _ => (Nat.succ_ne_zero _ h.symm).elim
  | _ :: _, [], _, _ :: _, _, h' => (Nat.succ_ne_zero _ h'.symm).elim
  | (D, u) :: ds, _ :: ds', σ, v :: vs, h, h' => by
      show v :: (recCallsA rc PRE np K v (substA σ D) .nonrecursive ++
        rhsArgsA rc PRE np K vs ((ds'.map plainA).map FieldA.shape)
          (instantiate0A v (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.up (ds.map plainA) res).1)) = v :: vs
      rw [instantiate0A_ctorFieldsA_plain f ls wF res (ds.map plainA) pl σ v,
        rhsArgsA_plain rc PRE np K f ls wF res pl ds ds' _ vs (Nat.succ.inj h) (Nat.succ.inj h')]
      rfl

/-- a minor premise of plain fields binds the fields' domains, substituted. -/
theorem piDomListA_minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    piDomListA (minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res).1 = substTelA σ ds
  | [], pl, mot, fl, σ => by
      simp only [List.map, minorFieldsA]
      rw [foldAppsA_snoc]
      rfl
  | (D, u) :: ds, pl, mot, fl, σ => by
      simp only [List.map, plainA, minorFieldsA, piDomListA, substTelA]
      rw [← piDomListA_minorFieldsA f c ls wF wM res ds]

/-- the variable of a telescope's outermost binder, under the later ones. -/
theorem lookupTypeA_telCtxA_head (D : ExprA) (u : Level) (ds : List (ExprA × Level)) (Θ : LCtxA) :
    lookupTypeA (telCtxA ((D, u) :: ds) ++ Θ) ds.length = some (liftA 0 (ds.length + 1) D) := by
  rw [telCtxA_cons_append]
  unfold lookupTypeA
  rw [List.get?_eq_getElem?, List.getElem?_append_right (by simp [telCtxA])]
  simp [telCtxA]

/-- the head binder's value read off the extension's substitution. -/
theorem consListA_cons_head (a : ExprA) (as : List ExprA) (σ : SubstA) :
    consListA (a :: as) σ as.length = a := by
  have h := consListA_add as (SubstA.cons a σ) 0
  rw [Nat.zero_add] at h
  exact h

theorem substA_consListA_cons_liftA (a : ExprA) (as : List ExprA) (σ : SubstA) (D : ExprA) :
    substA (consListA (a :: as) σ) (liftA 0 (as.length + 1) D) = substA σ D := by
  show substA (consListA as (SubstA.cons a σ)) (liftA 0 (as.length + 1) D) = substA σ D
  rw [show as.length + 1 = 1 + as.length from Nat.add_comm _ _,
    ← liftA_liftA_merge as.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) D, substA_consListA_liftA,
    substA_cons_liftA]

/-- W-1 (c): A CONVERTIBLE PAIR OF VALUES FOR A MINOR PREMISE'S PLAIN FIELDS is pointwise convertible
    along the minor's telescope. -/
theorem convArgsA_minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) {Δ : LCtxA} :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) →
    (σ σ' : SubstA) → (as as' : List ExprA) → as.length = ds.length → as'.length = ds.length →
    ConvSubstA E I n Δ (consListA as σ) (consListA as' σ') (telCtxA ds ++ Θ) →
    ConvArgsA E I n Δ (minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res).1 as as'
  | [], _, _, _, _, _, _, [], [], _, _, _ => .nil _
  | (D, u) :: ds, Θ, pl, mot, fl, σ, σ', a :: as, a' :: as', hl, hl', h => by
      have hl₀ : as.length = ds.length := Nat.succ.inj hl
      have hl₀' : as'.length = ds.length := Nat.succ.inj hl'
      have hc := h.conv ds.length _ (lookupTypeA_telCtxA_head D u ds Θ)
      rw [← hl₀, substA_consListA_cons_liftA] at hc
      have e1 : consListA (a :: as) σ as.length = a := consListA_cons_head a as σ
      have e2 : consListA (a' :: as') σ' as.length = a' := by
        rw [show as.length = as'.length by rw [hl₀, hl₀']]; exact consListA_cons_head a' as' σ'
      rw [e1, e2] at hc
      simp only [List.map, plainA, minorFieldsA]
      refine .cons _ _ _ _ a a' as as' ⟨hc⟩ ?_
      rw [instantiate0A_minorFieldsA_plain]
      have h' : ConvSubstA E I n Δ (consListA as (SubstA.cons a σ)) (consListA as' (SubstA.cons a' σ'))
          (telCtxA ds ++ (.assumption D :: Θ)) := (telCtxA_cons_append (D, u) ds Θ) ▸ h
      exact convArgsA_minorFieldsA f c ls wF wM res ds _ pl mot (fl ++ [a]) _ _ as as' hl₀ hl₀' h'

/-- W-1 (c): the same along a constructor's plain fields. -/
theorem convArgsA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) {Δ : LCtxA} :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (pl : List ExprA) →
    (σ σ' : SubstA) → (as as' : List ExprA) → as.length = ds.length → as'.length = ds.length →
    ConvSubstA E I n Δ (consListA as σ) (consListA as' σ') (telCtxA ds ++ Θ) →
    ConvArgsA E I n Δ (ctorFieldsA f ls w pl σ (ds.map plainA) res).1 as as'
  | [], _, _, _, _, [], [], _, _, _ => .nil _
  | (D, u) :: ds, Θ, pl, σ, σ', a :: as, a' :: as', hl, hl', h => by
      have hl₀ : as.length = ds.length := Nat.succ.inj hl
      have hl₀' : as'.length = ds.length := Nat.succ.inj hl'
      have hc := h.conv ds.length _ (lookupTypeA_telCtxA_head D u ds Θ)
      rw [← hl₀, substA_consListA_cons_liftA] at hc
      have e1 : consListA (a :: as) σ as.length = a := consListA_cons_head a as σ
      have e2 : consListA (a' :: as') σ' as.length = a' := by
        rw [show as.length = as'.length by rw [hl₀, hl₀']]; exact consListA_cons_head a' as' σ'
      rw [e1, e2] at hc
      simp only [List.map, plainA, ctorFieldsA]
      refine .cons _ _ _ _ a a' as as' ⟨hc⟩ ?_
      rw [instantiate0A_ctorFieldsA_plain]
      have h' : ConvSubstA E I n Δ (consListA as (SubstA.cons a σ)) (consListA as' (SubstA.cons a' σ'))
          (telCtxA ds ++ (.assumption D :: Θ)) := (telCtxA_cons_append (D, u) ds Θ) ▸ h
      exact convArgsA_ctorFieldsA f ls w res ds _ pl _ _ as as' hl₀ hl₀' h'

/-- W-1 (c): A VALID PAIR OF VALUES FOR A MINOR PREMISE'S PLAIN FIELDS is related along the minor's
    telescope. -/
theorem argsRelKA_minorFieldsA {ρ₀ : Nat → Nat} {k : Nat} (f c : Nat) (ls : List Level) (wF wM : Level)
    (res : List ExprA) {Δ : LCtxA} :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) →
    (σ σ' : SubstA) → (as as' : List ExprA) → as.length = ds.length → as'.length = ds.length →
    ValidSubstA E I n ρ₀ k Δ (consListA as σ) (consListA as' σ') (telCtxA ds ++ Θ) →
    ArgsRelKA E I n ρ₀ k Δ (minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res).1 as as'
  | [], _, _, _, _, _, _, [], [], _, _, _ => .nil _
  | (D, u) :: ds, Θ, pl, mot, fl, σ, σ', a :: as, a' :: as', hl, hl', h => by
      have hl₀ : as.length = ds.length := Nat.succ.inj hl
      have hl₀' : as'.length = ds.length := Nat.succ.inj hl'
      have hc := (h.1 ds.length _ (lookupTypeA_telCtxA_head D u ds Θ)).2
      rw [← hl₀, substA_consListA_cons_liftA] at hc
      have e1 : consListA (a :: as) σ as.length = a := consListA_cons_head a as σ
      have e2 : consListA (a' :: as') σ' as.length = a' := by
        rw [show as.length = as'.length by rw [hl₀, hl₀']]; exact consListA_cons_head a' as' σ'
      rw [e1, e2] at hc
      simp only [List.map, plainA, minorFieldsA]
      refine .cons _ _ _ _ a a' as as' hc ?_
      rw [instantiate0A_minorFieldsA_plain]
      have h' : ValidSubstA E I n ρ₀ k Δ (consListA as (SubstA.cons a σ)) (consListA as' (SubstA.cons a' σ'))
          (telCtxA ds ++ (.assumption D :: Θ)) := (telCtxA_cons_append (D, u) ds Θ) ▸ h
      exact argsRelKA_minorFieldsA f c ls wF wM res ds _ pl mot (fl ++ [a]) _ _ as as' hl₀ hl₀' h'

/-- a constructor's plain fields' telescope (its recursive fields skipped, as the plain context skips
    them). -/
def plainTelA : List FieldA → List (ExprA × Level)
  | [] => []
  | .plain D u :: fs => (D, u) :: plainTelA fs
  | .drec _ :: fs | .frec _ _ _ _ :: fs | .drecD _ _ :: fs => plainTelA fs

/-- with every field plain, the fields are their telescope's. -/
theorem fields_plainTelA : (fs : List FieldA) → (∀ fld ∈ fs, ∃ D u, fld = .plain D u) →
    fs = (plainTelA fs).map plainA
  | [], _ => rfl
  | .plain D u :: fs, h => by
      simp only [plainTelA, List.map, plainA]
      rw [← fields_plainTelA fs (fun fld hf => h fld (List.mem_cons_of_mem _ hf))]
  | .drec _ :: _, h | .frec _ _ _ _ :: _, h | .drecD _ _ :: _, h => by
      obtain ⟨D, u, e⟩ := h _ (List.mem_cons_self _ _)
      exact FieldA.noConfusion e

theorem plainTelA_instLevels (ls : List Level) :
    (fs : List FieldA) → plainTelA (fs.map (FieldA.instLevels ls)) = instDomsA ls (plainTelA fs)
  | [] => rfl
  | .plain D u :: fs => by
      simp only [List.map, FieldA.instLevels, plainTelA, instDomsA] at *
      rw [plainTelA_instLevels ls fs]
      rfl
  | .drec _ :: fs | .frec _ _ _ _ :: fs | .drecD _ _ :: fs => by
      simp only [List.map, FieldA.instLevels, plainTelA]
      exact plainTelA_instLevels ls fs

/-- the plain fields' typings, a telescope over the plain context. -/
def telTyA_of_fieldsTyA {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I n idxTel Γ k fs res → TelTyA E I n Γ (plainTelA fs)
  | _, _, _, _, .nil _ _ _ _ => .nil _
  | _, _, _, _, .plain Γ _ D u _ _ hD tl => .cons Γ D u _ hD (telTyA_of_fieldsTyA tl)
  | _, _, _, _, .drec Γ _ _ fs _ _ tl => (telTyA_of_fieldsTyA tl : TelTyA E I n Γ (plainTelA fs))
  | _, _, _, _, .frec Γ _ _ _ _ _ fs _ _ tl => (telTyA_of_fieldsTyA tl : TelTyA E I n Γ (plainTelA fs))
  | _, _, _, _, .drecD Γ _ _ _ fs _ _ tl => (telTyA_of_fieldsTyA tl : TelTyA E I n Γ (plainTelA fs))

/-- a minor premise of plain fields is the Π-telescope over its substituted domains, at the minor's
    state past them. -/
theorem minorFieldsA_plain_eq (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res =
      piTelA (substTelA σ ds)
        (minorFieldsA f c ls wF wM (pl.map (liftNA ds.length)) (liftNA ds.length mot)
          (fl.map (liftNA ds.length) ++ paramLocalsA ds.length) (upNA ds.length σ) [] res).1 wM
  | [], pl, mot, fl, σ => by
      have h1 : pl.map (liftNA 0) = pl := List.map_id'' (fun _ => rfl) pl
      have h2 : fl.map (liftNA 0) = fl := List.map_id'' (fun _ => rfl) fl
      simp only [List.map, List.length_nil, h1, h2, paramLocalsA, List.append_nil, substTelA, piTelA]
      rfl
  | (D, u) :: ds, pl, mot, fl, σ => by
      have ih := minorFieldsA_plain_eq f c ls wF wM res ds (pl.map (liftA 0 1)) (liftA 0 1 mot)
        (fl.map (liftA 0 1) ++ [.bvar 0]) σ.up
      have hl : ∀ e, liftNA ds.length (liftA 0 1 e) = liftNA (ds.length + 1) e := fun e => by
        rw [liftNA_eq, liftNA_eq, liftA_liftA_merge _ 1 0 0 (Nat.le_refl 0) (Nat.zero_le _), Nat.add_comm 1]
      have hpl : (pl.map (liftA 0 1)).map (liftNA ds.length) = pl.map (liftNA (ds.length + 1)) := by
        rw [List.map_map]; exact List.map_congr_left (fun e _ => hl e)
      have hfl : (fl.map (liftA 0 1) ++ [ExprA.bvar 0]).map (liftNA ds.length) ++ paramLocalsA ds.length =
          fl.map (liftNA (ds.length + 1)) ++ paramLocalsA (ds.length + 1) := by
        rw [List.map_append, List.map_map, List.map_singleton, liftNA_bvar, Nat.zero_add, List.append_assoc]
        congr 1
        · exact List.map_congr_left (fun e _ => hl e)
      rw [hpl, hl, hfl] at ih
      simp only [List.map, plainA, minorFieldsA, List.length_cons, substTelA, piTelA]
      rw [ih]
      rfl

/-- the plain fields' values, applied along a constructor's field telescope, extend its state. -/
theorem applyTelA_ctorFieldsA_plain (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) → (as : List ExprA) →
    as.length = ds.length →
    applyTelA as (ctorFieldsA f ls w pl σ (ds.map plainA) res).1 =
      some (ctorFieldsA f ls w pl (consListA as σ) [] res).1
  | [], _, _, [], _ => rfl
  | (D, u) :: ds, pl, σ, a :: as, h => by
      simp only [List.map, plainA, ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_plain]
      exact applyTelA_ctorFieldsA_plain f ls w res ds pl (SubstA.cons a σ) as (Nat.succ.inj h)
  | [], _, _, _ :: _, h => nomatch h
  | _ :: _, _, _, [], h => nomatch h

/-- the same along a minor premise's plain fields: the values join the field locals. -/
theorem applyTelA_minorFieldsA_plain (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    (as : List ExprA) → as.length = ds.length →
    applyTelA as (minorFieldsA f c ls wF wM pl mot fl σ (ds.map plainA) res).1 =
      some (minorFieldsA f c ls wF wM pl mot (fl ++ as) (consListA as σ) [] res).1
  | [], _, _, fl, _, [], _ => by rw [List.append_nil]; rfl
  | (D, u) :: ds, pl, mot, fl, σ, a :: as, h => by
      simp only [List.map, plainA, minorFieldsA, applyTelA]
      rw [instantiate0A_minorFieldsA_plain,
        applyTelA_minorFieldsA_plain f c ls wF wM res ds pl mot (fl ++ [a]) (SubstA.cons a σ) as (Nat.succ.inj h),
        List.append_assoc]
      rfl
  | [], _, _, _, _, _ :: _, h => nomatch h
  | _ :: _, _, _, _, _, [], h => nomatch h

/-- THE CONSTRUCTOR AT ITS PARAMETERS, ANY TAIL: a closed constructor type applied to its parameters is
    the field telescope at the state `(ps, consListA ps τ)`, whatever `τ` (`applyTelA_ctorTypeA_params` at
    `τ = id`). -/
theorem applyTelA_ctorTypeA_params_tail (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) (ps : List ExprA)
    (hps : ps.length = mirrors.length) (τ : SubstA) :
    applyTelA ps (substA τ (ctorTypeA f ls w mirrors fields res)) =
      some (ctorFieldsA f ls w ps (consListA ps τ) fields res).1 := by
  have h := applyTelA_piTelA (ctorFieldsA f ls w (paramLocalsA mirrors.length) SubstA.id fields res).1
    (ctorFieldsA f ls w (paramLocalsA mirrors.length) SubstA.id fields res).2 mirrors ps hps τ
  show applyTelA ps (substA τ (piTelA mirrors _ _).1) = _
  rw [h, substA_ctorFieldsA, ← hps, paramLocalsA_consListA]
  rfl

/-- a typed substitution, convertible with itself. -/
def convSubstA_refl {Δ Γ : LCtxA} {σ : SubstA} (h : SubstTyA E I n Δ σ Γ) : ConvSubstA E I n Δ σ σ Γ :=
  { left := h, right := h, conv := fun i A hA => .refl _ _ _ (h.ty i A hA) }

/-- a typing weakened past declarations pushed on top. -/
def hasTyA_liftN (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {e A : ExprA}
    (h : HasTyA E I n Γ e A) :
    (ds : List LocalDeclA) → HasTyA E I n (ds ++ Γ) (liftNA ds.length e) (liftNA ds.length A)
  | [] => h
  | d :: ds => hasTyWeakenA hE hI d (Nat.zero_le _) (hasTyA_liftN hE hI h ds)

/-- a pointwise list weakened past declarations pushed on top. -/
theorem convArgsA_liftN (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {T : ExprA} {xs ys : List ExprA}
    (h : ConvArgsA E I n Γ T xs ys) :
    (ds : List LocalDeclA) →
      ConvArgsA E I n (ds ++ Γ) (liftNA ds.length T) (xs.map (liftNA ds.length)) (ys.map (liftNA ds.length))
  | [] => by
      have e1 : xs.map (liftNA 0) = xs := List.map_id'' (fun _ => rfl) xs
      have e2 : ys.map (liftNA 0) = ys := List.map_id'' (fun _ => rfl) ys
      show ConvArgsA E I n Γ T (xs.map (liftNA 0)) (ys.map (liftNA 0))
      rw [e1, e2]
      exact h
  | d :: ds => by
      have h1 := convArgsA_wk hE hI [(d, 0)] ⟨Nat.zero_le _, trivial⟩ (convArgsA_liftN hE hI h ds)
      simp only [List.map_map] at h1
      exact h1

theorem substTelA_append : (σ : SubstA) → (xs ys : List (ExprA × Level)) →
    substTelA σ (xs ++ ys) = substTelA σ xs ++ substTelA (upNA xs.length σ) ys
  | _, [], _ => rfl
  | σ, (D, u) :: xs, ys => by
      show (substA σ D, u) :: substTelA σ.up (xs ++ ys) =
        ((substA σ D, u) :: substTelA σ.up xs) ++ substTelA (upNA (xs.length + 1) σ) ys
      rw [substTelA_append σ.up xs ys]
      rfl

/- (`telCtxA_length` landed upstream in `RcicAnnGroup` — same statement.) -/

/-- a list of values reads the same below its length, whatever the tail. -/
theorem consListA_lt_indep : (as : List ExprA) → (τ τ' : SubstA) → (j : Nat) → j < as.length →
    consListA as τ j = consListA as τ' j
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: as, τ, τ', j, h => by
      show consListA as (SubstA.cons a τ) j = consListA as (SubstA.cons a τ') j
      by_cases hj : j < as.length
      · exact consListA_lt_indep as _ _ j hj
      · obtain rfl : j = as.length := by simp only [List.length_cons] at h; omega
        have h1 := consListA_add as (SubstA.cons a τ) 0
        have h2 := consListA_add as (SubstA.cons a τ') 0
        rw [Nat.zero_add] at h1 h2
        rw [h1, h2]
        rfl

/-- values for a telescope's first binders, after the telescope's substitution pushed under them: the
    substitution extended by the values. -/
theorem substA_consListA_upNA (as : List ExprA) (σ : SubstA) (e : ExprA) :
    substA (consListA as SubstA.id) (substA (upNA as.length σ) e) = substA (consListA as σ) e := by
  rw [substA_substA]
  refine substA_ext (fun j => ?_) e
  by_cases hj : j < as.length
  · rw [upNA_lt _ _ _ hj, substA_bvar]
    exact consListA_lt_indep as _ _ j hj
  · obtain ⟨p, rfl⟩ : ∃ p, j = p + as.length := ⟨j - as.length, by omega⟩
    rw [upNA_add, liftNA_eq, substA_consListA_liftA, substA_id, consListA_add]

/-- instantiating the head binder of a substituted body under the values so far: one more value. -/
theorem instantiate0A_consListA_up (as : List ExprA) (a B : ExprA) :
    instantiate0A a (substA (consListA as SubstA.id).up B) = substA (consListA (as ++ [a]) SubstA.id) B := by
  rw [instantiate0A_substA_up, consListA_snoc]

theorem instantiate0A_liftA_one (a e : ExprA) : instantiate0A a (liftA 0 1 e) = e := by
  rw [instantiate0A_eq_substA_cons, substA_cons_liftA, substA_id]


end Tel

end Rcic.Declarative.Ann
