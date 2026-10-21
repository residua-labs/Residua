import rcic.RcicAnnTypedRows
import rcic.RcicAnnRecPins

/-!
# M3-c3 — ι subject reduction on the copy

`ConvA.iota` carries the reduct's typing at the redex's type (`hrhs`, a named M-001 deviation,
"discharged when the rows close"). The rows hold on the copy under the profile, and this module
discharges it: under every environment the copy admits (`AnnEnvA`), a ι step's reduct keeps the
redex's type (`iotaSRA`). So `hrhs` is derivable from the left-hand typing (`convA_iota_of_fn`), and
the annotation (`RcicAnnAnnotate`) and the rows on the typed judgment (`RcicAnnTypedRows`) hold with
no further hypothesis (§5).

The proof is syntactic. It runs on the copy's metatheory: type uniqueness (`hasTyA_uniq`), `PiConvInj`
at any codomain (`piConvInjA`), and row 3 (`famAppConvInjA_rec`).

* SPINE GENERATION (`spine_gen`). A typed spine's arguments walk its head's own type, each typed at the
  domain it reaches, and the type reached converts to the spine's type. Every argument fact below is
  read off a typed spine this way.
* At the redex the recursor's arguments split into parameters, motive, minors, indices and major.
  The major is a constructor application. Its type and the major's domain are two types of one term.
  Row 3 relates the constructor's parameters to the recursor's.
* The constructor's parameter telescope (its mirrors) differs from the family's. Type uniqueness
  relates them one domain at a time (`convArgsA_swap`), so the constructor at the recursor's levels and
  parameters converts with the major.
* The reduct's arguments walk the minor's telescope. A recursive call is a recursor spine at the
  field's indices, whose arguments join back along the recursor's telescope. The type reached is the
  motive at the minor's result indices and the rebuilt constructor. Row 3 again relates those indices
  to the redex's, so the two motive applications convert.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) walks along a telescope: split and join — in `RcicAnnRecTel` (W-1 (c) moved them up,
    for the recursors' clause at a struct group) -/

/-! ## (2) spine generation, the domain-wise swap, the minor walk -/

theorem applyTelA_single_pi {x U' U : ExprA} (h : applyTelA [x] U' = some U) :
    ∃ A u B v, U' = .pi A u B v ∧ U = instantiate0A x B := by
  cases U' <;> simp [applyTelA] at h
  exact ⟨_, _, _, _, rfl, h.symm⟩

theorem foldAppsA_ne_pi : (h : ExprA) → (∀ A u B v, h ≠ .pi A u B v) → (xs : List ExprA) →
    ∀ A u B v, foldAppsA h xs ≠ .pi A u B v
  | _, hh, [] => hh
  | h, _, x :: xs => foldAppsA_ne_pi (.app h x) (fun _ _ _ _ e => ExprA.noConfusion e) xs

theorem convArgsA_cons_pi {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {T x x' : ExprA}
    {xs xs' : List ExprA} (h : ConvArgsA E I n Γ T (x :: xs) (x' :: xs')) :
    ∃ A u B v, T = .pi A u B v := by
  cases h with
  | cons A u B v _ _ _ _ _ _ => exact ⟨A, u, B, v, rfl⟩

section Gen
variable {E : ResolvedEnvA} {n : Nat}

/-- SPINE GENERATION: a typed spine's arguments walk its head's type, each typed at the domain it
    reaches, and the type reached converts to the spine's type. -/
theorem spine_gen (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {h H : ExprA}
    (hh : HasTyA E (iotaIfaceA E) n Γ h H) :
    ∀ (xs : List ExprA) {U T : ExprA}, applyTelA xs H = some U →
      HasTyA E (iotaIfaceA E) n Γ (foldAppsA h xs) T →
      ConvArgsA E (iotaIfaceA E) n Γ H xs xs ∧ Nonempty (TyConvA E (iotaIfaceA E) n Γ U T) := by
  refine snocInduction (P := fun xs => ∀ {U T : ExprA}, applyTelA xs H = some U →
      HasTyA E (iotaIfaceA E) n Γ (foldAppsA h xs) T →
      ConvArgsA E (iotaIfaceA E) n Γ H xs xs ∧ Nonempty (TyConvA E (iotaIfaceA E) n Γ U T)) ?_ ?_
  · intro U T hU hT
    injection hU with hU
    subst hU
    exact ⟨.nil _, hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ hh hT⟩
  · intro xs x ih U T hU hT
    obtain ⟨U', hU', hx⟩ := applyTelA_append_some hU
    obtain ⟨A, u, B, v, rfl, rfl⟩ := applyTelA_single_pi hx
    rw [foldAppsA_snoc] at hT
    obtain ⟨A₁, u₁, B₁, v₁, _, ⟨hf⟩, ⟨ha⟩, _, _, ⟨t⟩⟩ := hasTyA_app_gen hT
    obtain ⟨hargs, ⟨tf⟩⟩ := ih hU' hf
    obtain ⟨cF⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hargs ⟨.refl Γ h H hh⟩ _ hU'
    obtain ⟨_, hl⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cF)
    have cpi := tyConvA_collapse C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ tf hl
    obtain ⟨_, _, ⟨tA⟩, ⟨tB⟩⟩ := piConvInjA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ cpi
    have ha' : HasTyA E (iotaIfaceA E) n Γ x A := hasTyA_of_tyConvA ha tA.symm
    refine ⟨convArgsA_append hargs hU' (.cons A u B v x x [] [] ⟨.refl Γ x A ha'⟩ (.nil _)), ?_⟩
    exact ⟨.trans _ _ _ _ (tyConvA_inst0 C.hE C.hI C.hR C.hIS hΓ ha' tB) t⟩

/-- THE DOMAIN-WISE SWAP: a list pointwise convertible with another along one telescope, and typed
    along a second, is pointwise convertible with it along the second. Each domain pair are two types of
    one term, so type uniqueness converts them. -/
theorem convArgsA_swap (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) :
    {T T' : ExprA} → {xs ys : List ExprA} → ConvArgsA E (iotaIfaceA E) n Γ T xs ys →
      ConvArgsA E (iotaIfaceA E) n Γ T' ys ys → ConvArgsA E (iotaIfaceA E) n Γ T' ys xs
  | _, _, _, _, .nil _, .nil T' => .nil T'
  | _, _, _, _, .cons _ _ _ _ x y _ _ ⟨c⟩ hs, .cons A' u' B' v' _ _ _ _ ⟨c'⟩ hs' => by
      obtain ⟨t⟩ := hasTyA_uniq C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ
        (convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c) (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c')
      exact .cons A' u' B' v' y x _ _ ⟨convA_of_tyConvA (.symm _ _ _ _ c) t⟩ (convArgsA_swap C hΓ hs hs')

/-- the bound variables of a Π-telescope's binders are typed along its weakening, pointwise. -/
theorem convArgsA_bvarsA (hE : EnvClosedA E) (hI : IotaLiftA (iotaIfaceA E)) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → {Θ₁ : LCtxA} → TelTyA E (iotaIfaceA E) n Θ₁ ds →
    ConvArgsA E (iotaIfaceA E) n (telCtxA ds ++ Θ₁) (liftNA ds.length (piTelA ds B w).1)
      (paramLocalsA ds.length) (paramLocalsA ds.length)
  | [], _, _ => .nil _
  | (D, u) :: ds, Θ₁, .cons _ _ _ _ hD tl => by
      have hlen : (telCtxA ((D, u) :: ds)).length = ds.length + 1 := by
        rw [telCtxA_length, List.length_cons]
      have hAty := hasTyA_liftN hE hI hD (telCtxA ((D, u) :: ds))
      rw [hlen, liftNA_sort, liftNA_eq] at hAty
      have hlk := lookupTypeA_telCtxA_head D u ds Θ₁
      have hpiE : liftNA (ds.length + 1) (piTelA ((D, u) :: ds) B w).1 =
          .pi (liftA 0 (ds.length + 1) D) u (liftA 1 (ds.length + 1) (piTelA ds B w).1)
            (piTelA ds B w).2 := by
        rw [liftNA_eq]; rfl
      simp only [List.length_cons]
      rw [hpiE]
      refine .cons _ _ _ _ _ _ _ _ ⟨.refl _ _ _ (.bvar _ ds.length _ u hlk hAty)⟩ ?_
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq]
      have e := telCtxA_cons_append (D, u) ds Θ₁
      have := convArgsA_bvarsA hE hI B w ds (Θ₁ := .assumption D :: Θ₁) tl
      rw [← e] at this
      exact this

/-- a function typed at a Π-telescope, weakened past its binders and applied to them, is typed at its body. -/
theorem hasTyA_appsVars (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {ds : List (ExprA × Level)} (td : TelTyA E (iotaIfaceA E) n Γ ds) {x B : ExprA} {w : Level}
    (hx : HasTyA E (iotaIfaceA E) n Γ x (piTelA ds B w).1) :
    Nonempty (HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ)
      (foldAppsA (liftNA ds.length x) (paramLocalsA ds.length)) B) := by
  have hΓ' := ctxWfA_telCtx td hΓ
  have hxl := hasTyA_liftN C.hE C.hI hx (telCtxA ds)
  rw [telCtxA_length] at hxl
  obtain ⟨c⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ' (convArgsA_bvarsA C.hE C.hI B w ds td)
    ⟨.refl _ _ _ hxl⟩ _ (applyTelA_bvars_piTelA B w ds)
  exact ⟨convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ' c⟩

/-- THE λ-WRAPPED CALL AT A FUNCTION-RECURSIVE FIELD IS TYPED at the induction hypothesis's binder, from the
    direct call typed at the inner binders. -/
theorem hasTyA_recCallFunA_frec {Γ : LCtxA} (rc : ExprA) (PRE : List ExprA) (np K : Nat) (v : ExprA)
    {ds : List (ExprA × Level)} (td : TelTyA E (iotaIfaceA E) n Γ ds) {f : Nat} {ls : List Level}
    {pl idx : List ExprA} {w : Level} {Bres : ExprA} {wM : Level}
    (hB : HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ) Bres (.sort wM))
    (hb : HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ)
      (recCallFieldA rc (PRE.map (liftNA ds.length)) np K (foldAppsA (liftNA ds.length v)
        (paramLocalsA ds.length))
        (foldAppsA (.const f ls) (pl ++ idx))) Bres) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ
      (recCallFunA rc PRE np K v (piTelA ds (foldAppsA (.const f ls) (pl ++ idx)) w).1)
      (piTelA ds Bres wM).1) := by
  have e1 : piDomListA (piTelA ds (foldAppsA (.const f ls) (pl ++ idx)) w).1 = ds := by
    rw [piDomListA_piTelA, piDomListA_of_not_pi (foldAppsA_const_ne_pi f ls _), List.append_nil]
  have e2 : piBodyA (piTelA ds (foldAppsA (.const f ls) (pl ++ idx)) w).1 = foldAppsA (.const f ls)
    (pl ++ idx) := by
    rw [piBodyA_piTelA, piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
  have hf : liftNA ds.length = liftA 0 ds.length := funext fun e => liftNA_eq e ds.length
  have key := hasTyA_recCallFunA rc PRE np K v (piTelA ds (foldAppsA (.const f ls) (pl ++ idx)) w).1
    (by rw [e1]; exact td) (Bres := Bres) (w := wM) (by rw [e1]; exact hB)
    (by rw [e1, e2, ← paramLocalsA_eq_range, ← hf]; exact hb)
  rw [e1] at key
  exact ⟨key⟩

/-- THE MINOR WALK: the ι reduct's arguments (each field, then its recursive call at a recursive
    field) walk the minor's telescope, the fields typed along the constructor's and every recursive call
    typed at its induction hypothesis (`hrec`); at a function-recursive field the λ-wrapped call, typed at
    the hypothesis's binder from the direct call at the inner binders (`hrecW`, R-NoFunRec-1 step 1
    (1c-ε2e)).

    At a δ-reached field (R-NoDeltaRec-4d-iii): the constructor telescope's domain is the surface `D`
    (the premise types the argument there), the minor's domain is the same `D`, but the recursive call
    the reduct emits sits at the domain the δ-NORMAL telescope peels — the family application at the
    field's indices. `hdd` carries the position-indexed conversion (the caller builds it from the
    view's `drecD_typed`, transported along the position's `SubstTyA`): at every `.drecD` position of
    `fsAll`, under the substitution the walk has reached, the surface domain's substitution converts to
    that family application. The walk tracks the seen prefix (`fsSeen`), the values (`fl`), and the
    substitution's `consListA`-form so the position's `SubstTyA` is discharged from the typing the walk
    consumed (`hσT`, extended at plain fields by `substTyA_cons`). -/
theorem minorWalkC (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) (rc : ExprA) (PRE : List ExprA) (np K : Nat) (f c : Nat) (ls : List Level)
    (wF wM : Level) (res : List ExprA) (mot : ExprA) (pl : List ExprA) (ni : Nat)
    (hrec : ∀ (v : ExprA) (idx : List ExprA), idx.length = ni →
      HasTyA E (iotaIfaceA E) n Γ v (foldAppsA (.const f ls) (pl ++ idx)) →
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (recCallFieldA rc PRE np K v (foldAppsA (.const f ls) (pl ++ idx)))
        (foldAppsA mot (idx ++ [v]))))
    (hrecW : ∀ (ds : List (ExprA × Level)), TelTyA E (iotaIfaceA E) n Γ ds → ∀ (v : ExprA) (idx : List ExprA),
      idx.length = ni →
      HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ) v (foldAppsA (.const f ls) (pl.map (liftNA ds.length)
        ++ idx)) →
      Nonempty (HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ)
        (recCallFieldA rc (PRE.map (liftNA ds.length)) np K v
          (foldAppsA (.const f ls) (pl.map (liftNA ds.length) ++ idx)))
        (foldAppsA (liftNA ds.length mot) (idx ++ [v]))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ) (foldAppsA (liftNA ds.length mot) (idx ++ [v]))
        (.sort wM)))
    (Θ : LCtxA) (fsAll : List FieldA) (σ₀ : SubstA)
    (hdd : ∀ (fsPre fsRest : List FieldA) (flP : List ExprA) (D : ExprA) (idx : List ExprA),
      fsAll = fsPre ++ .drecD D idx :: fsRest → flP.length = plainIdxA fsPre 0 →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA flP σ₀) (plainCtxA fsPre Θ)) →
      Nonempty (TyConvA E (iotaIfaceA E) n Γ (substA (consListA flP σ₀) D)
        (foldAppsA (.const f ls) (pl ++ idx.map (substA (consListA flP σ₀)))))) :
    (fsSeen fsR : List FieldA) → fsAll = fsSeen ++ fsR →
    (∀ idx, FieldA.drec idx ∈ fsAll.map FieldA.norm → idx.length = ni) → (∀ B uB Bs idx,
      FieldA.frec B uB Bs idx ∈ fsAll → idx.length = ni) →
    (fl : List ExprA) → (σ : SubstA) → (vs : List ExprA) →
    fl.length = fsSeen.length → σ = consListA (plainArgsA fsSeen fl) σ₀ →
    Nonempty (SubstTyA E (iotaIfaceA E) n Γ σ (plainCtxA fsSeen Θ)) →
    ConvArgsA E (iotaIfaceA E) n Γ (ctorFieldsA f ls wF pl σ fsR res).1 vs vs →
    ConvArgsA E (iotaIfaceA E) n Γ (minorFieldsA f c ls wF wM pl mot fl σ fsR res).1
      (rhsArgsA rc PRE np K vs (fsR.map FieldA.shape)
        (ctorFieldsA f ls wF pl σ (fsR.map FieldA.norm) res).1)
      (rhsArgsA rc PRE np K vs (fsR.map FieldA.shape)
        (ctorFieldsA f ls wF pl σ (fsR.map FieldA.norm) res).1)
  | _, [], _, _, _, _, _, [], _, _, _, _ => by
      simp only [List.map_nil, rhsArgsA]
      exact .nil _
  | _, .frec B uB Bs idx :: fsRest, _, _, _, fl, σ, [], _, _, _, h => by
      simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, rhsArgsA]
      exact .nil _
  | fsSeen, .frec B uB Bs idx :: fsRest, hSeen, hdl, hdlF, fl, σ, v :: vs, hfl, hσe, hσT, h => by
      simp only [ctorFieldsA] at h
      cases h with
      | cons _ _ _ _ _ _ _ _ hv hs =>
          rw [instantiate0A_ctorFieldsA_drec] at hs
          obtain ⟨cv⟩ := hv
          rw [frecDomA_eq_piTelA'] at cv
          have tv := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cv
          obtain ⟨_, htyp⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tv
          obtain ⟨⟨td⟩, hBc⟩ := telTyA_of_hasTy_piTelA _ _ _ htyp
          obtain ⟨hBs⟩ := hBc (by
            rw [substTelA_length, List.length_cons]; exact Nat.succ_pos _)
          obtain ⟨tvars⟩ := hasTyA_appsVars C hΓ td tv
          obtain ⟨⟨hcall⟩, ⟨hsort⟩⟩ := hrecW _ td _ _ (by
            rw [List.length_map]; exact hdlF B uB Bs idx (by
              rw [hSeen]; exact List.mem_append_right _ (List.mem_cons_self _ _))) tvars
          obtain ⟨hwT⟩ := hasTyA_recCallFunA_frec rc PRE np K v td hsort hcall
          simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA,
            recCallsA, List.singleton_append]
          simp only [frecDomA_eq_piTelA']
          refine .cons _ _ _ _ v v _ _ ⟨cv⟩ ?_
          rw [instantiate0A_ctorFieldsA_drec, instantiate0A_eq_substA_cons v, substA_pi, frecIHA_closed_cons]
          refine .cons _ _ _ _ _ _ _ _ ⟨.refl _ _ _ hwT⟩ ?_
          rw [instantiate0A_instantiate0A_up, substA_minorFieldsA_drec]
          exact minorWalkC C hΓ rc PRE np K f c ls wF wM res mot pl ni hrec hrecW Θ fsAll σ₀ hdd
            (fsSeen ++ [.frec B uB Bs idx]) fsRest
            (by rw [hSeen, List.append_assoc]; rfl) hdl hdlF (fl ++ [v]) σ vs
            (by simp [List.length_append, hfl])
            (by rw [plainArgsA_snoc_frec _ _ _ _ _ _ _ hfl]; exact hσe)
            (by rw [plainCtxA_append]; exact hσT) hs
  | _, [], _, _, _, _, _, _ :: _, _, _, _, h => by
      simp only [ctorFieldsA] at h
      obtain ⟨A, u, B, v, e⟩ := convArgsA_cons_pi h
      exact absurd e (foldAppsA_ne_pi _ (fun _ _ _ _ e => ExprA.noConfusion e) _ _ _ _ _)
  | _, .plain D u :: fsRest, _, _, _, fl, σ, [], _, _, _, h => by
      simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, rhsArgsA]
      exact .nil _
  | fsSeen, .plain D u :: fsRest, hSeen, hdl, hdlF, fl, σ, v :: vs, hfl, hσe, hσT, h => by
      simp only [ctorFieldsA] at h
      cases h with
      | cons _ _ _ _ _ _ _ _ hv hs =>
          rw [instantiate0A_ctorFieldsA_plain] at hs
          obtain ⟨hσp⟩ := hσT
          obtain ⟨cv⟩ := hv
          simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA,
            recCallsA, List.nil_append]
          refine .cons _ _ _ _ v v _ _ ⟨cv⟩ ?_
          rw [instantiate0A_ctorFieldsA_plain, instantiate0A_minorFieldsA_plain]
          exact minorWalkC C hΓ rc PRE np K f c ls wF wM res mot pl ni hrec hrecW Θ fsAll σ₀ hdd
            (fsSeen ++ [.plain D u]) fsRest
            (by rw [hSeen, List.append_assoc]; rfl) hdl hdlF (fl ++ [v]) (SubstA.cons v σ) vs
            (by simp [List.length_append, hfl])
            (by rw [plainArgsA_snoc_plain _ _ _ _ _ hfl, consListA_snoc, ← hσe])
            ⟨by
              rw [plainCtxA_append]
              exact substTyA_cons hσp (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cv)⟩ hs
  | _, .drec idx :: fsRest, _, _, _, fl, σ, [], _, _, _, h => by
      simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, rhsArgsA]
      exact .nil _
  | fsSeen, .drec idx :: fsRest, hSeen, hdl, hdlF, fl, σ, v :: vs, hfl, hσe, hσT, h => by
      simp only [ctorFieldsA] at h
      cases h with
      | cons _ _ _ _ _ _ _ _ hv hs =>
          rw [instantiate0A_ctorFieldsA_drec] at hs
          obtain ⟨cv⟩ := hv
          obtain ⟨trc⟩ := hrec v (idx.map (substA σ))
            (by
              rw [List.length_map]
              exact hdl idx (List.mem_map.mpr ⟨.drec idx,
                by rw [hSeen]; exact List.mem_append_right _ (List.mem_cons_self _ _), rfl⟩))
            (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cv)
          simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA,
            recCallsA, List.singleton_append]
          refine .cons _ _ _ _ v v _ _ ⟨cv⟩ ?_
          rw [instantiate0A_ctorFieldsA_drec, instantiate0A_eq_substA_cons v, substA_pi]
          refine .cons _ _ _ _ _ _ _ _ ⟨.refl _ _ _ (by rw [substA_cons_ihDom]; exact trc)⟩ ?_
          rw [instantiate0A_instantiate0A_up, substA_minorFieldsA_drec]
          exact minorWalkC C hΓ rc PRE np K f c ls wF wM res mot pl ni hrec hrecW Θ fsAll σ₀ hdd
            (fsSeen ++ [.drec idx]) fsRest
            (by rw [hSeen, List.append_assoc]; rfl) hdl hdlF (fl ++ [v]) σ vs
            (by simp [List.length_append, hfl])
            (by rw [plainArgsA_snoc_drec _ _ _ _ hfl]; exact hσe)
            (by rw [plainCtxA_append]; exact hσT) hs
  | _, .drecD _ _ :: _, _, _, _, _, _, [], _, _, _, h => by
      simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, rhsArgsA]
      exact .nil _
  | fsSeen, .drecD D idx :: fsRest, hSeen, hdl, hdlF, fl, σ, v :: vs, hfl, hσe, hσT, h => by
      simp only [ctorFieldsA] at h
      cases h with
      | cons _ _ _ _ _ _ _ _ hv hs =>
          rw [instantiate0A_ctorFieldsA_drec] at hs
          obtain ⟨hσp⟩ := hσT
          obtain ⟨cv⟩ := hv
          -- the δ-reached domain converts to the family application the normed telescope peels
          obtain ⟨tD⟩ := hdd fsSeen fsRest (plainArgsA fsSeen fl) D idx hSeen
            (by
              have hlen := plainIdxA_length fsSeen fl hfl 0
              rw [Nat.zero_add] at hlen
              exact hlen.symm)
            ⟨hσe ▸ hσp⟩
          have tD' : TyConvA E (iotaIfaceA E) n Γ (substA σ D)
              (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) := by
            rw [hσe]; exact tD
          have cvF : ConvA E (iotaIfaceA E) n Γ v v
              (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) :=
            convA_of_tyConvA cv tD'
          obtain ⟨trc⟩ := hrec v (idx.map (substA σ))
            (by
              rw [List.length_map]
              exact hdl idx (List.mem_map.mpr ⟨.drecD D idx,
                by rw [hSeen]; exact List.mem_append_right _ (List.mem_cons_self _ _), rfl⟩))
            (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cvF)
          simp only [List.map, FieldA.norm, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA,
            recCallsA, List.singleton_append]
          refine .cons _ _ _ _ v v _ _ ⟨cv⟩ ?_
          rw [instantiate0A_ctorFieldsA_drec, instantiate0A_eq_substA_cons v, substA_pi]
          refine .cons _ _ _ _ _ _ _ _ ⟨.refl _ _ _ (by rw [substA_cons_ihDom]; exact trc)⟩ ?_
          rw [instantiate0A_instantiate0A_up, substA_minorFieldsA_drec]
          exact minorWalkC C hΓ rc PRE np K f c ls wF wM res mot pl ni hrec hrecW Θ fsAll σ₀ hdd
            (fsSeen ++ [.drecD D idx]) fsRest
            (by rw [hSeen, List.append_assoc]; rfl) hdl hdlF (fl ++ [v]) σ vs
            (by simp [List.length_append, hfl])
            (by rw [plainArgsA_snoc_drecD _ _ _ _ _ hfl]; exact hσe)
            ⟨by rw [plainCtxA_append]; exact hσp⟩ hs

end Gen

/-! ## (3) helpers at the group -/

section Helpers
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

/-- a typed spine's head is typed. -/
theorem hasTyA_spine_head : (xs : List ExprA) → {h T : ExprA} →
    HasTyA E I n Γ (foldAppsA h xs) T → ∃ T', Nonempty (HasTyA E I n Γ h T')
  | [], _, T, ht => ⟨T, ⟨ht⟩⟩
  | x :: xs, h, _, ht => by
      obtain ⟨_, ⟨ht'⟩⟩ := hasTyA_spine_head xs (h := .app h x) ht
      obtain ⟨_, _, _, _, _, ⟨hf⟩, _⟩ := hasTyA_app_gen ht'
      exact ⟨_, ⟨hf⟩⟩

/-- a typed constant's level list has its member's arity. -/
theorem hasTyA_const_len : {Γ : LCtxA} → {r : Nat} → {ls : List Level} → {T : ExprA} →
    HasTyA E I n Γ (.const r ls) T → ∃ m, E.members r = some m ∧ ls.length = m.arity
  | _, _, _, _, .const _ _ _ m _ hres hlen _ _ => ⟨m, hres, hlen⟩
  | _, _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_const_len h

/-- the recursor's telescope at a full argument list reaches the motive at the indices and the
    major. -/
theorem applyTelA_recTel (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM w : Level) (cds : List MinorDataA) (qs : List ExprA) (mot : ExprA) (ms is : List ExprA)
    (x : ExprA) (hqs : qs.length = params.length) (hms : ms.length = cds.length)
    (his : is.length = idxs.length) :
    applyTelA (qs ++ ([mot] ++ ms ++ is ++ [x]))
      (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      some (foldAppsA mot (is ++ [x])) := by
  rw [recTel_blocks, applyTelA_piTelA _ _ _ _ (by
    simp only [List.length_append, List.length_singleton, minorDomsA_length, liftDomsA_length, hms, his, hqs,
      List.length_cons, List.length_nil]; omega) SubstA.id]
  congr 1
  rw [consListA_append, ← hms, ← his]
  exact substA_recBodyA mot x ms is

/-- the family over its locals, at the parameters and the indices. -/
theorem substA_famLocalsA (f : Nat) (ls : List Level) (qs is : List ExprA) :
    substA (consListA is (consListA qs SubstA.id)) (famLocalsA f ls qs.length is.length) =
      foldAppsA (.const f ls) (qs ++ is) := by
  have hfun : (substA (consListA is (consListA qs SubstA.id)) ∘ liftA 0 is.length) =
      substA (consListA qs SubstA.id) := funext fun e => substA_consListA_liftA is _ e
  rw [famLocalsA, substA_foldAppsA, substA_const, List.map_append, paramLocalsA_consListA, List.map_map, hfun,
    paramLocalsA_consListA]

/-- the family's type, instantiated, as one telescope over the parameters and the indices. -/
theorem famTy_tel {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level) :
    instantiateLevelsA ls fm.mtypeA = substA SubstA.id (piTelA (instDomsA ls fv.params ++ instDomsA ls fv.indices)
      (.sort (instLevel ls fv.sort)) (instLevel ls (.succ fv.sort))).1 := by
  have h := congrArg Prod.fst
    (instantiateLevelsA_piTelA ls (.sort fv.sort) (.succ fv.sort) (fv.params ++ fv.indices))
  simp only at h
  rw [substA_id, ← instDomsA_append, fv.stored, h]
  rfl

/-- pointwise lists along the family's type split at the parameters. -/
theorem famArgs_split {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level)
    {qs qs' idx idx' : List ExprA}
    (h : ConvArgsA E I n Γ (instantiateLevelsA ls fm.mtypeA) (qs ++ idx) (qs' ++ idx'))
    (hq : qs.length = fv.params.length) (hq' : qs'.length = fv.params.length) :
    (∀ (B : ExprA) (w : Level), ConvArgsA E I n Γ (piTelA (instDomsA ls fv.params) B w).1 qs qs') ∧
      ConvArgsA E I n Γ (substA (consListA qs SubstA.id) (piTelA (instDomsA ls fv.indices)
        (.sort (instLevel ls fv.sort)) (instLevel ls (.succ fv.sort))).1) idx idx' := by
  rw [famTy_tel fv] at h
  obtain ⟨h1, h2⟩ := convArgsA_piTelA_append_inv _ _ _ _ _ h (by rw [instDomsA_length]; exact hq)
    (by rw [instDomsA_length]; exact hq')
  refine ⟨fun B w => ?_, h2⟩
  have := h1 B w
  rwa [substA_id] at this

/-- pointwise lists along the family's type join from the parameters and the indices. -/
theorem famArgs_join {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level)
    {qs qs' idx idx' : List ExprA} {B : ExprA} {w : Level}
    (h1 : ConvArgsA E I n Γ (piTelA (instDomsA ls fv.params) (.sort .zero) .zero).1 qs qs')
    (hq : qs.length = fv.params.length)
    (h2 : ConvArgsA E I n Γ (substA (consListA qs SubstA.id) (piTelA (instDomsA ls fv.indices) B w).1) idx idx')
    (hi : idx.length = fv.indices.length) :
    ConvArgsA E I n Γ (instantiateLevelsA ls fm.mtypeA) (qs ++ idx) (qs' ++ idx') := by
  rw [famTy_tel fv]
  exact convArgsA_piTelA_append _ (.sort .zero) _ .zero _ _ _ (by rw [substA_id]; exact h1)
    (by rw [instDomsA_length]; exact hq)
    (convArgsA_piTelA_body _ _ _ _ _ _ h2 (by rw [instDomsA_length]; exact hi))

/-- the motive's type at the indices and the major reaches its sort. -/
theorem applyTelA_motTy (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM : Level)
    (σ : SubstA) (is : List ExprA) (x : ExprA) (his : is.length = idxs.length) :
    applyTelA (is ++ [x]) (substA σ (motTyA f ls params idxs wF wM).1) = some (.sort wM) := by
  rw [applyTelA_append, motTyA, applyTelA_piTelA _ _ idxs is his σ]
  rfl

/-- five-part lists with matching lengths are equal part by part. -/
theorem list5_inj {qs qs' ms ms' is is' : List ExprA} {mot mot' x x' : ExprA}
    (h : qs ++ ([mot] ++ ms ++ is ++ [x]) = qs' ++ ([mot'] ++ ms' ++ is' ++ [x']))
    (hq : qs.length = qs'.length) (hm : ms.length = ms'.length) (hi : is.length = is'.length) :
    qs = qs' ∧ mot = mot' ∧ ms = ms' ∧ is = is' ∧ x = x' := by
  obtain ⟨rfl, h2⟩ := List.append_inj h hq
  simp only [List.singleton_append, List.cons_append, List.cons.injEq] at h2
  obtain ⟨rfl, h3⟩ := h2
  obtain ⟨h4, h5⟩ := List.append_inj' (h3 : (ms ++ is) ++ [x] = (ms' ++ is') ++ [x']) rfl
  obtain ⟨rfl, rfl⟩ := List.append_inj h4 hm
  simp only [List.cons.injEq, and_true] at h5
  exact ⟨rfl, rfl, rfl, rfl, h5.1⟩

/-- four-part lists with matching lengths are equal part by part. -/
theorem list4_inj {qs qs' ms ms' is is' : List ExprA} {mot mot' : ExprA}
    (h : qs ++ [mot] ++ ms ++ is = qs' ++ [mot'] ++ ms' ++ is')
    (hq : qs.length = qs'.length) (hm : ms.length = ms'.length) :
    qs = qs' ∧ mot = mot' ∧ ms = ms' ∧ is = is' := by
  have h' : qs ++ ([mot] ++ ms ++ is ++ [(.sort .zero : ExprA)]) =
      qs' ++ ([mot'] ++ ms' ++ is' ++ [(.sort .zero : ExprA)]) := by
    have h'' := congrArg (· ++ [(.sort .zero : ExprA)]) h
    simp only [List.append_assoc] at h'' ⊢
    exact h''
  have hi : is.length = is'.length := by
    have := congrArg List.length h
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at this
    omega
  obtain ⟨h1, h2, h3, h4, -⟩ := list5_inj h' hq hm hi
  exact ⟨h1, h2, h3, h4⟩

end Helpers

/-! ## (4) ι SUBJECT REDUCTION -/

section SR
variable {E : ResolvedEnvA} {n : Nat}

/-- ROW 3 AT A FAMILY APPLICATION'S OWN SORT: two family applications of one family, the left typed
    canonically at the family's sort, type-convertible, are pointwise convertible along its type. -/
theorem famApp_conv_args (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {f : Nat} {fm : CheckedMemberA} (fv : FamViewA fm) (hmf : E.members f = some fm)
    (hcls : fm.mclass = .inductiveM) {ls ls' : List Level} {xs xs' : List ExprA}
    (hF : HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const f ls) xs) (.sort (instLevel ls fv.sort)))
    (t : TyConvA E (iotaIfaceA E) n Γ (foldAppsA (.const f ls) xs) (foldAppsA (.const f ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA ls fm.mtypeA) xs xs' := by
  obtain ⟨hW⟩ := C.wf
  have c := tyConvA_collapse C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ t hF
  cases hz : isZero (instLevel ls fv.sort) with
  | false => exact famAppConvInjA_rec hW posValA_one C.small C.propElim hΓ hmf hcls fv.piBody hz c
  | true => exact famAppConvInjA_prop_rec hW posValA_one C.small C.propElim hΓ hmf hcls hz c

/-- a member's constant at bounded levels of its arity, typed at its instantiated type. -/
theorem hasTyA_const_inst (C : AnnEnvA E) {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) {ls : List Level} (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA)) := by
  obtain ⟨u, ⟨hT⟩⟩ := hasTyA_memberTy_inst C hres hlen hwf Γ
  exact ⟨.const Γ r ls m u hres hlen hwf hT⟩

/-- ι subject reduction in its typing form: a ι step's reduct keeps the redex's type. -/
def IotaSRTyA (E : ResolvedEnvA) (n : Nat) : Prop :=
  ∀ {Γ : LCtxA} {lhs rhs T : ExprA}, CtxWfA E (iotaIfaceA E) n Γ → iotaFnA E lhs = some rhs →
    HasTyA E (iotaIfaceA E) n Γ lhs T → Nonempty (HasTyA E (iotaIfaceA E) n Γ rhs T)

/-- THE RECURSOR REDEX'S ARGUMENTS AND ITS RECURSIVE CALLS (R-NoFunRec-1 step 1 (1c-ε2e)): a typed recursor
    spine at a major splits into the parameters, the motive, the minors, the indices, each typed along the
    recursor's telescope, and every recursive call at a major of the family at the parameters and any
    indices is typed at the motive there, the motive instance at its sort. -/
theorem recRedexC (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {E₀ : ResolvedEnvA}
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)} (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs)
    (hmr : E.members (f + 1 + cs.length) = some rec.member) (hmf : E.members f = some fm)
    {ls lsF : List Level} (hlsF : ls.take fm.arity = lsF) (hlenF : lsF.length = fm.arity)
    (hlslen : ls.length = rec.member.arity) {pre : List ExprA} {major T : ExprA}
    (hplen : pre.length + 1 = piCountA rec.member.mtypeA)
    (ht : HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const (f + 1 + cs.length) ls) (pre ++ [major])) T) :
    ∃ (qs : List ExprA) (mot : ExprA) (ms is : List ExprA),
      qs ++ [mot] ++ ms ++ is = pre ∧ levelsBounded n ls = true ∧
      (instantiateLevelsA ls rec.member.mtypeA =
      (piTelA (recDomsA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
          (instLevel ls (rec.elim.motiveLevel fm.arity))
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)))
        (recBodyA (instDomsA lsF fv.indices).length ((cs.reverse.map GroupCtorA.minorData).map
          (MinorDataA.inst lsF)).length) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) ∧
      qs.length = (instDomsA lsF fv.params).length ∧
      ms.length = ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)).length ∧
      is.length = (instDomsA lsF fv.indices).length ∧
      (∀ (B : ExprA) (v : Level),
        ConvArgsA E (iotaIfaceA E) n Γ (piTelA (instDomsA lsF fv.params) B v).1 qs qs) ∧
      Nonempty (ConvA E (iotaIfaceA E) n Γ mot mot (substA (consListA qs SubstA.id)
        (motTyA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
          (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) ∧
      (∀ (i : Nat) (hi : i < ms.length)
        (hc : i < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)).length),
        Nonempty (ConvA E (iotaIfaceA E) n Γ ms[i] ms[i] (substA (SubstA.cons mot (consListA qs SubstA.id))
          (minorTyA f lsF (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
            (instDomsA lsF fv.params).length
            (((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF))[i]'hc)).1))) ∧
      (∀ (B : ExprA) (v : Level),
        ConvArgsA E (iotaIfaceA E) n Γ (substA (consListA qs SubstA.id) (piTelA (instDomsA lsF fv.indices)
          B v).1)
          is is) ∧
      Nonempty (ConvA E (iotaIfaceA E) n Γ major major (foldAppsA (.const f lsF) (qs ++ is))) ∧
      Nonempty (TyConvA E (iotaIfaceA E) n Γ (foldAppsA mot (is ++ [major])) T) ∧
      (∀ (v : ExprA) (idx : List ExprA), idx.length = fv.indices.length →
        HasTyA E (iotaIfaceA E) n Γ v (foldAppsA (.const f lsF) (qs ++ idx)) →
        Nonempty (HasTyA E (iotaIfaceA E) n Γ
          (recCallFieldA (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length v
            (foldAppsA (.const f lsF) (qs ++ idx))) (foldAppsA mot (idx ++ [v]))) ∧
        Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA mot (idx ++ [v]))
          (.sort (instLevel ls (rec.elim.motiveLevel fm.arity))))) := by
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  have hrar : rec.member.arity = fm.arity + rec.elim.extra := rec.harity
  have hrp : piCountA rec.member.mtypeA =
      fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [hst, piCountA_recTypeA, List.length_map, List.length_reverse]
  have htakeL := hlenF
  have hwfls : levelsBounded n ls = true := hasTyA_foldAppsA_const_bounded ht
  have hwfF : levelsBounded n lsF = true := by rw [← hlsF]; exact levelsBounded_take ls _ hwfls
  obtain ⟨hHead⟩ := hasTyA_const_inst C (Γ := Γ) hmr hlslen hwfls
  have hRty : instantiateLevelsA ls rec.member.mtypeA =
      (piTelA (recDomsA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
          (instLevel ls (rec.elim.motiveLevel fm.arity))
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)))
        (recBodyA (instDomsA lsF fv.indices).length ((cs.reverse.map GroupCtorA.minorData).map
          (MinorDataA.inst lsF)).length) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 := by
    simp only [instDomsA_length, List.length_map, List.length_reverse]
    rw [rec.stored, ← hlsF]
    exact instantiateLevelsA_groupRecTypeA cs rec.elim ls (by omega) ((C.hEL f fm hmf).1)
  rw [hRty] at hHead
  have hlenR : (pre ++ [major]).length =
      (recDomsA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
        (instLevel ls (rec.elim.motiveLevel fm.arity))
        ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF))).length := by
    simp only [recDomsA, List.length_append, List.length_singleton, minorDomsA_length, liftDomsA_length,
      instDomsA_length, List.length_map, List.length_reverse]
    rw [hrp] at hplen; omega
  have hU := applyTelA_piTelA (recBodyA (instDomsA lsF fv.indices).length
    ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)).length)
    (instLevel ls (rec.elim.motiveLevel fm.arity)) _ (pre ++ [major]) hlenR SubstA.id
  rw [substA_id] at hU
  obtain ⟨hargs, ⟨tU⟩⟩ := spine_gen C hΓ hHead (pre ++ [major]) hU ht
  -- (c) the recursor's arguments split
  obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', e1, e2, hqs, hqs', hms, hms', his, his', hpar, ⟨cmot⟩,
      hminC, hidxC, ⟨cmaj⟩, happR⟩ :=
    recArgsSplitC f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
      (instLevel ls (rec.elim.motiveLevel fm.arity)) (instLevel ls (rec.elim.motiveLevel fm.arity))
      ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)) hargs
      (by rw [hlenR]; simp only [recDomsA, List.length_append, List.length_singleton, minorDomsA_length,
            liftDomsA_length]; omega)
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := list5_inj (e1.symm.trans e2) (hqs.trans hqs'.symm) (hms.trans hms'.symm)
    (his.trans his'.symm)
  have e1' : pre ++ [major] = (qs ++ ([mot] ++ ms ++ is)) ++ [x] := by
    rw [e1]; simp only [List.append_assoc]
  obtain ⟨hpreE, hxE⟩ := List.append_inj' e1' rfl
  have hxE' : major = x := (List.cons.inj hxE).1
  subst hxE'
  rw [hU] at happR
  injection happR with hU0
  rw [hU0] at tU
  have hqsL : qs.length = fv.params.length := by rw [hqs, instDomsA_length]
  have hisL : is.length = fv.indices.length := by rw [his, instDomsA_length]
  have hmsL : ms.length = cs.length := by
    rw [hms, List.length_map, List.length_map, List.length_reverse]
  have hpre2 : qs ++ [mot] ++ ms ++ is = pre := by
    rw [hpreE]; simp only [List.append_assoc]
  have hlenF' := hlenF
  obtain ⟨hFH⟩ := hasTyA_const_inst C (Γ := Γ) hmf hlenF hwfF
  have hrecT : ∀ (v : ExprA) (idx : List ExprA), idx.length = fv.indices.length →
      HasTyA E (iotaIfaceA E) n Γ v (foldAppsA (.const f lsF) (qs ++ idx)) →
      Nonempty (HasTyA E (iotaIfaceA E) n Γ
        (recCallFieldA (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length v
          (foldAppsA (.const f lsF) (qs ++ idx))) (foldAppsA mot (idx ++ [v]))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA mot (idx ++ [v]))
        (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))) := by
    intro v idx hidxL hv
    obtain ⟨_, hAs⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ hv
    obtain ⟨hAargs, _⟩ := spine_gen C hΓ hFH (qs ++ idx)
      (fv.applyTel_full lsF (qs ++ idx) (by
        rw [instDomsA_length, List.length_append, List.length_append, hqsL, hidxL])) hAs
    obtain ⟨_, hIdx⟩ := famArgs_split fv lsF hAargs hqsL hqsL
    have hJ := recArgsJoinC (Γ := Γ) (E := E) (I := iotaIfaceA E) (n := n) f lsF (instDomsA lsF fv.params)
      (instDomsA lsF fv.indices) (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
      (instLevel ls (rec.elim.motiveLevel fm.arity))
      ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)) (x := v) (x' := v)
      hqs hms hms (by rw [instDomsA_length]; exact hidxL) (hpar (.sort .zero) .zero) ⟨cmot⟩ hminC
      (convArgsA_piTelA_body _ _ _ _ _ _ hIdx (by rw [instDomsA_length]; exact hidxL))
      ⟨.refl Γ v _ hv⟩
    obtain ⟨cR⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hJ ⟨.refl Γ _ _ hHead⟩ _
      (applyTelA_recTel f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
        (instLevel ls (rec.elim.motiveLevel fm.arity)) (instLevel ls (rec.elim.motiveLevel fm.arity))
        ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)) qs mot ms idx v hqs hms
        (by rw [instDomsA_length]; exact hidxL))
    rw [← hpre2, recCallFieldA_eq (f + 1 + cs.length) ls (qs ++ [mot] ++ ms) is fv.params.length cs.length
      (by simp only [List.length_append, List.length_singleton, hqsL, hmsL]) v f lsF qs idx hqsL]
    have e : qs ++ [mot] ++ ms ++ idx ++ [v] = qs ++ ([mot] ++ ms ++ idx ++ [v]) := by
      simp only [List.append_assoc]
    rw [e]
    have hidxL' : idx.length = (instDomsA lsF fv.indices).length := by rw [instDomsA_length]; exact hidxL
    have hMA : ConvArgsA E (iotaIfaceA E) n Γ
        (substA (consListA qs SubstA.id) (motTyA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices)
          (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)
        (idx ++ [v]) (idx ++ [v]) := by
      rw [motTyA]
      refine convArgsA_append (convArgsA_piTelA_body _ _ _ _ _ _ hIdx hidxL')
        (applyTelA_piTelA _ _ _ idx hidxL' _) ?_
      simp only [substA_pi]
      have hd := substA_famLocalsA f lsF qs idx
      rw [hqsL, hidxL, ← instDomsA_length lsF fv.params, ← instDomsA_length lsF fv.indices] at hd
      rw [hd]
      exact .cons _ _ _ _ _ _ [] [] ⟨.refl Γ v _ hv⟩ (.nil _)
    obtain ⟨cMS⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hMA ⟨cmot⟩ _
      (applyTelA_motTy f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
        (instLevel ls (rec.elim.motiveLevel fm.arity)) (consListA qs SubstA.id) idx v hidxL')
    exact ⟨⟨convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cR⟩, ⟨convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cMS⟩⟩
  exact ⟨qs, mot, ms, is, hpre2, hwfls, hRty, hqs, hms, his, hpar, ⟨cmot⟩, fun i hi hc => hminC i hi hi hc,
    hidxC, ⟨cmaj⟩, ⟨tU⟩, hrecT⟩

/-- ι SUBJECT REDUCTION ON THE COPY, WITH THE CARRIED CONVERSION: under every environment the copy admits,
    a ι step's reduct keeps the redex's type; and at a struct group (W-1 (e-2)), where the head step is the
    struct arm's, ι's contractum (the minor at the constructor's fields) converts to the arm's reduct (the
    minor at the major's projections) at the redex's type. The fields and the projections are proofs along
    the same telescope, so irrelevance relates them (`structSideTyA` at the recursor's levels and
    parameters). -/
theorem iotaSRA_core (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {lhs rhs T : ExprA}
    (h : iotaFnA E lhs = some rhs) (ht : HasTyA E (iotaIfaceA E) n Γ lhs T) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ rhs T) ∧
      (iotaAtStructA E lhs = true → ∃ f a e, lhs = .app f a ∧ recAtMajorA E f = true ∧
        structArmA E f a = some e ∧ Nonempty (ConvA E (iotaIfaceA E) n Γ rhs e T)) := by
  obtain ⟨hW⟩ := C.wf
  -- (a) the redex: a recursor spine of a group at a constructor of the group
  obtain ⟨⟨recRef, ls, pre, major⟩, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  have hAS := iotaAtStructA_of_layers hs hc hg
  have hsp := recSpineA_some hs
  simp only at hsp hc hg
  obtain ⟨hrm, hrk, _, _, _, _, _, hlt1, hlt2, _, _, _, _⟩ := iotaGroupA_some hg
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, hfreshR⟩ :=
    envWfA_recGroup hW _ _ hrm hrk
  subst hrr
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  have hfamf : g.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ := iotaGroupA_lastDom hg
    rw [← hrec, hst, piDomsA_recTypeA_getLast] at hD
    injection hD with hD
    rw [← hD, appsSpineA_majorDom] at hhead
    injection hhead with h1 _
    exact h1.symm
  rw [hfamf] at hlt1
  have hj : c - f - 1 < cs.length := by omega
  obtain ⟨gc, hgcj⟩ : ∃ gc, cs.reverse[c - f - 1]? = some gc :=
    ⟨cs.reverse[c - f - 1]'(by rw [List.length_reverse]; exact hj), List.getElem?_eq_getElem _⟩
  obtain ⟨href, _⟩ := ref_of_layoutA hlay hgcj
  have hcref : c = gc.ref := by omega
  subst hcref
  have hg' := iotaGroupA_groupRecA hfresh hlay hcls hpre hgcj
  rw [hg'] at hg
  injection hg with hg
  subst hg
  obtain ⟨hmr, hmf, hmc⟩ := members_groupRecA hfresh hlay hpre
  have hmg := hmc hgcj
  obtain ⟨shapes, minor, ctorAfter, hshapes, hmin, happ, _, he'⟩ := iotaReductA_inv hr
  obtain ⟨_, _, _, hplen, hlslen, hmlen, har⟩ := iotaReductA_some hr
  simp only at hshapes hmin happ he' hplen hlslen hmlen har
  rw [gc.normA_getD] at hshapes happ hmlen
  have hnpF : fv.params.length = fm.nparamsA := fv.nparams
  have hgar : gc.member.arity = fm.arity := gc.harity
  have hrar : rec.member.arity = fm.arity + rec.elim.extra := rec.harity
  have hcp : piCountA gc.member.mtypeA = fv.params.length + gc.view.fields.length := by
    rw [gc.view.stored, piCountA_ctorTypeA, gc.view.mirrors_length, hnpF]
  have hrp : piCountA rec.member.mtypeA =
      fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [hst, piCountA_recTypeA, List.length_map, List.length_reverse]
  have hkv : shapes = gc.view.fields.map FieldA.shape := by
    have := gc.view.shapes hfresh.base
    rw [← hnpF, hshapes] at this
    exact Option.some.inj this
  have htakeL : (ls.take fm.arity).length = fm.arity := by
    rw [List.length_take]; rw [hgar] at har; omega
  have htakeP : (pre.take fv.params.length).length = fm.nparamsA := by
    rw [List.length_take, ← hnpF]; rw [hrp] at hplen; omega
  have happV := gc.applyTel_params (ls.take fm.arity) htakeL (pre.take fv.params.length) htakeP
  rw [gc.normA_getD] at happV
  rw [hgar, happV] at happ
  injection happ with hca
  obtain ⟨lsC, hmh⟩ := spineHeadRefA_some hc
  have hmajE : major = foldAppsA (.const gc.ref lsC) (appsSpineA major).2 := by
    conv => lhs; rw [← foldAppsA_appsSpineA major]
    rw [hmh]
  have he : lhs = foldAppsA (.const (f + 1 + cs.length) ls) (pre ++ [major]) := by
    conv => lhs; rw [← foldAppsA_appsSpineA lhs]
    rw [hsp]
  have hmlen' : (appsSpineA major).2.length = fv.params.length + gc.view.fields.length := by
    rw [hmlen, piCountA_ctorTypeA, gc.view.mirrors_length, List.length_map, hnpF]
  -- notation
  generalize hlsF : ls.take fm.arity = lsF at htakeL hca happV
  generalize hyargs : (appsSpineA major).2 = yargs at hmajE hmlen' he'
  have hpsL : (yargs.take fv.params.length).length = fv.params.length := by
    rw [List.length_take]; omega
  have hfsL : (yargs.drop fv.params.length).length = gc.view.fields.length := by
    rw [List.length_drop]; omega
  have hyargs' : yargs = yargs.take fv.params.length ++ yargs.drop fv.params.length :=
    (List.take_append_drop _ _).symm
  generalize hps : yargs.take fv.params.length = ps at hpsL hyargs'
  generalize hfs : yargs.drop fv.params.length = fs at hfsL hyargs' he'
  subst hyargs'
  rw [he] at ht
  -- (b) the recursor's head and its telescope
  obtain ⟨qs, mot, ms, is, hpre2, hwfls, hRty, hqs, hms, his, hpar, ⟨cmot⟩, hminC, hidxC, ⟨cmaj⟩, ⟨tU⟩,
    hrecT⟩ :=
    recRedexC C hΓ rec hmr hmf hlsF htakeL hlslen hplen ht
  have hwfF : levelsBounded n lsF = true := by rw [← hlsF]; exact levelsBounded_take ls _ hwfls
  have hqsL : qs.length = fv.params.length := by rw [hqs, instDomsA_length]
  have hisL : is.length = fv.indices.length := by rw [his, instDomsA_length]
  have hmsL : ms.length = cs.length := by
    rw [hms, List.length_map, List.length_map, List.length_reverse]
  have hpreE : pre = qs ++ ([mot] ++ ms ++ is) := by rw [← hpre2]; simp only [List.append_assoc]
  have hpreQ : pre.take fv.params.length = qs := by
    rw [hpreE]; exact List.take_left' hqsL
  rw [hpreQ] at hca happV htakeP
  -- the major, typed at the family application at the parameters and the indices
  have tMaj := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cmaj
  rw [hmajE] at tMaj cmaj tU
  -- (d) the major's constructor and its telescope at the major's levels
  have hwfC : levelsBounded n lsC = true := hasTyA_foldAppsA_const_bounded tMaj
  obtain ⟨_, ⟨tcC⟩⟩ := hasTyA_spine_head _ tMaj
  obtain ⟨mC, hmC, hlenC0⟩ := hasTyA_const_len tcC
  rw [hmg] at hmC
  injection hmC with hmC
  subst hmC
  have hlenC : lsC.length = fm.arity := hlenC0.trans hgar
  obtain ⟨hCH⟩ := hasTyA_const_inst C (Γ := Γ) hmg hlenC0 hwfC
  have hpsN : ps.length = fm.nparamsA := hpsL.trans hnpF
  have happC := gc.view.applyTel_params lsC hlenC ps hpsN
  have hpre0 := applyTelA_groupCtor_prefix gc lsC (fsPre := gc.view.fields) (fsRest := [])
    (List.append_nil _).symm hfsL ps (consListA ps SubstA.id)
  simp only [List.map_nil, ctorFieldsA] at hpre0
  have hUc : applyTelA (ps ++ fs) (instantiateLevelsA lsC gc.member.mtypeA) =
      some (foldAppsA (.const f lsC) (ps ++ (gc.view.res.map (instantiateLevelsA lsC)).map
        (substA (consListA (plainArgsA gc.view.fields fs) (consListA ps SubstA.id))))) := by
    rw [applyTelA_append, happC]; exact hpre0
  obtain ⟨hCargs, ⟨tUcF₂⟩⟩ := spine_gen C hΓ hCH (ps ++ fs) hUc tMaj
  obtain ⟨Tps, hTps, hPS, hFS⟩ := convArgsA_append_inv rfl hCargs
  rw [happC] at hTps
  injection hTps with hTps
  subst hTps
  -- (e) the family application at the recursor's parameters and the redex's indices, typed at its sort
  have hlenF : lsF.length = fm.arity := htakeL
  obtain ⟨hFH⟩ := hasTyA_const_inst C (Γ := Γ) hmf hlenF hwfF
  have hF₂args := famArgs_join fv lsF (hpar (.sort .zero) .zero) hqsL (hidxC (.sort .zero) .zero) hisL
  obtain ⟨cF₂⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hF₂args ⟨.refl Γ _ _ hFH⟩ _
    (fv.applyTel_full lsF (qs ++ is) (by
      rw [instDomsA_length, List.length_append, List.length_append, hqsL, hisL]))
  have hF₂ := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cF₂
  -- ROW 3: the constructor's parameters are the recursor's
  obtain ⟨hlFC, _, hQP⟩ := famApp_conv_args C hΓ fv hmf hcls hF₂ tUcF₂.symm
  obtain ⟨hQPp, _⟩ := famArgs_split fv lsF hQP hqsL hpsL
  -- (f) the constructor at the recursor's levels and parameters converts with the major
  have hPQ := convArgsA_swap C hΓ (hQPp (.sort .zero) .zero) hPS
  obtain ⟨hcF⟩ := hasTyA_const_inst C (Γ := Γ) hmg (hlenF.trans hgar.symm) hwfF
  obtain ⟨_, ⟨cLev⟩⟩ := convA_memberTy_levels C hmg (hlenF.trans hgar.symm) hlenC0 hwfF hwfC hlFC Γ
  have hcF' := hasTyA_of_tyConvA hcF (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cLev)
  have cHead : ConvA E (iotaIfaceA E) n Γ (.const gc.ref lsC) (.const gc.ref lsF)
      (instantiateLevelsA lsC gc.member.mtypeA) :=
    .consts Γ gc.ref lsC lsF gc.member hmg hlenC0 hwfC hwfF (eqNListA_symm hlFC) hcF'
  obtain ⟨cY⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ (convArgsA_append hPQ happC hFS) ⟨cHead⟩ _ hUc
  -- (g) the rebuilt constructor's canonical type, and the fields along the recursor-side telescope
  have hlenFC : lsF.length = gc.member.arity := hlenF.trans hgar.symm
  have happF := gc.view.applyTel_params lsF hlenF qs (hqsL.trans hnpF)
  have hpreF := applyTelA_groupCtor_prefix gc lsF (fsPre := gc.view.fields) (fsRest := [])
    (List.append_nil _).symm hfsL qs (consListA qs SubstA.id)
  simp only [List.map_nil, ctorFieldsA] at hpreF
  have hUF : applyTelA (qs ++ fs) (instantiateLevelsA lsF gc.member.mtypeA) =
      some (foldAppsA (.const f lsF) (qs ++ (gc.view.res.map (instantiateLevelsA lsF)).map
        (substA (consListA (plainArgsA gc.view.fields fs) (consListA qs SubstA.id))))) := by
    rw [applyTelA_append, happF]; exact hpreF
  obtain ⟨hFargs, ⟨tF₁Uc⟩⟩ := spine_gen C hΓ hcF (qs ++ fs) hUF (convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cY)
  obtain ⟨TqF, hTqF, hQF, hFF⟩ := convArgsA_append_inv rfl hFargs
  rw [happF] at hTqF
  injection hTqF with hTqF
  subst hTqF
  -- (h) the minor at its type, and the reduct's arguments along its telescope
  obtain ⟨_, hjL⟩ := ref_of_layoutA hlay hgcj
  have hjm : gc.ref - f - 1 < ms.length := by rw [hmsL]; exact hjL
  have hjc : gc.ref - f - 1 < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF)).length := by
    simp only [List.length_map, List.length_reverse]; exact hjL
  obtain ⟨_, hjg⟩ := List.getElem?_eq_some_iff.mp hgcj
  have hMT : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst lsF))[gc.ref - f - 1]'hjc =
      (gc.ref, gc.view.fields.map (FieldA.instLevels lsF), gc.view.res.map (instantiateLevelsA lsF)) := by
    simp only [List.getElem_map, hjg]; rfl
  have hσ : (fun i => substA (SubstA.cons mot (consListA qs SubstA.id)) (SubstA.id.shift1 i)) =
      consListA qs SubstA.id := by
    funext i
    show substA (SubstA.cons mot (consListA qs SubstA.id)) (liftA 0 1 (SubstA.id i)) = consListA qs SubstA.id i
    rw [substA_cons_liftA]
    rfl
  have hpl : ((paramLocalsA (instDomsA lsF fv.params).length).map (liftA 0 1)).map
      (substA (SubstA.cons mot (consListA qs SubstA.id))) = qs := by
    rw [map_substA_cons_liftA, ← hqs, paramLocalsA_consListA]
  obtain ⟨cmin⟩ := hminC (gc.ref - f - 1) hjm hjc
  rw [hMT, minorTyA, substA_minorFieldsA, hpl, hσ] at cmin
  have hminE : minor = ms[gc.ref - f - 1]'hjm := by
    have h1 := getElem?_pfx_minorA (qs := qs) (mot := mot) (is := is) hjm
    rw [hqsL, hpre2, hmin] at h1
    exact Option.some.inj h1
  -- every recursive call typed at its induction hypothesis: the bound reads the NORMALIZED
  -- field list, so a `.drec` may come from a `.drec` or a `.drecD` in the raw fields
  -- (R-NoDeltaRec-4d-iii); `instLevels`/`norm` commute (`map_instLevels_norm`).
  have hdl : ∀ idx, FieldA.drec idx ∈
      (gc.view.fields.map (FieldA.instLevels lsF)).map FieldA.norm →
      idx.length = fv.indices.length := by
    intro idx hm
    rw [map_instLevels_norm] at hm
    obtain ⟨fld, hfld, hfe⟩ := List.mem_map.mp hm
    cases fld with
    | plain _ _ | frec _ _ _ _ | drecD _ _ => cases hfe
    | drec idx₀ =>
        simp only [FieldA.instLevels, FieldA.drec.injEq] at hfe
        subst hfe
        rw [List.length_map]
        exact gc.view.drec_length_norm idx₀ hfld
  have hdlF : ∀ B uB Bs idx, FieldA.frec B uB Bs idx ∈ gc.view.fields.map (FieldA.instLevels lsF) →
      idx.length = fv.indices.length := by
    intro B uB Bs idx hm
    obtain ⟨fld, hfld, hfe⟩ := List.mem_map.mp hm
    cases fld with
    | plain _ _ | drec _ | drecD _ _ => cases hfe
    | frec B₀ uB₀ Bs₀ idx₀ =>
        simp only [FieldA.instLevels, FieldA.frec.injEq] at hfe
        obtain ⟨-, -, -, rfl⟩ := hfe
        rw [List.length_map]
        exact gc.view.frec_length B₀ uB₀ Bs₀ idx₀ hfld
  have hrecW : ∀ (ds : List (ExprA × Level)), TelTyA E (iotaIfaceA E) n Γ ds → ∀ (v : ExprA)
    (idx : List ExprA),
      idx.length = fv.indices.length →
      HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ) v
        (foldAppsA (.const f lsF) (qs.map (liftNA ds.length) ++ idx)) →
      Nonempty (HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ)
        (recCallFieldA (.const (f + 1 + cs.length) ls) (pre.map (liftNA ds.length))
          fv.params.length cs.length v
          (foldAppsA (.const f lsF) (qs.map (liftNA ds.length) ++ idx)))
        (foldAppsA (liftNA ds.length mot) (idx ++ [v]))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n (telCtxA ds ++ Γ) (foldAppsA (liftNA ds.length mot) (idx ++ [v]))
        (.sort (instLevel ls (rec.elim.motiveLevel fm.arity))) ) := by
    intro ds td v idx hl hv
    have hΓ' := ctxWfA_telCtx td hΓ
    have htW := hasTyA_liftN C.hE C.hI ht (telCtxA ds)
    rw [telCtxA_length, liftNA_foldAppsA, liftNA_const, List.map_append, List.map_cons, List.map_nil] at htW
    obtain ⟨qs', mot', ms', is', hpre2', -, -, hqs', hms', -, -, -, -, -, -, -, hrecT'⟩ :=
      recRedexC C hΓ' rec hmr hmf hlsF htakeL hlslen (pre := pre.map (liftNA ds.length))
        (major := liftNA ds.length major) (by rw [List.length_map]; exact hplen) htW
    rw [← hpre2] at hpre2'
    simp only [List.map_append, List.map_cons, List.map_nil] at hpre2'
    obtain ⟨rfl, rfl, -, -⟩ := list4_inj hpre2' (by rw [List.length_map]; exact hqs'.trans hqs.symm)
      (by rw [List.length_map]; exact hms'.trans hms.symm)
    exact hrecT' v idx hl hv
  have hFF' : ConvArgsA E (iotaIfaceA E) n Γ
      (ctorFieldsA f lsF (instLevel lsF fv.sort) qs (consListA qs SubstA.id)
        (gc.view.fields.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 fs fs := hFF
  -- the walk's base context: the family's parameter telescope at the redex's levels; the
  -- substitution's typing is `hpar` walked along it (R-NoDeltaRec-4d-iii)
  obtain ⟨hσq⟩ : Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA qs SubstA.id)
      (instCtxA lsF (telCtxA fv.params))) := by
    have h0 := substTyA_of_convArgsA C.hE C.hI C.hR C.hIS hΓ (.sort .zero) .zero
      (instDomsA lsF fv.params) [] SubstA.id qs qs hqs
      (by rw [substA_id]; exact hpar (.sort .zero) .zero) ⟨substTyA_nil Γ SubstA.id⟩
    rw [List.append_nil] at h0
    rw [instCtxA_telCtxA]
    exact h0
  -- the position-indexed `.drecD` conversion: the view's `drecD_typed` at the raw position,
  -- extended to `E`, instantiated at `lsF`, and substituted along the walk's `SubstTyA`;
  -- the family application's parameter locals then close at `qs` (`hpl`)
  have hpreGw : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
    prefixA_trans (prefixA_extend _ _ _ hfreshR) hpre
  have hpreEF : PrefixA (extendEnvA E₀ f fm) E :=
    prefixA_trans (prefixA_extend_groupEnvA hfresh) hpreGw
  have hddE : ∀ (fsPre fsRest : List FieldA) (flP : List ExprA) (D : ExprA) (idx : List ExprA),
      gc.view.fields.map (FieldA.instLevels lsF) = fsPre ++ .drecD D idx :: fsRest →
      flP.length = plainIdxA fsPre 0 →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA flP (consListA qs SubstA.id))
        (plainCtxA fsPre (instCtxA lsF (telCtxA fv.params)))) →
      Nonempty (TyConvA E (iotaIfaceA E) n Γ (substA (consListA flP (consListA qs SubstA.id)) D)
        (foldAppsA (.const f lsF) (qs ++
          idx.map (substA (consListA flP (consListA qs SubstA.id)))))) := by
    intro fsPre fsRest flP D idx hfs hflP ⟨hσp⟩
    obtain ⟨fsPre₀, fd₀, fsRest₀, hsplit₀, hPreE, hFdE, _⟩ :=
      map_eq_append_cons _ _ _ _ hfs
    cases fd₀ with
    | drecD D₀ idx₀ =>
        simp only [FieldA.instLevels, FieldA.drecD.injEq] at hFdE
        obtain ⟨hDE, hidxE⟩ := hFdE
        subst hDE hidxE
        obtain ⟨-, hcv₀, -⟩ := gc.view.drecD_typed fsPre₀ D₀ idx₀ fsRest₀ hsplit₀
        obtain ⟨hc₀⟩ := hcv₀
        have hcE := convEnvA hpreEF hc₀
        have hcI := convA_instLevels C.hEL C.hIL hwfF hlenF hcE
        have hσp' : SubstTyA E (iotaIfaceA E) n Γ (consListA flP (consListA qs SubstA.id))
            (instCtxA lsF (plainCtxA fsPre₀ (telCtxA fv.params))) := by
          rw [instCtxA_plainCtxA, hPreE]
          exact hσp
        have hcσ := convA_substA C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hσp' hcI
        simp only [instantiateLevelsA, substA_sort] at hcσ
        have tD := tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ hcσ
        have hstep : instantiateLevelsA lsF ∘ liftA 0 (plainIdxA fsPre₀ 0) =
            liftA 0 (plainIdxA fsPre₀ 0) ∘ instantiateLevelsA lsF :=
          funext fun x => instantiateLevelsA_liftA lsF 0 _ x
        have h₂ : substA (consListA flP (consListA qs SubstA.id)) ∘
            liftA 0 (plainIdxA fsPre₀ 0) = substA (consListA qs SubstA.id) := by
          funext x
          show substA _ (liftA 0 (plainIdxA fsPre₀ 0) x) = _
          rw [show plainIdxA fsPre₀ 0 = flP.length from by
            rw [hflP, ← hPreE, plainIdxA_instLevels]]
          exact substA_consListA_liftA _ _ _
        have hpl : (paramLocalsA fv.params.length).map
            (substA (consListA flP (consListA qs SubstA.id)) ∘
              (instantiateLevelsA lsF ∘ liftA 0 (plainIdxA fsPre₀ 0))) = qs := by
          rw [hstep, ← List.map_map, ← List.map_map, map_instantiateLevelsA_paramLocalsA,
            List.map_map, h₂, ← hqsL, map_substA_consListA_paramLocalsA]
        have hAppF : substA (consListA flP (consListA qs SubstA.id))
            (instantiateLevelsA lsF (foldAppsA (.const f (canonLevelsA fm.arity))
              ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre₀ 0)) ++ idx₀))) =
          foldAppsA (.const f lsF) (qs ++ (idx₀.map (instantiateLevelsA lsF)).map
            (substA (consListA flP (consListA qs SubstA.id)))) := by
          rw [instantiateLevelsA_foldAppsA, substA_foldAppsA]
          simp only [List.map_append, List.map_map]
          congr 1
          · show substA _ (instantiateLevelsA lsF (.const f (canonLevelsA fm.arity))) = .const f lsF
            rw [show instantiateLevelsA lsF (.const f (canonLevelsA fm.arity)) =
                .const f ((canonLevelsA fm.arity).map (instLevel lsF)) from rfl, ← hlenF,
              canonLevelsA_instLevel, substA_const]
          · rw [hpl]
        rw [hAppF] at tD
        exact ⟨tD⟩
    | plain _ _ | drec _ | frec _ _ _ _ =>
        simp only [FieldA.instLevels] at hFdE
        cases hFdE
  have hWalk := minorWalkC C hΓ (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length f gc.ref lsF
    (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
    (gc.view.res.map (instantiateLevelsA lsF))
      mot qs fv.indices.length (fun v idx h hv => (hrecT v idx h hv).1) hrecW
    (instCtxA lsF (telCtxA fv.params)) (gc.view.fields.map (FieldA.instLevels lsF))
    (consListA qs SubstA.id) hddE
    [] (gc.view.fields.map (FieldA.instLevels lsF)) rfl hdl hdlF
    [] (consListA qs SubstA.id) fs rfl rfl ⟨hσq⟩ hFF'
  have happM := applyTelA_minor_rhsArgsA (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length f gc.ref
    lsF (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
    (gc.view.res.map (instantiateLevelsA lsF)) mot qs (gc.view.fields.map (FieldA.instLevels lsF)) []
    (consListA qs SubstA.id) fs (by rw [List.length_map]; exact hfsL)
  rw [plainArgsA_instLevels] at happM
  simp only [List.nil_append] at happM
  obtain ⟨cRhs⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hWalk ⟨cmin⟩ _ happM
  have tRhs := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cRhs
  rw [map_shape_instLevels, ← hkv, map_instLevels_norm, hca, ← hminE, ← he'] at tRhs
  -- (i) ROW 3 AGAIN: the minor's result indices are the redex's
  have tF₂F₁ : TyConvA E (iotaIfaceA E) n Γ (foldAppsA (.const f lsF) (qs ++ is))
      (foldAppsA (.const f lsF) (qs ++ (gc.view.res.map (instantiateLevelsA lsF)).map
        (substA (consListA (plainArgsA gc.view.fields fs) (consListA qs SubstA.id))))) :=
    .trans _ _ _ _ tUcF₂.symm tF₁Uc.symm
  obtain ⟨_, _, hIR⟩ := famApp_conv_args C hΓ fv hmf hcls hF₂ tF₂F₁
  obtain ⟨_, hIR'⟩ := famArgs_split fv lsF hIR hqsL hqsL
  -- (j) the two motive applications convert
  have cYF₂ : ConvA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref lsC) (ps ++ fs))
      (foldAppsA (.const gc.ref lsF) (qs ++ fs)) (foldAppsA (.const f lsF) (qs ++ is)) :=
    convA_of_tyConvA cY tUcF₂
  have hMotArgs : ConvArgsA E (iotaIfaceA E) n Γ
      (substA (consListA qs SubstA.id) (motTyA f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices)
        (instLevel lsF fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)
      (is ++ [foldAppsA (.const gc.ref lsC) (ps ++ fs)])
      ((gc.view.res.map (instantiateLevelsA lsF)).map
        (substA (consListA (plainArgsA gc.view.fields fs) (consListA qs SubstA.id))) ++
        [foldAppsA (.const gc.ref lsF) (qs ++ fs)]) := by
    rw [motTyA]
    refine convArgsA_append (convArgsA_piTelA_body _ _ _ _ _ _ hIR' his)
      (applyTelA_piTelA _ _ _ is his _) ?_
    simp only [substA_pi]
    have hd := substA_famLocalsA f lsF qs is
    rw [hqsL, hisL, ← instDomsA_length lsF fv.params, ← instDomsA_length lsF fv.indices] at hd
    rw [hd]
    exact .cons _ _ _ _ _ _ [] [] ⟨cYF₂⟩ (.nil _)
  obtain ⟨cMot⟩ := convA_spine C.hE C.hI C.hR C.hIS hΓ hMotArgs ⟨cmot⟩ _
    (applyTelA_motTy f lsF (instDomsA lsF fv.params) (instDomsA lsF fv.indices) (instLevel lsF fv.sort)
      (instLevel ls (rec.elim.motiveLevel fm.arity)) (consListA qs SubstA.id) is _ his)
  have tMot := tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cMot
  have tyR := TyConvA.trans _ _ _ _ tMot.symm tU
  refine ⟨⟨hasTyA_of_tyConvA tRhs tyR⟩, fun hst' => ?_⟩
  -- (k) W-1 (e-2), AT A STRUCT GROUP: ι's contractum, the minor at the constructor's fields, converts to the
  -- struct arm's reduct, the minor at the major's projections. The group's shape: one constructor, no
  -- index, plain fields in `Prop`
  have hstr : structGroupA (f + 1 + cs.length) rec.member = true := hAS.symm.trans hst'
  obtain ⟨gc₁, hgc, hnoidx, _, hplain, hzds, hnf⟩ := structCtorA_of_structGroupA rec hstr
  have hcs1 : cs.length = 1 := by
    have h0 := congrArg List.length hgc
    rwa [List.length_reverse] at h0
  have hgg : gc₁ = gc := by
    have hj0 : gc.ref - f - 1 = 0 := by omega
    rw [hgc, hj0] at hgcj
    simpa only [List.getElem?_cons_zero, Option.some.injEq] using hgcj
  subst gc₁
  have hres0 : gc.view.res = [] :=
    List.eq_nil_of_length_eq_zero (by rw [gc.view.res_length, hnoidx]; rfl)
  have hfl : gc.view.fields.length = (plainTelA gc.view.fields).length := by
    have h0 := congrArg List.length hplain
    rwa [List.length_map] at h0
  obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (by rw [hisL, hnoidx]; rfl)
  obtain ⟨mn, rfl⟩ : ∃ mn, ms = [mn] := by
    match ms, hmsL.trans hcs1 with
    | [mn], _ => exact ⟨mn, rfl⟩
  have hmn : minor = mn := by rw [hminE]; simp
  have hpreE : qs ++ [mot] ++ [mn] = pre := by rw [← hpre2, List.append_nil]
  subst hlsF
  -- the struct side at the recursor's levels and parameters (`structSideTyA`)
  have hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
    prefixA_trans (prefixA_extend _ _ _ hfreshR) hpre
  have hEL₀ : EnvLevelsA E₀ := fun r m hm =>
    C.hEL r m (prefixA_trans (prefixA_groupEnvA hfresh) hpreG r m hm)
  have hPq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) qs qs := by
    rw [fv.inst_split]; exact hpar _ _
  obtain ⟨_, _, hP3, hP4⟩ := structSideTyA C.hE C.hEL C.hEN C.hENL hEL₀ fv cs hfresh hlay rec hpre hpreG hstr hgc hnoidx
    hplain hzds hlslen hwfls hΓ (hqsL.trans hnpF) hPq hQF hFH
    (fun Δ _ => hasTyA_const_inst C (Γ := Δ) hmg hlenFC hwfF)
  -- the major, at the family application at the parameters
  have tx : HasTyA E (iotaIfaceA E) n Γ major (foldAppsA (.const f (ls.take fm.arity)) qs) := by
    have h0 := tMaj
    rw [List.append_nil] at h0
    rw [hmajE]
    exact h0
  -- the fields, a typed substitution along the constructor's plain telescope at the parameters
  obtain ⟨hσq⟩ : Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA qs SubstA.id)
      (telCtxA (instDomsA (ls.take fm.arity) fv.params))) := by
    have h0 := substTyA_of_convArgsA C.hE C.hI C.hR C.hIS hΓ (.sort .zero) .zero
      (instDomsA (ls.take fm.arity) fv.params) [] SubstA.id qs qs hqs
      (by rw [substA_id]; exact hpar (.sort .zero) .zero) ⟨substTyA_nil Γ SubstA.id⟩
    rwa [List.append_nil] at h0
  have hFFp : ConvArgsA E (iotaIfaceA E) n Γ (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      qs (consListA qs SubstA.id) ((instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA) []).1
      fs fs := by
    have h0 := hFF'
    rw [(congrArg (List.map (FieldA.instLevels (ls.take fm.arity))) hplain).trans (map_plainA_instLevels _ _),
      hres0] at h0
    exact h0
  have hfsD : fs.length = (plainTelA gc.view.fields).length := hfsL.trans hfl
  obtain ⟨hσF⟩ := substTyA_of_convArgsA_ctorFieldsA C.hE C.hI C.hR C.hIS hΓ f (ls.take fm.arity)
    (instLevel (ls.take fm.arity) fv.sort) [] (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))
    (telCtxA (instDomsA (ls.take fm.arity) fv.params)) qs (consListA qs SubstA.id) fs fs
    (hfsD.trans (instDomsA_length _ _).symm) hFFp ⟨hσq⟩
  -- the minor at its plain telescope, and the fields applied along it
  have cmin' := cmin
  rw [← hminE, hmn, (congrArg (List.map (FieldA.instLevels (ls.take fm.arity))) hplain).trans
    (map_plainA_instLevels _ _), hres0] at cmin'
  have hAppM : applyTelA fs (minorFieldsA f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      (instLevel ls (rec.elim.motiveLevel fm.arity)) qs mot [] (consListA qs SubstA.id)
      ((instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA) []).1 =
      some (.app mot (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs))) := by
    rw [applyTelA_minorFieldsA_plain _ _ _ _ _ _ _ _ _ _ _ _ (hfsD.trans (instDomsA_length _ _).symm)]
    simp only [minorFieldsA, List.map_nil, List.nil_append]
    rfl
  -- THE CARRIED CONVERSION, whatever telescope the projections are read along: the fields and the
  -- projections are proofs along the same telescope (`structSideTyA` (3) and (4)), so the minor at the
  -- fields converts to the minor at the projections
  have key : ∀ (Body : ExprA) (w : Level), Nonempty (ConvA E (iotaIfaceA E) n Γ (foldAppsA mn fs)
      (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs
        (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort)
        (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
        major (plainTelA gc.view.fields).length 0
        (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
          Body w).1))
      (.app mot (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs)))) := by
    intro Body w
    obtain ⟨hπ⟩ := hP3 major Body w tx
    have hlenπ := structProjsA_length (f + 1 + cs.length) (motZeroLevelsA ls) qs
      (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort)
      (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
      major Body w (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
      0 SubstA.id
    rw [substA_id, substTelA_length, instDomsA_length] at hlenπ
    obtain ⟨hcs⟩ := hP4 fs _ hfsD hlenπ ⟨hσF⟩ ⟨hπ⟩
    have hCA := convArgsA_minorFieldsA (E := E) (I := iotaIfaceA E) (n := n) f gc.ref (ls.take fm.arity)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) []
      (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)) (telCtxA (instDomsA (ls.take fm.arity) fv.params))
      qs mot [] (consListA qs SubstA.id) (consListA qs SubstA.id) fs _
      (hfsD.trans (instDomsA_length _ _).symm) (hlenπ.trans (instDomsA_length _ _).symm) hcs
    exact convA_spine C.hE C.hI C.hR C.hIS hΓ hCA ⟨cmin'⟩ _ hAppM
  -- ι's contractum is the minor at the fields (`rhsArgsA_plain`)
  rw [hkv, ← hca, ← map_instLevels_norm, congrArg (List.map FieldA.shape) hplain,
    (congrArg (List.map (FieldA.instLevels (ls.take fm.arity))) hplain).trans (map_plainA_instLevels _ _),
    map_norm_plainA,
    rhsArgsA_plain _ _ _ _ _ _ _ _ _ _ _ _ _ (hfsD.trans (instDomsA_length _ _).symm) (instDomsA_length _ _).symm,
    hmn] at he'
  -- the redex is the recursor's spine at its major, where the struct arm answers
  have hT_L : instantiateLevelsA ls rec.member.mtypeA = (piTelA (recDomsA f (ls.take fm.arity)
      (instDomsA (ls.take fm.arity) fv.params) [] (instLevel (ls.take fm.arity) fv.sort)
      (instLevel ls (rec.elim.motiveLevel fm.arity))
      [(gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])])
      (recBodyA 0 1) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 := by
    have hcd : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)) =
        [(gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])] := by
      rw [hgc]
      simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, MinorDataA.inst, hres0]
      rw [(congrArg (List.map (FieldA.instLevels (ls.take fm.arity))) hplain).trans (map_plainA_instLevels _ _)]
    rw [hRty, hcd, hnoidx]
    rfl
  have harm := structArmA_recSpineA hmr hstr hT_L (by rw [hnf, instDomsA_length]) hqs mot mn major
  rw [instDomsA_length] at harm
  have hlenP : (qs ++ [mot] ++ [mn]).length + 1 = piCountA rec.member.mtypeA := by rw [hpreE]; exact hplen
  refine ⟨_, major, _, by rw [he, ← hpreE, foldAppsA_snoc],
    recAtMajorA_recSpine hmr rec.hcls ((recHasCtorA_groupRecA rec).2 (List.ne_nil_of_length_pos (by omega)))
      ls _ hlenP, harm, ?_⟩
  rw [he']
  have tyR' : TyConvA E (iotaIfaceA E) n Γ (.app mot (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs))) T := by
    have h0 := tyR
    rw [hres0] at h0
    exact h0
  exact (key _ _).elim fun c => ⟨convA_of_tyConvA c tyR'⟩

/-- ι subject reduction in its typing form (`iotaSRA_core`'s first half). -/
theorem iotaSRA_ty (C : AnnEnvA E) : IotaSRTyA E n := fun hΓ h ht => (iotaSRA_core C hΓ h ht).1

/-- ι SUBJECT REDUCTION ON THE COPY, in its conversion form (W-1 (e-2)): under every environment the
    copy admits, a ι step at a typed redex is a conversion at the redex's type. Off a struct group it is
    `ConvA.iota`; at one, `ConvA.structIota` with the carried conversion (`iotaSRA_core`). -/
theorem iotaSRA (C : AnnEnvA E) : IotaSRA E n := by
  intro Γ lhs rhs T hΓ h ht
  obtain ⟨⟨tr⟩, hcarry⟩ := iotaSRA_core C hΓ h ht
  cases hs : iotaAtStructA E lhs with
  | false => exact ⟨.iota Γ lhs rhs T (iotaRelA_of_fn hs h) ht tr⟩
  | true =>
      obtain ⟨f, a, e, rfl, hrec, harm, ⟨hcv⟩⟩ := hcarry hs
      exact ⟨.structIota Γ f a rhs e T hrec harm h ht tr hcv⟩

end SR

/-! ## (5) the bridge and the rows, with no hypothesis beyond the copy's admission -/

section Final
variable {E : ResolvedEnvA} {n : Nat}

/-- the ι rules' right-hand premises (`hrhs`, the M-001 deviation NAMED at the constructor, and at a
    struct group the carried conversion) are derivable: under every environment the copy admits, a ι
    step at a typed redex is a conversion at the redex's type from the left-hand typing alone. -/
theorem convA_iota_of_fn (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {lhs rhs T : ExprA}
    (h : iotaFnA E lhs = some rhs) (hlhs : HasTyA E (iotaIfaceA E) n Γ lhs T) :
    Nonempty (ConvA E (iotaIfaceA E) n Γ lhs rhs T) :=
  iotaSRA C hΓ h hlhs

/-- ANNOTATION, discharged. The `EnvNormEraseA` hypothesis bounds the lift to environments whose
    normed constructor types erase to the stored ones — `drecD`-free (R-NoDeltaRec-4d-iii). -/
theorem annHasTyT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} {e T : Expr Nat}
    (h : HasTyT (eraseEnv E) n Γ e T)
    {ΓA : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n ΓA) (hctx : eraseCtx ΓA = Γ) :
    ∃ eA TA, erase eA = e ∧ erase TA = T ∧ Nonempty (HasTyA E (iotaIfaceA E) n ΓA eA TA) :=
  annHasTyT C (iotaSRA C) hn h hΓ hctx

theorem annCtxWfT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ) :
    ∃ ΓA, eraseCtx ΓA = Γ ∧ Nonempty (CtxWfA E (iotaIfaceA E) n ΓA) :=
  annCtxWfT C (iotaSRA C) hn hΓ

theorem annConvT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ a b T)
    {ΓA : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n ΓA) (hctx : eraseCtx ΓA = Γ) :
    ∃ aA bA TA, erase aA = a ∧ erase bA = b ∧ erase TA = T ∧
      Nonempty (ConvA E (iotaIfaceA E) n ΓA aA bA TA) :=
  annConvT C (iotaSRA C) hn h hΓ hctx

/-- ι SUBJECT REDUCTION ON THE TYPED JUDGMENT, over every environment the copy admits whose normed
    types erase to the stored ones (`EnvNormEraseA`; `drecD`-free — R-NoDeltaRec-4d-iii): annotate
    the redex, step the copy (`iotaFnA_of_derivedIota`), keep its type (`iotaSRA`), erase. -/
theorem hasTyT_iota_sr (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIota (eraseEnv E) lhs rhs) (hlhs : HasTyT (eraseEnv E) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv E) n Γ rhs T) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨eA, TA, he, hT, ⟨tA⟩⟩ := annHasTyT' C hn hlhs hΓA hctx
  subst he
  obtain ⟨hW⟩ := C.wf
  obtain ⟨e', hfn, he'⟩ := iotaFnA_of_derivedIota hW hn hd
  obtain ⟨t'⟩ := iotaSRA_ty C hΓA hfn tA
  obtain ⟨hT'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) t'
  rw [he', hT, hctx] at hT'
  exact ⟨hT'⟩

/-- `ConvT.iota`'s right-hand typing (R-TypedRules (4)) is derivable over every environment the
    copy admits whose normed types erase to the stored ones (R-NoDeltaRec-4d-iii). -/
theorem convT_iota_of_derived (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ)
    {lhs rhs T : Expr Nat} (hd : DerivedIota (eraseEnv E) lhs rhs) (hlhs : HasTyT (eraseEnv E) n Γ lhs T) :
    Nonempty (ConvT (eraseEnv E) n Γ lhs rhs T) := by
  obtain ⟨hrhs⟩ := hasTyT_iota_sr C hn hΓ hd hlhs
  exact ⟨.iota Γ lhs rhs T hd hlhs hrhs⟩

/-- ι SUBJECT REDUCTION AT THE SHAPE-BASED EVIDENCE (R-NoFunRec-1 B2, the phase-2B typed
    sibling): `hasTyT_iota_sr`'s proof shape — annotate the redex, step the copy, keep its
    type, erase — with the annotation direction now discharged by `IotaCorrTA.ann` under
    the certificates below `eraseEnv E` (`iotaCorrTA_of_envWfA`), instead of the
    unconditional legacy `iotaFnA_of_derivedIota`.  The `CorrCertsBelow` premise is the
    sound gate the countermodel demands: it is REFUTED at `vecEnvUT`
    (`RcicTypedGroupPinsVec.not_corrCertsBelow_vecEnvUT`, the `vecOnlyEnvU` deficient
    sub-env), so this route — unlike `hasTyT_iota_sr` — genuinely cannot fire at that
    environment even though it is `EnvWfT` + `InScope`. -/
theorem hasTyT_iota_srT (C : AnnEnvA E) (hn : EnvNormEraseA E) (hC : CorrCertsBelow (eraseEnv E))
    {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT (eraseEnv E) lhs rhs) (hlhs : HasTyT (eraseEnv E) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv E) n Γ rhs T) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨eA, TA, he, hT, ⟨tA⟩⟩ := annHasTyT' C hn hlhs hΓA hctx
  subst he
  obtain ⟨hW⟩ := C.wf
  have hcorr := iotaCorrTA_of_envWfA hW C.noFun hn
    (hC _ (envSub_refl _)).1 (hC _ (envSub_refl _)).2
  obtain ⟨e', hfn, he'⟩ := hcorr.ann _ _ hd
  obtain ⟨t'⟩ := iotaSRA_ty C hΓA hfn tA
  obtain ⟨hT'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) t'
  rw [he', hT, hctx] at hT'
  exact ⟨hT'⟩

/-- ROW 1 ON THE TYPED JUDGMENT, over every environment the copy admits. -/
theorem sortConvCharT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {l₁ l₂ : Level}
    {T : Expr Nat} (h : ConvT (eraseEnv E) n Γ (.sort l₁) (.sort l₂) T) : eqN l₁ l₂ :=
  sortConvCharT C (iotaSRA C) hn hΓ h

/-- ROW 2 ON THE TYPED JUDGMENT, over every environment the copy admits. -/
theorem piConvInjT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {A B A' B' T : Expr Nat}
    (h : ConvT (eraseEnv E) n Γ (.pi A B) (.pi A' B') T) :
    Nonempty (TyConvT (eraseEnv E) n Γ A A') ∧
      Nonempty (TyConvT (eraseEnv E) n (.assumption A :: Γ) B B') :=
  piConvInjT C (iotaSRA C) hn hΓ h

/-- ROW 3 ON THE TYPED JUDGMENT, at a Type-level family, over every environment the copy admits. -/
theorem famAppConvInjT' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat}
    {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {u₀ w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (hz : isZero (instLevel ls u₀) = false)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjT C (iotaSRA C) hn hΓ hm hind hsh hz h

/-- ROW 3 ON THE TYPED JUDGMENT, at a `Prop`-level conversion, over every environment the copy
    admits. -/
theorem famAppConvInjT_prop' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat}
    {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hw : isZero w = true)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjT_prop C (iotaSRA C) hn hΓ hm hind hw h

/-- ROW 3 ON THE TYPED JUDGMENT, at either level, over every environment the copy admits. -/
theorem famAppConvInjT_any' (C : AnnEnvA E) (hn : EnvNormEraseA E) {Γ : LCtx}
    (hΓ : CtxWfT (eraseEnv E) n Γ) {r : Nat}
    {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {u₀ w : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (h : ConvT (eraseEnv E) n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT (eraseEnv E) n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs' :=
  famAppConvInjT_any C (iotaSRA C) hn hΓ hm hind hsh h

end Final

/-! ## (6) the admission is inhabited by an environment with a recursor

`pinNatBuiltEnvA` (`RcicAnnRecPins`, M2-f (5)+(5b)) is `Nat` with `zero`, `succ` and its AnySort
recursor, admitted by `EnvWfA.groupRec`, with a ι step that fires (`pinNatGroupRec_iotaZero`). It meets
`AnnEnvA`, so every theorem above applies to it with no further hypothesis. -/

theorem annEnvA_pinNat : AnnEnvA pinNatBuiltEnvA :=
  ⟨⟨pinNatBuilt_wf⟩, pinNatBuilt_small, propElimStructA_of_propElimOnlyA pinNatBuilt_propElim,
    pinNatBuilt_noFun⟩

theorem iotaSRA_pinNat (n : Nat) : IotaSRA pinNatBuiltEnvA n :=
  iotaSRA annEnvA_pinNat

/-- W-1 (e-2), THE BRIDGE AT A STRUCT GROUP: `S` and `And` are outside `PropElimOnlyA`
    (`pinStruct_not_propElim`, `pinAnd_not_propElim`) and inside the copy's admission, so ι subject
    reduction, the bridge and the typed rows hold at them. -/
theorem annEnvA_pinStruct : AnnEnvA pinStructEnvA :=
  ⟨⟨pinStruct_wf⟩, pinStruct_small, pinStruct_propElimStruct, pinStruct_noFun⟩

theorem annEnvA_pinAnd : AnnEnvA pinAndEnvA :=
  ⟨⟨pinAnd_wf⟩, pinAnd_small, pinAnd_propElimStruct, pinAnd_noFun⟩

/-- at `S`'s constructor ι is not the head step (`pinStruct_ctor_notIotaRel`), so `ConvA.iota` does not
    fire there; ι subject reduction still converts the redex to ι's contractum, by `ConvA.structIota` with
    the carried conversion. -/
theorem pinStruct_ctor_conv (n : Nat) :
    Nonempty (ConvA pinStructEnvA (iotaIfaceA pinStructEnvA) n [] (.app pinStructF (.app (.const 51 []) pinIdTermA))
      (.app pinStructm pinIdTermA) (.app pinStructM (.app (.const 51 []) pinIdTermA))) :=
  iotaSRA annEnvA_pinStruct .nil pinStruct_ctor_iotaFn
    (pinStructFAppTy rfl rfl rfl _ (pinStructMkAppTy rfl rfl _ pinIdTermTy))

/-- `rec M m a ≡ S : Prop` at every proof `a : S`, at the copy's own ι (`pinStructConv` with the
    conversion above). -/
theorem pinStruct_conv (n : Nat) {a : ExprA}
    (ha : HasTyA pinStructEnvA (iotaIfaceA pinStructEnvA) n [] a (.const 50 [])) :
    Nonempty (ConvA pinStructEnvA (iotaIfaceA pinStructEnvA) n [] (.app pinStructF a) (.const 50 []) (.sort .zero)) :=
  (pinStruct_ctor_conv n).elim fun c3 => ⟨pinStructConv rfl rfl rfl c3 a ha⟩


end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.spine_gen
#print axioms Rcic.Declarative.Ann.convArgsA_swap
#print axioms Rcic.Declarative.Ann.recRedexC
#print axioms Rcic.Declarative.Ann.convArgsA_bvarsA
#print axioms Rcic.Declarative.Ann.hasTyA_appsVars
#print axioms Rcic.Declarative.Ann.hasTyA_recCallFunA_frec
#print axioms Rcic.Declarative.Ann.list4_inj
#print axioms Rcic.Declarative.Ann.minorWalkC
#print axioms Rcic.Declarative.Ann.iotaSRA_core
#print axioms Rcic.Declarative.Ann.iotaSRA_ty
#print axioms Rcic.Declarative.Ann.iotaSRA
#print axioms Rcic.Declarative.Ann.convA_iota_of_fn
#print axioms Rcic.Declarative.Ann.annHasTyT'
#print axioms Rcic.Declarative.Ann.annCtxWfT'
#print axioms Rcic.Declarative.Ann.hasTyT_iota_sr
#print axioms Rcic.Declarative.Ann.hasTyT_iota_srT
#print axioms Rcic.Declarative.Ann.convT_iota_of_derived
#print axioms Rcic.Declarative.Ann.annConvT'
#print axioms Rcic.Declarative.Ann.sortConvCharT'
#print axioms Rcic.Declarative.Ann.piConvInjT'
#print axioms Rcic.Declarative.Ann.famAppConvInjT'
#print axioms Rcic.Declarative.Ann.famAppConvInjT_prop'
#print axioms Rcic.Declarative.Ann.famAppConvInjT_any'
#print axioms Rcic.Declarative.Ann.annEnvA_pinNat
#print axioms Rcic.Declarative.Ann.iotaSRA_pinNat
#print axioms Rcic.Declarative.Ann.annEnvA_pinStruct
#print axioms Rcic.Declarative.Ann.annEnvA_pinAnd
#print axioms Rcic.Declarative.Ann.pinStruct_ctor_conv
#print axioms Rcic.Declarative.Ann.pinStruct_conv
