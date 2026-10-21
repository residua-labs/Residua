import rcic.RcicAnnLRChain
import rcic.RcicAnnLRStuckDatumG
import rcic.RcicAnnTyRedPrefix
import rcic.RcicAnnAnnotateG

/-!
# DT-025 / A-6 M1 — the guarded chain combinator `chainG` (cc ruling (c′))

The per-term normalizer on the **guarded** cone. `tyKAg_chain_sub` is the
`TyKAg`-copy of `tyKA_chain_sub`: a `TyKAg`-derivation's reached members carry
chains, with `hstuck` supplied per reached node. On the guarded cone `hstuck`
is *discharged by the datum* at `.stuck` and `.fam` nodes (`TyKAg.stuck`'s
relation carries the chains; `TyKA_uniqueg` at a `StuckA`-reached `.fam` node
rewrites `LfpWA` to the chained quadruple), and is the named premise
`PropStuckChainsA` at `.prop`-clause nodes only — cc ruling (c′): the
`.prop`-stuck members are the ONE explicit named residual, recorded under
`[rcic_cres_wall_f05b_loop]` as the propElim boundary, never assumed silently.

The measure analysis (scratch `M1_HOP_DISCHARGE_SCRATCH.md` addendum 2–3) is
why `chainG` is *not* a `WellFounded.fix`: `.prop`-members carry `ht`-arbitrary
typings while `happ` produces `ht`-bounded-but-`d`-fresh `fund`-data — no
`(size ht, size d)`-lex orders both. Under `hPSC` the `.prop`-members are
premised and the `htail`/`hlet`/`hlit` reducts are the named sub-wall
`TailChainsA`; the typed-head-step residual at a non-`Prop` `Π` is the named
`PiHeadStepTypedA`. `chainG` itself is then *non-recursive*:
`fund_selfg` + `tyKAg_chain_sub` + `hstuck := {stuck/fam → datum, prop → hPSC}`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## named residuals (cc (c′), `[rcic_cres_wall_f05b_loop]`) -/

/-- **the propElim boundary premise** — every `.prop`-clause member at a
`TyInKAg`-reached node whose whnf is a stuck proposition carries head chains
to `hStepFnA`-normal forms. The `.prop`-relation is `HasTyA + ConvA`
(no chains): this is the ONE named residual for `chainG`, recorded under
`[rcic_cres_wall_f05b_loop]` — the prop-clause was built for `irr`-proofs,
and a *stuck Prop* is not an impredicative-π situation. -/
def PropStuckChainsA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ' : LCtxA} {A' N' a' b' : ExprA}, Nonempty (CtxWfA E I n Γ') →
    WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → IsPropTy E I Γ' N' →
    Nonempty (HasTyA E I n Γ' a' N') → Nonempty (HasTyA E I n Γ' b' N') →
    Nonempty (ConvA E I n Γ' a' b' N') →
    ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none

/-- **the β/ζ/lit-tail sub-wall** — `htail`/`hlet`/`hlit` reducts of
`.prop`-stuck member heads: `inst0 a body` (β), `inst0 v body` (ζ), and
`natExpandA t` (lit) have `ht`-arbitrary typings (`ht_{Nf}`-opaque, chain-output
derived) — they break every `K·ht`-weighted measure. The named premise supplies
their chains; Hop is *reduced* to it (cc fallback (1)), not "broken". A
`TyKAg`-head-expansion-closure datum (Tait/Girard CR-style) would make it a
theorem — measured separately. -/
def TailChainsA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ' : LCtxA} {T A B a body Nc : ExprA},
    Nonempty (CtxWfA E I n Γ') →
    Nonempty (HasTyA E I n Γ' (instantiate0A a body) (instantiate0A a B)) →
    ∃ Nc', TyHRedStarA E I n Γ' (instantiate0A a body) Nc'
      (instantiate0A a B) ∧ hStepFnA E I.fn Γ' Nc' = none

/-- **`PiHeadStepTypedA`** — the typed-head-step premise at a non-`Prop` `Π`
    (cc ruling on #6351): every `hStepFnA`-step of a term typed at a `Type`-level
    `Π` is a typed step. Measured as *not* derivable on the general `AnnEnvA`
    cone: the `β`/`ζ`/`ζ`-local/`lit`/`δ`/`ι` arms are discharged (`hasTyA_*_gen`
    + `hasTyA_inst0'`/`hasTyA_inst0Let`, `hasTyA_memberBody_inst`,
    `iotaSRA_ty` + `IotaIfaceA.rel`'s graph) and the `major` arm is mechanical
    (`piHeadStepTypedA_major` — the inner `TyHRedA` + `tyHRedA_conv`/
    `tyHRedA_hasTy_right` + `inst0`-at-conv-args congruence).
    **The named residual is `kunit`/`kstruct`** — the irr/η equation at the
    recursor's major (`#6293`, W-ATR-3 family): `ConvA (app f a) mn T` /
    `ConvA (app f a) (minor applied to a's projections) T` for an *arbitrary*
    ι-refusing major `a`, semantically the record-η join `a ≡ mk (proj a)` of
    unit/struct groups — a `ConvA` obligation, *not* subject reduction, so the
    ATR `S` component does not produce it (the ctor's `hrt` follows from
    ι-schema typing + `hcv` transport once the equation exists). Named as
    Hop's remaining sub-wall under `[rcic_cres_wall_dt025_hop]`; the step-clean
    profile discharges it wholly (`hStepFnA_typedPi`). -/
def PiHeadStepTypedA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ' : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {e e' : ExprA}, CtxWfA E I n Γ' → isZero v = false →
    HasTyA E I n Γ' e (.pi D u C v) → hStepFnA E I.fn Γ' e = some e' →
    Nonempty (TyHRedA E I n Γ' e e' (.pi D u C v))

/-- **`HopFacesA`** — the δ-face supply property (cc ruling on #6351): at any
    reached node `(Γ', A' → N' stuck)`, every *transparent* member body carries
    a head chain at the instantiated member type, together with the body typing
    the `hdelta` face needs. The `TyInKA`/`e`-witness refinements of the
    `hstuck_of_faces` slot are omitted — the face adapts positionally. -/
def HopFacesA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ' : LCtxA} {A' N' : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA},
    Nonempty (CtxWfA E I n Γ') → WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
    E.members r = some m → m.bodyA = some b → transparent m.mclass = true →
    ls.length = m.arity → levelsBounded n ls = true →
    Nonempty (TyConvA E I n Γ' (instantiateLevelsA ls m.mtypeA) N') →
    Nonempty (HasTyA E I n Γ' (instantiateLevelsA ls b)
      (instantiateLevelsA ls m.mtypeA)) ∧
    ∃ Nb, TyHRedStarA E I n Γ' (instantiateLevelsA ls b) Nb
      (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ' Nb = none

/-! ## the guarded `TyInKA` -/

/-- `TyInKAg d Γ' A' R'`: a `TyKAg` node at `(Γ', A', R')` reached inside `d`
    through the positions the extraction threads `sub` through — reflexively at
    the root, and through `TyKAg.pi`'s codomain child. Mirrors `TyInKA`. -/
inductive TyInKAg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} :
    ∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
    TyKAg E I n ρ₀ k LE LT Γ A R → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | refl {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
      (d : TyKAg E I n ρ₀ k LE LT Γ A R) : TyInKAg d Γ A R
  | piCod {Γ : LCtxA} {A D C : ExprA} {u v : Level}
      {RD : WkSpecA → ExprA → ExprA → Prop}
      {RC : WkSpecA → ExprA → ExprA → ExprA → Prop}
      {hA : WhTyA E I n Γ A (.pi D u C v)}
      {hnp : ¬ IsPropTy E I Γ (.pi D u C v)}
      {hDty : Nonempty (HasTyA E I n Γ D (.sort u))}
      {hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v))}
      {hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)}
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
      {hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))}
      {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop}
      {ρ : WkSpecA} {hok : WkOkA E I n ρ Γ} {a a' : ExprA} {hr : RD ρ a a'} :
      TyInKAg (hC ρ hok a a' hr) Γ' A' R' →
      TyInKAg (TyKAg.pi hA hnp hDty hCty RD hD RC hC hCeq) Γ' A' R'

/-- `TyInKAg` membership carries the reached derivation. -/
theorem tyInKAg_extract {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ' : LCtxA} {A' : ExprA}
    {R' : ExprA → ExprA → Prop} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} {d : TyKAg E I n ρ₀ k LE LT Γ A R}
    (h : TyInKAg d Γ' A' R') : Nonempty (TyKAg E I n ρ₀ k LE LT Γ' A' R') := by
  induction h with
  | refl d => exact ⟨d⟩
  | piCod =>
    rename_i hsub ih
    exact ih

/-- a reached node at a whnf-stuck non-proposition type carries the guarded
    `stuck` clause's chained quadruple: `TyInKAg` extracts the derivation,
    `TyKA_uniqueg` identifies its relation with `TyKAg.stuck`'s. -/
theorem tyInKAg_stuck_rel {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    {d : TyKAg E I n ρ₀ k LE LT Γ A R} {Γ' : LCtxA} {A' : ExprA}
    {R' : ExprA → ExprA → Prop} {N' : ExprA}
    (hin : TyInKAg d Γ' A' R') (hA : WhTyA E I n Γ' A' N')
    (hN : StuckA E I Γ' N') (hnp : ¬ IsPropTy E I Γ' N') :
    R' = (fun a b => Nonempty (HasTyA E I n Γ' a N') ∧
      Nonempty (HasTyA E I n Γ' b N') ∧ Nonempty (ConvA E I n Γ' a b N') ∧
      ∃ Na, TyHRedStarA E I n Γ' a Na N' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b Nb N' ∧ hStepFnA E I.fn Γ' Nb = none) :=
  (tyInKAg_extract hin).elim fun d' => TyKA_uniqueg d' (.stuck hA hN hnp)

/-- a reached node at a whnf-stuck proposition type carries the `prop` clause's
    `HasTyA + ConvA` relation (the `hPSC` face). -/
theorem tyInKAg_prop_rel {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    {d : TyKAg E I n ρ₀ k LE LT Γ A R} {Γ' : LCtxA} {A' : ExprA}
    {R' : ExprA → ExprA → Prop} {N' : ExprA}
    (hin : TyInKAg d Γ' A' R') (hA : WhTyA E I n Γ' A' N')
    (hn : hStepFnA E I.fn Γ' N' = none) (hP : IsPropTy E I Γ' N') :
    R' = (fun a b => Nonempty (HasTyA E I n Γ' a N') ∧
      Nonempty (HasTyA E I n Γ' b N') ∧ Nonempty (ConvA E I n Γ' a b N')) :=
  (tyInKAg_extract hin).elim fun d' => TyKA_uniqueg d' (.prop hA hn hP)

/-- the guarded `TyKAg` datum's whnf — the `tyKA_whnf` copy. -/
theorem tyKAg_whnf {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} (h : TyKAg E I n ρ₀ k LE LT Γ A R) :
    ∃ N, WhTyA E I n Γ A N ∧ hStepFnA E I.fn Γ N = none := by
  cases h with
  | prop hA hn _ => exact ⟨_, hA, hn⟩
  | sortT hA _ _ => exact ⟨_, hA, hStepFnA_sort _ _ _ _⟩
  | sortP hA _ => exact ⟨_, hA, hStepFnA_sort _ _ _ _⟩
  | pi hA _ _ _ _ _ _ _ _ => exact ⟨_, hA, hStepFnA_pi _ _ _ _ _ _ _⟩
  | fam hA hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, hA, hn⟩
  | stuck hA hN _ => exact ⟨_, hA, hN.1⟩

end Rcic.Declarative.Ann

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- **`tyKAg_chain_sub`** — the guarded copy of `tyKA_chain_sub`: members of a
    `TyKAg`-derivation's reached relation carry head chains, `hstuck` supplied
    per `TyInKAg`-node. Same motive and arm structure; the env-consumer lemmas
    (`whnfChainA_at`, `hkey_of_sortTy`) take `hS` and are shared. -/
theorem tyKAg_chain_sub {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (d : TyKAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j) Γ A R)
    (hstuck : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {a' b' N' : ExprA},
      TyInKAg d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → R' a' b' →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep : PiHeadStepTypedA E I n)
    (hΓ : CtxWfA E I n Γ) {a b : ExprA} (hab : R a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  refine TyKAg.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ' T' RT' d' =>
      (∀ {Γ'' : LCtxA} {A'' : ExprA} {R'' : ExprA → ExprA → Prop},
        TyInKAg d' Γ'' A'' R'' → TyInKAg d Γ'' A'' R'') →
      Nonempty (CtxWfA E I n Γ') →
      (∀ {N' : ExprA}, WhTyA E I n Γ' T' N' → hStepFnA E I.fn Γ' N' = none →
        ¬ IsPropTy E I Γ' N' ∨ StuckA E I Γ' N') →
      ∀ a' b' : ExprA, RT' a' b' →
        ∃ Na, TyHRedStarA E I n Γ' a' Na T' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb T' ∧ hStepFnA E I.fn Γ' Nb = none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d (fun h => h) ⟨hΓ⟩ hkey a b hab
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · exact fun hA hn hP hsub hΓx hk a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rcases hk hA hn with hnp' | hst
      · exact absurd hP hnp'
      · exact hstuck (hsub (TyInKAg.refl _)) ⟨hΓ'⟩ hA hst hab
  · exact fun hA hz hk hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rename_i l
      obtain ⟨_, ⟨Ra, hRa⟩, ⟨Rb, hRb⟩, hta, htb, _⟩ := hab
      have hTa' : LRTyAg E I n ρ₀ (ht ρ₀ l) _ a' Ra := hRa
      have hTb' : LRTyAg E I n ρ₀ (ht ρ₀ l) _ b' Rb := hRb
      rw [LRTyA_eqg] at hTa' hTb'
      obtain ⟨Na, whNa, hnNa⟩ := tyKAg_whnf hTa'
      obtain ⟨Nb, whNb, hnNb⟩ := tyKAg_whnf hTb'
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hnNa hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hnNb htb hA
      exact ⟨Na, cha, hnNa, Nb, chb, hnNb⟩
  · exact fun hA hz hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      obtain ⟨⟨Na, whNa, hTa⟩, ⟨Nb, whNb, hTb⟩, hta, htb, _, _⟩ := hab
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hTa.1 hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hTb.1 htb hA
      exact ⟨Na, cha, hTa.1, Nb, chb, hTb.1⟩
  · exact fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq hsub hΓx hkey' f g hab => by
      rename_i Γ A D C u v
      obtain ⟨hΓ'⟩ := hΓx
      have hzv : isZero v = false := by
        cases hz : isZero v with
        | false => rfl
        | true => exact absurd ((isPropTy_pi_iff E I Γ D u C v).mpr hz) hnp
      have hΓD : Nonempty (CtxWfA E I n (.assumption D :: Γ)) :=
        hDty.elim fun t => ⟨.assumption hΓ' t⟩
      have hρ₀ : WkOkA E I n [(.assumption D, 0)] Γ :=
        ⟨⟨Nat.zero_le _, trivial⟩, hΓD⟩
      have hT'eq : instantiate0A (.bvar 0)
          (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C) = C :=
        instantiate0A_bvar0_liftA C
      have hCty' : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C))
          (.sort v)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) _ (.sort v))
        rw [hT'eq]
        exact hCty
      have hkeyC : ∀ {N' : ExprA}, WhTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C)) N' →
          hStepFnA E I.fn (wkCtxA [(.assumption D, 0)] Γ) N' = none →
          ¬ IsPropTy E I (wkCtxA [(.assumption D, 0)] Γ) N' ∨
            StuckA E I (wkCtxA [(.assumption D, 0)] Γ) N' :=
        fun hN' hn' => hCty'.elim fun hCt => hΓD.elim fun hΓD' =>
          hkey_of_sortTy hE hI hIS hEN hNC hR hS hρ hΓD' hfamkey hCt hzv hN' hn'
      have hxv : lookupValueA (wkCtxA [(.assumption D, 0)] Γ) 0 = none :=
        lookupValueA_cons_zero_assumption D Γ
      have hDx : ∃ R', LRTyAg E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) R' :=
        ⟨RD [(.assumption D, 0)], by rw [LRTyA_eqg]; exact hD _ hρ₀⟩
      have htx : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ) (.bvar 0)
          (wkExprA [(.assumption D, 0)] D)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) (.bvar 0) (liftA 0 1 D))
        exact (hasTyA_wk_ne hE hI [(.assumption D, 0)] ⟨Nat.zero_le _, trivial⟩ hDty).elim
          fun t => ⟨.bvar _ 0 _ _ (lookupTypeA_cons_zero_assumption D Γ) t⟩
      have hxrel : LRRelAg E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) (.bvar 0) (.bvar 0) :=
        LRRelA_bvarg hE hI (iotaConstHeadA_of_recHead hR)
          (propKeyA_holds hE hI hIS hEN hNC hR hS hρ) hΓD hxv hDx htx
      have hRD : RD [(.assumption D, 0)] (.bvar 0) (.bvar 0) :=
        LRRelAg.at hxrel (by rw [LRTyA_eqg]; exact hD _ hρ₀)
      have happR : RC [(.assumption D, 0)] (.bvar 0)
          (.app (wkExprA [(.assumption D, 0)] f) (.bvar 0))
          (.app (wkExprA [(.assumption D, 0)] g) (.bvar 0)) :=
        hab.1 _ hρ₀ _ _ hRD
      obtain ⟨Na, cha, hnNa, Nb, chb, hnNb⟩ :=
        ihC _ hρ₀ (.bvar 0) (.bvar 0) hRD
          (fun {Γ'' : LCtxA} {A'' : ExprA} {R'' : ExprA → ExprA → Prop}
              (h : TyInKAg (hC _ hρ₀ (.bvar 0) (.bvar 0) hRD) Γ'' A'' R'') =>
            hsub (@TyInKAg.piCod E I n ρ₀ k _ _ Γ A D C u v RD RC hA hnp hDty hCty hD
              hC hCeq Γ'' A'' R'' _ hρ₀ (.bvar 0) (.bvar 0) hRD h)) hΓD hkeyC _ _ happR
      obtain ⟨hf⟩ := hab.2.1
      obtain ⟨hg⟩ := hab.2.2.1
      obtain ⟨tcha⟩ := cha
      obtain ⟨Nf, hfred⟩ := piHeadPrefix tcha rfl hnNa
      obtain ⟨Nf', _, hfred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hfred
      obtain ⟨fuelf, hwf⟩ := hfred'
      have hnf' : hStepFnA E I.fn Γ Nf' = none :=
        whnfA_normal E I.fn Γ fuelf f Nf' hwf
      obtain ⟨chf⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelf hf hwf
      obtain ⟨tchb⟩ := chb
      obtain ⟨Ng, hgred⟩ := piHeadPrefix tchb rfl hnNb
      obtain ⟨Ng', _, hgred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hgred
      obtain ⟨fuelg, hwg⟩ := hgred'
      have hng' : hStepFnA E I.fn Γ Ng' = none :=
        whnfA_normal E I.fn Γ fuelg g Ng' hwg
      obtain ⟨chg⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelg hg hwg
      exact ⟨Nf', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chf⟩, hnf',
        Ng', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chg⟩, hng'⟩
  · intro Γ' A' r ls ps is m u u₀ hA
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsub hΓx hkey' a' b' hab
    exact fam_chain_pair hA hab
  · exact fun hA hN hnp hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      exact hstuck (hsub (TyInKAg.refl _)) ⟨hΓ'⟩ hA hN hab

/-- **`chainG`** — the per-term normalizer on the `AnnEnvA` cone, conditional on
    `PropStuckChainsA` (cc (c′)). `fund_selfg` gives the `TyKAg`-datum;
    `tyKAg_chain_sub` extracts the pair's chains with `hstuck` supplied by
    datum-extraction at `.stuck`/`.fam` nodes and `hPSC` at `.prop` nodes. -/
theorem chainG {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hSg : EnvSemAg E I n ρ₀)
    (hρ : PosValA ρ₀) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {t T : ExprA} (ht : HasTyA E I n Γ t T)
    (hPSC : PropStuckChainsA E I n)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ T N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep : PiHeadStepTypedA E I n) :
    ∃ N, TyHRedStarA E I n Γ t N T ∧ hStepFnA E I.fn Γ N = none := by
  obtain ⟨k₀, hk⟩ := fund_selfg hE hI hIS hEN hNC hR hSg hρ
    (propKeyA_holds hE hI hIS hEN hNC hR hS hρ) hΓ ht
  obtain ⟨R, hRK, hab⟩ := hk k₀ (Nat.le_refl _)
  rw [LRTyA_eqg] at hRK
  obtain ⟨N, chN, hnN, _⟩ := tyKAg_chain_sub hE hI hIS hEN hNC hR hS hρ hRK
    (fun hin hΓ' hA hN hab' => by
      obtain ⟨d'⟩ := tyInKAg_extract hin
      cases d' with
      | prop hA' hn' hP' =>
          rename_i Γ' A' R' N' a' b'
          have e' := whTyA_det hA hA' hN.1 hn'
          subst e'
          obtain ⟨hta, htb, hcv⟩ := hab'
          obtain ⟨hΓx⟩ := hΓ'
          exact hPSC ⟨hΓx⟩ hA hN hP' hta htb hcv
      | stuck hA' hN' hnp' =>
          rename_i Γ' A' R' N' a' b'
          obtain ⟨_, _, _, Na, cha, hna, Nb, chb, hnb⟩ := hab'
          have hcA := tyConvA_symm_ne (whTyA_tyConv hA')
          exact ⟨Na, tyHRedStarA_retype hcA cha, hna, Nb, tyHRedStarA_retype hcA chb, hnb⟩
      | sortT hA' _ _ =>
          rename_i Γ' A' R' N' a' b'
          have e' := whTyA_det hA hA' hN.1 (hStepFnA_sort _ _ _ _)
          subst e'
          exact absurd hN stuckA_not_sort
      | sortP hA' _ =>
          rename_i Γ' A' R' N' a' b'
          have e' := whTyA_det hA hA' hN.1 (hStepFnA_sort _ _ _ _)
          subst e'
          exact absurd hN stuckA_not_sort
      | pi hA' _ _ _ _ _ _ _ _ =>
          rename_i Γ' A' R' N' a' b'
          have e' := whTyA_det hA hA' hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
          subst e'
          exact absurd hN stuckA_not_pi
      | fam hA' hn' hnp' hm hind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          rename_i Γ' A' R' N' a' b'
          exact fam_chain_pair hA' hab')
    hkey hfamkey hpiStep hΓ hab
  exact ⟨N, chN, hnN⟩

/-- **`hopFacesA_of_envWf`** — the `HopFacesA` discharge on the `AnnEnvA` cone
    (cc ruling on #6351): conditional on `PropStuckChainsA` (the `.prop`-stuck
    members — the propElim boundary, `[rcic_cres_wall_f05b_loop]`) and
    `PiHeadStepTypedA` (typed `hStepFnA`-steps at a non-`Prop` `Π` — the
    remaining Hop sub-wall `[rcic_cres_wall_dt025_hop]`; discharged only on the
    step-clean profile, `hStepFnA_typedPi`). `closure_claim` stays `0`.

    Per transparent member `r`: the body typing at the instantiated member
    type is `hasTyA_memberBody_inst`; the chain is by sort-case on the
    (instantiated) member type:

    * `isZero u = false` — `chainG` directly (`hkey` by `hkey_of_sortTy` at the
      non-`Prop` sort; `.prop`-stuck nodes inside are `hPSC`).
    * `isZero u = true` — the member type's whnf is a proposition
      (`propKey_K1`), and `propKey_K3` transports `IsPropTy` across the face's
      `TyConvA` to the node's stuck type `N'`; `hPSC` at `(N', N')` then gives
      the body chain, retyped to the member type. -/
theorem hopFacesA_of_envWf (C : AnnEnvA E) {n : Nat}
    (hPSC : PropStuckChainsA E (iotaIfaceA E) n)
    (hPi : PiHeadStepTypedA E (iotaIfaceA E) n) :
    HopFacesA E (iotaIfaceA E) n := by
  intro Γ' A' N' r ls m b hΓ hA hN hres hbody _htr hlen hwf cN
  obtain ⟨hΓ'⟩ := hΓ
  obtain ⟨hb⟩ := hasTyA_memberBody_inst C hres hbody hlen hwf Γ'
  refine ⟨⟨hb⟩, ?_⟩
  obtain ⟨u, ⟨hX⟩⟩ := hasTyA_memberTy_inst C hres hlen hwf Γ'
  cases hz : isZero u with
  | false =>
    exact chainG C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) (C.hSg n)
      posValA_one hΓ' hb hPSC
      (hkey_of_sortTy C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓ'
        (hfamkey_of_propKey C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n)
          posValA_one) hX hz)
      (hfamkey_of_propKey C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n)
        posValA_one) hPi
  | true =>
    obtain ⟨k₀, hk⟩ := fund_selfg C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hSg n)
      posValA_one
      (propKeyA_holds C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one)
      hΓ' hb
    obtain ⟨R, hRK, _⟩ := hk k₀ (Nat.le_refl _)
    rw [LRTyA_eqg] at hRK
    obtain ⟨N'', hN'', hnN''⟩ := tyKAg_whnf hRK
    have hP'' := propKey_K1 C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n)
      posValA_one hΓ' hX hz hN'' hnN''
    obtain ⟨_, ⟨hN'ty⟩⟩ := whTyA_hasTy_end hA
    have hself := whTyA_of_hasTy hN'ty
    have hP' := (propKey_K3 C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n)
      posValA_one hΓ' cN hN'' hself hnN'' hN.1).1 hP''
    have hbN' : Nonempty (HasTyA E (iotaIfaceA E) n Γ'
        (instantiateLevelsA ls b) N') :=
      cN.elim fun c => ⟨hasTyA_of_tyConvA hb c⟩
    have hcv : Nonempty (ConvA E (iotaIfaceA E) n Γ'
        (instantiateLevelsA ls b) (instantiateLevelsA ls b) N') :=
      hbN'.elim fun t => ⟨.refl _ _ _ t⟩
    obtain ⟨Na, cha, hna, _⟩ := hPSC ⟨hΓ'⟩ hself hN hP' hbN' hbN' hcv
    exact ⟨Na, tyHRedStarA_retype (tyConvA_symm_ne cN) cha, hna⟩

/-- **`piHeadStepTypedA_major`** — the `major` arm of `PiHeadStepTypedA`,
    discharged (cc ruling on #6293): at a recursor spine `app f a` whose head
    does not step, whose group is neither unit nor struct, and whose ι refuses,
    a step in the major `a` is a typed step once `a`'s own step is typed at
    whatever type `a` is typed at (`hinner` — the discharge's recursive
    instance at the major argument). Mechanical, no ATR dependency:
    `hasTyA_app_gen` inverts the `Π`-typing; `tyHRedA_hasTy_right`/`tyHRedA_conv`
    turn the inner step into `a' : A` and `a ≡ a' : A`; `hasTyA_func0` moves
    that conversion under `instantiate0A`, giving `inst0 a' B ≡ inst0 a B`;
    `HasTyA.app` + `hasTyA_of_tyConvA` then produce `hrt`, and `TyHRedA.conv`
    retypes the whole step from `inst0 a B` back to the `Π` type. No sort guard
    needed — `major` works at any codomain sort. -/
theorem piHeadStepTypedA_major (C : AnnEnvA E) {n : Nat} {Γ : LCtxA}
    {f a a' : ExprA} {D : ExprA} {u : Level} {Ct : ExprA} {v : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (hrec : recAtMajorA E f = true) (hu : unitMinorA E f = none)
    (hs : structHeadA E f = false)
    (hf : hStepFnA E (iotaIfaceA E).fn Γ f = none)
    (hi : (iotaIfaceA E).fn (.app f a) = none)
    (ht : HasTyA E (iotaIfaceA E) n Γ (.app f a) (.pi D u Ct v))
    (hinner : ∀ {T : ExprA}, HasTyA E (iotaIfaceA E) n Γ a T →
      Nonempty (TyHRedA E (iotaIfaceA E) n Γ a a' T)) :
    Nonempty (TyHRedA E (iotaIfaceA E) n Γ (.app f a) (.app f a')
      (.pi D u Ct v)) := by
  obtain ⟨A, uB, B, vB, _w, ⟨hfTy⟩, ⟨ha⟩, ⟨hB⟩, _hTy, ⟨hTC⟩⟩ := hasTyA_app_gen ht
  obtain ⟨h⟩ := hinner ha
  have ha' := tyHRedA_hasTy_right h
  have hcv := tyHRedA_conv h
  have ⟨_, hwP⟩ := hasTyA_type_subst C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS
    (substTyA_id C.hE C.hI hΓ) hfTy
  rw [substA_id] at hwP
  obtain ⟨hAs⟩ := (hasTyA_pi_inv hwP).1
  have hBa := hasTyA_inst0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hB ha hAs
  have hBa' := hasTyA_inst0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hB ha' hAs
  have hconvB := hasTyA_func0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hB hcv hAs
  have hTC' : TyConvA E (iotaIfaceA E) n Γ (instantiate0A a' B) (instantiate0A a B) :=
    .of Γ _ _ vB vB vB hBa' (eqNA_refl vB) hBa (eqNA_refl vB) (.symm Γ _ _ _ hconvB)
  have happ' : HasTyA E (iotaIfaceA E) n Γ (.app f a') (instantiate0A a' B) :=
    .app Γ f a' A B uB vB vB hB hBa' hfTy ha'
  have hrt := hasTyA_of_tyConvA happ' hTC'
  exact ⟨TyHRedA.conv Γ _ _ _ _ (TyHRedA.major Γ f a a' A B A uB vB hrec hu hs hf
    hi h (.refl Γ A) hfTy hB hrt) hTC⟩

end Rcic.Declarative.Ann
