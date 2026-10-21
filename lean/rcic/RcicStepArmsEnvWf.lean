import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedValidity

namespace Rcic.Declarative

/-!
DT-010's `Step` arms at `EnvWfT` alone — one lemma per clean arm.

`oneStepSRT` (RcicDTMetaTypedSR.lean:485) discharges all six arms *in scope*
through the Ann bridge. This file splits the arms by what they actually need
syntactically, at `EnvWfT` only — the census-r3 follow-up's buildable item
(#6352, acted per cc).

| arm        | route                                            | status |
|------------|--------------------------------------------------|--------|
| zetaLocal  | `ctxWfTLookupValueAt` + `hasTyTInv_bvar`         | PAID `step_zetaLocal_srT` |
| delta      | `envWfT_bodyTyped` + `hasTyTInv_const`           | PAID `step_delta_srT` |
| lit        | `hasTyTInv_lit` + `LiteralExpansion`             | PAID `step_lit_srT` — no env premise at all |
| zeta       | `hasTyTInv_letE` + the `SubstLetT` front         | PAID `step_zeta_srT` — front stays named until #6329 lands |
| beta       | legacy strong Π row                            | REFUTED CONTRACT — `PiRowInjT`; see `RcicPiRowInjTRefutation` |
| iota       | needs a syntactic iota-SR package                | not here — DT-019's own measurement |

Premise discipline: `step_beta_srT` consumes `PiRowInjT` explicitly and
`step_zeta_srT` consumes `SubstLetT` explicitly — fronts are named premises,
never assumed at `EnvWfT` alone. Correction (cc, 2026-10-13): #6293's Loop
tooth refutes the semantic routes (`EnvSemA`, `PropKeyA ∧ EnvSemAg`, PSet), not
the Π row; piRow is open. The unguarded `PiRowInjT` below is itself uninhabited
at every `EnvWfT` env (`no_piRowInjT_of_envWfT`, `RcicPiRowInjTRefutation`), so the
β arm is restated at the row (`step_beta_srT_rows`, `RcicDT1011Rows`); the target
is `TypedRowsWf.piRow`. `closure_claim = 0`.
-/

/-- **W-F05b-PiRow** at the row the β arm actually consumes: from a type-level
    conversion between Π types, the domain conversion at a sort and the
    codomain conversion under the binder at a sort. This is TyConvT-level
    Π-injectivity — a named premise, never assumed silently.

    This unguarded contract is uninhabited at every `EnvWfT E`, as proved by
    `no_piRowInjT_of_envWfT` in `RcicPiRowInjTRefutation`. `TyConvT.refl`
    admits an ill-typed Pi, but this front would produce typed component
    conversions. The definition and its conditional consumers are retained
    unchanged; it must not be treated as an inhabitable closure obligation.
    This does not refute the `TypedRowsWf.piRow` chain-output interface or
    Pi injectivity with typed inputs. -/
def PiRowInjT (E : ResolvedEnv) : Type :=
  ∀ {n : Nat} {Γ : LCtx} {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Σ' (u v : Level),
      Nonempty (ConvT E n Γ A A' (.sort u)) ×'
      Nonempty (ConvT E n (LocalDecl.assumption A :: Γ) B B' (.sort v))

/-- ζ-local at `EnvWfT`: the looked-up value is typed at the index's stored
    type; the context walk supplies that typing and the lookup pin, and
    inversion supplies the type conversion. No scope, no env premise beyond
    closure. -/
def step_zetaLocal_srT (hW : EnvWfT E) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {i : Nat} {v S : Expr Nat} (hlv : lookupValue Γ i = some v)
    (h : HasTyT E n Γ (.bvar i) S) :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ v B ×' TyConvT E n Γ S B) := by
  obtain ⟨A0, hlk, hcv⟩ := hasTyTInv_bvar h rfl
  obtain ⟨A_v, hvty, hlk'⟩ :=
    ctxWfTLookupValueAt (envClosed_of_envWfT hW) hΓ i v hlv
  have hEq : some A0 = some A_v := hlk.symm.trans hlk'
  injection hEq with hAeq
  rw [← hAeq] at hvty
  exact ⟨A0, hvty, TyConvT.symmT hcv⟩

/-- δ at `EnvWfT`: the member's stored body typing, relocated into `Γ` by
    `envWfT_bodyTyped` (the arity-0 tripwire collapses the level list); the
    type index converts by inversion. No scope. -/
def step_delta_srT (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b S : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (h : HasTyT E n Γ (.const r ls) S) :
    Nonempty (Σ' (B : Expr Nat),
      HasTyT E n Γ (instantiateLevels ls b) B ×' TyConvT E n Γ S B) := by
  obtain ⟨m', hres', hlen, _hwf, hcv⟩ := hasTyTInv_const h rfl
  have hmeq : some m = some m' := hres.symm.trans hres'
  injection hmeq with hmeq'
  subst hmeq'
  exact ⟨_, envWfT_bodyTyped (n := n) (Γ := Γ) hW hres hbody hlen,
    TyConvT.symmT hcv⟩

/-- literal expansion at `EnvWfT`: the expansion's own typing is already the
    redex typing — `hasTyTInv_lit` reads it off. No env premise at all. -/
def step_lit_srT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp S : Expr Nat}
    (hlexp : LiteralExpansion t exp) (h : HasTyT E n Γ (.lit t) S) :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ exp B ×' TyConvT E n Γ S B) := by
  obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit (t := t) h rfl
  cases hlexp
  exact ⟨T', hnat, TyConvT.symmT hcv⟩

/-- ζ at `EnvWfT`, fronted: `hasTyTInv_letE` reads the let typing, the named
    `SubstLetT` front (L1, dttyped lane — #6329) substitutes the value through
    body and type. The front is consumed exactly here, nowhere else. -/
def step_zeta_srT {n : Nat} (hSL : SubstLetT E n) {Γ : LCtx}
    {A v b S : Expr Nat} (h : HasTyT E n Γ (.letE A v b) S) :
    Nonempty (Σ' (B : Expr Nat),
      HasTyT E n Γ (instantiate0 v b) B ×' TyConvT E n Γ S B) := by
  obtain ⟨_u, B_let, _hAty, hv, hb, hcv⟩ := hasTyTInv_letE h rfl
  exact ⟨_, hSL hv hb, TyConvT.symmT hcv⟩

/-- β at `EnvWfT`, WALL-FRONTED: inverting the application gives the lam's
    own Π type versus the application's; retyping the argument needs the
    domain leg and the instantiated codomain needs the codomain leg — both
    are `PiRowInjT` (W-F05b-PiRow), consumed here and only here. -/
def step_beta_srT (hW : EnvWfT E) (hrow : PiRowInjT E) {n : Nat} {Γ : LCtx}
    {A0 body arg S : Expr Nat}
    (h : HasTyT E n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (Σ' (B : Expr Nat),
      HasTyT E n Γ (instantiate0 arg body) B ×' TyConvT E n Γ S B) := by
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨_u0, B_lam, _hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨uA, uB, ⟨hdom⟩, ⟨hcod⟩⟩ := hrow hcv_lam
  have ha' : HasTyT E n Γ arg A0 :=
    HasTyT.conv _ _ _ _ uA ha (ConvT.symm _ _ _ _ hdom)
  have hsub := hasTyT_subst0_of_envWfT hW hbody ha'
  have hcod' : ConvT E n Γ (instantiate0 arg B_lam) (instantiate0 arg B1)
      (.sort uB) :=
    convT_subst0_of_envWfT hW hcod ha'
  exact ⟨_, hsub,
    .trans _ _ _ _ (TyConvT.symmT hcv) (TyConvT.symmT (.of _ _ _ _ hcod'))⟩

/-! ### pins — each arm consumed at a concrete fixture -/

/-- PIN (δ): the EnvWfT delta arm on `pinDefEnvU`'s definition member — the
    same redex `pin_DT010T_delta` exercises in scope, here without it. -/
theorem pin_step_delta_srT {n : Nat} :
    ∃ B, Nonempty (HasTyT pinDefEnvU n []
        (instantiateLevels [] (.sort .zero)) B) ∧
      Nonempty (TyConvT pinDefEnvU n []
        (instantiateLevels [] (.sort (.succ .zero))) B) :=
  (step_delta_srT pinDefEnvUWfT (r := 4)
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    rfl rfl (pinDeltaConst n)).elim
    fun ⟨B, hty, hcv⟩ => ⟨B, ⟨hty⟩, ⟨hcv⟩⟩

/-- the single-let context the ζ-local pin runs in. -/
def pinZetaLocalCtx : LCtx := [.letBinding (.const 0 []) (.const 1 [])]

def pinZetaLocalCtxWf : CtxWfT natEnvU 1 pinZetaLocalCtx :=
  CtxWfT.letBinding [] (.const 0 []) (.succ .zero) (.const 1 [])
    CtxWfT.nil pinIotaFamTy pinIotaZeroTy

/-- PIN (ζ-local): `bvar 0` in a `let N := zero` context unfolds to the stored
    value — `EnvWfT` only, no scope bridge. -/
theorem pin_step_zetaLocal_srT :
    ∃ B, Nonempty (HasTyT natEnvU 1 pinZetaLocalCtx
        (lift 0 1 (.const 1 [])) B) ∧
      Nonempty (TyConvT natEnvU 1 pinZetaLocalCtx (.const 0 []) B) :=
  (step_zetaLocal_srT natEnvUWfT pinZetaLocalCtxWf
    (i := 0) (v := lift 0 1 (.const 1 [])) rfl
    (HasTyT.bvar _ 0 (lift 0 1 (.const 0 [])) rfl)).elim
    fun ⟨B, hty, hcv⟩ => ⟨B, ⟨hty⟩, ⟨hcv⟩⟩

/-- PIN (lit): the literal `0` expands to `natExpand 0` typed at `N` —
    the arm needs no env premise at all. -/
theorem pin_step_lit_srT :
    ∃ B, Nonempty (HasTyT natEnvU 1 [] (natExpand 0) B) ∧
      Nonempty (TyConvT natEnvU 1 [] (.const 0 []) B) :=
  (step_lit_srT (LiteralExpansion.of 0)
    (HasTyT.lit [] 0 (.const 0 []) pinIotaZeroTy)).elim
    fun ⟨B, hty, hcv⟩ => ⟨B, ⟨hty⟩, ⟨hcv⟩⟩

/-- the let-redex the ζ pin runs on: `let x : Sort 1 := def4 in x`. -/
def pinLetTy (n : Nat) :
    HasTyT pinDefEnvU n [] (.letE (.sort (.succ .zero)) (.const 4 []) (.bvar 0))
      (.sort (.succ .zero)) :=
  HasTyT.letE [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.const 4 [])
    _ (.bvar 0) (HasTyT.sort [] (.succ .zero)) (pinDeltaConst n)
    (HasTyT.bvar _ 0 (lift 0 1 (.sort (.succ .zero))) rfl)

/-- PIN (ζ), fronted: consumes the named `SubstLetT` front — when #6329 lands,
    this pin discharges with no further work. -/
theorem pin_step_zeta_srT {n : Nat} (hSL : SubstLetT pinDefEnvU n) :
    ∃ B, Nonempty (HasTyT pinDefEnvU n []
        (instantiate0 (.const 4 []) (.bvar 0)) B) ∧
      Nonempty (TyConvT pinDefEnvU n [] (.sort (.succ .zero)) B) :=
  (step_zeta_srT hSL (pinLetTy n)).elim
    fun ⟨B, hty, hcv⟩ => ⟨B, ⟨hty⟩, ⟨hcv⟩⟩

/-- PIN: DT-012T consumed at `pinDefEnvU` — one term (`Sort 0`) at two
    convertible-but-distinct types (`Sort 1` and a ζ-redex of it) yields the
    type conversion. In-scope, per the theorem; the pin exercises the seal
    registration, not the EnvWfT claim. -/
theorem pin_DT012T_letE_sort1 {n : Nat} :
    Nonempty (TyConvT pinDefEnvU n []
      (.sort (.succ .zero))
      (.letE (.sort (.succ .zero)) (.const 4 []) (.sort (.succ .zero)))) :=
  DT012T_type_uniqueness pinDefEnvUWfT pinDefEnvU_inScope CtxWfT.nil
    (HasTyT.sort [] .zero)
    (HasTyT.conv _ _ _ _ _ (HasTyT.sort [] .zero)
      (ConvT.symm _ _ _ _
        (ConvT.zeta [] (.sort (.succ .zero)) (.const 4 [])
          (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
          (.succ (.succ .zero))
          (HasTyT.sort [] (.succ .zero)) (pinDeltaConst n)
          (HasTyT.sort _ (.succ .zero)))))

/-- the wall's interface is exactly the two-sort fragment — a definitional
    shape pin; if `PiRowInjT` ever narrows or drifts silently this stops
    compiling (same discipline as `pin_SubstLetT_shape`). -/
theorem pin_PiRowInjT_shape (E : ResolvedEnv) :
    PiRowInjT E = ∀ {n : Nat} {Γ : LCtx} {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Σ' (u v : Level),
        Nonempty (ConvT E n Γ A A' (.sort u)) ×'
        Nonempty (ConvT E n (LocalDecl.assumption A :: Γ) B B' (.sort v)) :=
  rfl

end Rcic.Declarative
