import rcic.RcicClassCRevealed
import rcic.RcicTypedConvTerm
import rcic.RcicKernelRowsAssembly

/-!
# cc-classc — row 3 at the class-(c) fixture `RI`, from rows 1–2

The revealed-index eliminator of `RI` internalises the injectivity of its own family.

* §1 `ri_inj_internal`. Take any context, `x x' : Sort 0` and a type-conversion chain
  `RI x ≡* RI x'`. Then `x ≡ x' : Sort 0` holds in `ConvT` itself. The steps: retype `mk x` along
  the chain, ι at `rec M₀ m₀ x' (mk x)` (the field `x` is read off the constructor), `irr` with
  `mk x'`, ι again (the field `x'`), and β on `m₀ := λ Y. Y`. The motive is
  `M₀ := λ Y _. Sort 0`. No row is used.
* §2 `ri_spine`. A typing of `RI.{ls} xs` is read with `PiRowField` and sort/Π disjointness
  (`SortPiDisj`, the shape that `not_tyConvT_sort_pi_of_allBelowScoped` supplies): `ls = []`, and
  either `xs = []` at a type `≡* Π (x : Sort 0), Sort 0`, or `xs = [x]` with `x : Sort 0` at a type
  `≡* Sort 0`.
* §3 the consequences at `riEnv`, for every level bound `n`:
  - `famRelevantSlotConv_ri : PiRowField riEnv n → SortPiDisj riEnv n → FamRelevantSlotConv riEnv n`;
  - `famAppRow_ri`: `TypedRowsWf.famAppRow`'s exact statement from the same two premises;
  - `typedRowsWf_ri_of_rows12`: `TypedRowsWf riEnv n` from rows 1–2 and `SortPiDisj` alone.

So at this class-(c) environment the catalogued argument-comparison input
(`FamRelevantSlotConv`, `W-F8-FAMAPP-ARG-COMPARISON`) is not an extra obligation, and row 3 is no
extra obligation either. What is left at `RI` is Π-injectivity (row 2, equivalently
`PiConvValleyData` under the landed adapters) plus sort/Π disjointness. `closure_claim = 0`.
-/

namespace Rcic.Syn.ClassC

set_option maxRecDepth 8192

open Rcic.Declarative

/-! ## §0 small calculus -/

theorem inst0_lift1 (v y : Expr Nat) : instantiate 0 v (lift 0 1 y) = y := by
  rw [instantiate_lift_cancel 1 0 0 v (Nat.le_refl _) (by decide)]
  exact lift_zero_idx 0 y

/-- sort/Π disjointness at a level bound, the shape the landed pack supplies. -/
def SortPiDisj (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {l : Level} {A B : Expr Nat},
    TyConvT E n Γ (.sort l) (.pi A B) → False

/-! ## §1 internal injectivity of `RI` -/

section internal

variable {n : Nat} {Γ : LCtx}

/-- `RI a`. -/
def riApp (a : Expr Nat) : Expr Nat := .app (.const 0 []) a
/-- `mk a`. -/
def mkApp (a : Expr Nat) : Expr Nat := .app (.const 1 []) a

def hS0 (Γ : LCtx) : HasTyT riEnv n Γ (.sort .zero) (.sort (.succ .zero)) := .sort Γ .zero

def hRIApp {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    HasTyT riEnv n Γ (riApp a) (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 0 [] riFam rfl rfl rfl) ha

def hMkApp {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    HasTyT riEnv n Γ (mkApp a) (riApp a) :=
  .app _ _ _ _ _ (.const _ 1 [] riCtor rfl rfl rfl) ha

/-- the motive `λ (Y : Sort 0) (_ : RI Y). Sort 0`. -/
def riM0 : Expr Nat := .lam (.sort .zero) (.lam (riApp (.bvar 0)) (.sort .zero))

def hM0Body (Γ : LCtx) :
    HasTyT riEnv n (.assumption (.sort .zero) :: Γ) (.lam (riApp (.bvar 0)) (.sort .zero))
      (.pi (riApp (.bvar 0)) (.sort (.succ .zero))) :=
  .lam _ _ .zero _ _ (hRIApp (.bvar _ 0 _ rfl)) (.sort _ .zero)

def hM0 (Γ : LCtx) :
    HasTyT riEnv n Γ riM0 (.pi (.sort .zero) (.pi (riApp (.bvar 0)) (.sort (.succ .zero)))) :=
  .lam Γ _ (.succ .zero) _ _ (hS0 Γ) (hM0Body Γ)

/-- `M₀ a t ≡ Sort 0 : Sort 1` by two β. -/
def m0Beta {a t : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero))
    (ht : HasTyT riEnv n Γ t (riApp a)) :
    ConvT riEnv n Γ (.app (.app riM0 a) t) (.sort .zero) (.sort (.succ .zero)) :=
  .trans Γ _ (.app (.lam (riApp a) (.sort .zero)) t) _ _
    (.app Γ (.app riM0 a) (.lam (riApp a) (.sort .zero)) t t
      (riApp a) (.sort (.succ .zero))
      (.beta Γ (.sort .zero) (.lam (riApp (.bvar 0)) (.sort .zero)) a
        (.pi (riApp (.bvar 0)) (.sort (.succ .zero))) (.succ .zero)
        (hS0 Γ) (hM0Body Γ) ha)
      (.refl Γ t _ ht))
    (.beta Γ (riApp a) (.sort .zero) t (.sort (.succ .zero)) .zero
      (hRIApp ha) (.sort _ .zero) ht)

/-- the minor `λ (Y : Sort 0). Y`. -/
def riM0m : Expr Nat := .lam (.sort .zero) (.bvar 0)

/-- `m₀ : Π (Y : Sort 0), M₀ Y (mk Y)`. -/
def hm0 (Γ : LCtx) :
    HasTyT riEnv n Γ riM0m
      (.pi (.sort .zero) (.app (.app riM0 (.bvar 0)) (mkApp (.bvar 0)))) :=
  .conv _ _ _ _ _
    (.lam Γ _ (.succ .zero) _ _ (hS0 Γ) (.bvar _ 0 _ rfl))
    (.pi Γ (.sort .zero) (.sort .zero) (.sort .zero)
      (.app (.app riM0 (.bvar 0)) (mkApp (.bvar 0))) (.succ .zero) (.succ .zero)
      (.refl _ _ _ (hS0 Γ))
      (.symm _ _ _ _ (m0Beta (.bvar _ 0 _ rfl) (hMkApp (.bvar _ 0 _ rfl)))))

/-- `m₀ a ≡ a : Sort 0`. -/
def m0AppBeta {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    ConvT riEnv n Γ (.app riM0m a) a (.sort .zero) :=
  .beta Γ (.sort .zero) (.bvar 0) a (.sort .zero) (.succ .zero) (hS0 Γ) (.bvar _ 0 _ rfl) ha

def hm0App {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    HasTyT riEnv n Γ (.app riM0m a) (.sort .zero) :=
  .conv _ _ _ _ _ (.app _ _ _ _ _ (hm0 Γ) ha) (m0Beta ha (hMkApp ha))

/-- `rec.{1} M₀ m₀`. -/
def riRecM0m : Expr Nat := foldApps (.const 2 [.succ .zero]) [riM0, riM0m]

def hRecM0m (Γ : LCtx) :
    HasTyT riEnv n Γ riRecM0m
      (.pi (.sort .zero) (.pi (riApp (.bvar 0)) (.app (.app riM0 (.bvar 1)) (.bvar 0)))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 2 [.succ .zero] riRec rfl rfl rfl) (hM0 Γ))
    (hm0 Γ)

/-- `rec M₀ m₀ y : Π (h : RI y), M₀ y h`. -/
def hRecM0mY {y : Expr Nat} (hy : HasTyT riEnv n Γ y (.sort .zero)) :
    HasTyT riEnv n Γ (.app riRecM0m y)
      (.pi (riApp y) (.app (.app riM0 (lift 0 1 y)) (.bvar 0))) :=
  .app _ _ _ _ _ (hRecM0m Γ) hy

/-- `rec M₀ m₀ y q : Sort 0`. -/
def hRecFull {y q : Expr Nat} (hy : HasTyT riEnv n Γ y (.sort .zero))
    (hq : HasTyT riEnv n Γ q (riApp y)) :
    HasTyT riEnv n Γ (.app (.app riRecM0m y) q) (.sort .zero) := by
  have h := HasTyT.app _ _ _ _ _ (hRecM0mY hy) hq
  have hT : instantiate0 q (.app (.app riM0 (lift 0 1 y)) (.bvar 0)) =
      .app (.app riM0 y) q := by
    show Expr.app (.app (instantiate 0 q riM0) (instantiate 0 q (lift 0 1 y))) q = _
    rw [inst0_lift1]; rfl
  rw [hT] at h
  exact .conv _ _ _ _ _ h (m0Beta hy hq)

/-- the ι witness at index `y` and field `x`. -/
def riWG (y x : Expr Nat) : IotaWitness riEnv :=
  { riW with
    ls := [.succ .zero]
    preMajor := [riM0, riM0m, y]
    fields := [x]
    minor := riM0m
    hpre := rfl
    hminor := rfl
    hlsLen := rfl
    hctorAfter := rfl }

/-- ι: `rec M₀ m₀ y (mk x) ≡ m₀ x : Sort 0`. -/
def riIotaG {x y : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hy : HasTyT riEnv n Γ y (.sort .zero)) (hq : HasTyT riEnv n Γ (mkApp x) (riApp y)) :
    ConvT riEnv n Γ (.app (.app riRecM0m y) (mkApp x)) (.app riM0m x) (.sort .zero) :=
  .iota _ _ _ _ (.of (riWG y x)) (hRecFull hy hq) (hm0App hx)

/-- **`RI` is injective inside `ConvT`, through its own recursor.** -/
def ri_inj_internal {x x' : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hx' : HasTyT riEnv n Γ x' (.sort .zero)) (hc : TyConvT riEnv n Γ (riApp x) (riApp x')) :
    ConvT riEnv n Γ x x' (.sort .zero) :=
  let hq : HasTyT riEnv n Γ (mkApp x) (riApp x') := hasTyT_of_tyConv (hMkApp hx) hc
  let hq' : HasTyT riEnv n Γ (mkApp x') (riApp x') := hMkApp hx'
  -- rec M₀ m₀ x' (mk x) ≡ rec M₀ m₀ x' (mk x'), by irr under app
  let hcong : ConvT riEnv n Γ (.app (.app riRecM0m x') (mkApp x))
      (.app (.app riRecM0m x') (mkApp x')) (.sort .zero) := by
    have h := ConvT.app Γ (.app riRecM0m x') (.app riRecM0m x') (mkApp x) (mkApp x')
      (riApp x') (.app (.app riM0 (lift 0 1 x')) (.bvar 0))
      (.refl _ _ _ (hRecM0mY hx')) (.irr _ _ _ _ (hRIApp hx') hq hq')
    have hT : instantiate0 (mkApp x) (.app (.app riM0 (lift 0 1 x')) (.bvar 0)) =
        .app (.app riM0 x') (mkApp x) := by
      show Expr.app (.app (instantiate 0 (mkApp x) riM0)
        (instantiate 0 (mkApp x) (lift 0 1 x'))) (mkApp x) = _
      rw [inst0_lift1]; rfl
    rw [hT] at h
    exact .tyConv _ _ _ _ _ (.succ .zero) h (m0Beta hx' hq)
  .trans _ _ _ _ _ (.symm _ _ _ _ (m0AppBeta hx))
    (.trans _ _ _ _ _ (.symm _ _ _ _ (riIotaG hx hx' hq))
      (.trans _ _ _ _ _ hcong
        (.trans _ _ _ _ _ (riIotaG hx' hx' hq') (m0AppBeta hx'))))

end internal

/-! ## §1b the recursor is definable

`rec ≡ λ M m X h. m X` at `rec`'s own type, in the empty context: four η steps and four `lam`
congruences around `riConvK`. So the group adds no conversion shape beyond its axiom fragment
(`RI`, `mk`); every redex `rec M m X p` is `m X`, for every proof `p`. -/

/-- `λ M m X h. m X`. -/
def riRecLam : Expr Nat :=
  .lam riMotTy (.lam riMinTy (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
    (.app (.bvar 2) (.bvar 1)))))

/-- the scopes `[X, m, M]`, `[m, M]`, `[M]`. -/
def riCtx3 : LCtx := [.assumption (.sort .zero), .assumption riMinTy, .assumption riMotTy]
def riCtx2 : LCtx := [.assumption riMinTy, .assumption riMotTy]
def riCtx1 : LCtx := [.assumption riMotTy]

/-- `rec M m X`, `rec M m`, `rec M`, `rec` at their scopes. -/
def riF3 : Expr Nat := foldApps riRecHead [.bvar 2, .bvar 1, .bvar 0]
def riF2 : Expr Nat := foldApps riRecHead [.bvar 1, .bvar 0]
def riF1 : Expr Nat := .app riRecHead (.bvar 0)

def riDomH : Expr Nat := .app (.const 0 []) (.bvar 0)

def riF3Ty : HasTyT riEnv 1 riCtx3 riF3 (.pi riDomH riTyL) := riTy _ _ _ rfl
def riF2Ty : HasTyT riEnv 1 riCtx2 riF2 (.pi (.sort .zero) (.pi riDomH riTyL)) :=
  riTy _ _ _ rfl
def riF1Ty : HasTyT riEnv 1 riCtx1 riF1
    (.pi riMinTy (.pi (.sort .zero) (.pi riDomH riTyL))) := riTy _ _ _ rfl
def riF0Ty : HasTyT riEnv 1 [] riRecHead riRecTy := riTy _ _ _ rfl

def riDomHTy : HasTyT riEnv 1 riCtx3 riDomH (.sort .zero) := riTy _ _ _ rfl
def riMinTyTy : HasTyT riEnv 1 riCtx1 riMinTy (.sort (.imax (.succ .zero) (.param 0))) :=
  riTy _ _ _ rfl
def riMotTyTy : HasTyT riEnv 1 [] riMotTy
    (.sort (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))) := riTy _ _ _ rfl

/-- level 4: `λ h. m X ≡ rec M m X` at `[X, m, M]`. -/
def riDef4 : ConvT riEnv 1 riCtx3 (.lam riDomH riRhs) riF3 (.pi riDomH riTyL) :=
  .trans _ _ (.lam riDomH riLhs) _ _
    (.lam _ _ _ _ _ _ .zero (.refl _ _ _ riDomHTy) (.symm _ _ _ _ riConvK))
    (.eta _ riF3 riDomH riTyL riF3Ty)

/-- level 3: `λ X h. m X ≡ rec M m` at `[m, M]`. -/
def riDef3 : ConvT riEnv 1 riCtx2 (.lam (.sort .zero) (.lam riDomH riRhs)) riF2
    (.pi (.sort .zero) (.pi riDomH riTyL)) :=
  .trans _ _ (.lam (.sort .zero) riF3) _ _
    (.lam _ _ _ _ _ _ (.succ .zero) (.refl _ _ _ (.sort _ .zero)) riDef4)
    (.eta _ riF2 (.sort .zero) (.pi riDomH riTyL) riF2Ty)

/-- level 2: `λ m X h. m X ≡ rec M` at `[M]`. -/
def riDef2 : ConvT riEnv 1 riCtx1 (.lam riMinTy (.lam (.sort .zero) (.lam riDomH riRhs))) riF1
    (.pi riMinTy (.pi (.sort .zero) (.pi riDomH riTyL))) :=
  .trans _ _ (.lam riMinTy riF2) _ _
    (.lam _ _ _ _ _ _ _ (.refl _ _ _ riMinTyTy) riDef3)
    (.eta _ riF1 riMinTy (.pi (.sort .zero) (.pi riDomH riTyL)) riF1Ty)

/-- **`RI`'s recursor is definable:** `λ M m X h. m X ≡ rec : riRecTy`. -/
def riRec_definable : ConvT riEnv 1 [] riRecLam riRecHead riRecTy :=
  .trans _ _ (.lam riMotTy riF1) _ _
    (.lam _ _ _ _ _ _ _ (.refl _ _ _ riMotTyTy) riDef2)
    (.eta _ riRecHead riMotTy (.pi riMinTy (.pi (.sort .zero) (.pi riDomH riTyL))) riF0Ty)

/-! ## §2 reading a typing of `RI.{ls} xs` with rows 1–2 -/

theorem riEnv_members_inductive {r : Nat} {m : CheckedMember} (hm : riEnv.members r = some m)
    (hind : m.mclass = .inductiveM) : r = 0 ∧ m = riFam := by
  by_cases h2 : r = 2
  · subst h2; cases hm; cases hind
  by_cases h1 : r = 1
  · subst h1; cases hm; cases hind
  by_cases h0 : r = 0
  · subst h0; cases hm; exact ⟨rfl, rfl⟩
  · simp [riEnv, riCtorEnv, riFamEnv, extendEnv, emptyEnv, h0, h1, h2] at hm

/-- the spine reading. -/
theorem ri_spine {n : Nat} (hpi : PiRowField riEnv n) (hsp : SortPiDisj riEnv n)
    {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) :
    ∀ {e T : Expr Nat}, HasTyT riEnv n Γ e T → ∀ {ls : List Level} {xs : List (Expr Nat)},
      appsSpine e = (.const 0 ls, xs) →
      ls = [] ∧
        ((xs = [] ∧ Nonempty (TyConvT riEnv n Γ T (.pi (.sort .zero) (.sort .zero)))) ∨
         (∃ x, xs = [x] ∧ Nonempty (TyConvT riEnv n Γ T (.sort .zero)) ∧
           Nonempty (HasTyT riEnv n Γ x (.sort .zero))))
  | _, _, .sort _ _, _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, _, he => by cases he
  | _, _, .const _ r ls' m hres hlen _, ls, xs, he => by
      simp only [appsSpine, Prod.mk.injEq, Expr.const.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      cases hres
      have : ls' = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      exact ⟨rfl, .inl ⟨rfl, ⟨.refl _ _⟩⟩⟩
  | _, _, .conv _ _ A B u D hc, ls, xs, he => by
      obtain ⟨hls, h⟩ := ri_spine hpi hsp hΓ D he
      refine ⟨hls, ?_⟩
      have hBA : TyConvT riEnv n Γ B A := (TyConvT.of _ _ _ u hc).symmT
      rcases h with ⟨hx, ⟨c⟩⟩ | ⟨x, hx, ⟨c⟩, hxt⟩
      · exact .inl ⟨hx, ⟨.trans _ _ _ _ hBA c⟩⟩
      · exact .inr ⟨x, hx, ⟨.trans _ _ _ _ hBA c⟩, hxt⟩
  | _, _, .app _ f a A B hf ha, ls, xs, he => by
      simp only [appsSpine] at he
      rcases hsf : appsSpine f with ⟨hd, xs₀⟩
      rw [hsf] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hls, h⟩ := ri_spine hpi hsp hΓ hf hsf
      refine ⟨hls, .inr ⟨a, ?_, ?_⟩⟩
      · rcases h with ⟨rfl, _⟩ | ⟨x, rfl, ⟨c⟩, _⟩
        · rfl
        · exact (hsp hΓ c.symmT).elim
      · rcases h with ⟨rfl, ⟨c⟩⟩ | ⟨x, rfl, ⟨c⟩, _⟩
        · obtain ⟨⟨cA⟩, ⟨cB⟩⟩ := hpi hΓ c
          exact ⟨⟨tyConvT_subst0_of_envWfT riEnvWfT ha cB⟩, ⟨hasTyT_of_tyConv ha cA⟩⟩
        · exact (hsp hΓ c.symmT).elim

/-- the right end of a type-conversion chain from a sort-typed left end is sort-typed. -/
def tyConvT_right_typed {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) :
    {X Y : Expr Nat} → {w : Level} → HasTyT E n Γ X (.sort w) → TyConvT E n Γ X Y →
      Σ' w', HasTyT E n Γ Y (.sort w')
  | _, _, w, hX, .refl _ _ => ⟨w, hX⟩
  | _, _, _, _, .of _ _ _ u c => ⟨u, (NativeValleys.convEnds hW hΓ c).2.1⟩
  | _, _, _, hX, .trans _ _ _ _ c₁ c₂ =>
      let ⟨_, hM⟩ := tyConvT_right_typed hW hΓ hX c₁
      tyConvT_right_typed hW hΓ hM c₂

/-! ## §3 row 3 and the argument-comparison input at `riEnv` -/

/-- both ends of a family conversion at `RI` are single applications with typed arguments. -/
theorem ri_famApp_shape {n : Nat} (hpi : PiRowField riEnv n) (hsp : SortPiDisj riEnv n)
    {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {w : Level} (hty : HasTyT riEnv n Γ (foldApps (.const 0 ls) xs) (.sort w))
    (h : TyConvT riEnv n Γ (foldApps (.const 0 ls) xs) (foldApps (.const 0 ls') xs')) :
    ∃ x x', ls = [] ∧ ls' = [] ∧ xs = [x] ∧ xs' = [x'] ∧
      Nonempty (HasTyT riEnv n Γ x (.sort .zero)) ∧
      Nonempty (HasTyT riEnv n Γ x' (.sort .zero)) := by
  obtain ⟨hls, hL⟩ := ri_spine hpi hsp hΓ hty (appsSpine_foldApps_const 0 ls xs)
  obtain ⟨w', hty'⟩ := tyConvT_right_typed riEnvWfT hΓ hty h
  obtain ⟨hls', hR⟩ := ri_spine hpi hsp hΓ hty' (appsSpine_foldApps_const 0 ls' xs')
  rcases hL with ⟨_, ⟨c⟩⟩ | ⟨x, rfl, _, ⟨hx⟩⟩
  · exact (hsp hΓ c).elim
  rcases hR with ⟨_, ⟨c⟩⟩ | ⟨x', rfl, _, ⟨hx'⟩⟩
  · exact (hsp hΓ c).elim
  exact ⟨x, x', hls, hls', rfl, rfl, ⟨hx⟩, ⟨hx'⟩⟩

open Rcic.Declarative.KernelRowsAssembly in
/-- **The argument-comparison input holds at `RI`, from row 2 and sort/Π disjointness.** -/
theorem famRelevantSlotConv_ri {n : Nat} (hpi : PiRowField riEnv n) (hsp : SortPiDisj riEnv n) :
    FamRelevantSlotConv riEnv n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty h
  obtain ⟨rfl, rfl⟩ := riEnv_members_inductive hm hind
  obtain ⟨x, x', rfl, rfl, rfl, rfl, ⟨hx⟩, ⟨hx'⟩⟩ := ri_famApp_shape hpi hsp hΓ hty h
  intro i y y' d u hy hy' hd _ _
  cases i with
  | zero =>
      cases hy; cases hy'; cases hd
      exact ⟨ri_inj_internal hx hx' h⟩
  | succ i => cases hd

/-- **Row 3 at `RI`, from row 2 and sort/Π disjointness** (`TypedRowsWf.famAppRow`'s statement). -/
theorem famAppRow_ri {n : Nat} (hpi : PiRowField riEnv n) (hsp : SortPiDisj riEnv n)
    {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : riEnv.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT riEnv n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT riEnv n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT riEnv n Γ (instantiateLevels ls m.mtype) xs xs' := by
  obtain ⟨rfl, rfl⟩ := riEnv_members_inductive hm hind
  obtain ⟨x, x', rfl, rfl, rfl, rfl, ⟨hx⟩, ⟨hx'⟩⟩ := ri_famApp_shape hpi hsp hΓ hty h
  exact ⟨trivial, rfl, .cons _ _ _ _ _ _ ⟨ri_inj_internal hx hx' h⟩ (.nil _)⟩

/-- **All three rows at `RI`, from rows 1–2 and sort/Π disjointness.** -/
theorem typedRowsWf_ri_of_rows12 {n : Nat}
    (hsort : ∀ {Γ : LCtx}, CtxWfT riEnv n Γ → ∀ {u v : Level},
      TyConvT riEnv n Γ (.sort u) (.sort v) → eqN u v)
    (hpi : PiRowField riEnv n) (hsp : SortPiDisj riEnv n) : TypedRowsWf riEnv n where
  sortRow := hsort
  piRow := hpi
  famAppRow := @fun _ hΓ _ _ _ _ _ _ _ hm hind hty h => famAppRow_ri hpi hsp hΓ hm hind hty h

end Rcic.Syn.ClassC

#print axioms Rcic.Syn.ClassC.ri_inj_internal
#print axioms Rcic.Syn.ClassC.riRec_definable
#print axioms Rcic.Syn.ClassC.ri_spine
#print axioms Rcic.Syn.ClassC.famRelevantSlotConv_ri
#print axioms Rcic.Syn.ClassC.famAppRow_ri
#print axioms Rcic.Syn.ClassC.typedRowsWf_ri_of_rows12
