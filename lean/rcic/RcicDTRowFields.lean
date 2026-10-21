import rcic.RcicDT021Rows

/-!
# DT census interface refactors — two-field DT-012 and sort-only DT-021

`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §9.2/§9.4 (docs PR
#7515; lane `pirow-D-census`). `closure_claim = 0`.

Interface refactors only: the census status does not change until the
native rows exist (§9.5). Both landed carriers stay untouched; these are
NEW theorems taking the consumed `TypedRowsWf` fields as separate
arguments so a native `sortRow`/`piRow` producer can feed them directly.

- `DT012T_type_uniqueness_of_sortRow_piRow` — the `RcicDT008Equiv`
  DT-012 proof structure (L192–236) parameterized on the `sortRow` and
  `piRow` fields alone: `sortRow` collapses the sort chains at the `.pi`
  arm, `piRow` injects the Π chain at the `.app` arm, and `famAppRow` is
  never consumed (two typings of ONE term never produce a
  family-application chain).
- `DT021T_no_cumulativity_of_sortRow` — the `RcicDT021Rows` DT-021 route
  (L58–65) parameterized on `sortRow` alone, the only field the proof
  reads.
-/

namespace Rcic.Declarative

/-- DT-012's shape at the two-field interface: two typings of one term
    have a `TyConvT` between their types, given `sortRow` and `piRow`
    separately instead of `TypedRowsWf`. The derivation stays
    `Nonempty`-valued so `piRow`'s existence form composes; `srow`
    collapses the sort chains at the `.pi` arm, `prow` injects the Π
    chain at the `.app` arm, and the `instantiate0` closures ride
    `convT_subst0_tyConvT` / `convT_substLet0_tyConvT` under `EnvWfT`.
    `famAppRow` is not consumed — two typings of ONE term never produce a
    family-application chain. Same proof structure as the landed
    `DT012T_type_uniqueness_of_typedRowsWf`, which is untouched. -/
def DT012T_type_uniqueness_of_sortRow_piRow {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (srow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
      TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    (prow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ) B B')) :
    {Γ : LCtx} → CtxWfT E n Γ → {e A : Expr Nat} → HasTyT E n Γ e A →
    {B : Expr Nat} → HasTyT E n Γ e B → Nonempty (TyConvT E n Γ A B)
  | _, _, _, _, .sort _ l, _, hB => ⟨hasTyTInv_sortT hB rfl⟩
  | _, _, _, _, .bvar _ _ _ h, _, hB => by
      obtain ⟨A', hlk', hcv⟩ := hasTyTInv_bvar hB rfl
      obtain rfl : A' = _ := Option.some.inj (hlk'.symm.trans h)
      exact ⟨hcv⟩
  | _, _, _, _, .const _ _ _ _ hres _ _, _, hB => by
      obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const hB rfl
      obtain rfl : m' = _ := Option.some.inj (hres'.symm.trans hres)
      exact ⟨hcv⟩
  | Γ, hΓ, _, _, .pi _ A u _ _ hA hB, _, hBt => by
      obtain ⟨u', v', hA', hB', hcv⟩ := hasTyTInv_pi hBt rfl
      obtain ⟨cA⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓ hA hA'
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓA hB hB'
      exact ⟨.trans _ _ _ _
        (.of _ _ _ _ (ConvT.sorts _ _ _
          (Ann.eqNA_imax (srow hΓ cA) (srow hΓA cB)))) hcv⟩
  | Γ, hΓ, _, _, .lam _ A u _ _ hA hb, _, hBt => by
      obtain ⟨_, B', _, hb', hcv⟩ := hasTyTInv_lam hBt rfl
      have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓA hb hb'
      exact ⟨.trans _ _ _ _ (tyConvT_pi_cod hA cB) hcv⟩
  | _, hΓ, _, _, .app _ _ _ _ _ hf ha, _, hBt => by
      obtain ⟨A', B', hf', _, hcv⟩ := hasTyTInv_app hBt rfl
      obtain ⟨cF⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓ hf hf'
      obtain ⟨cB⟩ := (prow hΓ cF).2
      obtain ⟨cI⟩ := convT_subst0_tyConvT hW cB ha
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | Γ, hΓ, _, _, .letE _ A u v _ _ hA hv hb, _, hBt => by
      obtain ⟨_, B', _, _, hb', hcv⟩ := hasTyTInv_letE hBt rfl
      have hΓL : CtxWfT E n (.letBinding A v :: Γ) := .letBinding Γ A u v hΓ hA hv
      obtain ⟨cB⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓL hb hb'
      obtain ⟨cI⟩ := convT_substLet0_tyConvT hW cB hv
      exact ⟨.trans _ _ _ _ cI hcv⟩
  | _, hΓ, _, _, .lit _ _ _ hexp, _, hBt => by
      obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit hBt rfl
      obtain ⟨c⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓ hexp hnat
      exact ⟨.trans _ _ _ _ c hcv⟩
  | _, hΓ, _, _, .conv _ _ _ _ _ h hc, _, hBt => by
      obtain ⟨c⟩ := DT012T_type_uniqueness_of_sortRow_piRow hW srow prow hΓ h hBt
      exact ⟨.trans _ _ _ _ (TyConvT.symmT (.of _ _ _ _ hc)) c⟩

/-- The landed `TypedRowsWf` carrier instantiates the two-field theorem by
    projection — the interface refactor is a pure composition. -/
theorem DT012T_type_uniqueness_of_sortRow_piRow_of_typedRowsWf
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW hrows.sortRow hrows.piRow hΓ hA hB

/-- DT-021 modulo the sort row alone: a typed conversion between two sorts
    collapses their levels. `DT009T_endpoints_envWfT` types both ends
    unconditionally; sort-inversion reads each as a `TyConvT` from the
    successor sort; `srow` collapses the chained
    `TyConvT (sort (u+1)) (sort (v+1))` to `eqN`. Same route as the landed
    `DT021T_no_cumulativity_of_typedRowsWf`, which reads nothing else and
    is untouched. -/
theorem DT021T_no_cumulativity_of_sortRow {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat}
    (srow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
      TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v := by
  obtain ⟨⟨h1⟩, ⟨h2⟩⟩ := DT009T_endpoints_envWfT hW hΓ hc
  exact eqN_succ_inj (srow hΓ
    (.trans _ _ _ _ (hasTyTInv_sortT h1 rfl) (hasTyTInv_sortT h2 rfl).symmT))

/-- The landed `TypedRowsWf` carrier instantiates the sort-only theorem by
    projection — a pure composition. -/
theorem DT021T_no_cumulativity_of_sortRow_of_typedRowsWf
    {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} {T : Expr Nat} (hc : ConvT E n Γ (.sort u) (.sort v) T) :
    eqN u v :=
  DT021T_no_cumulativity_of_sortRow hW hrows.sortRow hΓ hc

end Rcic.Declarative

#print axioms Rcic.Declarative.DT012T_type_uniqueness_of_sortRow_piRow
#print axioms Rcic.Declarative.DT012T_type_uniqueness_of_sortRow_piRow_of_typedRowsWf
#print axioms Rcic.Declarative.DT021T_no_cumulativity_of_sortRow
#print axioms Rcic.Declarative.DT021T_no_cumulativity_of_sortRow_of_typedRowsWf
