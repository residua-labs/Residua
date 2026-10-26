import rcic.RcicClassCAxSpine

/-!
# fable-famapp — the translation of `riEnv` into ANY scoped twin, and the family row's shadow

`RcicClassCAxSpine` (cc-classc) sends every derivation of the class-B fixture `riEnv`
(`RI : Sort 0 → Sort 0`, `mk : Π X, RI X`, AnySort recursor) into ONE twin `gEnv`, by the
translation `tr` (`RI ↦ RI₀`, `mk ↦ mk₀` at reference `2`, `rec.{l} ↦ recT l := λ M m X h. m X`),
and reads rows 1–2 off `gEnv`'s landed rows. Its typing lemmas are written against `gEnv`.

This module restates the typing side of that translation over an arbitrary target
`G : ResolvedEnv` given by a `TwinTarget`: `EnvWfT G`, the three rows of `G` (`TypedRowsWf G n`),
`RI₀ = riFam` at reference `0`, and at reference `2` a member whose stored type is `mk`'s
(`riCtor.mtype`, arity `0`) — an axiom, as in `gEnv`, or a constructor, as in the consistent twin
of `RcicFamAppTwin`. Nothing here depends on how `G` obtained its rows.

What is new is the third shadow: **the family row's shadow** (`famAppShadow`,
`famAppShadowConv`, `riIdxShadow`). A conversion in `riEnv` between two applications of `RI`
yields, in the twin, the landed family row's conclusion for the translated arguments:
`=ₙ` levels, equal lengths and `ConvArgsT G … (xs.map tr) (xs'.map tr)`; at one index,
`ConvT G (trCtx Γ) (tr x) (tr a) (Sort 0)`. Together with `riSortRow` and `riPiShadow`
(`RcicClassCAxSpine`) the three rows of `riEnv` each have their shadow in the twin.

**Why the shadow and not the row.** The way back (`ConvT G (tr x) (tr a) ⟹ ConvT riEnv x a`) is
the lift-back wall: it needs, in `riEnv`, type uniqueness for the translated redex (Π-inversion
against the known type of the recursor's image), which is `riEnv`'s own Π row. So the shadow is the
honest statement: it is the full content of `FamAppConvInj` at `RI` that the scope supply
delivers, and it is exactly what a semantic consumer (a model of the twin) can read.

The translation's one non-structural case is ι: `rec M m X (mk x) ⟶ m x` becomes
`recT l M' m' X' (mk₀ x') ≡ m' x'`, and the index `X'` must agree with the field `x'`. That agreement
is read in the TWIN (`iotaAgreeW`): four Π-inversions against the known type of `recT l` by the
twin's type uniqueness (its sort and Π rows), then the twin's family row at `RI₀`. This is
possible because the K-like cell of class B is ungated: `recT l` is well typed by `irr` against
`mk₀ X` at the SAME type (`recTypedW`), with no index-agreement side condition — unlike the
`Eq`-shaped cell, where the analogous term is untypable at a free index. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Syn
open Rcic.Syn.ClassC

/-- the metatheory of a twin that the translation consumes: the six facts an `EnvWfT` derivation
    supplies through the landed wrappers (`DT007T_typing_regularity_of_envWfT`, `NativeValleys.convEnds`,
    `convT_of_tyConvT_sort_rows`, `convT_subst0_of_envWfT`, `DT012T_type_uniqueness_of_sortRow_piRow`,
    `hasTyT_spineInv_rows`), as fields — so a twin WITHOUT an `EnvWfT` derivation (the copy-only twin of
    `RcicFamAppCopyTwin`, whose group has no recursor) can supply them from the predicate-level cores. -/
structure TwinMeta (G : ResolvedEnv) : Type where
  regular : ∀ {n : Nat} {Γ : LCtx}, CtxWfT G n Γ → ∀ {e T : Expr Nat}, HasTyT G n Γ e T →
    ∃ w : Level, Nonempty (HasTyT G n Γ T (.sort w))
  ends : ∀ {n : Nat} {Γ : LCtx}, CtxWfT G n Γ → ∀ {a b T : Expr Nat}, ConvT G n Γ a b T →
    HasTyT G n Γ a T ×' HasTyT G n Γ b T ×' (Σ' w, HasTyT G n Γ T (.sort w))
  collapse : ∀ {n : Nat} {Γ : LCtx}, CtxWfT G n Γ → ∀ {a b : Expr Nat} {u : Level},
    HasTyT G n Γ a (.sort u) → TyConvT G n Γ a b → Nonempty (ConvT G n Γ a b (.sort u))
  subst0 : ∀ {n : Nat} {v t : Expr Nat} {Γ : LCtx} {a b T : Expr Nat},
    ConvT G n (.assumption t :: Γ) a b T → HasTyT G n Γ v t →
    ConvT G n Γ (instantiate0 v a) (instantiate0 v b) (instantiate0 v T)
  uniq : ∀ {n : Nat} {Γ : LCtx}, CtxWfT G n Γ → ∀ {e A : Expr Nat}, HasTyT G n Γ e A →
    ∀ {B : Expr Nat}, HasTyT G n Γ e B → Nonempty (TyConvT G n Γ A B)
  spineInv : ∀ {n : Nat} {Γ : LCtx}, CtxWfT G n Γ → ∀ {r : Nat} {ls : List Level}
    {m : CheckedMember}, G.members r = some m → ∀ {doms : List (Expr Nat)} {U : Expr Nat},
    instantiateLevels ls m.mtype = policyPi doms U → ∀ (xs : List (Expr Nat)),
    doms.length = xs.length → ∀ {T : Expr Nat}, HasTyT G n Γ (foldApps (.const r ls) xs) T →
    Nonempty ((ls.length = m.arity) ×' (levelsBounded n ls = true) ×'
      (∀ i x d, xs[i]? = some x → doms[i]? = some d →
        HasTyT G n Γ x (instPrefix (xs.take i) d)) ×'
      TyConvT G n Γ (instPrefix xs U) T)

/-- an `EnvWfT` twin with its rows supplies the six facts through the landed wrappers. -/
def TwinMeta.ofEnvWfT {G : ResolvedEnv} (hG : EnvWfT G) (rows : ∀ n, TypedRowsWf G n) :
    TwinMeta G where
  regular := fun {_n _Γ} hΓ {_e _T} h => DT007T_typing_regularity_of_envWfT hG hΓ h
  ends := fun {_n _Γ} hΓ {_a _b _T} c => NativeValleys.convEnds hG hΓ c
  collapse := fun {_n _Γ} hΓ {_a _b _u} hA h => convT_of_tyConvT_sort_rows hG (rows _) hΓ hA h
  subst0 := fun {_n _v _t _Γ _a _b _T} h hv => convT_subst0_of_envWfT hG h hv
  uniq := fun {_n _Γ} hΓ {_e _A} h1 {_B} h2 =>
    DT012T_type_uniqueness_of_sortRow_piRow hG (rows _).sortRow (rows _).piRow hΓ h1 h2
  spineInv := fun {_n _Γ} hΓ {_r _ls _m} hres {_doms _U} hpi xs hlen {_T} hT =>
    hasTyT_spineInv_rows hG (rows _).piRow hΓ hres hpi xs hlen hT

/-- a target of `tr`: an environment with the six metatheory facts and its three rows, `RI₀ = riFam`
    at `0`, and at `2` a member with `mk`'s stored type and arity (`gEnv`'s axiom `mk₀`, or a
    constructor). `EnvWfT` is NOT required (`TwinMeta.ofEnvWfT` supplies `meta` when it holds). -/
structure TwinTarget (G : ResolvedEnv) : Type where
  meta : TwinMeta G
  rows : ∀ n, TypedRowsWf G n
  h0 : G.members 0 = some riFam
  m₂ : CheckedMember
  h2 : G.members 2 = some m₂
  h2t : m₂.mtype = riCtor.mtype
  h2a : m₂.arity = 0

/-! ## (1) retyping along a chain, over any environment -/

/-- a conversion retyped along a type-conversion chain (`RcicClassCAxSpine.convRetype`, over any
    environment). -/
def retype {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T S : Expr Nat} (c : ConvT E n Γ a b T) :
    TyConvT E n Γ T S → ConvT E n Γ a b S
  | .refl _ _ => c
  | .of _ _ _ u h => .tyConv _ _ _ _ _ u c h
  | .trans _ _ _ _ h1 h2 => retype (retype c h1) h2

/-! ## (2) `recT l` is typed in the twin at the translated recursor type -/

namespace TwinTarget

section Typed

variable {G : ResolvedEnv} {n : Nat}

/-- `RI₀ a : Sort 0`. -/
def riTy (W : TwinTarget G) {Γ : LCtx} {a : Expr Nat} (ha : HasTyT G n Γ a (.sort .zero)) :
    HasTyT G n Γ (.app (.const 0 []) a) (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 0 [] riFam W.h0 rfl rfl) ha

/-- the member at `2`, at `mk`'s stored type. -/
def mkConstTy (W : TwinTarget G) (Γ : LCtx) (ls : List Level) (hlen : ls.length = 0) (hwf : levelsBounded n ls = true) :
    HasTyT G n Γ (.const 2 ls) (instantiateLevels ls riCtor.mtype) := by
  have h := HasTyT.const Γ 2 ls W.m₂ W.h2 (by rw [W.h2a]; exact hlen) hwf
  rw [W.h2t] at h
  exact h

/-- `mk₀ a : RI₀ a`. -/
def mkTy (W : TwinTarget G) {Γ : LCtx} {a : Expr Nat} (ha : HasTyT G n Γ a (.sort .zero)) :
    HasTyT G n Γ (.app (.const 2 []) a) (.app (.const 0 []) a) :=
  .app _ _ _ _ _ (W.mkConstTy Γ [] rfl rfl) ha

def motTy (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n Γ (recMot l) (.sort (.imax (.succ .zero) (.imax .zero (.succ l)))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
    (.imax .zero (.succ l)) (.sort Γ .zero)
    (.pi _ (.app (.const 0 []) (.bvar 0)) .zero (.sort l) (.succ l)
      (W.riTy (.bvar _ 0 _ rfl)) (.sort _ l))

/-- under `[M]`: `M X (mk₀ X) : Sort l`, under `[X, M]`. -/
def minBody (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n (.assumption (.sort .zero) :: g1 Γ l)
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 2 []) (.bvar 0))) (.sort l) :=
  .app _ _ _ (.app (.const 0 []) (.bvar 0)) (.sort l)
    (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
      (.bvar _ 1 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))) rfl)
      (.bvar _ 0 _ rfl))
    (W.mkTy (.bvar _ 0 _ rfl))

def minTy (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n (g1 Γ l) recMin (.sort (.imax (.succ .zero) l)) :=
  .pi _ (.sort .zero) (.succ .zero) _ l (.sort _ .zero) (W.minBody Γ l)

/-- `m X : M X h`, under `[h, X, m, M]`: the body is typed by `irr` (`h ≡ mk₀ X : RI₀ X`, the
    ungated K-like cell of class B) and `tyConv`. -/
def body (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n (g4 Γ l) (.app (.bvar 2) (.bvar 1)) recB4 :=
  .conv _ _ (.app (.app (.bvar 3) (.bvar 1)) (.app (.const 2 []) (.bvar 1))) recB4 l
    (.app _ _ _ (.sort .zero) (.app (.app (.bvar 4) (.bvar 0)) (.app (.const 2 []) (.bvar 0)))
      (.bvar _ 2 (.pi (.sort .zero)
        (.app (.app (.bvar 4) (.bvar 0)) (.app (.const 2 []) (.bvar 0)))) rfl)
      (.bvar _ 1 _ rfl))
    (.app _ (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) (.bvar 1))
      (.app (.const 2 []) (.bvar 1)) (.bvar 0) (.app (.const 0 []) (.bvar 1)) (.sort l)
      (.refl _ _ (.pi (.app (.const 0 []) (.bvar 1)) (.sort l))
        (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
          (.bvar _ 3 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))) rfl)
          (.bvar _ 1 _ rfl)))
      (.irr _ (.app (.const 0 []) (.bvar 1)) (.app (.const 2 []) (.bvar 1)) (.bvar 0)
        (W.riTy (.bvar _ 1 _ rfl)) (W.mkTy (.bvar _ 1 _ rfl)) (.bvar _ 0 _ rfl)))

def lam4 (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n (g3 Γ l) (.lam ri0X (.app (.bvar 2) (.bvar 1))) (.pi ri0X recB4) :=
  .lam _ _ .zero _ _ (W.riTy (.bvar _ 0 _ rfl)) (W.body Γ l)

def lam3 (W : TwinTarget G) (Γ : LCtx) (l : Level) :
    HasTyT G n (g2 Γ l) (.lam (.sort .zero) (.lam ri0X (.app (.bvar 2) (.bvar 1))))
      (.pi (.sort .zero) (.pi ri0X recB4)) :=
  .lam _ _ (.succ .zero) _ _ (.sort _ .zero) (W.lam4 Γ l)

def lam2 (W : TwinTarget G) (Γ : LCtx) (l : Level) : HasTyT G n (g1 Γ l) recT1 recTy1 :=
  .lam _ _ _ _ _ (W.minTy Γ l) (W.lam3 Γ l)

/-- **the translated recursor is typed in the twin**, at every context. -/
def recTypedW (W : TwinTarget G) (Γ : LCtx) (l : Level) : HasTyT G n Γ (recT l) (recTyTr l) :=
  .lam _ _ _ _ _ (W.motTy Γ l) (W.lam2 Γ l)

/-- the translated recursor is level-congruent: `recT l ≡ recT l'` when `l =ₙ l'`. -/
def recConvW (W : TwinTarget G) (Γ : LCtx) (l l' : Level) (h : eqN l l') :
    ConvT G n Γ (recT l) (recT l') (recTyTr l) :=
  .lam Γ (recMot l) (recMot l') recT1 recT1 recTy1
    (.imax (.succ .zero) (.imax .zero (.succ l)))
    (.pi Γ (.sort .zero) (.sort .zero) _ _ (.succ .zero) (.imax .zero (.succ l))
      (.refl _ _ _ (.sort _ _))
      (.pi _ ri0X ri0X (.sort l) (.sort l') .zero (.succ l)
        (.refl _ _ _ (W.riTy (.bvar _ 0 _ rfl)))
        (.sorts _ l l' h)))
    (.refl _ _ _ (W.lam2 Γ l))

end Typed

/-! ## (3) reading the twin: β by its rows, the `CE` calculus, the four β steps -/

section Read

variable {G : ResolvedEnv} {n : Nat}

theorem betaConvW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {A0 body arg S : Expr Nat}
    (h : HasTyT G n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (ConvT G n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) S) := by
  have hrows := W.rows n
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u0, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
  obtain ⟨w, ⟨hBw⟩⟩ := W.meta.regular (.assumption Γ A0 u0 hΓ hA0ty) hbody
  obtain ⟨cdom⟩ := W.meta.collapse hΓ hA0ty hBdom
  obtain ⟨ccod⟩ := W.meta.collapse (.assumption Γ A0 u0 hΓ hA0ty) hBw hBcod
  have ha' : HasTyT G n Γ arg A0 :=
    HasTyT.conv _ _ _ _ u0 ha (ConvT.symm _ _ _ _ cdom)
  have hcod' : ConvT G n Γ (instantiate0 arg B_lam) (instantiate0 arg B1) (.sort w) :=
    W.meta.subst0 ccod ha'
  exact ⟨retype (ConvT.beta Γ A0 body arg B_lam u0 hA0ty hbody ha')
    (.trans _ _ _ _ (.of _ _ _ _ hcod') hcv)⟩

/-- `e ≡ e'` at every type of `e`. -/
def CEW (G : ResolvedEnv) (n : Nat) (Γ : LCtx) (e e' : Expr Nat) : Prop :=
  ∀ S, HasTyT G n Γ e S → Nonempty (ConvT G n Γ e e' S)

theorem ceBetaW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {A0 body arg : Expr Nat} :
    CEW G n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) :=
  fun _ h => W.betaConvW hΓ h

theorem ceTransW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {e e' e'' : Expr Nat}
    (h1 : CEW G n Γ e e') (h2 : CEW G n Γ e' e'') : CEW G n Γ e e'' := by
  intro S h
  obtain ⟨c1⟩ := h1 S h
  obtain ⟨c2⟩ := h2 S (W.meta.ends hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 c2⟩

theorem ceAppLW {Γ : LCtx} {f f' : Expr Nat} (a : Expr Nat)
    (h1 : CEW G n Γ f f') : CEW G n Γ (.app f a) (.app f' a) := by
  intro S h
  obtain ⟨A, B, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := h1 _ hf
  exact ⟨retype (ConvT.app Γ f f' a a A B c (ConvT.refl Γ a A ha)) hcv⟩

theorem ceOfEqW {Γ : LCtx} {e e' : Expr Nat} (h : e = e') : CEW G n Γ e e' :=
  fun _ hS => ⟨h ▸ ConvT.refl _ _ _ hS⟩

/-- the four β steps of the translated recursor. -/
theorem red4W (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (M' m' X' H' : Expr Nat) :
    CEW G n Γ (.app (.app (.app (.app (recT l) M') m') X') H') (.app m' X') := by
  refine W.ceTransW hΓ (ceAppLW _ (ceAppLW _ (ceAppLW _ (W.ceBetaW hΓ)))) ?_
  refine W.ceTransW hΓ (ceAppLW _ (ceAppLW _ (W.ceBetaW hΓ))) ?_
  refine W.ceTransW hΓ (ceAppLW _ (W.ceBetaW hΓ)) ?_
  refine W.ceTransW hΓ (W.ceBetaW hΓ) ?_
  apply ceOfEqW
  have h1 : instantiate (0 + 1 + 1 + 1) (lift 0 1 (lift 0 1 (lift 0 1 M')))
      ((Expr.bvar 2).app (Expr.bvar 1)) = (Expr.bvar 2).app (Expr.bvar 1) := by
    simp [instantiate]
  have h2 : instantiate (0 + 1 + 1) (lift 0 1 (lift 0 1 m')) ((Expr.bvar 2).app (Expr.bvar 1)) =
      (lift 0 1 (lift 0 1 m')).app (Expr.bvar 1) := by
    simp [instantiate]
  have hm : lift 0 1 (lift 0 1 m') = lift 0 2 m' := by
    rw [lift_lift_merge 1 1 0 0 (Nat.le_refl _) (by omega)]
  have h3 : instantiate (0 + 1) (lift 0 1 X') ((lift 0 2 m').app (Expr.bvar 1)) =
      (lift 0 1 m').app (lift 0 1 X') := by
    simp only [instantiate]
    rw [instantiate_lift_cancel 2 0 1 _ (by omega) (by omega)]
    simp [instantiate]
  have h4 : instantiate0 H' ((lift 0 1 m').app (lift 0 1 X')) = m'.app X' := by
    simp only [instantiate0, instantiate]
    rw [instantiate_lift_cancel 1 0 0 _ (by omega) (by omega),
      instantiate_lift_cancel 1 0 0 _ (by omega) (by omega)]
    simp [lift_zero_idx]
  rw [h1, h2, hm, h3, h4]

end Read

/-! ## (4) the ι cell, read in the twin -/

section Iota

variable {G : ResolvedEnv} {n : Nat}

/-- an application whose head has a known Π type reads the argument's type off the head (the
    twin's type uniqueness, from its sort and Π rows). -/
theorem appInvKnownW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {f a D C T' : Expr Nat}
    (hf : HasTyT G n Γ f (.pi D C)) (h : HasTyT G n Γ (.app f a) T') :
    Nonempty (HasTyT G n Γ a D) := by
  obtain ⟨A, B, hf', ha', _⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := W.meta.uniq hΓ hf' hf
  obtain ⟨⟨cA⟩, _⟩ := (W.rows n).piRow hΓ c
  exact ⟨hasTyT_of_tyConvT ha' cA⟩

/-- **the ι cell's agreement, read in the twin.** If `recT l M' m' X' (mk₀ x')` is typed, then
    `x' ≡ X' : Sort 0`: four Π-inversions against the known type of `recT l`, then the twin's
    family row at `RI₀`. -/
theorem iotaAgreeW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT G n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) T') :
    Nonempty (ConvT G n Γ x' X' (.sort .zero)) := by
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := W.appInvKnownW hΓ (W.recTypedW Γ l) he1
  have own1 := HasTyT.app Γ (recT l) M' _ _ (W.recTypedW Γ l) hM'
  obtain ⟨hm'⟩ := W.appInvKnownW hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := W.appInvKnownW hΓ own2 he3
  have own3 := HasTyT.app Γ _ X' _ _ own2 hX'
  obtain ⟨hH'⟩ := W.appInvKnownW hΓ own3 hlhs
  have hH'' : HasTyT G n Γ (.app (.const 2 lsC) x') (.app (.const 0 []) X') := hH'
  have hinst : instantiateLevels lsC W.m₂.mtype = policyPi [.sort .zero] ri0X := by
    rw [W.h2t]; rfl
  obtain ⟨⟨-, -, hargs, hconv⟩⟩ := W.meta.spineInv hΓ
    (r := 2) (ls := lsC) (m := W.m₂) W.h2 (doms := [.sort .zero]) (U := ri0X) hinst [x'] rfl hH''
  have hx' : HasTyT G n Γ x' (.sort .zero) := hargs 0 x' (.sort .zero) rfl rfl
  have hIP : instPrefix [x'] ri0X = .app (.const 0 []) x' := by
    simp [instPrefix, instantiate, lift_zero_idx]
  rw [hIP] at hconv
  obtain ⟨-, -, hc⟩ := (W.rows n).famAppRow hΓ (r := 0) (m := riFam) (ls := []) (ls' := [])
    (xs := [x']) (xs' := [X']) (w := .zero) W.h0 rfl (W.riTy hx') hconv
  have hc' : ConvArgsT G n Γ (.pi (.sort .zero) (.sort .zero)) [x'] [X'] := hc
  cases hc' with
  | cons A B f f' fs fs' h hs => exact h

/-- **the translated ι cell.** `recT l M' m' X' (mk₀ x') ≡ m' x'` at every type of the redex. -/
theorem iotaConvW (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT G n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) T') :
    Nonempty (ConvT G n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) (.app m' x') T') := by
  obtain ⟨cxX⟩ := W.iotaAgreeW hΓ l lsC M' m' X' x' T' hlhs
  obtain ⟨c1⟩ := W.red4W hΓ l M' m' X' (.app (.const 2 lsC) x') T' hlhs
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := W.appInvKnownW hΓ (W.recTypedW Γ l) he1
  have own1 := HasTyT.app Γ (recT l) M' _ _ (W.recTypedW Γ l) hM'
  obtain ⟨hm'⟩ := W.appInvKnownW hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := W.appInvKnownW hΓ own2 he3
  have hm'' : HasTyT G n Γ m' (.pi (.sort .zero) _) := hm'
  have c2 := ConvT.app Γ m' m' X' x' _ _ (ConvT.refl Γ m' _ hm'') (ConvT.symm _ _ _ _ cxX)
  have hmX := HasTyT.app Γ m' X' _ _ hm'' hX'
  obtain ⟨cT⟩ := W.meta.uniq hΓ hmX (W.meta.ends hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 (retype c2 cT)⟩

end Iota

/-! ## (5) the translation of derivations, `riEnv → G` -/

section Translate

variable {G : ResolvedEnv} {n : Nat}

mutual
theorem trTyW (W : TwinTarget G) : {Γ : LCtx} → {e A : Expr Nat} → HasTyT riEnv n Γ e A →
    CtxWfT G n (trCtx Γ) → Nonempty (HasTyT G n (trCtx Γ) (tr e) (tr A))
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ =>
      ⟨.bvar _ i (tr A) (by rw [lookupType_trCtx, h]; rfl)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      rcases riEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        exact ⟨W.recTypedW (trCtx Γ) l⟩
      · exact ⟨W.mkConstTy (trCtx Γ) ls hlen hwf⟩
      · exact ⟨.const _ 0 ls riFam W.h0 hlen hwf⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trTyW W hA hΓ'
      obtain ⟨hB'⟩ := trTyW W hB (.assumption _ (tr A) u hΓ' hA')
      exact ⟨.pi _ (tr A) u (tr B) v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ' => by
      obtain ⟨hA'⟩ := trTyW W hA hΓ'
      obtain ⟨hb'⟩ := trTyW W hbody (.assumption _ (tr A) u hΓ' hA')
      exact ⟨.lam _ (tr A) u (tr body) (tr B) hA' hb'⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ' => by
      obtain ⟨hf'⟩ := trTyW W hf hΓ'
      obtain ⟨ha'⟩ := trTyW W ha hΓ'
      rw [tr_instantiate0]
      exact ⟨.app _ (tr f) (tr a) (tr A) (tr B) hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTyW W hA hΓ'
      obtain ⟨hv'⟩ := trTyW W hv hΓ'
      obtain ⟨hb'⟩ := trTyW W hb (.letBinding _ (tr A) u (tr value) hΓ' hA' hv')
      rw [tr_instantiate0]
      exact ⟨.letE _ (tr A) u (tr value) (tr B) (tr body) hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ' => by
      obtain ⟨h⟩ := trTyW W hexp hΓ'
      rw [tr_natExpand] at h
      exact ⟨h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ' => by
      obtain ⟨h'⟩ := trTyW W h hΓ'
      obtain ⟨hc'⟩ := trConvW W hc hΓ'
      exact ⟨.conv _ (tr e) (tr A) (tr B) u h' hc'⟩

theorem trConvW (W : TwinTarget G) : {Γ : LCtx} → {a b A : Expr Nat} → ConvT riEnv n Γ a b A →
    CtxWfT G n (trCtx Γ) → Nonempty (ConvT G n (trCtx Γ) (tr a) (tr b) (tr A))
  | _, _, _, _, .refl Γ a A h, hΓ' => by
      obtain ⟨h'⟩ := trTyW W h hΓ'
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ' => by
      obtain ⟨h'⟩ := trConvW W h hΓ'
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConvW W h1 hΓ'
      obtain ⟨h2'⟩ := trConvW W h2 hΓ'
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ' => by
      obtain ⟨hA'⟩ := trTyW W hA hΓ'
      obtain ⟨hb'⟩ := trTyW W hbody (.assumption _ (tr A) u hΓ' hA')
      obtain ⟨ha'⟩ := trTyW W harg hΓ'
      rw [tr_instantiate0, tr_instantiate0]
      exact ⟨.beta _ (tr A) (tr body) (tr arg) (tr B) u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTyW W hA hΓ'
      obtain ⟨hv'⟩ := trTyW W hv hΓ'
      obtain ⟨hb'⟩ := trTyW W hb (.letBinding _ (tr A) u (tr value) hΓ' hA' hv')
      rw [tr_instantiate0, tr_instantiate0]
      exact ⟨.zeta _ (tr A) (tr value) (tr body) (tr B) u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ' => by
      obtain ⟨hv'⟩ := trTyW W hv hΓ'
      exact ⟨.zetaLocal _ i (tr A) (tr v) (by rw [lookupValue_trCtx, hval]; rfl)
        (by rw [lookupType_trCtx, hty]; rfl) hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody _ _ _ _, _ =>
      absurd hbody (by rw [riEnv_noBody hres]; exact Option.noConfusion)
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, hΓ' => by
      obtain ⟨hl'⟩ := trTyW W hl hΓ'
      obtain ⟨ls, lsC, M, m, X, x, hlen, hL, hR⟩ := riIota_inv' h
      obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
      rw [hL] at hl'
      rw [hL, hR]
      have e1 : tr (foldApps (.const 2 [l]) [M, m, X, foldApps (.const 1 lsC) [x]]) =
          .app (.app (.app (.app (recT l) (tr M)) (tr m)) (tr X)) (.app (.const 2 lsC) (tr x)) :=
        rfl
      rw [e1] at hl' ⊢
      exact W.iotaConvW hΓ' l lsC (tr M) (tr m) (tr X) (tr x) (tr T) hl'
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ' => by
      obtain ⟨h'⟩ := trTyW W hexp hΓ'
      rw [litExp_eq h, tr_natExpand] at *
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .app Γ f g a b A B h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConvW W h1 hΓ'
      obtain ⟨h2'⟩ := trConvW W h2 hΓ'
      rw [tr_instantiate0]
      exact ⟨.app _ (tr f) (tr g) (tr a) (tr b) (tr A) (tr B) h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ' => by
      obtain ⟨hA'⟩ := trConvW W hA hΓ'
      obtain ⟨hb'⟩ := trConvW W hb (.assumption _ (tr A) u hΓ'
        (W.meta.ends hΓ' hA').1)
      exact ⟨.lam _ (tr A) (tr A') (tr b) (tr b') (tr B) u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trConvW W hA hΓ'
      obtain ⟨hB'⟩ := trConvW W hB (.assumption _ (tr A) u hΓ'
        (W.meta.ends hΓ' hA').1)
      exact ⟨.pi _ (tr A) (tr A') (tr B) (tr B') u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trConvW W hA hΓ'
      obtain ⟨hv'⟩ := trConvW W hv hΓ'
      obtain ⟨hb'⟩ := trConvW W hb (.letBinding _ (tr A) u (tr v) hΓ'
        (W.meta.ends hΓ' hA').1 (W.meta.ends hΓ' hv').1)
      rw [tr_instantiate0]
      exact ⟨.letE _ (tr A) (tr A') (tr v) (tr v') (tr b) (tr b') (tr B) u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ => by
      rcases riEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        rcases ls' with _ | ⟨l', _ | ⟨l'', t⟩⟩
        · exact h.elim
        · exact ⟨W.recConvW (trCtx Γ) l l' h.1⟩
        · exact h.2.elim
      · have c := ConvT.consts (trCtx Γ) 2 ls ls' W.m₂ W.h2 (by rw [W.h2a]; exact hlen) hwf hwf' h
        rw [W.h2t] at c
        exact ⟨c⟩
      · exact ⟨.consts _ 0 ls ls' riFam W.h0 hlen hwf hwf' h⟩
  | _, _, _, _, .eta Γ f A B h, hΓ' => by
      obtain ⟨h'⟩ := trTyW W h hΓ'
      show Nonempty (ConvT G n (trCtx Γ) (.lam (tr A) (.app (tr (lift 0 1 f)) (.bvar 0))) (tr f)
        (.pi (tr A) (tr B)))
      rw [tr_lift]
      exact ⟨.eta _ (tr f) (tr A) (tr B) h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ' => by
      obtain ⟨hP'⟩ := trTyW W hP hΓ'
      obtain ⟨hp'⟩ := trTyW W hp hΓ'
      obtain ⟨hq'⟩ := trTyW W hq hΓ'
      exact ⟨.irr _ (tr P) (tr p) (tr q) hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ' => by
      obtain ⟨h'⟩ := trConvW W h hΓ'
      obtain ⟨hA'⟩ := trConvW W hA hΓ'
      exact ⟨.tyConv _ (tr a) (tr b) (tr A) (tr A') u h' hA'⟩
end

theorem trTyConvW (W : TwinTarget G) {Γ : LCtx} {a b : Expr Nat} (h : TyConvT riEnv n Γ a b)
    (hΓ' : CtxWfT G n (trCtx Γ)) : Nonempty (TyConvT G n (trCtx Γ) (tr a) (tr b)) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := W.trConvW h hΓ'; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem trCtxWfW (W : TwinTarget G) {Γ : LCtx} (h : CtxWfT riEnv n Γ) : Nonempty (CtxWfT G n (trCtx Γ)) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := W.trTyW hA hΓ'
      exact ⟨.assumption _ (tr A) u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := W.trTyW hA hΓ'
      obtain ⟨hv'⟩ := W.trTyW hv hΓ'
      exact ⟨.letBinding _ (tr A) u (tr v) hΓ' hA' hv'⟩

end Translate

/-! ## (6) the three shadows at `riEnv`, in any twin -/

section Shadows

variable {G : ResolvedEnv} {n : Nat}

/-- row 1 at `riEnv` (unconditional, as `riSortRow`; here from any twin). -/
theorem sortShadow (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {u v : Level}
    (h : TyConvT riEnv n Γ (.sort u) (.sort v)) : eqN u v := by
  obtain ⟨hΓ'⟩ := W.trCtxWfW hΓ
  obtain ⟨c⟩ := W.trTyConvW h hΓ'
  exact (W.rows n).sortRow hΓ' c

/-- row 2's shadow at `riEnv`, in the twin. -/
theorem piShadow (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {A B A' B' : Expr Nat}
    (h : TyConvT riEnv n Γ (.pi A B) (.pi A' B')) :
    Nonempty (TyConvT G n (trCtx Γ) (tr A) (tr A')) ∧
      Nonempty (TyConvT G n (.assumption (tr A) :: trCtx Γ) (tr B) (tr B')) := by
  obtain ⟨hΓ'⟩ := W.trCtxWfW hΓ
  obtain ⟨c⟩ := W.trTyConvW h hΓ'
  exact (W.rows n).piRow hΓ' c

/-- **row 3's shadow at `riEnv`, in the twin.** A chain in `riEnv` between two full applications
    of `RI`, the left one typed at a sort, yields the twin's family row at `RI₀` for the
    translated arguments: `=ₙ` level lists, equal lengths, pointwise `ConvArgsT` in the twin along
    the family's type. -/
theorem famAppShadow (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level}
    (hty : HasTyT riEnv n Γ (foldApps (.const 0 ls) xs) (.sort w))
    (h : TyConvT riEnv n Γ (foldApps (.const 0 ls) xs) (foldApps (.const 0 ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT G n (trCtx Γ) (instantiateLevels ls riFam.mtype) (xs.map tr) (xs'.map tr) := by
  obtain ⟨hΓ'⟩ := W.trCtxWfW hΓ
  obtain ⟨hty'⟩ := W.trTyW hty hΓ'
  obtain ⟨c⟩ := W.trTyConvW h hΓ'
  rw [tr_foldApps] at hty' c
  rw [tr_foldApps] at c
  have e0 : ∀ ls : List Level, tr (.const 0 ls) = .const 0 ls := fun _ => rfl
  rw [e0] at hty' c
  rw [e0] at c
  obtain ⟨h1, h2, h3⟩ := (W.rows n).famAppRow hΓ' (r := 0) (m := riFam) W.h0 rfl hty' c
  refine ⟨h1, ?_, h3⟩
  simpa using h2

/-- row 3's shadow from a single conversion at a sort. -/
theorem famAppShadowConv (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level}
    (h : ConvT riEnv n Γ (foldApps (.const 0 ls) xs) (foldApps (.const 0 ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT G n (trCtx Γ) (instantiateLevels ls riFam.mtype) (xs.map tr) (xs'.map tr) :=
  W.famAppShadow hΓ (NativeValleys.convEnds riEnvWfT hΓ h).1 (.of _ _ _ _ h)

/-- **the index shadow**: `RI x ≡ RI a : Sort w` in `riEnv` gives `tr x ≡ tr a : Sort 0` in the
    twin — the content of `FamAppConvInj` at `RI`, read in the twin. -/
theorem riIdxShadow (W : TwinTarget G) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {x a : Expr Nat} {w : Level}
    (h : ConvT riEnv n Γ (.app (.const 0 []) x) (.app (.const 0 []) a) (.sort w)) :
    Nonempty (ConvT G n (trCtx Γ) (tr x) (tr a) (.sort .zero)) := by
  obtain ⟨-, -, hc⟩ := W.famAppShadowConv hΓ (ls := []) (ls' := []) (xs := [x]) (xs' := [a]) h
  have hc' : ConvArgsT G n (trCtx Γ) (.pi (.sort .zero) (.sort .zero)) [tr x] [tr a] := hc
  cases hc' with
  | cons A B f f' fs fs' hh hs => exact hh

end Shadows

end TwinTarget

/-! ## (7) the landed twin is a target -/

/-- `gEnv` (`RcicClassCAxSpine`) is a `TwinTarget`: its rows are landed (`gRows`), `mk₀` is the
    axiom at `2` with `mk`'s stored type. -/
def gTwin : TwinTarget gEnv where
  meta := .ofEnvWfT gEnvWfT gRows
  rows := gRows
  h0 := rfl
  m₂ := gMk
  h2 := rfl
  h2t := rfl
  h2a := rfl

/-- the family row's shadow at `riEnv` in `gEnv`, completing cc-classc's shadow triple
    (`riSortRow`, `riPiShadow`). -/
theorem riFamAppShadow_gEnv {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {x a : Expr Nat} {w : Level}
    (h : ConvT riEnv n Γ (.app (.const 0 []) x) (.app (.const 0 []) a) (.sort w)) :
    Nonempty (ConvT gEnv n (trCtx Γ) (tr x) (tr a) (.sort .zero)) :=
  gTwin.riIdxShadow hΓ h

end Rcic.Syn.FamApp

#print axioms Rcic.Syn.FamApp.TwinTarget.recTypedW
#print axioms Rcic.Syn.FamApp.TwinTarget.iotaAgreeW
#print axioms Rcic.Syn.FamApp.TwinTarget.trConvW
#print axioms Rcic.Syn.FamApp.TwinTarget.famAppShadow
#print axioms Rcic.Syn.FamApp.TwinTarget.riIdxShadow
#print axioms Rcic.Syn.FamApp.riFamAppShadow_gEnv
