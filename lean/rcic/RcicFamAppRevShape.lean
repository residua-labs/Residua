import rcic.RcicFamAppRevTr
import rcic.RcicFamAppTwinGeneric

/-!
# RcicFamAppRevShape — the λ-recursor of ANY revealed singleton is typed by `irr`; the ι cell read in a twin

`RcicFamAppTwinGeneric` types the fixture's λ-recursor `recT l := λ M m X h. m X` in every target that has
`RI₀` at `0` and `mk`'s type at `2`, and reads the ι cell's agreement `x' ≡ X'` off the target's rows. This
module is the same for the tier's generic B1 shape (`RcicFamAppRevTr`): a `RevShape G` is an environment `G`
with the family `F : Π (i : I), Sort 0` at `f`, a member at `f + 1` of `mk`'s stored type and arity `0` (the
constructor itself, or the twin's axiom), and the closed level-free index type `I : Sort uI` typed everywhere.

* `RevShape.recTypedW : HasTyT G n Γ (recTG f I l) (recTyG f I l)` — the body `m i : M i h` by `irr` against
  `mk i` at the SAME type `F i` (the ungated K-like cell of class B), and `tyConv`; `recConvW` its level
  congruence. Both the environment of interest and its twin are `RevShape`s.
* `RevTwinTarget G` adds the six metatheory facts (`TwinMeta`) and the rows; on it the `CE` calculus (β by the
  rows), the four β steps of the λ-recursor (`red4W`), and **the ι cell** (`iotaAgreeW`: the index `X'` and the
  revealed field `x'` agree at type `I`, by four Π-inversions against the known type of `recTG l` and the
  twin's family row at `F`; `iotaConvW`: `recTG l M' m' X' (mk x') ≡ m' x'` at every type of the redex).

The fixture (`f = 0`, `I = Sort 0`) is literally an instance; nothing here reads the environment beyond the
three members. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin

set_option maxRecDepth 8192

/-- the signature of a revealed singleton: the family's reference `f` and the closed, level-free index type
    `I : Sort uI`. Shared by the environment of interest and its twin, so the translation's terms are the same
    terms on both sides. -/
structure RevSig : Type where
  f : Nat
  I : Expr Nat
  uI : Level
  hclI : ∀ k, lift k 1 I = I
  hlvlI : exprLevelsBounded 0 I = true

/-- the shape of a revealed singleton of signature `σ` inside `G`: `F` at `f`, a member of `mk`'s type and
    arity at `f + 1`, the index type typed at every level bound and context. -/
structure RevShape (σ : RevSig) (G : ResolvedEnv) : Type where
  hfam : G.members σ.f = some (revFamM σ.I)
  m₁ : CheckedMember
  h1 : G.members (σ.f + 1) = some m₁
  h1t : m₁.mtype = revCtorTy σ.f σ.I
  h1a : m₁.arity = 0
  hI : ∀ (n : Nat) (Γ : LCtx), HasTyT G n Γ σ.I (.sort σ.uI)

namespace RevShape

variable {σ : RevSig} {G : ResolvedEnv} (S : RevShape σ G) {n : Nat}

set_option linter.unusedVariables false in
/-- the family's reference. -/
abbrev f (_S : RevShape σ G) : Nat := σ.f
set_option linter.unusedVariables false in
/-- the index type. -/
abbrev I (_S : RevShape σ G) : Expr Nat := σ.I
set_option linter.unusedVariables false in
/-- the index type's sort. -/
abbrev uI (_S : RevShape σ G) : Level := σ.uI
set_option linter.unusedVariables false in
theorem hclI (_S : RevShape σ G) : ∀ k, lift k 1 σ.I = σ.I := σ.hclI
set_option linter.unusedVariables false in
theorem hlvlI (_S : RevShape σ G) : exprLevelsBounded 0 σ.I = true := σ.hlvlI

theorem liftI (c k : Nat) : lift c k S.I = S.I := lift_of_closed _ (S.hclI 0) c k

theorem instLvlsI (ls : List Level) : instantiateLevels ls S.I = S.I :=
  Ann.instantiateLevels_closed ls S.I S.hlvlI

theorem famTy_lvl : exprLevelsBounded 0 (revFamM S.I).mtype = true := by
  show exprLevelsBounded 0 (.pi S.I (.sort .zero)) = true
  simp [exprLevelsBounded, S.hlvlI, levelBounded]

theorem famTy_inst (ls : List Level) : instantiateLevels ls (revFamM S.I).mtype = .pi S.I (.sort .zero) := by
  show instantiateLevels ls (.pi S.I (.sort .zero)) = .pi S.I (.sort .zero)
  simp [instantiateLevels, S.instLvlsI, instLevel_zero]

theorem ctorTy_inst (ls : List Level) : instantiateLevels ls (revCtorTy S.f S.I) = .pi S.I (famApp0 S.f) := by
  simp [revCtorTy, instantiateLevels, S.instLvlsI]

theorem recTyS_inst (l : Level) : instantiateLevels [l] (recTyS S.f S.I) = recTyG S.f S.I l := by
  simp [recTyS, recTyG, motTy, minTy, instantiateLevels, S.instLvlsI, instLevel_param]

/-! ### typing helpers -/

/-- `F : Π (i : I), Sort 0` at every context and level bound. -/
def famConst (Γ : LCtx) : HasTyT G n Γ (.const S.f []) (.pi S.I (.sort .zero)) := by
  have h : HasTyT G n Γ (.const S.f []) (instantiateLevels [] (revFamM S.I).mtype) :=
    .const Γ S.f [] (revFamM S.I) S.hfam rfl rfl
  rwa [S.famTy_inst] at h

/-- `F a : Sort 0`. -/
def famTy {Γ : LCtx} {a : Expr Nat} (ha : HasTyT G n Γ a S.I) :
    HasTyT G n Γ (.app (.const S.f []) a) (.sort .zero) :=
  .app Γ (.const S.f []) a S.I (.sort .zero) (S.famConst Γ) ha

/-- the member at `f + 1`, at `mk`'s stored type. -/
def mkConstTy (Γ : LCtx) (ls : List Level) (hlen : ls.length = 0) (hwf : levelsBounded n ls = true) :
    HasTyT G n Γ (.const (S.f + 1) ls) (instantiateLevels ls (revCtorTy S.f S.I)) := by
  have h := HasTyT.const Γ (S.f + 1) ls S.m₁ S.h1 (by rw [S.h1a]; exact hlen) hwf
  rw [S.h1t] at h
  exact h

/-- `mk : Π (x : I), F x`. -/
def mkConst (Γ : LCtx) : HasTyT G n Γ (.const (S.f + 1) []) (.pi S.I (famApp0 S.f)) := by
  have h : HasTyT G n Γ (.const (S.f + 1) []) (instantiateLevels [] (revCtorTy S.f S.I)) :=
    S.mkConstTy Γ [] rfl rfl
  rwa [S.ctorTy_inst] at h

/-- `mk a : F a`. -/
def mkTy {Γ : LCtx} {a : Expr Nat} (ha : HasTyT G n Γ a S.I) :
    HasTyT G n Γ (.app (.const (S.f + 1) []) a) (.app (.const S.f []) a) :=
  .app Γ _ a S.I (famApp0 S.f) (S.mkConst Γ) ha

/-! ### the contexts under the λ-recursor's binders, and their lookups -/

def g1 (Γ : LCtx) (l : Level) : LCtx := .assumption (motTy S.f S.I l) :: Γ
def g2 (Γ : LCtx) (l : Level) : LCtx := .assumption (minTy S.f S.I) :: S.g1 Γ l
def g3 (Γ : LCtx) (l : Level) : LCtx := .assumption S.I :: S.g2 Γ l
def g4 (Γ : LCtx) (l : Level) : LCtx := .assumption (famApp0 S.f) :: S.g3 Γ l

/-- the minor's type as seen three binders further in (`M` is `bvar 4`). -/
def minTy3 : Expr Nat :=
  .pi S.I (.app (.app (.bvar 4) (.bvar 0)) (.app (.const (S.f + 1) []) (.bvar 0)))

theorem lift_motTy (c k : Nat) (l : Level) : lift c k (motTy S.f S.I l) = motTy S.f S.I l := by
  simp [motTy, lift, S.liftI]

theorem lk_g1I_1 (Γ : LCtx) (l : Level) :
    lookupType (.assumption S.I :: S.g1 Γ l) 1 = some (motTy S.f S.I l) := by
  simp [lookupType, g1, S.lift_motTy]

theorem lk_g1I_0 (Γ : LCtx) (l : Level) : lookupType (.assumption S.I :: S.g1 Γ l) 0 = some S.I := by
  simp [lookupType, S.liftI]

theorem lk_g3_0 (Γ : LCtx) (l : Level) : lookupType (S.g3 Γ l) 0 = some S.I := by
  simp [lookupType, g3, S.liftI]

theorem lk_g4_3 (Γ : LCtx) (l : Level) : lookupType (S.g4 Γ l) 3 = some (motTy S.f S.I l) := by
  simp [lookupType, g4, g3, g2, g1, S.lift_motTy]

theorem lk_g4_2 (Γ : LCtx) (l : Level) : lookupType (S.g4 Γ l) 2 = some S.minTy3 := by
  simp [lookupType, g4, g3, g2, minTy, minTy3, lift, S.liftI]

theorem lk_g4_1 (Γ : LCtx) (l : Level) : lookupType (S.g4 Γ l) 1 = some S.I := by
  simp [lookupType, g4, g3, S.liftI]

theorem lk_g4_0 (Γ : LCtx) (l : Level) :
    lookupType (S.g4 Γ l) 0 = some (.app (.const S.f []) (.bvar 1)) := by
  simp [lookupType, g4, lift]

/-! ### `recTG l` is typed at `recTyG l`, in every context -/

def motTyT (Γ : LCtx) (l : Level) :
    HasTyT G n Γ (motTy S.f S.I l) (.sort (.imax S.uI (.imax .zero (.succ l)))) :=
  .pi Γ S.I S.uI (.pi (famApp0 S.f) (.sort l)) (.imax .zero (.succ l)) (S.hI n Γ)
    (.pi _ (famApp0 S.f) .zero (.sort l) (.succ l)
      (S.famTy (.bvar _ 0 _ (by simp [lookupType, S.liftI]))) (.sort _ l))

/-- under `[x : I, M : motTy l]`: `M x (mk x) : Sort l`. -/
def minBody (Γ : LCtx) (l : Level) :
    HasTyT G n (.assumption S.I :: S.g1 Γ l)
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const (S.f + 1) []) (.bvar 0))) (.sort l) :=
  .app _ _ _ (.app (.const S.f []) (.bvar 0)) (.sort l)
    (.app _ _ _ S.I (.pi (famApp0 S.f) (.sort l))
      (.bvar _ 1 (motTy S.f S.I l) (S.lk_g1I_1 Γ l))
      (.bvar _ 0 _ (S.lk_g1I_0 Γ l)))
    (S.mkTy (.bvar _ 0 _ (S.lk_g1I_0 Γ l)))

def minTyT (Γ : LCtx) (l : Level) :
    HasTyT G n (S.g1 Γ l) (minTy S.f S.I) (.sort (.imax S.uI l)) :=
  .pi _ S.I S.uI _ l (S.hI n _) (S.minBody Γ l)

/-- `m i : M i h`, under `[h, i, m, M]`: the body is typed by `irr` (`h ≡ mk i : F i`, the ungated K-like
    cell of class B) and `tyConv`. -/
def body (Γ : LCtx) (l : Level) :
    HasTyT G n (S.g4 Γ l) (.app (.bvar 2) (.bvar 1)) recB4 :=
  let hX1 : HasTyT G n (S.g4 Γ l) (.bvar 1) S.I := .bvar _ 1 _ (S.lk_g4_1 Γ l)
  let hMX : HasTyT G n (S.g4 Γ l) (.app (.bvar 3) (.bvar 1)) (.pi (.app (.const S.f []) (.bvar 1)) (.sort l)) :=
    .app _ _ _ S.I (.pi (famApp0 S.f) (.sort l)) (.bvar _ 3 (motTy S.f S.I l) (S.lk_g4_3 Γ l)) hX1
  .conv _ _ (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (S.f + 1) []) (.bvar 1))) recB4 l
    (.app _ _ _ S.I (.app (.app (.bvar 4) (.bvar 0)) (.app (.const (S.f + 1) []) (.bvar 0)))
      (.bvar _ 2 S.minTy3 (S.lk_g4_2 Γ l)) hX1)
    (.app _ (.app (.bvar 3) (.bvar 1)) (.app (.bvar 3) (.bvar 1))
      (.app (.const (S.f + 1) []) (.bvar 1)) (.bvar 0) (.app (.const S.f []) (.bvar 1)) (.sort l)
      (.refl _ _ _ hMX)
      (.irr _ (.app (.const S.f []) (.bvar 1)) (.app (.const (S.f + 1) []) (.bvar 1)) (.bvar 0)
        (S.famTy hX1) (S.mkTy hX1) (.bvar _ 0 _ (S.lk_g4_0 Γ l))))

def lam4 (Γ : LCtx) (l : Level) :
    HasTyT G n (S.g3 Γ l) (.lam (famApp0 S.f) (.app (.bvar 2) (.bvar 1))) (.pi (famApp0 S.f) recB4) :=
  .lam _ _ .zero _ _ (S.famTy (.bvar _ 0 _ (S.lk_g3_0 Γ l))) (S.body Γ l)

def lam3 (Γ : LCtx) (l : Level) :
    HasTyT G n (S.g2 Γ l) (.lam S.I (.lam (famApp0 S.f) (.app (.bvar 2) (.bvar 1))))
      (.pi S.I (.pi (famApp0 S.f) recB4)) :=
  .lam _ _ S.uI _ _ (S.hI n _) (S.lam4 Γ l)

/-- the λ-recursor under its first binder. -/
def recT1 : Expr Nat := .lam (minTy S.f S.I) (.lam S.I (.lam (famApp0 S.f) (.app (.bvar 2) (.bvar 1))))

def recTy1 : Expr Nat := .pi (minTy S.f S.I) (.pi S.I (.pi (famApp0 S.f) recB4))

def lam2 (Γ : LCtx) (l : Level) : HasTyT G n (S.g1 Γ l) S.recT1 S.recTy1 :=
  .lam _ _ _ _ _ (S.minTyT Γ l) (S.lam3 Γ l)

/-- **the λ-recursor is typed at the recursor's type, in every context and at every level bound.** -/
def recTypedW (Γ : LCtx) (l : Level) : HasTyT G n Γ (recTG S.f S.I l) (recTyG S.f S.I l) :=
  .lam _ _ _ _ _ (S.motTyT Γ l) (S.lam2 Γ l)

/-- the λ-recursor is level-congruent: `recTG l ≡ recTG l'` when `l =ₙ l'`. -/
def recConvW (Γ : LCtx) (l l' : Level) (h : eqN l l') :
    ConvT G n Γ (recTG S.f S.I l) (recTG S.f S.I l') (recTyG S.f S.I l) :=
  .lam Γ (motTy S.f S.I l) (motTy S.f S.I l') S.recT1 S.recT1 S.recTy1
    (.imax S.uI (.imax .zero (.succ l)))
    (.pi Γ S.I S.I _ _ S.uI (.imax .zero (.succ l))
      (.refl _ _ _ (S.hI n Γ))
      (.pi _ (famApp0 S.f) (famApp0 S.f) (.sort l) (.sort l') .zero (.succ l)
        (.refl _ _ _ (S.famTy (.bvar _ 0 _ (by simp [lookupType, S.liftI]))))
        (.sorts _ l l' h)))
    (.refl _ _ _ (S.lam2 Γ l))

end RevShape

/-! ## a translation target: the shape, the six metatheory facts, the rows -/

/-- a target of the generic translation: a `RevShape` with the six metatheory facts and its three rows.
    `EnvWfT` is NOT required (the copy-only twin supplies `meta` from the predicate-level cores). -/
structure RevTwinTarget (σ : RevSig) (G : ResolvedEnv) extends RevShape σ G : Type where
  meta : TwinMeta G
  rows : ∀ n, TypedRowsWf G n

namespace RevTwinTarget

variable {σ : RevSig} {G : ResolvedEnv} {n : Nat}

/-! ### reading the twin: β by its rows, the `CE` calculus, the four β steps -/

theorem betaConvW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {A0 body arg S : Expr Nat}
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

theorem ceBetaW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {A0 body arg : Expr Nat} :
    CEW G n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) :=
  fun _ h => W.betaConvW hΓ h

theorem ceTransW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {e e' e'' : Expr Nat}
    (h1 : CEW G n Γ e e') (h2 : CEW G n Γ e' e'') : CEW G n Γ e e'' := by
  intro S h
  obtain ⟨c1⟩ := h1 S h
  obtain ⟨c2⟩ := h2 S (W.meta.ends hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 c2⟩

theorem ceAppLW {Γ : LCtx} {g g' : Expr Nat} (a : Expr Nat)
    (h1 : CEW G n Γ g g') : CEW G n Γ (.app g a) (.app g' a) := by
  intro S h
  obtain ⟨A, B, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := h1 _ hf
  exact ⟨retype (ConvT.app Γ g g' a a A B c (ConvT.refl Γ a A ha)) hcv⟩

theorem ceOfEqW {Γ : LCtx} {e e' : Expr Nat} (h : e = e') : CEW G n Γ e e' :=
  fun _ hS => ⟨h ▸ ConvT.refl _ _ _ hS⟩

/-- the four β steps of the λ-recursor. -/
theorem red4W (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (M' m' X' H' : Expr Nat) :
    CEW G n Γ (.app (.app (.app (.app (recTG W.f W.I l) M') m') X') H') (.app m' X') := by
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

/-! ### the ι cell, read in the twin -/

/-- an application whose head has a known Π type reads the argument's type off the head (the twin's type
    uniqueness, from its sort and Π rows). -/
theorem appInvKnownW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) {g a D C T' : Expr Nat}
    (hf : HasTyT G n Γ g (.pi D C)) (h : HasTyT G n Γ (.app g a) T') :
    Nonempty (HasTyT G n Γ a D) := by
  obtain ⟨A, B, hf', ha', _⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := W.meta.uniq hΓ hf' hf
  obtain ⟨⟨cA⟩, _⟩ := (W.rows n).piRow hΓ c
  exact ⟨hasTyT_of_tyConvT ha' cA⟩

/-- **the ι cell's agreement, read in the twin.** If `recTG l M' m' X' (mk x')` is typed, then `x' ≡ X' : I`:
    four Π-inversions against the known type of `recTG l`, then the twin's family row at `F`. -/
theorem iotaAgreeW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT G n Γ
      (.app (.app (.app (.app (recTG W.f W.I l) M') m') X') (.app (.const (W.f + 1) lsC) x')) T') :
    Nonempty (ConvT G n Γ x' X' W.I) := by
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := W.appInvKnownW hΓ (W.recTypedW Γ l) he1
  have own1 := HasTyT.app Γ (recTG W.f W.I l) M' _ _ (W.recTypedW Γ l) hM'
  obtain ⟨hm'⟩ := W.appInvKnownW hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := W.appInvKnownW hΓ own2 he3
  have own3 := HasTyT.app Γ _ X' _ _ own2 hX'
  obtain ⟨hH'⟩ := W.appInvKnownW hΓ own3 hlhs
  have hH'' : HasTyT G n Γ (.app (.const (W.f + 1) lsC) x') (.app (.const W.f []) X') := hH'
  have hinst : instantiateLevels lsC W.m₁.mtype = policyPi [W.I] (famApp0 W.f) := by
    rw [W.h1t, W.ctorTy_inst]; rfl
  obtain ⟨⟨-, -, hargs, hconv⟩⟩ := W.meta.spineInv hΓ
    (r := W.f + 1) (ls := lsC) (m := W.m₁) W.h1 (doms := [W.I]) (U := famApp0 W.f) hinst [x'] rfl hH''
  have hx' : HasTyT G n Γ x' W.I := hargs 0 x' W.I rfl rfl
  have hIP : instPrefix [x'] (famApp0 W.f) = .app (.const W.f []) x' := by
    simp [instPrefix, instantiate, lift_zero_idx]
  rw [hIP] at hconv
  obtain ⟨-, -, hc⟩ := (W.rows n).famAppRow hΓ (r := W.f) (m := revFamM W.I) (ls := []) (ls' := [])
    (xs := [x']) (xs' := [X']) (w := .zero) W.hfam rfl (W.famTy hx') hconv
  have hc' : ConvArgsT G n Γ (.pi W.I (.sort .zero)) [x'] [X'] := by
    rw [W.famTy_inst] at hc; exact hc
  cases hc' with
  | cons A B g g' fs fs' h hs => exact h

/-- **the translated ι cell.** `recTG l M' m' X' (mk x') ≡ m' x'` at every type of the redex. -/
theorem iotaConvW (W : RevTwinTarget σ G) {Γ : LCtx} (hΓ : CtxWfT G n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT G n Γ
      (.app (.app (.app (.app (recTG W.f W.I l) M') m') X') (.app (.const (W.f + 1) lsC) x')) T') :
    Nonempty (ConvT G n Γ
      (.app (.app (.app (.app (recTG W.f W.I l) M') m') X') (.app (.const (W.f + 1) lsC) x')) (.app m' x') T') := by
  obtain ⟨cxX⟩ := W.iotaAgreeW hΓ l lsC M' m' X' x' T' hlhs
  obtain ⟨c1⟩ := W.red4W hΓ l M' m' X' (.app (.const (W.f + 1) lsC) x') T' hlhs
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := W.appInvKnownW hΓ (W.recTypedW Γ l) he1
  have own1 := HasTyT.app Γ (recTG W.f W.I l) M' _ _ (W.recTypedW Γ l) hM'
  obtain ⟨hm'⟩ := W.appInvKnownW hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := W.appInvKnownW hΓ own2 he3
  have hX'' : HasTyT G n Γ X' W.I := by
    have h := hX'
    simp only [instantiate_of_closed W.I (W.hclI 0)] at h
    exact h
  have e : instantiate 0 M' (minTy W.f W.I) =
      .pi W.I (instantiate 1 (lift 0 1 M')
        (.app (.app (.bvar 1) (.bvar 0)) (.app (.const (W.f + 1) []) (.bvar 0)))) := by
    simp [minTy, instantiate, instantiate_of_closed W.I (W.hclI 0)]
  have hm'' : HasTyT G n Γ m' (.pi W.I (instantiate 1 (lift 0 1 M')
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const (W.f + 1) []) (.bvar 0))))) := by
    rw [e] at hm'; exact hm'
  have c2 := ConvT.app Γ m' m' X' x' _ _ (ConvT.refl Γ m' _ hm'') (ConvT.symm _ _ _ _ cxX)
  have hmX := HasTyT.app Γ m' X' _ _ hm'' hX''
  obtain ⟨cT⟩ := W.meta.uniq hΓ hmX (W.meta.ends hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 (retype c2 cT)⟩

end RevTwinTarget

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.RevShape.recTypedW
#print axioms Rcic.Syn.FamApp.Rev.RevShape.recConvW
#print axioms Rcic.Syn.FamApp.Rev.RevTwinTarget.iotaAgreeW
#print axioms Rcic.Syn.FamApp.Rev.RevTwinTarget.iotaConvW
