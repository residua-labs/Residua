import rcic.RcicFamAppRevEnv
import rcic.RcicCtxConvT

/-!
# RcicFamAppRevBack — the way back from the twin of ANY revealed singleton: the K-like cell, the round trip,
the identity transport

`RcicFamAppLiftBack` §5, §8, §9 did this for the fixture `riEnv`: the ι witness of `RI` at arbitrary arguments,
`recL l ≡ rec.{l}` by four η-expansions and the ungated K-like cell (`irr` against `mk X` at the same type, then ι),
the round trip `e ≡ bk (tr e)` on every typed term, and the context conversion. This module is the same for the
tier's generic B1 shape (`RevEnv`), with the layout of `RcicFamAppRevEnv` (the twin's axiom at the constructor's own
reference), so the way back `twin₁ → E` is the IDENTITY on terms: `bkTy`/`bkConv` re-read each rule in `E` (base
members and the family are the same members; the axiom `mk` is read as the constructor, same stored type and arity;
a base ι witness is re-packaged, `bkWitness`).

* §1 `revWAt`: the ι witness of the revealed singleton at arbitrary level and arguments; `revDerivedIota`.
* §2 the K-like cell: `kcellL : rec.{l} M m i h ≡ m i : M i h` under the four binders, by `irr`, `app`, ι, `tyConv`;
  `recTG_conv_rec : recTG l ≡ rec.{l} : recTyG l` in every context (η⁴ + the cell). The intermediate spine types are
  the fixture's with `Sort 0 ↦ I`, normalized by `instantiate_of_closed` (the only place the generic index type
  costs more than `rfl`).
* §3 the round trip `trConv_self : e ≡ tr e` at its type, for every term typed in `E` (the only non-identity leaf is the
  recursor); `ctxConv_tr`, `convT_tr_ctx`.
* §4 the way back `bkTy`/`bkConv`/`bkTyConv`/`bkCtxWf` (twin₁ → E).

closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin

set_option maxRecDepth 8192

namespace RevEnv

variable (R : RevEnv)

theorem liftI (c k : Nat) : lift c k R.I = R.I := lift_of_closed _ (R.hclI 0) c k

theorem recTyS_lift01 : lift 0 1 (recTyS R.f R.I) = recTyS R.f R.I := by
  simp [recTyS, recTyG, motTy, minTy, lift, R.liftI]

/-! ## §1 the ι witness of the revealed singleton at arbitrary arguments -/

/-- `rec.{l} M m X (mk x) ⇝ m x`: the witness with the level and the four arguments free. -/
def revWAt (l : Level) (lsC : List Level) (M m X x : Expr Nat) : IotaWitness R.E where
  recRef := R.f + 2
  ctorRef := R.f + 1
  ls := [l]
  lsC := lsC
  recMember := revRecM R.f R.I
  ctorMember := revCtorM R.f R.I
  hrec := R.hEf2
  hctor := R.hEf1
  hrecK := rfl
  hctorK := rfl
  preMajor := [M, m, X]
  fields := [x]
  ctorParams := []
  kinds := [.plain]
  minor := m
  hlen := rfl
  familyRef := R.f
  famMember := revFamM R.I
  hfam := R.hEf
  hfamK := rfl
  nparams := 0
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [R.I]
  ctorResult := famApp0 R.f
  hpeel := rfl
  hfamApp := by simp [isFamilyApp, appsSpine, occursConst]
  hkinds := analyzeFields_rev R.hIfree
  recDoms := [motTy R.f R.I (.param 0), minTy R.f R.I, R.I, famApp0 R.f]
  recBody := recB4
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := R.recTyS_lift01
  hctorClosed := R.revCtorTy_closed 0
  hlsLen := rfl
  ctorAfterParams := .pi R.I (famApp0 R.f)
  hctorAfter := by
    show applyTel [] (instantiateLevels [l] (revCtorTy R.f R.I)) = some _
    rw [R.shapeE.ctorTy_inst]
    rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem revWAt_lhs (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    iotaLhsOf (R.revWAt l lsC M m X x) =
      foldApps (.const (R.f + 2) [l]) [M, m, X, .app (.const (R.f + 1) lsC) x] := by
  simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps, revWAt]

theorem revWAt_rhs (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    iotaRhsOf (R.revWAt l lsC M m X x) = .app m x := by
  simp [iotaRhsOf, rhsArgs, foldApps, revWAt]

/-- the derived ι of the revealed singleton at arbitrary arguments. -/
def revDerivedIota (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    DerivedIota R.E (foldApps (.const (R.f + 2) [l]) [M, m, X, .app (.const (R.f + 1) lsC) x]) (.app m x) :=
  (R.revWAt_lhs l lsC M m X x) ▸ (R.revWAt_rhs l lsC M m X x) ▸ DerivedIota.of (R.revWAt l lsC M m X x)

/-! ## §2 the K-like cell, and `recTG l ≡ rec.{l}` -/

section KCell

variable {n : Nat}

/-- `rec.{l}` at its instantiated stored type, in every context. -/
def recConstL (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n Γ (.const (R.f + 2) [l]) (recTyG R.f R.I l) := by
  have h := HasTyT.const Γ (R.f + 2) [l] (revRecM R.f R.I) R.hEf2 rfl hl
  have e : instantiateLevels [l] (revRecM R.f R.I).mtype = recTyG R.f R.I l := R.shapeE.recTyS_inst l
  rw [e] at h
  exact h

/-- `rec.{l} M : Π (m : minTy) (i : I) (h : F i), M i h` under `[h, i, m, M]` (`M = bvar 3`, hence `bvar 6` under
    the three further binders). -/
def rec1L (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 3))
      (.pi R.shapeE.minTy3 (.pi R.I (.pi (famApp0 R.f) (.app (.app (.bvar 6) (.bvar 1)) (.bvar 0))))) := by
  have h := HasTyT.app (R.shapeE.g4 Γ l) _ (.bvar 3) _ _ (R.recConstL _ l hl)
    (.bvar _ 3 (motTy R.f R.I l) (R.shapeE.lk_g4_3 Γ l))
  simpa [instantiate0, instantiate, lift, minTy, RevShape.minTy3, instantiate_of_closed R.I (R.hclI 0)] using h

/-- `rec.{l} M m : Π (i : I) (h : F i), M i h` under `[h, i, m, M]`. -/
def rec2L (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 3)) (.bvar 2))
      (.pi R.I (.pi (famApp0 R.f) (.app (.app (.bvar 5) (.bvar 1)) (.bvar 0)))) := by
  have h := HasTyT.app (R.shapeE.g4 Γ l) _ (.bvar 2) _ _ (R.rec1L Γ l hl)
    (.bvar _ 2 R.shapeE.minTy3 (R.shapeE.lk_g4_2 Γ l))
  simpa [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)] using h

/-- `rec.{l} M m X : Π (h : F X), M X h` under `[h, X, m, M]`. -/
def rec3L (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1])
      (.pi (.app (.const R.f []) (.bvar 1)) (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))) := by
  have h := HasTyT.app (R.shapeE.g4 Γ l) _ (.bvar 1) _ _ (R.rec2L Γ l hl)
    (.bvar _ 1 R.I (R.shapeE.lk_g4_1 Γ l))
  simpa [instantiate0, instantiate, lift, foldApps] using h

/-- **the K-like cell at level `l`, under any context**: `rec.{l} M m X h ≡ m X : M X h`, by `irr` against
    `mk X` at the same type, `app`, ι at the constructor, and `tyConv`. -/
def kcellL (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n (R.shapeE.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
  let S := R.shapeE
  let hX : HasTyT R.E n (S.g4 Γ l) (.bvar 1) R.I := .bvar _ 1 _ (S.lk_g4_1 Γ l)
  let hRI : HasTyT R.E n (S.g4 Γ l) (.app (.const R.f []) (.bvar 1)) (.sort .zero) := S.famTy hX
  let hh : HasTyT R.E n (S.g4 Γ l) (.bvar 0) (.app (.const R.f []) (.bvar 1)) := .bvar _ 0 _ (S.lk_g4_0 Γ l)
  let hmk : HasTyT R.E n (S.g4 Γ l) (.app (.const (R.f + 1) []) (.bvar 1)) (.app (.const R.f []) (.bvar 1)) :=
    S.mkTy hX
  let cIrr : ConvT R.E n (S.g4 Γ l) (.bvar 0) (.app (.const (R.f + 1) []) (.bvar 1))
      (.app (.const R.f []) (.bvar 1)) :=
    .irr _ _ _ _ hRI hh hmk
  let h3 := R.rec3L Γ l hl
  let hMid : HasTyT R.E n (S.g4 Γ l)
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    HasTyT.app (S.g4 Γ l) _ (.app (.const (R.f + 1) []) (.bvar 1)) _ _ h3 hmk
  let hRhs : HasTyT R.E n (S.g4 Γ l) (.app (.bvar 2) (.bvar 1))
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    HasTyT.app (S.g4 Γ l) (.bvar 2) (.bvar 1) _ _ (.bvar _ 2 S.minTy3 (S.lk_g4_2 Γ l)) hX
  let hMX : HasTyT R.E n (S.g4 Γ l) (.app (.bvar 3) (.bvar 1))
      (.pi (.app (.const R.f []) (.bvar 1)) (.sort l)) :=
    HasTyT.app (S.g4 Γ l) (.bvar 3) (.bvar 1) _ _ (.bvar _ 3 (motTy R.f R.I l) (S.lk_g4_3 Γ l)) hX
  let step1 : ConvT R.E n (S.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
    .app _ _ _ (.bvar 0) (.app (.const (R.f + 1) []) (.bvar 1)) _ _ (.refl _ _ _ h3) cIrr
  let cIota : ConvT R.E n (S.g4 Γ l)
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    .iota _ _ _ _ (R.revDerivedIota l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)) hMid hRhs
  let tyFix : ConvT R.E n (S.g4 Γ l) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1)))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort l) :=
    .app _ _ _ (.app (.const (R.f + 1) []) (.bvar 1)) (.bvar 0) _ _ (.refl _ _ _ hMX) (.symm _ _ _ _ cIrr)
  .trans _ _ _ _ _ step1 (.tyConv _ _ _ _ _ l cIota tyFix)

/-- the fully η-expanded recursor, `λ M m i h. rec.{l} M m i h`. -/
def recE (l : Level) : Expr Nat :=
  .lam (motTy R.f R.I l) (.lam (minTy R.f R.I) (.lam R.I (.lam (famApp0 R.f)
    (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))))

/-- `recE l ≡ recTG l`: the K-like cell under the four binders. -/
def recE_conv_recTG (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (R.recE l) (recTG R.f R.I l) (recTyG R.f R.I l) :=
  let S := R.shapeE
  .lam Γ (motTy R.f R.I l) (motTy R.f R.I l) _ _ _ _ (.refl _ _ _ (S.motTyT Γ l))
    (.lam _ (minTy R.f R.I) (minTy R.f R.I) _ _ _ _ (.refl _ _ _ (S.minTyT Γ l))
      (.lam _ R.I R.I _ _ _ R.uI (.refl _ _ _ (S.hI n _))
        (.lam _ (famApp0 R.f) (famApp0 R.f) _ _ recB4 .zero
          (.refl _ _ _ (S.famTy (.bvar _ 0 _ (S.lk_g3_0 Γ l)))) (R.kcellL Γ l hl))))

/-- `rec.{l} M : Π (m : minTy) (i : I) (h : F i), M i h` under `[M]`. -/
def recEta1 (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g1 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 0)) R.shapeE.recTy1 := by
  have h := HasTyT.app (R.shapeE.g1 Γ l) _ (.bvar 0) _ _ (R.recConstL _ l hl)
    (.bvar _ 0 (motTy R.f R.I l) (by simp [lookupType, RevShape.g1, R.shapeE.lift_motTy]))
  simpa [instantiate0, instantiate, lift, minTy, RevShape.recTy1, instantiate_of_closed R.I (R.hclI 0)] using h

/-- `rec.{l} M m : Π (i : I) (h : F i), M i h` under `[m, M]`. -/
def recEta2 (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g2 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 1)) (.bvar 0))
      (.pi R.I (.pi (famApp0 R.f) recB4)) := by
  have h1 := HasTyT.app (R.shapeE.g2 Γ l) _ (.bvar 1) _ _ (R.recConstL _ l hl)
    (.bvar _ 1 (motTy R.f R.I l) (by simp [lookupType, RevShape.g2, RevShape.g1, R.shapeE.lift_motTy]))
  have h2 := HasTyT.app (R.shapeE.g2 Γ l) _ (.bvar 0) _ _ h1
    (.bvar _ 0 (instantiate 0 (.bvar 1) (minTy R.f R.I))
      (by simp [lookupType, RevShape.g2, minTy, lift, instantiate, R.liftI, instantiate_of_closed R.I (R.hclI 0)]))
  simpa [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)] using h2

/-- `rec.{l} M m X : Π (h : F X), M X h` under `[X, m, M]`. -/
def recEta3 (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g3 Γ l) (.app (.app (.app (.const (R.f + 2) [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.pi (famApp0 R.f) recB4) := by
  have h1 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 2) _ _ (R.recConstL _ l hl)
    (.bvar _ 2 (motTy R.f R.I l)
      (by simp [lookupType, RevShape.g3, RevShape.g2, RevShape.g1, R.shapeE.lift_motTy]))
  have h2 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 1) _ _ h1
    (.bvar _ 1 (instantiate 0 (.bvar 2) (minTy R.f R.I))
      (by simp [lookupType, RevShape.g3, RevShape.g2, minTy, lift, instantiate, R.liftI,
        instantiate_of_closed R.I (R.hclI 0)]))
  have h3 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 0) _ _ h2
    (.bvar _ 0 (instantiate 0 (Expr.bvar 1) (instantiate (0 + 1) (lift 0 1 (Expr.bvar 2)) R.I))
      (by simp [lookupType, RevShape.g3, R.liftI, instantiate_of_closed R.I (R.hclI 0)]))
  simpa [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)] using h3

/-- `rec.{l} ≡ recE l`: four η-expansions, each under the binders already opened. -/
def rec_conv_recE (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (.const (R.f + 2) [l]) (R.recE l) (recTyG R.f R.I l) :=
  let S := R.shapeE
  let h0 := R.recConstL Γ l hl
  let h1 := R.recEta1 Γ l hl
  let h2 := R.recEta2 Γ l hl
  let h3 := R.recEta3 Γ l hl
  -- η₄ under [X, m, M]: rec M m X ≡ λ h. rec M m X h
  let e4 : ConvT R.E n (S.g3 Γ l) (.app (.app (.app (.const (R.f + 2) [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.lam (famApp0 R.f) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))
      (.pi (famApp0 R.f) recB4) :=
    .symm _ _ _ _ (.eta (S.g3 Γ l) _ _ _ h3)
  -- η₃ under [m, M]: rec M m ≡ λ X. rec M m X, then the body by e4
  let e3 : ConvT R.E n (S.g2 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 1)) (.bvar 0))
      (.lam R.I (.lam (famApp0 R.f) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))
      (.pi R.I (.pi (famApp0 R.f) recB4)) :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta (S.g2 Γ l) _ _ _ h2))
      (.lam (S.g2 Γ l) R.I R.I _ _ _ R.uI (.refl _ _ _ (S.hI n _)) e4)
  let e2 : ConvT R.E n (S.g1 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 0))
      (.lam (minTy R.f R.I) (.lam R.I (.lam (famApp0 R.f)
        (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))) S.recTy1 :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta (S.g1 Γ l) _ _ _ h1))
      (.lam (S.g1 Γ l) (minTy R.f R.I) (minTy R.f R.I) _ _ _ _ (.refl _ _ _ (S.minTyT Γ l)) e3)
  .trans _ _ _ _ _ (.symm _ _ _ _ (.eta Γ _ _ _ h0))
    (.lam Γ (motTy R.f R.I l) (motTy R.f R.I l) _ _ _ _ (.refl _ _ _ (S.motTyT Γ l)) e2)

/-- **`recTG l ≡ rec.{l}` at the recursor's type, in every context**: the λ-recursor IS the recursor, up to
    conversion, in the environment of interest. -/
def recTG_conv_rec (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (recTG R.f R.I l) (.const (R.f + 2) [l]) (recTyG R.f R.I l) :=
  .symm _ _ _ _ (.trans _ _ _ _ _ (R.rec_conv_recE Γ l hl) (R.recE_conv_recTG Γ l hl))

end KCell

/-! ## §3 the round trip on `E`'s typed terms -/

section RoundTrip

variable {n : Nat}

/-- **the round trip on terms**: every term typed in `E` converts to its translation, at its type. The only
    non-identity leaf is the recursor, `rec.{l} ≡ recTG l` (§2). No row is assumed. -/
theorem trConv_self : {Γ : LCtx} → {e A : Expr Nat} → HasTyT R.E n Γ e A →
    Nonempty (ConvT R.E n Γ e (tr R.f R.I e) A)
  | _, _, _, .sort Γ l => ⟨.refl _ _ _ (.sort Γ l)⟩
  | _, _, _, .bvar Γ i A h => ⟨.refl _ _ _ (.bvar Γ i A h)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf => by
      rcases R.members_class hres with hlt | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨.refl _ _ _ (.const Γ r ls m hres hlen hwf)⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨.refl _ _ _ (.const Γ _ ls _ hres hlen hwf)⟩
      · rw [tr_const_ne R.f R.I (by omega)]
        exact ⟨.refl _ _ _ (.const Γ _ ls _ hres hlen hwf)⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        have e : instantiateLevels [l] (revRecM R.f R.I).mtype = recTyG R.f R.I l := R.shapeE.recTyS_inst l
        rw [tr_rec, e]
        exact ⟨.symm _ _ _ _ (R.recTG_conv_rec Γ l hwf)⟩
  | _, _, _, .pi Γ A u B v hA hB => by
      obtain ⟨cA⟩ := trConv_self hA
      obtain ⟨cB⟩ := trConv_self hB
      exact ⟨.pi Γ A (tr R.f R.I A) B (tr R.f R.I B) u v cA cB⟩
  | _, _, _, .lam Γ A u body B hA hbody => by
      obtain ⟨cA⟩ := trConv_self hA
      obtain ⟨cb⟩ := trConv_self hbody
      exact ⟨.lam Γ A (tr R.f R.I A) body (tr R.f R.I body) B u cA cb⟩
  | _, _, _, .app Γ g a A B hf ha => by
      obtain ⟨cf⟩ := trConv_self hf
      obtain ⟨ca⟩ := trConv_self ha
      exact ⟨.app Γ g (tr R.f R.I g) a (tr R.f R.I a) A B cf ca⟩
  | _, _, _, .letE Γ A u value B body hA hv hb => by
      obtain ⟨cA⟩ := trConv_self hA
      obtain ⟨cv⟩ := trConv_self hv
      obtain ⟨cb⟩ := trConv_self hb
      exact ⟨.letE Γ A (tr R.f R.I A) value (tr R.f R.I value) body (tr R.f R.I body) B u cA cv cb⟩
  | _, _, _, .lit Γ t T hexp => ⟨.refl _ _ _ (.lit Γ t T hexp)⟩
  | _, _, _, .conv Γ e A B u h hc => by
      obtain ⟨c⟩ := trConv_self h
      exact ⟨.tyConv Γ e (tr R.f R.I e) A B u c hc⟩

/-- **the round trip on contexts**: `tr Γ` converts to `Γ`, pointwise by the term round trip. -/
theorem ctxConv_tr : {Γ : LCtx} → CtxWfT R.E n Γ → Nonempty (CtxConvT R.E n (trCtx R.f R.I Γ) Γ)
  | _, .nil => ⟨.nil⟩
  | _, .assumption Γ A u hΓ hA => by
      obtain ⟨hcc⟩ := ctxConv_tr hΓ
      obtain ⟨cA⟩ := R.trConv_self hA
      have hA' : HasTyT R.E n Γ (tr R.f R.I A) (.sort u) := (NativeValleys.convEnds R.hW hΓ cA).2.1
      exact ⟨.assumption hcc hA' hA (.symm _ _ _ _ cA)⟩
  | _, .letBinding Γ A u v hΓ hA hv => by
      obtain ⟨hcc⟩ := ctxConv_tr hΓ
      obtain ⟨cA⟩ := R.trConv_self hA
      obtain ⟨cv⟩ := R.trConv_self hv
      have hA' : HasTyT R.E n Γ (tr R.f R.I A) (.sort u) := (NativeValleys.convEnds R.hW hΓ cA).2.1
      have hcv : ConvT R.E n Γ (tr R.f R.I v) v (tr R.f R.I A) :=
        .tyConv _ _ _ _ _ u (.symm _ _ _ _ cv) cA
      exact ⟨.letBinding hcc hA' hA (.symm _ _ _ _ cA) hv hcv⟩

/-- a conversion in `tr Γ` is one in `Γ`. -/
theorem convT_tr_ctx {Γ : LCtx} (hΓ : CtxWfT R.E n Γ) {a b T : Expr Nat}
    (c : ConvT R.E n (trCtx R.f R.I Γ) a b T) : Nonempty (ConvT R.E n Γ a b T) := by
  obtain ⟨hcc⟩ := R.ctxConv_tr hΓ
  exact ⟨convT_ctx (envClosed_of_envWfT R.hW) hcc c⟩

end RoundTrip

/-! ## §4 the way back, `twin₁ → E`: the identity on terms -/

section Back

variable {n : Nat}

/-- a recursor member of the twin is a base recursor. -/
theorem twin₁_rec_lt (w : IotaWitness R.twin₁) : w.recRef < R.f := by
  rcases R.twin₁_class w.hrec with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · have hk := w.hrecK; rw [h] at hk; exact MemberClass.noConfusion hk
  · have hk := w.hrecK; rw [h] at hk; exact MemberClass.noConfusion hk

/-- a ι witness of the twin is a ι witness of `E`: the three member lookups move, nothing else. -/
def bkWitness (w : IotaWitness R.twin₁) : IotaWitness R.E :=
  { w with
    hrec := by rw [← R.twin₁_agree _ (R.twin₁_rec_lt w)]; exact w.hrec
    hctor := by rw [← R.twin₁_agree _ (witness_refs_lt w (R.twin₁_rec_lt w)).1]; exact w.hctor
    hfam := by rw [← R.twin₁_agree _ (witness_refs_lt w (R.twin₁_rec_lt w)).2]; exact w.hfam }

/-- a derived ι of the twin is a derived ι of `E` at the same endpoints. -/
def bkIota {lhs rhs : Expr Nat} : DerivedIota R.twin₁ lhs rhs → DerivedIota R.E lhs rhs
  | .of w => .of (R.bkWitness w)

/-- a member read in the twin is read in `E`, at the same stored type (the axiom `mk` becomes the
    constructor). -/
theorem bkConst (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) :
    Nonempty (HasTyT R.E n Γ (.const r ls) (instantiateLevels ls m.mtype)) := by
  rcases R.twin₁_class hres with ⟨hlt, h0⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨.const Γ r ls m (by rw [R.hbase r hlt]; exact h0) hlen hwf⟩
  · exact ⟨.const Γ R.f ls (revFamM R.I) R.hEf hlen hwf⟩
  · exact ⟨.const Γ (R.f + 1) ls (revCtorM R.f R.I) R.hEf1 hlen hwf⟩

theorem bkConsts (Γ : LCtx) (r : Nat) (ls ls' : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls') :
    Nonempty (ConvT R.E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)) := by
  rcases R.twin₁_class hres with ⟨hlt, h0⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨.consts Γ r ls ls' m (by rw [R.hbase r hlt]; exact h0) hlen hwf hwf' h⟩
  · exact ⟨.consts Γ R.f ls ls' (revFamM R.I) R.hEf hlen hwf hwf' h⟩
  · exact ⟨.consts Γ (R.f + 1) ls ls' (revCtorM R.f R.I) R.hEf1 hlen hwf hwf' h⟩

/-- a member of the twin with a body is a base member of `E`. -/
theorem bkBody {r : Nat} {m : CheckedMember} {b : Expr Nat} (hres : R.twin₁.members r = some m)
    (hbody : m.body = some b) : R.E.members r = some m := by
  rcases R.twin₁_class hres with ⟨hlt, h0⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rw [R.hbase r hlt]; exact h0
  · exact Option.noConfusion hbody
  · exact Option.noConfusion hbody

mutual
theorem bkTy : {Γ : LCtx} → {e A : Expr Nat} → HasTyT R.twin₁ n Γ e A → CtxWfT R.E n Γ →
    Nonempty (HasTyT R.E n Γ e A)
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ => ⟨.bvar _ i A h⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => R.bkConst Γ r ls m hres hlen hwf
  | _, _, _, .pi Γ A u B v hA hB, hΓ => by
      obtain ⟨hA'⟩ := bkTy hA hΓ
      obtain ⟨hB'⟩ := bkTy hB (.assumption _ A u hΓ hA')
      exact ⟨.pi _ A u B v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ => by
      obtain ⟨hA'⟩ := bkTy hA hΓ
      obtain ⟨hb'⟩ := bkTy hbody (.assumption _ A u hΓ hA')
      exact ⟨.lam _ A u body B hA' hb'⟩
  | _, _, _, .app Γ g a A B hf ha, hΓ => by
      obtain ⟨hf'⟩ := bkTy hf hΓ
      obtain ⟨ha'⟩ := bkTy ha hΓ
      exact ⟨.app _ g a A B hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ => by
      obtain ⟨hA'⟩ := bkTy hA hΓ
      obtain ⟨hv'⟩ := bkTy hv hΓ
      obtain ⟨hb'⟩ := bkTy hb (.letBinding _ A u value hΓ hA' hv')
      exact ⟨.letE _ A u value B body hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ => by
      obtain ⟨h⟩ := bkTy hexp hΓ
      exact ⟨.lit _ t T h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ => by
      obtain ⟨h'⟩ := bkTy h hΓ
      obtain ⟨hc'⟩ := bkConv hc hΓ
      exact ⟨.conv _ e A B u h' hc'⟩

theorem bkConv : {Γ : LCtx} → {a b A : Expr Nat} → ConvT R.twin₁ n Γ a b A → CtxWfT R.E n Γ →
    Nonempty (ConvT R.E n Γ a b A)
  | _, _, _, _, .refl Γ a A h, hΓ => by
      obtain ⟨h'⟩ := bkTy h hΓ
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ => by
      obtain ⟨h'⟩ := bkConv h hΓ
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ => by
      obtain ⟨h1'⟩ := bkConv h1 hΓ
      obtain ⟨h2'⟩ := bkConv h2 hΓ
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ => by
      obtain ⟨hA'⟩ := bkTy hA hΓ
      obtain ⟨hb'⟩ := bkTy hbody (.assumption _ A u hΓ hA')
      obtain ⟨ha'⟩ := bkTy harg hΓ
      exact ⟨.beta _ A body arg B u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ => by
      obtain ⟨hA'⟩ := bkTy hA hΓ
      obtain ⟨hv'⟩ := bkTy hv hΓ
      obtain ⟨hb'⟩ := bkTy hb (.letBinding _ A u value hΓ hA' hv')
      exact ⟨.zeta _ A value body B u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ => by
      obtain ⟨hv'⟩ := bkTy hv hΓ
      exact ⟨.zetaLocal _ i A v hval hty hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb, hΓ => by
      obtain ⟨hb'⟩ := bkTy hb hΓ
      exact ⟨.delta _ r ls m b (R.bkBody hres hbody) hbody htr hlen hwf hb'⟩
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, hΓ => by
      obtain ⟨hl'⟩ := bkTy hl hΓ
      obtain ⟨hr'⟩ := bkTy hr hΓ
      exact ⟨.iota _ _ _ _ (R.bkIota h) hl' hr'⟩
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ => by
      obtain ⟨h'⟩ := bkTy hexp hΓ
      exact ⟨.lit _ t exp T h h'⟩
  | _, _, _, _, .app Γ g g' a b A B h1 h2, hΓ => by
      obtain ⟨h1'⟩ := bkConv h1 hΓ
      obtain ⟨h2'⟩ := bkConv h2 hΓ
      exact ⟨.app _ g g' a b A B h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ => by
      obtain ⟨hA'⟩ := bkConv hA hΓ
      obtain ⟨hb'⟩ := bkConv hb (.assumption _ A u hΓ (NativeValleys.convEnds R.hW hΓ hA').1)
      exact ⟨.lam _ A A' b b' B u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ => by
      obtain ⟨hA'⟩ := bkConv hA hΓ
      obtain ⟨hB'⟩ := bkConv hB (.assumption _ A u hΓ (NativeValleys.convEnds R.hW hΓ hA').1)
      exact ⟨.pi _ A A' B B' u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ => by
      obtain ⟨hA'⟩ := bkConv hA hΓ
      obtain ⟨hv'⟩ := bkConv hv hΓ
      obtain ⟨hb'⟩ := bkConv hb (.letBinding _ A u v hΓ
        (NativeValleys.convEnds R.hW hΓ hA').1 (NativeValleys.convEnds R.hW hΓ hv').1)
      exact ⟨.letE _ A A' v v' b b' B u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ =>
      R.bkConsts Γ r ls ls' m hres hlen hwf hwf' h
  | _, _, _, _, .eta Γ g A B h, hΓ => by
      obtain ⟨h'⟩ := bkTy h hΓ
      exact ⟨.eta _ g A B h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ => by
      obtain ⟨hP'⟩ := bkTy hP hΓ
      obtain ⟨hp'⟩ := bkTy hp hΓ
      obtain ⟨hq'⟩ := bkTy hq hΓ
      exact ⟨.irr _ P p q hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ => by
      obtain ⟨h'⟩ := bkConv h hΓ
      obtain ⟨hA'⟩ := bkConv hA hΓ
      exact ⟨.tyConv _ a b A A' u h' hA'⟩
end

theorem bkTyConv {Γ : LCtx} {a b : Expr Nat} (h : TyConvT R.twin₁ n Γ a b) (hΓ : CtxWfT R.E n Γ) :
    Nonempty (TyConvT R.E n Γ a b) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := R.bkConv h hΓ; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem bkCtxWf {Γ : LCtx} (h : CtxWfT R.twin₁ n Γ) : Nonempty (CtxWfT R.E n Γ) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := R.bkTy hA hΓ'
      exact ⟨.assumption _ A u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := R.bkTy hA hΓ'
      obtain ⟨hv'⟩ := R.bkTy hv hΓ'
      exact ⟨.letBinding _ A u v hΓ' hA' hv'⟩

end Back

end RevEnv

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.RevEnv.revDerivedIota
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.kcellL
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.recTG_conv_rec
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.trConv_self
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.ctxConv_tr
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.bkConv
