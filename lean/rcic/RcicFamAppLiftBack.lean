import rcic.RcicFamAppTwin
import rcic.RcicEtaKDecide
import rcic.RcicCtxConvT
import rcic.RcicParRedTSubst

/-!
# fable-famapp — the way back from the consistent twin, under `riEnv`'s Π row

(D3, in progress.) `bk : cEnv → riEnv` on terms sends `mk₂ ↦ mk`, `rec₂ ↦ bkRec := λ M m₁ m₂ X h.
rec.{0} M m₁ X h`, literals to their expansions, and everything else to itself. Every derivation of
`cEnv` is sent to a derivation of `riEnv` ASSUMING `riEnv`'s Π row (`PiRowField riEnv n`; the sort
row is landed, `riSortRow_chain`), because the ι cell of `rec₂` back-translates to five β steps and
a ι step of `rec.{0}` whose common type is read by type uniqueness (DT-012 from the two rows).
closure_claim = 0.
-/

namespace Rcic.Syn.FamApp

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Syn
open Rcic.Syn.ClassC

/-! ## §1 `bk` on terms -/

/-- `bk cMin2 = Π X, M X (mk X)` under `[m₁, M]`. -/
def cMin2R : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 2) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))

/-- `λ (M : Π X, RI X → Sort 0) (m₁ : Π X, M X (mk X)) (m₂ : Π X, M X (mk X)) (X : Sort 0) (h : RI X).
    rec.{0} M m₁ X h`. -/
def bkRec : Expr Nat :=
  .lam cMotTy (.lam cMin1 (.lam cMin2R (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
    (foldApps (.const 2 [.zero]) [.bvar 4, .bvar 3, .bvar 1, .bvar 0])))))

/-- the image of a literal's expansion: `natExpand t` with `mk₂ ↦ mk`. -/
def bkNat : Nat → Expr Nat
  | 0 => .const 1 []
  | t + 1 => .app (.const 1 []) (bkNat t)

def bk : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => if r = 2 then .const 1 ls else if r = 3 then bkRec else .const r ls
  | .app f x => .app (bk f) (bk x)
  | .lam a b => .lam (bk a) (bk b)
  | .pi a b => .pi (bk a) (bk b)
  | .letE a v b => .letE (bk a) (bk v) (bk b)
  | .lit t => bkNat t

def bkDecl : LocalDecl → LocalDecl
  | .assumption a => .assumption (bk a)
  | .letBinding a v => .letBinding (bk a) (bk v)

def bkCtx (Γ : LCtx) : LCtx := Γ.map bkDecl

theorem bk_natExpand (t : Nat) : bk (natExpand t) = bkNat t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [natExpand, litSucc, bk, bkNat, ih]; rfl

theorem bkRec_closed : ClosedE 0 bkRec := by
  simp [bkRec, cMotTy, cMin1, cMin2R, ClosedE, foldApps]

theorem bkNat_closed (t : Nat) : ClosedE 0 (bkNat t) := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨trivial, ih⟩

theorem bk_lift (k : Nat) : (e : Expr Nat) → ∀ c, bk (lift c k e) = lift c k (bk e)
  | .bvar i, c => by
      by_cases h : c ≤ i <;> simp [lift, bk, h]
  | .sort _, _ => rfl
  | .const r ls, c => by
      simp only [bk]
      split
      · rfl
      · split
        · rw [lift_closedE k bkRec bkRec_closed (Nat.zero_le c)]
        · rfl
  | .app f x, c => by simp only [lift, bk, bk_lift k f c, bk_lift k x c]
  | .lam a b, c => by simp only [lift, bk, bk_lift k a c, bk_lift k b (c + 1)]
  | .pi a b, c => by simp only [lift, bk, bk_lift k a c, bk_lift k b (c + 1)]
  | .letE a v b, c => by
      simp only [lift, bk, bk_lift k a c, bk_lift k v c, bk_lift k b (c + 1)]
  | .lit t, c => by
      simp only [lift, bk]
      rw [lift_closedE k (bkNat t) (bkNat_closed t) (Nat.zero_le c)]

theorem bk_instantiate (s : Expr Nat) : (e : Expr Nat) → ∀ j,
    bk (instantiate j s e) = instantiate j (bk s) (bk e)
  | .bvar i, j => by
      by_cases h1 : i = j
      · subst h1; simp [instantiate, bk]
      · by_cases h2 : j < i
        · simp [instantiate, bk, h1, h2]
        · simp [instantiate, bk, h1, h2]
  | .sort _, _ => rfl
  | .const r ls, j => by
      simp only [bk]
      split
      · rfl
      · split
        · rw [instantiate_closedE (bk s) bkRec bkRec_closed (Nat.zero_le j)]
        · rfl
  | .app f x, j => by simp only [instantiate, bk, bk_instantiate s f j, bk_instantiate s x j]
  | .lam a b, j => by
      simp only [instantiate, bk, bk_instantiate s a j, bk_instantiate (lift 0 1 s) b (j + 1), bk_lift]
  | .pi a b, j => by
      simp only [instantiate, bk, bk_instantiate s a j, bk_instantiate (lift 0 1 s) b (j + 1), bk_lift]
  | .letE a v b, j => by
      simp only [instantiate, bk, bk_instantiate s a j, bk_instantiate s v j,
        bk_instantiate (lift 0 1 s) b (j + 1), bk_lift]
  | .lit t, j => by
      simp only [instantiate, bk]
      rw [instantiate_closedE (bk s) (bkNat t) (bkNat_closed t) (Nat.zero_le j)]

theorem bk_instantiate0 (s e : Expr Nat) : bk (instantiate0 s e) = instantiate0 (bk s) (bk e) :=
  bk_instantiate s e 0

theorem bk_foldApps (f : Expr Nat) (xs : List (Expr Nat)) :
    bk (foldApps f xs) = foldApps (bk f) (xs.map bk) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [foldApps, ih, bk, List.map]

theorem lookupType_bkCtx (Γ : LCtx) (i : Nat) :
    lookupType (bkCtx Γ) i = (lookupType Γ i).map bk := by
  unfold lookupType bkCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp [bkDecl, bk_lift]
      | letBinding a v => simp [bkDecl, bk_lift]

theorem lookupValue_bkCtx (Γ : LCtx) (i : Nat) :
    lookupValue (bkCtx Γ) i = (lookupValue Γ i).map bk := by
  unfold lookupValue bkCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => rfl
      | letBinding a v => simp [bkDecl, bk_lift]

/-! ## §2 the members of `cEnv`, read -/

theorem cEnv_class {r : Nat} {m : CheckedMember} (h : cEnv.members r = some m) :
    (r = 3 ∧ m = cRec) ∨ (r = 2 ∧ m = riCtor) ∨ (r = 1 ∧ m = riCtor) ∨ (r = 0 ∧ m = riFam) := by
  rw [cEnv_members] at h
  by_cases h3 : r = 3
  · rw [if_pos h3] at h; exact Or.inl ⟨h3, (Option.some.inj h).symm⟩
  · rw [if_neg h3] at h
    by_cases h2 : r = 2
    · rw [if_pos h2] at h; exact Or.inr (Or.inl ⟨h2, (Option.some.inj h).symm⟩)
    · rw [if_neg h2] at h
      by_cases h1 : r = 1
      · rw [if_pos h1] at h; exact Or.inr (Or.inr (Or.inl ⟨h1, (Option.some.inj h).symm⟩))
      · rw [if_neg h1] at h
        by_cases h0 : r = 0
        · rw [if_pos h0] at h; exact Or.inr (Or.inr (Or.inr ⟨h0, (Option.some.inj h).symm⟩))
        · rw [if_neg h0] at h; exact Option.noConfusion h

theorem cEnv_noBody {r : Nat} {m : CheckedMember} (h : cEnv.members r = some m) : m.body = none := by
  rcases cEnv_class h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem cEnv_recursor {r : Nat} {m : CheckedMember} (h : cEnv.members r = some m)
    (hk : m.mclass = .recursorM) : r = 3 ∧ m = cRec := by
  rcases cEnv_class h with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem cEnv_ctor {r : Nat} {m : CheckedMember} (h : cEnv.members r = some m)
    (hk : m.mclass = .constructorM) : (r = 2 ∨ r = 1) ∧ m = riCtor := by
  rcases cEnv_class h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inr rfl, rfl⟩
  · exact absurd hk (by decide)

theorem cEnv_family {r : Nat} {m : CheckedMember} (h : cEnv.members r = some m)
    (hk : m.mclass = .inductiveM) : r = 0 ∧ m = riFam := by
  rcases cEnv_class h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h'
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact h'

/-- every ι witness of `cEnv` is `rec₂ M m₁ m₂ X (mk_i x) ⇝ m_i x`, for `i = 1` or `i = 2`. -/
theorem cIota_inv (w : IotaWitness cEnv) :
    ∃ (ls lsC : List Level) (M m₁ m₂ X x : Expr Nat), ls.length = 0 ∧
      ((iotaLhsOf w = foldApps (.const 3 ls) [M, m₁, m₂, X, foldApps (.const 1 lsC) [x]] ∧
          iotaRhsOf w = .app m₁ x) ∨
        (iotaLhsOf w = foldApps (.const 3 ls) [M, m₁, m₂, X, foldApps (.const 2 lsC) [x]] ∧
          iotaRhsOf w = .app m₂ x)) := by
  obtain ⟨recRef, ctorRef, ls, lsC, recMember, ctorMember, hrec, hctor, hrecK, hctorK,
    preMajor, fields, ctorParams, kinds, minor, hlen, familyRef, famMember, hfam, hfamK,
    nparams, nindices, nMinors, ctorIdx, hctorParams, hnpar, hnidx, hnmin, hidx, hctorIdx,
    hrecIdx, hpre, hminor, ctorDoms, ctorResult, hpeel, hfamApp, hkinds, recDoms, recBody,
    hpeelRec, hrecBody, hmajorTy, hrecClosed, hctorClosed, hlsLen, ctorAfterParams,
    hctorAfter, hctorTel, hfamTel, hresTel⟩ := w
  obtain ⟨rfl, rfl⟩ := cEnv_recursor hrec hrecK
  obtain ⟨hcr, rfl⟩ := cEnv_ctor hctor hctorK
  obtain ⟨rfl, rfl⟩ := cEnv_family hfam hfamK
  have hnM : nMinors = 2 := by omega
  have p1 : piCount riCtor.mtype = 1 := rfl
  have p2 : piCount riFam.mtype = 1 := rfl
  have p3 : piCount cRec.mtype = 5 := rfl
  rw [p1] at hnpar
  rw [p2] at hnidx
  rw [p3] at hnmin
  subst hnM
  have hP : peelPis 5 cRec.mtype = some ([cMotTy, cMin1, cMin2, .sort .zero,
      .app (.const 0 []) (.bvar 0)], .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) := rfl
  have hnp : nparams = 0 := by
    refine Decidable.byContradiction (fun hne => ?_)
    have h1 : nparams = 1 := by omega
    have h2 : nindices = 0 := by omega
    subst h1 h2
    have hPR : peelPis (1 + 1 + 2 + 0 + 1) cRec.mtype = some ([cMotTy, cMin1, cMin2, .sort .zero,
        .app (.const 0 []) (.bvar 0)], .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) := hP
    rw [hPR] at hpeelRec
    obtain ⟨-, hb⟩ := Prod.mk.inj (Option.some.inj hpeelRec)
    rw [← hb] at hrecBody
    simp [foldApps] at hrecBody
  subst hnp
  have hnI : nindices = 1 := by omega
  subst hnI
  have hfl : fields.length = 1 := by omega
  obtain ⟨x, rfl⟩ := List.length_eq_one.mp hfl
  obtain ⟨M, m₁, m₂, X, rfl⟩ : ∃ M m₁ m₂ X, preMajor = [M, m₁, m₂, X] := by
    match preMajor, hpre with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have hcp : ctorParams = [] := List.length_eq_zero.mp hctorParams
  subst hcp
  have hq : peelPis (0 + [x].length) riCtor.mtype = some ([.sort .zero], .app (.const 0 []) (.bvar 0)) := rfl
  rw [hq] at hpeel
  obtain ⟨hcd, -⟩ := Prod.mk.inj (Option.some.inj hpeel)
  subst hcd
  have ha : analyzeFields 0 (List.drop 0 [Expr.sort .zero]) = some [RecKind.plain] := rfl
  rw [ha] at hkinds
  have hks : kinds = [.plain] := (Option.some.inj hkinds).symm
  subst hks
  have hca : ctorAfterParams = instantiateLevels ls riCtor.mtype := by
    have := hctorAfter
    simp [applyTel] at this
    exact this.symm
  subst hca
  have hls0 : ls.length = 0 := hlsLen
  rcases hcr with rfl | rfl
  · -- ctorRef = 2 = 0 + 1 + ctorIdx ⇒ ctorIdx = 1 ⇒ minor = m₂
    have hci : ctorIdx = 1 := by omega
    subst hci
    have hmin : minor = m₂ := by
      have := hminor
      simp at this
      exact this.symm
    subst hmin
    refine ⟨ls, lsC, M, m₁, minor, X, x, hls0, Or.inr ⟨?_, ?_⟩⟩
    · simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps]
    · simp [iotaRhsOf, rhsArgs, foldApps, riCtor, instantiateLevels]
  · have hci : ctorIdx = 0 := by omega
    subst hci
    have hmin : minor = m₁ := by
      have := hminor
      simp at this
      exact this.symm
    subst hmin
    refine ⟨ls, lsC, M, minor, m₂, X, x, hls0, Or.inl ⟨?_, ?_⟩⟩
    · simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps]
    · simp [iotaRhsOf, rhsArgs, foldApps, riCtor, instantiateLevels]

theorem cIota_inv' {lhs rhs : Expr Nat} (d : DerivedIota cEnv lhs rhs) :
    ∃ (ls lsC : List Level) (M m₁ m₂ X x : Expr Nat), ls.length = 0 ∧
      ((lhs = foldApps (.const 3 ls) [M, m₁, m₂, X, foldApps (.const 1 lsC) [x]] ∧ rhs = .app m₁ x) ∨
        (lhs = foldApps (.const 3 ls) [M, m₁, m₂, X, foldApps (.const 2 lsC) [x]] ∧ rhs = .app m₂ x)) := by
  cases d with
  | of w => exact cIota_inv w


/-! ## §3 `bkRec` is typed in `riEnv` at `bk cRecTy` -/

/-- `bk cRecTy`: `Π (M : cMotTy) (m₁ : cMin1) (m₂ : cMin2R) (X : Sort 0) (h : RI X), M X h`. -/
def bkRecTy : Expr Nat :=
  .pi cMotTy (.pi cMin1 (.pi cMin2R (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))))))

theorem bk_cRecTy : bk cRecTy = bkRecTy := rfl

section BkRecTyped

variable {n : Nat}

/-- `RI a : Sort 0` in `riEnv`. -/
def riTyR {Γ : LCtx} {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    HasTyT riEnv n Γ (.app (.const 0 []) a) (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 0 [] riFam rfl rfl rfl) ha

/-- `mk a : RI a` in `riEnv`. -/
def mkTyR {Γ : LCtx} {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) :
    HasTyT riEnv n Γ (.app (.const 1 []) a) (.app (.const 0 []) a) :=
  .app _ _ _ _ _ (.const _ 1 [] riCtor rfl rfl rfl) ha

def motTyR (Γ : LCtx) :
    HasTyT riEnv n Γ cMotTy (.sort (.imax (.succ .zero) (.imax .zero (.succ .zero)))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))
    (.imax .zero (.succ .zero)) (.sort Γ .zero)
    (.pi _ (.app (.const 0 []) (.bvar 0)) .zero (.sort .zero) (.succ .zero)
      (riTyR (.bvar _ 0 _ rfl)) (.sort _ .zero))

/-- under `[X, M]`: `M X (mk X) : Sort 0`. -/
def min1BodyR (Γ : LCtx) :
    HasTyT riEnv n (.assumption (.sort .zero) :: .assumption cMotTy :: Γ)
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0))) (.sort .zero) :=
  .app _ _ _ (.app (.const 0 []) (.bvar 0)) (.sort .zero)
    (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))
      (.bvar _ 1 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))) rfl)
      (.bvar _ 0 _ rfl))
    (mkTyR (.bvar _ 0 _ rfl))

def min1TyR (Γ : LCtx) :
    HasTyT riEnv n (.assumption cMotTy :: Γ) cMin1 (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ (.sort .zero) (.succ .zero) _ .zero (.sort _ .zero) (min1BodyR Γ)

/-- under `[X, m₁, M]`: `M X (mk X) : Sort 0`. -/
def min2BodyR (Γ : LCtx) :
    HasTyT riEnv n (.assumption (.sort .zero) :: .assumption cMin1 :: .assumption cMotTy :: Γ)
      (.app (.app (.bvar 2) (.bvar 0)) (.app (.const 1 []) (.bvar 0))) (.sort .zero) :=
  .app _ _ _ (.app (.const 0 []) (.bvar 0)) (.sort .zero)
    (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))
      (.bvar _ 2 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))) rfl)
      (.bvar _ 0 _ rfl))
    (mkTyR (.bvar _ 0 _ rfl))

def min2TyR (Γ : LCtx) :
    HasTyT riEnv n (.assumption cMin1 :: .assumption cMotTy :: Γ) cMin2R
      (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ (.sort .zero) (.succ .zero) _ .zero (.sort _ .zero) (min2BodyR Γ)

/-- the five binders. -/
def bkΓ5 (Γ : LCtx) : LCtx :=
  .assumption (.app (.const 0 []) (.bvar 0)) :: .assumption (.sort .zero) :: .assumption cMin2R ::
    .assumption cMin1 :: .assumption cMotTy :: Γ

/-- `rec.{0} M m₁ X h : M X h` under `[h, X, m₂, m₁, M]`. -/
def bkBodyR (Γ : LCtx) :
    HasTyT riEnv n (bkΓ5 Γ) (foldApps (.const 2 [.zero]) [.bvar 4, .bvar 3, .bvar 1, .bvar 0])
      (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) :=
  let h0 : HasTyT riEnv n (bkΓ5 Γ) (.const 2 [.zero]) (instantiateLevels [.zero] riRecTy) :=
    .const _ 2 [.zero] riRec rfl rfl rfl
  let h1 := HasTyT.app (bkΓ5 Γ) _ (.bvar 4) _ _ h0 (.bvar _ 4 cMotTy rfl)
  let h2 := HasTyT.app (bkΓ5 Γ) _ (.bvar 3) _ _ h1 (.bvar _ 3 _ rfl)
  let h3 := HasTyT.app (bkΓ5 Γ) _ (.bvar 1) _ _ h2 (.bvar _ 1 (.sort .zero) rfl)
  HasTyT.app (bkΓ5 Γ) _ (.bvar 0) _ _ h3 (.bvar _ 0 (.app (.const 0 []) (.bvar 1)) rfl)

/-- **`bkRec` is typed in `riEnv` at `bk cRecTy`, in every context.** -/
def bkRecTyped (Γ : LCtx) : HasTyT riEnv n Γ bkRec bkRecTy :=
  .lam _ _ _ _ _ (motTyR Γ)
    (.lam _ _ _ _ _ (min1TyR Γ)
      (.lam _ _ _ _ _ (min2TyR Γ)
        (.lam _ _ (.succ .zero) _ _ (.sort _ .zero)
          (.lam _ _ .zero _ _ (riTyR (.bvar _ 0 _ rfl)) (bkBodyR Γ)))))

end BkRecTyped

/-! ## §4 reading `riEnv` under its Π row: type uniqueness, β, the five β steps -/

section RowsR

variable {n : Nat}

theorem riDT012 (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {e A B : Expr Nat}
    (hA : HasTyT riEnv n Γ e A) (hB : HasTyT riEnv n Γ e B) : Nonempty (TyConvT riEnv n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow riEnvWfT riSortRow_chain hpi hΓ hA hB

theorem riSortUniq (hpi : PiRowField riEnv n) {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (hΓ : CtxWfT riEnv n Γ) (hu : HasTyT riEnv n Γ T (.sort u)) (hv : HasTyT riEnv n Γ T (.sort v)) :
    eqN u v := by
  obtain ⟨c⟩ := riDT012 hpi hΓ hu hv
  exact riSortRow_chain hΓ c

/-- a type-conversion chain from a term typed at a sort is one conversion at that sort. -/
theorem convSortR (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {a b : Expr Nat}
    {u : Level} (hA : HasTyT riEnv n Γ a (.sort u)) (hc : TyConvT riEnv n Γ a b) :
    Nonempty (ConvT riEnv n Γ a b (.sort u)) :=
  F8EtaK.convT_of_tyConvT_sort_of_sortUniq riEnvWfT
    (fun {_} {_} {_} {_} hΓ' hu hv => riSortUniq hpi hΓ' hu hv) hΓ hA hc

theorem betaConvR (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    {A0 body arg S : Expr Nat} (h : HasTyT riEnv n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (ConvT riEnv n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) S) := by
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u0, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hpi hΓ hcv_lam
  obtain ⟨w, ⟨hBw⟩⟩ := DT007T_typing_regularity_of_envWfT riEnvWfT
    (.assumption Γ A0 u0 hΓ hA0ty) hbody
  obtain ⟨cdom⟩ := convSortR hpi hΓ hA0ty hBdom
  obtain ⟨ccod⟩ := convSortR hpi (.assumption Γ A0 u0 hΓ hA0ty) hBw hBcod
  have ha' : HasTyT riEnv n Γ arg A0 :=
    HasTyT.conv _ _ _ _ u0 ha (ConvT.symm _ _ _ _ cdom)
  have hcod' : ConvT riEnv n Γ (instantiate0 arg B_lam) (instantiate0 arg B1) (.sort w) :=
    convT_subst0_of_envWfT riEnvWfT ccod ha'
  exact ⟨retype (ConvT.beta Γ A0 body arg B_lam u0 hA0ty hbody ha')
    (.trans _ _ _ _ (.of _ _ _ _ hcod') hcv)⟩

/-- `e ≡ e'` at every type of `e`, in `riEnv`. -/
def CER (n : Nat) (Γ : LCtx) (e e' : Expr Nat) : Prop :=
  ∀ S, HasTyT riEnv n Γ e S → Nonempty (ConvT riEnv n Γ e e' S)

theorem ceBetaR (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {A0 body arg : Expr Nat} :
    CER n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) :=
  fun _ h => betaConvR hpi hΓ h

theorem ceTransR {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {e e' e'' : Expr Nat}
    (h1 : CER n Γ e e') (h2 : CER n Γ e' e'') : CER n Γ e e'' := by
  intro S h
  obtain ⟨c1⟩ := h1 S h
  obtain ⟨c2⟩ := h2 S (NativeValleys.convEnds riEnvWfT hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 c2⟩

theorem ceAppLR {Γ : LCtx} {f f' : Expr Nat} (a : Expr Nat)
    (h1 : CER n Γ f f') : CER n Γ (.app f a) (.app f' a) := by
  intro S h
  obtain ⟨A, B, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := h1 _ hf
  exact ⟨retype (ConvT.app Γ f f' a a A B c (ConvT.refl Γ a A ha)) hcv⟩

theorem ceOfEqR {Γ : LCtx} {e e' : Expr Nat} (h : e = e') : CER n Γ e e' :=
  fun _ hS => ⟨h ▸ ConvT.refl _ _ _ hS⟩

/-- the five β steps of `bkRec`: `bkRec M m₁ m₂ X h ≡ rec.{0} M m₁ X h`. -/
theorem red5R (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) (M m₁ m₂ X H : Expr Nat) :
    CER n Γ (.app (.app (.app (.app (.app bkRec M) m₁) m₂) X) H)
      (foldApps (.const 2 [.zero]) [M, m₁, X, H]) := by
  refine ceTransR hΓ (ceAppLR _ (ceAppLR _ (ceAppLR _ (ceAppLR _ (ceBetaR hpi hΓ))))) ?_
  refine ceTransR hΓ (ceAppLR _ (ceAppLR _ (ceAppLR _ (ceBetaR hpi hΓ)))) ?_
  refine ceTransR hΓ (ceAppLR _ (ceAppLR _ (ceBetaR hpi hΓ))) ?_
  refine ceTransR hΓ (ceAppLR _ (ceBetaR hpi hΓ)) ?_
  refine ceTransR hΓ (ceBetaR hpi hΓ) ?_
  apply ceOfEqR
  have l2 : ∀ e : Expr Nat, lift 0 1 (lift 0 1 e) = lift 0 2 e :=
    fun e => lift_lift_merge 1 1 0 0 (Nat.le_refl _) (by omega) e
  have l3 : ∀ e : Expr Nat, lift 0 1 (lift 0 2 e) = lift 0 3 e :=
    fun e => lift_lift_merge 1 2 0 0 (Nat.le_refl _) (by omega) e
  have l4 : ∀ e : Expr Nat, lift 0 1 (lift 0 3 e) = lift 0 4 e :=
    fun e => lift_lift_merge 1 3 0 0 (Nat.le_refl _) (by omega) e
  have c43 : ∀ r e : Expr Nat, instantiate 3 r (lift 0 4 e) = lift 0 3 e :=
    fun r e => instantiate_lift_cancel 4 0 3 r (Nat.zero_le _) (by omega) e
  have c32 : ∀ r e : Expr Nat, instantiate 2 r (lift 0 3 e) = lift 0 2 e :=
    fun r e => instantiate_lift_cancel 3 0 2 r (Nat.zero_le _) (by omega) e
  have c21 : ∀ r e : Expr Nat, instantiate 1 r (lift 0 2 e) = lift 0 1 e :=
    fun r e => instantiate_lift_cancel 2 0 1 r (Nat.zero_le _) (by omega) e
  have c10 : ∀ r e : Expr Nat, instantiate 0 r (lift 0 1 e) = lift 0 0 e :=
    fun r e => instantiate_lift_cancel 1 0 0 r (Nat.zero_le _) (by omega) e
  simp only [instantiate0, instantiate, lift, foldApps, lift_zero_idx, l2, l3, l4, c43, c32, c21, c10,
    Nat.zero_add, ite_true]

end RowsR


/-! ## §5 the ι witness of `riEnv` at arbitrary arguments, at level `0` -/

/-- `rec.{l} M m X (mk x) ⇝ m x`: `riW` with the level and the four arguments free. -/
def riWAtL (l : Level) (lsC : List Level) (M m X x : Expr Nat) : IotaWitness riEnv where
  recRef := 2
  ctorRef := 1
  ls := [l]
  lsC := lsC
  recMember := riRec
  ctorMember := riCtor
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [M, m, X]
  fields := [x]
  ctorParams := []
  kinds := [.plain]
  minor := m
  hlen := rfl
  familyRef := 0
  famMember := riFam
  hfam := rfl
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
  ctorDoms := [.sort .zero]
  ctorResult := .app (.const 0 []) (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [riMotTy, riMinTy, .sort .zero, .app (.const 0 []) (.bvar 0)]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := riCtor.mtype
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem riWAtL_lhs (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    iotaLhsOf (riWAtL l lsC M m X x) = foldApps (.const 2 [l]) [M, m, X, .app (.const 1 lsC) x] := by
  simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps, riWAtL]

theorem riWAtL_rhs (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    iotaRhsOf (riWAtL l lsC M m X x) = .app m x := by
  simp [iotaRhsOf, rhsArgs, foldApps, riWAtL, riCtor, instantiateLevels]

def riDerivedIotaL (l : Level) (lsC : List Level) (M m X x : Expr Nat) :
    DerivedIota riEnv (foldApps (.const 2 [l]) [M, m, X, .app (.const 1 lsC) x]) (.app m x) :=
  (riWAtL_lhs l lsC M m X x) ▸ (riWAtL_rhs l lsC M m X x) ▸ DerivedIota.of (riWAtL l lsC M m X x)

def riDerivedIota (lsC : List Level) (M m X x : Expr Nat) :
    DerivedIota riEnv (foldApps (.const 2 [.zero]) [M, m, X, .app (.const 1 lsC) x]) (.app m x) :=
  riDerivedIotaL .zero lsC M m X x

/-! ## §6 the back-translated ι cells -/

section IotaR

variable {n : Nat}

/-- an application whose head has a known Π type reads the argument's type off the head, in
    `riEnv` under its Π row. -/
theorem appInvKnownR (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    {f a D C T' : Expr Nat} (hf : HasTyT riEnv n Γ f (.pi D C)) (h : HasTyT riEnv n Γ (.app f a) T') :
    Nonempty (HasTyT riEnv n Γ a D) := by
  obtain ⟨A, B, hf', ha', _⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := riDT012 hpi hΓ hf' hf
  obtain ⟨⟨cA⟩, _⟩ := hpi hΓ c
  exact ⟨hasTyT_of_tyConvT ha' cA⟩

/-- the redex `bkRec M m₁ m₂ X (mk x)`. -/
abbrev bkRedex (M m₁ m₂ X : Expr Nat) (lsC : List Level) (x : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (.app bkRec M) m₁) m₂) X) (.app (.const 1 lsC) x)

/-- **the first ι cell, back-translated**: `bkRec M m₁ m₂ X (mk x) ≡ m₁ x` at a common type. -/
theorem iotaConvR1 (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    (M m₁ m₂ X : Expr Nat) (lsC : List Level) (x T : Expr Nat)
    (hl : HasTyT riEnv n Γ (bkRedex M m₁ m₂ X lsC x) T) (hr : HasTyT riEnv n Γ (.app m₁ x) T) :
    Nonempty (ConvT riEnv n Γ (bkRedex M m₁ m₂ X lsC x) (.app m₁ x) T) := by
  obtain ⟨c1⟩ := red5R hpi hΓ M m₁ m₂ X (.app (.const 1 lsC) x) T hl
  have hred := (NativeValleys.convEnds riEnvWfT hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 (.iota _ _ _ _ (riDerivedIota lsC M m₁ X x) hred hr)⟩

/-- the second minor's typing, read off the redex: `m₂ : Π X, M X (mk X)` (as `instantiate`s). -/
theorem bkRedex_minors (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    (M m₁ m₂ X : Expr Nat) (lsC : List Level) (x T : Expr Nat)
    (hl : HasTyT riEnv n Γ (bkRedex M m₁ m₂ X lsC x) T) :
    Nonempty (HasTyT riEnv n Γ M cMotTy) ∧
      Nonempty (HasTyT riEnv n Γ m₁
        (.pi (.sort .zero) (.app (.app (lift 0 1 M) (.bvar 0)) (.app (.const 1 []) (.bvar 0))))) ∧
      Nonempty (HasTyT riEnv n Γ m₂
        (.pi (.sort .zero) (.app (.app (lift 0 1 M) (.bvar 0)) (.app (.const 1 []) (.bvar 0))))) ∧
      Nonempty (HasTyT riEnv n Γ x (.sort .zero)) := by
  obtain ⟨_, _, he4, hH, _⟩ := hasTyTInv_app hl rfl
  obtain ⟨_, _, he3, hX, _⟩ := hasTyTInv_app he4 rfl
  obtain ⟨_, _, he2, hm2, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm1, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM⟩ := appInvKnownR hpi hΓ (bkRecTyped Γ) he1
  have own1 := HasTyT.app Γ bkRec M _ _ (bkRecTyped Γ) hM
  obtain ⟨hm1'⟩ := appInvKnownR hpi hΓ own1 he2
  have own2 := HasTyT.app Γ _ m₁ _ _ own1 hm1'
  obtain ⟨hm2'⟩ := appInvKnownR hpi hΓ own2 he3
  have own3 := HasTyT.app Γ _ m₂ _ _ own2 hm2'
  obtain ⟨hX'⟩ := appInvKnownR hpi hΓ own3 he4
  have own4 := HasTyT.app Γ _ X _ _ own3 hX'
  obtain ⟨hH'⟩ := appInvKnownR hpi hΓ own4 hl
  have hH'' : HasTyT riEnv n Γ (.app (.const 1 lsC) x) (.app (.const 0 []) X) := hH'
  obtain ⟨⟨-, -, hargs, -⟩⟩ := hasTyT_spineInv_rows riEnvWfT hpi hΓ
    (r := 1) (ls := lsC) (m := riCtor) rfl (doms := [.sort .zero]) (U := .app (.const 0 []) (.bvar 0)) rfl
    [x] rfl hH''
  have hx : HasTyT riEnv n Γ x (.sort .zero) := hargs 0 x (.sort .zero) rfl rfl
  have e2 : instantiate 1 (lift 0 1 m₁) (lift 0 1 (lift 0 1 M)) = lift 0 1 M := by
    rw [lift_lift_merge 1 1 0 0 (Nat.le_refl _) (by omega)]
    rw [instantiate_lift_cancel 2 0 1 _ (by omega) (by omega)]
  have et : instantiate 0 m₁ (instantiate (0 + 1) (lift 0 1 M) cMin2R) =
      .pi (.sort .zero) (.app (.app (instantiate 1 (lift 0 1 m₁) (lift 0 1 (lift 0 1 M))) (.bvar 0))
        (.app (.const 1 []) (.bvar 0))) := rfl
  have hm2'' : HasTyT riEnv n Γ m₂
      (.pi (.sort .zero) (.app (.app (lift 0 1 M) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))) := by
    have h := hm2'
    rw [et, e2] at h
    exact h
  exact ⟨⟨hM⟩, ⟨hm1'⟩, ⟨hm2''⟩, ⟨hx⟩⟩

/-- **the second ι cell, back-translated**: `bkRec M m₁ m₂ X (mk x) ≡ m₂ x` at a common type. The
    common type is read by type uniqueness (both `m₂ x` and the redex's reduct are typed at
    `M x (mk x)`), and the two minors are identified by `irr` at the `Prop` motive. -/
theorem iotaConvR2 (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    (M m₁ m₂ X : Expr Nat) (lsC : List Level) (x T : Expr Nat)
    (hl : HasTyT riEnv n Γ (bkRedex M m₁ m₂ X lsC x) T) (hr : HasTyT riEnv n Γ (.app m₂ x) T) :
    Nonempty (ConvT riEnv n Γ (bkRedex M m₁ m₂ X lsC x) (.app m₂ x) T) := by
  obtain ⟨⟨hM⟩, ⟨hm1⟩, ⟨hm2⟩, ⟨hx⟩⟩ := bkRedex_minors hpi hΓ M m₁ m₂ X lsC x T hl
  have e1 : instantiate0 x (.app (.app (lift 0 1 M) (.bvar 0)) (.app (.const 1 []) (.bvar 0))) =
      .app (.app M x) (.app (.const 1 []) x) := by
    simp only [instantiate0, instantiate]
    rw [instantiate_lift_cancel 1 0 0 _ (by omega) (by omega), lift_zero_idx]
    simp
  have hm1x : HasTyT riEnv n Γ (.app m₁ x) (.app (.app M x) (.app (.const 1 []) x)) := by
    have h := HasTyT.app Γ m₁ x _ _ hm1 hx
    rw [e1] at h
    exact h
  have hm2x : HasTyT riEnv n Γ (.app m₂ x) (.app (.app M x) (.app (.const 1 []) x)) := by
    have h := HasTyT.app Γ m₂ x _ _ hm2 hx
    rw [e1] at h
    exact h
  -- T ≡ M x (mk x), from the two typings of m₂ x
  obtain ⟨cT⟩ := riDT012 hpi hΓ hr hm2x
  have hm1T : HasTyT riEnv n Γ (.app m₁ x) T := hasTyT_of_tyConvT hm1x (TyConvT.symmT cT)
  obtain ⟨c1⟩ := iotaConvR1 hpi hΓ M m₁ m₂ X lsC x T hl hm1T
  -- m₁ x ≡ m₂ x at T: irr, since M x (mk x) : Sort 0, hence T : Sort 0
  -- M : Π X, RI X → Sort 0, so M x (mk x) : Sort 0
  have hMx : HasTyT riEnv n Γ (.app (.app M x) (.app (.const 1 []) x)) (.sort .zero) :=
    HasTyT.app Γ (.app M x) (.app (.const 1 []) x) _ _ (HasTyT.app Γ M x _ _ hM hx) (mkTyR hx)
  obtain ⟨cTs⟩ := convSortR hpi hΓ hMx (TyConvT.symmT cT)
  have hT0 : HasTyT riEnv n Γ T (.sort .zero) := (NativeValleys.convEnds riEnvWfT hΓ cTs).2.1
  have cirr : ConvT riEnv n Γ (.app m₁ x) (.app m₂ x) T := .irr _ _ _ _ hT0 hm1T hr
  exact ⟨.trans _ _ _ _ _ c1 cirr⟩

end IotaR

/-! ## §7 the translation of derivations, `cEnv → riEnv`, under `riEnv`'s Π row -/

section Translate

variable {n : Nat}

mutual
theorem bkTy (hpi : PiRowField riEnv n) : {Γ : LCtx} → {e A : Expr Nat} → HasTyT cEnv n Γ e A →
    CtxWfT riEnv n (bkCtx Γ) → Nonempty (HasTyT riEnv n (bkCtx Γ) (bk e) (bk A))
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ =>
      ⟨.bvar _ i (bk A) (by rw [lookupType_bkCtx, h]; rfl)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      rcases cEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hl : ls = [] := List.length_eq_zero.mp hlen
        subst hl
        exact ⟨bkRecTyped (bkCtx Γ)⟩
      · exact ⟨.const _ 1 ls riCtor rfl hlen hwf⟩
      · exact ⟨.const _ 1 ls riCtor rfl hlen hwf⟩
      · exact ⟨.const _ 0 ls riFam rfl hlen hwf⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hB'⟩ := bkTy hpi hB (.assumption _ (bk A) u hΓ' hA')
      exact ⟨.pi _ (bk A) u (bk B) v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ' => by
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hb'⟩ := bkTy hpi hbody (.assumption _ (bk A) u hΓ' hA')
      exact ⟨.lam _ (bk A) u (bk body) (bk B) hA' hb'⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ' => by
      obtain ⟨hf'⟩ := bkTy hpi hf hΓ'
      obtain ⟨ha'⟩ := bkTy hpi ha hΓ'
      rw [bk_instantiate0]
      exact ⟨.app _ (bk f) (bk a) (bk A) (bk B) hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hv'⟩ := bkTy hpi hv hΓ'
      obtain ⟨hb'⟩ := bkTy hpi hb (.letBinding _ (bk A) u (bk value) hΓ' hA' hv')
      rw [bk_instantiate0]
      exact ⟨.letE _ (bk A) u (bk value) (bk B) (bk body) hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ' => by
      obtain ⟨h⟩ := bkTy hpi hexp hΓ'
      rw [bk_natExpand] at h
      exact ⟨h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ' => by
      obtain ⟨h'⟩ := bkTy hpi h hΓ'
      obtain ⟨hc'⟩ := bkConv hpi hc hΓ'
      exact ⟨.conv _ (bk e) (bk A) (bk B) u h' hc'⟩

theorem bkConv (hpi : PiRowField riEnv n) : {Γ : LCtx} → {a b A : Expr Nat} → ConvT cEnv n Γ a b A →
    CtxWfT riEnv n (bkCtx Γ) → Nonempty (ConvT riEnv n (bkCtx Γ) (bk a) (bk b) (bk A))
  | _, _, _, _, .refl Γ a A h, hΓ' => by
      obtain ⟨h'⟩ := bkTy hpi h hΓ'
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ' => by
      obtain ⟨h'⟩ := bkConv hpi h hΓ'
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := bkConv hpi h1 hΓ'
      obtain ⟨h2'⟩ := bkConv hpi h2 hΓ'
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ' => by
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hb'⟩ := bkTy hpi hbody (.assumption _ (bk A) u hΓ' hA')
      obtain ⟨ha'⟩ := bkTy hpi harg hΓ'
      rw [bk_instantiate0, bk_instantiate0]
      exact ⟨.beta _ (bk A) (bk body) (bk arg) (bk B) u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hv'⟩ := bkTy hpi hv hΓ'
      obtain ⟨hb'⟩ := bkTy hpi hb (.letBinding _ (bk A) u (bk value) hΓ' hA' hv')
      rw [bk_instantiate0, bk_instantiate0]
      exact ⟨.zeta _ (bk A) (bk value) (bk body) (bk B) u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ' => by
      obtain ⟨hv'⟩ := bkTy hpi hv hΓ'
      exact ⟨.zetaLocal _ i (bk A) (bk v) (by rw [lookupValue_bkCtx, hval]; rfl)
        (by rw [lookupType_bkCtx, hty]; rfl) hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody _ _ _ _, _ =>
      absurd hbody (by rw [cEnv_noBody hres]; exact Option.noConfusion)
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, hΓ' => by
      obtain ⟨hl'⟩ := bkTy hpi hl hΓ'
      obtain ⟨hr'⟩ := bkTy hpi hr hΓ'
      obtain ⟨ls, lsC, M, m₁, m₂, X, x, hlen, hcase⟩ := cIota_inv' h
      have hl0 : ls = [] := List.length_eq_zero.mp hlen
      subst hl0
      rcases hcase with ⟨hL, hR⟩ | ⟨hL, hR⟩
      · rw [hL] at hl'
        rw [hL, hR]
        rw [hR] at hr'
        have e1 : bk (foldApps (.const 3 []) [M, m₁, m₂, X, foldApps (.const 1 lsC) [x]]) =
            bkRedex (bk M) (bk m₁) (bk m₂) (bk X) lsC (bk x) := rfl
        rw [e1] at hl' ⊢
        exact iotaConvR1 hpi hΓ' (bk M) (bk m₁) (bk m₂) (bk X) lsC (bk x) (bk T) hl' hr'
      · rw [hL] at hl'
        rw [hL, hR]
        rw [hR] at hr'
        have e1 : bk (foldApps (.const 3 []) [M, m₁, m₂, X, foldApps (.const 2 lsC) [x]]) =
            bkRedex (bk M) (bk m₁) (bk m₂) (bk X) lsC (bk x) := rfl
        rw [e1] at hl' ⊢
        exact iotaConvR2 hpi hΓ' (bk M) (bk m₁) (bk m₂) (bk X) lsC (bk x) (bk T) hl' hr'
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ' => by
      obtain ⟨h'⟩ := bkTy hpi hexp hΓ'
      rw [litExp_eq h, bk_natExpand] at *
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .app Γ f g a b A B h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := bkConv hpi h1 hΓ'
      obtain ⟨h2'⟩ := bkConv hpi h2 hΓ'
      rw [bk_instantiate0]
      exact ⟨.app _ (bk f) (bk g) (bk a) (bk b) (bk A) (bk B) h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ' => by
      obtain ⟨hA'⟩ := bkConv hpi hA hΓ'
      obtain ⟨hb'⟩ := bkConv hpi hb (.assumption _ (bk A) u hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1)
      exact ⟨.lam _ (bk A) (bk A') (bk b) (bk b') (bk B) u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := bkConv hpi hA hΓ'
      obtain ⟨hB'⟩ := bkConv hpi hB (.assumption _ (bk A) u hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1)
      exact ⟨.pi _ (bk A) (bk A') (bk B) (bk B') u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkConv hpi hA hΓ'
      obtain ⟨hv'⟩ := bkConv hpi hv hΓ'
      obtain ⟨hb'⟩ := bkConv hpi hb (.letBinding _ (bk A) u (bk v) hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1 (NativeValleys.convEnds riEnvWfT hΓ' hv').1)
      rw [bk_instantiate0]
      exact ⟨.letE _ (bk A) (bk A') (bk v) (bk v') (bk b) (bk b') (bk B) u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ => by
      rcases cEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hl : ls = [] := List.length_eq_zero.mp hlen
        have hl' : ls' = [] := List.length_eq_zero.mp
          ((eqNList_length _ _ h).symm.trans hlen)
        subst hl hl'
        exact ⟨.refl _ _ _ (bkRecTyped (bkCtx Γ))⟩
      · exact ⟨.consts _ 1 ls ls' riCtor rfl hlen hwf hwf' h⟩
      · exact ⟨.consts _ 1 ls ls' riCtor rfl hlen hwf hwf' h⟩
      · exact ⟨.consts _ 0 ls ls' riFam rfl hlen hwf hwf' h⟩
  | _, _, _, _, .eta Γ f A B h, hΓ' => by
      obtain ⟨h'⟩ := bkTy hpi h hΓ'
      show Nonempty (ConvT riEnv n (bkCtx Γ) (.lam (bk A) (.app (bk (lift 0 1 f)) (.bvar 0))) (bk f)
        (.pi (bk A) (bk B)))
      rw [bk_lift]
      exact ⟨.eta _ (bk f) (bk A) (bk B) h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ' => by
      obtain ⟨hP'⟩ := bkTy hpi hP hΓ'
      obtain ⟨hp'⟩ := bkTy hpi hp hΓ'
      obtain ⟨hq'⟩ := bkTy hpi hq hΓ'
      exact ⟨.irr _ (bk P) (bk p) (bk q) hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ' => by
      obtain ⟨h'⟩ := bkConv hpi h hΓ'
      obtain ⟨hA'⟩ := bkConv hpi hA hΓ'
      exact ⟨.tyConv _ (bk a) (bk b) (bk A) (bk A') u h' hA'⟩
end

theorem bkTyConv (hpi : PiRowField riEnv n) {Γ : LCtx} {a b : Expr Nat} (h : TyConvT cEnv n Γ a b)
    (hΓ' : CtxWfT riEnv n (bkCtx Γ)) : Nonempty (TyConvT riEnv n (bkCtx Γ) (bk a) (bk b)) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := bkConv hpi h hΓ'; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem bkCtxWf (hpi : PiRowField riEnv n) {Γ : LCtx} (h : CtxWfT cEnv n Γ) :
    Nonempty (CtxWfT riEnv n (bkCtx Γ)) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      exact ⟨.assumption _ (bk A) u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := bkTy hpi hA hΓ'
      obtain ⟨hv'⟩ := bkTy hpi hv hΓ'
      exact ⟨.letBinding _ (bk A) u (bk v) hΓ' hA' hv'⟩

end Translate


/-! ## §8 `recL l ≡ rec.{l}`: the λ-recursor is the recursor, by η and the K-like cell -/

/-- `bk (recT l)`: `λ (M : recMot l) (m : riMinTy) (X : Sort 0) (h : RI X). m X`. -/
def recL (l : Level) : Expr Nat :=
  .lam (recMot l) (.lam riMinTy (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
    (.app (.bvar 2) (.bvar 1)))))

theorem bk_recT (l : Level) : bk (recT l) = recL l := rfl

/-- the fully η-expanded recursor, `λ M m X h. rec.{l} M m X h`. -/
def recE (l : Level) : Expr Nat :=
  .lam (recMot l) (.lam riMinTy (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
    (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))))

/-- `[h : RI X, X : Sort 0, m : riMinTy, M : recMot l] ++ Γ`. -/
def kΓ (Γ : LCtx) (l : Level) : LCtx :=
  .assumption (.app (.const 0 []) (.bvar 0)) :: .assumption (.sort .zero) :: .assumption riMinTy ::
    .assumption (recMot l) :: Γ

section EtaK

variable {n : Nat}

def motTyL (Γ : LCtx) (l : Level) :
    HasTyT riEnv n Γ (recMot l) (.sort (.imax (.succ .zero) (.imax .zero (.succ l)))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
    (.imax .zero (.succ l)) (.sort Γ .zero)
    (.pi _ (.app (.const 0 []) (.bvar 0)) .zero (.sort l) (.succ l)
      (riTyR (.bvar _ 0 _ rfl)) (.sort _ l))

/-- under `[X, M]`: `M X (mk X) : Sort l`. -/
def minBodyL (Γ : LCtx) (l : Level) :
    HasTyT riEnv n (.assumption (.sort .zero) :: .assumption (recMot l) :: Γ)
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0))) (.sort l) :=
  .app _ _ _ (.app (.const 0 []) (.bvar 0)) (.sort l)
    (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
      (.bvar _ 1 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))) rfl)
      (.bvar _ 0 _ rfl))
    (mkTyR (.bvar _ 0 _ rfl))

def minTyL (Γ : LCtx) (l : Level) :
    HasTyT riEnv n (.assumption (recMot l) :: Γ) riMinTy (.sort (.imax (.succ .zero) l)) :=
  .pi _ (.sort .zero) (.succ .zero) _ l (.sort _ .zero) (minBodyL Γ l)

/-- `rec.{l}` at its instantiated stored type. -/
def recConstL (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT riEnv n Γ (.const 2 [l]) (instantiateLevels [l] riRecTy) :=
  .const _ 2 [l] riRec rfl rfl hl

/-- `rec.{l} M m X : Π (h : RI X), M X h` under `[h, X, m, M]`. -/
def rec3L (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT riEnv n (kΓ Γ l) (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1])
      (.pi (.app (.const 0 []) (.bvar 1)) (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))) :=
  let h1 := HasTyT.app (kΓ Γ l) _ (.bvar 3) _ _ (recConstL (kΓ Γ l) l hl) (.bvar _ 3 (recMot l) rfl)
  let h2 := HasTyT.app (kΓ Γ l) _ (.bvar 2) _ _ h1 (.bvar _ 2 _ rfl)
  HasTyT.app (kΓ Γ l) _ (.bvar 1) _ _ h2 (.bvar _ 1 (.sort .zero) rfl)

/-- **the K-like cell at level `l`, under any context**: `rec.{l} M m X h ≡ m X : M X h`, by `irr`
    against `mk X` at the same type, `app`, ι at the constructor, and `tyConv` (cc-classc's
    `riConvK`, with the level and the outer context free). -/
def kcellL (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT riEnv n (kΓ Γ l) (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
  let hX : HasTyT riEnv n (kΓ Γ l) (.bvar 1) (.sort .zero) := .bvar _ 1 _ rfl
  let hRI : HasTyT riEnv n (kΓ Γ l) (.app (.const 0 []) (.bvar 1)) (.sort .zero) := riTyR hX
  let hh : HasTyT riEnv n (kΓ Γ l) (.bvar 0) (.app (.const 0 []) (.bvar 1)) := .bvar _ 0 _ rfl
  let hmk : HasTyT riEnv n (kΓ Γ l) (.app (.const 1 []) (.bvar 1)) (.app (.const 0 []) (.bvar 1)) :=
    mkTyR hX
  let cIrr : ConvT riEnv n (kΓ Γ l) (.bvar 0) (.app (.const 1 []) (.bvar 1)) (.app (.const 0 []) (.bvar 1)) :=
    .irr _ _ _ _ hRI hh hmk
  let h3 := rec3L Γ l hl
  let hMid : HasTyT riEnv n (kΓ Γ l) (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const 1 []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const 1 []) (.bvar 1))) :=
    HasTyT.app (kΓ Γ l) _ (.app (.const 1 []) (.bvar 1)) _ _ h3 hmk
  let hRhs : HasTyT riEnv n (kΓ Γ l) (.app (.bvar 2) (.bvar 1))
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const 1 []) (.bvar 1))) :=
    HasTyT.app (kΓ Γ l) (.bvar 2) (.bvar 1) _ _
      (.bvar _ 2 (.pi (.sort .zero) (.app (.app (.bvar 4) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))) rfl) hX
  let hMX : HasTyT riEnv n (kΓ Γ l) (.app (.bvar 3) (.bvar 1)) (.pi (.app (.const 0 []) (.bvar 1)) (.sort l)) :=
    HasTyT.app (kΓ Γ l) (.bvar 3) (.bvar 1) _ _ (.bvar _ 3 (recMot l) rfl) hX
  let step1 : ConvT riEnv n (kΓ Γ l) (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const 1 []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
    .app _ _ _ (.bvar 0) (.app (.const 1 []) (.bvar 1)) _ _ (.refl _ _ _ h3) cIrr
  let cIota : ConvT riEnv n (kΓ Γ l)
      (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const 1 []) (.bvar 1)])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const 1 []) (.bvar 1))) :=
    .iota _ _ _ _ (riDerivedIotaL l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)) hMid hRhs
  let tyFix : ConvT riEnv n (kΓ Γ l) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const 1 []) (.bvar 1)))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort l) :=
    .app _ _ _ (.app (.const 1 []) (.bvar 1)) (.bvar 0) _ _ (.refl _ _ _ hMX) (.symm _ _ _ _ cIrr)
  .trans _ _ _ _ _ step1 (.tyConv _ _ _ _ _ l cIota tyFix)

/-- `recE l ≡ recL l`: the K-like cell under the four binders. -/
def recE_conv_recL (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT riEnv n Γ (recE l) (recL l) (instantiateLevels [l] riRecTy) :=
  .lam Γ (recMot l) (recMot l) _ _ _ _ (.refl _ _ _ (motTyL Γ l))
    (.lam _ riMinTy riMinTy _ _ _ _ (.refl _ _ _ (minTyL Γ l))
      (.lam _ (.sort .zero) (.sort .zero) _ _ _ (.succ .zero) (.refl _ _ _ (.sort _ .zero))
        (.lam _ (.app (.const 0 []) (.bvar 0)) (.app (.const 0 []) (.bvar 0)) _ _
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) .zero
          (.refl _ _ _ (riTyR (.bvar _ 0 _ rfl))) (kcellL Γ l hl))))

/-- `rec.{l} ≡ recE l`: four η-expansions, each under the binders already opened. -/
def rec_conv_recE (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT riEnv n Γ (.const 2 [l]) (recE l) (instantiateLevels [l] riRecTy) :=
  let Γ1 : LCtx := .assumption (recMot l) :: Γ
  let Γ2 : LCtx := .assumption riMinTy :: Γ1
  let Γ3 : LCtx := .assumption (.sort .zero) :: Γ2
  let h0 := recConstL Γ l hl
  let h1 : HasTyT riEnv n Γ1 (.app (.const 2 [l]) (.bvar 0)) _ :=
    HasTyT.app Γ1 _ (.bvar 0) _ _ (recConstL Γ1 l hl) (.bvar _ 0 (recMot l) rfl)
  let h2 : HasTyT riEnv n Γ2 (.app (.app (.const 2 [l]) (.bvar 1)) (.bvar 0)) _ :=
    HasTyT.app Γ2 _ (.bvar 0) _ _
      (HasTyT.app Γ2 _ (.bvar 1) _ _ (recConstL Γ2 l hl) (.bvar _ 1 (recMot l) rfl)) (.bvar _ 0 _ rfl)
  let h3 : HasTyT riEnv n Γ3 (.app (.app (.app (.const 2 [l]) (.bvar 2)) (.bvar 1)) (.bvar 0)) _ :=
    HasTyT.app Γ3 _ (.bvar 0) _ _
      (HasTyT.app Γ3 _ (.bvar 1) _ _
        (HasTyT.app Γ3 _ (.bvar 2) _ _ (recConstL Γ3 l hl) (.bvar _ 2 (recMot l) rfl)) (.bvar _ 1 _ rfl))
      (.bvar _ 0 (.sort .zero) rfl)
  -- η₄ under [X, m, M]: rec M m X ≡ λ h. rec M m X h
  let e4 : ConvT riEnv n Γ3 (.app (.app (.app (.const 2 [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.lam (.app (.const 0 []) (.bvar 0)) (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])) _ :=
    .symm _ _ _ _ (.eta Γ3 _ _ _ h3)
  -- η₃ under [m, M]: rec M m ≡ λ X. rec M m X, then the body by e4
  let e3 : ConvT riEnv n Γ2 (.app (.app (.const 2 [l]) (.bvar 1)) (.bvar 0))
      (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
        (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))) _ :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta Γ2 _ _ _ h2))
      (.lam Γ2 (.sort .zero) (.sort .zero) _ _ _ (.succ .zero) (.refl _ _ _ (.sort _ .zero)) e4)
  let e2 : ConvT riEnv n Γ1 (.app (.const 2 [l]) (.bvar 0))
      (.lam riMinTy (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
        (foldApps (.const 2 [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))) _ :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta Γ1 _ _ _ h1))
      (.lam Γ1 riMinTy riMinTy _ _ _ _ (.refl _ _ _ (minTyL Γ l)) e3)
  .trans _ _ _ _ _ (.symm _ _ _ _ (.eta Γ _ _ _ h0))
    (.lam Γ (recMot l) (recMot l) _ _ _ _ (.refl _ _ _ (motTyL Γ l)) e2)

/-- **`recL l ≡ rec.{l}` at the recursor's type, in every context**: `bk (tr rec.{l})` is `rec.{l}`
    up to conversion. -/
def recL_conv_rec (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT riEnv n Γ (recL l) (.const 2 [l]) (instantiateLevels [l] riRecTy) :=
  .symm _ _ _ _ (.trans _ _ _ _ _ (rec_conv_recE Γ l hl) (recE_conv_recL Γ l hl))

end EtaK

/-! ## §9 `bk ∘ tr` is the identity up to conversion, on `riEnv`'s typed terms -/

section BkTr

theorem bk_tr_lit (t : Nat) : bk (tr (.lit t)) = bk (tr (natExpand t)) := by
  rw [tr_natExpand]; rfl

theorem riEnv_members_cases {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m) :
    (r = 2 ∧ m = riRec) ∨ (r = 1 ∧ m = riCtor) ∨ (r = 0 ∧ m = riFam) := by
  rw [riEnv_members] at h
  by_cases h2 : r = 2
  · rw [if_pos h2] at h; exact Or.inl ⟨h2, (Option.some.inj h).symm⟩
  · rw [if_neg h2] at h
    by_cases h1 : r = 1
    · rw [if_pos h1] at h; exact Or.inr (Or.inl ⟨h1, (Option.some.inj h).symm⟩)
    · rw [if_neg h1] at h
      by_cases h0 : r = 0
      · rw [if_pos h0] at h; exact Or.inr (Or.inr ⟨h0, (Option.some.inj h).symm⟩)
      · rw [if_neg h0] at h; exact Option.noConfusion h

theorem riEnv_members_inductive' {r : Nat} {m : CheckedMember} (hm : riEnv.members r = some m)
    (hind : m.mclass = .inductiveM) : r = 0 ∧ m = riFam := by
  rcases riEnv_members_cases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · exact absurd hind (by decide)
  · exact absurd hind (by decide)
  · exact h

variable {n : Nat}

/-- **the round trip on terms**: every term typed in `riEnv` converts to its image under
    `bk ∘ tr`, at its type. The only non-identity leaf is the recursor, `rec.{l} ≡ recL l`
    (§8); literals go through their expansion. No row is assumed. -/
theorem trbkConv : {Γ : LCtx} → {e A : Expr Nat} → HasTyT riEnv n Γ e A →
    Nonempty (ConvT riEnv n Γ e (bk (tr e)) A)
  | _, _, _, .sort Γ l => ⟨.refl _ _ _ (.sort Γ l)⟩
  | _, _, _, .bvar Γ i A h => ⟨.refl _ _ _ (.bvar Γ i A h)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf => by
      rcases riEnv_members_cases hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hl1 : ls.length = 1 := hlen
        obtain ⟨l, rfl⟩ := List.length_eq_one.mp hl1
        exact ⟨.symm _ _ _ _ (recL_conv_rec Γ l hwf)⟩
      · exact ⟨.refl _ _ _ (.const Γ 1 ls riCtor rfl hlen hwf)⟩
      · exact ⟨.refl _ _ _ (.const Γ 0 ls riFam rfl hlen hwf)⟩
  | _, _, _, .pi Γ A u B v hA hB => by
      obtain ⟨cA⟩ := trbkConv hA
      obtain ⟨cB⟩ := trbkConv hB
      exact ⟨.pi Γ A (bk (tr A)) B (bk (tr B)) u v cA cB⟩
  | _, _, _, .lam Γ A u body B hA hbody => by
      obtain ⟨cA⟩ := trbkConv hA
      obtain ⟨cb⟩ := trbkConv hbody
      exact ⟨.lam Γ A (bk (tr A)) body (bk (tr body)) B u cA cb⟩
  | _, _, _, .app Γ f a A B hf ha => by
      obtain ⟨cf⟩ := trbkConv hf
      obtain ⟨ca⟩ := trbkConv ha
      exact ⟨.app Γ f (bk (tr f)) a (bk (tr a)) A B cf ca⟩
  | _, _, _, .letE Γ A u value B body hA hv hb => by
      obtain ⟨cA⟩ := trbkConv hA
      obtain ⟨cv⟩ := trbkConv hv
      obtain ⟨cb⟩ := trbkConv hb
      exact ⟨.letE Γ A (bk (tr A)) value (bk (tr value)) body (bk (tr body)) B u cA cv cb⟩
  | _, _, _, .lit Γ t T hexp => by
      obtain ⟨c⟩ := trbkConv hexp
      rw [bk_tr_lit]
      exact ⟨.trans _ _ _ _ _ (.lit Γ t (natExpand t) T (.of t) hexp) c⟩
  | _, _, _, .conv Γ e A B u h hc => by
      obtain ⟨c⟩ := trbkConv h
      exact ⟨.tyConv Γ e (bk (tr e)) A B u c hc⟩

/-- **the round trip on contexts**: `bk (tr Γ)` converts to `Γ` (as a `CtxConvT`, pointwise by
    the term round trip), for every well-formed `Γ`. -/
theorem ctxConv_bktr : {Γ : LCtx} → CtxWfT riEnv n Γ →
    Nonempty (CtxConvT riEnv n (bkCtx (trCtx Γ)) Γ)
  | _, .nil => ⟨.nil⟩
  | _, .assumption Γ A u hΓ hA => by
      obtain ⟨hcc⟩ := ctxConv_bktr hΓ
      obtain ⟨cA⟩ := trbkConv hA
      have hA' : HasTyT riEnv n Γ (bk (tr A)) (.sort u) :=
        (NativeValleys.convEnds riEnvWfT hΓ cA).2.1
      exact ⟨.assumption hcc hA' hA (.symm _ _ _ _ cA)⟩
  | _, .letBinding Γ A u v hΓ hA hv => by
      obtain ⟨hcc⟩ := ctxConv_bktr hΓ
      obtain ⟨cA⟩ := trbkConv hA
      obtain ⟨cv⟩ := trbkConv hv
      have hA' : HasTyT riEnv n Γ (bk (tr A)) (.sort u) :=
        (NativeValleys.convEnds riEnvWfT hΓ cA).2.1
      have hcv : ConvT riEnv n Γ (bk (tr v)) v (bk (tr A)) :=
        .tyConv _ _ _ _ _ u (.symm _ _ _ _ cv) cA
      exact ⟨.letBinding hcc hA' hA (.symm _ _ _ _ cA) hv hcv⟩

/-- a conversion in `bk (tr Γ)` is one in `Γ`. -/
theorem convT_bktr_ctx {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {a b T : Expr Nat}
    (c : ConvT riEnv n (bkCtx (trCtx Γ)) a b T) : Nonempty (ConvT riEnv n Γ a b T) := by
  obtain ⟨hcc⟩ := ctxConv_bktr hΓ
  exact ⟨convT_ctx (envClosed_of_envWfT riEnvWfT) hcc c⟩

end BkTr

/-! ## §10 the family row of `riEnv`, from its Π row -/

section FamRow

variable {n : Nat}

theorem convArgsT_sort_nil {E : ResolvedEnv} {Γ : LCtx} {u : Level} {fs fs' : List (Expr Nat)}
    (h : ConvArgsT E n Γ (.sort u) fs fs') : fs = [] ∧ fs' = [] := by
  cases h with
  | nil _ => exact ⟨rfl, rfl⟩

/-- `x : Sort 0` from `RI x : Sort w`, under the Π row. -/
theorem riIdxTyped (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {ls : List Level}
    {x : Expr Nat} {w : Level} (hty : HasTyT riEnv n Γ (foldApps (.const 0 ls) [x]) (.sort w)) :
    Nonempty (HasTyT riEnv n Γ x (.sort .zero)) := by
  obtain ⟨⟨-, -, hargs, -⟩⟩ := hasTyT_spineInv_rows riEnvWfT hpi hΓ
    (r := 0) (ls := ls) (m := riFam) rfl (doms := [.sort .zero]) (U := .sort .zero) rfl
    [x] rfl hty
  exact ⟨hargs 0 x (.sort .zero) rfl rfl⟩

/-- **the index row at `RI`, in `riEnv`, under its Π row**: `RI x ≡ RI a : Sort w` gives
    `x ≡ a : Sort 0`. Route: the shadow in the consistent twin (`riIdxShadow_cEnv`), `bk` on
    the twin's derivation (§7), the context round trip (§9), and the term round trip at both
    ends (§9). -/
theorem riIdxRow_of_piRow (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    {x a : Expr Nat} {w : Level}
    (h : ConvT riEnv n Γ (.app (.const 0 []) x) (.app (.const 0 []) a) (.sort w)) :
    Nonempty (ConvT riEnv n Γ x a (.sort .zero)) := by
  obtain ⟨cc⟩ := riIdxShadow_cEnv hΓ h
  obtain ⟨hΓc⟩ := cTwin.trCtxWfW hΓ
  obtain ⟨hΓb⟩ := bkCtxWf hpi hΓc
  obtain ⟨cb⟩ := bkConv hpi cc hΓb
  obtain ⟨cb'⟩ := convT_bktr_ctx hΓ cb
  have ends := NativeValleys.convEnds riEnvWfT hΓ h
  obtain ⟨hx⟩ := riIdxTyped hpi hΓ (ls := []) ends.1
  obtain ⟨ha⟩ := riIdxTyped hpi hΓ (ls := []) ends.2.1
  obtain ⟨c1⟩ := trbkConv hx
  obtain ⟨c2⟩ := trbkConv ha
  exact ⟨.trans _ _ _ _ _ c1 (.trans _ _ _ _ _ cb' (.symm _ _ _ _ c2))⟩

/-- **ROW 3 of `riEnv`, from its Π row**: `TypedRowsWf.famAppRow`'s exact field type. -/
theorem riFamAppRow_of_piRow (hpi : PiRowField riEnv n) {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ)
    {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (hm : riEnv.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT riEnv n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT riEnv n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT riEnv n Γ (instantiateLevels ls m.mtype) xs xs' := by
  obtain ⟨rfl, rfl⟩ := riEnv_members_inductive' hm hind
  obtain ⟨c⟩ := convSortR hpi hΓ hty h
  obtain ⟨hls, hlen, hargs⟩ := riFamAppShadow_cEnv hΓ c
  refine ⟨hls, hlen, ?_⟩
  have hargs' : ConvArgsT cEnv n (trCtx Γ) (.pi (.sort .zero) (.sort .zero))
      (xs.map tr) (xs'.map tr) := hargs
  show ConvArgsT riEnv n Γ (.pi (.sort .zero) (.sort .zero)) xs xs'
  cases xs with
  | nil =>
      cases xs' with
      | nil => exact .nil _
      | cons x' xs₁' => exact Nat.noConfusion hlen
  | cons x xs₁ =>
      cases xs' with
      | nil => exact Nat.noConfusion hlen
      | cons x' xs₁' =>
          simp only [List.map] at hargs'
          cases hargs' with
          | cons A B f f' fs fs' hc hs =>
              have hs' : ConvArgsT cEnv n (trCtx Γ) (.sort .zero) (xs₁.map tr) (xs₁'.map tr) := hs
              obtain ⟨hfs, hfs'⟩ := convArgsT_sort_nil hs'
              rw [List.map_eq_nil_iff] at hfs hfs'
              subst hfs hfs'
              have hls0 : ls = [] := by
                obtain ⟨⟨hl, -, -, -⟩⟩ := hasTyT_spineInv_rows riEnvWfT hpi hΓ
                  (r := 0) (ls := ls) (m := riFam) rfl (doms := [.sort .zero]) (U := .sort .zero) rfl
                  [x] rfl hty
                exact List.length_eq_zero.mp hl
              have hls0' : ls' = [] := by
                have ends := NativeValleys.convEnds riEnvWfT hΓ c
                obtain ⟨⟨hl, -, -, -⟩⟩ := hasTyT_spineInv_rows riEnvWfT hpi hΓ
                  (r := 0) (ls := ls') (m := riFam) rfl (doms := [.sort .zero]) (U := .sort .zero) rfl
                  [x'] rfl ends.2.1
                exact List.length_eq_zero.mp hl
              subst hls0 hls0'
              have c' : ConvT riEnv n Γ (.app (.const 0 []) x) (.app (.const 0 []) x') (.sort w) := c
              obtain ⟨cx⟩ := riIdxRow_of_piRow hpi hΓ c'
              exact .cons (.sort .zero) (.sort .zero) x x' [] [] ⟨cx⟩ (.nil _)

end FamRow

/-! ## §11 class B's rows reduce to its Π row -/

/-- **`TypedRowsWf riEnv n` from `PiRowField riEnv n`**: the sort row is landed
    (`riSortRow_chain`, through the axiomatic twin), the Π row is the hypothesis, and the
    family row is lifted back from the consistent twin (§10). -/
theorem riTypedRowsWf_of_piRow {n : Nat} (hpi : PiRowField riEnv n) : TypedRowsWf riEnv n where
  sortRow := fun {_Γ} hΓ {_u _v} h => riSortRow_chain hΓ h
  piRow := hpi
  famAppRow := fun {_Γ} hΓ {_r _m _ls _ls' _xs _xs' _w} hm hind hty h =>
    riFamAppRow_of_piRow hpi hΓ hm hind hty h

/-- **for class B's `RI`, the three rows are the Π row.** -/
theorem riTypedRowsWf_iff_piRow {n : Nat} : TypedRowsWf riEnv n ↔ PiRowField riEnv n :=
  ⟨fun t => t.piRow, riTypedRowsWf_of_piRow⟩

end Rcic.Syn.FamApp

#print axioms Rcic.Syn.FamApp.bkTy
#print axioms Rcic.Syn.FamApp.bkConv
#print axioms Rcic.Syn.FamApp.recL_conv_rec
#print axioms Rcic.Syn.FamApp.trbkConv
#print axioms Rcic.Syn.FamApp.riIdxRow_of_piRow
#print axioms Rcic.Syn.FamApp.riFamAppRow_of_piRow
#print axioms Rcic.Syn.FamApp.riTypedRowsWf_of_piRow
#print axioms Rcic.Syn.FamApp.riTypedRowsWf_iff_piRow
