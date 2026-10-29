import rcic.RcicTypedGroupPins
import rcic.RcicTypedScopeCheckPins
import rcic.RcicDTMetaTyped
import rcic.RcicClassCRevealed
import rcic.RcicTypedScopeCheck
import rcic.RcicDT1011Rows
import rcic.RcicNativeValleyOf

/-!
# cc-classc — the class-(c) fixture `RI` read through a scoped twin

`RI : Sort 0 → Sort 0` (`RcicClassCRevealed`) is a class-(c3) group: a `Prop` family, one constructor
`mk : Π X : Sort 0, RI X` whose field is data revealed as the bare index, eliminating into any sort.
It is outside the copy's profile, so no landed row speaks about it. `CLASSC_CEX.md` §6.4 asked for
axiom-spine injectivity, which would have let a group-free translation through. No landed row covers
an axiom head either, so this module goes another way.

**The twin `gEnv`** keeps the family `RI₀ := riFam` and drops the constructor. `RI₀` is then a `Prop`
family with an index and no constructor, which may eliminate into any sort (O1-a) and is in the copy's
profile. Its recursor is `rec₀` (reference `1`) and `mk₀ : Π X : Sort 0, RI₀ X` is an axiom
(reference `2`). `gEnv` passes the scope test, so its three rows are landed (`gRows`).

**The translation `tr`** sends `RI ↦ RI₀`, `mk ↦ mk₀`, and `rec.{l} ↦ recT l := λ M m X h. m X`; a
numeral literal goes to `trNat`. It commutes with `lift` and `instantiate`. `trTy`, `trConv`,
`trTyConv` and `trCtxWf` send every derivation of `riEnv` to a derivation of `gEnv`. The one rule that
needs work is `ι`: `rec M m X (mk x) ⟶ m x` translates to `recT l M' m' X' (mk₀ x') ≡ m' x'`, which
asks for `x' ≡ X'`. `iota_agree` reads `X'` off the redex's own typing (four Π-inversions against the
known type of `recT l`, by the rows of `gEnv`) and then applies `gEnv`'s landed `famAppRow` at `RI₀`.

* §2 the twin: `gEnv`, `gEnvWfT`. §3 `gEnvWfT_scopeCheck`, `gRows`.
* §4 `tr` and its `lift` / `instantiate` laws; §5 `recT_typed`, `recT_conv`.
* §6 β by the rows (`betaConv_rows`) and the `CE` calculus; `red4`; `appInvKnown`; `iota_agree`;
  `iota_conv`.
* §7 the shape of every ι witness of `riEnv` (`riIota_inv`).
* §8 the translation theorems. §9 `riSortRow`, `riSortRow_chain`, `riPiShadow`.

What the shadow does not give: a way back. `rec₀ : Π M X h, M X h` has no counterpart in `riEnv`
(`RI X` is inhabited there), so a conversion in `gEnv` between translated terms is not turned into a
conversion in `riEnv`. Row 1 is a `Prop` about levels and needs no way back (`riSortRow`). The domain
and codomain conversions of row 2 do (`riPiShadow` states them in `gEnv`). `closure_claim = 0`.
-/

namespace Rcic.Syn.ClassC

set_option maxRecDepth 8192

open Rcic.Declarative

/-! ## §2 the scoped twin `gEnv`

`RI₀ : Sort 0 → Sort 0` is `riFam` itself, a `Prop` family with an index and no constructor, which
eliminates into any sort (O1-a) and is therefore in the copy's profile. Its recursor is `rec₀`
(reference `1`), and `mk₀ : Π X : Sort 0, RI₀ X` is an axiom (reference `2`). -/

open Rcic.Syn

/-- `rec₀.{u} : Π (M : Π X : Sort 0, RI₀ X → Sort u) (X : Sort 0) (t : RI₀ X), M X t`. -/
def gRecTy : Expr Nat :=
  .pi riMotTy (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
    (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

def gRec : CheckedMember := ⟨.recursorM, 1, gRecTy, none⟩

def gGroupEnv : ResolvedEnv := extendEnv riFamEnv 1 gRec

def gMk : CheckedMember := ⟨.axiomM, 0, riCtor.mtype, none⟩

def gEnv : ResolvedEnv := extendEnv gGroupEnv 2 gMk

theorem gGroupEnv_members (r : Nat) :
    gGroupEnv.members r = if r = 1 then some gRec else if r = 0 then some riFam else none := rfl

theorem gCensus : CtorCensus riFamEnv 0 1 := by
  refine ⟨by decide, fun c => ⟨?_, fun h => absurd h (by omega)⟩⟩
  rintro ⟨cm, hc, hk, _⟩
  rw [riFamEnv_members] at hc
  split at hc
  · cases hc; cases hk
  · cases hc

def gPolicy : RecursorEliminationAdmitted riFamEnv 1 gRec where
  family := riFamView riFamEnv rfl
  constructors := []
  constructorViews := fun i => i.elim0
  constructorsPresent := fun i => i.elim0
  recursorRef := rfl
  minorTypes := []
  minorCount := rfl
  policy := .anySort
  selected := .emptyProp (fun _ => rfl) rfl
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

def gIotaClause : IotaDescriptorClause riFamEnv gPolicy where
  signatureOnly := rfl
  shapesAt := fun i => i.elim0
  fuelAt := fun i => i.elim0
  analyzed := fun i => i.elim0
  typed := fun i => i.elim0

def gRec_admitted : IndGroupAdmitted riFamEnv 1 gRec :=
  .recursor gPolicy rfl gCensus (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) gIotaClause

def gRecSort : Level :=
  .imax (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))
    (.imax (.succ .zero) (.imax .zero (.param 0)))

def gRecTyT : HasTyT riFamEnv 1 [] gRecTy (.sort gRecSort) :=
  (tyAtC riFamEnv 1 12 [] gRecTy (.sort gRecSort)).get (by rfl)

theorem gRecTyped : IndGroupTypedT gRec_admitted :=
  ⟨(by
    intro i
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    exact ⟨.sort _ _⟩), fun i => i.elim0, fun i => i.elim0⟩

def gMembers :
    GroupMembersT riFamEnv emptyEnv [(0, riFam), (1, gRec)] gGroupEnv :=
  .cons _ 0 riFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    riFam_admitted PUnit.unit _ riFamTyT (fun h => nomatch h) riFamGroupTyped
    (.cons _ 1 gRec _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      gRec_admitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ gRecTyT
      (fun h => nomatch h) gRecTyped (.nil _))

def gGroupWfT : EnvWfT gGroupEnv :=
  .group emptyEnv 0 riFam [] 1 gRec gGroupEnv .empty rfl (fun c hc => by simp at hc) rfl gMembers

def gMkTyT : HasTyT gGroupEnv 0 [] gMk.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (.const _ 0 [] riFam rfl rfl rfl) (.bvar _ 0 _ rfl))

def gEnvWfT : EnvWfT gEnv :=
  .axiom gGroupEnv 2 gMk.mtype _ gGroupWfT rfl gMkTyT (fun _ => rfl) rfl

/-! ## §3 `gEnv` passes the scope test, so its three rows are landed -/

theorem gEnvWfT_scopeCheck : gEnvWfT.ScopeCheck :=
  ⟨trivial, synChecker, (groupSkel? synChecker emptyEnv 8 0 riFam [] gRec 0).get rfl, rfl, by decide⟩

theorem gRows (n : Nat) : TypedRowsWf gEnv n :=
  typedRowsWf_of_scopeCheck gEnvWfT gEnvWfT_scopeCheck n

/-! ## §4 the translation `tr : riEnv → gEnv` on terms

`RI ↦ RI₀`, `mk ↦ mk₀`, and `rec.{l} ↦ recT l := λ M m X h. m X`. -/

/-- `Π (X : Sort 0), RI₀ X → Sort l`. -/
def recMot (l : Level) : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))

/-- `Π (X : Sort 0), M X (mk₀ X)`, under `[M]`. -/
def recMin : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 2 []) (.bvar 0)))

/-- `λ (M : motive) (m : minor) (X : Sort 0) (h : RI₀ X). m X`. -/
def recT (l : Level) : Expr Nat :=
  .lam (recMot l) (.lam recMin (.lam (.sort .zero) (.lam (.app (.const 0 []) (.bvar 0))
    (.app (.bvar 2) (.bvar 1)))))

/-- `Π M m X h, M X h` over the translated constructor: the type of `recT l`. -/
def recTyTr (l : Level) : Expr Nat :=
  .pi (recMot l) (.pi recMin (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))

/-- the translation of a numeral literal: `natExpand t` with `mk ↦ mk₀`, `rec ↦ recT`. -/
def trNat : Nat → Expr Nat
  | 0 => .const 2 []
  | t + 1 => .app (recT .zero) (trNat t)

def tr : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls =>
      if r = 1 then .const 2 ls else if r = 2 then recT (ls.headD .zero) else .const r ls
  | .app f x => .app (tr f) (tr x)
  | .lam a b => .lam (tr a) (tr b)
  | .pi a b => .pi (tr a) (tr b)
  | .letE a v b => .letE (tr a) (tr v) (tr b)
  | .lit t => trNat t

def trDecl : LocalDecl → LocalDecl
  | .assumption a => .assumption (tr a)
  | .letBinding a v => .letBinding (tr a) (tr v)

def trCtx (Γ : LCtx) : LCtx := Γ.map trDecl

theorem tr_natExpand (t : Nat) : tr (natExpand t) = trNat t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [natExpand, litSucc, tr, trNat, ih]; rfl

/-! closed terms are fixed by `lift` and `instantiate` -/

def ClosedE : Nat → Expr Nat → Prop
  | d, .bvar i => i < d
  | _, .sort _ => True
  | _, .const _ _ => True
  | d, .app f x => ClosedE d f ∧ ClosedE d x
  | d, .lam a b => ClosedE d a ∧ ClosedE (d + 1) b
  | d, .pi a b => ClosedE d a ∧ ClosedE (d + 1) b
  | d, .letE a v b => ClosedE d a ∧ ClosedE d v ∧ ClosedE (d + 1) b
  | _, .lit _ => True

theorem lift_closedE (k : Nat) : (e : Expr Nat) → ∀ {d c : Nat}, ClosedE d e → d ≤ c →
    lift c k e = e
  | .bvar i, d, c, h, hdc => by
      have : ¬ c ≤ i := by simp only [ClosedE] at h; omega
      simp [lift, this]
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .app f x, d, c, h, hdc => by
      simp only [lift, lift_closedE k f h.1 hdc, lift_closedE k x h.2 hdc]
  | .lam a b, d, c, h, hdc => by
      simp only [lift, lift_closedE k a h.1 hdc, lift_closedE k b h.2 (Nat.succ_le_succ hdc)]
  | .pi a b, d, c, h, hdc => by
      simp only [lift, lift_closedE k a h.1 hdc, lift_closedE k b h.2 (Nat.succ_le_succ hdc)]
  | .letE a v b, d, c, h, hdc => by
      simp only [lift, lift_closedE k a h.1 hdc, lift_closedE k v h.2.1 hdc,
        lift_closedE k b h.2.2 (Nat.succ_le_succ hdc)]
  | .lit _, _, _, _, _ => rfl

theorem instantiate_closedE (s : Expr Nat) : (e : Expr Nat) → ∀ {d j : Nat}, ClosedE d e → d ≤ j →
    instantiate j s e = e
  | .bvar i, d, j, h, hdj => by
      have h1 : i ≠ j := by simp only [ClosedE] at h; omega
      have h2 : ¬ j < i := by simp only [ClosedE] at h; omega
      simp [instantiate, h1, h2]
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .app f x, d, j, h, hdj => by
      simp only [instantiate, instantiate_closedE s f h.1 hdj, instantiate_closedE s x h.2 hdj]
  | .lam a b, d, j, h, hdj => by
      simp only [instantiate, instantiate_closedE s a h.1 hdj,
        instantiate_closedE (lift 0 1 s) b h.2 (Nat.succ_le_succ hdj)]
  | .pi a b, d, j, h, hdj => by
      simp only [instantiate, instantiate_closedE s a h.1 hdj,
        instantiate_closedE (lift 0 1 s) b h.2 (Nat.succ_le_succ hdj)]
  | .letE a v b, d, j, h, hdj => by
      simp only [instantiate, instantiate_closedE s a h.1 hdj, instantiate_closedE s v h.2.1 hdj,
        instantiate_closedE (lift 0 1 s) b h.2.2 (Nat.succ_le_succ hdj)]
  | .lit _, _, _, _, _ => rfl

theorem recT_closed (l : Level) : ClosedE 0 (recT l) := by
  simp [recT, recMot, recMin, ClosedE]

theorem trNat_closed (t : Nat) : ClosedE 0 (trNat t) := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨recT_closed _, ih⟩

theorem tr_lift (k : Nat) : (e : Expr Nat) → ∀ c, tr (lift c k e) = lift c k (tr e)
  | .bvar i, c => by
      by_cases h : c ≤ i <;> simp [lift, tr, h]
  | .sort _, _ => rfl
  | .const r ls, c => by
      simp only [tr]
      split
      · rfl
      · split
        · exact (lift_closedE k _ (recT_closed _) (Nat.zero_le c)).symm
        · rfl
  | .app f x, c => by simp only [lift, tr, tr_lift k f c, tr_lift k x c]
  | .lam a b, c => by simp only [lift, tr, tr_lift k a c, tr_lift k b (c + 1)]
  | .pi a b, c => by simp only [lift, tr, tr_lift k a c, tr_lift k b (c + 1)]
  | .letE a v b, c => by
      simp only [lift, tr, tr_lift k a c, tr_lift k v c, tr_lift k b (c + 1)]
  | .lit t, c => (lift_closedE k _ (trNat_closed t) (Nat.zero_le c)).symm

theorem tr_instantiate (s : Expr Nat) : (e : Expr Nat) → ∀ j,
    tr (instantiate j s e) = instantiate j (tr s) (tr e)
  | .bvar i, j => by
      by_cases h1 : i = j
      · simp [instantiate, tr, h1]
      · by_cases h2 : j < i <;> simp [instantiate, tr, h1, h2]
  | .sort _, _ => rfl
  | .const r ls, j => by
      simp only [tr]
      split
      · rfl
      · split
        · exact (instantiate_closedE _ _ (recT_closed _) (Nat.zero_le j)).symm
        · rfl
  | .app f x, j => by simp only [instantiate, tr, tr_instantiate s f j, tr_instantiate s x j]
  | .lam a b, j => by
      simp only [instantiate, tr, tr_instantiate s a j, tr_instantiate (lift 0 1 s) b (j + 1),
        tr_lift]
  | .pi a b, j => by
      simp only [instantiate, tr, tr_instantiate s a j, tr_instantiate (lift 0 1 s) b (j + 1),
        tr_lift]
  | .letE a v b, j => by
      simp only [instantiate, tr, tr_instantiate s a j, tr_instantiate s v j,
        tr_instantiate (lift 0 1 s) b (j + 1), tr_lift]
  | .lit t, j => (instantiate_closedE _ _ (trNat_closed t) (Nat.zero_le j)).symm

theorem tr_instantiate0 (s e : Expr Nat) : tr (instantiate0 s e) = instantiate0 (tr s) (tr e) :=
  tr_instantiate s e 0

theorem tr_foldApps (f : Expr Nat) (xs : List (Expr Nat)) :
    tr (foldApps f xs) = foldApps (tr f) (xs.map tr) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [foldApps, ih, tr, List.map]

/-! ## §5 `recT l` is typed in `gEnv` at the translated recursor type -/

section RecTyped

variable {n : Nat}

/-- `RI₀ (bvar 0)`: the `h` binder's domain, under `[X, …]`. -/
abbrev ri0X : Expr Nat := .app (.const 0 []) (.bvar 0)

/-- `M X h`, under `[h, X, m, M]`. -/
abbrev recB4 : Expr Nat := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)

def g1 (Γ : LCtx) (l : Level) : LCtx := .assumption (recMot l) :: Γ
def g2 (Γ : LCtx) (l : Level) : LCtx := .assumption recMin :: g1 Γ l
def g3 (Γ : LCtx) (l : Level) : LCtx := .assumption (.sort .zero) :: g2 Γ l
def g4 (Γ : LCtx) (l : Level) : LCtx := .assumption ri0X :: g3 Γ l

def gRIty {Γ : LCtx} {a : Expr Nat} (ha : HasTyT gEnv n Γ a (.sort .zero)) :
    HasTyT gEnv n Γ (.app (.const 0 []) a) (.sort .zero) :=
  .app _ _ _ _ _ (.const _ 0 [] riFam rfl rfl rfl) ha

def gMkty {Γ : LCtx} {a : Expr Nat} (ha : HasTyT gEnv n Γ a (.sort .zero)) :
    HasTyT gEnv n Γ (.app (.const 2 []) a) (.app (.const 0 []) a) :=
  .app _ _ _ _ _ (.const _ 2 [] gMk rfl rfl rfl) ha

def gMotTy (Γ : LCtx) (l : Level) :
    HasTyT gEnv n Γ (recMot l) (.sort (.imax (.succ .zero) (.imax .zero (.succ l)))) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
    (.imax .zero (.succ l)) (.sort Γ .zero)
    (.pi _ (.app (.const 0 []) (.bvar 0)) .zero (.sort l) (.succ l)
      (gRIty (.bvar _ 0 _ rfl)) (.sort _ l))

/-- under `[M]`: `M X (mk₀ X) : Sort l`, under `[X, M]`. -/
def gMinBody (Γ : LCtx) (l : Level) :
    HasTyT gEnv n (.assumption (.sort .zero) :: g1 Γ l)
      (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 2 []) (.bvar 0))) (.sort l) :=
  .app _ _ _ (.app (.const 0 []) (.bvar 0)) (.sort l)
    (.app _ _ _ (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))
      (.bvar _ 1 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort l))) rfl)
      (.bvar _ 0 _ rfl))
    (gMkty (.bvar _ 0 _ rfl))

def gMinTy (Γ : LCtx) (l : Level) :
    HasTyT gEnv n (g1 Γ l) recMin (.sort (.imax (.succ .zero) l)) :=
  .pi _ (.sort .zero) (.succ .zero) _ l (.sort _ .zero) (gMinBody Γ l)

/-- `m X : M X h`, under `[h, X, m, M]`. -/
def gBody (Γ : LCtx) (l : Level) :
    HasTyT gEnv n (g4 Γ l) (.app (.bvar 2) (.bvar 1)) recB4 :=
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
        (gRIty (.bvar _ 1 _ rfl)) (gMkty (.bvar _ 1 _ rfl)) (.bvar _ 0 _ rfl)))

end RecTyped

section RecTyped2

variable {n : Nat}

def gLam4 (Γ : LCtx) (l : Level) :
    HasTyT gEnv n (g3 Γ l) (.lam ri0X (.app (.bvar 2) (.bvar 1))) (.pi ri0X recB4) :=
  .lam _ _ .zero _ _ (gRIty (.bvar _ 0 _ rfl)) (gBody Γ l)

def gLam3 (Γ : LCtx) (l : Level) :
    HasTyT gEnv n (g2 Γ l) (.lam (.sort .zero) (.lam ri0X (.app (.bvar 2) (.bvar 1))))
      (.pi (.sort .zero) (.pi ri0X recB4)) :=
  .lam _ _ (.succ .zero) _ _ (.sort _ .zero) (gLam4 Γ l)

/-- the λ under the motive binder. -/
def recT1 : Expr Nat :=
  .lam recMin (.lam (.sort .zero) (.lam ri0X (.app (.bvar 2) (.bvar 1))))

def recTy1 : Expr Nat :=
  .pi recMin (.pi (.sort .zero) (.pi ri0X recB4))

def gLam2 (Γ : LCtx) (l : Level) : HasTyT gEnv n (g1 Γ l) recT1 recTy1 :=
  .lam _ _ _ _ _ (gMinTy Γ l) (gLam3 Γ l)

def recT_typed (Γ : LCtx) (l : Level) : HasTyT gEnv n Γ (recT l) (recTyTr l) :=
  .lam _ _ _ _ _ (gMotTy Γ l) (gLam2 Γ l)

/-- the translated recursor type is the translation of `rec`'s stored type at `[l]`. -/
theorem tr_recTy (l : Level) : tr (instantiateLevels [l] riRecTy) = recTyTr l := rfl

end RecTyped2

section RecConv

variable {n : Nat}

/-- the translated recursor is level-congruent: `recT l ≡ recT l'` when `l =ₙ l'`. -/
def recT_conv (Γ : LCtx) (l l' : Level) (h : eqN l l') :
    ConvT gEnv n Γ (recT l) (recT l') (recTyTr l) :=
  .lam Γ (recMot l) (recMot l') recT1 recT1 recTy1
    (.imax (.succ .zero) (.imax .zero (.succ l)))
    (.pi Γ (.sort .zero) (.sort .zero) _ _ (.succ .zero) (.imax .zero (.succ l))
      (.refl _ _ _ (.sort _ _))
      (.pi _ ri0X ri0X (.sort l) (.sort l') .zero (.succ l)
        (.refl _ _ _ (gRIty (.bvar _ 0 _ rfl)))
        (.sorts _ l l' h)))
    (.refl _ _ _ (gLam2 Γ l))

end RecConv

/-! ## §6 reading `gEnv`: β by the rows, and the `CE` calculus

`CE Γ e e'` says that `e ≡ e'` at every type of `e`. It is closed under β (`betaConv_rows`, the rows'
β arm), under transitivity and under the left congruence of application. -/

section Read

variable {n : Nat}

/-- retyping a conversion along a type-conversion chain. -/
def convRetype {Γ : LCtx} {a b T S : Expr Nat} (c : ConvT gEnv n Γ a b T) :
    TyConvT gEnv n Γ T S → ConvT gEnv n Γ a b S
  | .refl _ _ => c
  | .of _ _ _ u h => .tyConv _ _ _ _ _ u c h
  | .trans _ _ _ _ h1 h2 => convRetype (convRetype c h1) h2

theorem betaConv_rows {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) {A0 body arg S : Expr Nat}
    (h : HasTyT gEnv n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (ConvT gEnv n Γ (.app (.lam A0 body) arg) (instantiate0 arg body) S) := by
  have hrows := gRows n
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨u0, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
  obtain ⟨w, ⟨hBw⟩⟩ := DT007T_typing_regularity_of_envWfT gEnvWfT
    (.assumption Γ A0 u0 hΓ hA0ty) hbody
  obtain ⟨cdom⟩ := convT_of_tyConvT_sort_rows gEnvWfT hrows hΓ hA0ty hBdom
  obtain ⟨ccod⟩ := convT_of_tyConvT_sort_rows gEnvWfT hrows
    (.assumption Γ A0 u0 hΓ hA0ty) hBw hBcod
  have ha' : HasTyT gEnv n Γ arg A0 :=
    HasTyT.conv _ _ _ _ u0 ha (ConvT.symm _ _ _ _ cdom)
  have hcod' : ConvT gEnv n Γ (instantiate0 arg B_lam) (instantiate0 arg B1) (.sort w) :=
    convT_subst0_of_envWfT gEnvWfT ccod ha'
  exact ⟨convRetype (ConvT.beta Γ A0 body arg B_lam u0 hA0ty hbody ha')
    (.trans _ _ _ _ (.of _ _ _ _ hcod') hcv)⟩

def CE (Γ : LCtx) (e e' : Expr Nat) : Prop :=
  ∀ S, HasTyT gEnv n Γ e S → Nonempty (ConvT gEnv n Γ e e' S)

theorem ce_beta {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) {A0 body arg : Expr Nat} :
    CE (n := n) Γ (.app (.lam A0 body) arg) (instantiate0 arg body) :=
  fun _ h => betaConv_rows hΓ h

theorem ce_trans {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) {e e' e'' : Expr Nat}
    (h1 : CE (n := n) Γ e e') (h2 : CE (n := n) Γ e' e'') : CE (n := n) Γ e e'' := by
  intro S h
  obtain ⟨c1⟩ := h1 S h
  obtain ⟨c2⟩ := h2 S (NativeValleys.convEnds gEnvWfT hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 c2⟩

theorem ce_appL {Γ : LCtx} {f f' : Expr Nat} (a : Expr Nat)
    (h1 : CE (n := n) Γ f f') : CE (n := n) Γ (.app f a) (.app f' a) := by
  intro S h
  obtain ⟨A, B, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := h1 _ hf
  exact ⟨convRetype (ConvT.app Γ f f' a a A B c (ConvT.refl Γ a A ha)) hcv⟩

theorem ce_eq {Γ : LCtx} {e e' e'' : Expr Nat} (h : e' = e'') (c : CE (n := n) Γ e e') :
    CE (n := n) Γ e e'' := h ▸ c

end Read

section Red4

variable {n : Nat}

theorem ce_of_eq {Γ : LCtx} {e e' : Expr Nat} (h : e = e') : CE (n := n) Γ e e' :=
  fun _ hS => ⟨h ▸ ConvT.refl _ _ _ hS⟩

/-- the four β steps of the translated recursor. -/
theorem red4 {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) (l : Level) (M' m' X' H' : Expr Nat) :
    CE (n := n) Γ (.app (.app (.app (.app (recT l) M') m') X') H') (.app m' X') := by
  refine ce_trans hΓ (ce_appL _ (ce_appL _ (ce_appL _ (ce_beta hΓ)))) ?_
  refine ce_trans hΓ (ce_appL _ (ce_appL _ (ce_beta hΓ))) ?_
  refine ce_trans hΓ (ce_appL _ (ce_beta hΓ)) ?_
  refine ce_trans hΓ (ce_beta hΓ) ?_
  apply ce_of_eq
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

end Red4

section IotaCore

variable {n : Nat}

/-- an application whose head has a known Π type reads the argument's type off the head. -/
theorem appInvKnown {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) {f a D C T' : Expr Nat}
    (hf : HasTyT gEnv n Γ f (.pi D C)) (h : HasTyT gEnv n Γ (.app f a) T') :
    Nonempty (HasTyT gEnv n Γ a D) := by
  obtain ⟨A, B, hf', ha', _⟩ := hasTyTInv_app h rfl
  obtain ⟨c⟩ := DT012T_type_uniqueness_of_sortRow_piRow gEnvWfT (gRows n).sortRow
    (gRows n).piRow hΓ hf' hf
  obtain ⟨⟨cA⟩, _⟩ := (gRows n).piRow hΓ c
  exact ⟨hasTyT_of_tyConvT ha' cA⟩

/-- **The ι cell's agreement, read in `gEnv`.** If the translated redex
    `recT l M' m' X' (mk₀ x')` is typed, then `x' ≡ X' : Sort 0`. The index `X'` is read off the
    redex's own typing by four Π-inversions against the known type of `recT l`; `famAppRow` of `RI₀`
    (a landed row) then identifies the field `x'` with it. -/
theorem iota_agree {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT gEnv n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) T') :
    Nonempty (ConvT gEnv n Γ x' X' (.sort .zero)) := by
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := appInvKnown hΓ (recT_typed Γ l) he1
  have own1 := HasTyT.app Γ (recT l) M' _ _ (recT_typed Γ l) hM'
  obtain ⟨hm'⟩ := appInvKnown hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := appInvKnown hΓ own2 he3
  have own3 := HasTyT.app Γ _ X' _ _ own2 hX'
  obtain ⟨hH'⟩ := appInvKnown hΓ own3 hlhs
  have hH'' : HasTyT gEnv n Γ (.app (.const 2 lsC) x') (.app (.const 0 []) X') := hH'
  obtain ⟨⟨-, -, hargs, hconv⟩⟩ := hasTyT_spineInv_rows gEnvWfT (gRows n).piRow hΓ
    (r := 2) (ls := lsC) (m := gMk) rfl (doms := [.sort .zero]) (U := ri0X) rfl [x'] rfl hH''
  have hx' : HasTyT gEnv n Γ x' (.sort .zero) := hargs 0 x' (.sort .zero) rfl rfl
  have hIP : instPrefix [x'] ri0X = .app (.const 0 []) x' := by
    simp [instPrefix, instantiate, lift_zero_idx]
  rw [hIP] at hconv
  obtain ⟨-, -, hc⟩ := (gRows n).famAppRow hΓ (r := 0) (m := riFam) (ls := []) (ls' := [])
    (xs := [x']) (xs' := [X']) (w := .zero) rfl rfl (gRIty hx') hconv
  have hc' : ConvArgsT gEnv n Γ (.pi (.sort .zero) (.sort .zero)) [x'] [X'] := hc
  cases hc' with
  | cons A B f f' fs fs' h hs => exact h

end IotaCore

section IotaConv

variable {n : Nat}

/-- **The translated ι-cell.** `recT l M' m' X' (mk₀ x') ≡ m' x'` at every type of the redex. -/
theorem iota_conv {Γ : LCtx} (hΓ : CtxWfT gEnv n Γ) (l : Level) (lsC : List Level)
    (M' m' X' x' T' : Expr Nat)
    (hlhs : HasTyT gEnv n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) T') :
    Nonempty (ConvT gEnv n Γ
      (.app (.app (.app (.app (recT l) M') m') X') (.app (.const 2 lsC) x')) (.app m' x') T') := by
  obtain ⟨cxX⟩ := iota_agree hΓ l lsC M' m' X' x' T' hlhs
  obtain ⟨c1⟩ := red4 hΓ l M' m' X' (.app (.const 2 lsC) x') T' hlhs
  obtain ⟨_, _, he3, hH, _⟩ := hasTyTInv_app hlhs rfl
  obtain ⟨_, _, he2, hX, _⟩ := hasTyTInv_app he3 rfl
  obtain ⟨_, _, he1, hm, _⟩ := hasTyTInv_app he2 rfl
  obtain ⟨hM'⟩ := appInvKnown hΓ (recT_typed Γ l) he1
  have own1 := HasTyT.app Γ (recT l) M' _ _ (recT_typed Γ l) hM'
  obtain ⟨hm'⟩ := appInvKnown hΓ own1 he2
  have own2 := HasTyT.app Γ _ m' _ _ own1 hm'
  obtain ⟨hX'⟩ := appInvKnown hΓ own2 he3
  have hm'' : HasTyT gEnv n Γ m' (.pi (.sort .zero) _) := hm'
  have c2 := ConvT.app Γ m' m' X' x' _ _ (ConvT.refl Γ m' _ hm'') (ConvT.symm _ _ _ _ cxX)
  have hmX := HasTyT.app Γ m' X' _ _ hm'' hX'
  obtain ⟨cT⟩ := DT012T_type_uniqueness_of_sortRow_piRow gEnvWfT (gRows n).sortRow
    (gRows n).piRow hΓ hmX (NativeValleys.convEnds gEnvWfT hΓ c1).2.1
  exact ⟨.trans _ _ _ _ _ c1 (convRetype c2 cT)⟩

end IotaConv

/-! ## §7 the ι witnesses of `riEnv` -/

section IotaInv

theorem riEnv_members (r : Nat) :
    riEnv.members r =
      if r = 2 then some riRec else if r = 1 then some riCtor
      else if r = 0 then some riFam else none := rfl

theorem riEnv_class {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m) :
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

theorem riEnv_recursor {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m)
    (hk : m.mclass = .recursorM) : r = 2 ∧ m = riRec := by
  rcases riEnv_class h with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem riEnv_ctor {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m)
    (hk : m.mclass = .constructorM) : r = 1 ∧ m = riCtor := by
  rcases riEnv_class h with ⟨rfl, rfl⟩ | h' | ⟨rfl, rfl⟩
  · exact absurd hk (by decide)
  · exact h'
  · exact absurd hk (by decide)

theorem riEnv_family {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m)
    (hk : m.mclass = .inductiveM) : r = 0 ∧ m = riFam := by
  rcases riEnv_class h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h'
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact h'

/-- Every `ι` witness of `riEnv` has the shape of the fixture's: the recursor at `[l]`, three
    pre-major arguments, the constructor applied to one field, and the minor applied to that
    field. -/
theorem riIota_inv (w : IotaWitness riEnv) :
    ∃ (ls lsC : List Level) (M m X x : Expr Nat), ls.length = 1 ∧
      iotaLhsOf w = foldApps (.const 2 ls) [M, m, X, foldApps (.const 1 lsC) [x]] ∧
      iotaRhsOf w = .app m x := by
  obtain ⟨recRef, ctorRef, ls, lsC, recMember, ctorMember, hrec, hctor, hrecK, hctorK,
    preMajor, fields, ctorParams, kinds, minor, hlen, familyRef, famMember, hfam, hfamK,
    nparams, nindices, nMinors, ctorIdx, hctorParams, hnpar, hnidx, hnmin, hidx, hctorIdx,
    hrecIdx, hpre, hminor, ctorDoms, ctorResult, hpeel, hfamApp, hkinds, recDoms, recBody,
    hpeelRec, hrecBody, hmajorTy, hrecClosed, hctorClosed, hlsLen, ctorAfterParams,
    hctorAfter, hctorTel, hfamTel, hresTel⟩ := w
  obtain ⟨rfl, rfl⟩ := riEnv_recursor hrec hrecK
  obtain ⟨rfl, rfl⟩ := riEnv_ctor hctor hctorK
  obtain ⟨rfl, rfl⟩ := riEnv_family hfam hfamK
  have hnM : nMinors = 1 := by omega
  have hci : ctorIdx = 0 := by omega
  have p1 : piCount riCtor.mtype = 1 := rfl
  have p2 : piCount riFam.mtype = 1 := rfl
  have p3 : piCount riRec.mtype = 4 := rfl
  rw [p1] at hnpar
  rw [p2] at hnidx
  rw [p3] at hnmin
  subst hnM hci
  have hP : peelPis 4 riRec.mtype = some ([riMotTy, riMinTy, .sort .zero,
      .app (.const 0 []) (.bvar 0)], .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := rfl
  have hnp : nparams = 0 := by
    refine Decidable.byContradiction (fun hne => ?_)
    have h1 : nparams = 1 := by omega
    have h2 : nindices = 0 := by omega
    subst h1 h2
    have hPR : peelPis (1 + 1 + 1 + 0 + 1) riRec.mtype = some ([riMotTy, riMinTy, .sort .zero,
        .app (.const 0 []) (.bvar 0)], .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) := hP
    rw [hPR] at hpeelRec
    obtain ⟨-, hb⟩ := Prod.mk.inj (Option.some.inj hpeelRec)
    rw [← hb] at hrecBody
    simp [foldApps] at hrecBody
  subst hnp
  have hnI : nindices = 1 := by omega
  subst hnI
  have hfl : fields.length = 1 := by omega
  obtain ⟨x, rfl⟩ := List.length_eq_one.mp hfl
  obtain ⟨M, m, X, rfl⟩ : ∃ M m X, preMajor = [M, m, X] := by
    match preMajor, hpre with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
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
  have hmin : minor = m := by
    have := hminor
    simp at this
    exact this.symm
  subst hmin
  have hca : ctorAfterParams = instantiateLevels ls riCtor.mtype := by
    have := hctorAfter
    simp [applyTel] at this
    exact this.symm
  refine ⟨ls, lsC, M, minor, X, x, hlsLen, ?_, ?_⟩
  · simp [iotaLhsOf, recCall, ctorMajor, ctorSpine, foldApps]
  · subst hca
    simp [iotaRhsOf, rhsArgs, foldApps, riCtor, instantiateLevels]

end IotaInv

/-! ## §8 the translation of derivations, `riEnv → gEnv` -/

section Translate

theorem lookupType_trCtx (Γ : LCtx) (i : Nat) :
    lookupType (trCtx Γ) i = (lookupType Γ i).map tr := by
  unfold lookupType trCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp [trDecl, tr_lift]
      | letBinding a v => simp [trDecl, tr_lift]

theorem lookupValue_trCtx (Γ : LCtx) (i : Nat) :
    lookupValue (trCtx Γ) i = (lookupValue Γ i).map tr := by
  unfold lookupValue trCtx
  rw [List.get?_map]
  cases h : Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => rfl
      | letBinding a v => simp [trDecl, tr_lift]

theorem riEnv_noBody {r : Nat} {m : CheckedMember} (h : riEnv.members r = some m) :
    m.body = none := by
  rcases riEnv_class h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

end Translate

theorem litExp_eq {t : Nat} {exp : Expr Nat} (h : LiteralExpansion t exp) : exp = natExpand t := by
  cases h; rfl

/-- the `ι` redex of `riEnv`, as an equation, without cases on the proof object. -/
theorem riIota_inv' {lhs rhs : Expr Nat} (d : DerivedIota riEnv lhs rhs) :
    ∃ (ls lsC : List Level) (M m X x : Expr Nat), ls.length = 1 ∧
      lhs = foldApps (.const 2 ls) [M, m, X, foldApps (.const 1 lsC) [x]] ∧
      rhs = .app m x := by
  cases d with
  | of w => exact riIota_inv w

section Translate2

variable {n : Nat}

mutual
theorem trTy : {Γ : LCtx} → {e A : Expr Nat} → HasTyT riEnv n Γ e A →
    CtxWfT gEnv n (trCtx Γ) → Nonempty (HasTyT gEnv n (trCtx Γ) (tr e) (tr A))
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ =>
      ⟨.bvar _ i (tr A) (by rw [lookupType_trCtx, h]; rfl)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      rcases riEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        exact ⟨recT_typed (trCtx Γ) l⟩
      · exact ⟨.const _ 2 ls gMk rfl hlen hwf⟩
      · exact ⟨.const _ 0 ls riFam rfl hlen hwf⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hB'⟩ := trTy hB (.assumption _ (tr A) u hΓ' hA')
      exact ⟨.pi _ (tr A) u (tr B) v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ' => by
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hb'⟩ := trTy hbody (.assumption _ (tr A) u hΓ' hA')
      exact ⟨.lam _ (tr A) u (tr body) (tr B) hA' hb'⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ' => by
      obtain ⟨hf'⟩ := trTy hf hΓ'
      obtain ⟨ha'⟩ := trTy ha hΓ'
      rw [tr_instantiate0]
      exact ⟨.app _ (tr f) (tr a) (tr A) (tr B) hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hv'⟩ := trTy hv hΓ'
      obtain ⟨hb'⟩ := trTy hb (.letBinding _ (tr A) u (tr value) hΓ' hA' hv')
      rw [tr_instantiate0]
      exact ⟨.letE _ (tr A) u (tr value) (tr B) (tr body) hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ' => by
      obtain ⟨h⟩ := trTy hexp hΓ'
      rw [tr_natExpand] at h
      exact ⟨h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ' => by
      obtain ⟨h'⟩ := trTy h hΓ'
      obtain ⟨hc'⟩ := trConv hc hΓ'
      exact ⟨.conv _ (tr e) (tr A) (tr B) u h' hc'⟩

theorem trConv : {Γ : LCtx} → {a b A : Expr Nat} → ConvT riEnv n Γ a b A →
    CtxWfT gEnv n (trCtx Γ) → Nonempty (ConvT gEnv n (trCtx Γ) (tr a) (tr b) (tr A))
  | _, _, _, _, .refl Γ a A h, hΓ' => by
      obtain ⟨h'⟩ := trTy h hΓ'
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ' => by
      obtain ⟨h'⟩ := trConv h hΓ'
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConv h1 hΓ'
      obtain ⟨h2'⟩ := trConv h2 hΓ'
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ' => by
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hb'⟩ := trTy hbody (.assumption _ (tr A) u hΓ' hA')
      obtain ⟨ha'⟩ := trTy harg hΓ'
      rw [tr_instantiate0, tr_instantiate0]
      exact ⟨.beta _ (tr A) (tr body) (tr arg) (tr B) u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hv'⟩ := trTy hv hΓ'
      obtain ⟨hb'⟩ := trTy hb (.letBinding _ (tr A) u (tr value) hΓ' hA' hv')
      rw [tr_instantiate0, tr_instantiate0]
      exact ⟨.zeta _ (tr A) (tr value) (tr body) (tr B) u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ' => by
      obtain ⟨hv'⟩ := trTy hv hΓ'
      exact ⟨.zetaLocal _ i (tr A) (tr v) (by rw [lookupValue_trCtx, hval]; rfl)
        (by rw [lookupType_trCtx, hty]; rfl) hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody _ _ _ _, _ =>
      absurd hbody (by rw [riEnv_noBody hres]; exact Option.noConfusion)
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, hΓ' => by
      obtain ⟨hl'⟩ := trTy hl hΓ'
      obtain ⟨ls, lsC, M, m, X, x, hlen, hL, hR⟩ := riIota_inv' h
      obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
      rw [hL] at hl'
      rw [hL, hR]
      have e1 : tr (foldApps (.const 2 [l]) [M, m, X, foldApps (.const 1 lsC) [x]]) =
          .app (.app (.app (.app (recT l) (tr M)) (tr m)) (tr X)) (.app (.const 2 lsC) (tr x)) :=
        rfl
      rw [e1] at hl' ⊢
      exact iota_conv hΓ' l lsC (tr M) (tr m) (tr X) (tr x) (tr T) hl'
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ' => by
      obtain ⟨h'⟩ := trTy hexp hΓ'
      rw [litExp_eq h, tr_natExpand] at *
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .app Γ f g a b A B h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := trConv h1 hΓ'
      obtain ⟨h2'⟩ := trConv h2 hΓ'
      rw [tr_instantiate0]
      exact ⟨.app _ (tr f) (tr g) (tr a) (tr b) (tr A) (tr B) h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ' => by
      obtain ⟨hA'⟩ := trConv hA hΓ'
      obtain ⟨hb'⟩ := trConv hb (.assumption _ (tr A) u hΓ'
        (NativeValleys.convEnds gEnvWfT hΓ' hA').1)
      exact ⟨.lam _ (tr A) (tr A') (tr b) (tr b') (tr B) u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := trConv hA hΓ'
      obtain ⟨hB'⟩ := trConv hB (.assumption _ (tr A) u hΓ'
        (NativeValleys.convEnds gEnvWfT hΓ' hA').1)
      exact ⟨.pi _ (tr A) (tr A') (tr B) (tr B') u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := trConv hA hΓ'
      obtain ⟨hv'⟩ := trConv hv hΓ'
      obtain ⟨hb'⟩ := trConv hb (.letBinding _ (tr A) u (tr v) hΓ'
        (NativeValleys.convEnds gEnvWfT hΓ' hA').1 (NativeValleys.convEnds gEnvWfT hΓ' hv').1)
      rw [tr_instantiate0]
      exact ⟨.letE _ (tr A) (tr A') (tr v) (tr v') (tr b) (tr b') (tr B) u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ => by
      rcases riEnv_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨l, rfl⟩ := List.length_eq_one.mp hlen
        rcases ls' with _ | ⟨l', _ | ⟨l'', t⟩⟩
        · exact h.elim
        · exact ⟨recT_conv (trCtx Γ) l l' h.1⟩
        · exact h.2.elim
      · exact ⟨.consts _ 2 ls ls' gMk rfl hlen hwf hwf' h⟩
      · exact ⟨.consts _ 0 ls ls' riFam rfl hlen hwf hwf' h⟩
  | _, _, _, _, .eta Γ f A B h, hΓ' => by
      obtain ⟨h'⟩ := trTy h hΓ'
      show Nonempty (ConvT gEnv n (trCtx Γ) (.lam (tr A) (.app (tr (lift 0 1 f)) (.bvar 0))) (tr f)
        (.pi (tr A) (tr B)))
      rw [tr_lift]
      exact ⟨.eta _ (tr f) (tr A) (tr B) h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ' => by
      obtain ⟨hP'⟩ := trTy hP hΓ'
      obtain ⟨hp'⟩ := trTy hp hΓ'
      obtain ⟨hq'⟩ := trTy hq hΓ'
      exact ⟨.irr _ (tr P) (tr p) (tr q) hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ' => by
      obtain ⟨h'⟩ := trConv h hΓ'
      obtain ⟨hA'⟩ := trConv hA hΓ'
      exact ⟨.tyConv _ (tr a) (tr b) (tr A) (tr A') u h' hA'⟩
end

theorem trTyConv {Γ : LCtx} {a b : Expr Nat} (h : TyConvT riEnv n Γ a b)
    (hΓ' : CtxWfT gEnv n (trCtx Γ)) : Nonempty (TyConvT gEnv n (trCtx Γ) (tr a) (tr b)) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := trConv h hΓ'; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem trCtxWf {Γ : LCtx} (h : CtxWfT riEnv n Γ) : Nonempty (CtxWfT gEnv n (trCtx Γ)) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := trTy hA hΓ'
      exact ⟨.assumption _ (tr A) u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := trTy hA hΓ'
      obtain ⟨hv'⟩ := trTy hv hΓ'
      exact ⟨.letBinding _ (tr A) u (tr v) hΓ' hA' hv'⟩

end Translate2

/-! ## §9 consequences at `riEnv` -/

section Consequences

variable {n : Nat}

/-- **Row 1 at the class-(c) fixture `RI`, unconditionally.** In `riEnv`, at every well-formed
    context (inconsistent ones included) and at every type, `Sort u ≡ Sort v` forces `u =ₙ v`.
    The translation sends the derivation into `gEnv`, where the landed sort row applies. -/
theorem riSortRow {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {u v : Level} {T : Expr Nat}
    (h : ConvT riEnv n Γ (.sort u) (.sort v) T) : eqN u v := by
  obtain ⟨hΓ'⟩ := trCtxWf hΓ
  obtain ⟨c⟩ := trConv h hΓ'
  exact sortConvCharT_scopeCheck gEnvWfT gEnvWfT_scopeCheck hΓ' c

/-- the sort row in the ledger's form: a type-conversion chain between two sorts. -/
theorem riSortRow_chain {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {u v : Level}
    (h : TyConvT riEnv n Γ (.sort u) (.sort v)) : eqN u v := by
  obtain ⟨hΓ'⟩ := trCtxWf hΓ
  obtain ⟨c⟩ := trTyConv h hΓ'
  exact (gRows n).sortRow hΓ' c

/-- **The Π row's shadow at `RI`.** A conversion between two Π types in `riEnv` gives, in the
    twin `gEnv`, type-conversion chains between the translated domains and between the
    translated codomains. -/
theorem riPiShadow {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {A B A' B' : Expr Nat}
    (h : TyConvT riEnv n Γ (.pi A B) (.pi A' B')) :
    Nonempty (TyConvT gEnv n (trCtx Γ) (tr A) (tr A')) ∧
      Nonempty (TyConvT gEnv n (.assumption (tr A) :: trCtx Γ) (tr B) (tr B')) := by
  obtain ⟨hΓ'⟩ := trCtxWf hΓ
  obtain ⟨c⟩ := trTyConv h hΓ'
  exact (gRows n).piRow hΓ' c

end Consequences

end Rcic.Syn.ClassC

#print axioms Rcic.Syn.ClassC.gEnvWfT
#print axioms Rcic.Syn.ClassC.gEnvWfT_scopeCheck
#print axioms Rcic.Syn.ClassC.gRows
#print axioms Rcic.Syn.ClassC.iota_agree
#print axioms Rcic.Syn.ClassC.iota_conv
#print axioms Rcic.Syn.ClassC.riIota_inv
#print axioms Rcic.Syn.ClassC.trConv
#print axioms Rcic.Syn.ClassC.riSortRow
#print axioms Rcic.Syn.ClassC.riSortRow_chain
#print axioms Rcic.Syn.ClassC.riPiShadow
