import rcic.RcicAccPiTable

/-!
# accpi (H) — the simulation at the Prop Acc fixture, measured by the landed `TyP.eps`

Three cells, each a pair of HasTyT-typed endpoints at an admitted scope of `accPEnvWfT`, erased by
the landed `TyP.eps` at the canonical disposition (`ScopedCtx.can id`):

1. **the Lean ι cell** at a constructor major, free motive and minor:
   `rec M F x (intro x g)  ≡ι  F x g (λ y r. rec M F y (g y r))`.
   Erased: `rec M F x` and `F x (λ y. rec M F y)`.
   Under `tableOfK accPEnvWfT` (`= []`) the two are NOT `E`-convertible (`accIota_not_es_tableOfK`):
   the erased redex is stuck. Under (H) they are (`accIota_es_star`): one ★-unfold, three β.
2. **the irr+ι cell** at a NON-canonical major `h : AccP x`, the Abel–Coquand move:
   `rec M F x h ≡irr+app rec M F x (intro x g) ≡ι F x g (λ y r. rec M F y (g y r))` for any proof
   `g : Π y, R y x → AccP y` in scope. `irr`'s endpoints both erase to `★`; the composite's
   endpoints erase exactly as in cell 1 (`accIrr_eps`), so the same verdicts hold.
3. **the Abel–Coquand loop** at `rr : Π z, R z z`, large motive `M := λ x' _. Sort 0` (`rec.{1}`),
   minor `F := λ x' g ih. ih x' (rr x')`: `X := rec M F x h` unfolds by irr+ι+β back to itself.
   Every typed step has an erased image under (H) (`accLoop_es_star`) and `X̂ →⁺ X̂`
   (`accLoop_cycle`). At this minor the ι image is joined by β alone, so the loop by itself does
   not separate (H) from `tableOfK` (`accLoop_iota_es_tableOfK`); cell 1 does.

`ConvT` itself has no Acc ι (`accP_no_derivedIota`); the cells are typed pairs of the frec
extension's ι, not `ConvT` nodes. `closure_claim = 0`.
-/

namespace Rcic.Syn

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Declarative.Ann

/-! ## §1 the ι cell scope `[g, x, F, M]` -/

/-- `[g : Π y, R y x → AccP y, x : S0, F : minor, M : motive]`, innermost first. -/
def accIotaCtx : LCtx :=
  [.assumption paFieldDom, .assumption (.sort .zero), .assumption paMinorTy,
    .assumption paMotTy]

def accTy (Γ : LCtx) (e T : Expr Nat) (h : (tyAtC accPEnvT 1 32 Γ e T).isSome = true) :
    HasTyT accPEnvT 1 Γ e T :=
  (tyAtC accPEnvT 1 32 Γ e T).get h

/-- the minor's sort. -/
abbrev accMinorU : Level :=
  .imax (.succ .zero) (.imax (.imax (.succ .zero) (.imax .zero .zero))
    (.imax (.imax (.succ .zero) (.imax .zero (.param 0))) (.param 0)))

def accIotaCtxWf : CtxWfT accPEnvT 1 accIotaCtx :=
  .assumption _ paFieldDom _
    (.assumption _ (.sort .zero) _
      (.assumption _ paMinorTy _
        (.assumption [] paMotTy _ .nil
          (accTy [] paMotTy (.sort (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))) rfl))
        (accTy _ paMinorTy (.sort accMinorU) rfl))
      (HasTyT.sort _ .zero))
    (accTy _ paFieldDom (.sort (.imax (.succ .zero) (.imax .zero .zero))) rfl)


/-- the admitted scope of the ι cell. -/
def accIotaScope : ScopedCtx accPEnvT accPEnvT 1 accIotaCtx :=
  ⟨accPEnvWfT, envExt_refl _, accIotaCtxWf⟩

/-- `intro x g`. -/
def accIntroXG : Expr Nat := .app (.app (.const 11 []) (.bvar 1)) (.bvar 0)

/-- the ι redex `rec.{u} M F x (intro x g)`. -/
def accIotaLhs : Expr Nat :=
  foldApps (.const 12 [.param 0]) [.bvar 3, .bvar 2, .bvar 1, accIntroXG]

/-- its type `M x (intro x g)`. -/
def accIotaTyE : Expr Nat := .app (.app (.bvar 3) (.bvar 1)) accIntroXG

/-- the ι contractum's recursive hypothesis `λ (y:S0) (r : R y x). rec M F y (g y r)`. -/
def accIotaIH : Expr Nat :=
  .lam (.sort .zero)
    (.lam (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
      (foldApps (.const 12 [.param 0])
        [.bvar 5, .bvar 4, .bvar 1, .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)]))

/-- the ι contractum `F x g (λ y r. rec M F y (g y r))` — the Lean kernel's Acc ι reduct. -/
def accIotaRhs : Expr Nat := .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) accIotaIH

def accIotaLhsTy : HasTyT accPEnvT 1 accIotaCtx accIotaLhs accIotaTyE := accTy _ _ _ rfl
def accIotaRhsTy : HasTyT accPEnvT 1 accIotaCtx accIotaRhs accIotaTyE := accTy _ _ _ rfl

noncomputable def accIotaLhsP : TyP accPEnvT 1 accIotaCtx accIotaLhs accIotaTyE :=
  enrichHasTyT_of_envWfT accPEnvWfT accIotaCtxWf accIotaLhsTy
noncomputable def accIotaRhsP : TyP accPEnvT 1 accIotaCtx accIotaRhs accIotaTyE :=
  enrichHasTyT_of_envWfT accPEnvWfT accIotaCtxWf accIotaRhsTy

/-- the erased ι redex: `rec M F x` (the `★` major dropped; `M F x` at `2 1 0`, `g` dropped). -/
def accLhsE (ls : List Level) : ETm := ETm.appN (.const 12 ls) [.bvar 2, .bvar 1, .bvar 0]

/-- the erased ι contractum: `F x (λ y. rec M F y)` (`g` and the guard `r` dropped). -/
def accRhsE (ls : List Level) : ETm :=
  .app (.app (.bvar 1) (.bvar 0)) (.lam (accStarCall ls))

/-- PIN: the canonical disposition of `[g, x, F, M]` drops the proof `g`, keeps the rest. -/
theorem accIota_can : accIotaScope.can id = [.drop, .keep, .keep, .keep] := by
  with_unfolding_all rfl

/-- PIN: the landed erasure of the ι redex is `rec M F x`. -/
theorem accIota_eps_lhs : accIotaLhsP.eps id (accIotaScope.can id) = accLhsE [.param 0] := by
  with_unfolding_all rfl

/-- PIN: the landed erasure of the ι contractum is `F x (λ y. rec M F y)`. -/
theorem accIota_eps_rhs : accIotaRhsP.eps id (accIotaScope.can id) = accRhsE [.param 0] := by
  with_unfolding_all rfl

/-- the (H) chain: one ★-unfold at the head, then three β. -/
theorem accStar_chain (ls : List Level) : RStar (RStep accStarTable) (accLhsE ls) (accRhsE ls) :=
  .step (rStep_appN_head (.cr (.bare accStarRule_mem rfl ls [] rfl)) [.bvar 2, .bvar 1, .bvar 0])
    (.step (rStep_appN_head (.beta _ (.bvar 2)) [.bvar 1, .bvar 0])
      (.step (rStep_appN_head (.beta _ (.bvar 1)) [.bvar 0])
        (.step (.beta _ (.bvar 0)) (.refl _))))

/-- **(H) closes the Lean ι cell**: its two endpoints, erased by the landed `TyP.eps`, are
    `E`-convertible under the ★-unfold table. -/
theorem accIota_es_star :
    ConvMod (EStep accStarTable) LvlEq (accIotaLhsP.eps id (accIotaScope.can id))
      (accIotaRhsP.eps id (accIotaScope.can id)) := by
  rw [accIota_eps_lhs, accIota_eps_rhs]
  exact convMod_of_rstar_estep (accStar_chain _)

/-! ## §2 why `tableOfK` cannot: a bvar spine head is invariant, a `λ`-free term is normal -/

/-- every `E`-step keeps a `bvar` spine head (no rule, β or η redex is `bvar`-headed). -/
theorem rStep_spineHead_bvar {tbl : List CRule} {t z : ETm} (h : RStep tbl t z) {i : Nat}
    (ht : ETm.spineHead t = .bvar i) : ETm.spineHead z = .bvar i := by
  induction h with
  | beta M N => cases ht
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      rw [ETm.spineHead_appN] at ht
      cases ht
  | appL a _ ih => exact ih ht
  | appR f _ => exact ht
  | lam _ => cases ht
  | piL _ _ => cases ht
  | piR _ _ => cases ht

theorem etaStep_spineHead_bvar {t z : ETm} (h : EtaStep t z) {i : Nat}
    (ht : ETm.spineHead t = .bvar i) : ETm.spineHead z = .bvar i := by
  induction h with
  | eta F => cases ht
  | appL a _ ih => exact ih ht
  | appR f _ => exact ht
  | lam _ => cases ht
  | piL _ _ => cases ht
  | piR _ _ => cases ht

theorem rstar_spineHead_bvar {tbl : List CRule} {t z : ETm} (h : RStar (EStep tbl) t z) {i : Nat}
    (ht : ETm.spineHead t = .bvar i) : ETm.spineHead z = .bvar i := by
  induction h with
  | refl => exact ht
  | step h1 _ ih =>
      exact ih (h1.elim (fun h => rStep_spineHead_bvar h ht) (fun h => etaStep_spineHead_bvar h ht))

theorem lvlEq_spineHead_bvar {a b : ETm} (h : LvlEq a b) {i : Nat}
    (ha : ETm.spineHead a = .bvar i) : ETm.spineHead b = .bvar i := by
  induction h with
  | bvar j => exact ha
  | star => cases ha
  | sort _ => cases ha
  | const _ _ => cases ha
  | app _ _ ih _ => exact ih ha
  | lam _ _ => cases ha
  | pi _ _ _ _ => cases ha

/-- `λ`-free (and `Π`-free) terms. -/
def ETm.lamFree : ETm → Bool
  | .app f a => ETm.lamFree f && ETm.lamFree a
  | .lam _ => false
  | .pi _ _ => false
  | _ => true

/-- at the empty table a `λ`-free term is `E`-normal: no rule, no β, no η. -/
theorem eStep_nil_lamFree {t z : ETm} (ht : ETm.lamFree t = true) (h : EStep [] t z) : False := by
  rcases h with h | h
  · induction h with
    | beta M N => simp [ETm.lamFree] at ht
    | cr hc =>
        cases hc with
        | bare hρ => cases hρ
        | ctor hρ => cases hρ
    | appL a _ ih =>
        simp only [ETm.lamFree, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.lamFree, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.lamFree] at ht
    | piL _ _ => simp [ETm.lamFree] at ht
    | piR _ _ => simp [ETm.lamFree] at ht
  · induction h with
    | eta F => simp [ETm.lamFree] at ht
    | appL a _ ih =>
        simp only [ETm.lamFree, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.lamFree, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.lamFree] at ht
    | piL _ _ => simp [ETm.lamFree] at ht
    | piR _ _ => simp [ETm.lamFree] at ht

/-- the erased redex and contractum are not convertible at the empty table: the redex is
    normal and `const`-headed, every reduct of the contractum is `bvar 1`-headed. -/
theorem accIota_not_convE_nil (ls : List Level) :
    ¬ ConvMod (EStep []) LvlEq (accLhsE ls) (accRhsE ls) := by
  intro h
  have hW : TableWF [] := by
    rw [← tableOfK_accP]; exact tableWF_tableOfK accPEnvWfT
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  obtain rfl := rstar_of_normal (fun z hz => eStep_nil_lamFree (t := accLhsE ls) rfl hz) hc
  have hdh : ETm.spineHead d = .bvar 1 := rstar_spineHead_bvar hd rfl
  have := lvlEq_spineHead_bvar (lvlEq_equivalence.symm hq) hdh
  cases this

/-- **`tableOfK` does not close the Lean ι cell**: at the Prop Acc env the K table is empty and
    the erased ι endpoints are not `E`-convertible. This is the brief's doubt, measured: the
    erased `Acc.rec … ★` is stuck. -/
theorem accIota_not_es_tableOfK :
    ¬ ConvMod (EStep (tableOfK accPEnvWfT)) LvlEq (accIotaLhsP.eps id (accIotaScope.can id))
      (accIotaRhsP.eps id (accIotaScope.can id)) := by
  rw [accIota_eps_lhs, accIota_eps_rhs, tableOfK_accP]
  exact accIota_not_convE_nil _

/-! ## §3 the irr+ι cell at a non-canonical major: `[g, h, x, F, M]`

`h : AccP x` is a variable major. `irr` identifies it with `intro x g` for ANY proof
`g : Π y, R y x → AccP y` in scope (the Abel–Coquand move: the major is replaced by a
constructor whose field is an arbitrary proof), then ι fires. The chain is
`rec M F x h ≡irr+app rec M F x (intro x g) ≡ι F x g (λ y r. rec M F y (g y r))`. -/

/-- `Π (y:S0), R y x → AccP y` with `x` at index `1`. -/
def accGTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
    (.app (.const 10 []) (.bvar 1)))

def accIrrCtx : LCtx :=
  [.assumption accGTy, .assumption (.app (.const 10 []) (.bvar 0)), .assumption (.sort .zero),
    .assumption paMinorTy, .assumption paMotTy]

def accIrrCtxWf : CtxWfT accPEnvT 1 accIrrCtx :=
  .assumption _ accGTy _
    (.assumption _ (.app (.const 10 []) (.bvar 0)) _
      (.assumption _ (.sort .zero) _
        (.assumption _ paMinorTy _
          (.assumption [] paMotTy _ .nil
            (accTy [] paMotTy (.sort (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))) rfl))
          (accTy _ paMinorTy (.sort accMinorU) rfl))
        (HasTyT.sort _ .zero))
      (accTy _ _ (.sort .zero) rfl))
    (accTy _ accGTy (.sort (.imax (.succ .zero) (.imax .zero .zero))) rfl)

def accIrrScope : ScopedCtx accPEnvT accPEnvT 1 accIrrCtx :=
  ⟨accPEnvWfT, envExt_refl _, accIrrCtxWf⟩

/-- the variable major `h` and the constructor it is `irr`-identified with, `intro x g`. -/
def accIrrIntro : Expr Nat := .app (.app (.const 11 []) (.bvar 2)) (.bvar 0)
/-- `AccP x`. -/
def accIrrP : Expr Nat := .app (.const 10 []) (.bvar 2)

/-- `rec M F x h : M x h`. -/
def accIrrLhs : Expr Nat := foldApps (.const 12 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 1]
/-- `rec M F x (intro x g) : M x (intro x g)` — the redex after `irr` + `app` congruence. -/
def accIrrMid : Expr Nat := foldApps (.const 12 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, accIrrIntro]
/-- the ι contractum `F x g (λ y r. rec M F y (g y r))`. -/
def accIrrRhs : Expr Nat :=
  .app (.app (.app (.bvar 3) (.bvar 2)) (.bvar 0))
    (.lam (.sort .zero)
      (.lam (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
        (foldApps (.const 12 [.param 0])
          [.bvar 6, .bvar 5, .bvar 1, .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)])))

def accIrrTyL : Expr Nat := .app (.app (.bvar 4) (.bvar 2)) (.bvar 1)
def accIrrTyR : Expr Nat := .app (.app (.bvar 4) (.bvar 2)) accIrrIntro

def accIrrHTy : HasTyT accPEnvT 1 accIrrCtx (.bvar 1) accIrrP := HasTyT.bvar _ 1 _ rfl
def accIrrIntroTy : HasTyT accPEnvT 1 accIrrCtx accIrrIntro accIrrP := accTy _ _ _ rfl
def accIrrLhsTy : HasTyT accPEnvT 1 accIrrCtx accIrrLhs accIrrTyL := accTy _ _ _ rfl
def accIrrMidTy : HasTyT accPEnvT 1 accIrrCtx accIrrMid accIrrTyR := accTy _ _ _ rfl
def accIrrRhsTy : HasTyT accPEnvT 1 accIrrCtx accIrrRhs accIrrTyR := accTy _ _ _ rfl

/-- the `irr` leaf itself is a `ConvT` node at the fixture: `h ≡ intro x g : AccP x`. -/
def accIrrLeaf : ConvT accPEnvT 1 accIrrCtx (.bvar 1) accIrrIntro accIrrP :=
  .irr _ _ _ _ (accTy _ _ _ rfl) accIrrHTy accIrrIntroTy

noncomputable def accIrrHP := enrichHasTyT_of_envWfT accPEnvWfT accIrrCtxWf accIrrHTy
noncomputable def accIrrIntroP := enrichHasTyT_of_envWfT accPEnvWfT accIrrCtxWf accIrrIntroTy
noncomputable def accIrrLhsP := enrichHasTyT_of_envWfT accPEnvWfT accIrrCtxWf accIrrLhsTy
noncomputable def accIrrMidP := enrichHasTyT_of_envWfT accPEnvWfT accIrrCtxWf accIrrMidTy
noncomputable def accIrrRhsP := enrichHasTyT_of_envWfT accPEnvWfT accIrrCtxWf accIrrRhsTy

theorem accIrr_can : accIrrScope.can id = [.drop, .drop, .keep, .keep, .keep] := by
  with_unfolding_all rfl

/-- PIN: both `irr` endpoints erase to `★` — the leaf has an erased image (`≈`-refl). -/
theorem accIrr_eps_irr : accIrrHP.eps id (accIrrScope.can id) = .star ∧
    accIrrIntroP.eps id (accIrrScope.can id) = .star := by
  constructor <;> with_unfolding_all rfl

/-- PIN: the variable-major redex, the irr-rewritten redex and the contractum erase EXACTLY as
    the Lean ι cell's endpoints: the proof in the major, and inside the recursive hypothesis,
    is dropped wherever it came from. -/
theorem accIrr_eps : accIrrLhsP.eps id (accIrrScope.can id) = accLhsE [.param 0] ∧
    accIrrMidP.eps id (accIrrScope.can id) = accLhsE [.param 0] ∧
    accIrrRhsP.eps id (accIrrScope.can id) = accRhsE [.param 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **(H) closes the irr+ι composite at a non-canonical major.** -/
theorem accIrr_es_star :
    ConvMod (EStep accStarTable) LvlEq (accIrrLhsP.eps id (accIrrScope.can id))
      (accIrrRhsP.eps id (accIrrScope.can id)) := by
  rw [accIrr_eps.1, accIrr_eps.2.2]
  exact convMod_of_rstar_estep (accStar_chain _)

/-- **`tableOfK` does not**: the Abel–Coquand irr+ι step has no erased image there. -/
theorem accIrr_not_es_tableOfK :
    ¬ ConvMod (EStep (tableOfK accPEnvWfT)) LvlEq (accIrrLhsP.eps id (accIrrScope.can id))
      (accIrrRhsP.eps id (accIrrScope.can id)) := by
  rw [accIrr_eps.1, accIrr_eps.2.2, tableOfK_accP]
  exact accIota_not_convE_nil _

/-! ## §4 the Abel–Coquand loop: `[g, h, x, rr]`, large motive, a minor that recurses at `x`

`rr : Π z, R z z` makes the guard dischargeable at `x` itself; the motive is large (`rec.{1}`,
values in `Sort 1`), the minor calls its recursive hypothesis at `x`:

    M := λ x' _. Sort 0          F := λ x' g ih. ih x' (rr x')
    X := rec M F x h
      ≡irr+app rec M F x (intro x g)                         (T1)
      ≡ι       F x g (λ y r. rec M F y (g y r))              (T2)
      ≡β       (λ y r. rec M F y (g y r)) x (rr x)           (T3)
      ≡β       rec M F x (g x (rr x))                         (T4)
      ≡irr+app rec M F x h = X

The typed side unfolds forever (every turn is irr + ι + β). Every typing below is a hand-built
derivation (the checker `tyAtC` needs β here, and its kernel evaluation does not fit in memory). -/

/-- `Sort 0 : Sort 1` anywhere. -/
def accHS0 (Γ : LCtx) : HasTyT accPEnvT 1 Γ (.sort .zero) (.sort (.succ .zero)) := .sort Γ .zero

def accHAccP {Γ : LCtx} {a : Expr Nat} (ha : HasTyT accPEnvT 1 Γ a (.sort .zero)) :
    HasTyT accPEnvT 1 Γ (.app (.const 10 []) a) (.sort .zero) :=
  .app Γ (.const 10 []) a (.sort .zero) (.sort .zero) (.const Γ 10 [] accPFamT rfl rfl rfl) ha

def accHR {Γ : LCtx} {a b : Expr Nat} (ha : HasTyT accPEnvT 1 Γ a (.sort .zero))
    (hb : HasTyT accPEnvT 1 Γ b (.sort .zero)) :
    HasTyT accPEnvT 1 Γ (.app (.app (.const 9 []) a) b) (.sort .zero) :=
  .app Γ (.app (.const 9 []) a) b (.sort .zero) (.sort .zero)
    (.app Γ (.const 9 []) a (.sort .zero) (.pi (.sort .zero) (.sort .zero))
      (.const Γ 9 [] paRelT rfl rfl rfl) ha) hb

/-- the loop's large motive `λ (x':S0) (t : AccP x'). Sort 0`. -/
def accMLoop : Expr Nat := .lam (.sort .zero) (.lam (.app (.const 10 []) (.bvar 0)) (.sort .zero))

def accHMLoopBody (Γ : LCtx) :
    HasTyT accPEnvT 1 (.assumption (.sort .zero) :: Γ)
      (.lam (.app (.const 10 []) (.bvar 0)) (.sort .zero))
      (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.succ .zero))) :=
  .lam _ _ .zero _ _ (accHAccP (.bvar _ 0 _ (by rfl))) (.sort _ .zero)

def accHMLoop (Γ : LCtx) :
    HasTyT accPEnvT 1 Γ accMLoop
      (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.succ .zero)))) :=
  .lam Γ _ (.succ .zero) _ _ (accHS0 Γ) (accHMLoopBody Γ)

/-- `M a t ≡ Sort 0 : Sort 1` by two β. -/
def accCMBeta {Γ : LCtx} {a t : Expr Nat} (ha : HasTyT accPEnvT 1 Γ a (.sort .zero))
    (ht : HasTyT accPEnvT 1 Γ t (.app (.const 10 []) a)) :
    ConvT accPEnvT 1 Γ (.app (.app accMLoop a) t) (.sort .zero) (.sort (.succ .zero)) :=
  .trans Γ _ (.app (.lam (.app (.const 10 []) a) (.sort .zero)) t) _ _
    (.app Γ (.app accMLoop a) (.lam (.app (.const 10 []) a) (.sort .zero)) t t
      (.app (.const 10 []) a) (.sort (.succ .zero))
      (.beta Γ (.sort .zero) (.lam (.app (.const 10 []) (.bvar 0)) (.sort .zero)) a
        (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.succ .zero))) (.succ .zero)
        (accHS0 Γ) (accHMLoopBody Γ) ha)
      (.refl Γ t _ ht))
    (.beta Γ (.app (.const 10 []) a) (.sort .zero) t (.sort (.succ .zero)) .zero
      (accHAccP ha) (.sort _ .zero) ht)

/-- `paFieldDom` at any `x'`-extended context. -/
def accHFD (Γ : LCtx) :
    HasTyT accPEnvT 1 (.assumption (.sort .zero) :: Γ) paFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  .pi _ _ (.succ .zero) _ (.imax .zero .zero) (accHS0 _)
    (.pi _ _ .zero _ .zero (accHR (.bvar _ 0 _ (by rfl)) (.bvar _ 1 _ (by rfl)))
      (accHAccP (.bvar _ 1 _ (by rfl))))

/-- the minor's recursive-hypothesis domain at `M := accMLoop`, in `[g', x', …]`. -/
def accIhDom : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
    (.app (.app accMLoop (.bvar 1)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

/-- the minor's binder contexts over an ambient `Γ`: `x'`, `g'`, `ih`, and `y`, `r` inside `ih`'s
    domain. -/
abbrev accCX (Γ : LCtx) : LCtx := .assumption (.sort .zero) :: Γ
abbrev accCG (Γ : LCtx) : LCtx := .assumption paFieldDom :: accCX Γ
abbrev accCIH (Γ : LCtx) : LCtx := .assumption accIhDom :: accCG Γ
abbrev accCY (Γ : LCtx) : LCtx := .assumption (.sort .zero) :: accCG Γ
abbrev accCR (Γ : LCtx) : LCtx :=
  .assumption (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2)) :: accCY Γ

def accHIhDom (Γ : LCtx) :
    HasTyT accPEnvT 1 (accCG Γ) accIhDom (.sort (.imax (.succ .zero) (.imax .zero (.succ .zero)))) :=
  .pi (accCG Γ) _ (.succ .zero) _ _ (accHS0 _)
    (.pi (accCY Γ) _ .zero _ (.succ .zero)
      (accHR (.bvar (accCY Γ) 0 _ rfl) (.bvar (accCY Γ) 2 _ rfl))
      (.app (accCR Γ) _ _ _ _ (.app (accCR Γ) _ _ _ _ (accHMLoop _) (.bvar (accCR Γ) 1 _ rfl))
        (.app (accCR Γ) _ _ _ _
          (.app (accCR Γ) _ _ _ _ (.bvar (accCR Γ) 2 _ rfl) (.bvar (accCR Γ) 1 _ rfl))
          (.bvar (accCR Γ) 0 _ rfl))))

/-- `rr : Π z, R z z`. -/
def accRrTy : Expr Nat := .pi (.sort .zero) (.app (.app (.const 9 []) (.bvar 0)) (.bvar 0))

/-- the loop's minor `λ x' g ih. ih x' (rr x')`, with `rr` at index `k` of the ambient context. -/
def accFLoopAt (k : Nat) : Expr Nat :=
  .lam (.sort .zero) (.lam paFieldDom (.lam accIhDom
    (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar (k + 3)) (.bvar 2)))))

/-- the minor's required codomain `M x' (intro x' g')` at `M := accMLoop`. -/
def accFReq : Expr Nat :=
  .app (.app accMLoop (.bvar 2)) (.app (.app (.const 11 []) (.bvar 2)) (.bvar 1))

/-- the minor body's own type `M x' (g' x' (rr x'))`. -/
def accFNat (k : Nat) : Expr Nat :=
  .app (.app accMLoop (.bvar 2)) (.app (.app (.bvar 1) (.bvar 2)) (.app (.bvar (k + 3)) (.bvar 2)))

/-- the minor's typing: its body `ih x' (rr x') : M x' (g' x' (rr x'))` is moved to the
    required `M x' (intro x' g')` by `accCMBeta` on both sides (both are `Sort 0`). -/
def accHFLoop (Γ : LCtx) (k : Nat)
    (hrr : lookupType (accCIH Γ) (k + 3) = some accRrTy) :
    HasTyT accPEnvT 1 Γ (accFLoopAt k)
      (.pi (.sort .zero) (.pi paFieldDom (.pi accIhDom accFReq))) :=
  have hrrx : HasTyT accPEnvT 1 (accCIH Γ) (.app (.bvar (k + 3)) (.bvar 2))
      (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2)) :=
    .app (accCIH Γ) _ _ (.sort .zero) (.app (.app (.const 9 []) (.bvar 0)) (.bvar 0))
      (.bvar _ (k + 3) _ hrr) (.bvar (accCIH Γ) 2 _ rfl)
  have hnat : HasTyT accPEnvT 1 (accCIH Γ)
      (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar (k + 3)) (.bvar 2))) (accFNat k) :=
    .app (accCIH Γ) _ _ (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2))
      (.app (.app accMLoop (.bvar 3)) (.app (.app (.bvar 2) (.bvar 3)) (.bvar 0)))
      (.app (accCIH Γ) _ _ (.sort .zero)
        (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
          (.app (.app accMLoop (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))
        (.bvar (accCIH Γ) 0 _ rfl) (.bvar (accCIH Γ) 2 _ rfl))
      hrrx
  have hgx : HasTyT accPEnvT 1 (accCIH Γ)
      (.app (.app (.bvar 1) (.bvar 2)) (.app (.bvar (k + 3)) (.bvar 2)))
      (.app (.const 10 []) (.bvar 2)) :=
    .app (accCIH Γ) _ _ (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2))
      (.app (.const 10 []) (.bvar 3))
      (.app (accCIH Γ) _ _ (.sort .zero)
        (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3)) (.app (.const 10 []) (.bvar 1)))
        (.bvar (accCIH Γ) 1 _ rfl) (.bvar (accCIH Γ) 2 _ rfl))
      hrrx
  have hintro : HasTyT accPEnvT 1 (accCIH Γ) (.app (.app (.const 11 []) (.bvar 2)) (.bvar 1))
      (.app (.const 10 []) (.bvar 2)) :=
    .app (accCIH Γ) _ _
      (.pi (.sort .zero) (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
        (.app (.const 10 []) (.bvar 1))))
      (.app (.const 10 []) (.bvar 3))
      (.app (accCIH Γ) _ _ (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1)))
        (.const (accCIH Γ) 11 [] paIntroT rfl rfl rfl) (.bvar (accCIH Γ) 2 _ rfl))
      (.bvar (accCIH Γ) 1 _ rfl)
  have hx : HasTyT accPEnvT 1 (accCIH Γ) (.bvar 2) (.sort .zero) := .bvar (accCIH Γ) 2 _ rfl
  .lam Γ _ (.succ .zero) _ _ (accHS0 Γ)
    (.lam (accCX Γ) _ _ _ _ (accHFD Γ)
      (.lam (accCG Γ) _ _ _ _ (accHIhDom Γ)
        (.conv (accCIH Γ) _ (accFNat k) accFReq (.succ .zero) hnat
          (.trans (accCIH Γ) _ (.sort .zero) _ _ (accCMBeta hx hgx)
            (.symm (accCIH Γ) _ _ _ (accCMBeta hx hintro))))))

/-- `[g : Π y, R y x → AccP y, h : AccP x, x : S0, rr : Π z, R z z]`. -/
def accLoopCtx : LCtx :=
  [.assumption accGTy, .assumption (.app (.const 10 []) (.bvar 0)), .assumption (.sort .zero),
    .assumption accRrTy]

def accLoopCtxWf : CtxWfT accPEnvT 1 accLoopCtx :=
  .assumption _ _ (.imax (.succ .zero) (.imax .zero .zero))
    (.assumption _ _ .zero
      (.assumption _ _ (.succ .zero)
        (.assumption [] _ (.imax (.succ .zero) .zero) .nil
          (.pi [] _ _ _ _ (accHS0 _)
            (accHR (.bvar [.assumption (.sort .zero)] 0 _ rfl)
              (.bvar [.assumption (.sort .zero)] 0 _ rfl))))
        (accHS0 _))
      (accHAccP (.bvar (accLoopCtx.drop 2) 0 _ rfl)))
    (.pi (accLoopCtx.drop 1) _ _ _ _ (accHS0 _)
      (.pi (.assumption (.sort .zero) :: accLoopCtx.drop 1) _ _ _ _
        (accHR (.bvar (.assumption (.sort .zero) :: accLoopCtx.drop 1) 0 _ rfl)
          (.bvar (.assumption (.sort .zero) :: accLoopCtx.drop 1) 2 _ rfl))
        (accHAccP (.bvar (.assumption (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2)) ::
          .assumption (.sort .zero) :: accLoopCtx.drop 1) 1 _ rfl))))

def accLoopScope : ScopedCtx accPEnvT accPEnvT 1 accLoopCtx :=
  ⟨accPEnvWfT, envExt_refl _, accLoopCtxWf⟩

/-- `rec.{1} M F x t` at `x := bvar i`, with `F`'s `rr` at index `k`. -/
def accLoopRec (k i : Nat) (t : Expr Nat) : Expr Nat :=
  foldApps (.const 12 [.succ .zero]) [accMLoop, accFLoopAt k, .bvar i, t]

/-- its typing at `x := bvar 1`, from a typing of the major at `AccP x`. -/
def accHLoopRec1 (Γ : LCtx) (k : Nat) {t : Expr Nat}
    (hrr : lookupType (accCIH Γ) (k + 3) = some accRrTy)
    (hx : HasTyT accPEnvT 1 Γ (.bvar 1) (.sort .zero))
    (ht : HasTyT accPEnvT 1 Γ t (.app (.const 10 []) (.bvar 1))) :
    HasTyT accPEnvT 1 Γ (accLoopRec k 1 t) (.app (.app accMLoop (.bvar 1)) t) :=
  .app Γ _ _ (.app (.const 10 []) (.bvar 1)) (.app (.app accMLoop (.bvar 2)) (.bvar 0))
    (.app Γ _ _ (.sort .zero)
      (.pi (.app (.const 10 []) (.bvar 0)) (.app (.app accMLoop (.bvar 1)) (.bvar 0)))
      (.app Γ _ _ (.pi (.sort .zero) (.pi paFieldDom (.pi accIhDom accFReq)))
        (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0))
          (.app (.app accMLoop (.bvar 1)) (.bvar 0))))
        (.app Γ _ _ (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.succ .zero))))
          (.pi paMinorTy (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0))
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
          (.const Γ 12 [.succ .zero] paRecT rfl rfl rfl) (accHMLoop Γ))
        (accHFLoop Γ k hrr))
      hx)
    ht

/-- its typing at `x := bvar 2`, from a typing of the major at `AccP x`. -/
def accHLoopRec2 (Γ : LCtx) (k : Nat) {t : Expr Nat}
    (hrr : lookupType (accCIH Γ) (k + 3) = some accRrTy)
    (hx : HasTyT accPEnvT 1 Γ (.bvar 2) (.sort .zero))
    (ht : HasTyT accPEnvT 1 Γ t (.app (.const 10 []) (.bvar 2))) :
    HasTyT accPEnvT 1 Γ (accLoopRec k 2 t) (.app (.app accMLoop (.bvar 2)) t) :=
  .app Γ _ _ (.app (.const 10 []) (.bvar 2)) (.app (.app accMLoop (.bvar 3)) (.bvar 0))
    (.app Γ _ _ (.sort .zero)
      (.pi (.app (.const 10 []) (.bvar 0)) (.app (.app accMLoop (.bvar 1)) (.bvar 0)))
      (.app Γ _ _ (.pi (.sort .zero) (.pi paFieldDom (.pi accIhDom accFReq)))
        (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0))
          (.app (.app accMLoop (.bvar 1)) (.bvar 0))))
        (.app Γ _ _ (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.succ .zero))))
          (.pi paMinorTy (.pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0))
            (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
          (.const Γ 12 [.succ .zero] paRecT rfl rfl rfl) (accHMLoop Γ))
        (accHFLoop Γ k hrr))
      hx)
    ht

/-- `X := rec M F x h`. -/
def accLoopX : Expr Nat := accLoopRec 3 2 (.bvar 1)
/-- T1 `rec M F x (intro x g)`. -/
def accLoopT1 : Expr Nat := accLoopRec 3 2 (.app (.app (.const 11 []) (.bvar 2)) (.bvar 0))
/-- the recursive hypothesis `λ (y:S0) (r : R y x). rec M F y (g y r)`. -/
def accLoopIH : Expr Nat :=
  .lam (.sort .zero) (.lam (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
    (accLoopRec 5 1 (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))
/-- T2 `F x g (λ y r. rec M F y (g y r))` — the ι contractum. -/
def accLoopT2 : Expr Nat := .app (.app (.app (accFLoopAt 3) (.bvar 2)) (.bvar 0)) accLoopIH
/-- T3 `(λ y r. rec M F y (g y r)) x (rr x)`. -/
def accLoopT3 : Expr Nat := .app (.app accLoopIH (.bvar 2)) (.app (.bvar 3) (.bvar 2))
/-- T4 `rec M F x (g x (rr x))`. -/
def accLoopT4 : Expr Nat :=
  accLoopRec 3 2 (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar 3) (.bvar 2)))

/-- the inner contexts of `accLoopIH`. -/
abbrev accLoopCY : LCtx := .assumption (.sort .zero) :: accLoopCtx
abbrev accLoopCR : LCtx := .assumption (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3)) :: accLoopCY

def accHLoopX0 : HasTyT accPEnvT 1 accLoopCtx (.bvar 2) (.sort .zero) := .bvar accLoopCtx 2 _ rfl

def accHLoopRrx : HasTyT accPEnvT 1 accLoopCtx (.app (.bvar 3) (.bvar 2))
    (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2)) :=
  .app accLoopCtx _ _ (.sort .zero) (.app (.app (.const 9 []) (.bvar 0)) (.bvar 0))
    (.bvar accLoopCtx 3 _ rfl) accHLoopX0

def accHLoopIntro : HasTyT accPEnvT 1 accLoopCtx (.app (.app (.const 11 []) (.bvar 2)) (.bvar 0))
    (.app (.const 10 []) (.bvar 2)) :=
  .app accLoopCtx _ _
    (.pi (.sort .zero) (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
      (.app (.const 10 []) (.bvar 1))))
    (.app (.const 10 []) (.bvar 3))
    (.app accLoopCtx _ _ (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1)))
      (.const accLoopCtx 11 [] paIntroT rfl rfl rfl) accHLoopX0)
    (.bvar accLoopCtx 0 _ rfl)

def accHLoopGxr : HasTyT accPEnvT 1 accLoopCtx
    (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar 3) (.bvar 2))) (.app (.const 10 []) (.bvar 2)) :=
  .app accLoopCtx _ _ (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2))
    (.app (.const 10 []) (.bvar 3))
    (.app accLoopCtx _ _ (.sort .zero)
      (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3)) (.app (.const 10 []) (.bvar 1)))
      (.bvar accLoopCtx 0 _ rfl) accHLoopX0)
    accHLoopRrx

def accHLoopX : HasTyT accPEnvT 1 accLoopCtx accLoopX (.app (.app accMLoop (.bvar 2)) (.bvar 1)) :=
  accHLoopRec2 accLoopCtx 3 rfl accHLoopX0 (.bvar accLoopCtx 1 _ rfl)

def accHLoopT1 : HasTyT accPEnvT 1 accLoopCtx accLoopT1
    (.app (.app accMLoop (.bvar 2)) (.app (.app (.const 11 []) (.bvar 2)) (.bvar 0))) :=
  accHLoopRec2 accLoopCtx 3 rfl accHLoopX0 accHLoopIntro

/-- the type of `accLoopIH`. -/
def accLoopIHTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
    (.app (.app accMLoop (.bvar 1)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

def accHLoopIH : HasTyT accPEnvT 1 accLoopCtx accLoopIH accLoopIHTy :=
  .lam accLoopCtx _ (.succ .zero) _ _ (accHS0 _)
    (.lam accLoopCY _ .zero _ _
      (accHR (.bvar accLoopCY 0 _ rfl) (.bvar accLoopCY 3 _ rfl))
      (accHLoopRec1 accLoopCR 5 rfl (.bvar accLoopCR 1 _ rfl)
        (.app accLoopCR _ _ (.app (.app (.const 9 []) (.bvar 1)) (.bvar 4))
          (.app (.const 10 []) (.bvar 2))
          (.app accLoopCR _ _ (.sort .zero)
            (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 5)) (.app (.const 10 []) (.bvar 1)))
            (.bvar accLoopCR 2 _ rfl) (.bvar accLoopCR 1 _ rfl))
          (.bvar accLoopCR 0 _ rfl))))

def accHLoopT2 : HasTyT accPEnvT 1 accLoopCtx accLoopT2
    (.app (.app accMLoop (.bvar 2)) (.app (.app (.const 11 []) (.bvar 2)) (.bvar 0))) :=
  .app accLoopCtx _ _ _ _
    (.app accLoopCtx _ _ _ _
      (.app accLoopCtx _ _ (.sort .zero) (.pi paFieldDom (.pi accIhDom accFReq))
        (accHFLoop accLoopCtx 3 rfl) accHLoopX0)
      (.bvar accLoopCtx 0 _ rfl))
    accHLoopIH

def accHLoopT3 : HasTyT accPEnvT 1 accLoopCtx accLoopT3
    (.app (.app accMLoop (.bvar 2)) (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar 3) (.bvar 2)))) :=
  .app accLoopCtx _ _ (.app (.app (.const 9 []) (.bvar 2)) (.bvar 2))
    (.app (.app accMLoop (.bvar 3)) (.app (.app (.bvar 1) (.bvar 3)) (.bvar 0)))
    (.app accLoopCtx _ _ (.sort .zero)
      (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 3))
        (.app (.app accMLoop (.bvar 1)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))
      accHLoopIH accHLoopX0)
    accHLoopRrx

def accHLoopT4 : HasTyT accPEnvT 1 accLoopCtx accLoopT4
    (.app (.app accMLoop (.bvar 2)) (.app (.app (.bvar 0) (.bvar 2)) (.app (.bvar 3) (.bvar 2)))) :=
  accHLoopRec2 accLoopCtx 3 rfl accHLoopX0 accHLoopGxr

noncomputable def accLoopXP := enrichHasTyT_of_envWfT accPEnvWfT accLoopCtxWf accHLoopX
noncomputable def accLoopT1P := enrichHasTyT_of_envWfT accPEnvWfT accLoopCtxWf accHLoopT1
noncomputable def accLoopT2P := enrichHasTyT_of_envWfT accPEnvWfT accLoopCtxWf accHLoopT2
noncomputable def accLoopT3P := enrichHasTyT_of_envWfT accPEnvWfT accLoopCtxWf accHLoopT3
noncomputable def accLoopT4P := enrichHasTyT_of_envWfT accPEnvWfT accLoopCtxWf accHLoopT4

/-- erased `M := λ x' _. Sort 0` (the proof binder `t` drops). -/
def accMLoopE : ETm := .lam (.sort .zero)
/-- erased `F := λ x' g ih. ih x' (rr x')` (`g` and `rr x'` drop). -/
def accFLoopE : ETm := .lam (.lam (.app (.bvar 0) (.bvar 1)))
/-- erased `X = rec M F x h`: `rec M̂ F̂ x` (`x` at `0`; `g`, `h`, `rr` dropped). -/
def accLoopXE : ETm := ETm.appN (.const 12 [.succ .zero]) [accMLoopE, accFLoopE, .bvar 0]
/-- erased T2 `F̂ x (λ y. rec M̂ F̂ y)`. -/
def accLoopT2E : ETm := .app (.app accFLoopE (.bvar 0)) (.lam accLoopXE)
/-- erased T3 `(λ y. rec M̂ F̂ y) x`. -/
def accLoopT3E : ETm := .app (.lam accLoopXE) (.bvar 0)

theorem accLoop_can : accLoopScope.can id = [.drop, .drop, .keep, .drop] := by
  with_unfolding_all rfl

/-- PIN: the landed erasures of the five loop points. `X`, `T1`, `T4` (which differ only in the
    proof major `h` / `intro x g` / `g x (rr x)`) all erase to the SAME term. -/
theorem accLoop_eps :
    accLoopXP.eps id (accLoopScope.can id) = accLoopXE ∧
    accLoopT1P.eps id (accLoopScope.can id) = accLoopXE ∧
    accLoopT2P.eps id (accLoopScope.can id) = accLoopT2E ∧
    accLoopT3P.eps id (accLoopScope.can id) = accLoopT3E ∧
    accLoopT4P.eps id (accLoopScope.can id) = accLoopXE := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- the ι step's image under (H): one ★-unfold, three β. -/
theorem accLoop_iota_star : RStar (RStep accStarTable) accLoopXE accLoopT2E :=
  .step (rStep_appN_head (.cr (.bare accStarRule_mem rfl [.succ .zero] [] rfl))
      [accMLoopE, accFLoopE, .bvar 0])
    (.step (rStep_appN_head (.beta _ accMLoopE) [accFLoopE, .bvar 0])
      (.step (rStep_appN_head (.beta _ accFLoopE) [.bvar 0])
        (.step (.beta _ (.bvar 0)) (.refl _))))

/-- the two β steps' images (any table): `T2̂ →β T3̂`'s two contractions, then `T3̂ →β X̂`. -/
theorem accLoop_beta {tbl : List CRule} :
    RStar (RStep tbl) accLoopT2E accLoopT3E ∧ RStar (RStep tbl) accLoopT3E accLoopXE :=
  ⟨.step (.appL _ (.beta _ (.bvar 0))) (.step (.beta _ _) (.refl _)),
   .step (.beta _ (.bvar 0)) (.refl _)⟩

/-- **(H) reproduces the Abel–Coquand loop in the erased calculus**: the erasure of the
    non-normalising typed term `X` reduces, through the erasures of every loop point, back to
    itself — a genuine cycle (`X̂ →⁺ X̂`, first step the ★-unfold, seven steps). -/
theorem accLoop_cycle :
    ∃ z, RStep accStarTable accLoopXE z ∧ z ≠ accLoopXE ∧ RStar (RStep accStarTable) z accLoopXE := by
  refine ⟨_, rStep_appN_head (.cr (.bare accStarRule_mem rfl [.succ .zero] [] rfl))
      [accMLoopE, accFLoopE, .bvar 0], by decide, ?_⟩
  exact (RStar.trans' (.step (rStep_appN_head (.beta _ accMLoopE) [accFLoopE, .bvar 0])
    (.step (rStep_appN_head (.beta _ accFLoopE) [.bvar 0])
      (.step (.beta _ (.bvar 0)) (.refl _)))) (accLoop_beta.1.trans' accLoop_beta.2))

/-- **every typed step of the loop has an erased image under (H)**: irr+app (`X ≡ T1`,
    `T4 ≡ X`: equal erasures), ι (`T1 ≡ T2`), β (`T2 ≡ T3`, `T3 ≡ T4`). -/
theorem accLoop_es_star :
    accLoopXP.eps id (accLoopScope.can id) = accLoopT1P.eps id (accLoopScope.can id) ∧
    ConvMod (EStep accStarTable) LvlEq (accLoopT1P.eps id (accLoopScope.can id))
      (accLoopT2P.eps id (accLoopScope.can id)) ∧
    ConvMod (EStep accStarTable) LvlEq (accLoopT2P.eps id (accLoopScope.can id))
      (accLoopT3P.eps id (accLoopScope.can id)) ∧
    ConvMod (EStep accStarTable) LvlEq (accLoopT3P.eps id (accLoopScope.can id))
      (accLoopT4P.eps id (accLoopScope.can id)) ∧
    accLoopT4P.eps id (accLoopScope.can id) = accLoopXP.eps id (accLoopScope.can id) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := accLoop_eps
  rw [h0, h1, h2, h3, h4]
  exact ⟨rfl, convMod_of_rstar_estep accLoop_iota_star,
    convMod_of_rstar_estep accLoop_beta.1, convMod_of_rstar_estep accLoop_beta.2, rfl⟩

/-- **the loop alone does not separate (H) from `tableOfK`**: at this minor the ι step's two
    erasures are already joined by β (`T2̂ →β³ X̂ = T1̂`), with no rule. The separating cell is the
    Lean ι cell with a free minor (`accIota_not_es_tableOfK`, `accIrr_not_es_tableOfK`). -/
theorem accLoop_iota_es_tableOfK :
    ConvMod (EStep (tableOfK accPEnvWfT)) LvlEq (accLoopT1P.eps id (accLoopScope.can id))
      (accLoopT2P.eps id (accLoopScope.can id)) := by
  rw [accLoop_eps.2.1, accLoop_eps.2.2.1]
  exact ConvMod.symm' (fun h => lvlEq_equivalence.symm h) (convMod_of_rstar_estep (accLoop_beta.1.trans' accLoop_beta.2))

end Rcic.Syn

#print axioms Rcic.Syn.accIotaCtx
#print axioms Rcic.Syn.accTy
#print axioms Rcic.Syn.accIotaCtxWf
#print axioms Rcic.Syn.accIotaScope
#print axioms Rcic.Syn.accIntroXG
#print axioms Rcic.Syn.accIotaLhs
#print axioms Rcic.Syn.accIotaTyE
#print axioms Rcic.Syn.accIotaIH
#print axioms Rcic.Syn.accIotaRhs
#print axioms Rcic.Syn.accIotaLhsTy
#print axioms Rcic.Syn.accIotaRhsTy
#print axioms Rcic.Syn.accIotaLhsP
#print axioms Rcic.Syn.accIotaRhsP
#print axioms Rcic.Syn.accLhsE
#print axioms Rcic.Syn.accRhsE
#print axioms Rcic.Syn.accIota_can
#print axioms Rcic.Syn.accIota_eps_lhs
#print axioms Rcic.Syn.accIota_eps_rhs
#print axioms Rcic.Syn.accStar_chain
#print axioms Rcic.Syn.accIota_es_star
#print axioms Rcic.Syn.rStep_spineHead_bvar
#print axioms Rcic.Syn.etaStep_spineHead_bvar
#print axioms Rcic.Syn.rstar_spineHead_bvar
#print axioms Rcic.Syn.lvlEq_spineHead_bvar
#print axioms Rcic.Syn.ETm.lamFree
#print axioms Rcic.Syn.eStep_nil_lamFree
#print axioms Rcic.Syn.accIota_not_convE_nil
#print axioms Rcic.Syn.accIota_not_es_tableOfK
#print axioms Rcic.Syn.accGTy
#print axioms Rcic.Syn.accIrrCtx
#print axioms Rcic.Syn.accIrrCtxWf
#print axioms Rcic.Syn.accIrrScope
#print axioms Rcic.Syn.accIrrIntro
#print axioms Rcic.Syn.accIrrP
#print axioms Rcic.Syn.accIrrLhs
#print axioms Rcic.Syn.accIrrMid
#print axioms Rcic.Syn.accIrrRhs
#print axioms Rcic.Syn.accIrrTyL
#print axioms Rcic.Syn.accIrrTyR
#print axioms Rcic.Syn.accIrrHTy
#print axioms Rcic.Syn.accIrrIntroTy
#print axioms Rcic.Syn.accIrrLhsTy
#print axioms Rcic.Syn.accIrrMidTy
#print axioms Rcic.Syn.accIrrRhsTy
#print axioms Rcic.Syn.accIrrLeaf
#print axioms Rcic.Syn.accIrrHP
#print axioms Rcic.Syn.accIrrIntroP
#print axioms Rcic.Syn.accIrrLhsP
#print axioms Rcic.Syn.accIrrMidP
#print axioms Rcic.Syn.accIrrRhsP
#print axioms Rcic.Syn.accIrr_can
#print axioms Rcic.Syn.accIrr_eps_irr
#print axioms Rcic.Syn.accIrr_eps
#print axioms Rcic.Syn.accIrr_es_star
#print axioms Rcic.Syn.accIrr_not_es_tableOfK
#print axioms Rcic.Syn.accHS0
#print axioms Rcic.Syn.accHAccP
#print axioms Rcic.Syn.accHR
#print axioms Rcic.Syn.accMLoop
#print axioms Rcic.Syn.accHMLoopBody
#print axioms Rcic.Syn.accHMLoop
#print axioms Rcic.Syn.accCMBeta
#print axioms Rcic.Syn.accHFD
#print axioms Rcic.Syn.accIhDom
#print axioms Rcic.Syn.accHIhDom
#print axioms Rcic.Syn.accRrTy
#print axioms Rcic.Syn.accFLoopAt
#print axioms Rcic.Syn.accFReq
#print axioms Rcic.Syn.accFNat
#print axioms Rcic.Syn.accHFLoop
#print axioms Rcic.Syn.accLoopCtx
#print axioms Rcic.Syn.accLoopCtxWf
#print axioms Rcic.Syn.accLoopScope
#print axioms Rcic.Syn.accLoopRec
#print axioms Rcic.Syn.accHLoopRec1
#print axioms Rcic.Syn.accHLoopRec2
#print axioms Rcic.Syn.accLoopX
#print axioms Rcic.Syn.accLoopT1
#print axioms Rcic.Syn.accLoopIH
#print axioms Rcic.Syn.accLoopT2
#print axioms Rcic.Syn.accLoopT3
#print axioms Rcic.Syn.accLoopT4
#print axioms Rcic.Syn.accHLoopX0
#print axioms Rcic.Syn.accHLoopRrx
#print axioms Rcic.Syn.accHLoopIntro
#print axioms Rcic.Syn.accHLoopGxr
#print axioms Rcic.Syn.accHLoopX
#print axioms Rcic.Syn.accHLoopT1
#print axioms Rcic.Syn.accLoopIHTy
#print axioms Rcic.Syn.accHLoopIH
#print axioms Rcic.Syn.accHLoopT2
#print axioms Rcic.Syn.accHLoopT3
#print axioms Rcic.Syn.accHLoopT4
#print axioms Rcic.Syn.accLoopXP
#print axioms Rcic.Syn.accLoopT1P
#print axioms Rcic.Syn.accLoopT2P
#print axioms Rcic.Syn.accLoopT3P
#print axioms Rcic.Syn.accLoopT4P
#print axioms Rcic.Syn.accMLoopE
#print axioms Rcic.Syn.accFLoopE
#print axioms Rcic.Syn.accLoopXE
#print axioms Rcic.Syn.accLoopT2E
#print axioms Rcic.Syn.accLoopT3E
#print axioms Rcic.Syn.accLoop_can
#print axioms Rcic.Syn.accLoop_eps
#print axioms Rcic.Syn.accLoop_iota_star
#print axioms Rcic.Syn.accLoop_beta
#print axioms Rcic.Syn.accLoop_cycle
#print axioms Rcic.Syn.accLoop_es_star
#print axioms Rcic.Syn.accLoop_iota_es_tableOfK
