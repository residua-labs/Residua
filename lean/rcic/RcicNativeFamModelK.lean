import rcic.RcicNativeFamModel
import rcic.RcicNativePiModelDeltaIota
import rcic.RcicNativePiModelLRTermD
import rcic.RcicCensusWallsForall
import rcic.RcicSortUniqueRows

/-!
# RcicNativeFamModelK — K / η-K at non-canonical proof majors: the kernel counterexample (W-K)
and the restated K-aware family row

**Objective (desktop-Opus lane).**  Prove the K and η-K cases of the family fundamental lemma
`FundamentalLRFamINT` (`RcicNativeFamModel` §8) honestly — at a canonical major by ι, at a
non-canonical proof major by the proposition collapse — or, if K is unsound for the model
somewhere, give the kernel counterexample and the restated row.

**Finding (W-K): K is unsound for the model's READBACK.**  Every logical relation on `main`
(`LRTypeIN` / `LRTypeICtx` / `LRTypeFamIN`, and through their `.sort` / `.pi` clauses the term
relations `LRTermD` / `LRTermFamIN` / `LRTermFamIND`) reads a type back by SYNTACTIC weak-head
reduction (`WhRed E` / `WhRedCtx E Γ`), whose only ι step (`DerivedIotaU`) needs the major to BE a
constructor spine.  `ConvT` reaches more: `irr` identifies any proof `h : P` with the canonical
major, `ConvT.app` lifts that through the recursor spine, and ordinary ι fires — so a
large-eliminating recursor applied to a NON-canonical proof is convertible to its minor's value,
while no `WhRedCtx` step leaves it.  When the motive is a universe (the result is NOT a
proposition) the proposition collapse does not apply and the relation is false.  Two admitted
kernel instances, at the two compacts the row read-offs consume:

* **§1 `trueEnvU` (field-free, K proper), compact `.sort`.**  `kRec x = True.rec.{2} M (Sort 0) x`
  with `M = λ _ : True. Sort 1`.  For EVERY proof `x : True`, `Sort 0 ≡ kRec x : Sort 1`
  (`kRec_conv_sort`: `ι`⁻¹ at `intro`, then `ConvT.app` + `ConvT.irr`).  At the proof VARIABLE
  `x = bvar 0` (`kVarCtx = [h : True]`) and at the CLOSED non-canonical proof
  `x = (λ y : True. y) intro` (`Γ = []`), `kRec x` takes no `WhStepCtx` step
  (`whStepCtx_constSpine_false`).
* **§2 `andEnvU` (fieldful), compact `.pi ⊥ []`.**  The landed mixed pair
  `mixAndRedex = And.rec a b (λ _. Sort 1) (λ x y. Sort 0 → Sort 0) h ≡ Sort 0 → Sort 0`
  (`RcicAndHeadStepNoGo.mixAnd_conv`) — the Π-compact `piRow` probes.  A field-free K step
  (`ι★K`) does not cover it: the repair must replace a proof major by ANY canonical major of
  the same proposition.

Refuted at these admitted environments (all `n` at `trueEnvU`, `n = 0` at `andEnvU`):
`FundamentalLRFamINT`, `FundamentalLRFamIN`, `FundamentalLRICtx`, `FundamentalTermFamIN`,
`FundamentalTermFamIND` (main's newest family remainder, §10), and on the Π side
`FundamentalTermD` and `PiModelDeltaIotaAudit.FundamentalLRINBotDI` — a third wall independent of
W-DEMAND and W-ZETALOCAL.  The compacts used (`.sort`, `.pi ⊥ []`) are `BotPiCpt`, so the
compact-restricted restatements fall as well.  **η-K** (§1.5): `λ p : True. Sort 0 ≡ True.rec M
(Sort 0)` (η + K under the binder) refutes `FundamentalTermFamIND trueEnvU 0` through its λ clause
at the proof variable.

**Restated row (§3–§5).**
* `WhStepK E n Γ` — `WhStepCtx` plus the **proposition-major ι step** `pmajor` (a recursor spine
  whose major `x : P`, `P : Sort 0`, steps to the ι contractum of ANY canonical major `canon : P`;
  on typed terms it is the composite `irr` + `ConvT.app` + ι — an argument only, not compiled
  here and used by no consumer below; it is K when the constructor is field-free and the
  irr-mixed pair when it is fieldful), **recursor-argument reduction** `recArg` (the major is
  reduced before ι), and `appHead`.  Sorts, Π-types and admitted family spines stay normal
  (`whRedK_sort_eq`, `whRedK_pi_eq`, `whRedK_famApp_eq`).
* `LRTypeFamK` — `LRTypeFamIN` read back by `WhRedK`, with the Π codomain guarded by
  `BotDemand` (W-DEMAND) and the non-family spine clause asking for convertible reducts, not
  normal forms (cf. Abel–Coquand 2020: impredicative `Prop` + definitional proof irrelevance +
  K-like elimination is not normalising; the remainder must not ask for normal forms).  `lrTypeFamK_of_lrTypeFamIN`: the restatement is implied by
  the old relation, so it is no stronger.
* `FundamentalLRFamKT` — `FundamentalLRFamINT` with `LRTypeFamK`; it yields `PiRowField`,
  `FamAppRowLink` and, with `AllBelowScoped`, `TypedRowsWf` (`typedRowsWf_of_allBelowScoped_
  fundamentalLRFamKT`) — the single named remainder of the family route.
* **Non-vacuity: every refuting point is satisfied.**  At the K points (both majors, both
  directions, all compacts), the fieldful And point, `idPiProp` (W-DEMAND) and `zetaSortCtx`
  (W-ZETALOCAL) the remainder's instance HOLDS.  The type-level K case (`lrTypeFamK_pmajor_left`
  / `_right`), the canonical ι case (`lrTypeFamK_iota_left` / `_right`) and the η-K demanded
  output (`lrTypeFamK_etaK_app`) are proved.

`closure_claim = 0`.  No `sorry`, axioms ⊆ `{propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.FamModelKAudit

open Rcic.Declarative
open Rcic.Declarative.KernelRowsAssembly
open Rcic.Declarative.NativeValleys.PiModelAudit
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Syn

/-! ### §0 — Stuck constant spines -/

/-- A constant-headed spine is never a bound variable. -/
theorem foldApps_const_ne_bvar {r : Nat} {ls : List Level} (xs : List (Expr Nat)) (i : Nat) :
    foldApps (.const r ls) xs ≠ .bvar i := fun h => by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  exact Expr.noConfusion (congrArg Prod.fst hs)

/-- An application whose head is a λ is never a constant-headed spine. -/
theorem lamApp_ne_foldApps_const {c : Nat} {us : List Level} {A b a : Expr Nat}
    (ys : List (Expr Nat)) : .app (.lam A b) a ≠ foldApps (.const c us) ys := by
  intro heq
  rcases list_eq_nil_or_snoc ys with rfl | ⟨pre, y, rfl⟩
  · exact Expr.noConfusion heq
  · rw [foldApps_snoc] at heq
    injection heq with hf _
    exact F8EtaK.foldApps_const_ne_lam_any hf.symm

/-- Auxiliary induction for `whStepCtx_constSpine_false`: no `WhStepCtx E Γ a e` can have
    `a = foldApps (.const r ls) xs` when the head member has no body and no argument is a
    constant-headed spine. -/
theorem whStepCtx_constSpine_false_aux {E : ResolvedEnv} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {a e : Expr Nat} (h : WhStepCtx E Γ a e) :
    ∀ (xs : List (Expr Nat)),
      (∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
        x ≠ foldApps (.const c us) ys) →
      a = foldApps (.const r ls) xs → False := by
  induction h with
  | beta A b arg =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf _
        exact F8EtaK.foldApps_const_ne_lam_any hf.symm
  | zeta A v b =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | zetaLocal _ =>
      intro xs hxs heq
      exact foldApps_const_ne_bvar xs _ heq.symm
  | delta hres hbody' =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · injection heq with hr _
        subst hr
        rw [hm] at hres
        injection hres with hm'
        subst hm'
        rw [hbody] at hbody'
        exact Option.noConfusion hbody'
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | iota hI =>
      intro xs hxs heq
      cases hI with
      | ofU w =>
          have hs : foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) =
              foldApps (.const r ls) xs := heq
          obtain ⟨_, hxs_eq⟩ := foldApps_const_inj hs
          have hmem : ctorMajor w ∈ xs := by
            subst hxs_eq
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exact hxs (ctorMajor w) hmem w.ctorRef w.lsC (w.ctorParams ++ w.fields) rfl
      | ofUS w =>
          have hs : foldApps (.const w.recRef w.ls)
              (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC)
                (w.ctorParams ++ w.fields)]) =
              foldApps (.const r ls) xs := heq
          obtain ⟨_, hxs_eq⟩ := foldApps_const_inj hs
          have hmem : foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields) ∈ xs := by
            subst hxs_eq
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exact hxs _ hmem w.ctorRef w.lsC (w.ctorParams ++ w.fields) rfl
  | lit t =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | appHead _ ih =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hpre _
        exact ih pre (fun y hy c us ys h' => hxs y (List.mem_append_left _ hy) c us ys h') hpre

/-- A constant-headed spine whose head has no δ-body, and none of whose arguments is itself a
    constant-headed spine, takes no `WhStepCtx` step: β needs a λ head, δ a body, ι a
    constructor-spine major (`derivedIotaU`'s two arms), and `appHead` recurses on the prefix. -/
theorem whStepCtx_constSpine_false {E : ResolvedEnv} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none) :
    ∀ (xs : List (Expr Nat)),
      (∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
        x ≠ foldApps (.const c us) ys) →
      ∀ e, ¬ WhStepCtx E Γ (foldApps (.const r ls) xs) e :=
  fun xs hxs _ h => whStepCtx_constSpine_false_aux hm hbody h xs hxs rfl

/-- Reductions from such a spine are trivial. -/
theorem whRedCtx_constSpine_eq {E : ResolvedEnv} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {xs : List (Expr Nat)}
    (hxs : ∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
      x ≠ foldApps (.const c us) ys)
    {e : Expr Nat} (h : WhRedCtx E Γ (foldApps (.const r ls) xs) e) :
    e = foldApps (.const r ls) xs := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepCtx_constSpine_false hm hbody xs hxs _ hs).elim

/-- The context-free readback (`WhRed E`, the Π side) is trivial there too. -/
theorem whRed_constSpine_eq {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {xs : List (Expr Nat)}
    (hxs : ∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
      x ≠ foldApps (.const c us) ys)
    {e : Expr Nat} (h : WhRed E (foldApps (.const r ls) xs) e) :
    e = foldApps (.const r ls) xs := by
  cases h with
  | refl => rfl
  | step hs _ =>
      exact (whStepCtx_constSpine_false (Γ := []) hm hbody xs hxs _
        (whStep_to_whStepCtx hs)).elim

/-! ### §1 — W-K at `trueEnvU`: `True.rec.{2} (λ _. Sort 1) (Sort 0) x ≡ Sort 0` at a
non-canonical proof `x`, stuck for the readback -/

/-- The motive `M = λ _ : True. Sort 1`. -/
def kMot : Expr Nat := .lam (.const 0 []) (.sort (.succ .zero))

/-- `True.rec.{2} M (Sort 0)` — the recursor at its motive and minor, major pending. -/
def kRecHead : Expr Nat := .app (.app (.const 2 [.succ (.succ .zero)]) kMot) (.sort .zero)

/-- `True.rec.{2} M (Sort 0) x`. -/
def kRec (x : Expr Nat) : Expr Nat := .app kRecHead x

/-- The context `[h : True]`. -/
def kVarCtx : LCtx := [.assumption (.const 0 [])]

/-- A closed NON-canonical proof of `True`: `(λ y : True. y) intro`. -/
def kIdTt : Expr Nat := .app (.lam (.const 0 []) (.bvar 0)) (.const 1 [])

def kVarCtx_wf (n : Nat) : CtxWfT trueEnvU n kVarCtx :=
  .assumption [] (.const 0 []) .zero .nil trueEnvUF_ty

/-- `h : True` in `kVarCtx`. -/
def kVar_ty (n : Nat) : HasTyT trueEnvU n kVarCtx (.bvar 0) (.const 0 []) :=
  .bvar _ 0 _ rfl

/-- `(λ y : True. y) intro : True` in every context. -/
def kIdTt_ty {n : Nat} {Γ : LCtx} : HasTyT trueEnvU n Γ kIdTt (.const 0 []) :=
  .app _ _ _ _ _
    (.lam _ _ .zero _ _ trueEnvUF_ty (.bvar _ 0 _ rfl))
    trueEnvUtt_ty

/-- `True.rec.{2} M (Sort 0) : Π (t : True), M t` in every context. -/
def kRecHead_ty {n : Nat} {Γ : LCtx} :
    HasTyT trueEnvU n Γ kRecHead (.pi (.const 0 []) (.app kMot (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.const _ 2 [.succ (.succ .zero)] trueRecMemberU rfl rfl rfl)
      trueEnvUM_ty)
    trueEnvUS0_ty

/-- **The K conversion at an arbitrary proof:** for every `x : True`, `Sort 0 ≡ kRec x : Sort 1`
    — `ι`⁻¹ at `intro` (`trueEnvU_ci`), then `ConvT.app (refl kRecHead) (irr intro x)`
    retyped along `βK` (`trueEnvU_betaK`). -/
def kRec_conv_sort {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) :
    ConvT trueEnvU n Γ (.sort .zero) (kRec x) (.sort (.succ .zero)) :=
  .trans _ _ _ _ _ (.symm _ _ _ _ trueEnvU_ci)
    (.tyConv _ _ _ _ _ _
      (.app _ _ _ _ _ _ _
        (.refl _ _ _ kRecHead_ty)
        (.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty hx))
      trueEnvU_betaK)

def kRec_tyConvT {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) :
    TyConvT trueEnvU n Γ (.sort .zero) (kRec x) :=
  .of _ _ _ _ (kRec_conv_sort hx)

/-- `kRec (bvar i)` is stuck for `WhRedCtx` (any context). -/
theorem whRedCtx_kRec_bvar_eq {Γ : LCtx} {i : Nat} {e : Expr Nat}
    (h : WhRedCtx trueEnvU Γ (kRec (.bvar i)) e) : e = kRec (.bvar i) := by
  have hs := whRedCtx_constSpine_eq (xs := [kMot, .sort .zero, .bvar i]) rfl rfl (by
    intro x hx c us ys heq
    have hx' : x = kMot ∨ x = .sort .zero ∨ x = .bvar i := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl
    · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
    · exact foldApps_const_ne_sort _ _ _ _ heq.symm
    · exact foldApps_const_ne_bvar _ _ heq.symm) h
  exact hs

/-- `kRec kIdTt` is stuck for `WhRedCtx` (any context): ι needs a constructor-spine major,
    and the readback never reduces the major. -/
theorem whRedCtx_kRec_idTt_eq {Γ : LCtx} {e : Expr Nat}
    (h : WhRedCtx trueEnvU Γ (kRec kIdTt) e) : e = kRec kIdTt := by
  have hs := whRedCtx_constSpine_eq (xs := [kMot, .sort .zero, kIdTt]) rfl rfl (by
    intro x hx c us ys heq
    have hx' : x = kMot ∨ x = .sort .zero ∨ x = kIdTt := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl
    · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
    · exact foldApps_const_ne_sort _ _ _ _ heq.symm
    · exact lamApp_ne_foldApps_const ys heq) h
  exact hs

/-- **W-K, family readback, at the variable major.** -/
theorem not_lrTypeFamIN_sort_kRec_var (n : Nat) :
    ¬ LRTypeFamIN trueEnvU n kVarCtx (.sort .zero) (kRec (.bvar 0)) .sort := by
  intro h
  cases h with
  | sort _ h' => exact Expr.noConfusion (whRedCtx_kRec_bvar_eq h')

/-- **W-K, family readback, at the closed non-canonical major** (empty context). -/
theorem not_lrTypeFamIN_sort_kRec_idTt (n : Nat) :
    ¬ LRTypeFamIN trueEnvU n [] (.sort .zero) (kRec kIdTt) .sort := by
  intro h
  cases h with
  | sort _ h' => exact Expr.noConfusion (whRedCtx_kRec_idTt_eq h')

/-- §8's typed family fundamental lemma is false at the admitted `trueEnvU`. -/
theorem not_fundamentalLRFamINT_trueEnvU (n : Nat) : ¬ FundamentalLRFamINT trueEnvU n := by
  intro F
  exact not_lrTypeFamIN_sort_kRec_var n
    (F (kVarCtx_wf n) (.sort _ .zero) (kRec_tyConvT (kVar_ty n)) .sort (.sort _ .zero))

/-- ... already in the empty context, at the closed non-canonical proof `kIdTt`. -/
theorem not_fundamentalLRFamINT_trueEnvU_closed (n : Nat) :
    ¬ FundamentalLRFamINT trueEnvU n := by
  intro F
  exact not_lrTypeFamIN_sort_kRec_idTt n
    (F .nil (.sort _ .zero) (kRec_tyConvT kIdTt_ty) .sort (.sort _ .zero))

theorem not_fundamentalLRFamIN_trueEnvU (n : Nat) : ¬ FundamentalLRFamIN trueEnvU n := by
  intro F
  exact not_lrTypeFamIN_sort_kRec_var n
    (F (kVarCtx_wf n) (kRec_tyConvT (kVar_ty n)) .sort (.sort _ .zero))

/-- §7's repaired context-aware relation falls to the same point. -/
theorem not_fundamentalLRICtx_trueEnvU (n : Nat) : ¬ FundamentalLRICtx trueEnvU n := by
  intro F
  have h := F (kVarCtx_wf n) (kRec_tyConvT (kVar_ty n)) .sort (.sort _ .zero)
  cases h with
  | sort _ h' => exact Expr.noConfusion (whRedCtx_kRec_bvar_eq h')

/-- §9's term fundamental lemma (its conversion conjunct at the `.sort` compact). -/
theorem not_fundamentalTermFamIN_trueEnvU (n : Nat) : ¬ FundamentalTermFamIN trueEnvU n := by
  intro F
  have h := (lrTermFamIN_sort_iff _ _ _ _).mp
    (F.2 (kVarCtx_wf n) (kRec_conv_sort (kVar_ty n)) .sort (.sort _ .zero))
  rcases h with hprop | ⟨_, hLR⟩
  · exact not_isNonSortPropCtx_sort _ hprop
  · exact not_lrTypeFamIN_sort_kRec_var n hLR

/-- §10's term fundamental lemma — `main`'s newest named family remainder. -/
theorem not_fundamentalTermFamIND_trueEnvU (n : Nat) : ¬ FundamentalTermFamIND trueEnvU n := by
  intro F
  have h := (lrTermFamIND_sort_iff _ _ _ _).mp
    (F.2 (kVarCtx_wf n) (kRec_conv_sort (kVar_ty n)) .sort (.sort _ .zero))
  rcases h with hprop | ⟨_, hLR⟩
  · exact not_isNonSortPropCtx_sort _ hprop
  · exact not_lrTypeFamIN_sort_kRec_var n hLR

/-! #### §1.4 — the same wall on the Π side (context-free readback) -/

theorem not_lrTypeIN_sort_kRec_var (n : Nat) :
    ¬ LRTypeIN trueEnvU n kVarCtx (.sort .zero) (kRec (.bvar 0)) .sort := by
  intro h
  cases h with
  | sort _ h' =>
      have hs := whRed_constSpine_eq (xs := [kMot, .sort .zero, .bvar 0]) rfl rfl (by
        intro x hx c us ys heq
        have hx' : x = kMot ∨ x = .sort .zero ∨ x = .bvar 0 := by
          simpa using hx
        rcases hx' with rfl | rfl | rfl
        · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
        · exact foldApps_const_ne_sort _ _ _ _ heq.symm
        · exact foldApps_const_ne_bvar _ _ heq.symm) h'
      exact Expr.noConfusion hs

/-- `FundamentalTermD` (`RcicNativePiModelLRTermD`) falls to W-K too (third wall). -/
theorem not_fundamentalTermD_trueEnvU_K (n : Nat) : ¬ FundamentalTermD trueEnvU n := by
  intro F
  rcases F.2 (kVarCtx_wf n) (kRec_conv_sort (kVar_ty n)) .sort (.sort _ .zero) with hP | h
  · exact hP.2 (.succ .zero) rfl
  · rw [LRTermDCore.eq_def] at h
    exact not_lrTypeIN_sort_kRec_var n h.2

/-- `main`'s Π-side `BotPiCpt` / `ApproxDI` restatement falls to W-K too. -/
theorem not_fundamentalLRINBotDI_trueEnvU_K (n : Nat) :
    ¬ PiModelDeltaIotaAudit.FundamentalLRINBotDI trueEnvU n := by
  intro F
  exact not_lrTypeIN_sort_kRec_var n
    (F (kVarCtx_wf n) (.sort _ .zero) (.of _ _ _ _ (kRec_conv_sort (kVar_ty n)))
      .sort PiModelDeltaIotaAudit.BotPiCpt.sort
      (PiModelDeltaIotaAudit.ApproxDI.sort EnvI.bot .zero))

/-! #### §1.5 — η-K: `λ p : True. Sort 0 ≡ True.rec M (Sort 0)` -/

/-- **The η-K conversion** in `kVarCtx`: λ-congruence over the K conversion under the binder,
    then η (`ConvT.eta` at `kRecHead`, closed, so `lift 0 1 kRecHead = kRecHead`). -/
def etaK_conv (n : Nat) :
    ConvT trueEnvU n kVarCtx (.lam (.const 0 []) (.sort .zero)) kRecHead
      (.pi (.const 0 []) (.app kMot (.bvar 0))) :=
  .trans _ _ _ _ _
    (.lam _ _ _ _ _ _ .zero (.refl _ _ _ trueEnvUF_ty)
      (.tyConv _ _ _ _ _ _
        (kRec_conv_sort (.bvar _ 0 _ rfl))
        (.symm _ _ _ _
          (.beta _ _ _ _ _ _ trueEnvUF_ty (.sort _ (.succ .zero)) (.bvar _ 0 _ rfl)))))
    (.eta _ kRecHead _ _ kRecHead_ty)

/-- **η-K refutes §10's term fundamental lemma** at the λ compact `lam [([⊥], sort)]`: its λ
    clause, fed the proof VARIABLE `h` on both sides (related at `True` by the collapse),
    demands `Sort 0 ~ kRec h` at the `.sort` compact, which the readback cannot reach.  The
    Π index is not a proposition (sort uniqueness at `trueEnvU`, `sortUnique_of_inScope`). -/
theorem not_fundamentalTermFamIND_trueEnvU_etaK : ¬ FundamentalTermFamIND trueEnvU 0 := by
  intro F
  have h := F.2 (kVarCtx_wf 0) (etaK_conv 0) (.lam [([.bot], .sort)])
    (ApproxI.lam (fun s hs => by
      rcases List.mem_singleton.mp hs with rfl
      exact .sort _ .zero))
  rcases (lrTermFamIND_lam_iff _ _ _ _ _).mp h with hprop | ⟨A₁, B₁, w, hred, ⟨hΓ₁⟩, ⟨hB₁⟩, hstep⟩
  · obtain ⟨hno, ⟨hP⟩⟩ := hprop
    have hPi2 : HasTyT trueEnvU 0 kVarCtx (.pi (.const 0 []) (.app kMot (.bvar 0)))
        (.sort (.imax .zero (.succ (.succ .zero)))) :=
      .pi _ _ _ _ _ trueEnvUF_ty
        (.app _ _ _ _ _ trueEnvUM_ty (.bvar _ 0 _ rfl))
    have hSU := sortUnique_of_inScope trueEnvUWfT trueEnvUWfT_inScope 0
      trueEnvUWfT (kVarCtx_wf 0) hP hPi2
    have heq := hSU (fun _ => none)
    exact absurd (Option.some.inj heq) (by decide)
  · have hEq := whRedCtx_pi_eq hred
    injection hEq with eA eB
    subst eA; subst eB
    have hLR := hstep ([.bot], .sort) (List.mem_singleton_self _)
      (.bvar 0) (.bvar 0) (kVar_ty 0) (kVar_ty 0) (.refl _ _ _ (kVar_ty 0))
      (fun u hu => by
        rcases List.mem_singleton.mp hu with rfl
        exact lrTermFamIND_bot _ _ _ _)
    rw [lrTermFamIND_sort_iff] at hLR
    rcases hLR with hprop | ⟨_, hLR⟩
    · exact hprop.1 (.succ .zero) (.step (.beta _ _ _) (.refl _))
    · cases hLR with
      | sort _ h' => exact Expr.noConfusion (whRedCtx_kRec_bvar_eq h')

/-! ### §2 — W-K with fields at `andEnvU`, at the Π-compact `piRow` probes -/

/-- The mixed pair's left end is stuck for `WhRedCtx` (any context). -/
theorem whRedCtx_mixAndRedex_eq {Γ : LCtx} {e : Expr Nat}
    (h : WhRedCtx andEnvU Γ mixAndRedex e) : e = mixAndRedex := by
  have hs := whRedCtx_constSpine_eq
    (xs := [.bvar 4, .bvar 3, mixAndMot, mixAndMin, .bvar 0]) rfl rfl (by
    intro x hx c us ys heq
    have hx' : x = .bvar 4 ∨ x = .bvar 3 ∨ x = mixAndMot ∨ x = mixAndMin ∨
        x = .bvar 0 := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · exact foldApps_const_ne_bvar _ _ heq.symm
    · exact foldApps_const_ne_bvar _ _ heq.symm
    · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
    · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
    · exact foldApps_const_ne_bvar _ _ heq.symm) h
  exact hs

theorem not_lrTypeFamIN_pi_mixAnd :
    ¬ LRTypeFamIN andEnvU 0 mixAndCtx mixPi mixAndRedex (.pi .bot []) := by
  intro h
  cases h with
  | pi _ h' _ _ _ _ _ =>
      exact Expr.noConfusion (whRedCtx_mixAndRedex_eq h')

/-- `FundamentalLRFamINT` is false at `andEnvU`, at the very compact `piRowField_of_fundamental
    LRFamINT` probes. -/
theorem not_fundamentalLRFamINT_andEnvU : ¬ FundamentalLRFamINT andEnvU 0 := by
  intro F
  refine mixAnd_conv.elim fun hconv => ?_
  exact not_lrTypeFamIN_pi_mixAnd
    (F Rcic.Domain.Model.PiInversion.mixAndCtx_wf
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (.of _ _ _ _ (.symm _ _ _ _ hconv)) (.pi .bot [])
      (approxI_pi_bot_nil _ _ _))

theorem not_fundamentalTermFamIND_andEnvU : ¬ FundamentalTermFamIND andEnvU 0 := by
  intro F
  refine mixAnd_conv.elim fun hconv => ?_
  have h := F.2 Rcic.Domain.Model.PiInversion.mixAndCtx_wf
    (.symm _ _ _ _ hconv) (.pi .bot []) (approxI_pi_bot_nil _ _ _)
  rw [lrTermFamIND_pi_iff] at h
  rcases h with hprop | ⟨_, hLR⟩
  · exact not_isNonSortPropCtx_sort _ hprop
  · exact not_lrTypeFamIN_pi_mixAnd hLR

/-! ### §3 — The K-aware readback `WhStepK` -/

/-- **K-aware weak-head step.**  `WhStepCtx`, plus:
    * `pmajor` — the **proposition-major ι step**: if `recCall (const r ls) pre canon` is a
      `DerivedIotaU` redex with contractum `rhs`, and the major `x` and `canon` inhabit the same
      proposition `P : Sort 0`, then `recCall (const r ls) pre x` steps to `rhs`.  (On typed terms:
      `irr` at `P`, `ConvT.app`, ι — argument only, not compiled here.)  Field-free constructor:
      K; fieldful: the irr-mixed pair;
    * `recArg` — reduce the last argument of a recursor-headed spine (with `appHead`: any argument,
      in particular the major before ι);
    * `appHead` — congruence in the head. -/
inductive WhStepK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | ctx {a b : Expr Nat} (h : WhStepCtx E Γ a b) : WhStepK E n Γ a b
  | pmajor {r : Nat} {ls : List Level} {pre : List (Expr Nat)} {canon x rhs P : Expr Nat}
      (hI : DerivedIotaU E (recCall (.const r ls) pre canon) rhs)
      (hP : Nonempty (HasTyT E n Γ P (.sort .zero)))
      (hcanon : Nonempty (HasTyT E n Γ canon P))
      (hx : Nonempty (HasTyT E n Γ x P)) :
      WhStepK E n Γ (recCall (.const r ls) pre x) rhs
  | recArg {r : Nat} {ls : List Level} {m : CheckedMember} {pre : List (Expr Nat)}
      {x x' : Expr Nat}
      (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
      (h : WhStepK E n Γ x x') :
      WhStepK E n Γ (foldApps (.const r ls) (pre ++ [x])) (foldApps (.const r ls) (pre ++ [x']))
  | appHead {f f' a : Expr Nat} (h : WhStepK E n Γ f f') :
      WhStepK E n Γ (.app f a) (.app f' a)

/-- Reflexive-transitive closure of `WhStepK`. -/
inductive WhRedK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | refl (e : Expr Nat) : WhRedK E n Γ e e
  | step {a b c : Expr Nat} (h : WhStepK E n Γ a b) (hs : WhRedK E n Γ b c) : WhRedK E n Γ a c

theorem whRedK_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c : Expr Nat}
    (h₁ : WhRedK E n Γ a b) (h₂ : WhRedK E n Γ b c) : WhRedK E n Γ a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem whRedK_of_whRedCtx {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat}
    (h : WhRedCtx E Γ a b) : WhRedK E n Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (.ctx hs) ih

/-- Auxiliary for `whStepK_pi_false`: induction on `WhStepK` with the source equation explicit. -/
theorem whStepK_pi_false_aux {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a e : Expr Nat}
    (h : WhStepK E n Γ a e) : ∀ {A B : Expr Nat}, a = .pi A B → False := by
  induction h with
  | ctx h =>
      intro A B heq
      subst heq
      exact whStepCtx_pi_false h
  | pmajor hI _ _ _ =>
      intro A B heq
      have hs : foldApps (.const _ _) (_ ++ [_]) = .pi A B := heq
      exact foldApps_const_ne_pi _ _ _ _ _ hs
  | recArg _ _ _ =>
      intro A B heq
      exact foldApps_const_ne_pi _ _ _ _ _ heq
  | appHead _ _ =>
      intro A B heq
      exact Expr.noConfusion heq

theorem whStepK_pi_false {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B e : Expr Nat}
    (h : WhStepK E n Γ (.pi A B) e) : False :=
  whStepK_pi_false_aux h rfl

/-- Auxiliary for `whStepK_sort_false`: induction on `WhStepK` with the source equation
    explicit. -/
theorem whStepK_sort_false_aux {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a e : Expr Nat}
    (h : WhStepK E n Γ a e) : ∀ {u : Level}, a = .sort u → False := by
  induction h with
  | ctx h =>
      intro u heq
      subst heq
      exact whStepCtx_sort_false h
  | pmajor hI _ _ _ =>
      intro u heq
      have hs : foldApps (.const _ _) (_ ++ [_]) = .sort u := heq
      exact foldApps_const_ne_sort _ _ _ _ hs
  | recArg _ _ _ =>
      intro u heq
      exact foldApps_const_ne_sort _ _ _ _ heq
  | appHead _ _ =>
      intro u heq
      exact Expr.noConfusion heq

theorem whStepK_sort_false {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level} {e : Expr Nat}
    (h : WhStepK E n Γ (.sort u) e) : False :=
  whStepK_sort_false_aux h rfl

/-- Auxiliary for `whStepK_famApp_false`: induction on `WhStepK`, universally quantified over
    the spine arguments. -/
theorem whStepK_famApp_false_aux {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {a e : Expr Nat} (h : WhStepK E n Γ a e) :
    ∀ (xs : List (Expr Nat)), a = foldApps (.const r ls) xs → False := by
  induction h with
  | ctx h =>
      intro xs heq
      exact whStepCtx_famApp_false_aux hW hm hind h xs heq
  | pmajor hI _ _ _ =>
      intro xs heq
      rcases derivedIotaU_recHead hI with ⟨r₀, ls₀, pre₀, major, m₀, hlhs, hm₀, hrec₀⟩
      have hs : foldApps (.const _ _) (_ ++ [_]) = foldApps (.const r ls) xs := heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj hs
      have hlhs' : foldApps (.const _ _) (_ ++ [_]) =
          foldApps (.const r₀ ls₀) (pre₀ ++ [major]) := hlhs
      obtain ⟨hconst₂, _⟩ := foldApps_const_inj hlhs'
      injection hconst with hr _
      subst hr
      injection hconst₂ with hr₂ _
      subst hr₂
      rw [hm] at hm₀
      injection hm₀ with hmeq
      subst hmeq
      exact MemberClass.noConfusion (hind.symm.trans hrec₀)
  | recArg hm' hrec _ =>
      intro xs heq
      have hs : foldApps (.const _ _) (_ ++ [_]) = foldApps (.const r ls) xs := heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj hs
      injection hconst with hr _
      subst hr
      rw [hm] at hm'
      injection hm' with hmeq
      subst hmeq
      exact MemberClass.noConfusion (hind.symm.trans hrec)
  | appHead _ ih =>
      intro xs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hpre _
        exact ih pre hpre

/-- An admitted family spine takes no `WhStepK` step: `pmajor` and `recArg` are recursor-headed. -/
theorem whStepK_famApp_false {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} (xs : List (Expr Nat)) {e : Expr Nat}
    (h : WhStepK E n Γ (foldApps (.const r ls) xs) e) : False :=
  whStepK_famApp_false_aux hW hm hind h xs rfl

theorem whRedK_pi_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B e : Expr Nat}
    (h : WhRedK E n Γ (.pi A B) e) : e = .pi A B := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepK_pi_false hs).elim

theorem whRedK_sort_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level} {e : Expr Nat}
    (h : WhRedK E n Γ (.sort u) e) : e = .sort u := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepK_sort_false hs).elim

theorem whRedK_famApp_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)} {e : Expr Nat}
    (h : WhRedK E n Γ (foldApps (.const r ls) xs) e) : e = foldApps (.const r ls) xs := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepK_famApp_false hW hm hind xs hs).elim

/-- The K point reduces: one `pmajor` step at `wTrueRecU` (canonical major `intro`). -/
theorem whRedK_kRec {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) :
    WhRedK trueEnvU n Γ (kRec x) (.sort .zero) :=
  .step (.pmajor (.ofU wTrueRecU) ⟨trueEnvUF_ty⟩ ⟨trueEnvUtt_ty⟩ ⟨hx⟩) (.refl _)

/-- The fieldful And point reduces: `pmajor` at `mixAndW` (canonical major `intro a b x y`),
    then two β steps. -/
theorem whRedK_mixAndRedex : WhRedK andEnvU 0 mixAndCtx mixAndRedex mixPi :=
  .step
    (.pmajor (.ofU mixAndW) ⟨mixAndFamTy⟩ ⟨mixAndMkTy⟩ ⟨mixTyH⟩)
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

/-! ### §4 — The restated family relation `LRTypeFamK` and the remainder `FundamentalLRFamKT` -/

/-- **K-aware, demand-guarded family logical relation.**  `LRTypeFamIN` (§8) with
    (1) every readback `WhRedCtx E Γ` replaced by `WhRedK E n Γ` (W-K),
    (2) the Π codomain recursion guarded by `BotDemand s.1` (W-DEMAND), and
    (3) the non-family spine clause asking for convertible reducts, not normal forms. -/
inductive LRTypeFamK (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A A' : Expr Nat) : LRTypeFamK E n Γ A A' .bot
  | sort {Γ : LCtx} {A A' : Expr Nat} {u u' : Level}
      (h : WhRedK E n Γ A (.sort u)) (h' : WhRedK E n Γ A' (.sort u')) :
      LRTypeFamK E n Γ A A' .sort
  | pi {Γ : LCtx} {A A' A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (h : WhRedK E n Γ A (.pi A₁ B₁)) (h' : WhRedK E n Γ A' (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂) (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeFamK E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, PiModelDeltaIotaAudit.BotDemand s.1 →
        LRTypeFamK E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeFamK E n Γ A A' (.pi a f)
  | famSpine {Γ : LCtx} {A A' : Expr Nat} {r : Nat} {m : CheckedMember}
      {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' : Level} {args : List CptI}
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (h : WhRedK E n Γ A (foldApps (.const r ls) xs))
      (h' : WhRedK E n Γ A' (foldApps (.const r ls') xs'))
      (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
      (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
      (hc : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs'))
      (heqN : eqNList ls ls')
      (hlen : xs.length = (piDomsOf m.mtype).length)
      (hlen' : xs'.length = (piDomsOf m.mtype).length)
      (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs') :
      LRTypeFamK E n Γ A A' (.spine r args)
  | otherSpine {Γ : LCtx} {A A' X X' : Expr Nat} {r : Nat} {args : List CptI}
      (hnot : ∀ m, E.members r = some m → m.mclass ≠ .inductiveM)
      (h : WhRedK E n Γ A X) (h' : WhRedK E n Γ A' X')
      (hc : TyConvT E n Γ X X') :
      LRTypeFamK E n Γ A A' (.spine r args)

/-- Closure under K-aware weak-head expansion on both sides. -/
theorem lrTypeFamK_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' X X' : Expr Nat}
    {c : CptI} (hX : WhRedK E n Γ A X) (hX' : WhRedK E n Γ A' X')
    (h : LRTypeFamK E n Γ X X' c) : LRTypeFamK E n Γ A A' c := by
  cases h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort (whRedK_trans hX h) (whRedK_trans hX' h')
  | pi h h' hΓ₁ hdom hcod ra rf =>
      exact .pi (whRedK_trans hX h) (whRedK_trans hX' h') hΓ₁ hdom hcod ra rf
  | famSpine hm hind h h' hty hty' hc heqN hlen hlen' hargs =>
      exact .famSpine hm hind (whRedK_trans hX h) (whRedK_trans hX' h')
        hty hty' hc heqN hlen hlen' hargs
  | otherSpine hnot h h' hc =>
      exact .otherSpine hnot (whRedK_trans hX h) (whRedK_trans hX' h') hc

/-- **The restatement is no stronger:** every `LRTypeFamIN` derivation is an `LRTypeFamK` one. -/
theorem lrTypeFamK_of_lrTypeFamIN {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    {c : CptI} (h : LRTypeFamIN E n Γ A A' c) : LRTypeFamK E n Γ A A' c := by
  induction h with
  | bot Γ A A' => exact .bot _ _ _
  | sort h h' => exact .sort (whRedK_of_whRedCtx h) (whRedK_of_whRedCtx h')
  | pi h h' hΓ₁ hdom hcod ra rf ihra ihrf =>
      exact .pi (whRedK_of_whRedCtx h) (whRedK_of_whRedCtx h') hΓ₁ hdom hcod ihra
        (fun s hs _ => ihrf s hs)
  | famSpine hm hind h h' hty hty' hc heqN hlen hlen' hargs =>
      exact .famSpine hm hind (whRedK_of_whRedCtx h) (whRedK_of_whRedCtx h')
        hty hty' hc heqN hlen hlen' hargs
  | otherSpine hnot h h' _ _ hc =>
      exact .otherSpine hnot (whRedK_of_whRedCtx h) (whRedK_of_whRedCtx h') hc

theorem lrTypeFamK_pi_components {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : LRTypeFamK E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  cases h with
  | pi h h' _ hdom hcod _ _ =>
      have e₁ := whRedK_pi_eq h
      have e₂ := whRedK_pi_eq h'
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

theorem lrTypeFamK_famApp_components {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {args : List CptI}
    (h : LRTypeFamK E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.spine r args)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  cases h with
  | famSpine hm' _ hred hred' _ _ _ heqN hlen hlen' hargs =>
      rw [hm] at hm'
      injection hm' with hm_eq
      subst hm_eq
      have e₁ := whRedK_famApp_eq hW hm hind hred
      have e₂ := whRedK_famApp_eq hW hm hind hred'
      obtain ⟨hconst₁, hxs₁⟩ := foldApps_const_inj e₁.symm
      obtain ⟨hconst₂, hxs₂⟩ := foldApps_const_inj e₂.symm
      injection hconst₁ with _ hls₁
      injection hconst₂ with _ hls₂
      subst hls₁; subst hxs₁; subst hls₂; subst hxs₂
      exact ⟨heqN, hlen.trans hlen'.symm, hargs⟩
  | otherSpine hnot _ _ _ =>
      exact (hnot m hm hind).elim

/-- **The restated typed family fundamental lemma — the single named remainder.** -/
def FundamentalLRFamKT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, ApproxI (ctxEnvI Γ) A c → LRTypeFamK E n Γ A A' c

/-- The old (refuted) statement implies the restated one. -/
theorem fundamentalLRFamKT_of_fundamentalLRFamINT {E : ResolvedEnv} {n : Nat}
    (F : FundamentalLRFamINT E n) : FundamentalLRFamKT E n := by
  intro Γ hΓ A A' u hA hc c hcA
  exact lrTypeFamK_of_lrTypeFamIN (F hΓ hA hc c hcA)

theorem piRowField_of_fundamentalLRFamKT {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRFamKT E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrTypeFamK_pi_components
      (F hΓ hPi hc (.pi .bot []) (approxI_pi_bot_nil (ctxEnvI Γ) A B))

theorem famAppRow_of_fundamentalLRFamKT {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRFamKT E n) : FamAppRowLink E n :=
  fun {_} hΓ {r _ ls _ xs _ _} hm hind hty hc =>
    lrTypeFamK_famApp_components hW hm hind
      (F hΓ hty hc (.spine r (botVecI xs)) (approxI_famApp_botVecI (ctxEnvI _) r ls xs))

theorem famRelevantSlotConv_of_fundamentalLRFamKT {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (F : FundamentalLRFamKT E n) : FamRelevantSlotConv E n :=
  fun {_} hΓ {r _ ls _ xs _ _} hm hind hty hc =>
    relevantSlotConv_of_convArgsT hW hm hind
      (lrTypeFamK_famApp_components hW hm hind
        (F hΓ hty hc (.spine r (botVecI xs)) (approxI_famApp_botVecI (ctxEnvI _) r ls xs))).2.2

/-- **`TypedRowsWf E n` from `EnvWfT E` + `AllBelowScoped` + the single named remainder
    `FundamentalLRFamKT E n`.** -/
theorem typedRowsWf_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv}
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_fundamentalLRFamKT hW F
  famAppRow := famAppRow_of_fundamentalLRFamKT hW F

theorem dt012_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_build hW hBel)
    (piRowField_of_fundamentalLRFamKT hW F) hΓ hA hB

theorem dt010_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRFamKT hW hBel F) hΓ h hs

theorem dt011_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRFamKT hW hBel F) hΓ h hs

theorem dt019_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRFamKT hW hBel F) hΓ hd hlhs

theorem ia024_of_allBelowScoped_fundamentalLRFamKT {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    {n : Nat} (F : FundamentalLRFamKT E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRFamKT hW hBel F)

/-! ### §5 — The K / ι / η-K cases and non-vacuity: every refuting point is satisfied -/

/-- **K at a non-canonical proof major (type level), left side:** the K-aware readback takes the
    `pmajor` step to the ι contractum of any canonical major of the same proposition. -/
theorem lrTypeFamK_pmajor_left {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {pre : List (Expr Nat)} {canon x rhs P X : Expr Nat} {c : CptI}
    (hI : DerivedIotaU E (recCall (.const r ls) pre canon) rhs)
    (hP : HasTyT E n Γ P (.sort .zero)) (hcanon : HasTyT E n Γ canon P)
    (hx : HasTyT E n Γ x P)
    (h : LRTypeFamK E n Γ rhs X c) : LRTypeFamK E n Γ (recCall (.const r ls) pre x) X c :=
  lrTypeFamK_expand
    (.step (.pmajor hI ⟨hP⟩ ⟨hcanon⟩ ⟨hx⟩) (.refl _)) (.refl _) h

theorem lrTypeFamK_pmajor_right {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {pre : List (Expr Nat)} {canon x rhs P X : Expr Nat} {c : CptI}
    (hI : DerivedIotaU E (recCall (.const r ls) pre canon) rhs)
    (hP : HasTyT E n Γ P (.sort .zero)) (hcanon : HasTyT E n Γ canon P)
    (hx : HasTyT E n Γ x P)
    (h : LRTypeFamK E n Γ X rhs c) : LRTypeFamK E n Γ X (recCall (.const r ls) pre x) c :=
  lrTypeFamK_expand (.refl _)
    (.step (.pmajor hI ⟨hP⟩ ⟨hcanon⟩ ⟨hx⟩) (.refl _)) h

/-- **ι at a canonical major (type level).** -/
theorem lrTypeFamK_iota_left {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs X : Expr Nat} {c : CptI} (hI : DerivedIotaU E lhs rhs)
    (h : LRTypeFamK E n Γ rhs X c) : LRTypeFamK E n Γ lhs X c :=
  lrTypeFamK_expand (.step (.ctx (.iota hI)) (.refl _)) (.refl _) h

theorem lrTypeFamK_iota_right {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs X : Expr Nat} {c : CptI} (hI : DerivedIotaU E lhs rhs)
    (h : LRTypeFamK E n Γ X rhs c) : LRTypeFamK E n Γ X lhs c :=
  lrTypeFamK_expand (.refl _) (.step (.ctx (.iota hI)) (.refl _)) h

/-- **Non-vacuity at the K point** (left `Sort 0`, every compact, every proof `x : True`, every
    context) — exactly where `not_fundamentalLRFamINT_trueEnvU` refutes the old row. -/
theorem fundamentalLRFamKT_at_kRec {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (.sort .zero) c) :
    LRTypeFamK trueEnvU n Γ (.sort .zero) (kRec x) c := by
  rcases approxI_sort_inv hc with rfl | rfl
  · exact .bot _ _ _
  · exact .sort (.refl _) (whRedK_kRec hx)

/-- ... and in the reverse direction (left `kRec x`; its compacts are `⊥` or recursor spines). -/
theorem fundamentalLRFamKT_at_kRec_symm {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (kRec x) c) :
    LRTypeFamK trueEnvU n Γ (kRec x) (.sort .zero) c := by
  have hc' : ApproxI (ctxEnvI Γ)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, x]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact .bot _ _ _
  · exact .otherSpine
      (fun m hm hind => by
        have e' : trueRecMemberU = m := Option.some.inj hm
        subst e'
        exact MemberClass.noConfusion hind)
      (whRedK_kRec hx) (.refl _) (.refl _ _)

/-- **Non-vacuity at the fieldful And point** (left `Sort 0 → Sort 0`, every compact). -/
theorem fundamentalLRFamKT_at_mixAnd (c : CptI)
    (hc : ApproxI (ctxEnvI mixAndCtx) mixPi c) :
    LRTypeFamK andEnvU 0 mixAndCtx mixPi mixAndRedex c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact .bot _ _ _
  · have hΓ₁ : CtxWfT andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx) :=
      .assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort _ .zero)
    have rf : ∀ s ∈ f, PiModelDeltaIotaAudit.BotDemand s.1 →
        LRTypeFamK andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx)
          (.sort .zero) (.sort .zero) s.2 := fun s hs _ => by
      rcases approxI_sort_inv (hB s hs) with h | h
      · rw [h]; exact .bot _ _ _
      · rw [h]; exact .sort (.refl _) (.refl _)
    rcases approxI_sort_inv hA with rfl | rfl
    · exact .pi (.refl _) whRedK_mixAndRedex hΓ₁ (.refl _ _) (.refl _ _) (.bot _ _ _) rf
    · exact .pi (.refl _) whRedK_mixAndRedex hΓ₁ (.refl _ _) (.refl _ _)
        (.sort (.refl _) (.refl _)) rf

theorem fundamentalLRFamKT_at_mixAnd_symm (c : CptI)
    (hc : ApproxI (ctxEnvI mixAndCtx) mixAndRedex c) :
    LRTypeFamK andEnvU 0 mixAndCtx mixAndRedex mixPi c := by
  have hc' : ApproxI (ctxEnvI mixAndCtx)
      (foldApps (.const 2 [.succ (.succ .zero)])
        [.bvar 4, .bvar 3, mixAndMot, mixAndMin, .bvar 0]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact .bot _ _ _
  · exact .otherSpine
      (fun m hm hind => by
        have e' : andRecMemberU = m := Option.some.inj hm
        subst e'
        exact MemberClass.noConfusion hind)
      whRedK_mixAndRedex (.refl _) (.refl _ _)

/-- **Non-vacuity at W-DEMAND** (`idPiProp`, every compact, every `E`, `n`). -/
theorem fundamentalLRFamKT_at_idPiProp (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI []) PiModelDeltaIotaAudit.idPiProp c) :
    LRTypeFamK E n [] PiModelDeltaIotaAudit.idPiProp PiModelDeltaIotaAudit.idPiProp c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact .bot _ _ _
  · have hΓ₁ : CtxWfT E n [.assumption (.sort .zero)] :=
      .assumption _ _ _ .nil (.sort _ .zero)
    have rf : ∀ s ∈ f, PiModelDeltaIotaAudit.BotDemand s.1 →
        LRTypeFamK E n [.assumption (.sort .zero)] (.bvar 0) (.bvar 0) s.2 := by
      intro s hs hbd
      rcases approxI_bvar_inv (hB s hs) with h | hb
      · rw [h]; exact .bot _ _ _
      · have hmem : s.2 ∈ s.1 := hb
        rw [hbd s.2 hmem]
        exact .bot _ _ _
    rcases approxI_sort_inv hA with rfl | rfl
    · exact .pi (.refl _) (.refl _) hΓ₁ (.refl _ _) (.refl _ _) (.bot _ _ _) rf
    · exact .pi (.refl _) (.refl _) hΓ₁ (.refl _ _) (.refl _ _)
        (.sort (.refl _) (.refl _)) rf

/-- **Non-vacuity at W-ZETALOCAL** (`zetaSortCtx`, both directions), composed from §8's landed
    `lrTypeFamIN_zetaSortCtx` / `_symm`. -/
theorem fundamentalLRFamKT_at_zetaSortCtx (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaSortCtx) (.sort .zero) c) :
    LRTypeFamK E n zetaSortCtx (.sort .zero) (.bvar 0) c :=
  lrTypeFamK_of_lrTypeFamIN (lrTypeFamIN_zetaSortCtx E n c hc)

theorem fundamentalLRFamKT_at_zetaSortCtx_symm (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaSortCtx) (.bvar 0) c) :
    LRTypeFamK E n zetaSortCtx (.bvar 0) (.sort .zero) c :=
  lrTypeFamK_of_lrTypeFamIN (lrTypeFamIN_zetaSortCtx_symm E n c hc)

/-- **The η-K demanded output holds in the restated readback:** for every proof `N'` of `True`,
    `(λ p. Sort 0) N ~ True.rec M (Sort 0) N'` at every compact of the left (β on the left, the
    `pmajor` step on the right) — the instance `not_fundamentalTermFamIND_trueEnvU_etaK` refutes
    for the old readback. -/
theorem lrTypeFamK_etaK_app {n : Nat} {Γ : LCtx} {N N' : Expr Nat}
    (hN' : HasTyT trueEnvU n Γ N' (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (.app (.lam (.const 0 []) (.sort .zero)) N) c) :
    LRTypeFamK trueEnvU n Γ (.app (.lam (.const 0 []) (.sort .zero)) N) (.app kRecHead N') c := by
  rcases approxI_app_inv hc with rfl | ⟨g, s, rfl, hf, hsf, _⟩ | ⟨r, args, u, rfl, hf, _⟩
  · exact .bot _ _ _
  · rcases approxI_lam_inv hf with hbot | ⟨f', hg, hbody⟩
    · exact CptI.noConfusion hbot
    · injection hg with hg'
      subst hg'
      rcases approxI_sort_inv (hbody s hsf) with hs2 | hs2
      · rw [hs2]
        exact .bot _ _ _
      · rw [hs2]
        exact .sort (.step (.ctx (.beta _ _ _)) (.refl _)) (whRedK_kRec hN')
  · nomatch hf

#print axioms foldApps_const_ne_bvar
#print axioms lamApp_ne_foldApps_const
#print axioms whStepCtx_constSpine_false_aux
#print axioms whStepCtx_constSpine_false
#print axioms whRedCtx_constSpine_eq
#print axioms whRed_constSpine_eq
#print axioms kMot
#print axioms kRecHead
#print axioms kRec
#print axioms kVarCtx
#print axioms kIdTt
#print axioms kVarCtx_wf
#print axioms kVar_ty
#print axioms kIdTt_ty
#print axioms kRecHead_ty
#print axioms kRec_conv_sort
#print axioms kRec_tyConvT
#print axioms whRedCtx_kRec_bvar_eq
#print axioms whRedCtx_kRec_idTt_eq
#print axioms not_lrTypeFamIN_sort_kRec_var
#print axioms not_lrTypeFamIN_sort_kRec_idTt
#print axioms not_fundamentalLRFamINT_trueEnvU
#print axioms not_fundamentalLRFamINT_trueEnvU_closed
#print axioms not_fundamentalLRFamIN_trueEnvU
#print axioms not_fundamentalLRICtx_trueEnvU
#print axioms not_fundamentalTermFamIN_trueEnvU
#print axioms not_fundamentalTermFamIND_trueEnvU
#print axioms not_lrTypeIN_sort_kRec_var
#print axioms not_fundamentalTermD_trueEnvU_K
#print axioms not_fundamentalLRINBotDI_trueEnvU_K
#print axioms etaK_conv
#print axioms not_fundamentalTermFamIND_trueEnvU_etaK
#print axioms whRedCtx_mixAndRedex_eq
#print axioms not_lrTypeFamIN_pi_mixAnd
#print axioms not_fundamentalLRFamINT_andEnvU
#print axioms not_fundamentalTermFamIND_andEnvU
#print axioms WhStepK
#print axioms WhRedK
#print axioms whRedK_trans
#print axioms whRedK_of_whRedCtx
#print axioms whStepK_pi_false_aux
#print axioms whStepK_pi_false
#print axioms whStepK_sort_false_aux
#print axioms whStepK_sort_false
#print axioms whStepK_famApp_false_aux
#print axioms whStepK_famApp_false
#print axioms whRedK_pi_eq
#print axioms whRedK_sort_eq
#print axioms whRedK_famApp_eq
#print axioms whRedK_kRec
#print axioms whRedK_mixAndRedex
#print axioms LRTypeFamK
#print axioms lrTypeFamK_expand
#print axioms lrTypeFamK_of_lrTypeFamIN
#print axioms lrTypeFamK_pi_components
#print axioms lrTypeFamK_famApp_components
#print axioms FundamentalLRFamKT
#print axioms fundamentalLRFamKT_of_fundamentalLRFamINT
#print axioms piRowField_of_fundamentalLRFamKT
#print axioms famAppRow_of_fundamentalLRFamKT
#print axioms famRelevantSlotConv_of_fundamentalLRFamKT
#print axioms typedRowsWf_of_allBelowScoped_fundamentalLRFamKT
#print axioms dt012_of_allBelowScoped_fundamentalLRFamKT
#print axioms dt010_of_allBelowScoped_fundamentalLRFamKT
#print axioms dt011_of_allBelowScoped_fundamentalLRFamKT
#print axioms dt019_of_allBelowScoped_fundamentalLRFamKT
#print axioms ia024_of_allBelowScoped_fundamentalLRFamKT
#print axioms lrTypeFamK_pmajor_left
#print axioms lrTypeFamK_pmajor_right
#print axioms lrTypeFamK_iota_left
#print axioms lrTypeFamK_iota_right
#print axioms fundamentalLRFamKT_at_kRec
#print axioms fundamentalLRFamKT_at_kRec_symm
#print axioms fundamentalLRFamKT_at_mixAnd
#print axioms fundamentalLRFamKT_at_mixAnd_symm
#print axioms fundamentalLRFamKT_at_idPiProp
#print axioms fundamentalLRFamKT_at_zetaSortCtx
#print axioms fundamentalLRFamKT_at_zetaSortCtx_symm
#print axioms lrTypeFamK_etaK_app

end Rcic.Declarative.NativeValleys.FamModelKAudit
