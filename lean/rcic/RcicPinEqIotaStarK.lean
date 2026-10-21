import rcic.RcicPinEqEraseWf
import rcic.RcicParRedCore
import rcic.RcicParRedIota

set_option maxRecDepth 8192

/-!
# `pinEqT` — the `iotaStarK` Eq pins (F05b, cc on #6421)

Three pins over the erased `EnvWfT eqEnvT` group (`RcicPinEqEraseWf`), the
F05b `ParRedT.iotaStarK` fixtures. `iotaStarK`'s typed gate — the major must
type at the constructor's result `I ps (idx_c f)` — IS the `b ≡ a` side
condition for `Eq`.

(i)  GATE MET (`pinEqGate_met` / `pinEq_convK`): at `q : Eq α a a`, the
     gate premise is a context lookup (`q` types at the ctor's result).
     The derived conversion `rec α a M m a q ⇒ m : M a q` exists as
     `ConvT`: `irr` at the shared `Eq α a a` (its `hp` IS the gate),
     `app`-congruence on the major, `ConvT.iota` at the `refl`-headed
     `iotaLhsOf eqKWitness`, `tyConv` for the index exchange.
     `eqKWitness` is the field-free `IotaWitness`.
(ii) GATE NOT MET (`pinEq_stuck_neutral` / `pinEq_gateNotMet`): at
     `q : Eq α a b` with `b` a DISTINCT bvar (`bvar 1 ≠ bvar 3`), the
     major cannot type at `Eq α a a`. Every `ParRedStar` reduct of
     `rec α a M m b q` keeps the `const 65`-headed bvar spine — ordinary
     ι stays stuck and there is no `ParRedStar` join with `m`.
(iii) THE TOOTH (`pinEq_tooth`): at `q : Eq α a a` the `irr + ι`
     `ConvT` exists while the `ParRedStar` join does not — one-shot, not
     cyclic (`refl` is field-free). The Eq twin of
     `postponeJoinable_false_at_loop`.

`closure_claim` stays 0: fixtures for the gate, not the discharged wall.
-/

namespace Rcic.Declarative

/-! Generic bvar/spine ports needed here (they live in
`RcicIrrPostponeRefuted` behind the Ann chain; the small generic arms are
re-derived inside `EqPin` so this fixture does not import it). -/
namespace EqPin

theorem foldApps_const_ne_of_spine {r : Nat} {ls : List Level} {xs : List (Expr Nat)}
    {e hd : Expr Nat} {tl : List (Expr Nat)}
    (he : appsSpine e = (hd, tl)) (hne : ∀ r0 ls0, hd ≠ .const r0 ls0) :
    e ≠ foldApps (.const r ls) xs := fun h => by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const, he] at hs
  exact hne _ _ (congrArg Prod.fst hs)

theorem foldApps_app_ne_bvar (f a : Expr Nat) :
    (xs : List (Expr Nat)) → {i : Nat} → foldApps (.app f a) xs ≠ .bvar i
  | [], _, h => nomatch h
  | x :: xs, _, h => foldApps_app_ne_bvar (.app f a) x xs h

theorem foldApps_const_ne_bvar {r i : Nat} {ls : List Level} :
    (xs : List (Expr Nat)) → foldApps (.const r ls) xs ≠ .bvar i
  | [], h => nomatch h
  | x :: xs, h => foldApps_app_ne_bvar (.const r ls) x xs h

/-- A free variable whose context slot is not a `letBinding` is a normal
form of one-step `ParRed` (the `bvarZeta` arm dies on the declaration
class). -/
def parRed_bvar_normal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    (hz : ∀ A v, Γ.get? i ≠ some (.letBinding A v)) :
    {e t : Expr Nat} → ParRed E n Γ e t → e = .bvar i → t = .bvar i
  | _, _, .refl _ _, heq => heq
  | _, _, .bvarZeta _ _ _ _ _ hg _, heq => by
      cases heq
      exact absurd hg (hz _ _)
  | _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      absurd heq (foldApps_snoc_ne_bvar _ _ _)
  | _, _, .sortEq _ _ _ _, heq => nomatch heq
  | _, _, .consts _ _ _ _ _, heq => nomatch heq
  | _, _, .delta .., heq => nomatch heq
  | _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .beta .., heq => nomatch heq
  | _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .pi .., heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .zeta .., heq => nomatch heq
  | _, _, .lit _ _, heq => nomatch heq

/-- Star form: a `bvar` at a non-let slot stays that `bvar`. -/
def parRedStar_bvar_normal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    (hz : ∀ A v, Γ.get? i ≠ some (.letBinding A v)) :
    {a c : Expr Nat} → ParRedStar E n Γ a c → a = .bvar i → c = .bvar i
  | _, _, .refl _ _, heq => heq
  | _, _, .tail h s, heq => by
      have h' := parRed_bvar_normal hz h heq
      exact parRedStar_bvar_normal hz s h'

/-- TOTAL `ParRed` inversion on a `const 65`-headed spine at any
environment where member 65 is an OPAQUE member (`m`, `hmem`, `htr`),
for argument lists that contain no constructor-headed spine (`hnf`).
Every step is pointwise congruence: δ dies on opacity, ι dies on `hnf`
(its major IS a `foldApps (const ..)`), β and every other head dies on
the const spine head. Instantiated at `eqRecT` and `heqRecT`. -/
def parRed_recSpine_opaque {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls : List Level}
    (m : CheckedMember) (hmem : E.members 65 = some m)
    (htr : transparent m.mclass = false) :
    {e t : Expr Nat} → ParRed E n Γ e t →
    (xs : List (Expr Nat)) → e = foldApps (.const 65 ls) xs →
    (∀ x, x ∈ xs → ∀ (r : Nat) (ls' : List Level) (ys : List (Expr Nat)),
      foldApps (.const r ls') ys ≠ x) →
    Σ' (ls' : List Level) (xs' : List (Expr Nat)),
      (t = foldApps (.const 65 ls') xs') ×'
      ParRedArgs E n Γ xs xs'
  | _, _, .refl _ _, xs, heq, _ => ⟨ls, xs, heq, parRedArgs_refl xs⟩
  | _, _, .sortEq _ _ _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .consts _ r0 ls0 ls' _, xs, heq, _ => by
      have hc : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      have hs := congrArg appsSpine heq
      rw [hc, appsSpine_foldApps_const] at hs
      have hfst : (Expr.const r0 ls0) = (Expr.const 65 ls) := congrArg Prod.fst hs
      have hsnd : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      injection hfst with hr0 _
      subst hr0
      subst xs
      exact ⟨ls', [], rfl, .nil _⟩
  | _, _, .bvarZeta _ _ _ _ _ _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .delta _ r0 ls0 m0 _ hres _ htr0, _, heq, _ => by
      have hc : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      have hs := congrArg appsSpine heq
      rw [hc, appsSpine_foldApps_const] at hs
      have hfst : (Expr.const r0 ls0) = (Expr.const 65 ls) := congrArg Prod.fst hs
      injection hfst with hr0 _
      subst hr0
      rw [hmem] at hres
      cases hres
      rw [htr] at htr0
      nomatch htr0
  | _, _, .app _ f0 f0' a0 a0' hf ha, xs, heq, hnf => by
      have happ : appsSpine (.app f0 a0) =
          ((appsSpine f0).1, (appsSpine f0).2 ++ [a0]) := rfl
      have hs := congrArg appsSpine heq
      rw [happ, appsSpine_foldApps_const] at hs
      have hhead : (appsSpine f0).1 = .const 65 ls := congrArg Prod.fst hs
      have hargs : (appsSpine f0).2 ++ [a0] = xs := congrArg Prod.snd hs
      obtain ⟨ls', ys', hf'eq, hys⟩ :=
        parRed_recSpine_opaque m hmem htr hf ((appsSpine f0).2)
          (by rw [← hhead]; exact (foldApps_appsSpine f0).symm)
          (fun x hx r ls0 ys0 => hnf x (hargs ▸ List.mem_append.mpr (.inl hx)) r ls0 ys0)
      refine ⟨ls', ys' ++ [a0'], ?_, ?_⟩
      · rw [hf'eq]
        exact (foldApps_snoc _ _ _).symm
      · rw [← hargs]
        exact parRedArgs_snoc hys ha
  | _, _, .beta .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .lam .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .pi .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .letE .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .zeta .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .iotaSpine _ w2 lsR lsC _ _ pre _ fields _ _ _ _ _ _, xs, heq, hnf => by
      have hsrc : recCall (.const w2.recRef lsR) pre
          (foldApps (.const w2.ctorRef lsC) fields) =
          foldApps (.const w2.recRef lsR)
            (pre ++ [foldApps (.const w2.ctorRef lsC) fields]) := rfl
      have hs := congrArg appsSpine heq
      rw [hsrc, appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
      have hargs : pre ++ [foldApps (.const w2.ctorRef lsC) fields] = xs :=
        congrArg Prod.snd hs
      have hmem2 : foldApps (.const w2.ctorRef lsC) fields ∈ xs :=
        hargs ▸ List.mem_append.mpr (.inr (List.mem_singleton_self _))
      exact absurd rfl (hnf _ hmem2 _ _ _)
  | _, _, .lit _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))

/-- Pointwise `ParRedArgs` on an all-bvar list is the identity (each
argument is a normal free variable at a no-let context). -/
def parRedArgs_bvar_fixed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v)) :
    {xs ys : List (Expr Nat)} → (∀ x ∈ xs, ∃ i, x = .bvar i) →
    ParRedArgs E n Γ xs ys → ys = xs
  | _, _, _, .nil _ => rfl
  | _, _, hbv, .cons h t => by
      obtain ⟨i, hi⟩ := hbv _ (List.mem_cons_self _ _)
      subst hi
      have hy := parRed_bvar_normal (hz i) h rfl
      subst hy
      rw [parRedArgs_bvar_fixed hz
        (fun x0 hx0 => hbv x0 (List.mem_cons_of_mem _ hx0)) t]

/-- The `hnf` premise discharged by all-bvar argument lists. -/
theorem bvars_hnf {xs : List (Expr Nat)}
    (hbv : ∀ x ∈ xs, ∃ i, x = .bvar i) :
    ∀ x ∈ xs, ∀ (r : Nat) (ls' : List Level) (ys : List (Expr Nat)),
      foldApps (.const r ls') ys ≠ x := by
  intro x hx r ls' ys
  obtain ⟨i, hi⟩ := hbv x hx
  subst hi
  exact foldApps_const_ne_bvar ys

/-- The bvar-spine `X`-class: every `ParRedStar` reduct of a
`const 65`-headed spine whose arguments are all bvars keeps the SAME
spine — only the recursor's universe list may drift. Ordinary ι never
gets a constructor-headed major. -/
def parRedStar_rec_bvar_class {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {c : Expr Nat}
    (m : CheckedMember) (hmem : E.members 65 = some m)
    (htr : transparent m.mclass = false)
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v)) {ls : List Level}
    {xs : List (Expr Nat)} (hbv : ∀ x ∈ xs, ∃ i, x = .bvar i) :
    {a : Expr Nat} → ParRedStar E n Γ a c →
    a = foldApps (.const 65 ls) xs →
    Σ' (ls' : List Level), c = foldApps (.const 65 ls') xs
  | _, .refl _ _, heq => ⟨ls, heq⟩
  | _, .tail h s, heq => by
      obtain ⟨ls', xs', hteq, hargs⟩ :=
        parRed_recSpine_opaque m hmem htr h xs heq (bvars_hnf hbv)
      have hxs : xs' = xs := parRedArgs_bvar_fixed hz hbv hargs
      subst hxs
      exact parRedStar_rec_bvar_class m hmem htr hz hbv s hteq

/-- Route-P1's joinability predicate: a common `ParRedStar` reduct. -/
def Joinable (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b : Expr Nat) : Prop :=
  ∃ c, Nonempty (ParRedStar E n Γ a c) ∧ Nonempty (ParRedStar E n Γ b c)

end EqPin

/-! ## contexts and spine terms -/

/-- `p`'s stored type in the join context: `Eq α a a` under `[m, M, a, α]`
— the `iotaStarK` gate premise `q : I ps (idx_c f)` literally. -/
def eqPTy : Expr Nat := foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 2]

/-- `Eq α a a` at the use site `Γ = [p, m, M, a, α]` (`lift 0 1 eqPTy`). -/
def eqPTyAt0 : Expr Nat := foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 3]

/-- the join context `[p : Eq α a a, m : M a (refl α a),
    M : Π b, Eq α a b → Sort (param 0), a : α, α : Sort 1]`. -/
def eqJoinCtx : LCtx :=
  [.assumption eqPTy, .assumption eqMinorT, .assumption eqMotT,
    .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `refl α a` at the join-context positions. -/
def eqReflApp : Expr Nat := foldApps (.const 64 []) [.bvar 4, .bvar 3]

/-- the recursor's pre-major spine `[α, a, M, m, a]` (`b := a`). -/
def eqRecPreJ : List (Expr Nat) :=
  [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 3]

/-- `rec α a M m a` — the redex's function part. -/
def eqRecFive : Expr Nat := foldApps (.const 65 [.param 0]) eqRecPreJ

/-- `Π (p : Eq α a a), M a p` — the redex function's type. -/
def eqMotApPi : Expr Nat :=
  .pi eqPTyAt0 (.app (.app (.bvar 3) (.bvar 4)) (.bvar 0))

/-- `M a p` — the join's type. -/
def eqMotAp : Expr Nat := .app (.app (.bvar 2) (.bvar 3)) (.bvar 0)

/-- `p`'s stored type in the neutral context: `Eq α a b` under
`[b, m, M, a, α]` — `b` is `bvar 0`, `a` is `bvar 3`: DISTINCT bvars. -/
def eqNeutPTy : Expr Nat := foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]

/-- the neutral context `[p : Eq α a b, b : α, m, M, a, α]`. -/
def eqNeutCtx : LCtx :=
  [.assumption eqNeutPTy, .assumption (.bvar 3), .assumption eqMinorT,
    .assumption eqMotT, .assumption (.bvar 0),
    .assumption (.sort (.succ .zero))]

/-- the all-bvar neutral spine `[α, a, M, m, b, p]`. -/
def eqNeutSpine : List (Expr Nat) :=
  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]

/-- `rec α a M m b p` — the gate-not-met redex. -/
def eqNeutRedex : Expr Nat := foldApps (.const 65 [.param 0]) eqNeutSpine

theorem eqJoinCtx_noLet (i : Nat) (A v : Expr Nat) :
    eqJoinCtx.get? i ≠ some (.letBinding A v) := by
  match i with
  | 0 => simp [eqJoinCtx]
  | 1 => simp [eqJoinCtx]
  | 2 => simp [eqJoinCtx]
  | 3 => simp [eqJoinCtx]
  | 4 => simp [eqJoinCtx]
  | n + 5 =>
      intro h
      have hle : eqJoinCtx.length ≤ n + 5 := by
        have : eqJoinCtx.length = 5 := rfl
        omega
      rw [List.get?_eq_none.mpr hle] at h
      exact Option.noConfusion h

theorem eqNeutCtx_noLet (i : Nat) (A v : Expr Nat) :
    eqNeutCtx.get? i ≠ some (.letBinding A v) := by
  match i with
  | 0 => simp [eqNeutCtx]
  | 1 => simp [eqNeutCtx]
  | 2 => simp [eqNeutCtx]
  | 3 => simp [eqNeutCtx]
  | 4 => simp [eqNeutCtx]
  | 5 => simp [eqNeutCtx]
  | n + 6 =>
      intro h
      have hle : eqNeutCtx.length ≤ n + 6 := by
        have : eqNeutCtx.length = 6 := rfl
        omega
      rw [List.get?_eq_none.mpr hle] at h
      exact Option.noConfusion h

theorem eqNeut_b_ne_a : (.bvar 0 : Expr Nat) ≠ .bvar 3 := by decide

/-! ## HasTyT leaves -/

def eqTyα : HasTyT eqEnvT 1 eqJoinCtx (.bvar 4) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 4 _ rfl

def eqTya : HasTyT eqEnvT 1 eqJoinCtx (.bvar 3) (.bvar 4) :=
  HasTyT.bvar _ 3 _ rfl

def eqTyM : HasTyT eqEnvT 1 eqJoinCtx (.bvar 2) (lift 0 3 eqMotT) :=
  HasTyT.bvar _ 2 _ rfl

def eqTym : HasTyT eqEnvT 1 eqJoinCtx (.bvar 1) eqEqLhs :=
  HasTyT.bvar _ 1 _ rfl

/-- THE GATE, met: `q` types at the constructor's result `Eq α a a`
(`I ps (idx_c f)`) by context lookup. -/
def pinEqGate_met : HasTyT eqEnvT 1 eqJoinCtx (.bvar 0) eqPTyAt0 :=
  HasTyT.bvar _ 0 _ rfl

/-- `refl α a : Eq α a a` — the constructor application the gate unifies
the major with. -/
def eqReflTy0 : HasTyT eqEnvT 1 eqJoinCtx (.const 64 [])
    (instantiateLevels [] eqReflT.mtype) :=
  HasTyT.const _ 64 [] eqReflT rfl rfl rfl

def eqReflTy1 : HasTyT eqEnvT 1 eqJoinCtx (.app (.const 64 []) (.bvar 4))
    (.pi (.bvar 4) (foldApps (.const 63 []) [.bvar 5, .bvar 0, .bvar 0])) :=
  HasTyT.app _ _ _ _ _ eqReflTy0 eqTyα

def eqReflTy2 : HasTyT eqEnvT 1 eqJoinCtx eqReflApp eqPTyAt0 :=
  HasTyT.app _ _ _ _ _ eqReflTy1 eqTya

/-- `Eq α a a : Sort 0` — the `irr` Prop premise. -/
def eqFamTy0 : HasTyT eqEnvT 1 eqJoinCtx (.const 63 [])
    (instantiateLevels [] eqFamT.mtype) :=
  HasTyT.const _ 63 [] eqFamT rfl rfl rfl

def eqFamTy1 : HasTyT eqEnvT 1 eqJoinCtx (.app (.const 63 []) (.bvar 4))
    (.pi (.bvar 4) (.pi (.bvar 5) (.sort .zero))) :=
  HasTyT.app _ _ _ _ _ eqFamTy0 eqTyα

def eqFamTy2 : HasTyT eqEnvT 1 eqJoinCtx
    (.app (.app (.const 63 []) (.bvar 4)) (.bvar 3))
    (.pi (.bvar 4) (.sort .zero)) :=
  HasTyT.app _ _ _ _ _ eqFamTy1 eqTya

def eqFamTy3 : HasTyT eqEnvT 1 eqJoinCtx eqPTyAt0 (.sort .zero) :=
  HasTyT.app _ _ _ _ _ eqFamTy2 eqTya

/-- `irr` at the shared `Eq α a a`: `q ≡ refl α a`. The gate is `irr`'s
`hp` premise — proof irrelevance supplies what the named K-ι could not
safely assume. -/
def eqIrr : ConvT eqEnvT 1 eqJoinCtx (.bvar 0) eqReflApp eqPTyAt0 :=
  ConvT.irr _ eqPTyAt0 (.bvar 0) eqReflApp eqFamTy3 pinEqGate_met eqReflTy2

/-- the recursor's spine typing: `rec α a M m a : Π p : Eq α a a, M a p`. -/
def eqRecTy0 : HasTyT eqEnvT 1 eqJoinCtx (.const 65 [.param 0])
    (instantiateLevels [.param 0] eqRecT.mtype) :=
  HasTyT.const _ 65 [.param 0] eqRecT rfl rfl rfl

def eqRecTy1 := HasTyT.app _ _ _ _ _ eqRecTy0 eqTyα
def eqRecTy2 := HasTyT.app _ _ _ _ _ eqRecTy1 eqTya
def eqRecTy3 := HasTyT.app _ _ _ _ _ eqRecTy2 eqTyM
def eqRecTy4 := HasTyT.app _ _ _ _ _ eqRecTy3 eqTym

def eqRecTy5 : HasTyT eqEnvT 1 eqJoinCtx eqRecFive eqMotApPi :=
  HasTyT.app _ _ _ _ _ eqRecTy4 eqTya

/-- the iota lhs typing: `rec α a M m a (refl α a) : M a (refl α a)`. -/
def eqRecLhsTy : HasTyT eqEnvT 1 eqJoinCtx (.app eqRecFive eqReflApp)
    eqEqLhs :=
  HasTyT.app _ _ _ _ _ eqRecTy5 eqReflTy2

/-- `M a : Π p : Eq α a a, Sort (param 0)` — for the `tyConv` exchange. -/
def eqMaTy : HasTyT eqEnvT 1 eqJoinCtx (.app (.bvar 2) (.bvar 3))
    (.pi eqPTyAt0 (.sort (.param 0))) :=
  HasTyT.app _ _ _ _ _ eqTyM eqTya

/-! ## the `refl`-major iota witness -/

/-- The field-free `IotaWitness` at the `refl`-headed major
`Eq.refl α a` (ctor levels `[]`, recursor levels `[param 0]`). -/
def eqKWitness : IotaWitness eqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [.param 0]
  lsC := []
  recMember := eqRecT
  ctorMember := eqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 3]
  fields := []
  ctorParams := [.bvar 4, .bvar 3]
  kinds := []
  minor := .bvar 1
  hlen := rfl
  familyRef := 63
  famMember := eqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
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
  ctorDoms := [.sort (.succ .zero), .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3,
    foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 3]
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-! ## the three pins -/

/-- `app`-congruence: the `irr` conversion lifts the variable major to
the `refl`-headed major inside the redex, at type `M a p`. -/
def eqAppCong : ConvT eqEnvT 1 eqJoinCtx (.app eqRecFive (.bvar 0))
    (.app eqRecFive eqReflApp) eqMotAp :=
  ConvT.app _ eqRecFive eqRecFive (.bvar 0) eqReflApp eqPTyAt0
    (.app (.app (.bvar 3) (.bvar 4)) (.bvar 0))
    (ConvT.refl _ _ _ eqRecTy5) eqIrr

/-- the type exchange: `M a p ≡ M a (refl α a)` at `Sort (param 0)` —
`irr` at the index, `refl` at `M a`. -/
def eqTyX : ConvT eqEnvT 1 eqJoinCtx eqMotAp eqEqLhs (.sort (.param 0)) :=
  ConvT.app _ _ _ (.bvar 0) eqReflApp eqPTyAt0 (.sort (.param 0))
    (ConvT.refl _ _ _ eqMaTy) eqIrr

/-- honest iota: `rec α a M m a (refl α a) ⇒ m` at `M a (refl α a)`,
carried by `DerivedIota eqKWitness` and real `HasTyT` legs — the kernel
ι's contractum, typed. -/
def eqIotaK : ConvT eqEnvT 1 eqJoinCtx
    (.app eqRecFive eqReflApp) (.bvar 1) eqEqLhs :=
  ConvT.iota _ _ _ _ (.of eqKWitness) eqRecLhsTy eqTym

/-- the iota conversion transported to `M a p` by the index exchange. -/
def eqIotaAtP : ConvT eqEnvT 1 eqJoinCtx
    (.app eqRecFive eqReflApp) (.bvar 1) eqMotAp :=
  ConvT.tyConv _ _ _ _ _ (.param 0) eqIotaK (ConvT.symm _ _ _ _ eqTyX)

/-- PIN (i), the join: at `q : Eq α a a` the typed-K gate is met and
`rec α a M m a q ⇒ m : M a q` exists as a `ConvT` — `irr` at the shared
`Eq α a a` + `app`-congruence + `iota` + `tyConv`. THE `iotaStarK`
derived conversion at the Eq fixture. -/
def pinEq_convK :
    Nonempty (ConvT eqEnvT 1 eqJoinCtx (.app eqRecFive (.bvar 0))
      (.bvar 1) eqMotAp) :=
  ⟨ConvT.trans _ _ _ _ _ eqAppCong eqIotaAtP⟩

/-- PIN (ii) part 1: at `q : Eq α a b` (`b` a distinct bvar) every
`ParRedStar` reduct of `rec α a M m b q` keeps the `const 65`-headed
all-bvar spine — ordinary ι is stuck; the recursor is `⇒`-neutral. -/
def pinEq_stuck_neutral {n : Nat} {c : Expr Nat}
    (hR : ParRedStar eqEnvT n eqNeutCtx eqNeutRedex c) :
    Σ' (ls' : List Level),
      c = foldApps (.const 65 ls') eqNeutSpine :=
  EqPin.parRedStar_rec_bvar_class eqRecT rfl rfl (xs := eqNeutSpine)
    eqNeutCtx_noLet
    (by
      intro x hx
      simp only [eqNeutSpine, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨5, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩)
    hR rfl

/-- PIN (ii) part 2, the gate refusal: `rec α a M m b q` and `m` have no
common `ParRedStar` reduct — the all-bvar spine and the minor's `bvar 2`
live in disjoint reduct classes. -/
theorem pinEq_gateNotMet {n : Nat} :
    ¬ EqPin.Joinable eqEnvT n eqNeutCtx eqNeutRedex (.bvar 2) := by
  rintro ⟨c, ⟨hR⟩, ⟨hM⟩⟩
  obtain ⟨ls', hc⟩ := pinEq_stuck_neutral hR
  have hc' : c = .bvar 2 :=
    EqPin.parRedStar_bvar_normal (eqNeutCtx_noLet 2) hM rfl
  rw [hc] at hc'
  exact EqPin.foldApps_const_ne_bvar _ hc'

/-- PIN (iii), the tooth: at `q : Eq α a a` the `irr + ι` `ConvT` exists
while the `ParRedStar` join does not — ordinary ι needs the constructor
major SYNTACTICALLY and `q` is a `bvar`. One-shot, not cyclic (`refl`
is field-free). -/
theorem pinEq_tooth {n : Nat} :
    Nonempty (ConvT eqEnvT 1 eqJoinCtx (.app eqRecFive (.bvar 0))
        (.bvar 1) eqMotAp) ∧
    ¬ EqPin.Joinable eqEnvT n eqJoinCtx (.app eqRecFive (.bvar 0))
      (.bvar 1) :=
  ⟨pinEq_convK, by
    rintro ⟨c, ⟨hR⟩, ⟨hM⟩⟩
    obtain ⟨ls', hc⟩ :=
      EqPin.parRedStar_rec_bvar_class eqRecT rfl rfl
        (xs := [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 3, .bvar 0])
        eqJoinCtx_noLet (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨4, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨0, rfl⟩)
        hR (show (.app eqRecFive (.bvar 0)) =
          foldApps (.const 65 [.param 0])
            [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 3, .bvar 0] from rfl)
    have hc' : c = .bvar 1 :=
      EqPin.parRedStar_bvar_normal (eqJoinCtx_noLet 1) hM rfl
    rw [hc] at hc'
    exact EqPin.foldApps_const_ne_bvar _ hc'⟩

#print axioms pinEqGate_met
#print axioms eqKWitness
#print axioms pinEq_convK
#print axioms pinEq_stuck_neutral
#print axioms pinEq_gateNotMet
#print axioms pinEq_tooth

end Rcic.Declarative
