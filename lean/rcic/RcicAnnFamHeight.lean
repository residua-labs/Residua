import rcic.RcicAnnEnvWf

/-!
# M2-f (3c) — the repaired `fam` clause: acceptance, and the large-index boundary

M2-f (3c)-0 (#6124) measured two over-demands of the M2-f (3b) clause: its family-telescope
walk `hFldF` (and the constructor walk `hFld`) began at the telescope's first binder, so a
PARAMETER `A : Sort l` had to be valid at the clause's own height (`ht l < k`), and both walks
ranged over EVERY level list. Read at the family's sort `Sort u` (height `ht u`), every
application of a family whose first parameter lives at `ht u ≤ ht l` was related to nothing.

The (3c) clause (`RcicAnnLR`) takes L-RING's repair (D2): the carrier's parameters are fixed
(`ps`, its `nparamsA` leading arguments); the family walk starts AFTER them, the constructor
walks start after the constructors' parameter mirrors instantiated AT them; every level list is
`=ₙ` the carrier's. This file measures the repaired clause.

(1) THE BOUNDARY THAT REMAINS. The index binders are still walked at the clause's height, so a
    family application valid at height `k` whose first index lives in `Sort l` forces
    `ht l < k` (`tyKA_famApp_firstIndexSort_lt`), and one whose first index lives at
    `ht u ≤ ht l` relates nothing at its sort (`LRRelA_famApp_firstIndexSort_refuted`). 05 §7
    bounds the constructor FIELDS by the family's sort (`v ≤ₙ uI`), not its indices: excluding
    such indices is a NEW research-scope condition, stated as the explicit premise
    `SmallIndexProfileA` (which the families' clause of M2-f (4b) carries), not derived from 05.
(2) ACCEPTANCE. At `nparamsA = 1`, (3c)-0's receipt `F (Sort 0)`, `F : Π (A : Sort 1), Sort 1`,
    is related to itself at `Sort 1` (`pinFamF1App_related`: the negation of (3c)-0's
    `pinFamFApp_refuted` at this declaration); so is `G.{0} (Sort 0)`, `G.{u} : Π (A : Sort (succ
    u)), Sort (succ u)` — (3c)-0's level-quantifier shape with its binder a parameter
    (`pinFamGApp_related`). A CONSTRUCTOR WALK THROUGH A PARAMETER MIRROR,
    `box : Π (A : Sort 1), A → Box A`: the walk starts at the field `A`, the mirror instantiated
    at the carrier's parameter `Sort 0`, valid at every positive height (`sortP`), where the
    (3b) walk demanded the mirror's domain `Sort 1` at the clause's height
    (`pinBoxApp_related`). AN INDEX WALK AT TIED LEVELS, `H.{u} : Π (x : Sort u), Sort (succ u)`:
    a small index whose domain mentions the level parameter; at `H.{1} (Sort 0)` the index walk
    holds at the clause's height because its level lists are `=ₙ` the carrier's
    (`pinFamHApp_related`; (3c)-0's level quantifier demanded `Sort L` for EVERY closed `L`).
(3) THE BOUNDARY RECEIPT. The same `F` declared with `nparamsA = 0` — its binder an INDEX of type
    `Sort 1` in a family of sort `Sort 1`, outside `SmallIndexProfileA` — at a well-formed
    environment: the semantic environment and the families' clause `EnvSemIndA` are
    unsatisfiable (`pinFamF0_envSem_false`, `pinFamF0_envSemInd_false`; (3c)-0's chain, now
    exactly this case).

THE PARAMETER COUNT IS DECLARED BY THE GROUP (M2-f (4a)). Every pin's environment is an
`EnvWfA.group` step whose family view (`FamViewA`) builds the stored type from its parameters and
indices and ties `nparamsA` to the parameter count: `F` with one parameter (`pinFamF1ViewA`), the
same `F` with its binder an index (`pinFamF0ViewA`, the boundary receipt's environment), `Box`
with the constructor `box` through its view (one mirror, one plain field). A count the telescope
cannot carry has no view (`pinFamF2_noView`: `F` declared with `nparamsA = 2`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FamHeight
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a type whose normal form is a non-`Prop` sort is valid only above that sort's
    height. -/
theorem tyKA_sort_ht_lt {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {l : Level}
    {R : ExprA → ExprA → Prop} (h : TyKA E I n ρ₀ k LE LT Γ (.sort l) R)
    (hz : isZero l = false) : ht ρ₀ l < k := by
  rcases tyKA_sort_inv h with ⟨_, hk, _⟩ | ⟨hz', _⟩
  · exact hk
  · rw [hz] at hz'
    cases hz'

/-- a Type-level family application valid at height `k` whose family telescope, AFTER the
    carrier's parameters `ps`, opens with a non-`Prop` sort binder `Sort l` (an INDEX
    `x : Sort l`): `ht l < k`, by `hFldF` at the empty index prefix. -/
theorem tyKA_famApp_firstIndexSort_lt {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {A : ExprA} {r : Nat} {ls : List Level} {ps is : List ExprA} {m : CheckedMemberA}
    {l uD vC : Level} {C : ExprA} {R : ExprA → ExprA → Prop}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hps : ps.length = m.nparamsA)
    (hT : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some (.pi (.sort l) uD C vC))
    (hz : isZero l = false) (h : TyKA E I n ρ₀ k LE LT Γ A R) : ht ρ₀ l < k := by
  cases h with
  | prop hA' hn' hP =>
      have e := whTyA_det hA hA' hn hn'
      subst e
      exact absurd hP hnp
  | sortT hA' _ _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | sortP hA' _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA' _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA' hn (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | fam hA' hn' _ hm' _ _ hps' _ _ _ RsF _ _ hFldF _ _ _ _ =>
      have e := whTyA_det hA hA' hn hn'
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er
      subst els
      rw [hm] at hm'
      cases hm'
      obtain ⟨eps, _⟩ := List.append_inj exs (by rw [hps, hps'])
      subst eps
      have hD := hFldF [] (wkOk₀A_nil E I n Γ) ls (.pi (.sort l) uD C vC) [] [] (.sort l) uD C vC
        (eqNListB_refl (whTyA_famApp_bounded hA)) (by rw [map_wkExprA_nil]; exact hT) (.nil _ _ _) rfl
      exact tyKA_sort_ht_lt hD hz
  | stuck hA' hN =>
      have e := whTyA_det hA hA' hn hN.1
      subst e
      exact (hN.2 (by rw [foldAppsA_const_head]; exact ⟨m, hm, hind⟩)).elim

/-- THE LARGE-INDEX BOUNDARY: a Type-level sort `Sort u` relates its elements by validity at
    `ht u`, so a family application whose first INDEX (after the carrier's parameters) lives
    in `Sort l`, `ht u ≤ ht l`, is related at `Sort u` to nothing, at any height. -/
theorem LRRelA_famApp_firstIndexSort_refuted {k : Nat} {Γ : LCtxA} {A B : ExprA} {r : Nat}
    {ls : List Level} {ps is : List ExprA} {m : CheckedMemberA} {u l uD vC : Level} {C : ExprA}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hps : ps.length = m.nparamsA)
    (hT : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some (.pi (.sort l) uD C vC))
    (hz : isZero l = false) (hzu : isZero u = false) (hle : ht ρ₀ u ≤ ht ρ₀ l) :
    ¬ LRRelA E I n ρ₀ k Γ (.sort u) A B := by
  intro h
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eq] at hR
  rcases tyKA_sort_inv hR with ⟨_, hk, e⟩ | ⟨hz', _⟩
  · subst e
    obtain ⟨_, ⟨R', hR'⟩, _⟩ := hab
    rw [LRTyA_eq] at hR'
    exact absurd (tyKA_famApp_firstIndexSort_lt hA hn hm hind hnp hps hT hz hR') (Nat.not_lt.mpr hle)
  · rw [hzu] at hz'
    cases hz'

end FamHeight

/-! ## (1') the small-index profile — the premise the boundary names

`piDomLevelsA` and `SmallIndexProfileA` live in `RcicAnnGroup` (M2-f (4b): the families' clause
reads them below this module). -/

/-! ## (2) acceptance -/

section Accept

/-- a sort is not a Π after any prefix. -/
theorem applyTelA_sort_ne_pi : (pre : List ExprA) → {l : Level} → {D C : ExprA} → {uD vC : Level} →
    applyTelA pre (.sort l) ≠ some (.pi D uD C vC)
  | [], _, _, _, _, _, h => by cases h
  | _ :: _, _, _, _, _, _, h => by cases h

/-- a one-parameter family `Π (A : D), Sort l` has NO index binder: after its parameter, at any
    world and level list, its telescope is a sort. -/
theorem oneParamFam_noIdx {m : CheckedMemberA} {D₀ : ExprA} {u₀ v₀ l₀ : Level}
    (hT0 : m.mtypeA = .pi D₀ u₀ (.sort l₀) v₀) (p : ExprA) (ρ : WkSpecA) (lsF : List Level)
    {TF : ExprA} (hTF : applyTelA ([p].map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF)
    {pre : List ExprA} {D C : ExprA} {uD vC : Level}
    (hT : applyTelA pre TF = some (.pi D uD C vC)) : False := by
  rw [hT0] at hTF
  have h1 : applyTelA ([p].map (wkExprA ρ)) (instantiateLevelsA lsF (.pi D₀ u₀ (.sort l₀) v₀)) =
      some (.sort (instLevel lsF l₀)) := rfl
  rw [h1] at hTF
  cases hTF
  exact applyTelA_sort_ne_pi pre hT

theorem singleton_eq_append_cons {α : Type} {a b : α} {xs ys : List α} (h : [a] = xs ++ b :: ys) :
    xs = [] ∧ a = b ∧ ys = [] := by
  cases xs with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h.1, h.2.symm⟩
  | cons x xs =>
      simp at h

theorem eqNList_nil_left {ls : List Level} (h : eqNList [] ls) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons _ _ => exact h.elim

theorem eqNList_one {L : Level} {ls : List Level} (h : eqNList [L] ls) :
    ∃ L', ls = [L'] ∧ eqN L L' := by
  cases ls with
  | nil => exact h.elim
  | cons L' t =>
      cases t with
      | nil => exact ⟨L', rfl, h.1⟩
      | cons _ _ => exact h.2.elim

/-- the closed parameter `Sort 0` does not move under a weakening. -/
theorem pinSort0_wk (ρ : WkSpecA) : [ExprA.sort .zero].map (wkExprA ρ) = [.sort .zero] := by
  simp [wkExprA_sort]

/-- THE PINS' PARAMETER CONVERSIONS (M2-f (6)): the closed parameter `Sort 0` against a domain
    `Sort l` with `l =ₙ 1` is convertible with itself — the clause's `hpar` at the pins below
    (`F`, `G` and `Box` take `Sort 0` for their one parameter). -/
theorem pinSort0_convArgs {E : ResolvedEnvA} {n : Nat} {Γ : LCtxA} {l : Level}
    (hl : eqN (.succ .zero) l) (u : Level) (B : ExprA) (v : Level) :
    ConvArgsA E noIotaA n Γ (.pi (.sort l) u B v) [.sort .zero] [.sort .zero] :=
  .cons _ _ _ _ _ _ _ _ ⟨convA_of_tyConvA (.refl Γ _ _ (.sort Γ .zero)) (tyConvA_sorts Γ hl)⟩ (.nil _)

/-- the relation `TyKA.sortP` gives `Sort 0`: valid propositions, typed, convertible, with the same
    structure (`PropEqA`, M2-g′). -/
def pinPropRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → ExprA → Prop :=
  fun a b => PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧ Nonempty (HasTyA E I n Γ a (.sort .zero)) ∧
    Nonempty (HasTyA E I n Γ b (.sort .zero)) ∧ Nonempty (ConvA E I n Γ a b (.sort .zero)) ∧
    PropEqA E I n Γ a b

/-- the relation `TyKA.sortT` gives a non-`Prop` sort `Sort l`, at the tied knot. -/
def pinSortRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA)
    (l : Level) : ExprA → ExprA → Prop := fun a b =>
  LREqA E I n ρ₀ (ht ρ₀ l) Γ a b ∧ (∃ R, LRTyA E I n ρ₀ (ht ρ₀ l) Γ a R) ∧
    (∃ R, LRTyA E I n ρ₀ (ht ρ₀ l) Γ b R) ∧ Nonempty (HasTyA E I n Γ a (.sort l)) ∧
    Nonempty (HasTyA E I n Γ b (.sort l)) ∧ Nonempty (ConvA E I n Γ a b (.sort l))

/-! ### `F : Π (A : Sort 1), Sort 1`, declared with `np` parameters -/

/-- (3c)-0's family `F : Π (A : Sort 1), Sort 1`, declared with `np` parameters: `np = 1`
    makes `A` a parameter (this section), `np = 0` an index (section 3). -/
def pinFamFA (np : Nat) : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)), none, np, none⟩

def pinFamFEnvA (np : Nat) : ResolvedEnvA := extendEnvA emptyEnvA 0 (pinFamFA np)

/-- `F (Sort 0)`. -/
def pinFamFAppA : ExprA := .app (.const 0 []) (.sort .zero)

theorem pinFamF_members (np : Nat) : (pinFamFEnvA np).members 0 = some (pinFamFA np) := rfl

theorem pinFamF_ind {np c : Nat} {cm : CheckedMemberA} (h : (pinFamFEnvA np).members c = some cm) :
    cm.mclass = .inductiveM := by
  by_cases hr : c = 0
  · subst hr
    cases h
    rfl
  · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at h

/-- `F`'s type is typed in every environment (sorts only). -/
def pinFamFTypeTy (np : Nat) (E : ResolvedEnvA) (n : Nat) (Γ : LCtxA) :
    HasTyA E noIotaA n Γ (pinFamFA np).mtypeA
      (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  .pi Γ (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort Γ (.succ .zero)) (.sort _ (.succ .zero))

theorem pinFamF_inst0 (np : Nat) :
    instantiateLevelsA [] (pinFamFA np).mtypeA = (pinFamFA np).mtypeA := rfl

/-- `F` itself, at any environment holding it at reference `0`. -/
def pinFamFConstTy {E : ResolvedEnvA} {np : Nat} (hE : E.members 0 = some (pinFamFA np)) (n : Nat)
    (Γ : LCtxA) : HasTyA E noIotaA n Γ (.const 0 [])
      (.pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))) :=
  .const Γ 0 [] (pinFamFA np) _ hE rfl rfl ((pinFamF_inst0 np) ▸ pinFamFTypeTy np _ n Γ)

def pinFamFAppTy {E : ResolvedEnvA} {np : Nat} (hE : E.members 0 = some (pinFamFA np)) (n : Nat)
    (Γ : LCtxA) : HasTyA E noIotaA n Γ pinFamFAppA (.sort (.succ .zero)) :=
  .app Γ (.const 0 []) (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero)) (pinFamFConstTy hE n Γ) (.sort Γ .zero)

theorem pinFamFApp_nf {E : ResolvedEnvA} {np : Nat} (hE : E.members 0 = some (pinFamFA np))
    (Γ : LCtxA) : hStepFnA E noIotaA.fn Γ (foldAppsA (.const 0 []) [.sort .zero]) = none :=
  hStepFnA_constSpine_none (noIotaA_recHead E) hE (Or.inr rfl)
    (fun h => MemberClass.noConfusion h) Γ _ (by rw [foldAppsA_const_head])

theorem pinFamFApp_notProp {E : ResolvedEnvA} {np : Nat} (hE : E.members 0 = some (pinFamFA np))
    (Γ : LCtxA) : ¬ IsPropTy E noIotaA Γ (foldAppsA (.const 0 []) [.sort .zero]) := by
  intro h
  have := ((isPropTy_famApp_iff (u₀ := .succ .zero) hE rfl [] [.sort .zero]).1 h).2.2
  exact Bool.noConfusion this

theorem pinFamF_closed (np : Nat) : EnvClosedA (pinFamFEnvA np) := by
  intro r m hm
  by_cases hr : r = 0
  · subst hr
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm

/-- `F`'s view with its binder a PARAMETER (`nparamsA = 1`). -/
def pinFamF1ViewA : FamViewA (pinFamFA 1) :=
  ⟨[(.sort (.succ .zero), .succ (.succ .zero))], [], .succ .zero, rfl, rfl,
    Or.inr fun _ => Nat.zero_lt_one⟩

/-- `F`'s view with its binder an INDEX (`nparamsA = 0`). -/
def pinFamF0ViewA : FamViewA (pinFamFA 0) :=
  ⟨[], [(.sort (.succ .zero), .succ (.succ .zero))], .succ .zero, rfl, rfl,
    Or.inr fun _ => Nat.zero_lt_one⟩

/-- `F` declared with two parameters has no view: the telescope has one binder. -/
theorem pinFamF2_noView (fv : FamViewA (pinFamFA 2)) : False := by
  have h := congrArg (fun e => (piDomsA e).length) fv.stored
  simp only [piDomsA_piTelA] at h
  rw [List.length_append, List.length_map, List.length_append, fv.nparams] at h
  have h1 : (piDomsA (pinFamFA 2).mtypeA).length = 1 := rfl
  have h0 : (piDomsA (ExprA.sort fv.sort)).length = 0 := rfl
  rw [h1, h0] at h
  exact absurd h (by show ¬ (1 = 2 + fv.indices.length + 0); omega)

/-- the environment is well formed: the group of `F` alone, at its view. -/
def pinFamFEnvWfA (np : Nat) (fv : FamViewA (pinFamFA np)) : EnvWfA noIotaA (pinFamFEnvA np) :=
  .group emptyEnvA 0 (pinFamFA np) (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) .empty rfl rfl
    (fun _ => rfl) (pinFamFTypeTy np emptyEnvA 0 []) rfl fv [] rfl

/-- `F (Sort 0)`'s parameter conversions, `F` declared with its binder a parameter, in any
    environment holding it (`Box`'s too): the level lists `=ₙ []` are `[]`. -/
theorem pinFamF1_selfConv {E : ResolvedEnvA} {n : Nat} {Γ : LCtxA} (ρ : WkSpecA) (lsX : List Level)
    (hlX : eqNListB n [] lsX) :
    ConvArgsA E noIotaA n (wkCtxA ρ Γ) (instantiateLevelsA lsX (pinFamFA 1).mtypeA)
      ([ExprA.sort .zero].map (wkExprA ρ)) ([ExprA.sort .zero].map (wkExprA ρ)) := by
  rw [eqNList_nil_left hlX.1, pinSort0_wk]
  exact pinSort0_convArgs (eqNA_refl _) _ _ _

theorem pinFamF1_tyKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) : ∃ R, TyKA (pinFamFEnvA 1) noIotaA n ρ₀ k LE LT Γ pinFamFAppA R := by
  refine ⟨_, .fam (r := 0) (ls := []) (ps := [.sort .zero]) (is := []) (m := pinFamFA 1)
    (u := .succ .zero) (u₀ := .succ .zero) (whTyA_of_hasTy (pinFamFAppTy (pinFamF_members 1) n Γ))
    (pinFamFApp_nf (pinFamF_members 1) Γ) (pinFamFApp_notProp (pinFamF_members 1) Γ)
    (pinFamF_members 1) rfl rfl rfl rfl rfl
    (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False) ?_ ?_ ?_ ?_ ?_ (fun _ _ => .nil _ _ _) ?_ ?_ ?_ ?_⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'

theorem pinFamF1_eqKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) : EqKA (pinFamFEnvA 1) noIotaA n ρ₀ k LE LT Γ pinFamFAppA pinFamFAppA := by
  refine .fam (r := 0) (ls := []) (ls' := []) (ps := [.sort .zero]) (ps' := [.sort .zero]) (is := [])
    (is' := []) (m := pinFamFA 1) (u₀ := .succ .zero)
    (whTyA_of_hasTy (pinFamFAppTy (pinFamF_members 1) n Γ))
    (whTyA_of_hasTy (pinFamFAppTy (pinFamF_members 1) n Γ)) (pinFamFApp_nf (pinFamF_members 1) Γ)
    (pinFamFApp_nf (pinFamF_members 1) Γ) (pinFamF_members 1) rfl rfl trivial rfl rfl
    (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun _ _ => .nil _ _ _) ⟨.refl _ _⟩
    (fun ρ _ lsX hlX => parConvA_refl (pinFamF1_selfConv ρ lsX hlX)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'

/-- ACCEPTANCE AT A PARAMETER: declared with one parameter, `F (Sort 0)` is related to itself at
    `Sort 1` above that sort's height — (3c)-0's `pinFamFApp_refuted` held at EVERY height over
    the clause of M2-f (3b). -/
theorem pinFamF1App_related (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 1 < k) :
    LRRelA (pinFamFEnvA 1) noIotaA n ρ₀ k Γ (.sort (.succ .zero)) pinFamFAppA pinFamFAppA := by
  have hk1 : ht ρ₀ (.succ .zero) < k := hk
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ .zero))) rfl hk1, ?_⟩
  obtain ⟨R, hR⟩ := pinFamF1_tyKA (k := ht ρ₀ (.succ .zero))
    (LE := fun j _ => LREqA (pinFamFEnvA 1) noIotaA n ρ₀ j)
    (LT := fun j _ => LRTyA (pinFamFEnvA 1) noIotaA n ρ₀ j) n ρ₀ Γ
  refine ⟨?_, ⟨R, ?_⟩, ⟨R, ?_⟩, ⟨pinFamFAppTy (pinFamF_members 1) n Γ⟩,
    ⟨pinFamFAppTy (pinFamF_members 1) n Γ⟩, ⟨.refl _ _ _ (pinFamFAppTy (pinFamF_members 1) n Γ)⟩⟩
  · show LREqA (pinFamFEnvA 1) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA pinFamFAppA
    rw [LREqA_eq]
    exact pinFamF1_eqKA n ρ₀ Γ
  · show LRTyA (pinFamFEnvA 1) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA R
    rw [LRTyA_eq]
    exact hR
  · show LRTyA (pinFamFEnvA 1) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA R
    rw [LRTyA_eq]
    exact hR

/-! ### a polymorphic first parameter: `G.{u} : Π (A : Sort (succ u)), Sort (succ u)` -/

/-- `G.{u} : Π (A : Sort (succ u)), Sort (succ u)`, one universe parameter, declared with one
    parameter: (3c)-0's level-quantifier shape, its binder now a parameter. -/
def pinFamGA : CheckedMemberA :=
  ⟨.inductiveM, 1, .pi (.sort (.succ (.param 0))) (.succ (.succ (.param 0)))
    (.sort (.succ (.param 0))) (.succ (.succ (.param 0))), none, 1, none⟩

def pinFamGEnvA : ResolvedEnvA := extendEnvA emptyEnvA 0 pinFamGA

/-- `G.{0} (Sort 0) : Sort 1`. -/
def pinFamGAppA : ExprA := .app (.const 0 [.zero]) (.sort .zero)

theorem pinFamG_members : pinFamGEnvA.members 0 = some pinFamGA := rfl

theorem pinFamG_ind {c : Nat} {cm : CheckedMemberA} (h : pinFamGEnvA.members c = some cm) :
    cm.mclass = .inductiveM := by
  by_cases hr : c = 0
  · subst hr
    cases h
    rfl
  · simp [pinFamGEnvA, extendEnvA, emptyEnvA, hr] at h

def pinFamGAppTy (n : Nat) (Γ : LCtxA) :
    HasTyA pinFamGEnvA noIotaA n Γ pinFamGAppA (.sort (.succ .zero)) :=
  .app Γ (.const 0 [.zero]) (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero))
    (.const Γ 0 [.zero] pinFamGA _ pinFamG_members rfl rfl
      (show HasTyA _ noIotaA n Γ (instantiateLevelsA [.zero] pinFamGA.mtypeA) _ from
        pinFamFTypeTy 1 _ n Γ))
    (.sort Γ .zero)

theorem pinFamGApp_nf (Γ : LCtxA) :
    hStepFnA pinFamGEnvA noIotaA.fn Γ (foldAppsA (.const 0 [.zero]) [.sort .zero]) = none :=
  hStepFnA_constSpine_none (noIotaA_recHead pinFamGEnvA) pinFamG_members (Or.inr rfl)
    (fun h => MemberClass.noConfusion h) Γ _ (by rw [foldAppsA_const_head])

theorem pinFamGApp_notProp (Γ : LCtxA) :
    ¬ IsPropTy pinFamGEnvA noIotaA Γ (foldAppsA (.const 0 [.zero]) [.sort .zero]) := by
  intro h
  have := ((isPropTy_famApp_iff (u₀ := .succ (.param 0)) pinFamG_members rfl [.zero]
    [.sort .zero]).1 h).2.2
  exact Bool.noConfusion this

/-- `G.{0} (Sort 0)`'s parameter conversions: at `[L] =ₙ [0]` the domain is `Sort (succ L)`. -/
theorem pinFamG_selfConv {n : Nat} {Γ : LCtxA} (ρ : WkSpecA) (lsX : List Level)
    (hlX : eqNListB n [.zero] lsX) :
    ConvArgsA pinFamGEnvA noIotaA n (wkCtxA ρ Γ) (instantiateLevelsA lsX pinFamGA.mtypeA)
      ([ExprA.sort .zero].map (wkExprA ρ)) ([ExprA.sort .zero].map (wkExprA ρ)) := by
  obtain ⟨L, rfl, hL⟩ := eqNList_one hlX.1
  rw [pinSort0_wk]
  exact pinSort0_convArgs (eqNA_succ hL) _ _ _

theorem pinFamG_tyKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) : ∃ R, TyKA pinFamGEnvA noIotaA n ρ₀ k LE LT Γ pinFamGAppA R := by
  refine ⟨_, .fam (r := 0) (ls := [.zero]) (ps := [.sort .zero]) (is := []) (m := pinFamGA)
    (u := .succ .zero) (u₀ := .succ (.param 0)) (whTyA_of_hasTy (pinFamGAppTy n Γ))
    (pinFamGApp_nf Γ) (pinFamGApp_notProp Γ) pinFamG_members rfl rfl rfl rfl rfl
    (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False) ?_ ?_ ?_ ?_ ?_ (fun _ _ => .nil _ _ _) ?_ ?_ ?_ ?_⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'

theorem pinFamG_eqKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) : EqKA pinFamGEnvA noIotaA n ρ₀ k LE LT Γ pinFamGAppA pinFamGAppA := by
  refine .fam (r := 0) (ls := [.zero]) (ls' := [.zero]) (ps := [.sort .zero]) (ps' := [.sort .zero])
    (is := []) (is' := []) (m := pinFamGA) (u₀ := .succ (.param 0)) (whTyA_of_hasTy (pinFamGAppTy n Γ))
    (whTyA_of_hasTy (pinFamGAppTy n Γ)) (pinFamGApp_nf Γ) (pinFamGApp_nf Γ) pinFamG_members rfl rfl
    ⟨eqNA_refl _, trivial⟩ rfl rfl (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => .nil _ _ _) ⟨.refl _ _⟩
    (fun ρ _ lsX hlX => parConvA_refl (pinFamG_selfConv ρ lsX hlX)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamG_ind hcm] at hk'
    cases hk'

/-- ACCEPTANCE AT A POLYMORPHIC PARAMETER: `G.{0} (Sort 0)` is related to itself at `Sort 1`.
    Over the clause of M2-f (3b) the binder `Sort (succ u)` was walked at every level list, which
    no height admits ((3c)-0's `tyKA_famApp_levelQuant_refuted`); here it is a parameter, fixed by
    the carrier and never walked. -/
theorem pinFamGApp_related (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 1 < k) :
    LRRelA pinFamGEnvA noIotaA n ρ₀ k Γ (.sort (.succ .zero)) pinFamGAppA pinFamGAppA := by
  have hk1 : ht ρ₀ (.succ .zero) < k := hk
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ .zero))) rfl hk1, ?_⟩
  obtain ⟨R, hR⟩ := pinFamG_tyKA (k := ht ρ₀ (.succ .zero))
    (LE := fun j _ => LREqA pinFamGEnvA noIotaA n ρ₀ j)
    (LT := fun j _ => LRTyA pinFamGEnvA noIotaA n ρ₀ j) n ρ₀ Γ
  refine ⟨?_, ⟨R, ?_⟩, ⟨R, ?_⟩, ⟨pinFamGAppTy n Γ⟩, ⟨pinFamGAppTy n Γ⟩,
    ⟨.refl _ _ _ (pinFamGAppTy n Γ)⟩⟩
  · show LREqA pinFamGEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamGAppA pinFamGAppA
    rw [LREqA_eq]
    exact pinFamG_eqKA n ρ₀ Γ
  · show LRTyA pinFamGEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamGAppA R
    rw [LRTyA_eq]
    exact hR
  · show LRTyA pinFamGEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamGAppA R
    rw [LRTyA_eq]
    exact hR

/-! ### a constructor walk through a parameter mirror: `box : Π (A : Sort 1), A → Box A` -/

/-- `box : Π (A : Sort 1), A → Box A` (`Box` is `F` declared with one parameter, at reference
    `0`): its first binder the parameter MIRROR, its one field of type `A`. -/
def pinBoxCtorA : CheckedMemberA :=
  ⟨.constructorM, 0, .pi (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.succ .zero) (.app (.const 0 []) (.bvar 1)) (.succ .zero))
    (.imax (.succ .zero) (.succ .zero)), none, 0,
    some (ctorTypeA 0 (canonLevelsA (pinFamFA 1).arity) (.succ .zero)
      [(.sort (.succ .zero), .succ (.succ .zero))] [.plain (.bvar 0) (.succ .zero)] [])⟩

def pinBoxEnvA : ResolvedEnvA := extendEnvA (pinFamFEnvA 1) 1 pinBoxCtorA

theorem pinBox_members : pinBoxEnvA.members 0 = some (pinFamFA 1) := rfl

/-- `box`'s type is typed over `Box` (the mirror `A : Sort 1`, the field `A`, the result
    `Box A`). -/
def pinBoxCtorTy : HasTyA (pinFamFEnvA 1) noIotaA 0 [] pinBoxCtorA.mtypeA
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.succ .zero) (.app (.const 0 []) (.bvar 1)) (.succ .zero))
    (.imax (.succ .zero) (.succ .zero)) (.sort [] (.succ .zero))
    (.pi _ (.bvar 0) (.succ .zero) (.app (.const 0 []) (.bvar 1)) (.succ .zero)
      (.bvar _ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (.sort _ (.succ .zero)))
      (.app _ (.const 0 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
        (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
        (.sort _ (.succ .zero)) (.sort _ (.succ .zero)) (pinFamFConstTy (pinFamF_members 1) 0 _)
        (.bvar _ 1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (.sort _ (.succ .zero)))))

/-- `box`'s view in the base scope: the mirror `A : Sort 1` (the parameter itself), the plain
    field `A` (the parameter local, at sort `1 ≤ 1`), no index. -/
def pinBoxViewA : CtorViewA emptyEnvA noIotaA 0 (pinFamFA 1) pinFamF1ViewA pinBoxCtorA where
  mirrors := [(.sort (.succ .zero), .succ (.succ .zero))]
  fields := [.plain (.bvar 0) (.succ .zero)]
  res := []
  stored := rfl
  mirrorsConv := .cons [] _ _ _ _ [] [] (.refl [] _) (fun _ => rfl) (.nil _)
  typed := .plain _ 0 (.bvar 0) (.succ .zero) [] []
    (.bvar _ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (.sort _ (.succ .zero)))
    (.nil _ 1 [] (.nil (.succ .zero)))
  univ := fun D u h => by
    rcases List.mem_singleton.mp h with ⟨⟩
    exact Or.inr ⟨fun _ => Nat.zero_lt_one, fun ρ x y hx hy => by
      have hy' : eval ρ (.succ .zero) = some y := hy
      rw [hx] at hy'
      cases hy'
      exact Nat.le_refl _⟩
  univI := fun _ _ _ _ h => by cases List.mem_singleton.mp h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinBoxCtorTy⟩⟩

/-- `box` as a constructor of the group `Box`: typed over the family (ConstructorScope), its
    view in the base. -/
def pinBoxGroupCtorA : GroupCtorA noIotaA emptyEnvA 0 (pinFamFA 1) pinFamF1ViewA where
  ref := 1
  member := pinBoxCtorA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => by simp [pinBoxCtorA, liftA]
  u := .imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))
  hT := pinBoxCtorTy
  hlvl := rfl
  view := pinBoxViewA
  hnorm := rfl
  hclN := fun _ => by simp [ctorTypeA, ctorFieldsA, piTelA, paramLocalsA, SubstA.id,
    foldAppsA, appsSpineA, consListA, liftA]
  hlvlN := rfl

/-- the environment `Box`, `box` is well formed: ONE group step. -/
def pinBoxEnvWfA : EnvWfA noIotaA pinBoxEnvA :=
  .group emptyEnvA 0 (pinFamFA 1) (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) .empty rfl rfl
    (fun _ => rfl) (pinFamFTypeTy 1 emptyEnvA 0 []) rfl pinFamF1ViewA [pinBoxGroupCtorA] ⟨rfl, rfl⟩

/-- the shapes the relation reads at `box` are its view's, through the builder's law. -/
theorem pinBox_kinds_view : ctorShapesA 0 (pinFamFA 1).nparamsA pinBoxCtorA.mtypeA = some [.nonrecursive] :=
  pinBoxViewA.shapes rfl

theorem pinBox_ctor {c : Nat} {cm : CheckedMemberA} (h : pinBoxEnvA.members c = some cm)
    (hk : cm.mclass = .constructorM) : c = 1 ∧ cm = pinBoxCtorA := by
  by_cases h1 : c = 1
  · subst h1
    cases h
    exact ⟨rfl, rfl⟩
  · by_cases h0 : c = 0
    · subst h0
      cases h
      cases hk
    · simp [pinBoxEnvA, pinFamFEnvA, extendEnvA, emptyEnvA, h0, h1] at h

theorem pinBox_kinds {kinds : List FieldShape}
    (h : ctorShapesA 0 (pinFamFA 1).nparamsA pinBoxCtorA.mtypeA = some kinds) : kinds = [.nonrecursive] := by
  have h0 : ctorShapesA 0 (pinFamFA 1).nparamsA pinBoxCtorA.mtypeA = some [.nonrecursive] := rfl
  rw [h0] at h
  cases h
  rfl

/-- the carrier's parameter at a world: `Sort 0` does not move. -/
theorem pinBox_ps (ρ : WkSpecA) : [ExprA.sort .zero].map (wkExprA ρ) = [.sort .zero] :=
  pinSort0_wk ρ

/-- `box`'s telescope after its parameter mirror, at the carrier's parameter `Sort 0`: the field
    `Sort 0`, then `Box (Sort 0)`. -/
abbrev pinBoxFieldTelA : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.app (.const 0 []) (.sort .zero)) (.succ .zero)

theorem pinBox_tel (ρ : WkSpecA) :
    applyTelA ([ExprA.sort .zero].map (wkExprA ρ)) (instantiateLevelsA [] pinBoxCtorA.mtypeA) =
      some pinBoxFieldTelA := by
  rw [pinBox_ps]
  rfl

/-- the same telescope read at the normed type — `normA.getD` collapses to the literal
    (`FieldA.norm` is the identity on `.plain` fields). -/
theorem pinBox_telN (ρ : WkSpecA) :
    applyTelA ([ExprA.sort .zero].map (wkExprA ρ))
      (instantiateLevelsA [] (pinBoxCtorA.normA.getD pinBoxCtorA.mtypeA)) =
      some pinBoxFieldTelA := by
  rw [pinBox_ps]
  rfl

/-- `Box (Sort 0)` is valid at every positive height: the constructor walk starts at the field,
    the mirror `A` instantiated at the carrier's parameter `Sort 0`, valid by `sortP`. -/
theorem pinBox_tyKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (hk : 0 < k) (n : Nat)
    (ρ₀ : Nat → Nat) (Γ : LCtxA) : ∃ R, TyKA pinBoxEnvA noIotaA n ρ₀ k LE LT Γ pinFamFAppA R := by
  refine ⟨_, .fam (r := 0) (ls := []) (ps := [.sort .zero]) (is := []) (m := pinFamFA 1)
    (u := .succ .zero) (u₀ := .succ .zero) (whTyA_of_hasTy (pinFamFAppTy pinBox_members n Γ))
    (pinFamFApp_nf pinBox_members Γ) (pinFamFApp_notProp pinBox_members Γ) pinBox_members rfl rfl
    rfl rfl rfl (fun ρ _ _ _ _ => pinPropRelA pinBoxEnvA noIotaA n (wkCtxA ρ Γ))
    (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False) ?_ ?_ ?_ ?_ ?_ (fun _ _ => .nil _ _ _) ?_ ?_ ?_ ?_⟩
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp hlA hlAC hT hw hD
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨rfl, -, rfl⟩ := singleton_eq_append_cons hsp
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    rw [pinBox_telN ρ] at hT
    cases hT
    cases hw
    cases hD
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp hlA hlAC hlCC hT hT' hw hD hD'
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨rfl, -, rfl⟩ := singleton_eq_append_cons hsp
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    obtain rfl := eqNList_nil_left hlCC.1
    rw [pinBox_telN ρ] at hT hT'
    cases hT
    cases hT'
    cases hw
    cases hD
    cases hD'
    exact .sort (whTyA_of_hasTy (.sort _ .zero)) (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _)
      ⟨.refl _ _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h

theorem pinBox_eqKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (hk : 0 < k) (n : Nat)
    (ρ₀ : Nat → Nat) (Γ : LCtxA) : EqKA pinBoxEnvA noIotaA n ρ₀ k LE LT Γ pinFamFAppA pinFamFAppA := by
  refine .fam (r := 0) (ls := []) (ls' := []) (ps := [.sort .zero]) (ps' := [.sort .zero]) (is := [])
    (is' := []) (m := pinFamFA 1) (u₀ := .succ .zero) (whTyA_of_hasTy (pinFamFAppTy pinBox_members n Γ))
    (whTyA_of_hasTy (pinFamFAppTy pinBox_members n Γ)) (pinFamFApp_nf pinBox_members Γ)
    (pinFamFApp_nf pinBox_members Γ) pinBox_members rfl rfl trivial rfl rfl
    (fun ρ _ _ _ _ => pinPropRelA pinBoxEnvA noIotaA n (wkCtxA ρ Γ)) (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => .nil _ _ _) ⟨.refl _ _⟩
    (fun ρ _ lsX hlX => parConvA_refl (pinFamF1_selfConv ρ lsX hlX)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp hlA hlAC hT hw hD
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨rfl, -, rfl⟩ := singleton_eq_append_cons hsp
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    rw [pinBox_telN ρ] at hT
    cases hT
    cases hw
    cases hD
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · intro ρ _ lsF _ _ _ _ _ _ _ _ hTF _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp hlA hlAC hlCC hT hT' hw hD hD'
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨rfl, -, rfl⟩ := singleton_eq_append_cons hsp
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    obtain rfl := eqNList_nil_left hlCC.1
    rw [pinBox_telN ρ] at hT hT'
    cases hT
    cases hT'
    cases hw
    cases hD
    cases hD'
    exact .sort (whTyA_of_hasTy (.sort _ .zero)) (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _)
      ⟨.refl _ _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp hlA hlAC hT hT' hw hD hD'
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨rfl, -, rfl⟩ := singleton_eq_append_cons hsp
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    rw [pinBox_telN ρ] at hT hT'
    cases hT
    cases hT'
    cases hw
    cases hD
    cases hD'
    exact .sort (whTyA_of_hasTy (.sort _ .zero)) (whTyA_of_hasTy (.sort _ .zero)) hk (eqNA_refl _)
      ⟨.refl _ _⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hlA hlAC hT hT' hw hR hR'
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    rw [pinBox_telN ρ] at hT hT'
    cases hT
    cases hT'
    cases hw with
    | plain _ _ _ _ _ _ _ _ _ _ _ _ hs =>
        cases hs
        cases hR
        cases hR'
        rw [pinBox_ps ρ]
        exact ⟨[], [], [], [], _, _, rfl, rfl, ⟨trivial, rfl⟩, ⟨trivial, rfl⟩, rfl, rfl, .nil _ _ _, ⟨.refl _ _⟩⟩
  · intro ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hlA hlAC hlCC hT hT' hT'' hw hR' hR''
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain rfl := eqNList_nil_left hlA
    obtain rfl := eqNList_nil_left hlAC.1
    obtain rfl := eqNList_nil_left hlCC.1
    rw [pinBox_telN ρ] at hT hT' hT''
    cases hT
    cases hT'
    cases hT''
    cases hw with
    | plain _ _ _ _ _ _ _ _ _ _ _ _ hs =>
        cases hs
        cases hR'
        cases hR''
        rw [pinBox_ps ρ]
        exact ⟨[], [], [], [], _, _, rfl, rfl, ⟨trivial, rfl⟩, ⟨trivial, rfl⟩, rfl, rfl, .nil _ _ _, ⟨.refl _ _⟩⟩
  · intro ρ _ lsF _ _ _ _ _ _ _ _ _ _ _ _ _ hTF _ _ hD
    exact (oneParamFam_noIdx rfl _ ρ lsF hTF hD).elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk' _ hkinds hsp
    obtain ⟨rfl, rfl⟩ := pinBox_ctor hcm hk'
    obtain rfl := pinBox_kinds hkinds
    obtain ⟨-, h, -⟩ := singleton_eq_append_cons hsp
    cases h

/-- ACCEPTANCE THROUGH A PARAMETER MIRROR: `Box (Sort 0)` is related to itself at `Sort 1`. The
    (3b) walk began at `box`'s mirror `A : Sort 1` and demanded `Sort 1` valid at the clause's
    height `ht 1` (`tyKA_sort_ht_lt`: no height `1` admits it); the (3c) walk begins at the field,
    whose domain is the mirror instantiated at the carrier's parameter. -/
theorem pinBoxApp_related (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 1 < k) :
    LRRelA pinBoxEnvA noIotaA n ρ₀ k Γ (.sort (.succ .zero)) pinFamFAppA pinFamFAppA := by
  have hk1 : ht ρ₀ (.succ .zero) < k := hk
  have h0 : 0 < ht ρ₀ (.succ .zero) := Nat.zero_lt_one
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ .zero))) rfl hk1, ?_⟩
  obtain ⟨R, hR⟩ := pinBox_tyKA (LE := fun j _ => LREqA pinBoxEnvA noIotaA n ρ₀ j)
    (LT := fun j _ => LRTyA pinBoxEnvA noIotaA n ρ₀ j) h0 n ρ₀ Γ
  refine ⟨?_, ⟨R, ?_⟩, ⟨R, ?_⟩, ⟨pinFamFAppTy pinBox_members n Γ⟩,
    ⟨pinFamFAppTy pinBox_members n Γ⟩, ⟨.refl _ _ _ (pinFamFAppTy pinBox_members n Γ)⟩⟩
  · show LREqA pinBoxEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA pinFamFAppA
    rw [LREqA_eq]
    exact pinBox_eqKA h0 n ρ₀ Γ
  · show LRTyA pinBoxEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA R
    rw [LRTyA_eq]
    exact hR
  · show LRTyA pinBoxEnvA noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) Γ pinFamFAppA R
    rw [LRTyA_eq]
    exact hR

/-! ### an index walk at tied levels: `H.{u} : Π (x : Sort u), Sort (succ u)` -/

/-- `H.{u} : Π (x : Sort u), Sort (succ u)`: one universe parameter, NO parameter, one SMALL
    index whose domain mentions the level parameter (its sort `succ u` is the family's). -/
def pinFamHA : CheckedMemberA :=
  ⟨.inductiveM, 1, .pi (.sort (.param 0)) (.succ (.param 0)) (.sort (.succ (.param 0)))
    (.succ (.succ (.param 0))), none, 0, none⟩

def pinFamHEnvA : ResolvedEnvA := extendEnvA emptyEnvA 0 pinFamHA

/-- `H.{1} (Sort 0) : Sort 2`. -/
def pinFamHAppA : ExprA := .app (.const 0 [.succ .zero]) (.sort .zero)

theorem pinFamH_members : pinFamHEnvA.members 0 = some pinFamHA := rfl

theorem pinFamH_ind {c : Nat} {cm : CheckedMemberA} (h : pinFamHEnvA.members c = some cm) :
    cm.mclass = .inductiveM := by
  by_cases hr : c = 0
  · subst hr
    cases h
    rfl
  · simp [pinFamHEnvA, extendEnvA, emptyEnvA, hr] at h

/-- `H`'s type at a level list `[L]`, typed in every environment. -/
def pinFamHInstTy (E : ResolvedEnvA) (n : Nat) (Γ : LCtxA) (L : Level) :
    HasTyA E noIotaA n Γ (instantiateLevelsA [L] pinFamHA.mtypeA)
      (.sort (.imax (.succ L) (.succ (.succ L)))) :=
  .pi Γ (.sort L) (.succ L) (.sort (.succ L)) (.succ (.succ L)) (.sort Γ L) (.sort _ (.succ L))

def pinFamHAppTy (n : Nat) (Γ : LCtxA) :
    HasTyA pinFamHEnvA noIotaA n Γ pinFamHAppA (.sort (.succ (.succ .zero))) :=
  .app Γ (.const 0 [.succ .zero]) (.sort .zero) (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (.succ (.succ .zero)) (.succ (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
    (.sort _ (.succ (.succ .zero))) (.sort Γ (.succ (.succ .zero)))
    (.const Γ 0 [.succ .zero] pinFamHA _ pinFamH_members rfl rfl (pinFamHInstTy _ n Γ (.succ .zero)))
    (.sort Γ .zero)

theorem pinFamHApp_nf (Γ : LCtxA) :
    hStepFnA pinFamHEnvA noIotaA.fn Γ (foldAppsA (.const 0 [.succ .zero]) [.sort .zero]) = none :=
  hStepFnA_constSpine_none (noIotaA_recHead pinFamHEnvA) pinFamH_members (Or.inr rfl)
    (fun h => MemberClass.noConfusion h) Γ _ (by rw [foldAppsA_const_head])

theorem pinFamHApp_notProp (Γ : LCtxA) :
    ¬ IsPropTy pinFamHEnvA noIotaA Γ (foldAppsA (.const 0 [.succ .zero]) [.sort .zero]) := by
  intro h
  have := ((isPropTy_famApp_iff (u₀ := .succ (.param 0)) pinFamH_members rfl [.succ .zero]
    [.sort .zero]).1 h).2.2
  exact Bool.noConfusion this

/-- `H`'s family telescope at any level list: one index of domain `Sort L`, then a sort. -/
theorem pinFamH_idx {lsF : List Level} {pre : List ExprA} {D C : ExprA} {uD vC : Level}
    (hT : applyTelA pre (instantiateLevelsA lsF pinFamHA.mtypeA) = some (.pi D uD C vC)) :
    pre = [] ∧ D = .sort (instLevel lsF (.param 0)) := by
  cases pre with
  | nil =>
      cases hT
      exact ⟨rfl, rfl⟩
  | cons x rest =>
      have h1 : applyTelA (x :: rest) (instantiateLevelsA lsF pinFamHA.mtypeA) =
          applyTelA rest (.sort (instLevel lsF (.succ (.param 0)))) := rfl
      rw [h1] at hT
      exact (applyTelA_sort_ne_pi rest hT).elim

/-- the index pair of `H.{1} (Sort 0)`: `Sort 0 ≈ Sort 0` at `Sort 1`. -/
theorem pinFamH_idxRel (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) :
    pinSortRelA pinFamHEnvA noIotaA n ρ₀ Γ (.succ .zero) (.sort .zero) (.sort .zero) := by
  have h01 : ht ρ₀ .zero < ht ρ₀ (.succ .zero) := Nat.zero_lt_one
  exact ⟨LREqA_sort_refl Γ h01, LRTyA_sort_valid Γ h01, LRTyA_sort_valid Γ h01, ⟨.sort Γ .zero⟩,
    ⟨.sort Γ .zero⟩, ⟨.refl Γ _ _ (.sort Γ .zero)⟩⟩

/-- `H.{1} (Sort 0)` is valid above height `1`: its index walk reads `Sort L` at level lists
    `[L] =ₙ [1]` only — the carrier's. -/
theorem pinFamH_tyKA (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 1 < k) :
    ∃ R, LRTyA pinFamHEnvA noIotaA n ρ₀ k Γ pinFamHAppA R := by
  apply Exists.intro
  rw [LRTyA_eq]
  refine .fam (r := 0) (ls := [.succ .zero]) (ps := []) (is := [.sort .zero]) (m := pinFamHA)
    (u := .succ (.succ .zero)) (u₀ := .succ (.param 0)) (whTyA_of_hasTy (pinFamHAppTy n Γ))
    (pinFamHApp_nf Γ) (pinFamHApp_notProp Γ) pinFamH_members rfl rfl rfl rfl rfl
    (fun _ _ _ _ _ _ _ => False)
    (fun ρ lsF _ _ => pinSortRelA pinFamHEnvA noIotaA n ρ₀ (wkCtxA ρ Γ) (instLevel lsF (.param 0))) (fun _ _ _ _ _ _ _ _ _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ hl hTF _ hD
    cases hTF
    obtain ⟨rfl, rfl⟩ := pinFamH_idx hD
    obtain ⟨L, rfl, hL⟩ := eqNList_one hl.1
    have hzL : isZero L = false := by rw [← isZero_eqN hL]; rfl
    have hkL : ht ρ₀ L < k := by rw [← ht_of_eqN hL]; exact hk
    exact .sortT (l := L) (whTyA_of_hasTy (.sort _ L)) hzL hkL
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl hll hTF hTF' hw hD hD'
    cases hTF
    cases hTF'
    obtain ⟨rfl, rfl⟩ := pinFamH_idx hD
    cases hw
    obtain ⟨-, rfl⟩ := pinFamH_idx hD'
    obtain ⟨L, rfl, hL⟩ := eqNList_one hl.1
    obtain ⟨L', rfl, hLL'⟩ := eqNList_one hll.1
    have hkL : ht ρ₀ L < k := by rw [← ht_of_eqN hL]; exact hk
    exact .sort (l := L) (l' := L') (whTyA_of_hasTy (.sort _ L)) (whTyA_of_hasTy (.sort _ L')) hkL hLL'
      ⟨tyConvA_sorts _ hLL'⟩
  · intro TF hTF
    cases hTF
    exact .cons _ _ _ _ _ _ _ _ _ _ (pinFamH_idxRel n ρ₀ Γ) (.nil _ _ _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'

theorem pinFamH_eqKA (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 1 < k) :
    LREqA pinFamHEnvA noIotaA n ρ₀ k Γ pinFamHAppA pinFamHAppA := by
  rw [LREqA_eq]
  refine .fam (r := 0) (ls := [.succ .zero]) (ls' := [.succ .zero]) (ps := []) (ps' := [])
    (is := [.sort .zero]) (is' := [.sort .zero]) (m := pinFamHA) (u₀ := .succ (.param 0))
    (whTyA_of_hasTy (pinFamHAppTy n Γ)) (whTyA_of_hasTy (pinFamHAppTy n Γ)) (pinFamHApp_nf Γ)
    (pinFamHApp_nf Γ) pinFamH_members rfl rfl ⟨eqNA_refl _, trivial⟩ rfl rfl
    (fun _ _ _ _ _ _ _ => False)
    (fun ρ lsF _ _ => pinSortRelA pinFamHEnvA noIotaA n ρ₀ (wkCtxA ρ Γ) (instLevel lsF (.param 0))) (fun _ _ _ _ _ _ _ _ _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨.refl _ _⟩ (fun _ _ _ _ => .nil _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ hl hTF _ hD
    cases hTF
    obtain ⟨rfl, rfl⟩ := pinFamH_idx hD
    obtain ⟨L, rfl, hL⟩ := eqNList_one hl.1
    have hzL : isZero L = false := by rw [← isZero_eqN hL]; rfl
    have hkL : ht ρ₀ L < k := by rw [← ht_of_eqN hL]; exact hk
    exact .sortT (l := L) (whTyA_of_hasTy (.sort _ L)) hzL hkL
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl hll hTF hTF' hw hD hD'
    cases hTF
    cases hTF'
    obtain ⟨rfl, rfl⟩ := pinFamH_idx hD
    cases hw
    obtain ⟨-, rfl⟩ := pinFamH_idx hD'
    obtain ⟨L, rfl, hL⟩ := eqNList_one hl.1
    obtain ⟨L', rfl, hLL'⟩ := eqNList_one hll.1
    have hkL : ht ρ₀ L < k := by rw [← ht_of_eqN hL]; exact hk
    exact .sort (l := L) (l' := L') (whTyA_of_hasTy (.sort _ L)) (whTyA_of_hasTy (.sort _ L')) hkL hLL'
      ⟨tyConvA_sorts _ hLL'⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl hTF hTF' _ hD hD'
    cases hTF
    cases hTF'
    obtain ⟨rfl, rfl⟩ := pinFamH_idx hD
    obtain ⟨-, rfl⟩ := pinFamH_idx hD'
    obtain ⟨L, rfl, hL⟩ := eqNList_one hl.1
    have hkL : ht ρ₀ L < k := by rw [← ht_of_eqN hL]; exact hk
    exact .sort (l := L) (l' := L) (whTyA_of_hasTy (.sort _ L)) (whTyA_of_hasTy (.sort _ L)) hkL
      (eqNA_refl _) ⟨.refl _ _⟩
  · intro TF hTF
    cases hTF
    exact .cons _ _ _ _ _ _ _ _ _ _ (pinFamH_idxRel n ρ₀ Γ) (.nil _ _ _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamH_ind hcm] at hk'
    cases hk'

/-- ACCEPTANCE AT TIED LEVELS: `H.{1} (Sort 0)` is related to itself at `Sort 2`. Its index walk
    reads `Sort L` at the level lists `=ₙ [1]` only; over every level list it would need `Sort L`
    valid at the clause's height for every closed `L`, which no height admits (the argument of
    (3c)-0's `tyKA_famApp_levelQuant_refuted` on the clause of M2-f (3b)). -/
theorem pinFamHApp_related (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) {k : Nat} (hk : 2 < k) :
    LRRelA pinFamHEnvA noIotaA n ρ₀ k Γ (.sort (.succ (.succ .zero))) pinFamHAppA pinFamHAppA := by
  have hk2 : ht ρ₀ (.succ (.succ .zero)) < k := hk
  have h12 : 1 < ht ρ₀ (.succ (.succ .zero)) := Nat.one_lt_two
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT (whTyA_of_hasTy (.sort Γ (.succ (.succ .zero)))) rfl hk2,
    ?_⟩
  exact ⟨pinFamH_eqKA n ρ₀ Γ h12, pinFamH_tyKA n ρ₀ Γ h12, pinFamH_tyKA n ρ₀ Γ h12,
    ⟨pinFamHAppTy n Γ⟩, ⟨pinFamHAppTy n Γ⟩, ⟨.refl _ _ _ (pinFamHAppTy n Γ)⟩⟩

/-- `H` is in the small-index profile. -/
theorem pinFamH_small : SmallIndexProfileA pinFamHEnvA := by
  intro r m u₀ hm _ hsh v hv ρ x y hx hy _
  by_cases hr : r = 0
  · subst hr
    cases hm
    cases hsh
    simp only [pinFamHA, piDomLevelsA, List.drop, List.mem_singleton] at hv
    subst hv
    rw [hx] at hy
    cases hy
    exact Nat.le_refl _
  · simp [pinFamHEnvA, extendEnvA, emptyEnvA, hr] at hm

end Accept

/-! ## (3) the boundary receipt: `F` with its binder an INDEX -/

section PinLargeIndex

/-- `F` declared with NO parameter is outside the small-index profile: its index `x : Sort 1`
    has sort `2` in a family of sort `1`. -/
theorem pinFamF0_not_small : ¬ SmallIndexProfileA (pinFamFEnvA 0) := by
  intro h
  have := h 0 (pinFamFA 0) (.succ .zero) rfl rfl rfl (.succ (.succ .zero)) (List.mem_cons_self _ _)
    (fun _ => none) 2 1 rfl rfl Nat.zero_lt_one
  omega

/-- declared with no parameter, `F (Sort 0)` is related to nothing at `Sort 1`, at any height
    (section 1 at `l = u = 1`): the large-index boundary. -/
theorem pinFamF0App_refuted (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (B : ExprA) :
    ¬ LRRelA (pinFamFEnvA 0) noIotaA n ρ₀ k Γ (.sort (.succ .zero)) pinFamFAppA B :=
  LRRelA_famApp_firstIndexSort_refuted (r := 0) (ls := []) (ps := []) (is := [.sort .zero])
    (m := pinFamFA 0) (l := .succ .zero) (uD := .succ (.succ .zero)) (vC := .succ (.succ .zero))
    (C := .sort (.succ .zero))
    (whTyA_of_hasTy (pinFamFAppTy (pinFamF_members 0) n Γ)) (pinFamFApp_nf (pinFamF_members 0) Γ)
    (pinFamF_members 0) rfl (pinFamFApp_notProp (pinFamF_members 0) Γ) rfl rfl rfl rfl (Nat.le_refl _)

/-- THE SEMANTIC ENVIRONMENT FAILS outside the profile: the fundamental theorem would relate the
    derived `F (Sort 0) : Sort 1` to itself. -/
theorem pinFamF0_envSem_false {n : Nat} {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀) :
    ¬ EnvSemA (pinFamFEnvA 0) noIotaA n ρ₀ := by
  intro hS
  obtain ⟨k₀, h⟩ := (fundA (pinFamF_closed 0) noIotaA_lift noIotaA_subst
    (envWfA_normCtorType (pinFamFEnvWfA 0 pinFamF0ViewA))
    (envWfA_normClosed (pinFamFEnvWfA 0 pinFamF0ViewA))
    (noIotaA_recHead (pinFamFEnvA 0)) hS hρ).1 (pinFamFAppTy (pinFamF_members 0) n [])
  have := (h k₀ (Nat.le_refl _) [] SubstA.id SubstA.id ⟨.nil⟩ (ValidSubstA_nil [] _ _)).2
  simp only [substA_id] at this
  exact pinFamF0App_refuted n ρ₀ k₀ [] _ this

/-- so the families' clause `EnvSemIndA` is UNSATISFIABLE at a well-formed environment outside
    the small-index profile: the premise M2-f (4b) carries is not removable. -/
theorem pinFamF0_envSemInd_false {n : Nat} {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀) :
    ¬ EnvSemIndA (pinFamFEnvA 0) noIotaA n ρ₀ := by
  intro hInd
  exact pinFamF0_envSem_false hρ (envSemA_of_envWfA (pinFamFEnvWfA 0 pinFamF0ViewA) noIotaA_lift noIotaA_subst
    noIotaA_levels (noIotaA_recHead _) hρ hInd
    (envSemRecA_of_noRec (fun r m hm => by
      by_cases hr : r = 0
      · subst hr; cases hm; exact fun h => MemberClass.noConfusion h
      · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm)))

end PinLargeIndex

#print axioms Rcic.Declarative.Ann.tyKA_sort_ht_lt
#print axioms Rcic.Declarative.Ann.tyKA_famApp_firstIndexSort_lt
#print axioms Rcic.Declarative.Ann.LRRelA_famApp_firstIndexSort_refuted
#print axioms Rcic.Declarative.Ann.pinFamF1App_related
#print axioms Rcic.Declarative.Ann.pinFamGApp_related
#print axioms Rcic.Declarative.Ann.pinBoxApp_related
#print axioms Rcic.Declarative.Ann.pinFamHApp_related
#print axioms Rcic.Declarative.Ann.pinFamH_small
#print axioms Rcic.Declarative.Ann.pinFamF0_not_small
#print axioms Rcic.Declarative.Ann.pinFamF0App_refuted
#print axioms Rcic.Declarative.Ann.pinFamF0_envSem_false
#print axioms Rcic.Declarative.Ann.pinFamF0_envSemInd_false
#print axioms Rcic.Declarative.Ann.pinFamF2_noView
#print axioms Rcic.Declarative.Ann.pinBox_kinds_view

end Rcic.Declarative.Ann
