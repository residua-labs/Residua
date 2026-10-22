import rcic.RcicSynSortRow
import rcic.RcicSynTableK
import rcic.RcicSynTableBuildI
import rcic.RcicSortUniqueRows

/-!
# `RcicSynPiLift` — link B measurement: erased Π-component lifting

The erased Π-inversion leg is landed (`convE_pi_inv_wf`): under `TableWF tbl`,

    ConvMod (EStep tbl) LvlEq (.pi cA cB) (.pi cA' cB')
      ⇒ ConvMod (EStep tbl) LvlEq cA cA'  ∧  ConvMod (EStep tbl) LvlEq cB cB'.

What `piRow`-flavoured consumers still lack is the leg back to the TYPED side —
the "erased component lifting":

    ConvMod (EStep tbl) LvlEq (dlA.eps σ ρ) (drA.eps σ ρ)  ⟹  TyConvT E n Γ A A'
    ConvMod (EStep tbl) LvlEq (dlB.eps σ (d::ρ)) (drB.eps σ (d::ρ))
        ⟹  TyConvT E n (assumption A :: Γ) B B'

This module pins the precise statement, decomposes it into its three real
dependencies, proves the conditional consumer, and gives the inhabited
counterexample for the ungated statement.

## Statement

* `EpsConvReflects tbl E n` — the per-component leg: erased conversion of
  eps-images of sort-typed endpoints reflects to `TyConvT`.
* `PiEraseLift tbl E n` — the row-level demand: from the erased conversion of
  the two Π *surfaces* (exactly the shapes `eps_pi_drop`/`eps_pi_keep` emit),
  obtain `TyConvT Γ A A' ∧ TyConvT (A::Γ) B B'`.  Its bit-coherence premise
  `levelIsZero (σ u) = levelIsZero (σ u')` is what sort-coherence supplies
  (`levelIsZero_iff` turns `eqN (σ u) (σ u')` into the bit equality).

## Dependency table (who consumes the lifting)

| consumer | consumes link B? | what it actually needs |
|---|---|---|
| `sortRow` closer / es cells | **no** | erased `ConvMod`/`CL` chains only; `es_pi`'s ports (`es_pi_ih_dom`/`es_pi_ih_body`) are IH-produced erased edges, never `TyConvT` |
| row 7 `es_lit` gated walls (`litSurfaceCL_lhom_wall`, `litEsubCollapseCL`, #7863) | **no** | surface `CL`s / literal-esub collapse at `LevelHom` |
| row 10 `es_pi` gated walls (`piLeftSurfaceCL_lhom_wall`, `piRightSurfaceCL_lhom_wall`, `thsaLhom_pi_wall`, #7863) | **no** | surface `CL`s / `TransportHeadSortAt` at `LevelHom` |
| `DT012T`'s `prow`, `AnnRowsSupply.piRow` | takes `TyConvT` directly | `TyConvT (Π A B) (Π A' B') → components`; erased lifting is needed only by a supplier that holds *only* erased evidence for the components |
| `PiEraseLift` itself | decomposes | `convE_pi_inv_wf` (landed, `TableWF`) + `PiSlotConvForget` (slot cancellation, named) + `EpsConvReflects` (the residual) |

## Verdict

`EpsConvReflects` is **false as stated, on-cone**: `LevelHom` carries no
`map_param` field, so `collapseParam` (all `.param i ↦ .param 0`) is a
`LevelHom`; it erases `.sort (.param 1)` and `.sort (.param 5)` to the same
`.sort (.param 0)` — `ConvMod.refl` — while `TyConvT` between them is refuted
via `sort_chain_eq` (`SortUnique`, landed at `emptyEnv` by
`sortUnique_of_inScope`) and a discriminating level evaluation.  The instance
is fully inhabited at `emptyEnv`, at **every** rule table — `tableOfK` and
`tableOfI` (the Acc-★ table) included; at `EnvWfT.empty` both are `[]`.

The gate that survives is `EpsLevelFaithful σ` (`eqN`-reflection of the level
map): `id` has it (`epsLevelFaithful_id`), `collapseParam` refutes it
(`epsLevelFaithful_collapseParam_false`).  The gated restatement
`EpsConvReflectsG` is the named residual — **measured, not supplied**.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the statements -/

/-- LINK B, component leg.  Erased conversion of the eps-images of two
    sort-typed derivations reflects to typed conversion of the subjects.
    This is what a `piRow`-flavoured consumer needs after
    `convE_pi_inv_wf` splits the erased Π surface.  FALSE ungated —
    `epsConvReflects_false`. -/
def EpsConvReflects (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp} {A A' : Expr Nat}
    {u u' : Level}
    (dl : TyP E n Γ A (.sort u)) (dr : TyP E n Γ A' (.sort u')),
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) →
    Nonempty (TyConvT E n Γ A A')

/-- The on-cone gate the counterexample isolates: the level map may not
    identify `eqN`-distinct levels through erased sort images. -/
def EpsLevelFaithful (σ : Level → Level) : Prop :=
  ∀ {l l' : Level}, eqN (σ l) (σ l') → eqN l l'

/-- The gated restatement of `EpsConvReflects`: reflection under a
    `LevelHom` σ that is additionally `eqN`-faithful.  Status: OPEN —
    named residual, not a supply. -/
def EpsConvReflectsG (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp} {A A' : Expr Nat}
    {u u' : Level},
    LevelHom σ → EpsLevelFaithful σ →
    (dl : TyP E n Γ A (.sort u)) → (dr : TyP E n Γ A' (.sort u')) →
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) →
    Nonempty (TyConvT E n Γ A A')

/-- The codomain slot leg: cancellation of `piSlot` on the erased side.
    `convE_pi_inv_wf` returns the codomain conversion still wrapped in
    `piSlot`; the forward direction is landed (`convMod_piSlot`), the
    inverse is the named dependency.  Only the same-bit form is needed
    once the domain sort bits agree. -/
def PiSlotConvForget (tbl : List CRule) : Prop :=
  ∀ {b : Bool} {q q' : ETm},
    ConvMod (EStep tbl) LvlEq (piSlot b q) (piSlot b q') →
    ConvMod (EStep tbl) LvlEq q q'

/-- The row-level consumer shape: from the erased conversion of the two
    Π surfaces, recover the typed domain/codomain conversions — the
    output `piRow`-flavoured closers want when their evidence is only
    erased.  The `hbit` premise is the bit-coherence the sortRow/ZSC
    supply is for.  FALSE ungated at the component leg —
    `piEraseLift_false`. -/
def PiEraseLift (tbl : List CRule) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {σ : Level → Level} {ρ : List Disp}
    {A B A' B' : Expr Nat} {u v u' v' : Level},
    (dlA : TyP E n Γ A (.sort u)) → (drA : TyP E n Γ A' (.sort u')) →
    levelIsZero (σ u) = levelIsZero (σ u') →
    (dlB : TyP E n (.assumption A :: Γ) B (.sort v)) →
    (drB : TyP E n (.assumption A :: Γ) B' (.sort v')) →
    ConvMod (EStep tbl) LvlEq
      (.pi (dlA.eps σ ρ)
        (piSlot (levelIsZero (σ u))
          (dlB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))))
      (.pi (drA.eps σ ρ)
        (piSlot (levelIsZero (σ u'))
          (drB.eps σ (binderDisp (levelIsZero (σ u')) :: ρ)))) →
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- Conditional consumer — MEASUREMENT, not a supply: the row-level lift
    decomposes into `convE_pi_inv_wf` (landed) + the named slot leg +
    two instances of the component reflection.  Nothing here assumes
    `EpsConvReflects`; it is taken as a premise. -/
theorem piEraseLift_of_epsConvReflects {tbl : List CRule} {E : ResolvedEnv} {n : Nat}
    (hW : TableWF tbl) (hR : EpsConvReflects tbl E n)
    (hslot : PiSlotConvForget tbl) : PiEraseLift tbl E n := by
  intro Γ σ ρ A B A' B' u v u' v' dlA drA hbit dlB drB h
  obtain ⟨hd, hb⟩ := convE_pi_inv_wf hW h
  refine ⟨hR dlA drA hd, ?_⟩
  rw [hbit] at hb
  exact hR dlB drB (hslot hb)

/-- The gated form is the weaker demand: any unconditional reflection
    would of course supply it.  Included to mark `EpsConvReflectsG` as
    the restated residual, not a new wall. -/
theorem epsConvReflectsG_of_epsConvReflects {tbl E n}
    (h : EpsConvReflects tbl E n) : EpsConvReflectsG tbl E n :=
  fun _ _ dl dr hconv => h dl dr hconv

/-! ## §2 the inhabited counterexample -/

/-- A `LevelHom` with no `map_param` field admits a param-collapsing map:
    every `.param i` goes to `.param 0`, structure preserved. -/
def collapseParam : Level → Level
  | .zero => .zero
  | .succ l => .succ (collapseParam l)
  | .imax a b => .imax (collapseParam a) (collapseParam b)
  | .max a b => .max (collapseParam a) (collapseParam b)
  | .param _ => .param 0

theorem levelHom_collapseParam : LevelHom collapseParam where
  map_zero := rfl
  map_succ := fun _ => rfl
  map_max := fun _ _ => rfl
  map_imax := fun _ _ => rfl

/-- `param 1` and `param 5` are `eqN`-distinct: evaluate at a ρ that
    discriminates them. -/
theorem eqN_param15_false : ¬ eqN (.param 1) (.param 5) := fun h => by
  have hρ := h (fun i => if i = 1 then some 0 else some 7)
  simp only [eval] at hρ
  exact absurd hρ (by decide)

theorem epsLevelFaithful_id : EpsLevelFaithful id := fun h => h

theorem epsLevelFaithful_collapseParam_false : ¬ EpsLevelFaithful collapseParam :=
  fun h => eqN_param15_false (h (fun _ => rfl))

/-- Domain fixture: `sort (param 1) : sort (succ (param 1))` at the empty
    environment/context. -/
def plLiftDL : TyP emptyEnv 0 [] (.sort (.param 1)) (.sort (.succ (.param 1))) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- Right endpoint: `sort (param 5)`. -/
def plLiftDR : TyP emptyEnv 0 [] (.sort (.param 5)) (.sort (.succ (.param 5))) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- Codomain fixture under the left binder: `sort 0 : sort 1`. -/
def plLiftDB : TyP emptyEnv 0 [.assumption (.sort (.param 1))]
    (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- The typed side fails: `sort (param 1)` and `sort (param 5)` are not
    `TyConvT` — `sort_chain_eq` would give `eqN` of the two levels, which
    `eqN_param15_false` refutes. -/
theorem not_tyConvT_sort_param15 :
    ¬ Nonempty (TyConvT emptyEnv 0 [] (.sort (.param 1)) (.sort (.param 5))) :=
  fun ⟨c⟩ =>
    eqN_param15_false
      (F8A2Support.sort_chain_eq (sortUnique_of_inScope EnvWfT.empty trivial 0)
        EnvWfT.empty CtxWfT.nil c)

/-- REFUTATION of the ungated component leg: at the param-collapsing
    `LevelHom` the erased images of `sort (param 1)`/`sort (param 5)`
    coincide (`ConvMod.refl`), while `TyConvT` between them is false.
    Holds at **every** rule table — `tableOfK`/`tableOfI` included. -/
theorem epsConvReflects_false (tbl : List CRule) :
    ¬ EpsConvReflects tbl emptyEnv 0 := fun h =>
  not_tyConvT_sort_param15
    (h (σ := collapseParam) (ρ := []) plLiftDL plLiftDR (.refl _))

/-- The same instance refutes the row-level lift: both Π surfaces erase
    to `.pi (sort (param 0)) (sort 0)` (both bits `false`, so the slots
    are `.keep`/identity), `ConvMod.refl` again, and the demanded domain
    `TyConvT` is false. -/
theorem piEraseLift_false (tbl : List CRule) :
    ¬ PiEraseLift tbl emptyEnv 0 := fun h =>
  not_tyConvT_sort_param15
    (h (σ := collapseParam) (ρ := []) plLiftDL plLiftDR rfl plLiftDB plLiftDB
      (.refl _)).1

/-- Pin: the ungated reflection fails at the K table of the empty env —
    `tableOfK` instantiates the generic refutation. -/
theorem epsConvReflects_tableOfK_false :
    ¬ EpsConvReflects (tableOfK EnvWfT.empty) emptyEnv 0 :=
  epsConvReflects_false _

/-- Pin: same at `tableOfI` — the Acc-★ table of the empty env. -/
theorem epsConvReflects_tableOfI_false :
    ¬ EpsConvReflects (tableOfI EnvWfT.empty) emptyEnv 0 :=
  epsConvReflects_false _

/-- Pin: the row-level lift fails at `tableOfK` as well. -/
theorem piEraseLift_tableOfK_false :
    ¬ PiEraseLift (tableOfK EnvWfT.empty) emptyEnv 0 :=
  piEraseLift_false _

end Rcic.Syn

#print axioms Rcic.Syn.EpsConvReflects
#print axioms Rcic.Syn.EpsLevelFaithful
#print axioms Rcic.Syn.EpsConvReflectsG
#print axioms Rcic.Syn.PiSlotConvForget
#print axioms Rcic.Syn.PiEraseLift
#print axioms Rcic.Syn.piEraseLift_of_epsConvReflects
#print axioms Rcic.Syn.epsConvReflectsG_of_epsConvReflects
#print axioms Rcic.Syn.collapseParam
#print axioms Rcic.Syn.levelHom_collapseParam
#print axioms Rcic.Syn.eqN_param15_false
#print axioms Rcic.Syn.epsLevelFaithful_id
#print axioms Rcic.Syn.epsLevelFaithful_collapseParam_false
#print axioms Rcic.Syn.plLiftDL
#print axioms Rcic.Syn.plLiftDR
#print axioms Rcic.Syn.plLiftDB
#print axioms Rcic.Syn.not_tyConvT_sort_param15
#print axioms Rcic.Syn.epsConvReflects_false
#print axioms Rcic.Syn.piEraseLift_false
#print axioms Rcic.Syn.epsConvReflects_tableOfK_false
#print axioms Rcic.Syn.epsConvReflects_tableOfI_false
#print axioms Rcic.Syn.piEraseLift_tableOfK_false
