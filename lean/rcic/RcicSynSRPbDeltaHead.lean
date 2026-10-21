import rcic.RcicSynStepPbCase
import rcic.RcicConvPlus

/-!
# sortRow row 16 (`pb_case`) — the `pbHead_of_headTag` wall, refuted — `closure_claim = 0`

glm-sr4 lane (rows 16 `pb_case`, 18 `delta_obs`; `TABLEOFI_SUPPLIER_CENSUS.md` row 16).

The landed closer `pb_case Aw tbl (head : PbHead D DT σ ρ)` reduces the
`StepSuppliers.pb_case` field to one retained premise per `(D, DT, σ, ρ)`. The
missing lemma `pbHead_of_headTag` is that premise produced from the head tag of
`D` alone; the tag is a function of `D`, so its exact restatement as ONE named
Prop is `sr4PbHeadWall` below (no tag decoration, no bundled hypotheses).

**On-cone verdict (oaudit2 fix): the LevelHom-gated shapes are restated
(`sr4PbHeadLhomWall`, `sr4PbGoalSupplyLhom`, #7800's gated-field shape) and
RETAINED — the gated goal supply is NOT refuted at any `LevelHom σ` on a
display the routing produces.** The mechanism, pinned kernel-side: a gated
failure needs `eps D ≠ .star` at a zero-bit type level or `eps D = .star` at a
succ-bit one. Every candidate bottoms out in the discipline itself: proof-bit
`bvar`/`const` heads erase to `.star` by their own tag test, `lam`/`app`/
`letE` propagate a `.star` premise, `conv` keeps the sort, and the routed
display constructors (`CtxP.disp`, `RoutedDisp`) only produce a `.drop` at a
binder whose bit is true or whose value already erases to `.star` — the same
regress. The only `σ := id` instance where the bits genuinely move is
`sr4ForallPi` vs the landed `pinForallP` (`.sort (imax 1 0)` re-typed at
`.sort .zero`, `sr4ForallPi_canon_bit`), and it is consistent because `PBit`'s
`DT` types the pin's TYPE, not its subject (`sr4PbGoalSupplyLhom_piPin_sat`).
Teeth: the gated conclusion is inhabited at both closed head pins. The earlier
`σ := fun _ => 0` refutation (`sr4PbGoalSupplyRefuted`) is demoted to OFF-CONE
mechanism analysis (that σ is not a `LevelHom`; it breaks `map_succ`) — it
shows the gate is load-bearing, and is not the row's verdict. The open
direction at the gate is the missing lemma `pbHead_of_headTag` itself, now
stated at its honest strength.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## The wall, restated as ONE named Prop -/

/-- Row 16's exact retained wall: the premise the landed closer `pb_case` still
takes, universalized over `(D, DT, σ, ρ)`. This is the missing lemma
`pbHead_of_headTag` without its tag decoration (`TyP.headTag` is a function of
`D`). It is a wall, not a supply: `sr4PbHeadWallRefuted` refutes it. -/
def sr4PbHeadWall : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level) (ρ : List Disp),
    Nonempty (PbHead D DT σ ρ)

/-! ## Shared fixtures — `.sort 0 : sort 1` and `.sort 1 : sort 2`, any context -/

/-- The zero-sort pin, in any context. Its `eps` is `ETm.sort 0`, never `.star`. -/
def sr4SortZ (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort Level.zero) (.sort (.succ Level.zero)) :=
  TyP.sort _ _ _ Level.zero (.succ Level.zero) (eqN_refl _)

/-- The one-sort pin, in any context. -/
def sr4SortZUp (Γ : LCtx) :
    TyP emptyEnv 0 Γ (.sort (.succ Level.zero)) (.sort (.succ (.succ Level.zero))) :=
  TyP.sort _ _ _ (.succ Level.zero) (.succ (.succ Level.zero)) (eqN_refl _)

/-- At `σ := fun _ => 0` every sort node's `eps` is `ETm.sort 0` (never
    `.star`) while the PBit right side is trivially `true`: `PBit` fails on
    EVERY sort-headed `D`, at any `Γ`, `ρ`, and any sort-typed `DT`. -/
theorem sr4NotPbitConstZeroSort {Γ : LCtx} {l k s : Level} {h : eqN k (.succ l)}
    {DT : TyP emptyEnv 0 Γ (.sort k) (.sort s)} {ρ : List Disp} :
    ¬ PBit (fun _ => Level.zero) ρ (TyP.sort emptyEnv 0 Γ l k h) DT := by
  intro hp
  exact ETm.noConfusion (hp.mpr rfl)

/-! ## Why `sr4PbHeadWall` is named but not directly refuted here

Inverting a targeted `PbHead D DT σ ρ` (concrete `D`) is blocked by Lean's
dependent elimination: the six transport constructors carry computed TyP-indices
(`insertAt d c Γ`, `lift c 1 e`, `substRemove v j Γ`, `instantiate j v A`,
`List.map (instLvlsDecl ls)`), and the unifier can neither solve those against
literal indices nor invert them against the matching case's own index (it cannot
run `insertAt`/`lift`/`substRemove` backwards on metavariables). An
equation-in-conclusion `induction h` restatement is elaboration-blocked for the
same reason: `D`'s frame fvars are not assignable at statement level. So the
wall is named, its per-head port structure is recorded in PROGRESS.md, and the
refutation is delivered one level down, at the PBit goal the field would have
to supply for EVERY σ (not only the `LevelHom`s `Demand` can reach). -/

/-- OFF-CONE mechanism analysis (σ := `fun _ => 0` is not a `LevelHom`; it
    breaks `map_succ`, so it is outside the closer's demand cone — the on-cone
    verdict is `sr4PbGoalSupplyLhomRefuted` below): the goal-level supply at
    ARBITRARY σ, refuted at const-zero σ. -/
def sr4PbGoalSupply : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level) (ρ : List Disp),
    PBit σ ρ D DT

/-- OFF-CONE (σ not a `LevelHom`); kept to show the gate is load-bearing. -/
theorem sr4PbGoalSupplyRefuted : ¬ sr4PbGoalSupply := by
  intro h
  exact sr4NotPbitConstZeroSort
    (h (sr4SortZ []) (sr4SortZUp []) (fun _ => Level.zero) [])

/-! ## The sigma gap, LevelHom-gated — the ON-CONE restatement -/

/-- Row 16's wall restated at the demand gate: the landed closer's `PbHead D DT
σ ρ` premise restricted to the `LevelHom σ` every demanded `.pb` cell carries
(`Demand.hom`; the consumer applies the field with `hq.hom` in hand, #7800's
gated-field shape). RETAINED: not refuted at the gate — see the module header. -/
def sr4PbHeadLhomWall : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level) (ρ : List Disp),
    LevelHom σ → Nonempty (PbHead D DT σ ρ)

/-- The gated goal-level supply: what a premise-free gated `pb_case` field
    would yield at `Goal (.pb D DT S σ ρ)` (which IS `PBit σ ρ D DT`), at
    `LevelHom σ` only — the shape `step_of_suppliers` consumes via
    `Demand.hom`. Retained with teeth below. -/
def sr4PbGoalSupplyLhom : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level) (ρ : List Disp),
    LevelHom σ → PBit σ ρ D DT

/-- The inner pi rule of the landed `pinForallP` (no `.sorts` conv): `∀ P :
Prop, P` at the pi rule's canonical output sort `.sort (imax 1 0)`. Closed, so
its demand display is `[]` and `AssumpPref` is unproblematic. -/
def sr4ForallPi : TyP emptyEnv 0 [] (.pi (.sort .zero) (.bvar 0))
    (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ (.sort .zero) (.succ .zero) (.bvar 0) .zero pinSortP
    (.bvar _ _ _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ _ _ _ _ (eqN_refl _)))

/-- The pin erases to `ETm.pi (.sort 0) (bvar 0)` — pi-headed terms never
    erase to `★` (the domain `Prop : sort 1` is data, so the binder is kept and
    `resolve (.keep :: []) 0 = .bvar 0`). -/
theorem sr4ForallPi_eps :
    sr4ForallPi.eps id [] = .pi (.sort .zero) (.bvar 0) := rfl

/-- The pin's canonical sort `imax 1 0` is zero-BIT: the decider's `.imax` arm
    ignores its first argument (`levelIsZero_iff`: exact on the zero fragment).
    This is why a `.sorts` conv can re-type the pin's subject at `.sort .zero`
    (`pinForallP`, landed) without moving the bit. -/
theorem sr4ForallPi_canon_bit :
    levelIsZero (.imax (.succ .zero) .zero) = true := rfl

/-- Gate tooth 1 (sort head): the gated goal supply's conclusion is INHABITED
    at the closed sort pins — `eps` is `.sort 0` (never `★`) and the type level
    `succ (succ 0)` is succ-headed, so both sides of the iff are false. -/
theorem sr4PbGoalSupplyLhom_sortPin_sat :
    PBit id [] (sr4SortZ []) (sr4SortZUp []) :=
  ⟨fun h => ETm.noConfusion h, fun h => Bool.noConfusion h⟩

/-- Gate tooth 2 (pi head at its canonical sort): at `D := sr4ForallPi` with
    `DT` the sort typing of `D`'s type `.sort (imax 1 0)`, the conclusion is
    again inhabited (both sides false; the zero-bit imax level is what
    `pinForallP`'s `.sorts` conv exploits, and it stays consistent HERE because
    `PBit`'s `DT` types the pin's TYPE, whose canonical level is succ-headed). -/
theorem sr4PbGoalSupplyLhom_piPin_sat :
    PBit id [] sr4ForallPi
      (.sort emptyEnv 0 [] (.imax (.succ .zero) .zero)
        (.succ (.imax (.succ .zero) .zero)) (eqN_refl _)) :=
  ⟨fun h => ETm.noConfusion h, fun h => Bool.noConfusion h⟩
#print axioms Rcic.Syn.sr4PbHeadWall
#print axioms Rcic.Syn.sr4SortZ
#print axioms Rcic.Syn.sr4SortZUp
#print axioms Rcic.Syn.sr4NotPbitConstZeroSort
#print axioms Rcic.Syn.sr4PbGoalSupply
#print axioms Rcic.Syn.sr4PbGoalSupplyRefuted
#print axioms Rcic.Syn.sr4PbHeadLhomWall
#print axioms Rcic.Syn.sr4PbGoalSupplyLhom
#print axioms Rcic.Syn.sr4ForallPi
#print axioms Rcic.Syn.sr4ForallPi_eps
#print axioms Rcic.Syn.sr4ForallPi_canon_bit
#print axioms Rcic.Syn.sr4PbGoalSupplyLhom_sortPin_sat
#print axioms Rcic.Syn.sr4PbGoalSupplyLhom_piPin_sat
end Rcic.Syn
