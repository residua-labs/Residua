import rcic.RcicNativePiModelLRTermD
import rcic.RcicNativePiModelDeltaIota

/-!
# RcicNativePiModelTermDFund — `FundamentalTermD` is false; two independent walls

The objective (devin-desktop/fundamental-termd): construct `FundamentalTermD E n`
(`RcicNativePiModelLRTermD`) for every admitted environment, assemble `TypeSoundnessI E n`,
and read Π-injectivity off `piRow_of_fundamentalTermD`.  Neither premise of that consumer is
constructible, and the module records why as kernel counterexamples composed from landed pins.

**Refuted, unconditionally (every `E : ResolvedEnv`, every `n : Nat`).**
* `not_fundamentalTermD` — the diagonal conjunct at `idPiProp = Π (P : Sort 0), P` and the Π
  compact `idPiPropSortStep = pi ⊥ [([sort], sort)]` (`RcicNativePiModelDeltaIota` §12.1's pin):
  the step demands `sort` on the bound variable, a demand no typed argument of `Sort 0`
  realises, and `LRTypeIN.pi` evaluates the codomain `bvar 0` UNDER the binder, where a
  variable never weak-head reduces to a sort.  Wall **W-DEMAND**: the untyped Π/λ clauses of
  `ApproxI` record unrealisable demands, and the type-level relation's Π clause is not
  substitution-style.
* `not_fundamentalTermD_zetaLocal`, `not_fundamentalTermD_zetaLocal_piBotNil` — the conversion
  conjunct at `ConvT.symm (ConvT.zetaLocal …)` in a one-entry let-context.  At `EnvI.bot` a
  let-bound variable denotes `{⊥}` while its value has `sort` (or `pi ⊥ []`), and the relation's
  readback `WhRed E` is CONTEXT-FREE (`whRed_bvar_eq`): `bvar 0` is weak-head normal, so it is
  related to nothing at a `sort` or Π compact (`lrTypeIN_bvar_right_sort_false`,
  `lrTypeIN_bvar_right_pi_false`).  Wall **W-ZETALOCAL**.  The second instance is at
  `pi ⊥ []`, the one compact `piRow_of_fundamentalTermD` consumes.  The same instance without
  `symm` HOLDS (`fundamentalTermD_zetaLocal_left_holds`): the wall is bidirectionality
  (`ConvT.symm`) against the left-biased compact index, not `zetaLocal` as such.
* `not_fundamentalLRINBotDI`, `not_fundamentalLRINBotDI_sort` — `main`'s own `BotPiCpt`
  restatement (`RcicNativePiModelDeltaIota` §12.3) falls to **W-ZETALOCAL** at the same
  contexts: restricting the compacts does not touch the readback.
* `piRow_of_fundamentalTermD_premises_unsat` — the consumer's two model premises are jointly
  unsatisfiable (`not_typeSoundnessI` is `RcicNativePiModelDeltaIota` §12.2's; the second
  conjunct is this module's).  The consumer on `main` is vacuous.

**What is NOT claimed.**  No repaired relation is defined here.  The two walls are walls of the
MODEL (its readback and its Π/λ demands), not of a proof technique, and each forces a design
choice recorded in the PR body (context-aware weak-head readback in the manner of
`ParRedT.bvarZeta`, or a typed let-collapse of the context; a substitution-style Π clause at the
type level).  Those are the exact remaining named statements.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelTermDFundAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### §1 Readback teeth: a variable is weak-head normal, so it is never related at a `sort`
or Π compact on either side of `LRTypeIN`, nor on the right of `LRTermD` at a literal sort. -/

theorem lrTypeIN_bvar_left_sort_false {Γ : LCtx} {A : Expr Nat} {i : Nat}
    (h : LRTypeIN E n Γ (.bvar i) A .sort) : False := by
  cases h with
  | sort h _ => exact nomatch whRed_bvar_eq h

theorem lrTypeIN_bvar_right_sort_false {Γ : LCtx} {A : Expr Nat} {i : Nat}
    (h : LRTypeIN E n Γ A (.bvar i) .sort) : False := by
  cases h with
  | sort _ h' => exact nomatch whRed_bvar_eq h'

theorem lrTypeIN_bvar_left_pi_false {Γ : LCtx} {A : Expr Nat} {i : Nat} {a : CptI}
    {f : List (List CptI × CptI)} (h : LRTypeIN E n Γ (.bvar i) A (.pi a f)) : False := by
  cases h with
  | pi h _ _ _ _ _ _ => exact nomatch whRed_bvar_eq h

theorem lrTypeIN_bvar_right_pi_false {Γ : LCtx} {A : Expr Nat} {i : Nat} {a : CptI}
    {f : List (List CptI × CptI)} (h : LRTypeIN E n Γ A (.bvar i) (.pi a f)) : False := by
  cases h with
  | pi _ h' _ _ _ _ _ => exact nomatch whRed_bvar_eq h'

/-- A literal sort is not a proposition index (`IsPropTyI`'s second conjunct). -/
theorem not_isPropTyI_sort_lit (Γ : LCtx) (u : Level) : ¬ IsPropTyI E n Γ (.sort u) :=
  fun h => h.2 u rfl

theorem lrTermD_bvar_right_sort_false {Γ : LCtx} {M : Expr Nat} {i : Nat} {u : Level}
    (h : LRTermD E n Γ M (.bvar i) (.sort u) .sort) : False := by
  rcases h with hP | h
  · exact not_isPropTyI_sort_lit Γ u hP
  · rw [LRTermDCore.eq_def] at h
    exact lrTypeIN_bvar_right_sort_false h.2

theorem lrTermD_bvar_right_pi_false {Γ : LCtx} {M : Expr Nat} {i : Nat} {u : Level} {a : CptI}
    {f : List (List CptI × CptI)} (h : LRTermD E n Γ M (.bvar i) (.sort u) (.pi a f)) : False := by
  rcases h with hP | h
  · exact not_isPropTyI_sort_lit Γ u hP
  · rw [LRTermDCore.eq_def] at h
    exact lrTypeIN_bvar_right_pi_false h.2

/-! ### §2 The let-contexts -/

/-- `ConvT.symm` of §12.2's `zetaLocalSortCtx_conv`: `Sort 0 ≡ X : Sort 1` under
    `let X : Sort 1 := Sort 0`. -/
def zetaLocalSortCtx_conv_symm (E : ResolvedEnv) (n : Nat) :
    ConvT E n zetaLocalSortCtx (.sort .zero) (.bvar 0) (.sort (.succ .zero)) :=
  .symm _ _ _ _ (zetaLocalSortCtx_conv E n)

/-- The sort of `idPiProp`. -/
def idPiPropSort : Level := .imax (.succ .zero) .zero

/-- `idPiProp : Sort (imax 1 0)` in EVERY context (the `[]` instance is
    `RcicNativePiModelDeltaIota.hasTyT_idPiProp`). -/
def hasTyT_idPiProp_at (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idPiProp (.sort idPiPropSort) :=
  .pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort Γ .zero)
    (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- The well-formed context `let X : Sort (imax 1 0) := Π (P : Sort 0), P`. -/
def zetaLocalPiCtx : LCtx := [.letBinding (.sort idPiPropSort) idPiProp]

def zetaLocalPiCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n zetaLocalPiCtx :=
  .letBinding [] (.sort idPiPropSort) (.succ idPiPropSort) idPiProp
    .nil (.sort [] idPiPropSort) (hasTyT_idPiProp_at E n [])

/-- `ConvT.zetaLocal`: `X ≡ Π (P : Sort 0), P` at `Sort (imax 1 0)` in `zetaLocalPiCtx`
    (`idPiProp` is closed, so the stored lifted value is `idPiProp` itself). -/
def zetaLocalPiCtx_conv (E : ResolvedEnv) (n : Nat) :
    ConvT E n zetaLocalPiCtx (.bvar 0) idPiProp (.sort idPiPropSort) :=
  .zetaLocal zetaLocalPiCtx 0 (.sort idPiPropSort) idPiProp rfl rfl
    (hasTyT_idPiProp_at E n zetaLocalPiCtx)

def zetaLocalPiCtx_conv_symm (E : ResolvedEnv) (n : Nat) :
    ConvT E n zetaLocalPiCtx idPiProp (.bvar 0) (.sort idPiPropSort) :=
  .symm _ _ _ _ (zetaLocalPiCtx_conv E n)

/-! ### §3 `FundamentalTermD` is false -/

/-- **W-DEMAND.**  The diagonal conjunct fails at `idPiProp` and `idPiPropSortStep`, for every
    `E, n` (`RcicNativePiModelDeltaIota.not_lrTypeIN_idPiProp_sortStep` is the pin). -/
theorem not_fundamentalTermD (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermD E n := by
  intro F
  have h := F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep approxI_idPiProp_sortStep
  rcases h with hP | h
  · exact not_isPropTyI_sort_lit _ _ hP
  · have h' : (∃ l, WhRed E (.sort (.imax (.succ .zero) .zero)) (.sort l)) ∧
        LRTypeIN E n [] idPiProp idPiProp idPiPropSortStep := by
      unfold idPiPropSortStep at h ⊢
      rw [LRTermDCore.eq_def] at h
      exact h
    exact not_lrTypeIN_idPiProp_sortStep E n h'.2

/-- **W-ZETALOCAL.**  The conversion conjunct fails at `Sort 0 ≡ X : Sort 1` under
    `let X : Sort 1 := Sort 0`, at the compact `sort ∈ ⟦Sort 0⟧_⊥`. -/
theorem not_fundamentalTermD_zetaLocal (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermD E n := by
  intro F
  exact lrTermD_bvar_right_sort_false
    (F.2 (zetaLocalSortCtx_wf E n) (zetaLocalSortCtx_conv_symm E n) .sort (.sort EnvI.bot .zero))

/-- **W-ZETALOCAL at the consumer's compact.**  The conversion conjunct fails at
    `Π (P : Sort 0), P ≡ X` under `let X := Π (P : Sort 0), P`, at `pi ⊥ []` — exactly the
    compact `piRow_of_fundamentalTermD` (through `piRow_of_fundamentalLRINT`) consumes. -/
theorem not_fundamentalTermD_zetaLocal_piBotNil (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalTermD E n := by
  intro F
  exact lrTermD_bvar_right_pi_false
    (F.2 (zetaLocalPiCtx_wf E n) (zetaLocalPiCtx_conv_symm E n) (.pi .bot [])
      (approxI_pi_bot_nil EnvI.bot (.sort .zero) (.bvar 0)))

/-- The SAME instance without `symm` holds: at `EnvI.bot` the variable has only `⊥`.  The wall
    is `ConvT.symm` against the left-biased compact index, not `zetaLocal` by itself. -/
theorem fundamentalTermD_zetaLocal_left_holds (E : ResolvedEnv) (n : Nat) :
    ∀ u, ApproxI EnvI.bot (.bvar 0) u →
      LRTermD E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) u := by
  intro u hu
  rcases approxI_bvar_inv hu with h0 | h0
  · subst h0; exact lrTermD_bot _ _ _ _
  · have : u = .bot := h0
    subst this; exact lrTermD_bot _ _ _ _

/-- The consumer `piRow_of_fundamentalTermD` has jointly unsatisfiable model premises:
    `TypeSoundnessI E n` (§12.2's `not_typeSoundnessI`) and `FundamentalTermD E n`. -/
theorem piRow_of_fundamentalTermD_premises_unsat (E : ResolvedEnv) (n : Nat) :
    ¬ (TypeSoundnessI E n ∧ FundamentalTermD E n) :=
  fun h => not_typeSoundnessI E n h.1

/-! ### §4 `main`'s `BotPiCpt` restatement falls to the same wall -/

/-- **W-ZETALOCAL** against `FundamentalLRINBotDI` at `pi ⊥ []` (`botPiCpt_pi_bot_nil`): the
    `TyConvT.of` link `Π (P : Sort 0), P ≡ X` under `let X := Π (P : Sort 0), P`. -/
theorem not_fundamentalLRINBotDI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRINBotDI E n := by
  intro F
  exact lrTypeIN_bvar_right_pi_false
    (F (zetaLocalPiCtx_wf E n) (hasTyT_idPiProp_at E n zetaLocalPiCtx)
      (.of _ _ _ _ (zetaLocalPiCtx_conv_symm E n)) (.pi .bot []) botPiCpt_pi_bot_nil
      (.pi (.bot _ _) (fun _ hs => (List.not_mem_nil _ hs).elim)))

/-- The same at `sort` in the minimal context `let X : Sort 1 := Sort 0`. -/
theorem not_fundamentalLRINBotDI_sort (E : ResolvedEnv) (n : Nat) : ¬ FundamentalLRINBotDI E n := by
  intro F
  exact lrTypeIN_bvar_right_sort_false
    (F (zetaLocalSortCtx_wf E n) (.sort zetaLocalSortCtx .zero)
      (.of _ _ _ _ (zetaLocalSortCtx_conv_symm E n)) .sort .sort (.sort EnvI.bot .zero))

#print axioms lrTypeIN_bvar_left_sort_false
#print axioms lrTypeIN_bvar_right_sort_false
#print axioms lrTypeIN_bvar_left_pi_false
#print axioms lrTypeIN_bvar_right_pi_false
#print axioms not_isPropTyI_sort_lit
#print axioms lrTermD_bvar_right_sort_false
#print axioms lrTermD_bvar_right_pi_false
#print axioms zetaLocalSortCtx_conv_symm
#print axioms idPiPropSort
#print axioms hasTyT_idPiProp_at
#print axioms zetaLocalPiCtx
#print axioms zetaLocalPiCtx_wf
#print axioms zetaLocalPiCtx_conv
#print axioms zetaLocalPiCtx_conv_symm
#print axioms not_fundamentalTermD
#print axioms not_fundamentalTermD_zetaLocal
#print axioms not_fundamentalTermD_zetaLocal_piBotNil
#print axioms fundamentalTermD_zetaLocal_left_holds
#print axioms piRow_of_fundamentalTermD_premises_unsat
#print axioms not_fundamentalLRINBotDI
#print axioms not_fundamentalLRINBotDI_sort

end Rcic.Declarative.NativeValleys.PiModelTermDFundAudit
