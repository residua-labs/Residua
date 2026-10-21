import rcic.RcicAnnRowsSupply
import rcic.RcicRefutations

/-!
# M3-b GLM-1(r1) — pins, chain regressions and negative controls for the chain-rows interface

* `pin_chain_twoOf`: a two-`.of` chain (`sorts` at `Sort 2`, then its `symm`) consumed
    through the interface. Not a `.refl` pin.
* `pin_chain_crossIdx`: the adapter's load-bearing regression — the two legs carry
    SYNTACTICALLY DIFFERENT sort indices and the middle term is written at a
    syntactically different level (`max 1 1` vs `1`), so the collapse must retype the
    first leg across the index change (`tyConv`), not merely carry it.
* `pin_singletonEnv_supply`: a NONEMPTY, legal singleton `EnvWfT` environment (one
    axiom whose stored type is `Sort 1 : Sort 2`) bridged to `AnnEnvA`
    (`annEnvA_of_envWfT`, no inductive group) and supplied `TypedRowsWf`; row 1
    consumed there on a real `sorts` chain.
* Negative controls — each states the NEGATIVE conclusion itself, and each is paired
    with a positive call and a recorded interface-mutation check (see the module doc
    of `RcicTypedRowsNegativeChecks` below for the mutation receipts):
  - `ctrl_sorts_notTotal`: through ANY `TypedRowsWf`, a `Sort 0 ≡ Sort 1` chain is
    refutable (`refutEqN_zero_succ_false` reused unchanged).
  - `ctrl_famAppRow_noLookup`: at an environment where `E.members r = none`, the
    lookup premise of row 3 is UNSATISFIABLE FOR EVERY MEMBER — exported as the
    consumable negative conclusion `∀ m, E.members r ≠ some m` — so the row's
    conclusion is unobtainable there (the hypothesis cannot be discharged).
  - `ctrl_famAppRow_noGroupVacuous`: at a `NoGroupEnv` the class premise is
    unsatisfiable — row 3 is VACUOUS in the no-group range and is NOT family
    coverage (M3-b boundary; the group range is M3-e-2/GLM-4, not this slice).
  - `ctrl_CtxWfT_shape` (renamed from `ctrl_CtxWfT_demanded`): an interface SHAPE
    check — the row field's TYPE carries the `CtxWfT` premise definitionally, so a
    call omitting the context argument does not elaborate against the field. The
    corresponding omitted-argument failure is recorded (with its position) in
    `RcicTypedRowsNegativeChecks`'s docstring as a compile-failure receipt; it is a
    type-shape fact, not a mathematical-necessity claim.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) two-`.of` chains consumed through the interface -/

section TwoOf

variable {E : ResolvedEnv} {n : Nat}

/-- step 1: the `sorts` rule on `Sort 1 ≡ Sort 1`, a conversion AT `Sort 2`. -/
def pinStep1 : ConvT E n [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  ConvT.sorts [] (.succ .zero) (.succ .zero) (fun _ => rfl)

/-- step 2: the same equation run BACKWARDS — `ConvT.symm` of step 1, a second
    real `.of` leg derived by a different rule (symmetry, not `sorts` directly). -/
def pinStep2 : ConvT E n [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  ConvT.symm _ _ _ _ pinStep1

/-- THE CHAIN: two `.of` legs, `sorts` then its `symm`, both real steps. -/
def pinChain : TyConvT E n [] (.sort (.succ .zero)) (.sort (.succ .zero)) :=
  TyConvT.trans _ _ _ _
    (TyConvT.of _ _ _ _ pinStep1)
    (TyConvT.of _ _ _ _ pinStep2)

/-- CONSUMPTION: the supplier's adapter collapses the two-leg chain to ONE `ConvT`
    at the left end's own sort (`Sort 2`, `HasTyT.sort`'s typing). -/
theorem pin_chain_twoOf (C : AnnEnvA EA) (hn : EnvNormEraseA EA) (n : Nat)
    (hΓ : CtxWfT (eraseEnv EA) n []) :
    Nonempty (ConvT (eraseEnv EA) n [] (.sort (.succ .zero)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero)))) :=
  convT_of_tyConvT_sort C hn hΓ (HasTyT.sort [] (.succ .zero)) pinChain

/-- the same chain through row 1 of the interface: `eqN 1 1`. -/
theorem pin_chain_row1 (C : AnnEnvA EA) (hn : EnvNormEraseA EA) (n : Nat) (hΓ : CtxWfT (eraseEnv EA) n []) :
    eqN (.succ .zero) (.succ .zero) :=
  (typedRowsWf_of_annEnvA C hn n).sortRow hΓ pinChain

end TwoOf

/-! ## (1b) the cross-index regression: the middle level at `max 1 1`, the legs at
    syntactically different sort indices (`Sort 2` vs `Sort (succ (max 1 1))`).
    `eqN 1 (max 1 1)` holds pointwise (`eval ρ (max 1 1) = some 1`), so `sorts`
    applies at the `max`-written level while the left end stays the literal `1` —
    the collapse must transport each leg to the left end's own `Sort 2`, not assume
    its index already matches. -/

section CrossIdx

variable {E : ResolvedEnv} {n : Nat}

/-- `eval ρ (max 1 1) = some 1` for every `ρ`: `1 =ₙ max 1 1` pointwise. -/
theorem eqN_one_max : eqN (.succ .zero) (.max (.succ .zero) (.succ .zero)) := by
  intro ρ
  rfl

/-- leg 1: `sorts` at the `max`-written level — the conversion's endpoints are
    `Sort 1` and `Sort (max 1 1)`, SYNTACTICALLY DIFFERENT, at index `Sort 2`. -/
def pinXStep1 : ConvT E n [] (.sort (.succ .zero)) (.sort (.max (.succ .zero) (.succ .zero)))
    (.sort (.succ (.succ .zero))) :=
  ConvT.sorts [] (.succ .zero) (.max (.succ .zero) (.succ .zero)) eqN_one_max

/-- leg 2: `sorts` again at the `max`-written level — a second real `.of` leg whose
    sort index is `Sort (succ (max 1 1))`, SYNTACTICALLY DIFFERENT from leg 1's
    `Sort 2` (it is `Sort 2` only up to `Level` computation, not syntactically). -/
def pinXStep2 : ConvT E n [] (.sort (.max (.succ .zero) (.succ .zero)))
    (.sort (.max (.succ .zero) (.succ .zero)))
    (.sort (.succ (.max (.succ .zero) (.succ .zero)))) :=
  ConvT.sorts [] (.max (.succ .zero) (.succ .zero)) (.max (.succ .zero) (.succ .zero))
    (fun _ => rfl)

/-- THE CROSS-INDEX CHAIN: leg 1 at `Sort 2`, leg 2 at `Sort (succ (max 1 1))`; the
    right end and the middle are `Sort (max 1 1)` while the left end is the literal
    `Sort 1`. -/
def pinXChain : TyConvT E n [] (.sort (.succ .zero)) (.sort (.max (.succ .zero) (.succ .zero))) :=
  TyConvT.trans _ _ _ _
    (TyConvT.of _ _ _ _ pinXStep1)
    (TyConvT.of _ _ _ _ pinXStep2)

/-- CONSUMPTION: the adapter collapses the cross-index chain to ONE `ConvT` at the
    left end's own sort (`Sort 2`), retyping leg 2's `Sort 3` index down — the
    load-bearing branch of `convT_of_tyConvT_sort` exercised on a real index change. -/
theorem pin_chain_crossIdx (C : AnnEnvA EA) (hn : EnvNormEraseA EA) (n : Nat)
    (hΓ : CtxWfT (eraseEnv EA) n []) :
    Nonempty (ConvT (eraseEnv EA) n [] (.sort (.succ .zero))
      (.sort (.max (.succ .zero) (.succ .zero))) (.sort (.succ (.succ .zero)))) :=
  convT_of_tyConvT_sort C hn hΓ (HasTyT.sort [] (.succ .zero)) pinXChain

/-- and through row 1: the literal level and its `max` form are `=ₙ`. -/
theorem pin_chain_crossIdx_row1 (C : AnnEnvA EA) (hn : EnvNormEraseA EA) (n : Nat)
    (hΓ : CtxWfT (eraseEnv EA) n []) :
    eqN (.succ .zero) (.max (.succ .zero) (.succ .zero)) :=
  (typedRowsWf_of_annEnvA C hn n).sortRow hΓ pinXChain

end CrossIdx

/-! ## (2) a nonempty singleton environment, supplied -/

section Singleton

/-- one axiom whose STORED TYPE is `Sort 1` (so its sort is `Sort 2`) at index 0 — a
    legal nonempty `EnvWfT` environment. -/
def pinAxEnvT : EnvWfT (extendEnv emptyEnv 0
    ⟨.axiomM, 0, .sort (.succ .zero), none⟩) :=
  EnvWfT.axiom emptyEnv 0 (.sort (.succ .zero)) (.succ (.succ .zero))
    .empty rfl (.sort [] (.succ .zero)) (fun _ => rfl)
    rfl

/-- it has no inductive group. -/
def pinAxNoGroup : NoGroupEnv (extendEnv emptyEnv 0
    ⟨.axiomM, 0, .sort (.succ .zero), none⟩) := by
  intro r m hm
  by_cases hr : r = 0
  · subst hr; rw [show (extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort (.succ .zero), none⟩).members 0 = some ⟨.axiomM, 0, .sort (.succ .zero), none⟩ from rfl] at hm
    cases hm
    exact ⟨fun h => MemberClass.axiomM.noConfusion h,
      fun h => MemberClass.axiomM.noConfusion h,
      fun h => MemberClass.axiomM.noConfusion h⟩
  · rw [members_extend_ne emptyEnv 0 _ r hr] at hm
    exact absurd hm (by rw [show emptyEnv.members r = none from rfl]; exact Option.noConfusion)

/-- the singleton environment bears the chain rows, through the bridge and the
    supplier — a NONEMPTY legal environment, not `emptyEnv`. -/
theorem pin_singletonEnv_supply (n : Nat) :
    TypedRowsWf (extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort (.succ .zero), none⟩) n := by
  obtain ⟨EA, hE, C, hn⟩ := annEnvA_of_envWfT pinAxEnvT pinAxNoGroup
  rw [← hE]
  exact typedRowsWf_of_annEnvA C hn n

/-- row 1 consumed there: a real sorts chain collapses to `eqN`. -/
theorem pin_singletonEnv_row1 (n : Nat) :
    eqN (.succ .zero) (.succ .zero) := by
  have R := pin_singletonEnv_supply n
  exact R.sortRow CtxWfT.nil
    (TyConvT.of _ _ _ _ (pinStep2 (E := (extendEnv emptyEnv 0
      ⟨.axiomM, 0, .sort (.succ .zero), none⟩))))

end Singleton

/-! ## (3) negative controls

Each control EXPORTS its negative conclusion (no `True`-valued stubs); each is paired
with the positive call one line above or below; the interface-mutation receipts are
in `RcicTypedRowsNegativeChecks`'s docstring (kept as a module docstring — a comment
— so the receipts are in-tree without introducing a second proof-carrying file). -/

/-- CONTROL (a): through ANY interface supply, `Sort 0` and `Sort 1` are not
    type-convertible — the row is not the total relation. Positive pair:
    `pin_singletonEnv_row1` (row 1 CONSUMED where the supply exists). -/
theorem ctrl_sorts_notTotal {E : ResolvedEnv} {n : Nat} (R : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (h : TyConvT E n Γ (.sort .zero) (.sort (.succ .zero))) : False :=
  refutEqN_zero_succ_false (R.sortRow hΓ h)

/-- CONTROL (b): at an environment with NO member at `r`, row 3's lookup premise is
    unsatisfiable FOR EVERY MEMBER — exported as the consumable negative conclusion.
    Consequence: the `famAppRow` field's hypothesis `hm : E.members r = some m` cannot
    be discharged at any `m`, so the row's conclusion is unobtainable there. Positive
    pair: `pin_singletonEnv_row1` consumes row 1 of the SAME interface; the family row
    has no positive instance in this slice's range (see control (c)). -/
theorem ctrl_famAppRow_noLookup {E : ResolvedEnv} {n : Nat} {r : Nat}
    (hnone : E.members r = none) :
    ∀ m : CheckedMember, E.members r ≠ some m := by
  intro m hm
  rw [hnone] at hm
  exact Option.noConfusion hm

/-- CONTROL (c): in the no-group range row 3 is VACUOUS — the class premise is
    unsatisfiable — and is not family coverage. -/
theorem ctrl_famAppRow_noGroupVacuous {E : ResolvedEnv} (hno : NoGroupEnv E)
    {n : Nat} (R : TypedRowsWf E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) : ¬ (m.mclass = .inductiveM) :=
  fun hind => (hno r m hm).1 hind

/-- CONTROL (d) — INTERFACE SHAPE CHECK (renamed from `_demanded`): the row field's
    TYPE carries the `CtxWfT` premise definitionally, i.e. the context argument is a
    mandatory explicit argument of the field's function type — a call omitting it
    does not elaborate against the field. This is a type-shape fact (checked by
    `rfl` at the field type), NOT a claim of mathematical necessity; the
    omitted-argument compile-failure receipt is recorded in
    `RcicTypedRowsNegativeChecks`'s docstring. Positive pair: every `sortRow`/`piRow`
    call in this file passes `hΓ` explicitly. -/
theorem ctrl_CtxWfT_shape {E : ResolvedEnv} {n : Nat} (R : TypedRowsWf E n) :
    (∀ {Γ}, CtxWfT E n Γ → ∀ {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) →
      eqN u v) := R.sortRow

end Rcic.Declarative.Ann

/-!
# Interface-mutation receipts (compile-failure checks, recorded)

These are RECEIPTS from controlled elaboration attempts against the interface's
declared types, re-run whenever this file changes; they are documented as a module
docstring comment so no proof-carrying duplicate of the interface exists. Each names
the mutation, the EXPECTED failure position, and what the compiled checks above DO
cover (the positive side); the failure side is re-checked by the re-run recipe.

* Mutation 1 — drop the `CtxWfT` premise from `sortRow`'s call.
  RUN (2026-10-05, scratch `/tmp/mutcheck.lean`, `lake env lean`):
  `example (R : TypedRowsWf E n) (h : TyConvT E n [] (.sort u) (.sort v)) :
    eqN u v := R.sortRow h`
  ACTUAL: error at `h` — «application type mismatch ... h has type
  `TyConvT E n [] (Expr.sort u) (Expr.sort v)` but is expected to have type
  `CtxWfT E n ?m`» — a type mismatch AT THE ARGUMENT, not an unresolved name or
  import error. The compiled shape check `ctrl_CtxWfT_shape` pins the premise's
  presence definitionally (`:= R.sortRow` typechecks only because the field's type
  includes the premise).

* Mutation 2 — call `famAppRow` with the lookup omitted (the next premise lands in
  the lookup slot).
  RUN (2026-10-05, scratch `/tmp/mutcheck2.lean`, `lake env lean`):
  `R.famAppRow hΓ hind hty h` — the class premise `hind` passed where the lookup
  `hm : E.members r = some m` is expected.
  ACTUAL: error at `hind` — «application type mismatch ... hind has type
  `m.mclass = MemberClass.inductiveM` but is expected to have type
  `E.members ?r = some ?m`» — the lookup slot is the first explicit premise after
  the context and CANNOT be skipped or filled by a non-lookup term.
  `ctrl_famAppRow_noLookup` supplies the mathematical side: at `E.members r = none`
  NO `m` makes the premise provable, so the row's conclusion is unobtainable.

Re-run recipe for both (scratch, never landed): `lake env lean` on a file importing
`RcicTypedRowsSupplyPins` with the two `example`s above; both must fail with
«type mismatch» AT THE NAMED ARGUMENT (`h` / `hind`). A failure that instead reports
an unresolved identifier, import error or parse error does not count and must be
re-derived.
-/

#print axioms Rcic.Declarative.Ann.pin_chain_twoOf
#print axioms Rcic.Declarative.Ann.pin_chain_row1
#print axioms Rcic.Declarative.Ann.eqN_one_max
#print axioms Rcic.Declarative.Ann.pin_chain_crossIdx
#print axioms Rcic.Declarative.Ann.pin_chain_crossIdx_row1
#print axioms Rcic.Declarative.Ann.pin_singletonEnv_supply
#print axioms Rcic.Declarative.Ann.pin_singletonEnv_row1
#print axioms Rcic.Declarative.Ann.ctrl_sorts_notTotal
#print axioms Rcic.Declarative.Ann.ctrl_famAppRow_noLookup
#print axioms Rcic.Declarative.Ann.ctrl_famAppRow_noGroupVacuous
#print axioms Rcic.Declarative.Ann.ctrl_CtxWfT_shape
