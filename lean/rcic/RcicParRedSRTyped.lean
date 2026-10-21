import Lean
import rcic.RcicParRedCore
import rcic.RcicConvChar
import rcic.RcicDTMetaTypedSR

/-!
# O2S segment v — `parRedSRT` SEALED under R-1″ (2026-10-09, the THIRD ruling)

ARCHITECT RULINGS 2026-10-09 (cc), and where they stand after this segment:

## R-1″ (the THIRD ruling) — the 13-arm `parRedSRT` mutual SEALED

R-1 is WITHDRAWN (its premise addition on `ParRed.consts` refutes the sealed
`parRedInstantiateLevels` and walls at `RcicParRedDiamond.lean:809` — the
record below keeps the measurement). R-1′ ruled the consts-only `levelsIn`
scope; its scoped claim was then REFUTED at iotaSpine
(`parRedSRT_levelsIn_claimFalse` below, kept as a true theorem on the
preserved consts-only predicate `levelsInR1`). R-1″ closes the segment:

* **THE SECOND COUNTEREXAMPLE IS CORRECT and refutes the CONSTS-ONLY
  enumeration, not the predicate approach**: `w2` is a constructor parameter,
  so a derivation predicate CAN read `w2.ls` — the counterexample's
  `[.imax (.param 5) .zero]` fails `levelsBounded 1` and is excluded once
  read. No new rule is needed.
* **CONTENT RULE**: every list a level-equality premise carries into the
  target must be in the level context. `sortEq` exempt (`HasTyT.sort` has no
  bound premise).
* **MEASURED ENUMERATION** — in `ParRed`'s constructor block
  (`RcicParRedCore.lean`, `inductive ParRed` line 131 through `end` line 225
  of its mutual block), `grep eqN` — exactly THREE premise sites:

      $ grep -n 'eqN' lean/rcic/RcicParRedCore.lean | head
      6:level equality (`eqN*`), `foldApps` head lemmas, `step_parRed`,
      29:theorem eqN_refl (l : Level) : eqN l l := fun _ => rfl
      31:theorem eqN_symm {a b : Level} (h : eqN a b) : eqN b a :=
      34:theorem eqN_trans {a b c : Level} (h1 : eqN a b) (h2 : eqN b c) : eqN a c :=
      129:spine. Level drift on the two heads is `eqNList`. Lengths sit on
      133:  | sortEq (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
      135:  | consts (Γ : LCtx) (r : Nat) (ls ls' : List Level) (h : eqNList ls ls') :
      184:      (hlsR : eqNList w2.ls lsR) (hlsC : eqNList w2.lsC lsC)
      245:lemma is the missing leg at `eqNList ls₁ ls₂`.
      254:    (T : Expr Nat) → {ls ls' : List Level} → eqNList ls ls' →

  The block's three eqN-PREMISE sites are `sortEq` (:133), `consts` (:135)
  and `iotaSpine` (:184) — no fourth. The remaining grep hits are no premise:
  :6/:129 are docstring prose, :29-34 the `eqN_refl`/`eqN_symm`/`eqN_trans`
  toolbox ABOVE the block, and :245/:254 sit AFTER the block's `end` (:225)
  in the `parRed_to_conv` companions (consumers, not constructors;
  `ParRedArgs`/`ParRedCtx` in the block carry no eqN premise).
* **THE CHANGE — ONE ARM**: `levelsIn`'s `iotaSpine` arm additionally checks
  `levelsBounded n w2.ls = true` AND `levelsBounded n w2.lsC = true` (besides
  the existing `levelsInArgs` conjunction). `parRedSRT`'s STATEMENT is
  UNCHANGED (still just `levelsIn d = true`).
* **SUPPLY CONDITIONED ON THE SOURCE TYPING**:
  `step_to_parRed_levelsIn (s) (h : HasTyT E n Γ a T)` — the ι arm builds
  the ctor at `w2.ls`/`w2.lsC` (the SOURCE's own lists), and the typed
  source spine-inverts to bounded heads (`hasTyTConstSpineBound`); the other
  five arms do not read the typing. The typed source is not a new obligation:
  SR's consumers already hold it.
* **SEALED**: the 13-arm `parRedSRT` (statement unchanged) rides the sealed
  machinery — the conv member `parRedConvT` carries the arms, the typing
  member reads the reduct's typing off `DT009T_endpoints_inScope`; the
  iotaSpine arm moves both spine heads by `hasTyTConstMove`/
  `hasTyTConstMoveConv` at the bounds the predicate now supplies, closes the
  major's value-congruence through `convTInst0ValueSort` with the codomain's
  under-binder sort-typing from R-2 + Π-inversion, then hands `iotaLhsOf w2`
  to `iotaPreserveT` (=`hasTyT_iota_sr` through the scope bridge); β/ζ ride
  the Π row in scope (`typedRowsWf_of_envWfT_semPrefix`) and
  `convTInst0ValueSort`/`…SortLet`; the spine partners are `parRedArgsSRT`
  (the typing mover, the legacy `parRedArgsSR` mirror) and
  `parRedArgsConvT`.

RECORDS: DT-025's normalization row is stated on the typed root along the
scope `levelsIn` carves out, and STAYS OPEN (the row's content is not this
segment's). In-scope confluence is UNESTABLISHED — the wall remains at
`RcicParRedDiamond.lean:809`, currently unowned; the typed root uses NO
legacy diamond (ι rides `hasTyT_iota_sr` through `iotaPreserveT` only) —
keep it that way.

## The settled history (kept; `iotaSpine_hlsPinned` itself DELETED per cc)

* R-2 (sort-typing invariant through the annotation bridge) — SEALED below:
  `hasTyA_type_sort` (copy side: `hasTyA_type_subst` at the identity
  substitution), `hasTyT_type_sort_exists` (adapter form, the
  `hasTyT_sort_of_convT` shape), `hasTyT_type_sort_exists_scope` (the
  `EnvWfT`+`InScope` packaging via `annEnvA_of_envWfT_semPrefix`), and the
  consumption pin `pin_hasTyT_type_sort_typed` (natEnvU, const arm, arity 1 > 0).
  This discharges `convTInst0ValueSort`'s one premise wherever the π-codomain's
  typing is in hand, by `hasTyT_type_sort_exists_scope` applied to it.
* R-1 (`ParRed.consts` gains `hwf' : levelsBounded n ls' = true`) — ruled, and
  measured against the tree: the premise addition REFUTES the sealed legacy
  lemma `parRedInstantiateLevels` (`RcicParRedCore.lean:253`, pinned by
  `RcicFoundationSeal`'s CollectAxioms sweep): its statement promises the
  const-arm step `instantiateLevels ls T ↠ instantiateLevels ls' T` from bare
  `eqNList ls ls'`, and the premise is not derivable — countermodel
  `n = 1`, `T = .const r [.param 0]`, `ls = [.zero]`,
  `ls' = [.imax (.param 5) .zero]` (eqNList holds by the imax-zero mask,
  `levelsBounded 1 [imax (param 5) zero] = false`). The same wall sits at
  `RcicParRedDiamond.lean:809` (`.consts Γ w.recRef w.ls w2.ls hls` from bare
  `eqNList w.ls w2.ls`; `IotaWitness` carries no level bounds). The seal
  forbids sorry (elaboration-time axiom sweep, 1931 names), the dispatch
  forbids legacy statement changes, so R-1 CANNOT LAND GREEN without a second
  ruling — either sanction `parRedInstantiateLevels`'s retirement/premise plus
  a diamond rework, or weaken the premise. A full mechanical adaptation
  (constructor +1 and every consumer patched) is preserved on branch
  `glm/o2s-seg4-r1-attempt` (local, unpushed) for that ruling to diff.
* iotaSpine drift check (cc's second question) — FIRST MEASURED WRONG,
  CORRECTED UNDER R-1′, SETTLED UNDER R-1″: an early reading (commit
  adad14e77e) claimed `hlhs` pins the heads SYNTACTICALLY so the eqN
  premises were redundant — RETRACTED: at the constructor the premise
  instantiates with the witness's own lists (`hlhs` names `w2.ls`/`w2.lsC`
  itself, `RcicParRedCore.lean:191-193`), where any such pin is REFLEXIVE —
  the drift channels are the constructor's OWN `hlsR`/`hlsC` (the third
  eqN-mask channel; see the (B) record). The pin lemma that fed the
  misreading chain was ordered removed by cc and is deleted; the
  measurement stands. `sortEq` confirmed needs no bound premise
  (`HasTyT.sort` has none). Ledger note: DT-025's normalization row (stated
  along ParRed "up to level equality") is narrowed by R-1′/R-1″ to the
  `levelsIn` fragment's level context; the row stays open.

Consequence for the segment: `parRedSRT` remains FALSE as dispatched (the
unconditioned form, `parRedSRT_claimFalse` below — KEPT as a true theorem)
and was FALSE under the R-1′ consts-only scope (`parRedSRT_levelsIn_claimFalse`
below — KEPT as a true theorem on the preserved `levelsInR1`, documenting why
consts-only failed); under R-1″'s content-rule `levelsIn` the 13-arm mutual is
SEALED, and the β pin is rewired through the full theorem. The rest of this
header (the machine, the app-arm refutation, the beta/zeta analysis) is the
standing evidence.

OUTCOME (read before the rest): the dispatched statement

    parRedSRT {E} (hW : EnvWfT E) (hP : hW.InScope) {n Γ} (hΓ : CtxWfT E n Γ) :
      {e A e'}→ HasTyT E n Γ e A → ParRed E n Γ e e' →
      Nonempty (HasTyT E n Γ e' A)

is FALSE. `parRedSRT_claimFalse` below refutes it at `natEnvU` (the dispatch's own
pin environment), `n = 1`, `Γ = []`, one `ParRed.consts` step. The machine:
* `eqN (.imax (.param i) .zero) (.imax (.param j) .zero)` holds for ALL `i j`
  (`eqN_imaxParam_zero`): imax's right argument `.zero` makes both sides evaluate
  to `some 0` at every valuation — 02 §2's `imax u 0 = 0`, quoted as
  `RcicLevelDec`'s first local identity.
* `levelsBounded n` does NOT transport along `eqN`: `levelBounded 1 (.param 0) =
  decide (0 < 1) = true` but `levelBounded 1 (.param 5) = decide (5 < 1) = false`,
  and the imax-zero mask hides the parameter from `eval` entirely. So
  `ParRed.consts`' premise `eqNList ls ls'` permits stepping
  `.const 3 [.imax (.param 0) .zero] ↠ .const 3 [.imax (.param 5) .zero]`.
* Every typing of a const bounds its level list (`hasTyTInv_const`'s third
  component, fording over the `.conv` wrappers): the source is typable at `n = 1`
  (`parRedSRT_constsSrcTyped`, `natRecMemberU.arity = 1`), the target is typable
  at NO type (`parRedSRT_constsTgtUntyped`).

The legacy `parRedSR` never saw this because legacy `HasTy.const`'s side
condition (`∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n`,
`RcicParRedSR.eqNList_hwf`'s input) is vacuously satisfiable — `eval` at the empty
valuation is `none` on every level. O-2's typed judgment turned that into the
real side condition `levelsBounded n ls`, and `ParRed.consts` does not respect
it. This is a divergence between the UNCONDITIONAL reduction relation and the
typed judgment, not a missing lemma: no proof of the dispatched shape can
exist. R-1′/R-1″ resolved it by scoping `parRedSRT` at the derivation
predicate `levelsIn`, whose consts arm carries the content rule
(`levelsBounded n ls'`); the unconditional form stays refuted, as the tooth
records.

## The KNOWN WALL as dispatched: REFUTED for the app arm, RELOCATED for beta/zeta

The dispatch's wall located the app congruence arm as needing a typed
`conv_instantiate0_value`. Measured false — twice:

* CONV FORM (`parRedApp_armCloses` below, sealed): from the IH-shaped premises
  `ConvT f f' (.pi A B)` and `ConvT a a' A`, `ConvT.app` concludes at
  `instantiate0 a B` (the LEFT argument's instantiation — the constructor carries
  the type), and the app-inversion's `TyConvT (instantiate0 a B) T` moves it to
  `T` by `convT_of_tyConv`. No value-congruence is ever formed.
* TYPING FORM: build `HasTyT.app f' a A B hf' ha₀` (the OLD argument, typed
  `ha₀`), move the argument by `ConvT.app` with `f'`-refl, read the reduct's
  typing off `DT009T_endpoints_inScope`, retype along `hcv`. The endpoint
  theorem absorbs the value-congruence the legacy needed `conv_instantiate0_value`
  for.

The REAL wall as dispatched sat behind the beta and zeta arms (and iotaSpine
with them), and it was one lemma, `convTInst0ValueSort` below — SEALED,
conditional on its one premise. Both arms reduce to a type-level value
congruence `TyConvT (instantiate0 v B) (instantiate0 v' B)` (beta: the two
beta-rules at `arg` and `arg'` conclude at `instantiate0 arg B_lam` and
`instantiate0 arg' B_lam`; zeta: same shape at the let's codomain; iotaSpine:
the major premise's move at `B₀`). The construction — a THREE-BETA ROUNDTRIP
at a sort, replacing legacy's zeta roundtrip `RcicDTMeta.conv_instantiate0_value`
— needs exactly

    HasTyT E n (LocalDecl.assumption A :: Γ) B (.sort w)

(the codomain sort-typed under the domain binder; then all three legs live at
`.sort w` since `instantiate0 v (.sort w) = .sort w`). That premise is the
invariant "every type-index of a `HasTyT` derivation is sort-typed". An
interim reading located it OPEN at the direct-`lam` case (where it seemed to
reduce to a typed level-substitution theorem for GROUP members at arity > 0 —
measured absent in this tree); the interim guess is SUPERSEDED, not by a
level-substitution theorem but by R-2: `hasTyT_type_sort_exists_scope` seals
the invariant for EVERY `HasTyT` type-index (through the annotation bridge),
and the under-binder form falls out by Π-term inversion
(`hasTyTInv_pi` on R-2's output at the π). `parRedBeta_armCloses_of_sort`
below keeps the conditional closure as the machine-checked intermediate
record; the R-1″ mutual consumes the same route unconditionally.

Premise disclosure: no statement below mentions a legacy judgment (`HasTy`,
`Conv`, `CtxWf`, `EnvWf`), and no premise names a row, `TypedRowsWf`,
`AnnEnvA`, `EnvSemA` or `IotaSRA` (`parRedBeta_armCloses_of_sort`'s `hcB` is
the Π row's OUTPUT shape — a plain `TyConvT` chain — supplied as a
demonstration premise, not part of any `parRedSRT` statement; the R-1″
mutual DERIVES the rows in scope via `typedRowsWf_of_envWfT_semPrefix` from
`hW`/`hP` — no row is a premise). The ι route rides `iotaPreserveT` only.
axioms within {propext, Quot.sound}; closure_claim 0.
-/

namespace Rcic.Declarative

open Rcic.Declarative.Ann

/-! ## the countermodel's engine -/

/-- imax with a `.zero` right argument is the constantly-`some 0` level, so its
    left parameter is invisible to `eval` at every valuation: ANY two parameters
    give `=ₙ`-equal levels. -/
theorem eqN_imaxParam_zero (i j : Nat) :
    eqN (.imax (.param i) .zero) (.imax (.param j) .zero) := by
  intro ρ
  rfl

/-! ## the app-arm wall, refuted (both forms route through tools that exist) -/

/-- The dispatched wall's arm closes with NO value-congruence: the app
    congruence concludes at the LEFT argument's instantiation, which is exactly
    the app-inversion's chain start. This is the conv-form construction the
    `parRedConvT` mutual would use at its `app` arm (IH-shaped premises). -/
theorem parRedApp_armCloses {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' a a' A B T : Expr Nat}
    (hcv : TyConvT E n Γ (instantiate0 a B) T)
    (ihf : Nonempty (ConvT E n Γ f f' (.pi A B)))
    (iha : Nonempty (ConvT E n Γ a a' A)) :
    Nonempty (ConvT E n Γ (.app f a) (.app f' a') T) :=
  ihf.elim fun c1 => iha.elim fun c2 =>
    ⟨convT_of_tyConv (ConvT.app Γ f f' a a' A B c1 c2) hcv⟩

/-! ## the relocated wall's one lemma, sealed -/

/-- Substituting a value into a type-conversion CHAIN (the Π row's codomain
    output is a `TyConvT`, not one `ConvT`; each `.of` step substitutes by
    `convT_subst0_of_envWfT` and the chain reassembles). -/
def convT_subst0_tyConvT {E : ResolvedEnv} (hW : EnvWfT E) {v t : Expr Nat}
    {n : Nat} {Γ : LCtx} :
    {X Y : Expr Nat}→ TyConvT E n (LocalDecl.assumption t :: Γ) X Y →
    HasTyT E n Γ v t →
    Nonempty (TyConvT E n Γ (instantiate0 v X) (instantiate0 v Y))
  | _, _, .refl _ _, _ => ⟨TyConvT.refl _ _⟩
  | _, _, .of _ _ _ _ hc, hv => by
      have hc' := convT_subst0_of_envWfT hW hc hv
      simp only [instantiate, instantiate0] at hc'
      exact ⟨TyConvT.of _ _ _ _ hc'⟩
  | _, _, .trans _ _ _ _ h1 h2, hv =>
      (convT_subst0_tyConvT hW h1 hv).elim fun c1 =>
        (convT_subst0_tyConvT hW h2 hv).elim fun c2 =>
          ⟨TyConvT.trans _ _ _ _ c1 c2⟩

/-- THE MINIMAL UNBLOCKING LEMMA for the beta/zeta/iotaSpine arms: the typed
    value-congruence at a sort, by a three-beta roundtrip (legacy's
    `conv_instantiate0_value` was a zeta roundtrip; the typed zeta rule needs
    the body typed under a LET binder, which the assumption-side supply cannot
    give without a let-morphism — the beta roundtrip needs only the assumption
    supply). All three legs live at `.sort w` because the beta rule's codomain
    is instantiated at a sort, which `instantiate0 v (.sort w) = .sort w` keeps
    constant in `v`. The ONE premise beyond the value conversion is `hbody`:
    the instantiated-into expression typed AT A SORT under the domain binder —
    the "type-indices are sort-typed" invariant (see the module header for where
    it is and is not available). -/
theorem convTInst0ValueSort {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body v v' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (LocalDecl.assumption A :: Γ) body (.sort w))
    (hc : ConvT E n Γ v v' A) :
    Nonempty (ConvT E n Γ (instantiate0 v body) (instantiate0 v' body) (.sort w)) := by
  obtain ⟨hv⟩ := (DT009T_endpoints_inScope hW hP hΓ hc).1
  obtain ⟨hv'⟩ := (DT009T_endpoints_inScope hW hP hΓ hc).2
  have l1 : ConvT E n Γ (instantiate0 v body) (.app (.lam A body) v) (.sort w) :=
    ConvT.symm _ _ _ _ (ConvT.beta Γ A body v (.sort w) u hA hbody hv)
  have l2 : ConvT E n Γ (.app (.lam A body) v) (.app (.lam A body) v') (.sort w) :=
    ConvT.app Γ (.lam A body) (.lam A body) v v' A (.sort w)
      (ConvT.lam Γ A A body body (.sort w) u
        (ConvT.refl Γ A (.sort u) hA)
        (ConvT.refl (LocalDecl.assumption A :: Γ) body (.sort w) hbody))
      hc
  have l3 : ConvT E n Γ (.app (.lam A body) v') (instantiate0 v' body) (.sort w) :=
    ConvT.beta Γ A body v' (.sort w) u hA hbody hv'
  exact ⟨ConvT.trans _ _ _ _ _ l1 (ConvT.trans _ _ _ _ _ l2 l3)⟩

/-- The beta arm's conditional closure, machine-checked: GIVEN the codomain's
    under-binder sort-typing (`hsort` — the "type-indices are sort-typed"
    invariant's residue at this arm) and the Π row's codomain chain (`hcB` —
    the row's output shape), the arm closes through `hasTyT_subst0_of_envWfT`,
    `convTInst0ValueSort` and `convT_subst0_tyConvT`. No `parRedSRT` statement
    carries these: they are demonstration premises standing for what the
    missing level-substitution theorem would discharge. -/
theorem parRedBeta_armCloses_of_sort {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B_lam B0 T body' arg arg' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody' : HasTyT E n (LocalDecl.assumption A :: Γ) body' B_lam)
    (harg : HasTyT E n Γ arg A) (harg' : HasTyT E n Γ arg' A)
    (iharg : Nonempty (ConvT E n Γ arg arg' A))
    (hcB : Nonempty (TyConvT E n (LocalDecl.assumption A :: Γ) B_lam B0))
    (hsort : Nonempty (HasTyT E n (LocalDecl.assumption A :: Γ) B_lam (.sort w)))
    (hcv : TyConvT E n Γ (instantiate0 arg B0) T) :
    Nonempty (HasTyT E n Γ (instantiate0 arg' body') T) := by
  have hty0' : HasTyT E n Γ (instantiate0 arg' body') (instantiate0 arg' B_lam) :=
    hasTyT_subst0_of_envWfT hW hbody' harg'
  obtain ⟨hs⟩ := hsort
  obtain ⟨hcB'⟩ := hcB
  obtain ⟨iharg'⟩ := iharg
  obtain ⟨vc⟩ := convTInst0ValueSort hW hP hΓ hA hs iharg'
  obtain ⟨c2l⟩ := convT_subst0_tyConvT hW hcB' harg
  exact ⟨hasTyT_of_tyConv hty0'
    (TyConvT.trans _ _ _ _ (TyConvT.symmT (TyConvT.of _ _ _ w vc))
      (TyConvT.trans _ _ _ _ c2l hcv))⟩

/-! ## consumption pin: the roundtrip at a real in-scope environment -/

/-- PIN: `convTInst0ValueSort` consumed on `natEnvU` at `n = 1` — the value is
    the beta redex `(λ (x : Sort 1), x) Sort 0` against its reduct, the
    instantiated-into expression is `Π (x : Sort 0), x`-in-binder-shape
    `.pi (.sort .zero) (.bvar 0)` (a genuine bvar-0 consumer, sort-typed at
    `.imax 1 0` under the domain binder), and the conclusion instantiates the π
    at the REDEX on one side and at its reduct on the other. -/
theorem pin_convTInst0ValueSort :
    Nonempty (ConvT natEnvU 1 []
      (instantiate0
        (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
        (.pi (.sort .zero) (.bvar 0)))
      (instantiate0 (instantiate0 (.sort .zero) (.bvar 0))
        (.pi (.sort .zero) (.bvar 0)))
      (.sort (.imax (.succ .zero) .zero))) :=
  convTInst0ValueSort natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    (HasTyT.sort [] (.succ .zero))
    (HasTyT.pi [LocalDecl.assumption (.sort (.succ .zero))]
      (.sort .zero) (.succ .zero) (.bvar 0) .zero
      (HasTyT.sort [LocalDecl.assumption (.sort (.succ .zero))] .zero)
      (HasTyT.bvar
        [LocalDecl.assumption (.sort .zero),
          LocalDecl.assumption (.sort (.succ .zero))]
        0 (.sort .zero) rfl))
    (ConvT.beta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (HasTyT.sort [] (.succ .zero))
      (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0
        (.sort (.succ .zero)) rfl)
      (HasTyT.sort [] .zero))

/-! ## the refutation of the dispatched statement -/

/-- the source const is typable at `n = 1`: `param 0` is in bounds, and
    `natRecMemberU.arity = 1` makes the one-level list the right length. -/
def parRedSRT_constsSrcTyped :
    HasTyT natEnvU 1 [] (.const 3 [.imax (.param 0) .zero])
      (instantiateLevels [.imax (.param 0) .zero] natRecMemberU.mtype) :=
  HasTyT.const [] 3 [.imax (.param 0) .zero] natRecMemberU rfl rfl rfl

/-- the step is a legal `ParRed.consts`: the two level lists are `=ₙ`-equal
    (the imax-zero mask). -/
def parRedSRT_constsStep :
    ParRed natEnvU 1 [] (.const 3 [.imax (.param 0) .zero])
      (.const 3 [.imax (.param 5) .zero]) :=
  ParRed.consts [] 3 [.imax (.param 0) .zero] [.imax (.param 5) .zero]
    ⟨eqN_imaxParam_zero 0 5, trivial⟩

/-- the target const is typable at NO type: every const typing bounds its level
    list (forking through the `.conv` wrappers), and `param 5` is out of bounds
    at `n = 1`. -/
theorem parRedSRT_constsTgtUntyped (T : Expr Nat) :
    ¬ Nonempty (HasTyT natEnvU 1 [] (.const 3 [.imax (.param 5) .zero]) T) := by
  intro h
  obtain ⟨ht⟩ := h
  obtain ⟨m, _, _, hwf, _⟩ := hasTyTInv_const (r := 3) ht rfl
  exact absurd hwf (by decide)

/-- the dispatched goal, verbatim shape. -/
def ParRedSRTClaim : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (_hP : hW.InScope) {n : Nat} {Γ : LCtx}
    (_hΓ : CtxWfT E n Γ),
    {e A e' : Expr Nat}→ HasTyT E n Γ e A → ParRed E n Γ e e' →
    Nonempty (HasTyT E n Γ e' A)

/-- THE REFUTATION: on the real in-scope environment `natEnvU`, at `n = 1`,
    `Γ = []`, one parallel `consts` step takes a typed const to an untypable
    one. The typed judgment's `levelsBounded` side condition is not preserved
    by `eqNList` level drift; fixing this is a rule decision (strengthen
    `ParRed.consts`, or normalize levels in the typed const rule), not a lemma. -/
theorem parRedSRT_claimFalse : ¬ ParRedSRTClaim := by
  intro h
  have hout := h natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    parRedSRT_constsSrcTyped parRedSRT_constsStep
  exact hout.elim fun hT => parRedSRT_constsTgtUntyped _ ⟨hT⟩

/-! ## the sortEq arm's inversion (documented route helper) -/

/-- sort-inversion, typed: every typing of `.sort l` reads the type as a
    `TyConvT` from `.sort (.succ l)`. The `sortEq` arm of the would-be mutual
    closes by `convT_of_tyConv (.sorts Γ l₁ l₂ hl) (hasTyTInv_sortT h rfl)`. -/
def hasTyTInv_sortT {E : ResolvedEnv} {n : Nat} {l : Level} :
    {Γ : LCtx}→ {e T : Expr Nat}→ HasTyT E n Γ e T → e = .sort l →
    TyConvT E n Γ (.sort (.succ l)) T
  | _, _, _, .sort _ _, heq => by
      injection heq with hl
      subst hl
      exact .refl _ _
  | _, _, _, .conv _ _ _ _ _ h hc, heq =>
      .trans _ _ _ _ (hasTyTInv_sortT h heq) (.of _ _ _ _ hc)
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq


/-! ## R-2 (architect ruling 2026-10-09): the sort-typing invariant through the annotation bridge

`parRedSRT`'s beta/zeta/iotaSpine arms need "every type-index of a `HasTyT`
derivation is sort-typed". Obtained the way the other seven counterparts obtain
facts: IN SCOPE, THROUGH THE COPY — annotate (`annHasTyT'`), read the copy's own
sort-typing of the annotated type, erase back (`hasTyT_of_hasTyA`); the AnnEnvA
arrives through the semantic-prefix bridge (`annEnvA_of_envWfT_semPrefix`). The
const arm at arity > 0 is covered by the copy's RULE ITSELF: `HasTyA.const`
carries `hT : HasTyA … (instantiateLevelsA ls m.mtypeA) (.sort u)` as a field.
NO parallel lemma on `HasTyT`, no `parRedSRT` premise. -/

/-- COPY SIDE: every type of a copy-typed term is sort-typed — the copy's
    `hasTyA_type_subst` at the identity substitution (`substTyA_id`).
    Each arm reads the annotated rule's own type-side premise: bvar's `hA`,
    const's `hT` (the arity > 0 const arm included), pi/lam's
    domain/codomain sorts, app/letE's `hTy`, lit's recursion into the
    expansion, conv's `hB`. -/
def hasTyA_type_sort {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    {e A : ExprA}→ HasTyA E I n Γ e A → Σ u : Level, HasTyA E I n Γ A (.sort u)
  | _, _, h => by
    have hs := hasTyA_type_subst hE hI hR hIS (substTyA_id hE hI hΓ) h
    rw [substA_id] at hs
    exact hs

/-- R-2, adapter form (the `hasTyT_sort_of_convT` shape, `RcicAnnRowsSupply`):
    every type-index of a `HasTyT` derivation is sort-typed, through the
    copy. The packaging is the `Nonempty`-style Prop `∃ w, Nonempty …` —
    HasTyT is Type-valued, and consumers (`parRedSRT`-shaped proofs,
    `Nonempty`-concluded) destructure it inside their own Prop goals. -/
theorem hasTyT_type_sort_exists {E : ResolvedEnvA} (C : AnnEnvA E) (hn : EnvNormEraseA E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ) {e T : Expr Nat}
    (h : HasTyT (eraseEnv E) n Γ e T) :
    ∃ w : Level, Nonempty (HasTyT (eraseEnv E) n Γ T (.sort w)) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨eA, TA, _he, hT, ⟨tA⟩⟩ := annHasTyT' C hn h hΓA hctx
  obtain ⟨w, hw⟩ :=
    hasTyA_type_sort C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓA tA
  obtain ⟨hW⟩ := C.wf
  obtain ⟨t'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) hw
  rw [hT, hctx] at t'
  exact ⟨w, ⟨t'⟩⟩

/-- R-2 at the scope, the packaging `parRedSRT` consumes: over `EnvWfT` +
    `hW.InScope` (judgment side), through the semantic-prefix bridge. -/
theorem hasTyT_type_sort_exists_scope {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (h : HasTyT E n Γ e T) :
    ∃ w : Level, Nonempty (HasTyT E n Γ T (.sort w)) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_type_sort_exists C hn hΓ h

/-- PIN: R-2 consumed on `natEnvU` at the refuted step's own source — the
    const arm at arity 1 > 0: the masked instantiation's type is sort-typed
    through the bridge. -/
theorem pin_hasTyT_type_sort_typed :
    ∃ w : Level, Nonempty (HasTyT natEnvU 1 []
      (instantiateLevels [.imax (.param 0) .zero] natRecMemberU.mtype) (.sort w)) :=
  hasTyT_type_sort_exists_scope natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
     parRedSRT_constsSrcTyped

/-- 02 §14 DT-007 (typing regularity), the O2S counterpart name for the
    typed root: `hasTyT_type_sort_exists_scope` itself, named under the
    DT lane's convention now that `[DT007T_seal_collision]` is closed —
    SRTyped co-imports with SR after the six-helper dedupe. -/
theorem DT007T_typing_regularity {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (h : HasTyT E n Γ e T) :
    ∃ w : Level, Nonempty (HasTyT E n Γ T (.sort w)) :=
  hasTyT_type_sort_exists_scope hW hP hΓ h

/-- PIN (DT-007T): `pin_hasTyT_type_sort_typed` under the census name —
    regularity consumed on `natEnvU`. -/
theorem pin_DT007T_natU :
    ∃ w : Level, Nonempty (HasTyT natEnvU 1 []
      (instantiateLevels [.imax (.param 0) .zero] natRecMemberU.mtype) (.sort w)) :=
  pin_hasTyT_type_sort_typed

/- The iotaSpine measurement this section's DELETED lemma once encoded, kept
    as history: `hlhs` equates `iotaLhsOf w2` (heads `.const w2.recRef w2.ls` /
    `.const w2.ctorRef w2.lsC` by construction) with the reduced spine at the
    SAME witness lists — the constructor's `hlsR`/`hlsC` remain the drift
    channels into the SOURCE spine's heads, and R-1″'s `levelsIn` reads the
    witness lists to close them (see the R-1″ record in the header). `sortEq`
    needs no bound premise: `HasTyT.sort` (`RcicDeclarative.lean:3185`) has
    none, so the arm closes by
    `convT_of_tyConv (.sorts Γ l₁ l₂ h) (hasTyTInv_sortT h rfl)` as before. -/


/-! ## R-1″ (A): the `levelsIn` scope predicate — the content rule at ONE arm

DECIDABLE (Bool-valued), a recursion over the EXISTING `ParRed` — no rule is
copied or edited. The CONTENT RULE (every list a level-equality premise
carries into the target must be in the level context; `sortEq` exempt —
`HasTyT.sort` has no bound premise) is realized at the enumeration's sites:
the `.consts` arm checks the TARGET list (`ls'`), and — THE R-1″ CHANGE, the
ONE arm touched — the `.iotaSpine` arm additionally checks
`levelsBounded n w2.ls` AND `levelsBounded n w2.lsC` (the constructor's own
lists, which the third eqN-drift channel `hlsR`/`hlsC` carries into the
reduced spine's heads). Every other arm conjoins its sub-derivations
(`beta`/`lam`/`pi`/`letE`/`zeta` include their type-level `ParRed` premise);
`refl`/`sortEq`/`delta`/`lit` are `true` (delta's `ls` comes from the
source — ruled fine). -/
mutual
def levelsIn {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ {e e' : Expr Nat}→ ParRed E n Γ e e' → Bool
  | _, _, _, .refl _ _ => true
  | _, _, _, .sortEq _ _ _ _ => true
  | _, _, _, .consts _ _ _ ls' _ => levelsBounded n ls'
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => levelsIn hv
  | _, _, _, .delta _ _ _ _ _ _ _ _ => true
  | _, _, _, .app _ _ _ _ _ hf ha => levelsIn hf && levelsIn ha
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha =>
      levelsIn hA && levelsIn hb && levelsIn ha
  | _, _, _, .lam _ _ _ _ _ hA hb => levelsIn hA && levelsIn hb
  | _, _, _, .pi _ _ _ _ _ hA hb => levelsIn hA && levelsIn hb
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      levelsIn hA && levelsIn hv && levelsIn hb
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb =>
      levelsIn hA && levelsIn hv && levelsIn hb
  | _, _, _, .iotaSpine _ w2 _ _ _ _ _ _ _ _ hf ha _ _ _ =>
      levelsBounded n w2.ls && levelsBounded n w2.lsC &&
        (levelsInArgs hf && levelsInArgs ha)
  | _, _, _, .lit _ _ => true

def levelsInArgs {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ {xs ys : List (Expr Nat)}→ ParRedArgs E n Γ xs ys → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons h t => levelsIn h && levelsInArgs t
end

/- The R-1′ CONSTS-ONLY predicate, preserved VERBATIM (the iotaSpine arm is
    the spine conjunction only, no witness bounds): the enumeration R-1′
    settled on, and the one `parRedSRT_levelsIn_claimFalse` refutes — kept so
    the refutation stays a living theorem documenting WHY consts-only failed
    (the third eqN-dr channel is the iotaSpine heads, which the consts-only
    enumeration never reads). -/
mutual
def levelsInR1 {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ {e e' : Expr Nat}→ ParRed E n Γ e e' → Bool
  | _, _, _, .refl _ _ => true
  | _, _, _, .sortEq _ _ _ _ => true
  | _, _, _, .consts _ _ _ ls' _ => levelsBounded n ls'
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => levelsInR1 hv
  | _, _, _, .delta _ _ _ _ _ _ _ _ => true
  | _, _, _, .app _ _ _ _ _ hf ha => levelsInR1 hf && levelsInR1 ha
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha =>
      levelsInR1 hA && levelsInR1 hb && levelsInR1 ha
  | _, _, _, .lam _ _ _ _ _ hA hb => levelsInR1 hA && levelsInR1 hb
  | _, _, _, .pi _ _ _ _ _ hA hb => levelsInR1 hA && levelsInR1 hb
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      levelsInR1 hA && levelsInR1 hv && levelsInR1 hb
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb =>
      levelsInR1 hA && levelsInR1 hv && levelsInR1 hb
  | _, _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ hf ha _ _ _ =>
      levelsInR1Args hf && levelsInR1Args ha
  | _, _, _, .lit _ _ => true

def levelsInR1Args {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ {xs ys : List (Expr Nat)}→ ParRedArgs E n Γ xs ys → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons h t => levelsInR1 h && levelsInR1Args t
end

/-! ## R-1″ (C): the supply lemma's J-helpers -/

theorem levelsInArgs_parRedArgs_refl (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ∀ (xs : List (Expr Nat)),
      levelsInArgs (parRedArgs_refl (E := E) (n := n) (Γ := Γ) xs) = true := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [parRedArgs_refl, levelsInArgs, levelsIn, ih, Bool.and_true]

/-- J-helper for the source-side transport `step_to_parRed`'s iota arm
    performs (`Eq.mpr` along a congrArg of the spine equation): `levelsIn`
    is invariant under it. -/
theorem levelsIn_eq_mpr {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {tgt : Expr Nat} :
    {src e2 : Expr Nat}→ (he : src = e2)→
    {sp : ParRed E n Γ e2 tgt}→
    levelsIn (Eq.mpr (congrArg (fun e => ParRed E n Γ e tgt) he) sp)
      = levelsIn sp := by
  intro src e2 he sp
  subst he
  rfl

/-- the target-side dual (the `▸` inside the zetaLocal arm). -/
theorem levelsIn_eq_mpr_tgt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {src : Expr Nat} :
    {tgt tgt2 : Expr Nat}→ (he : tgt = tgt2)→
    {sp : ParRed E n Γ src tgt2}→
    levelsIn (Eq.mpr (congrArg (fun x => ParRed E n Γ src x) he) sp)
      = levelsIn sp := by
  intro tgt tgt2 he sp
  subst he
  rfl

/-! ### the typed source's spine-head bounds (the ι supply's engine) -/

/-- `foldApps_cons_is_app` (the `RcicParRedIota` toolbox, Σ'-form) says a
    nonempty `foldApps` spine is `.app`-headed; this companion DECOMPOSES a
    nonempty spine that equals an `.app`: the function is the SAME spine,
    strictly shorter, at one fewer leading argument. -/
def foldApps_cons_eq_app_inv {c x : Expr Nat} :
    (xs : List (Expr Nat))→ {f a : Expr Nat}→
    foldApps c (x :: xs) = .app f a →
    Σ' init : List (Expr Nat), x :: xs = init ++ [a] ∧ f = foldApps c init
  | [], f, a, h => by
      injection h with hf ha
      subst ha
      subst hf
      exact ⟨[], rfl, rfl⟩
  | y :: ys, f, a, h =>
      match foldApps_cons_eq_app_inv (c := .app c x) ys h with
      | ⟨init, hargs, hf⟩ =>
          ⟨x :: init, by simp only [List.cons_append, hargs], hf⟩

/-- THE SPINE-HEAD BOUND: every typing of a const-headed `foldApps` spine
    bounds the head's level list — by recursion on the TYPING (the `.app`
    arm inverts one layer and recurses into the function's typing at a
    strictly shorter spine; the `.conv` arm peels; every other arm is
    source-disjoint with the head shape, by the `.app`-headedness of
    nonempty spines). This is the typed source's own content —
    `HasTyT.const`'s `hwf` read off however deep the spine sits. -/
def hasTyTConstSpineBound {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (r : Nat)
    (ls : List Level) :
    {e T : Expr Nat}→ HasTyT E n Γ e T → (args : List (Expr Nat))→
    e = foldApps (.const r ls) args → levelsBounded n ls = true
  | _, _, .const _ _ _ _ _ _ hwf, args, heq => by
      cases args with
      | nil =>
          simp only [foldApps] at heq
          injection heq with _ hls
          subst hls
          exact hwf
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .app _ f a _ _ hf _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨init, hargs, hfinit⟩ :=
            foldApps_cons_eq_app_inv (c := .const r ls) xs heq.symm
          subst hfinit
          exact hasTyTConstSpineBound r ls hf init rfl
  | _, _, .conv _ _ _ _ _ h _, args, heq =>
      hasTyTConstSpineBound r ls h args heq
  | _, _, .sort _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .bvar _ _ _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .lam _ _ _ _ _ _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .letE _ _ _ _ _ _ _ _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq
  | _, _, .lit _ _ _ _, args, heq => by
      cases args with
      | nil => simp only [foldApps] at heq; nomatch heq
      | cons x xs =>
          obtain ⟨g, a, hfa⟩ := foldApps_cons_is_app (.const r ls) x xs
          rw [hfa] at heq
          nomatch heq

/-! ## R-1″ (C): the supply lemma, conditioned on the SOURCE TYPING -/

/-- MEASUREMENT (re-done, matching cc's): `step_to_parRed` (`RcicConvChar.lean:455`)
has SIX arms — `.beta`/`.zeta` build with refl-premises, `.zetaLocal` builds
`.bvarZeta` with a refl premise, `.delta` re-exports delta, `.iota` builds
`.iotaSpine` at the SOURCE's own lists (`w.ls`/`w.lsC`, eqNList-refl heads,
`parRedArgs_refl` spines), `.lit` re-exports lit. NONE constructs `.consts`
or `.sortEq`. Under the R-1″ predicate the ι arm's bounds come from the
TYPED SOURCE (`h : HasTyT E n Γ a T`, `a = iotaLhsOf w`): the recursor head
bounds `w.ls` directly (`hasTyTConstSpineBound` on the whole redex spine),
and one app-inversion exposes the major, whose constructor head bounds
`w.lsC` — "the typed source spine-inverts to bounded heads". The other five
arms do not read the typing. The typed source is not a new obligation: SR's
consumers already hold it. -/
theorem step_to_parRed_levelsIn {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ {a b : Expr Nat}→ (hs : Step E n Γ a b)→
    {T : Expr Nat}→ HasTyT E n Γ a T →
    levelsIn (step_to_parRed hs) = true
  | _, _, _, .beta _ _ _ _, _, _ => rfl
  | _, _, _, .zeta _ _ _ _, _, _ => rfl
  | _, _, _, .zetaLocal Γ i v h, _, _ => by
      simp only [step_to_parRed]
      split
      · next A v0 hg =>
          have hv : v = lift 0 (i + 1) v0 := by
            simp only [lookupValue, hg] at h
            exact Option.some.inj h.symm
          subst hv
          first
          | rfl
          | (rw [levelsIn_eq_mpr_tgt]; rfl)
      · next hg => simp only [lookupValue, hg] at h; cases h
      · next hg => simp only [lookupValue, hg] at h; cases h
  | _, _, _, .delta _ _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, .iota _ _ _ hι, _, hT => by
      cases hι with
      | of w =>
          simp only [step_to_parRed]
          have he : iotaLhsOf w = recCall (.const w.recRef w.ls) w.preMajor
              (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) := by
            simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]
          rw [he] at hT
          -- the typed source spine-inverts to bounded heads:
          have hwfR : levelsBounded n w.ls = true :=
            hasTyTConstSpineBound w.recRef w.ls hT (w.preMajor ++ [ctorMajor w]) rfl
          simp only [recCall] at hT
          rw [foldApps_snoc] at hT
          obtain ⟨_, _, _, harg, _⟩ := hasTyTInv_app hT rfl
          have hwfC : levelsBounded n w.lsC = true :=
            hasTyTConstSpineBound w.ctorRef w.lsC harg (w.ctorParams ++ w.fields) rfl
          rw [levelsIn_eq_mpr he]
          simp only [levelsIn, levelsInArgs_parRedArgs_refl, hwfR, hwfC,
            Bool.true_and, Bool.and_true]
  | _, _, _, .lit _ t _ h, _, _ => by
      simp only [step_to_parRed]
      cases h
      rfl

/-! ## R-1′ infrastructure — everything built BESIDE, nothing legacy edited -/

/-- a let-binding's value at a `get?` index, in `lookupValue` spelling. -/
theorem lookupValue_getQ_letBinding {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v)) :
    lookupValue Γ i = some (lift 0 (i + 1) v) := by
  simp only [lookupValue, h]

/- the replaced-index type/value readouts (`lookupType_replace_let_*`,
   `lookupValue_replace_let_*`) moved to `RcicConvChar` — single-owned
   there, imported here. carve-out-removal: [DT007T_seal_collision].
   `get?_lt_length` moved with them. -/

/-- the typed mirror of `ctxWf_drop` (`RcicInvertFamily`): tails of a
    well-formed typed context are well-formed. -/
def ctxWfT_drop {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ CtxWfT E n Γ → (k : Nat) → CtxWfT E n (Γ.drop k)
  | _, h, 0 => by simp only [List.drop_zero]; exact h
  | _, .nil, _k + 1 => .nil
  | _, .assumption _ _ _ hΓ _, k + 1 => ctxWfT_drop hΓ k
  | _, .letBinding _ _ _ _ hΓ _ _, k + 1 => ctxWfT_drop hΓ k

/-- the UNTRANSPORTED value typing `ParRed.bvarZeta` needs (the typed mirror
    of `ctxWfLookupValueAt`): the stored value is typed at its stored type in
    the tail below its own binder — no lifting applied. -/
def ctxWfTLookupValueAtDrop {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx}→ CtxWfT E n Γ → (i : Nat)→ {A v : Expr Nat}→
    Γ.get? i = some (.letBinding A v) → HasTyT E n (Γ.drop (i + 1)) v A
  | _, .nil, _, _, _, h => Option.noConfusion h
  | _, .assumption Γ0 A0 _ hΓ _, i, _, _, h => by
      cases i with
      | zero =>
          have he : (LocalDecl.assumption A0 :: Γ0).get? 0 =
              some (LocalDecl.assumption A0) := rfl
          rw [he] at h
          injection h with h1
          exact LocalDecl.noConfusion h1
      | succ i' =>
          have he : (LocalDecl.assumption A0 :: Γ0).get? (i' + 1) = Γ0.get? i' := rfl
          rw [he] at h
          have rec := ctxWfTLookupValueAtDrop hΓ i' h
          simpa only [List.drop_succ_cons] using rec
  | _, .letBinding Γ0 A0 _ v0 hΓ _ hv0, i, _, _, h => by
      cases i with
      | zero =>
          have he : (LocalDecl.letBinding A0 v0 :: Γ0).get? 0 =
              some (LocalDecl.letBinding A0 v0) := rfl
          rw [he] at h
          injection h with hd
          injection hd with hA0 hv00
          subst hA0; subst hv00
          exact hv0
      | succ i' =>
          have he : (LocalDecl.letBinding A0 v0 :: Γ0).get? (i' + 1) =
              Γ0.get? i' := rfl
          rw [he] at h
          have rec := ctxWfTLookupValueAtDrop hΓ i' h
          simpa only [List.drop_succ_cons] using rec

/-! ### the prefix-lift pair (typed, mutual)

`ParRed.bvarZeta`'s premises live in `Γ.drop (i+1)`; the outputs must be
carried back into `Γ = Γ.take (i+1) ++ Γ.drop (i+1)` by multi-weakening under
the prefix. One pair serves the typing, one the conversion; the two
`...PrefixDecl` singletons weaken a premise under a prefix ending in one
declaration (the morphisms' bvar repairs). -/
mutual
def hasTyTLiftPrefix {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    (Δ : LCtx)→ {Γ' : LCtx}→ {e A : Expr Nat}→
    HasTyT E n Γ' e A →
    HasTyT E n (Δ ++ Γ') (lift 0 Δ.length e) (lift 0 Δ.length A)
  | [], _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]; exact h
  | d :: Δ, Γ', e, A, h => by
      have ih := hasTyTLiftPrefix hcl Δ h
      have hw := hasTyTWeaken d hcl (c := 0) ih
      simp only [insertAt_zero] at hw
      rw [lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) e,
          lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) A] at hw
      simp only [List.cons_append, List.length_cons, Nat.add_comm] at hw ⊢
      exact hw

def convTLiftPrefix {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E) :
    (Δ : LCtx)→ {Γ' : LCtx}→ {a b T : Expr Nat}→
    ConvT E n Γ' a b T →
    ConvT E n (Δ ++ Γ') (lift 0 Δ.length a) (lift 0 Δ.length b)
      (lift 0 Δ.length T)
  | [], _, _, _, _, c => by
      simp only [List.nil_append, List.length_nil, lift_zero]; exact c
  | d :: Δ, Γ', a, b, T, c => by
      have ih := convTLiftPrefix hcl Δ c
      have hw := convTWeaken d hcl (c := 0) ih
      simp only [insertAt_zero] at hw
      rw [lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) a,
          lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) b,
          lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) T] at hw
      simp only [List.cons_append, List.length_cons, Nat.add_comm] at hw ⊢
      exact hw
end

def hasTyTLiftPrefixDecl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hcl : EnvClosed E) (Δ : LCtx) (d : LocalDecl) {e A : Expr Nat}
    (h : HasTyT E n Γ e A) :
    HasTyT E n (Δ ++ d :: Γ) (lift 0 (Δ.length + 1) e)
      (lift 0 (Δ.length + 1) A) := by
  have hw := hasTyTLiftPrefix hcl (Δ ++ [d]) h
  have hlen : (Δ ++ [d]).length = Δ.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hctx : (Δ ++ [d]) ++ Γ = Δ ++ d :: Γ := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hlen, hctx] at hw
  exact hw

def convTLiftPrefixDecl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hcl : EnvClosed E) (Δ : LCtx) (d : LocalDecl) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    ConvT E n (Δ ++ d :: Γ) (lift 0 (Δ.length + 1) a)
      (lift 0 (Δ.length + 1) b) (lift 0 (Δ.length + 1) T) := by
  have hw := convTLiftPrefix hcl (Δ ++ [d]) h
  have hlen : (Δ ++ [d]).length = Δ.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hctx : (Δ ++ [d]) ++ Γ = Δ ++ d :: Γ := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hlen, hctx] at hw
  exact hw

/-! ### the typed context-morphism pairs (assumption + letBinding)

The `hasTyTConvAssump`-analogue the ruling named: no typed copy version
exists (measured — `ConvAssump`/`convAssump`/`hasTyA_conv` grep hits only the
legacy `RcicConvChar`/`RcicParRedSR`), so built by induction beside, mirroring
those templates on `ConvT`'s constructor set. The assumption pair needs no
extra premise (an assumption carries no value, so the `zetaLocal` arm is
IMPOSSIBLE at the replaced index and unchanged away from it). The letBinding
pair (the `hasTyConvLet` analogue) carries the new value's typing: at the
replaced index the value lookup CHANGES, so the `zetaLocal` arm rebuilds at
the new value and converts back along the weakened value conversion. -/
mutual
def convTConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hc : ConvT E n Γ A' A (.sort u)) :
    (Δ : LCtx)→ {a b T : Expr Nat}→
    ConvT E n (Δ ++ LocalDecl.assumption A :: Γ) a b T →
    ConvT E n (Δ ++ LocalDecl.assumption A' :: Γ) a b T
  | Δ, _, _, _, .refl _ _ _ h => .refl _ _ _ (hasTyTConvAssumpAt hcl hc Δ h)
  | Δ, _, _, _, .symm _ _ _ _ h => .symm _ _ _ _ (convTConvAssumpAt hcl hc Δ h)
  | Δ, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      .trans _ _ _ _ _ (convTConvAssumpAt hcl hc Δ h1)
        (convTConvAssumpAt hcl hc Δ h2)
  | Δ, _, _, _, .beta _ A0 body arg B0 u0 hA hbody harg =>
      .beta _ _ _ _ _ _ (hasTyTConvAssumpAt hcl hc Δ hA)
        (hasTyTConvAssumpAt hcl hc (LocalDecl.assumption A0 :: Δ) hbody)
        (hasTyTConvAssumpAt hcl hc Δ harg)
  | Δ, _, _, _, .zeta _ A0 value body B0 u0 hA hv hb =>
      .zeta _ _ _ _ _ _ (hasTyTConvAssumpAt hcl hc Δ hA)
        (hasTyTConvAssumpAt hcl hc Δ hv)
        (hasTyTConvAssumpAt hcl hc (LocalDecl.letBinding A0 value :: Δ) hb)
  | Δ, _, _, _, .zetaLocal _ i A0 v0 hval hty hv => by
      by_cases hi : i = Δ.length
      · subst hi
        have hval0 : lookupValue (Δ ++ LocalDecl.assumption A :: Γ) Δ.length
            = none := by
          simp only [lookupValue, get?_replace_head_at]
        rw [hval0] at hval
        exact Option.noConfusion hval
      · exact .zetaLocal _ i A0 v0
          (by rw [← lookupValue_replace_assump Δ A A' Γ i]; exact hval)
          (by rw [← lookupType_replace_assump_ne Δ A A' Γ i hi]; exact hty)
          (hasTyTConvAssumpAt hcl hc Δ hv)
  | Δ, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb =>
      .delta _ r ls m b hres hbody htr hlen hwf
        (hasTyTConvAssumpAt hcl hc Δ hb)
  | Δ, _, _, _, .iota _ lhs rhs T hd hlhs hrhs =>
      .iota _ lhs rhs T hd (hasTyTConvAssumpAt hcl hc Δ hlhs)
        (hasTyTConvAssumpAt hcl hc Δ hrhs)
  | Δ, _, _, _, .lit _ t exp T hd hexp =>
      .lit _ t exp T hd (hasTyTConvAssumpAt hcl hc Δ hexp)
  | Δ, _, _, _, .app _ _ _ _ _ _ _ h1 h2 =>
      .app _ _ _ _ _ _ _ (convTConvAssumpAt hcl hc Δ h1)
        (convTConvAssumpAt hcl hc Δ h2)
  | Δ, _, _, _, .lam _ _ _ _ _ _ _ hA hb =>
      .lam _ _ _ _ _ _ _ (convTConvAssumpAt hcl hc Δ hA)
        (convTConvAssumpAt hcl hc (LocalDecl.assumption _ :: Δ) hb)
  | Δ, _, _, _, .pi _ _ _ _ _ _ _ hA hB =>
      .pi _ _ _ _ _ _ _ (convTConvAssumpAt hcl hc Δ hA)
        (convTConvAssumpAt hcl hc (LocalDecl.assumption _ :: Δ) hB)
  | Δ, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      .letE _ _ _ _ _ _ _ _ _ (convTConvAssumpAt hcl hc Δ hA)
        (convTConvAssumpAt hcl hc Δ hv)
        (convTConvAssumpAt hcl hc (LocalDecl.letBinding _ _ :: Δ) hb)
  | _, _, _, _, .sorts _ _ _ h => .sorts _ _ _ h
  | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h => .consts _ _ _ _ _ hres hlen hwf hwf' h
  | Δ, _, _, _, .eta _ _ _ _ hh => .eta _ _ _ _ (hasTyTConvAssumpAt hcl hc Δ hh)
  | Δ, _, _, _, .irr _ _ _ _ hP hp hq =>
      .irr _ _ _ _ (hasTyTConvAssumpAt hcl hc Δ hP)
        (hasTyTConvAssumpAt hcl hc Δ hp) (hasTyTConvAssumpAt hcl hc Δ hq)
  | Δ, _, _, _, .tyConv _ _ _ _ _ _ h hT =>
      .tyConv _ _ _ _ _ _ (convTConvAssumpAt hcl hc Δ h)
        (convTConvAssumpAt hcl hc Δ hT)

def hasTyTConvAssumpAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hc : ConvT E n Γ A' A (.sort u)) :
    (Δ : LCtx)→ {e T : Expr Nat}→
    HasTyT E n (Δ ++ LocalDecl.assumption A :: Γ) e T →
    HasTyT E n (Δ ++ LocalDecl.assumption A' :: Γ) e T
  | _, _, _, .sort _ _ => .sort _ _
  | Δ, _, _, .bvar _ i T h => by
      by_cases hi : i = Δ.length
      · subst hi
        have h0 : lookupType (Δ ++ LocalDecl.assumption A :: Γ) Δ.length =
            some (lift 0 (Δ.length + 1) A) := lookupType_replace_assump_zero Δ A Γ
        have heq : some T = some (lift 0 (Δ.length + 1) A) := h.symm.trans h0
        injection heq with hTeq
        subst hTeq
        have hcL : ConvT E n (Δ ++ LocalDecl.assumption A' :: Γ)
            (lift 0 (Δ.length + 1) A') (lift 0 (Δ.length + 1) A) (.sort u) :=
          convTLiftPrefixDecl hcl Δ (LocalDecl.assumption A') hc
        exact .conv _ _ _ _ u
          (.bvar _ Δ.length _ (lookupType_replace_assump_zero Δ A' Γ)) hcL
      · exact .bvar _ i T
          (by rw [← lookupType_replace_assump_ne Δ A A' Γ i hi]; exact h)
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m hres hlen hwf
  | Δ, _, _, .pi _ _ u0 _ v hA hB =>
      .pi _ _ u0 _ v (hasTyTConvAssumpAt hcl hc Δ hA)
        (hasTyTConvAssumpAt hcl hc (LocalDecl.assumption _ :: Δ) hB)
  | Δ, _, _, .lam _ _ u0 _ _ hA hbody =>
      .lam _ _ u0 _ _ (hasTyTConvAssumpAt hcl hc Δ hA)
        (hasTyTConvAssumpAt hcl hc (LocalDecl.assumption _ :: Δ) hbody)
  | Δ, _, _, .app _ _ _ _ _ hf ha =>
      .app _ _ _ _ _ (hasTyTConvAssumpAt hcl hc Δ hf)
        (hasTyTConvAssumpAt hcl hc Δ ha)
  | Δ, _, _, .letE _ _ u0 _ _ _ hA hv hb =>
      .letE _ _ u0 _ _ _ (hasTyTConvAssumpAt hcl hc Δ hA)
        (hasTyTConvAssumpAt hcl hc Δ hv)
        (hasTyTConvAssumpAt hcl hc (LocalDecl.letBinding _ _ :: Δ) hb)
  | Δ, _, _, .conv _ _ _ _ u0 h hcc =>
      .conv _ _ _ _ u0 (hasTyTConvAssumpAt hcl hc Δ h)
        (convTConvAssumpAt hcl hc Δ hcc)
  | Δ, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyTConvAssumpAt hcl hc Δ hexp)
end

def hasTyTConvAssump {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hc : ConvT E n Γ A' A (.sort u)) {e T : Expr Nat} :
    HasTyT E n (LocalDecl.assumption A :: Γ) e T →
    HasTyT E n (LocalDecl.assumption A' :: Γ) e T :=
  hasTyTConvAssumpAt hcl hc []

mutual
def convTConvLetAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hcA : ConvT E n Γ A' A (.sort u)) (hcv : ConvT E n Γ v' v A)
    (hv'A' : HasTyT E n Γ v' A') :
    (Δ : LCtx)→ {a b T : Expr Nat}→
    ConvT E n (Δ ++ LocalDecl.letBinding A v :: Γ) a b T →
    ConvT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ) a b T
  | Δ, _, _, _, .refl _ _ _ h =>
      .refl _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ h)
  | Δ, _, _, _, .symm _ _ _ _ h => .symm _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ h)
  | Δ, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      .trans _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ h1)
        (convTConvLetAt hcl hcA hcv hv'A' Δ h2)
  | Δ, _, _, _, .beta _ A0 body arg B0 u0 hA hbody harg =>
      .beta _ _ _ _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (hasTyTConvLetAt hcl hcA hcv hv'A' (LocalDecl.assumption A0 :: Δ) hbody)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ harg)
  | Δ, _, _, _, .zeta _ A0 value body B0 u0 hA hv hb =>
      .zeta _ _ _ _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hv)
        (hasTyTConvLetAt hcl hcA hcv hv'A' (LocalDecl.letBinding A0 value :: Δ) hb)
  | Δ, _, _, _, .zetaLocal _ i A0 v0 hval hty hv => by
      by_cases hi : i = Δ.length
      · subst hi
        have hvq : lookupValue (Δ ++ LocalDecl.letBinding A v :: Γ) Δ.length =
            some (lift 0 (Δ.length + 1) v) := lookupValue_replace_let_zero Δ A v Γ
        have heq : some v0 = some (lift 0 (Δ.length + 1) v) :=
          hval.symm.trans hvq
        injection heq with hv0
        subst hv0
        have hTq : lookupType (Δ ++ LocalDecl.letBinding A v :: Γ) Δ.length =
            some (lift 0 (Δ.length + 1) A) := lookupType_replace_let_zero Δ A v Γ
        have hTeq : some A0 = some (lift 0 (Δ.length + 1) A) :=
          hty.symm.trans hTq
        injection hTeq with hT0
        subst hT0
        have hv'l : HasTyT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ)
            (lift 0 (Δ.length + 1) v') (lift 0 (Δ.length + 1) A') :=
          hasTyTLiftPrefixDecl hcl Δ (LocalDecl.letBinding A' v') hv'A'
        have l1 : ConvT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ)
            (.bvar Δ.length) (lift 0 (Δ.length + 1) v')
            (lift 0 (Δ.length + 1) A') :=
          ConvT.zetaLocal _ Δ.length _ _
            (lookupValue_replace_let_zero Δ A' v' Γ)
            (lookupType_replace_let_zero Δ A' v' Γ) hv'l
        have hcAL : ConvT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ)
            (lift 0 (Δ.length + 1) A') (lift 0 (Δ.length + 1) A) (.sort u) :=
          convTLiftPrefixDecl hcl Δ (LocalDecl.letBinding A' v') hcA
        have hcvL : ConvT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ)
            (lift 0 (Δ.length + 1) v') (lift 0 (Δ.length + 1) v)
            (lift 0 (Δ.length + 1) A) :=
          convTLiftPrefixDecl hcl Δ (LocalDecl.letBinding A' v') hcv
        exact ConvT.trans _ _ _ _ _
          (convT_of_tyConv l1 (TyConvT.of _ _ _ u hcAL)) hcvL
      · exact .zetaLocal _ i A0 v0
          (by rw [← lookupValue_replace_let_ne Δ A v A' v' Γ i hi]; exact hval)
          (by rw [← lookupType_replace_let_ne Δ A v A' v' Γ i hi]; exact hty)
          (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hv)
  | Δ, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb =>
      .delta _ r ls m b hres hbody htr hlen hwf
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hb)
  | Δ, _, _, _, .iota _ lhs rhs T hd hlhs hrhs =>
      .iota _ lhs rhs T hd (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hlhs)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hrhs)
  | Δ, _, _, _, .lit _ t exp T hd hexp =>
      .lit _ t exp T hd (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hexp)
  | Δ, _, _, _, .app _ _ _ _ _ _ _ h1 h2 =>
      .app _ _ _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ h1)
        (convTConvLetAt hcl hcA hcv hv'A' Δ h2)
  | Δ, _, _, _, .lam _ _ _ _ _ _ _ hA hb =>
      .lam _ _ _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (convTConvLetAt hcl hcA hcv hv'A' (LocalDecl.assumption _ :: Δ) hb)
  | Δ, _, _, _, .pi _ _ _ _ _ _ _ hA hB =>
      .pi _ _ _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (convTConvLetAt hcl hcA hcv hv'A' (LocalDecl.assumption _ :: Δ) hB)
  | Δ, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      .letE _ _ _ _ _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (convTConvLetAt hcl hcA hcv hv'A' Δ hv)
        (convTConvLetAt hcl hcA hcv hv'A' (LocalDecl.letBinding _ _ :: Δ) hb)
  | _, _, _, _, .sorts _ _ _ h => .sorts _ _ _ h
  | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h => .consts _ _ _ _ _ hres hlen hwf hwf' h
  | Δ, _, _, _, .eta _ _ _ _ hh =>
      .eta _ _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hh)
  | Δ, _, _, _, .irr _ _ _ _ hP hp hq =>
      .irr _ _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hP)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hp)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hq)
  | Δ, _, _, _, .tyConv _ _ _ _ _ _ h hT =>
      .tyConv _ _ _ _ _ _ (convTConvLetAt hcl hcA hcv hv'A' Δ h)
        (convTConvLetAt hcl hcA hcv hv'A' Δ hT)

def hasTyTConvLetAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hcA : ConvT E n Γ A' A (.sort u)) (hcv : ConvT E n Γ v' v A)
    (hv'A' : HasTyT E n Γ v' A') :
    (Δ : LCtx)→ {e T : Expr Nat}→
    HasTyT E n (Δ ++ LocalDecl.letBinding A v :: Γ) e T →
    HasTyT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ) e T
  | _, _, _, .sort _ _ => .sort _ _
  | Δ, _, _, .bvar _ i T h => by
      by_cases hi : i = Δ.length
      · subst hi
        have h0 : lookupType (Δ ++ LocalDecl.letBinding A v :: Γ) Δ.length =
            some (lift 0 (Δ.length + 1) A) := lookupType_replace_let_zero Δ A v Γ
        have heq : some T = some (lift 0 (Δ.length + 1) A) := h.symm.trans h0
        injection heq with hTeq
        subst hTeq
        have hcL : ConvT E n (Δ ++ LocalDecl.letBinding A' v' :: Γ)
            (lift 0 (Δ.length + 1) A') (lift 0 (Δ.length + 1) A) (.sort u) :=
          convTLiftPrefixDecl hcl Δ (LocalDecl.letBinding A' v') hcA
        exact .conv _ _ _ _ u
          (.bvar _ Δ.length _ (lookupType_replace_let_zero Δ A' v' Γ)) hcL
      · exact .bvar _ i T
          (by rw [← lookupType_replace_let_ne Δ A v A' v' Γ i hi]; exact h)
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m hres hlen hwf
  | Δ, _, _, .pi _ _ u0 _ w hA hB =>
      .pi _ _ u0 _ w (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (hasTyTConvLetAt hcl hcA hcv hv'A' (LocalDecl.assumption _ :: Δ) hB)
  | Δ, _, _, .lam _ _ u0 _ _ hA hbody =>
      .lam _ _ u0 _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (hasTyTConvLetAt hcl hcA hcv hv'A' (LocalDecl.assumption _ :: Δ) hbody)
  | Δ, _, _, .app _ _ _ _ _ hf ha =>
      .app _ _ _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hf)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ ha)
  | Δ, _, _, .letE _ _ u0 _ _ _ hA hv hb =>
      .letE _ _ u0 _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hA)
        (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hv)
        (hasTyTConvLetAt hcl hcA hcv hv'A' (LocalDecl.letBinding _ _ :: Δ) hb)
  | Δ, _, _, .conv _ _ _ _ u0 h hcc =>
      .conv _ _ _ _ u0 (hasTyTConvLetAt hcl hcA hcv hv'A' Δ h)
        (convTConvLetAt hcl hcA hcv hv'A' Δ hcc)
  | Δ, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyTConvLetAt hcl hcA hcv hv'A' Δ hexp)
end

def hasTyTConvLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' : Expr Nat} {u : Level} (hcl : EnvClosed E)
    (hcA : ConvT E n Γ A' A (.sort u)) (hcv : ConvT E n Γ v' v A)
    (hv'A' : HasTyT E n Γ v' A')
    {e T : Expr Nat} :
    HasTyT E n (LocalDecl.letBinding A v :: Γ) e T →
    HasTyT E n (LocalDecl.letBinding A' v' :: Γ) e T :=
  hasTyTConvLetAt hcl hcA hcv hv'A' []

/-! ### the in-range typed const-move (through `ConvT.consts` + endpoints) -/

/-- The typed `hasTyConstMove`: from `eqNList ls ls'` AND BOTH bounds the
    const retype goes through — `ConvT.consts` (which carries both bounds,
    `RcicDeclarative.lean:3253-3257`) plus `DT009T_endpoints_inScope` (the
    right endpoint reads the target const's typing at the source
    instantiation) plus the chain-collapse. No legacy judgment. -/
theorem hasTyTConstMove {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls ls' : List Level}
    (hls : eqNList ls ls') (hwf' : levelsBounded n ls' = true) {S : Expr Nat}
    (h : HasTyT E n Γ (.const r ls) S) :
    Nonempty (HasTyT E n Γ (.const r ls') S) := by
  obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const h rfl
  have hcc := ConvT.consts Γ r ls ls' m hres hlen hwf hwf' hls
  obtain ⟨_, ⟨hr⟩⟩ := DT009T_endpoints_inScope hW hP hΓ hcc
  exact ⟨hasTyT_of_tyConv hr hcv⟩

/-- the conversion form of the same move (the iotaSpine arm's head mover). -/
theorem hasTyTConstMoveConv {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls ls' : List Level}
    (hls : eqNList ls ls') (hwf' : levelsBounded n ls' = true) {S : Expr Nat}
    (h : HasTyT E n Γ (.const r ls) S) :
    Nonempty (ConvT E n Γ (.const r ls) (.const r ls') S) := by
  obtain ⟨m, hres, hlen, hwf, hcv⟩ := hasTyTInv_const h rfl
  exact ⟨convT_of_tyConv
    (ConvT.consts Γ r ls ls' m hres hlen hwf hwf' hls) hcv⟩

/-! ### the let-binder value congruence (the zeta counterpart of
`convTInst0ValueSort`)

Legacy `conv_instantiate0_value` was an UNTYPED zeta roundtrip (junk domain
`Sort 0`, no premises). The typed `ConvT.zeta` types its value at the let's
REAL domain, so the roundtrip runs at the real `(A, v)` binder with `B`
itself as the let's body: `instantiate0 v B ←ζ⁻¹ (.letE A v B)
→letE-cong (.letE A v' B) →ζ instantiate0 v' B`, all at `.sort w` because
`instantiate0 _ (.sort w) = .sort w`. The two sort-typings of `B` under the
old/new binders come from R-2 on the body typing (old) and the let-morphism
(new). -/
theorem convTInst0ValueSortLet {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v v' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ v A)
    (hv' : HasTyT E n Γ v' A)
    (hBv : HasTyT E n (LocalDecl.letBinding A v :: Γ) B (.sort w))
    (hBv' : HasTyT E n (LocalDecl.letBinding A v' :: Γ) B (.sort w))
    (hc : ConvT E n Γ v v' A) :
    Nonempty (ConvT E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w)) := by
  have l1 : ConvT E n Γ (.letE A v B) (instantiate0 v B) (.sort w) :=
    ConvT.zeta Γ A v B (.sort w) u hA hv hBv
  have l2 : ConvT E n Γ (.letE A v B) (.letE A v' B) (.sort w) :=
    ConvT.letE Γ A A v v' B B (.sort w) u
      (ConvT.refl Γ A (.sort u) hA) hc (ConvT.refl _ B (.sort w) hBv)
  have l3 : ConvT E n Γ (.letE A v' B) (instantiate0 v' B) (.sort w) :=
    ConvT.zeta Γ A v' B (.sort w) u hA hv' hBv'
  exact ⟨ConvT.trans _ _ _ _ _
    (ConvT.symm _ _ _ _ l1) (ConvT.trans _ _ _ _ _ l2 l3)⟩

/-- pin transports: the syntactic pin equations move bounds and eqNLists
    between the witness's lists and the constructor's. -/
theorem eqNList_pin {ls ls' : List Level} (h : ls = ls') : eqNList ls' ls := by
  cases h
  exact eqNList_refl _

theorem levelsBounded_pin {n : Nat} {ls ls' : List Level} (h : ls = ls')
    (hwf : levelsBounded n ls' = true) : levelsBounded n ls = true := by
  cases h
  exact hwf

/-! ## R-1″ (B): the 13-arm theorem — SEALED at every arm

HISTORY THAT RESET THE ARM (kept from the R-1′ round, updated to the settled
reading): R-1′'s iotaSpine prescription rode a syntactic pin of `hlhs`
("hlhs pins the lists, so the eqN-masks never enter"). Applied AT THE
CONSTRUCTOR that pin is VACUOUS: `ParRed.iotaSpine`'s own `hlhs`
(`RcicParRedCore.lean:191-193`) names `w2.ls`/`w2.lsC` in the head
positions — the pin degenerates to `w2.ls = w2.ls`. The ACTUAL drift
channels at this arm are the constructor's OWN `hlsR : eqNList w2.ls lsR`
and `hlsC : eqNList w2.lsC lsC` — the same imax-zero masks the consts
refutation used — and `IotaWitness`'s `ls`/`lsC` fields carry no bounds
(the struct's own doc: "Consistency is a typing premise of IotaPreserve,
not redux identity", `RcicDeclarative.lean:2180`).

So the arm needs

    ⊢ levelsBounded n w2.ls = true
    ⊢ levelsBounded n w2.lsC = true

(the REDUCED spine `iotaLhsOf w2`'s heads — every route to `hlhsTy` for
`iotaPreserveT` types a `(.const w2.recRef w2.ls)`- or
`(.const w2.ctorRef w2.lsC)`-headed term: `HasTyT.const`, `ConvT.consts`,
and `DT009T_endpoints_inScope` all demand the bounds), and the R-1′
consts-only `levelsIn` could not supply them — machine-checked by the
countermodel below: the source TYPED at the drifted witness
(`parRedSRT_iotaSrcTyped`, through the impredicative-Prop motive
`icmTrue`), the step IN the consts-only fragment (`parRedSRT_iotaStep`,
refl spines, `parRedSRT_iotaStep_levelsInR1`), the reduct typable at NO
type (`parRedSRT_iotaTgtUntyped`) — `parRedSRT_levelsIn_claimFalse`, the
consts-only claim FALSE (kept as a true theorem on `levelsInR1`). The
R-1′ round closed with the reading "the bounds must live on the WITNESS";
R-1″ corrected it: `w2` is a constructor PARAMETER, so the DERIVATION
predicate reads the witness lists directly — `levelsIn`'s iotaSpine arm
now carries exactly the two bounds above, the counterexample's
`[.imax (.param 5) .zero]` is excluded (tooth
`parRedSRT_iotaStep_levelsInFalse`), and the arm closes.

THE SEALED ARM (below, in the `parRedConvT`/`parRedSRT` mutual): from the
typed source, ONE app-inversion exposes the recursor spine's function and
the ctor major; the two spine heads move `lsR ↦ w2.ls` / `lsC ↦ w2.lsC` by
`hasTyTConstMove`/`hasTyTConstMoveConv` (both bounds in hand — the
predicate's own, and the source's by inversion); the spines move by
`parRedArgsSRT`/`parRedArgsConvT`; `HasTyT.app` reassembles the reduced
redex, `convTInst0ValueSort` (codomain sort-typed under the binder by R-2
+ Π-inversion) bridges the type to `T`, and `iotaPreserveT`
(`hasTyT_iota_sr` through the scope bridge) hands back the reduct's
typing. The other twelve arms: `refl` is the input; `sortEq`/`consts`/
`delta`/`lit` also stand alone below (the teeth's content); the congruence
arms (`app`/`lam`/`pi`/`letE`) are inversions + `ConvT` congruences +
`hasTyTConvAssump`/`hasTyTConvLet`; `beta`/`zeta`/`bvarZeta` ride the Π
row in scope, `convTInst0ValueSort`/`…SortLet`, `hasTyT_subst0_of_envWfT`
and the prefix lifts — every piece sealed in this module or its imports. -/

/-- the `sortEq` arm, standalone: the sort-typing inversion plus the sorts
    congruence, endpoint read off `DT009T`. -/
theorem parRedSRT_sortEq {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l₁ l₂ : Level} {T : Expr Nat}
    (hl : eqN l₁ l₂) (h : HasTyT E n Γ (.sort l₁) T) :
    Nonempty (HasTyT E n Γ (.sort l₂) T) :=
  (DT009T_endpoints_inScope hW hP hΓ
    (convT_of_tyConv (ConvT.sorts Γ l₁ l₂ hl) (hasTyTInv_sortT h rfl))).2

/-- the `consts` arm, standalone — the R-1′ content itself: with the
    TARGET list bounded, the const retype goes through. -/
theorem parRedSRT_consts {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {ls ls' : List Level}
    (hls : eqNList ls ls') (hwf' : levelsBounded n ls' = true) {S : Expr Nat}
    (h : HasTyT E n Γ (.const r ls) S) :
    Nonempty (HasTyT E n Γ (.const r ls') S) :=
  hasTyTConstMove hW hP hΓ hls hwf' h

/-- the `delta` arm, standalone: the body typing from the `EnvWfT`
    admission, retyped along the const inversion's chain. -/
theorem parRedSRT_delta {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {T : Expr Nat}
    (h : HasTyT E n Γ (.const r ls) T) :
    Nonempty (HasTyT E n Γ (instantiateLevels ls b) T) := by
  obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const h rfl
  have hmeq : some m = some m' := hres.symm.trans hres'
  injection hmeq with hmeq'
  subst hmeq'
  exact ⟨hasTyT_of_tyConv (envWfT_bodyTyped (Γ := Γ) hW hres hbody hlen) hcv⟩

/-- the `lit` arm, standalone. -/
theorem parRedSRT_lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat}
    {T : Expr Nat} (h : HasTyT E n Γ (.lit t) T) :
    Nonempty (HasTyT E n Γ (natExpand t) T) := by
  obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit (E := E) (n := n) h rfl
  exact ⟨hasTyT_of_tyConv hnat hcv⟩

/-! ## R-1′ (D): the teeth -/

/-- TOOTH 2: the refuted masked step is OUTSIDE the predicate — by `decide`. -/
theorem parRedSRT_constsStep_levelsInFalse :
    levelsIn parRedSRT_constsStep = false := by decide

/-- TOOTH 3's engine: `imax(ρᵢ,ρᵢ) = ρᵢ` at every valuation. -/
theorem eqN_imaxParam_rightZero (i : Nat) :
    eqN (.imax (.param i) .zero) (.zero) := by
  intro ρ
  rfl

/-- TOOTH 3 (the ruling's exact instance): an IN-RANGE level-equality
    consts step RETAINS SR — `.const 3 [.imax (.param 0) .zero] ↠
    .const 3 [.zero]` at natEnvU `n = 1`: the eqN holds (the imax-zero
    mask, `eqN_imaxParam_rightZero`), BOTH lists are `levelsBounded 1`
    (`[.zero]` is closed, so the arm's bound premise is `rfl`; the source
    list's bound is its own `HasTyT.const` premise), the SOURCE is the
    refutation's own source (`parRedSRT_constsSrcTyped` — the same typed
    const the masked step left from), and the pin consumes the SEALED
    consts arm to type the target at the source's own type. -/
theorem pin_parRedSRT_constsInRange :
    Nonempty (HasTyT natEnvU 1 [] (.const 3 [.zero])
      (instantiateLevels [.imax (.param 0) .zero] natRecMemberU.mtype)) :=
  parRedSRT_consts (r := 3) (n := 1) (ls := [.imax (.param 0) .zero])
    (ls' := [.zero]) natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    ⟨eqN_imaxParam_rightZero 0, trivial⟩
    rfl
    parRedSRT_constsSrcTyped

/-! TOOTH 4 (the β pin) and TOOTH 5 (the ι drift pin) sit AFTER the R-1″
mutual below — both consume the FULL `parRedSRT` (the β pin's derivation is
`.beta [] (.sort 1) (.sort 1) (.bvar 0) (.bvar 0) (.sort 0) (.sort 0)
(.refl) (.refl) (.refl)`, `levelsIn = true` by `rfl` under the R-1″
predicate too). -/

/-! ## R-1′ FINAL OUTCOME (2026-10-09 second measurement; SETTLED by R-1″):
## the CONSTS-ONLY-scoped claim is FALSE — the iotaSpine COUNTERMODEL,
## machine-checked and KEPT as the record of why consts-only failed

The dispatch's own obstruction guess ("the source spine's typing seems to
force a motive at `Sort (instLevel lsR (param 0))` = `Sort .zero`-ish, which
no natEnvU term inhabits … no Prop members exist") MEASURED WRONG, and with
it the vacuous-safety hope for the arm. `HasTyT.pi` is IMPREDICATIVE
(`RcicDeclarative.lean:3192-3195`: the Π concludes at `.sort (.imax u v)`,
and an imax with a `.zero`-evaluating right argument evaluates to 0), so
CLOSED Props are TERM-BUILT from `.sort`/`.pi`/`.lam`/`.bvar` alone — no
environment member needed:

    True := Π (X : Prop), Π (_ : X), X : Sort (imax 1 (imax 0 0)) ≡ Sort 0
    tt   := λ (X : Prop) (x : X), x : True

(`eqN_iotaCM_true_zero`: the sort level and `.zero` are `=ₙ`-equal, both
evaluate to `some 0` at every valuation — the ConvT.sorts bridge moves
between them). The masked motive position `Π (_ : N), Sort zero` is
therefore INHABITED (`icmMotiveTy`), the typed source EXISTS at the drifted
witness (`parRedSRT_iotaSrcTyped`), and the arm — with it the R-1′-scoped
theorem — is a REFUTATION, not a wall: `parRedSRT_levelsIn_claimFalse`.

THE COUNTERMODEL, at `natEnvU` `n = 1` `Γ = []` (the dispatch's own pin
environment, `EnvWfT` + `InScope` by `natEnvUWfT`/`natEnvUWfT_inScope`):

* witness `wSuccDrift`: `wSuccU`'s succ redex at the UNBOUNDED recursor
  levels `ls := [.imax (.param 5) .zero]`, with `preMajor` replaced by the
  True-motive minors — witness fields are DATA equations (typing is a
  premise of `IotaPreserve`, never of the witness,
  `RcicDeclarative.lean:2184-2186`), and every field of the replacement
  checks by `rfl`/`decide` (`wSuccDrift` below).
* the step (`parRedSRT_iotaStep`): `ParRed.iotaSpine` at `lsR := [.zero]`,
  `lsC := []`, refl argument spines — `hlsR` holds by the imax-zero mask
  (`eqN_imaxParam_rightZero 5`), `hlhs` by `rfl` (`iotaLhsOf_wSuccDrift`),
  and `levelsInR1` of the whole derivation is `true`
  (`parRedSRT_iotaStep_levelsInR1`, refl spines only).
* the SOURCE is TYPED (`parRedSRT_iotaSrcTyped`): head `.const 3 [.zero]`
  (closed, `levelsBounded 1` by `rfl`), motive `λ (_ : N), True` at the
  `d0`-instantiation `Π (_ : N), Sort zero` (the impredicative inhabitant),
  minors through the beta conversions `M n ≡ True`, major `succ zero : N`
  (the sealed `pinIotaMajorTy`).
* the TARGET `iotaRhsOf wSuccDrift` is typable at NO type
  (`parRedSRT_iotaTgtUntyped`): its `rhsArgs` carry the DirectRec recursive
  call `N.rec.{[.imax (.param 5) .zero]} M tz ms zero`
  (`iotaRhsOf_wSuccDrift`, by `rfl`), whose head const's
  `levelsBounded 1 [.imax (.param 5) .zero]` is `false` (`param 5`) —
  app-inversion four times, const-inversion once, `decide`.

R-1′ read this as "no `levelsIn`-shaped predicate on the derivation seals
`parRedSRT`". R-1″ corrected the reading: what the countermodel refutes is
the CONSTS-ONLY enumeration — the drift runs through the WITNESS's own
`ls`, and a derivation predicate CAN read it (`w2` is a constructor
parameter). The R-1″ `levelsIn` does exactly that, the counterexample's
derivation leaves the fragment (`parRedSRT_iotaStep_levelsInFalse`, the
excluded step is FALSE under the new predicate), and an IN-CONTEXT drift
step at the same shape stays legal (`pin_parRedSRT_iotaDrift` below). Both
refutation theorems stand as true theorems — the unconditioned form
(`parRedSRT_claimFalse`) and the consts-only-scoped form
(`parRedSRT_levelsIn_claimFalse`, on the preserved `levelsInR1`). -/

/-- the closed Prop: `Π (X : Prop), Π (_ : X), X`, at the closed level
    `imax (succ zero) (imax zero zero)` (evaluates to 0 at every valuation). -/
def icmTrue : Expr Nat := .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))

def icmTrueLvl : Level := .imax (.succ .zero) (.imax .zero .zero)

theorem eqN_iotaCM_true_zero : eqN icmTrueLvl .zero := by
  intro ρ
  rfl

/-- `True : Sort icmTrueLvl` — two Π rules; the outer one is the impredicative
    step (`Sort 0` domain at `u = 1`, Prop-valued codomain at `v = 0`-eval). -/
def icmTrueSort : HasTyT natEnvU 1 [] icmTrue (.sort icmTrueLvl) :=
  HasTyT.pi [] (.sort .zero) (.succ .zero) (.pi (.bvar 0) (.bvar 1)) (.imax .zero .zero)
    (HasTyT.sort [] .zero)
    (HasTyT.pi [LocalDecl.assumption (.sort .zero)] (.bvar 0) .zero (.bvar 1) .zero
      (HasTyT.bvar [LocalDecl.assumption (.sort .zero)] 0 (.sort .zero) rfl)
      (HasTyT.bvar [LocalDecl.assumption (.bvar 0),
        LocalDecl.assumption (.sort .zero)] 1 (.sort .zero) rfl))

/-- the closed inhabitant: `λ (X : Prop) (x : X), x : True`. -/
def icmTT : Expr Nat := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

def icmTTTrue : HasTyT natEnvU 1 [] icmTT icmTrue :=
  HasTyT.lam [] (.sort .zero) (.succ .zero)
    (.lam (.bvar 0) (.bvar 0)) (.pi (.bvar 0) (.bvar 1))
    (HasTyT.sort [] .zero)
    (HasTyT.lam [LocalDecl.assumption (.sort .zero)] (.bvar 0) .zero (.bvar 0) (.bvar 1)
      (HasTyT.bvar [LocalDecl.assumption (.sort .zero)] 0 (.sort .zero) rfl)
      (HasTyT.bvar [LocalDecl.assumption (.bvar 0),
        LocalDecl.assumption (.sort .zero)] 0 (.bvar 1) rfl))

/-! ### the motive and minors at the masked instantiations -/

/-- the motive `λ (_ : N), True` at its base sort `Π (_ : N), Sort icmTrueLvl`. -/
def icmMotive : Expr Nat := .lam (.const 0 []) icmTrue

def icmMotiveBase : HasTyT natEnvU 1 [] icmMotive (.pi (.const 0 []) (.sort icmTrueLvl)) :=
  HasTyT.lam [] (.const 0 []) (.succ .zero) icmTrue (.sort icmTrueLvl)
    pinIotaFamTy
    (hasTyTWeaken (LocalDecl.assumption (.const 0 []))
      (envClosed_of_envWfT natEnvUWfT) (c := 0) icmTrueSort)

/-- sorts-bridge `Sort icmTrueLvl ≡ Sort zero` in any context. -/
def icmTrueSortConv (Γ : LCtx) :
    ConvT natEnvU 1 Γ (.sort icmTrueLvl) (.sort .zero) (.sort (.succ icmTrueLvl)) :=
  ConvT.sorts Γ icmTrueLvl .zero eqN_iotaCM_true_zero

/-- THE MASKED MOTIVE POSITION IS INHABITED: the motive retyped at the
    `d0`-instantiation for `lsR := [.zero]`, `Π (_ : N), Sort zero` — the
    position the dispatch's obstruction guessed was empty. -/
def icmMotiveTy : HasTyT natEnvU 1 [] icmMotive (.pi (.const 0 []) (.sort .zero)) :=
  HasTyT.conv [] icmMotive (.pi (.const 0 []) (.sort icmTrueLvl))
    (.pi (.const 0 []) (.sort .zero))
    (.imax (.succ .zero) (.succ icmTrueLvl)) icmMotiveBase
    (ConvT.pi [] (.const 0 []) (.const 0 []) (.sort icmTrueLvl) (.sort .zero)
      (.succ .zero) (.succ icmTrueLvl)
      (ConvT.refl [] (.const 0 []) (.sort (.succ .zero)) pinIotaFamTy)
      (icmTrueSortConv [LocalDecl.assumption (.const 0 [])]))

/-- the succ-minor at the True-motive: `λ (n : N) (ih : True), tt`. -/
def icmMinorS : Expr Nat := .lam (.const 0 []) (.lam icmTrue icmTT)

/-- N's const-typing weakened under one and two binders. -/
def icmNSortN : HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])] (.const 0 [])
    (.sort (.succ .zero)) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) pinIotaFamTy

def icmNSortTN : HasTyT natEnvU 1
    [LocalDecl.assumption icmTrue, LocalDecl.assumption (.const 0 [])] (.const 0 [])
    (.sort (.succ .zero)) :=
  hasTyTWeaken (LocalDecl.assumption icmTrue) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) icmNSortN

/-- True's sort-typing weakened under (N), (N, N), (True, N), (N, True, N). -/
def icmTrueSortN : HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])] icmTrue
    (.sort icmTrueLvl) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) icmTrueSort

def icmTrueSortNN : HasTyT natEnvU 1
    [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])] icmTrue
    (.sort icmTrueLvl) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) icmTrueSortN

def icmTrueSortTN : HasTyT natEnvU 1
    [LocalDecl.assumption icmTrue, LocalDecl.assumption (.const 0 [])] icmTrue
    (.sort icmTrueLvl) :=
  hasTyTWeaken (LocalDecl.assumption icmTrue) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) icmTrueSortN

def icmTrueSortNNN : HasTyT natEnvU 1
    [LocalDecl.assumption (.const 0 []), LocalDecl.assumption icmTrue,
      LocalDecl.assumption (.const 0 [])] icmTrue (.sort icmTrueLvl) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) icmTrueSortTN

/-- `tt` weakened under (True, N). -/
def icmTTTrueTN : HasTyT natEnvU 1
    [LocalDecl.assumption icmTrue, LocalDecl.assumption (.const 0 [])] icmTT icmTrue :=
  hasTyTWeaken (LocalDecl.assumption icmTrue) (envClosed_of_envWfT natEnvUWfT)
    (c := 0)
    (hasTyTWeaken (LocalDecl.assumption (.const 0 []))
      (envClosed_of_envWfT natEnvUWfT) (c := 0) icmTTTrue)

/-- the beta conversion `M zero ≡ True` at the empty context. -/
def icmMotiveZeroConv :
    ConvT natEnvU 1 [] (.app icmMotive (.const 1 [])) icmTrue (.sort icmTrueLvl) :=
  ConvT.beta [] (.const 0 []) icmTrue (.const 1 []) (.sort icmTrueLvl) (.succ .zero)
    pinIotaFamTy icmTrueSortN pinIotaZeroTy

/-- the minor-z: `tt : M zero` (through the beta conversion, the
    `pinIotaMinorZTy` pattern at the True motive). -/
def icmMinorZTy : HasTyT natEnvU 1 [] icmTT (.app icmMotive (.const 1 [])) :=
  HasTyT.conv [] icmTT icmTrue (.app icmMotive (.const 1 [])) icmTrueLvl icmTTTrue
    (ConvT.symm _ _ _ _ icmMotiveZeroConv)

/-- the succ-minor's base typing: `λ (n : N) (ih : True), tt : Π n ih, True`. -/
def icmMinorSBase : HasTyT natEnvU 1 [] icmMinorS
    (.pi (.const 0 []) (.pi icmTrue icmTrue)) :=
  HasTyT.lam [] (.const 0 []) (.succ .zero) (.lam icmTrue icmTT) (.pi icmTrue icmTrue)
    pinIotaFamTy
    (HasTyT.lam [LocalDecl.assumption (.const 0 [])] icmTrue icmTrueLvl icmTT icmTrue
      icmTrueSortN icmTTTrueTN)

/-- the succ-minor at the `d2`-instantiation `Π n, Π ih : M n, M (succ n)`
    (the `pinIotaMinorSTy` pattern: Π congruences along the beta
    conversions `M n ≡ True`, `M (succ n) ≡ True`). -/
def icmMinorSTy : HasTyT natEnvU 1 [] icmMinorS
    (.pi (.const 0 [])
      (.pi (.app icmMotive (.bvar 0))
        (.app icmMotive (.app (.const 2 []) (.bvar 1))))) :=
  HasTyT.conv [] icmMinorS (.pi (.const 0 []) (.pi icmTrue icmTrue))
    (.pi (.const 0 [])
      (.pi (.app icmMotive (.bvar 0))
        (.app icmMotive (.app (.const 2 []) (.bvar 1)))))
    (.imax (.succ .zero) (.imax icmTrueLvl icmTrueLvl)) icmMinorSBase
    (ConvT.pi [] (.const 0 []) (.const 0 [])
      (.pi icmTrue icmTrue)
      (.pi (.app icmMotive (.bvar 0))
        (.app icmMotive (.app (.const 2 []) (.bvar 1))))
      (.succ .zero) (.imax icmTrueLvl icmTrueLvl)
      (ConvT.refl [] (.const 0 []) (.sort (.succ .zero)) pinIotaFamTy)
      (ConvT.pi [LocalDecl.assumption (.const 0 [])] icmTrue (.app icmMotive (.bvar 0))
        icmTrue (.app icmMotive (.app (.const 2 []) (.bvar 1)))
        icmTrueLvl icmTrueLvl
        (ConvT.symm _ _ _ _
          (ConvT.beta [LocalDecl.assumption (.const 0 [])] (.const 0 []) icmTrue
            (.bvar 0) (.sort icmTrueLvl) (.succ .zero)
            icmNSortN icmTrueSortNN
            (HasTyT.bvar [LocalDecl.assumption (.const 0 [])] 0 (.const 0 []) rfl)))
        (ConvT.symm _ _ _ _
          (ConvT.beta
            [LocalDecl.assumption icmTrue, LocalDecl.assumption (.const 0 [])]
            (.const 0 []) icmTrue (.app (.const 2 []) (.bvar 1))
            (.sort icmTrueLvl) (.succ .zero)
            icmNSortTN icmTrueSortNNN
            (HasTyT.app [LocalDecl.assumption icmTrue, LocalDecl.assumption (.const 0 [])]
              (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
              (HasTyT.const _ 2 [] natSuccMember rfl rfl rfl)
              (HasTyT.bvar _ 1 (.const 0 []) rfl))))))

/-! ### the drifted witness and its rhs -/

/-- `wSuccU`'s succ redex at the UNBOUNDED recursor levels
    `[.imax (.param 5) .zero]`, `preMajor` replaced by the True-motive
    minors. Witness fields are data equations; every field checks by
    `rfl`/`decide` (the level-sensitive ones: `hlsLen` length 1 = arity 1;
    `hctorAfter` at `preMajor.take 0 = []` and the param-free ctor type). -/
def wSuccDrift : IotaWitness natEnvU where
  recRef := 3
  ctorRef := 2
  ls := [.imax (.param 5) .zero]
  lsC := []
  recMember := natRecMemberU
  ctorMember := natSuccMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [icmMotive, icmTT, icmMinorS]
  fields := [natField]
  ctorParams := []
  kinds := [.directRec]
  minor := icmMinorS
  hlen := rfl
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 0 []]
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := natRecDomsU
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 0 []) (.const 0 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- the poisoned recursive call `rhsArgs` emits for the DirectRec field:
    head at the witness's OWN (unbounded) `ls`. -/
def icmRecall : Expr Nat :=
  foldApps (.const 3 [.imax (.param 5) .zero]) [icmMotive, icmTT, icmMinorS, natField]

theorem iotaRhsOf_wSuccDrift :
    iotaRhsOf wSuccDrift = .app (.app icmMinorS natField) icmRecall := rfl

theorem iotaLhsOf_wSuccDrift :
    iotaLhsOf wSuccDrift =
      recCall (.const 3 [.imax (.param 5) .zero]) [icmMotive, icmTT, icmMinorS]
        (foldApps (.const 2 []) ([] ++ [natField])) := rfl

/-! ### the countermodel's three legs -/

def parRedSRT_iotaSrc : Expr Nat :=
  recCall (.const 3 [.zero]) [icmMotive, icmTT, icmMinorS]
    (foldApps (.const 2 []) [natField])

/-- LEG 1 — the source spine is TYPED at `n = 1`: the head at the IN-RANGE
    `[.zero]`, the impredicative motive at the masked `d0` position, the
    minors through the beta conversions, the major `succ zero : N` (the
    sealed `pinIotaMajorTy`). -/
def parRedSRT_iotaSrcTyped :
    HasTyT natEnvU 1 [] parRedSRT_iotaSrc
      (.app icmMotive (foldApps (.const 2 []) [natField])) := by
  have h0 : HasTyT natEnvU 1 [] (.const 3 [.zero]) (instantiateLevels [.zero] natRecTypeU) :=
    HasTyT.const [] 3 [.zero] natRecMemberU rfl rfl rfl
  have h1 : HasTyT natEnvU 1 [] (.app (.const 3 [.zero]) icmMotive) (.pi (.app icmMotive (.const 1 [])) (.pi (.pi (.const 0 []) (.pi (.app icmMotive (.bvar 0)) (.app icmMotive (.app (.const 2 []) (.bvar 1))))) (.pi (.const 0 []) (.app icmMotive (.bvar 0))))) :=
    HasTyT.app [] _ _ _ _ h0 icmMotiveTy
  have h2 : HasTyT natEnvU 1 [] (.app (.app (.const 3 [.zero]) icmMotive) icmTT) (.pi (.pi (.const 0 []) (.pi (.app icmMotive (.bvar 0)) (.app icmMotive (.app (.const 2 []) (.bvar 1))))) (.pi (.const 0 []) (.app icmMotive (.bvar 0)))) :=
    HasTyT.app [] _ _ _ _ h1 icmMinorZTy
  have h3 : HasTyT natEnvU 1 [] (.app (.app (.app (.const 3 [.zero]) icmMotive) icmTT) icmMinorS) (.pi (.const 0 []) (.app icmMotive (.bvar 0))) :=
    HasTyT.app [] _ _ _ _ h2 icmMinorSTy
  have h4 : HasTyT natEnvU 1 [] (.app (.app (.app (.app (.const 3 [.zero]) icmMotive) icmTT) icmMinorS) (foldApps (.const 2 []) [natField])) (.app icmMotive (foldApps (.const 2 []) [natField])) :=
    HasTyT.app [] _ _ _ _ h3 pinIotaMajorTy
  exact h4

/-- LEG 2 — the step is a legal `ParRed.iotaSpine` with `levelsIn = true`:
    `hlsR` by the imax-zero mask, refl spines, `hlhs` by `rfl`. -/
def parRedSRT_iotaStep :
    ParRed natEnvU 1 [] parRedSRT_iotaSrc (iotaRhsOf wSuccDrift) :=
  ParRed.iotaSpine [] wSuccDrift [.zero] []
    ⟨eqN_imaxParam_rightZero 5, trivial⟩
    (eqNList_refl [])
    [icmMotive, icmTT, icmMinorS] [icmMotive, icmTT, icmMinorS]
    ([] ++ [natField]) ([] ++ [natField])
    (parRedArgs_refl [icmMotive, icmTT, icmMinorS])
    (parRedArgs_refl ([] ++ [natField]))
    rfl rfl rfl

theorem parRedSRT_iotaStep_levelsInR1 :
    levelsInR1 parRedSRT_iotaStep = true := rfl

/-- LEG 3 — the reduct is typable at NO type: the poisoned recursive call's
    head `.const 3 [.imax (.param 5) .zero]` fails `levelsBounded 1` (`param 5`),
    and app-inversion (4×, conv-forking) + const-inversion read the bound off
    any would-be typing. -/
theorem parRedSRT_iotaTgtUntyped (T : Expr Nat) :
    ¬ Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccDrift) T) := by
  intro h
  obtain ⟨ht⟩ := h
  rw [iotaRhsOf_wSuccDrift] at ht
  obtain ⟨_, _, _, harg, _⟩ := hasTyTInv_app ht rfl
  obtain ⟨_, _, hf3, _, _⟩ := hasTyTInv_app harg rfl
  obtain ⟨_, _, hf2, _, _⟩ := hasTyTInv_app hf3 rfl
  obtain ⟨_, _, hf1, _, _⟩ := hasTyTInv_app hf2 rfl
  obtain ⟨_, _, hhead, _, _⟩ := hasTyTInv_app hf1 rfl
  obtain ⟨m, _, _, hwf, _⟩ := hasTyTInv_const (r := 3) hhead rfl
  exact absurd hwf (by decide)

/-- R-1″ TOOTH A: the excluded iotaStep is FALSE under the NEW predicate —
    the countermodel's `w2.ls = [.imax (.param 5) .zero]` is READ and
    rejected (`param 5` out of the `n = 1` level context), by `decide`. This
    REVERSES the old counterexample-leg `parRedSRT_iotaStep_levelsIn`
    (`= true` by `rfl` under the R-1′ predicate — preserved above as
    `_levelsInR1` on `levelsInR1`): under the R-1″ arm the same derivation
    leaves the fragment, which is exactly why the countermodel no longer
    refutes the R-1″-scoped claim. -/
theorem parRedSRT_iotaStep_levelsInFalse :
    levelsIn parRedSRT_iotaStep = false := by decide

/-! ### the R-1′-form claim (CONSTS-ONLY), refuted and KEPT -/

/-- the R-1′-form statement: `parRedSRT` conditioned on the CONSTS-ONLY
    derivation predicate (`levelsInR1` — the enumeration R-1′ settled on).
    Kept so the refutation below stays a living theorem documenting WHY
    consts-only failed; the R-1″-scoped claim on the strengthened
    `levelsIn` is the SEALED theorem `parRedSRT` further below. -/
def ParRedSRTLevelsInClaim : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (_hP : hW.InScope) {n : Nat} {Γ : LCtx}
    (_hΓ : CtxWfT E n Γ),
    {e A e' : Expr Nat}→ HasTyT E n Γ e A → (d : ParRed E n Γ e e') →
    levelsInR1 d = true →
    Nonempty (HasTyT E n Γ e' A)

/-- THE SECOND REFUTATION, KEPT AS A TRUE THEOREM: the CONSTS-ONLY scope
    does not save the theorem. The countermodel's derivation is in that
    fragment (refl spines; the only arm `levelsInR1` constrains —
    `.consts` — never appears in it), the source is typed, and the reduct
    is typable at no type — the drift runs through the witness's own `ls`,
    which the consts-only enumeration never reads. Beside
    `parRedSRT_claimFalse` (the unconditioned form) this fixes the content
    rule's enumeration: the only unread level-equality channel was the
    iotaSpine heads, and R-1″'s `levelsIn` reads it. -/
theorem parRedSRT_levelsIn_claimFalse : ¬ ParRedSRTLevelsInClaim := by
  intro h
  have hout := h natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    parRedSRT_iotaSrcTyped parRedSRT_iotaStep parRedSRT_iotaStep_levelsInR1
  exact hout.elim fun hT => parRedSRT_iotaTgtUntyped _ ⟨hT⟩

/-! ## R-1″ (B): the 13-arm mutual — `parRedConvT` carries the arms,
## `parRedSRT` reads the reduct's typing off the endpoints theorem

ARCHITECTURE (statement unchanged: `levelsIn d = true` is the ONLY premise
beyond the source typing): the conv member builds, from the source typing
`h : HasTyT e A`, the step `d`, and `hl : levelsIn d = true`, a
`ConvT e e' A` at the SOURCE'S OWN TYPE; the typing member `parRedSRT` is
the conv member plus `DT009T_endpoints_inScope` (every typed conversion
determines BOTH endpoints' typings). The spine partners mirror the legacy
mutual's shapes: `parRedArgsSRT` is the typing mover (`parRedArgsSR`'s
counterpart — a head-mover argument, at the two const heads of an
iotaSpine it is `hasTyTConstMove` fed the predicate's own bounds),
`parRedArgsConvT` its conv twin (`parRedArgs_foldApps_to_conv`'s). The
body matches on the REDUCTION discriminant ahead of the typing one (the
elaborator order the legacy records). The iotaSpine arm is the R-1″
closure: see the (B) record above for its route. -/

/-- THE CHAIN ADAPTER IN SCOPE (the R-1″ mutual's Π-row consumption):
    with the left end typed at a sort, a `TyConvT` chain to any right end is
    one `ConvT` at that sort — `Ann.convT_of_tyConvT_sort` behind the
    semantic-prefix bridge, so no environment substitution happens inside
    the mutual's arms (the beta arm consumes it). -/
theorem convT_of_tyConvT_sort_scope {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b : Expr Nat} {u : Level} (hA : HasTyT E n Γ a (.sort u))
    (h : TyConvT E n Γ a b) :
    Nonempty (ConvT E n Γ a b (.sort u)) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  exact Ann.convT_of_tyConvT_sort C hn hΓ hA h

set_option maxHeartbeats 4000000 in
mutual

/-- CONV MEMBER: one `ParRed` step is a typed conversion at the source's
    own type, under the R-1″ content rule. -/
noncomputable def parRedConvT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T e' : Expr Nat} (h : HasTyT E n Γ e T) (d : ParRed E n Γ e e') :
    levelsIn d = true → Nonempty (ConvT E n Γ e e' T) := by
  intro hl
  exact match e, e', d, h with
  | _, _, .refl _ _, h => ⟨ConvT.refl _ _ _ h⟩
  | _, _, .sortEq _ l₁ l₂ hlq, h =>
      ⟨convT_of_tyConv (ConvT.sorts _ l₁ l₂ hlq) (hasTyTInv_sortT h rfl)⟩
  | _, _, .consts _ _ _ _ hls, h => by
      simp only [levelsIn] at hl
      exact hasTyTConstMoveConv hW hP hΓ hls hl h
  | _, _, .bvarZeta Γ i A0 v v' hlk hv, h => by
      obtain ⟨A', hlkT, hcv⟩ := hasTyTInv_bvar (i := i) h rfl
      have hlu : lookupType Γ i = some (lift 0 (i + 1) A0) :=
        lookupType_getQ_letBinding hlk
      have heq : some A' = some (lift 0 (i + 1) A0) := hlkT.symm.trans hlu
      injection heq with hA'
      subst hA'
      simp only [levelsIn] at hl
      have hvA : HasTyT E n (Γ.drop (i + 1)) v A0 :=
        ctxWfTLookupValueAtDrop hΓ i hlk
      obtain ⟨cv⟩ := parRedConvT hW hP (ctxWfT_drop hΓ (i + 1)) hvA hv hl
      have hlen : i + 1 ≤ Γ.length := get?_lt_length Γ hlk
      have htake : (Γ.take (i + 1)).length = i + 1 := by
        simp only [List.length_take, Nat.min_eq_left hlen]
      have hliftv : HasTyT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) A0) := by
        have hr := hasTyTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1)) hvA
        rw [htake, List.take_append_drop] at hr
        exact hr
      have hliftcv : ConvT E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) v')
          (lift 0 (i + 1) A0) := by
        have hr := convTLiftPrefix (envClosed_of_envWfT hW) (Γ.take (i + 1)) cv
        rw [htake, List.take_append_drop] at hr
        exact hr
      exact ⟨convT_of_tyConv
        (ConvT.trans Γ _ _ _ _
          (ConvT.zetaLocal Γ i (lift 0 (i + 1) A0) (lift 0 (i + 1) v)
            (lookupValue_getQ_letBinding hlk) hlu hliftv)
          hliftcv) hcv⟩
  | _, _, .delta Γ r ls m b hres hbody htr, h => by
      obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const (r := r) (ls := ls) h rfl
      have hmeq : some m = some m' := hres.symm.trans hres'
      injection hmeq with hmeq'
      subst hmeq'
      exact ⟨convT_of_tyConv
        (ConvT.delta Γ r ls m b hres hbody htr hlen hwf
          (envWfT_bodyTyped hW hres hbody hlen)) hcv⟩
  | _, _, .app Γ f f' a a' hf ha, h => by
      obtain ⟨A0, B0, hfun, harg, hcv⟩ := hasTyTInv_app h rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨hlf, hla⟩ := hl
      obtain ⟨cf⟩ := parRedConvT hW hP hΓ hfun hf hlf
      obtain ⟨ca⟩ := parRedConvT hW hP hΓ harg ha hla
      exact ⟨convT_of_tyConv (ConvT.app Γ f f' a a' A0 B0 cf ca) hcv⟩
  | _, _, .beta Γ A A' body body' arg arg' hA hb ha, h => by
      obtain ⟨A_inv, B_inv, hflam, harg, hcv⟩ := hasTyTInv_app h rfl
      obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hflam rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨⟨hlA, hlb⟩, hla⟩ := hl
      -- the Π row, DERIVED in scope (no premise; `oneStepSRT`'s idiom):
      have hrows := Ann.typedRowsWf_of_envWfT_semPrefix hW hP n
      obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
      obtain ⟨cdom⟩ := convT_of_tyConvT_sort_scope hW hP hΓ hA0ty hBdom
      -- the three IH convs:
      obtain ⟨cA⟩ := parRedConvT hW hP hΓ hA0ty hA hlA
      obtain ⟨cb⟩ :=
        parRedConvT hW hP (CtxWfT.assumption Γ A u hΓ hA0ty) hbody hb hlb
      obtain ⟨ca⟩ := parRedConvT hW hP hΓ harg ha hla
      have caA : ConvT _ n Γ arg arg' A := convT_of_tyConv ca (TyConvT.symmT hBdom)
      have hargA : HasTyT _ n Γ arg A :=
        HasTyT.conv _ _ _ _ u harg (ConvT.symm _ _ _ _ cdom)
      -- M1: congruence redex ↠ (.lam A' body') arg':
      have capp : ConvT _ n Γ (.app (.lam A body) arg) (.app (.lam A' body') arg')
          (instantiate0 arg B_lam) :=
        ConvT.app Γ (.lam A body) (.lam A' body') arg arg' A B_lam
          (ConvT.lam Γ A A' body body' B_lam u cA cb) caA
      -- M2: the beta step at the NEW λ and argument:
      obtain ⟨hA'ty⟩ := (DT009T_endpoints_inScope hW hP hΓ cA).2
      obtain ⟨hb'ty⟩ :=
        (DT009T_endpoints_inScope hW hP (CtxWfT.assumption Γ A u hΓ hA0ty) cb).2
      have hb''ty : HasTyT _ n (LocalDecl.assumption A' :: Γ) body' B_lam :=
        hasTyTConvAssump (envClosed_of_envWfT hW) (ConvT.symm _ _ _ _ cA) hb'ty
      obtain ⟨hargA'⟩ := (DT009T_endpoints_inScope hW hP hΓ caA).2
      have hargA'' : HasTyT _ n Γ arg' A' :=
        HasTyT.conv _ _ _ _ u hargA' cA
      have cbeta : ConvT _ n Γ (.app (.lam A' body') arg') (instantiate0 arg' body')
          (instantiate0 arg' B_lam) :=
        ConvT.beta Γ A' body' arg' B_lam u hA'ty hb''ty hargA''
      -- the chains to T (codomain-substituted, value-congruent at the
      -- app-inversion's own codomain, R-2 + Π-inversion for its sort):
      obtain ⟨c1⟩ := convT_subst0_tyConvT hW hBcod hargA'
      obtain ⟨w, ⟨hps⟩⟩ := hasTyT_type_sort_exists_scope hW hP hΓ hflam
      obtain ⟨u2, v2, hA2ty, hB2ty, _⟩ := hasTyTInv_pi hps rfl
      obtain ⟨c2⟩ :=
        convTInst0ValueSort hW hP hΓ hA2ty hB2ty (ConvT.symm _ _ _ _ ca)
      obtain ⟨d1⟩ := convT_subst0_tyConvT hW hBcod hargA
      have chainApp : TyConvT _ n Γ (instantiate0 arg B_lam) T :=
        TyConvT.trans _ _ _ _ d1 hcv
      have chainBeta : TyConvT _ n Γ (instantiate0 arg' B_lam) T :=
        TyConvT.trans _ _ _ _ c1 (TyConvT.trans _ _ _ _ (TyConvT.of _ _ _ _ c2) hcv)
      exact ⟨ConvT.trans _ _ _ _ _ (convT_of_tyConv capp chainApp)
        (convT_of_tyConv cbeta chainBeta)⟩
  | _, _, .lam Γ A A' b b' hA hb, h => by
      obtain ⟨u, B, hA0ty, hbty, hcv⟩ := hasTyTInv_lam h rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨hlA, hlb⟩ := hl
      obtain ⟨cA⟩ := parRedConvT hW hP hΓ hA0ty hA hlA
      obtain ⟨cb⟩ :=
        parRedConvT hW hP (CtxWfT.assumption Γ A u hΓ hA0ty) hbty hb hlb
      exact ⟨convT_of_tyConv (ConvT.lam Γ A A' b b' B u cA cb) hcv⟩
  | _, _, .pi Γ A A' b b' hA hb, h => by
      obtain ⟨u, v, hA0ty, hB0ty, hcv⟩ := hasTyTInv_pi h rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨hlA, hlb⟩ := hl
      obtain ⟨cA⟩ := parRedConvT hW hP hΓ hA0ty hA hlA
      obtain ⟨cb⟩ :=
        parRedConvT hW hP (CtxWfT.assumption Γ A u hΓ hA0ty) hB0ty hb hlb
      exact ⟨convT_of_tyConv (ConvT.pi Γ A A' b b' u v cA cb) hcv⟩
  | _, _, .letE Γ A A' v v' b b' hA hv hb, h => by
      obtain ⟨u, B, hAty, hvty, hbty, hcv⟩ := hasTyTInv_letE h rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨⟨hlA, hlv⟩, hlb⟩ := hl
      obtain ⟨cA⟩ := parRedConvT hW hP hΓ hAty hA hlA
      obtain ⟨cv⟩ := parRedConvT hW hP hΓ hvty hv hlv
      obtain ⟨cb⟩ :=
        parRedConvT hW hP (CtxWfT.letBinding Γ A u v hΓ hAty hvty) hbty hb hlb
      exact ⟨convT_of_tyConv (ConvT.letE Γ A A' v v' b b' B u cA cv cb) hcv⟩
  | _, _, .zeta Γ A A' v v' b b' hA hv hb, h => by
      obtain ⟨u, B, hAty, hvty, hbty, hcv⟩ := hasTyTInv_letE h rfl
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨⟨hlA, hlv⟩, hlb⟩ := hl
      obtain ⟨cA⟩ := parRedConvT hW hP hΓ hAty hA hlA
      obtain ⟨cv⟩ := parRedConvT hW hP hΓ hvty hv hlv
      obtain ⟨cb⟩ :=
        parRedConvT hW hP (CtxWfT.letBinding Γ A u v hΓ hAty hvty) hbty hb hlb
      -- the A'/v'-side pieces:
      obtain ⟨hA'ty⟩ := (DT009T_endpoints_inScope hW hP hΓ cA).2
      obtain ⟨hv'ty⟩ := (DT009T_endpoints_inScope hW hP hΓ cv).2
      have hv'A' : HasTyT E n Γ v' A' := HasTyT.conv _ _ _ _ u hv'ty cA
      obtain ⟨hb'ty0⟩ :=
        (DT009T_endpoints_inScope hW hP
          (CtxWfT.letBinding Γ A u v hΓ hAty hvty) cb).2
      have hb'ty : HasTyT E n (LocalDecl.letBinding A' v' :: Γ) b' B :=
        hasTyTConvLet (envClosed_of_envWfT hW) (ConvT.symm _ _ _ _ cA)
          (ConvT.symm _ _ _ _ cv) hv'A' hb'ty0
      -- the let congruence at the OLD let, the zeta at the NEW:
      have clet : ConvT E n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B) :=
        ConvT.letE Γ A A' v v' b b' B u cA cv cb
      have czeta : ConvT E n Γ (.letE A' v' b') (instantiate0 v' b')
          (instantiate0 v' B) :=
        ConvT.zeta Γ A' v' b' B u hA'ty hv'A' hb'ty
      -- the value congruence at the let's own codomain (R-2 on the body
      -- typing, moved across the let-morphism so BOTH sides sit at one w):
      obtain ⟨w, ⟨hBv⟩⟩ := hasTyT_type_sort_exists_scope hW hP
        (CtxWfT.letBinding Γ A u v hΓ hAty hvty) hbty
      have hBv' : HasTyT E n (LocalDecl.letBinding A v' :: Γ) B (.sort w) :=
        hasTyTConvLet (envClosed_of_envWfT hW)
          (ConvT.refl Γ A (.sort u) hAty) (ConvT.symm _ _ _ _ cv) hv'ty hBv
      obtain ⟨vc⟩ :=
        convTInst0ValueSortLet hW hP hΓ hAty hvty hv'ty hBv hBv' cv
      have chainZ : TyConvT _ n Γ (instantiate0 v' B) T :=
        TyConvT.trans _ _ _ _ (TyConvT.symmT (TyConvT.of _ _ _ _ vc)) hcv
      exact ⟨ConvT.trans _ _ _ _ _ (convT_of_tyConv clet hcv)
        (convT_of_tyConv czeta chainZ)⟩
  | _, _, .iotaSpine Γ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha _hpreLen _hfieldsLen hlhs, h => by
      simp only [levelsIn, Bool.and_eq_true] at hl
      obtain ⟨⟨hwfR, hwfC⟩, ⟨hlf, hla⟩⟩ := hl
      simp only [recCall] at h
      rw [foldApps_snoc] at h
      obtain ⟨A0, B0, hfun, harg, hcv⟩ := hasTyTInv_app h rfl
      -- the two head movers at the predicate's own bounds:
      -- the two head movers at the predicate's own bounds (the sealed
      -- const-move, CONV-shaped; `parRedArgsSRT` reads the typing off):
      have hmR : ∀ (S : Expr Nat), HasTyT E n Γ (.const w2.recRef lsR) S →
          Nonempty (ConvT E n Γ (.const w2.recRef lsR) (.const w2.recRef w2.ls) S) :=
        fun S hS => hasTyTConstMoveConv hW hP hΓ (eqNList_symm hlsR) hwfR hS
      have hmC : ∀ (S : Expr Nat), HasTyT E n Γ (.const w2.ctorRef lsC) S →
          Nonempty (ConvT E n Γ (.const w2.ctorRef lsC) (.const w2.ctorRef w2.lsC) S) :=
        fun S hS => hasTyTConstMoveConv hW hP hΓ (eqNList_symm hlsC) hwfC hS
      -- TYPING route (the legacy `parRedArgsSR` mirror — `parRedArgsSRT`'s
      -- own body: the conv twin plus the endpoints theorem):
      obtain ⟨c1⟩ := parRedArgsConvT hW hP hΓ hf hmR hfun hlf
      obtain ⟨hfun'⟩ := (DT009T_endpoints_inScope hW hP hΓ c1).2
      obtain ⟨c2⟩ := parRedArgsConvT hW hP hΓ ha hmC harg hla
      obtain ⟨harg'⟩ := (DT009T_endpoints_inScope hW hP hΓ c2).2
      have happ : HasTyT E n Γ
          (.app (foldApps (.const w2.recRef w2.ls) pre')
            (foldApps (.const w2.ctorRef w2.lsC) fields'))
          (instantiate0 (foldApps (.const w2.ctorRef w2.lsC) fields') B0) :=
        HasTyT.app _ _ _ _ _ hfun' harg'
      -- the major's value congruence at the codomain, sort-typed under the
      -- binder by R-2 + Π-inversion on the function's own π-typing:
      obtain ⟨w, ⟨hps⟩⟩ := hasTyT_type_sort_exists_scope hW hP hΓ hfun
      obtain ⟨u2, v2, hA0ty, hB0ty, _⟩ := hasTyTInv_pi hps rfl
      obtain ⟨vc⟩ := convTInst0ValueSort hW hP hΓ hA0ty hB0ty c2
      have hchain : TyConvT E n Γ
          (instantiate0 (foldApps (.const w2.ctorRef w2.lsC) fields') B0) T :=
        TyConvT.trans _ _ _ _ (TyConvT.symmT (TyConvT.of _ _ _ _ vc)) hcv
      have hlhsTy : HasTyT E n Γ (iotaLhsOf w2) T := by
        rw [hlhs]
        simp only [recCall, foldApps_snoc]
        exact hasTyT_of_tyConv happ hchain
      obtain ⟨hrhs⟩ := iotaPreserveT hW hP hΓ (DerivedIota.of w2) hlhsTy
      -- CONV route (the output at the source's own type):
      have capp : ConvT E n Γ
          (.app (foldApps (.const w2.recRef lsR) pre)
            (foldApps (.const w2.ctorRef lsC) fields))
          (.app (foldApps (.const w2.recRef w2.ls) pre')
            (foldApps (.const w2.ctorRef w2.lsC) fields'))
          (instantiate0 (foldApps (.const w2.ctorRef lsC) fields) B0) :=
        ConvT.app _ _ _ _ _ _ _ c1 c2
      have cl : ConvT E n Γ (.app (foldApps (.const w2.recRef lsR) pre)
          (foldApps (.const w2.ctorRef lsC) fields)) (iotaLhsOf w2) T := by
        rw [hlhs]
        simp only [recCall, foldApps_snoc]
        exact convT_of_tyConv capp hcv
      simp only [recCall, foldApps_snoc]
      exact ⟨ConvT.trans _ _ _ _ _ cl
        (ConvT.iota Γ (iotaLhsOf w2) (iotaRhsOf w2) T (DerivedIota.of w2)
          hlhsTy hrhs)⟩
  | _, _, .lit Γ t, h => by
      obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit (t := t) h rfl
      exact ⟨convT_of_tyConv
        (ConvT.lit Γ t (natExpand t) T' (LiteralExpansion.of t) hnat) hcv⟩
termination_by sizeOf d
decreasing_by
  all_goals
    first
    | (simp <;> omega)
    | (trace_state; omega)
    | assumption
    | (simp_all <;> omega)

/-- the spine CONV twin: a `ParRedArgs` spine plus a const head move is a
    typed conversion of the whole application spine (`ConvT.app` per layer,
    each layer's element conv by the conv member). -/
noncomputable def parRedArgsConvT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {xs ys : List (Expr Nat)} (t : ParRedArgs E n Γ xs ys)
    {f f' : Expr Nat}
    (hmove : (S : Expr Nat) → HasTyT E n Γ f S → Nonempty (ConvT E n Γ f f' S))
    {T : Expr Nat} (h : HasTyT E n Γ (foldApps f xs) T) :
    levelsInArgs t = true →
    Nonempty (ConvT E n Γ (foldApps f xs) (foldApps f' ys) T) := by
  intro hl
  exact match t with
  | .nil _ => hmove _ h
  | .cons (x := x) (y := y) hx ht => by
      simp only [levelsInArgs, Bool.and_eq_true] at hl
      obtain ⟨hlx, hlt⟩ := hl
      refine parRedArgsConvT hW hP hΓ ht
        (f := .app f x) (f' := .app f' y) ?_ h hlt
      intro S hS
      obtain ⟨A0, B0, hf0, hx0, hcv⟩ := hasTyTInv_app hS rfl
      obtain ⟨c1⟩ := hmove _ hf0
      obtain ⟨c2⟩ := parRedConvT hW hP hΓ hx0 hx hlx
      exact ⟨convT_of_tyConv (ConvT.app Γ f f' x y A0 B0 c1 c2) hcv⟩
termination_by sizeOf t
decreasing_by
  all_goals
    first
    | (simp <;> omega)
    | (trace_state; omega)
    | assumption
    | (simp_all <;> omega)

end

/-- the spine TYPING mover (the legacy `parRedArgsSR`'s counterpart): from
    the head-mover (at the two const heads of an iotaSpine, the sealed
    `hasTyTConstMoveConv` at the predicate's own bounds) the reduced spine
    is TYPED at the source spine's own type — the conv twin plus the
    endpoints theorem, the same reading `parRedSRT` itself performs. -/
def parRedArgsSRT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {xs ys : List (Expr Nat)} (t : ParRedArgs E n Γ xs ys)
    {f f' : Expr Nat}
    (hmove : (S : Expr Nat) → HasTyT E n Γ f S → Nonempty (ConvT E n Γ f f' S))
    {T : Expr Nat} (h : HasTyT E n Γ (foldApps f xs) T) :
    levelsInArgs t = true → Nonempty (HasTyT E n Γ (foldApps f' ys) T) :=
  fun hl => (parRedArgsConvT hW hP hΓ t hmove h hl).elim fun c =>
    (DT009T_endpoints_inScope hW hP hΓ c).2

/-- THE 13-ARM THEOREM (R-1″, statement unchanged): one `ParRed` step in
    the content-rule fragment preserves the subject's type — the conv
    member plus the endpoints theorem. NO premise beyond `levelsIn d =
    true` (beyond the source typing SR's consumers already hold). -/
def parRedSRT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A e' : Expr Nat}
    (h : HasTyT E n Γ e A) (d : ParRed E n Γ e e') :
    levelsIn d = true → Nonempty (HasTyT E n Γ e' A) :=
  fun hl => (parRedConvT hW hP hΓ h d hl).elim fun c =>
    (DT009T_endpoints_inScope hW hP hΓ c).2

/-! ### the R-1″ pins — both consume the FULL `parRedSRT` -/

/-- TOOTH 4: the β-redex pin at natEnvU, REWIRED through the FULL sealed
    theorem: the source redex `(λ (x : Sort 1), x) Sort 0` is typed by
    `HasTyT.app`/`HasTyT.lam` constructors, the derivation is `.beta` with
    refl-premises (`levelsIn = true` by `rfl` under the R-1″ predicate
    too), and `parRedSRT` returns the reduct's typing at the redex's own
    type. -/
def parRedSRT_betaSrc :
    HasTyT natEnvU 1 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) :=
  HasTyT.app [] (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (HasTyT.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
      (.sort (.succ .zero))
      (HasTyT.sort [] (.succ .zero))
      (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0
        (.sort (.succ .zero)) rfl))
    (HasTyT.sort [] .zero)

def parRedSRT_betaStep :
    ParRed natEnvU 1 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (instantiate0 (.sort .zero) (.bvar 0)) :=
  .beta [] (.sort (.succ .zero)) (.sort (.succ .zero)) (.bvar 0) (.bvar 0)
    (.sort .zero) (.sort .zero) (.refl _ _) (.refl _ _) (.refl _ _)

theorem pin_parRedSRT_beta :
    Nonempty (HasTyT natEnvU 1 [] (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  parRedSRT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    parRedSRT_betaSrc parRedSRT_betaStep rfl

/-- TOOTH 5 / THE ι PIN: an IN-CONTEXT head-level drift step REMAINS legal
    under R-1″ — the countermodel's exact shape with the drift parameter
    moved IN range: `w2.ls := [.imax (.param 0) .zero]` (`param 0` is in
    the `n = 1` level context, so `levelsBounded 1` is `true` — READ and
    ADMITTED by the strengthened arm), `lsR := [.zero]` (the eqN mask). The
    source is the countermodel's own source (`parRedSRT_iotaSrcTyped` — a
    source at `[.zero]`), and the FULL `parRedSRT` consumes the step: the
    drift lands in the reduct's recursive call at the IN-RANGE head. -/
def wSuccDrift0 : IotaWitness natEnvU := { wSuccDrift with ls := [.imax (.param 0) .zero] }

theorem iotaRhsOf_wSuccDrift0 :
    iotaRhsOf wSuccDrift0 = .app (.app icmMinorS natField)
      (foldApps (.const 3 [.imax (.param 0) .zero])
        [icmMotive, icmTT, icmMinorS, natField]) := rfl

def parRedSRT_iotaDriftStep :
    ParRed natEnvU 1 [] parRedSRT_iotaSrc (iotaRhsOf wSuccDrift0) :=
  ParRed.iotaSpine [] wSuccDrift0 [.zero] []
    ⟨eqN_imaxParam_rightZero 0, trivial⟩
    (eqNList_refl [])
    [icmMotive, icmTT, icmMinorS] [icmMotive, icmTT, icmMinorS]
    ([] ++ [natField]) ([] ++ [natField])
    (parRedArgs_refl [icmMotive, icmTT, icmMinorS])
    (parRedArgs_refl ([] ++ [natField]))
    rfl rfl rfl

theorem parRedSRT_iotaDriftStep_levelsIn :
    levelsIn parRedSRT_iotaDriftStep = true := rfl

theorem pin_parRedSRT_iotaDrift :
    Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccDrift0)
      (.app icmMotive (foldApps (.const 2 []) [natField]))) :=
  parRedSRT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    parRedSRT_iotaSrcTyped parRedSRT_iotaDriftStep
    parRedSRT_iotaDriftStep_levelsIn


/-! ## R-1″ (D5): the dependency audit, reflective

Mirrors `RcicFoundationSeal`'s DT-024 pattern (`:3007`, "no judgment
constructor mentions a machine artifact") at module scale: a transitive BFS
over the constants a definition mentions (type + value used-constants),
refusing any member of the forbidden judgment set. The POSITIVE CONTROL runs
FIRST: the same traversal applied to `hasTyTConstMove` MUST find `HasTyT` (a
checker that cannot catch what it must catch is not a checker), reported as a
compile-time `logInfo`; then `levelsIn`/`levelsInArgs` (the R-1″ predicate,
whose iotaSpine arm now also reads the witness lists) and the preserved
`levelsInR1`/`levelsInR1Args` are asserted CLEAN on the full forbidden list. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : List Name :=
    [`Rcic.Declarative.HasTyT, `Rcic.Declarative.ConvT,
     `Rcic.Declarative.TyConvT, `Rcic.Declarative.CtxWfT,
     `Rcic.Declarative.EnvWfT, `Rcic.Declarative.EnvWfT.InScope,
     `AnnEnvA, `EnvSemA, `IotaSRA, `PiConvInj, `FamAppConvInj,
     `SortConvChar, `TypedRowsWf]
  let isBad (n : Name) : Bool :=
    forbidden.any fun f => (n.toString.splitOn f.toString).length > 1
  let collect (root : Name) : Lean.Elab.Command.CommandElabM (Array Name × Nat) := do
    let mut visited : Lean.NameSet := ∅
    let mut stack : Array Name := #[root]
    let mut bad : Array Name := #[]
    let mut steps := 0
    while stack.size > 0 do
      steps := steps + 1
      if steps > 30000 then
        throwError "[parRedSRT_levelsIn_audit] BFS fuel exhausted at {root}"
      let cur := stack.back
      stack := stack.pop
      if visited.contains cur then
        continue
      visited := visited.insert cur
      if isBad cur && cur != root then
        bad := bad.push cur
      match env.find? cur with
      | none => continue
      | some ci =>
        let mut used := ci.type.getUsedConstants
        match ci.value? with
        | some v => used := used ++ v.getUsedConstants
        | none => pure ()
        for u in used do
          unless visited.contains u do
            stack := stack.push u
    return (bad, visited.size)
  let (badSRT, sizeSRT) ← collect `Rcic.Declarative.parRedSRT
  unless badSRT.contains `Rcic.Declarative.HasTyT do
    throwError "[parRedSRT_levelsIn_audit] POSITIVE CONTROL FAILED: the control subject's dependency closure does not mention HasTyT"
  logInfo m!"[parRedSRT_levelsIn_audit] positive control (subject: Rcic.Declarative.parRedSRT): closure ({sizeSRT} constants) DOES mention the forbidden judgment names {badSRT}"
  for nm in [`Rcic.Declarative.levelsIn, `Rcic.Declarative.levelsInArgs,
             `Rcic.Declarative.levelsInR1, `Rcic.Declarative.levelsInR1Args] do
    let (bad, size) ← collect nm
    unless bad.isEmpty do
      throwError "[parRedSRT_levelsIn_audit] {nm} transitively mentions forbidden judgment constants: {bad}"
    logInfo m!"[parRedSRT_levelsIn_audit] {nm} CLEAN ({size} constants in closure, no judgment mention)"

end Rcic.Declarative

#print axioms Rcic.Declarative.eqN_imaxParam_zero
#print axioms Rcic.Declarative.parRedApp_armCloses
#print axioms Rcic.Declarative.convT_subst0_tyConvT
#print axioms Rcic.Declarative.convTInst0ValueSort
#print axioms Rcic.Declarative.parRedBeta_armCloses_of_sort
#print axioms Rcic.Declarative.pin_convTInst0ValueSort
#print axioms Rcic.Declarative.parRedSRT_constsSrcTyped
#print axioms Rcic.Declarative.parRedSRT_constsStep
#print axioms Rcic.Declarative.parRedSRT_constsTgtUntyped
#print axioms Rcic.Declarative.parRedSRT_claimFalse
#print axioms Rcic.Declarative.hasTyTInv_sortT
#print axioms Rcic.Declarative.hasTyA_type_sort
#print axioms Rcic.Declarative.hasTyT_type_sort_exists
#print axioms Rcic.Declarative.hasTyT_type_sort_exists_scope
#print axioms Rcic.Declarative.DT007T_typing_regularity
#print axioms Rcic.Declarative.pin_DT007T_natU
#print axioms Rcic.Declarative.convT_of_tyConvT_sort_scope
#print axioms Rcic.Declarative.pin_hasTyT_type_sort_typed
#print axioms Rcic.Declarative.levelsIn
#print axioms Rcic.Declarative.levelsInArgs
#print axioms Rcic.Declarative.levelsInR1
#print axioms Rcic.Declarative.levelsInR1Args
#print axioms Rcic.Declarative.levelsInArgs_parRedArgs_refl
#print axioms Rcic.Declarative.levelsIn_eq_mpr
#print axioms Rcic.Declarative.levelsIn_eq_mpr_tgt
#print axioms Rcic.Declarative.foldApps_cons_is_app
#print axioms Rcic.Declarative.foldApps_cons_eq_app_inv
#print axioms Rcic.Declarative.hasTyTConstSpineBound
#print axioms Rcic.Declarative.step_to_parRed_levelsIn
#print axioms Rcic.Declarative.get?_lt_length
#print axioms Rcic.Declarative.lookupType_getQ_letBinding
#print axioms Rcic.Declarative.lookupValue_getQ_letBinding
#print axioms Rcic.Declarative.lookupType_replace_let_zero
#print axioms Rcic.Declarative.lookupType_replace_let_ne
#print axioms Rcic.Declarative.lookupValue_replace_let_zero
#print axioms Rcic.Declarative.lookupValue_replace_let_ne
#print axioms Rcic.Declarative.ctxWfT_drop
#print axioms Rcic.Declarative.ctxWfTLookupValueAtDrop
#print axioms Rcic.Declarative.hasTyTLiftPrefix
#print axioms Rcic.Declarative.convTLiftPrefix
#print axioms Rcic.Declarative.hasTyTLiftPrefixDecl
#print axioms Rcic.Declarative.convTLiftPrefixDecl
#print axioms Rcic.Declarative.convTConvAssumpAt
#print axioms Rcic.Declarative.hasTyTConvAssumpAt
#print axioms Rcic.Declarative.hasTyTConvAssump
#print axioms Rcic.Declarative.convTConvLetAt
#print axioms Rcic.Declarative.hasTyTConvLetAt
#print axioms Rcic.Declarative.hasTyTConvLet
#print axioms Rcic.Declarative.hasTyTConstMove
#print axioms Rcic.Declarative.hasTyTConstMoveConv
#print axioms Rcic.Declarative.convTInst0ValueSortLet
#print axioms Rcic.Declarative.eqNList_pin
#print axioms Rcic.Declarative.levelsBounded_pin
#print axioms Rcic.Declarative.parRedSRT_sortEq
#print axioms Rcic.Declarative.parRedSRT_consts
#print axioms Rcic.Declarative.parRedSRT_delta
#print axioms Rcic.Declarative.parRedSRT_lit
#print axioms Rcic.Declarative.parRedSRT_constsStep_levelsInFalse
#print axioms Rcic.Declarative.eqN_imaxParam_rightZero
#print axioms Rcic.Declarative.pin_parRedSRT_constsInRange
#print axioms Rcic.Declarative.pin_parRedSRT_beta
#print axioms Rcic.Declarative.eqN_iotaCM_true_zero
#print axioms Rcic.Declarative.icmTrueSort
#print axioms Rcic.Declarative.icmTTTrue
#print axioms Rcic.Declarative.icmMotiveTy
#print axioms Rcic.Declarative.icmMinorZTy
#print axioms Rcic.Declarative.icmMinorSTy
#print axioms Rcic.Declarative.iotaRhsOf_wSuccDrift
#print axioms Rcic.Declarative.iotaLhsOf_wSuccDrift
#print axioms Rcic.Declarative.parRedSRT_iotaSrcTyped
#print axioms Rcic.Declarative.parRedSRT_iotaStep
#print axioms Rcic.Declarative.parRedSRT_iotaStep_levelsInR1
#print axioms Rcic.Declarative.parRedSRT_iotaStep_levelsInFalse
#print axioms Rcic.Declarative.parRedSRT_iotaTgtUntyped
#print axioms Rcic.Declarative.parRedSRT_levelsIn_claimFalse
#print axioms Rcic.Declarative.parRedConvT
#print axioms Rcic.Declarative.parRedArgsConvT
#print axioms Rcic.Declarative.parRedArgsSRT
#print axioms Rcic.Declarative.parRedSRT
#print axioms Rcic.Declarative.parRedSRT_betaSrc
#print axioms Rcic.Declarative.parRedSRT_betaStep
#print axioms Rcic.Declarative.wSuccDrift0
#print axioms Rcic.Declarative.iotaRhsOf_wSuccDrift0
#print axioms Rcic.Declarative.parRedSRT_iotaDriftStep
#print axioms Rcic.Declarative.parRedSRT_iotaDriftStep_levelsIn
#print axioms Rcic.Declarative.pin_parRedSRT_iotaDrift
