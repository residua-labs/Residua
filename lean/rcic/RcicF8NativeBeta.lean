import rcic.RcicDT0709EnvWf
import rcic.RcicTypedSubst
import rcic.RcicF8JTotalityPins

/-!
# `RcicF8NativeBeta` — native β / symmetric-β valley producer (piRow C)

`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §4 (in-tree via
#7515); lane brief `pirow-C-beta`. `closure_claim = 0`.

§4.1: from a `ConvT.beta` node's three typing children, regularity +
head substitution build the `ParRedT.beta` step; the native valley puts
that step on the left leg and `ParRedT.refl` on the right, centre
`N = instantiate0 arg body`. The symmetric form swaps the legs. No sort
uniqueness, Π row, family row, recursive J call or diamond supplier is
used.

§4.2: the recipe is keyed by the ORIGINAL β derivation and retains only
`[.ty hA, .ty hbody, .ty harg]` — the regularity proof, the two
substituted typings and the parallel step are evaluator outputs, not new
literal leaves. On the landed U→X fixture, the β child of the first
symmetric request and the later top-level β request have different
occurrence addresses though their source derivations coincide; each is
evaluated through its own source receipt.

§4.3 boundary: `ParRedValleyT` is NOT a value of the old `Valley` —
`EvPar`'s six constructors and `EvParX`'s six have no β arm. The exact
carrier integration needed is recorded in
`research/rcic/sortrow/PIROW_STATUS_pirow-C-beta.md`; no `literalWorker`
claim is made.
-/

namespace Rcic.Declarative

open F8Measure

variable {E : ResolvedEnv} {n : Nat}

/-- Native join at a fixed type index over the typed parallel star —
    the carrier-agnostic analogue of the old provenance `Valley`
    (`RcicF8EvParStar`), whose `EvPar`/`EvParX` step carriers have no
    β arm. No provenance receipts are asserted. -/
structure ParRedValleyT (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M₁ M₂ T : Expr Nat) where
  /-- the common reduct both legs reach. -/
  N : Expr Nat
  left : ParRedTStar PEq E n Γ M₁ N T
  right : ParRedTStar PEq E n Γ M₂ N T
  ty₁ : HasTyT E n Γ M₁ T
  ty₂ : HasTyT E n Γ M₂ T

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
  {Γ : LCtx} {M₁ M₂ T : Expr Nat}

/-- leg swap — the symmetric form shares centre and typings. -/
def ParRedValleyT.symm (V : ParRedValleyT PEq E n Γ M₁ M₂ T) :
    ParRedValleyT PEq E n Γ M₂ M₁ T :=
  ⟨V.N, V.right, V.left, V.ty₂, V.ty₁⟩

variable {A body arg B : Expr Nat} {u : Level}

/-- §4.1 — the β valley, centre `N = instantiate0 arg body`. Regularity
    on the body typing gives `B : sort v` under `assumption A :: Γ`;
    head substitution gives `hTy : instantiate0 arg B : sort v` (the
    sort is closed under `instantiate0`) and
    `hred : instantiate0 arg body : instantiate0 arg B`. The left leg is
    the single `ParRedT.beta` step followed by refl; the right leg is
    refl. `ty₁` is the ordinary application typing; `ty₂` is `hred`. -/
def betaParRedValley (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    ParRedValleyT PEq E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B) := by
  let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
  let ⟨v, hB⟩ := regularT_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓA hbody
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  have hred : HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B) :=
    hasTyT_subst0S hcl hinst hbody harg
  have hTy : HasTyT E n Γ (instantiate0 arg B) (.sort v) :=
    hasTyT_subst0S hcl hinst hB harg
  exact ⟨instantiate0 arg body,
    .tail
      (.beta Γ A body body arg arg B u v v hA hB hTy
        (.refl _ _ _ hbody) (.refl _ _ _ harg) hred)
      (.refl _ _ _ hred),
    .refl _ _ _ hred,
    .app Γ (.lam A body) arg A B (.lam Γ A u body B hA hbody) harg,
    hred⟩

/-- §4.2 — a native β answer: the valley plus the retained literal
    support. `kept` is exactly the β constructor's own typing children;
    the regularity proof, the two substituted typings and the parallel
    step are evaluator outputs, not new literal leaves. -/
structure NativeBetaAnswer
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat) where
  valley : ParRedValleyT PEq E n Γ a b T
  kept : List (Jd E n)

/-- §4.1–§4.2 — the recipe keyed by the ORIGINAL β derivation. A `beta`
    node answers with the §4.1 valley; a `symm` node whose child is
    `beta` answers with the swapped valley, `kept` still being the β
    child's three typing children (strictly below the symmetric parent).
    Every other constructor is refused — the recipe claims no other
    arm. -/
def nativeBetaValley (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) : Option (NativeBetaAnswer PEq E n Γ a b T) :=
  match h with
  | .beta _ A body arg B _u hA hbody harg =>
      some ⟨betaParRedValley hW hΓ hA hbody harg,
        [.ty hA, .ty hbody, .ty harg]⟩
  | .symm _ _ _ _ (.beta _ A body arg B _u hA hbody harg) =>
      some ⟨(betaParRedValley hW hΓ hA hbody harg).symm,
        [.ty hA, .ty hbody, .ty harg]⟩
  | _ => none

/-- `kept` for a raw β literal is exactly its three typing children. -/
theorem nativeBetaValley_kept_beta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    (nativeBetaValley PEq hW hΓ
      (.beta Γ A body arg B u hA hbody harg)).map NativeBetaAnswer.kept =
        some [.ty hA, .ty hbody, .ty harg] := rfl

/-- `kept` for a symmetric β literal is still the β child's three typing
    children — strictly below the symmetric parent. -/
theorem nativeBetaValley_kept_symmBeta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    (nativeBetaValley PEq hW hΓ
      (.symm Γ (.app (.lam A body) arg) (instantiate0 arg body)
        (instantiate0 arg B)
        (.beta Γ A body arg B u hA hbody harg))).map
          NativeBetaAnswer.kept =
        some [.ty hA, .ty hbody, .ty harg] := rfl

/-- The kept children of a symmetric β sit strictly below the symmetric
    parent literal: each is a `.ty` child of the β node, itself the
    `.cv` child of the symm literal. -/
theorem kept_subOf_symmBeta {Γ : LCtx} {A body arg B : Expr Nat}
    {u : Level} (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    ∀ ℓ ∈ ([.ty hA, .ty hbody, .ty harg] : List (Jd E n)),
      SubOf ℓ (.cv (.symm Γ (.app (.lam A body) arg)
        (instantiate0 arg body) (instantiate0 arg B)
        (.beta Γ A body arg B u hA hbody harg))) :=
  fun _ℓ hℓ => .trans
    (.child (y := .cv (.beta Γ A body arg B u hA hbody harg)) hℓ)
    (.child (cvChildSymm (.beta Γ A body arg B u hA hbody harg)))

end Rcic.Declarative

/-! ### §4.2 on the landed fixture — two β occurrences, two receipts -/

namespace Rcic.Declarative.F8Measure.JTotality.Pins

open Rcic.Declarative.F8Measure.UAppDemandPins
open Rcic.Declarative

/-- The later raw request's own source receipt — the `.cv`-literal
    certificate `betaSecondCert`, reached by the conv-child descent. -/
theorem qRawBeta_own_receipt : qRawBeta.hs = betaSecondCert := rfl

/-- The first symmetric request's own source receipt. -/
theorem qBeta_own_receipt : qBeta.hs = betaFirstCert := rfl

/-- The β child below the symmetric parent evaluates the same
    `betaInCtx` through a strict sub-derivation receipt: `.cv betaInCtx`
    is the `.symm` child of `.cv betaToRedex`, itself certified by
    `betaFirstCert`. Its own source receipt — a different certificate
    path than `betaSecondCert`'s conv-child descent, for the same source
    derivation. -/
def firstBetaChildReceipt : ∃ r ∈ roots, SubEq (.cv betaInCtx) r :=
  certOfChild (cvChildSymm betaInCtx) betaFirstCert

/-- The recipe's kept leaves for the symmetric parent are its β child's
    typing children — strictly below the symmetric literal. -/
theorem fixture_symm_kept_below_parent :
    ∀ ℓ ∈ Jd.cvChildren betaInCtx, SubOf ℓ (.cv betaToRedex) :=
  fun _ℓ hℓ => .trans (.child (y := .cv betaInCtx) hℓ)
    (.child (cvChildSymm betaInCtx))

/-- §4.2 census on the actual fixture: the β child of the first
    symmetric request and the later top-level β request share one source
    derivation (`betaInCtx`), keep different occurrence addresses, and
    each is evaluated through its own source receipt — the raw request
    through `betaSecondCert`, the child through `firstBetaChildReceipt`,
    the symmetric parent through `betaFirstCert`. The keyed recipe
    answers all three. -/
theorem fixture_beta_occurrence_census :
    firstBetaChild.h = qRawBeta.h ∧
    firstBetaChild.address.xOccurrence ≠ qRawBeta.path ∧
    qRawBeta.hs = betaSecondCert ∧
    qBeta.hs = betaFirstCert ∧
    (nativeBetaValley (PEqLeafT emptyEnv 0) EnvWfT.empty ctxWf
      qRawBeta.h).isSome = true ∧
    (nativeBetaValley (PEqLeafT emptyEnv 0) EnvWfT.empty ctxWf
      firstBetaChild.h).isSome = true ∧
    (nativeBetaValley (PEqLeafT emptyEnv 0) EnvWfT.empty ctxWf
      qBeta.h).isSome = true :=
  ⟨child_and_later_request_same_source,
    child_and_later_request_distinct_address,
    rfl, rfl, rfl, rfl, rfl⟩

end Rcic.Declarative.F8Measure.JTotality.Pins

#print axioms Rcic.Declarative.ParRedValleyT
#print axioms Rcic.Declarative.betaParRedValley
#print axioms Rcic.Declarative.NativeBetaAnswer
#print axioms Rcic.Declarative.nativeBetaValley
#print axioms Rcic.Declarative.nativeBetaValley_kept_beta
#print axioms Rcic.Declarative.nativeBetaValley_kept_symmBeta
#print axioms Rcic.Declarative.kept_subOf_symmBeta
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.firstBetaChildReceipt
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.fixture_symm_kept_below_parent
#print axioms Rcic.Declarative.F8Measure.JTotality.Pins.fixture_beta_occurrence_census
