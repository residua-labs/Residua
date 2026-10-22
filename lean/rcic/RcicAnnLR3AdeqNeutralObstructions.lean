import rcic.RcicAnnLR3AdeqRelation
import rcic.RcicAnnLR3NeutralKSource
import rcic.RcicAnnLR3CandidatePi
import rcic.RcicAnnLR3TypedNeutralAttachment
import rcic.RcicAnnLR3InductiveCodeControls

/-!
# Proof irrelevance, K, and neutral-PER boundaries for adequacy / readback

This module kernel-checks the exact positive laws and inhabited obstructions governing
how proof irrelevance (`ConvT.irr` / `ConvA.irr`) and singleton-Prop elimination (`K`)
enter adequacy and readback in the `RcicAnnLR3*` paired PER model:

1. **Glued `Sort 0` adequacy vs unglued value-only reification (§1)**:
   - *Positive law (`glued_native_prop_readback_irr`, `glued_ann_prop_readback_irr`,
     `glued_native_proof_indexed_type_readback`)*: in a glued adequacy relation that
     retains the well-typed source terms `Γ ⊢ a, b : P` at a proposition `Γ ⊢ P : .sort .zero`,
     syntactic conversion `Conv Γ a b P` is discharged unconditionally in a single
     `Conv.irr` step—without inspecting or reifying the semantic proof values `x, y`—and
     lifts by `Conv.app` to any proof-indexed type family `F : Π (_ : P), .sort u`.
   - *Unglued obstruction (`unglued_value_reification_obstruction`)*: raw semantic values
     in `NeutralPER` and `CandidatePi` cannot be reified to unique syntax up to conversion
     without gluing, because `ProofPER` equates `neutralAtom r` and `unitValue` (under `True`)
     and equates all `neutralAtom r, s` (even under `False`), while `CandidatePi.falseElement`
     and `CandidatePi.trueElement` have the exact same raw `Value` (`collision_same_value`)
     despite `¬ ElementRel falseElement trueElement`.

2. **Neutral-type collapse in `NeutralCodes` / `legacyUniverseSystem` (§2)**:
   - *Inhabited obstruction (`neutralCodes_universe_collapses_distinct_names`,
     `generic_bvars_collide_in_neutralCodes`)*: `NeutralCodes.Related` equates
     `.neutralType k r₁` and `.neutralType k r₂` whenever `k = k`, ignoring `r₁` vs `r₂`.
     Consequently, `(universeNeutral k r₁).value` and `(universeNeutral k r₂).value` (for
     `r₁ ≠ r₂`, e.g. `91` and `92` from `TypedNeutralAttachment`) have `¬ ValueEq`, yet
     satisfy `NeutralCodes.UniversePER k` and `RelatedCode legacyUniverseSystem`. Likewise,
     in a context with two distinct sort assumptions, `nativeGeneric` reflects them to
     distinct values that are `RelatedCode`-related in `NeutralCodes.codeSystem`. Any
     unglued type readback from `NeutralCodes` / `legacyUniverseSystem` would falsely
     equate distinct neutral type variables or axioms of the same universe level.

3. **Forward-only K vs large-K `CodePair` / Π-domain inversion in `CodeI` (§3)**:
   - *Why the K converse (`ExactK`) is not needed by readback*: `NeutralKSource` refutes
     `ExactK` at a `Prop` target (`targetProp := Eq Prop parameter parameter`) because
     two `ConvA.irr` steps through a neutral bridge relate `stuckCall` and `minor` when
     their endpoints `parameter` and `domain` are apart. Readback does not need `ExactK`:
     at `Sort 0` targets `Conv.irr` suffices directly, while at higher-sort targets
     readback only traverses forward `Seed.k` edges whose `Guard` supplies endpoint
     relatedness (`Conv Γ a b A`), which in RCIC syntax derives the K step via
     `Conv.irr` (aligning the neutral major with `refl`) + `Conv.app` + `Conv.iota`
     (witnessed by `EqLargeFixture.conversion`).
   - *Inhabited obstruction (`inhabited_large_k_pi_domain_obstruction`)*: in the admitted
     `EqLargeFixture.env` and well-formed `EqLargeFixture.context`, `EqLargeFixture.call (.bvar 0)`
     is a stuck large `Eq.rec` at `.sort one` (`StuckA`) convertible to the canonical Π type
     `EqLargeFixture.result = .pi (.sort .zero) one (.sort .zero) one`, inducing an inhabited
     Π-type conversion `ConvA ... (.pi (call (.bvar 0)) one (.sort .zero) one) (.pi result one (.sort .zero) one) (.sort (.imax one one))`.
     In `InductiveCodes.legacyUniverseSystem` (`CodeI`), `result` decodes via `CodeI.pi` to
     `InductiveCodeControls.productPER`. However, when `.bvar 0` is reflected to a neutral,
     neither a raw neutral atom `neutralAtom r` nor any tagged neutral type
     `reify (.neutralType l name)` can form a `CodePair` (or `RelatedCode`) with `result` in
     `CodeI`: `neutralAtom r` has no `CodeI` presentation at all (`¬ SortMember`), while
     `El (.neutralType l name) = ProofPER Neutral False` contains `neutralAtom 0` whereas
     `productPER` does not (`¬ Same (El (.neutralType l name)) productPER`). Thus adding a
     post-hoc forward edge in `NeutralK.Saturated` at `Sort 1` without transporting the
     `CodeI` element PER breaks `UniverseTransport` and semantic Π-domain `CodePair` inversion.

No `sorry`, no `Classical.choice`, no `native_decide`, no new axioms.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.AdeqNeutralObstructions

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralExtraction PairedStatements
open InductiveCodes AdeqRelation

/-! ## §1 Proof Irrelevance at `Sort 0`: Glued Adequacy vs Unglued Value Reification -/

/-- Glued adequacy readback at `Sort 0` on native `Expr Nat`: whenever two well-typed
source proofs `a, b` inhabit the same proposition `P : .sort .zero`, syntactic conversion
`ConvT E n Γ a b P` holds in one `ConvT.irr` step without inspecting semantic values. -/
theorem glued_native_prop_readback_irr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P a b : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (ha : HasTyT E n Γ a P) (hb : HasTyT E n Γ b P) :
    Nonempty (ConvT E n Γ a b P) :=
  ⟨.irr Γ P a b hP ha hb⟩

/-- Glued adequacy readback at `Sort 0` on annotated `ExprA`: `ConvA.irr` equates any
two well-typed proofs of the same proposition `P : .sort .zero` without inspecting
their semantic proof values. -/
theorem glued_ann_prop_readback_irr {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {P a b : ExprA}
    (hP : HasTyA E I n Γ P (.sort .zero))
    (ha : HasTyA E I n Γ a P) (hb : HasTyA E I n Γ b P) :
    Nonempty (ConvA E I n Γ a b P) :=
  ⟨.irr Γ P a b hP ha hb⟩

/-- Proof-indexed type family congruence on native `Expr Nat`: if `F : .pi P (.sort u)`
is a type family indexed by a proposition `P : .sort .zero`, then for any two well-typed
proofs `a, b : P`, the applied types `.app F a` and `.app F b` are convertible at `.sort u`
via `ConvT.irr` + `ConvT.app`, with no neutral-spine reification required at `P`. -/
theorem glued_native_proof_indexed_type_readback {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P F a b : Expr Nat} {u : Level}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hF : HasTyT E n Γ F (.pi P (.sort u)))
    (ha : HasTyT E n Γ a P) (hb : HasTyT E n Γ b P) :
    Nonempty (ConvT E n Γ (.app F a) (.app F b) (.sort u)) :=
  ⟨.app Γ F F a b P (.sort u) (.refl Γ F (.pi P (.sort u)) hF) (.irr Γ P a b hP ha hb)⟩

/-- Unglued value-only reification obstruction: in `NeutralPER` and `CandidatePi`,
(1) `ProofPER Neutral False` relates distinct neutral atoms `neutralAtom 0` and
`neutralAtom 1` even when `truth = False`,
(2) `ProofPER Neutral True` relates `neutralAtom 0` and `unitValue EnvI.bot` despite
`¬ ValueEq (neutralAtom 0) (unitValue EnvI.bot)`, and
(3) `CandidatePi.falseElement` and `CandidatePi.trueElement` have the exact same raw
`Value` despite `¬ CandidatePi.ElementRel falseElement trueElement`, so no function on
raw `Value` can recover the element PER or distinguish `falseElement` from `trueElement`. -/
theorem unglued_value_reification_obstruction :
    NeutralPER.ProofPER NeutralCodes.Neutral False
      (NeutralPER.neutralAtom 0) (NeutralPER.neutralAtom 1) ∧
    NeutralPER.ProofPER NeutralCodes.Neutral True
      (NeutralPER.neutralAtom 0) (unitValue EnvI.bot) ∧
    (¬ ValueEq (NeutralPER.neutralAtom 0) (unitValue EnvI.bot)) ∧
    CandidatePi.falseElement.value = CandidatePi.trueElement.value ∧
    (¬ CandidatePi.ElementRel CandidatePi.falseElement CandidatePi.trueElement) ∧
    (∀ D : Value → Relation,
      ¬ (∀ e : CandidatePi.Element, Same (D e.value) (CandidatePi.decode e))) :=
  ⟨NeutralPER.proofPER_irrelevant
      (NeutralPER.neutral_member NeutralCodes.Neutral False ⟨0, ValueEq.refl _⟩)
      (NeutralPER.neutral_member NeutralCodes.Neutral False ⟨1, ValueEq.refl _⟩),
    NeutralPER.proofPER_irrelevant
      (NeutralPER.neutral_member NeutralCodes.Neutral True ⟨0, ValueEq.refl _⟩)
      (NeutralPER.unit_member_of_truth NeutralCodes.Neutral trivial),
    NeutralPER.neutralAtom_not_unit 0,
    CandidatePi.collision_same_value,
    CandidatePi.collision_not_related,
    CandidatePi.no_raw_fibre_decoder⟩

/-! ## §2 Neutral-Type Collapse in `NeutralCodes` and `legacyUniverseSystem` -/

/-- For any universe level `k` and distinct names `r₁ ≠ r₂`, `TypedNeutralProducer.universeNeutral`
produces distinct values (`¬ ValueEq`) that are nevertheless related in
`NeutralCodes.UniversePER k` and `RelatedCode legacyUniverseSystem`. -/
theorem neutralCodes_universe_collapses_distinct_names (k : Option Nat)
    {r₁ r₂ : Nat} (hne : r₁ ≠ r₂) :
    (¬ ValueEq (TypedNeutralProducer.universeNeutral k r₁).value
        (TypedNeutralProducer.universeNeutral k r₂).value) ∧
    NeutralCodes.UniversePER k
      (TypedNeutralProducer.universeNeutral k r₁).value
      (TypedNeutralProducer.universeNeutral k r₂).value ∧
    RelatedCode legacyUniverseSystem
      (TypedNeutralProducer.universeNeutral k r₁).value
      (TypedNeutralProducer.universeNeutral k r₂).value := by
  have hnotEq : ¬ ValueEq (TypedNeutralProducer.universeNeutral k r₁).value
      (TypedNeutralProducer.universeNeutral k r₂).value := by
    intro h
    have hd := NeutralCodes.reify_injective
      (d := .neutralType k r₁) (e := .neutralType k r₂) h
    exact hne (NeutralCodes.Descriptor.neutralType.inj hd).2
  have hUniv : NeutralCodes.UniversePER k
      (TypedNeutralProducer.universeNeutral k r₁).value
      (TypedNeutralProducer.universeNeutral k r₂).value :=
    ⟨.neutralType k r₁, .neutralType k r₂, rfl, rfl, ValueEq.refl _, ValueEq.refl _⟩
  obtain ⟨R, S, hPair⟩ := legacyUniverseTransport.relate hUniv
  exact ⟨hnotEq, hUniv, ⟨k, R, S, hPair⟩⟩

/-- Concrete pin at the two constant references `91` (opaque) and `92` (axiom) of
`TypedNeutralAttachment` at level `some 1` (`Sort 1`): their attached universe-neutral
values are distinct (`¬ ValueEq`), yet `RelatedCode legacyUniverseSystem` equates them. -/
theorem typedNeutralAttachment_refs_91_92_related_code :
    (¬ ValueEq (TypedNeutralProducer.universeNeutral (some 1) 91).value
        (TypedNeutralProducer.universeNeutral (some 1) 92).value) ∧
    RelatedCode legacyUniverseSystem
      (TypedNeutralProducer.universeNeutral (some 1) 91).value
      (TypedNeutralProducer.universeNeutral (some 1) 92).value := by
  have h := neutralCodes_universe_collapses_distinct_names (some 1)
    (r₁ := 91) (r₂ := 92) (by decide)
  exact ⟨h.1, h.2.2⟩

/-- In a context with two sort-typed assumptions, `NeutralCodes.reflect` reflects levels
`0` and `1` at `universeValue k` to distinct neutral type values (`¬ ValueEq`) that are
nevertheless `RelatedCode`-related in `NeutralCodes.codeSystem`. -/
theorem generic_bvars_collide_in_neutralCodes (k : Option Nat) :
    (¬ ValueEq (NeutralCodes.reflect (universeValue k) 0)
        (NeutralCodes.reflect (universeValue k) 1)) ∧
    RelatedCode NeutralCodes.codeSystem
      (NeutralCodes.reflect (universeValue k) 0)
      (NeutralCodes.reflect (universeValue k) 1) := by
  have h0 : ValueEq (NeutralCodes.reflect (universeValue k) 0)
      (NeutralCodes.reify (.neutralType k 0)) :=
    NeutralCodes.reflect_at (d := .univ k) (ValueEq.refl _) 0
  have h1 : ValueEq (NeutralCodes.reflect (universeValue k) 1)
      (NeutralCodes.reify (.neutralType k 1)) :=
    NeutralCodes.reflect_at (d := .univ k) (ValueEq.refl _) 1
  have hdist := NeutralCodes.distinct_related_neutral_codes k
  have hnotEq : ¬ ValueEq (NeutralCodes.reflect (universeValue k) 0)
      (NeutralCodes.reflect (universeValue k) 1) := by
    intro heq
    exact hdist.1 (h0.symm.trans (heq.trans h1))
  have hCode0 : NeutralCodes.Code k (NeutralCodes.reflect (universeValue k) 0)
      (NeutralCodes.El (.neutralType k 0)) :=
    ⟨.neutralType k 0, rfl, h0, fun _ _ => Iff.rfl⟩
  have hCode1 : NeutralCodes.Code k (NeutralCodes.reflect (universeValue k) 1)
      (NeutralCodes.El (.neutralType k 1)) :=
    ⟨.neutralType k 1, rfl, h1, fun _ _ => Iff.rfl⟩
  exact ⟨hnotEq, ⟨k, _, _, ⟨hCode0, hCode1, hdist.2.2⟩⟩⟩

/-! ## §3 Inhabited Large-K Obstruction to `CodePair` and Π-Domain Inversion in `CodeI` -/

/-- A raw neutral atom `neutralAtom r` has no `CodeI` presentation at any universe
level `k` (`¬ CodeI k (neutralAtom r) R`), because every `CodeI` type value satisfies
`SortMember k`, which `neutralAtom r` fails. -/
theorem raw_neutralAtom_not_codeI (k : Option Nat) (r : Nat) (R : Relation) :
    ¬ CodeI k (NeutralPER.neutralAtom r) R :=
  fun h => NeutralPER.neutralAtom_not_sort_member r k (code_level h)

/-- Consequently, a raw neutral atom `neutralAtom r` is never `RelatedCode`-related in
`legacyUniverseSystem` to any value `W`. -/
theorem raw_neutralAtom_not_relatedCode (r : Nat) (W : Value) :
    ¬ RelatedCode legacyUniverseSystem (NeutralPER.neutralAtom r) W := by
  rintro ⟨k, R, _, hPair⟩
  exact raw_neutralAtom_not_codeI k r R hPair.left_code

/-- `NeutralPER.neutralAtom 0` is a member of `NeutralCodes.El (.neutralType l name)`. -/
theorem neutralAtom0_member_neutralType_el (l : Option Nat) (name : Nat) :
    Member (NeutralCodes.El (.neutralType l name)) (NeutralPER.neutralAtom 0) :=
  NeutralCodes.reflectDescriptor_member (.neutralType l name) 0

/-- `NeutralPER.neutralAtom 0` is NOT a member of `InductiveCodeControls.productPER`
(the `CodeI` element PER of `EqLargeFixture.result = .pi (.sort .zero) one (.sort .zero) one`),
because applying `neutralAtom 0` to `reify (.proof False)` produces the untagged neutral
spine `.spine 0 [.bot]`, which violates `SortMember (some 0)` of `UniversePER (some 0)`. -/
theorem neutralAtom0_not_member_productPER :
    ¬ Member InductiveCodeControls.productPER (NeutralPER.neutralAtom 0) := by
  intro hmem
  let x : Value := NeutralCodes.reify (.proof False)
  have hx : Member (NeutralCodes.UniversePER (some 0)) x :=
    NeutralCodes.code_member_universe (NeutralCodes.code (.proof False))
  have happ : Member (NeutralCodes.UniversePER (some 0))
      (NeutralPi.applyValue (NeutralPER.neutralAtom 0) x) :=
    hmem x x hx
  have hsort : SortMember (some 0)
      (NeutralPi.applyValue (NeutralPER.neutralAtom 0) x) :=
    (NeutralCodes.universe_elim (NeutralCodes.code_universe (some 0)) happ).1
  have hspine : NeutralPi.applyValue (NeutralPER.neutralAtom 0) x (.spine 0 [.bot]) :=
    Or.inr (Or.inr ⟨0, [], .bot, rfl, ApproxI.const EnvI.bot 0 [], Or.inl rfl⟩)
  have htag := hsort (.spine 0 [.bot]) hspine
  cases htag

/-- No `CodeI` presentation of a tagged neutral type `reify (.neutralType l name)` has
an element PER equivalent (`Same`) to `InductiveCodeControls.productPER`. -/
theorem neutralType_codeI_not_same_productPER {k l : Option Nat} {name : Nat}
    {R : Relation} (hR : CodeI k (NeutralCodes.reify (.neutralType l name)) R) :
    ¬ Same R InductiveCodeControls.productPER := by
  intro hSame
  have hOld : CodeI l (NeutralCodes.reify (.neutralType l name))
      (NeutralCodes.El (.neutralType l name)) :=
    .old (NeutralCodes.code (.neutralType l name))
  have hCoherent : Same R (NeutralCodes.El (.neutralType l name)) :=
    code_coherent hR hOld
  have hMemR : Member R (NeutralPER.neutralAtom 0) :=
    (hCoherent _ _).mpr (neutralAtom0_member_neutralType_el l name)
  exact neutralAtom0_not_member_productPER ((hSame _ _).mp hMemR)

/-- No `CodePair` (and hence no `RelatedCode`) exists in `legacyUniverseSystem` between
any tagged neutral type `reify (.neutralType l name)` and the semantic image of
`EqLargeFixture.result` (`UnitModel.denote zeroValuation EnvI.bot EqLargeFixture.result`). -/
theorem neutralType_not_relatedCode_result (l : Option Nat) (name : Nat) :
    ¬ RelatedCode legacyUniverseSystem
        (NeutralCodes.reify (.neutralType l name))
        (UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot
          EqLargeFixture.result) := by
  rintro ⟨k, R, S, hPair⟩
  have hS : Same S InductiveCodeControls.productPER :=
    code_coherent hPair.right_code InductiveCodeControls.product_source_code
  have hR : Same R InductiveCodeControls.productPER :=
    fun x y => (hPair.transport x y).trans (hS x y)
  exact neutralType_codeI_not_same_productPER hPair.left_code hR

/-- Inhabited Π-type conversion in `EqLargeFixture.env` and `EqLargeFixture.context`
whose left domain is the stuck large-K call `EqLargeFixture.call (.bvar 0)` and whose
right domain is the canonical Π type `EqLargeFixture.result`. -/
theorem pi_domain_large_k_conversion :
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context
      (.pi (EqLargeFixture.call (.bvar 0)) EqLargeFixture.one
        (.sort .zero) EqLargeFixture.one)
      (.pi EqLargeFixture.result EqLargeFixture.one
        (.sort .zero) EqLargeFixture.one)
      (.sort (.imax EqLargeFixture.one EqLargeFixture.one))) := by
  obtain ⟨hc⟩ := EqLargeFixture.conversion
  have hrt : HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context
      (.pi EqLargeFixture.result EqLargeFixture.one (.sort .zero) EqLargeFixture.one)
      (.sort (.imax EqLargeFixture.one EqLargeFixture.one)) :=
    .pi EqLargeFixture.context EqLargeFixture.result EqLargeFixture.one
      (.sort .zero) EqLargeFixture.one
      EqLargeFixture.resultTyped (.sort _ .zero)
  exact ⟨.pi EqLargeFixture.context
    (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result
    (.sort .zero) (.sort .zero)
    EqLargeFixture.one EqLargeFixture.one EqLargeFixture.one EqLargeFixture.one
    (eqNA_refl _) (eqNA_refl _) hc
    (.refl _ (.sort .zero) (.sort EqLargeFixture.one) (.sort _ .zero))
    hrt⟩

/-- Combined inhabited boundary for large K + Π-domain inversion in `CodeI`:
(1) `EqLargeFixture.env` is admitted (`EnvWfA`) and `EqLargeFixture.context` is well-formed (`CtxWfA`),
(2) `EqLargeFixture.call (.bvar 0)` is a stuck (`StuckA`) large-K elimination at `.sort one`
    convertible (`ConvA`) to `EqLargeFixture.result = .pi (.sort .zero) one (.sort .zero) one`,
(3) wrapping both as domains produces an inhabited `ConvA` between two Π types at `.sort (imax one one)`,
(4) `EqLargeFixture.result` has the `CodeI (some 1)` presentation `InductiveCodeControls.product_source_code`,
(5) yet neither a raw neutral atom `neutralAtom r` nor any tagged neutral type
    `reify (.neutralType l name)` is `RelatedCode`-related to `EqLargeFixture.result` in
    `legacyUniverseSystem`. -/
theorem inhabited_large_k_pi_domain_obstruction (r : Nat) (l : Option Nat) (name : Nat) :
    eraseEnv EqLargeFixture.env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context) ∧
    StuckA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0)) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context
      (.pi (EqLargeFixture.call (.bvar 0)) EqLargeFixture.one
        (.sort .zero) EqLargeFixture.one)
      (.pi EqLargeFixture.result EqLargeFixture.one
        (.sort .zero) EqLargeFixture.one)
      (.sort (.imax EqLargeFixture.one EqLargeFixture.one))) ∧
    CodeI (some 1)
      (UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot
        EqLargeFixture.result)
      InductiveCodeControls.productPER ∧
    (¬ RelatedCode legacyUniverseSystem
        (NeutralPER.neutralAtom r)
        (UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot
          EqLargeFixture.result)) ∧
    (¬ RelatedCode legacyUniverseSystem
        (NeutralCodes.reify (.neutralType l name))
        (UnitModel.denote InductiveCodeControls.zeroValuation EnvI.bot
          EqLargeFixture.result)) :=
  ⟨EqLargeFixture.erase_env,
    EqLargeFixture.wf,
    ⟨EqLargeFixture.contextWf⟩,
    EqLargeFixture.callStuck,
    EqLargeFixture.conversion,
    pi_domain_large_k_conversion,
    InductiveCodeControls.product_source_code,
    raw_neutralAtom_not_relatedCode r _,
    neutralType_not_relatedCode_result l name⟩

end Rcic.Declarative.Ann.LR3.AdeqNeutralObstructions
