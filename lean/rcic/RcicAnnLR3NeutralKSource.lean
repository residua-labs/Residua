import rcic.RcicAnnLR3NeutralK
import rcic.RcicAnnLR3NeutralPER
import rcic.RcicAnnLR3UnitContextBoundary

/-!
# An actual admitted source instance of the neutral K exact-iff obstruction

The source endpoints are the existing closed propositions `parameter` and
`domain`. Both have exact Prop-universe membership, and their existing
compositional images are separated. The context assumes their equality
and also a proof of the inhabited proposition `domain`.

Eq.rec at level zero is applied to a constant motive returning `domain`
and the canonical minor `refl parameter`. Its neutral-major call is typed
at that same proposition. Two actual `ConvA.irr` nodes give the chain from
the call through the second neutral proof to the minor. Neither node
requires related source endpoints or a K computation.

This binds the algebraic obstruction to real source typing/conversion.
The last section also supplies an explicit local assignment on the actual
Value carrier: a neutral major in the extended equality PER, a canonical
minor, and neutral call/bridge members of the result proposition. Thus the
single-conversion soundness premise of the conditional theorem is itself
inhabited. This is not a compositional evaluator or a full semantic model,
and does not assert preservation of all old images by every possible repair.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Rcic.Declarative.Ann.LR3.NeutralKSource

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open EqLargeFixture UnitContextBoundary UnitModel TypedPER

private def applyTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) := by
  have parts := hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface hΓ hf).2
  exact .app Γ f a D C u v v parts.2
    (hasTyA_inst0 closed liftIface (iotaRecHeadTypedA_of (iotaFnA_recHead env))
      substIface hΓ parts.2 ha parts.1) hf ha

abbrev targetProp : ExprA := domain
abbrev minor : ExprA := reflAt parameter

def targetTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ targetProp (.sort .zero) :=
  eqTyped hΓ parameterTyped parameterTyped

def minorTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ minor targetProp :=
  reflTyped hΓ parameterTyped

/-- The outer assumption is p : Eq parameter domain; the new innermost
assumption q : domain is a neutral proof of the result proposition. -/
abbrev proofContext : LCtxA := .assumption targetProp :: apartContext

def proofContextWf : CtxWfA env (iotaIfaceA env) 0 proofContext :=
  .assumption apartContext_wf (targetTyped apartContext_wf)

def majorTyped : HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 1) apartProp :=
  .bvar proofContext 1 apartProp .zero rfl (apartProp_typed proofContextWf)

def bridgeTyped : HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 0) targetProp :=
  .bvar proofContext 0 targetProp .zero rfl (targetTyped proofContextWf)

abbrev propMotiveTail (a : ExprA) : ExprA :=
  .pi (eqAt parameter a) .zero (.sort .zero) one
abbrev propMotiveBody : ExprA :=
  .lam (eqAt parameter (.bvar 0)) .zero targetProp
abbrev propMotive : ExprA := .lam (.sort .zero) one propMotiveBody
abbrev propMotiveTy : ExprA :=
  .pi (.sort .zero) one (propMotiveTail (.bvar 0)) (.imax .zero one)
abbrev propMotiveAt (a p : ExprA) : ExprA := .app (.app propMotive a) p

private def propVar {Γ : LCtxA} : HasTyA env (iotaIfaceA env) 0
    (.assumption (.sort .zero) :: Γ) (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) one rfl (.sort _ .zero)

private def tailLamTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ
      (.lam (eqAt parameter a) .zero targetProp) (propMotiveTail a) :=
  .lam Γ (eqAt parameter a) .zero targetProp (.sort .zero) one
    (eqTyped hΓ parameterTyped ha) (.sort _ .zero)
    (targetTyped (.assumption hΓ (eqTyped hΓ parameterTyped ha)))

def propMotiveTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ propMotive propMotiveTy :=
  .lam Γ (.sort .zero) one propMotiveBody (propMotiveTail (.bvar 0))
    (.imax .zero one) (.sort Γ .zero)
    (.pi _ (eqAt parameter (.bvar 0)) .zero (.sort .zero) one
      (eqTyped (.assumption hΓ (.sort Γ .zero)) parameterTyped propVar) (.sort _ .zero))
    (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar)

def propMotiveAtTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    HasTyA env (iotaIfaceA env) 0 Γ (propMotiveAt a p) (.sort .zero) :=
  applyTyped hΓ (applyTyped hΓ (propMotiveTyped hΓ) ha) hp

def propMotiveBeta {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    ConvA env (iotaIfaceA env) 0 Γ (propMotiveAt a p) targetProp (.sort .zero) := by
  have hfirst : ConvA env (iotaIfaceA env) 0 Γ (.app propMotive a)
      (.lam (eqAt parameter a) .zero targetProp) (propMotiveTail a) :=
    .beta Γ (.sort .zero) one propMotiveBody a (propMotiveTail (.bvar 0)) (.sort Γ .zero)
      (tailLamTyped (.assumption hΓ (.sort Γ .zero)) propVar) ha (tailLamTyped hΓ ha)
  have hc : ConvA env (iotaIfaceA env) 0 Γ (propMotiveAt a p)
      (.app (.lam (eqAt parameter a) .zero targetProp) p) (.sort .zero) :=
    .app Γ (.app propMotive a) (.lam (eqAt parameter a) .zero targetProp) p p
      (eqAt parameter a) (.sort .zero) .zero one hfirst (.refl Γ p _ hp)
      (.sort _ .zero) (applyTyped hΓ (tailLamTyped hΓ ha) hp)
  exact .trans Γ _ _ _ _ hc
    (.beta Γ (eqAt parameter a) .zero targetProp p (.sort .zero)
      (eqTyped hΓ parameterTyped ha)
      (targetTyped (.assumption hΓ (eqTyped hΓ parameterTyped ha))) hp (targetTyped hΓ))

def propMotiveTypeConv {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {a p : ExprA} (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 Γ p (eqAt parameter a)) :
    TyConvA env (iotaIfaceA env) 0 Γ (propMotiveAt a p) targetProp :=
  .of Γ _ _ .zero .zero .zero (propMotiveAtTyped hΓ ha hp) (eqNA_refl _)
    (targetTyped hΓ) (eqNA_refl _) (propMotiveBeta hΓ ha hp)

theorem propRecConstTyped (Γ : LCtxA) : Nonempty
    (HasTyA env (iotaIfaceA env) 0 Γ (.const 65 [.zero])
      (instantiateLevelsA [.zero] recTy)) := by
  obtain ⟨w, ⟨hT⟩⟩ := recTyTypedNoIota
  have h0 := hasTyA_instLevels (envWfA_levels prefixWf) noIotaA_levels
    (n := 0) (ls := [.zero]) rfl rfl hT
  have h1 := hasTyA_env_iface prefix_in_env prefix_iface h0
  have h2 := hasTyClosedWeakenA closed liftIface
    (fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide)))
    (fun _ => rfl) Γ h1
  exact ⟨.const Γ 65 [.zero] recMember (instLevel [.zero] w) rfl rfl rfl h2⟩

abbrev propPre : List ExprA := [.sort .zero, parameter, propMotive, minor, domain]
abbrev propPrefix : ExprA := foldAppsA (.const 65 [.zero]) propPre
abbrev propCall (p : ExprA) : ExprA := .app propPrefix p
abbrev stuckCall : ExprA := propCall (.bvar 1)

theorem propPrefixTyped : Nonempty
    (HasTyA env (iotaIfaceA env) 0 proofContext propPrefix
      (.pi apartProp .zero (propMotiveAt domain (.bvar 0)) .zero)) := by
  obtain ⟨hr⟩ := propRecConstTyped proofContext
  have h0 := applyTyped proofContextWf hr (.sort proofContext .zero)
  have h1 := applyTyped proofContextWf h0 parameterTyped
  have h2 := applyTyped proofContextWf h1 (propMotiveTyped proofContextWf)
  have hm := hasTyA_of_tyConvA (minorTyped proofContextWf)
    (propMotiveTypeConv proofContextWf parameterTyped
      (reflTyped proofContextWf parameterTyped)).symm
  have h3 := applyTyped proofContextWf h2 hm
  exact ⟨applyTyped proofContextWf h3 (targetTyped proofContextWf)⟩

theorem callTyped : Nonempty
    (HasTyA env (iotaIfaceA env) 0 proofContext stuckCall targetProp) := by
  obtain ⟨hf⟩ := propPrefixTyped
  have hc := applyTyped proofContextWf hf majorTyped
  exact ⟨hasTyA_of_tyConvA hc
    (propMotiveTypeConv proofContextWf (targetTyped proofContextWf) majorTyped)⟩

theorem call_bridge_conversion : Nonempty
    (ConvA env (iotaIfaceA env) 0 proofContext stuckCall (.bvar 0) targetProp) := by
  obtain ⟨hc⟩ := callTyped
  exact ⟨.irr proofContext targetProp stuckCall (.bvar 0)
    (targetTyped proofContextWf) hc bridgeTyped⟩

def bridge_minor_conversion :
    ConvA env (iotaIfaceA env) 0 proofContext (.bvar 0) minor targetProp :=
  .irr proofContext targetProp (.bvar 0) minor
    (targetTyped proofContextWf) bridgeTyped (minorTyped proofContextWf)

theorem conversion : Nonempty
    (ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp) := by
  obtain ⟨h⟩ := call_bridge_conversion
  exact ⟨.trans proofContext _ _ _ _ h bridge_minor_conversion⟩

theorem callStuck : StuckA env (iotaIfaceA env) proofContext stuckCall := by
  have hn := neutKA_bvar closed liftIface
    (iotaConstHeadA_of_recHead (iotaFnA_recHead env))
    (Γ := proofContext) (i := 1) rfl
  exact neutKA_stuck (neutKA_recApp closed liftIface (r := 65) (m := recMember)
    rfl rfl (ls := [.zero]) (pre := propPre) (N := .bvar 1) rfl
    (.inl ⟨neutKA_stuckTm hn, by decide, by decide⟩))

/-- This is the same exact inhabited source PER as the existing boundary,
with the same observation proving that the two endpoints are unrelated. -/
theorem source_guard_false (ν : Valuation) (ρ : EnvI) :
    ¬ SortPER (some 0) (UnitModel.denote ν ρ parameter) (UnitModel.denote ν ρ domain) :=
  fun h => parameter_domain_separated ν ρ h.2.2

/-- A relation sound for this actual conversion cannot characterize its
call/minor equality by the separated source guard. The result values are
parameters, so this does not assume that every repair keeps old J images. -/
theorem no_exact_iff_of_conversion_sound (ν : Valuation) (ρ : EnvI)
    (R : Relation) (j c : Value)
    (sound : ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp → R j c) :
    ¬ (R j c ↔ SortPER (some 0)
      (UnitModel.denote ν ρ parameter) (UnitModel.denote ν ρ domain)) := by
  intro exactGuard
  obtain ⟨hc⟩ := conversion
  exact source_guard_false ν ρ (exactGuard.mp (sound hc))

theorem inhabited_source_exact_iff_obstruction :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 proofContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext parameter (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext domain (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 1) apartProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] minor targetProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 0) targetProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext stuckCall targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext stuckCall (.bvar 0) targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext (.bvar 0) minor targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp) ∧
    StuckA env (iotaIfaceA env) proofContext stuckCall ∧
    (∀ ν ρ, Member (SortPER (some 0)) (UnitModel.denote ν ρ parameter) ∧
      Member (SortPER (some 0)) (UnitModel.denote ν ρ domain)) ∧
    (∀ ν ρ, ¬ SortPER (some 0)
      (UnitModel.denote ν ρ parameter) (UnitModel.denote ν ρ domain)) :=
  ⟨wf, ⟨proofContextWf⟩, ⟨parameterTyped⟩, ⟨targetTyped proofContextWf⟩,
    ⟨majorTyped⟩, ⟨minorTyped .nil⟩, ⟨bridgeTyped⟩, callTyped,
    call_bridge_conversion, ⟨bridge_minor_conversion⟩, conversion, callStuck,
    endpoints_in_prop_universe, source_guard_false⟩

namespace ValueInterpretation

/-- Concrete neutral constants on the inherited finitary Value carrier. -/
def Neutral (x : Value) : Prop := ∃ r : Nat, NeutralPER.AtomNeutral r x

theorem neutral_atom (r : Nat) : Neutral (NeutralPER.neutralAtom r) :=
  ⟨r, NeutralPER.neutralAtom_is_neutral r⟩

def sourcePER : Relation := SortPER (some 0)

def leftValue (ν : Valuation) (ρ : EnvI) : Value :=
  UnitModel.denote ν ρ parameter

def rightValue (ν : Valuation) (ρ : EnvI) : Value :=
  UnitModel.denote ν ρ domain

def majorValue : Value := NeutralPER.neutralAtom 301
def callValue : Value := NeutralPER.neutralAtom 302
def bridgeValue : Value := NeutralPER.neutralAtom 303
def minorValue : Value := unitValue EnvI.bot

def majorPER (ν : Valuation) (ρ : EnvI) : Relation :=
  NeutralPER.EqPER Neutral sourcePER (leftValue ν ρ) (rightValue ν ρ)

/-- The constant target proposition is Eq parameter parameter. -/
def targetPER (ν : Valuation) (ρ : EnvI) : Relation :=
  NeutralPER.EqPER Neutral sourcePER (leftValue ν ρ) (leftValue ν ρ)

theorem source_laws : Laws sourcePER := sortPER_laws (some 0)

theorem left_member (ν : Valuation) (ρ : EnvI) :
    Member sourcePER (leftValue ν ρ) :=
  (endpoints_in_prop_universe ν ρ).1

theorem right_member (ν : Valuation) (ρ : EnvI) :
    Member sourcePER (rightValue ν ρ) :=
  (endpoints_in_prop_universe ν ρ).2

theorem endpoints_apart (ν : Valuation) (ρ : EnvI) :
    ¬ sourcePER (leftValue ν ρ) (rightValue ν ρ) :=
  source_guard_false ν ρ

theorem major_laws (ν : Valuation) (ρ : EnvI) : Laws (majorPER ν ρ) :=
  NeutralPER.eqPER_laws Neutral sourcePER (leftValue ν ρ) (rightValue ν ρ)

theorem target_laws (ν : Valuation) (ρ : EnvI) : Laws (targetPER ν ρ) :=
  NeutralPER.eqPER_laws Neutral sourcePER (leftValue ν ρ) (leftValue ν ρ)

/-- The false-guard equality carrier is inhabited by the actual neutral
constant, without deriving the endpoint relation or selecting a proof. -/
theorem major_member (ν : Valuation) (ρ : EnvI) : Member (majorPER ν ρ) majorValue :=
  NeutralPER.eqPER_neutral Neutral sourcePER (leftValue ν ρ) (rightValue ν ρ)
    (neutral_atom 301)

theorem minor_member (ν : Valuation) (ρ : EnvI) : Member (targetPER ν ρ) minorValue :=
  NeutralPER.eqPER_refl Neutral (left_member ν ρ)

theorem call_member (ν : Valuation) (ρ : EnvI) : Member (targetPER ν ρ) callValue :=
  NeutralPER.eqPER_neutral Neutral sourcePER (leftValue ν ρ) (leftValue ν ρ)
    (neutral_atom 302)

theorem bridge_member (ν : Valuation) (ρ : EnvI) : Member (targetPER ν ρ) bridgeValue :=
  NeutralPER.eqPER_neutral Neutral sourcePER (leftValue ν ρ) (leftValue ν ρ)
    (neutral_atom 303)

theorem call_bridge (ν : Valuation) (ρ : EnvI) :
    targetPER ν ρ callValue bridgeValue :=
  NeutralPER.proofPER_irrelevant (call_member ν ρ) (bridge_member ν ρ)

theorem bridge_minor (ν : Valuation) (ρ : EnvI) :
    targetPER ν ρ bridgeValue minorValue :=
  NeutralPER.proofPER_irrelevant (bridge_member ν ρ) (minor_member ν ρ)

theorem call_minor (ν : Valuation) (ρ : EnvI) :
    targetPER ν ρ callValue minorValue :=
  (target_laws ν ρ).trans (call_bridge ν ρ) (bridge_minor ν ρ)

/-- Proof PER equality does not erase the neutral's observations. -/
theorem call_not_minor : ¬ ValueEq callValue minorValue :=
  NeutralPER.neutralAtom_not_unit 302

theorem major_nonbottom : ¬ ValueEq majorValue bottom :=
  NeutralPER.neutralAtom_nonbottom 301

/-- An explicit local interpretation of the one displayed source
conversion. Irrelevance already supplies equality of these admitted proof
members. This is not a source image function or a global fundamental
theorem, and makes no claim about other syntax or conversion rules. -/
theorem single_conversion_sound (ν : Valuation) (ρ : EnvI) :
    ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp →
      targetPER ν ρ callValue minorValue :=
  fun _ => call_minor ν ρ

/-- The preceding conditional no-iff theorem now has a concrete supplied
soundness premise on Value; the unrelated equality carrier is inhabited. -/
theorem no_exact_iff (ν : Valuation) (ρ : EnvI) :
    ¬ (targetPER ν ρ callValue minorValue ↔
      sourcePER (leftValue ν ρ) (rightValue ν ρ)) :=
  no_exact_iff_of_conversion_sound ν ρ (targetPER ν ρ) callValue minorValue
    (single_conversion_sound ν ρ)

/-- Source admission/typing and every semantic carrier/member in the
obstruction are supplied together. The target relation is a lawful PER;
the failed condition is only its characterization by the source guard. -/
theorem inhabited_value_source_obstruction (ν : Valuation) (ρ : EnvI) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 proofContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext parameter (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext domain (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 1) apartProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] minor targetProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext (.bvar 0) targetProp) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofContext stuckCall targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext stuckCall (.bvar 0) targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext (.bvar 0) minor targetProp) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp) ∧
    StuckA env (iotaIfaceA env) proofContext stuckCall ∧
    Laws sourcePER ∧ Member sourcePER (leftValue ν ρ) ∧
    Member sourcePER (rightValue ν ρ) ∧
    (¬ sourcePER (leftValue ν ρ) (rightValue ν ρ)) ∧
    Laws (majorPER ν ρ) ∧ Member (majorPER ν ρ) majorValue ∧
    Laws (targetPER ν ρ) ∧ Member (targetPER ν ρ) minorValue ∧
    Member (targetPER ν ρ) callValue ∧ Member (targetPER ν ρ) bridgeValue ∧
    targetPER ν ρ callValue bridgeValue ∧ targetPER ν ρ bridgeValue minorValue ∧
    targetPER ν ρ callValue minorValue ∧
    (ConvA env (iotaIfaceA env) 0 proofContext stuckCall minor targetProp →
      targetPER ν ρ callValue minorValue) ∧
    (¬ ValueEq majorValue bottom) ∧ (¬ ValueEq callValue minorValue) ∧
    ¬ (targetPER ν ρ callValue minorValue ↔
      sourcePER (leftValue ν ρ) (rightValue ν ρ)) :=
  ⟨wf, ⟨proofContextWf⟩, ⟨parameterTyped⟩, ⟨targetTyped proofContextWf⟩,
    ⟨majorTyped⟩, ⟨minorTyped .nil⟩, ⟨bridgeTyped⟩, callTyped,
    call_bridge_conversion, ⟨bridge_minor_conversion⟩, conversion, callStuck,
    source_laws, left_member ν ρ, right_member ν ρ, endpoints_apart ν ρ,
    major_laws ν ρ, major_member ν ρ, target_laws ν ρ, minor_member ν ρ,
    call_member ν ρ, bridge_member ν ρ, call_bridge ν ρ, bridge_minor ν ρ,
    call_minor ν ρ, single_conversion_sound ν ρ, major_nonbottom,
    call_not_minor, no_exact_iff ν ρ⟩

end ValueInterpretation

#print axioms propMotiveBeta
#print axioms callTyped
#print axioms conversion
#print axioms callStuck
#print axioms no_exact_iff_of_conversion_sound
#print axioms inhabited_source_exact_iff_obstruction
#print axioms ValueInterpretation.single_conversion_sound
#print axioms ValueInterpretation.no_exact_iff
#print axioms ValueInterpretation.inhabited_value_source_obstruction

end Rcic.Declarative.Ann.LR3.NeutralKSource
