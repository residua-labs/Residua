import rcic.RcicAnnLR3RCodeSoundCoreSubstitution
import rcic.RcicAnnLR3IotaLiftLaw
import rcic.RcicAnnLRFundBind

/-!
# Kripke weakening of sound worlds and a uniform section from one fresh readback

**Weakening.** `push W T lT hT v` adds one assumption `T` to the source
context and the raw value `v` to the retained environment.
`RCodeSoundPi.extend` is literally this morphism at a domain member.
Admitted typing, conversion, typed neutrals and the actual evaluator
transport along it. The evaluator law is the inherited exact lifting law;
its environment hypotheses are collected in `Stable` and kept explicit.

**Monotonicity.** A sound instance weakens with its code unchanged.
Membership is therefore literally preserved, and every readback weakens to a
readback. Its fragments are the old ones together with the typed neutrals of
the new world. Those neutrals need actual reflections with exact images and
same-source coherence; this data is `PushReflection`. It is constructed for
every level-zero instance with a raw reflector. This covers all
`RCodeSoundZeroInstances` (propositions, native neutrals, guarded codes).

**Fresh variable.** In a pushed world the new variable is a typed source
neutral with its actual raw image. The eta body `(lift t) 0` of a Pi source
is typed at the codomain.

**Gluing.** A `KripkeFamily` has three parts: a generic domain member, one
uniform fragment index shared by every fibre (sources equal, transports
respected), and realization of the generic fibre by uniform fragments. A
`KripkeAction` is natural from the generic argument to every argument. Then
ONE existential elimination at the generic fibre gives a `Section` realizing
the action, so no pointwise choice is needed. If that one readback targets
the eta body of a Pi source `t`, the section's lambda converts to `t`.
Substitution coherence then follows: the raw part reuses
`Section.core_substitution`, and the source part is application congruence
plus beta. The lambda also weakens along `push` with an unchanged
evaluation. The PiControl family and its section action inhabit every
premise.

This is item 2 of the cc continuation. General Pi codes, universes and the
Fundamental theorem are not claimed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundKripke

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower RCodeSoundInterface RCodeSoundPi

universe u v w z q

/-! ## A. One-binder weakening of retained worlds -/

def push (W : World) (T : ExprA) (lT : Level)
    (hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT)) (val : Value) : World where
  env := W.env
  iota := W.iota
  levelCount := W.levelCount
  context := .assumption T :: W.context
  family := W.family
  valuation := W.valuation
  rawEnvironment := EnvI.cons val W.rawEnvironment
  envWf := W.envWf
  contextWf := .assumption W.contextWf hT

/-- Extension at a domain member is exactly the weakening morphism. -/
theorem extend_eq_push {W : World} {a : Nat} (A : RCodeSound.{u,v} W a)
    (x : Member A.code) :
    extend A x = push W A.sourceType A.sourceLevel A.typeTyped (A.code.erase x.val) := rfl

/-- The explicit structural hypotheses under which source typing and the
inherited evaluator both commute with lifting. -/
structure Stable (W : World) : Prop where
  envClosed : EnvClosedA W.env
  iotaLift : IotaLiftA W.iota
  bodies : EnvironmentPortConditions.DefinitionBodiesClosed W.env
  hook : EnvironmentPortConditions.HookLiftFixed W.env W.family

/-- The empty admitted environment satisfies every stability hypothesis. -/
theorem stable_empty (W : World) (henv : W.env = emptyEnvA)
    (hiota : W.iota = iotaIfaceA emptyEnvA) : Stable W := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [henv]; exact emptyEnvA_closed
  · rw [hiota]; exact iotaFnA_lift emptyEnvA_closed (fun _ _ h => Option.noConfusion h)
  · rw [henv]
    intro r ls b h
    exact Option.noConfusion h
  · rw [henv]
    intro _ r _ m h
    exact Option.noConfusion h

section Weakening

variable {W : World} {T : ExprA} {lT : Level}
variable {hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT)} {val : Value}

theorem push_evaluate_lift (hs : Stable W) (e : ExprA) :
    (push W T lT hT val).evaluate (liftA 0 1 e) = W.evaluate e := by
  have h := IotaRecursor.denote_lift (ν := W.valuation) hs.bodies hs.hook
    W.rawEnvironment 0 val e
  rw [EnvI.insert_zero] at h
  exact h

def weakenTyped (hs : Stable W) {e S : ExprA}
    (h : HasTyA W.env W.iota W.levelCount W.context e S) :
    HasTyA W.env W.iota W.levelCount (.assumption T :: W.context) (liftA 0 1 e) (liftA 0 1 S) :=
  hasTyWeakenA hs.envClosed hs.iotaLift (.assumption T) (c := 0) (Nat.zero_le _) h

def weakenConv (hs : Stable W) {a b S : ExprA}
    (h : ConvA W.env W.iota W.levelCount W.context a b S) :
    ConvA W.env W.iota W.levelCount (.assumption T :: W.context)
      (liftA 0 1 a) (liftA 0 1 b) (liftA 0 1 S) :=
  convWeakenA hs.envClosed hs.iotaLift (.assumption T) (c := 0) (Nat.zero_le _) h

def weakenSource (hs : Stable W) {S : ExprA} (s : Source W S) :
    Source (push W T lT hT val) (liftA 0 1 S) :=
  ⟨liftA 0 1 s.term, weakenTyped hs s.typed⟩

/-- A typed neutral keeps its raw value; its image is the lifting law. -/
def weakenNeutral (hs : Stable W) {S : ExprA} (n : Neutral W S) :
    Neutral (push W T lT hT val) (liftA 0 1 S) where
  term := liftA 0 1 n.term
  typed := weakenTyped hs n.typed
  value := n.value
  image := by
    rw [push_evaluate_lift hs]
    exact n.image
  neutral := n.neutral

theorem weakenNeutral_source (hs : Stable W) {S : ExprA} (n : Neutral W S) :
    (weakenNeutral (T := T) (lT := lT) (hT := hT) (val := val) hs n).toSource =
      weakenSource hs n.toSource := rfl

end Weakening

theorem liftA_one_injective {a b : ExprA} (h : liftA 0 1 a = liftA 0 1 b) : a = b := by
  have h' := congrArg (instantiateA 0 (.bvar 0)) h
  rwa [instantiateA_liftA_id, instantiateA_liftA_id] at h'

/-! ## B. Monotonicity of sound instances along weakening -/

/-- Actual reflections of the new world's typed neutrals, with exact images
and same-source coherence against the old fragments. -/
structure PushReflection {W : World} {k : Nat} (hs : Stable W) (C : RCodeSound.{u,v} W k)
    (T : ExprA) (lT : Level) (hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT))
    (val : Value) where
  reflect : Neutral (push W T lT hT val) (liftA 0 1 C.sourceType) → Member C.code
  source : Neutral (push W T lT hT val) (liftA 0 1 C.sourceType) →
    Source (push W T lT hT val) (liftA 0 1 C.sourceType)
  conv : ∀ n, Nonempty (ConvA W.env W.iota W.levelCount (.assumption T :: W.context)
    (source n).term n.term (liftA 0 1 C.sourceType))
  image : ∀ n, ValueEq (C.code.erase (reflect n).val)
    ((push W T lT hT val).evaluate (source n).term)
  coherent_old : ∀ s n, liftA 0 1 (C.source s).term = (source n).term →
    Related (C.evalSem s) (reflect n)
  coherent_new : ∀ n m, (source n).term = (source m).term → Related (reflect n) (reflect m)

section Monotone

variable {W : World} {k : Nat} {hs : Stable W} {C : RCodeSound.{u,v} W k}
variable {T : ExprA} {lT : Level}
variable {hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT)} {val : Value}

/-- The same code over the pushed world. -/
def weakenSound (R : PushReflection hs C T lT hT val) :
    RCodeSound.{u,v} (push W T lT hT val) k where
  code := C.code
  sourceType := liftA 0 1 C.sourceType
  sourceLevel := C.sourceLevel
  typeTyped := weakenTyped hs C.typeTyped
  level := C.level
  typeImage := by
    rw [push_evaluate_lift hs]
    exact C.typeImage
  Fragment := C.Fragment ⊕ Neutral (push W T lT hT val) (liftA 0 1 C.sourceType)
  source := fun s => match s with
    | .inl s => weakenSource hs (C.source s)
    | .inr n => R.source n
  evalSem := fun s => match s with
    | .inl s => C.evalSem s
    | .inr n => R.reflect n
  erasure := fun s => match s with
    | .inl s => by
        show ValueEq _ ((push W T lT hT val).evaluate (liftA 0 1 (C.source s).term))
        rw [push_evaluate_lift hs]
        exact C.erasure s
    | .inr n => R.image n
  source_coherence := fun s t h => match s, t with
    | .inl s, .inl t => C.source_coherence s t (liftA_one_injective h)
    | .inl s, .inr n => R.coherent_old s n h
    | .inr n, .inl s => related_symm (R.coherent_old s n h.symm)
    | .inr n, .inr m => R.coherent_new n m h
  realization := fun x => by
    obtain ⟨s, hs⟩ := C.realization x
    exact ⟨.inl s, hs⟩
  reflect := R.reflect
  reflection_source := fun n => ⟨.inr n, related_refl _, R.conv n⟩

/-- Membership is literally preserved: the code is unchanged. -/
theorem weakenSound_code (R : PushReflection hs C T lT hT val) :
    (weakenSound R).code = C.code := rfl

/-- Every readback weakens to a readback of the weakened source. -/
theorem weakenSound_readsBack (R : PushReflection hs C T lT hT val)
    {s : C.Fragment} {x : C.Element} {t : Source W C.sourceType}
    (h : C.ReadsBack s x t) :
    (weakenSound R).ReadsBack (.inl s) x (weakenSource hs t) := by
  obtain ⟨hc⟩ := h.2
  exact ⟨h.1, ⟨weakenConv hs hc⟩⟩

/-- Old neutrals are reflected in the weakened instance with a readback. -/
theorem weakenSound_neutral_readback (R : PushReflection hs C T lT hT val)
    (n : Neutral W C.sourceType) :
    ∃ s, (weakenSound R).ReadsBack s ((weakenSound R).reflect (weakenNeutral hs n))
      (weakenNeutral hs n).toSource :=
  (weakenSound R).reflected_readback (weakenNeutral hs n)

end Monotone

/-- Every level-zero instance with a raw reflector weakens. Coherence is
level-zero irrelevance; images are the reflector's exact image law. -/
def zeroReflection {W : World} (hs : Stable W) (C : RCodeSound.{u,v} W 0)
    (r : GuardedKernel.Reflector C.code.kernel)
    (T : ExprA) (lT : Level) (hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT))
    (val : Value) : PushReflection hs C T lT hT val where
  reflect := fun n => ⟨r.reflect n.value n.neutral, r.member n.value n.neutral⟩
  source := fun n => n.toSource
  conv := fun n => ⟨.refl _ n.term _ n.typed⟩
  image := fun n => (r.image n.value n.neutral).trans n.image.symm
  coherent_old := fun s _ _ => C.code.view.irrelevant rfl _ _ (C.evalSem s).property
    (r.member _ _)
  coherent_new := fun _ _ _ => C.code.view.irrelevant rfl _ _ (r.member _ _) (r.member _ _)

/-! ## C. The fresh variable and the eta body -/

/-- The newly bound variable is an actual typed source neutral. -/
def freshNeutral {W : World} (T : ExprA) (lT : Level)
    (hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT))
    (hs : Stable W) (val : Value) (hv : CandidatePi.Neutral val) :
    Neutral (push W T lT hT val) (liftA 0 1 T) where
  term := .bvar 0
  typed := .bvar _ 0 (liftA 0 1 T) lT rfl (weakenTyped hs hT)
  value := val
  image := RCodeProofReadback.environment_variable_image W.env W.family W.valuation
    (EnvI.cons val W.rawEnvironment) 0 (RCodeSoundPiControl.neutral_bot hv)
  neutral := hv

abbrev etaBody (t : ExprA) : ExprA := .app (liftA 0 1 t) (.bvar 0)

/-! ## D. Kripke families, natural actions, and one fresh readback -/

section Gluing

variable {W : World} {a b : Nat} {A : RCodeSound.{u,v} W a}
variable {B : ExprA} {lB : Level}

/-- A generic argument and one fragment index shared by all fibres. The
generic fibre is realized by these uniform fragments. -/
structure KripkeFamily (D : Family.{u,v,w,z} A b B lB) where
  generic : Member A.code
  generic_fresh : CandidatePi.Neutral (A.code.erase generic.val)
  Uniform : Type q
  fragment : (x : Member A.code) → Uniform → (D.fibre x).Fragment
  source_uniform : ∀ x i, ((D.fibre x).source (fragment x i)).term =
    ((D.fibre generic).source (fragment generic i)).term
  respect : ∀ x y (h : Related x y) i,
    (D.fibre y).code.view.relation
      ((D.transport x y h).forward ((D.fibre x).evalSem (fragment x i)).val)
      ((D.fibre y).evalSem (fragment y i)).val
  generic_realization : ∀ m : Member (D.fibre generic).code,
    ∃ i, Related m ((D.fibre generic).evalSem (fragment generic i))

/-- A dependent action whose relation to a uniform fragment at the generic
argument holds at every argument. -/
structure KripkeAction {D : Family.{u,v,w,z} A b B lB} (K : KripkeFamily.{u,v,w,z,q} D) where
  action : RCodeDependentPi.Action A.code.kernel D.kernels D.transports
  natural : ∀ i,
    (D.fibre K.generic).code.view.relation (action.run K.generic).val
      ((D.fibre K.generic).evalSem (K.fragment K.generic i)).val →
    ∀ x, (D.fibre x).code.view.relation (action.run x).val
      ((D.fibre x).evalSem (K.fragment x i)).val

/-- In the generic fibre's world the bound variable is the fresh source
neutral, with the generic argument's actual raw image. -/
def KripkeFamily.freshVariable {D : Family.{u,v,w,z} A b B lB}
    (K : KripkeFamily.{u,v,w,z,q} D) (hs : Stable W) :
    Neutral (extend A K.generic) (liftA 0 1 A.sourceType) :=
  freshNeutral A.sourceType A.sourceLevel A.typeTyped hs (A.code.erase K.generic.val)
    K.generic_fresh

/-- The section determined by one uniform fragment index. -/
def KripkeFamily.sectionAt {D : Family.{u,v,w,z} A b B lB}
    (K : KripkeFamily.{u,v,w,z,q} D) (i : K.Uniform) : Section D where
  body := ((D.fibre K.generic).source (K.fragment K.generic i)).term
  fragment := fun x => K.fragment x i
  source_eq := fun x => K.source_uniform x i
  respect := fun x y h => K.respect x y h i

theorem KripkeFamily.sectionAt_run {D : Family.{u,v,w,z} A b B lB}
    (K : KripkeFamily.{u,v,w,z,q} D) (i : K.Uniform) (x : Member A.code) :
    ((K.sectionAt i).action.run x) = (D.fibre x).evalSem (K.fragment x i) := rfl

/-- ONE realization at the generic fibre gives a uniform section realizing
the whole action. Only that single existential is eliminated, inside Prop. -/
theorem KripkeAction.uniform_section {D : Family.{u,v,w,z} A b B lB}
    {K : KripkeFamily.{u,v,w,z,q} D} (f : KripkeAction K) :
    ∃ i : K.Uniform, RCodeDependentPi.ActionRel f.action (K.sectionAt i).action := by
  obtain ⟨i, hi⟩ := K.generic_realization (f.action.run K.generic)
  exact ⟨i, fun x => f.natural i hi x⟩

theorem KripkeAction.section_exists {D : Family.{u,v,w,z} A b B lB}
    {K : KripkeFamily.{u,v,w,z,q} D} (f : KripkeAction K) :
    ∃ σ : Section D, RCodeDependentPi.ActionRel f.action σ.action := by
  obtain ⟨i, hi⟩ := f.uniform_section
  exact ⟨K.sectionAt i, hi⟩

/-- The eta body of a Pi source is typed at the codomain in the extended
context, which is the context of every fibre. -/
def etaBodyTyped (hs : Stable W) (D : Family.{u,v,w,z} A b B lB)
    (t : Source W (.pi A.sourceType A.sourceLevel B lB)) :
    HasTyA W.env W.iota W.levelCount (.assumption A.sourceType :: W.context)
      (etaBody t.term) B :=
  hasTyA_eta_body hs.envClosed hs.iotaLift A.typeTyped D.codomainTyped t.typed

/-- One fresh readback (semantic relation plus source conversion to the eta
body of `t`) in the generic fibre at a uniform fragment yields a section realizing the action whose lambda
converts to `t`. -/
theorem KripkeAction.readback {D : Family.{u,v,w,z} A b B lB}
    {K : KripkeFamily.{u,v,w,z,q} D} (hs : Stable W) (f : KripkeAction K)
    (t : Source W (.pi A.sourceType A.sourceLevel B lB))
    (hfresh : ∃ i, (D.fibre K.generic).code.view.relation (f.action.run K.generic).val
        ((D.fibre K.generic).evalSem (K.fragment K.generic i)).val ∧
      Nonempty (ConvA W.env W.iota W.levelCount (.assumption A.sourceType :: W.context)
        ((D.fibre K.generic).source (K.fragment K.generic i)).term (etaBody t.term) B)) :
    ∃ σ : Section D, RCodeDependentPi.ActionRel f.action σ.action ∧
      Nonempty (ConvA W.env W.iota W.levelCount W.context
        (.lam A.sourceType A.sourceLevel σ.body) t.term
        (.pi A.sourceType A.sourceLevel B lB)) := by
  obtain ⟨i, hrel, hconv⟩ := hfresh
  refine ⟨K.sectionAt i, fun x => f.natural i hrel x, ?_⟩
  obtain ⟨hc'⟩ := hconv
  have hlamEta : HasTyA W.env W.iota W.levelCount W.context
      (.lam A.sourceType A.sourceLevel (etaBody t.term))
      (.pi A.sourceType A.sourceLevel B lB) :=
    .lam _ _ _ _ _ _ A.typeTyped D.codomainTyped (etaBodyTyped hs D t)
  have hlam : ConvA W.env W.iota W.levelCount W.context
      (.lam A.sourceType A.sourceLevel (K.sectionAt i).body)
      (.lam A.sourceType A.sourceLevel (etaBody t.term))
      (.pi A.sourceType A.sourceLevel B lB) :=
    .lam _ _ _ _ _ _ _ _ _ (fun _ => rfl) (.refl _ _ _ A.typeTyped) hc' hlamEta
  have heta : ConvA W.env W.iota W.levelCount W.context
      (.lam A.sourceType A.sourceLevel (etaBody t.term)) t.term
      (.pi A.sourceType A.sourceLevel B lB) :=
    .eta _ _ _ _ _ _ t.typed hlamEta
  exact ⟨.trans _ _ _ _ _ hlam heta⟩

/-- Substitution coherence at the source: applying `t` to an actual domain
source converts to the substituted uniform body. -/
theorem Section.app_substitution_conv {D : Family.{u,v,w,z} A b B lB}
    (σ : Section D) (hs : Stable W)
    (hR : IotaRecHeadTypedA W.env W.iota) (hIS : IotaSubstA W.iota)
    (t : Source W (.pi A.sourceType A.sourceLevel B lB))
    (ht : Nonempty (ConvA W.env W.iota W.levelCount W.context
      (.lam A.sourceType A.sourceLevel σ.body) t.term
      (.pi A.sourceType A.sourceLevel B lB)))
    (arg : A.Fragment) :
    Nonempty (ConvA W.env W.iota W.levelCount W.context
      (.app t.term (A.source arg).term) (instantiate0A (A.source arg).term σ.body)
      (instantiate0A (A.source arg).term B)) := by
  obtain ⟨ht⟩ := ht
  have hred := σ.substitutionTyped arg hs.envClosed hs.iotaLift hR hIS
  have hBsub : HasTyA W.env W.iota W.levelCount W.context
      (instantiate0A (A.source arg).term B) (.sort lB) :=
    hasTyA_inst0 hs.envClosed hs.iotaLift hR hIS W.contextWf D.codomainTyped
      (A.source arg).typed A.typeTyped
  have happ : HasTyA W.env W.iota W.levelCount W.context
      (.app (.lam A.sourceType A.sourceLevel σ.body) (A.source arg).term)
      (instantiate0A (A.source arg).term B) :=
    .app _ _ _ _ _ _ _ _ D.codomainTyped hBsub σ.lambdaTyped (A.source arg).typed
  have hcong : ConvA W.env W.iota W.levelCount W.context
      (.app t.term (A.source arg).term)
      (.app (.lam A.sourceType A.sourceLevel σ.body) (A.source arg).term)
      (instantiate0A (A.source arg).term B) :=
    .app _ _ _ _ _ _ _ _ _ (.symm _ _ _ _ ht) (.refl _ _ _ (A.source arg).typed)
      D.codomainTyped happ
  have hbeta : ConvA W.env W.iota W.levelCount W.context
      (.app (.lam A.sourceType A.sourceLevel σ.body) (A.source arg).term)
      (instantiate0A (A.source arg).term σ.body) (instantiate0A (A.source arg).term B) :=
    .beta _ _ _ _ _ _ A.typeTyped σ.bodyTyped (A.source arg).typed hred
  exact ⟨.trans _ _ _ _ _ hcong hbeta⟩

/-- Weakening coherence: the section's lambda weakens to a typed lambda in
any pushed world with an unchanged evaluation. -/
theorem Section.weaken_lambda {D : Family.{u,v,w,z} A b B lB} (σ : Section D)
    (hs : Stable W) (T : ExprA) (lT : Level)
    (hT : HasTyA W.env W.iota W.levelCount W.context T (.sort lT)) (val : Value) :
    Nonempty (HasTyA W.env W.iota W.levelCount (.assumption T :: W.context)
      (liftA 0 1 (.lam A.sourceType A.sourceLevel σ.body))
      (liftA 0 1 (.pi A.sourceType A.sourceLevel B lB))) ∧
    (push W T lT hT val).evaluate (liftA 0 1 (.lam A.sourceType A.sourceLevel σ.body)) =
      W.evaluate (.lam A.sourceType A.sourceLevel σ.body) :=
  ⟨⟨weakenTyped hs σ.lambdaTyped⟩, push_evaluate_lift hs _⟩

end Gluing

/-! ## E. The PiControl family is a Kripke family with a natural action -/

section Control

open RCodeSoundPiControl

def controlKripke (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    KripkeFamily.{0,0,0,0,0} (family F ν name) where
  generic := (domain F ν name).point 0
  generic_fresh := .atom 0
  Uniform := PUnit
  fragment := fun _ _ => .basepoint
  source_uniform := fun _ _ => rfl
  respect := fun _ _ h _ => h
  generic_realization := fun m =>
    ⟨⟨⟩, (domain F ν name).code.view.irrelevant rfl _ _ m.property
      ((fibre F ν name ((domain F ν name).point 0)).evalSem .basepoint).property⟩

def controlAction (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    KripkeAction (controlKripke F ν name) where
  action := (uniformSection F ν name).action
  natural := fun _ _ x => ((uniformSection F ν name).action.run x).property

/-- All gluing premises are constructed for the control family. -/
theorem control_uniform_section (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) :
    ∃ σ : Section (family F ν name),
      RCodeDependentPi.ActionRel (controlAction F ν name).action σ.action :=
  (controlAction F ν name).section_exists

theorem control_stable (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    Stable (RCodeSoundZeroInstances.world F ν
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))) :=
  stable_empty _ rfl rfl

/-- The generic argument of the control family is the fresh variable of its
generic fibre world, with its actual typed source and raw image. -/
def controlFresh (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    Neutral (extend (domain F ν name) (controlKripke F ν name).generic)
      (liftA 0 1 (domain F ν name).sourceType) :=
  (controlKripke F ν name).freshVariable (control_stable F ν name)

/-- A constructed monotone instance: the native neutral zero instance weakened
along the push by its own type, with a fresh raw atom. -/
def controlWeakened (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    RCodeSound.{0,0} (push _ (domain F ν name).sourceType (domain F ν name).sourceLevel
      (domain F ν name).typeTyped (NeutralPER.neutralAtom 7)) 0 :=
  weakenSound (zeroReflection (control_stable F ν name) (domain F ν name)
    (GuardedKernel.nativeNeutralReflector.{0} 0 name) _ _ _ _)

theorem controlWeakened_packet (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (s : (domain F ν name).Fragment) :
    (controlWeakened F ν name).code = (domain F ν name).code ∧
    (controlWeakened F ν name).ReadsBack (.inl s) ((domain F ν name).evalSem s)
      (weakenSource (control_stable F ν name) ((domain F ν name).source s)) :=
  ⟨rfl, weakenSound_readsBack _ ((domain F ν name).readback_total s)⟩

end Control

end Rcic.Declarative.Ann.LR3.RCodeSoundKripke
