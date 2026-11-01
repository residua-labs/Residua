import rcic.RcicF3ReaderSupport
import rcic.RcicF3RecFieldMaskLambdaAttack

/-!
# An ignored identity capture at the actual W reader

The typed source applies a lambda to the identity on the actual DATA
family. Its body ignores that capture and returns the original PendA W
field type. The reader emits exactly that field's clean parameter domain.
The support producer proves that the unclean identity capture is unused.

The two actual beta-body contexts fit, using the source and enlarged
identity graphs respectively. No SINGLE value can fill that capture in
both contexts: a common graph would identify the strict family domains.
This refutes only a proposed same-capture provenance invariant, not the
reader, masking, admission or the A premise. The read domain nevertheless
agrees by the new support theorem, and the earlier real W witnesses stay
in the literal conjunction. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderSupportAttack
open Rcic.Declarative RawFamily PiIndex
open NormFreshHeadAttack (base C D model parameter σ admissible_C admissible_D prefix_sound)
open RecFieldConsumerAttack (parameterΓ)
open PendAWBridge (fd)

def ρ : Nat → PSet.{4} := vcons parameter ρ0
def family : Expr Nat := .app (.const 4 []) (.bvar 0)
def familyLift : Expr Nat := .app (.const 4 []) (.bvar 1)
def level : Level := .imax (.succ .zero) (.succ .zero)
def captureType : Expr Nat := .pi family familyLift
def identity : Expr Nat := .lam family (.bvar 0)
def preDomain : Expr Nat := .bvar 1
def body : Expr Nat := .pi preDomain (.app (.const 4 []) (.bvar 2))
def source : Expr Nat := .app (.lam captureType body) identity

noncomputable def family_typed : HasTyT PendAW.eFam 0 parameterΓ family
    (.sort (.succ .zero)) :=
  .app parameterΓ (.const 4 []) (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 0 _ rfl)

noncomputable def capture_typed : HasTyT PendAW.eFam 0 parameterΓ captureType (.sort level) :=
  .pi parameterΓ family (.succ .zero) familyLift (.succ .zero) family_typed
    (.app _ (.const 4 []) (.bvar 1) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 1 _ rfl))

noncomputable def identity_typed : HasTyT PendAW.eFam 0 parameterΓ identity captureType :=
  .lam parameterΓ family (.succ .zero) (.bvar 0) familyLift
    family_typed (.bvar _ 0 _ rfl)

noncomputable def body_typed : HasTyT PendAW.eFam 0
    (.assumption captureType :: parameterΓ) body (.sort level) :=
  .pi _ preDomain (.succ .zero) (.app (.const 4 []) (.bvar 2)) (.succ .zero)
    (.bvar _ 1 _ rfl)
    (.app _ (.const 4 []) (.bvar 2) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 2 _ rfl))

noncomputable def source_typed : HasTyT PendAW.eFam 0 parameterΓ source (.sort level) :=
  .app parameterΓ (.lam captureType body) identity captureType (.sort level)
    (.lam parameterΓ captureType level body (.sort level) capture_typed body_typed)
    identity_typed

private theorem family_bound (τ K : Nat → Nat) : LOKt τ 4 K family_typed :=
  ⟨fun _ h => (List.not_mem_nil _ h).elim, True.intro⟩

theorem identity_bound (τ K : Nat → Nat) : LOKt τ 4 K identity_typed :=
  ⟨family_bound τ K, True.intro⟩

theorem source_bound (τ K : Nat → Nat) : LOKt τ 4 K source_typed :=
  ⟨⟨⟨by change 1 ≤ 4; decide, by change 1 ≤ 4; decide,
      family_bound τ K, (fun _ h => (List.not_mem_nil _ h).elim), True.intro⟩,
    ⟨by change 1 ≤ 4; decide, by change 1 ≤ 4; decide, True.intro,
      (fun _ h => (List.not_mem_nil _ h).elim), True.intro⟩⟩,
    identity_bound τ K⟩

theorem whnf_reader : whnfFuel PendAW.eFam 16 source = some PendAW.field := rfl
theorem telescope_reader : piTelescopeFuel PendAW.eFam 16 source =
    some ([.bvar 0], .app (.const 4 []) (.bvar 1)) := rfl

/-- The actual capture is not clean, but the source domain does not read
it. This result is obtained from the simultaneous substitution producer. -/
theorem ignored_capture : occursConst 4 identity = true ∧
    occursConst 4 (instantiate0 identity preDomain) = false ∧
    freeBvarRef 0 0 preDomain = false := by
  refine ⟨rfl, rfl, ?_⟩
  exact ReaderSupport.unused_unclean_capture 4 preDomain
    (SubstT.single 0 identity) rfl 0 rfl

noncomputable def value (P : Premises4) (X : Frame) : PSet.{4} :=
  den (model P X) σ ρ identity
noncomputable def familyValue (P : Premises4) (X : Frame) : PSet.{4} :=
  den (model P X) σ ρ family

theorem parameter_fits (P : Premises4) :
    Fits (model P (C P)) σ parameterΓ ρ ∧ Fits (model P (D P)) σ parameterΓ ρ :=
  PiGraphInversionAttack.parameter_fits P

/-- The existing actual beta producer pays the two original body fits.
Their captured values are separately evaluated in the two family models. -/
theorem two_body_contexts (P : Premises4) (K : Nat → Nat) :
    Fits (model P (C P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (C P)) ρ) ∧
    Fits (model P (D P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (D P)) ρ) := by
  obtain ⟨u, B, dA, db, hA, hb, hC, hD⟩ :=
    BoundedBetaOrigin.paired_of_type P
      (table P (base P) fd (C P)) (table P (base P) fd (D P)) σ K
      source_typed (source_bound σ K)
      (prefix_sound P (C P) (admissible_C P) σ K 0)
      (prefix_sound P (D P) (admissible_D P) σ K 0)
      ρ ρ (parameter_fits P).1 (parameter_fits P).2
  exact ⟨hC.fits, hD.fits⟩

private theorem family_read (P : Premises4) (X : Frame) (hX : Admissible fd X) :
    Equiv (Ed (model P X) (familyValue P X)) (X [] (key [parameter])) :=
  RawFamilyEnlarge.application_read P (base P) fd X hX 0 σ ρ [.bvar 0]
    (by intro e he; cases List.mem_singleton.mp he; rfl)
    (PendAWBridge.argsFit P (base P) pempty)

private theorem omega_mem (P : Premises4) (X : Frame) (hX : Admissible fd X)
    (hx : fxZW P ∈ X [] (key [parameter])) :
    fxZW P ∈ Ed (model P X) (familyValue P X) :=
  mem_congr_right (family_read P X hX).symm hx

private theorem ed_table (P : Premises4) (μ ν : Nat → List Nat → PSet.{4})
    (t : PSet.{4}) : Ed (mkM P μ) t = Ed (mkM P ν) t := rfl

private theorem pi_table (P : Premises4) (μ ν : Nat → List Nat → PSet.{4})
    (A : PSet.{4}) (B : PSet.{4} → PSet.{4}) :
    piVal (mkM P μ) A B = piVal (mkM P ν) A B := rfl

/-- Both capture types are actual graph types. A shared graph would make
the strict source/enlarged family domains equal, which is impossible. -/
theorem no_common_capture (P : Premises4) (g : PSet.{4})
    (hc : g ∈ Ed (model P (C P)) (den (model P (C P)) σ ρ captureType))
    (hd : g ∈ Ed (model P (D P)) (den (model P (D P)) σ ρ captureType)) : False := by
  let M := mkM P (base P)
  let A := familyValue P (C P)
  let A' := familyValue P (D P)
  change g ∈ Ed (model P (C P)) (piVal (model P (C P)) A (fun _ => A)) at hc
  change g ∈ Ed (model P (D P)) (piVal (model P (D P)) A' (fun _ => A')) at hd
  rw [pi_table P (table P (base P) fd (C P)) (base P),
    ed_table P (table P (base P) fd (C P)) (base P)] at hc
  rw [pi_table P (table P (base P) fd (D P)) (base P),
    ed_table P (table P (base P) fd (D P)) (base P)] at hd
  have hω := omega_mem P (C P) (admissible_C P) (NormFreshHeadAttack.omega_C P)
  have hω' := omega_mem P (D P) (admissible_D P) (NormFreshHeadAttack.omega_D P)
  rw [ed_table P (table P (base P) fd (C P)) (base P)] at hω
  rw [ed_table P (table P (base P) fd (D P)) (base P)] at hω'
  have hne : ¬ Equiv (fxZW P) pempty := by
    have hface := (admissible_C P [] (key [parameter])).2
    change ∀ z, z ∈ C P [] (key [parameter]) → ¬ Equiv z pempty at hface
    exact hface _ (NormFreshHeadAttack.omega_C P)
  have hp : ¬ PiProp M A (fun _ => A) := fun hp => hne (hp _ hω _ hω)
  have hp' : ¬ PiProp M A' (fun _ => A') := fun hp => hne (hp _ hω' _ hω')
  have eC := ed_piVal M A (fun _ => A) (fun _ _ _ => Equiv.rfl)
  have eD := ed_piVal M A' (fun _ => A') (fun _ _ _ => Equiv.rfl)
  rw [cond_neg hp] at eC
  rw [cond_neg hp'] at eD
  have hgC : g ∈ piSet (Ed M A) (fun _ => Ed M A) := mem_congr_right eC hc
  have hgD : g ∈ piSet (Ed M A') (fun _ => Ed M A') := mem_congr_right eD hd
  have he : Equiv (Ed M A) (Ed M A') := ext fun x =>
    ⟨fun hx => piSet_dom (B := fun _ => Ed M A') (B' := fun _ => Ed M A)
        (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) hgD hgC hx,
      fun hx => piSet_dom (B := fun _ => Ed M A) (B' := fun _ => Ed M A')
        (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) hgC hgD hx⟩
  have rC := family_read P (C P) (admissible_C P)
  have rD := family_read P (D P) (admissible_D P)
  rw [ed_table P (table P (base P) fd (C P)) (base P)] at rC
  rw [ed_table P (table P (base P) fd (D P)) (base P)] at rD
  exact NormFreshHeadAttack.strict_all P [] (key [parameter])
    (rC.symm.trans (he.trans rD))

theorem no_common_body_context (P : Premises4) (g : PSet.{4}) :
    ¬ (Fits (model P (C P)) σ (.assumption captureType :: parameterΓ) (vcons g ρ) ∧
      Fits (model P (D P)) σ (.assumption captureType :: parameterΓ) (vcons g ρ)) :=
  fun h => no_common_capture P g h.1.2 h.2.2

theorem capture_values_differ (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (value P (C P)) (value P (D P)) := by
  intro he
  have h := two_body_contexts P K
  exact no_common_capture P (value P (C P)) h.1.2
    (mem_congr_left he.symm h.2.2)

/-- The clean emitted domain still agrees. The generic theorem derives
agreement from read support, without equating the unused identity captures. -/
theorem domain_agrees (P : Premises4) :
    Equiv (den (model P (C P)) σ (vcons (value P (C P)) ρ) preDomain)
      (den (model P (D P)) σ (vcons (value P (D P)) ρ) preDomain) :=
  ReaderSupport.captured_models_agree P (base P) 4
    (ofFrame P (base P) fd (C P)) (ofFrame P (base P) fd (D P)) σ
    preDomain (SubstT.single 0 identity) rfl ρ

def Witness (P : Premises4) : Prop :=
  RecFieldMaskLambdaAttack.Witness P ∧
  Nonempty (HasTyT PendAW.eFam 0 parameterΓ source (.sort level)) ∧
  whnfFuel PendAW.eFam 16 source = some PendAW.field ∧
  piTelescopeFuel PendAW.eFam 16 source =
    some ([.bvar 0], .app (.const 4 []) (.bvar 1)) ∧
  occursConst 4 identity = true ∧
  occursConst 4 (instantiate0 identity preDomain) = false ∧
  freeBvarRef 0 0 preDomain = false ∧
  (∀ K, LOKt σ 4 K source_typed ∧
    Fits (model P (C P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (C P)) ρ) ∧
    Fits (model P (D P)) σ (.assumption captureType :: parameterΓ)
      (vcons (value P (D P)) ρ) ∧
    ¬ Equiv (value P (C P)) (value P (D P))) ∧
  (∀ g, ¬ (Fits (model P (C P)) σ (.assumption captureType :: parameterΓ) (vcons g ρ) ∧
    Fits (model P (D P)) σ (.assumption captureType :: parameterΓ) (vcons g ρ))) ∧
  Equiv (den (model P (C P)) σ (vcons (value P (C P)) ρ) preDomain)
    (den (model P (D P)) σ (vcons (value P (D P)) ρ) preDomain)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldMaskLambdaAttack.component_witness P, ⟨source_typed⟩,
    whnf_reader, telescope_reader, ignored_capture.1, ignored_capture.2.1,
    ignored_capture.2.2,
    fun K => ⟨source_bound σ K, (two_body_contexts P K).1,
      (two_body_contexts P K).2, capture_values_differ P K⟩,
    no_common_body_context P, domain_agrees P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.ReaderSupportAttack
