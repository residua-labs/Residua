import rcic.RcicAnnLR3UnifiedPi

/-!
# Finite demand of reflected neutral, proof, and universe code families

Every descriptor in the current NeutralCodes grammar has a mandatory
finite observation. Sharing that observation forces equality of the
reflected value. Thus finite demand of a code-valued family supplies
finite demand of its reflected family; reflected finite demand is no
longer a separate premise for this fragment.

The canonical version uses `NeutralCodes.reflect (V x) name` directly.
Code presentations are unpacked only inside proofs of Prop-valued finite
demands. No descriptor or element relation is selected from Prop to
define a value operation. Native code bodies supply the initial finite
demand by the inherited approximation-factorization theorem.

The resulting graph applies exactly to the reflected codomain value at
every legal argument. Its membership theorem uses the actual codomain
code relations and their coherence, with no `Extended` substitution.
This closes the reflected-family demand step for the three existing code
constructors; it does not add Pi or general-family code constructors or
assert their corresponding marker properties or source soundness.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ReflectionDemand

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

/-- Each marker is an actual mandatory compact observation. A universe
uses a full exact level tag with bottom payload; that payload cannot be
the mandatory payload of a neutral-type or proof descriptor. -/
def marker : NeutralCodes.Descriptor → CptI
  | .neutralType k name => NeutralCodes.fullTag k (NeutralCodes.neutralPayload name)
  | .proof _ => NeutralCodes.fullTag (some 0) (.spine 24 [])
  | .univ k => NeutralCodes.fullTag (k.map Nat.succ) .bot

theorem marker_member (d : NeutralCodes.Descriptor) :
    NeutralCodes.reify d (marker d) := by
  cases d with
  | neutralType k name => exact Or.inr rfl
  | proof P => exact Or.inr (Or.inl rfl)
  | univ k =>
      exact approxI_famApp 10 []
        (.cons (.const EnvI.bot (levelRef (k.map Nat.succ)) [])
          (.cons (.bot EnvI.bot (.app (.const 11 []) (levelTerm k))) .nil))

theorem successor_index_injective {k l : Option Nat}
    (h : k.map Nat.succ = l.map Nat.succ) : k = l := by
  cases k with
  | none => cases l <;> first | rfl | cases h
  | some a =>
      cases l with
      | none => cases h
      | some b =>
          exact congrArg some (Nat.succ.inj (Option.some.inj h))

/-- Native universe payloads cannot contain a lambda observation. -/
theorem universe_no_lambda_payload (k l : Option Nat) (g : NeutralPi.Graph) :
    ¬ universeValue k (NeutralCodes.fullTag l (.lam g)) := by
  intro h
  rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm (k.map Nat.succ), .app (.const 11 []) (levelTerm k)]) h
    with hb | ⟨us, hu, hs⟩
  · cases hb
  · cases hs with
    | cons ha hs =>
      cases hs with
      | cons hp hs =>
        cases hs
        cases hu
        rcases approxI_foldApps_const_inv (r := 11) (ls := [])
          (xs := [levelTerm k]) hp with hb | ⟨vs, hv, _⟩
        · cases hb
        · cases hv

theorem universe_no_proof_marker (k : Option Nat) :
    ¬ universeValue k (NeutralCodes.fullTag (some 0) (.spine 24 [])) := by
  intro h
  have hk : k.map Nat.succ = some 0 := tagAt_full_index (sort_member EnvI.bot k _ h)
  cases k with
  | none => cases hk
  | some n => exact Nat.noConfusion (Option.some.inj hk)

/-- Marker sharing needs only the reflected value to agree. Truth
parameters and neutral type names need not be reconstructed or decided. -/
theorem marker_reflection {d e : NeutralCodes.Descriptor}
    (h : NeutralCodes.reify e (marker d)) (name : Nat) :
    ValueEq (NeutralCodes.reflectDescriptor d name)
      (NeutralCodes.reflectDescriptor e name) := by
  cases d with
  | neutralType k other =>
      cases e with
      | neutralType l second => exact ValueEq.refl _
      | proof P => exact ValueEq.refl _
      | univ l =>
          exact (universe_no_lambda_payload l k [([], .spine other [])] h).elim
  | proof P =>
      cases e with
      | neutralType l second => exact ValueEq.refl _
      | proof Q => exact ValueEq.refl _
      | univ l => exact (universe_no_proof_marker l h).elim
  | univ k =>
      cases e with
      | neutralType l second =>
          simp [marker, NeutralCodes.reify, NeutralCodes.neutralTypeValue,
            NeutralCodes.fullTag, NeutralCodes.neutralPayload] at h
      | proof P =>
          simp [marker, NeutralCodes.reify, NeutralCodes.proofCodeValue,
            NeutralCodes.fullTag] at h
      | univ l =>
          have hl : l.map Nat.succ = k.map Nat.succ :=
            tagAt_full_index (sort_member EnvI.bot l _ h)
          have hlk : l = k := successor_index_injective hl
          subst l
          exact ValueEq.refl _

/-- Finite demand of reified code values constructs finite demand of
their reflected values for the whole current descriptor grammar. -/
theorem descriptor_reflection_finiteDemand {D : Relation}
    (B : Value → NeutralCodes.Descriptor)
    (hfinite : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reify (B x)))
    (name : Nat) :
    UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflectDescriptor (B x) name) := by
  intro x hx c hc
  obtain ⟨us, hus, hrow⟩ := hfinite x hx (marker (B x)) (marker_member (B x))
  refine ⟨us, hus, ?_⟩
  intro y hy huy
  exact (marker_reflection (hrow y hy huy) name c).mp hc

theorem descriptorGraph_member_of_codeDemand {D : Relation} (hD : Laws D)
    (B : Value → NeutralCodes.Descriptor)
    (hB : FamilyCoherent D (fun x => NeutralCodes.El (B x)))
    (hfinite : UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reify (B x)))
    (name : Nat) :
    Member (FunctionPER NeutralPi.applyValue D (fun x => NeutralCodes.El (B x)))
      (UnifiedPi.descriptorGraph D B name) :=
  UnifiedPi.descriptorGraph_member hD B hB name
    (descriptor_reflection_finiteDemand B hfinite name)

/-- Canonical reflection needs no selected descriptor family. Each
existential presentation is used only inside this Prop-valued proof. -/
theorem reflection_finiteDemand_of_presentations {D : Relation} {V : Value → Value}
    (hfinite : UnifiedPi.LegalFiniteDemand D V)
    (hpresent : ∀ x : Value, Member D x →
      ∃ d : NeutralCodes.Descriptor, ValueEq (V x) (NeutralCodes.reify d))
    (name : Nat) :
    UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (V x) name) := by
  intro x hx c hc
  obtain ⟨d, hd⟩ := hpresent x hx
  have hdmarker : V x (marker d) := (hd _).mpr (marker_member d)
  have hdc : NeutralCodes.reflectDescriptor d name c :=
    (NeutralCodes.reflect_at hd name c).mp hc
  obtain ⟨us, hus, hrow⟩ := hfinite x hx (marker d) hdmarker
  refine ⟨us, hus, ?_⟩
  intro y hy huy
  obtain ⟨e, he⟩ := hpresent y hy
  have hemarker : NeutralCodes.reify e (marker d) := (he _).mp (hrow y hy huy)
  exact (NeutralCodes.reflect_at he name c).mpr
    ((marker_reflection hemarker name c).mp hdc)

theorem reflection_finiteDemand_of_codes {D : Relation} {V : Value → Value}
    (hfinite : UnifiedPi.LegalFiniteDemand D V)
    (hcodes : ∀ x : Value, Member D x →
      ∃ (k : Option Nat) (R : Relation), NeutralCodes.Code k (V x) R)
    (name : Nat) :
    UnifiedPi.LegalFiniteDemand D (fun x => NeutralCodes.reflect (V x) name) := by
  apply reflection_finiteDemand_of_presentations hfinite _ name
  intro x hx
  obtain ⟨k, R, d, _, hd, _⟩ := hcodes x hx
  exact ⟨d, hd⟩

theorem reflection_bot_of_code {k : Option Nat} {V : Value} {R : Relation}
    (hcode : NeutralCodes.Code k V R) (name : Nat) : NeutralCodes.reflect V name .bot := by
  obtain ⟨d, _, hd, _⟩ := hcode
  exact (NeutralCodes.reflect_at hd name .bot).mpr (UnifiedPi.reflectDescriptor_bot d name)

/-- The value operation uses the canonical reflection directly, without
extracting code data or a PER from an existential presentation. -/
def codeFamilyGraph (D : Relation) (V : Value → Value) (name : Nat) : Value :=
  UnifiedPi.legalGraph D (fun x => NeutralCodes.reflect (V x) name)

theorem codeFamilyGraph_application {D : Relation} {V : Value → Value}
    (hfinite : UnifiedPi.LegalFiniteDemand D V)
    (hcodes : ∀ x : Value, Member D x →
      ∃ (k : Option Nat) (R : Relation), NeutralCodes.Code k (V x) R)
    (name : Nat) {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (codeFamilyGraph D V name) x)
      (NeutralCodes.reflect (V x) name) := by
  apply UnifiedPi.applyValue_legalGraph _
    (reflection_finiteDemand_of_codes hfinite hcodes name) hx
  intro y hy
  obtain ⟨k, R, hc⟩ := hcodes y hy
  exact reflection_bot_of_code hc name

/-- Actual membership uses the chosen codomain codes and their PER
coherence. Reflected finite demand is supplied by the marker theorem. -/
theorem codeFamilyGraph_member {D : Relation} (hD : Laws D)
    {V : Value → Value} {C : Value → Relation}
    (hfinite : UnifiedPi.LegalFiniteDemand D V)
    (hcodes : ∀ x : Value, Member D x →
      ∃ k : Option Nat, NeutralCodes.Code k (V x) (C x))
    (hC : FamilyCoherent D C) (name : Nat) :
    Member (FunctionPER NeutralPi.applyValue D C) (codeFamilyGraph D V name) := by
  have hpresent : ∀ x : Value, Member D x →
      ∃ (k : Option Nat) (R : Relation), NeutralCodes.Code k (V x) R := by
    intro x hx
    obtain ⟨k, hk⟩ := hcodes x hx
    exact ⟨k, C x, hk⟩
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
      (codeFamilyGraph_application hfinite hpresent name (left_member hD hxy)),
    NeutralCodes.valueEq_eq
      (codeFamilyGraph_application hfinite hpresent name (right_member hD hxy))]
  obtain ⟨k, hx⟩ := hcodes x (left_member hD hxy)
  obtain ⟨l, hy⟩ := hcodes y (right_member hD hxy)
  exact NeutralCodes.reflect_relation hx hy (hC x y hxy) name

/-- The source-independent native body theorem supplies code-family
finite demand, so no second continuity premise is needed here. -/
theorem native_codeFamilyGraph_application (D : Relation) (ρ : EnvI) (body : Expr Nat)
    (hcodes : ∀ x : Value, Member D x →
      ∃ (k : Option Nat) (R : Relation),
        NeutralCodes.Code k (denI (EnvI.cons x ρ) body) R)
    (name : Nat) {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue
      (codeFamilyGraph D (fun y => denI (EnvI.cons y ρ) body) name) x)
      (NeutralCodes.reflect (denI (EnvI.cons x ρ) body) name) :=
  codeFamilyGraph_application (UnifiedPi.native_body_legalFiniteDemand D ρ body)
    hcodes name hx

theorem native_codeFamilyGraph_member {D : Relation} (hD : Laws D)
    (ρ : EnvI) (body : Expr Nat) {C : Value → Relation}
    (hcodes : ∀ x : Value, Member D x →
      ∃ k : Option Nat, NeutralCodes.Code k (denI (EnvI.cons x ρ) body) (C x))
    (hC : FamilyCoherent D C) (name : Nat) :
    Member (FunctionPER NeutralPi.applyValue D C)
      (codeFamilyGraph D (fun x => denI (EnvI.cons x ρ) body) name) :=
  codeFamilyGraph_member hD (UnifiedPi.native_body_legalFiniteDemand D ρ body)
    hcodes hC name

end Rcic.Declarative.Ann.LR3.ReflectionDemand
