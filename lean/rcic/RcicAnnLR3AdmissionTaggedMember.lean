import rcic.RcicAnnLR3TaggedSaturatedTower
import rcic.RcicAnnLR3SemanticMemberAdmissionControls

/-!
# Actual tagged universe/member data produced by admission readback

The defined-level success branch constructs a canonical tagged universe.
An admitted axiom with such a stored-type read retains its actual native
type code as an element of that universe. The arbitrary-depth controls
supply the source admission, typing and successful read.

The inner none level has no Nat-indexed tagged code here. Unsupported
stored types still require other producers; no general Ty_const or
unified raw CodeSystem is supplied. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.AdmissionTaggedMember
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open AdmissionUniverseReadback TaggedSaturatedTower

structure UniverseReading (E : ResolvedEnvA) (ν : Valuation) (A : ExprA) where
  level : Nat
  code : Code.{1} (level + 1)
  isUniverse : code.tag = .univ
  image : ∀ (F : EnvironmentEval.FamilySyntax) (ρ : EnvI),
    ValueEq (EnvironmentEval.denote (SemanticMemberEval.view E) F ν ρ A) code.view.value

def readTaggedUniverse {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) (A : ExprA) : Option (UniverseReading E ν A) :=
  match h : readAdmitted hE ν A with
  | some (some k) => some {
      level := k
      code := universeCode.{0} k
      isUniverse := rfl
      image := fun F ρ => readAdmitted_sound hE (prefixA_refl E) ν A (some k) h F ρ }
  | _ => none

theorem readTaggedUniverse_success {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) (A : ExprA) (k : Nat)
    (h : readAdmitted hE ν A = some (some k)) :
    (readTaggedUniverse hE ν A).map UniverseReading.level = some k := by
  unfold readTaggedUniverse
  split <;> simp_all

structure MemberReading (k : Nat) (typeImage memberImage : Value) where
  code : Code.{0} k
  type_image : ValueEq typeImage (universeCode.{0} k).view.value
  member_image : ValueEq memberImage
    ((universeCode.{0} k).erase (universeEncode k code))

/-- Membership is proved from the retained code, not an input to reading. -/
theorem MemberReading.member {k : Nat} {A a : Value} (x : MemberReading k A a) :
    (universeCode.{0} k).view.relation (universeEncode k x.code) (universeEncode k x.code) :=
  universe_member k x.code

def axiomElement {I : IotaIfaceA} {E : ResolvedEnvA} {r : Nat}
    {ls : List Level} {m : CheckedMemberA} (hE : EnvWfA I E)
    (hm : E.members r = some m) (hc : m.mclass = .axiomM)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (k : Nat)
    (hk : readAdmitted hE ν (instantiateLevelsA ls m.mtypeA) = some (some k)) :
    MemberReading k (image hE F ν ρ (instantiateLevelsA ls m.mtypeA))
      (image hE F ν ρ (.const r ls)) where
  code := Code.neutral.{0} k r
  type_image := stored_type_image hE F ν ρ _ _ hk
  member_image := axiom_image hE hm hc F ν ρ (some k) hk

open AdmissionUniverseControls

def probeElement (I : IotaIfaceA) (depth : Nat)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    MemberReading 0 (image (probe_admitted I depth) F ν ρ (.const depth []))
      (image (probe_admitted I depth) F ν ρ (.const (depth+1) [])) :=
  axiomElement (m := probeMember depth) (probe_admitted I depth)
    (members_extendEnvA_self _ _ _) rfl F ν ρ 0 (read_probe_type I depth ν)

theorem probe_pair (I : IotaIfaceA) (depth : Nat)
    (F : EnvironmentEval.FamilySyntax) (ν μ : Valuation) (ρ σ : EnvI) :
    (universeCode.{0} 0).view.relation
      (probeElement I depth F ν ρ).code (probeElement I depth F μ σ).code :=
  codeRelated_refl (Code.neutral.{0} 0 (depth+1))

theorem admitted_tagged_control (depth : Nat)
    (F : EnvironmentEval.FamilySyntax) (ν μ : Valuation) (ρ σ : EnvI) :
    Nonempty (EnvWfA (iotaIfaceA (probeEnv depth)) (probeEnv depth)) ∧
    Nonempty (HasTyA (probeEnv depth) (iotaIfaceA (probeEnv depth)) 0 []
      (.const (depth+1) []) (.const depth [])) ∧
    (universeCode.{0} 0).view.relation
      (probeElement (iotaIfaceA (probeEnv depth)) depth F ν ρ).code
      (probeElement (iotaIfaceA (probeEnv depth)) depth F μ σ).code ∧
    ValueEq (image (probe_admitted (iotaIfaceA (probeEnv depth)) depth)
      F ν ρ (.const (depth+1) []))
      ((universeCode.{0} 0).erase
        (probeElement (iotaIfaceA (probeEnv depth)) depth F ν ρ).code) ∧
    ValueEq (image (probe_admitted (iotaIfaceA (probeEnv depth)) depth)
      F μ σ (.const (depth+1) []))
      ((universeCode.{0} 0).erase
        (probeElement (iotaIfaceA (probeEnv depth)) depth F μ σ).code) :=
  ⟨⟨probe_admitted _ depth⟩, ⟨source_probe _ depth []⟩, probe_pair _ depth F ν μ ρ σ,
    (probeElement _ depth F ν ρ).member_image, (probeElement _ depth F μ σ).member_image⟩

end Rcic.Declarative.Ann.LR3.AdmissionTaggedMember
