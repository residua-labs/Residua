import rcic.RcicAnnLR3TaggedKClosure
import rcic.RcicAnnLR3TaggedKPiFixture
import rcic.RcicAnnLR3TaggedKEvaluation

/-!
# Image-compatible certified K attachments and element coherence

The source is the admitted large-K fixture and the evaluator uses the
inherited Eq/refl/J combinators. The call's family attachment is permitted
by the present Witness.family interface, which accepts an explicitly typed
raw image. It is not asserted to be the output forced by a source reader.
The source-neutral major is realized by the nonbottom proof unit.

This tests the policy accepting every certified endpoint attachment with
the correct actual image. It is not a source-language counterexample.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace Rcic.Declarative.Ann.LR3.TaggedKCoherenceBoundary
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower TaggedKClosure

def emptyConstructor : NeutralFamily.ConstructorOp TypedInductive.emptySignature :=
  fun _ r _ => nomatch r

def callCode (ν : Valuation) : Code.{0} 1 :=
  familyCode 0 TypedInductive.emptySignature emptyConstructor ()
    (TaggedKEvaluation.image ν fixtureEnv (EqLargeFixture.call (.bvar 0)))
    (TaggedKEvaluation.call_level ν) (TaggedKEvaluation.call_defined ν)

theorem callCode_tag (ν : Valuation) : (callCode ν).tag = .family := rfl

theorem callCode_image (ν : Valuation) :
    ValueEq (callCode ν).view.value
      (TaggedKEvaluation.image ν fixtureEnv (EqLargeFixture.call (.bvar 0))) :=
  ValueEq.refl _

def reflectedPoint (ν : Valuation) (name : Nat) : (callCode ν).Element :=
  SaturatedFamilyCode.reflect TypedInductive.emptySignature emptyConstructor ()
    (NativeMemberValues.value (some 1) name)
    (SaturatedFamilyNative.member_neutral (some 1) name)

theorem reflectedPoint_member (ν : Valuation) (name : Nat) :
    (callCode ν).view.relation (reflectedPoint ν name) (reflectedPoint ν name) :=
  SaturatedFamilyCode.reflect_member TypedInductive.emptySignature emptyConstructor ()
    (NativeMemberValues.value (some 1) name)
    (SaturatedFamilyNative.member_neutral (some 1) name)

theorem reflectedPoint_image (ν : Valuation) (name : Nat) :
    ValueEq ((callCode ν).erase (reflectedPoint ν name))
      (NativeMemberValues.value (some 1) name) := ValueEq.refl _

def equalityPER (ν : Valuation) : TypedPER.Relation :=
  NeutralPER.EqPER CandidatePi.Neutral (SortPER (some 0))
    (TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter)
    (TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter)

theorem actual_major_member (ν : Valuation) :
    Member (equalityPER ν) (TaggedKEvaluation.image ν fixtureEnv (.bvar 0)) := by
  have hp : UnitModel.ProofMember EnvI.bot
      (TaggedKEvaluation.image ν fixtureEnv (.bvar 0)) :=
    (TaggedKEvaluation.major_is_unit ν).trans
      (unit_cons EnvI.bot (unitValue EnvI.bot))
  exact ⟨Or.inl ⟨TaggedKEvaluation.parameter_guard ν, hp⟩,
    Or.inl ⟨TaggedKEvaluation.parameter_guard ν, hp⟩⟩

theorem actual_refl_member (ν : Valuation) :
    Member (equalityPER ν) (unitValue EnvI.bot) :=
  NeutralPER.eqPER_refl CandidatePi.Neutral (TaggedKEvaluation.parameter_guard ν)


def minorCode (ν : Valuation) : Code.{0} 1 :=
  TaggedKPiFixture.code EqLargeFixture.env TaggedKEvaluation.eqSyntax ν fixtureEnv

theorem minorCode_tag (ν : Valuation) : (minorCode ν).tag = .pi := rfl

theorem minorCode_image (ν : Valuation) :
    ValueEq (minorCode ν).view.value
      (TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.result) := ValueEq.refl _

theorem endpoint_images_agree (ν : Valuation) :
    ValueEq (callCode ν).view.value (minorCode ν).view.value :=
  TaggedKEvaluation.open_call_image ν

theorem endpoint_tags_differ (ν : Valuation) :
    (callCode ν).tag ≠ (minorCode ν).tag := by
  intro h
  cases h

theorem endpoint_universe_members (ν : Valuation) :
    (universeCode.{0} 1).view.relation (callCode ν) (callCode ν) ∧
    (universeCode.{0} 1).view.relation (minorCode ν) (minorCode ν) :=
  ⟨universe_member 1 (callCode ν), universe_member 1 (minorCode ν)⟩

theorem reflected_good (ν : Valuation) (name : Nat) :
    Good (callCode ν) (NativeMemberValues.value (some 1) name) :=
  ⟨reflectedPoint ν name, reflectedPoint_member ν name, reflectedPoint_image ν name⟩

theorem minor_not_good (ν : Valuation) (name : Nat) :
    ¬ Good (minorCode ν) (NativeMemberValues.value (some 1) name) :=
  TaggedKPiFixture.native_not_erased_member
    EqLargeFixture.env TaggedKEvaluation.eqSyntax ν fixtureEnv (some 1) name

theorem minor_inhabited (ν : Valuation) :
    ∃ f : (minorCode ν).Element, (minorCode ν).view.relation f f :=
  TaggedKPiFixture.code_inhabited
    EqLargeFixture.env TaggedKEvaluation.eqSyntax ν fixtureEnv

theorem decoded_not_same (ν : Valuation) :
    ¬ NeutralK.Same (Decoded (callCode ν)) (Decoded (minorCode ν)) := by
  intro hs
  have hN := (decoded_member_iff (callCode ν) _).mpr (reflected_good ν 0)
  exact minor_not_good ν 0
    ((decoded_member_iff (minorCode ν) _).mp ((hs _ _).mp hN))

theorem no_pairTransport (ν : Valuation) :
    ¬ PairTransport (callCode ν) (minorCode ν) := by
  intro h
  have hN := (decoded_member_iff (callCode ν) _).mpr (reflected_good ν 0)
  exact minor_not_good ν 0
    ((decoded_member_iff (minorCode ν) _).mp (decoded_of_pairTransport h hN))

/-- Even a one-way map preserving erasure on members is impossible here. -/
theorem no_total_erased_transport (ν : Valuation) :
    ¬ ∃ tr : (callCode ν).Element → (minorCode ν).Element,
      ∀ a, (callCode ν).view.relation a a →
        ValueEq ((minorCode ν).erase (tr a)) ((callCode ν).erase a) := by
  rintro ⟨tr, he⟩
  exact TaggedKPiFixture.no_native_element
    EqLargeFixture.env TaggedKEvaluation.eqSyntax ν fixtureEnv
    (tr (reflectedPoint ν 0)) (some 1) 0
    ((he (reflectedPoint ν 0) (reflectedPoint_member ν 0)).trans
      (reflectedPoint_image ν 0))

def frame (ν : Valuation) : Frame.{0} 1 where
  source := SortPER (some 0)
  left := TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter
  right := TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter
  major := TaggedKEvaluation.image ν fixtureEnv (.bvar 0)
  call := callCode ν
  minor := minorCode ν

/-- This policy admits every certified endpoint with the actual source images.
It includes source formation, the real typed K frame and a fitting major.
It deliberately does not assert that a source reader produced the family
attachment, or put the desired transport into an admission field. -/
structure AtTarget (ν : Valuation) (f : Frame.{0} 1) : Prop where
  environment : Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env)
  context : Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
    0 EqLargeFixture.context)
  source_frame : Nonempty (KStage.Frame EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
    0 EqLargeFixture.context KEqPositive.eqShape)
  call_typed : Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
    0 EqLargeFixture.context (EqLargeFixture.call (.bvar 0)) (.sort EqLargeFixture.one))
  minor_typed : Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
    0 EqLargeFixture.context EqLargeFixture.result (.sort EqLargeFixture.one))
  major_typed : Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
    0 EqLargeFixture.context (.bvar 0) EqLargeFixture.domain)
  fitting : FitsFixture ν fixtureEnv
  source_relation : f.source = SortPER (some 0)
  left_index : f.left = TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter
  right_index : f.right = TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.parameter
  major_image : ValueEq f.major (TaggedKEvaluation.image ν fixtureEnv (.bvar 0))
  major_member : Member (equalityPER ν) f.major
  call_image : ValueEq f.call.view.value
    (TaggedKEvaluation.image ν fixtureEnv (EqLargeFixture.call (.bvar 0)))
  minor_image : ValueEq f.minor.view.value
    (TaggedKEvaluation.image ν fixtureEnv EqLargeFixture.result)

theorem atTarget (ν : Valuation) : AtTarget ν (frame ν) := by
  refine {
    environment := EqLargeFixture.wf
    context := ⟨EqLargeFixture.contextWf⟩
    source_frame := KEqPositive.eqFrame
    call_typed := ?_
    minor_typed := ⟨EqLargeFixture.resultTyped⟩
    major_typed := ⟨EqLargeFixture.majorTyped⟩
    fitting := fixtureEnv_fits ν
    source_relation := rfl
    left_index := rfl
    right_index := rfl
    major_image := ValueEq.refl _
    major_member := actual_major_member ν
    call_image := callCode_image ν
    minor_image := minorCode_image ν }
  obtain ⟨hc⟩ := EqLargeFixture.conversion
  exact ⟨convA_hasTy_left EqLargeFixture.closed EqLargeFixture.liftIface
    (iotaFnA_recHead EqLargeFixture.env) EqLargeFixture.substIface
    EqLargeFixture.contextWf hc⟩

theorem atTarget_guard {ν : Valuation} {f : Frame.{0} 1}
    (hf : AtTarget ν f) : Guard f := by
  unfold Guard
  rw [hf.source_relation, hf.left_index, hf.right_index]
  exact TaggedKEvaluation.parameter_guard ν

theorem frame_guard (ν : Valuation) : Guard (frame ν) :=
  atTarget_guard (atTarget ν)

theorem forced_edge (ν : Valuation) :
    KEdge (frame ν) (callCode ν) (minorCode ν) :=
  (kEdge_iff (frame ν)).mpr (frame_guard ν)

theorem forced_related (ν : Valuation) :
    Related (AtTarget ν) (callCode ν) (minorCode ν) :=
  k_related (AtTarget ν) (frame ν) (atTarget ν) (frame_guard ν)

theorem closure_not_coherent (ν : Valuation) : ¬ Coherent (AtTarget ν) :=
  fun h => decoded_not_same ν (h _ _ (forced_related ν))

/-- Independent of the weak Base: any relation containing this actual
admitted forward edge fails to preserve the fixed decoded fibres. -/
theorem no_coherent_forward_extension (ν : Valuation)
    (R : Code.{0} 1 → Code.{0} 1 → Prop)
    (forward : ∀ f, AtTarget ν f → Guard f → R f.call f.minor) :
    ¬ (∀ C D, R C D → NeutralK.Same (Decoded C) (Decoded D)) := by
  intro hc
  exact decoded_not_same ν
    (hc _ _ (forward (frame ν) (atTarget ν) (frame_guard ν)))

/-- All source, image, guard and membership premises are supplied together.
This is not a claim that every source interpreter chooses these fibres. -/
theorem inhabited_coherence_boundary (ν : Valuation) :
    AtTarget ν (frame ν) ∧
    StuckA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env)
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0)) ∧
    KStage.Head EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result KEqPositive.eqShape.resultType ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    Guard (frame ν) ∧
    ValueEq (callCode ν).view.value (minorCode ν).view.value ∧
    (∀ ρ, ValueEq
      (TaggedKEvaluation.image ν ρ StrictProofModelBoundary.canonicalCallA3)
      (TaggedKEvaluation.image ν ρ EqLargeFixture.result)) ∧
    (callCode ν).tag ≠ (minorCode ν).tag ∧
    Good (callCode ν) (NativeMemberValues.value (some 1) 0) ∧
    (∃ f : (minorCode ν).Element, (minorCode ν).view.relation f f) ∧
    Related (AtTarget ν) (callCode ν) (minorCode ν) ∧
    ¬ PairTransport (callCode ν) (minorCode ν) ∧
    ¬ NeutralK.Same (Decoded (callCode ν)) (Decoded (minorCode ν)) ∧
    ¬ Coherent (AtTarget ν) :=
  ⟨atTarget ν, EqLargeFixture.callStuck, KEqPositive.eqHead, EqLargeFixture.conversion,
    frame_guard ν, endpoint_images_agree ν, TaggedKEvaluation.canonical_call_image ν,
    endpoint_tags_differ ν, reflected_good ν 0, minor_inhabited ν,
    forced_related ν, no_pairTransport ν, decoded_not_same ν, closure_not_coherent ν⟩


/-- A concrete compatible attachment for the same source K call. This
control makes no claim that a general reader can yet produce it. -/
def compatibleFrame (ν : Valuation) : Frame.{0} 1 :=
  { frame ν with call := minorCode ν }

theorem compatible_atTarget (ν : Valuation) : AtTarget ν (compatibleFrame ν) :=
  { atTarget ν with call_image := (TaggedKEvaluation.open_call_image ν).symm }

theorem compatible_guard (ν : Valuation) : Guard (compatibleFrame ν) :=
  atTarget_guard (compatible_atTarget ν)

theorem compatible_transport (ν : Valuation) :
    PairTransport (compatibleFrame ν).call (compatibleFrame ν).minor :=
  pairTransport_of_kernelIso (KernelIso.refl (minorCode ν).kernel)

theorem compatible_decoded_same (ν : Valuation) :
    NeutralK.Same (Decoded (compatibleFrame ν).call)
      (Decoded (compatibleFrame ν).minor) :=
  fun _ _ => Iff.rfl

theorem compatible_control (ν : Valuation) :
    AtTarget ν (compatibleFrame ν) ∧ Guard (compatibleFrame ν) ∧
    PairTransport (compatibleFrame ν).call (compatibleFrame ν).minor ∧
    PairTransport (compatibleFrame ν).minor (compatibleFrame ν).call ∧
    NeutralK.Same (Decoded (compatibleFrame ν).call)
      (Decoded (compatibleFrame ν).minor) :=
  ⟨compatible_atTarget ν, compatible_guard ν, compatible_transport ν,
    compatible_transport ν, compatible_decoded_same ν⟩

end Rcic.Declarative.Ann.LR3.TaggedKCoherenceBoundary
