import rcic.RcicNativeTypedModelCovWConvValley

/-!
# A sorted Pi conversion whose transitivity midpoint is not a Pi

The two distinct written Pi endpoints are the existing beta-domain pair.
The new midpoint is an identity beta expansion of the left endpoint.
Both conversion legs and their explicit ConvT.trans composition are typed
at one written sort. The endpoints still have an actual NativeValley.

This measures the shape missing from a direct induction restricted to two
written Pi endpoints: neither immediate subderivation of this trans node
has two written Pi endpoints. It is not a counterexample to PiConvValleyData
or a claim that every possible proof of that producer must use confluence.
No sorting-coherence, Pi-injectivity, or valley producer is assumed.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open TypedModelCovWConvAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

def covWRigidPiTransLevel : Level :=
  .imax (.succ (.succ .zero)) (.succ (.succ .zero))

/-- A non-Pi expression with exactly the left Pi endpoint's universe. -/
def covWRigidPiTransMiddle : Expr Nat :=
  .app (.lam (.sort covWRigidPiTransLevel) (.bvar 0)) convValleyPiLeft

def covWRigidPiTrans_middle_typed :
    HasTyT E n Γ covWRigidPiTransMiddle (.sort covWRigidPiTransLevel) :=
  .app Γ (.lam (.sort covWRigidPiTransLevel) (.bvar 0))
    convValleyPiLeft (.sort covWRigidPiTransLevel) (.sort covWRigidPiTransLevel)
    (.lam Γ (.sort covWRigidPiTransLevel) (.succ covWRigidPiTransLevel)
      (.bvar 0) (.sort covWRigidPiTransLevel)
      (.sort Γ covWRigidPiTransLevel)
      (.bvar (.assumption (.sort covWRigidPiTransLevel) :: Γ) 0
        (.sort covWRigidPiTransLevel) rfl))
    convValleyPiLeft_hasTy

def covWRigidPiTrans_middle_beta :
    ConvT E n Γ covWRigidPiTransMiddle convValleyPiLeft
      (.sort covWRigidPiTransLevel) :=
  .beta Γ (.sort covWRigidPiTransLevel) (.bvar 0) convValleyPiLeft
    (.sort covWRigidPiTransLevel) (.succ covWRigidPiTransLevel)
    (.sort Γ covWRigidPiTransLevel)
    (.bvar (.assumption (.sort covWRigidPiTransLevel) :: Γ) 0
      (.sort covWRigidPiTransLevel) rfl)
    convValleyPiLeft_hasTy

/-- The first immediate premise has a Pi source and an application target. -/
def covWRigidPiTrans_left_leg :
    ConvT E n Γ convValleyPiLeft covWRigidPiTransMiddle
      (.sort covWRigidPiTransLevel) :=
  .symm Γ covWRigidPiTransMiddle convValleyPiLeft
    (.sort covWRigidPiTransLevel) covWRigidPiTrans_middle_beta

/-- The second immediate premise has an application source and a Pi target. -/
def covWRigidPiTrans_right_leg :
    ConvT E n Γ covWRigidPiTransMiddle convValleyPiRight
      (.sort covWRigidPiTransLevel) :=
  .trans Γ covWRigidPiTransMiddle convValleyPiLeft convValleyPiRight
    (.sort covWRigidPiTransLevel)
    covWRigidPiTrans_middle_beta convValleyPi_nativeConv

/-- The outer trans node has two distinct written Pi endpoints at a sort. -/
def covWRigidPiTrans_conversion :
    ConvT E n Γ convValleyPiLeft convValleyPiRight
      (.sort covWRigidPiTransLevel) :=
  .trans Γ convValleyPiLeft covWRigidPiTransMiddle convValleyPiRight
    (.sort covWRigidPiTransLevel)
    covWRigidPiTrans_left_leg covWRigidPiTrans_right_leg

theorem covWRigidPiTrans_middle_not_pi (A B : Expr Nat) :
    covWRigidPiTransMiddle ≠ .pi A B := by
  intro h
  cases h

/-- The same input instance has an actual ParRedT valley, independently of
the presentation of its conversion by the trans node above. -/
def covWRigidPiTrans_nativeValley :
    NativeValley E n Γ convValleyPiLeft convValleyPiRight
      (.sort covWRigidPiTransLevel) :=
  convValleyPi_actualNativeValley

/-- Every native premise is inhabited in the admitted empty environment.
The syntactic midpoint obstruction and the positive valley are simultaneous. -/
theorem covWRigidPiTrans_inhabited (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧
    Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] convValleyPiLeft
      (.sort covWRigidPiTransLevel)) ∧
    Nonempty (HasTyT emptyEnv n [] covWRigidPiTransMiddle
      (.sort covWRigidPiTransLevel)) ∧
    Nonempty (HasTyT emptyEnv n [] convValleyPiRight
      (.sort covWRigidPiTransLevel)) ∧
    Nonempty (ConvT emptyEnv n [] convValleyPiLeft covWRigidPiTransMiddle
      (.sort covWRigidPiTransLevel)) ∧
    Nonempty (ConvT emptyEnv n [] covWRigidPiTransMiddle convValleyPiRight
      (.sort covWRigidPiTransLevel)) ∧
    Nonempty (ConvT emptyEnv n [] convValleyPiLeft convValleyPiRight
      (.sort covWRigidPiTransLevel)) ∧
    (∀ A B : Expr Nat, covWRigidPiTransMiddle ≠ .pi A B) ∧
    convValleyPiLeft ≠ convValleyPiRight ∧
    Nonempty (NativeValley emptyEnv n [] convValleyPiLeft convValleyPiRight
      (.sort covWRigidPiTransLevel)) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨convValleyPiLeft_hasTy⟩,
    ⟨covWRigidPiTrans_middle_typed⟩, ⟨convValleyPiRight_hasTy⟩,
    ⟨covWRigidPiTrans_left_leg⟩, ⟨covWRigidPiTrans_right_leg⟩,
    ⟨covWRigidPiTrans_conversion⟩, covWRigidPiTrans_middle_not_pi,
    convValleyPi_distinct, ⟨covWRigidPiTrans_nativeValley⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_RIGID_PI_TRANS_ROOTS
#print axioms covWRigidPiTransLevel
#print axioms covWRigidPiTransMiddle
#print axioms covWRigidPiTrans_middle_typed
#print axioms covWRigidPiTrans_middle_beta
#print axioms covWRigidPiTrans_left_leg
#print axioms covWRigidPiTrans_right_leg
#print axioms covWRigidPiTrans_conversion
#print axioms covWRigidPiTrans_middle_not_pi
#print axioms covWRigidPiTrans_nativeValley
#print axioms covWRigidPiTrans_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_RIGID_PI_TRANS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit
