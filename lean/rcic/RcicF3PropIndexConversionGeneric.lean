import rcic.RcicF3PropIndexConversionAttack

/-!
# The unadmitted Prop-Bool conversion in an arbitrary containing environment

Only the four lookup equations at refs 3, 4, 5, and 6 are required. The
environment may independently contain a genuinely admitted target group
at refs 0/1/2, and proposition arguments may be local variables. No facts
about those unrelated references or the local context are assumed beyond
the actual HasTyT derivations supplied for the two proposition terms.

This is the syntactic conversion gadget only. The four declarations do
not assert EnvWfT for the containing environment. No hereditary semantic
soundness or full IotaAt counterexample is claimed. The direct LOKc proof
retains the bounds on the supplied typings and needs no additional bound
on the empty universe vectors of the four added constants.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false


namespace Rcic.F3.PSet.PropIndexConversionGeneric

open Rcic.Declarative
open PropIndexConversionAttack (boolMember ctorMember recMember recType motive partialRec)

/-- Exactly the four signature lookups used by the gadget. -/
structure Lookups (S : ResolvedEnv) : Prop where
  bool_lookup : S.members 3 = some boolMember
  first_lookup : S.members 4 = some ctorMember
  second_lookup : S.members 5 = some ctorMember
  rec_lookup : S.members 6 = some recMember

section Generic

variable {S : ResolvedEnv} (L : Lookups S) {n : Nat}

noncomputable def boolTyped (Γ : LCtx) : HasTyT S n Γ (.const 3 []) (.sort .zero) :=
  .const Γ 3 [] boolMember L.bool_lookup rfl rfl

noncomputable def firstTyped (Γ : LCtx) : HasTyT S n Γ (.const 4 []) (.const 3 []) :=
  .const Γ 4 [] ctorMember L.first_lookup rfl rfl

noncomputable def secondTyped (Γ : LCtx) : HasTyT S n Γ (.const 5 []) (.const 3 []) :=
  .const Γ 5 [] ctorMember L.second_lookup rfl rfl

noncomputable def motiveTyped (Γ : LCtx) :
    HasTyT S n Γ motive (.pi (.const 3 []) (.sort (.succ .zero))) :=
  .lam Γ (.const 3 []) .zero (.sort .zero) (.sort (.succ .zero))
    (boolTyped L Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero)

noncomputable def betaFirst (Γ : LCtx) :
    ConvT S n Γ (.app motive (.const 4 [])) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 3 []) (.sort .zero) (.const 4 []) (.sort (.succ .zero)) .zero
    (boolTyped L Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero) (firstTyped L Γ)

noncomputable def betaSecond (Γ : LCtx) :
    ConvT S n Γ (.app motive (.const 5 [])) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 3 []) (.sort .zero) (.const 5 []) (.sort (.succ .zero)) .zero
    (boolTyped L Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero) (secondTyped L Γ)

noncomputable def firstWitness (U V : Expr Nat) : IotaWitness S where
  recRef := 6
  ctorRef := 4
  ls := []
  lsC := []
  recMember := recMember
  ctorMember := ctorMember
  hrec := L.rec_lookup
  hctor := L.first_lookup
  hrecK := rfl
  hctorK := rfl
  preMajor := [motive, U, V]
  fields := []
  ctorParams := []
  kinds := []
  minor := U
  hlen := rfl
  familyRef := 3
  famMember := boolMember
  hfam := L.bool_lookup
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := []
  ctorResult := .const 3 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 3 []) (.sort (.succ .zero)),
    .app (.bvar 0) (.const 4 []), .app (.bvar 1) (.const 5 []), .const 3 []]
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 3 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

noncomputable def secondWitness (U V : Expr Nat) : IotaWitness S :=
  { firstWitness L U V with
    ctorRef := 5
    hctor := L.second_lookup
    minor := V
    ctorIdx := 1
    hidx := by change 1 < 2; decide
    hctorIdx := rfl
    hminor := rfl }

noncomputable def partialTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero))
    (hV : HasTyT S n Γ V (.sort .zero)) :
    HasTyT S n Γ (partialRec U V)
      (.pi (.const 3 []) (.app (Rcic.Declarative.lift 0 1 motive) (.bvar 0))) := by
  have hR : HasTyT S n Γ (.const 6 []) recType :=
    .const Γ 6 [] recMember L.rec_lookup rfl rfl
  have h1 := HasTyT.app Γ (.const 6 []) motive _ _ hR (motiveTyped L Γ)
  have hU' : HasTyT S n Γ U (.app motive (.const 4 [])) :=
    .conv Γ U (.sort .zero) (.app motive (.const 4 [])) (.succ .zero) hU
      (.symm Γ _ _ _ (betaFirst L Γ))
  have hV' : HasTyT S n Γ V (.app motive (.const 5 [])) :=
    .conv Γ V (.sort .zero) (.app motive (.const 5 [])) (.succ .zero) hV
      (.symm Γ _ _ _ (betaSecond L Γ))
  have h2 := HasTyT.app Γ _ U _ _ h1 hU'
  exact HasTyT.app Γ _ V _ _ h2 hV'

noncomputable def firstLhsTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero))
    (hV : HasTyT S n Γ V (.sort .zero)) :
    HasTyT S n Γ (iotaLhsOf (firstWitness L U V)) (.sort .zero) :=
  .conv Γ _ (.app motive (.const 4 [])) (.sort .zero) (.succ .zero)
    (.app Γ _ (.const 4 []) _ _ (partialTyped L Γ U V hU hV) (firstTyped L Γ))
    (betaFirst L Γ)

noncomputable def secondLhsTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero))
    (hV : HasTyT S n Γ V (.sort .zero)) :
    HasTyT S n Γ (iotaLhsOf (secondWitness L U V)) (.sort .zero) :=
  .conv Γ _ (.app motive (.const 5 [])) (.sort .zero) (.succ .zero)
    (.app Γ _ (.const 5 []) _ _ (partialTyped L Γ U V hU hV) (secondTyped L Γ))
    (betaSecond L Γ)

/-- Actual typing inputs produce the conversion. No conversion,
semantic code equality, or index comparator is an antecedent. -/
noncomputable def propositionConversion (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero))
    (hV : HasTyT S n Γ V (.sort .zero)) :
    ConvT S n Γ U V (.sort .zero) := by
  have hi0 : ConvT S n Γ (iotaLhsOf (firstWitness L U V)) U (.sort .zero) :=
    .iota Γ _ _ _ (.of (firstWitness L U V)) (firstLhsTyped L Γ U V hU hV) hU
  have hi1 : ConvT S n Γ (iotaLhsOf (secondWitness L U V)) V (.sort .zero) :=
    .iota Γ _ _ _ (.of (secondWitness L U V)) (secondLhsTyped L Γ U V hU hV) hV
  have hc : ConvT S n Γ (.const 4 []) (.const 5 []) (.const 3 []) :=
    .irr Γ (.const 3 []) (.const 4 []) (.const 5 [])
      (boolTyped L Γ) (firstTyped L Γ) (secondTyped L Γ)
  have hm : ConvT S n Γ (iotaLhsOf (firstWitness L U V))
      (iotaLhsOf (secondWitness L U V)) (.sort .zero) :=
    .tyConv Γ _ _ (.app motive (.const 4 [])) (.sort .zero) (.succ .zero)
      (.app Γ (partialRec U V) (partialRec U V) (.const 4 []) (.const 5 [])
        (.const 3 []) (.app (Rcic.Declarative.lift 0 1 motive) (.bvar 0))
        (.refl Γ _ _ (partialTyped L Γ U V hU hV)) hc)
      (betaFirst L Γ)
  exact .trans Γ U _ V (.sort .zero) (.symm Γ _ _ _ hi0)
    (.trans Γ _ _ _ (.sort .zero) hm hi1)

private theorem nil_levels (σ K : Nat → Nat) (r : Nat) : LevelsOK σ (K r) [] :=
  fun l h => (List.not_mem_nil l h).elim

theorem motive_bound (σ K : Nat → Nat) (Γ : LCtx) :
    LOKt σ 4 K (motiveTyped (n := n) L Γ) :=
  ⟨nil_levels σ K 3, by change 1 ≤ 4; decide⟩

theorem betaFirst_bound (σ K : Nat → Nat) (Γ : LCtx) :
    LOKc σ 4 K (betaFirst (n := n) L Γ) :=
  ⟨nil_levels σ K 3, by change 1 ≤ 4; decide, nil_levels σ K 4⟩

theorem betaSecond_bound (σ K : Nat → Nat) (Γ : LCtx) :
    LOKc σ 4 K (betaSecond (n := n) L Γ) :=
  ⟨nil_levels σ K 3, by change 1 ≤ 4; decide, nil_levels σ K 5⟩

theorem partial_bound (σ K : Nat → Nat) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero)) (hV : HasTyT S n Γ V (.sort .zero))
    (lU : LOKt σ 4 K hU) (lV : LOKt σ 4 K hV) :
    LOKt σ 4 K (partialTyped L Γ U V hU hV) :=
  ⟨⟨⟨nil_levels σ K 6, motive_bound L σ K Γ⟩, ⟨lU, betaFirst_bound L σ K Γ⟩⟩,
    ⟨lV, betaSecond_bound L σ K Γ⟩⟩

theorem firstLhs_bound (σ K : Nat → Nat) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero)) (hV : HasTyT S n Γ V (.sort .zero))
    (lU : LOKt σ 4 K hU) (lV : LOKt σ 4 K hV) :
    LOKt σ 4 K (firstLhsTyped L Γ U V hU hV) :=
  ⟨⟨partial_bound L σ K Γ U V hU hV lU lV, nil_levels σ K 4⟩,
    betaFirst_bound L σ K Γ⟩

theorem secondLhs_bound (σ K : Nat → Nat) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero)) (hV : HasTyT S n Γ V (.sort .zero))
    (lU : LOKt σ 4 K hU) (lV : LOKt σ 4 K hV) :
    LOKt σ 4 K (secondLhsTyped L Γ U V hU hV) :=
  ⟨⟨partial_bound L σ K Γ U V hU hV lU lV, nil_levels σ K 5⟩,
    betaSecond_bound L σ K Γ⟩

/-- The introduced syntax has a direct bound at N=4 for every valuation
and K; in particular K may be the constant-one bound of the final attack. -/
theorem propositionConversion_bound (σ K : Nat → Nat) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT S n Γ U (.sort .zero)) (hV : HasTyT S n Γ V (.sort .zero))
    (lU : LOKt σ 4 K hU) (lV : LOKt σ 4 K hV) :
    LOKc σ 4 K (propositionConversion L Γ U V hU hV) :=
  ⟨⟨firstLhs_bound L σ K Γ U V hU hV lU lV, lU⟩,
    ⟨⟨⟨partial_bound L σ K Γ U V hU hV lU lV,
      ⟨nil_levels σ K 3, nil_levels σ K 4, nil_levels σ K 5⟩⟩,
      betaFirst_bound L σ K Γ⟩,
      ⟨secondLhs_bound L σ K Γ U V hU hV lU lV, lV⟩⟩⟩

end Generic

/-- The original explicit extension inhabits the four-lookup interface;
this does not assert that extension's admission. -/
noncomputable def originalLookups : Lookups PropIndexConversionAttack.extension :=
  ⟨rfl, rfl, rfl, rfl⟩

noncomputable def familyConversion : ConvT PropIndexConversionAttack.extension 0 []
    (.app (.const 0 []) (.const 1 [])) (.app (.const 0 []) (.const 2 [])) (.sort .zero) :=
  propositionConversion originalLookups [] _ _
    PropIndexConversionAttack.falseFamilyTyped PropIndexConversionAttack.trueFamilyTyped

theorem familyConversion_bound (σ : Nat → Nat) :
    LOKc σ 4 (fun _ => 1) familyConversion :=
  propositionConversion_bound originalLookups σ (fun _ => 1) [] _ _
    PropIndexConversionAttack.falseFamilyTyped PropIndexConversionAttack.trueFamilyTyped
    ⟨nil_levels σ (fun _ => 1) 0, nil_levels σ (fun _ => 1) 1⟩
    ⟨nil_levels σ (fun _ => 1) 0, nil_levels σ (fun _ => 1) 2⟩

/-- A concrete typed conversion produced by the generalized theorem,
composed with its actual bound for every syntax valuation. -/
noncomputable def Witness : Prop :=
  ∃ c : ConvT PropIndexConversionAttack.extension 0 []
    (.app (.const 0 []) (.const 1 [])) (.app (.const 0 []) (.const 2 [])) (.sort .zero),
    ∀ σ : Nat → Nat, LOKc σ 4 (fun _ => 1) c

theorem component_witness : Witness := ⟨familyConversion, familyConversion_bound⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness → (Premises4 → False)) := fun h => h component_witness P

end Rcic.F3.PSet.PropIndexConversionGeneric

#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.firstWitness
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.secondWitness
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.propositionConversion
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.propositionConversion_bound
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.familyConversion
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.familyConversion_bound
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.component_witness
#print axioms Rcic.F3.PSet.PropIndexConversionGeneric.component_nonrefutable
