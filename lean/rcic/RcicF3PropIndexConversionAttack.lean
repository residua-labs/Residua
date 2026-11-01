import rcic.RcicF3PropFamilyKeyAttack

/-!
# A concrete unadmitted extension converts arbitrary proposition codes

This is a separate syntax attack on the unrestricted extension domain of
IotaAt. The extension has a two-constructor Prop family and a monomorphic
large recursor. It is deliberately not asserted EnvWfT. Its literal legacy
witnesses nevertheless build two ConvT.iota rules. Congruence over proof
irrelevance of the constructors connects the two rules and converts any
two terms of Sort 0.

The module proves actual typed syntax, not a full semantic counterexample
to IotaAt. A complete attack must additionally supply hereditary soundness
and level bounds for the specific conversion and the target recursor redex,
plus the target group's actual admission and installed-table equations.
None of those remaining certificates is postulated here.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false


namespace Rcic.F3.PSet.PropIndexConversionAttack
open Rcic.Declarative

noncomputable def boolMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
noncomputable def ctorMember : CheckedMember := ⟨.constructorM, 0, .const 3 [], none⟩

noncomputable def recType : Expr Nat :=
  .pi (.pi (.const 3 []) (.sort (.succ .zero)))
    (.pi (.app (.bvar 0) (.const 4 []))
      (.pi (.app (.bvar 1) (.const 5 []))
        (.pi (.const 3 []) (.app (.bvar 3) (.bvar 0)))))

noncomputable def recMember : CheckedMember := ⟨.recursorM, 0, recType, none⟩

/-- No admission of this large two-constructor Prop eliminator is claimed. -/
noncomputable def extension : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv (extendEnv PropFamilyKeyAttack.signature
    3 boolMember) 4 ctorMember) 5 ctorMember) 6 recMember

noncomputable def motive : Expr Nat := .lam (.const 3 []) (.sort .zero)

noncomputable def boolTyped (Γ : LCtx) : HasTyT extension 0 Γ (.const 3 []) (.sort .zero) :=
  .const Γ 3 [] boolMember rfl rfl rfl

noncomputable def firstTyped (Γ : LCtx) : HasTyT extension 0 Γ (.const 4 []) (.const 3 []) :=
  .const Γ 4 [] ctorMember rfl rfl rfl

noncomputable def secondTyped (Γ : LCtx) : HasTyT extension 0 Γ (.const 5 []) (.const 3 []) :=
  .const Γ 5 [] ctorMember rfl rfl rfl

noncomputable def motiveTyped (Γ : LCtx) :
    HasTyT extension 0 Γ motive (.pi (.const 3 []) (.sort (.succ .zero))) :=
  .lam Γ (.const 3 []) .zero (.sort .zero) (.sort (.succ .zero))
    (boolTyped Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero)

noncomputable def betaFirst (Γ : LCtx) :
    ConvT extension 0 Γ (.app motive (.const 4 [])) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 3 []) (.sort .zero) (.const 4 []) (.sort (.succ .zero)) .zero
    (boolTyped Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero) (firstTyped Γ)

noncomputable def betaSecond (Γ : LCtx) :
    ConvT extension 0 Γ (.app motive (.const 5 [])) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 3 []) (.sort .zero) (.const 5 []) (.sort (.succ .zero)) .zero
    (boolTyped Γ) (.sort (.assumption (.const 3 []) :: Γ) .zero) (secondTyped Γ)

noncomputable def firstWitness (U V : Expr Nat) : IotaWitness extension where
  recRef := 6
  ctorRef := 4
  ls := []
  lsC := []
  recMember := recMember
  ctorMember := ctorMember
  hrec := rfl
  hctor := rfl
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
  hfam := rfl
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

noncomputable def secondWitness (U V : Expr Nat) : IotaWitness extension :=
  { firstWitness U V with
    ctorRef := 5
    hctor := rfl
    minor := V
    ctorIdx := 1
    hidx := by change 1 < 2; decide
    hctorIdx := rfl
    hminor := rfl }

noncomputable def partialRec (U V : Expr Nat) : Expr Nat :=
  .app (.app (.app (.const 6 []) motive) U) V

noncomputable def partialTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero))
    (hV : HasTyT extension 0 Γ V (.sort .zero)) :
    HasTyT extension 0 Γ (partialRec U V)
      (.pi (.const 3 []) (.app (Rcic.Declarative.lift 0 1 motive) (.bvar 0))) := by
  have hR : HasTyT extension 0 Γ (.const 6 []) recType :=
    .const Γ 6 [] recMember rfl rfl rfl
  have h1 := HasTyT.app Γ (.const 6 []) motive _ _ hR (motiveTyped Γ)
  have hU' : HasTyT extension 0 Γ U (.app motive (.const 4 [])) :=
    .conv Γ U (.sort .zero) (.app motive (.const 4 [])) (.succ .zero) hU
      (.symm Γ _ _ _ (betaFirst Γ))
  have hV' : HasTyT extension 0 Γ V (.app motive (.const 5 [])) :=
    .conv Γ V (.sort .zero) (.app motive (.const 5 [])) (.succ .zero) hV
      (.symm Γ _ _ _ (betaSecond Γ))
  have h2 := HasTyT.app Γ _ U _ _ h1 hU'
  exact HasTyT.app Γ _ V _ _ h2 hV'

noncomputable def firstLhsTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero))
    (hV : HasTyT extension 0 Γ V (.sort .zero)) :
    HasTyT extension 0 Γ (iotaLhsOf (firstWitness U V)) (.sort .zero) :=
  .conv Γ _ (.app motive (.const 4 [])) (.sort .zero) (.succ .zero)
    (.app Γ _ (.const 4 []) _ _ (partialTyped Γ U V hU hV) (firstTyped Γ))
    (betaFirst Γ)

noncomputable def secondLhsTyped (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero))
    (hV : HasTyT extension 0 Γ V (.sort .zero)) :
    HasTyT extension 0 Γ (iotaLhsOf (secondWitness U V)) (.sort .zero) :=
  .conv Γ _ (.app motive (.const 5 [])) (.sort .zero) (.succ .zero)
    (.app Γ _ (.const 5 []) _ _ (partialTyped Γ U V hU hV) (secondTyped Γ))
    (betaSecond Γ)

/-- Actual syntax: two legacy iotas and congruence over proof irrelevance.
The target is arbitrary Sort-0 terms; no conversion or index equality is
assumed as an input. -/
noncomputable def propositionConversion (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero))
    (hV : HasTyT extension 0 Γ V (.sort .zero)) :
    ConvT extension 0 Γ U V (.sort .zero) := by
  have hi0 : ConvT extension 0 Γ (iotaLhsOf (firstWitness U V)) U (.sort .zero) :=
    .iota Γ _ _ _ (.of (firstWitness U V)) (firstLhsTyped Γ U V hU hV) hU
  have hi1 : ConvT extension 0 Γ (iotaLhsOf (secondWitness U V)) V (.sort .zero) :=
    .iota Γ _ _ _ (.of (secondWitness U V)) (secondLhsTyped Γ U V hU hV) hV
  have hc : ConvT extension 0 Γ (.const 4 []) (.const 5 []) (.const 3 []) :=
    .irr Γ (.const 3 []) (.const 4 []) (.const 5 [])
      (boolTyped Γ) (firstTyped Γ) (secondTyped Γ)
  have hm : ConvT extension 0 Γ (iotaLhsOf (firstWitness U V))
      (iotaLhsOf (secondWitness U V)) (.sort .zero) :=
    .tyConv Γ _ _ (.app motive (.const 4 [])) (.sort .zero) (.succ .zero)
      (.app Γ (partialRec U V) (partialRec U V) (.const 4 []) (.const 5 [])
        (.const 3 []) (.app (Rcic.Declarative.lift 0 1 motive) (.bvar 0))
        (.refl Γ _ _ (partialTyped Γ U V hU hV)) hc)
      (betaFirst Γ)
  exact .trans Γ U _ V (.sort .zero) (.symm Γ _ _ _ hi0)
    (.trans Γ _ _ _ (.sort .zero) hm hi1)

noncomputable def falseFamilyTyped : HasTyT extension 0 []
    (.app (.const 0 []) (.const 1 [])) (.sort .zero) :=
  .app [] (.const 0 []) (.const 1 []) (.sort .zero) (.sort .zero)
    (.const [] 0 [] PropFamilyKeyAttack.familyMember rfl rfl rfl)
    (.const [] 1 [] PropFamilyKeyAttack.indexMember rfl rfl rfl)

noncomputable def trueFamilyTyped : HasTyT extension 0 []
    (.app (.const 0 []) (.const 2 [])) (.sort .zero) :=
  .app [] (.const 0 []) (.const 2 []) (.sort .zero) (.sort .zero)
    (.const [] 0 [] PropFamilyKeyAttack.familyMember rfl rfl rfl)
    (.const [] 2 [] PropFamilyKeyAttack.indexMember rfl rfl rfl)

/-- A concrete family-code conversion at two syntactically distinct indices. -/
noncomputable def familyConversion : ConvT extension 0 []
    (.app (.const 0 []) (.const 1 [])) (.app (.const 0 []) (.const 2 [])) (.sort .zero) :=
  propositionConversion [] _ _ falseFamilyTyped trueFamilyTyped

/-- The syntax component is inhabited independently of Premises4. -/
theorem syntax_witness : Nonempty (ConvT extension 0 []
    (.app (.const 0 []) (.const 1 [])) (.app (.const 0 []) (.const 2 [])) (.sort .zero)) :=
  ⟨familyConversion⟩

theorem syntax_nonrefutable (P : Premises4) :
    ¬ (Nonempty (ConvT extension 0 []
      (.app (.const 0 []) (.const 1 [])) (.app (.const 0 []) (.const 2 [])) (.sort .zero)) →
      (Premises4 → False)) :=
  fun h => h syntax_witness P

end Rcic.F3.PSet.PropIndexConversionAttack

#print axioms Rcic.F3.PSet.PropIndexConversionAttack.propositionConversion
#print axioms Rcic.F3.PSet.PropIndexConversionAttack.familyConversion
#print axioms Rcic.F3.PSet.PropIndexConversionAttack.syntax_witness
#print axioms Rcic.F3.PSet.PropIndexConversionAttack.syntax_nonrefutable
