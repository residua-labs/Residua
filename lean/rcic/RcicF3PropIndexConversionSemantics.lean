import rcic.RcicF3PropIndexConversionAttack

/-!
# Hereditarily sound family-code conversion in the bad extension

The unadmitted Bool recursor below selects its first minor. This is a
member of its stored type because all Bool proofs are erased. At the two
specific family-code minors both values coincide, so both specialized
iota conversions are semantically sound, as are all their hereditary
typing and conversion subnodes. The distinct data indices are retained.

This module does not assert an admitted environment for the bad extension
or refute full IotaAt. The final admitted target recursor redex and its
installed-table equations remain separate obligations.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000


namespace Rcic.F3.PSet.PropIndexConversionSemantics
open Rcic.Declarative Rcic.Model.PS
open PropEvalSafeIndex (witnessTable falseCode trueCode)
open PropFamilyKeyAttack (valuation bound familyMember indexMember)
open PropIndexConversionAttack

noncomputable def baseTable (P : Premises4) : Nat → List Nat → PSet.{4}
  | 3, _ => trueCode
  | r, vs => PropFamilyKeyAttack.table P r vs

noncomputable def recValue (P : Premises4) : PSet.{4} :=
  piLam (mkM P (baseTable P)) valuation (fun ρ => ρ 2) ρ0 recType

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4}
  | 6, _ => recValue P
  | r, vs => baseTable P r vs

noncomputable abbrev model (P : Premises4) : Interp.{4} := mkM P (table P)

theorem bool_proof (P : Premises4) : pempty ∈ Ed (model P) (table P 3 []) :=
  mem_congr_right (ed_tyv (model P) (dich_tv True)).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem bool_erased (P : Premises4) {z : PSet.{4}}
    (hz : z ∈ Ed (model P) (table P 3 [])) : Equiv z pempty :=
  (mem_tv.mp (mem_congr_right (ed_tyv (model P) (dich_tv True)) hz)).2

/-- The bad recursor has actual stored-type membership; no iota law is
used here. Its output is the first minor, transported along erased proofs. -/
theorem rec_mem (P : Premises4) :
    recValue P ∈ Ed (model P) (den (model P) valuation ρ0 recType) := by
  change piLam (model P) valuation (fun ρ => ρ 2) ρ0 recType ∈ _
  apply piLam_mem (model P) valuation (fun _ _ h => h 2) recType ρ0
  intro mo hmo x hx y hy z hz
  change x ∈ Ed (model P) (fapp mo z)
  change x ∈ Ed (model P) (fapp mo pempty) at hx
  exact mem_congr_right (ed_congr (model P)
    (fapp_congr Equiv.rfl (bool_erased P hz).symm)) hx

private theorem app_hsound (P : Premises4) {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT extension 0 Γ f (.pi A B)) (ha : HasTyT extension 0 Γ a A)
    (sf : HSoundT (model P) valuation hf) (sa : HSoundT (model P) valuation ha) :
    HSoundT (model P) valuation (.app Γ f a A B hf ha) := by
  refine ⟨?_, sf, sa⟩
  intro ρ hρ
  change fapp (den (model P) valuation ρ f) (den (model P) valuation ρ a) ∈
    Ed (model P) (den (model P) valuation ρ (instantiate0 a B))
  rw [den_inst0]
  exact app_mem (model P) (den_resp (model P) valuation ρ B)
    (sf.root ρ hρ) (sa.root ρ hρ)

private theorem conv_hsound (P : Premises4) {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (ht : HasTyT extension 0 Γ e A) (hc : ConvT extension 0 Γ A B (.sort u))
    (st : HSoundT (model P) valuation ht) (sc : HSoundC (model P) valuation hc) :
    HSoundT (model P) valuation (.conv Γ e A B u ht hc) :=
  ⟨fun ρ hρ => mem_congr_right (ed_congr (model P) (sc.root ρ hρ).1)
    (st.root ρ hρ), st, sc⟩

private theorem refl_hsound (P : Premises4) {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT extension 0 Γ e A) (s : HSoundT (model P) valuation h) :
    HSoundC (model P) valuation (.refl Γ e A h) :=
  ⟨fun ρ hρ => ⟨Equiv.rfl, s.root ρ hρ⟩, s⟩

private theorem symm_hsound (P : Premises4) {Γ : LCtx} {a b A : Expr Nat}
    (h : ConvT extension 0 Γ a b A) (s : HSoundC (model P) valuation h) :
    HSoundC (model P) valuation (.symm Γ a b A h) :=
  ⟨fun ρ hρ => ⟨(s.root ρ hρ).1.symm,
    mem_congr_left (s.root ρ hρ).1 (s.root ρ hρ).2⟩, s⟩

private theorem trans_hsound (P : Premises4) {Γ : LCtx} {a b c A : Expr Nat}
    (h1 : ConvT extension 0 Γ a b A) (h2 : ConvT extension 0 Γ b c A)
    (s1 : HSoundC (model P) valuation h1) (s2 : HSoundC (model P) valuation h2) :
    HSoundC (model P) valuation (.trans Γ a b c A h1 h2) :=
  ⟨fun ρ hρ => ⟨(s1.root ρ hρ).1.trans (s2.root ρ hρ).1,
    (s1.root ρ hρ).2⟩, s1, s2⟩

private theorem appConv_hsound (P : Premises4) {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : ConvT extension 0 Γ f g (.pi A B)) (h2 : ConvT extension 0 Γ a b A)
    (s1 : HSoundC (model P) valuation h1) (s2 : HSoundC (model P) valuation h2) :
    HSoundC (model P) valuation (.app Γ f g a b A B h1 h2) := by
  refine ⟨?_, s1, s2⟩
  intro ρ hρ
  refine ⟨fapp_congr (s1.root ρ hρ).1 (s2.root ρ hρ).1, ?_⟩
  change fapp (den (model P) valuation ρ f) (den (model P) valuation ρ a) ∈
    Ed (model P) (den (model P) valuation ρ (instantiate0 a B))
  rw [den_inst0]
  exact app_mem (model P) (den_resp (model P) valuation ρ B)
    (s1.root ρ hρ).2 (s2.root ρ hρ).2

private theorem tyConv_hsound (P : Premises4) {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
    (h : ConvT extension 0 Γ a b A) (hA : ConvT extension 0 Γ A A' (.sort u))
    (s : HSoundC (model P) valuation h) (sA : HSoundC (model P) valuation hA) :
    HSoundC (model P) valuation (.tyConv Γ a b A A' u h hA) :=
  ⟨fun ρ hρ => ⟨(s.root ρ hρ).1,
    mem_congr_right (ed_congr (model P) (sA.root ρ hρ).1) (s.root ρ hρ).2⟩, s, sA⟩

theorem bool_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) valuation (boolTyped Γ) :=
  fun _ _ => (PropEvalSafeIndex.true_fits P valuation).1

theorem first_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) valuation (firstTyped Γ) := fun _ _ => bool_proof P

theorem second_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) valuation (secondTyped Γ) := fun _ _ => bool_proof P

theorem sort_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) valuation (HasTyT.sort (E := extension) (n := 0) Γ .zero) :=
  fun _ _ => sort_mem (P.good _ rfl) (by decide : 1 ≤ 4)

theorem motive_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) valuation (motiveTyped Γ) := by
  refine ⟨?_, bool_hsound P Γ, sort_hsound P (.assumption (.const 3 []) :: Γ)⟩
  intro ρ hρ
  exact lam_mem (model P)
    (den_resp (model P) valuation ρ (.sort .zero))
    (den_resp (model P) valuation ρ (.sort (.succ .zero)))
    (fun x hx => sort_mem (P.good _ rfl) (by decide : 1 ≤ 4))

theorem betaFirst_hsound (P : Premises4) (Γ : LCtx) :
    HSoundC (model P) valuation (betaFirst Γ) := by
  refine ⟨?_, bool_hsound P Γ, sort_hsound P (.assumption (.const 3 []) :: Γ), first_hsound P Γ⟩
  intro ρ hρ
  refine ⟨beta_val (model P) (fun _ _ _ => Equiv.rfl) (bool_proof P), ?_⟩
  exact app_mem (model P) (den_resp (model P) valuation ρ (.sort (.succ .zero)))
    ((motive_hsound P Γ).root ρ hρ) (bool_proof P)

theorem betaSecond_hsound (P : Premises4) (Γ : LCtx) :
    HSoundC (model P) valuation (betaSecond Γ) := by
  refine ⟨?_, bool_hsound P Γ, sort_hsound P (.assumption (.const 3 []) :: Γ), second_hsound P Γ⟩
  intro ρ hρ
  refine ⟨beta_val (model P) (fun _ _ _ => Equiv.rfl) (bool_proof P), ?_⟩
  exact app_mem (model P) (den_resp (model P) valuation ρ (.sort (.succ .zero)))
    ((motive_hsound P Γ).root ρ hρ) (bool_proof P)

theorem partial_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV) :
    HSoundT (model P) valuation (partialTyped Γ U V hU hV) := by
  dsimp only [partialTyped]
  apply app_hsound
  · apply app_hsound
    · apply app_hsound
      · intro ρ _
        exact rec_mem P
      · exact motive_hsound P Γ
    · exact conv_hsound P hU _ sU (symm_hsound P _ (betaFirst_hsound P Γ))
  · exact conv_hsound P hV _ sV (symm_hsound P _ (betaSecond_hsound P Γ))

theorem firstLhs_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV) :
    HSoundT (model P) valuation (firstLhsTyped Γ U V hU hV) :=
  conv_hsound P _ _
    (app_hsound P _ _ (partial_hsound P Γ U V hU hV sU sV) (first_hsound P Γ))
    (betaFirst_hsound P Γ)

theorem secondLhs_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV) :
    HSoundT (model P) valuation (secondLhsTyped Γ U V hU hV) :=
  conv_hsound P _ _
    (app_hsound P _ _ (partial_hsound P Γ U V hU hV sU sV) (second_hsound P Γ))
    (betaSecond_hsound P Γ)

noncomputable def domains : List (Expr Nat) :=
  [.pi (.const 3 []) (.sort (.succ .zero)),
    .app (.bvar 0) (.const 4 []), .app (.bvar 1) (.const 5 []), .const 3 []]

/-- Actual application of the stored abstraction; both constructor values
are literally the same proof value, so both return the first minor. -/
theorem application_first (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV)
    (ρ : Nat → PSet.{4}) (hρ : Fits (model P) valuation Γ ρ) :
    Equiv (fapps (recValue P)
      [den (model P) valuation ρ motive, den (model P) valuation ρ U,
        den (model P) valuation ρ V, pempty]) (den (model P) valuation ρ U) := by
  have hx : den (model P) valuation ρ U ∈ Ed (model P)
      (fapp (den (model P) valuation ρ motive) pempty) :=
    mem_congr_right (ed_congr (model P) ((betaFirst_hsound P Γ).root ρ hρ).1).symm
      (sU.root ρ hρ)
  have hy : den (model P) valuation ρ V ∈ Ed (model P)
      (fapp (den (model P) valuation ρ motive) pempty) :=
    mem_congr_right (ed_congr (model P) ((betaSecond_hsound P Γ).root ρ hρ).1).symm
      (sV.root ρ hρ)
  have hfit : TelFits (model P) valuation domains ρ0
      [den (model P) valuation ρ motive, den (model P) valuation ρ U,
        den (model P) valuation ρ V, pempty] :=
    ⟨(motive_hsound P Γ).root ρ hρ, hx, hy, bool_proof P, True.intro⟩
  exact fapps_piLam (model P) valuation (fun _ _ h => h 2)
    (.app (.bvar 3) (.bvar 0)) domains ρ0 _ hfit

theorem firstLhs_value (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV)
    (ρ : Nat → PSet.{4}) (hρ : Fits (model P) valuation Γ ρ) :
    Equiv (den (model P) valuation ρ (iotaLhsOf (firstWitness U V)))
      (den (model P) valuation ρ U) :=
  application_first P Γ U V hU hV sU sV ρ hρ

theorem secondLhs_value (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV)
    (ρ : Nat → PSet.{4}) (hρ : Fits (model P) valuation Γ ρ) :
    Equiv (den (model P) valuation ρ (iotaLhsOf (secondWitness U V)))
      (den (model P) valuation ρ U) :=
  application_first P Γ U V hU hV sU sV ρ hρ

/-- The only semantic relation needed is between the proposition CODE
minors. No relation between their indices is accepted or inferred. -/
theorem propositionConversion_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) valuation hU) (sV : HSoundT (model P) valuation hV)
    (hUV : ∀ ρ, Fits (model P) valuation Γ ρ →
      Equiv (den (model P) valuation ρ U) (den (model P) valuation ρ V)) :
    HSoundC (model P) valuation (propositionConversion Γ U V hU hV) := by
  dsimp only [propositionConversion]
  apply trans_hsound
  · apply symm_hsound
    exact ⟨fun ρ hρ => ⟨firstLhs_value P Γ U V hU hV sU sV ρ hρ,
      (firstLhs_hsound P Γ U V hU hV sU sV).root ρ hρ⟩,
      firstLhs_hsound P Γ U V hU hV sU sV, sU⟩
  · apply trans_hsound
    · apply tyConv_hsound
      · apply appConv_hsound
        · exact refl_hsound P _ (partial_hsound P Γ U V hU hV sU sV)
        · exact ⟨fun _ _ => ⟨Equiv.rfl, bool_proof P⟩,
            bool_hsound P Γ, first_hsound P Γ, second_hsound P Γ⟩
      · exact betaFirst_hsound P Γ
    · exact ⟨fun ρ hρ => ⟨(secondLhs_value P Γ U V hU hV sU sV ρ hρ).trans (hUV ρ hρ),
        (secondLhs_hsound P Γ U V hU hV sU sV).root ρ hρ⟩,
        secondLhs_hsound P Γ U V hU hV sU sV, sV⟩

theorem falseFamily_hsound (P : Premises4) :
    HSoundT (model P) valuation falseFamilyTyped :=
  app_hsound P _ _ (fun _ _ => PropFamilyKeyAttack.family_mem P)
    (fun _ _ => (PropEvalSafeIndex.false_fits P valuation).1)

theorem trueFamily_hsound (P : Premises4) :
    HSoundT (model P) valuation trueFamilyTyped :=
  app_hsound P _ _ (fun _ _ => PropFamilyKeyAttack.family_mem P)
    (fun _ _ => (PropEvalSafeIndex.true_fits P valuation).1)

/-- Actual code equality is produced by the concrete family interpretation. -/
theorem family_codes_equal (P : Premises4) (ρ : Nat → PSet.{4}) :
    Equiv (den (model P) valuation ρ (.app (.const 0 []) (.const 1 [])))
      (den (model P) valuation ρ (.app (.const 0 []) (.const 2 []))) :=
  (PropFamilyKeyAttack.at_false P).trans (PropFamilyKeyAttack.at_true P).symm

theorem familyConversion_hsound (P : Premises4) :
    HSoundC (model P) valuation familyConversion :=
  propositionConversion_hsound P [] _ _ falseFamilyTyped trueFamilyTyped
    (falseFamily_hsound P) (trueFamily_hsound P) (fun ρ _ => family_codes_equal P ρ)

private theorem nil_levels (r : Nat) : LevelsOK valuation (bound r) [] :=
  fun l h => (List.not_mem_nil l h).elim

theorem motive_bound (Γ : LCtx) : LOKt valuation 4 bound (motiveTyped Γ) :=
  ⟨nil_levels 3, by change 1 ≤ 4; decide⟩

theorem betaFirst_bound (Γ : LCtx) : LOKc valuation 4 bound (betaFirst Γ) :=
  ⟨nil_levels 3, by change 1 ≤ 4; decide, nil_levels 4⟩

theorem betaSecond_bound (Γ : LCtx) : LOKc valuation 4 bound (betaSecond Γ) :=
  ⟨nil_levels 3, by change 1 ≤ 4; decide, nil_levels 5⟩

theorem partial_bound (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (lU : LOKt valuation 4 bound hU) (lV : LOKt valuation 4 bound hV) :
    LOKt valuation 4 bound (partialTyped Γ U V hU hV) :=
  ⟨⟨⟨nil_levels 6, motive_bound Γ⟩, ⟨lU, betaFirst_bound Γ⟩⟩,
    ⟨lV, betaSecond_bound Γ⟩⟩

theorem firstLhs_bound (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (lU : LOKt valuation 4 bound hU) (lV : LOKt valuation 4 bound hV) :
    LOKt valuation 4 bound (firstLhsTyped Γ U V hU hV) :=
  ⟨⟨partial_bound Γ U V hU hV lU lV, nil_levels 4⟩, betaFirst_bound Γ⟩

theorem secondLhs_bound (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (lU : LOKt valuation 4 bound hU) (lV : LOKt valuation 4 bound hV) :
    LOKt valuation 4 bound (secondLhsTyped Γ U V hU hV) :=
  ⟨⟨partial_bound Γ U V hU hV lU lV, nil_levels 5⟩, betaSecond_bound Γ⟩

theorem propositionConversion_bound (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (lU : LOKt valuation 4 bound hU) (lV : LOKt valuation 4 bound hV) :
    LOKc valuation 4 bound (propositionConversion Γ U V hU hV) :=
  ⟨⟨firstLhs_bound Γ U V hU hV lU lV, lU⟩,
    ⟨⟨⟨partial_bound Γ U V hU hV lU lV,
      ⟨nil_levels 3, nil_levels 4, nil_levels 5⟩⟩, betaFirst_bound Γ⟩,
      ⟨secondLhs_bound Γ U V hU hV lU lV, lV⟩⟩⟩

theorem familyConversion_bound : LOKc valuation 4 bound familyConversion :=
  propositionConversion_bound [] _ _ falseFamilyTyped trueFamilyTyped
    ⟨nil_levels 0, nil_levels 1⟩ ⟨nil_levels 0, nil_levels 2⟩

theorem bounded_good (P : Premises4) :
    ∃ Lv : Nat → PSet.{4} → Prop, Good (model P) 4 Lv :=
  ⟨_, P.good _ rfl⟩

noncomputable def Witness (P : Premises4) : Prop :=
  HSoundC (model P) valuation familyConversion ∧
  LOKc valuation 4 bound familyConversion ∧
  (∃ Lv : Nat → PSet.{4} → Prop, Good (model P) 4 Lv) ∧
  PiIndex.key [falseCode] ≠ PiIndex.key [trueCode]

theorem component_witness (P : Premises4) : Witness P :=
  ⟨familyConversion_hsound P, familyConversion_bound, bounded_good P,
    PropFamilyKeyAttack.unequal_keys P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropIndexConversionSemantics

#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.rec_mem
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.application_first
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.propositionConversion_hsound
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.familyConversion_hsound
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.familyConversion_bound
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.bounded_good
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.component_witness
#print axioms Rcic.F3.PSet.PropIndexConversionSemantics.component_nonrefutable
