import rcic.RcicAnnLR3LevelFundamental

/-!
# Sort membership at generic environments (level model)

The level Fundamental (`LevelFundamental.fundamental`) relates a type's
images by the reading of its universe, and the universe relates images of
closed codes. Hence:

- `sort_member_of_typed`: in every realizing environment, a `TypedL` type
  of universe level `k` has a defined image that is a sort member of level
  `k`;
- `genericEnv` / `genericEnv_gr`: every well-kinded context has a generic
  realizing environment, with type variables at the named neutral type
  (`named13`) and term variables at reflections of their types' images
  (CR3, `LevelGirardSystem.el_reflect`);
- `generic_sort_member`: hence sort membership at the generic environment.

Instance `eq_generic_sort_member`: in the AnySort Eq environment with the
K-like hook, in the context `[X : Prop]`, an Eq recursor call whose minor is
`X` has a level-zero sort-member image at the generic environment, at every
major. This is the large-elimination case that a neutral major leaves stuck
under the Scott hook (`EqReflectionChoice.neutral_major_not_sort`).

The level model has no empty type, so this route is not obstructed by G1.
Not claimed: the same for `HasTyA` derivations. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelGeneric

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open CandidateTowerProbe (REnv CEnv rcons ccons Sat SatFor Ntr)
open CandidateCodeSystem (σ0 ρ0 botRel botRel_sat botRel_satFor)
open LevelGirard LevelGirardSystem LevelSubstitution LevelReader LevelFundamental

/-- Sort membership at every realizing environment. -/
theorem sort_member_of_typed {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    (hK : KLike E H) {ν : Valuation} {Γ : List Entry} {T : ExprA} {k : Nat}
    (h : TypedL E H ν Γ T (.univ k)) (s : EnvI) (ρ : CEnv) (hρ : ∀ i, Sat (ρ i))
    (hG : GRL Γ s s ρ) :
    SortMember (some k) (EnvironmentEval.denote E H ν s T) ∧
      TypeDefined (EnvironmentEval.denote E H ν s T) := by
  obtain ⟨c, _, hc, _, _, hV, _⟩ := fundamental hK h s s ρ hρ hG
  have hl := nonvar_level σ0 c [] hc.1 (wfc_nonvar c hc)
  exact ⟨sortMember_congr hV.symm hl.1, typeDefined_congr hV.symm hl.2⟩

/-- Well-kinded contexts: each term variable's type is kinded by the kinds
of the variables before it. -/
def CtxOK : List Entry → Prop
  | [] => True
  | .ty _ :: Γ => CtxOK Γ
  | .tm c :: Γ => Kinded (kinds Γ) c ∧ CtxOK Γ

/-- The reflection used for a term variable. -/
def genericAtom : Value := NeutralPER.neutralAtom 12

theorem ntr_genericAtom : Ntr genericAtom := CandidateReflection.ntr_reflectAtom 0

/-- The generic raw environment of a context. -/
def genericEnv : List Entry → EnvI
  | [] => fun _ => bottom
  | .ty k :: Γ => rcons (image σ0 (named13 k)) (genericEnv Γ)
  | .tm c :: Γ => rcons (ObservationReflection.reflV (image σ0 c) genericAtom) (genericEnv Γ)

/-- Every well-kinded context is realized by its generic environment, with
the bottom candidate everywhere. -/
theorem genericEnv_gr : (Γ : List Entry) → CtxOK Γ → GRL Γ (genericEnv Γ) (genericEnv Γ) ρ0
  | [], _ => trivial
  | .ty k :: Γ, hΓ =>
      ⟨⟨named13 k, named13 k, named13_wfc k, named13_wfc k, twin_refl _, ValueEq.refl _,
        ValueEq.refl _⟩, botRel_satFor _ _, genericEnv_gr Γ hΓ⟩
  | .tm c :: Γ, hΓ => by
      refine ⟨?_, genericEnv_gr Γ hΓ.2⟩
      exact el_reflect c (kinds Γ) σ0 σ0 ρ0 hΓ.1 CandidateCodeSystem.sat0 (fun _ => rfl)
        (fun i _ _ => botRel_satFor _ _) _ _ ntr_genericAtom ntr_genericAtom

/-- Sort membership at the generic environment. -/
theorem generic_sort_member {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    (hK : KLike E H) {ν : Valuation} {Γ : List Entry} (hΓ : CtxOK Γ) {T : ExprA} {k : Nat}
    (h : TypedL E H ν Γ T (.univ k)) :
    SortMember (some k) (EnvironmentEval.denote E H ν (genericEnv Γ) T) ∧
      TypeDefined (EnvironmentEval.denote E H ν (genericEnv Γ) T) :=
  sort_member_of_typed hK h _ ρ0 (fun _ => botRel_sat) (genericEnv_gr Γ hΓ)

/-- In `[X : Prop]`, an Eq recursor call with minor `X` is a level-zero
sort member at the generic environment, at every major, with the K-like
hook. -/
theorem eq_generic_sort_member (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env)
    (ν : Valuation) (u : Level) (A a P b e : ExprA) :
    SortMember (some 0)
        (EnvironmentEval.denote (SemanticMemberEval.view EqLargeFixture.env)
          (AdmissionUniverseReadback.hook hE EqKLikeHook.eqKHook) ν (genericEnv [.ty 0])
          (EqReflectionChoice.jcall u A a P (.bvar 0) b e)) ∧
      TypeDefined
        (EnvironmentEval.denote (SemanticMemberEval.view EqLargeFixture.env)
          (AdmissionUniverseReadback.hook hE EqKLikeHook.eqKHook) ν (genericEnv [.ty 0])
          (EqReflectionChoice.jcall u A a P (.bvar 0) b e)) :=
  generic_sort_member (eqK_klike hE) (Γ := [.ty 0]) trivial
    (.jK (cR := .univ 0) (.tyVar rfl) (twin_refl _) trivial)

end Rcic.Declarative.Ann.LR3.LevelGeneric
