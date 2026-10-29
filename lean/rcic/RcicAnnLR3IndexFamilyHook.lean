import rcic.RcicAnnLR3EqTargetIota
import rcic.RcicAnnLR3EnvironmentTelescopeInsertion

/-!
# An index-retaining family hook for the Target

Under `F := iotaHook E` an inductive family evaluates to its bare constant,
so a family application such as `Eq A a b` is an untagged neutral spine: it
is not a sort member, so no code system can decode it as a type. The
landed telescope hook (`NativeTelescopeValues`) instead returns one tagged
neutral type for all arguments, so `Eq A a b` and `Eq A a a` would get the
same image. Image coherence would then force an index-free Eq relation,
which breaks J's retyping (`EqTracer.index_free_mutant`).

`indexHook E` sends an inductive family whose type is a sort-ending
telescope of depth `n` to `familyTerm n k r`: `n` binders, then the
level-tagged neutral application of the family to all of them. Constructors
and recursors still go to `iotaTerm E r`.

- `familyTerm_apply`: applied to `n` bottom-carrying arguments, the term is
  the level-`k` tagged neutral application of the family to them.
- `indexHook_target_conv_iota` / `_structIota`: arm 17 (and the struct arm)
  on the Target `annSemantics C (view E) (hook hE (indexHook E))`, under the
  same side conditions as with `iotaHook`.
- For the admitted AnySort Eq group, `eq_type_image`: the Target image of
  `Eq Prop a b` is `taggedValue (some 0)` of the neutral application of
  family `63` to the images of `Prop`, `a` and `b`. It is a level-zero sort
  member and a defined type (`eq_type_level`, `eq_type_defined`), and it
  keeps the index: the image of `b` is observed inside it
  (`eq_type_retains_index`). Arm 17 holds there (`eq_index_conv_iota`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IndexFamilyHook

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open IotaRecursor AdmissionUniverseReadback EqTargetIota

/-- `n` binders, then the level-tagged neutral application of family `r` to
them. -/
def familyTerm (n : Nat) (k : Option Nat) (r : Nat) : Expr Nat :=
  lams n (taggedTerm k (foldApps (.const r []) (argVars 0 n)))

def indexHook (E : ResolvedEnvA) : EnvironmentEval.FamilySyntax := fun ν r ls m =>
  match m.mclass with
  | .inductiveM =>
      match EnvironmentTelescopeInsertion.sortTail m.mtypeA with
      | some (n, l) => familyTerm n (eval ν (instLevel ls l)) r
      | none => .const r []
  | _ => iotaTerm E r

theorem familyTerm_apply (n : Nat) (k : Option Nat) (r : Nat) (ρ : EnvI) (xs : List Value)
    (hn : xs.length = n) (hb : ∀ x ∈ xs, x .bot) :
    ValueEq (applyAll (denI ρ (familyTerm n k r)) xs)
      (InductiveCodes.taggedValue k (applyAll (NeutralPER.neutralAtom r) xs)) := by
  rw [familyTerm, lams_apply n _ ρ xs hn]
  refine (InductiveCodes.taggedValue_denI _ k _).symm.trans ?_
  rw [foldApps_denI]
  have hargs : (argVars 0 n).map (denI (pushAll xs ρ)) = xs := by
    have h := argVars_denI xs ρ [] hb
    rw [← hn]
    exact h
  rw [hargs]
  have hc : denI (pushAll xs ρ) (.const r []) = NeutralPER.neutralAtom r :=
    NeutralCodes.valueEq_eq (FunctionEval.constant_environment _ _ r [])
  rw [hc]
  exact ValueEq.refl _

theorem indexHook_ctorRec (E : ResolvedEnvA) :
    ∀ ν r ls (m : CheckedMemberA), E.members r = some m →
      (m.mclass = .constructorM ∨ m.mclass = .recursorM) → indexHook E ν r ls m = iotaTerm E r := by
  intro ν r ls m _ hc
  rcases hc with hc | hc <;> simp [indexHook, hc]

theorem indexHook_target_conv_iota (C : CodeSystem) {E : ResolvedEnvA}
    (hE : EnvWfA (iotaIfaceA E) E) (hpi : CtorRecPi E) (harity : FirstOrderArity E) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view E) (hook hE (indexHook E)))
      E (iotaIfaceA E) n :=
  conv_iota_supplied C (routes_target_of hE hpi _ (indexHook_ctorRec E)) harity n

theorem indexHook_target_conv_structIota (C : CodeSystem) {E : ResolvedEnvA}
    (hE : EnvWfA (iotaIfaceA E) E) (hpi : CtorRecPi E) (harity : FirstOrderArity E) (n : Nat) :
    PairedArms.Conv_structIota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view E) (hook hE (indexHook E)))
      E (iotaIfaceA E) n :=
  conv_structIota_supplied C (routes_target_of hE hpi _ (indexHook_ctorRec E)) harity n

/-! ## The AnySort Eq group -/

section Eq

open EqLargeFixture

theorem eq_index_conv_iota (C : CodeSystem) (hE : EnvWfA (iotaIfaceA env) env) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view env) (hook hE (indexHook env)))
      env (iotaIfaceA env) n :=
  indexHook_target_conv_iota C hE eq_ctorRecPi EqTracer.eq_firstOrderArity n

theorem fam_sortTail : EnvironmentTelescopeInsertion.sortTail famTy = some (3, .zero) := by
  decide

theorem eq_const_image (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation)
    (ρ : EnvI) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ
      (.const 63 []) = denI ρ (familyTerm 3 (some 0) 63) := by
  have hm : env.members 63 = some fam := rfl
  have hbody : EnvironmentEval.definitionBody (SemanticMemberEval.view env) 63 [] = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, fam, transparent]
  have hread : readAdmitted hE ν (instantiateLevelsA [] famTy) = none :=
    read_pi_none hE ν _ _ _ _
  have hv : (SemanticMemberEval.view env).members 63 = some (SemanticMemberEval.route fam) := by
    simp [SemanticMemberEval.view, hm]
  have hrigid : EnvironmentEval.rigidTerm (SemanticMemberEval.view env) (hook hE (indexHook env))
      ν 63 [] = familyTerm 3 (some 0) 63 := by
    have hc : fam.mclass = .inductiveM := rfl
    have ht : fam.mtypeA = famTy := rfl
    simp [EnvironmentEval.rigidTerm, hv, SemanticMemberEval.route, hc, hook, hm,
      indexHook, ht, fam_sortTail]
    rw [hread]
    rfl
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_rigid hbody _ ν ρ), hrigid]

/-- The Target image of `Eq Prop a b`: the level-zero tagged neutral
application of the family to the images of its arguments. -/
theorem eq_type_image (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation)
    (ρ : EnvI) (a b : ExprA) :
    ValueEq
      (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ (eqAt a b))
      (InductiveCodes.taggedValue (some 0)
        (applyAll (NeutralPER.neutralAtom 63)
          [EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ
              (.sort .zero),
            EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ a,
            EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ b])) := by
  show ValueEq (EnvironmentEval.denote _ _ ν ρ (foldAppsA (.const 63 []) [.sort .zero, a, b])) _
  rw [denote_foldAppsA, eq_const_image hE ν ρ]
  exact familyTerm_apply 3 (some 0) 63 ρ _ rfl (by
    intro x hx
    simp only [List.map, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact EnvironmentEval.denote_bot _ _ _ _ _)

theorem eq_type_level (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation)
    (ρ : EnvI) (a b : ExprA) :
    SortMember (some 0)
      (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ (eqAt a b)) :=
  sortMember_congr (eq_type_image hE ν ρ a b).symm (TypeZeroTowerProbe.tagged_level _ _)

theorem eq_type_defined (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation)
    (ρ : EnvI) (a b : ExprA) :
    TypeDefined
      (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ (eqAt a b)) :=
  typeDefined_congr (eq_type_image hE ν ρ a b).symm
    ⟨some 0, .bot, (InductiveCodes.taggedValue_full _ _ _).mpr (Or.inl rfl)⟩

/-- The index is retained: every observation of the image of `b` occurs in
the image of `Eq Prop a b`, as the last argument of the tagged payload. -/
theorem eq_type_retains_index (hE : EnvWfA (iotaIfaceA env) env)
    (ν : Valuation) (ρ : EnvI) (a b : ExprA) (u : CptI)
    (hu : EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ b u) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE (indexHook env)) ν ρ (eqAt a b)
      (.spine 10 [.spine (levelRef (some 0)) [], .spine 63 [.bot, .bot, u]]) := by
  refine ((eq_type_image hE ν ρ a b) _).mpr ?_
  refine (InductiveCodes.taggedValue_full _ _ _).mpr ?_
  show NeutralPi.applyValue (NeutralPi.applyValue (NeutralPi.applyValue
    (NeutralPER.neutralAtom 63) _) _) _ (.spine 63 ([.bot, .bot] ++ [u]))
  refine Or.inr (Or.inr ⟨63, [.bot, .bot], u, rfl, ?_, hu⟩)
  refine Or.inr (Or.inr ⟨63, [.bot], .bot, rfl, ?_, EnvironmentEval.denote_bot _ _ _ _ _⟩)
  exact Or.inr (Or.inr ⟨63, [], .bot, rfl, NeutralPER.neutralAtom_observed 63,
    EnvironmentEval.denote_bot _ _ _ _ _⟩)

end Eq

end Rcic.Declarative.Ann.LR3.IndexFamilyHook
