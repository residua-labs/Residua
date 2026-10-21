import rcic.RcicIARecMotive
import rcic.ScmSrcGroupsEnvWfT
import rcic.RcicTypedGroupPinsList
import rcic.RcicTypedGroupPinsVec
import rcic.RcicTypedEnvEntry

/-!
# IA-rec segment A: pins at real recursor cells, a second instrument, and a tooth

`IA017T_motive_well_formed` and `IA021T_tail_typed` instantiated at admitted recursor cells of real
fixtures, each with the cell's own `FamilyTypedT` (the K3c / M3-e leaves) and the prefix's closedness
read off the `EnvWfT` environment after the recursor:

* srcEnvG slot 128, `recNEL` (family `NEL` 125, two indices, `PropOnly`, arity 0);
* srcEnvG slot 108, `recBCT` (family `BCT` 106, no index, `AnySort`, arity 1: the family's typings
  move from arity 0 by `hasTyT_levelMono`);
* `listGroupU` (one parameter, universe-polymorphic family, `AnySort`, arity 2);
* `vecGroupU` (one parameter and one index, `AnySort`).

Second instrument (`*_checker`): the conversion checker `sortTyAtC` (`ScmSrcGroupsEnvWfTAux`),
evaluated by the kernel, types the same motive type in the same context and returns exactly the sort
`motiveSortT` the theorem predicts. That equation could fail; it does not.

Tooth (`tooth_*`): `policyMotiveTypeOffByOne` is 05 §11's motive with its family application reading
the locals one binder too far out (the de Bruijn slip GM-IND-004 names for minors, here in the
motive). At NEL, List and Vec the checker refuses it (`= false`). At BCT there is no local to slip.

`closure_claim` 0.
-/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192

namespace Rcic.Declarative

/-- the mutant: 05 §11's motive type with the family application's locals lifted by one. -/
def policyMotiveTypeOffByOne {E : ResolvedEnv} (v : PolicyFamilyView E) (p : EliminationPolicy) :
    Expr Nat :=
  policyPi v.indices
    (.pi (foldApps (.const v.ref (policyFamilyLevels v))
        ((policyLocals (v.parameters.length + v.indices.length)).map (lift 0 1)))
      (.sort (policyMotiveLevel v.member.arity p)))

/-! ## srcEnvG slot 128: `recNEL` (indexed, `PropOnly`) -/

theorem envClosed_envPre128 : EnvClosed (envPre 128) := by
  have h : envPre 129 = extendEnv (envPre 128) 128 recNEL := by
    rw [envPre_succ (by decide)]; rfl
  exact envClosed_of_extend_fresh (h ▸ envClosed_of_envWfT wft129)
    (Option.isNone_iff_eq_none.mp freshB128)

theorem famTyped128 : FamilyTypedT dRec128.1.family := famTypedT_of (fuel := 96) _ famB128

/-- PIN (IA-017T, NEL): the motive of NEL's admitted recursor is well formed. -/
theorem pin_IA017T_NEL :
    Nonempty (HasTyT (envPre 128) recNEL.arity
        (policyPrefixContext dRec128.1.family.parameters dRec128.1.family.parameters.length)
        (policyMotiveType dRec128.1.family dRec128.1.policy)
        (.sort (motiveSortT dRec128.1.family dRec128.1.policy))) ∧
      levelBounded recNEL.arity (policyMotiveLevel dRec128.1.family.member.arity dRec128.1.policy) = true ∧
      ∃ rest, recNEL.mtype = policyPi dRec128.1.family.parameters
        (.pi (policyMotiveType dRec128.1.family dRec128.1.policy) rest) :=
  IA017T_motive_well_formed dRec128.1 envClosed_envPre128 famTyped128

/-- PIN (IA-021T skeleton, NEL): the signature's tail after the minors is typed. -/
theorem pin_IA021T_tail_NEL :
    ∃ T w, recNEL.mtype = policyPi dRec128.1.family.parameters
        (.pi (policyMotiveType dRec128.1.family dRec128.1.policy) (policyPi dRec128.1.minorTypes T)) ∧
      Nonempty (HasTyT (envPre 128) recNEL.arity
        (policyPrefixContext dRec128.1.minorTypes dRec128.1.minorTypes.length ++
          (.assumption (policyMotiveType dRec128.1.family dRec128.1.policy) ::
            policyPrefixContext dRec128.1.family.parameters dRec128.1.family.parameters.length))
        T (.sort w)) :=
  IA021T_tail_typed dRec128.1 envClosed_envPre128 famTyped128

/- SECOND INSTRUMENT (NEL): the checker types the motive at exactly the predicted sort. -/
kernel_rfl_theorem pin_IA017T_NEL_checker :
    (sortTyAtC (envPre 128) recNEL.arity 96 [] (policyMotiveType dRec128.1.family dRec128.1.policy)).map
      Sigma.fst = some (motiveSortT dRec128.1.family dRec128.1.policy)

/- TOOTH (NEL): the off-by-one motive is refused. -/
kernel_rfl_theorem tooth_IA017T_NEL_offByOne :
    (sortTyAtC (envPre 128) recNEL.arity 96 []
      (policyMotiveTypeOffByOne dRec128.1.family dRec128.1.policy)).isSome = false

/-! ## srcEnvG slot 108: `recBCT` (`AnySort`, arity 1) -/

kernel_rfl_theorem freshIA108 : ((envPre 108).members 108).isNone = true

theorem envClosed_envPre108 : EnvClosed (envPre 108) := by
  have h : envPre 109 = extendEnv (envPre 108) 108 recBCT := by
    rw [envPre_succ (by decide)]; rfl
  exact envClosed_of_extend_fresh (h ▸ envClosed_of_envWfT wft109)
    (Option.isNone_iff_eq_none.mp freshIA108)

theorem famTyped108 : FamilyTypedT dRec108.1.family := famTypedT_of (fuel := 96) _ famB108

/-- PIN (IA-017T, BCT): an `AnySort` motive, at the recursor's arity 1 over a family at arity 0. -/
theorem pin_IA017T_BCT :
    Nonempty (HasTyT (envPre 108) recBCT.arity
        (policyPrefixContext dRec108.1.family.parameters dRec108.1.family.parameters.length)
        (policyMotiveType dRec108.1.family dRec108.1.policy)
        (.sort (motiveSortT dRec108.1.family dRec108.1.policy))) ∧
      levelBounded recBCT.arity (policyMotiveLevel dRec108.1.family.member.arity dRec108.1.policy) = true ∧
      ∃ rest, recBCT.mtype = policyPi dRec108.1.family.parameters
        (.pi (policyMotiveType dRec108.1.family dRec108.1.policy) rest) :=
  IA017T_motive_well_formed dRec108.1 envClosed_envPre108 famTyped108

theorem pin_IA021T_tail_BCT :
    ∃ T w, recBCT.mtype = policyPi dRec108.1.family.parameters
        (.pi (policyMotiveType dRec108.1.family dRec108.1.policy) (policyPi dRec108.1.minorTypes T)) ∧
      Nonempty (HasTyT (envPre 108) recBCT.arity
        (policyPrefixContext dRec108.1.minorTypes dRec108.1.minorTypes.length ++
          (.assumption (policyMotiveType dRec108.1.family dRec108.1.policy) ::
            policyPrefixContext dRec108.1.family.parameters dRec108.1.family.parameters.length))
        T (.sort w)) :=
  IA021T_tail_typed dRec108.1 envClosed_envPre108 famTyped108

/- SECOND INSTRUMENT (BCT): the checker, at arity 1, returns the predicted sort `imax 1 (succ (param 0))`. -/
kernel_rfl_theorem pin_IA017T_BCT_checker :
    (sortTyAtC (envPre 108) recBCT.arity 96 [] (policyMotiveType dRec108.1.family dRec108.1.policy)).map
      Sigma.fst = some (motiveSortT dRec108.1.family dRec108.1.policy)

/-! ## `listGroupU` (a parameter, a universe-polymorphic family) -/

theorem envClosed_listPrefixU : EnvClosed listPrefixU :=
  envClosed_of_extend_fresh (envClosed_of_envWfT listEnvUWfT) rfl

/-- PIN (IA-017T, List): the motive in the context of the parameter `A : Type u`. -/
theorem pin_IA017T_list :
    Nonempty (HasTyT listPrefixU listURecMember.arity
        (policyPrefixContext listGroupU.family.parameters listGroupU.family.parameters.length)
        (policyMotiveType listGroupU.family listGroupU.policy)
        (.sort (motiveSortT listGroupU.family listGroupU.policy))) ∧
      levelBounded listURecMember.arity
        (policyMotiveLevel listGroupU.family.member.arity listGroupU.policy) = true ∧
      ∃ rest, listURecMember.mtype = policyPi listGroupU.family.parameters
        (.pi (policyMotiveType listGroupU.family listGroupU.policy) rest) :=
  IA017T_motive_well_formed listGroupU envClosed_listPrefixU listRecTypedU.1

theorem pin_IA021T_tail_list :
    ∃ T w, listURecMember.mtype = policyPi listGroupU.family.parameters
        (.pi (policyMotiveType listGroupU.family listGroupU.policy) (policyPi listGroupU.minorTypes T)) ∧
      Nonempty (HasTyT listPrefixU listURecMember.arity
        (policyPrefixContext listGroupU.minorTypes listGroupU.minorTypes.length ++
          (.assumption (policyMotiveType listGroupU.family listGroupU.policy) ::
            policyPrefixContext listGroupU.family.parameters listGroupU.family.parameters.length))
        T (.sort w)) :=
  IA021T_tail_typed listGroupU envClosed_listPrefixU listRecTypedU.1

kernel_rfl_theorem pin_IA017T_list_checker :
    (sortTyAtC listPrefixU listURecMember.arity 96
        (policyPrefixContext listGroupU.family.parameters listGroupU.family.parameters.length)
        (policyMotiveType listGroupU.family listGroupU.policy)).map Sigma.fst =
      some (motiveSortT listGroupU.family listGroupU.policy)

kernel_rfl_theorem tooth_IA017T_list_offByOne :
    (sortTyAtC listPrefixU listURecMember.arity 96
        (policyPrefixContext listGroupU.family.parameters listGroupU.family.parameters.length)
        (policyMotiveTypeOffByOne listGroupU.family listGroupU.policy)).isSome = false

/-! ## `vecGroupU` (a parameter and an index) -/

theorem envClosed_vecPrefixU : EnvClosed vecPrefixU :=
  envClosed_of_extend_fresh (envClosed_of_envWfT vecEnvUWfT) rfl

theorem pin_IA017T_vec :
    Nonempty (HasTyT vecPrefixU vecRecMemberU.arity
        (policyPrefixContext vecGroupU.family.parameters vecGroupU.family.parameters.length)
        (policyMotiveType vecGroupU.family vecGroupU.policy)
        (.sort (motiveSortT vecGroupU.family vecGroupU.policy))) ∧
      levelBounded vecRecMemberU.arity
        (policyMotiveLevel vecGroupU.family.member.arity vecGroupU.policy) = true ∧
      ∃ rest, vecRecMemberU.mtype = policyPi vecGroupU.family.parameters
        (.pi (policyMotiveType vecGroupU.family vecGroupU.policy) rest) :=
  IA017T_motive_well_formed vecGroupU envClosed_vecPrefixU vecRecTypedU.1

theorem pin_IA021T_tail_vec :
    ∃ T w, vecRecMemberU.mtype = policyPi vecGroupU.family.parameters
        (.pi (policyMotiveType vecGroupU.family vecGroupU.policy) (policyPi vecGroupU.minorTypes T)) ∧
      Nonempty (HasTyT vecPrefixU vecRecMemberU.arity
        (policyPrefixContext vecGroupU.minorTypes vecGroupU.minorTypes.length ++
          (.assumption (policyMotiveType vecGroupU.family vecGroupU.policy) ::
            policyPrefixContext vecGroupU.family.parameters vecGroupU.family.parameters.length))
        T (.sort w)) :=
  IA021T_tail_typed vecGroupU envClosed_vecPrefixU vecRecTypedU.1

kernel_rfl_theorem pin_IA017T_vec_checker :
    (sortTyAtC vecPrefixU vecRecMemberU.arity 96
        (policyPrefixContext vecGroupU.family.parameters vecGroupU.family.parameters.length)
        (policyMotiveType vecGroupU.family vecGroupU.policy)).map Sigma.fst =
      some (motiveSortT vecGroupU.family vecGroupU.policy)

kernel_rfl_theorem tooth_IA017T_vec_offByOne :
    (sortTyAtC vecPrefixU vecRecMemberU.arity 96
        (policyPrefixContext vecGroupU.family.parameters vecGroupU.family.parameters.length)
        (policyMotiveTypeOffByOne vecGroupU.family vecGroupU.policy)).isSome = false

end Rcic.Declarative

#print axioms Rcic.Declarative.pin_IA017T_NEL
#print axioms Rcic.Declarative.pin_IA021T_tail_NEL
#print axioms Rcic.Declarative.pin_IA017T_NEL_checker
#print axioms Rcic.Declarative.tooth_IA017T_NEL_offByOne
#print axioms Rcic.Declarative.pin_IA017T_BCT
#print axioms Rcic.Declarative.pin_IA021T_tail_BCT
#print axioms Rcic.Declarative.pin_IA017T_BCT_checker
#print axioms Rcic.Declarative.pin_IA017T_list
#print axioms Rcic.Declarative.pin_IA021T_tail_list
#print axioms Rcic.Declarative.pin_IA017T_list_checker
#print axioms Rcic.Declarative.tooth_IA017T_list_offByOne
#print axioms Rcic.Declarative.pin_IA017T_vec
#print axioms Rcic.Declarative.pin_IA021T_tail_vec
#print axioms Rcic.Declarative.pin_IA017T_vec_checker
#print axioms Rcic.Declarative.tooth_IA017T_vec_offByOne
