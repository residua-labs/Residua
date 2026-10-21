import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovZRigidId

/-!
# Exact scope of the neutral-reflection addition

The admitted rigid identity head obtains one additional valid Pi code under
`r = true`. Its declared domain cannot denote this code under `r = false`.
Constructors retain the exact telescope branch. Positive proposition codes
still exclude every non-bottom spine. The remaining shape exclusions are
consequences of the requested inversion fields, not new normalization claims.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelAudit.TypingFin TypedModelCovZMeasureAudit

variable {E : ResolvedEnv} {reflect : Bool}

theorem ctyCovP2_constructor_pi_iff {r : Nat} {us : List CptT} {a : CptT}
    {g : List (List CptT × CptT)} {m : CheckedMember}
    (hm : E.members r = some m) (hc : m.mclass = .constructorM) :
    CTyCovP2 reflect E (.spine r us) (.pi a g) ↔
      ¬ IsPropCTP E (.pi a g) ∧ RigidPiGateP (CTyCovP2 reflect E) E r us a g := by
  rw [CTyCovP2]
  constructor
  · rintro ⟨hp, hg | ⟨_, hn⟩⟩
    · exact ⟨hp, hg⟩
    · exact (neutralHeadP_not_constructor hn hm hc).elim
  · rintro ⟨hp, hg⟩
    exact ⟨hp, Or.inl hg⟩

theorem ctyCovP2_positive_excludes_spine {a : CptT} {r : Nat} {us : List CptT}
    (hp : IsPropCTP E a) : ¬ CTyCovP2 reflect E (.spine r us) a :=
  fun ht => CptT.noConfusion (ctyCovP2_prop_bot hp ht)

theorem covPIdentity_neutral_head : NeutralHeadP covZRigidIdEnv 0 :=
  ⟨covZRigidIdMember, rfl, rfl, Or.inl rfl⟩

def covPReflectionCode : CptT := .pi .prop []

theorem covPReflectionCode_type : TyCodeCT covPReflectionCode :=
  .pi .prop (by intro t ht; cases ht)

theorem covPReflectionCode_not_positive :
    ¬ IsPropCTP covZRigidIdEnv covPReflectionCode :=
  not_isPropCTP_pi_nil _ _

theorem covP_reflection_extra_gate :
    CTyCovP2 true covZRigidIdEnv (.spine 0 []) covPReflectionCode :=
  .reflectedPi rfl covPIdentity_neutral_head covPReflectionCode_not_positive

theorem covP_no_extra_gate_without_reflection :
    ¬ CTyCovP2 false covZRigidIdEnv (.spine 0 []) covPReflectionCode := by
  intro ht
  change CTyCovP2 false covZRigidIdEnv (.spine 0 []) (.pi .prop []) at ht
  rw [CTyCovP2] at ht
  rcases ht.2 with hg | ⟨hf, _⟩
  · obtain ⟨m, ls, hm, _, hlen, _, Tres, hTres, hobs⟩ := hg
    have he : m = covZRigidIdMember := Option.some.inj hm.symm
    subst m
    have hls : ls = [] := List.length_eq_zero.mp hlen
    subst ls
    have hTres' : Tres = cexPolyIdTy := (Option.some.inj hTres).symm
    subst Tres
    change ApproxT covZRigidIdEnv EnvT.bot cexPolyIdTy (.pi .prop []) at hobs
    rcases approxT_pi_inv hobs with hb | ⟨a, g, he, hd, _⟩
    · exact CptT.noConfusion hb
    · cases he
      rcases approxT_sort_inv hd with hb | hs
      · exact CptT.noConfusion hb
      · exact CptT.noConfusion hs
  · cases hf

theorem old_prop_bot_incompatible (E : ResolvedEnv) (reflect : Bool) :
    ¬ (∀ {a u}, IsPropCT E a → CTyCovP2 reflect E u a → u = .bot) := by
  intro h
  have hp : IsPropCT E (.pi .bot []) :=
    .pi .bot (by intro t ht; cases ht)
  have ht : CTyCovP2 reflect E (.lam []) (.pi .bot []) :=
    .lam (not_isPropCTP_pi_nil E .bot)
      (by intro s hs; cases hs) (by intro s hs; cases hs)
  exact CptT.noConfusion (h hp ht)

/-- Even a non-bottom type-code guard must preserve universe Prop membership:
an arbitrary neutral is not automatically a proposition-code observation. -/
theorem reflection_universe_guard_necessary (C : CovTypingP E)
    (r : Nat) (us : List CptT) (hnp : ¬ IsPropCT E (.spine r us))
    (hr : ∀ a, a ≠ .bot → TyCodeCT a → ¬ IsPropCTP E a →
      C.ty (.spine r us) a) : False := by
  have ht := hr .prop CptT.noConfusion .prop (not_isPropCTP_prop E)
  rcases C.prop_inv ht with hb | hp
  · exact CptT.noConfusion hb
  · exact hnp hp

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_REFLECTION_ROOTS
#print axioms ctyCovP2_constructor_pi_iff
#print axioms ctyCovP2_positive_excludes_spine
#print axioms covPIdentity_neutral_head
#print axioms covPReflectionCode
#print axioms covPReflectionCode_type
#print axioms covPReflectionCode_not_positive
#print axioms covP_reflection_extra_gate
#print axioms covP_no_extra_gate_without_reflection
#print axioms old_prop_bot_incompatible
#print axioms reflection_universe_guard_necessary
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_REFLECTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
