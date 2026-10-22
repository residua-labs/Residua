import rcic.RcicAnnKDeterminism
import rcic.RcicAnnKEqPositive
import rcic.RcicAnnLRChain

/-!
# An arbitrary matching Eq frame supplies the fixed canonical typing

The complete source call determines its recursor, parameters and actual
index.  The singleton stored target then determines its constructor and
group.  It does not syntactically determine `familyLevels`, `ctorLevels`
or the declared indices.

The two level lists are recovered from ordinary typing generation:
`familyHeadType` and `canonicalType` each contain a two-argument constant
spine, and both stored constants have universe arity zero.  This uses
neither type uniqueness nor a semantic-environment premise.

There is no need to identify the arbitrary declared indices.  The supplied
`Frame.familyConversion` retypes `canonicalType` at the actual proposition.
Consequently every frame for the assumption-context call supplies the
single fixed typing of `reflAt parameter` at `eqAt parameter (bvar 1)`.

This is an extraction consumer for the conversion/typing-erasure coherence
reduction.  It supplies neither a matching frame nor a separation theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.FrameSource

open Rcic.Declarative EqLargeFixture RouteCKContext

/-- Exactly the frame fields fixed by the actual source and target layout. -/
structure ContextCallFieldsA3 (s : KStage.Shape) : Prop where
  recRef : s.recRef = 65
  recLevels : s.recLevels = [two]
  ctorRef : s.ctorRef = 64
  group : s.group = KEqPositive.group
  params : s.params = [.sort .zero, parameter]
  actualIndices : s.actualIndices = [.bvar 1]
  motive : s.motive = EqLargeFixture.motive
  minor : s.minor = result
  major : s.major = .bvar 0

theorem contextCallFieldsA3_of_target {s : KStage.Shape}
    (w : KStage.Target env s) (he : s.source = contextCall) :
    ContextCallFieldsA3 s := by
  have hhead : ExprA.const s.recRef s.recLevels = .const 65 [two] := by
    simpa only [KStage.Shape.source, KStage.Shape.prefix, contextCall,
      appsSpineA, appsSpineA_foldAppsA] using
      congrArg (fun e => (appsSpineA e).1) he
  have hr := (ExprA.const.inj hhead).1
  have hls := (ExprA.const.inj hhead).2
  have hc : s.ctorRef = 64 := by
    have hn := w.ctorNext
    omega
  have hg : s.group = KEqPositive.group := by
    have h := w.group
    rw [hr, hc] at h
    exact Option.some.inj
      (h.symm.trans (rfl : iotaGroupA env 65 64 = some KEqPositive.group))
  have hpl : s.params.length = 2 := by
    simpa only [hg, KEqPositive.group] using w.paramCount
  have hil : s.actualIndices.length = 1 := by
    simpa only [hg, KEqPositive.group] using w.indexCount
  have hargs : s.params ++ ([s.motive, s.minor] ++ (s.actualIndices ++ [s.major])) =
      [.sort .zero, parameter] ++
        ([EqLargeFixture.motive, result] ++ ([.bvar 1] ++ [.bvar 0])) := by
    simpa only [KStage.Shape.source, KStage.Shape.prefix, KStage.Shape.pre,
      contextCall, appsSpineA, appsSpineA_foldAppsA, List.nil_append,
      List.append_assoc] using congrArg (fun e => (appsSpineA e).2) he
  obtain ⟨hps, htail⟩ := List.append_inj hargs hpl
  change s.motive :: s.minor :: (s.actualIndices ++ [s.major]) =
    EqLargeFixture.motive :: result :: ([.bvar 1] ++ [.bvar 0]) at htail
  have hm := (List.cons.inj htail).1
  have htail' := (List.cons.inj htail).2
  have hmn := (List.cons.inj htail').1
  have hlast := (List.cons.inj htail').2
  obtain ⟨his, hmaj⟩ := List.append_inj hlast hil
  exact ⟨hr, hls, hc, hg, hps, his, hm, hmn, (List.cons.inj hmaj).1⟩

private theorem twoApps_const_arity {Γ : LCtxA} {r : Nat} {ls : List Level}
    {a b T : ExprA} {m : CheckedMemberA} (hm : env.members r = some m)
    (ht : HasTyA env (iotaIfaceA env) 0 Γ (.app (.app (.const r ls) a) b) T) :
    ls.length = m.arity := by
  obtain ⟨_, _, _, _, _, ⟨hf⟩, _⟩ := hasTyA_app_gen ht
  obtain ⟨_, _, _, _, _, ⟨hc⟩, _⟩ := hasTyA_app_gen hf
  obtain ⟨m', hm', hl, _, _⟩ := hasTyA_const_full hc
  rw [hm] at hm'
  cases hm'
  exact hl

/-- Typing, rather than source equality, forces the two unstored level lists. -/
theorem contextFrameLevelsA3 {Γ : LCtxA} {s : KStage.Shape}
    (w : KStage.Frame env (iotaIfaceA env) 0 Γ s) (he : s.source = contextCall) :
    s.familyLevels = [] ∧ s.ctorLevels = [] := by
  have d := contextCallFieldsA3_of_target w.target he
  have hf := w.familyHeadType
  change HasTyA env (iotaIfaceA env) 0 Γ
    (foldAppsA (.const s.group.familyRef s.familyLevels) s.params) w.familyTelescope at hf
  rw [d.group, d.params] at hf
  have hfl : s.familyLevels.length = 0 :=
    twoApps_const_arity (rfl : env.members 63 = some fam) hf
  have hc := w.canonicalType
  change HasTyA env (iotaIfaceA env) 0 Γ
    (foldAppsA (.const s.ctorRef s.ctorLevels) s.params) s.declaredProp at hc
  rw [d.ctorRef, d.params] at hc
  have hcl : s.ctorLevels.length = 0 :=
    twoApps_const_arity (rfl : env.members 64 = some reflMember) hc
  constructor
  · cases hls : s.familyLevels with
    | nil => rfl
    | cons l ls => simp only [hls, List.length_cons] at hfl; omega
  · cases hls : s.ctorLevels with
    | nil => rfl
    | cons l ls => simp only [hls, List.length_cons] at hcl; omega

/-- The canonical term and actual proposition are fixed; declared indices remain free. -/
theorem contextFrameFormsA3 {Γ : LCtxA} {s : KStage.Shape}
    (w : KStage.Frame env (iotaIfaceA env) 0 Γ s) (he : s.source = contextCall) :
    s.canonical = reflAt parameter ∧ s.actualProp = eqAt parameter (.bvar 1) := by
  have d := contextCallFieldsA3_of_target w.target he
  obtain ⟨hF, hC⟩ := contextFrameLevelsA3 w he
  constructor
  · change foldAppsA (.const s.ctorRef s.ctorLevels) s.params = reflAt parameter
    rw [d.ctorRef, hC, d.params]
  · change foldAppsA (foldAppsA (.const s.group.familyRef s.familyLevels) s.params)
      s.actualIndices = eqAt parameter (.bvar 1)
    rw [d.group, hF, d.params, d.actualIndices]
    rfl

/-- Every matching frame supplies the same canonical typing at the actual index.
The arbitrary declared indices are consumed through `Frame.familyConversion`. -/
theorem contextFrameCanonicalActualA3 {Γ : LCtxA} {s : KStage.Shape}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    (w : KStage.Frame env (iotaIfaceA env) 0 Γ s) (he : s.source = contextCall) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ
      (reflAt parameter) (eqAt parameter (.bvar 1))) := by
  obtain ⟨hFamily⟩ := w.familyConversion closed liftIface (iotaFnA_recHead env) substIface hΓ
  have hdecl := convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface hΓ hFamily
  have hactual := convA_hasTy_right closed liftIface (iotaFnA_recHead env) substIface hΓ hFamily
  have ht : HasTyA env (iotaIfaceA env) 0 Γ s.canonical s.actualProp :=
    .conv Γ s.canonical s.declaredProp s.actualProp .zero .zero
      w.canonicalType hdecl (eqNA_refl _) hactual hFamily
  obtain ⟨hcanon, hprop⟩ := contextFrameFormsA3 w he
  rw [hcanon, hprop] at ht
  exact ⟨ht⟩

/-- Specialization to the actual open assumption-context call.  No frame is assumed to exist. -/
theorem assumptionFrameCanonicalActualA3 {s : KStage.Shape}
    (w : KStage.Frame env (iotaIfaceA env) 0 assumptionContext s)
    (he : s.source = contextCall) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext
      (reflAt parameter) (eqAt parameter (.bvar 1))) :=
  contextFrameCanonicalActualA3 assumptionContextWf w he

#print axioms ContextCallFieldsA3
#print axioms contextCallFieldsA3_of_target
#print axioms contextFrameLevelsA3
#print axioms contextFrameFormsA3
#print axioms contextFrameCanonicalActualA3
#print axioms assumptionFrameCanonicalActualA3

end Rcic.Declarative.Ann.LR3.FrameSource
