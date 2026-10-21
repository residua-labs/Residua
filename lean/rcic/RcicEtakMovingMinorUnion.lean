import rcic.RcicPinEqIotaStarK
import rcic.RcicParRedT
import rcic.RcicIotaLegacyAdm

/-!
All-witness Eq computation at pin
76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. No sorry/axiom.
This control covers BOTH branches of DerivedIotaU. It does not use
native normalization, native/erased reflection, InScope, sort uniqueness,
type uniqueness, or a supplied family/Pi row. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.NativeMovingMinorUnion76

theorem legacyData (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 ∧
      w.ctorIdx = 0 ∧ w.ctorMember = eqReflT ∧ w.fields = [] := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hd := IotaWitness.recData_admitted eqGroupAdm
    (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  obtain ⟨hfr, _, hnp, hni, hnm⟩ := hd
  have hidx : w.ctorIdx = 0 := by
    have h := w.hidx
    rw [hnm] at h
    omega
  have hcr : w.ctorRef = 64 := by
    rw [w.hctorIdx, hfr, hidx]
  have hcm : w.ctorMember = eqReflT := by
    have h := w.hctor
    rw [hcr] at h
    exact (Option.some.inj h).symm
  have hfl : w.fields.length = 0 := by
    have h := w.hnpar
    rw [hnp, hcm] at h
    change 2 + w.fields.length = 2 at h
    omega
  exact ⟨hnp, hni, hnm, hidx, hcm, List.eq_nil_of_length_eq_zero hfl⟩

theorem schemaData (w : IotaWitnessS eqEnvT) (hr : w.recRef = 65) :
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 ∧
      w.ctorIdx = 0 ∧ w.ctorMember = eqReflT ∧ w.fields = [] := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hd := IotaWitnessS.recData_admitted eqGroupAdm
    (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  obtain ⟨hfr, _, hnp, hni, hnm⟩ := hd
  have hidx : w.ctorIdx = 0 := by
    have h := w.hidx
    rw [hnm] at h
    omega
  have hcr : w.ctorRef = 64 := by
    rw [w.hctorIdx, hfr, hidx]
  have hcm : w.ctorMember = eqReflT := by
    have h := w.hctor
    rw [hcr] at h
    exact (Option.some.inj h).symm
  have hfl : w.fields.length = 0 := by
    have h := w.hnpar
    rw [hnp, hcm] at h
    change 2 + w.fields.length = 2 at h
    omega
  exact ⟨hnp, hni, hnm, hidx, hcm, List.eq_nil_of_length_eq_zero hfl⟩

theorem legacyRhs (w : IotaWitness eqEnvT) (hr : w.recRef = 65)
    (a0 a1 a2 a3 a4 : Expr Nat)
    (hp : w.preMajor = [a0, a1, a2, a3, a4]) :
    iotaRhsOf w = a3 := by
  obtain ⟨hnp, _, _, hidx, _, hf⟩ := legacyData w hr
  rw [iotaRhs_nil_fields w hf]
  have hm := w.hminor
  rw [hnp, hidx, hp] at hm
  exact (Option.some.inj hm).symm

theorem schema_is_bvar1 (w : IotaWitnessS eqEnvT) (hr : w.recRef = 65) :
    w.schema = .bvar 1 := by
  obtain ⟨hnp, hni, hnm, hidx, hcm, hf⟩ := schemaData w hr
  have hd : w.ctorDoms = [.sort (.succ .zero), .bvar 0] := by
    have h := w.hpeel
    rw [hnp, hf, hcm] at h
    exact (congrArg Prod.fst (Option.some.inj h)).symm
  have hsh : w.shapes = [] := by
    have h := w.hshapes
    rw [hnp, hd] at h
    change some [] = some w.shapes at h
    exact (Option.some.inj h).symm
  have h := w.hschema
  rw [hf, hni, hnm, hidx, hnp, hsh] at h
  change some (.bvar 1) = some w.schema at h
  exact (Option.some.inj h).symm

theorem schemaRhs (w : IotaWitnessS eqEnvT) (hr : w.recRef = 65)
    (a0 a1 a2 a3 a4 : Expr Nat)
    (hp : w.preMajor = [a0, a1, a2, a3, a4]) :
    iotaRhsOfS w = a3 := by
  obtain ⟨_, _, _, _, _, hf⟩ := schemaData w hr
  rw [iotaRhsOfS, hf, List.append_nil, schema_is_bvar1 w hr, hp]
  change instPrefix [a0, a1, a2, a3, a4] (.bvar 1) = a3
  exact instPrefix_bvar_lt (show (1 : Nat) < 5 by decide) rfl

/-- The union's RHS is the unchanged FOURTH argument on every six-slot
Eq redex. The synthetic major and all constructor-side parameters/levels
may vary; both union witnesses still read this same prefix slot. -/
theorem unionRhs : {lhs rhs : Expr Nat} → DerivedIotaU eqEnvT lhs rhs →
    ∀ (ls : List Level) (a0 a1 a2 a3 a4 major : Expr Nat),
    lhs = recCall (.const 65 ls) [a0, a1, a2, a3, a4] major → rhs = a3
  | _, _, .ofU w, ls, a0, a1, a2, a3, a4, major, heq => by
      have hs := congrArg appsSpine heq
      simp only [iotaLhsOf, recCall, appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      have ha := congrArg Prod.snd hs
      have hr : w.recRef = 65 := (Expr.const.inj hh).1
      obtain ⟨hnp, hni, hnm, _, _, _⟩ := legacyData w hr
      have hl : w.preMajor.length = [a0, a1, a2, a3, a4].length := by
        rw [w.hpre, hnp, hni, hnm]
        rfl
      have hp : w.preMajor = [a0, a1, a2, a3, a4] :=
        (List.append_inj ha hl).1
      exact legacyRhs w hr a0 a1 a2 a3 a4 hp
  | _, _, .ofUS w, ls, a0, a1, a2, a3, a4, major, heq => by
      have hs := congrArg appsSpine heq
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hs
      have hh := congrArg Prod.fst hs
      have ha := congrArg Prod.snd hs
      have hr : w.recRef = 65 := (Expr.const.inj hh).1
      obtain ⟨hnp, hni, hnm, _, _, _⟩ := schemaData w hr
      have hl : w.preMajor.length = [a0, a1, a2, a3, a4].length := by
        rw [w.hpre, hnp, hni, hnm]
        rfl
      have hp : w.preMajor = [a0, a1, a2, a3, a4] :=
        (List.append_inj ha hl).1
      exact schemaRhs w hr a0 a1 a2 a3 a4 hp

end Rcic.Declarative.NativeMovingMinorUnion76
