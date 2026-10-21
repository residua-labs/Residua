import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeTypedModelCovVHo
import rcic.RcicNativeTypedModelW6Iota

/-!
# The original divergent major remains unobservable above bottom

The invariant fixes the recursor head and requires a non-constant-headed
third argument whenever present. It is inherited by application prefixes
and by the fresh application used in typed eta. Every ordinary structured
iota witness at this recursor instead has precisely two pre-major arguments
and a constructor-headed third argument. Native K is impossible because the
higher-order field admits no legacy witness. This proof examines the new
grammar itself and uses neither the removed source filter nor old guarded
observation forgetting. `closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit FamModelLRSAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit TypedModelW6IotaAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def hoSafeArgs : List (Expr Nat) → Prop
  | _ :: _ :: x :: _ => headConst x = none
  | _ => True

private theorem hoSafeArgs_prefix (xs : List (Expr Nat)) (a : Expr Nat)
    (h : hoSafeArgs (xs ++ [a])) : hoSafeArgs xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
      cases xs with
      | nil => trivial
      | cons y xs =>
          cases xs with
          | nil => trivial
          | cons z xs => exact h

private theorem headConst_lift_native (e : Expr Nat) (cutoff amount : Nat) :
    headConst (lift cutoff amount e) = headConst e := by
  induction e with
  | bvar i => by_cases hi : cutoff ≤ i <;> simp [lift, hi, headConst]
  | sort => rfl
  | const => rfl
  | app f a ihf _ => exact ihf
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit => rfl

private theorem appsSpine_lift_args (e : Expr Nat) (cutoff amount : Nat) :
    (appsSpine (lift cutoff amount e)).2 =
      ((appsSpine e).2.map (lift cutoff amount)) := by
  induction e with
  | bvar i => by_cases hi : cutoff ≤ i <;> simp [lift, hi, appsSpine]
  | sort => rfl
  | const => rfl
  | app f a ihf _ =>
      simp only [lift, appsSpine, ihf, List.map_append, List.map_cons, List.map_nil]
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit => rfl

private theorem hoSafeArgs_lift (xs : List (Expr Nat)) (cutoff amount : Nat)
    (h : hoSafeArgs xs) : hoSafeArgs (xs.map (lift cutoff amount)) := by
  cases xs with
  | nil => trivial
  | cons x xs =>
      cases xs with
      | nil => trivial
      | cons y xs =>
          cases xs with
          | nil => trivial
          | cons z xs =>
              exact (headConst_lift_native z cutoff amount).trans h

private theorem hoSafeArgs_fresh (xs : List (Expr Nat))
    (h : hoSafeArgs xs) : hoSafeArgs (xs ++ [.bvar 0]) := by
  cases xs with
  | nil => trivial
  | cons x xs =>
      cases xs with
      | nil => trivial
      | cons y xs =>
          cases xs with
          | nil => rfl
          | cons z xs => exact h

private def hoBlocked (e : Expr Nat) : Prop :=
  headConst e = some 65 ∧ hoSafeArgs (appsSpine e).2

private theorem hoBlocked_prefix {f a : Expr Nat}
    (h : hoBlocked (.app f a)) : hoBlocked f :=
  ⟨h.1, hoSafeArgs_prefix (appsSpine f).2 a h.2⟩

private theorem hoBlocked_eta {e : Expr Nat} (h : hoBlocked e) :
    hoBlocked (.app (lift 0 1 e) (.bvar 0)) := by
  refine ⟨?_, ?_⟩
  · exact (headConst_lift_native e 0 1).trans h.1
  · change hoSafeArgs ((appsSpine (lift 0 1 e)).2 ++ [.bvar 0])
    rw [appsSpine_lift_args]
    exact hoSafeArgs_fresh _ (hoSafeArgs_lift _ 0 1 h.2)

private theorem ho_pre_length (w : IotaWitnessS covUHoEnv)
    (hr : w.recRef = 65) : w.preMajor.length = 2 := by
  have hm : w.recMember = covUHoRec := by
    have hh := w.hrec
    rw [hr] at hh
    exact (Option.some.inj hh).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
  have hp := w.hpre
  omega

private theorem list_of_length_two {α : Type} (xs : List α)
    (h : xs.length = 2) : ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      cases xs with
      | nil => simp at h
      | cons b xs =>
          cases xs with
          | nil => exact ⟨a, b, rfl⟩
          | cons c xs => simp at h

private theorem ho_iota_not_blocked (w : IotaWitnessS covUHoEnv) :
    ¬ hoBlocked (iotaLhsOfS w) := by
  intro h
  have hr : w.recRef = 65 := by
    apply Option.some.inj
    have hh := h.1
    simpa only [iotaLhsOfS, recCall, headConst_foldApps, headConst] using hh
  obtain ⟨a, b, hp⟩ := list_of_length_two w.preMajor (ho_pre_length w hr)
  have hs := h.2
  simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const, hp] at hs
  change headConst (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) = none at hs
  simp only [headConst_foldApps, headConst] at hs
  cases hs

/-- The invariant is proved by induction over every new guarded constructor,
including typed eta and both native computation clauses. -/
private theorem ho_blocked_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNative covUHoEnv n Γ ρ e c) : hoBlocked e → c = .bot := by
  induction h with
  | bot => intro _; rfl
  | bvar => intro hh; cases hh.1
  | sort => intro hh; cases hh.1
  | const Γ ρ r ls hr hp =>
      intro hh
      have he : r = 65 := Option.some.inj hh.1
      subst r
      exact (not_rigidConst_of_recursor covUHoWitness hr).elim
  | recursor ls hnp hpre hfld h ih =>
      intro hh
      exact (hnp (covVHo_rec_family_prop _ (Option.some.inj hh.1))).elim
  | pi => intro hh; cases hh.1
  | lam => intro hh; cases hh.1
  | app hf hs ha ihf iha =>
      intro hh
      cases ihf (hoBlocked_prefix hh)
  | appSpine hf ha hslot hfield ihf iha =>
      intro hh
      cases ihf (hoBlocked_prefix hh)
  | @delta Γ ρ r ls m b c hd h ih =>
      intro hh
      have he : r = 65 := Option.some.inj hh.1
      subst r
      exact (not_deltaConst_of_recursor covUHoWitness hd).elim
  | letE => intro hh; cases hh.1
  | lit => intro hh; cases hh.1
  | iota w h ih => intro hh; exact (ho_iota_not_blocked w hh).elim
  | recursorPropK w x hk hn hi hc h ih =>
      intro hh
      have hr : w.recRef = 65 := by
        apply Option.some.inj
        have he := hh.1
        simpa only [recCall, headConst_foldApps, headConst] using he
      exact (covUHo_no_legacy_witness w hr).elim
  | eta he hD ht hne hb ihD ihb =>
      intro hh
      obtain ⟨s, hs, hn⟩ := hne
      exact (hn (ihb s hs (hoBlocked_eta hh))).elim

/-- Unlike the constructor-major I* fixture, the original call's divergent
major has no constructor head. All its guarded observations are bottom. -/
theorem covWNativeHo_type_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTKWNative covUHoEnv n Γ ρ covUHoType c) : c = .bot :=
  ho_blocked_only_bot h ⟨rfl, rfl⟩

theorem covWNativeHo_type_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWNativeObservation covUHoEnv n Γ ρ covUHoType c ↔ c = .bot := by
  constructor
  · rintro ⟨d, he, hd⟩
    have hb := covWNativeHo_type_only_bot hd
    subst d
    exact he.symm
  · intro hc
    subst c
    exact ⟨.bot, rfl, .bot _ _ _⟩

theorem covWNativeHo_repaired_instance (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) ∧
    ApproxTKWNativeStage covUHoEnv n 1 [] EnvWIrrel.bot covUHoType .bot ∧
    (∀ c, ApproxTKWNative covUHoEnv n [] EnvWIrrel.bot covUHoType c → c = .bot) ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, covWNative_realized_nil covUHoEnv n 1,
    ⟨covUHoType_hasTy n []⟩,
    ⟨.bot _ _ _, by simp [covTObservationBudget, covWIrrelErase]⟩,
    (fun _ h => covWNativeHo_type_only_bot h), covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HO_CONTROL_ROOTS
#print axioms covWNativeHo_type_only_bot
#print axioms covWNativeHo_type_observation_iff
#print axioms covWNativeHo_repaired_instance
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HO_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit


namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open TypedModelCovTAudit TypedModelCovWIrrelAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit

/-- Public use of the already checked invariant at an arbitrary major with
no constant head. This also applies to the variable before beta substitution. -/
theorem covWNativeHo_nonconstant_major_only_bot {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel} {ls : List Level}
    {M m x : Expr Nat} (hx : headConst x = none)
    (h : ApproxTKWNative covUHoEnv n Γ ρ
      (recCall (.const 65 ls) [M, m] x) c) : c = .bot := by
  apply ho_blocked_only_bot h
  exact ⟨by simp only [recCall, foldApps, headConst],
    by simpa only [recCall, appsSpine_foldApps_const, hoSafeArgs] using hx⟩

/-- The same invariant covers the two-argument prefix itself: typed eta
tests a fresh nonconstructor major, so no finite nonbottom graph is supplied. -/
theorem covWNativeHo_prefix_only_bot {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel} {ls : List Level} {M m : Expr Nat}
    (h : ApproxTKWNative covUHoEnv n Γ ρ
      (foldApps (.const 65 ls) [M, m]) c) : c = .bot := by
  apply ho_blocked_only_bot h
  exact ⟨by simp only [foldApps, headConst],
    by simp only [appsSpine_foldApps_const, hoSafeArgs]⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HO_EXPOSED_ROOTS
#print axioms covWNativeHo_nonconstant_major_only_bot
#print axioms covWNativeHo_prefix_only_bot
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HO_EXPOSED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
