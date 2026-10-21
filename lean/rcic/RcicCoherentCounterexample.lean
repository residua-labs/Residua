import rcic.RcicCoherentEta
import rcic.RcicNativeDecoLeaf
import rcic.RcicNativeWallHostProp
import rcic.RcicSortUniqueRows

/-!
# The canonical coherent diamond fails in the admitted empty environment

This negative client specializes the existing in-scope sort-uniqueness
theorem to `EnvWfT.empty`, whose `InScope` proof is `True.intro`. It does
not assume a sort row, type uniqueness, a Pi row, consistency, or any
negative proofhood premise. The specialized sort theorem and the existing
host-Prop transfer discharge the eta fixture's three negative premises.

The peak and its source-decoration equation are the actual canonical
`lamPeakStep` and `etaPeakStep`. The no-join theorem excludes every pair
of alternative certified one-step legs. The two-step coherent repair in
`RcicCoherentEta` remains valid.

The reverse orientation is stronger: every certified star from `f = x p`
retains the variable head `x`, whereas every single certified step from
the non-eta lambda `d` retains a lambda root. The proof below constructs
that invariant for arbitrary intervening arguments and therefore excludes
all reverse asymmetric joins. Both the ordered `AsymmetricDiamond` and
its equivalent `ShortRightDiamond` are refuted for the same admitted
canonical instance. A short-right consumer remains a valid conditional
theorem, but its global native premise cannot be supplied here.

This module is a negative admitted-model client, not a dependency of the
positive row constructions or their consumers. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentCounterexampleAudit

open CoherentCanonicalAudit (nativeLeafIface)
open CoherentEtaAudit (lamPeakStep etaPeakStep)

/-- The existing in-scope theorem is concretely specialized to the empty
environment. No sort-coherence premise is supplied by the caller. -/
private theorem empty_zeroSortCoherence :
    HostPropAudit.ZeroSortCoherence emptyEnv 0 := by
  intro _ Γ A u hΓ hA hP
  exact sortUnique_of_inScope EnvWfT.empty trivial 0 EnvWfT.empty hΓ hA hP

private theorem piP_level_ne_zero :
    ¬ eqN (.imax .zero (.succ .zero)) .zero := by
  intro h
  have hz := h (fun _ => none)
  simp [eval] at hz

private theorem x_level_ne_zero :
    ¬ eqN (.imax .zero (.imax .zero (.succ .zero))) .zero := by
  intro h
  have hz := h (fun _ => none)
  simp [eval] at hz

/-- Any hypothetical proof typing transports Prop sorting to the
fixture's displayed index. Its displayed nonzero sort then contradicts
the constructed empty-environment sort-uniqueness theorem. -/
private theorem notProof_of_displayed_sort {e T : Expr Nat} {v : Level}
    (he : HasTyT emptyEnv 0 etaLeafCtx e T)
    (hT : HasTyT emptyEnv 0 etaLeafCtx T (.sort v))
    (hv : ¬ eqN v .zero) : NotProof emptyEnv 0 etaLeafCtx e := by
  intro P hp hP
  have hT0 := HostPropAudit.hostPropData_of_zeroSortCoherence
    EnvWfT.empty empty_zeroSortCoherence etaLeafCtx_wf he hP hp
  exact hv (empty_zeroSortCoherence EnvWfT.empty etaLeafCtx_wf hT hT0)

private theorem empty_d_notProof :
    NotProof emptyEnv 0 etaLeafCtx (.lam etaLeafP etaLeafBody') :=
  notProof_of_displayed_sort etaLeafD_ty (etaLeafPiP_ty etaLeafCtx)
    piP_level_ne_zero

private theorem empty_f_notProof :
    NotProof emptyEnv 0 etaLeafCtx etaLeafF :=
  notProof_of_displayed_sort etaLeafF_ty (etaLeafPiP_ty etaLeafCtx)
    piP_level_ne_zero

private theorem empty_x_notProof :
    NotProof emptyEnv 0 etaLeafCtx (.bvar 1) :=
  notProof_of_displayed_sort etaLeafX_var (etaLeafX_ty etaLeafCtx)
    x_level_ne_zero

/-- Every possible ordinary one-step join of the canonical fixture is
excluded in `emptyEnv`, with no remaining negative or coherence premise. -/
theorem canonical_eta_no_join {T₁ T₂ : Expr Nat}
    (j : Join emptyEnv 0 (ProofLeaf emptyEnv 0) etaLeafCtx
      (.lam etaLeafP etaLeafBody') etaLeafF T₁ T₂) : False :=
  etaLeaf_no_join (nativeLeafIface emptyEnv 0)
    empty_d_notProof empty_f_notProof empty_x_notProof j

/-- The actual equal-source-decoration canonical peak has no coherent
one-step join, including any alternative choice of certified legs. -/
theorem canonical_eta_no_stepJoin :
    ¬ Nonempty (DecoStarAudit.StepJoin (nativeLeafIface emptyEnv 0)
      etaLeafCtx_wf (lamPeakStep emptyEnv 0) (etaPeakStep emptyEnv 0)) := by
  rintro ⟨j⟩
  exact canonical_eta_no_join ⟨j.centre, j.left, j.right⟩

/-- An admitted canonical countermodel to the existing coherent diamond.
The environment and context witnesses, the actual peak, and the source
decoration equality are all constructed here or in the imported fixture. -/
theorem admitted_canonical_coherentDiamond_false :
    Nonempty (EnvWfT emptyEnv) ∧
      ¬ Nonempty (DecoStarAudit.CoherentDiamond (nativeLeafIface emptyEnv 0)) := by
  refine ⟨⟨.empty⟩, ?_⟩
  rintro ⟨D⟩
  exact canonical_eta_no_stepJoin
    ⟨D etaLeafCtx_wf (lamPeakStep emptyEnv 0) (etaPeakStep emptyEnv 0)
      (CoherentEtaAudit.peak_source_deco emptyEnv 0)⟩

/-- The unchanged variable head is not a proof, so neither is any
application of it, regardless of how its argument has reduced. -/
private theorem empty_xApp_notProof (a : Expr Nat) :
    NotProof emptyEnv 0 etaLeafCtx (.app (.bvar 1) a) := by
  intro P hp hP
  obtain ⟨Q, ⟨hQ⟩, ⟨hx⟩⟩ := F8A2Support.proof_app_function
    (sortUnique_of_inScope EnvWfT.empty trivial 0) EnvWfT.empty etaLeafCtx_wf
    ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  exact empty_x_notProof hx hQ

/-- Every certified step from an application of `x` keeps that head.
Only the original `Certified.conv` and `Certified.iotaSpine` children
are recursive subjects. The function child of an application is handled
by the existing `bvarStep_target`; no generated step is recursed over. -/
private theorem xAppStep_target (a : Expr Nat) :
    {x j T : Expr Nat} →
    {p : ParRedT (ProofLeaf emptyEnv 0) emptyEnv 0 etaLeafCtx x j T} →
    Certified p → x = .app (.bvar 1) a →
    ∃ a' : Expr Nat, j = .app (.bvar 1) a'
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx => by
      subst hx
      exact ⟨a, rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ _ _ _ ch, hx =>
      xAppStep_target a ch hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx => by
      subst hx
      exact (empty_xApp_notProof a h.hp h.hT).elim
  | _, _, _, _, @Certified.app _ _ _ _ _ _ _ a' _ _ _ _ _ _ _ _ _ _ _ _ cf _, hx => by
      injection hx with h1 _
      have e := bvarStep_target (nativeLeafIface emptyEnv 0)
        (Γ := etaLeafCtx) (i := 1) (X := etaLeafX) rfl empty_x_notProof cf h1
      subst e
      exact ⟨a', rfl⟩
  | _, _, _, _, @Certified.beta .., hx => by
      injection hx with h1 _
      exact nomatch h1
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, hx => by
      obtain ⟨a', e⟩ := xAppStep_target a cs hx
      subst e
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp only [recCall, foldApps_snoc, Expr.app.injEq] at hl
      have hs := F8EtaK.appsSpine_fst_of_eq_foldApps_const hl.1
      simp [appsSpine] at hs
  | _, _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, _, .consts .., hx => nomatch hx
  | _, _, _, _, .bvarZeta .., hx => nomatch hx
  | _, _, _, _, .delta .., hx => nomatch hx
  | _, _, _, _, .lam .., hx => nomatch hx
  | _, _, _, _, .pi .., hx => nomatch hx
  | _, _, _, _, .letE .., hx => nomatch hx
  | _, _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, _, .lit .., hx => nomatch hx
  | _, _, _, _, .eta .., hx => nomatch hx

/-- The head is preserved along every existing certified star. The sole
recursive call consumes the original star's literal tail `ps`. -/
private theorem xAppStar_target :
    {x j T : Expr Nat} →
    (s : CStar emptyEnv 0 (ProofLeaf emptyEnv 0) etaLeafCtx x j T) →
    (a : Expr Nat) → x = .app (.bvar 1) a →
    ∃ a' : Expr Nat, j = .app (.bvar 1) a'
  | _, _, _, .refl _ _ _ _, a, hx => ⟨a, hx⟩
  | _, _, _, .tail p ps, a, hx => by
      obtain ⟨a', hp⟩ := xAppStep_target a p.cert hx
      exact xAppStar_target ps a' hp

/-- No ordinary certified star from `f` can meet a one-step reduct of
`d`, even at independent type indices and with no decoration restrictions. -/
theorem canonical_eta_no_star_step_join {j T₁ T₂ : Expr Nat}
    (s : CStar emptyEnv 0 (ProofLeaf emptyEnv 0) etaLeafCtx etaLeafF j T₁)
    (p : CStep emptyEnv 0 (ProofLeaf emptyEnv 0) etaLeafCtx
      (.lam etaLeafP etaLeafBody') j T₂) : False := by
  obtain ⟨a', he⟩ := xAppStar_target s (.bvar 0) rfl
  obtain ⟨A', b', hd⟩ := lamStep_target (nativeLeafIface emptyEnv 0)
    etaLeafBody'_not_eta empty_d_notProof p.cert rfl
  rw [he] at hd
  cases hd

/-- Every coherent star repair of the reversed peak has more than one
step on its lambda side. This quantifies over all such repairs. -/
theorem canonical_eta_reverse_right_not_short
    (j : CoherentConsumerAudit.StarStepJoin (nativeLeafIface emptyEnv 0)
      etaLeafCtx_wf (etaPeakStep emptyEnv 0) (lamPeakStep emptyEnv 0)) :
    ¬ CoherentConsumerAudit.AtMostOne j.right := by
  intro hs
  let p := CoherentConsumerAudit.stepOf_short (nativeLeafIface emptyEnv 0)
    etaLeafCtx_wf j.right hs j.rightCoherent
  exact canonical_eta_no_star_step_join j.left p.1

/-- In the reversed eta-left/lambda-right orientation, no arbitrary
certified left star can meet any single certified right step. This rules
out all alternative joins, not merely the exhibited two-step repair. -/
theorem canonical_eta_no_asymmetric_reverse :
    ¬ Nonempty (CoherentConsumerAudit.AsymmetricStepJoin
      (nativeLeafIface emptyEnv 0) etaLeafCtx_wf
      (etaPeakStep emptyEnv 0) (lamPeakStep emptyEnv 0)) := by
  rintro ⟨j⟩
  exact canonical_eta_no_star_step_join j.left j.right

/-- The asymmetric consumer's ordered global local-peak premise is also
false for the admitted canonical instance: its reverse eta row fails. -/
theorem admitted_canonical_asymmetricDiamond_false :
    Nonempty (EnvWfT emptyEnv) ∧
      ¬ Nonempty (CoherentConsumerAudit.AsymmetricDiamond
        (nativeLeafIface emptyEnv 0)) := by
  refine ⟨⟨.empty⟩, ?_⟩
  rintro ⟨D⟩
  exact canonical_eta_no_asymmetric_reverse
    ⟨D etaLeafCtx_wf (etaPeakStep emptyEnv 0) (lamPeakStep emptyEnv 0)
      (CoherentEtaAudit.peak_source_deco emptyEnv 0).symm⟩

/-- The equivalent short-right-star formulation cannot hold globally
for the same admitted canonical instance. -/
theorem admitted_canonical_shortRightDiamond_false :
    Nonempty (EnvWfT emptyEnv) ∧
      ¬ Nonempty (CoherentConsumerAudit.ShortRightDiamond
        (nativeLeafIface emptyEnv 0)) := by
  refine ⟨⟨.empty⟩, ?_⟩
  rintro ⟨D⟩
  exact admitted_canonical_asymmetricDiamond_false.2
    ⟨CoherentConsumerAudit.asymmetricOf_shortRight (nativeLeafIface emptyEnv 0) D⟩

#print axioms canonical_eta_no_join
#print axioms canonical_eta_no_stepJoin
#print axioms admitted_canonical_coherentDiamond_false
#print axioms canonical_eta_no_star_step_join
#print axioms canonical_eta_reverse_right_not_short
#print axioms canonical_eta_no_asymmetric_reverse
#print axioms admitted_canonical_asymmetricDiamond_false
#print axioms admitted_canonical_shortRightDiamond_false

end Rcic.Declarative.NativeValleys.CoherentCounterexampleAudit
