import rcic.RcicNativeTypedModelCovWConvUniverse

/-! A larger, explicit completeness fragment of the full guarded grammar:
products whose domain and codomain are bare universes.  The witnesses use the
ordinary public observations and produce native ConvT.pi derivations. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open TypedModelCovWIrrelAudit

def covWConvPiSortCode (u v : Level) : CptWConv :=
  .pi (.sort (LevelCode.ofLevel u)) [([], .sort (LevelCode.ofLevel v))]

theorem covWConv_pi_sort_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWConvR) (u v : Level) :
    CovWConvObservation E n Γ ρ (.pi (.sort u) (.sort v))
      (covWConvPiSortCode u v) := by
  refine ⟨.pi (.sort u) [([], .sort v)], rfl, .pi (.sort Γ ρ u) ?_ ?_⟩
  · intro s hs c hc
    obtain rfl := List.mem_singleton.mp hs
    cases hc
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .sort _ _ v

/-- The whole displayed finite observation determines both universe labels.
The codomain row is recovered from the mapped public row list. -/
theorem covWConv_pi_sort_observation_exact {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} (u v u' v' : Level) :
    CovWConvObservation emptyEnv n Γ ρ (.pi (.sort u) (.sort v))
      (covWConvPiSortCode u' v') ↔ eqN u u' ∧ eqN v v' := by
  constructor
  · rintro ⟨c, hc, ho⟩
    generalize heq : (Expr.pi (.sort u) (.sort v) : Expr Nat) = e at ho
    cases ho with
    | bot => cases hc
    | bvar => cases heq
    | sort => cases heq
    | const => cases heq
    | recursor => cases heq
    | pi hA ht hb =>
      cases heq
      have hp := CptWConv.pi.inj hc
      have hdom : eqN u u' :=
        (covWConv_sort_observation_exact u u').mp ⟨_, hp.1, hA⟩
      have hmem : (([] : List CptWConv), CptWConv.sort (LevelCode.ofLevel v')) ∈
          [([], CptWConv.sort (LevelCode.ofLevel v'))] := List.mem_singleton.mpr rfl
      rw [← hp.2, covWConv_code_rows] at hmem
      obtain ⟨s, hs, hscode⟩ := List.mem_map.mp hmem
      have hbody : eqN v v' :=
        (covWConv_sort_observation_exact v v').mp
          ⟨s.2, congrArg Prod.snd hscode, hb s hs⟩
      exact ⟨hdom, hbody⟩
    | lam => cases heq
    | app => cases heq
    | appSpine => cases heq
    | delta => cases heq
    | letE => cases heq
    | lit => cases heq
    | iota w hl hr h => cases w.hrec
    | recursorPropK w x hk h => cases w.hrec
    | eta he hD ht hn hb => cases hc
  · rintro ⟨hu, hv⟩
    have heu := (LevelCode.ofLevel_eq_iff u u').mpr hu
    have hev := (LevelCode.ofLevel_eq_iff v v').mpr hv
    have hcode : covWConvPiSortCode u v = covWConvPiSortCode u' v' := by
      unfold covWConvPiSortCode
      rw [heu, hev]
    rw [← hcode]
    exact covWConv_pi_sort_observed emptyEnv n Γ ρ u v

theorem covWConv_pi_sort_observations_determine_levels {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {u v u' v' : Level}
    (h : ∀ c,
      CovWConvObservation emptyEnv n Γ ρ (.pi (.sort u) (.sort v)) c ↔
      CovWConvObservation emptyEnv n Γ ρ (.pi (.sort u') (.sort v')) c) :
    eqN u u' ∧ eqN v v' :=
  (covWConv_pi_sort_observation_exact u v u' v').mp
    ((h (covWConvPiSortCode u' v')).mpr
      (covWConv_pi_sort_observed emptyEnv n Γ ρ u' v'))

/-- An actual native derivation, at the canonical universe of the left Pi. -/
def covWConv_pi_sort_complete {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {u v u' v' : Level}
    (h : ∀ c,
      CovWConvObservation emptyEnv n Γ ρ (.pi (.sort u) (.sort v)) c ↔
      CovWConvObservation emptyEnv n Γ ρ (.pi (.sort u') (.sort v')) c) :
    ConvT emptyEnv n Γ (.pi (.sort u) (.sort v)) (.pi (.sort u') (.sort v'))
      (.sort (.imax (.succ u) (.succ v))) := by
  have he := covWConv_pi_sort_observations_determine_levels h
  exact .pi Γ (.sort u) (.sort u') (.sort v) (.sort v') (.succ u) (.succ v)
    (.sorts Γ u u' he.1)
    (.sorts (.assumption (.sort u) :: Γ) v v' he.2)

def covWConv_pi_sort_native_typed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (u v : Level) :
    HasTyT E n Γ (.pi (.sort u) (.sort v)) (.sort (.imax (.succ u) (.succ v))) :=
  .pi Γ (.sort u) (.succ u) (.sort v) (.succ v)
    (.sort Γ u) (.sort (.assumption (.sort u) :: Γ) v)

/-- For well-formed contexts the full raw grammar gives no additional sort
shapes: in particular, the typed eta rule cannot apply to a universe. -/
theorem covWConv_empty_raw_sort_shape {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    (hΓ : CtxWfT emptyEnv n Γ) {u : Level} {c : CptWConvR}
    (ho : ApproxTKWConv emptyEnv n Γ ρ (.sort u) c) :
    c = .bot ∨ c = .sort u := by
  generalize heq : (Expr.sort u : Expr Nat) = e at ho
  cases ho with
  | bot => exact Or.inl rfl
  | bvar => cases heq
  | sort => cases heq; exact Or.inr rfl
  | const => cases heq
  | recursor => cases heq
  | pi => cases heq
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w hl hr h => cases w.hrec
  | recursorPropK w x hk h => cases w.hrec
  | eta he hD ht hn hb =>
    cases heq
    exact (covWIrrel_native_not_sort_and_pi (.empty : EnvWfT emptyEnv)
      trivial hΓ (.sort Γ u) he).elim

theorem covWConv_empty_sort_observation_shape {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} (hΓ : CtxWfT emptyEnv n Γ) (u : Level) (c : CptWConv) :
    CovWConvObservation emptyEnv n Γ ρ (.sort u) c ↔
      c = .bot ∨ c = .sort (LevelCode.ofLevel u) := by
  constructor
  · rintro ⟨d, hd, ho⟩
    rcases covWConv_empty_raw_sort_shape hΓ ho with rfl | rfl
    · exact Or.inl hd.symm
    · exact Or.inr hd.symm
  · rintro (rfl | rfl)
    · exact ⟨.bot, rfl, .bot Γ ρ (.sort u)⟩
    · exact ⟨.sort u, rfl, .sort Γ ρ u⟩

/-- Full observation invariance is proved here for the bare-sort fragment. -/
theorem covWConv_empty_sort_invariant {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    (hΓ : CtxWfT emptyEnv n Γ) {u v : Level} (he : eqN u v) (c : CptWConv) :
    CovWConvObservation emptyEnv n Γ ρ (.sort u) c ↔
      CovWConvObservation emptyEnv n Γ ρ (.sort v) c := by
  rw [covWConv_empty_sort_observation_shape hΓ u c,
    covWConv_empty_sort_observation_shape hΓ v c,
    (LevelCode.ofLevel_eq_iff u v).mpr he]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_UNIVERSE_FRAGMENT_ROOTS
#print axioms covWConv_pi_sort_observed
#print axioms covWConv_pi_sort_observation_exact
#print axioms covWConv_pi_sort_observations_determine_levels
#print axioms covWConv_pi_sort_complete
#print axioms covWConv_pi_sort_native_typed
#print axioms covWConv_empty_raw_sort_shape
#print axioms covWConv_empty_sort_observation_shape
#print axioms covWConv_empty_sort_invariant
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_UNIVERSE_FRAGMENT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
