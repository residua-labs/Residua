import rcic.RcicNativeTypedModelTypingFin
import rcic.RcicNativeTypedModelSubst

/-!
# `RcicNativeTypedModelCovArms` — named supplies + assembly + exercises for the
  `ApproxT` CTyCov strong induction (§4B, `devin/swe-ctycov`, #7738/#7737/#7749).

`RcicNativeTypedModelTypingFin` discharges **8 of 9** `HasTyT` constructors
(`sort`, `bvar`, `pi`, `lam`, `app`, `letE`, `lit`, `conv`) and **14 of 18**
`ConvT` constructors (`refl`, `symm`, `trans`, `zetaLocal`, `delta`, `iota`,
`lit`, `app`, `lam`, `pi`, `sorts`, `consts`, `irr`, `tyConv`) directly on
`ApproxT E`.  The remaining `CovModelCases` fields — `const`, `beta`, `zeta`,
`letEConv`, `eta` — plus the `iota` model law are **not unconditional theorems**
on `ApproxT`: each one is refuted at a concrete member or redex.  This module
packages them as the named-supply structure `CovApproxArms` (one structure
field per arm, each recording exactly what the arm needs), assembles
`CovModelCases` and the simultaneous `TypingLemmaEnvCovT`/`ConvSoundEnvCovT`
from a supply, and exercises the supply shapes non-degenerately:

* `memberDeltaCov`/`memberRigidCov`/`memberRecCovRec`/`memberRecCovProp` — the
  four `ApproxT` clauses of `HasTyT.const` (`MemberDeltaCovT`, `MemberRigidCovT`,
  `MemberRecCovT`): the member's `instantiateLevels ls m.mtype` must denote a
  `CTyCov`-covering code for every const compact.  Refuted at `natEnvU`
  (`not_memberRigidCovT_natEnvU`, `not_memberRecCovT_natEnvU`), hence per-member.
* `beta`/`zeta` — the backward direction needs `TypingFin.ArgTypedFinAt` at the
  redex (`covConv_beta_of_argTypedFinAt`, `covConv_zeta_of_argTypedFinAt`); the
  forward is unconditional (`covConv_beta_fwd`, `covConv_zeta_fwd`).  Refuted
  at `cexPolyId` (`not_semEqT_polyId_beta` below), hence per-redex.
* `letEConv` — needs the `zeta` `SemEqT` on both sides plus the let-binding
  environment (`denT` of the value), via `covConv_letE_of_zeta`.
* `eta` — needs η-saturation of the lam denotations; refuted at rigid
  constants (`not_semEqT_eta_natSucc`).
* `iota` — `ModelIotaStepT`: derived-ι pairs denote equally; supplied per-env
  (e.g. via `modelIotaStepT_of_iotaSoundT`), not from `ApproxT.recursorProp`
  (`Eq.rec` reads as its minor, #7749).

The β direction uses the unconditional `modelSubstFactorT_approxT` of
`devin/swe-modelsubst` (#7746) via the field-identical bridge
`typingFinModelSubstFactorT_approxT`.

`closure_claim = 0`.  No `sorry`, no `Classical.choice`, axioms
`⊆ {propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}

/-- The #7746 `TypedModelAudit.ModelSubstFactorT` instance fills the
    `TypingFin.ModelSubstFactorT` consumer shape field-for-field — the two
    structures are text-identical. -/
theorem typingFinModelSubstFactorT_approxT (E : ResolvedEnv) :
    TypingFin.ModelSubstFactorT (ctxModelT_approxT E) where
  subst0_intro := (modelSubstFactorT_approxT E).subst0_intro
  subst0_factor := (modelSubstFactorT_approxT E).subst0_factor

/-- **Named supplies for the remaining `CovModelCases` arms on `ApproxT E`.**
    One structure field per arm; each docstring records exactly what the arm
    needs and the counterexample that keeps it from being unconditional. -/
structure CovApproxArms (E : ResolvedEnv) (n : Nat) : Prop where
  /-- `HasTyT.const`, `ApproxT.delta` arm: every compact of the instantiated
      transparent body is `CTyCov`-covered at `instantiateLevels ls m.mtype`
      (`MemberDeltaCovT`).  Needs: the member's type denotes a covering code —
      checking at `EnvT.bot` suffices by closed mtype
      (`constCovClauseT_iff_bot` + `envWfT_member_mtype_closed`). -/
  memberDeltaCov : MemberDeltaCovT E n
  /-- `HasTyT.const`, `ApproxT.const` rigid arm: `ElTCov` of `.spine r []` at
      `instantiateLevels ls m.mtype` (`MemberRigidCovT`).  Refuted at `natEnvU`
      (`not_memberRigidCovT_natEnvU`: `Nat.succ`'s spine outruns the codomain's
      denotations) ⇒ per-member supply. -/
  memberRigidCov : MemberRigidCovT E n
  /-- `HasTyT.const`, `ApproxT.recursor` arm (non-strict major): the
      `curryStepT (us_pre ++ [ctorDemandT ..]) c` output is covered at
      `instantiateLevels ls m.mtype`.  `MemberRecDiagT` is FALSE on `natEnvU`
      (#7737; `not_memberRecCovT_natEnvU`) ⇒ named per-witness supply, not
      derived from `ApproxT.recursorProp`. -/
  memberRecCovRec : ∀ {w : IotaWitnessS E} {ls : List Level} {m : CheckedMember},
    E.members w.recRef = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ {us_pre us_fields : List (List CptT)} {c : CptT},
      ¬ PropFamilyS w →
      us_pre.length = w.preMajor.length → us_fields.length = w.fields.length →
      ApproxT E (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c →
      ElTCov E EnvT.bot (instantiateLevels ls m.mtype)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
  /-- `HasTyT.const`, `ApproxT.recursorProp` arm (strict, Prop-major family):
      the `curryStepT (us_pre ++ [[]]) c` output is covered at
      `instantiateLevels ls m.mtype`.  `Eq.rec` reads as its minor whatever
      the indices (#7749, `eqRec_model_minor`) ⇒ named per-witness supply. -/
  memberRecCovProp : ∀ {w : IotaWitnessS E} {ls : List Level} {m : CheckedMember},
    E.members w.recRef = some m → ls.length = m.arity → levelsBounded n ls = true →
    ∀ {us_pre : List (List CptT)} {c : CptT},
      PropFamilyS w →
      us_pre.length = w.preMajor.length →
      ApproxT E (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c →
      ElTCov E EnvT.bot (instantiateLevels ls m.mtype)
        (curryStepT (us_pre ++ [[]]) c)
  /-- `ConvT.beta`: the backward direction `ApproxT (instantiate0 arg body) c →
      ApproxT (.app (.lam A body) arg) c` needs `TypingFin.ArgTypedFinAt` at the
      redex — the argument's finite demand lists jointly `CTyS`-typed at one
      code of `A` (`covConv_beta_of_argTypedFinAt`; forward is
      `covConv_beta_fwd`, unconditional).  Refuted at `cexPolyId`
      (`not_semEqT_polyId_beta`) ⇒ per-redex named supply. -/
  beta : ∀ {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A),
    IHBelowCov E n (sizeOf (ConvT.beta Γ A body arg B u hA hb harg)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.app (.lam A body) arg) (instantiate0 arg body)
  /-- `ConvT.zeta`: same backward-expansion need as `beta` at `(value, A)`
      (`covConv_zeta_of_argTypedFinAt`; `SemEqT` reduces to β through
      `approxT_letE_iff`).  Per-let named supply. -/
  zeta : ∀ {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    IHBelowCov E n (sizeOf (ConvT.zeta Γ A value body B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.letE A value body) (instantiate0 value body)
  /-- `ConvT.letE`: needs the `zeta` `SemEqT` on both `(A, v, b)` and
      `(A', v', b')` plus `ElTCov` typing of `v`'s compacts to build the
      let-binding context env (`covConv_letE_of_zeta`) — the step-demand envs
      (`demandT s.1`) do not match the let-binding env (`denT v`) in general. -/
  letEConv : ∀ {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ v v' A) (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    IHBelowCov E n (sizeOf (ConvT.letE Γ A A' v v' b b' B u hA hv hb)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.letE A v b) (.letE A' v' b')
  /-- `ConvT.eta`: needs η-saturation of `f`'s lam denotations (a fabricated
      lam compact whose steps are demanded extensions of `f`'s steps must
      itself denote at `f`), and joint `CTyS` of the demands at a domain code.
      Refuted at rigid constants (`not_semEqT_eta_natSucc`) ⇒ named supply. -/
  eta : ∀ {Γ : LCtx} {f A B : Expr Nat} (h : HasTyT E n Γ f (.pi A B)),
    IHBelowCov E n (sizeOf (ConvT.eta Γ f A B h)) →
    ∀ {ρ : EnvT}, EnvTypedCovAtT E Γ ρ → SemEqT E ρ (.lam A (.app (lift 0 1 f) (.bvar 0))) f
  /-- `ConvT.iota`: needs derived-ι denotation equality —
      `ModelIotaStepT E (ctxModelT_approxT E)`, supplied per-env (e.g. via
      `modelIotaStepT_of_iotaSoundT`).  The `ApproxT.recursor`/`recursorProp`
      clauses compute `curryStepT` outputs; `Eq.rec` reads as its minor
      (#7749) ⇒ named supply, not derived from `recursorProp`. -/
  iota : TypingFin.ModelIotaStepT E (ctxModelT_approxT E)

/-- **`CovModelCases` on `ApproxT E` from `CovApproxArms`**: `const` is assembled
    from the three member arms through `constCovClauseT_of_arms` +
    `covTyping_const`; `beta`, `zeta`, `letEConv`, `eta` are the named supplies
    themselves. -/
theorem covModelCases_of_covApproxArms (hW : EnvWfT E) (S : CovApproxArms E n) :
    CovModelCases E n where
  const {_Γ _r _ls _m} hres hlen hwf {_ρ} hρ {_u} hu :=
    covTyping_const
      (constCovClauseT_of_arms hW S.memberDeltaCov S.memberRigidCov
        fun {_w _ls _m} hres hlen hbound =>
          ⟨S.memberRecCovRec hres hlen hbound, S.memberRecCovProp hres hlen hbound⟩)
      hres hlen hwf hρ hu
  beta := S.beta
  zeta := S.zeta
  letEConv := S.letEConv
  eta := S.eta

/-- **Simultaneous `TypingLemmaEnvCovT` + `ConvSoundEnvCovT` on `ApproxT E` from
    `CovApproxArms`** (`typingLemmaEnvCovT_and_convSound_of_arms`): discharges
    `ModelSubstFactorT` unconditionally via `covModelSubstFactorT_approxT`. -/
theorem typingLemmaEnvCovT_and_convSound_of_arms (hW : EnvWfT E) (S : CovApproxArms E n) :
    TypingLemmaEnvCovT E n ∧ ConvSoundEnvCovT E n :=
  typingLemmaEnvCovT_and_convSound_of_cases_approxT hW S.iota
    (covModelCases_of_covApproxArms hW S)

/-! ### Exercises — non-degenerate instances of the named-supply shapes -/

/-- **polyId, negative**: `SemEqT` for β fails at `cexPolyId` even for the
    singleton-demand body `bvar 0`: `polyIdCpt01 ∈ den(cexPolyId)` but no code
    of `cexPolyIdTy` types it (`not_elT_polyId_cpt01`), so no joint-typed lam
    step outputs it.  This is why `beta` is a named per-redex supply. -/
theorem not_semEqT_polyId_beta (E : ResolvedEnv) (ρ : EnvT) :
    ¬ SemEqT E ρ (.app (.lam TypingFin.cexPolyIdTy (.bvar 0)) TypingFin.cexPolyId)
      TypingFin.cexPolyId := by
  intro hse
  have hlhs : ApproxT E ρ (.app (.lam TypingFin.cexPolyIdTy (.bvar 0)) TypingFin.cexPolyId)
      polyIdCpt01 :=
    (hse polyIdCpt01).mpr (approxT_cexPolyId_cpt01 E ρ)
  rcases approxT_app_inv hlhs with h0 | ⟨g, s, hs2, hlam, hsg, _⟩ | ⟨r, args, u, hsp, hlam, _⟩
  · exact CptT.noConfusion h0
  · rcases approxT_lam_inv hlam with hbot | ⟨a, g', heq, hAa, _, hg⟩
    · exact CptT.noConfusion hbot
    · injection heq with heq'; subst heq'
      have hb2 := (hg s hsg).2
      rw [← hs2] at hb2
      rcases approxT_bvar_inv hb2 with h0 | hmem
      · exact CptT.noConfusion h0
      · exact not_elT_polyId_cpt01 E ρ ⟨a, hAa, (hg s hsg).1 polyIdCpt01 hmem⟩
  · rcases approxT_lam_inv hlam with hbot | ⟨_, _, heq, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-- **polyId, positive**: at the same `cexPolyId` argument with the constant
    body `.sort .zero`, β needs no demand typing at all — the fabricated lam
    `[([], sortCode .zero)]` closes `SemEqT`.  β on `ApproxT` is per-redex, not
    per-argument. -/
theorem semEqT_polyId_beta_sort (E : ResolvedEnv) (ρ : EnvT) :
    SemEqT E ρ (.app (.lam TypingFin.cexPolyIdTy (.sort .zero)) TypingFin.cexPolyId)
      (.sort .zero) := by
  intro c
  constructor
  · intro h
    have hfwd := covConv_beta_fwd (typingFinModelSubstFactorT_approxT E) ρ
      TypingFin.cexPolyIdTy (.sort .zero) TypingFin.cexPolyId h
    rwa [instantiate0] at hfwd
  · intro h
    rcases approxT_sort_inv h with rfl | rfl
    · exact .bot _ _
    · have hlam : ApproxT E ρ (.lam TypingFin.cexPolyIdTy (.sort .zero))
          (.lam [([], sortCode .zero)]) := by
        refine .lam (.bot _ _) ?_ ⟨([], sortCode .zero), List.mem_singleton.mpr rfl, ?_⟩ ?_
        · intro s hs u hu
          rcases List.mem_singleton.mp hs with rfl
          exact (List.not_mem_nil _ hu).elim
        · rw [sortCode_zero]
          exact CptT.noConfusion
        · intro s hs
          rcases List.mem_singleton.mp hs with rfl
          exact .sort _ _
      exact .app hlam (List.mem_singleton.mpr rfl) (fun u hu => (List.not_mem_nil _ hu).elim)

/-- **Nat.rec on `natEnvUWfT`**: at the witness `covWNatSucc` the `.spine 1 []`
    schema output yields `covGoodRecCpt`, which IS in `ElTCov` at the
    instantiated recursor mtype — the good branch of the `memberRecCov` named
    supply (the bad branch is refuted by `not_memberRecCovT_natEnvU`). -/
theorem memberRecCov_covWNatSucc_good :
    ElTCov natEnvU EnvT.bot (instantiateLevels [.succ .zero] natRecMemberU.mtype)
      covGoodRecCpt :=
  elTCov_natRec_covGoodRecCpt EnvT.bot

/-- **A let in context, `zeta` supply at `letSort1`**: the value's compacts at
    `sortCode (.succ .zero)` are jointly `CTyS`-typed at `.sort`, discharging
    `ArgTypedFinAt`; `covConv_zeta_of_argTypedFinAt` then yields the `zeta`
    `SemEqT`. -/
theorem argTypedFinAt_letSort1 (E : ResolvedEnv) (ρ : EnvT) :
    TypingFin.ArgTypedFinAt E ρ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  intro us hus
  refine ⟨.sort, ?_, fun u hu => ?_⟩
  · have := approxT_sort_code E ρ (.succ (.succ .zero))
    rwa [TypingFin.sortCode_succ] at this
  · rcases approxT_sort_inv (hus u hu) with rfl | rfl
    · exact ctyS_bot _
    · rw [TypingFin.sortCode_succ]
      exact ctyS_sort_sort E

theorem covZeta_letSort1 (E : ResolvedEnv) (ρ : EnvT) :
    SemEqT E ρ letSort1 (instantiate0 (.sort (.succ .zero)) (.bvar 0)) :=
  covConv_zeta_of_argTypedFinAt (typingFinModelSubstFactorT_approxT E)
    (argTypedFinAt_letSort1 E ρ)

#print axioms typingFinModelSubstFactorT_approxT
#print axioms CovApproxArms
#print axioms covModelCases_of_covApproxArms
#print axioms typingLemmaEnvCovT_and_convSound_of_arms
#print axioms not_semEqT_polyId_beta
#print axioms semEqT_polyId_beta_sort
#print axioms memberRecCov_covWNatSucc_good
#print axioms argTypedFinAt_letSort1
#print axioms covZeta_letSort1

end Rcic.Declarative.NativeValleys.TypedModelAudit
