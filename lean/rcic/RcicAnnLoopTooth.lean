import rcic.RcicAnnLRStuckDatumG
import rcic.RcicAnnLREnv

/-!
# DT-025 / A-6 — the R-A6-S1b′ tooth: a recursor-site loop, admitted by `EnvSemA`, refused by `EnvSemAg`

The erratum R-A6-S1b′ recorded (`RcicAnnDecl.lean:46-72`): the argument that semantic
environment well-formedness excludes a looping ι ("the head constant's membership at its pi
type puts the stuck application into the relation at the codomain, which demands a normal
form") was unsound for main's relation — main's `stuck` clause demands NO normal form. The
guarded copy's does (S1-g.2). This file machine-checks the separation at one environment:

* the environment `toothEnvA`: axioms `X : Sort 1`, `Y : X → Sort 1`, and a member `r : Π x : X, Y x`
  of RECURSOR class, so ι may fire at its full-arity spines (`IotaRecHeadA`);
* the oracle `toothLoopA`: at a full-arity `r` spine it answers the spine itself — `r x` steps to
  `r x` forever (`toothLoop_no_whnf`); it is positional, lift- and substitution-stable;
* `toothLoop_envSemA`: main's `EnvSemA` HOLDS — `X`, `Y` by reflection (`envSemClauseA_rigid`), `r` by
  its pi clause, whose codomain `Y a` is stuck, where main's relation is typed-and-convertible;
* `toothLoop_not_envSemAg`: the guarded `EnvSemAg` FAILS — `r` related at its pi type puts `r x`
  into the guarded relation at the stuck, non-`Prop` `Y x`, whose datum is a head chain to a
  normal form (`hstuck_of_datumg`), and `r x` has none.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the environment and the looping oracle -/

/-- `X : Sort 1` (an axiom). -/
def toothXA : CheckedMemberA := ⟨.axiomM, 0, .sort (.succ .zero), none, 0, none⟩

/-- `Y : X → Sort 1` (an axiom). -/
def toothYA : CheckedMemberA :=
  ⟨.axiomM, 0, .pi (.const 0 []) (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero)), none, 0, none⟩

/-- `r : Π x : X, Y x` (a member of RECURSOR class). -/
def toothRA : CheckedMemberA :=
  ⟨.recursorM, 0, .pi (.const 0 []) (.succ .zero) (.app (.const 1 []) (.bvar 0)) (.succ .zero), none, 0, none⟩

def toothE1A : ResolvedEnvA := extendEnvA emptyEnvA 0 toothXA
def toothE2A : ResolvedEnvA := extendEnvA toothE1A 1 toothYA
def toothEnvA : ResolvedEnvA := extendEnvA toothE2A 2 toothRA

/-- the loop's trigger: a spine headed by `r` with exactly one argument (its full arity). -/
def toothSpineB (p : ExprA × List ExprA) : Bool :=
  match p.1 with
  | .const r _ => r == 2 && p.2.length == 1
  | _ => false

/-- the LOOPING ι: at a full-arity `r` spine it answers the spine itself. -/
def toothLoopA : IotaIfaceA where
  fn := fun e => if toothSpineB (appsSpineA e) then some e else none

def toothCtxA : LCtxA := [.assumption (.const 0 [])]

theorem toothSpineB_liftA (c : Nat) (e : ExprA) :
    toothSpineB (appsSpineA (liftA c 1 e)) = toothSpineB (appsSpineA e) := by
  rw [appsSpineA_liftA]
  have hna := appsSpineA_fst_not_app e
  generalize appsSpineA e = p at hna ⊢
  obtain ⟨h, xs⟩ := p
  simp only at hna ⊢
  cases h with
  | bvar i => simp only [liftA]; split <;> simp [toothSpineB]
  | app f x => exact absurd rfl (hna f x)
  | _ => simp [toothSpineB, liftA, List.length_map]

theorem toothLoop_lift : IotaLiftA toothLoopA := fun c e => by
  show (if toothSpineB (appsSpineA (liftA c 1 e)) then some (liftA c 1 e) else none) =
    (if toothSpineB (appsSpineA e) then some e else none).map (liftA c 1)
  rw [toothSpineB_liftA]
  split <;> rfl

theorem toothSpineB_const {e : ExprA} (h : toothSpineB (appsSpineA e) = true) :
    ∃ ls, (appsSpineA e).1 = .const 2 ls ∧ (appsSpineA e).2.length = 1 := by
  unfold toothSpineB at h
  revert h
  generalize (appsSpineA e).1 = hd
  cases hd <;> simp

theorem toothLoop_fn {e e' : ExprA} (h : toothLoopA.fn e = some e') :
    toothSpineB (appsSpineA e) = true ∧ e' = e := by
  show toothSpineB (appsSpineA e) = true ∧ e' = e
  have h' : (if toothSpineB (appsSpineA e) then some e else none) = some e' := h
  split at h'
  · exact ⟨by assumption, (Option.some.inj h').symm⟩
  · exact Option.noConfusion h'

theorem toothLoop_subst : IotaSubstA toothLoopA := fun σ e e' h => by
  obtain ⟨hb, he⟩ := toothLoop_fn h
  rw [he]
  obtain ⟨ls, hh, hl⟩ := toothSpineB_const hb
  show (if toothSpineB (appsSpineA (substA σ e)) then some (substA σ e) else none) = some (substA σ e)
  rw [appsSpineA_substA_const σ e hh]
  simp [toothSpineB, hl, List.length_map]

theorem toothLoop_recHead : IotaRecHeadA toothEnvA toothLoopA := fun e e' h => by
  obtain ⟨hb, _⟩ := toothLoop_fn h
  obtain ⟨ls, hh, hl⟩ := toothSpineB_const hb
  exact ⟨2, ls, toothRA, hh, rfl, rfl, hl⟩

theorem toothEnv_closed : EnvClosedA toothEnvA := fun r m h => by
  unfold toothEnvA toothE2A toothE1A extendEnvA emptyEnvA at h
  simp only at h
  split at h
  · cases h; exact ⟨fun k => rfl, fun _ hb => Option.noConfusion hb⟩
  · split at h
    · cases h; exact ⟨fun k => rfl, fun _ hb => Option.noConfusion hb⟩
    · split at h
      · cases h; exact ⟨fun k => rfl, fun _ hb => Option.noConfusion hb⟩
      · exact Option.noConfusion h

/-- no member of the tooth's environment is a constructor (`X`, `Y` axioms, `r` a recursor). -/
theorem toothEnv_noCtor {r : Nat} {m : CheckedMemberA} (h : toothEnvA.members r = some m) :
    m.mclass ≠ .constructorM := by
  unfold toothEnvA toothE2A toothE1A extendEnvA emptyEnvA at h
  simp only at h
  split at h
  · cases h; exact fun h => MemberClass.noConfusion h
  · split at h
    · cases h; exact fun h => MemberClass.noConfusion h
    · split at h
      · cases h; exact fun h => MemberClass.noConfusion h
      · exact Option.noConfusion h

/-- R-NoDeltaRec-4d-iii's `hEN`/`hNC` at the tooth: vacuous, no constructor. -/
theorem toothEnv_normCtor : EnvNormCtorTypeA toothEnvA := fun _ _ h hc => absurd hc (toothEnv_noCtor h)
theorem toothEnv_normClosed : EnvNormClosedA toothEnvA := fun _ _ h hc => absurd hc (toothEnv_noCtor h)

/-- `r x` loops: no fuel reaches a normal form. -/
theorem toothLoop_step (Γ : LCtxA) (a : ExprA) :
    hStepFnA toothEnvA toothLoopA.fn Γ (.app (.const 2 []) a) = some (.app (.const 2 []) a) := by
  rw [hStepFnA_app_nonlam toothEnvA toothLoopA.fn _ a (fun _ _ _ h => ExprA.noConfusion h)]
  rfl

theorem toothLoop_no_whnf (Γ : LCtxA) (a : ExprA) :
    ∀ fuel, whnfA toothEnvA toothLoopA.fn Γ fuel (.app (.const 2 []) a) = none
  | 0 => by simp only [whnfA, toothLoop_step]
  | fuel + 1 => by simp only [whnfA, toothLoop_step]; exact toothLoop_no_whnf Γ a fuel

/-! ## (2) typings, in any environment containing the members -/

section Typings
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def toothX_ty (hX : E.members 0 = some toothXA) (Γ : LCtxA) :
    HasTyA E I n Γ (.const 0 []) (.sort (.succ .zero)) :=
  .const Γ 0 [] toothXA (.succ (.succ .zero)) hX rfl rfl (.sort Γ (.succ .zero))

def toothY_ty (hX : E.members 0 = some toothXA) (hY : E.members 1 = some toothYA) (Γ : LCtxA) :
    HasTyA E I n Γ (.const 1 []) toothYA.mtypeA :=
  .const Γ 1 [] toothYA (.imax (.succ .zero) (.succ (.succ .zero))) hY rfl rfl
    (.pi Γ (.const 0 []) (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero)) (toothX_ty hX Γ)
      (.sort _ _))

def toothYx_ty (hX : E.members 0 = some toothXA) (hY : E.members 1 = some toothYA) (Γ : LCtxA)
    {a : ExprA} (ha : HasTyA E I n Γ a (.const 0 [])) :
    HasTyA E I n Γ (.app (.const 1 []) a) (.sort (.succ .zero)) :=
  .app Γ (.const 1 []) a (.const 0 []) (.sort (.succ .zero)) (.succ .zero) (.succ (.succ .zero))
    (.succ (.succ .zero)) (.sort _ _) (.sort _ _) (toothY_ty hX hY Γ) ha

def toothV0_ty (hX : E.members 0 = some toothXA) (Γ : LCtxA) :
    HasTyA E I n (.assumption (.const 0 []) :: Γ) (.bvar 0) (.const 0 []) :=
  .bvar _ 0 _ (.succ .zero) rfl (toothX_ty hX _)

def toothRty_ty (hX : E.members 0 = some toothXA) (hY : E.members 1 = some toothYA) (Γ : LCtxA) :
    HasTyA E I n Γ toothRA.mtypeA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ _ _ _ _ (toothX_ty hX Γ) (toothYx_ty hX hY _ (toothV0_ty hX Γ))

end Typings

theorem toothEnv_X : toothEnvA.members 0 = some toothXA := rfl
theorem toothEnv_Y : toothEnvA.members 1 = some toothYA := rfl
theorem toothEnv_R : toothEnvA.members 2 = some toothRA := rfl

def toothR_ty {I : IotaIfaceA} {n : Nat} (Γ : LCtxA) :
    HasTyA toothEnvA I n Γ (.const 2 []) toothRA.mtypeA :=
  .const Γ 2 [] toothRA (.imax (.succ .zero) (.succ .zero)) toothEnv_R rfl rfl
    (toothRty_ty toothEnv_X toothEnv_Y Γ)

def toothRx_ty {I : IotaIfaceA} {n : Nat} (Γ : LCtxA) {a : ExprA}
    (ha : HasTyA toothEnvA I n Γ a (.const 0 [])) :
    HasTyA toothEnvA I n Γ (.app (.const 2 []) a) (.app (.const 1 []) a) :=
  .app Γ (.const 2 []) a (.const 0 []) (.app (.const 1 []) (.bvar 0)) (.succ .zero) (.succ .zero)
    (.succ .zero) (toothYx_ty toothEnv_X toothEnv_Y _ (toothV0_ty toothEnv_X Γ))
    (toothYx_ty toothEnv_X toothEnv_Y Γ ha) (toothR_ty Γ) ha

/-- `Y a` is stuck: `Y` is an axiom (no δ) and ι refuses at a `Y`-headed spine. -/
theorem toothYx_stuck (Γ : LCtxA) (a : ExprA) :
    StuckA toothEnvA toothLoopA Γ (.app (.const 1 []) a) :=
  ⟨hStepFnA_constSpine_none toothLoop_recHead toothEnv_Y (Or.inl rfl)
      (fun h => MemberClass.noConfusion h) Γ _ rfl,
   not_isShapeHeadA_const toothEnv_Y (fun h => MemberClass.noConfusion h)⟩

/-! ## (3) main's `EnvSemA` holds -/

section Main
variable {n : Nat}

theorem toothR_clause {k₀ : Nat}
    (hT : ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA toothEnvA toothLoopA n Δ) →
      LRRelA toothEnvA toothLoopA n (fun _ => 1) k Δ (.sort (.imax (.succ .zero) (.succ .zero)))
        toothRA.mtypeA toothRA.mtypeA) :
    EnvSemClauseA toothEnvA toothLoopA n (fun _ => 1) 2 toothRA := by
  intro ls ls' hlen _ _ heq
  have hls : ls = [] := list_nil_of_length_zero ls hlen
  have hls' : ls' = [] :=
    list_nil_of_length_zero ls' ((eqNList_length ls ls' heq).symm.trans (hls ▸ rfl))
  subst hls; subst hls'
  show ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA toothEnvA toothLoopA n Δ) →
    LRRelA toothEnvA toothLoopA n (fun _ => 1) k Δ toothRA.mtypeA (.const 2 []) (.const 2 [])
  refine ⟨k₀, fun k hk Δ hΔ => ?_⟩
  obtain ⟨_, ⟨R, hR⟩, _, _, _, _⟩ := LRRelA_sort_elim (hT k hk Δ hΔ)
  have hnp : ¬ IsPropTy toothEnvA toothLoopA Δ toothRA.mtypeA := fun h => by
    have := (isPropTy_pi_iff toothEnvA toothLoopA Δ _ _ _ _).1 h
    cases this
  refine ⟨R, hR, ?_⟩
  rw [LRTyA_eq] at hR
  obtain ⟨RD, RC, hD, hC, _, e⟩ := tyKA_pi_inv hR hnp
  subst e
  refine ⟨fun ρ hρ a a' hr => ?_, ⟨toothR_ty Δ⟩, ⟨toothR_ty Δ⟩, ⟨.refl _ _ _ (toothR_ty Δ)⟩⟩
  obtain ⟨⟨ta⟩, ⟨ta'⟩⟩ := escapeA_hasTy (hD ρ hρ) hr
  obtain ⟨caa⟩ := escapeA (hD ρ hρ) hr
  have eX : wkExprA ρ (ExprA.const 0 []) = .const 0 [] := wkExprA_closed (e := .const 0 []) (fun _ => rfl) ρ
  rw [eX] at ta ta' caa
  have hCr := hC ρ hρ a a' hr
  have eC : instantiate0A a (wkExprA (WkSpecA.ub ρ) (.app (.const 1 []) (.bvar 0))) =
      .app (.const 1 []) a := by
    rw [wkExprA_app, wkExprA_closed (e := .const 1 []) (fun _ => rfl), wkExprA_ub_bvar0]
    rfl
  rw [eC] at hCr
  have tYa := toothYx_ty toothEnv_X toothEnv_Y (wkCtxA ρ Δ) ta
  rw [TyKA_unique hCr (.stuck (whTyA_of_hasTy tYa) (toothYx_stuck (wkCtxA ρ Δ) a))]
  have eR : wkExprA ρ (ExprA.const 2 []) = .const 2 [] := wkExprA_closed (e := .const 2 []) (fun _ => rfl) ρ
  rw [eR]
  have cYa : ConvA toothEnvA toothLoopA n (wkCtxA ρ Δ) (.app (.const 1 []) a') (.app (.const 1 []) a)
      (.sort (.succ .zero)) :=
    .app _ _ _ _ _ _ _ _ _ (.refl _ _ _ (toothY_ty toothEnv_X toothEnv_Y _)) (.symm _ _ _ _ caa)
      (.sort _ _) (toothYx_ty toothEnv_X toothEnv_Y _ ta)
  have tra' : HasTyA toothEnvA toothLoopA n (wkCtxA ρ Δ) (.app (.const 2 []) a') (.app (.const 1 []) a) :=
    .conv _ _ _ _ (.succ .zero) (.succ .zero) (toothRx_ty _ ta')
      (toothYx_ty toothEnv_X toothEnv_Y _ ta') (eqNA_refl _) tYa cYa
  refine ⟨⟨toothRx_ty _ ta⟩, ⟨tra'⟩, ⟨?_⟩⟩
  exact .app _ _ _ _ _ _ _ _ _ (.refl _ _ _ (toothR_ty _)) caa
    (toothYx_ty toothEnv_X toothEnv_Y _ (toothV0_ty toothEnv_X _)) tra'

theorem toothPre0 : PrefixA emptyEnvA toothEnvA := fun _ _ h => Option.noConfusion h

theorem toothPre1 : PrefixA toothE1A toothEnvA := fun r m h => by
  unfold toothE1A extendEnvA emptyEnvA at h
  simp only at h
  split at h
  · subst_vars; cases h; rfl
  · exact Option.noConfusion h

theorem toothPre2 : PrefixA toothE2A toothEnvA := fun r m h => by
  unfold toothE2A toothE1A extendEnvA emptyEnvA at h
  simp only at h
  split at h
  · subst_vars; cases h; rfl
  · split at h
    · subst_vars; cases h; rfl
    · exact Option.noConfusion h

theorem toothX_clause :
    EnvSemClauseA toothEnvA toothLoopA n (fun _ => 1) 0 toothXA := by
  have ih : EnvSemAt toothEnvA toothLoopA n (fun _ => 1) (domA emptyEnvA) :=
    fun _ _ hD _ => hD.elim fun _ hm => Option.noConfusion hm
  have harms := fundArmsA_at toothEnv_closed toothLoop_lift toothLoop_subst toothEnv_normCtor toothEnv_normClosed toothLoop_recHead
    posValA_one ih
  obtain ⟨k₀, hT⟩ := fundArmA_nil (fundHasTyPrefixA toothPre0 harms.1 harms.2
    (HasTyA.sort (E := emptyEnvA) (I := toothLoopA) (n := n) [] (.succ .zero)))
  exact envSemClauseA_rigid toothEnv_closed toothLoop_lift toothLoop_recHead toothEnv_X rfl (Or.inl rfl)
    (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
    (fun h => MemberClass.noConfusion h) hT

theorem toothY_clause :
    EnvSemClauseA toothEnvA toothLoopA n (fun _ => 1) 1 toothYA := by
  have ih : EnvSemAt toothEnvA toothLoopA n (fun _ => 1) (domA toothE1A) := fun r m hD hres => by
    obtain ⟨m₀, hm₀⟩ := hD
    unfold toothE1A extendEnvA emptyEnvA at hm₀
    simp only at hm₀
    split at hm₀
    · subst_vars; rw [toothEnv_X] at hres; cases hres; exact toothX_clause
    · exact Option.noConfusion hm₀
  have harms := fundArmsA_at toothEnv_closed toothLoop_lift toothLoop_subst toothEnv_normCtor toothEnv_normClosed toothLoop_recHead
    posValA_one ih
  obtain ⟨k₀, hT⟩ := fundArmA_nil (fundHasTyPrefixA toothPre1 harms.1 harms.2
    (HasTyA.pi (E := toothE1A) (I := toothLoopA) (n := n) [] _ _ _ _ (toothX_ty rfl []) (.sort _ _)))
  exact envSemClauseA_rigid toothEnv_closed toothLoop_lift toothLoop_recHead toothEnv_Y rfl (Or.inl rfl)
    (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
    (fun h => MemberClass.noConfusion h) hT

/-- **main's semantic environment HOLDS for the looping oracle**: `X`, `Y` by reflection, `r` by
    its pi clause at the stuck codomain `Y a`, where main's relation demands no normal form. -/
theorem toothLoop_envSemA : EnvSemA toothEnvA toothLoopA n (fun _ => 1) := by
  have ih : EnvSemAt toothEnvA toothLoopA n (fun _ => 1) (domA toothE2A) := fun r m hD hres => by
    obtain ⟨m₀, hm₀⟩ := hD
    unfold toothE2A toothE1A extendEnvA emptyEnvA at hm₀
    simp only at hm₀
    split at hm₀
    · subst_vars; rw [toothEnv_Y] at hres; cases hres; exact toothY_clause
    · split at hm₀
      · subst_vars; rw [toothEnv_X] at hres; cases hres; exact toothX_clause
      · exact Option.noConfusion hm₀
  have harms := fundArmsA_at toothEnv_closed toothLoop_lift toothLoop_subst toothEnv_normCtor toothEnv_normClosed toothLoop_recHead
    posValA_one ih
  obtain ⟨k₀, hT⟩ := fundArmA_nil (fundHasTyPrefixA toothPre2 harms.1 harms.2
    (toothRty_ty (E := toothE2A) (I := toothLoopA) (n := n) rfl rfl []))
  intro r m hres
  unfold toothEnvA toothE2A toothE1A extendEnvA emptyEnvA at hres
  simp only at hres
  split at hres
  · subst_vars; cases hres; exact toothR_clause hT
  · split at hres
    · subst_vars; cases hres; exact toothY_clause
    · split at hres
      · subst_vars; cases hres; exact toothX_clause
      · exact Option.noConfusion hres

end Main

/-! ## (4) the guarded `EnvSemAg` fails -/

/-- **THE TOOTH**: the guarded semantic environment REFUSES the loop. `r` related at its pi type
    (the clause at `r`) puts `r x` into the guarded relation at the stuck, non-`Prop` `Y x`
    (`x : X` a variable, related by reflection), whose datum is a head chain to a normal form
    (`hstuck_of_datumg`); `whnfA` never reaches one from `r x` (`toothLoop_no_whnf`). -/
theorem toothLoop_not_envSemAg {n : Nat} : ¬ EnvSemAg toothEnvA toothLoopA n (fun _ => 1) := by
  intro hSg
  have hK : PropKeyA toothEnvA toothLoopA n :=
    propKeyA_holds toothEnv_closed toothLoop_lift toothLoop_subst toothEnv_normCtor toothEnv_normClosed toothLoop_recHead toothLoop_envSemA
      posValA_one
  have hΓ : CtxWfA toothEnvA toothLoopA n toothCtxA := .assumption .nil (toothX_ty toothEnv_X [])
  obtain ⟨k₀, hr⟩ := hSg 2 toothRA toothEnv_R [] [] rfl rfl rfl (eqNListA_refl [])
  obtain ⟨k₁, hX⟩ := fund_selfg toothEnv_closed toothLoop_lift toothLoop_subst toothEnv_normCtor toothEnv_normClosed toothLoop_recHead hSg
    posValA_one hK hΓ (toothX_ty toothEnv_X toothCtxA)
  have hk₀ : k₀ ≤ max k₀ k₁ := Nat.le_max_left _ _
  have hk₁ : k₁ ≤ max k₀ k₁ := Nat.le_max_right _ _
  obtain ⟨_, hXv, _, _, _, _⟩ := LRRelA_sort_elimg (hX _ hk₁)
  have hx : LRRelAg toothEnvA toothLoopA n (fun _ => 1) (max k₀ k₁) toothCtxA (.const 0 [])
      (.bvar 0) (.bvar 0) :=
    LRRelA_bvarg toothEnv_closed toothLoop_lift (iotaConstHeadA_of_recHead toothLoop_recHead) hK
      ⟨hΓ⟩ rfl hXv ⟨toothV0_ty toothEnv_X []⟩
  have hrr := hr _ hk₀ toothCtxA ⟨hΓ⟩
  simp only [instantiateLevelsA_nil] at hrr
  have hnp : ¬ IsPropTy toothEnvA toothLoopA toothCtxA toothRA.mtypeA := fun h => by
    have := (isPropTy_pi_iff toothEnvA toothLoopA toothCtxA _ _ _ _).1 h
    cases this
  have happ := LRRelA_pi_elimg hrr hnp [] ⟨trivial, ⟨hΓ⟩⟩ (.bvar 0) (.bvar 0) hx
  have e1 : instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub []) (.app (.const 1 []) (.bvar 0))) =
      .app (.const 1 []) (.bvar 0) := by
    rw [wkExprA_app, wkExprA_closed (e := .const 1 []) (fun _ => rfl), wkExprA_ub_bvar0]
    rfl
  rw [e1] at happ
  have hnpY : ¬ IsPropTy toothEnvA toothLoopA toothCtxA (.app (.const 1 []) (.bvar 0)) :=
    not_isPropTy_of_inferSortA (fuel := 3) (l := .succ .zero) (by decide) rfl
  obtain ⟨Na, ⟨cha⟩, hna, _⟩ := hstuck_of_datumg happ
    (whTyA_of_hasTy (toothYx_ty toothEnv_X toothEnv_Y _ (toothV0_ty toothEnv_X [])))
    (toothYx_stuck toothCtxA (.bvar 0)) hnpY
  obtain ⟨fuel, hf⟩ := tmChainA_redTo cha hna
  rw [show wkExprA ([] : WkSpecA) (ExprA.const 2 []) = .const 2 [] from rfl,
    toothLoop_no_whnf] at hf
  exact Option.noConfusion hf

/-- **the separation**: at one environment and one looping ι at a recursor site, main's semantic
    environment holds and the guarded one does not — the R-A6-S1b′ erratum, machine-checked. -/
theorem toothLoop_separates {n : Nat} :
    EnvSemA toothEnvA toothLoopA n (fun _ => 1) ∧ ¬ EnvSemAg toothEnvA toothLoopA n (fun _ => 1) :=
  ⟨toothLoop_envSemA, toothLoop_not_envSemAg⟩

#print axioms toothLoop_lift
#print axioms toothLoop_subst
#print axioms toothLoop_recHead
#print axioms toothEnv_closed
#print axioms toothLoop_no_whnf
#print axioms toothR_clause
#print axioms toothLoop_envSemA
#print axioms toothLoop_not_envSemAg
#print axioms toothLoop_separates

end Rcic.Declarative.Ann
