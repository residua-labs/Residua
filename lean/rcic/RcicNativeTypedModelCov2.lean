import rcic.RcicNativeTypedModelCovArms
import rcic.RcicNativeTypedModelCovKTyping

/-!
# `RcicNativeTypedModelCov2` — `CTyCov2`: covariant compact typing with a rigid
  Π branch for rigid function spines (cc 05:30Z, `devin/swe-ctycov2`, #7761).

ChatGPT's #7761 (`not_cov_global_of_natSucc_observations`) proves that with
`CptT`/`CTyCov` fixed, three things cannot all hold on `natEnvU`: (1) `Nat.succ`
keeps its rigid observation `.spine 2 []`; (2) the model's `Nat → Nat` codes are
`ApproxT`'s; (3) the global `TypingLemmaEnvCovM`.  The cause is `CTyCov`'s Π
branch, which accepts a non-`⊥` compact at `.pi a g` only if it is `.lam …` —
the same obstruction as `not_memberRigidCovT_natEnvU`.

`CTyCov2` is `CTyCov` plus a second accepted shape at `.pi a g`: a rigid spine
`.spine h us` whose head `h` is a rigid member (`RigidConst`: constructor,
axiom, inductive family, or body-free member — the brief's "constructor/axiom")
whose declared type is a Π telescope.  Pointwise argument coverage is the
demand-env semantics the recursor clauses already use: at consumed position `i`
the domain `D_i` is denotation-checked in `spineArgEnv us i` (var `j` ↦
`demandT [us[i-1-j]]`), and each argument compact `us[i]` must be `CTyCov2` at
some denotation of `D_i`.  The residual telescope must itself denote the target
code `.pi a g` — the compact typing follows the member's declared telescope
instead of requiring a λ.  The `¬ IsPropCT` side condition is kept, so §3.6
proposition collapse is unchanged (`ctyCov2_prop_bot`).

Fully-applied spines need no Π clause: their residual is the codomain, and they
already inhabit `.spine`-codes under the existing `.spine` arm.

Termination is on `sizeOf u` (the compact), not `sizeOf a` as in `CTyCov`: the
spine arm recurses on `us[i]` at codes `d` of the member's *declared* domains,
which bear no size relation to the target code.

### §4B consumer changes under `CTyCov2` (d)

* Unchanged by construction: the embedding chain `ctyCov2_of_ctyS` —
  `ctyCov2_of_ctyCov`, `ctyCov2_bot`, `ctyCov2_prop_bot`, and every §4B lemma
  that only *constructs* `CTyCov`-proofs (`covTyping_sort`/`pi`/`lam`/`bvar`/
  `app`/`letE`/`lit`/`conv`, `covConv_*`, `covConv_irr` via `ctyCov_prop_bot`)
  ports verbatim with `CTyCov ↦ CTyCov2`, `ElTCov ↦ ElTCov2`.
* Changed — inversion-side consumers gain a third Π-disjunct in
  `ctyCov2_pi_inv`; `not_ctyCov_spine_of_approxT_pi` and `not_elTCov_spine_pi`
  are FALSE for `CTyCov2` (that is the point: (a)/(b));
  `MemberRigidCovT`-shaped supplies become inhabited for rigid Π members
  (`memberRigidCov2_natSucc`); `ctyCov_pi_mono_steps` has NO `CTyCov2` analogue
  for spine compacts (the residual must denote the *exact* code `.pi a g`, not
  an enlarged step list) — its `CTyCov2` form holds only for `.bot`/`.lam`
  compacts.

`closure_claim = 0`.  No `sorry`, no `Classical.choice`, axioms
`⊆ {propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelCovKAudit

variable {E : ResolvedEnv} {n : Nat}

/-- Residual of `T` after peeling `i` Π-binders (`none` when `T` runs out). -/
def peelPi : Expr Nat → Nat → Option (Expr Nat)
  | e, 0 => some e
  | .pi _ B, i + 1 => peelPi B i
  | _, _ + 1 => none

/-- Demand env of the first `i` consumed spine arguments: inside domain `i`,
    `bvar j` denotes the singletons of `us[i-1-j]` — the `EnvT.pushArgs`
    convention (`last` binder ↦ index 0). -/
def spineArgEnv (us : List CptT) (i : Nat) : EnvT :=
  EnvT.pushArgs ((us.take i).map (fun v => demandT [v])) EnvT.bot

/-- **Covariant semantic typing with a rigid Π branch** (`CTyCov2`): `CTyCov`'s
    clauses verbatim, plus at `.pi a g` the additional rigid-spine shape —
    `.spine h us` where `h` is a `RigidConst` member whose declared mtype is a
    Π telescope that (a) covers each `us[i]` at a denotation of domain `i` in
    the earlier-argument demand env, and (b) has residual denoting `.pi a g`.
    The `¬ IsPropCT` side condition preserves §3.6 collapse. -/
def CTyCov2 (E : ResolvedEnv) : CptT → CptT → Prop
  | u, .bot => u = .bot
  | u, .prop => u = .bot ∨ IsPropCT E u
  | u, .sort => u = .bot ∨ TyCodeCT u
  | .bot, .pi _ _ => True
  | .lam f, .pi a g => ¬ IsPropCT E (.pi a g) ∧
      (∀ s ∈ f, ∀ v ∈ s.1, CTyCov2 E v a) ∧
      (∀ s ∈ f, s.2 = .bot ∨ ∃ (t : List CptT × CptT) (_ : t ∈ g),
        (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov2 E s.2 t.2)
  | .spine h us, .pi a g => ¬ IsPropCT E (.pi a g) ∧
      ∃ m ls, E.members h = some m ∧ RigidConst E h ∧ ls.length = m.arity ∧
        (∀ i (hi : i < us.length) (D C : Expr Nat),
          peelPi (instantiateLevels ls m.mtype) i = some (.pi D C) →
          ∃ d, ApproxT E (spineArgEnv us i) D d ∧ CTyCov2 E us[i] d) ∧
        ∃ Tres, peelPi (instantiateLevels ls m.mtype) us.length = some Tres ∧
          ApproxT E (spineArgEnv us us.length) Tres (.pi a g)
  | _, .pi _ _ => False
  | u, .lam _ => u = .bot
  | u, .spine r' args' => u = .bot ∨
      ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args'))
  termination_by u _ => sizeOf u
  decreasing_by
    all_goals simp_wf
    · have h₁ := List.sizeOf_lt_of_mem (show v ∈ s.1 from ‹_›)
      have h₂ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
      have h₃ := sizeOfT_fst_lt s
      omega
    · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
      have h₂ := sizeOfT_snd_lt s
      omega
    · have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›)
      omega

/-! ### inversion / introduction -/

theorem ctyCov2_bot_inv {u : CptT} (h : CTyCov2 E u .bot) : u = .bot := by
  cases u <;> simp only [CTyCov2] at h ⊢ <;> first | exact h | trivial

theorem ctyCov2_prop_inv {u : CptT} (h : CTyCov2 E u .prop) : u = .bot ∨ IsPropCT E u := by
  cases u <;> simp only [CTyCov2] at h ⊢ <;> first | exact h | (exact Or.inl trivial)

theorem ctyCov2_sort_inv {u : CptT} (h : CTyCov2 E u .sort) : u = .bot ∨ TyCodeCT u := by
  cases u <;> simp only [CTyCov2] at h ⊢ <;> first | exact h | (exact Or.inl trivial)

theorem ctyCov2_lam_inv {u : CptT} {g : List (List CptT × CptT)} (h : CTyCov2 E u (.lam g)) :
    u = .bot := by
  cases u <;> simp only [CTyCov2] at h ⊢ <;> first | exact h | trivial

theorem ctyCov2_spine_inv {u : CptT} {r' : Nat} {args' : List CptT}
    (h : CTyCov2 E u (.spine r' args')) :
    u = .bot ∨ ((∃ r args, u = .spine r args) ∧ ¬ IsPropCT E (.spine r' args')) := by
  cases u <;> simp only [CTyCov2] at h ⊢ <;> first | exact h | (exact Or.inl trivial)

/-- Π-code inversion, three-way: `.bot`, `.lam` (the `CTyCov` shape), or a rigid
    spine whose declared telescope covers the code. -/
theorem ctyCov2_pi_inv {u a : CptT} {g : List (List CptT × CptT)} (h : CTyCov2 E u (.pi a g)) :
    u = .bot ∨
      (∃ f, u = .lam f ∧ ¬ IsPropCT E (.pi a g) ∧
        (∀ s ∈ f, ∀ v ∈ s.1, CTyCov2 E v a) ∧
        (∀ s ∈ f, s.2 = .bot ∨ ∃ (t : List CptT × CptT) (_ : t ∈ g),
          (∀ v ∈ t.1, v ∈ s.1) ∧ CTyCov2 E s.2 t.2)) ∨
      (∃ h' us, u = .spine h' us ∧ ¬ IsPropCT E (.pi a g) ∧
        ∃ m ls, E.members h' = some m ∧ RigidConst E h' ∧ ls.length = m.arity ∧
          (∀ i (hi : i < us.length) (D C : Expr Nat),
            peelPi (instantiateLevels ls m.mtype) i = some (.pi D C) →
            ∃ d, ApproxT E (spineArgEnv us i) D d ∧ CTyCov2 E us[i] d) ∧
          ∃ Tres, peelPi (instantiateLevels ls m.mtype) us.length = some Tres ∧
            ApproxT E (spineArgEnv us us.length) Tres (.pi a g)) := by
  cases u <;> simp only [CTyCov2] at h
    <;> first
      | (exact Or.inl rfl)
      | (exact False.elim h)
      | (exact Or.inr (Or.inl ⟨_, rfl, h.1, h.2.1, h.2.2⟩))
      | (exact Or.inr (Or.inr ⟨_, _, rfl, h⟩))

theorem ctyCov2_bot (a : CptT) : CTyCov2 E .bot a := by
  cases a <;> simp only [CTyCov2]
    <;> first | trivial | rfl | (exact Or.inl trivial) | (exact Or.inl rfl)

/-- **`CTyCov` implies `CTyCov2`** (`ctyCov2_of_ctyCov`): the λ-disjunct ports
    verbatim; the rigid-spine disjunct is additional. -/
theorem ctyCov2_of_ctyCov : ∀ (a u : CptT), CTyCov E u a → CTyCov2 E u a
  | .bot, u, h => by rw [ctyCov_bot_inv h]; exact ctyCov2_bot _
  | .prop, u, h => by simp only [CTyCov2]; exact ctyCov_prop_inv h
  | .sort, u, h => by simp only [CTyCov2]; exact ctyCov_sort_inv h
  | .pi a g, u, h => by
      rcases ctyCov_pi_inv h with rfl | ⟨f, rfl, hnp, hdom, hcov⟩
      · exact ctyCov2_bot _
      · simp only [CTyCov2]
        refine ⟨hnp, fun s hs v hv => ctyCov2_of_ctyCov a v (hdom s hs v hv),
          fun s hs => ?_⟩
        rcases hcov s hs with hbot | ⟨t, htg, hsub⟩
        · exact Or.inl hbot
        · exact Or.inr ⟨t, htg, hsub.1, ctyCov2_of_ctyCov t.2 s.2 hsub.2⟩
  | .lam g, u, h => by rw [ctyCov_lam_inv h]; exact ctyCov2_bot _
  | .spine r' args', u, h => by simp only [CTyCov2]; exact ctyCov_spine_inv h
termination_by a _ => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show t ∈ g from ‹_›)
       have h₂ := sizeOfT_snd_lt t
       omega)

/-- **`CTyS` implies `CTyCov2`** — composition of the two embeddings. -/
theorem ctyCov2_of_ctyS {a u : CptT} (h : CTyS E u a) : CTyCov2 E u a :=
  ctyCov2_of_ctyCov a u (ctyCov_of_ctyS a u h)

/-- **§3.6 collapse preserved** (`ctyCov2_prop_bot`): every compact typed at a
    proposition code is `.bot` — the rigid-spine Π disjunct keeps the
    `¬ IsPropCT` side condition. -/
theorem ctyCov2_prop_bot {a u : CptT} (hP : IsPropCT E a) (h : CTyCov2 E u a) : u = .bot := by
  cases a with
  | bot => exact ctyCov2_bot_inv h
  | prop => cases hP
  | sort => cases hP
  | pi a g =>
      rcases ctyCov2_pi_inv h with rfl | ⟨_, _, hnp, _⟩ | ⟨_, _, _, hnp, _⟩
      · rfl
      · exact (hnp hP).elim
      · exact (hnp hP).elim
  | lam g => exact ctyCov2_lam_inv h
  | spine r' args' =>
      rcases ctyCov2_spine_inv h with rfl | ⟨_, hnp⟩
      · rfl
      · exact (hnp hP).elim

/-! ### `CTyCov2` typing interfaces -/

/-- `ElTCov` with `CTyCov2`. -/
def ElTCov2 (E : ResolvedEnv) (ρ : EnvT) (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, ApproxT E ρ A a ∧ CTyCov2 E u a

/-- Model-parametric `ElTCov` with `CTyCov2` (the #7761 `ElTCovM` shape). -/
def ElTCov2M (M : CtxModelT E) (ρ : EnvT) (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, M.Ap ρ A a ∧ CTyCov2 E u a

/-- Model-parametric covariant environment typing with `CTyCov2` + `CtxEnvM`. -/
def EnvTypedCov2M (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  (∀ i A, lookupType Γ i = some A → ∀ u, ρ i u → ElTCov2M M ρ A u) ∧ CtxEnvM M Γ ρ

/-- Model-parametric local covariant typing with `CTyCov2`. -/
def CovTyping2AtM (M : CtxModelT E) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {ρ : EnvT}, EnvTypedCov2M M Γ ρ → ∀ u, M.Ap ρ e u → ElTCov2M M ρ A u

/-- The #7761 `TypingLemmaEnvCovM` shape under `CTyCov2`. -/
def TypingLemmaEnvCov2M (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A → CovTyping2AtM M Γ e A

theorem elTCov2_of_elTCov {ρ : EnvT} {A : Expr Nat} {u : CptT} (h : ElTCov E ρ A u) :
    ElTCov2 E ρ A u :=
  let ⟨a, ha, hua⟩ := h; ⟨a, ha, ctyCov2_of_ctyCov a u hua⟩

theorem elTCov2M_of_elTCov2 {ρ : EnvT} {A : Expr Nat} {u : CptT}
    (h : ElTCov2 E ρ A u) : ElTCov2M (ctxModelT_approxT E) ρ A u := h

/-! ### (a) — `.spine 2 []` is covered at a `Nat → Nat` code on `natEnvU` -/

/-- The canonical non-Prop `Nat → Nat` code: domain `Nat`'s spine, one step
    `[Nat] ↦ Nat`. -/
def natNatCovCode : CptT := .pi (.spine 0 []) [([.spine 0 []], .spine 0 [])]

theorem not_isPropCT_natNatCovCode : ¬ IsPropCT natEnvU natNatCovCode := by
  intro h
  cases h with
  | pi _ hout =>
      exact not_isPropCT_natEnvU_nat_spine [] (hout _ (List.mem_singleton.mpr rfl))

theorem approxT_natNat_covCode (ρ : EnvT) :
    ApproxT natEnvU ρ (.pi (.const 0 []) (.const 0 [])) natNatCovCode := by
  refine .pi (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat) ?_ ?_
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    rw [CTyS]
    exact Or.inr ⟨⟨0, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact .const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat

/-- **(a)**: the rigid `Nat.succ` observation `.spine 2 []` is `CTyCov2`-covered
    at every non-Prop `Nat → Nat` code — `natSuccMember.mtype = Nat → Nat` is
    rigid, arity 0, no arguments consumed, and the residual denotes the code. -/
theorem ctyCov2_natSucc_spine {ρ : EnvT} {a : CptT}
    (ha : ApproxT natEnvU ρ (.pi (.const 0 []) (.const 0 [])) a)
    (hnp : ¬ IsPropCT natEnvU a) : CTyCov2 natEnvU (.spine 2 []) a := by
  rcases approxT_pi_inv ha with hbot | ⟨a', g', rfl, _⟩
  · rw [hbot] at hnp; exact (hnp .bot).elim
  · simp only [CTyCov2]
    refine ⟨hnp, natSuccMember, [], rfl, rigidConst_natEnvU_succ, rfl,
      fun i hi => (Nat.not_lt_zero _ hi).elim,
      instantiateLevels [] natSuccMember.mtype, rfl, ?_⟩
    exact approxT_closed0_env_cov ρ EnvT.bot (by rfl) ha

theorem elTCov2_natSucc_spine (ρ : EnvT) :
    ElTCov2 natEnvU ρ (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) :=
  ⟨natNatCovCode, approxT_natNat_covCode ρ,
    ctyCov2_natSucc_spine (approxT_natNat_covCode ρ) not_isPropCT_natNatCovCode⟩

/-! ### (b) — the #7761 three-way incompatibility no longer applies -/

/-- **(b)**: the universal exclusion that #7761's trio consumes —
    `∀ a ∈ den(Nat → Nat), ¬ CTyCov2 (spine 2 []) a` — is refuted for `CTyCov2`
    by `natNatCovCode`. -/
theorem not_ctyCov2_excludes_natSucc_spine (ρ : EnvT) :
    ¬ (∀ a, ApproxT natEnvU ρ (.pi (.const 0 []) (.const 0 [])) a →
        ¬ CTyCov2 natEnvU (.spine 2 []) a) :=
  fun h => h _ (approxT_natNat_covCode ρ)
    (ctyCov2_natSucc_spine (approxT_natNat_covCode ρ) not_isPropCT_natNatCovCode)

/-- At the concrete `ctxModelT_approxT` (whose `hA` is the identity inclusion),
    the formerly-blocked obligation — `Nat.succ`'s rigid observation covered at
    `Nat → Nat` — is inhabited: the trio's final step no longer fires. -/
theorem elTCov2M_natSucc_spine_approxT :
    ElTCov2M (ctxModelT_approxT natEnvU) EnvT.bot
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) :=
  elTCov2_natSucc_spine EnvT.bot

/-! ### (c) — the cex fix transports -/

/-- **(c)**: `covTyping_cexTerm`/`covTyping_cexType` hold for `CTyCov2` by
    `ctyCov2_of_ctyCov` transport. -/
theorem covTyping2_cexTerm (E : ResolvedEnv) (ρ : EnvT) {u : CptT}
    (hu : ApproxT E ρ cexTerm u) : ElTCov2 E ρ cexType u :=
  elTCov2_of_elTCov (covTyping_cexTerm E ρ hu)

theorem covTyping2_cexType (E : ResolvedEnv) (ρ : EnvT) {u : CptT}
    (hu : ApproxT E ρ cexType u) :
    ElTCov2 E ρ (.sort (.imax U2 (.imax U1 U2))) u :=
  elTCov2_of_elTCov (covTyping_cexType E ρ hu)

/-! ### (d) — `MemberRigidCov`-shape supply at `Nat.succ` is now inhabited -/

/-- **(d)**: the rigid-member supply arm at `Nat.succ` — `instantiateLevels []
    natSuccMember.mtype = Nat → Nat` covers `.spine 2 []` under `CTyCov2` —
    the `MemberRigidCovT` field `not_memberRigidCovT_natEnvU` refuted for
    `CTyCov` has an inhabitant for `CTyCov2`. -/
theorem memberRigidCov2_natSucc :
    ElTCov2 natEnvU EnvT.bot (instantiateLevels [] natSuccMember.mtype) (.spine 2 []) := by
  rw [instantiateLevels_nil]
  exact elTCov2_natSucc_spine EnvT.bot

#print axioms peelPi
#print axioms spineArgEnv
#print axioms CTyCov2
#print axioms ctyCov2_bot_inv
#print axioms ctyCov2_prop_inv
#print axioms ctyCov2_sort_inv
#print axioms ctyCov2_lam_inv
#print axioms ctyCov2_spine_inv
#print axioms ctyCov2_pi_inv
#print axioms ctyCov2_bot
#print axioms ctyCov2_of_ctyCov
#print axioms ctyCov2_of_ctyS
#print axioms ctyCov2_prop_bot
#print axioms ElTCov2
#print axioms ElTCov2M
#print axioms EnvTypedCov2M
#print axioms CovTyping2AtM
#print axioms TypingLemmaEnvCov2M
#print axioms elTCov2_of_elTCov
#print axioms elTCov2M_of_elTCov2
#print axioms natNatCovCode
#print axioms not_isPropCT_natNatCovCode
#print axioms approxT_natNat_covCode
#print axioms ctyCov2_natSucc_spine
#print axioms elTCov2_natSucc_spine
#print axioms not_ctyCov2_excludes_natSucc_spine
#print axioms elTCov2M_natSucc_spine_approxT
#print axioms covTyping2_cexTerm
#print axioms covTyping2_cexType
#print axioms memberRigidCov2_natSucc

end Rcic.Declarative.NativeValleys.TypedModelAudit
