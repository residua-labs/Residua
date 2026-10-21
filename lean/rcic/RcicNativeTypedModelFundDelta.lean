import rcic.RcicNativeTypedModelFundStrong
import rcic.RcicNativeTypedModelIota
import rcic.RcicNativePiModelDeltaIota
import rcic.RcicNativeFamModel
import rcic.RcicIotaShape
import rcic.RcicIota
import rcic.RcicSubstT
import rcic.RcicLevelCalc
import rcic.RcicTypedEnvEntry

/-!
# RcicNativeTypedModelFundDelta — `delta` and the non-recursor fragment of `const` / `consts`

`FundCases` (`RcicNativeTypedModelFundStrong`) fields discharged at the concrete model
`ctxModelT_approxT` (the `Ap`-inversions are model facts — `CtxModelTLaws` reads no
constant clause, so the case split goes through `approxT_const_inv`).

* `fundT_delta` is structural: the `hb` premise is an original child derivation, so
  `IHBelow` supplies the instantiated body's diagonal.  The δ readback step and the
  closedness lifts do the rest.
* `fundT_consts` (and `fundT_const` as its `ls' = ls` diagonal specialization) covers
  **non-recursor members only** (`hnrec : m.mclass ≠ .recursorM`): rigid constants become
  the one-step `SpineClauseS` (refl readbacks, `eqNList`, `ConvArgsT.nil`); transparent
  definitions double-expand through the member-body diagonal.  The recursor-member clause
  is *not* provable at this model: `MemberRecDiagT (ctxModelT_approxT natEnvU)` is
  kernel-refuted (`RcicNativeTypedModelRecDiagCounter.not_memberRecDiagT_natEnvU`), so the
  clause is split off and recorded there as a model-level finding for the relation
  re-foundation.
* The member diagonals are the **named admission-induction premises**: member derivations
  are not children of the context derivation, so `IHBelow` cannot supply them — exactly
  the "`fundamental lemma at the member's body`" the parent module's header names.

Named premises, each witnessed non-vacuously on an environment with a real definition
**and** a real axiom (`fundDeltaEnv` — `d₀ := Sort 0 : Sort 1` at ref 0, axiom `a₁ : Sort 1`
at ref 1 — §4):

* `ConstDeltaStepT R E` — transparent-body constants δ-step under the readback
  (`whStepCtx_deltaStep`, by `WhStepCtx.delta`).
* `ConstBodyFreeNormalT R E` — body-free constants are readback-normal
  (`whStepCtx_bodyFreeNormal` via `FamModelAudit.whStepCtx_const_opaque_false`);
  exercised non-degenerately by the axiom member.
* `MemberTyDiagT M R n` — the member's declared type is valid
  (`fundDeltaEnv_memberTyDiag`).
* `MemberBodyDiagT M R n` — the member-body fundamental diagonal
  (`fundDeltaEnv_memberBodyDiag`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the named premises -/

/-- Transparent-body constants δ-step under the readback.  `ReadbackLaws` does not carry a
    δ law, so the field proofs take it as an input; `WhStepCtx` supplies it. -/
def ConstDeltaStepT (R : Readback) (E : ResolvedEnv) : Prop :=
  ∀ (Γ : LCtx) {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat},
    E.members r = some m → m.body = some b → R Γ (.const r ls) (instantiateLevels ls b)

/-- Body-free constants are readback-normal: no head step.  Under `EnvWfT` every
    approximation-rigid member is body-free (`CtorNoBody`), so this is exactly the
    normality the rigid spine clause needs. -/
def ConstBodyFreeNormalT (R : Readback) (E : ResolvedEnv) : Prop :=
  ∀ (Γ : LCtx) {r : Nat} {m : CheckedMember} {ls : List Level},
    E.members r = some m → m.body = none → ∀ e, ¬ R Γ (.const r ls) e

/-- **The member-type diagonal** — the declared type's validity.  `IHBelow` cannot reach
    it: the member's type-derivation is not a child of the context derivation. -/
def MemberTyDiagT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {r : Nat} {m : CheckedMember} {ls : List Level},
    E.members r = some m → ls.length = m.arity → levelsBounded n ls = true →
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    TyValidAt M R n Γ (instantiateLevels ls m.mtype)

/-- **The member-body diagonal** — the fundamental lemma at the member's stored body
    (admission induction): the instantiated body's typing diagonal and its
    level-congruent conversion diagonal at the member's declared type. -/
def MemberBodyDiagT (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {r : Nat} {m : CheckedMember} {b : Expr Nat} {ls ls' : List Level},
    E.members r = some m → m.body = some b →
    ls.length = m.arity → ls'.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    CtxWfT E n Γ → CtxValidAt M R n Γ →
    FundTyAt M R n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) ∧
    FundConvAt M R n Γ (instantiateLevels ls b) (instantiateLevels ls' b)
      (instantiateLevels ls m.mtype)

/-! ### §2 — model-side: closed-term environment invariance (`approxT_closedAt_env`) -/

/-- Port of `approxDI_closedAt_env`: if `exprClosedAt k e = true` and `ρ` agrees with `ρ'`
    on all variables `< k`, then `ApproxT E ρ e c → ApproxT E ρ' e c`. -/
theorem approxT_closedAt_env {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) :
    ∀ {k : Nat} {ρ' : EnvT}, exprClosedAt k e = true → (∀ i < k, ρ i = ρ' i) →
      ApproxT E ρ' e c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, decide_eq_true_eq] at hcl
      exact .bvar (heq i hcl ▸ h)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .pi (ihA hcl.1 heq) hT (fun s hs => (ihf s hs) hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | lam _ hT hnt _ ihA ihb =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .lam (ihA hcl.1 heq) hT hnt (fun s hs => (ihb s hs) hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | app _ hs _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .app (ihf hcl.1 heq) hs (fun u hu => iha u hu hcl.2 heq)
  | const _ _ _ hrigid hnp => intro _ _ _ _; exact .const _ _ _ hrigid hnp
  | delta hd h => intro _ _ _ _; exact .delta hd h
  | recursor ls hnp hpre hflds h => intro _ _ _ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h => intro _ _ _ _; exact .recursorProp ls hP hpre h
  | appSpine _ _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .appSpine (ihf hcl.1 heq) (iha hcl.2 heq)
  | @letE _ A v b _ h ih =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      have hcl' : exprClosedAt k (.app (.lam A b) v) = true := by
        simp only [exprClosedAt, Bool.and_eq_true]
        exact ⟨⟨hcl.1.1, hcl.2⟩, hcl.1.2⟩
      exact .letE (ih hcl' heq)
  | lit _ ih =>
      intro k ρ' _ heq
      exact .lit (ih (exprClosedAt_natExpand k _) heq)

/-- Closed terms (`exprClosedAt 0 e = true`) have environment-independent approximations. -/
theorem approxT_closed0_env {E : ResolvedEnv} (ρ ρ' : EnvT) {e : Expr Nat}
    (hcl : exprClosedAt 0 e = true) {c : CptT}
    (h : ApproxT E ρ e c) : ApproxT E ρ' e c :=
  approxT_closedAt_env h hcl (fun _ hi => (Nat.not_lt_zero _ hi).elim)

/-! ### §3 — readback-side suppliers -/

/-- `WhStepCtx` supplies `ConstDeltaStepT` at every environment. -/
theorem whStepCtx_deltaStep (E : ResolvedEnv) : ConstDeltaStepT (WhStepCtx E) E :=
  fun _ {_ _ _ _} hres hbody => .delta hres hbody

/-- `WhStepCtx` supplies `ConstBodyFreeNormalT` at every environment: a body-free constant
    takes no weak-head step (`FamModelAudit.whStepCtx_const_opaque_false` — δ needs a
    stored body, ι left-hand sides are application spines). -/
theorem whStepCtx_bodyFreeNormal (E : ResolvedEnv) : ConstBodyFreeNormalT (WhStepCtx E) E :=
  fun _ {_ _ _} hres hnob _ h => whStepCtx_const_opaque_false hres hnob _ h

/-! ### §4 — the rigid spine clause and the three fields -/

/-- A rigid constant at level lists `ls₁`, `ls₂` is related to itself at `.spine r []`:
    the refl-readback `SpineClauseS`, with the inductive-family saturation package
    discharged by `instMtype_policyPi_of_inductiveM`. -/
theorem spineClauseS_rigid_const (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hNR : ConstBodyFreeNormalT R E) {Δ : LCtx} {r : Nat} {m : CheckedMember}
    {ls₁ ls₂ : List Level}
    (hres : E.members r = some m) (hrig : RigidConst E r)
    (hlen₁ : ls₁.length = m.arity) (hwf₁ : levelsBounded n ls₁ = true)
    (hlen₂ : ls₂.length = m.arity) (hwf₂ : levelsBounded n ls₂ = true)
    (heq : eqNList ls₁ ls₂) :
    SpineClauseS R E n Δ (.const r ls₁) (.const r ls₂)
      (instantiateLevels ls₁ m.mtype) r [] := by
  have hnob : m.body = none := by
    rcases (hrig m hres).1 with hn | hctor
    · exact hn
    · exact ctorNoBody_of_envWfT hW r m hres hctor
  refine ⟨m, ls₁, ls₂, [], [], hres, .refl _, .refl _,
    hNR Δ hres hnob, hNR Δ hres hnob, heq, Nat.zero_le _, Nat.zero_le _, .nil _, ?_⟩
  rintro ⟨l, hRl⟩ hind
  rw [instMtype_policyPi_of_inductiveM hW hres hind ls₁] at hRl
  have hdoms : piDomsOf m.mtype = [] := by
    cases hpd : piDomsOf m.mtype with
    | nil => rfl
    | cons A₀ rest =>
        rw [hpd] at hRl
        cases redR_pi_eq hL hRl
  have hsort₁ : instantiateLevels ls₁ m.mtype =
      .sort (instLevel ls₁ (inductiveSortLevel hW hres hind)) := by
    simp only [instMtype_policyPi_of_inductiveM hW hres hind ls₁, hdoms, List.map_nil, policyPi]
  have hsort₂ : instantiateLevels ls₂ m.mtype =
      .sort (instLevel ls₂ (inductiveSortLevel hW hres hind)) := by
    simp only [instMtype_policyPi_of_inductiveM hW hres hind ls₂, hdoms, List.map_nil, policyPi]
  exact ⟨by rw [hdoms], by rw [hdoms],
    ⟨_, ⟨hsort₁ ▸ HasTyT.const Δ r ls₁ m hres hlen₁ hwf₁⟩⟩,
    ⟨_, ⟨hsort₂ ▸ HasTyT.const Δ r ls₂ m hres hlen₂ hwf₂⟩⟩⟩

/-- **`consts`, non-recursor members**: level-congruent constants are related at every
    compact either side denotes — rigid spines via `spineClauseS_rigid_const`,
    transparent bodies via `MemberBodyDiagT` and two δ expansions.  Recursor members are
    excluded by `hnrec`: the recursor-member clause (`MemberRecDiagT`) is refuted on
    `natEnvU` — see `RcicNativeTypedModelRecDiagCounter`. -/
theorem fundT_consts (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hNR : ConstBodyFreeNormalT R E) (hδ : ConstDeltaStepT R E)
    (hMB : MemberBodyDiagT (ctxModelT_approxT E) R n)
    (hMT : MemberTyDiagT (ctxModelT_approxT E) R n)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hnrec : m.mclass ≠ .recursorM)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (hΓ : CtxWfT E n Γ) (hV : CtxValidAt (ctxModelT_approxT E) R n Γ) :
    FundConvAt (ctxModelT_approxT E) R n Γ (.const r ls) (.const r ls')
        (instantiateLevels ls m.mtype) ∧
      TyValidAt (ctxModelT_approxT E) R n Γ (instantiateLevels ls m.mtype) := by
  have hcl := envClosed_of_envWfT hW
  have hclT : ∀ k, lift k 1 (instantiateLevels ls m.mtype) =
      instantiateLevels ls m.mtype := lift_instantiateLevels_closedT (hcl r m hres).1 ls
  have hlen' : ls'.length = m.arity := (eqNList_length ls ls' h).symm.trans hlen
  refine ⟨fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_, hMT hres hlen hwf hΓ hV⟩
  have hmrec : ∀ (w : IotaWitnessS E), w.recRef = r → m.mclass = .recursorM := by
    intro w hwr
    have h1 : E.members r = some w.recMember := hwr ▸ w.hrec
    have h2 : w.recMember = m := Option.some.inj (h1.symm.trans hres)
    exact h2 ▸ w.hrecK
  rcases hc with hc | hc
  · rcases approxT_const_inv hc with rfl | ⟨hrig, _, rfl⟩ | ⟨m₂, b, hd, hb⟩ |
      ⟨w, _, _, _, hwr, _, _, _, _, rfl⟩ | ⟨w, _, _, hwr, _, _, _, rfl⟩
    · exact lrSCoreS_bot _ _ _ _
    · have hsp := spineClauseS_rigid_const (Δ := Δ) hL hW hNR hres hrig hlen hwf hlen' hwf' h
      rw [← substT_closed hclT σ] at hsp
      exact (lrSCoreS_spine_iff Δ _ _ _ _ _).mpr hsp
    · obtain rfl : m = m₂ := (Option.some.inj (hd.1.symm.trans hres)).symm
      obtain ⟨-, hFC⟩ := hMB hres hd.2.1 hlen hlen' hwf hwf' h hΓ hV
      have hclb₀ : exprClosedAt 0 (instantiateLevels ls b) = true := by
        rw [exprClosedAt_instantiateLevels]
        exact (envWfT_member_body_closed hW r m b hres hd.2.1).2
      have hclb' : ∀ k, lift k 1 (instantiateLevels ls' b) = instantiateLevels ls' b :=
        lift_instantiateLevels_closedT ((hcl r m hres).2 b hd.2.1) ls'
      have hclb : ∀ k, lift k 1 (instantiateLevels ls b) = instantiateLevels ls b :=
        lift_instantiateLevels_closedT ((hcl r m hres).2 b hd.2.1) ls
      have hrel := hFC hΔ hS c
        (Or.inl (approxT_closed0_env _ _ hclb₀ hb) :
          ApproxT E ρ (instantiateLevels ls b) c ∨ ApproxT E ρ' (instantiateLevels ls' b) c)
      rw [substT_closed hclb σ, substT_closed hclb' σ'] at hrel
      exact lrSCoreS_expand hL (hδ Δ hres hd.2.1) c
        (lrSCoreS_expand_right hL (hδ Δ hres hd.2.1) c hrel)
    · exact (hnrec (hmrec w hwr)).elim
    · exact (hnrec (hmrec w hwr)).elim
  · rcases approxT_const_inv hc with rfl | ⟨hrig, _, rfl⟩ | ⟨m₂, b, hd, hb⟩ |
      ⟨w, _, _, _, hwr, _, _, _, _, rfl⟩ | ⟨w, _, _, hwr, _, _, _, rfl⟩
    · exact lrSCoreS_bot _ _ _ _
    · have hsp := spineClauseS_rigid_const (Δ := Δ) hL hW hNR hres hrig hlen hwf hlen' hwf' h
      rw [← substT_closed hclT σ] at hsp
      exact (lrSCoreS_spine_iff Δ _ _ _ _ _).mpr hsp
    · obtain rfl : m = m₂ := (Option.some.inj (hd.1.symm.trans hres)).symm
      obtain ⟨-, hFC⟩ := hMB hres hd.2.1 hlen hlen' hwf hwf' h hΓ hV
      have hclb₀ : exprClosedAt 0 (instantiateLevels ls' b) = true := by
        rw [exprClosedAt_instantiateLevels]
        exact (envWfT_member_body_closed hW r m b hres hd.2.1).2
      have hclb' : ∀ k, lift k 1 (instantiateLevels ls' b) = instantiateLevels ls' b :=
        lift_instantiateLevels_closedT ((hcl r m hres).2 b hd.2.1) ls'
      have hclb : ∀ k, lift k 1 (instantiateLevels ls b) = instantiateLevels ls b :=
        lift_instantiateLevels_closedT ((hcl r m hres).2 b hd.2.1) ls
      have hrel := hFC hΔ hS c
        (Or.inr (approxT_closed0_env _ _ hclb₀ hb) :
          ApproxT E ρ (instantiateLevels ls b) c ∨ ApproxT E ρ' (instantiateLevels ls' b) c)
      rw [substT_closed hclb σ, substT_closed hclb' σ'] at hrel
      exact lrSCoreS_expand hL (hδ Δ hres hd.2.1) c
        (lrSCoreS_expand_right hL (hδ Δ hres hd.2.1) c hrel)
    · exact (hnrec (hmrec w hwr)).elim
    · exact (hnrec (hmrec w hwr)).elim

/-- **`const`, non-recursor members**: the `ls' = ls` diagonal of `fundT_consts` —
    `FundConvAt Γ a a A` is `FundTyAt Γ a A`. -/
theorem fundT_const (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hNR : ConstBodyFreeNormalT R E) (hδ : ConstDeltaStepT R E)
    (hMB : MemberBodyDiagT (ctxModelT_approxT E) R n)
    (hMT : MemberTyDiagT (ctxModelT_approxT E) R n)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hnrec : m.mclass ≠ .recursorM)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hΓ : CtxWfT E n Γ) (hV : CtxValidAt (ctxModelT_approxT E) R n Γ) :
    FundTyAt (ctxModelT_approxT E) R n Γ (.const r ls)
        (instantiateLevels ls m.mtype) ∧
      TyValidAt (ctxModelT_approxT E) R n Γ (instantiateLevels ls m.mtype) :=
  fundT_consts hL hW hNR hδ hMB hMT hres hnrec hlen hwf hwf (eqNList_refl ls) hΓ hV

/-- At a δ-member the iota-witness arms are excluded: the resolution is unique. -/
theorem iotaWitnessS_recRef_ne_delta {E : ResolvedEnv} (w : IotaWitnessS E) {r : Nat}
    {m : CheckedMember} {b : Expr Nat} (hwr : w.recRef = r) (hd : DeltaConst E r m b) :
    False := by
  have h1 : E.members r = some w.recMember := hwr ▸ w.hrec
  have h2 : w.recMember = m := Option.some.inj (h1.symm.trans hd.1)
  exact hd.2.2.1 (h2 ▸ w.hrecK)

/-- **`delta`**: `hb` is an original child, so `IHBelow` gives the instantiated body's
    diagonal; one δ expansion moves the left endpoint back to the constant. -/
theorem fundT_delta (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hδ : ConstDeltaStepT R E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hΓ : CtxWfT E n Γ) (hV : CtxValidAt (ctxModelT_approxT E) R n Γ)
    (ih : IHBelow (ctxModelT_approxT E) R n
      (sizeOf (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb))) :
    FundConvAt (ctxModelT_approxT E) R n Γ (.const r ls) (instantiateLevels ls b)
        (instantiateLevels ls m.mtype) ∧
      TyValidAt (ctxModelT_approxT E) R n Γ (instantiateLevels ls m.mtype) := by
  have hcl := envClosed_of_envWfT hW
  have hd := deltaConst_of_transparent hres hbody htr
  have hclb : ∀ k, lift k 1 (instantiateLevels ls b) = instantiateLevels ls b :=
    lift_instantiateLevels_closedT ((hcl r m hres).2 b hbody) ls
  have hclT : ∀ k, lift k 1 (instantiateLevels ls m.mtype) =
      instantiateLevels ls m.mtype := lift_instantiateLevels_closedT (hcl r m hres).1 ls
  have hclb₀ : exprClosedAt 0 (instantiateLevels ls b) = true := by
    rw [exprClosedAt_instantiateLevels]
    exact (envWfT_member_body_closed hW r m b hres hbody).2
  have hlt : sizeOf hb < sizeOf (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb) := by
    simp; omega
  obtain ⟨ihb, ihV⟩ := ih.1 hb hlt hΓ hV
  refine ⟨fun {Δ ρ ρ' σ σ'} hΔ hS c hc => ?_, ihV⟩
  change LRSCoreS R E n Δ (.const r ls) (substT σ' (instantiateLevels ls b))
    (substT σ (instantiateLevels ls m.mtype)) c
  rw [substT_closed hclb σ', substT_closed hclT σ]
  have hcb : ApproxT E ρ (instantiateLevels ls b) c ∨
      ApproxT E ρ' (instantiateLevels ls b) c := by
    rcases hc with hc | hc
    · rcases approxT_const_inv hc with rfl | ⟨hrig, _, _⟩ | ⟨m₂, b₂, hd₂, hb₂⟩ |
        ⟨w, _, _, _, hwr, _, _, _, _, _⟩ | ⟨w, _, _, hwr, _, _, _, _⟩
      · exact Or.inl (.bot _ _)
      · exact absurd hrig (not_rigidConst_of_deltaConst hd)
      · obtain rfl : m = m₂ := (Option.some.inj (hd₂.1.symm.trans hres)).symm
        obtain rfl : b = b₂ := (Option.some.inj (hd₂.2.1.symm.trans hbody)).symm
        exact Or.inl (approxT_closed0_env _ _ hclb₀ hb₂)
      · exact (iotaWitnessS_recRef_ne_delta w hwr hd).elim
      · exact (iotaWitnessS_recRef_ne_delta w hwr hd).elim
    · exact Or.inr hc
  have hrel := ihb hΔ hS c hcb
  rw [substT_closed hclb σ, substT_closed hclb σ', substT_closed hclT σ] at hrel
  exact lrSCoreS_expand hL (hδ Δ hres hbody) c hrel

/-! ### §5 — the named premises are inhabited at a real-definition + real-axiom env -/

/-- `fundDeltaEnv`: two members over `emptyEnv` — `d₀ := Sort 0 : Sort 1` (`definitionM`,
    arity 0, a real definition) at ref 0 and `a₁ : Sort 1` (`axiomM`, body-free, a real
    axiom) at ref 1.  Non-`emptyEnv` witness for every named premise: the definition
    member exercises the δ/`MemberBodyDiagT` paths for real, and the axiom member makes
    `ConstBodyFreeNormalT` non-degenerate. -/
def fundDeltaEnv : ResolvedEnv :=
  extendEnv (extendEnv emptyEnv 0 ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    1 ⟨.axiomM, 0, .sort (.succ .zero), none⟩

theorem fundDeltaEnv_members_zero : fundDeltaEnv.members 0 =
    some ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ := by
  rw [fundDeltaEnv, members_extend_ne _ 1 _ 0 (by decide)]
  exact members_extend_eq _ _ _

theorem fundDeltaEnv_members_one : fundDeltaEnv.members 1 =
    some ⟨.axiomM, 0, .sort (.succ .zero), none⟩ :=
  members_extend_eq _ _ _

theorem fundDeltaEnv_members_ne {r : Nat} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    fundDeltaEnv.members r = none := by
  rw [fundDeltaEnv, members_extend_ne _ 1 _ r h1,
    members_extend_ne emptyEnv 0 _ r h0]
  rfl

/-- `WhStepCtx` supplies the δ step — here at the real-definition + real-axiom env. -/
theorem fundDeltaEnv_deltaStep : ConstDeltaStepT (WhStepCtx fundDeltaEnv) fundDeltaEnv :=
  whStepCtx_deltaStep _

/-- `WhStepCtx` supplies body-free normality — non-degenerate: the axiom member `a₁`
    (`body = none`) exercises the `body = none` branch for real. -/
theorem fundDeltaEnv_bodyFreeNormal :
    ConstBodyFreeNormalT (WhStepCtx fundDeltaEnv) fundDeltaEnv :=
  whStepCtx_bodyFreeNormal _

/-- `MemberTyDiagT` at `fundDeltaEnv`: both members have `mtype = Sort 1`, valid at
    sort 2. -/
theorem fundDeltaEnv_memberTyDiag (n : Nat) :
    MemberTyDiagT (ctxModelT_approxT fundDeltaEnv) (WhStepCtx fundDeltaEnv) n := by
  intro Γ r m ls hres hlen hwf hΓ hV
  by_cases h0 : r = 0
  · subst h0
    rw [fundDeltaEnv_members_zero] at hres
    injection hres with hm; subst hm
    have hls : ls = [] := List.eq_nil_of_length_eq_zero hlen
    subst hls
    rw [instantiateLevels_nil]
    exact ⟨.succ (.succ .zero),
      fundT_sort (ctxModelTLaws_approxT fundDeltaEnv) (.succ .zero)⟩
  · by_cases h1 : r = 1
    · subst h1
      rw [fundDeltaEnv_members_one] at hres
      injection hres with hm; subst hm
      have hls : ls = [] := List.eq_nil_of_length_eq_zero hlen
      subst hls
      rw [instantiateLevels_nil]
      exact ⟨.succ (.succ .zero),
        fundT_sort (ctxModelTLaws_approxT fundDeltaEnv) (.succ .zero)⟩
    · rw [fundDeltaEnv_members_ne h0 h1] at hres
      exact Option.noConfusion hres

/-- `MemberBodyDiagT` at `fundDeltaEnv`: the only member-with-body is `d₀ := Sort 0`,
    whose typing diagonal is `sort` and whose conversion diagonal is the `sort`
    reflexivity; the axiom member has no body. -/
theorem fundDeltaEnv_memberBodyDiag (n : Nat) :
    MemberBodyDiagT (ctxModelT_approxT fundDeltaEnv) (WhStepCtx fundDeltaEnv) n := by
  intro Γ r m b ls ls' hres hbody hlen hlen' hwf hwf' heq hΓ hV
  by_cases h0 : r = 0
  · subst h0
    rw [fundDeltaEnv_members_zero] at hres
    injection hres with hm; subst hm
    obtain rfl : _ = b := Option.some.inj hbody
    have hls : ls = [] := List.eq_nil_of_length_eq_zero hlen
    have hls' : ls' = [] := List.eq_nil_of_length_eq_zero hlen'
    subst hls; subst hls'
    simp only [instantiateLevels_nil]
    exact ⟨fundT_sort (ctxModelTLaws_approxT fundDeltaEnv) .zero,
      fundT_sort (ctxModelTLaws_approxT fundDeltaEnv) .zero⟩
  · by_cases h1 : r = 1
    · subst h1
      rw [fundDeltaEnv_members_one] at hres
      injection hres with hm; subst hm
      exact Option.noConfusion hbody
    · rw [fundDeltaEnv_members_ne h0 h1] at hres
      exact Option.noConfusion hres

end Rcic.Declarative.NativeValleys.TypedModelAudit
