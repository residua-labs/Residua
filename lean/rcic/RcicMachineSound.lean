/-
RCIC F-03 Batch A — soundness rows (M-3, M-7, M-10 partial).
Imports RcicMachine + RcicConvChar + RcicParRedSR — no cycle.
Placement rule: everything consuming ParRedStar/RedOnly lives HERE.
-/
import rcic.RcicMachine
import rcic.RcicDTMeta
import rcic.RcicConvChar
import rcic.RcicParRedSR

namespace Rcic.Machine
open Rcic.Declarative

/-! ## M-2 (continued): machineRed_toParRedStar — the second map

`machineRed_toParRedStar` moved to `RcicMachine` (same `Rcic.Machine` FQN)
so the typed slice (`RcicMachineSoundTyped`) can reach it without
importing this module — and with it the legacy `RcicParRedSR` chain,
whose six helper names (`get?_lt_length`,
`lookupType_getQ_letBinding`, `lookup{Type,Value}_replace_let_{zero,ne}`)
still collide with `RcicParRedSRTyped`'s copies at this head.  Open PR
#6265 moves those six to single ownership in `RcicConvChar`; once it
lands, the collision — and this move — can be reverted. -/

/-! ## M-3: slice subject reduction — machineRedSR -/

/-- Spine transport (Annex 21 M-3): `hasTyAppInv` returns the function's
Π-typing directly and `HasTy.conv` consumes the inversion's conversion
without inverting anything (§19.3 F-05b C-1 applied to a new statement). -/
noncomputable def hasTyFoldAppsHead {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f f' : Expr Nat}
    (hstep : (S : Expr Nat) → HasTy E n Γ f S →
       HasTy E n Γ f' S) :
    (xs : List (Expr Nat)) → {T : Expr Nat} →
    HasTy E n Γ (foldApps f xs) T →
    HasTy E n Γ (foldApps f' xs) T
  | [], _, h => hstep _ h
  | x :: xs, _, h =>
      hasTyFoldAppsHead (f := .app f x) (f' := .app f' x)
        (fun S hS =>
          let ⟨A0, B0, hf, ha, hcv⟩ := hasTyAppInv hS rfl
          .conv Γ (.app f' x) (instantiate0 x B0) S
            (.app Γ f' x A0 B0 (hstep (.pi A0 B0) hf) ha) hcv)
        xs h

/-- A single beta step preserves typing (M-3's core; transcribed from
`oneStepSR`'s beta arm, `RcicDTMeta.lean:420-438`, C-11/G-28: closes with
`.conv … (Conv.symm …)` to land at `S`). -/
noncomputable def machineBetaStep {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) (A body arg : Expr Nat) :
    (S : Expr Nat) → HasTy E n Γ (.app (.lam A body) arg) S →
    HasTy E n Γ (instantiate0 arg body) S
  | _, h => by
      let ⟨A_inv, B_inv, hf, ha, hcv⟩ := hasTyAppInv h rfl
      let ⟨_u, B_lam, _hAty, hbody, hcv_lam⟩ := hasTyLamInv hf rfl
      let ⟨hdom, hcod⟩ := hpci hE Γ A B_lam A_inv B_inv hΓ hcv_lam
      have ha' : HasTy E n Γ arg A :=
        .conv _ _ _ _ ha (.symm _ _ _ hdom)
      have hget : (LocalDecl.assumption A :: Γ)[(0:Nat)]? =
          some (.assumption A) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove arg 0 (LocalDecl.assumption A :: Γ))
          (lift 0 0 arg) (lift 0 0 A) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact ha'
      have hty0 := hasTySubst (j := 0) hE
        arg A hbody hget hvty
      have hcod0 := convSubst (j := 0) hE
        arg A hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hty0 hcod0
      exact .conv _ _ _ _ hty0 (.trans _ _ _ _ hcod0 hcv)

/-- A single zeta step preserves typing (zeta arm `:439-454`; carries
`hE` ALONE — the arm names no `CtxWf`). -/
noncomputable def machineZetaStep {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx}
    (A value body : Expr Nat) :
    (S : Expr Nat) → HasTy E n Γ (.letE A value body) S →
    HasTy E n Γ (instantiate0 value body) S
  | _, h => by
      let ⟨_u, B_let, _hAty, hv, hb, hcv⟩ := hasTyLetInv h rfl
      have hget : (LocalDecl.letBinding A value :: Γ)[(0:Nat)]? =
          some (.letBinding A value) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove value 0 (LocalDecl.letBinding A value :: Γ))
          (lift 0 0 value) (lift 0 0 A) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hv
      have hty0 := hasTySubstLet (j := 0) hE
        A value hb hget hvty
      have hcod0 := convSubstLet (j := 0) hE
        A value (a := B_let) (b := B_let)
        (.refl (LocalDecl.letBinding A value :: Γ) B_let) hget hvty
      rw [substRemove_zero_cons, lift_zero] at hty0 hcod0
      exact .conv _ _ _ _ hty0 (.trans _ _ _ _ hcod0 hcv)

/-- A single delta step preserves typing (delta arm `:462-471`; carries
`hE` alone, no `htr`). -/
noncomputable def machineDeltaStep {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx} (r : Nat) (ls : List Level)
    (m : CheckedMember) (b : Expr Nat)
    (hres : E.members r = some m) (hbody : m.body = some b) :
    (S : Expr Nat) → HasTy E n Γ (.const r ls) S →
    HasTy E n Γ (instantiateLevels ls b) S
  | _, h => by
      let ⟨m', hres', hlen, hcv⟩ := hasTyConstInv h rfl
      have hmeq : some m = some m' := hres.symm.trans hres'
      injection hmeq with hmeq'
      subst hmeq'
      have hty := envWf_bodyTyped hE Γ r m b ls hres hbody hlen
      exact .conv _ _ _ _ hty hcv

/-- HasTy is preserved along MachineRed (the machine's slice), by
iterated head steps under `hasTyFoldAppsHead`. -/
noncomputable def machineRedSR {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) :
    {e A e' : Expr Nat} → HasTy E n Γ e A →
    MachineRed E n Γ e e' → HasTy E n Γ e' A
  | _, _, _, h, k =>
      match k, h with
      | .refl _ _, h => h
      | .headBeta _ A body arg rest k', h =>
          machineRedSR hpci hE hΓ
            (hasTyFoldAppsHead
              (machineBetaStep hpci hE hΓ A body arg) rest h) k'
      | .headZeta _ A value body rest k', h =>
          machineRedSR hpci hE hΓ
            (hasTyFoldAppsHead
              (machineZetaStep hE A value body) rest h) k'
      | .headDelta _ r ls m b rest hres hbody _htr k', h =>
          machineRedSR hpci hE hΓ
            (hasTyFoldAppsHead
              (machineDeltaStep hE r ls m b hres hbody) rest h) k'

/-! ## M-7: join rows -/

/-- RedOnly of a bare step (top-level statement so the iota-reduction
happens during elaboration, unlike under a metavariable). -/
theorem redOnly_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat}
    (hs : Step E n Γ a b) : RedOnly (.step Γ a b hs) := trivial

/-- machineConvFoldApps preserves RedOnly (app of refl is red-only). -/
theorem machineConvFoldApps_redOnly {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat} (hf : Conv E n Γ f f') (hro : RedOnly hf)
    (xs : List (Expr Nat)) :
    RedOnly (machineConvFoldApps hf xs) := by
  cases xs with
  | nil => exact hro
  | cons x xs =>
      have happ : RedOnly (.app Γ f f' x x hf (.refl Γ x)) :=
        ⟨hro, trivial⟩
      exact machineConvFoldApps_redOnly _ happ xs

/-- machineRed_toConv produces only RedOnly Conv values
(every MachineRed arm is steps/refl/trans — no irr, no eta). -/
theorem machineRed_toConv_redOnly {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (k : MachineRed E n Γ a b) →
    RedOnly (machineRed_toConv k)
  | _, _, _, .refl _ _ => by simp only [machineRed_toConv]; trivial
  | _, _, _, .headBeta _ A body arg rest k => by
      simp only [machineRed_toConv]
      exact ⟨machineConvFoldApps_redOnly
        (.step _ (.app (.lam A body) arg) (instantiate0 arg body)
          (.beta _ A body arg)) (redOnly_step _) rest,
        machineRed_toConv_redOnly k⟩
  | _, _, _, .headZeta _ A value body rest k => by
      simp only [machineRed_toConv]
      exact ⟨machineConvFoldApps_redOnly
        (.step _ (.letE A value body) (instantiate0 value body)
          (.zeta _ A value body)) (redOnly_step _) rest,
        machineRed_toConv_redOnly k⟩
  | _, _, _, .headDelta _ r ls m b rest hres hbody htr k => by
      simp only [machineRed_toConv]
      exact ⟨machineConvFoldApps_redOnly
        (.step _ (.const r ls) (instantiateLevels ls b)
          (.delta _ r ls m b hres hbody htr)) (redOnly_step _) rest,
        machineRed_toConv_redOnly k⟩

/-- RM017_cert_redOnly: convCert produces only RedOnly Conv values. -/
theorem RM017_cert_redOnly {E : ResolvedEnv} {n : Nat}
    (fuel : Nat) (Γ : LCtx) (A l r : Expr Nat)
    (c : Conv E n Γ l r)
    (h : convCert E n fuel Γ A l r = .ok c) :
    RedOnly c := by
  induction fuel generalizing Γ A l r c with
  | zero =>
      -- E-F03 (a)(iii), attempt 1: the restored M-4 arm is
      -- unconditional at fuel 0 — no ite left to split, the equation
      -- is an immediate constructor clash
      rw [convCert] at h
      cases h
  | succ f ih =>
      simp only [convCert] at h
      split at h
      · -- l = r: c := .refl
        rename_i hlr; subst hlr
        injection h with hc; subst hc; trivial
      · split at h
        · -- whnf l = .no msg
          nomatch h
        · split at h
          · -- whnf r = .no msg
            nomatch h
          · split at h
            · -- wl = wr
              rename_i hwleq; subst hwleq
              injection h with hc; subst hc
              exact ⟨machineRed_toConv_redOnly _, ⟨trivial,
                machineRed_toConv_redOnly _⟩⟩
            · -- wl ≠ wr: head match (sort/const/app/catch-all) +
              -- ites; closer per Annex 21 §21.7 D-75 (which amends
              -- D-71 with the two-attempt record and the seal-axiom
              -- backstop). The app-congruence arm nests the two
              -- recursive-call matches — the extra `try split`s
              -- expose their .ok/.no cases; the .ok·.ok leaf's
              -- sub-derivations are RedOnly by `ih` (discharged
              -- through the split-produced convCert equations).
              split at h
              all_goals try split at h
              all_goals try split at h
              all_goals try simp_all [RedOnly, machineRed_toConv_redOnly]
              · rw [← h]
                exact ⟨machineRed_toConv_redOnly _,
                  ⟨⟨ih _ _ _ _ _ (by assumption),
                    ih _ _ _ _ _ (by assumption)⟩,
                    machineRed_toConv_redOnly _⟩⟩

/-- RM017_cert_join: convCert output joins at a common reduct (EnvWf). -/
noncomputable def RM017_cert_join {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (fuel : Nat) (Γ : LCtx) (A l r : Expr Nat)
    (c : Conv E n Γ l r)
    (h : convCert E n fuel Γ A l r = .ok c) :
    Σ' (d : Expr Nat), ParRedStar E n Γ l d ×' ParRedStar E n Γ r d :=
  convRedOnly_join hE c (RM017_cert_redOnly fuel Γ A l r c h)

/-! ## M-10: soundness rows that consume ParRedStar/RedOnly -/

/-- RM014_whnf_typed: WHNF preserves the type (machineRedSR applied). -/
noncomputable def RM014_whnf_typed {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ)
    (s : RawState) (hamb : s.ambient = ⟨E, n, Γ⟩)
    (A e w : Expr Nat) (htask : s.task = .whnfAt A e)
    (hty : HasTy E n Γ e A)
    (hacc : kernelStepRaw s = .result (.accepted (.inferredWhnf A w))) :
    HasTy E n Γ w A := by
  -- Unfold kernelStepRaw at the whnfAt arm to get whnfCert's .ok
  -- containing the MachineRed chain, then apply machineRedSR.
  cases hb : s.budget with
  | zero =>
      simp only [kernelStepRaw, htask, hb] at hacc
      nomatch hacc
  | succ b =>
      simp only [kernelStepRaw, htask, hb] at hacc
      split at hacc
      · next w' kred _heq =>
          have hw : w' = w := by
            simp only [StepOutcome.result.injEq, RunResult.accepted.injEq,
              AcceptedPayload.inferredWhnf.injEq] at hacc
            exact hacc.2
          subst hw
          -- kred : MachineRed s.ambient.… e w; transport (E-P2-13):
          rw [hamb] at kred
          exact machineRedSR hpci hE hΓ hty kred
      · nomatch hacc

/-- RM018_no_irr_in_slice: convCert never produces Conv.irr. -/
theorem RM018_no_irr_in_slice {E : ResolvedEnv} {n : Nat}
    (fuel : Nat) (Γ : LCtx) (A P p q : Expr Nat)
    (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ p P) (hq : HasTy E n Γ q P) :
    convCert E n fuel Γ A p q ≠ .ok (Conv.irr Γ P p q hP hp hq) := by
  intro h
  have hro := RM017_cert_redOnly fuel Γ A p q _ h
  exact hro

/-- RM019_no_eta_in_slice: convCert never produces Conv.eta. -/
theorem RM019_no_eta_in_slice {E : ResolvedEnv} {n : Nat}
    (fuel : Nat) (Γ : LCtx) (A f dom cod : Expr Nat)
    (hf : HasTy E n Γ f (.pi dom cod)) :
    convCert E n fuel Γ A
        (.lam dom (.app (lift 0 1 f) (.bvar 0))) f
      ≠ .ok (Conv.eta Γ f dom cod hf) := by
  intro h
  have hro := RM017_cert_redOnly fuel Γ A _ f _ h
  exact hro

/-! ## RM017_join_typed (needs parRedStarSR + FamAppConvInj) -/

noncomputable def RM017_join_typed {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n) {Γ : LCtx} (hΓ : CtxWf E n Γ)
    (fuel : Nat) (A l r T : Expr Nat) (c : Conv E n Γ l r)
    (h : convCert E n fuel Γ A l r = .ok c)
    (hty : HasTy E n Γ l T) :
    Σ' (d : Expr Nat), ParRedStar E n Γ l d ×' ParRedStar E n Γ r d ×' HasTy E n Γ d T := by
  have ⟨d, hd1, hd2⟩ := RM017_cert_join hE fuel Γ A l r c h
  exact ⟨d, hd1, hd2, parRedStarSR hpci hfaci hE hΓ hty hd1⟩

end Rcic.Machine
