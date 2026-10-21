import rcic.RcicParRedTSubst
import rcic.RcicDTMetaTypedSR
import rcic.RcicDT0709EnvWf

/-!
# `parRedT_substSame'` — the uniform typed substitution WITHOUT the simulation premise (W-X-SUBST S0, #7107)

`parRedT_substSame` (`RcicParRedTSubst.lean:1056`) carries `hTC : ParRedT → ConvT` that its body never
consumes (measured: the binder and the recursive passes are its only occurrences). This is the same
definition by the same induction with that binder removed — the sealed original is untouched. cc's ruling on
#7107: X/D/J use only this twin, which also removes the DT-012 circularity (`hTC`'s only supplier,
`parRedT_to_convT`, needs type uniqueness under `CtxWfT`). The premises that remain are the real ones:
`CtxWfT` of both contexts, regularity as data `hS`, the un-lifted `hvt`, and the `PEq` suppliers.

One premise is WEAKER than the original's: `hS` is `CtxWfT`-conditional. The original's `hS` is
Γ-unconditional, which no environment can supply (`[x : lit 5] ⊢ bvar 0 : lit 5` has no sort typing of
`lit 5`) — so the original is unpinnable as stated. The body's single `hS` call (the `app` arm) sits
where `hΓwf : CtxWfT E n Γ` is in scope, so the conditional supplier discharges it by the same term.
`parRedT_substSame'_uncond` is the exact-premise twin (original `hS`), a one-line corollary.
Pinned on a real β step under `[x : N]` substituted by `zero` (`RcicParRedTSubstNoTCPins`,
`natEnvU`, `hS` from `endpoints3_of_envWfT`). `closure_claim` 0.
-/

namespace Rcic.Declarative

section
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat}

-- The merged-main dependency cone needs more elaboration heartbeats; the term is unchanged.
set_option maxHeartbeats 800000 in
def parRedT_substSame'
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat}, CtxWfT E n Γ →
        HasTyT E n Γ e T → (u : Level) ×' HasTyT E n Γ T (.sort u))
    (hPEqSub : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.assumption t) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedT PEq E n Γ a b T →
    (hget : Γ[j]? = some (.assumption t)) →
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) →
    (hΓwf : CtxWfT E n Γ) →
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | _,  _,  _,  _, _, ParRedT.refl _ _ _ h, hget, hvty, _, _, _ =>
      .refl _ _ _ (hasTyT_substS hcl hinst v t h hget hvty)
  | _,  _,  _,  _, _, .sortEq _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .sortEq _ _ _ _ h
        (hasTyT_substS hcl hinst v t hl hget hvty)
        (hasTyT_substS hcl hinst v t hr hget hvty)
  | _,  _,  _,  _, _, .consts _ _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .consts _ _ _ _ _ h
        (hasTyT_substS hcl hinst v t hl hget hvty)
        (hasTyT_substS hcl hinst v t hr hget hvty)
  | j,  Γ,  _,  _, _, .delta _ r ls m b T hres hbody htr hlen hwf hl hr,
      hget, hvty, _, _, _ => by
      have hid := (hinst r m hres).2 b hbody ls (lift 0 j v) j
      simp only [instantiate]
      rw [hid]
      have hr' := hasTyT_substS hcl hinst v t hr hget hvty
      rw [hid] at hr'
      exact .delta _ _ _ _ _ _ hres hbody htr hlen hwf
        (hasTyT_substS hcl hinst v t hl hget hvty) hr'
  | j,  Γ,  _,  _, _, .conv _ a b A A' h hc, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have h' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        h hget hvty hvt hΓ'wf hΓwf
      have hc' := tyConvT_substS hcl hinst v t hc hget hvty
      exact .conv _ _ _ _ _ h' hc'
  | j,  Γ,  _,  _, _, .lit _ tl _ hexp, hget, hvty, _, _, _ => by
      have hexp' := hasTyT_substS hcl hinst v t hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      rw [natExpand_instantiate j (lift 0 j v) tl]
      exact .lit _ _ _ hexp'
  | j,  Γ,  _,  _, _, .eta _ f f' A B hf hl, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hf' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hf hget hvty hvt hΓ'wf hΓwf
      have hl' := hasTyT_substS hcl hinst v t hl hget hvty
      simp only [instantiate,
        if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
        if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
        at hf' hl' ⊢
      have e2 : instantiate (j + 1) (lift 0 1 (lift 0 j v)) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      rw [e2] at hl' ⊢
      exact .eta _ _ _ _ _ hf' hl'
  | j,  Γ,  _,  _, _, .peq _ p q _ h, hget, hvty, _, _, _ =>
      .peq _ _ _ _ (hPEqSub h hget hvty)
  | j,  Γ,  _,  _, _, .iotaSpine _ lhs lhs' rhs _ hstep hI hred hrhs,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hstep' := parRedT_substSame' hcl hinst hPEqL hPEqT hS
        hPEqSub hstep hget hvty hvt hΓ'wf hΓwf
      have hI' := derivedIotaU_subst j (lift 0 j v) hI
      exact .iotaSpine _ _ _ _ _ hstep' hI'
        (hasTyT_substS hcl hinst v t hred hget hvty)
        (hasTyT_substS hcl hinst v t hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarK _ w major Tm rhs _ rl afs hrl hsel hfam
      hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hI' := derivedIotaU_subst j (lift 0 j v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hlι' := hasTyT_substS hcl hinst v t hlι hget hvty
      rw [← iotaLhsOf_instantiate] at hlι'
      have hlhs' := hasTyT_substS hcl hinst v t hlhs hget hvty
      rw [recCall_instantiate] at hlhs'
      simp only [instantiate] at hlhs'
      rw [recCall_instantiate]
      simp only [instantiate]
      have hmk' := hasTyT_substS hcl hinst v t hmk hget hvty
      rw [← ctorMajor_instantiate] at hmk'
      have hfam' : ∃ lsF, (appsSpine (instantiate j (lift 0 j v) Tm)).1 =
          .const (instWitness j (lift 0 j v) w).familyRef lsF := by
        obtain ⟨lsF, hf⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const j (lift 0 j v)
              w.familyRef lsF Tm hf)
          simp only [instWitness] at this
          exact this⟩
      exact .iotaStarK _ (instWitness j (lift 0 j v) w) _ _ _ _ _ _
        hrl hsel hfam'
        (hasTyT_substS hcl hinst v t hmajor hget hvty)
        hmk'
        (hasTyT_substS hcl hinst v t hTm0 hget hvty)
        hI' hlι' hlhs'
        (hasTyT_substS hcl hinst v t hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs happ hA hf
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hb0 : instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0 : Expr Nat) = .bvar 0 := by
        simp only [instantiate,
          if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
          if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
      have hsrc :
          instantiate (j + 1) (lift 0 (j + 1) v)
            (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) =
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) := by
        rw [recCall_instantiate, hb0]; rfl
      have e2 : instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [← lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      have happ' :
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) =
          .app (lift 0 1 (instantiate j (lift 0 j v) f)) (.bvar 0) := by
        rw [← hsrc, happ]
        change Expr.app (instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f))
          (instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0)) = _
        rw [e2, hb0]
      have hfam' : ∃ lsF, (appsSpine (instantiate (j + 1) (lift 0 (j + 1) v) Tm)).1 =
          .const (instWitness (j + 1) (lift 0 (j + 1) v) w).familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const (j + 1) (lift 0 (j + 1) v)
              w.familyRef lsF Tm hlsF)
          simp only [instWitness] at this
          exact this⟩
      have hI' := derivedIotaU_subst (j + 1) (lift 0 (j + 1) v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hmajor' := hasTyT_substS hcl hinst v t hmajor hget' hvty'
      have hmk' := hasTyT_substS hcl hinst v t hmk hget' hvty'
      have hTm0' := hasTyT_substS hcl hinst v t hTm0 hget' hvty'
      have hlι' := hasTyT_substS hcl hinst v t hlι hget' hvty'
      have hlhs' := hasTyT_substS hcl hinst v t hlhs hget' hvty'
      have hrhs' := hasTyT_substS hcl hinst v t hrhs hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hmajor' hmk' hTm0' hlι' hlhs' hrhs'
      rw [hb0] at hmajor'
      rw [← ctorMajor_instantiate] at hmk'
      rw [← iotaLhsOf_instantiate] at hlι'
      rw [hsrc] at hlhs'
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hf' := hasTyT_substS hcl hinst v t hf hget hvty
      simp only [instantiate] at hf' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hf' ⊢
      exact .iotaStarKEta _ (instWitness (j + 1) (lift 0 (j + 1) v) w) _ _ _ _ _ _ _ _
        happ' hA' hf' hrl hsel hfam' hmajor' hmk' hTm0' hI' hlι' hlhs' hrhs'
  | j, Γ, _, _, _, .app _ f f' a a' A B T₀ u w hf hc hB hTy ha hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hf' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hf hget hvty hvt hΓ' hΓwf
      have ha' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        ha hget hvty hvt hΓ' hΓwf
      have hpi := (hS hΓwf (hasTyT_of_tyConvT
        (parRedT_typed hPEqT hΓwf hf).1 hc)).2
      have ⟨u₀, w₀, hAu, hBw, _⟩ := hasTyTInv_pi hpi rfl
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hAu
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hc' := tyConvT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw
        (parRedT_typed hPEqT hΓwf ha).1
      have hTy' := hasTyT_substS hcl hinst v t hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' ⊢
      have happT := HasTyT.app _ _ _ _ _
        (hasTyT_of_tyConvT (parRedT_typed hPEqT hΓ' hf').2 hc')
        (parRedT_typed hPEqT hΓ' ha').2
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at happT
      have hr' := hasTyT_substS hcl hinst v t hr hget hvty
      simp only [instantiate] at hr'
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hr'
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) T₀)
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        have h0 := tyConvT_substS hcl hinst v t hc hget hvty
        simp only [instantiate] at h0 ⊢
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
          at h0
        exact h0
      exact .app _ _ _ _ _ _ _ _ _ _ hf' hcc hB' hTy' ha' hr'
  | j,  Γ,  _,  _, _, .beta _ A body body' arg arg' B u v' w hA hB hTy hb ha
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have ha' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        ha hget hvty hvt hΓ' hΓwf
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hred' := hasTyT_substS hcl hinst v t hred hget hvty
      have hcommB : instantiate j (lift 0 j v) (instantiate0 arg B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg (lift 0 j v)
          (Nat.zero_le j) B
      have hcommBody : instantiate j (lift 0 j v) (instantiate0 arg' body') =
          instantiate0 (instantiate j (lift 0 j v) arg')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .beta _ _ _ _ _ _ _ _ _ _ hA' hB' hTy' hb' ha' hred'
  | j,  Γ,  _,  _, _, .lam _ A A' body body' B u v' hc hA hB hb hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      simp only [instantiate] at hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .lam _ _ _ _ _ _ _ _ hcA hA' hB' hb' hrt'
  | j,  Γ,  _,  _, _, .pi _ A A' B B' u v' hA hc hB hcB hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hcB' := convT_substS hcl hinst v t hcB hget' hvty'
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      simp only [instantiate, substRemove_succ_cons, instDecl]
        at hcB' hB' hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .pi _ _ _ _ _ _ _ hA' hcA hB' hcB' hrt'
  | j,  Γ,  _,  _, _, .letE _ A A' value value' body body' B u w hc hA hv hB
      hTy hb hrt, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := subst_arg_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := subst_arg_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hv' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      simp only [instantiate] at hTy' hrt' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' hrt' ⊢
      exact .letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv' hB' hTy' hb' hrt'
  | j,  Γ,  _,  _, _, .zeta _ A value value' body body' B u w hA hv hB hTy hb
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := subst_arg_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := subst_arg_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hv' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame' hcl hinst hPEqL hPEqT hS hPEqSub
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hred' := hasTyT_substS hcl hinst v t hred hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      have hcomm' : instantiate j (lift 0 j v) (instantiate0 value' body') =
          instantiate0 (instantiate j (lift 0 j v) value')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .zeta _ _ _ _ _ _ _ _ _ hA' hv' hB' hTy' hb' hred'
  | j,  Γ,  _,  _, _, .bvarZeta _ i A val val' T h hv hl hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      by_cases hij : i = j
      · subst hij
        have h' : Γ[i]? = some (.letBinding A val) :=
          (List.get?_eq_getElem? Γ i).symm ▸ h
        rw [h'] at hget
        exact nomatch hget
      · by_cases hlt : i < j
        · -- the let slot sits above the hole: index keeps `i`, the
          -- stored decl is `instDecl`-instantiated, and the value step
          -- recurses in the dropped tail at the shifted hole `j-i-1`.
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_lt (v := v) hlt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) v) =
              lift 0 j v := by
            have hc := lift_zero_comp (i + 1) (j - i - 1) v
            rw [show i + 1 + (j - i - 1) = j from by omega] at hc
            exact hc
          have hcomm (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 (i + 1)
                  (instantiate (j - i - 1) (lift 0 (j - i - 1) v) e) := by
            have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1)
              (lift 0 (j - i - 1) v) (Nat.zero_le _) e
            rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
            exact h1.symm
          have hstored : stored =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) val :=
            lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm val))
          have hdrop : (substRemove v j Γ).drop (i + 1) =
              substRemove v (j - i - 1) (Γ.drop (i + 1)) := by
            rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
            congr 1
          have hgetD : (Γ.drop (i + 1))[j - i - 1]? =
              some (.assumption t) := by
            rw [← List.get?_eq_getElem?, get?_drop,
              show j - i - 1 + (i + 1) = j from by omega]
            exact (List.get?_eq_getElem? Γ j).symm ▸ hget
          have hvtD : HasTyT E n
              ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) v t := by
            have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) =
                Γ.drop (j + 1) := by
              rw [List.drop_drop]
              congr 1
              omega
            rw [hd]; exact hvt
          have hvtyD := subst_hvty_of_drop hcl hgetD hvtD
          have hΓwfD := ctxWfT_drop hΓwf (i + 1)
          have hΓ'wfD : CtxWfT E n
              (substRemove v (j - i - 1) (Γ.drop (i + 1))) :=
            hdrop ▸ ctxWfT_drop hΓ'wf (i + 1)
          have hv' := parRedT_substSame' hcl hinst hPEqL hPEqT hS
            hPEqSub hv hgetD hvtyD hvtD hΓ'wfD hΓwfD
          rw [← hdrop] at hv'
          have hA' : A' =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_lt (v := v) hlt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) i =
                some (lift 0 (i + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            exact lift_zero_amount_inj (i + 1)
              (hinj.trans (hcomm A))
          rw [← hstored, ← hA'] at hv'
          have hl' := hasTyT_substS hcl hinst v t hl hget hvty
          have hr' := hasTyT_substS hcl hinst v t hr hget hvty
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)] at hl' hr'
          rw [hcomm val'] at hr'
          exact (hcomm val') ▸
            .bvarZeta _ i A' stored
              (instantiate (j - i - 1) (lift 0 (j - i - 1) v) val') _
              hg' hv' hl' hr'
        · -- the let slot sits below the hole: index drops to `i-1`,
          -- the stored decl passes through untouched, `hv` needs no
          -- recursion (the hole is gone from the dropped tail).
          have hgt : j < i := by omega
          simp only [instantiate, if_neg hij, if_pos hgt]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_gt (v := v) hgt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 i e :=
            instantiate_lift_cancel (i + 1) 0 j (lift 0 j v)
              (Nat.zero_le j) (by omega) e
          have hi1 : i - 1 + 1 = i := by omega
          have hstored : stored = val := by
            have heq' : lift 0 i stored = lift 0 i val := by
              have h1 := heq.symm.trans (hcan val)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hA' : A' = A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_gt (v := v) hgt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) (i - 1) =
                some (lift 0 ((i - 1) + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            have heq' : lift 0 i A' = lift 0 i A := by
              have h1 := hinj.trans (hcan A)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hdrop : (substRemove v j Γ).drop i =
              Γ.drop (i + 1) := by
            rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
          have hv' : ParRedT PEq E n
              ((substRemove v j Γ).drop (i - 1 + 1)) val val' A := by
            rw [hi1]; exact hdrop ▸ hv
          have hl' := hasTyT_substS hcl hinst v t hl hget hvty
          have hr' := hasTyT_substS hcl hinst v t hr hget hvty
          simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr'
          rw [hcan val'] at hr'
          have hr'' : HasTyT E n (substRemove v j Γ)
              (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) := by
            rw [hi1]; exact hr'
          have htgt : lift 0 i val' =
              instantiate j (lift 0 j v) (lift 0 (i + 1) val') :=
            (hcan val').symm
          rw [← hstored, ← hA'] at hv'
          exact htgt ▸ (hi1 ▸
            .bvarZeta _ (i - 1) A' stored val' _ hg' hv' hl' hr'')
  termination_by j Γ a b T h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)


/-- the exact-premise twin: the original's Γ-unconditional `hS`, no `hTC`. -/
def parRedT_substSame'_uncond
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → (u : Level) ×' HasTyT E n Γ T (.sort u))
    (hPEqSub : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.assumption t) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v t : Expr Nat} {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT PEq E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t)
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hΓwf : CtxWfT E n Γ) :
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T) :=
  parRedT_substSame' hcl hinst hPEqL hPEqT (fun _ h => hS h) hPEqSub
    h hget hvty hvt hΓ'wf hΓwf

end

end Rcic.Declarative

#print axioms Rcic.Declarative.parRedT_substSame'
#print axioms Rcic.Declarative.parRedT_substSame'_uncond
