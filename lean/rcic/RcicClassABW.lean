import rcic.RcicClassABDelta
import rcic.RcicTypedFunRecPins

/-!
# cc-classab — class (a): the function-recursive ι cell at the W fixture

The Type-valued twin of `RcicAccPiMeasure` at `wEnvWfT` (`RcicTypedFunRecPins`): the Nat core, then
`W : Sort 1`, `sup : (a : Nat) → (f : Nat → W) → W`, `Wrec`. The field `f` is function-recursive, and
`main`'s ι refuses it (`supIota_legacy_refused`), so `ConvT` has no ι at `sup`. Unlike Acc, both
fields of `sup` are DATA, so no bare ★-unfold rule can express the extension's ι: the rule needs the
constructor-major pattern (G1's bare overrides do not cover it).

`closure_claim = 0`.
-/

namespace Rcic.Syn.ClassAB

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Syn
open Rcic.Syn.ClassC

/-- the redex `Wrec.{u} M m (sup a f)`. -/
def wIotaLhs : Expr Nat :=
  foldApps (.const 6 [.param 0]) [.bvar 3, .bvar 2, .app (.app (.const 5 []) (.bvar 1)) (.bvar 0)]

def wTy (Γ : LCtx) (e T : Expr Nat) (h : (tyAtC wEnv 1 8 Γ e T).isSome = true) :
    HasTyT wEnv 1 Γ e T :=
  (tyAtC wEnv 1 8 Γ e T).get h

def wIotaLhsTy : HasTyT wEnv 1 wIotaCtx wIotaLhs wEqTy := wTy _ _ _ rfl
def wIotaRhsTy : HasTyT wEnv 1 wIotaCtx wSchema wEqTy := wTy _ _ _ rfl

/-- the minor's sort. -/
abbrev wMinorU : Level :=
  .imax (.succ .zero) (.imax (.imax (.succ .zero) (.succ .zero))
    (.imax (.imax (.succ .zero) (.param 0)) (.param 0)))

def wIotaCtxWf : CtxWfT wEnv 1 wIotaCtx :=
  .assumption _ wFieldF _
    (.assumption _ wFieldA _
      (.assumption _ wMinorTy _
        (.assumption [] wMotTy _ .nil
          (wTy [] wMotTy (.sort (.imax (.succ .zero) (.succ (.param 0)))) rfl))
        (wTy _ wMinorTy (.sort wMinorU) rfl))
      (wTy _ wFieldA (.sort (.succ .zero)) rfl))
    (wTy _ wFieldF (.sort (.imax (.succ .zero) (.succ .zero))) rfl)

def wIotaScope : ScopedCtx wEnv wEnv 1 wIotaCtx :=
  ⟨wEnvWfT, envExt_refl _, wIotaCtxWf⟩

noncomputable def wIotaLhsP : TyP wEnv 1 wIotaCtx wIotaLhs wEqTy :=
  enrichHasTyT_of_envWfT wEnvWfT wIotaCtxWf wIotaLhsTy
noncomputable def wIotaRhsP : TyP wEnv 1 wIotaCtx wSchema wEqTy :=
  enrichHasTyT_of_envWfT wEnvWfT wIotaCtxWf wIotaRhsTy

/-- the erased redex: `rec M m (sup a f)`, both data fields KEPT. -/
def wLhsE (ls : List Level) : ETm :=
  ETm.appN (.const 6 ls) [.bvar 3, .bvar 2, ETm.appN (.const 5 []) [.bvar 1, .bvar 0]]

/-- the erased contractum: `m a f (λ b. rec M m (f b))`. -/
def wRhsE (ls : List Level) : ETm :=
  .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
    (.lam (ETm.appN (.const 6 ls) [.bvar 4, .bvar 3, .app (.bvar 1) (.bvar 0)]))

theorem w_can : wIotaScope.can id = [.keep, .keep, .keep, .keep] := by
  with_unfolding_all rfl

theorem w_eps_lhs : wIotaLhsP.eps id (wIotaScope.can id) = wLhsE [.param 0] := by
  with_unfolding_all rfl

theorem w_eps_rhs : wIotaRhsP.eps id (wIotaScope.can id) = wRhsE [.param 0] := by
  with_unfolding_all rfl

/-! ## §2 `tableOfK` at the W fixture is the Nat core's -/

theorem natEnvU_members (c : Nat) :
    natEnvU.members c =
      if c = 3 then some natRecMemberU else if c = 2 then some natSuccMember
      else if c = 1 then some natZeroMember else if c = 0 then some natFamMember else none := rfl

theorem natEnvU_lt {c : Nat} {m : CheckedMember} (h : natEnvU.members c = some m) : c < 4 := by
  rw [natEnvU_members] at h
  by_cases h3 : c = 3
  · omega
  by_cases h2 : c = 2
  · omega
  by_cases h1 : c = 1
  · omega
  by_cases h0 : c = 0
  · omega
  simp [h3, h2, h1, h0] at h

theorem tableOfK_w : tableOfK wEnvWfT = tableOfK natEnvUWfT := by
  show iotaRulesKOf 4 wFamMember [(5, wSupMember)] 6 wRecMember ++ tableOfK natEnvUWfT = _
  have : iotaRulesKOf 4 wFamMember [(5, wSupMember)] 6 wRecMember = [] := rfl
  rw [this]; rfl

/-- every rule of the table is headed below `4` and matches a constructor below `4`: it is the Nat
    core's. -/
theorem tableOfK_w_low {σ : CRule} (h : σ ∈ tableOfK wEnvWfT) :
    σ.head < 4 ∧ ∀ {e : Nat} {n : List Level → Nat}, σ.major = some (e, n) → e < 4 := by
  rw [tableOfK_w] at h
  rcases tableOfK_head_major natEnvUWfT σ h with ⟨m, hm, -, htb⟩ | ⟨m, hm, -, hmaj⟩
  · exact ⟨natEnvU_lt hm, fun {e n} hmj => by
      rw [major_none_tableOf natEnvUWfT σ htb] at hmj; cases hmj⟩
  · refine ⟨natEnvU_lt hm, fun {e n} hmj => ?_⟩
    rcases hmaj with hn | ⟨d, k, md, hmaj', hd, -⟩
    · rw [hn] at hmj; cases hmj
    · rw [hmaj'] at hmj
      injection hmj with hmj
      injection hmj with hde _
      subst hde
      exact natEnvU_lt hd

/-! ## §3 the erased cell is not closed by `tableOfK` -/

/-- terms with no `λ`, no `Π` and no constant below `k`. -/
def ETm.plainGe (k : Nat) : ETm → Bool
  | .app f a => ETm.plainGe k f && ETm.plainGe k a
  | .const c _ => decide (k ≤ c)
  | .lam _ => false
  | .pi _ _ => false
  | _ => true

theorem plainGe_appN_head {k : Nat} : ∀ (xs : List ETm) {f : ETm},
    ETm.plainGe k (ETm.appN f xs) = true → ETm.plainGe k f = true
  | [], _, h => h
  | x :: xs, f, h => by
      have := plainGe_appN_head xs h
      simp only [ETm.plainGe, Bool.and_eq_true] at this
      exact this.1

/-- at a table headed below `k`, a term without `λ`, `Π` and constants below `k` is `E`-normal. -/
theorem eStep_headLt_plain {k : Nat} {tbl : List CRule} (hh : ∀ ρ ∈ tbl, ρ.head < k) {t z : ETm}
    (ht : ETm.plainGe k t = true) (h : EStep tbl t z) : False := by
  rcases h with h | h
  · induction h with
    | beta M N => simp [ETm.plainGe] at ht
    | cr hc =>
        cases hc with
        | bare hρ hm ls args hn =>
            have := plainGe_appN_head args ht
            simp only [ETm.plainGe] at this
            have h1 := of_decide_eq_true this
            have h2 := hh _ hρ
            omega
        | ctor hρ hm ls ls' args bs hn hb =>
            have := plainGe_appN_head _ ht
            simp only [ETm.plainGe] at this
            have h1 := of_decide_eq_true this
            have h2 := hh _ hρ
            omega
    | appL a _ ih =>
        simp only [ETm.plainGe, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.plainGe, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.plainGe] at ht
    | piL _ _ => simp [ETm.plainGe] at ht
    | piR _ _ => simp [ETm.plainGe] at ht
  · induction h with
    | eta F => simp [ETm.plainGe] at ht
    | appL a _ ih =>
        simp only [ETm.plainGe, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.plainGe, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.plainGe] at ht
    | piL _ _ => simp [ETm.plainGe] at ht
    | piR _ _ => simp [ETm.plainGe] at ht

theorem wLhsE_plain (ls : List Level) : ETm.plainGe 4 (wLhsE ls) = true := rfl

theorem w_not_convE_tableOfK (ls : List Level) :
    ¬ ConvMod (EStep (tableOfK wEnvWfT)) LvlEq (wLhsE ls) (wRhsE ls) := by
  intro h
  have hW : TableWF (tableOfK wEnvWfT) := tableWF_tableOfK wEnvWfT
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  obtain rfl := rstar_of_normal
    (fun z hz => eStep_headLt_plain (fun ρ hρ => (tableOfK_w_low hρ).1) (wLhsE_plain ls) hz) hc
  have hdh : ETm.spineHead d = .bvar 2 := rstar_spineHead_bvar hd rfl
  have := lvlEq_spineHead_bvar (lvlEq_equivalence.symm hq) hdh
  cases this

/-- **`tableOfK` does not close the function-recursive ι cell at W.** -/
theorem w_iota_not_es_tableOfK :
    ¬ ConvMod (EStep (tableOfK wEnvWfT)) LvlEq (wIotaLhsP.eps id (wIotaScope.can id))
      (wIotaRhsP.eps id (wIotaScope.can id)) := by
  rw [w_eps_lhs, w_eps_rhs]
  exact w_not_convE_tableOfK _

/-! ## §4 a constructor-major rule closes it -/

def wMajorRule : CRule where
  head := 6
  nargs := fun _ => 2
  major := some (5, fun _ => 2)
  rhs := fun ls _ => .lam (.lam (.lam (.lam (wRhsE ls))))

noncomputable def wExtTable : List CRule := wMajorRule :: tableOfK wEnvWfT

theorem wExtTable_wf : TableWF wExtTable := by
  refine tableWF_cons_major (tableWF_tableOfK wEnvWfT) (d := 5) (m := fun _ => 2) rfl ?_ ?_
    (by decide) ?_ ?_ ?_
  · exact
      { rhs := by
          intro ρ hρ ls ls₂ ms ms₂ hls _
          simp only [List.mem_singleton] at hρ; subst hρ
          exact .lam (.lam (.lam (.lam (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
            (.lam (.app (.app (.app (.const 6 hls) (.bvar 4)) (.bvar 3))
              (.app (.bvar 1) (.bvar 0))))))))
        nargs := by
          intro ρ hρ _ _ _
          simp only [List.mem_singleton] at hρ; subst hρ; rfl
        marity := by
          intro ρ hρ d m hm ls ls₂ _
          simp only [List.mem_singleton] at hρ; subst hρ
          simp only [wMajorRule, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨-, rfl⟩ := hm; rfl }
  · intro ls ms
    simp [wMajorRule, wRhsE, ETm.appN, ETm.ClosedAt]
  · intro σ hσ; have := (tableOfK_w_low hσ).1; show σ.head ≠ 6; omega
  · intro σ hσ; have := (tableOfK_w_low hσ).1; show σ.head ≠ 5; omega
  · intro σ hσ e n hσm
    have := (tableOfK_w_low hσ).2 hσm
    show e ≠ 6
    omega

theorem wMajorRule_mem : wMajorRule ∈ wExtTable := List.Mem.head _

theorem w_chain (ls : List Level) : RStar (RStep wExtTable) (wLhsE ls) (wRhsE ls) :=
  .step (.cr (.ctor wMajorRule_mem rfl ls [] [.bvar 3, .bvar 2] [.bvar 1, .bvar 0] rfl rfl))
    (.step (rStep_appN_head (.beta _ (.bvar 3)) [.bvar 2, .bvar 1, .bvar 0])
      (.step (rStep_appN_head (.beta _ (.bvar 2)) [.bvar 1, .bvar 0])
        (.step (rStep_appN_head (.beta _ (.bvar 1)) [.bvar 0])
          (.step (.beta _ (.bvar 0)) (.refl _)))))

/-- **the constructor-major rule closes the function-recursive ι cell at W.** -/
theorem w_iota_es_ext :
    ConvMod (EStep wExtTable) LvlEq (wIotaLhsP.eps id (wIotaScope.can id))
      (wIotaRhsP.eps id (wIotaScope.can id)) := by
  rw [w_eps_lhs, w_eps_rhs]
  exact convMod_of_rstar_estep (w_chain _)

theorem w_ext_confluent : Confluent (EStep wExtTable) := confluent_eStep_wf wExtTable_wf

theorem w_ext_sortSep {l l' : Level} (h : ConvMod (EStep wExtTable) LvlEq (.sort l) (.sort l')) :
    eqN l l' :=
  eqN_of_convE_sort_wf wExtTable_wf h

theorem w_ext_piInj {A B A' B' : ETm} (h : ConvMod (EStep wExtTable) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep wExtTable) LvlEq A A' ∧ ConvMod (EStep wExtTable) LvlEq B B' :=
  convE_pi_inv_wf wExtTable_wf h

/-- no rule of the extended table is headed at the family `W` (`4`). -/
theorem w_ext_noHead_fam : NoHeadRule wExtTable 4 := by
  intro ρ hρ hh
  rcases List.mem_cons.mp hρ with h | h
  · rw [h] at hh; exact absurd hh (by decide)
  · have := (tableOfK_w_low h).1; omega

theorem w_ext_famRigid {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep wExtTable) LvlEq (ETm.appN (.const 4 ls) xs) (ETm.appN (.const 4 ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧ List.Forall₂ (ConvMod (EStep wExtTable) LvlEq) xs ys :=
  convE_appN_const_inv_wf wExtTable_wf w_ext_noHead_fam h

end Rcic.Syn.ClassAB
