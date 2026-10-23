import rcic.RcicClassABCex
import rcic.RcicAccPiMeasure

/-!
# cc-classab — class (b): the ι cell at the δ-hidden fixture, measured by the landed `TyP.eps`

The twin of `RcicAccPiMeasure` §1–§2 at `drEnvWfT` (`Id : Sort 1 → Sort 1 := λ A, A`, `F : Sort 1`,
`mk : Id F → F`, `F.rec`). `ConvT` has no ι at `mk` (`dr_no_derivedIota`), so the cell is a typed pair
of the extension's ι (`DerivedIotaT`), not a `ConvT` node. Both endpoints are `HasTyT`-typed at an
admitted scope; the landed erasure is read off by `rfl`.

`closure_claim = 0`.
-/

namespace Rcic.Syn.ClassAB

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Syn
open Rcic.Syn.ClassC

/-- the redex `F.rec.{u} M m (mk x)`. -/
def drIotaLhs : Expr Nat :=
  foldApps (.const 3 [.param 0]) [.bvar 2, .bvar 1, .app (.const 2 []) (.bvar 0)]

def drTy (Γ : LCtx) (e T : Expr Nat) (h : (tyAtC drEnv 1 8 Γ e T).isSome = true) :
    HasTyT drEnv 1 Γ e T :=
  (tyAtC drEnv 1 8 Γ e T).get h

def drIotaLhsTy : HasTyT drEnv 1 drIotaCtx drIotaLhs drEqTy := drTy _ _ _ rfl
def drIotaRhsTy : HasTyT drEnv 1 drIotaCtx drSchema drEqTy := drTy _ _ _ rfl

/-- the minor's sort. -/
abbrev drMinorU : Level := .imax (.succ .zero) (.imax (.param 0) (.param 0))

def drIotaCtxWf : CtxWfT drEnv 1 drIotaCtx :=
  .assumption _ drField _
    (.assumption _ drMinorTy _
      (.assumption [] drMotiveTy _ .nil
        (drTy [] drMotiveTy (.sort (.imax (.succ .zero) (.succ (.param 0)))) rfl))
      (drTy _ drMinorTy (.sort drMinorU) rfl))
    (drTy _ drField (.sort (.succ .zero)) rfl)

/-- the admitted scope of the ι cell. -/
def drIotaScope : ScopedCtx drEnv drEnv 1 drIotaCtx :=
  ⟨drEnvWfT, envExt_refl _, drIotaCtxWf⟩

noncomputable def drIotaLhsP : TyP drEnv 1 drIotaCtx drIotaLhs drEqTy :=
  enrichHasTyT_of_envWfT drEnvWfT drIotaCtxWf drIotaLhsTy
noncomputable def drIotaRhsP : TyP drEnv 1 drIotaCtx drSchema drEqTy :=
  enrichHasTyT_of_envWfT drEnvWfT drIotaCtxWf drIotaRhsTy

/-- the erased redex: `rec M m (mk x)` — the data field is KEPT (its type `Id F : Sort 1` is no proof). -/
def drLhsE (ls : List Level) : ETm :=
  ETm.appN (.const 3 ls) [.bvar 2, .bvar 1, .app (.const 2 []) (.bvar 0)]

/-- the erased contractum: `m x (rec M m x)`. -/
def drRhsE (ls : List Level) : ETm :=
  .app (.app (.bvar 1) (.bvar 0)) (ETm.appN (.const 3 ls) [.bvar 2, .bvar 1, .bvar 0])

theorem dr_can : drIotaScope.can id = [.keep, .keep, .keep] := by
  with_unfolding_all rfl

theorem dr_eps_lhs : drIotaLhsP.eps id (drIotaScope.can id) = drLhsE [.param 0] := by
  with_unfolding_all rfl

theorem dr_eps_rhs : drIotaRhsP.eps id (drIotaScope.can id) = drRhsE [.param 0] := by
  with_unfolding_all rfl

/-! ## §2 `tableOfK` at the δ-hidden env: only `Id`'s δ rule -/

theorem dr_iotaRulesKOf_nil :
    iotaRulesKOf 1 drFamMember [(2, drMkMember)] 3 drRecMember = [] := rfl

theorem tableOfK_dr : tableOfK drEnvWfT = tableOfK drBaseWfT := by
  show iotaRulesKOf 1 drFamMember [(2, drMkMember)] 3 drRecMember ++ tableOfK drBaseWfT = _
  rw [dr_iotaRulesKOf_nil]
  rfl

/-- every rule of `tableOfK drEnvWfT` is `Id`'s bare δ rule. -/
theorem tableOfK_dr_bare {σ : CRule} (h : σ ∈ tableOfK drEnvWfT) : σ.head = 0 ∧ σ.major = none := by
  rw [tableOfK_dr] at h
  change σ ∈ (_ :: tableOfK EnvWfT.empty : List CRule) at h
  rw [tableOfK_empty] at h
  rcases List.mem_cons.mp h with rfl | h
  · exact ⟨rfl, rfl⟩
  · cases h

theorem tableOfK_dr_head {σ : CRule} (h : σ ∈ tableOfK drEnvWfT) : σ.head = 0 :=
  (tableOfK_dr_bare h).1

/-! ## §3 the erased cell is not closed by `tableOfK` -/

/-- terms with no `λ`, no `Π` and no constant `Id`. -/
def ETm.plainNo0 : ETm → Bool
  | .app f a => ETm.plainNo0 f && ETm.plainNo0 a
  | .const c _ => c != 0
  | .lam _ => false
  | .pi _ _ => false
  | _ => true

theorem plainNo0_appN_head : ∀ (xs : List ETm) {f : ETm},
    ETm.plainNo0 (ETm.appN f xs) = true → ETm.plainNo0 f = true
  | [], _, h => h
  | x :: xs, f, h => by
      have := plainNo0_appN_head xs h
      simp only [ETm.plainNo0, Bool.and_eq_true] at this
      exact this.1

/-- at a table headed only at `Id`, a term without `λ`, `Π` and `Id` is `E`-normal. -/
theorem eStep_headZero_plain {tbl : List CRule} (hh : ∀ ρ ∈ tbl, ρ.head = 0) {t z : ETm}
    (ht : ETm.plainNo0 t = true) (h : EStep tbl t z) : False := by
  rcases h with h | h
  · induction h with
    | beta M N => simp [ETm.plainNo0] at ht
    | cr hc =>
        cases hc with
        | bare hρ hm ls args hn =>
            have := plainNo0_appN_head args ht
            simp only [ETm.plainNo0, hh _ hρ] at this
            exact absurd this (by decide)
        | ctor hρ hm ls ls' args bs hn hb =>
            have := plainNo0_appN_head _ ht
            simp only [ETm.plainNo0, hh _ hρ] at this
            exact absurd this (by decide)
    | appL a _ ih =>
        simp only [ETm.plainNo0, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.plainNo0, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.plainNo0] at ht
    | piL _ _ => simp [ETm.plainNo0] at ht
    | piR _ _ => simp [ETm.plainNo0] at ht
  · induction h with
    | eta F => simp [ETm.plainNo0] at ht
    | appL a _ ih =>
        simp only [ETm.plainNo0, Bool.and_eq_true] at ht
        exact ih ht.1
    | appR f _ ih =>
        simp only [ETm.plainNo0, Bool.and_eq_true] at ht
        exact ih ht.2
    | lam _ => simp [ETm.plainNo0] at ht
    | piL _ _ => simp [ETm.plainNo0] at ht
    | piR _ _ => simp [ETm.plainNo0] at ht

theorem drLhsE_plain (ls : List Level) : ETm.plainNo0 (drLhsE ls) = true := rfl

/-- the redex is stuck and `const`-headed, every reduct of the contractum is `bvar 1`-headed. -/
theorem dr_not_convE_tableOfK (ls : List Level) :
    ¬ ConvMod (EStep (tableOfK drEnvWfT)) LvlEq (drLhsE ls) (drRhsE ls) := by
  intro h
  have hW : TableWF (tableOfK drEnvWfT) := tableWF_tableOfK drEnvWfT
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  obtain rfl := rstar_of_normal
    (fun z hz => eStep_headZero_plain (fun ρ hρ => tableOfK_dr_head hρ) (drLhsE_plain ls) hz) hc
  have hdh : ETm.spineHead d = .bvar 1 := rstar_spineHead_bvar hd rfl
  have := lvlEq_spineHead_bvar (lvlEq_equivalence.symm hq) hdh
  cases this

/-- **`tableOfK` does not close the δ-hidden ι cell.** -/
theorem dr_iota_not_es_tableOfK :
    ¬ ConvMod (EStep (tableOfK drEnvWfT)) LvlEq (drIotaLhsP.eps id (drIotaScope.can id))
      (drIotaRhsP.eps id (drIotaScope.can id)) := by
  rw [dr_eps_lhs, dr_eps_rhs]
  exact dr_not_convE_tableOfK _

/-! ## §4 a constructor-major rule closes it, and keeps the table `TableWF` -/

/-- adding ONE major rule at a fresh recursor head keeps `TableWF`: its constructor head is never a
    rule head, and no major rule of the table matches its head. -/
theorem tableWF_cons_major {t : List CRule} {ρ : CRule} (ht : TableWF t) {d : Nat}
    {m : List Level → Nat} (hm : ρ.major = some (d, m)) (hcongr : TableCongr [ρ])
    (hclosed : ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)) (hρd : ρ.head ≠ d)
    (hfresh : ∀ σ ∈ t, σ.head ≠ ρ.head) (hrigid : ∀ σ ∈ t, σ.head ≠ d)
    (hnoctor : ∀ σ ∈ t, ∀ {e : Nat} {n : List Level → Nat}, σ.major = some (e, n) → e ≠ ρ.head) :
    TableWF (ρ :: t) where
  congr := tableCongr_append hcongr ht.congr
  closed := by
    intro σ hσ ls ms
    rcases List.mem_cons.mp hσ with h | hσ
    · rw [h]; exact hclosed ls ms
    · exact ht.closed σ hσ ls ms
  rigid := by
    intro σ hσ e n hσm τ hτ
    rcases List.mem_cons.mp hσ with h | hσ
    · rw [h, hm] at hσm
      injection hσm with hσm
      injection hσm with hde _
      subst hde
      rcases List.mem_cons.mp hτ with h' | hτ
      · rw [h']; exact hρd
      · exact hrigid τ hτ
    · rcases List.mem_cons.mp hτ with h' | hτ
      · rw [h']; exact fun h => hnoctor σ hσ hσm h.symm
      · exact ht.rigid σ hσ hσm τ hτ
  bare_unique := by
    intro σ hσ hσm τ hτ hh
    rcases List.mem_cons.mp hσ with h | hσ
    · rw [h, hm] at hσm; cases hσm
    · rcases List.mem_cons.mp hτ with h' | hτ
      · rw [h'] at hh; exact absurd hh.symm (hfresh σ hσ)
      · exact ht.bare_unique σ hσ hσm τ hτ hh
  ctor_disjoint := by
    intro σ hσ τ hτ hh e e' n n' hσm hτm
    rcases List.mem_cons.mp hσ with h | hσ <;> rcases List.mem_cons.mp hτ with h' | hτ
    · rw [h, h']; exact ⟨rfl, fun _ => rfl⟩
    · rw [h] at hh; exact absurd hh.symm (hfresh τ hτ)
    · rw [h'] at hh; exact absurd hh (hfresh σ hσ)
    · exact ht.ctor_disjoint σ hσ τ hτ hh hσm hτm
  bare_nullary := by
    intro σ hσ hσm ls
    rcases List.mem_cons.mp hσ with h | hσ
    · rw [h, hm] at hσm; cases hσm
    · exact ht.bare_nullary σ hσ hσm ls

/-- the constructor-major ι rule of the δ-hidden group, as `tableOfK` emits it for an ordinary group:
    `rec M m (mk x) ↦ m x (rec M m x)`. -/
def drMajorRule : CRule where
  head := 3
  nargs := fun _ => 2
  major := some (2, fun _ => 1)
  rhs := fun ls _ =>
    .lam (.lam (.lam (.app (.app (.bvar 1) (.bvar 0))
      (ETm.appN (.const 3 ls) [.bvar 2, .bvar 1, .bvar 0]))))

noncomputable def drExtTable : List CRule := drMajorRule :: tableOfK drEnvWfT

theorem drExtTable_wf : TableWF drExtTable := by
  refine tableWF_cons_major (tableWF_tableOfK drEnvWfT) (d := 2) (m := fun _ => 1) rfl ?_ ?_
    (by decide) ?_ ?_ ?_
  · exact
      { rhs := by
          intro ρ hρ ls ls₂ ms ms₂ hls _
          simp only [List.mem_singleton] at hρ; subst hρ
          exact .lam (.lam (.lam (.app (.app (.bvar 1) (.bvar 0))
            (.app (.app (.app (.const 3 hls) (.bvar 2)) (.bvar 1)) (.bvar 0)))))
        nargs := by
          intro ρ hρ _ _ _
          simp only [List.mem_singleton] at hρ; subst hρ; rfl
        marity := by
          intro ρ hρ d m hm ls ls₂ _
          simp only [List.mem_singleton] at hρ; subst hρ
          simp only [drMajorRule, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨-, rfl⟩ := hm; rfl }
  · intro ls ms
    simp [drMajorRule, ETm.appN, ETm.ClosedAt]
  · intro σ hσ; rw [tableOfK_dr_head hσ]; decide
  · intro σ hσ; rw [tableOfK_dr_head hσ]; decide
  · intro σ hσ e n hσm
    rw [(tableOfK_dr_bare hσ).2] at hσm
    cases hσm

theorem drMajorRule_mem : drMajorRule ∈ drExtTable := List.Mem.head _

/-- the chain: the constructor-major rule at `mk x`, then three β. -/
theorem dr_chain (ls : List Level) : RStar (RStep drExtTable) (drLhsE ls) (drRhsE ls) :=
  .step (.cr (.ctor drMajorRule_mem rfl ls [] [.bvar 2, .bvar 1] [.bvar 0] rfl rfl))
    (.step (rStep_appN_head (.beta _ (.bvar 2)) [.bvar 1, .bvar 0])
      (.step (rStep_appN_head (.beta _ (.bvar 1)) [.bvar 0])
        (.step (.beta _ (.bvar 0)) (.refl _))))

/-- **the constructor-major rule closes the δ-hidden ι cell**: the two landed-`TyP.eps` endpoints are
    `E`-convertible under `drExtTable`. -/
theorem dr_iota_es_ext :
    ConvMod (EStep drExtTable) LvlEq (drIotaLhsP.eps id (drIotaScope.can id))
      (drIotaRhsP.eps id (drIotaScope.can id)) := by
  rw [dr_eps_lhs, dr_eps_rhs]
  exact convMod_of_rstar_estep (dr_chain _)

/-- the extended erased system is confluent. -/
theorem dr_ext_confluent : Confluent (EStep drExtTable) := confluent_eStep_wf drExtTable_wf

theorem dr_ext_sortSep {l l' : Level} (h : ConvMod (EStep drExtTable) LvlEq (.sort l) (.sort l')) :
    eqN l l' :=
  eqN_of_convE_sort_wf drExtTable_wf h

theorem dr_ext_piInj {A B A' B' : ETm} (h : ConvMod (EStep drExtTable) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep drExtTable) LvlEq A A' ∧ ConvMod (EStep drExtTable) LvlEq B B' :=
  convE_pi_inv_wf drExtTable_wf h

/-- no rule of the extended table is headed at the family `F`. -/
theorem dr_ext_noHead_fam : NoHeadRule drExtTable 1 := by
  intro ρ hρ hh
  rcases List.mem_cons.mp hρ with h | h
  · rw [h] at hh; exact absurd hh (by decide)
  · rw [tableOfK_dr_head h] at hh; exact absurd hh (by decide)

theorem dr_ext_famRigid {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep drExtTable) LvlEq (ETm.appN (.const 1 ls) xs) (ETm.appN (.const 1 ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧ List.Forall₂ (ConvMod (EStep drExtTable) LvlEq) xs ys :=
  convE_appN_const_inv_wf drExtTable_wf dr_ext_noHead_fam h

end Rcic.Syn.ClassAB
