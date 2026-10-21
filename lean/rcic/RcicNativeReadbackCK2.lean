import rcic.RcicNativeReadbackCK2Conv

/-!
# CK2: the native index-conversion candidate, on the entire CK core

The old `WhStepCK` is unchanged. Every K step in this new relation carries
the explicit `KIndexConvAt` and `KCommonAt` certificates. Context reduction,
head reduction and non-K major reduction retain the old scheduling policy.
In particular, a new K step can occur inside either recursive context.

The structural argument below classifies every additional source as a
saturated recursor spine. It reuses the landed context exclusions and canon
uniqueness rather than copying CK's individual normal-head inductions.
Determinism quantifies over every source in a well-formed environment; there
is no source-typing restriction in `DetR`. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2Audit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- The repaired K relation, with the complete two recursive contexts. -/
inductive WhStepCK2 (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop
  | ctx {a b} (h : WhStepCtx E Γ a b) : WhStepCK2 E n Γ a b
  | native {a b} (h : KNativeHead E n Γ a b) : WhStepCK2 E n Γ a b
  | recMajor {r : Nat} {m : CheckedMember} {ls : List Level}
      {pre : List (Expr Nat)} {x x' : Expr Nat}
      (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
      (hlen : pre.length + 1 = piCount m.mtype)
      (hnK : ¬ KFreeRec E r) (hnP : ¬ KProjRec E r)
      (h : WhStepCK2 E n Γ x x') :
      WhStepCK2 E n Γ (recCall (.const r ls) pre x)
        (recCall (.const r ls) pre x')
  | appHead {f f' a} (h : WhStepCK2 E n Γ f f') :
      WhStepCK2 E n Γ (.app f a) (.app f' a)

/-- The source invariant of every step added to `WhStepCtx`. -/
def SaturatedRecSource (E : ResolvedEnv) (e : Expr Nat) : Prop :=
  ∃ (r : Nat) (ls : List Level) (xs : List (Expr Nat)) (m : CheckedMember),
    e = foldApps (.const r ls) xs ∧ E.members r = some m ∧
    m.mclass = .recursorM ∧ 0 < xs.length ∧ piCount m.mtype ≤ xs.length

theorem saturatedRecSource_app {f a : Expr Nat} (h : SaturatedRecSource E f) :
    SaturatedRecSource E (.app f a) := by
  obtain ⟨r, ls, xs, m, rfl, hm, hr, hp, hl⟩ := h
  exact ⟨r, ls, xs ++ [a], m, (foldApps_snoc _ _ _).symm, hm, hr,
    by simp, by simpa using Nat.le_trans hl (Nat.le_add_right xs.length 1)⟩

/-- One subderivation induction handles every additional source shape. -/
theorem whStepCK2_ctx_or_saturated {a b : Expr Nat} (h : WhStepCK2 E n Γ a b) :
    WhStepCtx E Γ a b ∨ SaturatedRecSource E a := by
  induction h with
  | ctx h => exact .inl h
  | native h =>
      cases h with
      | intro hK hnc hi hc =>
          rename_i w x
          refine .inr ⟨w.recRef, w.ls, w.preMajor ++ [x], w.recMember,
            ?_, w.hrec, w.hrecK, by simp, ?_⟩
          · rw [recCall_eq_app, foldApps_snoc]
          · have h₁ := w.hpre; have h₂ := w.hnmin
            simp only [List.length_append, List.length_singleton]
            omega
  | @recMajor r m ls pre x x' hm hr hl _ _ _ _ =>
      refine .inr ⟨r, ls, pre ++ [x], m, ?_, hm, hr, by simp, ?_⟩
      · rw [recCall_eq_app, foldApps_snoc]
      · simpa using Nat.le_of_eq hl.symm
  | appHead _ ih =>
      exact ih.elim (fun hs => .inl (.appHead hs))
        (fun hs => .inr (saturatedRecSource_app hs))

/-- Every additional source is an application, independently of admission. -/
theorem saturatedRecSource_is_app {a : Expr Nat} (h : SaturatedRecSource E a) :
    ∃ f x, a = .app f x := by
  obtain ⟨r, ls, xs, m, he, _, _, hp, _⟩ := h
  rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
  · simp at hp
  · exact ⟨_, x, he.trans (foldApps_snoc _ _ _)⟩

/-- At a fixed constant spine, the invariant identifies its member and arity. -/
theorem saturatedRecSource_spine {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) {ls : List Level} {xs : List (Expr Nat)}
    (h : SaturatedRecSource E (foldApps (.const r ls) xs)) :
    m.mclass = .recursorM ∧ piCount m.mtype ≤ xs.length := by
  obtain ⟨s, us, ys, mm, he, hs, hr, _, hl⟩ := h
  obtain ⟨hhead, hargs⟩ := foldApps_const_inj he
  obtain ⟨rfl, rfl⟩ := Expr.const.inj hhead
  obtain rfl := Option.some.inj (hm.symm.trans hs)
  exact ⟨hr, hargs ▸ hl⟩

theorem normalR_sortCK2 (Γ : LCtx) (u : Level) :
    NormalR (WhStepCK2 E n) Γ (.sort u) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_sort_false h
  · obtain ⟨f, a, he⟩ := saturatedRecSource_is_app h
    exact Expr.noConfusion he

theorem normalR_piCK2 (Γ : LCtx) (A B : Expr Nat) :
    NormalR (WhStepCK2 E n) Γ (.pi A B) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_pi_false h
  · obtain ⟨f, a, he⟩ := saturatedRecSource_is_app h
    exact Expr.noConfusion he

theorem normalR_lamCK2 (Γ : LCtx) (A body : Expr Nat) :
    NormalR (WhStepCK2 E n) Γ (.lam A body) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_lam_false_aux h rfl
  · obtain ⟨f, a, he⟩ := saturatedRecSource_is_app h
    exact Expr.noConfusion he

theorem normalR_bvarCK2 {i : Nat} (hv : lookupValue Γ i = none) :
    NormalR (WhStepCK2 E n) Γ (.bvar i) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCK_bvar_none_false hv (.ctx h) rfl
  · obtain ⟨f, a, he⟩ := saturatedRecSource_is_app h
    exact Expr.noConfusion he

theorem normalR_famAppCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .inductiveM)
    (Γ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) xs) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_famApp_false hW hm hr xs h
  · exact MemberClass.noConfusion ((saturatedRecSource_spine hm h).1.symm.trans hr)

theorem normalR_ctorSpineCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .constructorM)
    (Γ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) xs) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_ctorApp_false_aux hW hm hr h xs rfl
  · exact MemberClass.noConfusion ((saturatedRecSource_spine hm h).1.symm.trans hr)

theorem normalR_recPrefixCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .recursorM)
    (Γ : LCtx) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length + 1 ≤ piCount m.mtype) :
    NormalR (WhStepCK2 E n) Γ (foldApps (.const r ls) xs) := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_recPrefix_false_aux hW hm hr h rfl hlen
  · have := (saturatedRecSource_spine hm h).2
    omega

/-- The entire landed relation interface, at the new readback. -/
theorem readbackLaws_whStepCK2 (E : ResolvedEnv) (n : Nat) :
    ReadbackLaws E (WhStepCK2 E n) where
  sort_normal := normalR_sortCK2
  pi_normal := normalR_piCK2
  famApp_normal := fun hW Γ _ _ hm hr ls xs => normalR_famAppCK2 hW hm hr Γ ls xs
  appHead := fun _ _ _ _ h => .appHead h
  beta := fun _ A body arg => .ctx (.beta A body arg)

/-- The small application inversion shared by the new compatibility proofs. -/
theorem whStepCtx_app_cases {f a b : Expr Nat} (h : WhStepCtx E Γ (.app f a) b) :
    (∃ A body, f = .lam A body ∧ b = instantiate0 a body) ∨
    Nonempty (DerivedIotaU E (.app f a) b) ∨
    (∃ f', WhStepCtx E Γ f f' ∧ b = .app f' a) := by
  cases h with
  | beta A body a => exact .inl ⟨A, body, rfl, rfl⟩
  | iota hi => exact .inr (.inl ⟨hi⟩)
  | appHead h => exact .inr (.inr ⟨_, h, rfl⟩)

/-- Context reduction at a saturated recursor requires a constructor major. -/
theorem whStepCtx_recCall_ctor (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .recursorM)
    {ls : List Level} {pre : List (Expr Nat)} {x b : Expr Nat}
    (hlen : pre.length + 1 = piCount m.mtype)
    (h : WhStepCtx E Γ (recCall (.const r ls) pre x) b) : IsCtorSpine E x := by
  have hh : WhStepCtx E Γ (.app (foldApps (.const r ls) pre) x) b := by
    simpa only [recCall_eq_app] using h
  rcases whStepCtx_app_cases hh with ⟨A, body, hf, _⟩ | hi | ⟨f', hf, _⟩
  · exact (F8EtaK.foldApps_const_ne_lam_any hf).elim
  · obtain ⟨hi⟩ := hi
    generalize he : Expr.app (foldApps (.const r ls) pre) x = lhs at hi
    cases hi with
    | ofU w =>
        rw [iotaLhsOf_eq_app] at he
        exact ⟨w.ctorRef, w.lsC, w.ctorParams ++ w.fields,
          w.ctorMember, (Expr.app.inj he).2, w.hctor, w.hctorK⟩
    | ofUS w =>
        unfold iotaLhsOfS at he
        rw [recCall_eq_app] at he
        exact ⟨w.ctorRef, w.lsC, w.ctorParams ++ w.fields,
          w.ctorMember, (Expr.app.inj he).2, w.hctor, w.hctorK⟩
  · exact (whStepCtx_recPrefix_false_aux hW hm hr hf rfl (by omega)).elim

/-- A context step and a CK2 step at the same source coincide. -/
theorem whStepCK2_ctx_det (hW : EnvWfT E) {a b c : Expr Nat}
    (hs : WhStepCtx E Γ a b) (ht : WhStepCK2 E n Γ a c) : b = c := by
  induction ht generalizing b with
  | ctx ht => exact detR_whStepCK hW Γ (.ctx hs) (.ctx ht)
  | native ht => exact (kNativeHead_ck_det hW ht (.ctx hs)).symm
  | recMajor hm hr hl _ _ hsub _ =>
      obtain ⟨r, us, ys, m, he, hc, hk⟩ := whStepCtx_recCall_ctor hW hm hr hl hs
      subst he
      exact (normalR_ctorSpineCK2 hW hc hk _ _ _ _ hsub).elim
  | appHead hsub ih =>
      rcases whStepCtx_app_cases hs with ⟨A, body, rfl, _⟩ | hi | ⟨f', hf, rfl⟩
      · exact (normalR_lamCK2 _ _ _ _ hsub).elim
      · obtain ⟨hi⟩ := hi
        rcases derivedIotaU_app_head hi rfl with ⟨w, hf, hl⟩ | ⟨w, hf, hl⟩
        · subst hf
          exact (normalR_recPrefixCK2 hW w.hrec w.hrecK _ _ _ hl _ hsub).elim
        · subst hf
          exact (normalR_recPrefixCK2 hW w.hrec w.hrecK _ _ _ hl _ hsub).elim
      · exact congrArg (fun f => Expr.app f _) (ih hf)

/-- Injectivity of the fixed recursor spine, independent of the reduction rule. -/
theorem recCall_const_inj {r s : Nat} {ls us : List Level}
    {pre other : List (Expr Nat)} {x y : Expr Nat}
    (h : recCall (.const r ls) pre x = recCall (.const s us) other y) :
    r = s ∧ ls = us ∧ pre = other ∧ x = y := by
  have hh : .app (foldApps (.const r ls) pre) x =
      Expr.app (foldApps (.const s us) other) y := by
    simpa only [recCall_eq_app] using h
  obtain ⟨hf, hx⟩ := Expr.app.inj hh
  obtain ⟨hc, hp⟩ := foldApps_const_inj hf
  obtain ⟨hr, hu⟩ := Expr.const.inj hc
  exact ⟨hr, hu, hp, hx⟩

/-- The canonical K head is compatible with the complete new core. -/
theorem kNativeHead_whStepCK2_det (hW : EnvWfT E) {a b c : Expr Nat}
    (hk : KNativeHead E n Γ a b) (hs : WhStepCK2 E n Γ a c) : b = c := by
  cases hk with
  | intro hK hnc hi hc =>
      rename_i w x
      generalize he : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at hs
      cases hs with
      | ctx h =>
          exact (whStepCtx_recCall_nonCtorMajor_aux hW (he.symm ▸ h) rfl hnc).elim
      | native h =>
          exact detR_kNativeHead E n Γ (.intro hK hnc hi hc) (he.symm ▸ h)
      | recMajor hm hr hl hnK hnP h =>
          have hh := (recCall_const_inj he).1
          rcases hK with hK | ⟨hK, _⟩
          · exact (hnK ⟨w, hh, hK⟩).elim
          · exact (hnP ⟨w, hh, hK⟩).elim
      | appHead h =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [← hh] at h
          exact (normalR_recPrefixCK2 hW w.hrec w.hrecK _ _ _
            (by have h₁ := w.hpre; have h₂ := w.hnmin; omega) _ h).elim

/-- Determinism on the whole core, by induction only on a step's children. -/
theorem detR_whStepCK2 (hW : EnvWfT E) : DetR (WhStepCK2 E n) := by
  intro Γ a b c h₁ h₂
  induction h₁ generalizing c with
  | ctx h => exact whStepCK2_ctx_det hW h h₂
  | native h => exact kNativeHead_whStepCK2_det hW h h₂
  | recMajor hm hr hl hnK hnP hs ih =>
      rename_i r m ls pre x x'
      generalize he : recCall (.const r ls) pre x = a₀ at h₂
      cases h₂ with
      | ctx h =>
          exact (whStepCK2_ctx_det hW (he.symm ▸ h)
            (.recMajor hm hr hl hnK hnP hs)).symm
      | native h =>
          exact (kNativeHead_whStepCK2_det hW (he.symm ▸ h)
            (.recMajor hm hr hl hnK hnP hs)).symm
      | recMajor hm' hr' hl' hnK' hnP' ht =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := recCall_const_inj he
          exact congrArg (recCall (.const r ls) pre) (ih ht)
      | appHead h =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [← hh] at h
          exact (normalR_recPrefixCK2 hW hm hr _ _ _ (by omega) _ h).elim
  | appHead hs ih =>
      rename_i f f' x
      generalize he : Expr.app f x = a₀ at h₂
      cases h₂ with
      | ctx h => exact (whStepCK2_ctx_det hW (he.symm ▸ h) (.appHead hs)).symm
      | native h => exact (kNativeHead_whStepCK2_det hW (he.symm ▸ h) (.appHead hs)).symm
      | recMajor hm hr hl _ _ h =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [hh] at hs
          exact (normalR_recPrefixCK2 hW hm hr _ _ _ (by omega) _ hs).elim
      | appHead ht =>
          obtain ⟨rfl, rfl⟩ := Expr.app.inj he
          exact congrArg (fun f => Expr.app f x) (ih ht)

theorem normalUniqueR_whStepCK2 (hW : EnvWfT E) : NormalUniqueR (WhStepCK2 E n) :=
  normalUniqueR_of_det (detR_whStepCK2 hW)

/-- At a K-eligible recursor and non-constructor major, excluding the native
gate excludes every core step. The premise names the head rule, not a
normality or normalization assumption. -/
theorem normalR_kRec_of_no_native (hW : EnvWfT E) {w : IotaWitness E}
    {x : Expr Nat} (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
    (hnative : ∀ e, ¬ KNativeHead E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor x) e) :
    NormalR (WhStepCK2 E n) Γ (recCall (.const w.recRef w.ls) w.preMajor x) := by
  intro e hs
  generalize he : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at hs
  cases hs with
  | ctx h =>
      exact whStepCtx_recCall_nonCtorMajor_aux hW (he.symm ▸ h) rfl hnc
  | native h => exact hnative _ (he.symm ▸ h)
  | recMajor hm hr hl hnK hnP h =>
      have hh := (recCall_const_inj he).1
      rcases hK with hK | hK
      · exact hnK ⟨w, hh, hK⟩
      · exact hnP ⟨w, hh, hK⟩
  | appHead h =>
      simp only [recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      rw [← hh] at h
      exact normalR_recPrefixCK2 hW w.hrec w.hrecK _ _ _
        (by have h₁ := w.hpre; have h₂ := w.hnmin; omega) _ h

/-- The repaired beta-index gap is a genuine new step. -/
theorem whStepCK2_eqGap (n : Nat) :
    WhStepCK2 eqEnvT n eqGapCtx eqGapRedex (.sort .zero) :=
  .native (kNativeHead_eqGap n)

theorem redR_whStepCK2_eqGap (n : Nat) :
    RedR (WhStepCK2 eqEnvT n) eqGapCtx eqGapRedex (.sort .zero) :=
  redR_single (whStepCK2_eqGap n)

-- BEGIN RCIC_NATIVE_READBACK_CK2_ROOTS
#print axioms WhStepCK2
#print axioms WhStepCK2.ctx
#print axioms WhStepCK2.native
#print axioms WhStepCK2.recMajor
#print axioms WhStepCK2.appHead
#print axioms SaturatedRecSource
#print axioms saturatedRecSource_app
#print axioms whStepCK2_ctx_or_saturated
#print axioms saturatedRecSource_is_app
#print axioms saturatedRecSource_spine
#print axioms normalR_sortCK2
#print axioms normalR_piCK2
#print axioms normalR_lamCK2
#print axioms normalR_bvarCK2
#print axioms normalR_famAppCK2
#print axioms normalR_ctorSpineCK2
#print axioms normalR_recPrefixCK2
#print axioms readbackLaws_whStepCK2
#print axioms whStepCtx_app_cases
#print axioms whStepCtx_recCall_ctor
#print axioms whStepCK2_ctx_det
#print axioms recCall_const_inj
#print axioms kNativeHead_whStepCK2_det
#print axioms detR_whStepCK2
#print axioms normalUniqueR_whStepCK2
#print axioms normalR_kRec_of_no_native
#print axioms whStepCK2_eqGap
#print axioms redR_whStepCK2_eqGap
-- END RCIC_NATIVE_READBACK_CK2_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2Audit
