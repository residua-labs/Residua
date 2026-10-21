import rcic.RcicNativeReadbackCK2
import rcic.RcicNativeReadbackCK2Index

/-!
# Exact determinism of the complete index-scheduled CK2 candidate

The proof composes the existing CK determinism and exclusions, the existing
projection-canon invariance, and the first-mismatch scheduler's determinism.
Two small CK inversion lemmas expose its recursive contexts.  No CK proof
block or CK relation is replaced. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit

variable {E : ResolvedEnv} {Γ : LCtx}

/-- An index scheduler cannot step when its whole input already equals its target. -/
theorem firstWhnfMismatch_ne {xs target ys : List (Expr Nat)}
    (h : FirstWhnfMismatch E Γ xs target ys) : xs ≠ target := by
  induction h with
  | here hne _ =>
      intro he
      exact hne (List.cons.inj he).1
  | there _ _ ih =>
      intro he
      exact ih (List.cons.inj he).2

/-- Every quantity the scheduler reads is fixed by the recursor source.
The arbitrary witness fields affect only their fixed field count; projected
fields are then equal by the landed projection-canon theorem. -/
theorem indexSchedule_data_eq {w₁ w₂ : IotaWitness E} {x : Expr Nat}
    (hK₁ : KFreeW w₁ ∨ KFieldW w₁) (hK₂ : KFreeW w₂ ∨ KFieldW w₂)
    (hr : w₁.recRef = w₂.recRef) (hls : w₁.ls = w₂.ls)
    (hp : w₁.preMajor = w₂.preMajor) :
    redexIdx w₁ = redexIdx w₂ ∧
    scheduledCanonIdx w₁ x = scheduledCanonIdx w₂ x ∧
    w₁.preMajor.take (w₁.nparams + 1 + w₁.nMinors) =
      w₂.preMajor.take (w₂.nparams + 1 + w₂.nMinors) := by
  have hnm₁ : w₁.nMinors = 1 := hK₁.elim (fun h => h.2.1) (fun h => h.2.1)
  have hnm₂ : w₂.nMinors = 1 := hK₂.elim (fun h => h.2.1) (fun h => h.2.1)
  have hnm : w₁.nMinors = w₂.nMinors := hnm₁.trans hnm₂.symm
  have hci₁ : w₁.ctorIdx = 0 := by have h := w₁.hidx; omega
  have hci₂ : w₂.ctorIdx = 0 := by have h := w₂.hidx; omega
  have hcr : w₁.ctorRef = w₂.ctorRef := by
    have h₁ := w₁.hctorIdx; have h₂ := w₂.hctorIdx
    have h₃ := w₁.hrecIdx; have h₄ := w₂.hrecIdx
    omega
  obtain ⟨_, hcm, hfr, _, hni, hnp, _, hk⟩ :=
    iotaWitness_env_of_same_refs hr hcr (congrArg List.length hp)
  have hfm : w₁.famMember = w₂.famMember := by
    have h₁ := w₁.hfam; have h₂ := w₂.hfam
    rw [hfr] at h₁
    exact Option.some.inj (h₁.symm.trans h₂)
  have hresult : w₁.ctorResult = w₂.ctorResult := by
    have h₁ := w₁.hpeel; have h₂ := w₂.hpeel
    rw [w₁.hnpar, hcm] at h₁
    rw [w₂.hnpar] at h₂
    exact congrArg Prod.snd (Option.some.inj (h₁.symm.trans h₂))
  have hfields := fields_length_eq_of_same_lhs hnm₁ hnm₂ hr hp
  have hpf := projFields_eq_of hr hls hfr hfm hcm hcr hni hnp hk hresult hnm hp x
  refine ⟨?_, ?_, ?_⟩
  · unfold redexIdx
    rw [hp, hnp, hnm]
  · unfold scheduledCanonIdx
    by_cases hf₁ : w₁.fields = []
    · have hf₂ : w₂.fields = [] := by
        apply List.length_eq_zero.mp
        rw [← hfields, hf₁]
        rfl
      rw [if_pos hf₁, if_pos hf₂]
      unfold resultIdxAt
      rw [hp, hnp, hls, hcm]
    · have hf₂ : w₂.fields ≠ [] := by
        intro he
        apply hf₁
        apply List.length_eq_zero.mp
        rw [hfields, he]
        rfl
      rw [if_neg hf₁, if_neg hf₂]
      unfold resultIdxAt
      rw [hpf, hp, hnp, hls, hcm]
  · rw [hp, hnp, hnm]

/-- Isolate the single new head operation from its contextual closure. -/
inductive IndexHead (E : ResolvedEnv) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | intro {w : IotaWitness E} {x : Expr Nat} {idxs : List (Expr Nat)}
      (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
      (hs : FirstWhnfMismatch E Γ (redexIdx w) (scheduledCanonIdx w x) idxs) :
      IndexHead E Γ (recCall (.const w.recRef w.ls) w.preMajor x)
        (recCall (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.nMinors) ++ idxs) x)

theorem IndexHead.toStep {a b : Expr Nat} (h : IndexHead E Γ a b) :
    WhStepIndexCK2 E Γ a b := by
  cases h with
  | intro hK hnc hs => exact .index hK hnc hs

/-- The chosen index position and contractum are unique across every witness. -/
theorem detR_indexHead (hW : EnvWfT E) : DetR (IndexHead E) := by
  intro Γ a b c h₁ h₂
  cases h₁ with
  | intro hK₁ hnc₁ hs₁ =>
      rename_i w₁ x₁ idxs₁
      generalize he : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ = a₀ at h₂
      cases h₂ with
      | intro hK₂ hnc₂ hs₂ =>
          rename_i w₂ x₂ idxs₂
          obtain ⟨hr, hls, hp, hx⟩ := recCall_const_inj he
          subst hx
          obtain ⟨hred, htarget, hpre⟩ := indexSchedule_data_eq hK₁ hK₂ hr hls hp
          rw [← hred, ← htarget] at hs₂
          have hidx := firstWhnfMismatch_det hW hs₁ hs₂
          rw [hr, hls, hpre, hidx]

/-- New index heads have no old CK step: context/iota and recursive contexts
are excluded by the old schedule, and syntactic K agreement excludes a mismatch. -/
theorem indexHead_ck_false (hW : EnvWfT E) {a b c : Expr Nat}
    (h₁ : IndexHead E Γ a b) (h₂ : WhStepCK E Γ a c) : False := by
  cases h₁ with
  | intro hK hnc hs =>
      rename_i w x idxs
      generalize he : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at h₂
      cases h₂ with
      | ctx hc => exact whStepCtx_recCall_nonCtorMajor_aux hW (he.symm ▸ hc) rfl hnc
      | kStar hK' hnc' hidx =>
          obtain ⟨hr, hls, hp, hx⟩ := recCall_const_inj he
          subst hx
          obtain ⟨hred, htarget, _⟩ := indexSchedule_data_eq hK (.inl hK') hr hls hp
          apply firstWhnfMismatch_ne hs
          apply hred.trans
          apply Eq.trans _ htarget.symm
          unfold scheduledCanonIdx
          rw [if_pos hK'.1]
          exact hidx
      | kProj hK' hnc' hf' hidx =>
          obtain ⟨hr, hls, hp, hx⟩ := recCall_const_inj he
          subst hx
          obtain ⟨hred, htarget, _⟩ := indexSchedule_data_eq hK (.inr hK') hr hls hp
          apply firstWhnfMismatch_ne hs
          apply hred.trans
          apply Eq.trans _ htarget.symm
          unfold scheduledCanonIdx
          rw [if_neg hK'.1]
          exact hidx
      | recMajor hm hr hl hnK hnP hc =>
          have hh := (recCall_const_inj he).1
          exact hK.elim (fun h => hnK ⟨w, hh, h⟩) (fun h => hnP ⟨w, hh, h⟩)
      | appHead hc =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [← hh] at hc
          exact whStepCK_recPrefix_false_aux hW w.hrec w.hrecK hc rfl
            (by have h₁ := w.hpre; have h₂ := w.hnmin; omega)

/-- At an application, an old CK step either follows its head or has a head
which remains normal for the entire extended grammar. -/
theorem ck_app_cases_index (hW : EnvWfT E) {f a b : Expr Nat}
    (h : WhStepCK E Γ (.app f a) b) :
    NormalR (WhStepIndexCK2 E) Γ f ∨
      ∃ f', WhStepCK E Γ f f' ∧ b = .app f' a := by
  generalize he : Expr.app f a = lhs at h
  cases h with
  | ctx hc =>
      rcases whStepCtx_app_cases (he.symm ▸ hc) with ⟨A, body, hf, _⟩ | hi | ⟨f', hf, hb⟩
      · exact .inl (hf.symm ▸ normalR_lamIndexCK2 Γ A body)
      · obtain ⟨hi⟩ := hi
        rcases derivedIotaU_app_head hi rfl with ⟨w, hf, hl⟩ | ⟨w, hf, hl⟩
        · refine .inl ?_
          intro e hs
          exact whStepIndexCK2_recPrefix_false_aux hW w.hrec w.hrecK hs hf hl
        · refine .inl ?_
          intro e hs
          exact whStepIndexCK2_recPrefix_false_aux hW w.hrec w.hrecK hs hf hl
      · exact .inr ⟨f', .ctx hf, hb⟩
  | kStar hK hnc hi =>
      rename_i w x
      simp only [recCall_eq_app] at he
      refine .inl (fun e hs => ?_)
      exact whStepIndexCK2_recPrefix_false_aux hW w.hrec w.hrecK hs
        (Expr.app.inj he).1 (by have h₁ := w.hpre; have h₂ := w.hnmin; omega)
  | kProj hK hnc hf hi =>
      rename_i w x
      simp only [recCall_eq_app] at he
      refine .inl (fun e hs => ?_)
      exact whStepIndexCK2_recPrefix_false_aux hW w.hrec w.hrecK hs
        (Expr.app.inj he).1 (by have h₁ := w.hpre; have h₂ := w.hnmin; omega)
  | recMajor hm hr hl hnK hnP hc =>
      simp only [recCall_eq_app] at he
      refine .inl (fun e hs => ?_)
      exact whStepIndexCK2_recPrefix_false_aux hW hm hr hs (Expr.app.inj he).1 (by omega)
  | appHead hf =>
      obtain ⟨rfl, rfl⟩ := Expr.app.inj he
      exact .inr ⟨_, hf, rfl⟩

/-- At a non-K recursor, an old CK step either follows its major or has a
constructor major which remains normal for the entire extended grammar. -/
theorem ck_recMajor_cases_index (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    {ls : List Level} {pre : List (Expr Nat)} {x b : Expr Nat}
    (hm : E.members r = some m) (hr : m.mclass = .recursorM)
    (hl : pre.length + 1 = piCount m.mtype)
    (hnK : ¬ KFreeRec E r) (hnP : ¬ KProjRec E r)
    (h : WhStepCK E Γ (recCall (.const r ls) pre x) b) :
    NormalR (WhStepIndexCK2 E) Γ x ∨
      ∃ x', WhStepCK E Γ x x' ∧ b = recCall (.const r ls) pre x' := by
  generalize he : recCall (.const r ls) pre x = lhs at h
  cases h with
  | ctx hc =>
      obtain ⟨s, us, ys, mm, hx, hm', hc'⟩ :=
        whStepCtx_recCall_ctor hW hm hr hl (he.symm ▸ hc)
      exact .inl (hx.symm ▸ normalR_ctorIndexCK2 hW hm' hc' Γ us ys)
  | kStar hK hnc hi =>
      have hh := (recCall_const_inj he).1
      exact (hnK ⟨_, hh.symm, hK⟩).elim
  | kProj hK hnc hf hi =>
      have hh := (recCall_const_inj he).1
      exact (hnP ⟨_, hh.symm, hK⟩).elim
  | recMajor hm' hr' hl' hnK' hnP' hc =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := recCall_const_inj he
      exact .inr ⟨_, hc, rfl⟩
  | appHead hc =>
      simp only [recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      rw [← hh] at hc
      exact (whStepCK_recPrefix_false_aux hW hm hr hc rfl (by omega)).elim

/-- CK determinism composes with both recursive contexts and the disjoint
index operation.  Only the extension's subderivation is the induction argument. -/
theorem whStepIndexCK2_ck_det (hW : EnvWfT E) {a b c : Expr Nat}
    (h : WhStepCK E Γ a b) (hs : WhStepIndexCK2 E Γ a c) : b = c := by
  induction hs generalizing b with
  | ck hs => exact detR_whStepCK hW Γ h hs
  | index hK hnc hi => exact (indexHead_ck_false hW (.intro hK hnc hi) h).elim
  | recMajor hm hr hl hnK hnP hs ih =>
      rcases ck_recMajor_cases_index hW hm hr hl hnK hnP h with hn | ⟨x', hx, rfl⟩
      · exact (hn _ hs).elim
      · exact congrArg (recCall _ _) (ih hx)
  | appHead hs ih =>
      rcases ck_app_cases_index hW h with hn | ⟨f', hf, rfl⟩
      · exact (hn _ hs).elim
      · exact congrArg (fun f => Expr.app f _) (ih hf)

/-- The new head operation is compatible with the complete contextual core. -/
theorem indexHead_whStepIndexCK2_det (hW : EnvWfT E) {a b c : Expr Nat}
    (hi : IndexHead E Γ a b) (hs : WhStepIndexCK2 E Γ a c) : b = c := by
  cases hi with
  | intro hK hnc hmismatch =>
      rename_i w x idxs
      generalize he : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at hs
      cases hs with
      | ck hc => exact (indexHead_ck_false hW (.intro hK hnc hmismatch) (he.symm ▸ hc)).elim
      | index hK' hnc' hs' =>
          exact detR_indexHead hW Γ (.intro hK hnc hmismatch)
            (he.symm ▸ IndexHead.intro hK' hnc' hs')
      | recMajor hm hr hl hnK hnP hs =>
          have hh := (recCall_const_inj he).1
          exact (hK.elim (fun h => hnK ⟨w, hh, h⟩) (fun h => hnP ⟨w, hh, h⟩)).elim
      | appHead hs =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [← hh] at hs
          exact (whStepIndexCK2_recPrefix_false_aux hW w.hrec w.hrecK hs rfl
            (by have h₁ := w.hpre; have h₂ := w.hnmin; omega)).elim

/-- Exact determinism on every raw source in a well-formed environment. -/
theorem detR_whStepIndexCK2 (hW : EnvWfT E) : DetR (WhStepIndexCK2 E) := by
  intro Γ a b c h₁ h₂
  induction h₁ generalizing c with
  | ck hc => exact whStepIndexCK2_ck_det hW hc h₂
  | index hK hnc hi => exact indexHead_whStepIndexCK2_det hW (.intro hK hnc hi) h₂
  | recMajor hm hr hl hnK hnP hs ih =>
      rename_i r m ls pre x x'
      generalize he : recCall (.const r ls) pre x = a₀ at h₂
      cases h₂ with
      | ck hc =>
          exact (whStepIndexCK2_ck_det hW (he.symm ▸ hc)
            (.recMajor hm hr hl hnK hnP hs)).symm
      | index hK' hnc' hi =>
          exact (indexHead_whStepIndexCK2_det hW (he.symm ▸ IndexHead.intro hK' hnc' hi)
            (.recMajor hm hr hl hnK hnP hs)).symm
      | recMajor hm' hr' hl' hnK' hnP' ht =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ := recCall_const_inj he
          exact congrArg (recCall (.const r ls) pre) (ih ht)
      | appHead ht =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [← hh] at ht
          exact (whStepIndexCK2_recPrefix_false_aux hW hm hr ht rfl (by omega)).elim
  | appHead hs ih =>
      rename_i f f' x
      generalize he : Expr.app f x = a₀ at h₂
      cases h₂ with
      | ck hc => exact (whStepIndexCK2_ck_det hW (he.symm ▸ hc) (.appHead hs)).symm
      | index hK hnc hi =>
          exact (indexHead_whStepIndexCK2_det hW (he.symm ▸ IndexHead.intro hK hnc hi)
            (.appHead hs)).symm
      | recMajor hm hr hl hnK hnP ht =>
          simp only [recCall_eq_app] at he
          have hh := (Expr.app.inj he).1
          rw [hh] at hs
          exact (whStepIndexCK2_recPrefix_false_aux hW hm hr hs rfl (by omega)).elim
      | appHead ht =>
          obtain ⟨rfl, rfl⟩ := Expr.app.inj he
          exact congrArg (fun f => Expr.app f x) (ih ht)

theorem normalUniqueR_whStepIndexCK2 (hW : EnvWfT E) :
    NormalUniqueR (WhStepIndexCK2 E) :=
  normalUniqueR_of_det (detR_whStepIndexCK2 hW)

-- BEGIN RCIC_NATIVE_READBACK_CK2_INDEX_DET_ROOTS
#print axioms firstWhnfMismatch_ne
#print axioms indexSchedule_data_eq
#print axioms IndexHead
#print axioms IndexHead.intro
#print axioms IndexHead.toStep
#print axioms detR_indexHead
#print axioms indexHead_ck_false
#print axioms ck_app_cases_index
#print axioms ck_recMajor_cases_index
#print axioms whStepIndexCK2_ck_det
#print axioms indexHead_whStepIndexCK2_det
#print axioms detR_whStepIndexCK2
#print axioms normalUniqueR_whStepIndexCK2
-- END RCIC_NATIVE_READBACK_CK2_INDEX_DET_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit
