import rcic.RcicF3KTWRecMem
import rcic.RcicIndGroupNonIRScope

/-!
# F3 S7 KT-2 hN: the semantic non-IR premise `NonIRSem` from a syntactic one

`NonIRKinds f Fs`: no field free-references (`freeBvarRef`, #8067) an earlier
field whose kind is not `plain`. Then the denotation of every field (and of its
`piDom`) at `push pre ρp` depends only on the plain values of `pre`
(`den_freeAgree`), which is `NonIRSem`.

`closure_claim = 0`.
-/

namespace Rcic.F3

namespace PSet

open Rcic.Declarative

/-- Moving one slot from the base into the depth leaves the scan unchanged. -/
theorem freeBvarRef_succ (b : Nat) : (d : Nat) → (e : Expr Nat) →
    freeBvarRef (b + 1) d e = freeBvarRef b (d + 1) e
  | d, .bvar i => by
      show decide (i = b + 1 + d) = decide (i = b + (d + 1))
      rw [show b + 1 + d = b + (d + 1) by omega]
  | _, .sort _ => rfl
  | _, .lit _ => rfl
  | _, .const _ _ => rfl
  | d, .app g a => by
      show (freeBvarRef (b + 1) d g || freeBvarRef (b + 1) d a) =
        (freeBvarRef b (d + 1) g || freeBvarRef b (d + 1) a)
      rw [freeBvarRef_succ b d g, freeBvarRef_succ b d a]
  | d, .lam A B => by
      show (freeBvarRef (b + 1) d A || freeBvarRef (b + 1) (d + 1) B) =
        (freeBvarRef b (d + 1) A || freeBvarRef b (d + 1 + 1) B)
      rw [freeBvarRef_succ b d A, freeBvarRef_succ b (d + 1) B]
  | d, .pi A B => by
      show (freeBvarRef (b + 1) d A || freeBvarRef (b + 1) (d + 1) B) =
        (freeBvarRef b (d + 1) A || freeBvarRef b (d + 1 + 1) B)
      rw [freeBvarRef_succ b d A, freeBvarRef_succ b (d + 1) B]
  | d, .letE A v B => by
      show (freeBvarRef (b + 1) d A || freeBvarRef (b + 1) d v ||
          freeBvarRef (b + 1) (d + 1) B) =
        (freeBvarRef b (d + 1) A || freeBvarRef b (d + 1) v || freeBvarRef b (d + 1 + 1) B)
      rw [freeBvarRef_succ b d A, freeBvarRef_succ b d v, freeBvarRef_succ b (d + 1) B]

/-- Agreement under one binder: slot `0` is the new value, slot `i+1` is the
outer slot `i` (read at depth `1`). -/
theorem vcons_freeAgree {x x' : PSet.{T}} {ρ ρ' : Nat → PSet.{T}} (hx : Equiv x x')
    (b : Expr Nat) (h : ∀ i, freeBvarRef i 1 b = true → Equiv (ρ i) (ρ' i)) :
    ∀ i, freeBvarRef i 0 b = true → Equiv (vcons x ρ i) (vcons x' ρ' i)
  | 0, _ => hx
  | i + 1, hi => h i (by rw [← freeBvarRef_succ i 0 b]; exact hi)

/-- The denotation only reads the free slots of the expression. -/
theorem den_freeAgree (M : Interp.{T}) (σ : Nat → Nat) :
    (e : Expr Nat) → ∀ {ρ ρ' : Nat → PSet.{T}},
      (∀ i, freeBvarRef i 0 e = true → Equiv (ρ i) (ρ' i)) →
      Equiv (den M σ ρ e) (den M σ ρ' e)
  | .bvar i, _, _, h => h i (by show decide (i = i + 0) = true; exact decide_eq_true rfl)
  | .sort _, _, _, _ => Equiv.rfl
  | .const _ _, _, _, _ => Equiv.rfl
  | .lit _, _, _, _ => Equiv.rfl
  | .app f a, _, _, h =>
      fapp_congr (den_freeAgree M σ f fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)))
        (den_freeAgree M σ a fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi)))
  | .lam A b, _, _, h =>
      lamVal_congr M (den_freeAgree M σ A fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)))
        (fun _ _ hx => den_freeAgree M σ b
          (vcons_freeAgree hx b fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi))))
  | .pi A B, _, _, h =>
      piVal_congr M (den_freeAgree M σ A fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl hi)))
        (fun _ _ hx => den_freeAgree M σ B
          (vcons_freeAgree hx B fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi))))
  | .letE A v b, _, _, h =>
      den_freeAgree M σ b
        (vcons_freeAgree (den_freeAgree M σ v fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr hi))))) b
          fun i hi => h i (Bool.or_eq_true_iff.mpr (Or.inr hi)))

/-- `piDom` only shrinks the free slots. -/
theorem freeBvarRef_piDom (i : Nat) : (A : Expr Nat) →
    freeBvarRef i 0 (piDom A) = true → freeBvarRef i 0 A = true
  | .pi _ _, h => Bool.or_eq_true_iff.mpr (Or.inl h)
  | .bvar _, h => h
  | .sort _, h => h
  | .lit _, h => h
  | .const _ _, h => h
  | .app _ _, h => h
  | .lam _ _, h => h
  | .letE _ _ _, h => h

/-- Equal plain values: the entries at plain positions agree. -/
theorem plainVals_agree : (ks : List PKind) → (xs ys : List PSet.{T}) →
    (hx : ks.length = xs.length) → (hy : ks.length = ys.length) →
    LEq (plainVals ks xs) (plainVals ks ys) →
    ∀ j (hj : j < ks.length), ks[j] = .plain →
      Equiv (xs[j]'(by omega)) (ys[j]'(by omega))
  | [], _, _, _, _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, hx, _, _, _, _, _ => absurd hx (by simp)
  | _ :: _, _ :: _, [], _, hy, _, _, _, _ => absurd hy (by simp)
  | .plain :: ks, x :: xs, y :: ys, hx, hy, hle, j, hj, hk => by
      obtain ⟨hxy, hle'⟩ := hle
      cases j with
      | zero => exact hxy
      | succ j =>
          exact plainVals_agree ks xs ys (by simpa using hx) (by simpa using hy) hle' j
            (by simpa using hj) (by simpa using hk)
  | .direct :: ks, _ :: xs, _ :: ys, hx, hy, hle, j, hj, hk => by
      cases j with
      | zero => exact absurd hk (by simp)
      | succ j =>
          exact plainVals_agree ks xs ys (by simpa using hx) (by simpa using hy) hle j
            (by simpa using hj) (by simpa using hk)
  | .fn :: ks, _ :: xs, _ :: ys, hx, hy, hle, j, hj, hk => by
      cases j with
      | zero => exact absurd hk (by simp)
      | succ j =>
          exact plainVals_agree ks xs ys (by simpa using hx) (by simpa using hy) hle j
            (by simpa using hj) (by simpa using hk)

/-- The syntactic class-A boundary on one field list: no field free-references
an earlier non-`plain` field (`freeBvarRef (k-1-j) 0`, the #8067 slot). -/
def NonIRKinds (f : Nat) (Fs : List (Expr Nat)) : Prop :=
  ∀ j k, j < k → k < Fs.length → kindOf f (fieldAt Fs j) ≠ .plain →
    freeBvarRef (k - 1 - j) 0 (fieldAt Fs k) = false

/-- `fieldAt` inside the list is indexing. -/
theorem fieldAt_eq_getElem {Fs : List (Expr Nat)} {k : Nat} (hk : k < Fs.length) :
    fieldAt Fs k = Fs[k] := by
  show Fs.getD k (.sort .zero) = Fs[k]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- Agreement of two pushed prefixes at every free slot of `e` whose prefix
entry is read: slots `≥ k` read the common base. -/
theorem push_freeAgree (k : Nat) {pre pre' : List PSet.{T}} (hpre : pre.length = k)
    (hpre' : pre'.length = k) (ρ : Nat → PSet.{T}) (e : Expr Nat)
    (hag : ∀ j (hj : j < k), freeBvarRef (k - 1 - j) 0 e = true →
      Equiv (pre[j]'(by omega)) (pre'[j]'(by omega))) :
    ∀ i, freeBvarRef i 0 e = true → Equiv (push pre ρ i) (push pre' ρ i) := by
  intro i hi
  by_cases hik : i < k
  · rw [push_lt pre ρ i (by omega), push_lt pre' ρ i (by omega)]
    have h := hag (k - 1 - i) (by omega) (by rw [show k - 1 - (k - 1 - i) = i by omega]; exact hi)
    simp only [hpre, hpre']
    exact h
  · rw [show i = (i - k) + pre.length by omega, push_ge]
    rw [show (i - k) + pre.length = (i - k) + pre'.length by omega, push_ge]
    exact Equiv.rfl

/-- The syntactic boundary gives the semantic one. -/
theorem nonIRSem_of_kinds (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ρp : Nat → PSet.{4}) {f : Nat} {Fs : List (Expr Nat)} (h : NonIRKinds f Fs) :
    NonIRSem P μ σ ρp f Fs := by
  intro k hk pre pre' hpre hpre' hle
  have hks : ((kindsOf f Fs).take k).length = k := by
    simp only [kindsOf, List.length_take, List.length_map]; omega
  have hag : ∀ e, (∀ i, freeBvarRef i 0 e = true → freeBvarRef i 0 (fieldAt Fs k) = true) →
      ∀ i, freeBvarRef i 0 e = true → Equiv (push pre ρp i) (push pre' ρp i) := by
    intro e he
    refine push_freeAgree k hpre hpre' ρp e ?_
    intro j hj hfr
    have hkj : ((kindsOf f Fs).take k)[j]'(by omega) = kindOf f (fieldAt Fs j) := by
      simp only [List.getElem_take, kindsOf, List.getElem_map]
      rw [fieldAt_eq_getElem (by omega)]
    have hpl : ((kindsOf f Fs).take k)[j]'(by omega) = .plain := by
      rw [hkj]
      cases hq : kindOf f (fieldAt Fs j) with
      | plain => rfl
      | direct =>
          have := h j k (by omega) hk (by rw [hq]; exact PKind.noConfusion)
          rw [he _ hfr] at this; exact Bool.noConfusion this
      | fn =>
          have := h j k (by omega) hk (by rw [hq]; exact PKind.noConfusion)
          rw [he _ hfr] at this; exact Bool.noConfusion this
    exact plainVals_agree _ pre pre' (by omega) (by omega) hle j (by omega) hpl
  exact ⟨den_freeAgree _ σ _ (hag _ fun _ hi => hi),
    den_freeAgree _ σ _ (hag _ fun i hi => freeBvarRef_piDom i _ hi)⟩

/-- The `famKT_fix` premise `hN` from per-constructor `NonIRKinds`. -/
theorem hN_of_kinds (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (h : ∀ c, c ∈ fd.ctors → NonIRKinds fd.fref c.1) :
    ∀ σ ρp (j : Fin fd.ctors.length), NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1 :=
  fun σ ρp _ => nonIRSem_of_kinds P μ σ ρp (h _ (List.get_mem _ _ _))

/-- #8067's `NonIRFieldList` gives `NonIRKinds` on a direct-recursion field list
(`FieldsClass`): a non-`plain` field is a literal family application, hence
family-visible. -/
theorem nonIRKinds_of_fieldList {E : ResolvedEnv} {fam ar np nq d : Nat}
    {Fs : List (Expr Nat)} (hcls : FieldsClass fam ar np nq Fs d)
    (h : NonIRFieldList E fam Fs) : NonIRKinds fam Fs := by
  intro j k hjk hk hkind
  have hj : j < Fs.length := by omega
  have hvis : FamilyVisible E fam Fs[j] := by
    rcases hcls.mem _ (List.getElem_mem hj) with hfree | ⟨_, idx, hA, _, _⟩
    · exact absurd (fieldAt_eq_getElem hj ▸ kindOf_free hfree) hkind
    · rw [hA]; exact familyVisible_ctorDoms_drec
  rw [fieldAt_eq_getElem hk]
  exact h ⟨j, hj⟩ ⟨k, hk⟩ hjk hvis

/-- `hN` for an admitted direct-recursion group whose views are non-IR. -/
theorem hN_of_admitted (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (G : RecGroup a) (hNI : a.NonIR) :
    ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1 := by
  refine hN_of_kinds P μ (famDataOf a) ?_
  intro c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  exact nonIRKinds_of_fieldList (G.fields i) (hNI i)

/-- `hN` from the environment: an admitted direct-recursion group of an
`EnvWfT` environment passing the scope test (#8067's scoped discharge). -/
theorem hN_of_scope (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hC : hW.ScopeCheck) (hp : E.members r = some m)
    (a : RecursorEliminationAdmitted E r m) (G : RecGroup a) :
    ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1 :=
  hN_of_admitted P μ a G (admitted_group_nonIR_scoped hW hC hp a)

/-- `recVal_mem_rec_KT` with `hN` discharged from the environment
(`EnvWfT` + scope test, #8067). -/
theorem recVal_mem_rec_KT_scoped (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hC : hW.ScopeCheck) (hp : E.members r = some m)
    (a : RecursorEliminationAdmitted E r m) (G : RecGroup a) (vs : List Nat)
    (ps : List PSet.{4}) (hpsl : ps.length = a.family.parameters.length)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hType : evalTotal (σOf vs) a.family.resultLevel ≠ 0) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) :=
  recVal_mem_rec_KT P μ a G vs ps hpsl (hN_of_scope P μ hW hC hp a G) hf hKT hctorμ hType

/-- `recVal_mem_recP_KT` with `hN` discharged from the environment. -/
theorem recVal_mem_recP_KT_scoped (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hC : hW.ScopeCheck) (hp : E.members r = some m)
    (a : RecursorEliminationAdmitted E r m) (G : RecGroup a) (vs : List Nat)
    (ps : List PSet.{4}) (hpsl : ps.length = a.family.parameters.length)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hProp : evalTotal (σOf vs) a.family.resultLevel = 0)
    (hpol : a.policy = .propOnly) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) :=
  recVal_mem_recP_KT P μ a G vs ps hpsl (hN_of_scope P μ hW hC hp a G) hf hKT hctorμ hProp hpol

end PSet

end Rcic.F3
